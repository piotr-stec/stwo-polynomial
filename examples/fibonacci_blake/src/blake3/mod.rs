//! AIR for blake2s and blake3.
//! See <https://en.wikipedia.org/wiki/BLAKE_(hash_function)>

use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, Sub};
use std::simd::u32x16;

use num_traits::One;
use stwo::core::channel::Channel;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::BaseField;
use stwo::prover::backend::simd::m31::PackedBaseField;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo_constraint_framework::{EvalAtRow, Relation, RelationEntry, relation};
use xor_table::{xor4, xor7, xor8, xor9, xor12};

pub mod air;
pub mod blake3;
pub mod preprocessed_columns;
pub mod round;
pub mod scheduler;
pub mod xor_table;

// Re-export for integration
pub use air::{
    AllElements, BlakeComponents, BlakeComponentsForIntegration, BlakeStatement0, BlakeStatement1,
};

#[cfg(test)]
mod test_our_blake3;

const STATE_SIZE: usize = 16;
const MESSAGE_SIZE: usize = 16;
const N_FELTS_IN_U32: usize = 2;
const N_ROUND_INPUT_FELTS: usize = (STATE_SIZE + STATE_SIZE + MESSAGE_SIZE) * N_FELTS_IN_U32;

// Parameters for Blake3.
pub const N_ROUNDS: usize = 7;
/// A splitting N_ROUNDS into several powers of 2.
/// 7 = 4 + 2 + 1 = 2^2 + 2^1 + 2^0
pub const ROUND_LOG_SPLIT: [u32; 3] = [2, 1, 0];

/// Minimum log_size values for XOR lookup tables.
/// These represent the trace size requirements (log2 of number of rows) for each XOR table component.
/// XOR tables precompute XOR operations for different bit widths to avoid expensive range checks in circuit.
pub const XOR12_MIN_LOG_SIZE: u32 = 16; // XOR table for 12-bit operations
pub const XOR9_MIN_LOG_SIZE: u32 = 14; // XOR table for 9-bit operations
pub const XOR8_MIN_LOG_SIZE: u32 = 12; // XOR table for 8-bit operations
pub const XOR7_MIN_LOG_SIZE: u32 = 10; // XOR table for 7-bit operations
pub const XOR4_MIN_LOG_SIZE: u32 = 8; // XOR table for 4-bit operations

#[derive(Default)]
pub struct XorAccums {
    pub xor12: xor12::XorAccumulator<12, 4>,
    pub xor9: xor9::XorAccumulator<9, 2>,
    pub xor8: xor8::XorAccumulator<8, 2>,
    pub xor7: xor7::XorAccumulator<7, 2>,
    pub xor4: xor4::XorAccumulator<4, 0>,
}
impl XorAccums {
    fn add_input(&mut self, w: u32, a: u32x16, b: u32x16) {
        match w {
            12 => self.xor12.add_input(a, b),
            9 => self.xor9.add_input(a, b),
            8 => self.xor8.add_input(a, b),
            7 => self.xor7.add_input(a, b),
            4 => self.xor4.add_input(a, b),
            _ => panic!("Invalid w"),
        }
    }
}

relation!(XorElements12, 3);
relation!(XorElements9, 3);
relation!(XorElements8, 3);
relation!(XorElements7, 3);
relation!(XorElements4, 3);

#[derive(Clone)]
pub struct BlakeXorElements {
    pub xor12: XorElements12,
    pub xor9: XorElements9,
    pub xor8: XorElements8,
    pub xor7: XorElements7,
    pub xor4: XorElements4,
}
impl BlakeXorElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            xor12: XorElements12::draw(channel),
            xor9: XorElements9::draw(channel),
            xor8: XorElements8::draw(channel),
            xor7: XorElements7::draw(channel),
            xor4: XorElements4::draw(channel),
        }
    }
    fn dummy() -> Self {
        Self {
            xor12: XorElements12::dummy(),
            xor9: XorElements9::dummy(),
            xor8: XorElements8::dummy(),
            xor7: XorElements7::dummy(),
            xor4: XorElements4::dummy(),
        }
    }

    // TODO(alont): Generalize this to variable sizes batches if ever used.
    fn use_relation<E: EvalAtRow>(&self, eval: &mut E, w: u32, values: [&[E::F]; 2]) {
        match w {
            12 => {
                eval.add_to_relation(RelationEntry::new(&self.xor12, E::EF::one(), values[0]));
                eval.add_to_relation(RelationEntry::new(&self.xor12, E::EF::one(), values[1]));
            }
            9 => {
                eval.add_to_relation(RelationEntry::new(&self.xor9, E::EF::one(), values[0]));
                eval.add_to_relation(RelationEntry::new(&self.xor9, E::EF::one(), values[1]));
            }
            8 => {
                eval.add_to_relation(RelationEntry::new(&self.xor8, E::EF::one(), values[0]));
                eval.add_to_relation(RelationEntry::new(&self.xor8, E::EF::one(), values[1]));
            }
            7 => {
                eval.add_to_relation(RelationEntry::new(&self.xor7, E::EF::one(), values[0]));
                eval.add_to_relation(RelationEntry::new(&self.xor7, E::EF::one(), values[1]));
            }
            4 => {
                eval.add_to_relation(RelationEntry::new(&self.xor4, E::EF::one(), values[0]));
                eval.add_to_relation(RelationEntry::new(&self.xor4, E::EF::one(), values[1]));
            }
            _ => panic!("Invalid w"),
        };
    }

    fn combine(&self, w: u32, values: &[PackedBaseField]) -> PackedSecureField {
        match w {
            12 => self.xor12.combine(values),
            9 => self.xor9.combine(values),
            8 => self.xor8.combine(values),
            7 => self.xor7.combine(values),
            4 => self.xor4.combine(values),
            _ => panic!("Invalid w"),
        }
    }
}

/// Utility for representing a u32 as two field elements, for constraint evaluation.
#[derive(Clone, Debug)]
struct Fu32<F>
where
    F: FieldExpOps
        + Clone
        + Debug
        + AddAssign<F>
        + Add<F, Output = F>
        + Sub<F, Output = F>
        + Mul<BaseField, Output = F>,
{
    l: F,
    h: F,
}
impl<F> Fu32<F>
where
    F: FieldExpOps
        + Clone
        + Debug
        + AddAssign<F>
        + Add<F, Output = F>
        + Sub<F, Output = F>
        + Mul<BaseField, Output = F>,
{
    fn into_felts(self) -> [F; 2] {
        [self.l, self.h]
    }
}

/// Utility for splitting a u32 into 2 field elements in trace generation.
fn to_felts(x: &u32x16) -> [PackedBaseField; 2] {
    [
        unsafe { PackedBaseField::from_simd_unchecked(x & u32x16::splat(0xffff)) },
        unsafe { PackedBaseField::from_simd_unchecked(x >> 16) },
    ]
}
