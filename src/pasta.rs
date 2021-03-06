//! This module contains implementations for the Pallas and Vesta elliptic curve
//! groups.

#[macro_use]
mod macros;
mod curves;
mod fields;

pub mod pallas;
pub mod vesta;

pub use curves::*;
pub use fields::*;

#[test]
fn test_endo_consistency() {
    use crate::arithmetic::{Curve, FieldExt};

    let a = pallas::Point::one();
    assert_eq!(a * pallas::Scalar::ZETA, a.endo());
    let a = vesta::Point::one();
    assert_eq!(a * vesta::Scalar::ZETA, a.endo());
}
