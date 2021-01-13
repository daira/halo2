//! This module implements "simplified SWU" hashing to short Weierstrass curves
//! with a = 0.

use core::fmt::Debug;
use core::marker::PhantomData;
use subtle::ConstantTimeEq;

use super::{Curve, CurveAffine, FieldExt};

/// A method of hashing to an elliptic curve.
/// (If no isogeny is required, then C and I should be the same.)
pub trait HashToCurve<F: FieldExt, I: CurveAffine<Base = F>, C: CurveAffine<Base = F>> {
    /// A non-uniform map from a field element to the isogenous curve. This is *not*
    /// suitable for applications requiring a random oracle. Use `hash_to_curve`
    /// instead unless you are really sure that a non-uniform map is sufficient.
    fn map_to_curve(&self, u: &C::Base) -> I::Projective;

    /// The isogeny map from curve I to curve C.
    /// (If no isogeny is required, this should be the identity function.)
    fn iso_map(&self, p: &I::Projective) -> C::Projective;

    /// The random oracle map.
    fn hash_to_curve(&self, u: &C::Base) -> C::Projective;
}

/// The simplified SWU hash-to-curve method, using an isogenous curve
/// y^2 = x^3 + a*x + b.
#[derive(Debug)]
pub struct SimplifiedSWUWithDegree3Isogeny<
    F: FieldExt,
    I: CurveAffine<Base = F>,
    C: CurveAffine<Base = F>,
> {
    /// `Z` parameter (ξ in [WB2019]).
    pub z: F,

    /// Precomputed -b/a for the isogenous curve.
    pub minus_b_over_a: F,

    /// Precomputed b/Za for the isogenous curve.
    pub b_over_za: F,

    /// Precomputed sqrt(Z / ROOT_OF_UNITY).
    pub theta: F,

    /// Constants for the isogeny.
    pub isogeny_constants: [F; 13],

    marker_curve: PhantomData<C>,
    marker_iso: PhantomData<I>,
}

impl<F: FieldExt, I: CurveAffine<Base = F>, C: CurveAffine<Base = F>>
    SimplifiedSWUWithDegree3Isogeny<F, I, C>
{
    /// Create a SimplifiedSWUWithDegree3Isogeny method for the given parameters.
    ///
    /// # Panics
    /// Panics if z is square.
    pub fn new(z: &F, isogeny_constants: &[F; 13]) -> Self {
        let a = I::a();
        let b = I::b();

        SimplifiedSWUWithDegree3Isogeny {
            z: *z,
            minus_b_over_a: (-b) * &(a.invert().unwrap()),
            b_over_za: b * &((*z * a).invert().unwrap()),
            theta: (F::ROOT_OF_UNITY.invert().unwrap() * z).sqrt().unwrap(),
            isogeny_constants: *isogeny_constants,
            marker_curve: PhantomData,
            marker_iso: PhantomData,
        }
    }
}

impl<F: FieldExt, I: CurveAffine<Base = F>, C: CurveAffine<Base = F>> HashToCurve<F, I, C>
    for SimplifiedSWUWithDegree3Isogeny<F, I, C>
{
    fn map_to_curve(&self, u: &F) -> I::Projective {
        // 1. tv1 = inv0(Z^2 * u^4 + Z * u^2)
        // 2. x1 = (-B / A) * (1 + tv1)
        // 3. If tv1 == 0, set x1 = B / (Z * A)
        // 4. gx1 = x1^3 + A * x1 + B
        //
        // We use the "Avoiding inversions" optimization in [WB2019, section 4.2]
        // (not to be confused with section 4.3):
        //
        //   here       [WB2019]
        //   -------    ---------------------------------
        //   Z          ξ
        //   u          t
        //   Z * u^2    ξ * t^2 (called u, confusingly)
        //   x1         X_0(t)
        //   x2         X_1(t)
        //   gx1        g(X_0(t))
        //   gx2        g(X_1(t))
        //
        // Using the "here" names:
        //    x1 = num_x1/div      = [B*(Z^2 * u^4 + Z * u^2 + 1)] / [-A*(Z^2 * u^4 + Z * u^2]
        //   gx1 = num_gx1/div_gx1 = [num_x1^3 + A * num_x1 * div^2 + B * div^3] / div^3

        let a = I::a();
        let b = I::b();
        let z_u2 = self.z * u.square();
        let ta = z_u2.square() + z_u2;
        let num_x1 = b * (ta + F::one());
        let div = -a * ta;
        let num2_x1 = num_x1.square();
        let div2 = div.square();
        let div3 = div2 * div;
        let ta_is_zero = ta.ct_is_zero();
        let num_gx1 = F::conditional_select(
            &((num2_x1 + a * div2) * num_x1 + b * div3),
            &self.b_over_za,
            ta_is_zero,
        );
        let div_gx1 = F::conditional_select(&div3, &F::one(), ta_is_zero);

        // debug
        let x1 = num_x1 * div.invert().unwrap();
        let gx1 = num_gx1 * div_gx1.invert().unwrap();
        let tv1 = if ta.is_zero() {
            F::zero()
        } else {
            ta.invert().unwrap()
        };
        assert!(
            x1 == if tv1.is_zero() {
                self.b_over_za
            } else {
                self.minus_b_over_a * (F::one() + tv1)
            }
        );
        assert!(gx1 == (x1.square() + a) * x1 + b);

        // 5. x2 = Z * u^2 * x1
        let num_x2 = z_u2 * num_x1; // same div

        // 6. gx2 = x2^3 + A * x2 + B  [optimized out; see below]
        // 7. If is_square(gx1), set x = x1 and y = sqrt(gx1)
        // 8. Else set x = x2 and y = sqrt(gx2)
        let (gx1_square, y1) = F::sqrt_ratio(&num_gx1, &div_gx1);

        // This magic also comes from a generalization of [WB2019, section 4.2].
        //
        // The Sarkar square root algorithm with input s gives us a square root of
        // ROOT_OF_UNITY * s for free when s is not square, where h is a fixed nonsquare.
        // We know that Z / ROOT_OF_UNITY is a square since both Z and ROOT_OF_UNITY are
        // nonsquares. Precompute theta as a square root of Z / ROOT_OF_UNITY.
        //
        // We have gx2 = g(Z * u^2 * x1) = Z^3 * u^6 * gx1
        //                               = (Z * u^3)^2 * (Z/h * h * gx1)
        //                               = (Z * theta * u^3)^2 * (h * gx1)
        //
        // When gx1 is not square, y1 is a square root of h * gx1, and so Z * theta * u^3 * y1
        // is a square root of gx2. Note that we don't actually need to compute gx2.

        let y2 = self.theta * z_u2 * u * y1;

        // debug
        if bool::from(gx1_square) {
            let x2 = num_x2 * div.invert().unwrap();
            assert!(y1.square() == F::ROOT_OF_UNITY * gx1);
            assert!(y2.square() == (x2.square() + a) * x2 + b);
        }

        let num_x = F::conditional_select(&num_x2, &num_x1, gx1_square);
        let y = F::conditional_select(&y2, &y1, gx1_square);

        // 9. If sgn0(u) != sgn0(y), set y = -y
        let y = F::conditional_select(
            &(-y),
            &y,
            (u.get_lower_32() % 2).ct_eq(&(y.get_lower_32() % 2)),
        );

        //println!("num_x = {:?}\ndiv   = {:?}\ny     = {:?}\ndiv3  = {:?}", num_x, div, y, div3);
        I::Projective::new_jacobian(num_x * div, y * div3, div).unwrap()
    }

    /// Implements a degree 3 isogeny map.
    fn iso_map(&self, p: &I::Projective) -> C::Projective {
        // The input and output are in Jacobian coordinates, using the method
        // in "Avoiding inversions" [WB2019, section 4.3].

        let iso = self.isogeny_constants;
        let (x, y, z) = p.jacobian_coordinates();

        let z2 = z.square();
        let z3 = z2 * z;
        let z4 = z2.square();
        let z6 = z3.square();

        let num_x = ((iso[0] * x + iso[1] * z2) * x + iso[2] * z4) * x + iso[3] * z6;
        let div_x = (z2 * x + iso[4] * z4) * x + iso[5] * z6;

        let num_y = (((iso[6] * x + iso[7] * z2) * x + iso[8] * z4) * x + iso[9] * z6) * y;
        let div_y = (((x + iso[10] * z2) * x + iso[11] * z4) * x + iso[12] * z6) * z3;

        let zo = div_x * div_y;
        let xo = num_x * div_y * zo;
        let yo = num_y * div_x * zo;

        C::Projective::new_jacobian(xo, yo, zo).unwrap()
    }

    fn hash_to_curve(&self, x: &F) -> C::Projective {
        todo!()
    }
}
