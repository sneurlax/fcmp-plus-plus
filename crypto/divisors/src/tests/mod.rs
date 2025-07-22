use rand_core::OsRng;

use group::{ff::Field, Group};
use dalek_ff_group::EdwardsPoint;
use pasta_curves::{Ep, Eq};

use crate::{DivisorCurve, Poly, new_divisor};

mod poly;

// Equation 4 in the security proofs
fn check_divisor<C: DivisorCurve>(points: Vec<C>) {
  // Create the divisor
  let divisor = new_divisor::<C>(&points).unwrap();
  let eval = |c| {
    let (x, y) = C::to_xy(c).unwrap();
    divisor.eval(x, y)
  };

  // Decide challgenges
  let c0 = C::random(&mut OsRng);
  let c1 = C::random(&mut OsRng);
  let c2 = -(c0 + c1);
  let (slope, intercept) = crate::slope_intercept::<C>(c0, c1);

  let mut rhs = <C as DivisorCurve>::FieldElement::ONE;
  for point in points {
    let (x, y) = C::to_xy(point).unwrap();
    rhs *= intercept - (y - (slope * x));
  }
  assert_eq!(eval(c0) * eval(c1) * eval(c2), rhs);
}

fn test_divisor<C: DivisorCurve>() {
  for i in 1 ..= 255 {
    println!("Test iteration {i}");

    // Select points
    let mut points = vec![];
    for _ in 0 .. i {
      points.push(C::random(&mut OsRng));
    }
    points.push(-points.iter().sum::<C>());
    println!("Points {}", points.len());

    // Perform the original check
    check_divisor(points.clone());

    // Create the divisor
    let divisor = new_divisor::<C>(&points).unwrap();

    // For a divisor interpolating 256 points, as one does when interpreting a 255-bit discrete log
    // with the result of its scalar multiplication against a fixed generator, the lengths of the
    // yx/x coefficients shouldn't supersede the following bounds
    assert!((divisor.yx_coefficients.first().unwrap_or(&vec![]).len()) <= 126);
    assert!((divisor.x_coefficients.len() - 1) <= 127);
    assert!(
      (1 + divisor.yx_coefficients.first().unwrap_or(&vec![]).len() +
        (divisor.x_coefficients.len() - 1) +
        1) <=
        255
    );

    // Decide challgenges
    let c0 = C::random(&mut OsRng);
    let c1 = C::random(&mut OsRng);
    let c2 = -(c0 + c1);
    let (slope, intercept) = crate::slope_intercept::<C>(c0, c1);

    // Perform the Logarithmic derivative check
    {
      let dx_over_dz = {
        let dx = Poly {
          y_coefficients: vec![],
          yx_coefficients: vec![],
          x_coefficients: vec![C::FieldElement::ZERO, C::FieldElement::from(3)],
          zero_coefficient: C::a(),
        };

        let dy = Poly {
          y_coefficients: vec![C::FieldElement::from(2)],
          yx_coefficients: vec![],
          x_coefficients: vec![],
          zero_coefficient: C::FieldElement::ZERO,
        };

        let dz = (dy.clone() * -slope) + &dx;

        // We want dx/dz, and dz/dx is equal to dy/dx - slope
        // Sagemath claims this, dy / dz, is the proper inverse
        (dy, dz)
      };

      {
        let sanity_eval = |c| {
          let (x, y) = C::to_xy(c).unwrap();
          dx_over_dz.0.eval(x, y) * dx_over_dz.1.eval(x, y).invert().unwrap()
        };
        let sanity = sanity_eval(c0) + sanity_eval(c1) + sanity_eval(c2);
        // This verifies the dx/dz polynomial is correct
        assert_eq!(sanity, C::FieldElement::ZERO);
      }

      // Logarithmic derivative check
      let test = |divisor: Poly<_>| {
        let (dx, dy) = divisor.differentiate();

        let lhs = |c| {
          let (x, y) = C::to_xy(c).unwrap();

          let n_0 = (C::FieldElement::from(3) * (x * x)) + C::a();
          let d_0 = (C::FieldElement::from(2) * y).invert().unwrap();
          let p_0_n_0 = n_0 * d_0;

          let n_1 = dy.eval(x, y);
          let first = p_0_n_0 * n_1;

          let second = dx.eval(x, y);

          let d_1 = divisor.eval(x, y);

          let fraction_1_n = first + second;
          let fraction_1_d = d_1;

          let fraction_2_n = dx_over_dz.0.eval(x, y);
          let fraction_2_d = dx_over_dz.1.eval(x, y);

          fraction_1_n * fraction_2_n * (fraction_1_d * fraction_2_d).invert().unwrap()
        };
        let lhs = lhs(c0) + lhs(c1) + lhs(c2);

        let mut rhs = C::FieldElement::ZERO;
        for point in &points {
          let (x, y) = <C as DivisorCurve>::to_xy(*point).unwrap();
          rhs += (intercept - (y - (slope * x))).invert().unwrap();
        }

        assert_eq!(lhs, rhs);
      };
      // Test the divisor and the divisor with a normalized x coefficient
      test(divisor.clone());
      test(divisor.normalize_x_coefficient());
    }
  }
}

fn test_same_point<C: DivisorCurve>() {
  let mut points = vec![C::random(&mut OsRng)];
  points.push(points[0]);
  points.push(-points.iter().sum::<C>());
  check_divisor(points);
}

fn test_subset_sum_to_infinity<C: DivisorCurve>() {
  // Internally, a binary tree algorithm is used
  // This executes the first pass to end up with [0, 0] for further reductions
  {
    let mut points = vec![C::random(&mut OsRng)];
    points.push(-points[0]);

    let next = C::random(&mut OsRng);
    points.push(next);
    points.push(-next);
    check_divisor(points);
  }

  // This executes the first pass to end up with [0, X, -X, 0]
  {
    let mut points = vec![C::random(&mut OsRng)];
    points.push(-points[0]);

    let x_1 = C::random(&mut OsRng);
    let x_2 = C::random(&mut OsRng);
    points.push(x_1);
    points.push(x_2);

    points.push(-x_1);
    points.push(-x_2);

    let next = C::random(&mut OsRng);
    points.push(next);
    points.push(-next);
    check_divisor(points);
  }
}

#[test]
fn test_divisor_pallas() {
  test_same_point::<Ep>();
  test_subset_sum_to_infinity::<Ep>();
  test_divisor::<Ep>();
}

#[test]
fn test_divisor_vesta() {
  test_same_point::<Eq>();
  test_subset_sum_to_infinity::<Eq>();
  test_divisor::<Eq>();
}

/// Does FCMP++'s additive inverse padding create witnesses equivalent to Silver Bullet's identity padding?
#[test]
fn test_3_vs_4_inputs() {
  // Test if odd-length inputs (which trigger additive inverse padding) produce witnesses quivalent to Silver Bullet's identity padding approach.  
  // If Line(C,-C) ≡ Line(C,0), then both padding methods create mathematically equivalent witnesses.
  let a = Ep::random(&mut OsRng);
  let b = Ep::random(&mut OsRng);
  let c = -(a + b);  // Force sum to identity.
  let three_points = vec![a, b, c];
  
  let result_3 = new_divisor::<Ep>(&three_points);
  
  // Verify witness passes FCMP++ verification equations.
  if result_3.is_some() {
    check_divisor(three_points.clone());
    
    // Test core equivalence: Does FCMP++'s Line(C,-C) equal Silver Bullet's Line(C,0)?
    // If true: both padding methods produce equivalent witnesses.
    // If false: padding methods create fundamentally different mathematical structures.
    let line_c_neg_c = crate::line::<Ep>(c, -c);
    let silver_bullet_line = crate::line::<Ep>(c, Ep::identity());
    
    let lines_equivalent = line_c_neg_c.y_coefficients   == silver_bullet_line.y_coefficients &&
                           line_c_neg_c.x_coefficients   == silver_bullet_line.x_coefficients &&
                           line_c_neg_c.zero_coefficient == silver_bullet_line.zero_coefficient;
    
    println!("Line(C,-C) ≡ Line(C,0): {}", lines_equivalent);
  }
  
  // Test even-length inputs (no padding required) as control case.
  // Even-length avoids the padding equivalence issue entirely.
  let d = Ep::random(&mut OsRng);
  let e = Ep::random(&mut OsRng);
  let f = Ep::random(&mut OsRng);
  let g = -(d + e + f);
  let four_points = vec![d, e, f, g];
  
  let result_4 = new_divisor::<Ep>(&four_points);
  
  if result_4.is_some() {
    check_divisor(four_points.clone());
  }
  
  // Both should succeed, but they work through different mechanisms.
  assert!(result_3.is_some(), "3 points should succeed");
  assert!(result_4.is_some(), "4 points should succeed");
}

/// Does the i=2 case produce a vertical line instead of a tangent?
#[test]
fn test_i2_edge_case() {
  // i=2: points [A, B, -(A+B)].
  let a = Ep::random(&mut OsRng);
  let b = Ep::random(&mut OsRng); 
  let c = -(a + b);
  let points = vec![a, b, c];
  
  let witness_result = new_divisor::<Ep>(&points);
  
  if let Some(_) = witness_result {
    check_divisor(points.clone());
    
    // In the pairing algorithm, unpaired point C gets paired with -C.
    let line_c_neg_c = crate::line::<Ep>(c, -c);
    
    // Verify this produces a vertical line (x - constant).
    let is_vertical = line_c_neg_c.y_coefficients == vec![<Ep as DivisorCurve>::FieldElement::ZERO] &&
                      line_c_neg_c.x_coefficients == vec![<Ep as DivisorCurve>::FieldElement::ONE] &&
                      line_c_neg_c.yx_coefficients.is_empty();
    
    // Compare to tangent at C.
    let tangent_at_c = crate::line::<Ep>(c, c);
    let equals_tangent = line_c_neg_c.y_coefficients == tangent_at_c.y_coefficients &&
                         line_c_neg_c.x_coefficients == tangent_at_c.x_coefficients &&
                         line_c_neg_c.zero_coefficient == tangent_at_c.zero_coefficient;
    
    // Line(C, -C) should be vertical, not tangent.
    assert!(is_vertical);
    assert!(!equals_tangent);
  }
  
  assert!(witness_result.is_some());
}

#[test]
fn test_divisor_ed25519() {
  // Since we're implementing Wei25519 ourselves, check the isomorphism works as expected
  {
    let incomplete_add = |p1, p2| {
      let (x1, y1) = EdwardsPoint::to_xy(p1).unwrap();
      let (x2, y2) = EdwardsPoint::to_xy(p2).unwrap();

      // mmadd-1998-cmo
      let u = y2 - y1;
      let uu = u * u;
      let v = x2 - x1;
      let vv = v * v;
      let vvv = v * vv;
      let R = vv * x1;
      let A = uu - vvv - R.double();
      let x3 = v * A;
      let y3 = (u * (R - A)) - (vvv * y1);
      let z3 = vvv;

      // Normalize from XYZ to XY
      let x3 = x3 * z3.invert().unwrap();
      let y3 = y3 * z3.invert().unwrap();

      // Edwards addition -> Wei25519 coordinates should be equivalent to Wei25519 addition
      assert_eq!(EdwardsPoint::to_xy(p1 + p2).unwrap(), (x3, y3));
    };

    for _ in 0 .. 256 {
      incomplete_add(EdwardsPoint::random(&mut OsRng), EdwardsPoint::random(&mut OsRng));
    }
  }

  test_same_point::<EdwardsPoint>();
  test_subset_sum_to_infinity::<EdwardsPoint>();
  test_divisor::<EdwardsPoint>();
}
