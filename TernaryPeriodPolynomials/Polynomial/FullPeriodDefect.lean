module

public import TernaryPeriodPolynomials.Polynomial.AdditivePolynomial
public import TernaryPeriodPolynomials.Polynomial.PeriodSubstitution

@[expose] public section


/-! # Elimination of the binary rotation defect

A normalized norm-zero binary polynomial whose rotation defect is additive in the
first variable satisfies the full two-term period relation. The argument is over
an arbitrary commutative rational algebra and uses no eigenspace decomposition.
-/

noncomputable section
open MvPolynomial

namespace TernaryPoly.Paper
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The rotation defect before the two-term relation has been proved. -/
def reflectionDefect (q : Binary R) : Binary R := q + binaryEval q (X 1) (-X 0)

/-- Axis normalization and the norm eliminate an additive rotation defect. -/
theorem two_term_of_defect_doubling (q : Binary R)
    (hx : bind₁ (![0, X 1] : Fin 2 → Binary R) q = 0)
    (hy : bind₁ (![X 0, 0] : Fin 2 → Binary R) q = 0)
    (hn : q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0)
    (hd : bind₁ ![2 * X 0, X 1] (reflectionDefect q) = 2 * reflectionDefect q) :
    q + bind₁ ![-X 1, X 0] q = 0 := by
  let A (b : Binary R) : Binary R := binaryEval (reflectionDefect q) 1 b
  have hlin := eq_X_mul_axis_of_doubling (reflectionDefect q) hd
  have hH (a b : Binary R) : binaryEval q a b + binaryEval q b (-a) = a * A b := by
    have h := congrArg (fun p : Binary R => binaryEval p a b) hlin
    simpa [reflectionDefect, A, binaryEval, bind₁_bind₁, bind_vec2] using h
  have hcycle (a b : Binary R) :
      a * A b - b * A (-a) - a * A (-b) + b * A a = 0 := by
    have h₁ := hH a b
    have h₂ := hH b (-a)
    have h₃ := hH (-a) (-b)
    have h₄ := hH (-b) a
    simp only [neg_neg] at h₂ h₃ h₄
    linear_combination -h₁ + h₂ - h₃ + h₄
  have htwo : IsUnit (2 : Binary R) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map
        (algebraMap ℚ (Binary R))
  have hA1 : A 1 = A (-1) := by
    have h : (2 : Binary R) * (A 1 - A (-1)) = 0 := by
      linear_combination hcycle 1 1
    exact sub_eq_zero.mp (htwo.mul_right_eq_zero.mp h)
  have hAe (b : Binary R) : A (-b) = A b := by
    have h := hcycle 1 b
    rw [hA1] at h
    linear_combination -h
  have hodd (a b : Binary R) :
      binaryEval q a b - binaryEval q (-a) (-b) = a * A b - b * A a := by
    have h₁ := hH a b
    have h₂ := hH b (-a)
    simp only [hAe] at h₂
    linear_combination h₁ - h₂
  have hnorm (a b : Binary R) :
      binaryEval q a b + binaryEval q (-b) (a-b) + binaryEval q (b-a) (-a) = 0 := by
    have h := congrArg (fun p : Binary R => binaryEval p a b) hn
    simpa [binaryEval, bind₁_bind₁, bind_vec2] using h
  have hnormodd (a b : Binary R) :
      a * A b - b * A a - b * A (a-b) - (a-b) * A b +
        (b-a) * A a + a * A (a-b) = 0 := by
    have h₁ := hnorm a b
    have h₂ := hnorm (-a) (-b)
    have h₃ := hodd a b
    have h₄ := hodd (-b) (a-b)
    have h₅ := hodd (b-a) (-a)
    have hab : -a - -b = b-a := by ring
    have hba : -b - -a = a-b := by ring
    have hab' : -(a-b) = b-a := by ring
    have hba' : -(b-a) = a-b := by ring
    simp only [neg_neg, hab, hba, hab', hba', hAe] at h₂ h₄ h₅
    have he : A (b-a) = A (a-b) := by rw [← hab', hAe]
    rw [he] at h₅
    linear_combination h₁ - h₂ - h₃ - h₄ - h₅
  have hdouble (b : Binary R) : (2*b) * A (2*b) = 2 * (b * A b) := by
    have h := hnormodd (2*b) b
    have h₁ : 2*b-b=b := by ring
    have h₂ : b-2*b=-b := by ring
    simp only [h₁, h₂] at h
    linear_combination -h
  let g : Binary R := X 0 * A (X 0)
  have hg : bind₁ ![2 * X 0, X 1] g = 2 * g := by
    simpa [g, A, binaryEval, bind₁_bind₁, bind_vec2] using hdouble (X 0)
  have hglinear := eq_X_mul_axis_of_doubling g hg
  have hfactor : (X 0 : Binary R) * A (X 0) = X 0 * A 1 := by
    simpa [g, A, binaryEval, bind₁_bind₁, bind_vec2] using hglinear
  have hconstant : A (X 0) = A 1 := (isRegular_X (n := (0 : Fin 2))).left hfactor
  have hAconstant (b : Binary R) : A b = A 1 := by
    have h := congrArg (fun p : Binary R => binaryEval p b 0) hconstant
    simpa [A, binaryEval, bind₁_bind₁, bind_vec2] using h
  have haxisx (b : Binary R) : binaryEval q 0 b = 0 := by
    have h := congrArg (fun p : Binary R => binaryEval p 0 b) hx
    simpa [binaryEval, bind₁_bind₁, bind_vec2] using h
  have haxisy (a : Binary R) : binaryEval q a 0 = 0 := by
    have h := congrArg (fun p : Binary R => binaryEval p a 0) hy
    simpa [binaryEval, bind₁_bind₁, bind_vec2] using h
  have hA0 : A 0 = 0 := by
    have h := hH 1 0
    simpa only [haxisx, haxisy, add_zero, one_mul] using h.symm
  have hAz (b : Binary R) : A b = 0 := by rw [hAconstant b, ← hAconstant 0, hA0]
  change q + binaryEval q (-X 1) (X 0) = 0
  have h := hH (-X 1) (X 0)
  simpa only [hAz, mul_zero, neg_neg, binaryEval_X, add_comm] using h

end TernaryPoly.Paper
