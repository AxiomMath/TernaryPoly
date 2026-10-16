module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LineEdge
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


/-!
# The Kostant law of the good line from the derivative form

The Kostant law `LineKostantLaw n lam c` of `DetectLineEdge` follows from the elementary derivative
form of the generator values of the radical cocycle, by Euler's identity for homogeneous
polynomials.  The generator values of the genuine line radical at the lattice `3ℤ²` are the
`x₃`-free forms

  `lam e₀ q = κ ∂₁ q`,   `lam e₁ q = -κ ∂₀ q`    (`κ = -3`),

lifted from the binary forms in `x₁, x₂` to ternary forms (`binaryPolynomialLift`); they are killed
by the lower radical generators `-3 X_i ∂₂`, so the inverse average equivalence does not change them
(`lowerRadicalAverageEquiv_symm_of_killed`), and the contraction `X₁ α - X₀ β` is `κ (n + 1) q`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open MvPolynomial GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- A ternary form lifted from a binary polynomial is killed by the lower radical generators. -/
theorem lowerRadicalGenerator_lift_eq_zero (n : ℕ) (i : Fin 2) (v : HomogeneousPoly n)
    (f : Binary.Poly) (hv : v.val = binaryPolynomialLift f) :
    lowerRadicalGenerator n i v = 0 := by
  apply Subtype.ext
  change (-3 : ℂ) • (X i.castSucc * pderiv 2 v.val) = 0
  rw [hv, binaryPolynomialLift_pderiv_third, mul_zero, smul_zero]

/-- The average equivalence fixes the vectors killed by the generator. -/
theorem lowerRadicalAverageEquiv_apply_of_killed (n : ℕ) (i : Fin 2) (v : HomogeneousPoly n)
    (h : lowerRadicalGenerator n i v = 0) : lowerRadicalAverageEquiv n i v = v := by
  change nilpotentExponentialAverage (lowerRadicalGenerator n i) (n + 1) v = v
  have hpow : ∀ k : ℕ, (lowerRadicalGenerator n i ^ (k + 1)) v = 0 := by
    intro k
    rw [pow_succ, Module.End.mul_apply, h, map_zero]
  simp only [nilpotentExponentialAverage, LinearMap.sum_apply, rationalEnd_smul_apply]
  rw [Finset.sum_range_succ']
  simp [hpow]

/-- The inverse average equivalence fixes the vectors killed by the generator. -/
theorem lowerRadicalAverageEquiv_symm_of_killed (n : ℕ) (i : Fin 2) (v : HomogeneousPoly n)
    (h : lowerRadicalGenerator n i v = 0) : (lowerRadicalAverageEquiv n i).symm v = v :=
  (LinearEquiv.symm_apply_eq _).mpr (lowerRadicalAverageEquiv_apply_of_killed n i v h).symm

theorem radicalLatticeGenerator_zero : radicalLatticeGenerator 0 = radicalLatticeFirst :=
  ite_eq_left rfl

theorem radicalLatticeGenerator_one : radicalLatticeGenerator 1 = radicalLatticeSecond :=
  ite_eq_right (by decide)

/-- **The Kostant law from the derivative form.**  If the generator values of `lam` are the
`x₃`-free forms `κ ∂₁ q` and `-κ ∂₀ q`, the law holds with `c = κ (n + 1)`. -/
theorem lineKostantLaw_of_derivative {n : ℕ} {lam : RadicalLattice → (LineQ n →ₗ[ℂ] LineV n)}
    {κ : ℂ}
    (h0 : ∀ q : LineQ n, (lam radicalLatticeFirst q).val =
      binaryPolynomialLift (κ • pderiv (1 : Fin 2) q.val))
    (h1 : ∀ q : LineQ n, (lam radicalLatticeSecond q).val =
      binaryPolynomialLift (-(κ • pderiv (0 : Fin 2) q.val))) :
    LineKostantLaw n lam (κ * ((n + 1 : ℕ) : ℂ)) := by
  intro q
  have hq : q.val.IsHomogeneous (n + 1) := (MvPolynomial.mem_homogeneousSubmodule _ _).mp q.2
  have euler := hq.sum_X_mul_pderiv
  rw [Fin.sum_univ_two] at euler
  have e0 : (lowerRadicalAverageEquiv n 0).symm (lam (radicalLatticeGenerator 0) q) =
      lam radicalLatticeFirst q := by
    rw [radicalLatticeGenerator_zero]
    exact lowerRadicalAverageEquiv_symm_of_killed n 0 _
      (lowerRadicalGenerator_lift_eq_zero n 0 _ _ (h0 q))
  have e1 : (lowerRadicalAverageEquiv n 1).symm (lam (radicalLatticeGenerator 1) q) =
      lam radicalLatticeSecond q := by
    rw [radicalLatticeGenerator_one]
    exact lowerRadicalAverageEquiv_symm_of_killed n 1 _
      (lowerRadicalGenerator_lift_eq_zero n 1 _ _ (h1 q))
  have r0 : binaryPolynomialRestrict (X (0 : Fin 3)) = (X (0 : Fin 2) : Binary.Poly) := by
    simp [binaryPolynomialRestrict_X]
  have r1 : binaryPolynomialRestrict (X (1 : Fin 3)) = (X (1 : Fin 2) : Binary.Poly) := by
    simp [binaryPolynomialRestrict_X]
  have key : (X (1 : Fin 2) : Binary.Poly) * (κ • pderiv (1 : Fin 2) q.val) -
      X (0 : Fin 2) * (-(κ • pderiv (0 : Fin 2) q.val)) =
      κ • (X (0 : Fin 2) * pderiv (0 : Fin 2) q.val +
        X (1 : Fin 2) * pderiv (1 : Fin 2) q.val) := by
    simp only [smul_eq_C_mul]
    ring
  apply Subtype.ext
  change binaryPolynomialRestrict (lowerRadicalContraction
      ((lowerRadicalAverageEquiv n 0).symm (lam (radicalLatticeGenerator 0) q)).val
      ((lowerRadicalAverageEquiv n 1).symm (lam (radicalLatticeGenerator 1) q)).val) =
    ((κ * ((n + 1 : ℕ) : ℂ)) • q).val
  rw [e0, e1, h0 q, h1 q]
  simp only [lowerRadicalContraction, map_sub, map_mul, binaryPolynomialRestrict_lift, r0, r1]
  rw [key, euler, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  try rfl

end TernaryPeriodPolynomials.SourceConstruction
