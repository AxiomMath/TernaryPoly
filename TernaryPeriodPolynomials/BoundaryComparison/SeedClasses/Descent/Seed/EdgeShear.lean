module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EichlerCompare
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlusSpecial
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedCusp

@[expose] public section


/-!
# Radical shears and the average of the seed cocycle (Lemma C.3, S4c)

Polynomial calculus for the edge of the seed cocycle: on `ℂ[X, Y, Z]` the radical generator
`D_i = -Z ∂_i` (`shearD`), the finite Taylor expansion of the radical translation
`(X, Y, Z) ↦ (X - δ_{i0} Z, Y - δ_{i1} Z, Z)` (`shift_taylor`), and the identity
`avg(D_i)((n+1)⁻¹ ∂_i P) = -(n+1)⁻¹ ((S_{e_i} - 1) P)/Z` for `P` homogeneous of degree `n + 1`
(`avg_pair`), where `avg` is the library's nilpotent average (`nilpotentExponentialAverage`) used to
define the coordinates of the radical cohomology (`upperRadicalCocyclePair`).

Paper: Lemma C.3 (`ar:lem:seed`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3

/-- The shear `q ↦ -Z ∂_i q` (the `i`-th upper radical generator on polynomials). -/
def shearD (i : Fin 2) : Module.End ℂ Poly :=
  (-1 : ℂ) • polynomialShearDerivation i.castSucc 2

theorem shearD_apply (i : Fin 2) (q : Poly) :
    shearD i q = -(X 2 * pderiv i.castSucc q) := by
  simp [shearD, polynomialShearDerivation]

theorem shearD_Z (i : Fin 2) (q : Poly) : shearD i (X 2 * q) = X 2 * shearD i q := by
  have h2 : pderiv i.castSucc (X (2 : Fin 3) : Poly) = 0 := by fin_cases i <;> simp
  rw [shearD_apply, shearD_apply, Derivation.leibniz, h2]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

theorem shearD_pow_Z (i : Fin 2) (j : ℕ) (q : Poly) :
    (shearD i ^ j) (X 2 * q) = X 2 * (shearD i ^ j) q := by
  induction j generalizing q with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, shearD_Z, ih]

/-- The substitution `(X, Y, Z) ↦ (X - w₀ Z, Y - w₁ Z, Z)`. -/
def shiftSub (w : Fin 2 → ℝ) : Fin 3 → Poly :=
  ![X 0 - C (w 0 : ℂ) * X 2, X 1 - C (w 1 : ℂ) * X 2, X 2]

/-- The unit shift in direction `i`. -/
def unitShift (i : Fin 2) : Fin 3 → Poly :=
  fun idx => X idx + if idx = i.castSucc then C (-1 : ℂ) * X 2 else 0

theorem unitShift_eq (i : Fin 2) :
    unitShift i = shiftSub (fun j => if j = i then (1 : ℝ) else 0) := by
  funext idx
  fin_cases i <;> fin_cases idx <;> simp [unitShift, shiftSub] <;> ring

theorem shift_taylor (i : Fin 2) {d : ℕ} (P : Poly) (hP : P.IsHomogeneous d) :
    bind₁ (unitShift i) P =
      ∑ p ∈ Finset.range (d + 1), (p.factorial : ℚ)⁻¹ • ((shearD i ^ p) P) := by
  have hdist : (2 : Fin 3) ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  have h := shearPolynomialCurve_finite_taylor (degree := d) i.castSucc 2 (-1) hdist
    ⟨P, (mem_homogeneousSubmodule d P).mpr hP⟩
  rw [shearPolynomialCurve_eval_one] at h
  exact h

theorem shearD_pow_succ (i : Fin 2) (p : ℕ) (P : Poly) :
    (shearD i ^ (p + 1)) P = -(X 2 * (shearD i ^ p) (pderiv i.castSucc P)) := by
  rw [pow_succ, Module.End.mul_apply, shearD_apply, show -(X 2 * pderiv i.castSucc P) =
    X 2 * (-(pderiv i.castSucc P)) by ring, shearD_pow_Z, map_neg]
  ring

theorem shift_sub (i : Fin 2) (n : ℕ) (P : Poly) (hP : P.IsHomogeneous (n + 1)) :
    bind₁ (unitShift i) P - P = X 2 *
      -(∑ j ∈ Finset.range (n + 1),
        ((j + 1).factorial : ℚ)⁻¹ • (shearD i ^ j) (pderiv i.castSucc P)) := by
  rw [shift_taylor i P hP, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero, Module.End.one_apply]
  rw [add_sub_cancel_right, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [shearD_pow_succ, smul_neg, mul_smul_comm]

attribute [local instance] complexEndRationalAlgebra

theorem avg_val (n : ℕ) (i : Fin 2) (a : HomogeneousPoly n) :
    (nilpotentExponentialAverage (upperRadicalGenerator n i) (n + 1) a).val =
      ∑ j ∈ Finset.range (n + 1), ((j + 1).factorial : ℚ)⁻¹ • (shearD i ^ j) a.val := by
  unfold nilpotentExponentialAverage
  simp only [LinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ((((((j + 1).factorial : ℚ)⁻¹ : ℚ) : ℂ) • upperRadicalGenerator n i ^ j) a).val = _
  rw [LinearMap.smul_apply, Submodule.coe_smul, Rat.cast_smul_eq_qsmul]
  congr 1
  exact homogeneousShearDerivation_smul_power_coe n i.castSucc 2 (-1) j a

theorem ddiv_X_two_mul (q : Poly) : ddiv (X 2 * q) = q := by
  have h := X_two_mul_ddiv (dvd_mul_right (X 2 : Poly) q)
  exact mul_left_cancel₀ (X_ne_zero 2) h

theorem shearD_pow_C_mul (i : Fin 2) (j : ℕ) (c : ℂ) (q : Poly) :
    (shearD i ^ j) (C c * q) = C c * (shearD i ^ j) q := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]

/-- **The key identity**: the radical-lattice average of `a = (n+1)⁻¹ ∂_i P` is
`-(n+1)⁻¹ (S_{e_i} - 1) P / Z`. -/
theorem avg_pair (n : ℕ) (i : Fin 2) (P : Poly) (hP : P.IsHomogeneous (n + 1))
    (a c : HomogeneousPoly n) (ha : a.val = C (((n : ℂ) + 1)⁻¹) * pderiv i.castSucc P)
    (hc : c.val = -(C (((n : ℂ) + 1)⁻¹) * ddiv (bind₁ (unitShift i) P - P))) :
    nilpotentExponentialAverage (upperRadicalGenerator n i) (n + 1) a = c := by
  apply Subtype.ext
  rw [avg_val, hc, shift_sub i n P hP, ddiv_X_two_mul, ha, mul_neg, neg_neg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, shearD_pow_C_mul]

end TernaryPeriodPolynomials.Argument.SeedC3S4c
