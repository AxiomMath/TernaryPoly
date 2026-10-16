module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Basic

@[expose] public section


/-! Differential identities for the coefficient compact and full Casimir operators. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

def rotation (i j : Fin 3) (p : Poly) : Poly := X i * pderiv j p - X j * pderiv i p

def eulerOperator (p : Poly) : Poly := ∑ i : Fin 3, X i * pderiv i p

def radialSquared : Poly := ∑ i : Fin 3, (X i)^2

def polynomialLaplacian (p : Poly) : Poly := ∑ i : Fin 3, pderiv i (pderiv i p)

def compactCoefficientCasimir (p : Poly) : Poly :=
  -(1/2 : ℝ) • (rotation 0 1 (rotation 0 1 p) + rotation 0 2 (rotation 0 2 p) +
    rotation 1 2 (rotation 1 2 p))

def fullCoefficientCasimir (p : Poly) : Poly :=
  (∑ i : Fin 5, tangentWeight i •
    infinitesimal (tangentFrame i) (infinitesimal (tangentFrame i) p)) +
      compactCoefficientCasimir p

theorem pderiv_commute (i j : Fin 3) (p : Poly) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  by_cases hij : i = j
  · subst j; rfl
  · ext d
    simp [coeff_pderiv, hij, Ne.symm hij, add_comm, add_left_comm, mul_comm, mul_left_comm]

theorem eulerOperator_homogeneous {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    eulerOperator p = (n : ℝ) • p := by
  simpa only [eulerOperator, Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using hp.sum_X_mul_pderiv

theorem compactCoefficientCasimir_differential (p : Poly) :
    compactCoefficientCasimir p = (1/2 : ℝ) •
      (eulerOperator (eulerOperator p) + eulerOperator p - radialSquared * polynomialLaplacian p) := by
  simp [compactCoefficientCasimir, rotation, eulerOperator, radialSquared, polynomialLaplacian,
    Fin.sum_univ_succ, map_add, map_sub, mul_add, add_mul, mul_sub, pow_two]
  simp only [pderiv_commute 1 0, pderiv_commute 2 0, pderiv_commute 2 1, smul_eq_C_mul]
  ring

theorem eulerOperator_smul (c : ℝ) (p : Poly) :
    eulerOperator (c • p) = c • eulerOperator p := by
  simp [eulerOperator, Derivation.map_smul, Finset.smul_sum]

theorem compactCoefficientCasimir_homogeneous {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    compactCoefficientCasimir p = (1/2 : ℝ) •
      (((n : ℝ) * (n + 1)) • p - radialSquared * polynomialLaplacian p) := by
  rw [compactCoefficientCasimir_differential, eulerOperator_homogeneous hp,
    eulerOperator_smul, eulerOperator_homogeneous hp]
  module

theorem factorialPairing_radialSquared (p q : Poly) :
    factorialPairing (radialSquared * p) q = factorialPairing p (polynomialLaplacian q) := by
  simp only [radialSquared, polynomialLaplacian, Finset.sum_mul, map_sum,
    LinearMap.sum_apply, pow_two, mul_assoc, factorialPairing_X_mul]

theorem compactCoefficientCasimir_upper {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    factorialPairing (compactCoefficientCasimir p) p ≤
      ((n : ℝ) * (n + 1) / 2) * factorialPairing p p := by
  rw [compactCoefficientCasimir_homogeneous hp]
  simp only [map_smul, LinearMap.smul_apply, map_sub, LinearMap.sub_apply,
    factorialPairing_radialSquared, smul_eq_mul]
  have h := factorialPairing_self_nonneg (polynomialLaplacian p)
  nlinarith

theorem fullCoefficientCasimir_differential (p : Poly) :
    fullCoefficientCasimir p = (2/3 : ℝ) • eulerOperator (eulerOperator p) +
      (2 : ℝ) • eulerOperator p := by
  apply smul_right_injective Poly (by norm_num : (6 : ℝ) ≠ 0)
  norm_num [fullCoefficientCasimir, compactCoefficientCasimir, tangentWeight,
    Fin.sum_univ_succ, smul_add, smul_smul]
  simp [rotation, eulerOperator, tangentFrame, infinitesimal_apply, Fin.sum_univ_succ,
    smul_eq_C_mul, mul_add, mul_sub]
  simp only [pderiv_commute 1 0, pderiv_commute 2 0, pderiv_commute 2 1, map_ofNat]
  ring

theorem fullCoefficientCasimir_homogeneous {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    fullCoefficientCasimir p = (2 * (n : ℝ) * (n + 3) / 3) • p := by
  rw [fullCoefficientCasimir_differential, eulerOperator_homogeneous hp,
    eulerOperator_smul, eulerOperator_homogeneous hp]
  module

/-- Orthogonal skew frame, each of squared length two for `-tr(AB)`. -/
def skewFrame : Fin 3 → Mat := ![
  !![0, 1, 0; -1, 0, 0; 0, 0, 0],
  !![0, 0, 1; 0, 0, 0; -1, 0, 0],
  !![0, 0, 0; 0, 0, 1; 0, -1, 0]]

theorem skewFrame_transpose (i : Fin 3) : (skewFrame i).transpose = -skewFrame i := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [skewFrame]

theorem infinitesimal_skewFrame (i : Fin 3) (p : Poly) :
    infinitesimal (skewFrame i) p = ![rotation 0 1 p, rotation 0 2 p, rotation 1 2 p] i := by
  fin_cases i <;> simp [skewFrame, infinitesimal_apply, rotation, Fin.sum_univ_succ] <;> abel

theorem compactCoefficientCasimir_eq_sum (p : Poly) :
    compactCoefficientCasimir p = -(1/2 : ℝ) • ∑ i : Fin 3,
      infinitesimal (skewFrame i) (infinitesimal (skewFrame i) p) := by
  simp [compactCoefficientCasimir, Fin.sum_univ_succ, infinitesimal_skewFrame, add_assoc]

theorem compactCoefficientCasimir_energy (p : Poly) :
    factorialPairing (compactCoefficientCasimir p) p = (1/2 : ℝ) * ∑ i : Fin 3,
      factorialPairing (infinitesimal (skewFrame i) p) (infinitesimal (skewFrame i) p) := by
  rw [compactCoefficientCasimir_eq_sum]
  simp only [map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply, smul_eq_mul]
  have hi (i : Fin 3) :
      factorialPairing (infinitesimal (skewFrame i) (infinitesimal (skewFrame i) p)) p =
        -factorialPairing (infinitesimal (skewFrame i) p) (infinitesimal (skewFrame i) p) := by
    rw [infinitesimal_skew_adjoint _ (skewFrame_transpose i)]
  simp_rw [hi, Finset.sum_neg_distrib]
  ring

theorem compactCoefficientCasimir_nonneg (p : Poly) :
    0 ≤ factorialPairing (compactCoefficientCasimir p) p := by
  rw [compactCoefficientCasimir_energy]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => factorialPairing_self_nonneg _))

end TernaryPoly.SL3PolynomialCoercivity
