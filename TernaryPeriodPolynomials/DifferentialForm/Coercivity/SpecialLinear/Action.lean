module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Cartan
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.Derivation.Lie

@[expose] public section

/-! The infinitesimal inverse-substitution action on real ternary polynomials. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

abbrev Poly := MvPolynomial (Fin 3) ℝ

/-- The derivative of the convention `f(g⁻¹ x)`. -/
def infinitesimal (A : Mat) : Derivation ℝ Poly Poly :=
  mkDerivation ℝ (fun i => -∑ j, A i j • X j)

@[simp] theorem infinitesimal_X (A : Mat) (i : Fin 3) :
    infinitesimal A (X i) = -∑ j, A i j • X j := mkDerivation_X _ _ _

theorem infinitesimal_add (A B : Mat) : infinitesimal (A + B) =
    infinitesimal A + infinitesimal B := by
  apply derivation_ext
  intro i
  simp [add_smul, Finset.sum_add_distrib, add_comm]

theorem infinitesimal_smul (c : ℝ) (A : Mat) : infinitesimal (c • A) =
    c • infinitesimal A := by
  apply derivation_ext
  intro i
  simp [smul_smul, Finset.smul_sum]

theorem infinitesimal_commutator (A B : Mat) :
    infinitesimal (A * B - B * A) = ⁅infinitesimal A, infinitesimal B⁆ := by
  apply derivation_ext
  intro i
  simp [Derivation.commutator_apply, Matrix.mul_apply, Fin.sum_univ_succ,
    sub_smul, add_smul, smul_add, smul_smul]
  module

theorem infinitesimal_eq_sum (A : Mat) : infinitesimal A =
    -∑ i : Fin 3, ∑ j : Fin 3, A i j • ((X j : Poly) • pderiv i) := by
  apply derivation_ext
  intro k
  fin_cases k <;> simp [pderiv_X, Fin.sum_univ_succ]

theorem infinitesimal_apply (A : Mat) (f : Poly) :
    infinitesimal A f = -∑ i : Fin 3, ∑ j : Fin 3, A i j • (X j * pderiv i f) := by
  rw [infinitesimal_eq_sum]
  simp [Fin.sum_univ_succ, smul_eq_mul]

theorem infinitesimal_preserves_degree (A : Mat) {n : ℕ} {f : Poly}
    (hf : f.IsHomogeneous n) : (infinitesimal A f).IsHomogeneous n := by
  rw [infinitesimal_apply]
  by_cases hn : n = 0
  · subst n
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hf
    rw [hf]
    simp [isHomogeneous_zero]
  · apply IsHomogeneous.neg
    apply IsHomogeneous.sum
    intro i hi
    apply IsHomogeneous.sum
    intro j hj
    apply (homogeneousSubmodule (Fin 3) ℝ n).smul_mem
    change (X j * pderiv i f).IsHomogeneous n
    have hd : 1 + (n - 1) = n := by omega
    simpa only [hd] using (isHomogeneous_X (i := j) (R := ℝ)).mul (hf.pderiv (i := i))

/-- The actual endomorphism on the homogeneous coefficient space. -/
def homogeneousInfinitesimal (n : ℕ) (A : Mat) :
    homogeneousSubmodule (Fin 3) ℝ n →ₗ[ℝ] homogeneousSubmodule (Fin 3) ℝ n :=
  (infinitesimal A).toLinearMap.restrict (fun _ hf => infinitesimal_preserves_degree A hf)

@[simp] theorem homogeneousInfinitesimal_apply (n : ℕ) (A : Mat)
    (f : homogeneousSubmodule (Fin 3) ℝ n) :
    (homogeneousInfinitesimal n A f : Poly) = infinitesimal A f := rfl

end TernaryPoly.SL3PolynomialCoercivity
