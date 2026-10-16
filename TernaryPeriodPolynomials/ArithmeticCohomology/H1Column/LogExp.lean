module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.H1Column.LogTaylor

@[expose] public section


/-!
# `ρ(U_ij) = exp(-x_j ∂_{x_i})` on `E = Sym^n((ℚ³)*)` (MR-8)

Formalized by Claude Sonnet 5.5.  Paper: "on dual polynomial coefficients, `log ρ(U_ij) = -x_j ∂_{x_i}`".

`unipotentGL i j` is the elementary matrix `U_ij = 1 + E_ij ∈ GL₃(ℤ)`; `rho_unipotent_eq_shear`: its action on `E_n` (the left inverse-substitution representation, determinant exponent `0`) is the shear `x_i ↦ x_i - x_j`.
`lieOpH n i j` is `-x_j ∂_{x_i}` on `E_n`; it is nilpotent (`lieOpH_pow_succ`) and `rho_unipotent_eq_exp`: `ρ(U_ij) = exp(-x_j ∂_{x_i})` as endomorphisms of `E_n`.
-/

open MvPolynomial Finset

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPoly.RadicalCoinvariantAlgebra (shear shear_X)
open TernaryPoly.PolynomialGLAction (HomogeneousPoly integralAction)

variable {i j : Fin 3}

theorem shear_eq_sum (hij : i ≠ j) (f : Poly) (N : ℕ) (hN : ∀ s ∈ f.support, s i < N) :
    shear i j f = ∑ k ∈ range N, ((k.factorial : ℚ)⁻¹) • (lieOp i j ^ k) f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum]
  simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  exact shear_monomial_eq_sum hij s _ N (hN s hs)

theorem lieOp_pow_eq_zero (hij : i ≠ j) (f : Poly) (N : ℕ) (hN : ∀ s ∈ f.support, s i < N) :
    (lieOp i j ^ N) f = 0 := by
  conv_lhs => rw [f.as_sum]
  simp only [map_sum]
  exact Finset.sum_eq_zero fun s hs => lieOp_pow_monomial_eq_zero hij s _ N (hN s hs)

theorem support_lt_of_homogeneous {n : ℕ} {f : Poly} (hf : f.IsHomogeneous n) (s : Fin 3 →₀ ℕ) (hs : s ∈ f.support) :
    s i < n + 1 := by
  have h1 : s.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hs)
  have h2 : s i ≤ s.degree := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.single_le_sum (f := fun k => s k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- The elementary matrix `U_ij = 1 + E_ij ∈ GL₃(ℤ)`. -/
def unipotentGL (i j : Fin 3) (hij : i ≠ j) : Matrix.GeneralLinearGroup (Fin 3) ℤ :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j 1) (by
    rw [Matrix.det_transvection_of_ne i j hij]
    exact isUnit_one)

theorem substitute_inv_unipotent (hij : i ≠ j) :
    TernaryPoly.PolynomialGLAction.substitute
      (((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (unipotentGL i j hij))⁻¹ :
        Matrix.GeneralLinearGroup (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) = shear i j := by
  have hU : (((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (unipotentGL i j hij) :
      Matrix.GeneralLinearGroup (Fin 3) ℚ)) : Matrix (Fin 3) (Fin 3) ℚ) = Matrix.transvection i j 1 := by
    ext a b
    simp [unipotentGL, Matrix.transvection, Matrix.single_apply, Matrix.one_apply]
  have hinv : (((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (unipotentGL i j hij))⁻¹ :
      Matrix.GeneralLinearGroup (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) = Matrix.transvection i j (-1) := by
    rw [Matrix.coe_units_inv, hU]
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.transvection_mul_transvection_same i j hij]
    simp
  rw [hinv]
  apply MvPolynomial.algHom_ext
  intro k
  rw [TernaryPoly.PolynomialGLAction.substitute_X, shear_X]
  simp only [TernaryPoly.PolynomialGLAction.linearForm, Matrix.transvection, Matrix.single_apply, Matrix.add_apply,
    Matrix.one_apply, add_mul, Finset.sum_add_distrib, map_add]
  have h1 : ∑ x, C (if k = x then (1 : ℚ) else 0) * (X x : Poly) = X k := by
    simp [apply_ite C, ite_mul]
  have h2 : ∑ x, C (if i = k ∧ j = x then (-1 : ℚ) else 0) * (X x : Poly) = if k = i then -X j else 0 := by
    by_cases hk : k = i
    · subst hk
      simp [apply_ite C, ite_mul]
    · have : i ≠ k := fun h => hk h.symm
      simp [hk, this]
  rw [h1, h2]
  by_cases hk : k = i
  · simp [hk, sub_eq_add_neg]
  · simp [hk]

/-- The action of `U_ij` on `E_n` (left inverse-substitution representation, determinant exponent `0`) is the shear `x_i ↦ x_i - x_j`. -/
theorem rho_unipotent_eq_shear (hij : i ≠ j) (n : ℕ) (f : HomogeneousPoly n) :
    ((integralAction n 0 (unipotentGL i j hij) f : HomogeneousPoly n) : Poly) = shear i j f := by
  rw [TernaryPoly.PolynomialGLAction.integralAction_coe, TernaryPoly.PolynomialGLAction.action_apply,
    substitute_inv_unipotent hij]
  simp [TernaryPoly.PolynomialGLAction.determinantCharacter]

theorem lieOp_homogeneous {n : ℕ} {f : Poly} (hf : f.IsHomogeneous n) : (lieOp i j f).IsHomogeneous n := by
  rcases n with _ | n
  · by_cases h0 : f = 0
    · simp only [h0, map_zero]; exact isHomogeneous_zero _ _ _
    · have h1 := hf.totalDegree h0
      have h2 := (totalDegree_eq_zero_iff_eq_C).mp h1
      rw [lieOp_apply, h2, pderiv_C]
      simp only [mul_zero]; exact isHomogeneous_zero _ _ _
  · have h1 := MvPolynomial.IsHomogeneous.pderiv (i := i) hf
    simp only [Nat.add_sub_cancel] at h1
    rw [lieOp_apply]
    have := ((isHomogeneous_X ℚ j).neg).mul h1
    rwa [add_comm] at this

/-- `-x_j ∂_{x_i}` as an endomorphism of `E_n`. -/
def lieOpH (n : ℕ) (i j : Fin 3) : Module.End ℚ (HomogeneousPoly n) where
  toFun f := ⟨lieOp i j f.1, lieOp_homogeneous f.property⟩
  map_add' f g := Subtype.ext (map_add (lieOp i j) f.1 g.1)
  map_smul' c f := Subtype.ext (map_smul (lieOp i j) c f.1)

theorem lieOpH_pow_coe (n k : ℕ) (f : HomogeneousPoly n) :
    (((lieOpH n i j ^ k) f : HomogeneousPoly n) : Poly) = (lieOp i j ^ k) f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ih]
    rfl

/-- `-x_j ∂_{x_i}` is nilpotent on `E_n`: its `(n+1)`-st power vanishes. -/
theorem lieOpH_pow_succ (hij : i ≠ j) (n : ℕ) : lieOpH n i j ^ (n + 1) = 0 := by
  ext f : 1
  apply Subtype.ext
  rw [lieOpH_pow_coe]
  exact lieOp_pow_eq_zero hij f (n + 1) (support_lt_of_homogeneous f.property)

theorem isNilpotent_lieOpH (hij : i ≠ j) (n : ℕ) : IsNilpotent (lieOpH n i j) := ⟨n + 1, lieOpH_pow_succ hij n⟩

/-- **`ρ(U_ij) = exp(-x_j ∂_{x_i})`** on `E_n = Sym^n((ℚ³)*)`: the action of the elementary matrix `U_ij` is the exponential of the nilpotent operator `-x_j ∂_{x_i}`. -/
theorem rho_unipotent_eq_exp (hij : i ≠ j) (n : ℕ) :
    integralAction n 0 (unipotentGL i j hij) = IsNilpotent.exp (lieOpH n i j) := by
  rw [IsNilpotent.exp_eq_sum (lieOpH_pow_succ hij n)]
  ext f : 1
  apply Subtype.ext
  rw [rho_unipotent_eq_shear hij n f, shear_eq_sum hij f (n + 1) (support_lt_of_homogeneous f.property)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, lieOpH_pow_coe]

end TernaryPeriodPolynomials.Argument.Identities
