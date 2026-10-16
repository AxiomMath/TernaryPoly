module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneJoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Quotient

@[expose] public section


/-!
# The level-three joint eigenspace is parabolic, and transfer along an injective equivariant map

Two ingredients of the bound `dim levelJoint ≤ 2`:

* `levelJoint_le_parabolic`: if the pair character is within `3/4` of `1` at `T_2`
  (`‖c(T_2) - 1‖ ≤ 3/4`, true for the pair character of a nonzero associate pair with trivial
  character and `n ≥ 3`), the `T_2`-eigenvalue `2^{n+2}(c(T_2) - 1)` of `levelJoint` has modulus
  `≤ (3/4) 2^{n+2} < 2 (2^{n+2} - 1) = |q_∞|, |q_0|` lower bound, so by
  `mem_parabolicH1_of_mem_maxGenEigenspace_of_ne` every element is parabolic.
* `exists_submodule_of_injective_equivariant`: an injective linear map `R : S → V` intertwining
  families of operators `A i` and `B i` pulls the joint generalized eigenspace `J ≤ range R` of the
  `B i` back to an isomorphic subspace of the joint generalized eigenspace of the `A i`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.TwoGenerator

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneBound

open GeneralEisenstein
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction (intertwine_sub_pow)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneJoint (levelJoint)
open TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryEisenstein (two)

/-- **Every element of `levelJoint` is parabolic** when the pair character is within `3/4` of `1`
at `T_2`. -/
theorem levelJoint_le_parabolic (n : ℕ) (hn : 1 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4) :
    levelJoint n c ≤ parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1) := by
  intro x hx
  have h23 : two.val ≠ 3 := by decide
  have hx2 := (Submodule.mem_iInf _).mp hx ⟨two, h23⟩
  have h2 : ((two.val : ℕ) : ℝ) = 2 := by simp [two]
  have hX : (8 : ℝ) ≤ 2 ^ (n + 2) := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hnorm : ‖(c (TpExistence.tp two) - 1) / (((two.val : ℕ) : ℂ) ^ (n + 2))⁻¹‖ ≤
      3 / 4 * 2 ^ (n + 2) := by
    rw [div_inv_eq_mul, norm_mul, norm_pow, Complex.norm_natCast, h2]
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hlt : ‖(c (TpExistence.tp two) - 1) / (((two.val : ℕ) : ℂ) ^ (n + 2))⁻¹‖ <
      ((two.val : ℕ) : ℝ) ^ (-(-1 : ℤ)) * (((two.val : ℕ) : ℝ) ^ (n + 1 + 1) - 1) := by
    rw [h2, neg_neg, zpow_one, show n + 1 + 1 = n + 2 from rfl]
    linarith
  exact LevelThreeBoundaryQuotient.mem_parabolicH1_of_mem_maxGenEigenspace_of_ne (n + 1) (-1)
    two h23 _ (LevelThreeBoundaryQuotient.ne_qInf_of_norm_lt _ hlt)
    (LevelThreeBoundaryQuotient.ne_qZero_of_norm_lt _ hlt) hx2

/-! ### Transfer along an injective equivariant map -/

section Transfer

variable {ι : Type*} {S V : Type*} [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]

/-- **Pullback of a joint generalized eigenspace.** If `R : S → V` is injective and intertwines
`A i` with `B i`, the preimage of `J ≤ range R ⊓ ⨅ i, maxGenEigenspace (B i) (μ i)` lies in
`⨅ i, maxGenEigenspace (A i) (μ i)` and has the same dimension as `J`. -/
theorem finrank_le_of_injective_equivariant (R : S →ₗ[ℂ] V) (hR : Function.Injective R)
    (A : ι → Module.End ℂ S) (B : ι → Module.End ℂ V) (hcomm : ∀ i f, R (A i f) = B i (R f))
    (μ : ι → ℂ) (J : Submodule ℂ V) (hJ : J ≤ ⨅ i, (B i).maxGenEigenspace (μ i))
    (hJR : J ≤ LinearMap.range R) [Module.Finite ℂ S] :
    Module.finrank ℂ J ≤ Module.finrank ℂ (⨅ i, (A i).maxGenEigenspace (μ i) : Submodule ℂ S) := by
  have hle : J.comap R ≤ ⨅ i, (A i).maxGenEigenspace (μ i) := by
    intro f hf
    rw [Submodule.mem_iInf]
    intro i
    have hf' := (Submodule.mem_iInf _).mp (hJ (Submodule.mem_comap.mp hf)) i
    rw [Module.End.mem_maxGenEigenspace] at hf' ⊢
    obtain ⟨k, hk⟩ := hf'
    refine ⟨k, hR ?_⟩
    rw [intertwine_sub_pow R (A i) (B i) (hcomm i) (μ i) k f, hk, map_zero]
  have hmap : (J.comap R).map R = J := Submodule.map_comap_eq_of_le hJR
  have hfin : Module.finrank ℂ (J.comap R) = Module.finrank ℂ J := by
    have e := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective R hR (J.comap R))
    rw [hmap] at e
    exact e
  rw [← hfin]
  exact Submodule.finrank_mono hle

/-- Scaling an operator rescales its generalized eigenvalue. -/
theorem mem_maxGen_of_smul {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Module.End ℂ W)
    (a μ : ℂ) (ha : a ≠ 0) {v : W} (hv : v ∈ (a • T : Module.End ℂ W).maxGenEigenspace μ) :
    v ∈ T.maxGenEigenspace (μ / a) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  have hmul : a * (μ / a) = μ := by field_simp
  have h : (a • T : Module.End ℂ W) - μ • 1 = a • (T - (μ / a) • 1) := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, smul_sub,
      smul_smul, hmul]
  rw [h, smul_pow, LinearMap.smul_apply] at hk
  exact (smul_eq_zero.mp hk).resolve_left (pow_ne_zero k ha)

end Transfer

end TernaryPeriodPolynomials.LevelThree.GoodPlaneBound
