module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationPlaneLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.HeckeImage

@[expose] public section


/-!
# Level-three vectors of a cuspidal representation

The level `K₁(3)·GL₂(ℤ̂^{(3)})` is `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}`
(`Separation.PlaneLeviLevel`). `levelThreeValues σ` is the closed subspace of its fixed
vectors, and `levelThreeClassicalVectors σ halfWeight` the smooth level-three vectors of rotation
weight `2 * halfWeight` whose scalar realization is holomorphic; these are the level-three analogues
of `cuspSphericalValues` and `cuspClassicalVectors`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.MultiplicityOne

open TernaryPeriodPolynomials.Separation (PlaneLeviLevel PlaneLevelVector)

/-- Vectors fixed by the level `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}`. -/
def levelThreeValues (σ : CuspidalRepresentation) : Submodule ℂ σ.H where
  carrier := {v | ∀ k : GeneralLinearGroup (Fin 2) IntegralAdeles, PlaneLeviLevel k →
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) v = v}
  zero_mem' := by simp
  add_mem' hv hw := by
    intro k hk
    rw [map_add, hv k hk, hw k hk]
  smul_mem' c v hv := by
    intro k hk
    rw [map_smul, hv k hk]

theorem mem_levelThreeValues {σ : CuspidalRepresentation} {v : σ.H} :
    v ∈ levelThreeValues σ ↔ ∀ k : GeneralLinearGroup (Fin 2) IntegralAdeles, PlaneLeviLevel k →
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) v = v :=
  Iff.rfl

theorem cuspSphericalValues_le_levelThreeValues (σ : CuspidalRepresentation) :
    cuspSphericalValues σ ≤ levelThreeValues σ :=
  fun _ hv k _ => hv k

theorem planeLevelVector_true_iff (σ : CuspidalRepresentation) :
    PlaneLevelVector σ true ↔ ∃ v : σ.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues σ := by
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, fun k hk => h k fun _ => hk⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, fun k hk => h k (hk rfl)⟩

/-- Smooth level-three vectors of rotation weight `2 * halfWeight` with holomorphic scalar
realization. -/
def levelThreeClassicalVectors (σ : CuspidalRepresentation) (halfWeight : ℤ) :
    Submodule ℂ σ.smooth where
  carrier := {v | v.val ∈ levelThreeValues σ ∧
    (∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) ∧
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (cuspScalarWeightedLinear σ halfWeight 1 v)}
  zero_mem' := by
    refine ⟨(levelThreeValues σ).zero_mem, ?_, ?_⟩
    · intro angle
      simp
    · rw [map_zero]
      exact mdifferentiable_const
  add_mem' first second := by
    refine ⟨(levelThreeValues σ).add_mem first.1 second.1, ?_, ?_⟩
    · intro angle
      simp only [Submodule.coe_add, map_add, first.2.1 angle, second.2.1 angle, smul_add]
    · rw [map_add]
      exact first.2.2.add second.2.2
  smul_mem' scalar v member := by
    refine ⟨(levelThreeValues σ).smul_mem scalar member.1, ?_, ?_⟩
    · intro angle
      simp only [Submodule.coe_smul, map_smul, member.2.1 angle]
      exact smul_comm _ _ _
    · rw [map_smul]
      exact member.2.2.const_smul scalar

theorem cuspClassicalVectors_le_levelThreeClassicalVectors (σ : CuspidalRepresentation)
    (halfWeight : ℤ) :
    cuspClassicalVectors σ halfWeight ≤ levelThreeClassicalVectors σ halfWeight :=
  fun _ hv => ⟨cuspSphericalValues_le_levelThreeValues σ hv.1, hv.2.1, hv.2.2⟩

end TernaryPeriodPolynomials.MultiplicityOne
