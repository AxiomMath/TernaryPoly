module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.WeylRegularity
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.PartitionOfUnity
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section


/-!
# Hodge data and the real operator `H` of the Hermitian metric

A Hodge datum consists of a representation `ρ` of `Γ` on `ℂ^d` and a smooth field of invertible
operators `S` (a frame of the Hodge metric `h_z(u, v) = ⟪S z u, S z v⟫`) for which `ρ` is pointwise
unitary.  The real operator `H z = (S z)ᴴ (S z)` represents the real part of `h_z`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff InnerProductSpace MatrixGroups

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob)

/-- The coefficient space. -/
abbrev Wd (d : ℕ) := EuclideanSpace ℂ (Fin d)

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

/-- A Hodge datum: a representation `ρ` of `Γ` on `ℂ^d` together with a smooth field `S` of
invertible operators (a frame of the Hodge metric `h_z(u, v) = ⟪S z u, S z v⟫`) which makes `ρ`
unitary pointwise: `h_{γ z}(ρ γ u, ρ γ v) = h_z(u, v)`. -/
structure HodgeDatum (Γ : Subgroup SL(2, ℤ)) (d : ℕ) where
  ρ : Γ →* (Wd d →L[ℂ] Wd d)
  S : ℂ → (Wd d →L[ℂ] Wd d)
  S_smooth : ContDiffOn ℝ ∞ S U
  S_unit : ∀ z ∈ U, IsUnit (S z)
  S_equiv : ∀ γ : Γ, ∀ z ∈ U, ∀ u v : Wd d,
    ⟪S (mob (γ : SL(2, ℤ)) z) (ρ γ u), S (mob (γ : SL(2, ℤ)) z) (ρ γ v)⟫_ℂ = ⟪S z u, S z v⟫_ℂ

namespace HodgeDatum

variable (D : HodgeDatum Γ d)

/-- The real-linear structure of the representation. -/
def ρR (γ : Γ) : Wd d →L[ℝ] Wd d := (D.ρ γ).restrictScalars ℝ

/-- The real-linear map of the Hermitian form `h_z`: `⟪x, H y⟫_ℝ = Re ⟪S x, S y⟫`. -/
def H (z : ℂ) : Wd d →L[ℝ] Wd d :=
  ((D.S z).adjoint.restrictScalars ℝ).comp ((D.S z).restrictScalars ℝ)

theorem real_inner_wd (x y : Wd d) : ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp [PiLp.inner_apply, Complex.re_sum]

@[simp] theorem H_apply (z : ℂ) (x : Wd d) : D.H z x = (D.S z).adjoint (D.S z x) := rfl

theorem inner_H (z : ℂ) (x y : Wd d) : ⟪x, D.H z y⟫_ℝ = ⟪D.S z x, D.S z y⟫_ℝ := by
  have e1 : ⟪x, D.H z y⟫_ℝ = (⟪x, (D.S z).adjoint (D.S z y)⟫_ℂ).re := real_inner_wd _ _
  rw [e1, real_inner_wd, ContinuousLinearMap.adjoint_inner_right]

theorem H_selfAdj (z : ℂ) (x y : Wd d) : ⟪D.H z x, y⟫_ℝ = ⟪x, D.H z y⟫_ℝ := by
  rw [real_inner_comm, inner_H, inner_H, real_inner_comm]

/-- The adjoint, as a real-linear continuous self-map of the endomorphisms. -/
def adjointR : (Wd d →L[ℂ] Wd d) →L[ℝ] (Wd d →L[ℂ] Wd d) where
  toFun T := ContinuousLinearMap.adjoint T
  map_add' _ _ := map_add _ _ _
  map_smul' r T := by
    have h := (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Wd d) (F := Wd d)).map_smulₛₗ (r : ℂ) T
    simp only [RingHom.id_apply]
    rw [show r • T = (r : ℂ) • T from (Complex.coe_smul r T).symm]
    rw [h, show r • ContinuousLinearMap.adjoint T = (r : ℂ) • ContinuousLinearMap.adjoint T from
      (Complex.coe_smul r _).symm]
    simp
  cont := (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Wd d) (F := Wd d)).continuous

theorem smooth_SR : ContDiffOn ℝ ∞ (fun z => (D.S z).restrictScalars ℝ) U :=
  (ContinuousLinearMap.restrictScalarsL ℂ (Wd d) (Wd d) ℝ ℝ).contDiff.comp_contDiffOn D.S_smooth

theorem smooth_adj : ContDiffOn ℝ ∞ (fun z => (ContinuousLinearMap.adjoint (D.S z))) U :=
  (adjointR (d := d)).contDiff.comp_contDiffOn D.S_smooth

theorem smooth_AR : ContDiffOn ℝ ∞
    (fun z => (ContinuousLinearMap.adjoint (D.S z)).restrictScalars ℝ) U :=
  (ContinuousLinearMap.restrictScalarsL ℂ (Wd d) (Wd d) ℝ ℝ).contDiff.comp_contDiffOn D.smooth_adj

theorem smooth_H : ContDiffOn ℝ ∞ D.H U := D.smooth_AR.clm_comp D.smooth_SR

theorem unit_H {z : ℂ} (hz : z ∈ U) : IsUnit (D.H z) := by
  obtain ⟨u, hu⟩ := D.S_unit z hz
  have h1 : IsUnit ((D.S z).adjoint ∘L D.S z) := by
    have : IsUnit (star (D.S z)) := (hu ▸ u.isUnit.star)
    exact IsUnit.mul (by simpa [ContinuousLinearMap.star_eq_adjoint] using this) ⟨u, hu⟩
  obtain ⟨v, hv⟩ := h1
  refine ⟨⟨D.H z,
    (v⁻¹ : (Wd d →L[ℂ] Wd d)ˣ).val.restrictScalars ℝ, ?_, ?_⟩, rfl⟩
  · refine ContinuousLinearMap.ext fun x => ?_
    have := congrArg (fun T : Wd d →L[ℂ] Wd d => T x) (v.mul_inv)
    simp only [hv] at this
    simpa [H_apply] using this
  · refine ContinuousLinearMap.ext fun x => ?_
    have := congrArg (fun T : Wd d →L[ℂ] Wd d => T x) (v.inv_mul)
    simp only [hv] at this
    simpa [H_apply] using this

theorem hField : Weyl.HField U D.H where
  isOpen := isOpen_U
  smooth := D.smooth_H
  selfAdj z _ x y := D.H_selfAdj z x y
  unit _ hz := D.unit_H hz

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
