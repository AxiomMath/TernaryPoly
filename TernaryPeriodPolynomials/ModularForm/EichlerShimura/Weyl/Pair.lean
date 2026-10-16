module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Dirac
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section


/-!
# The Dirac pair on `E × E` and smooth fields of invertible symmetric operators

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section Pair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `L²` product `E × E`. -/
abbrev XP (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := WithLp 2 (E × E)

/-- The element `(a, b)` of `XP E`. -/
def mkX (a b : E) : XP E := WithLp.toLp 2 (a, b)

@[simp] theorem mkX_fst (a b : E) : (mkX a b).fst = a := rfl
@[simp] theorem mkX_snd (a b : E) : (mkX a b).snd = b := rfl

theorem inner_mkX (a b a' b' : E) : ⟪mkX a b, mkX a' b'⟫_ℝ = ⟪a, a'⟫_ℝ + ⟪b, b'⟫_ℝ := by
  simp [mkX]

theorem neg_mkX (a b : E) : -mkX a b = mkX (-a) (-b) := rfl

theorem mkX_eta (x : XP E) : mkX x.fst x.snd = x := rfl

/-- The first Dirac matrix `(a, b) ↦ (b, a)`. -/
def P0 : XP E →L[ℝ] XP E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.snd ℝ E E).prod (ContinuousLinearMap.fst ℝ E E)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

/-- The second Dirac matrix `(a, b) ↦ (-a, b)`. -/
def P1 : XP E →L[ℝ] XP E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap ∘L
    ((-ContinuousLinearMap.fst ℝ E E).prod (ContinuousLinearMap.snd ℝ E E)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

@[simp] theorem P0_apply (x : XP E) : P0 x = mkX x.snd x.fst := rfl
@[simp] theorem P1_apply (x : XP E) : P1 x = mkX (-x.fst) x.snd := rfl

/-- The Dirac pair on `E × E`. -/
def Pdirac : Fin 2 → XP E →L[ℝ] XP E := ![P0, P1]

theorem diracPair_Pdirac [FiniteDimensional ℝ E] : DiracPair (Pdirac (E := E)) where
  selfAdj := by
    intro j x y
    fin_cases j
    · simp [Pdirac]; ring
    · simp [Pdirac]
  sq := by
    intro j x
    fin_cases j
    · simp [Pdirac]; rfl
    · simp [Pdirac]; rfl
  anti := by
    intro x
    simp [Pdirac, neg_mkX]

end Pair

section HField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth field of invertible symmetric operators on an open set. -/
structure HField (U : Set ℂ) (Hm : ℂ → E →L[ℝ] E) : Prop where
  isOpen : IsOpen U
  smooth : ContDiffOn ℝ ∞ Hm U
  selfAdj : ∀ z ∈ U, ∀ x y, ⟪Hm z x, y⟫_ℝ = ⟪x, Hm z y⟫_ℝ
  unit : ∀ z ∈ U, IsUnit (Hm z)

/-- The inverse field. -/
def invField (Hm : ℂ → E →L[ℝ] E) : ℂ → E →L[ℝ] E := fun z => Ring.inverse (Hm z)

namespace HField

variable {U : Set ℂ} {Hm : ℂ → E →L[ℝ] E} (hH : HField U Hm)
include hH

theorem smooth_inv : ContDiffOn ℝ ∞ (invField Hm) U := by
  intro z hz
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (Hm z) := by
    obtain ⟨u, hu⟩ := hH.unit z hz
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact (h1.comp_contDiffWithinAt z (hH.smooth z hz))

omit [FiniteDimensional ℝ E] in
theorem inv_mul (z : ℂ) (hz : z ∈ U) : invField Hm z ∘L Hm z = ContinuousLinearMap.id ℝ E :=
  Ring.inverse_mul_cancel _ (hH.unit z hz)

omit [FiniteDimensional ℝ E] in
theorem mul_inv (z : ℂ) (hz : z ∈ U) : Hm z ∘L invField Hm z = ContinuousLinearMap.id ℝ E :=
  Ring.mul_inverse_cancel _ (hH.unit z hz)

omit [FiniteDimensional ℝ E] in
theorem selfAdj_inv (z : ℂ) (hz : z ∈ U) (x y : E) :
    ⟪invField Hm z x, y⟫_ℝ = ⟪x, invField Hm z y⟫_ℝ := by
  have e1 : ∀ w, Hm z (invField Hm z w) = w := fun w => by
    simpa using congrArg (fun T => T w) (hH.mul_inv z hz)
  calc ⟪invField Hm z x, y⟫_ℝ = ⟪invField Hm z x, Hm z (invField Hm z y)⟫_ℝ := by rw [e1]
    _ = ⟪Hm z (invField Hm z x), invField Hm z y⟫_ℝ := (hH.selfAdj z hz _ _).symm
    _ = ⟪x, invField Hm z y⟫_ℝ := by rw [e1]

theorem selfAdj_fderiv_inv (z : ℂ) (hz : z ∈ U) (e : ℂ) (x y : E) :
    ⟪fderiv ℝ (invField Hm) z e x, y⟫_ℝ = ⟪x, fderiv ℝ (invField Hm) z e y⟫_ℝ := by
  let A : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ E x) -
      (innerSL ℝ x).comp (ContinuousLinearMap.apply ℝ E y)
  have hA : ∀ T : E →L[ℝ] E, A T = ⟪T x, y⟫_ℝ - ⟪x, T y⟫_ℝ := fun T => by
    simp [A, real_inner_comm]
  have hz0 : (fun w => A (invField Hm w)) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hH.isOpen.mem_nhds hz] with w hw
    rw [hA, hH.selfAdj_inv w hw, sub_self]
  have hd : DifferentiableAt ℝ (invField Hm) z :=
    ((hH.smooth_inv z hz).contDiffAt (hH.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have h0 := (A.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  have h1 : fderiv ℝ (⇑A ∘ invField Hm) z = 0 := by
    have : (⇑A ∘ invField Hm) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := hz0
    rw [this.fderiv_eq]
    exact fderiv_const_apply 0
  have h2 := congrArg (fun L => L e) (h0.symm.trans h1)
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at h2
  rw [hA] at h2
  linarith [h2]

end HField

end HField

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
