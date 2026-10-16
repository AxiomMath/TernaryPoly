module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TranslatedJets
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open Set
open scoped Pointwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AffineJets

theorem iterated_affine {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (function : E → F) (set : Set E) (openSet : IsOpen set) (smooth : ContDiffOn ℝ ⊤ function set)
    (linear : V →L[ℝ] E) (constant : E) (point : V) (membership : linear point + constant ∈ set)
    (order : ℕ) :
    iteratedFDerivWithin ℝ order (fun value => function (linear value + constant))
        ((fun value => linear value + constant) ⁻¹' set) point =
      (iteratedFDerivWithin ℝ order function set (linear point + constant)).compContinuousLinearMap
        (fun _ => linear) := by
  let shifted := (fun value : E => value + constant) ⁻¹' set
  have shiftedOpen : IsOpen shifted := openSet.preimage (continuous_id.add continuous_const)
  have shiftedSmooth : ContDiffOn ℝ ⊤ (fun value : E => function (value + constant)) shifted :=
    smooth.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ membership => membership)
  have translated : constant +ᵥ shifted = set := by
    ext value
    constructor
    · rintro ⟨source, membership, rfl⟩
      change source + constant ∈ set at membership
      simpa only [vadd_eq_add, add_comm] using membership
    · intro membership
      refine ⟨value - constant, ?_, ?_⟩
      · change value - constant + constant ∈ set
        simpa only [sub_add_cancel] using membership
      · change constant + (value - constant) = value
        abel
  have chain := linear.iteratedFDerivWithin_comp_right shiftedSmooth shiftedOpen.uniqueDiffOn
    (shiftedOpen.preimage linear.continuous).uniqueDiffOn membership (i := order) (by simp)
  have translate := iteratedFDerivWithin_comp_add_right (𝕜 := ℝ) (f := function)
    (s := shifted) order constant (linear point)
  rw [translated] at translate
  rw [translate] at chain
  exact chain

def jet {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (function : E → F) (set : Set E) (order : ℕ) (linear : V →L[ℝ] E)
    (constant : E) (point : V) : ContinuousMultilinearMap ℝ (fun _ : Fin order => V) F :=
  (iteratedFDerivWithin ℝ order function set (linear point + constant)).compContinuousLinearMap
    (fun _ => linear)

theorem jet_continuousOn {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : Type*} [TopologicalSpace X]
    (function : E → F) (set : Set E) (openSet : IsOpen set) (smooth : ContDiffOn ℝ ⊤ function set)
    (order : ℕ) (linear : X → V →L[ℝ] E) (constant : X → E) (point : X → V)
    (linearContinuous : Continuous linear) (constantContinuous : Continuous constant)
    (pointContinuous : Continuous point) :
    ContinuousOn (fun index => jet function set order (linear index) (constant index) (point index))
      {index | linear index (point index) + constant index ∈ set} := by
  let compose := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin order => V) (fun _ : Fin order => E) F
  have operators : Continuous (fun index => compose (fun _ : Fin order => linear index)) :=
    compose.cont.comp (continuous_pi (fun _ => linearContinuous))
  have values : ContinuousOn
      (fun index => iteratedFDerivWithin ℝ order function set (linear index (point index) + constant index))
      {index | linear index (point index) + constant index ∈ set} :=
    (smooth.continuousOn_iteratedFDerivWithin (by simp) openSet.uniqueDiffOn).comp
      ((linearContinuous.clm_apply pointContinuous).add constantContinuous).continuousOn
      (fun _ membership => membership)
  exact operators.continuousOn.clm_apply values

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AffineJets
