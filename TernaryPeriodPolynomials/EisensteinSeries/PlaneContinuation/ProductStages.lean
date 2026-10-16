module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.BanachLift
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.StageCutoff

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductStages

variable {Index : Type} [Fintype Index]

abbrev Source (data : CuspidalRepresentation) (radii : Index → ℝ≥0) (positive : ∀ index, 0 < radii index) :=
  ∀ index, analyticStage data finiteCongruence (radii index) (positive index)

instance sourceSMulComm (data : CuspidalRepresentation) (radii : Index → ℝ≥0) (positive : ∀ index, 0 < radii index) :
    SMulCommClass ℝ ℂ (Source data radii positive) where
  smul_comm real complex value := by
    funext index
    apply Subtype.ext
    exact Prod.ext (smul_comm real complex (value index).val.1) (smul_comm real complex (value index).val.2)

def hilbertMap (data : CuspidalRepresentation) (radii : Index → ℝ≥0) (positive : ∀ index, 0 < radii index) :
    Source data radii positive →L[ℂ] data.H :=
  CompactBanachLift.sumMap (fun index => stageHilbertMap data finiteCongruence (radii index) (positive index))

def smoothMap (data : CuspidalRepresentation) (radii : Index → ℝ≥0) (positive : ∀ index, 0 < radii index) :
    Source data radii positive →ₗ[ℂ] TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedSmooth data finiteCongruence :=
  ∑ index, (stageSmoothMap data finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
    (radii index) (positive index)).comp (LinearMap.proj index)

theorem smoothMap_hilbert (data : CuspidalRepresentation) (radii : Index → ℝ≥0) (positive : ∀ index, 0 < radii index)
    (value : Source data radii positive) :
    (smoothMap data radii positive value).val.val = hilbertMap data radii positive value := by
  simp only [smoothMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum, hilbertMap, CompactBanachLift.sumMap_apply]
  rfl

theorem smoothMap_continuous (data : CuspidalRepresentation) (radii : Index → ℝ≥0) (positive : ∀ index, 0 < radii index) :
    Continuous (fun value => (smoothMap data radii positive value).val.val) := by
  simpa only [smoothMap_hilbert] using (hilbertMap data radii positive).continuous

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductStages
