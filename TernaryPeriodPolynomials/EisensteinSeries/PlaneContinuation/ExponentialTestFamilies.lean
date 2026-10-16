module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.TestFamilies

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ExponentialTestFamilies

variable {Domain Target : Type}
variable [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target] [NormedSpace ℂ Target] [IsScalarTower ℝ ℂ Target]

def joint (center : ℂ) (height : Domain → ℝ) (test : SchwartzMap Domain Target) (pair : ℂ × Domain) : Target :=
  Complex.exp ((pair.1 - center) * (height pair.2 : ℂ)) • test pair.2

theorem joint_contDiff (center : ℂ) (height : Domain → ℝ) (test : SchwartzMap Domain Target)
    (heightSmooth : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (joint center height test) := by
  apply contDiff_iff_contDiffAt.mpr
  intro pair
  by_cases inside : pair.2 ∈ tsupport (fun value => test value)
  · have heightAt : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun pair : ℂ × Domain => (height pair.2 : ℂ)) pair :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp pair ((heightSmooth pair.2 inside).comp pair contDiffAt_snd)
    have exponentAt : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun pair : ℂ × Domain => (pair.1 - center) * (height pair.2 : ℂ)) pair :=
      (contDiffAt_fst.sub contDiffAt_const).mul heightAt
    exact (Complex.contDiff_exp.contDiffAt.comp pair exponentAt).smul
      ((test.smooth ⊤).contDiffAt.comp pair contDiffAt_snd)
  · apply contDiffAt_const.congr_of_eventuallyEq
    have zeroNearby := (continuous_snd.continuousAt : ContinuousAt (fun pair : ℂ × Domain => pair.2) pair).tendsto.eventually
      (notMem_tsupport_iff_eventuallyEq.mp inside)
    filter_upwards [zeroNearby] with value zeroValue
    change Complex.exp ((value.1 - center) * (height value.2 : ℂ)) • test value.2 = 0
    rw [show test value.2 = 0 from zeroValue, smul_zero]

theorem fixed_contDiff (center : ℂ) (height : Domain → ℝ) (test : SchwartzMap Domain Target)
    (heightSmooth : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point)
    (parameter : ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point => joint center height test (parameter, point)) :=
  (joint_contDiff center height test heightSmooth).comp (contDiff_const.prodMk contDiff_id)

def family (center : ℂ) (height : Domain → ℝ) (test : SchwartzMap Domain Target)
    (compact : HasCompactSupport (fun point => test point))
    (heightSmooth : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point)
    (parameter : ℂ) : SchwartzMap Domain Target :=
  (compact.smul_left (f := fun point => Complex.exp ((parameter - center) * (height point : ℂ)))).toSchwartzMap
    (fixed_contDiff center height test heightSmooth parameter)

theorem family_apply (center : ℂ) (height : Domain → ℝ) (test : SchwartzMap Domain Target)
    (compact : HasCompactSupport (fun point => test point))
    (heightSmooth : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point)
    (parameter : ℂ) (point : Domain) :
    family center height test compact heightSmooth parameter point =
      Complex.exp ((parameter - center) * (height point : ℂ)) • test point := rfl

theorem family_support (center : ℂ) (height : Domain → ℝ) (test : SchwartzMap Domain Target)
    (compact : HasCompactSupport (fun point => test point))
    (heightSmooth : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point)
    (parameter : ℂ) :
    tsupport (fun point => family center height test compact heightSmooth parameter point) ⊆
      tsupport (fun point => test point) :=
  tsupport_smul_subset_right _ _

theorem family_joint_contDiff (center : ℂ) (height : Domain → ℝ) (test : SchwartzMap Domain Target)
    (compact : HasCompactSupport (fun point => test point))
    (heightSmooth : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun pair : ℂ × Domain => family center height test compact heightSmooth pair.1 pair.2) :=
  joint_contDiff center height test heightSmooth

theorem family_pointwise_differentiable (center : ℂ) (height : Domain → ℝ) (test : SchwartzMap Domain Target)
    (compact : HasCompactSupport (fun point => test point))
    (heightSmooth : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point)
    (point : Domain) :
    Differentiable ℂ (fun parameter => family center height test compact heightSmooth parameter point) :=
  (Complex.differentiable_exp.comp ((differentiable_id.sub_const center).mul_const (height point : ℂ))).smul_const (test point)

theorem family_uniform_seminorms (center : ℂ) (height : Domain → ℝ) (test : SchwartzMap Domain Target)
    (compact : HasCompactSupport (fun point => test point))
    (heightSmooth : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point)
    (parameterSet : Set ℂ) (parameterCompact : IsCompact parameterSet) (weight order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameterSet,
      SchwartzMap.seminorm ℂ weight order (family center height test compact heightSmooth parameter) ≤ bound := by
  apply CompactTestFamilies.uniform_seminorm_bound _ (family_joint_contDiff center height test compact heightSmooth)
    (tsupport (fun point => test point)) compact
  intro parameter point outside
  rw [family_apply, image_eq_zero_of_notMem_tsupport outside, smul_zero]
  exact parameterCompact

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ExponentialTestFamilies
