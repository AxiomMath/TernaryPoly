module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamComplex
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Calculus.MeanValue
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set ContinuousAlternatingMap MeasureTheory
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The canonical identification of coefficient values with alternating zero-forms. -/
abbrev zeroEquiv : F ≃ₗᵢ[ℝ] (E [⋀^Fin 0]→L[ℝ] F) := constOfIsEmptyLIE ℝ E F (Fin 0)

/-- The canonical identification of linear maps with alternating one-forms. -/
abbrev oneEquiv : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (E [⋀^Fin 1]→L[ℝ] F) :=
  ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)

/-- An actual smooth coefficient function regarded as a chart zero-form. -/
def ofFunction {s : Set E} (f : E → F) (hf : ContDiffOn ℝ ∞ f s) : Form (F := F) s 0 :=
  restrictForm s (fun x => zeroEquiv (f x)) (by
    exact (zeroEquiv (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hf)

@[simp] theorem ofFunction_apply {s : Set E} (f : E → F) (hf : ContDiffOn ℝ ∞ f s)
    {x : E} (hx : x ∈ s) : (ofFunction f hf : RawForm E F 0) x = zeroEquiv (f x) :=
  by simp [ofFunction, hx]

/-- The degree-zero differential is the ordinary Frechet derivative, literally. -/
theorem d_ofFunction {s : Set E} (hs : IsOpen s) (f : E → F)
    (hf : ContDiffOn ℝ ∞ f s) {x : E} (hx : x ∈ s) :
    (d hs 0 (ofFunction f hf) : RawForm E F 1) x = oneEquiv (fderiv ℝ f x) := by
  rw [d_apply hs _ hx]
  have heq : (ofFunction f hf : RawForm E F 0) =ᶠ[𝓝 x] fun y => zeroEquiv (f y) := by
    filter_upwards [hs.mem_nhds hx] with y hy using ofFunction_apply f hf hy
  rw [heq.extDeriv_eq (𝕜 := ℝ)]
  exact extDeriv_constOfIsEmpty f x

/-- A smooth function defines a closed zero-form exactly when it is constant on a connected chart. -/
theorem closed_ofFunction_iff_constant {s : Set E} (hs : IsOpen s)
    (hc : IsPreconnected s) (f : E → F) (hf : ContDiffOn ℝ ∞ f s) :
    d hs 0 (ofFunction f hf) = 0 ↔ ∃ c : F, ∀ x ∈ s, f x = c := by
  constructor
  · intro h
    apply hs.exists_is_const_of_fderiv_eq_zero hc (hf.differentiableOn (by simp))
    intro x hx
    have hd := congrArg (fun w : Form (F := F) s 1 => (w : RawForm E F 1) x) h
    rw [d_ofFunction hs f hf hx] at hd
    apply (oneEquiv (E := E) (F := F)).injective
    simp only [Pi.zero_apply, _root_.map_zero]
    exact hd
  · rintro ⟨c, hc⟩
    apply Form.ext
    intro x hx
    rw [d_ofFunction hs f hf hx]
    have heq : f =ᶠ[𝓝 x] fun _ => c := by
      filter_upwards [hs.mem_nhds hx] with y hy using hc y hy
    rw [heq.fderiv_eq (𝕜 := ℝ)]
    simpa only [fderiv_fun_const, Pi.zero_apply, ZeroMemClass.coe_zero] using (oneEquiv (E := E) (F := F)).map_zero


/-- Exterior differentiation of an alternating one-form is antisymmetrized differentiation. -/
theorem extDeriv_oneEquiv (a : E → E →L[ℝ] F) (x u v : E) :
    extDeriv (fun y => oneEquiv (a y)) x ![u, v] =
      fderiv ℝ a x u v - fderiv ℝ a x v u := by
  unfold extDeriv
  change (alternatizeUncurryFin (fderiv ℝ ((oneEquiv (E := E) (F := F)) ∘ a) x)) ![u, v] = _
  rw [(oneEquiv (E := E) (F := F)).comp_fderiv]
  simp [alternatizeUncurryFin_apply, Fin.sum_univ_two, oneEquiv, sub_eq_add_neg, Fin.removeNth]

/-- Vanishing of the actual exterior differential is precisely the closed-one-form condition. -/
theorem extDeriv_oneEquiv_eq_zero_iff (a : E → E →L[ℝ] F) (x : E) :
    extDeriv (fun y => oneEquiv (a y)) x = 0 ↔
      ∀ u v, fderiv ℝ a x u v = fderiv ℝ a x v u := by
  constructor
  · intro h u v
    have hv := congrArg (fun w : E [⋀^Fin 2]→L[ℝ] F => w ![u, v]) h
    rw [extDeriv_oneEquiv] at hv
    exact sub_eq_zero.mp hv
  · intro h
    ext v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv, extDeriv_oneEquiv, h]
    simp

/-- Decode a chart zero-form as its actual coefficient-valued function. -/
def toFunction {s : Set E} (w : Form (F := F) s 0) : E → F :=
  fun x => zeroEquiv.symm ((w : RawForm E F 0) x)

theorem smooth_toFunction {s : Set E} (w : Form (F := F) s 0) :
    ContDiffOn ℝ ∞ (toFunction w) s := by
  exact (zeroEquiv (E := E) (F := F)).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn
    (Form.smooth w)

@[simp] theorem ofFunction_toFunction {s : Set E} (w : Form (F := F) s 0) :
    ofFunction (toFunction w) (smooth_toFunction w) = w := by
  apply Form.ext
  intro x hx
  rw [ofFunction_apply _ _ hx]
  exact zeroEquiv.apply_symm_apply _

/-- The constants are actual constant coefficient sections restricted to the chart. -/
def constant (s : Set E) (c : F) : Form (F := F) s 0 :=
  ofFunction (fun _ => c) contDiffOn_const

/-- All closed smooth zero-forms on a connected open chart are constant sections. -/
theorem closed_zero_iff_constant {s : Set E} (hs : IsOpen s) (hc : IsPreconnected s)
    (w : Form (F := F) s 0) : d hs 0 w = 0 ↔ ∃ c : F, w = constant s c := by
  rw [← ofFunction_toFunction w, closed_ofFunction_iff_constant hs hc]
  constructor
  · rintro ⟨c, h⟩
    refine ⟨c, ?_⟩
    apply Form.ext
    intro x hx
    simp only [ofFunction_apply _ _ hx, constant]
    rw [h x hx]
  · rintro ⟨c, h⟩
    refine ⟨c, fun x hx => ?_⟩
    have hp := congrArg (fun z : Form (F := F) s 0 => (z : RawForm E F 0) x) h
    simp only [ofFunction_apply _ _ hx, constant] at hp
    exact (zeroEquiv (E := E) (F := F)).injective hp

end TernaryPoly.SmoothLocalDeRham
