module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamComplex
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Compactness.LocallyCompact
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology

universe u
variable {E G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Parameters whose whole integration segment lies in the open smoothness domain. -/
def sliceDomain (D : Set (E × ℝ)) : Set E := {x | ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ D}

omit [NormedSpace ℝ E] in
theorem sliceDomain_isOpen {D : Set (E × ℝ)} (hD : IsOpen D) : IsOpen (sliceDomain D) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U, V, hU, _, hxU, hIV, hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := x)) isCompact_Icc hD
      (by rintro ⟨y, t⟩ ⟨hy, ht⟩; obtain rfl := mem_singleton_iff.mp hy; exact hx t ht)
  exact mem_of_superset (hU.mem_nhds (hxU (mem_singleton x)))
    (fun y hy t ht => hUV ⟨hy, hIV ht⟩)

/-- The partial derivative in the chart parameter, as a genuine continuous linear map. -/
def parameterDerivative (f : E × ℝ → G) (p : E × ℝ) : E →L[ℝ] G :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)

theorem parameterDerivative_smooth {D : Set (E × ℝ)} (hD : IsOpen D)
    {f : E × ℝ → G} (hf : ContDiffOn ℝ ∞ f D) :
    ContDiffOn ℝ ∞ (parameterDerivative f) D := by
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hD).mp hf).2.clm_comp contDiffOn_const

theorem parameterDerivative_hasFDerivAt {D : Set (E × ℝ)} (hD : IsOpen D)
    {f : E × ℝ → G} (hf : ContDiffOn ℝ ∞ f D) {x : E} {t : ℝ} (hp : (x, t) ∈ D) :
    HasFDerivAt (fun y => f (y, t)) (parameterDerivative f (x, t)) x := by
  have ht := (((hf (x, t) hp).contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  exact ht.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))

variable [FiniteDimensional ℝ E]

/-- Smoothness on an open neighborhood of a compact integration segment supplies a uniform bound. -/
theorem parameterDerivative_local_bound {D : Set (E × ℝ)} (hD : IsOpen D)
    {f : E × ℝ → G} (hf : ContDiffOn ℝ ∞ f D) {x : E} (hx : x ∈ sliceDomain D) :
    ∃ K : Set E, K ∈ 𝓝 x ∧ K ⊆ sliceDomain D ∧
      ∃ C : ℝ, ∀ y ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ‖parameterDerivative f (y, t)‖ ≤ C := by
  obtain ⟨K, hK, hxK, hKD⟩ := exists_compact_subset (sliceDomain_isOpen hD) hx
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    ((parameterDerivative_smooth hD hf).continuousOn.mono
      (fun p hp => hKD hp.1 p.2 hp.2))
  exact ⟨K, mem_interior_iff_mem_nhds.mp hxK, hKD, C, fun y hy t ht => hC (y, t) ⟨hy, ht⟩⟩

/-- Differentiation of an actual interval integral in a finite-dimensional chart parameter. -/
theorem hasFDerivAt_parameterIntegral {D : Set (E × ℝ)} (hD : IsOpen D)
    {f : E × ℝ → G} (hf : ContDiffOn ℝ ∞ f D) {x : E} (hx : x ∈ sliceDomain D) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, f (y, t))
      (∫ t in (0 : ℝ)..1, parameterDerivative f (x, t)) x := by
  obtain ⟨K, hK, hKD, C, hC⟩ := parameterDerivative_local_bound hD hf hx
  have hcont (y : E) (hy : y ∈ sliceDomain D) : ContinuousOn (fun t => f (y, t)) (Icc (0 : ℝ) 1) :=
    hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hy
  have hdcont : ContinuousOn (fun t => parameterDerivative f (x, t)) (Icc (0 : ℝ) 1) :=
    (parameterDerivative_smooth hD hf).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hx
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := K) (bound := fun _ => C) hK
  · filter_upwards [hK] with y hy
    simpa only [uIoc_of_le zero_le_one] using
      ((hcont y (hKD hy)).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
  · exact (hcont x hx).intervalIntegrable_of_Icc zero_le_one
  · simpa only [uIoc_of_le zero_le_one] using
      (hdcont.mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
  · filter_upwards [] with t ht y hy
    exact hC y hy t (by simpa using Ioc_subset_Icc_self ht)
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht y hy
    exact parameterDerivative_hasFDerivAt hD hf (hKD hy t (by simpa using Ioc_subset_Icc_self ht))

/-- Every finite smoothness order of the parameter integral follows by differentiating again. -/
theorem parameterIntegral_contDiffOn_nat (n : ℕ) {D : Set (E × ℝ)} (hD : IsOpen D)
    {f : E × ℝ → G} (hf : ContDiffOn ℝ ∞ f D) :
    ContDiffOn ℝ n (fun x => ∫ t in (0 : ℝ)..1, f (x, t)) (sliceDomain D) := by
  induction n generalizing G with
  | zero =>
    simp only [Nat.cast_zero, contDiffOn_zero]
    exact DifferentiableOn.continuousOn (𝕜 := ℝ)
      (fun x hx => (hasFDerivAt_parameterIntegral hD hf hx).differentiableAt.differentiableWithinAt)
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp]
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (sliceDomain_isOpen hD)).mpr
    refine ⟨fun x hx => (hasFDerivAt_parameterIntegral hD hf hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    apply (ih (parameterDerivative_smooth hD hf)).congr
    intro x hx
    exact (hasFDerivAt_parameterIntegral hD hf hx).fderiv

/-- An actual interval integral of a smooth function is smooth on its full compact-slice domain. -/
theorem parameterIntegral_smooth {D : Set (E × ℝ)} (hD : IsOpen D)
    {f : E × ℝ → G} (hf : ContDiffOn ℝ ∞ f D) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, f (x, t)) (sliceDomain D) := by
  rw [contDiffOn_infty]
  intro n
  exact parameterIntegral_contDiffOn_nat n hD hf

end TernaryPoly.SmoothLocalDeRham
