module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Data.String.Defs
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Weak derivatives and iterated `L²` regularity on `ℂ ≅ ℝ²`

Foundation file of the unconditional Eichler--Shimura route: weak derivatives `WD` of vector valued functions against scalar smooth test
functions, square integrable functions supported in a compact set (`L2s`), and the iterated weak
differentiability predicate `Hk`, closed under sums, linear maps and multiplication by smooth
functions.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology
open scoped ContDiff

/-- The two coordinate directions of `ℂ ≅ ℝ²`. -/
def dir (j : Fin 2) : ℂ := if j = 0 then 1 else Complex.I

/-- Scalar smooth compactly supported test functions on `ℂ`. -/
def IsTest (φ : ℂ → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `g` is the weak derivative of `v` in the coordinate direction `j`. -/
def WD (j : Fin 2) (v g : ℂ → X) : Prop :=
  ∀ φ : ℂ → ℝ, IsTest φ → ∫ z, φ z • g z = - ∫ z, fderiv ℝ φ z (dir j) • v z

/-- Square integrable and vanishing almost everywhere outside the set `K`. -/
def L2s (K : Set ℂ) (v : ℂ → X) : Prop := MemLp v 2 volume ∧ ∀ᵐ z, z ∉ K → v z = 0

theorem IsTest.mul {φ ψ : ℂ → ℝ} (hφ : IsTest φ) (hψ : ContDiff ℝ ∞ ψ) :
    IsTest (fun z => φ z * ψ z) :=
  ⟨hφ.1.mul hψ, hφ.2.mul_right⟩

theorem IsTest.continuous {φ : ℂ → ℝ} (hφ : IsTest φ) : Continuous φ := hφ.1.continuous

theorem IsTest.fderiv_apply {φ : ℂ → ℝ} (hφ : IsTest φ) (e : ℂ) :
    Continuous fun z => fderiv ℝ φ z e :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem IsTest.fderiv_compact {φ : ℂ → ℝ} (hφ : IsTest φ) (e : ℂ) :
    HasCompactSupport fun z => fderiv ℝ φ z e :=
  (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L e) (by simp)

omit [NormedSpace ℝ X] in
theorem L2s.integrable {K : Set ℂ} (hK : IsCompact K) {v : ℂ → X} (hv : L2s K v) :
    Integrable v := by
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have h1 : Integrable v (volume.restrict K) :=
    (hv.1.restrict K).integrable one_le_two
  have h2 : Integrable v (volume.restrict Kᶜ) :=
    (integrable_zero ℂ X _).congr (by
      rw [EventuallyEq, ae_restrict_iff' hK.measurableSet.compl]
      filter_upwards [hv.2] with z hz hzK using (hz hzK).symm)
  have := h1.add_measure h2
  rwa [Measure.restrict_add_restrict_compl hK.measurableSet] at this

theorem integrable_smul_cont {χ : ℂ → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {v : ℂ → X} (hv : Integrable v) : Integrable fun z => χ z • v z :=
  hv.smul_of_top_right (hχ.memLp_top_of_hasCompactSupport hc volume)

theorem WD.congr_right {j : Fin 2} {v g g' : ℂ → X} (h : WD j v g) (hg : g =ᵐ[volume] g') :
    WD j v g' := fun φ hφ => by
  rw [← h φ hφ]
  exact integral_congr_ae (hg.mono fun z hz => by simp [hz])

theorem WD.congr_left {j : Fin 2} {v v' g : ℂ → X} (h : WD j v g) (hv : v =ᵐ[volume] v') :
    WD j v' g := fun φ hφ => by
  rw [h φ hφ]
  congr 1
  exact integral_congr_ae (hv.mono fun z hz => by simp [hz])

theorem WD.unique [CompleteSpace X] {j : Fin 2} {v g g' : ℂ → X} (h : WD j v g) (h' : WD j v g')
    (hg : Integrable g) (hg' : Integrable g') : g =ᵐ[volume] g' := by
  have := ae_eq_of_integral_contDiff_smul_eq (μ := volume) hg.locallyIntegrable hg'.locallyIntegrable
    (fun φ hφ hc => (h φ ⟨hφ, hc⟩).trans (h' φ ⟨hφ, hc⟩).symm)
  exact this

theorem WD.zero_off [CompleteSpace X] {K : Set ℂ} (hK : IsCompact K) {j : Fin 2} {v g : ℂ → X}
    (hv : ∀ᵐ z, z ∉ K → v z = 0) (h : WD j v g) (hg : Integrable g) :
    ∀ᵐ z, z ∉ K → g z = 0 := by
  have := hK.isClosed.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hg.locallyIntegrable.locallyIntegrableOn (Kᶜ)) (fun φ hφ hc hs => by
      rw [h φ ⟨hφ, hc⟩]
      have : ∀ᵐ z, fderiv ℝ φ z (dir j) • v z = 0 := by
        filter_upwards [hv] with z hz
        by_cases hzK : z ∈ K
        · have : fderiv ℝ φ z = 0 := by
            apply fderiv_of_notMem_tsupport
            exact fun hz' => hs hz' hzK
          simp [this]
        · simp [hz hzK]
      rw [integral_congr_ae this]
      simp)
  exact this

theorem WD.add {j : Fin 2} {v w g h : ℂ → X} (hvg : WD j v g) (hwh : WD j w h)
    (hv : Integrable v) (hw : Integrable w) (hg : Integrable g) (hh : Integrable h) :
    WD j (fun z => v z + w z) (fun z => g z + h z) := fun φ hφ => by
  have a1 := integrable_smul_cont hφ.continuous hφ.2 hg
  have a2 := integrable_smul_cont hφ.continuous hφ.2 hh
  have b1 := integrable_smul_cont (hφ.fderiv_apply (dir j)) (hφ.fderiv_compact (dir j)) hv
  have b2 := integrable_smul_cont (hφ.fderiv_apply (dir j)) (hφ.fderiv_compact (dir j)) hw
  simp only [smul_add]
  rw [integral_add a1 a2, integral_add b1 b2, hvg φ hφ, hwh φ hφ, neg_add]

theorem WD.smul_const {j : Fin 2} {v g : ℂ → X} (c : ℝ) (h : WD j v g) :
    WD j (fun z => c • v z) (fun z => c • g z) := fun φ hφ => by
  have e1 : ∀ z, φ z • c • g z = c • (φ z • g z) := fun z => smul_comm _ _ _
  have e2 : ∀ z, fderiv ℝ φ z (dir j) • c • v z = c • (fderiv ℝ φ z (dir j) • v z) :=
    fun z => smul_comm _ _ _
  simp only [e1, e2, integral_smul, h φ hφ, smul_neg]

theorem WD.clm {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace X]
    [CompleteSpace Y] {j : Fin 2} {v g : ℂ → X} (T : X →L[ℝ] Y) (h : WD j v g)
    (hv : Integrable v) (hg : Integrable g) :
    WD j (fun z => T (v z)) (fun z => T (g z)) := fun φ hφ => by
  have a1 := integrable_smul_cont hφ.continuous hφ.2 hg
  have b1 := integrable_smul_cont (hφ.fderiv_apply (dir j)) (hφ.fderiv_compact (dir j)) hv
  have e1 : ∀ z, φ z • T (g z) = T (φ z • g z) := fun z => (map_smul T _ _).symm
  have e2 : ∀ z, fderiv ℝ φ z (dir j) • T (v z) = T (fderiv ℝ φ z (dir j) • v z) :=
    fun z => (map_smul T _ _).symm
  simp only [e1, e2]
  rw [ContinuousLinearMap.integral_comp_comm T a1, ContinuousLinearMap.integral_comp_comm T b1,
    h φ hφ, map_neg]

theorem WD.smul_smooth [CompleteSpace X] {j : Fin 2} {v g : ℂ → X} (h : WD j v g) (hv : Integrable v)
    (hg : Integrable g) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    WD j (fun z => ψ z • v z) (fun z => fderiv ℝ ψ z (dir j) • v z + ψ z • g z) := fun φ hφ => by
  have hφψ : IsTest fun z => φ z * ψ z := hφ.mul hψ
  have e1 := h _ hφψ
  have hdψ : Continuous fun z => fderiv ℝ ψ z (dir j) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have c1 : Continuous fun z => φ z * fderiv ℝ ψ z (dir j) := hφ.continuous.mul hdψ
  have k1 : HasCompactSupport fun z => φ z * fderiv ℝ ψ z (dir j) := hφ.2.mul_right
  have c2 : Continuous fun z => fderiv ℝ φ z (dir j) * ψ z :=
    (hφ.fderiv_apply (dir j)).mul hψ.continuous
  have k2 : HasCompactSupport fun z => fderiv ℝ φ z (dir j) * ψ z :=
    (hφ.fderiv_compact (dir j)).mul_right
  have i1 := integrable_smul_cont c1 k1 hv
  have i2 := integrable_smul_cont c2 k2 hv
  have i3 : Integrable fun z => (φ z * ψ z) • g z :=
    integrable_smul_cont (hφ.continuous.mul hψ.continuous) hφψ.2 hg
  have hd : ∀ z, fderiv ℝ (fun z => φ z * ψ z) z (dir j) =
      fderiv ℝ φ z (dir j) * ψ z + φ z * fderiv ℝ ψ z (dir j) := fun z => by
    rw [fderiv_fun_mul (hφ.1.differentiable (by simp) z) (hψ.differentiable (by simp) z)]
    simp only [smul_eq_mul, add_apply, smul_apply]
    ring
  have p1 : ∀ z, φ z • (fderiv ℝ ψ z (dir j) • v z + ψ z • g z) =
      (φ z * fderiv ℝ ψ z (dir j)) • v z + (φ z * ψ z) • g z := fun z => by
    simp only [smul_add, smul_smul]
  have p2 : ∀ z, fderiv ℝ φ z (dir j) • ψ z • v z = (fderiv ℝ φ z (dir j) * ψ z) • v z :=
    fun z => by simp only [smul_smul]
  have p3 : ∀ z, fderiv ℝ (fun z => φ z * ψ z) z (dir j) • v z =
      (fderiv ℝ φ z (dir j) * ψ z) • v z + (φ z * fderiv ℝ ψ z (dir j)) • v z := fun z => by
    rw [hd z, add_smul]
  simp only [p1, p2]
  simp only [p3] at e1
  rw [integral_add i2 i1] at e1
  rw [integral_add i1 i3, e1]
  abel

/-- Iterated weak differentiability in `L²`, supported in `K`. -/
def Hk (K : Set ℂ) : ℕ → (ℂ → X) → Prop
  | 0, v => L2s K v
  | k + 1, v => L2s K v ∧ ∃ g : Fin 2 → ℂ → X, (∀ j, WD j v (g j)) ∧ ∀ j, Hk K k (g j)

theorem Hk.l2s {K : Set ℂ} {k : ℕ} {v : ℂ → X} (h : Hk K k v) : L2s K v := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

theorem Hk.mono {K : Set ℂ} {k : ℕ} {v : ℂ → X} (h : Hk K (k + 1) v) : Hk K k v := by
  induction k generalizing v with
  | zero => exact h.1
  | succ k ih =>
    obtain ⟨hv, g, hg, hgk⟩ := h
    exact ⟨hv, g, hg, fun j => ih (hgk j)⟩

omit [NormedSpace ℝ X] in
theorem L2s.congr {K : Set ℂ} {v v' : ℂ → X} (h : L2s K v) (hv : v =ᵐ[volume] v') : L2s K v' :=
  ⟨h.1.ae_eq hv, by filter_upwards [h.2, hv] with z hz hz' hzK using hz'.symm.trans (hz hzK)⟩

omit [NormedSpace ℝ X] in
theorem L2s.add {K : Set ℂ} {v w : ℂ → X} (h : L2s K v) (h' : L2s K w) :
    L2s K fun z => v z + w z :=
  ⟨h.1.add h'.1, by
    filter_upwards [h.2, h'.2] with z h1 h2 hz
    simp [h1 hz, h2 hz]⟩

theorem Hk.congr {K : Set ℂ} {k : ℕ} {v v' : ℂ → X} (h : Hk K k v) (hv : v =ᵐ[volume] v') :
    Hk K k v' := by
  induction k generalizing v v' with
  | zero => exact L2s.congr h hv
  | succ k ih =>
    obtain ⟨hl, g, hg, hgk⟩ := h
    exact ⟨hl.congr hv, g, fun j => (hg j).congr_left hv, hgk⟩

theorem Hk.add [CompleteSpace X] {K : Set ℂ} (hK : IsCompact K) {k : ℕ} {v w : ℂ → X}
    (hv : Hk K k v) (hw : Hk K k w) : Hk K k (fun z => v z + w z) := by
  induction k generalizing v w with
  | zero => exact L2s.add hv hw
  | succ k ih =>
    obtain ⟨hl, g, hg, hgk⟩ := hv
    obtain ⟨hl', g', hg', hgk'⟩ := hw
    refine ⟨L2s.add hl hl', fun j => fun z => g j z + g' j z, fun j => ?_,
      fun j => ih (hgk j) (hgk' j)⟩
    exact (hg j).add (hg' j) (hl.integrable hK) (hl'.integrable hK) ((hgk j).l2s.integrable hK)
      ((hgk' j).l2s.integrable hK)

omit [NormedSpace ℝ X] in
theorem L2s.smul_smooth {K : Set ℂ} (hK : IsCompact K) {v : ℂ → X} (h : L2s K v) [NormedSpace ℝ X]
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) : L2s K fun z => ψ z • v z := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hψ.continuousOn
  refine ⟨h.1.of_le_mul (c := C) (hψ.aestronglyMeasurable.smul h.1.aestronglyMeasurable) ?_, ?_⟩
  · filter_upwards [h.2] with z hz
    by_cases hzK : z ∈ K
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC z hzK) (norm_nonneg _)
    · simp [hz hzK]
  · filter_upwards [h.2] with z hz hzK
    simp [hz hzK]

theorem L2s.clm {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {K : Set ℂ} {v : ℂ → X}
    (h : L2s K v) (T : X →L[ℝ] Y) : L2s K fun z => T (v z) :=
  ⟨T.comp_memLp' h.1, by
    filter_upwards [h.2] with z hz hzK
    simp [hz hzK]⟩

theorem Hk.smul_smooth [CompleteSpace X] {K : Set ℂ} (hK : IsCompact K) {k : ℕ} :
    ∀ {v : ℂ → X}, Hk K k v → ∀ {ψ : ℂ → ℝ}, ContDiff ℝ ∞ ψ → Hk K k fun z => ψ z • v z := by
  induction k with
  | zero =>
    intro v hv ψ hψ
    exact L2s.smul_smooth hK hv hψ.continuous
  | succ k ih =>
    intro v hv ψ hψ
    obtain ⟨hl, g, hg, hgk⟩ := hv
    refine ⟨hl.smul_smooth hK hψ.continuous,
      fun j => fun z => fderiv ℝ ψ z (dir j) • v z + ψ z • g j z, fun j => ?_, fun j => ?_⟩
    · exact (hg j).smul_smooth (hl.integrable hK) ((hgk j).l2s.integrable hK) hψ
    · have hψ' : ContDiff ℝ ∞ fun z => fderiv ℝ ψ z (dir j) :=
        (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact Hk.add hK (ih (Hk.mono ⟨hl, g, hg, hgk⟩) hψ') (ih (hgk j) hψ)

theorem Hk.clm [CompleteSpace X] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] {K : Set ℂ} (hK : IsCompact K) (T : X →L[ℝ] Y) {k : ℕ} :
    ∀ {v : ℂ → X}, Hk K k v → Hk K k fun z => T (v z) := by
  induction k with
  | zero => exact fun hv => L2s.clm hv T
  | succ k ih =>
    intro v hv
    obtain ⟨hl, g, hg, hgk⟩ := hv
    exact ⟨hl.clm T, fun j z => T (g j z), fun j =>
      (hg j).clm T (hl.integrable hK) ((hgk j).l2s.integrable hK), fun j => ih (hgk j)⟩

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
