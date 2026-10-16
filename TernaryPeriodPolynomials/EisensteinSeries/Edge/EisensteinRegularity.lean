module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.Inputs
public import TernaryPeriodPolynomials.EisensteinSeries.Edge.RecoveryConstruction
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.ConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.Continuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Helpers

@[expose] public section


/-!
# Continuity and plane constant term of the Eisenstein value at `s₀`, in every degree

Let `f` be a plane section at `s₀ = -3/2` and `E(f)` the value at `s₀` of the continuation of the
Eisenstein series of its flat extension `F`, holomorphic at `s₀` by `PlaneEisensteinHolomorphic`.
Unlike the absolutely convergent range `4 ≤ n`, no series is available at `s₀` when `n = 3`. We use
instead the regular continuation `C` of `RecoveryConstruction.exists_continuation`, whose germs at
`s₀` agree with those of `E` away from `s₀`.

* `eisensteinContinuous`: on every compact set the restrictions of `C(s)` form a meromorphic family
  of continuous functions whose slices have nonnegative order at `s₀`, so the limit `E(f)` is
  continuous on compact sets, hence (sequentially, `GL₃(𝔸)` is second countable) continuous.
* `planeConstantTerm`: the plane constant term of `C(s)` is meromorphic in `s` and equals `F_s` for
  `Re s` large (absolutely convergent series), hence near `s₀` by the identity theorem; uniform bounds
  on the compact radical domain give the limit at `s₀`, which is `F_{s₀} = f`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein.EisensteinRegularity

/-- A continuation agrees near `s₀` with one that is analytic at `s₀`: its slices converge to the
analytic value and have nonnegative order. -/
theorem germ {extension continuation analytic : ℂ → AdelicGL → ℂ}
    (continues : IsEisensteinContinuation extension continuation)
    (analyticContinues : IsEisensteinContinuation extension analytic)
    (regular : ∀ point, AnalyticAt ℂ (fun parameter => analytic parameter point) cohomologicalPoint)
    (point : AdelicGL) :
    Tendsto (fun parameter => continuation parameter point) (𝓝[≠] cohomologicalPoint)
        (𝓝 (analytic cohomologicalPoint point)) ∧
      0 ≤ meromorphicOrderAt (fun parameter => continuation parameter point) cohomologicalPoint := by
  have equality := TernaryPeriodPolynomials.EisensteinRegularization.Helpers.continuation_germs_agree
    continues analyticContinues point cohomologicalPoint
  refine ⟨((regular point).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' equality.symm,
    ?_⟩
  rw [meromorphicOrderAt_congr equality]
  exact (regular point).meromorphicOrderAt_nonneg

/-- The limit at `s₀` of a compactly regular continuation is continuous. -/
theorem value_continuous {continuation : ℂ → AdelicGL → ℂ}
    (compact : CompactContinuation.Regular continuation) (value : AdelicGL → ℂ)
    (order : ∀ point,
      0 ≤ meromorphicOrderAt (fun parameter => continuation parameter point) cohomologicalPoint)
    (limit : ∀ point, Tendsto (fun parameter => continuation parameter point)
      (𝓝[≠] cohomologicalPoint) (𝓝 (value point))) :
    Continuous value := by
  apply continuous_iff_seqContinuous.mpr
  intro sequence point convergent
  have compactSet : IsCompact (insert point (Set.range sequence)) :=
    convergent.isCompact_insert_range
  have : CompactSpace ↥(insert point (Set.range sequence)) :=
    isCompact_iff_compactSpace.mp compactSet
  obtain ⟨family, meromorphic, equality⟩ :=
    compact ↥(insert point (Set.range sequence)) Subtype.val continuous_subtype_val
  have restricted : Continuous (fun element : ↥(insert point (Set.range sequence)) =>
      value element.val) :=
    CompactContinuation.limit_continuous (meromorphic cohomologicalPoint)
      (fun element => by simpa only [equality] using order element.val)
      (fun element => value element.val)
      (fun element => by simpa only [equality] using limit element.val)
  have inside : Tendsto (fun index =>
      (⟨sequence index, Set.mem_insert_of_mem _ ⟨index, rfl⟩⟩ :
        ↥(insert point (Set.range sequence))))
      atTop (𝓝 ⟨point, Set.mem_insert _ _⟩) :=
    tendsto_subtype_rng.mpr convergent
  exact (restricted.tendsto _).comp inside

/-- **Continuity of the Eisenstein value at `s₀`**, in every degree. -/
theorem eisensteinContinuous {n : ℕ} (D : InducingData n) (hol : PlaneEisensteinHolomorphic D) :
    EisensteinContinuous D hol := by
  intro f
  obtain ⟨analytic, analyticContinues, regular, valueEq⟩ :=
    SectionSpace.sectionEisensteinValue_realizes D hol f
  obtain ⟨continuation, continues, -, compact⟩ :=
    RecoveryConstruction.exists_continuation (SectionSpace.linearFlatExtension D hol f).property
  rw [valueEq]
  exact value_continuous compact (analytic cohomologicalPoint)
    (fun point => (germ continues analyticContinues regular point).2)
    (fun point => (germ continues analyticContinues regular point).1)

/-- **The plane constant term of the Eisenstein value at `s₀`** is the section, in every degree. -/
theorem planeConstantTerm {n : ℕ} (D : InducingData n) (hol : PlaneEisensteinHolomorphic D) :
    PlaneConstantTermAtEdge D hol := by
  intro f g
  obtain ⟨analytic, analyticContinues, regular, valueEq⟩ :=
    SectionSpace.sectionEisensteinValue_realizes D hol f
  have flat := (SectionSpace.linearFlatExtension D hol f).property
  obtain ⟨continuation, continues, plane, compact⟩ := RecoveryConstruction.exists_continuation flat
  rw [valueEq]
  let extension : ℂ → AdelicGL → ℂ := (SectionSpace.linearFlatExtension D hol f).val
  let average : ℂ → ℂ := fun parameter => PlaneConstantTerm.average (continuation parameter) g
  -- the plane constant term of the continuation is the section near `s₀`
  have nearPoint : ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
      average parameter = extension parameter g := by
    obtain ⟨threshold, convergence⟩ := continues.2
    let lower : ℝ := max threshold (-(n : ℝ) / 2)
    let base : ℂ := (lower + 1 : ℝ)
    have baseLarge : lower < base.re := by
      dsimp [base]
      exact lt_add_one lower
    have nearBase : ∀ᶠ parameter in 𝓝 base, average parameter = extension parameter g := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem baseLarge]
        with parameter large
      have aboveThreshold : threshold < parameter.re := lt_of_le_of_lt (le_max_left _ _) large
      have halfPlane : -(n : ℝ) / 2 < parameter.re := lt_of_le_of_lt (le_max_right _ _) large
      have sumEq : continuation parameter = ScalarSeries.literalSum extension parameter := by
        funext point
        exact (convergence parameter aboveThreshold point).tsum_eq.symm
      change PlaneConstantTerm.average (continuation parameter) g = _
      rw [sumEq]
      exact FlatConstantTerm.average_literalSum flat parameter halfPlane g
    have meromorphicDifference : MeromorphicOn
        (fun parameter => average parameter - extension parameter g) Set.univ := by
      intro parameter _
      exact (plane.2 g parameter).sub (flat.2.1 g parameter).meromorphicAt
    have orderBase : meromorphicOrderAt
        (fun parameter => average parameter - extension parameter g) base = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      filter_upwards [nearBase.filter_mono nhdsWithin_le_nhds] with parameter same
      exact sub_eq_zero.mpr same
    have orderPoint : meromorphicOrderAt
        (fun parameter => average parameter - extension parameter g) cohomologicalPoint = ⊤ := by
      by_contra notTop
      exact (meromorphicDifference.meromorphicOrderAt_ne_top_of_isPreconnected
        isPreconnected_univ (Set.mem_univ _) (Set.mem_univ base) notTop) orderBase
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp orderPoint] with parameter zero
    exact sub_eq_zero.mp zero
  -- uniform bounds on the compact radical domain
  have domainCompact : CompactSpace ↥(UnipotentCompactDomain.closureBox ×ˢ
      UnipotentCompactDomain.closureBox) :=
    isCompact_iff_compactSpace.mp
      (UnipotentCompactDomain.closureBox_compact.prod UnipotentCompactDomain.closureBox_compact)
  let embed : ↥(UnipotentCompactDomain.closureBox ×ˢ UnipotentCompactDomain.closureBox) →
      AdelicGL := fun pair => planeUnipotent pair.val.1 pair.val.2 * g
  have embedContinuous : Continuous embed :=
    (TernaryPeriodPolynomials.EisensteinRegularization.Helpers.planeUnipotent_continuous.comp
      continuous_subtype_val).mul continuous_const
  obtain ⟨family, meromorphic, equality⟩ := compact _ embed embedContinuous
  obtain ⟨bound, bounded⟩ := CompactContinuation.eventually_bounded
    (meromorphic cohomologicalPoint)
    (fun pair => by simpa only [equality] using
      (germ continues analyticContinues regular (embed pair)).2)
  have limit : Tendsto average (𝓝[≠] cohomologicalPoint)
      (𝓝 (PlaneConstantTerm.average (analytic cohomologicalPoint) g)) := by
    show Tendsto (fun parameter => ∫ pair, continuation parameter
        (planeUnipotent pair.1 pair.2 * g) ∂PlaneConstantTerm.parameterMeasure) _
      (𝓝 (∫ pair, analytic cohomologicalPoint (planeUnipotent pair.1 pair.2 * g)
        ∂PlaneConstantTerm.parameterMeasure))
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => bound)
    · exact Eventually.of_forall (fun parameter => (plane.1 g parameter).aestronglyMeasurable)
    · filter_upwards [bounded] with parameter bounds
      filter_upwards [UnipotentCompactDomain.ae_mem_domain] with pair membership
      have value := bounds ⟨pair, UnipotentCompactDomain.domain_subset membership.1,
        UnipotentCompactDomain.domain_subset membership.2⟩
      rw [equality] at value
      exact value
    · exact integrable_const _
    · exact Eventually.of_forall (fun pair =>
        (germ continues analyticContinues regular (planeUnipotent pair.1 pair.2 * g)).1)
  have sectionLimit : Tendsto average (𝓝[≠] cohomologicalPoint)
      (𝓝 (extension cohomologicalPoint g)) :=
    ((flat.2.1 g cohomologicalPoint).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (EventuallyEq.symm nearPoint)
  have same := tendsto_nhds_unique limit sectionLimit
  change PlaneConstantTerm.average (analytic cohomologicalPoint) g = _
  rw [same]
  exact congrFun (SectionSpace.linearFlatExtension_endpoint D hol f) g

end TernaryPeriodPolynomials.EdgeEisenstein.EisensteinRegularity
