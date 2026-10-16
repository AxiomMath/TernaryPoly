module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.TwistedTests
public import TernaryPeriodPolynomials.EisensteinSeries.Edge.FrameMultiplier
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.RecoveryConstruction
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersXiSmooth

@[expose] public section


/-!
# The recovered Eisenstein continuation of a height-twisted flat family

For a real `h` write `ρ_h(y)^z = SectionMultipliers.heightMultiplier logXi h z y`
(`= (Ξ(y h)/Ξ(y))^z`). This multiplier is a function of the real frame of `y`
(`FrameMultiplier.heightMultiplier_eq_frameLog`), invariant under the right `GL₂` action on frames,
so multiplying a Godement section by it amounts to multiplying the Schwartz test by
`exp (z · frameLog h)` (`godement_twist`). It is also invariant under right translation by integral
finite elements (`heightMultiplier_inclusion`).

The recovery construction of the plane Eisenstein continuation (AxiomDeep `PlaneContinuation`,
in the explicit form of Sol's `LineRecoveryConstruction`) writes a flat family as a finite
combination, with universal meromorphic coefficients, of finite-level averages of Godement sections
attached to finitely many real Schwartz families. Running it once for a flat family `F` and twisting
every Godement test by `exp (w(s) · frameLog h)` gives, for EVERY entire exponent function `w`, an
explicit Eisenstein continuation of `s ↦ ρ_h^{w(s)} F_s` (`exists_twisted_continuation`), whose only
dependence on `w` is through the tests. This is the uniformity in the twist needed for the right
real equivariance of the Eisenstein value at `s₀`.

Original work by Claude Opus 5.5 (AxiomCode), following the step structure of AxiomDeep
`PlaneEisensteinContinuation.PlaneContinuation` and the Sol reference implementation
`StandardConstruction.LineRecoveryConstruction`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfilePackages
open TernaryPeriodPolynomials.EdgeConvergence
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein.TwistRecovery

variable {degree : ℕ} {data : InducingData degree}

/-- A real Schwartz family whose tests are supported in a fixed compact set of full-rank frames. -/
structure SupportedFamily (data : InducingData degree) where
  base : RealFamily data
  support : Set RealSpace
  compact : IsCompact support
  fullRank : support ⊆ {value : RealSpace | FullRank (coordinateEquiv.symm value)}
  supported : ∀ parameter, tsupport (fun value => base.tests parameter value) ⊆ support

/-- `FlatProfilePackages.exists_realFamily`, keeping the support of the tests. -/
theorem exists_supportedFamily {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction) (point : FiniteLevel.IntegralFiniteGL)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ result : SupportedFamily data, ∀ parameter value,
      (result.base.family (result.base.tests parameter value)).val =
        cutoff (coordinateEquiv.symm value) •
          FrameProfile.profile (flat.1 parameter) (RealFrameChart.adelicFrame
            (Matrix.GeneralLinearGroup.map integralEmbedding point) (coordinateEquiv.symm value)) := by
  obtain ⟨indices, radii, positive, tests, testsSupport, _, holomorphic, bounded, image⟩ :=
    FlatProfileTestFamilies.exists_family flat point cutoff smooth compact supported
  refine ⟨{
    base := {
      Source := ProductStages.Source data.cusp radii positive
      family := ProductStages.smoothMap data.cusp radii positive
      tests := tests
      continuous := ProductStages.smoothMap_continuous data.cusp radii positive
      holomorphic := holomorphic
      bounded := fun parameters compactSet =>
        UniformSchwartzBounds.image_family tests parameters (bounded parameters compactSet) }
    support := coordinateEquiv.symm ⁻¹' tsupport cutoff
    compact := coordinateEquiv.symm.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr compact
    fullRank := fun _ membership => supported membership
    supported := testsSupport }, ?_⟩
  intro parameter value
  apply Subtype.ext
  exact (ProductStages.smoothMap_hilbert data.cusp radii positive _).trans (image parameter value)

/-! ### Twisted tests and twisted real families -/

theorem exists_twistedTests (real : RealGL3) (family : SupportedFamily data) :
    ∃ twisted : ℂ × ℂ → SchwartzMap RealSpace family.base.Source,
      (∀ s z v, twisted (s, z) v =
        Complex.exp (z * (FrameMultiplier.frameLog real v : ℂ)) • family.base.tests s v) ∧
      (∀ pairs : Set (ℂ × ℂ), IsCompact pairs →
        UniformSchwartzBounds.Bounded (twisted '' pairs)) :=
  TwistedTests.exists_twist family.base.tests family.support family.compact family.supported
    family.base.holomorphic family.base.bounded (FrameMultiplier.frameLog real) _
    FrameMultiplier.fullRank_isOpen family.fullRank (FrameMultiplier.frameLog_contDiffOn real)

/-- The tests of a supported family twisted by `exp (z · frameLog h)`. -/
def twistedTests (real : RealGL3) (family : SupportedFamily data) :
    ℂ × ℂ → SchwartzMap RealSpace family.base.Source :=
  (exists_twistedTests real family).choose

theorem twistedTests_apply (real : RealGL3) (family : SupportedFamily data) (s z : ℂ)
    (v : RealSpace) :
    twistedTests real family (s, z) v =
      Complex.exp (z * (FrameMultiplier.frameLog real v : ℂ)) • family.base.tests s v :=
  (exists_twistedTests real family).choose_spec.1 s z v

theorem twistedTests_bounded (real : RealGL3) (family : SupportedFamily data)
    (pairs : Set (ℂ × ℂ)) (compact : IsCompact pairs) :
    UniformSchwartzBounds.Bounded (twistedTests real family '' pairs) :=
  (exists_twistedTests real family).choose_spec.2 pairs compact

theorem twistedTests_pointwise (real : RealGL3) (family : SupportedFamily data) (v : RealSpace) :
    Continuous (fun pair : ℂ × ℂ => twistedTests real family pair v) := by
  have formula : (fun pair : ℂ × ℂ => twistedTests real family pair v) = fun pair =>
      Complex.exp (pair.2 * (FrameMultiplier.frameLog real v : ℂ)) • family.base.tests pair.1 v := by
    funext pair
    exact twistedTests_apply real family pair.1 pair.2 v
  rw [formula]
  exact ((continuous_snd.mul continuous_const).cexp).smul
    ((family.base.holomorphic v).continuous.comp continuous_fst)

/-- The real family twisted along an entire exponent function `w`: tests `s ↦ exp (w s · frameLog h)
· tests s`. -/
def twistFamily (real : RealGL3) (family : SupportedFamily data) (exponent : ℂ → ℂ)
    (differentiable : Differentiable ℂ exponent) : RealFamily data where
  Source := family.base.Source
  family := family.base.family
  tests := fun parameter => twistedTests real family (parameter, exponent parameter)
  continuous := family.base.continuous
  holomorphic := by
    intro vector
    show Differentiable ℂ (fun parameter => twistedTests real family (parameter, exponent parameter) vector)
    have formula : (fun parameter => twistedTests real family (parameter, exponent parameter) vector) =
        fun parameter => Complex.exp (exponent parameter * (FrameMultiplier.frameLog real vector : ℂ)) •
          family.base.tests parameter vector := by
      funext parameter
      exact twistedTests_apply real family parameter (exponent parameter) vector
    rw [formula]
    exact (differentiable.mul_const _).cexp.smul (family.base.holomorphic vector)
  bounded := by
    intro parameters compact
    show UniformSchwartzBounds.Bounded
      ((fun parameter => twistedTests real family (parameter, exponent parameter)) '' parameters)
    have image : (fun parameter => twistedTests real family (parameter, exponent parameter)) '' parameters =
        twistedTests real family '' ((fun parameter => (parameter, exponent parameter)) '' parameters) := by
      rw [Set.image_image]
    rw [image]
    exact twistedTests_bounded real family _
      (compact.image (continuous_id.prodMk differentiable.continuous))

/-- The interpolated test of the twisted families is the twisted interpolated test. -/
theorem interpolation_test (real : RealGL3) {KeyType : Type} [Fintype KeyType]
    (families : KeyType → SupportedFamily data) (boxes : KeyType → Boxes) (exponent : ℂ → ℂ)
    (differentiable : Differentiable ℂ exponent) (parameter : ℂ) (value : Rectangular Adeles) :
    FlatProfileInterpolation.test data
        (fun key => twistFamily real (families key) exponent differentiable) boxes parameter value =
      Complex.exp (exponent parameter * (FrameMultiplier.frameLog real (archimedean value) : ℂ)) •
        FlatProfileInterpolation.test data (fun key => (families key).base) boxes parameter value := by
  rw [FlatProfileInterpolation.test_eq, FlatProfileInterpolation.test_eq, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro key _
  change (boxes key).test (finite value) • ((families key).base.family
      (twistedTests real (families key) (parameter, exponent parameter) (archimedean value))).val = _
  rw [twistedTests_apply, map_smul, Submodule.coe_smul, smul_comm]

/-! ### The multiplier on Godement sections and finite averages -/

/-- Multiplying a Godement section by `ρ_h^z` twists its test by `exp (z · frameLog h)`. -/
theorem godement_twist (real : RealGL3) (z : ℂ) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) :
    VectorGodement.sectionFunction data
        (fun value => Complex.exp (z * (FrameMultiplier.frameLog real (archimedean value) : ℂ)) •
          test value) parameter point =
      SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real z point *
        VectorGodement.sectionFunction data test parameter point := by
  have pointwise : ∀ binary : BinaryAdelicGL,
      VectorGodement.integrand data
          (fun value => Complex.exp (z * (FrameMultiplier.frameLog real (archimedean value) : ℂ)) •
            test value) parameter point binary =
        SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real z point *
          VectorGodement.integrand data test parameter point binary := by
    intro binary
    simp only [VectorGodement.integrand]
    rw [map_smul, Pi.smul_apply, smul_eq_mul,
      ← FrameMultiplier.heightMultiplier_eq_frameLog real z point binary]
    ring
  unfold VectorGodement.sectionFunction
  simp_rw [pointwise]
  rw [integral_const_mul]
  ring

/-- `ρ_h^z` is invariant under right translation by integral finite elements. -/
theorem heightMultiplier_inclusion (real : RealGL3) (z : ℂ) (point : AdelicGL)
    (matrix : FiniteLevel.IntegralFiniteGL) :
    SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real z
        (point * FiniteSectionProjection.inclusion matrix) =
      SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real z point := by
  have compact : inMaximalCompact (FiniteSectionProjection.inclusion matrix) := by
    simpa only [one_mul] using
      FiniteSectionProjection.compact_right 1 SectionMultipliersXi.one_mem_compact matrix
  have commute : point * FiniteSectionProjection.inclusion matrix * atInfinity real =
      point * atInfinity real * FiniteSectionProjection.inclusion matrix := by
    change point * atFinite (GeneralLinearGroup.map integralEmbedding matrix) * atInfinity real =
      point * atInfinity real * atFinite (GeneralLinearGroup.map integralEmbedding matrix)
    rw [mul_assoc, FiniteLevel.atFinite_atInfinity_commute, ← mul_assoc]
  unfold SectionMultipliers.heightMultiplier
  rw [commute, SectionMultipliersXi.logXi_rightCompact _ _ compact,
    SectionMultipliersXi.logXi_rightCompact _ _ compact]

/-! ### The recovery chain, twisted -/

theorem linearProfile_twist (real : RealGL3) {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ families : UniversalFiniteProfiles.Key data → SupportedFamily data,
      ∀ (exponent : ℂ → ℂ) (differentiable : Differentiable ℂ exponent),
        IsEisensteinContinuation
          (fun parameter point =>
            SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
              point *
            VectorGodement.sectionFunction data (LinearProfileRecovery.test (flat.1 parameter) cutoff)
              parameter point)
          (FlatProfileInterpolation.continuation data
            (fun key => twistFamily real (families key) exponent differentiable)
            (UniversalFiniteProfiles.boxes data)) := by
  choose families image using fun key : UniversalFiniteProfiles.Key data =>
    exists_supportedFamily flat (UniversalFiniteProfiles.representative data key) cutoff smooth
      compact supported
  have equality : FlatProfileInterpolation.test data (fun key => (families key).base)
      (UniversalFiniteProfiles.boxes data) =
      fun parameter => LinearProfileRecovery.test (flat.1 parameter) cutoff := by
    funext parameter value
    rw [FlatProfileInterpolation.test_eq]
    simp only [image]
    rfl
  refine ⟨families, fun exponent differentiable => ?_⟩
  have continues := FlatProfileInterpolation.continues data
    (fun key => twistFamily real (families key) exponent differentiable)
    (UniversalFiniteProfiles.boxes data)
  have sections : (fun parameter point => VectorGodement.sectionFunction data
      (FlatProfileInterpolation.test data
        (fun key => twistFamily real (families key) exponent differentiable)
        (UniversalFiniteProfiles.boxes data) parameter) parameter point) =
      fun parameter point =>
        SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
          point *
        VectorGodement.sectionFunction data (LinearProfileRecovery.test (flat.1 parameter) cutoff)
          parameter point := by
    funext parameter point
    have testEq : FlatProfileInterpolation.test data
        (fun key => twistFamily real (families key) exponent differentiable)
        (UniversalFiniteProfiles.boxes data) parameter = fun value =>
          Complex.exp (exponent parameter * (FrameMultiplier.frameLog real (archimedean value) : ℂ)) •
            LinearProfileRecovery.test (flat.1 parameter) cutoff value := by
      funext value
      rw [interpolation_test, equality]
    rw [testEq, godement_twist]
  exact ContinuationAlgebra.transfer continues 0 (fun parameter _ point =>
    congrFun (congrFun sections parameter) point)

theorem finiteRecovery_twist (real : RealGL3) {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) :
    ∃ families : UniversalFiniteProfiles.Key data → SupportedFamily data, ∃ constant : ℂ,
      ∀ (exponent : ℂ → ℂ) (differentiable : Differentiable ℂ exponent),
        IsEisensteinContinuation
          (fun parameter point =>
            SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
              point * FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point)
          (fun parameter point => constant * FlatProfileInterpolation.continuation data
            (fun key => twistFamily real (families key) exponent differentiable)
            (UniversalFiniteProfiles.boxes data) parameter point) := by
  obtain ⟨cutoff, smooth, compact, supported, nonzero, mass⟩ := ConstantRealMass.exists_cutoff
  obtain ⟨families, continues⟩ := linearProfile_twist real flat cutoff smooth compact supported
  refine ⟨families, (ConstantRealMass.baseMass cutoff)⁻¹, fun exponent differentiable => ?_⟩
  have result : IsEisensteinContinuation
      (fun parameter point => (ConstantRealMass.baseMass cutoff)⁻¹ *
        (SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
            point *
          VectorGodement.sectionFunction data (LinearProfileRecovery.test (flat.1 parameter) cutoff)
            parameter point))
      (fun parameter point => (ConstantRealMass.baseMass cutoff)⁻¹ *
        FlatProfileInterpolation.continuation data
          (fun key => twistFamily real (families key) exponent differentiable)
          (UniversalFiniteProfiles.boxes data) parameter point) :=
    ContinuationAlgebra.multiply (continues exponent differentiable)
      (fun _ => (ConstantRealMass.baseMass cutoff)⁻¹) (fun parameter => MeromorphicAt.const _ parameter)
  have equality : (fun parameter point => (ConstantRealMass.baseMass cutoff)⁻¹ *
        (SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
            point *
          VectorGodement.sectionFunction data (LinearProfileRecovery.test (flat.1 parameter) cutoff)
            parameter point)) =
      fun parameter point =>
        SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
          point * FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point := by
    funext parameter point
    rw [FiniteRecoveryIntegral.section_eq (flat.1 parameter) cutoff point, mass point,
      mul_left_comm (ConstantRealMass.baseMass cutoff)⁻¹, inv_mul_cancel_left₀ nonzero]
  exact ContinuationAlgebra.transfer result 0 (fun parameter _ point =>
    congrFun (congrFun equality parameter) point)

theorem finiteProjection_twist (real : RealGL3) {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) :
    ∃ families : UniversalFiniteProfiles.Key data → SupportedFamily data, ∃ constant : ℂ,
      ∀ (exponent : ℂ → ℂ) (differentiable : Differentiable ℂ exponent),
        IsEisensteinContinuation
          (fun parameter point =>
            SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
              point * FiniteSectionProjection.sectionFunction (flat.1 parameter) point)
          (fun parameter => FiniteSectionProjection.average data (fun point =>
            constant * FlatProfileInterpolation.continuation data
              (fun key => twistFamily real (families key) exponent differentiable)
              (UniversalFiniteProfiles.boxes data) parameter point)) := by
  obtain ⟨families, constant, continues⟩ := finiteRecovery_twist real flat
  refine ⟨families, constant, fun exponent differentiable => ?_⟩
  have averaged : IsEisensteinContinuation
      (fun parameter => FiniteSectionProjection.average data (fun point =>
        SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
          point * FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point))
      (fun parameter => FiniteSectionProjection.average data (fun point =>
        constant * FlatProfileInterpolation.continuation data
          (fun key => twistFamily real (families key) exponent differentiable)
          (UniversalFiniteProfiles.boxes data) parameter point)) :=
    FiniteSectionProjection.average_continuation data (continues exponent differentiable)
  have equality : (fun parameter => FiniteSectionProjection.average data (fun point =>
        SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
          point * FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point)) =
      fun parameter point =>
        SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
          point * FiniteSectionProjection.sectionFunction (flat.1 parameter) point := by
    funext parameter point
    unfold FiniteSectionProjection.sectionFunction FiniteSectionProjection.average
    simp only [heightMultiplier_inclusion, ← Finset.mul_sum]
    ring
  exact ContinuationAlgebra.transfer averaged 0 (fun parameter _ point =>
    congrFun (congrFun equality parameter) point)

/-- The explicit twisted continuation: a combination with meromorphic coefficients of finite-level
averages of interpolated Godement continuations of the twisted real families. -/
def twistedContinuation (real : RealGL3) {Indices : Type} [Fintype Indices]
    (coefficients : ℂ → Indices → ℂ)
    (families : Indices → UniversalFiniteProfiles.Key data → SupportedFamily data)
    (constants : Indices → ℂ) (exponent : ℂ → ℂ) (differentiable : Differentiable ℂ exponent) :
    ℂ → AdelicGL → ℂ :=
  fun parameter point => ∑ index, coefficients parameter index *
    FiniteSectionProjection.average data (fun point' => constants index *
      FlatProfileInterpolation.continuation data
        (fun key => twistFamily real (families index key) exponent differentiable)
        (UniversalFiniteProfiles.boxes data) parameter point') point

/-- The twisted continuation continues the combination of the twisted sections. -/
theorem twistedContinuation_continues (real : RealGL3) {Indices : Type} [Fintype Indices]
    (coefficients : ℂ → Indices → ℂ)
    (meromorphic : ∀ index parameter,
      MeromorphicAt (fun parameter => coefficients parameter index) parameter)
    (sections : Indices → ℂ → AdelicGL → ℂ)
    (families : Indices → UniversalFiniteProfiles.Key data → SupportedFamily data)
    (constants : Indices → ℂ) (exponent : ℂ → ℂ) (differentiable : Differentiable ℂ exponent)
    (continues : ∀ index, IsEisensteinContinuation
      (fun parameter point =>
        SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
          point * sections index parameter point)
      (fun parameter => FiniteSectionProjection.average data (fun point =>
        constants index * FlatProfileInterpolation.continuation data
          (fun key => twistFamily real (families index key) exponent differentiable)
          (UniversalFiniteProfiles.boxes data) parameter point))) :
    IsEisensteinContinuation
      (fun parameter point => ∑ index ∈ Finset.univ, coefficients parameter index *
        (SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
          point * sections index parameter point))
      (twistedContinuation real coefficients families constants exponent differentiable) :=
  ContinuationAlgebra.finset_sum Finset.univ
    (fun index parameter point => coefficients parameter index *
      (SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
        point * sections index parameter point))
    (fun index parameter point => coefficients parameter index *
      FiniteSectionProjection.average data (fun point' => constants index *
        FlatProfileInterpolation.continuation data
          (fun key => twistFamily real (families index key) exponent differentiable)
          (UniversalFiniteProfiles.boxes data) parameter point') point)
    (fun index _ => ContinuationAlgebra.multiply (continues index)
      (fun parameter => coefficients parameter index) (meromorphic index))

/-- Multiplying a recovered combination by the twist. -/
theorem combination_twist (real : RealGL3) (exponent : ℂ → ℂ) (original : ℂ → AdelicGL → ℂ)
    {Indices : Type} [Fintype Indices] (coefficients : ℂ → Indices → ℂ)
    (sections : Indices → ℂ → AdelicGL → ℂ) (parameter : ℂ) (point : AdelicGL)
    (sum : ∑ index, coefficients parameter index * sections index parameter point =
      original parameter point) :
    ∑ index ∈ Finset.univ, coefficients parameter index *
        (SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
          point * sections index parameter point) =
      SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
        point * original parameter point := by
  rw [← sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- **The twisted continuation.** For a flat family `F` there are universal meromorphic coefficients,
supported real families and constants such that, for every entire exponent function `w`, the
explicit function `twistedContinuation` is an Eisenstein continuation of `s ↦ ρ_h^{w(s)} F_s`. -/
theorem exists_twisted_continuation (real : RealGL3) {original : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data original) :
    ∃ (size : ℕ) (coefficients : ℂ → Fin size → ℂ)
      (families : Fin size → UniversalFiniteProfiles.Key data → SupportedFamily data)
      (constants : Fin size → ℂ),
      (∀ index parameter, MeromorphicAt (fun parameter => coefficients parameter index) parameter) ∧
      ∀ (exponent : ℂ → ℂ) (differentiable : Differentiable ℂ exponent),
        IsEisensteinContinuation
          (fun parameter point =>
            SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real (exponent parameter)
              point * original parameter point)
          (twistedContinuation real coefficients families constants exponent differentiable) := by
  classical
  let basis := Module.finBasis ℂ (RecoveryTupleAlgebra.algebra data)
  obtain ⟨coefficients, cutoffValue, bound, meromorphic, inverse⟩ :=
    MeromorphicRecoveryAlgebra.exists_inverse_coefficients data basis
  choose groupFamilies familiesFlat realizations using fun index =>
    FlatAlgebraRealization.exists_flat flat (basis index)
  choose families constants continues using fun index =>
    finiteProjection_twist real (familiesFlat index)
  refine ⟨_, coefficients, families, constants, meromorphic, fun exponent differentiable => ?_⟩
  refine ContinuationAlgebra.transfer (twistedContinuation_continues real coefficients meromorphic
    (fun index parameter point =>
      FiniteSectionProjection.sectionFunction ((familiesFlat index).1 parameter) point)
    families constants exponent differentiable
    (fun index => continues index exponent differentiable)) cutoffValue ?_
  intro parameter above point
  exact combination_twist real exponent original coefficients
    (fun index parameter point =>
      FiniteSectionProjection.sectionFunction ((familiesFlat index).1 parameter) point)
    parameter point
    (congrFun (RecoveredAlgebraCombination.eq_original flat familiesFlat
      (fun index => basis index) coefficients realizations parameter (lt_trans bound above)
      (inverse ⟨parameter, lt_trans bound above⟩ above.le).1) point)

end TernaryPeriodPolynomials.EdgeEisenstein.TwistRecovery
