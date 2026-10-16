module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.CompactContinuation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.ConstantTermBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.NormContinuity

@[expose] public section


/-!
# Godement theta continuations are meromorphic families of continuous functions

The Godement continuation `VectorGodementContinuation.continuation` of a holomorphic family of
Schwartz tests is `outerCharacter(det g) · Θ(s, g) / r(s)`, where `Θ(s, g)` is an integral over a
fundamental domain of `GL₂(ℚ)\GL₂(𝔸)` of a theta series and `r` is an entire regularization factor.
The theta integrand is continuous in `g` and dominated, uniformly for `g` in a compact set, by an
integrable function (`CompactThetaIntegral.exists_bound`), so `Θ(s, ·)` is continuous
(`total_continuousOn`). Together with the uniform bounds `CompactThetaIntegral.total_bound` and
holomorphy in `s`, this makes the restriction to any compact space a holomorphic family of
continuous functions, and the continuation a meromorphic one (`godement_regular`). The finite
combinations of the flat-profile interpolation inherit the property (`flatProfile_regular`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzRegularization
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementScalingFactor
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein.GodementCompact

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

/-- The theta integral is continuous in the point on every compact set. -/
theorem total_continuousOn {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact →
      UniformSchwartzBounds.Bounded (tests '' compact))
    (zeroValue : ∀ parameter, tests parameter 0 = 0)
    (zeroFourier : ∀ parameter, FourierTransform.fourier (tests parameter) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (points : Set AdelicGL) (pointsCompact : IsCompact points) (parameter : ℂ) :
    ContinuousOn (fun point => VectorThetaIntegral.total data family
      (BanachAdelicTheta.tensorTest (tests parameter)
        (RectangularAdelicPoisson.finiteTest finiteScale offset)) point parameter) points := by
  obtain ⟨bound, integrable, bounds⟩ := CompactThetaIntegral.exists_bound data family continuous
    tests holomorphic bounded zeroValue zeroFourier finiteScale offset points pointsCompact
    {parameter} isCompact_singleton
  unfold VectorThetaIntegral.total
  apply continuousOn_of_dominated (bound := bound)
  · intro point _
    exact (VectorThetaIntegral.integrand_measurable data family continuous (tests parameter) _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset)
      point parameter).aestronglyMeasurable
  · intro point membership
    exact Eventually.of_forall (fun binary =>
      bounds parameter (Set.mem_singleton _) point membership binary)
  · exact integrable
  · refine Eventually.of_forall (fun binary => ?_)
    exact ((VectorTheta.fullTheta_continuous data family continuous (tests parameter) _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset)).comp
        (continuous_id.prodMk continuous_const) |>.const_mul _).continuousOn

/-- The outer character of the determinant is jointly continuous in the parameter and the point. -/
theorem outerCharacter_continuous {degree : ℕ} (data : InducingData degree) :
    Continuous (fun pair : ℂ × AdelicGL =>
      GodementIntegral.outerCharacter data pair.1 (GeneralLinearGroup.det pair.2)) := by
  have determinant : Continuous (fun pair : ℂ × AdelicGL => GeneralLinearGroup.det pair.2) :=
    GodementConstantTermBounds.determinant_continuous.comp continuous_snd
  have exponent : Continuous (fun pair : ℂ × AdelicGL =>
      -2 * inductionExponent .plane pair.1) := by
    simp only [inductionExponent]
    fun_prop
  change Continuous (fun pair : ℂ × AdelicGL =>
    data.chi.toMonoidHom (GeneralLinearGroup.det pair.2) *
      normPower (GeneralLinearGroup.det pair.2) (-2 * inductionExponent .plane pair.1))
  exact (data.chi.continuous.comp determinant).mul
    (TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_continuous.comp
      (determinant.prodMk exponent))

/-- The outer character along continuous parameter and point maps. -/
theorem outerCharacter_comp_continuous {degree : ℕ} (data : InducingData degree) {Space : Type}
    [TopologicalSpace Space] {parameters : Space → ℂ} {points : Space → AdelicGL}
    (parametersContinuous : Continuous parameters) (pointsContinuous : Continuous points) :
    Continuous (fun element => GodementIntegral.outerCharacter data (parameters element)
      (GeneralLinearGroup.det (points element))) := by
  have determinant : Continuous (fun element => GeneralLinearGroup.det (points element)) :=
    GodementConstantTermBounds.determinant_continuous.comp pointsContinuous
  have exponent : Continuous (fun element =>
      -2 * inductionExponent .plane (parameters element)) := by
    simp only [inductionExponent]
    fun_prop
  change Continuous (fun element =>
    data.chi.toMonoidHom (GeneralLinearGroup.det (points element)) *
      normPower (GeneralLinearGroup.det (points element))
        (-2 * inductionExponent .plane (parameters element)))
  exact (data.chi.continuous.comp determinant).mul
    (TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_continuous.comp
      (determinant.prodMk exponent))

/-- **Godement continuations are regular** on every compact space. -/
theorem godement_regular {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact →
      UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    CompactContinuation.Regular (fun parameter point => VectorGodementContinuation.continuation
      data family (tests parameter) finiteScale offset parameter point) := by
  intro Space _ _ embed embedContinuous
  let regularized : ℂ → SchwartzMap RealSpace Source := fun parameter => regularize (tests parameter)
  have regularizedHolomorphic : ∀ vector,
      Differentiable ℂ (fun parameter => regularized parameter vector) :=
    RegularizedTestFamilies.pointwise_differentiable tests holomorphic
  have regularizedBounded : ∀ compact : Set ℂ, IsCompact compact →
      UniformSchwartzBounds.Bounded (regularized '' compact) :=
    fun compact compactIs => RegularizedTestFamilies.family_bounded tests compact
      (bounded compact compactIs)
  have regularizedZero : ∀ parameter, regularized parameter 0 = 0 :=
    fun parameter => regularize_zero (tests parameter)
  have regularizedFourier : ∀ parameter, FourierTransform.fourier (regularized parameter) 0 = 0 :=
    fun parameter => regularize_fourier_zero (tests parameter)
  let theta : ℂ → AdelicGL → ℂ := fun parameter point => VectorThetaIntegral.total data family
    (BanachAdelicTheta.tensorTest (regularized parameter)
      (RectangularAdelicPoisson.finiteTest finiteScale offset)) point parameter
  let numerator : ℂ → Space → ℂ := fun parameter point =>
    GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det (embed point)) *
      theta parameter (embed point)
  have rangeCompact : IsCompact (Set.range embed) := isCompact_range embedContinuous
  have numeratorContinuous : ∀ parameter, Continuous (numerator parameter) := by
    intro parameter
    have outer : Continuous (fun point : Space =>
        GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det (embed point))) :=
      outerCharacter_comp_continuous data (continuous_const (y := parameter)) embedContinuous
    have thetaContinuous : Continuous (fun point : Space => theta parameter (embed point)) :=
      (total_continuousOn data family continuous regularized regularizedHolomorphic
        regularizedBounded regularizedZero regularizedFourier finiteScale offset (Set.range embed)
        rangeCompact parameter).comp_continuous embedContinuous (fun point => ⟨point, rfl⟩)
    exact outer.mul thetaContinuous
  have numeratorHolomorphic : ∀ point,
      Differentiable ℂ (fun parameter => numerator parameter point) := by
    intro point
    exact (ZeroConstantThetaIntegral.outer_differentiable data
      (GeneralLinearGroup.det (embed point))).mul
      (UniformVectorIntegral.differentiable data family continuous regularized
        regularizedHolomorphic regularizedBounded regularizedZero regularizedFourier finiteScale
        offset (embed point))
  have numeratorBounded : ∀ compact : Set ℂ, IsCompact compact →
      ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ compact, ∀ point,
        ‖numerator parameter point‖ ≤ bound := by
    intro compact compactIs
    obtain ⟨thetaBound, thetaNonnegative, thetaBounds⟩ := CompactThetaIntegral.total_bound data
      family continuous regularized regularizedHolomorphic regularizedBounded regularizedZero
      regularizedFourier finiteScale offset (Set.range embed) rangeCompact compact compactIs
    have outerBoundExists : ∃ bound : ℝ, ∀ parameter ∈ compact, ∀ point : Space,
        ‖GodementIntegral.outerCharacter data parameter
          (GeneralLinearGroup.det (embed point))‖ ≤ bound := by
      obtain ⟨bound, bounds⟩ := (compactIs.prod
        (isCompact_univ : IsCompact (Set.univ : Set Space))).exists_bound_of_continuousOn
        (outerCharacter_comp_continuous data continuous_fst
          (embedContinuous.comp continuous_snd)).continuousOn
      exact ⟨bound, fun parameter membership point =>
        bounds (parameter, point) ⟨membership, Set.mem_univ _⟩⟩
    obtain ⟨outerBound, outerBounds⟩ := outerBoundExists
    refine ⟨max outerBound 0 * thetaBound, mul_nonneg (le_max_right _ _) thetaNonnegative, ?_⟩
    intro parameter membership point
    have outerLe := (outerBounds parameter membership point).trans (le_max_left outerBound 0)
    have thetaLe := thetaBounds parameter membership (embed point) ⟨point, rfl⟩
    change ‖GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det (embed point)) *
      theta parameter (embed point)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul outerLe thetaLe (norm_nonneg _) (le_max_right _ _)
  obtain ⟨values, differentiable, equality⟩ := CompactContinuation.differentiable_of_continuous
    numerator numeratorContinuous numeratorHolomorphic numeratorBounded
  refine ⟨fun parameter => (regularizationFactor data parameter)⁻¹ • values parameter, ?_, ?_⟩
  · intro parameter
    exact ((factor_differentiable data).analyticAt parameter).meromorphicAt.inv.smul
      (differentiable.analyticAt parameter).meromorphicAt
  · intro parameter point
    change (regularizationFactor data parameter)⁻¹ * values parameter point = _
    rw [equality]
    simp only [numerator, theta, regularized, VectorGodementContinuation.continuation,
      VectorThetaIntegral.continuation]
    rw [div_eq_inv_mul]

/-- The finite Godement combinations of the flat-profile interpolation are regular. -/
theorem flatProfile_regular {KeyType : Type} [Fintype KeyType] {degree : ℕ}
    (data : InducingData degree) (families : KeyType → FlatProfilePackages.RealFamily data)
    (boxes : KeyType → FlatProfilePackages.Boxes) :
    CompactContinuation.Regular (FlatProfileInterpolation.continuation data families boxes) := by
  apply CompactContinuation.regular_sum Finset.univ
  intro index _
  exact CompactContinuation.regular_mul (godement_regular data (families index.1).family
    (families index.1).continuous (families index.1).tests
    (families index.1).holomorphic (families index.1).bounded _ _) _
    (fun parameter => MeromorphicAt.const _ parameter)

end TernaryPeriodPolynomials.EdgeEisenstein.GodementCompact
