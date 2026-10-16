module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BoundedMeromorphicFamily
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.AverageContinuation

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzRegularization
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementScalingFactor TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentCompactDomain

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineCompactContinuation

abbrev Domain := ↥(closureBox ×ˢ closureBox)

abbrev BoundedDomain := BoundedMeromorphicFamily.BoundedFunctions Domain

def Regular (continuation : ℂ → AdelicGL → ℂ) : Prop :=
  ∀ point, ∃ family : ℂ → BoundedDomain,
    (∀ parameter, MeromorphicAt family parameter) ∧
    ∀ parameter (pair : Domain), family parameter (.toTopology ⊥ pair) =
      continuation parameter (lineUnipotent pair.val.1 pair.val.2 * point)

theorem regular_mul {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation)
    (coefficient : ℂ → ℂ) (meromorphic : ∀ parameter, MeromorphicAt coefficient parameter) :
    Regular (fun parameter point => coefficient parameter * continuation parameter point) := by
  intro point
  obtain ⟨family, familyMeromorphic, equality⟩ := regular point
  refine ⟨fun parameter => coefficient parameter • family parameter,
    fun parameter => (meromorphic parameter).smul (familyMeromorphic parameter), ?_⟩
  intro parameter pair
  change coefficient parameter * family parameter (.toTopology ⊥ pair) = _
  rw [equality]

theorem regular_sum {Index : Type} (indices : Finset Index)
    (continuations : Index → ℂ → AdelicGL → ℂ)
    (regular : ∀ index ∈ indices, Regular (continuations index)) :
    Regular (fun parameter point => ∑ index ∈ indices, continuations index parameter point) := by
  classical
  intro point
  have existsFamily (index : Index) : ∃ family : ℂ → BoundedDomain,
      (∀ parameter, MeromorphicAt family parameter) ∧
      ∀ parameter (pair : Domain), index ∈ indices → family parameter (.toTopology ⊥ pair) =
        continuations index parameter (lineUnipotent pair.val.1 pair.val.2 * point) := by
    by_cases membership : index ∈ indices
    · obtain ⟨family, meromorphic, equality⟩ := regular index membership point
      exact ⟨family, meromorphic, fun parameter pair _ => equality parameter pair⟩
    · exact ⟨fun _ => 0, fun _ => MeromorphicAt.const _ _, fun _ _ h => (membership h).elim⟩
  choose families meromorphic equality using existsFamily
  refine ⟨fun parameter => ∑ index ∈ indices, families index parameter,
    fun parameter => MeromorphicAt.fun_sum (fun index _ => meromorphic index parameter), ?_⟩
  intro parameter pair
  simp only [BoundedContinuousFunction.sum_apply]
  exact Finset.sum_congr rfl (fun index membership => equality index parameter pair membership)

theorem regular_right {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation)
    (matrix : AdelicGL) : Regular (fun parameter point => continuation parameter (point * matrix)) := by
  intro point
  obtain ⟨family, meromorphic, equality⟩ := regular (point * matrix)
  exact ⟨family, meromorphic, fun parameter pair => by simpa only [mul_assoc] using equality parameter pair⟩

theorem regular_average {degree : ℕ} (data : InducingData degree)
    {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation) :
    Regular (fun parameter => FiniteSectionProjection.average data (continuation parameter)) :=
  regular_mul
    (regular_sum Finset.univ _ (fun index _ => regular_right regular
      (FiniteSectionProjection.inclusion (FiniteSectionProjection.representative data index))))
    (fun _ => (Fintype.card (FiniteSectionProjection.levelImage data) : ℂ)⁻¹)
    (fun _ => analyticAt_const.meromorphicAt)

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem theta_family {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (zeroValue : ∀ parameter, tests parameter 0 = 0)
    (zeroFourier : ∀ parameter, FourierTransform.fourier (tests parameter) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) :
    ∃ values : ℂ → BoundedDomain, Differentiable ℂ values ∧
      ∀ parameter (pair : Domain), values parameter (.toTopology ⊥ pair) =
        VectorThetaIntegral.total data family
          (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset))
          (lineUnipotent pair.val.1 pair.val.2 * point) parameter := by
  apply BoundedMeromorphicFamily.differentiable
  · intro pair
    exact UniformVectorIntegral.differentiable data family continuous tests holomorphic bounded zeroValue zeroFourier
      finiteScale offset (lineUnipotent pair.val.1 pair.val.2 * point)
  · intro parameters compact
    let points := (fun pair : Adeles × Adeles => lineUnipotent pair.1 pair.2 * point) '' (closureBox ×ˢ closureBox)
    have pointsCompact : IsCompact points := (closureBox_compact.prod closureBox_compact).image
      (TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.InducedContinuity.lineUnipotent_continuous.mul continuous_const)
    obtain ⟨bound, nonnegative, bounds⟩ := CompactThetaIntegral.total_bound data family continuous tests holomorphic bounded
      zeroValue zeroFourier finiteScale offset points pointsCompact parameters compact
    exact ⟨bound, nonnegative, fun parameter membership pair =>
      bounds parameter membership _ ⟨pair.val, pair.property, rfl⟩⟩

theorem godement_regular {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    Regular (fun parameter point => VectorGodementContinuation.continuation data family
      (tests parameter) finiteScale offset parameter point) := by
  intro point
  obtain ⟨values, differentiable, equality⟩ := theta_family data family continuous
    (fun parameter => regularize (tests parameter))
    (RegularizedTestFamilies.pointwise_differentiable tests holomorphic)
    (fun compact compactIs => RegularizedTestFamilies.family_bounded tests compact (bounded compact compactIs))
    (fun parameter => regularize_zero (tests parameter))
    (fun parameter => regularize_fourier_zero (tests parameter)) finiteScale offset point
  refine ⟨fun parameter => (GodementIntegral.outerCharacter data parameter (Matrix.GeneralLinearGroup.det point) /
    regularizationFactor data parameter) • values parameter, ?_, ?_⟩
  · intro parameter
    exact (((ZeroConstantThetaIntegral.outer_differentiable data (Matrix.GeneralLinearGroup.det point)).analyticAt parameter).meromorphicAt.div
      ((factor_differentiable data).analyticAt parameter).meromorphicAt).smul
      (differentiable.analyticAt parameter).meromorphicAt
  · intro parameter pair
    change (_ / _) * values parameter (.toTopology ⊥ pair) = _
    rw [equality]
    simp only [VectorGodementContinuation.continuation, VectorThetaIntegral.continuation,
      map_mul, TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HeightMajorant.lineUnipotent_det, one_mul]
    ring

theorem flatProfile_regular {KeyType : Type} [Fintype KeyType] {degree : ℕ}
    (data : InducingData degree) (families : KeyType → FlatProfilePackages.RealFamily data)
    (boxes : KeyType → FlatProfilePackages.Boxes) :
    Regular (FlatProfileInterpolation.continuation data families boxes) := by
  apply regular_sum Finset.univ
  intro index _
  exact regular_mul (godement_regular data (families index.1).family
    (families index.1).continuous (families index.1).tests
    (families index.1).holomorphic (families index.1).bounded _ _) _
    (fun parameter => MeromorphicAt.const _ parameter)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineCompactContinuation
