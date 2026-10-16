module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HilbertModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SmoothCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CompactCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryHilbertCocycle_identity (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (first second : BinaryRealGL) :
    binaryHilbertEmbedding cusp basis (cycle (first * second)) =
      binaryHilbertEmbedding cusp basis (cycle first) +
        binaryHilbertOperator cusp basis first (binaryHilbertEmbedding cusp basis (cycle second)) := by
  have equality := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property first second
  let embedding : (binaryCuspidalRep cusp degree) →ₗ[ℂ] (index → cusp.H) :=
    binaryHilbertEmbedding cusp basis
  have embedded := congrArg embedding equality
  rw [map_add] at embedded
  have intertwines : embedding ((binaryCuspidalRep cusp degree).ρ first (cycle second)) =
      binaryHilbertOperator cusp basis first (embedding (cycle second)) :=
    (binaryHilbertOperator_intertwines cusp basis first (cycle second)).symm
  exact embedded.trans ((congrArg (fun vector : index → cusp.H => vector + embedding (cycle first))
    intertwines).trans (add_comm _ _))

theorem binaryHilbertCocycle_smooth (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : BinaryRealGL → binaryCuspidalValues cusp degree)
    (smooth : Smooth (fun point : Fin 2 → BinaryRealGL =>
      binaryHilbertEmbedding cusp basis
        (binaryRightTranslation cusp degree (atInfinity (point 1)) (cycle (point 0))))) :
    Smooth (fun point : Fin 1 → BinaryRealGL => binaryHilbertEmbedding cusp basis (cycle (point 0))) := by
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    atInfinity_one, binaryRightTranslation_one, Module.End.one_apply] using
    smooth_pair_with_one smooth

theorem binaryHilbertCocycle_continuous (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : BinaryRealGL → binaryCuspidalValues cusp degree)
    (smooth : Smooth (fun point : Fin 2 → BinaryRealGL =>
      binaryHilbertEmbedding cusp basis
        (binaryRightTranslation cusp degree (atInfinity (point 1)) (cycle (point 0))))) :
    Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)) := by
  have section_continuous : Continuous (fun matrix : BinaryRealGL =>
      ![matrix, 1]) := by
    apply continuous_pi
    intro position
    fin_cases position
    · exact continuous_id
    · exact continuous_const
  have continuous := (smooth_continuous smooth).comp section_continuous
  simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, atInfinity_one, binaryRightTranslation_one, Module.End.one_apply]
    using continuous

theorem cohomological_exists_continuous_nonzero_H1 (cusp : CuspidalRepresentation)
    (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree),
      groupCohomology.H1π (binaryCuspidalRep cusp degree) cycle ≠ 0 ∧
      Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)) ∧
      Smooth (fun point : Fin 2 → BinaryRealGL =>
        binaryHilbertEmbedding cusp basis
          (binaryRightTranslation cusp degree (atInfinity (point 1)) (cycle (point 0)))) ∧
      ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧
        ∀ element : level, ∀ matrix,
          binaryRightTranslation cusp degree (atFinite element.val) (cycle matrix) =
            cycle matrix := by
  rcases cohomological with ⟨cycle, cuspidal, smooth_lifts, level_fixed, cocycle, nonboundary⟩
  let group_cycle := binaryCocycleToGroupCocycle cusp cycle cuspidal cocycle
  have smooth : Smooth (fun point : Fin 2 → BinaryRealGL =>
      binaryHilbertEmbedding cusp basis
        (binaryRightTranslation cusp degree (atInfinity (point 1)) (group_cycle (point 0)))) :=
    binarySmoothCoordinates_smooth cusp basis _ smooth_lifts
  refine ⟨group_cycle, ?_, binaryHilbertCocycle_continuous cusp basis _ smooth, smooth, ?_⟩
  · exact fun zero => nonboundary
      ((binaryCocycleToGroupCocycle_H1_zero_iff cusp cycle cuspidal cocycle).mp zero)
  · rcases level_fixed with ⟨level, level_open, level_compact, fixed⟩
    refine ⟨level, level_open, level_compact, ?_⟩
    intro element matrix
    apply Subtype.ext
    funext argument
    exact fixed element matrix argument

theorem binaryHilbertCocycle_compact_primitive (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)))
    {compact : Type*} [Group compact] [TopologicalSpace compact] [CompactSpace compact]
    [MeasurableSpace compact] [OpensMeasurableSpace compact] [MeasurableMul compact]
    (inclusion : compact →* BinaryRealGL) (inclusion_continuous : Continuous inclusion)
    (measure : MeasureTheory.Measure compact) [MeasureTheory.IsProbabilityMeasure measure]
    [measure.IsMulLeftInvariant] (element : compact) :
    binaryHilbertEmbedding cusp basis (cycle (inclusion element)) =
      binaryHilbertOperator cusp basis (inclusion element)
        (-(∫ argument, binaryHilbertEmbedding cusp basis (cycle (inclusion argument)) ∂measure)) -
      (-(∫ argument, binaryHilbertEmbedding cusp basis (cycle (inclusion argument)) ∂measure)) := by
  apply compactCocycle_average measure
    (fun argument => binaryHilbertOperator cusp basis (inclusion argument))
    (fun argument => binaryHilbertEmbedding cusp basis (cycle (inclusion argument)))
    _ (continuous.comp inclusion_continuous) element
  intro first second
  rw [map_mul]
  exact binaryHilbertCocycle_identity cusp basis cycle (inclusion first) (inclusion second)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
