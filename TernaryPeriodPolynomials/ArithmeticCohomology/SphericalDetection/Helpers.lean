module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

@[simp] theorem atInfinity_one {dimension : ℕ} :
    atInfinity (1 : GeneralLinearGroup (Fin dimension) ℝ) = 1 := by
  apply Units.ext
  funext row column
  change ((1 : Matrix (Fin dimension) (Fin dimension) ℝ) row column,
    (1 : Matrix (Fin dimension) (Fin dimension) FiniteAdeles) row column) =
      (1 : Matrix (Fin dimension) (Fin dimension) Adeles) row column
  by_cases equal : row = column <;> simp only [Matrix.one_apply, equal, ite_true, ite_false] <;>
    rfl

theorem classOf_eq_zero_iff {group coefficient : Type} [Group group]
    [AddCommGroup coefficient] [Module ℂ coefficient]
    (level : Subgroup group) (representation : Representation ℂ group coefficient)
    (cycle : cocycles level representation) :
    classOf level representation cycle = 0 ↔
      ∃ primitive : cochains level representation 1,
        differentialOne level representation primitive = cycle.val := by
  change Submodule.Quotient.mk cycle = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨primitive, equality⟩
    exact ⟨primitive, congrArg Subtype.val equality⟩
  · rintro ⟨primitive, equality⟩
    exact ⟨primitive, Subtype.ext equality⟩

theorem badPlaneRepresentative_vanishesOnGood {degree : ℕ}
    (data : InducingData degree) (coordinate : boundarySummand data .plane)
    (supported : BadPlaneRepresentative data coordinate) :
    VanishesOnGood degree data.chi .plane coordinate.val := by
  rcases supported with ⟨source, cycle, _, evaluates, represents, support⟩
  refine ⟨cycle, represents, 0, ?_⟩
  intro vertices flag good
  induction flag using Quotient.inductionOn with
  | h representative =>
    rw [evaluates vertices representative]
    simpa using support
      (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
      representative good 1

theorem badPlaneRepresentative_eq_zero_of_source_eq_zero {degree : ℕ}
    (data : InducingData degree) (coordinate : boundarySummand data .plane)
    (source : SourceCochain degree) (cycle : MaximalCycles degree data.chi .plane)
    (evaluates : Evaluates data .plane source cycle)
    (represents : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle =
        coordinate.val)
    (source_zero : source = 0) : coordinate = 0 := by
  have cycle_zero : cycle = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices flag
    induction flag using Quotient.inductionOn with
    | h representative =>
      simpa [source_zero] using evaluates vertices representative
  apply Subtype.ext
  rw [← represents, cycle_zero, map_zero]
  rfl

theorem vanishesOnGood_iff_for_representative {degree : ℕ}
    (character : RankOneCharacter) (side : Side)
    (cycle : MaximalCycles degree character side) :
    VanishesOnGood degree character side
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side) cycle) ↔
      ∃ primitive : MaximalCochains degree character side 1,
        ∀ vertices flag, GoodFlag side flag →
          cycle.val.val vertices flag =
            (differentialOne rationalLevel
              (flagRepresentation (rationalCoefficientComponent degree character) side)
              primitive).val vertices flag := by
  constructor
  · rintro ⟨other_cycle, same_class, primitive, vanishing⟩
    have difference_zero : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        (cycle - other_cycle) = 0 := by
      rw [map_sub, same_class, sub_self]
    rcases (classOf_eq_zero_iff _ _ _).mp difference_zero with
      ⟨correction, corrects⟩
    refine ⟨correction + primitive, ?_⟩
    intro vertices flag good
    have pointwise := congrArg
      (fun cochain : MaximalCochains degree character side 2 => cochain.val vertices flag)
      corrects
    change _ = cycle.val.val vertices flag - other_cycle.val.val vertices flag at pointwise
    change cycle.val.val vertices flag = _
    rw [map_add]
    change cycle.val.val vertices flag =
      (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        correction).val vertices flag +
      (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        primitive).val vertices flag
    rw [pointwise, ← vanishing vertices flag good, sub_add_cancel]
  · rintro ⟨primitive, vanishing⟩
    exact ⟨cycle, rfl, primitive, vanishing⟩

theorem localBadPlaneEntry_detects_value
    (local_entry : LocalBadPlaneEntry) (measure : MeasureTheory.Measure ℚ_[3])
    (haar : measure.IsAddHaarMeasure) (normalized : measure {scalar | ‖scalar‖ ≤ 1} = 1)
    (section_value : LocalThreeGL → ℂ) (support : LocalBadPlaneSupport section_value)
    (invariant : LocalRightInvariant section_value)
    (integral_zero :
      (∫ parameter, localBadPlaneIntegrand section_value parameter
        ∂(measure.prod measure)) = 0) : section_value 1 = 0 := by
  have entry := (local_entry measure haar normalized section_value support invariant).2
  rw [integral_zero] at entry
  have factor_nonzero : (1 / 9 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp entry.symm).resolve_left factor_nonzero

theorem realizesStandard_good_coboundary {degree : ℕ}
    (data : InducingData degree)
    (operator : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (realizes : RealizesStandard data operator)
    (coordinate : boundarySummand data .plane)
    (source : SourceCochain degree)
    (cycle : MaximalCycles degree data.chi .plane)
    (source_cycle : IsSourceCocycle data .plane source)
    (evaluates : Evaluates data .plane source cycle)
    (represents : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle =
        coordinate.val)
    (good_zero : VanishesOnGood degree data.chi .line (operator coordinate).val) :
    ∃ (flat standard : ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
      (target_cycle : MaximalCycles degree data.chi .line)
      (primitive : MaximalCochains degree data.chi .line 1),
      (∀ vertices monomial, IsFlatSection data
        (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)) ∧
      flat cohomologicalPoint = source ∧
      (∀ vertices monomial, IsStandardContinuation
        (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
        (fun parameter argument => (standard parameter vertices argument).val.coeff monomial)) ∧
      (∀ vertices argument monomial, AnalyticAt ℂ
        (fun parameter => (standard parameter vertices argument).val.coeff monomial) cohomologicalPoint) ∧
      IsSourceCocycle data .line (standard cohomologicalPoint) ∧
      Evaluates data .line (standard cohomologicalPoint) target_cycle ∧
      (operator coordinate).val = classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
        target_cycle ∧
      ∀ vertices representative, GoodFlag .line (QuotientGroup.mk representative) →
        standard cohomologicalPoint
          (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
          (rationalGroup representative⁻¹) =
            (differentialOne rationalLevel
              (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
              primitive).val vertices (QuotientGroup.mk representative) := by
  have membership : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle ∈
        boundarySummand data .plane := by
    rw [represents]
    exact coordinate.property
  have realized := realizes source source_cycle cycle evaluates membership
  rcases realized with
    ⟨flat, standard, flat_sections, endpoint, continuations, analytic,
      standard_cycle, target_cycle, target_evaluates, target_represents⟩
  have same_coordinate :
      (⟨classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle,
        membership⟩ : boundarySummand data .plane) = coordinate :=
    Subtype.ext represents
  rw [same_coordinate] at target_represents
  rw [target_represents] at good_zero
  rcases (vanishesOnGood_iff_for_representative data.chi .line target_cycle).mp good_zero with
    ⟨primitive, coboundary⟩
  refine ⟨flat, standard, target_cycle, primitive, flat_sections, endpoint,
    continuations, analytic, standard_cycle, target_evaluates, target_represents, ?_⟩
  intro vertices representative good
  rw [← target_evaluates vertices representative]
  exact coboundary vertices (QuotientGroup.mk representative) good

theorem coordinate_eq_zero_of_representative_coboundary {degree : ℕ}
    (data : InducingData degree) (coordinate : boundarySummand data .plane)
    (cycle : MaximalCycles degree data.chi .plane)
    (represents : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle =
        coordinate.val)
    (primitive : MaximalCochains degree data.chi .plane 1)
    (coboundary : differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
      primitive = cycle.val) : coordinate = 0 := by
  apply Subtype.ext
  change coordinate.val = 0
  rw [← represents]
  exact (classOf_eq_zero_iff _ _ cycle).mpr ⟨primitive, coboundary⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
