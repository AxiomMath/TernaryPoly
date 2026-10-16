module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PeriodicIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BruhatSums

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ClosedCellIntegral

theorem binaryUnipotent_add {R : Type*} [CommRing R] (first second : R) :
    binaryUnipotent (first + second) = binaryUnipotent first * binaryUnipotent second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem map_binaryUnipotent {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (value : R) :
    Matrix.GeneralLinearGroup.map hom (binaryUnipotent value) =
      binaryUnipotent (hom value) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;> simp [binaryUnipotent]

theorem binaryUnipotent_det {R : Type*} [CommRing R] (value : R) :
    Matrix.GeneralLinearGroup.det (binaryUnipotent value) = 1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.det, binaryUnipotent, Matrix.det_fin_two]

theorem lineUnipotent_plane (first second : Adeles) :
    lineUnipotent first second =
      planeUnipotent second 0 * planeLevi (binaryUnipotent first) 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [upperUnipotent, planeUnipotent, planeLevi, planeBlock, binaryUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem induced_unipotent_cusp {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (argument : AdelicGL) :
    ∃ vector : data.cusp.smooth, ∀ first second : Adeles,
      function (lineUnipotent first second * argument) =
        data.cusp.realize vector (binaryUnipotent first) := by
  obtain ⟨vector, vectorEquality⟩ := induced.2.2.2.2.2 argument
  refine ⟨vector, ?_⟩
  intro first second
  rw [lineUnipotent_plane, mul_assoc, induced.2.2.2.1]
  have evaluated := congrFun vectorEquality (binaryUnipotent first)
  rw [binaryUnipotent_det] at evaluated
  simpa [normPower] using evaluated.symm

theorem cusp_periodic (data : CuspidalRepresentation) (vector : data.smooth)
    (rational : ℚ) (value : Adeles) :
    data.realize vector (binaryUnipotent (rationalAdele rational + value)) =
      data.realize vector (binaryUnipotent value) := by
  rw [binaryUnipotent_add, ← map_binaryUnipotent]
  exact data.leftRational (binaryUnipotent rational) vector (binaryUnipotent value)

theorem rational_linear_quasiMeasurePreserving (first second : ℚ)
    (nonzero : first ≠ 0 ∨ second ≠ 0) :
    MeasureTheory.Measure.QuasiMeasurePreserving (fun coordinates : Adeles × Adeles =>
      rationalAdele first * coordinates.1 + rationalAdele second * coordinates.2)
      radicalMeasure adeleMeasure := by
  by_cases firstZero : first = 0
  · subst first
    have secondNonzero := nonzero.resolve_left (not_ne_iff.mpr rfl)
    simpa only [map_zero, zero_mul, zero_add, Function.comp_def, radicalMeasure,
      PeriodicIntegral.scalingEquiv_apply, Units.val_mk0] using
      (PeriodicIntegral.scaling_preserves (Units.mk0 second secondNonzero)).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_snd (μ := adeleMeasure) (ν := adeleMeasure))
  · by_cases secondZero : second = 0
    · subst second
      simpa only [map_zero, zero_mul, add_zero, Function.comp_def, radicalMeasure,
        PeriodicIntegral.scalingEquiv_apply, Units.val_mk0] using
        (PeriodicIntegral.scaling_preserves (Units.mk0 first firstZero)).quasiMeasurePreserving.comp
          (Measure.quasiMeasurePreserving_fst (μ := adeleMeasure) (ν := adeleMeasure))
    · have scaling := (PeriodicIntegral.scaling_preserves (Units.mk0 first firstZero)).prod
        (PeriodicIntegral.scaling_preserves (Units.mk0 second secondZero))
      have shear := (measurePreserving_add_prod adeleMeasure adeleMeasure).comp scaling
      exact (Measure.quasiMeasurePreserving_fst (μ := adeleMeasure) (ν := adeleMeasure)).comp
        shear.quasiMeasurePreserving

theorem linear_cusp_integrable (function : Adeles → ℂ)
    (periodic : ∀ rational value, function (rationalAdele rational + value) = function value)
    (integrable : IntegrableOn function additiveDomain adeleMeasure)
    (bounded : ∃ bound : ℝ, ∀ value, ‖function value‖ ≤ bound)
    (first second : ℚ) (nonzero : first ≠ 0 ∨ second ≠ 0) :
    IntegrableOn (fun coordinates : Adeles × Adeles =>
      function (rationalAdele first * coordinates.1 + rationalAdele second * coordinates.2))
        (additiveDomain ×ˢ additiveDomain) radicalMeasure := by
  have measurable := PeriodicIntegral.aestronglyMeasurable_of_periodic_on function periodic
    integrable.aestronglyMeasurable
  have composed := measurable.comp_quasiMeasurePreserving
    (rational_linear_quasiMeasurePreserving first second nonzero)
  obtain ⟨bound, bounds⟩ := bounded
  exact Integrable.of_bound (composed.mono_measure Measure.restrict_le_self) bound
    (Filter.Eventually.of_forall fun coordinates => bounds _)

theorem linear_cusp_integral (function : Adeles → ℂ)
    (periodic : ∀ rational value, function (rationalAdele rational + value) = function value)
    (vanishes : (∫ value in additiveDomain, function value ∂adeleMeasure) = 0)
    (first second : ℚ) (nonzero : first ≠ 0 ∨ second ≠ 0)
    (integrable : IntegrableOn (fun coordinates : Adeles × Adeles =>
      function (rationalAdele first * coordinates.1 + rationalAdele second * coordinates.2))
        (additiveDomain ×ˢ additiveDomain) radicalMeasure) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      function (rationalAdele first * coordinates.1 + rationalAdele second * coordinates.2)
        ∂radicalMeasure) = 0 := by
  change (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      function (rationalAdele first * coordinates.1 + rationalAdele second * coordinates.2)
        ∂adeleMeasure.prod adeleMeasure) = 0
  rw [setIntegral_prod _ integrable]
  by_cases secondZero : second = 0
  · subst second
    have firstNonzero : first ≠ 0 := nonzero.resolve_right (not_ne_iff.mpr rfl)
    simp only [map_zero, zero_mul, add_zero]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Norms.additiveDomain_measure,
      ENNReal.toReal_one, one_smul]
    exact (PeriodicIntegral.integral_rational_mul function periodic
      (Units.mk0 first firstNonzero)).trans vanishes
  · have inner : ∀ firstCoordinate : Adeles,
        (∫ secondCoordinate in additiveDomain,
          function (rationalAdele first * firstCoordinate +
            rationalAdele second * secondCoordinate) ∂adeleMeasure) = 0 := by
      intro firstCoordinate
      simp_rw [add_comm (rationalAdele first * firstCoordinate)]
      exact (PeriodicIntegral.integral_affine function periodic (Units.mk0 second secondZero)
        (rationalAdele first * firstCoordinate)).trans vanishes
    simp_rw [inner]
    exact integral_zero _ _

theorem lineUnipotent_lineLevi (matrix : BinaryAdelicGL) (first second : Adeles) :
    lineUnipotent first second * lineLevi 1 matrix =
      lineLevi 1 matrix * lineUnipotent
        (first * matrix.val 0 0 + second * matrix.val 1 0)
        (first * matrix.val 0 1 + second * matrix.val 1 1) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [upperUnipotent, lineLevi_val, Matrix.mul_apply, Fin.sum_univ_three]

theorem lineLevi_inverse_unipotent (matrix : BinaryAdelicGL) (first second : Adeles) :
    (lineLevi 1 matrix)⁻¹ * lineUnipotent first second =
      lineUnipotent (first * matrix.val 0 0 + second * matrix.val 1 0)
        (first * matrix.val 0 1 + second * matrix.val 1 1) * (lineLevi 1 matrix)⁻¹ := by
  calc
    _ = (lineLevi 1 matrix)⁻¹ *
        (lineUnipotent first second * lineLevi 1 matrix) * (lineLevi 1 matrix)⁻¹ := by
          simp [mul_assoc]
    _ = _ := by rw [lineUnipotent_lineLevi]; simp

theorem first_column_nonzero (matrix : BinaryRationalGL) :
    matrix.val 0 0 ≠ 0 ∨ matrix.val 1 0 ≠ 0 := by
  by_contra vanishes
  push Not at vanishes
  have inverseEquality := congrArg (fun value : Matrix (Fin 2) (Fin 2) ℚ => value 0 0)
    matrix.inv_val
  simp [Matrix.mul_apply, Fin.sum_univ_two, vanishes.1, vanishes.2] at inverseEquality

theorem closed_integrand_cusp {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (matrix : BinaryRationalGL) :
    ∃ vector : data.cusp.smooth, ∀ coordinates : Adeles × Adeles,
      eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument)
          (QuotientGroup.mk (lineLevi 1 matrix)) =
      data.cusp.realize vector (binaryUnipotent
        (rationalAdele (matrix.val 0 0) * coordinates.1 +
          rationalAdele (matrix.val 1 0) * coordinates.2)) := by
  let adelicMatrix := Matrix.GeneralLinearGroup.map rationalAdele matrix
  obtain ⟨vector, vectorEquality⟩ := induced_unipotent_cusp data parameter
    (extension parameter) induced ((lineLevi 1 adelicMatrix)⁻¹ * argument)
  refine ⟨vector, ?_⟩
  intro coordinates
  rw [RationalEisenstein.eisensteinSummand_mk data extension parameter induced, map_inv]
  change extension parameter
    ((Matrix.GeneralLinearGroup.map rationalAdele (lineLevi 1 matrix))⁻¹ *
      (lineUnipotent coordinates.1 coordinates.2 * argument)) = _
  rw [LineDecomposition.map_lineLevi, map_one, ← mul_assoc, lineLevi_inverse_unipotent,
    mul_assoc, vectorEquality]
  apply congrArg (fun value : Adeles => data.cusp.realize vector (binaryUnipotent value))
  change coordinates.1 * rationalAdele (matrix.val 0 0) +
    coordinates.2 * rationalAdele (matrix.val 1 0) = _
  ring

theorem closed_representative_integral {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (matrix : BinaryRationalGL)
    (integrable : IntegrableOn (fun coordinates : Adeles × Adeles =>
      eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument)
          (QuotientGroup.mk (lineLevi 1 matrix)))
      (additiveDomain ×ˢ additiveDomain) radicalMeasure) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument)
          (QuotientGroup.mk (lineLevi 1 matrix)) ∂radicalMeasure) = 0 := by
  obtain ⟨vector, vectorEquality⟩ := closed_integrand_cusp data extension parameter
    induced argument matrix
  simp_rw [vectorEquality] at integrable ⊢
  apply linear_cusp_integral (fun value => data.cusp.realize vector (binaryUnipotent value))
    (cusp_periodic data.cusp vector) _ _ _ (first_column_nonzero matrix) integrable
  simpa only [mul_one] using (data.cusp.cuspidal vector 1).2

theorem closed_representative_integrable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (matrix : BinaryRationalGL) :
    IntegrableOn (fun coordinates : Adeles × Adeles =>
      eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument)
          (QuotientGroup.mk (lineLevi 1 matrix)))
      (additiveDomain ×ˢ additiveDomain) radicalMeasure := by
  obtain ⟨vector, vectorEquality⟩ := closed_integrand_cusp data extension parameter
    induced argument matrix
  simp_rw [vectorEquality]
  apply linear_cusp_integrable (fun value => data.cusp.realize vector (binaryUnipotent value))
    (cusp_periodic data.cusp vector) _ _ _ _ (first_column_nonzero matrix)
  · simpa only [mul_one] using (data.cusp.cuspidal vector 1).1
  · obtain ⟨bound, bounds⟩ := data.cusp.bounded vector
    exact ⟨bound, fun _ => bounds _⟩

theorem closedFlag_integrable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (flag : BruhatSums.ClosedFlags) :
    IntegrableOn (fun coordinates : Adeles × Adeles =>
      eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument) flag.val)
      (additiveDomain ×ˢ additiveDomain) radicalMeasure := by
  obtain ⟨matrix, equality⟩ := BruhatCells.closedFlag_representative flag.val flag.property
  rw [equality]
  exact closed_representative_integrable data extension parameter induced argument matrix

theorem closedFlag_integral {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (flag : BruhatSums.ClosedFlags) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument) flag.val ∂radicalMeasure) = 0 := by
  have integrable := closedFlag_integrable data extension parameter induced argument flag
  obtain ⟨matrix, equality⟩ := BruhatCells.closedFlag_representative flag.val flag.property
  rw [equality] at integrable ⊢
  exact closed_representative_integral data extension parameter induced argument matrix integrable

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ClosedCellIntegral
