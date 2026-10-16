module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.Vectors

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic

variable {CoefficientRing : Type*} [CommRing CoefficientRing]

def planeCornerUnit (parabolicElement : planeParabolic CoefficientRing) : CoefficientRingˣ where
  val := parabolicElement.val.val 2 2
  inv := parabolicElement.val.inv 2 2
  val_inv := by
    have identityEntry := congrArg
      (fun matrix : Matrix (Fin 3) (Fin 3) CoefficientRing => matrix 2 2)
      parabolicElement.val.mul_inv
    simpa [Matrix.mul_apply, Fin.sum_univ_three, parabolicElement.property.1,
      parabolicElement.property.2] using identityEntry
  inv_val := by
    have identityEntry := congrArg
      (fun matrix : Matrix (Fin 3) (Fin 3) CoefficientRing => matrix 2 2)
      parabolicElement.val.mul_inv
    have cornerIdentity : parabolicElement.val.val 2 2 * parabolicElement.val.inv 2 2 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three, parabolicElement.property.1,
        parabolicElement.property.2] using identityEntry
    exact (mul_comm _ _).trans cornerIdentity

def planeBinaryBlock (parabolicElement : planeParabolic CoefficientRing) :
    Matrix.GeneralLinearGroup (Fin 2) CoefficientRing where
  val := fun row column => parabolicElement.val.val row.castSucc column.castSucc
  inv := fun row column => parabolicElement.val.inv row.castSucc column.castSucc
  val_inv := by
    have inverseParabolic := inPlane_inv parabolicElement.property
    have inverseZeroFirst : (parabolicElement.val.val)⁻¹ 2 0 = 0 := by
      simpa only [Matrix.GeneralLinearGroup.coe_inv] using inverseParabolic.1
    have inverseZeroSecond : (parabolicElement.val.val)⁻¹ 2 1 = 0 := by
      simpa only [Matrix.GeneralLinearGroup.coe_inv] using inverseParabolic.2
    apply Matrix.ext
    intro row column
    have identityEntry := congrArg
      (fun matrix : Matrix (Fin 3) (Fin 3) CoefficientRing =>
        matrix row.castSucc column.castSucc) parabolicElement.val.mul_inv
    change (∑ index : Fin 2, parabolicElement.val.val row.castSucc index.castSucc *
      parabolicElement.val.inv index.castSucc column.castSucc) =
        (if row = column then 1 else 0)
    fin_cases row <;> fin_cases column <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
        inverseZeroFirst, inverseZeroSecond] using identityEntry
  inv_val := by
    apply Matrix.ext
    intro row column
    have identityEntry := congrArg
      (fun matrix : Matrix (Fin 3) (Fin 3) CoefficientRing =>
        matrix row.castSucc column.castSucc) parabolicElement.val.inv_mul
    change (∑ index : Fin 2, parabolicElement.val.inv row.castSucc index.castSucc *
      parabolicElement.val.val index.castSucc column.castSucc) =
        (if row = column then 1 else 0)
    fin_cases row <;> fin_cases column <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
        parabolicElement.property.1, parabolicElement.property.2] using identityEntry

theorem planeParabolic_factorization (parabolicElement : planeParabolic CoefficientRing) :
    parabolicElement.val =
      planeUnipotent
        (parabolicElement.val.val 0 2 * (planeCornerUnit parabolicElement).inv)
        (parabolicElement.val.val 1 2 * (planeCornerUnit parabolicElement).inv) *
      planeLevi (planeBinaryBlock parabolicElement) (planeCornerUnit parabolicElement) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  have cornerInverse : (parabolicElement.val.val)⁻¹ 2 2 * parabolicElement.val.val 2 2 = 1 := by
    have cornerIdentity := (planeCornerUnit parabolicElement).inv_val
    change (parabolicElement.val⁻¹).val 2 2 * parabolicElement.val.val 2 2 = 1 at cornerIdentity
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using cornerIdentity
  fin_cases row <;> fin_cases column <;>
    simp [planeUnipotent, planeLevi, planeBlock, planeBinaryBlock, planeCornerUnit,
      Matrix.mul_apply, Fin.sum_univ_three, parabolicElement.property.1,
      parabolicElement.property.2, mul_assoc, cornerInverse]

theorem induced_planeParabolic_formula {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (parabolicElement : planeParabolic Adeles) (basePoint : AdelicGL) :
    sectionFunction (parabolicElement.val * basePoint) =
      data.chi.toMonoidHom (planeCornerUnit parabolicElement) *
        normPower (planeCornerUnit parabolicElement) (-2 * inductionExponent .plane parameter) *
        (normPower (Matrix.GeneralLinearGroup.det (planeBinaryBlock parabolicElement))
          (binaryInductionExponent degree .plane parameter) *
          data.cusp.realize (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector inducedSection basePoint)
            (planeBinaryBlock parabolicElement)) := by
  rw [planeParabolic_factorization parabolicElement, mul_assoc,
    inducedSection.2.2.2.1, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.induced_planeLevi_scalar inducedSection,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.induced_eq_planeCuspVector inducedSection]

theorem planeCuspVector_planeParabolic {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (parabolicElement : planeParabolic Adeles) (basePoint : AdelicGL) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector inducedSection (parabolicElement.val * basePoint) =
      (data.chi.toMonoidHom (planeCornerUnit parabolicElement) *
        normPower (planeCornerUnit parabolicElement) (-2 * inductionExponent .plane parameter)) •
      (normPower (Matrix.GeneralLinearGroup.det (planeBinaryBlock parabolicElement))
          (binaryInductionExponent degree .plane parameter) •
        (⟨data.cusp.π (planeBinaryBlock parabolicElement)
            (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector inducedSection basePoint).val,
          data.cusp.smooth_stable (planeBinaryBlock parabolicElement) _
            (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector inducedSection basePoint).property⟩ :
          data.cusp.smooth)) := by
  rw [planeParabolic_factorization parabolicElement, mul_assoc,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector_unipotent inducedSection,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.planeLevi_split, mul_assoc,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector_scalar inducedSection,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector_binaryLevi inducedSection]

theorem flatSection_planeParabolic_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (parabolicElement : planeParabolic Adeles) (compactElement : AdelicGL)
    (compactMembership : inMaximalCompact compactElement) (parameter : ℂ) :
    sectionFamily parameter (parabolicElement.val * compactElement) =
      (normPower (planeCornerUnit parabolicElement)
          (-2 * (parameter - cohomologicalPoint) / 3) *
        normPower (Matrix.GeneralLinearGroup.det (planeBinaryBlock parabolicElement))
          ((parameter - cohomologicalPoint) / 3)) *
      sectionFamily cohomologicalPoint (parabolicElement.val * compactElement) := by
  rw [induced_planeParabolic_formula (flatSection.1 parameter),
    induced_planeParabolic_formula (flatSection.1 cohomologicalPoint),
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.flatSection_planeCuspVector_eq flatSection parameter
      compactElement compactMembership]
  have scalarExponent : -2 * inductionExponent .plane parameter =
      -2 * (parameter - cohomologicalPoint) / 3 +
        -2 * inductionExponent .plane cohomologicalPoint := by
    simp only [inductionExponent]
    ring
  have binaryExponent : binaryInductionExponent degree .plane parameter =
      (parameter - cohomologicalPoint) / 3 +
        binaryInductionExponent degree .plane cohomologicalPoint := by
    simp only [binaryInductionExponent, inductionExponent]
    ring
  rw [scalarExponent, binaryExponent, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_add,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_add]
  ring

noncomputable def planeHeightLog (parabolicElement : planeParabolic Adeles) : ℝ :=
  (Real.log (adeleNorm (Matrix.GeneralLinearGroup.det (planeBinaryBlock parabolicElement)) : ℝ) -
    2 * Real.log (adeleNorm (planeCornerUnit parabolicElement) : ℝ)) / 3

theorem flatSection_planeParabolic_exp {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (parabolicElement : planeParabolic Adeles) (compactElement : AdelicGL)
    (compactMembership : inMaximalCompact compactElement) (parameter : ℂ) :
    sectionFamily parameter (parabolicElement.val * compactElement) =
      Complex.exp ((parameter - cohomologicalPoint) *
        (planeHeightLog parabolicElement : ℂ)) *
      sectionFamily cohomologicalPoint (parabolicElement.val * compactElement) := by
  rw [flatSection_planeParabolic_parameter flatSection parabolicElement compactElement
    compactMembership, normPower, normPower, ← Complex.exp_add]
  congr 2
  simp only [planeHeightLog, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem norm_flatSection_planeParabolic {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (parabolicElement : planeParabolic Adeles) (compactElement : AdelicGL)
    (compactMembership : inMaximalCompact compactElement) (parameter : ℂ) :
    ‖sectionFamily parameter (parabolicElement.val * compactElement)‖ =
      Real.exp ((parameter.re - cohomologicalPoint.re) * planeHeightLog parabolicElement) *
        ‖sectionFamily cohomologicalPoint (parabolicElement.val * compactElement)‖ := by
  rw [flatSection_planeParabolic_exp flatSection parabolicElement compactElement
    compactMembership, norm_mul, Complex.norm_exp]
  simp

theorem det_planeParabolic (parabolicElement : planeParabolic CoefficientRing) :
    Matrix.GeneralLinearGroup.det parabolicElement.val =
      Matrix.GeneralLinearGroup.det (planeBinaryBlock parabolicElement) *
        planeCornerUnit parabolicElement := by
  apply Units.ext
  change parabolicElement.val.val.det =
    (planeBinaryBlock parabolicElement).val.det * (planeCornerUnit parabolicElement).val
  rw [Matrix.det_fin_two (planeBinaryBlock parabolicElement).val]
  simp only [planeBinaryBlock, planeCornerUnit, Matrix.det_fin_three,
    parabolicElement.property.1, parabolicElement.property.2, mul_zero, sub_zero,
    add_zero, Fin.castSucc_zero, Fin.castSucc_one]
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic
