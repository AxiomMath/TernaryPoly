module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.Haar

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral

noncomputable def outerCharacter {degree : ℕ} (data : InducingData degree) (parameter : ℂ) : Adelesˣ →* ℂ where
  toFun scalar := data.chi.toMonoidHom scalar * normPower scalar (-2 * inductionExponent .plane parameter)
  map_one' := by rw [map_one, normPower_one, mul_one]
  map_mul' first second := by rw [map_mul, normPower_mul]; ring

noncomputable def innerCharacter {degree : ℕ} (data : InducingData degree) (parameter : ℂ) : Adelesˣ →* ℂ where
  toFun scalar := (data.chi.toMonoidHom scalar)⁻¹ *
    normPower scalar (binaryInductionExponent degree .plane parameter + 2 * inductionExponent .plane parameter)
  map_one' := by rw [map_one, inv_one, normPower_one, mul_one]
  map_mul' first second := by rw [map_mul, mul_inv, normPower_mul]; ring

theorem characters_product {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (scalar : Adelesˣ) :
    outerCharacter data parameter scalar * innerCharacter data parameter scalar =
      normPower scalar (binaryInductionExponent degree .plane parameter) := by
  have nonzero : data.chi.toMonoidHom scalar ≠ 0 := by
    intro vanishing
    have unitary := data.chi.unitary scalar
    simp only [vanishing, norm_zero, zero_ne_one] at unitary
  change (data.chi.toMonoidHom scalar * normPower scalar _) *
    ((data.chi.toMonoidHom scalar)⁻¹ * normPower scalar _) = _
  rw [mul_mul_mul_comm, mul_inv_cancel₀ nonzero, one_mul, ← normPower_add]
  congr 1
  ring

theorem det_planeLevi {ring : Type*} [CommRing ring] (binary : GeneralLinearGroup (Fin 2) ring)
    (scalar : ringˣ) : GeneralLinearGroup.det (planeLevi binary scalar) = GeneralLinearGroup.det binary * scalar := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, planeLevi, planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem det_planeUnipotent {ring : Type*} [CommRing ring] (first second : ring) :
    GeneralLinearGroup.det (planeUnipotent first second) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, planeUnipotent, Matrix.det_fin_three]

noncomputable def raw (test : Rectangular Adeles → ℂ) (weight : Adelesˣ →* ℂ)
    (data : CuspidalRepresentation) (vector : data.smooth) (point : AdelicGL) : ℂ :=
  ∫ binary, kernel test point binary * weight (GeneralLinearGroup.det binary) * data.realize vector binary
    ∂BinaryHaar.measure

noncomputable def orbit (test : Rectangular Adeles → ℂ) (weight : Adelesˣ →* ℂ)
    (data : CuspidalRepresentation) (vector : data.smooth) (point : AdelicGL) (left : BinaryAdelicGL) : ℂ :=
  ∫ binary, kernel test point binary * weight (GeneralLinearGroup.det binary) * data.realize vector (left * binary)
    ∂BinaryHaar.measure

theorem raw_planeLevi (test : Rectangular Adeles → ℂ) (weight : Adelesˣ →* ℂ)
    (data : CuspidalRepresentation) (vector : data.smooth) (point : AdelicGL)
    (left : BinaryAdelicGL) (scalar : Adelesˣ) :
    raw test weight data vector (planeLevi left scalar * point) =
      weight (GeneralLinearGroup.det left) * orbit test weight data vector point left := by
  unfold raw orbit
  rw [← integral_mul_left_eq_self (fun binary => kernel test (planeLevi left scalar * point) binary *
    weight (GeneralLinearGroup.det binary) * data.realize vector binary) left]
  simp only [kernel_plane_levi, inv_mul_cancel_left, map_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => by ring)

theorem raw_planeUnipotent (test : Rectangular Adeles → ℂ) (weight : Adelesˣ →* ℂ)
    (data : CuspidalRepresentation) (vector : data.smooth) (point : AdelicGL) (first second : Adeles) :
    raw test weight data vector (planeUnipotent first second * point) = raw test weight data vector point := by
  simp only [raw, kernel_plane_unipotent]

noncomputable def sectionFunction {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) : ℂ :=
  outerCharacter data parameter (GeneralLinearGroup.det point) *
    raw test (innerCharacter data parameter) data.cusp vector point

theorem section_planeUnipotent {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (first second : Adeles) :
    sectionFunction data test vector parameter (planeUnipotent first second * point) =
      sectionFunction data test vector parameter point := by
  rw [sectionFunction, raw_planeUnipotent, map_mul, det_planeUnipotent, one_mul]
  rfl

theorem section_planeLevi {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (left : BinaryAdelicGL) (scalar : Adelesˣ) :
    sectionFunction data test vector parameter (planeLevi left scalar * point) =
      (data.chi.toMonoidHom scalar * normPower scalar (-2 * inductionExponent .plane parameter)) *
        normPower (GeneralLinearGroup.det left) (binaryInductionExponent degree .plane parameter) *
          (outerCharacter data parameter (GeneralLinearGroup.det point) *
            orbit test (innerCharacter data parameter) data.cusp vector point left) := by
  rw [sectionFunction, raw_planeLevi, map_mul, det_planeLevi, map_mul, map_mul]
  have cancellation := characters_product data parameter (GeneralLinearGroup.det left)
  calc
    _ = outerCharacter data parameter scalar *
        (outerCharacter data parameter (GeneralLinearGroup.det left) * innerCharacter data parameter (GeneralLinearGroup.det left)) *
        (outerCharacter data parameter (GeneralLinearGroup.det point) *
          orbit test (innerCharacter data parameter) data.cusp vector point left) := by ring
    _ = _ := by rw [cancellation]; rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
