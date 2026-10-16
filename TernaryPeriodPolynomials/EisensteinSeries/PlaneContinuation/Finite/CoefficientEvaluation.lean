module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.BinarySymmetry

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteCoefficientEvaluation

def integral {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (boxes : FlatProfilePackages.Boxes) (parameter : ℂ) (point : FiniteGL) (evaluation : BinaryAdelicGL) : ℂ :=
  ∫ binary : BinaryFiniteGL,
    boxes.test (finite (FrameProfile.frame (atFinite point) * (atFinite binary).val)) *
      innerCharacter data parameter (GeneralLinearGroup.det (atFinite binary)) *
      data.cusp.realize vector (evaluation * atFinite binary) ∂BinaryProductHaar.finiteMeasure

theorem frame_shift (point : FiniteGL) (matrix : BinaryFiniteGL) :
    FrameProfile.frame (atFinite (planeLevi matrix 1 * point)) =
      FrameProfile.frame (atFinite point) * (atFinite matrix)⁻¹.val := by
  rw [atFinite_mul, ← planeLevi_atFinite, ← inv_inv (atFinite matrix), FrameProfile.frame_levi]
  rw [inv_inv]

theorem finite_shift {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (boxes : FlatProfilePackages.Boxes) (parameter : ℂ) (point : FiniteGL) (evaluation : BinaryFiniteGL) :
    integral data vector boxes parameter point (atFinite evaluation) =
      (innerCharacter data parameter (GeneralLinearGroup.det (atFinite evaluation)))⁻¹ *
        coefficientIntegral data vector boxes.test parameter (planeLevi evaluation 1 * point) := by
  have inverse : atFinite evaluation⁻¹ = (atFinite evaluation)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [← atFinite_mul, mul_inv_cancel, CompactAveraging.atFinite_one]
  unfold integral coefficientIntegral
  rw [← integral_mul_left_eq_self (μ := BinaryProductHaar.finiteMeasure)
    (fun binary : BinaryFiniteGL => boxes.test (finite (FrameProfile.frame (atFinite point) * (atFinite binary).val)) *
      innerCharacter data parameter (GeneralLinearGroup.det (atFinite binary)) *
      data.cusp.realize vector (atFinite evaluation * atFinite binary)) evaluation⁻¹]
  simp only [atFinite_mul, inverse, map_mul, map_inv, Units.val_mul, ← Matrix.mul_assoc,
    mul_inv_cancel_left]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro binary
  simp only [kernel, frame_shift]
  ring

theorem real_shift {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (boxes : FlatProfilePackages.Boxes) (parameter : ℂ) (point : FiniteGL)
    (finiteEvaluation : BinaryFiniteGL) (realEvaluation : BinaryRealGL) :
    integral data vector boxes parameter point (atFinite finiteEvaluation * atInfinity realEvaluation) =
      integral data (smoothTranslate data.cusp realEvaluation vector) boxes parameter point (atFinite finiteEvaluation) := by
  unfold integral
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro binary
  dsimp only
  have commute : atFinite finiteEvaluation * atInfinity realEvaluation * atFinite binary =
      atFinite finiteEvaluation * atFinite binary * atInfinity realEvaluation := by
    rw [mul_assoc, ← atFinite_atInfinity_commute, ← mul_assoc]
  rw [smoothTranslate_realize, commute]

theorem inner_meromorphic {degree : ℕ} (data : InducingData degree) (scalar : Adelesˣ) (parameter : ℂ) :
    MeromorphicAt (fun parameter => innerCharacter data parameter scalar) parameter := by
  have expression : (fun parameter => innerCharacter data parameter scalar) =
      fun parameter => (data.chi.toMonoidHom scalar)⁻¹ *
        Complex.exp ((((degree : ℂ) / 2 + 3 + parameter) * (Real.log (adeleNorm scalar : ℝ) : ℂ))) := by
    funext parameter
    change (data.chi.toMonoidHom scalar)⁻¹ * Complex.exp (_ * _) = _
    congr 2
    simp only [binaryInductionExponent, inductionExponent]
    ring
  rw [expression]
  apply AnalyticAt.meromorphicAt
  fun_prop

theorem exists_meromorphic {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (boxes : FlatProfilePackages.Boxes) (point : FiniteGL) (evaluation : BinaryAdelicGL) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : ℂ, (1 - (degree : ℝ)) / 2 < parameter.re →
        continuation parameter = integral data vector boxes parameter point evaluation := by
  let realEvaluation := (BinaryProductHaar.combineEquiv.symm evaluation).1
  let finiteEvaluation := (BinaryProductHaar.combineEquiv.symm evaluation).2
  have split : evaluation = atFinite finiteEvaluation * atInfinity realEvaluation :=
    (BinaryProductHaar.combineEquiv.apply_symm_apply evaluation).symm.trans
      (BinaryProductHaar.combine_eq realEvaluation finiteEvaluation)
  have translatedFixed : (smoothTranslate data.cusp realEvaluation vector).val ∈ fixedSubspace data.cusp finiteCongruence :=
    fixedSubspace_real_stable data.cusp finiteCongruence realEvaluation vector.val fixed
  obtain ⟨continuation, meromorphic, equality⟩ := BinaryOrbitCoefficients.exists_boxes_meromorphic data
    (smoothTranslate data.cusp realEvaluation vector) translatedFixed boxes (planeLevi finiteEvaluation 1 * point)
  refine ⟨fun parameter => (innerCharacter data parameter (GeneralLinearGroup.det (atFinite finiteEvaluation)))⁻¹ * continuation parameter,
    fun parameter => (inner_meromorphic data _ parameter).inv.mul (meromorphic parameter), ?_⟩
  intro parameter halfPlane
  dsimp only
  rw [split, real_shift, finite_shift, equality parameter halfPlane]

theorem recovery_exists_meromorphic {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : FiniteGL) (key : UniversalFiniteProfiles.Key data) (evaluation : BinaryAdelicGL) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : ℂ, (1 - (degree : ℝ)) / 2 < parameter.re →
        continuation parameter = ∫ binary : BinaryFiniteGL,
          RecoveryCoefficients.coefficient data parameter (atFinite point) key binary *
            data.cusp.realize vector (evaluation * atFinite binary) ∂BinaryProductHaar.finiteMeasure :=
  exists_meromorphic data vector fixed (UniversalFiniteProfiles.boxes data key) point evaluation

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteCoefficientEvaluation
