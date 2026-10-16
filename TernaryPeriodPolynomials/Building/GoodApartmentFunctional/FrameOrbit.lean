module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.Presentation

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit

noncomputable section

def referenceIntegral : IntegralGL3 :=
  ⟨!![1,0,0;0,1,0;1,1,1], !![1,0,0;0,1,0;-1,-1,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def referenceFrame : NormalizedFrames :=
  ⟨referenceIntegral, by intro column; fin_cases column <;> rfl⟩

def frameToLevel (frame : NormalizedFrames) : arithmeticLevel :=
  ⟨frame.val * referenceIntegral⁻¹, by
    change lastRow ᵥ* (GeneralLinearGroup.map (Int.castRingHom (ZMod 3))
      (frame.val * referenceIntegral⁻¹)).val = lastRow
    funext column
    fin_cases column <;>
      simp [lastRow, Pi.single_apply, Matrix.vecMul, dotProduct, Matrix.mul_apply,
        Fin.sum_univ_three, referenceIntegral, frame.property]⟩

def levelToFrame (groupElement : arithmeticLevel) : NormalizedFrames :=
  translateNormalizedFrame groupElement referenceFrame

theorem levelToFrame_frameToLevel (frame : NormalizedFrames) :
    levelToFrame (frameToLevel frame) = frame := by
  apply Subtype.ext
  exact inv_mul_cancel_right frame.val referenceIntegral

theorem frameToLevel_levelToFrame (groupElement : arithmeticLevel) :
    frameToLevel (levelToFrame groupElement) = groupElement := by
  apply Subtype.ext
  exact mul_inv_cancel_right groupElement.val referenceIntegral

def normalizedFramesEquivLevel : NormalizedFrames ≃ arithmeticLevel where
  toFun := frameToLevel
  invFun := levelToFrame
  left_inv := levelToFrame_frameToLevel
  right_inv := frameToLevel_levelToFrame

theorem frameToLevel_translate (groupElement : arithmeticLevel) (frame : NormalizedFrames) :
    frameToLevel (translateNormalizedFrame groupElement frame) =
      groupElement * frameToLevel frame := by
  apply Subtype.ext
  exact mul_assoc groupElement.val frame.val referenceIntegral⁻¹

theorem normalizedApartment_orbit (frame : NormalizedFrames) :
    normalizedApartment frame =
      goodCycleAction ⟨rationalInclusion (frameToLevel frame),
        MonoidHom.mem_range.mpr ⟨frameToLevel frame, rfl⟩⟩
        (normalizedApartment referenceFrame) := by
  apply Subtype.ext
  have translation := normalizedApartment_translate (frameToLevel frame) referenceFrame
  rw [show translateNormalizedFrame (frameToLevel frame) referenceFrame = frame from
    levelToFrame_frameToLevel frame] at translation
  exact translation

theorem normalizedFrameEvaluation_orbit {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (frame : NormalizedFrames) :
    normalizedFrameEvaluation polynomial frame =
      rationalCoefficientComponent degree trivialCharacter (rationalInclusion (frameToLevel frame))
        (normalizedFrameEvaluation polynomial referenceFrame) := by
  have translation := normalizedFrameEvaluation_translate polynomial (frameToLevel frame)
    referenceFrame
  rw [show translateNormalizedFrame (frameToLevel frame) referenceFrame = frame from
    levelToFrame_frameToLevel frame] at translation
  exact translation.trans
    (TernaryPeriodPolynomials.GoodApartmentFunctional.Descent.rationalCoefficient_integral (frameToLevel frame).val
      (normalizedFrameEvaluation polynomial referenceFrame)).symm

theorem normalizedFrameEvaluation_reference {degree : ℕ}
    (polynomial : HomogeneousPoly degree) :
    (normalizedFrameEvaluation polynomial referenceFrame).val =
      MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1,
        MvPolynomial.X 2 - MvPolynomial.X 0 - MvPolynomial.X 1] polynomial.val := by
  rw [normalizedFrameEvaluation_coe]
  have determinant : (GeneralLinearGroup.det referenceIntegral : ℤ) = 1 := by
    simp [GeneralLinearGroup.val_det_apply, referenceIntegral, Matrix.det_fin_three]
  have inverse : (GeneralLinearGroup.map (Int.castRingHom ℂ) referenceIntegral)⁻¹.val =
      !![1,0,0;0,1,0;-1,-1,1] := by
    rw [← map_inv]
    ext row column
    fin_cases row <;> fin_cases column <;> simp [referenceIntegral]
  have substitution :
      substitute (GeneralLinearGroup.map (Int.castRingHom ℂ) referenceIntegral)⁻¹.val =
        MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1,
          MvPolynomial.X 2 - MvPolynomial.X 0 - MvPolynomial.X 1] := by
    rw [inverse]
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;>
      simp [substitute_X, linearForm, Fin.sum_univ_three,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  change MvPolynomial.C ((GeneralLinearGroup.det referenceIntegral : ℤ) : ℂ) *
    substitute (GeneralLinearGroup.map (Int.castRingHom ℂ) referenceIntegral)⁻¹.val
      polynomial.val = _
  rw [determinant, Int.cast_one, MvPolynomial.C_1, one_mul, substitution]

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit
