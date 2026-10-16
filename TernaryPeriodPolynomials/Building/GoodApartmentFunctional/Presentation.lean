module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.Descent

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.Relations

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.Presentation

noncomputable section

def rightNormFrame (frame : NormalizedFrames) : NormalizedFrames :=
  ⟨frame.val * normMatrix, by
    intro column
    fin_cases column
    · simp [normMatrix, Matrix.mul_apply, Fin.sum_univ_three, frame.property]
    · simp [normMatrix, Matrix.mul_apply, Fin.sum_univ_three, frame.property]
      decide
    · simp [normMatrix, Matrix.mul_apply, Fin.sum_univ_three, frame.property]⟩

def rightCycleFrame (frame : NormalizedFrames) : NormalizedFrames :=
  ⟨frame.val * integralWeyl, by
    intro column
    simpa [pow_one] using normalized_rotated_frame frame.val frame.property 1 column⟩

def rightSwapFrame (frame : NormalizedFrames) : NormalizedFrames :=
  ⟨frame.val * swapMatrix, by
    intro column
    fin_cases column <;>
      simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_three, frame.property]⟩

def normRelation (frame : NormalizedFrames) : NormalizedFrames →₀ ℂ :=
  Finsupp.single frame 1 + Finsupp.single (rightNormFrame frame) 1 +
    Finsupp.single (rightNormFrame (rightNormFrame frame)) 1

def cycleRelation (frame : NormalizedFrames) : NormalizedFrames →₀ ℂ :=
  Finsupp.single (rightCycleFrame frame) 1 - Finsupp.single frame 1

def swapRelation (frame : NormalizedFrames) : NormalizedFrames →₀ ℂ :=
  Finsupp.single (rightSwapFrame frame) 1 + Finsupp.single frame 1

def presentationRelations : Submodule ℂ (NormalizedFrames →₀ ℂ) :=
  Submodule.span ℂ
    (Set.range normRelation ∪ Set.range cycleRelation ∪ Set.range swapRelation)

theorem map_normMatrix (ringMap : ℤ →+* ℂ) :
    GeneralLinearGroup.map ringMap (normMatrix : IntegralGL3) = normMatrix := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [normMatrix]

theorem map_swapMatrix (ringMap : ℤ →+* ℂ) :
    GeneralLinearGroup.map ringMap (swapMatrix : IntegralGL3) = swapMatrix := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [swapMatrix]

theorem evaluation_rightNormFrame {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (frame : NormalizedFrames) :
    normalizedFrameEvaluation polynomial (rightNormFrame frame) =
      homogeneousAction degree (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) frame.val)
        (homogeneousAction degree (-1) normMatrix polynomial) := by
  simp [normalizedFrameEvaluation, rightNormFrame, map_mul, map_normMatrix,
    Module.End.mul_apply]

theorem evaluation_rightCycleFrame {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (frame : NormalizedFrames) :
    normalizedFrameEvaluation polynomial (rightCycleFrame frame) =
      homogeneousAction degree (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) frame.val)
        (homogeneousAction degree (-1) Adelic.weyl polynomial) := by
  simp [normalizedFrameEvaluation, rightCycleFrame, integralWeyl, map_mul,
    Adelic.map_weyl, Module.End.mul_apply]

theorem evaluation_rightSwapFrame {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (frame : NormalizedFrames) :
    normalizedFrameEvaluation polynomial (rightSwapFrame frame) =
      homogeneousAction degree (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) frame.val)
        (homogeneousAction degree (-1) swapMatrix polynomial) := by
  simp [normalizedFrameEvaluation, rightSwapFrame, map_mul, map_swapMatrix,
    Module.End.mul_apply]

theorem normRelation_evaluation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (solution : SymmetricSolution polynomial) (frame : NormalizedFrames) :
    frameEvaluation polynomial (normRelation frame) = 0 := by
  have equality := congrArg
    (homogeneousAction degree (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) frame.val))
    (polynomial_norm_relation polynomial solution)
  simpa only [normRelation, map_add, frameEvaluation, Finsupp.linearCombination_single,
    one_smul, normalizedFrameEvaluation, rightNormFrame, map_mul, map_normMatrix,
    map_pow, pow_two, Module.End.mul_apply, map_zero] using equality

theorem cycleRelation_evaluation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (solution : SymmetricSolution polynomial) (frame : NormalizedFrames) :
    frameEvaluation polynomial (cycleRelation frame) = 0 := by
  simp only [cycleRelation, map_sub, frameEvaluation, Finsupp.linearCombination_single,
    one_smul]
  rw [evaluation_rightCycleFrame, polynomial_cycle_relation polynomial solution]
  exact sub_self _

theorem swapRelation_evaluation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (solution : SymmetricSolution polynomial) (frame : NormalizedFrames) :
    frameEvaluation polynomial (swapRelation frame) = 0 := by
  simp only [swapRelation, map_add, frameEvaluation, Finsupp.linearCombination_single,
    one_smul]
  rw [evaluation_rightSwapFrame, polynomial_swap_relation polynomial solution, map_neg]
  exact neg_add_cancel _

theorem presentationRelations_evaluation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (solution : SymmetricSolution polynomial) :
    presentationRelations ≤ (frameEvaluation polynomial).ker := by
  apply Submodule.span_le.mpr
  intro combination membership
  rcases membership with (⟨frame, rfl⟩ | ⟨frame, rfl⟩) | ⟨frame, rfl⟩
  · exact normRelation_evaluation polynomial solution frame
  · exact cycleRelation_evaluation polynomial solution frame
  · exact swapRelation_evaluation polynomial solution frame

theorem apartment_cycle (frame : RationalGL3) :
    apartment (frame * Adelic.weyl) = apartment frame := by
  have square : frame * Adelic.weyl * Adelic.weyl = frame * Adelic.weyl ^ 2 := by
    simp [pow_two, mul_assoc]
  have cube : frame * Adelic.weyl * Adelic.weyl ^ 2 = frame := by
    rw [mul_assoc, ← pow_succ', weyl_cubed, mul_one]
  simp only [apartment, square, cube]
  abel

theorem swapFirstTwo_square : swapFirstTwo * swapFirstTwo = (1 : RationalGL3) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [swapFirstTwo, Matrix.mul_apply, Fin.sum_univ_three]

theorem swapFirstTwo_weyl :
    swapFirstTwo * Adelic.weyl = (Adelic.weyl : RationalGL3) ^ 2 * swapFirstTwo := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [swapFirstTwo, Adelic.weyl, pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem swapFirstTwo_weyl_square :
    swapFirstTwo * (Adelic.weyl : RationalGL3) ^ 2 = Adelic.weyl * swapFirstTwo := by
  rw [pow_two, ← mul_assoc, swapFirstTwo_weyl, mul_assoc, swapFirstTwo_weyl,
    ← mul_assoc, ← pow_add]
  have fourth : (Adelic.weyl : RationalGL3) ^ (2 + 2) = Adelic.weyl := by
    rw [show 2 + 2 = 3 + 1 by rfl, pow_add, weyl_cubed, one_mul, pow_one]
  rw [fourth]

theorem apartment_swap (frame : RationalGL3) :
    apartment (frame * swapFirstTwo) = -apartment frame := by
  simp only [apartment, mul_assoc, swapFirstTwo_square, mul_one,
    swapFirstTwo_weyl, swapFirstTwo_weyl_square]
  abel

theorem map_integralWeyl :
    GeneralLinearGroup.map (Int.castRingHom ℚ) integralWeyl = Adelic.weyl :=
  integralWeyl_rational

theorem map_integralSwap :
    GeneralLinearGroup.map (Int.castRingHom ℚ) (swapMatrix : IntegralGL3) =
      swapFirstTwo := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem cycleRelation_apartment (frame : NormalizedFrames) :
    apartmentPresentation (cycleRelation frame) = 0 := by
  apply Subtype.ext
  simp [cycleRelation, apartmentPresentation, normalizedApartment, rightCycleFrame,
    map_mul, map_integralWeyl, apartment_cycle]

theorem swapRelation_apartment (frame : NormalizedFrames) :
    apartmentPresentation (swapRelation frame) = 0 := by
  apply Subtype.ext
  simp [swapRelation, apartmentPresentation, normalizedApartment, rightSwapFrame,
    map_mul, map_integralSwap, apartment_swap]

theorem norm_edge_id :
    (QuotientGroup.mk (normMatrix : RationalGL3) : Edges) =
      QuotientGroup.mk swapFirstTwo := by
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic (normMatrix⁻¹ * swapFirstTwo) ∧
    InLineParabolic (normMatrix⁻¹ * swapFirstTwo)
  constructor <;> constructor <;>
    simp [normMatrix, swapFirstTwo,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem norm_edge_swap :
    (QuotientGroup.mk ((normMatrix : RationalGL3) * swapFirstTwo) : Edges) =
      QuotientGroup.mk (normMatrix ^ 2 : RationalGL3) := by
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic ((normMatrix * swapFirstTwo)⁻¹ * normMatrix ^ 2) ∧
    InLineParabolic ((normMatrix * swapFirstTwo)⁻¹ * normMatrix ^ 2)
  constructor <;> constructor <;>
    simp [normMatrix, swapFirstTwo,
      pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem norm_edge_cycle :
    (QuotientGroup.mk ((normMatrix : RationalGL3) * Adelic.weyl) : Edges) =
      QuotientGroup.mk (normMatrix ^ 2 * Adelic.weyl ^ 2 * swapFirstTwo : RationalGL3) := by
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic ((normMatrix * Adelic.weyl)⁻¹ *
      (normMatrix ^ 2 * Adelic.weyl ^ 2 * swapFirstTwo)) ∧
    InLineParabolic ((normMatrix * Adelic.weyl)⁻¹ *
      (normMatrix ^ 2 * Adelic.weyl ^ 2 * swapFirstTwo))
  constructor <;> constructor <;>
    simp [normMatrix, swapFirstTwo, Adelic.weyl,
      pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem norm_edge_cycle_swap :
    (QuotientGroup.mk ((normMatrix : RationalGL3) * Adelic.weyl * swapFirstTwo) : Edges) =
      QuotientGroup.mk (normMatrix ^ 2 * Adelic.weyl ^ 2 : RationalGL3) := by
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic ((normMatrix * Adelic.weyl * swapFirstTwo)⁻¹ *
      (normMatrix ^ 2 * Adelic.weyl ^ 2)) ∧
    InLineParabolic ((normMatrix * Adelic.weyl * swapFirstTwo)⁻¹ *
      (normMatrix ^ 2 * Adelic.weyl ^ 2))
  constructor <;> constructor <;>
    simp [normMatrix, swapFirstTwo, Adelic.weyl,
      pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem norm_edge_cycle_square :
    (QuotientGroup.mk ((normMatrix : RationalGL3) * Adelic.weyl ^ 2) : Edges) =
      QuotientGroup.mk (Adelic.weyl * swapFirstTwo : RationalGL3) := by
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic ((normMatrix * Adelic.weyl ^ 2)⁻¹ *
      (Adelic.weyl * swapFirstTwo)) ∧
    InLineParabolic ((normMatrix * Adelic.weyl ^ 2)⁻¹ * (Adelic.weyl * swapFirstTwo))
  constructor <;> constructor <;>
    simp [normMatrix, swapFirstTwo, Adelic.weyl,
      pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem norm_edge_cycle_square_swap :
    (QuotientGroup.mk ((normMatrix : RationalGL3) * Adelic.weyl ^ 2 * swapFirstTwo) : Edges) =
      QuotientGroup.mk (Adelic.weyl : RationalGL3) := by
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic ((normMatrix * Adelic.weyl ^ 2 * swapFirstTwo)⁻¹ * Adelic.weyl) ∧
    InLineParabolic ((normMatrix * Adelic.weyl ^ 2 * swapFirstTwo)⁻¹ * Adelic.weyl)
  constructor <;> constructor <;>
    simp [normMatrix, swapFirstTwo, Adelic.weyl,
      pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem norm_square_edge_swap :
    (QuotientGroup.mk ((normMatrix : RationalGL3) ^ 2 * swapFirstTwo) : Edges) =
      QuotientGroup.mk (1 : RationalGL3) := by
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic ((normMatrix ^ 2 * swapFirstTwo)⁻¹ * 1) ∧
    InLineParabolic ((normMatrix ^ 2 * swapFirstTwo)⁻¹ * 1)
  constructor <;> constructor <;>
    simp [normMatrix, swapFirstTwo,
      pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem norm_square_edge_cycle :
    (QuotientGroup.mk ((normMatrix : RationalGL3) ^ 2 * Adelic.weyl) : Edges) =
      QuotientGroup.mk (Adelic.weyl ^ 2 * swapFirstTwo : RationalGL3) := by
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic ((normMatrix ^ 2 * Adelic.weyl)⁻¹ *
      (Adelic.weyl ^ 2 * swapFirstTwo)) ∧
    InLineParabolic ((normMatrix ^ 2 * Adelic.weyl)⁻¹ *
      (Adelic.weyl ^ 2 * swapFirstTwo))
  constructor <;> constructor <;>
    simp [normMatrix, swapFirstTwo, Adelic.weyl,
      pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem norm_square_edge_cycle_swap :
    (QuotientGroup.mk ((normMatrix : RationalGL3) ^ 2 * Adelic.weyl * swapFirstTwo) : Edges) =
      QuotientGroup.mk (Adelic.weyl ^ 2 : RationalGL3) := by
  apply QuotientGroup.eq.mpr
  change InPlaneParabolic ((normMatrix ^ 2 * Adelic.weyl * swapFirstTwo)⁻¹ * Adelic.weyl ^ 2) ∧
    InLineParabolic ((normMatrix ^ 2 * Adelic.weyl * swapFirstTwo)⁻¹ * Adelic.weyl ^ 2)
  constructor <;> constructor <;>
    simp [normMatrix, swapFirstTwo, Adelic.weyl,
      pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem apartment_norm_identity :
    apartment (1 : RationalGL3) + apartment normMatrix +
      apartment (normMatrix ^ 2 : RationalGL3) = 0 := by
  simp only [apartment, one_mul, norm_edge_id, norm_edge_swap, norm_edge_cycle,
    norm_edge_cycle_swap, norm_edge_cycle_square, norm_edge_cycle_square_swap,
    norm_square_edge_swap, norm_square_edge_cycle, norm_square_edge_cycle_swap]
  abel

theorem apartment_norm (frame : RationalGL3) :
    apartment frame + apartment (frame * normMatrix) +
      apartment (frame * normMatrix ^ 2 : RationalGL3) = 0 := by
  have equality := congrArg (translateChain frame) apartment_norm_identity
  simpa only [map_add, map_zero, translateChain_apartment, mul_one] using equality

theorem map_integralNorm :
    GeneralLinearGroup.map (Int.castRingHom ℚ) (normMatrix : IntegralGL3) =
      normMatrix := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [normMatrix]

theorem normRelation_apartment (frame : NormalizedFrames) :
    apartmentPresentation (normRelation frame) = 0 := by
  apply Subtype.ext
  simpa [normRelation, apartmentPresentation, normalizedApartment, rightNormFrame,
    map_mul, map_integralNorm, pow_two, mul_assoc] using
      apartment_norm (GeneralLinearGroup.map (Int.castRingHom ℚ) frame.val)

theorem presentationRelations_apartment :
    presentationRelations ≤ apartmentPresentation.ker := by
  apply Submodule.span_le.mpr
  intro combination membership
  rcases membership with (⟨frame, rfl⟩ | ⟨frame, rfl⟩) | ⟨frame, rfl⟩
  · exact normRelation_apartment frame
  · exact cycleRelation_apartment frame
  · exact swapRelation_apartment frame

theorem functional_of_complete_presentation {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (solution : SymmetricSolution polynomial)
    (spanning : Function.Surjective apartmentPresentation)
    (completeRelations : apartmentPresentation.ker ≤ presentationRelations) :
    ∃ extension : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial extension := by
  exact TernaryPeriodPolynomials.GoodApartmentFunctional.Descent.functional_of_presentation polynomial spanning
    (completeRelations.trans (presentationRelations_evaluation polynomial solution))

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.Presentation
