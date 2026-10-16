module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.FrameEvaluations

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous MvPolynomial

def integralBinaryA : IntegralGL3 :=
  ⟨!![1,0,0;0,1,-1;0,3,-2], !![1,0,0;0,-2,1;0,-3,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]⟩

theorem integralBinaryA_levi : BadLineLevi integralBinaryA := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  change lastRow ᵥ* (reductionThree integralBinaryA).val = lastRow
  simp only [lastRow, Matrix.single_vecMul, one_smul]
  ext index
  fin_cases index
  · rfl
  · change (3 : ZMod 3) = 0
    decide
  · change (-2 : ZMod 3) = 1
    decide

def arithmeticBinaryA : rationalLevel := integralImage integralBinaryA integralBinaryA_levi.1

theorem arithmeticBinaryA_val : arithmeticBinaryA.val = binaryA := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [arithmeticBinaryA, integralImage, integralBinaryA, binaryA,
      GeneralLinearGroup.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem specialPaths_binaryA : specialPaths arithmeticBinaryA =
    connectingChain - translateChain binaryA connectingChain := by
  unfold arithmeticBinaryA
  rw [specialPaths_integralLevi integralBinaryA integralBinaryA_levi]
  change connectingChain - translateChain arithmeticBinaryA.val connectingChain = _
  rw [arithmeticBinaryA_val]

def binaryAPath : EdgeChains := connectingChain - translateChain binaryA connectingChain

def firstFrame : RationalGL3 := GeneralLinearGroup.map (Int.castRingHom ℚ) firstBernoulliFrame

def secondFrame : RationalGL3 := GeneralLinearGroup.map (Int.castRingHom ℚ) secondBernoulliFrame

def thirdFrame : RationalGL3 := GeneralLinearGroup.map (Int.castRingHom ℚ) thirdBernoulliFrame

private theorem edge_eq_of_entries {first second : RationalGL3}
    (plane : Adelic.InPlaneParabolic (first⁻¹ * second))
    (line : Adelic.InLineParabolic (first⁻¹ * second)) :
    (QuotientGroup.mk first : Edges) = QuotientGroup.mk second :=
  QuotientGroup.eq.mpr ⟨plane, line⟩

macro "cancel_frame_flag" : tactic =>
  `(tactic| (apply edge_eq_of_entries <;> constructor <;>
    norm_num [firstFrame, secondFrame, thirdFrame, firstBernoulliFrame,
      secondBernoulliFrame, thirdBernoulliFrame, baseEdgeFrame, otherEdgeFrame,
      binaryA, Adelic.lineUnipotent, Adelic.upperUnipotent, Adelic.weyl,
      swapFirstTwo, _root_.mul_inv_rev, ← map_inv, GeneralLinearGroup.map_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, pow_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]))

theorem otherEdge_firstFrame : (QuotientGroup.mk otherEdgeFrame : Edges) =
    QuotientGroup.mk (firstFrame * Adelic.weyl ^ 2 * swapFirstTwo) := by
  cancel_frame_flag

theorem binaryA_otherEdge_firstFrame :
    binaryA • (QuotientGroup.mk otherEdgeFrame : Edges) =
      QuotientGroup.mk (firstFrame * Adelic.weyl ^ 2) := by
  change (QuotientGroup.mk (binaryA * otherEdgeFrame) : Edges) = _
  cancel_frame_flag

theorem binaryA_baseEdge_firstFrame :
    binaryA • (QuotientGroup.mk baseEdgeFrame : Edges) =
      QuotientGroup.mk (firstFrame * Adelic.weyl * swapFirstTwo) := by
  change (QuotientGroup.mk (binaryA * baseEdgeFrame) : Edges) = _
  cancel_frame_flag

theorem firstRadical_frameCancellation :
    translateChain (Adelic.lineUnipotent 1 0) binaryAPath - binaryAPath =
      apartment firstFrame := by
  have first_edge : Adelic.lineUnipotent (1 : ℚ) 0 • (QuotientGroup.mk otherEdgeFrame : Edges) =
      QuotientGroup.mk firstFrame := by
    change (QuotientGroup.mk (Adelic.lineUnipotent 1 0 * otherEdgeFrame) : Edges) = _
    cancel_frame_flag
  have second_edge : Adelic.lineUnipotent (1 : ℚ) 0 • (QuotientGroup.mk baseEdgeFrame : Edges) =
      QuotientGroup.mk baseEdgeFrame := by
    change (QuotientGroup.mk (Adelic.lineUnipotent 1 0 * baseEdgeFrame) : Edges) = _
    cancel_frame_flag
  have third_edge : Adelic.lineUnipotent (1 : ℚ) 0 • binaryA •
      (QuotientGroup.mk otherEdgeFrame : Edges) =
      QuotientGroup.mk (firstFrame * swapFirstTwo) := by
    change (QuotientGroup.mk (Adelic.lineUnipotent 1 0 * (binaryA * otherEdgeFrame)) : Edges) = _
    cancel_frame_flag
  have fourth_edge : Adelic.lineUnipotent (1 : ℚ) 0 • binaryA •
      (QuotientGroup.mk baseEdgeFrame : Edges) =
      QuotientGroup.mk (firstFrame * Adelic.weyl) := by
    change (QuotientGroup.mk (Adelic.lineUnipotent 1 0 * (binaryA * baseEdgeFrame)) : Edges) = _
    cancel_frame_flag
  simp only [binaryAPath, connectingChain, map_sub, translateChain,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, apartment, otherEdge, baseEdge]
  rw [first_edge, second_edge, third_edge, fourth_edge]
  rw [binaryA_otherEdge_firstFrame, binaryA_baseEdge_firstFrame, otherEdge_firstFrame]
  abel

theorem secondRadical_frameCancellation :
    translateChain (Adelic.lineUnipotent 0 1) binaryAPath - binaryAPath =
      apartment firstFrame + apartment secondFrame + apartment thirdFrame := by
  have first_edge : Adelic.lineUnipotent (0 : ℚ) 1 • (QuotientGroup.mk otherEdgeFrame : Edges) =
      QuotientGroup.mk (secondFrame * Adelic.weyl) := by
    change (QuotientGroup.mk (Adelic.lineUnipotent 0 1 * otherEdgeFrame) : Edges) = _
    cancel_frame_flag
  have second_edge : Adelic.lineUnipotent (0 : ℚ) 1 • (QuotientGroup.mk baseEdgeFrame : Edges) =
      QuotientGroup.mk (secondFrame * swapFirstTwo) := by
    change (QuotientGroup.mk (Adelic.lineUnipotent 0 1 * baseEdgeFrame) : Edges) = _
    cancel_frame_flag
  have third_edge : Adelic.lineUnipotent (0 : ℚ) 1 • binaryA •
      (QuotientGroup.mk otherEdgeFrame : Edges) =
      QuotientGroup.mk (secondFrame * Adelic.weyl * swapFirstTwo) := by
    change (QuotientGroup.mk (Adelic.lineUnipotent 0 1 * (binaryA * otherEdgeFrame)) : Edges) = _
    cancel_frame_flag
  have fourth_edge : Adelic.lineUnipotent (0 : ℚ) 1 • binaryA •
      (QuotientGroup.mk baseEdgeFrame : Edges) =
      QuotientGroup.mk (thirdFrame * Adelic.weyl) := by
    change (QuotientGroup.mk (Adelic.lineUnipotent 0 1 * (binaryA * baseEdgeFrame)) : Edges) = _
    cancel_frame_flag
  have base_edge : (QuotientGroup.mk baseEdgeFrame : Edges) = QuotientGroup.mk secondFrame := by
    cancel_frame_flag
  have first_third : (QuotientGroup.mk firstFrame : Edges) =
      QuotientGroup.mk (thirdFrame * Adelic.weyl ^ 2 * swapFirstTwo) := by
    cancel_frame_flag
  have first_third_swap : (QuotientGroup.mk (firstFrame * swapFirstTwo) : Edges) =
      QuotientGroup.mk (thirdFrame * Adelic.weyl ^ 2) := by
    cancel_frame_flag
  have first_third_weyl : (QuotientGroup.mk (firstFrame * Adelic.weyl) : Edges) =
      QuotientGroup.mk (thirdFrame * Adelic.weyl * swapFirstTwo) := by
    cancel_frame_flag
  have second_third : (QuotientGroup.mk (secondFrame * Adelic.weyl ^ 2) : Edges) =
      QuotientGroup.mk (thirdFrame * swapFirstTwo) := by
    cancel_frame_flag
  have second_third_swap : (QuotientGroup.mk (secondFrame * Adelic.weyl ^ 2 * swapFirstTwo) : Edges) =
      QuotientGroup.mk thirdFrame := by
    cancel_frame_flag
  simp only [binaryAPath, connectingChain, map_sub, translateChain,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, apartment, otherEdge, baseEdge]
  rw [first_edge, second_edge, third_edge, fourth_edge]
  rw [binaryA_otherEdge_firstFrame, binaryA_baseEdge_firstFrame, otherEdge_firstFrame, base_edge]
  rw [first_third, first_third_swap, first_third_weyl, second_third, second_third_swap]
  abel

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
