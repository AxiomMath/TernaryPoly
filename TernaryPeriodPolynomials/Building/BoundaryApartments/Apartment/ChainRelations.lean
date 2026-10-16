module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.RelationValues

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous

def rationalNormGenerator : RationalGL3 :=
  GeneralLinearGroup.map (Int.castRingHom ℚ) integralNormGenerator

private theorem relation_edge_eq {first second : RationalGL3}
    (plane : Adelic.InPlaneParabolic (first⁻¹ * second))
    (line : Adelic.InLineParabolic (first⁻¹ * second)) :
    (QuotientGroup.mk first : Edges) = QuotientGroup.mk second :=
  QuotientGroup.eq.mpr ⟨plane, line⟩

macro "norm_relation_edge" : tactic =>
  `(tactic| (apply relation_edge_eq <;> constructor <;>
    norm_num [rationalNormGenerator, integralNormGenerator, Adelic.weyl, swapFirstTwo,
      _root_.mul_inv_rev, ← map_inv, GeneralLinearGroup.map_apply, pow_two,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]))

theorem apartment_norm_relation :
    apartment 1 + apartment rationalNormGenerator + apartment (rationalNormGenerator ^ 2) = 0 := by
  have first : (QuotientGroup.mk (1 : RationalGL3) : Edges) =
      QuotientGroup.mk (rationalNormGenerator ^ 2 * swapFirstTwo) := by norm_relation_edge
  have second : (QuotientGroup.mk swapFirstTwo : Edges) =
      QuotientGroup.mk rationalNormGenerator := by norm_relation_edge
  have third : (QuotientGroup.mk (Adelic.weyl : RationalGL3) : Edges) =
      QuotientGroup.mk (rationalNormGenerator * Adelic.weyl ^ 2 * swapFirstTwo) := by
    norm_relation_edge
  have fourth : (QuotientGroup.mk (Adelic.weyl * swapFirstTwo) : Edges) =
      QuotientGroup.mk (rationalNormGenerator * Adelic.weyl ^ 2) := by norm_relation_edge
  have fifth : (QuotientGroup.mk ((Adelic.weyl : RationalGL3) ^ 2) : Edges) =
      QuotientGroup.mk (rationalNormGenerator ^ 2 * Adelic.weyl * swapFirstTwo) := by
    norm_relation_edge
  have sixth : (QuotientGroup.mk (Adelic.weyl ^ 2 * swapFirstTwo) : Edges) =
      QuotientGroup.mk (rationalNormGenerator ^ 2 * Adelic.weyl) := by norm_relation_edge
  have seventh : (QuotientGroup.mk (rationalNormGenerator * Adelic.weyl) : Edges) =
      QuotientGroup.mk (rationalNormGenerator ^ 2 * Adelic.weyl ^ 2 * swapFirstTwo) := by
    norm_relation_edge
  have eighth : (QuotientGroup.mk (rationalNormGenerator * swapFirstTwo) : Edges) =
      QuotientGroup.mk (rationalNormGenerator ^ 2) := by norm_relation_edge
  have ninth : (QuotientGroup.mk (rationalNormGenerator * Adelic.weyl * swapFirstTwo) : Edges) =
      QuotientGroup.mk (rationalNormGenerator ^ 2 * Adelic.weyl ^ 2) := by norm_relation_edge
  simp only [apartment, one_mul, first, second, third, fourth, fifth, sixth, seventh,
    eighth, ninth]
  abel

theorem weyl_cube : (Adelic.weyl : RationalGL3) ^ 3 = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [pow_succ, Adelic.weyl, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

theorem apartment_cyclic_relation : apartment (Adelic.weyl : RationalGL3) = apartment 1 := by
  have cube : (Adelic.weyl : RationalGL3) * Adelic.weyl ^ 2 = 1 := by
    rw [← pow_succ', weyl_cube]
  simp only [apartment, one_mul, ← pow_two, cube, one_mul]
  abel

theorem apartment_swap_relation : apartment swapFirstTwo = -apartment 1 := by
  have first : (QuotientGroup.mk (swapFirstTwo * swapFirstTwo) : Edges) =
      QuotientGroup.mk (1 : RationalGL3) := by norm_relation_edge
  have second : (QuotientGroup.mk (swapFirstTwo * Adelic.weyl) : Edges) =
      QuotientGroup.mk (Adelic.weyl ^ 2 * swapFirstTwo) := by norm_relation_edge
  have third : (QuotientGroup.mk (swapFirstTwo * Adelic.weyl * swapFirstTwo) : Edges) =
      QuotientGroup.mk ((Adelic.weyl : RationalGL3) ^ 2) := by norm_relation_edge
  have fourth : (QuotientGroup.mk (swapFirstTwo * Adelic.weyl ^ 2) : Edges) =
      QuotientGroup.mk (Adelic.weyl * swapFirstTwo) := by norm_relation_edge
  have fifth : (QuotientGroup.mk (swapFirstTwo * Adelic.weyl ^ 2 * swapFirstTwo) : Edges) =
      QuotientGroup.mk (Adelic.weyl : RationalGL3) := by norm_relation_edge
  simp only [apartment, one_mul, first, second, third, fourth, fifth]
  abel

def referenceApartment : goodCycleModule :=
  normalizedApartmentCycle referenceFrame referenceFrame_normalized

theorem referenceApartment_norm_relation :
    referenceApartment + translateGoodCycle apartmentNormGenerator referenceApartment +
      translateGoodCycle (apartmentNormGenerator ^ 2) referenceApartment = 0 := by
  apply Subtype.ext
  change apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame) +
    translateChain apartmentNormGenerator.val
      (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame)) +
    translateChain (apartmentNormGenerator ^ 2).val
      (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame)) = 0
  have first_product : apartmentNormGenerator.val *
      GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame =
        GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame * rationalNormGenerator := by
    change GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate integralNormGenerator) *
      GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame = _
    rw [← map_mul]
    simp only [frameConjugate, mul_assoc, inv_mul_cancel, mul_one, map_mul, rationalNormGenerator]
  have second_product : (apartmentNormGenerator ^ 2).val *
      GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame =
        GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame * rationalNormGenerator ^ 2 := by
    rw [Subgroup.coe_pow, pow_two, mul_assoc, first_product, ← mul_assoc, first_product,
      mul_assoc, pow_two]
  rw [apartment_translate, apartment_translate, first_product, second_product]
  have translated := congrArg (translateChain
    (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame)) apartment_norm_relation
  simpa only [map_add, map_zero, apartment_translate, mul_one] using translated

theorem conjugate_referenceApartment (matrix : IntegralGL3)
    (matrix_arithmetic : frameConjugate matrix ∈ arithmeticLevel) :
    (translateGoodCycle (integralImage (frameConjugate matrix) matrix_arithmetic)
      referenceApartment).val =
        apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame *
          GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) := by
  change translateChain
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate matrix))
      (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) referenceFrame)) = _
  rw [apartment_translate, ← map_mul]
  simp only [frameConjugate, mul_assoc, inv_mul_cancel, mul_one, map_mul]

theorem referenceApartment_cyclic_relation :
    translateGoodCycle apartmentCyclicGenerator referenceApartment = referenceApartment := by
  apply Subtype.ext
  rw [show apartmentCyclicGenerator = integralImage (frameConjugate integralCyclicGenerator)
    (frameConjugate_arithmetic integralCyclicGenerator cyclicGenerator_covector) from rfl,
    conjugate_referenceApartment]
  have cyclic_map : GeneralLinearGroup.map (Int.castRingHom ℚ) integralCyclicGenerator =
      (Adelic.weyl : RationalGL3) := by
    apply GeneralLinearGroup.ext
    intro row column
    fin_cases row <;> fin_cases column <;> rfl
  rw [cyclic_map, ← apartment_translate, apartment_cyclic_relation, apartment_translate, mul_one]
  rfl

theorem referenceApartment_swap_relation :
    translateGoodCycle apartmentSwapGenerator referenceApartment = -referenceApartment := by
  apply Subtype.ext
  rw [show apartmentSwapGenerator = integralImage (frameConjugate integralSwapGenerator)
    (frameConjugate_arithmetic integralSwapGenerator swapGenerator_covector) from rfl,
    conjugate_referenceApartment]
  have swap_map : GeneralLinearGroup.map (Int.castRingHom ℚ) integralSwapGenerator =
      swapFirstTwo := by
    apply GeneralLinearGroup.ext
    intro row column
    fin_cases row <;> fin_cases column <;> rfl
  rw [swap_map, ← apartment_translate, apartment_swap_relation, map_neg,
    apartment_translate, mul_one]
  rfl

theorem translateGoodCycle_mul (first second : rationalLevel) (chain : goodCycleModule) :
    translateGoodCycle (first * second) chain =
      translateGoodCycle first (translateGoodCycle second chain) := by
  apply Subtype.ext
  exact translateChain_mul first.val second.val chain.val

theorem translateGoodCycle_one (chain : goodCycleModule) :
    translateGoodCycle 1 chain = chain := by
  apply Subtype.ext
  exact translateChain_one chain.val

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
