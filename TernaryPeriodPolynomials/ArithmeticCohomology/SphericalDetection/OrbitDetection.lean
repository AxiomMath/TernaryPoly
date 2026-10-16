module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OrbitPrimitives

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers


def transportFlagCochain {degree : ℕ} (character : RankOneCharacter)
    (side : Side) (flag : Flags side) (element : rationalLevel)
    (cochain_degree : ℕ) :
    cochains (flagArithmeticStabilizer side flag)
      (rationalCoefficientComponent degree character) cochain_degree →ₗ[ℂ]
    cochains (flagArithmeticStabilizer side (element.val • flag))
      (rationalCoefficientComponent degree character) cochain_degree where
  toFun primitive := ⟨fun vertices =>
    rationalCoefficientComponent degree character element.val
      (primitive.val (fun index => element.val⁻¹ * vertices index)), by
    intro stabilizer vertices
    let conjugate : flagArithmeticStabilizer side flag :=
      ⟨element.val⁻¹ * stabilizer.val * element.val,
        ⟨rationalLevel.mul_mem
          (rationalLevel.mul_mem (rationalLevel.inv_mem element.property)
            stabilizer.property.1) element.property,
          MulAction.mem_stabilizer_iff.mpr (by
            rw [mul_smul, mul_smul,
              MulAction.mem_stabilizer_iff.mp stabilizer.property.2,
              inv_smul_smul])⟩⟩
    have equivariance := primitive.property conjugate
      (fun index => element.val⁻¹ * vertices index)
    have same_vertices :
        (fun index => conjugate.val * (element.val⁻¹ * vertices index)) =
          (fun index => element.val⁻¹ * (stabilizer.val * vertices index)) := by
      funext index
      simp [conjugate, mul_assoc]
    rw [same_vertices] at equivariance
    change rationalCoefficientComponent degree character element.val
        (primitive.val (fun index => element.val⁻¹ * (stabilizer.val * vertices index))) =
      rationalCoefficientComponent degree character stabilizer.val
        (rationalCoefficientComponent degree character element.val
          (primitive.val (fun index => element.val⁻¹ * vertices index)))
    rw [equivariance]
    have same_product : element.val * conjugate.val = stabilizer.val * element.val := by
      simp [conjugate, mul_assoc]
    simpa only [map_mul, Module.End.mul_apply] using congrArg
      (fun matrix => rationalCoefficientComponent degree character matrix
        (primitive.val (fun index => element.val⁻¹ * vertices index))) same_product⟩
  map_add' first second := by
    apply Subtype.ext
    funext vertices
    exact map_add _ _ _
  map_smul' scalar primitive := by
    apply Subtype.ext
    funext vertices
    exact map_smul (rationalCoefficientComponent degree character element.val) scalar _

theorem transportFlagCochain_differentialOne {degree : ℕ}
    (character : RankOneCharacter) (side : Side) (flag : Flags side)
    (element : rationalLevel)
    (primitive : cochains (flagArithmeticStabilizer side flag)
      (rationalCoefficientComponent degree character) 1) :
    differentialOne (flagArithmeticStabilizer side (element.val • flag))
      (rationalCoefficientComponent degree character)
      (transportFlagCochain character side flag element 1 primitive) =
    transportFlagCochain character side flag element 2
      (differentialOne (flagArithmeticStabilizer side flag)
        (rationalCoefficientComponent degree character) primitive) := by
  apply Subtype.ext
  funext vertices
  have pair_transforms (first_index second_index : Fin 3) :
      (fun index : Fin 2 => element.val⁻¹ *
        ![vertices first_index, vertices second_index] index) =
        ![element.val⁻¹ * vertices first_index, element.val⁻¹ * vertices second_index] := by
    funext index
    fin_cases index <;> rfl
  simp only [transportFlagCochain, differentialOne, LinearMap.coe_mk,
    AddHom.coe_mk, pair_transforms]
  rw [map_add, map_sub]

theorem transportFlagCochain_evaluateFlagCycle {degree : ℕ}
    (character : RankOneCharacter) (side : Side) (flag : Flags side)
    (element : rationalLevel) (cycle : MaximalCycles degree character side) :
    transportFlagCochain character side flag element 2
      (evaluateFlagCycle character side flag cycle).val =
      (evaluateFlagCycle character side (element.val • flag) cycle).val := by
  apply Subtype.ext
  funext vertices
  have equivariance := congrFun
    (cycle.val.property element (fun index => element.val⁻¹ * vertices index))
    (element.val • flag)
  change cycle.val.val
      (fun index => element.val * (element.val⁻¹ * vertices index)) (element.val • flag) =
    rationalCoefficientComponent degree character element.val
      (cycle.val.val (fun index => element.val⁻¹ * vertices index)
        (element.val⁻¹ • (element.val • flag))) at equivariance
  have same_vertices :
      (fun index => element.val * (element.val⁻¹ * vertices index)) = vertices := by
    funext index
    exact mul_inv_cancel_left _ _
  rw [same_vertices, inv_smul_smul] at equivariance
  exact equivariance.symm

theorem flagRestriction_smul_zero {degree : ℕ}
    (character : RankOneCharacter) (side : Side) (flag : Flags side)
    (element : rationalLevel) (coordinate : StratumH2 degree character side)
    (vanishing : flagRestriction character side flag coordinate = 0) :
    flagRestriction character side (element.val • flag) coordinate = 0 := by
  induction coordinate using Submodule.Quotient.induction_on with
  | _ cycle =>
    change flagRestriction character side flag
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side) cycle) = 0
        at vanishing
    change flagRestriction character side (element.val • flag)
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side) cycle) = 0
    rw [flagRestriction_classOf] at vanishing ⊢
    rcases (classOf_eq_zero_iff _ _ _).mp vanishing with ⟨primitive, coboundary⟩
    apply (classOf_eq_zero_iff _ _ _).mpr
    refine ⟨transportFlagCochain character side flag element 1 primitive, ?_⟩
    rw [transportFlagCochain_differentialOne, coboundary,
      transportFlagCochain_evaluateFlagCycle]

theorem flagRestriction_smul_eq_zero_iff {degree : ℕ}
    (character : RankOneCharacter) (side : Side) (flag : Flags side)
    (element : rationalLevel) (coordinate : StratumH2 degree character side) :
    flagRestriction character side (element.val • flag) coordinate = 0 ↔
      flagRestriction character side flag coordinate = 0 := by
  constructor
  · intro vanishing
    have transported := flagRestriction_smul_zero character side (element.val • flag)
      element⁻¹ coordinate vanishing
    change flagRestriction character side (element.val⁻¹ • (element.val • flag))
      coordinate = 0 at transported
    rw [inv_smul_smul] at transported
    exact transported
  · exact flagRestriction_smul_zero character side flag element coordinate

theorem coordinate_eq_zero_iff_orbitRestrictions {degree : ℕ}
    (character : RankOneCharacter) (side : Side)
    (coordinate : StratumH2 degree character side) :
    coordinate = 0 ↔ ∀ flag,
      flagRestriction character side (arithmeticFlagRepresentative side flag)
        coordinate = 0 := by
  constructor
  · intro zero flag
    rw [zero, map_zero]
  · intro vanishing
    induction coordinate using Submodule.Quotient.induction_on with
    | _ cycle =>
      apply (classOf_eq_zero_iff_all_flagRestrictions character side cycle).mpr
      intro flag
      have transported := flagRestriction_smul_zero character side
        (arithmeticFlagRepresentative side flag)
        (arithmeticFlagTransporter side flag)
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree character) side) cycle)
        (vanishing flag)
      rw [arithmeticFlagTransporter_smul] at transported
      exact transported

theorem coordinate_eq_zero_of_good_and_badRestrictions {degree : ℕ}
    (character : RankOneCharacter) (side : Side)
    (coordinate : StratumH2 degree character side)
    (good_zero : VanishesOnGood degree character side coordinate)
    (bad_zero : ∀ flag, ¬ GoodFlag side flag →
      flagRestriction character side flag coordinate = 0) : coordinate = 0 := by
  classical
  apply (coordinate_eq_zero_iff_orbitRestrictions character side coordinate).mpr
  intro flag
  by_cases good : GoodFlag side (arithmeticFlagRepresentative side flag)
  · exact vanishesOnGood_flagRestriction_zero character side coordinate good_zero _ good
  · exact bad_zero _ good

theorem badPlaneRepresentative_eq_zero_of_badRestrictions {degree : ℕ}
    (data : InducingData degree) (coordinate : boundarySummand data .plane)
    (supported : BadPlaneRepresentative data coordinate)
    (bad_zero : ∀ flag, ¬ GoodFlag .plane flag →
      flagRestriction data.chi .plane flag coordinate.val = 0) : coordinate = 0 := by
  apply Subtype.ext
  exact coordinate_eq_zero_of_good_and_badRestrictions data.chi .plane coordinate.val
    (badPlaneRepresentative_vanishesOnGood data coordinate supported) bad_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
