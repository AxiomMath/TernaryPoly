module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Helpers

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def flagArithmeticStabilizer (side : Side) (flag : Flags side) :
    Subgroup RationalGL3 :=
  rationalLevel ⊓ MulAction.stabilizer RationalGL3 flag

def evaluateFlagCochain {degree : ℕ} (character : RankOneCharacter)
    (side : Side) (flag : Flags side) (cochain_degree : ℕ) :
    cochains rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) side)
      cochain_degree →ₗ[ℂ]
    cochains (flagArithmeticStabilizer side flag)
      (rationalCoefficientComponent degree character) cochain_degree where
  toFun cochain := ⟨fun vertices => cochain.val vertices flag, by
    intro element vertices
    have equivariance := congrFun
      (cochain.property ⟨element.val, element.property.1⟩ vertices) flag
    have fixes : element.val⁻¹ • flag = flag :=
      MulAction.mem_stabilizer_iff.mp
        ((MulAction.stabilizer RationalGL3 flag).inv_mem element.property.2)
    change cochain.val (fun index => element.val * vertices index) flag =
      rationalCoefficientComponent degree character element.val
        (cochain.val vertices flag)
    change cochain.val (fun index => element.val * vertices index) flag =
      rationalCoefficientComponent degree character element.val
        (cochain.val vertices (element.val⁻¹ • flag)) at equivariance
    simpa only [fixes] using equivariance⟩
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

theorem evaluateFlagCochain_differentialOne {degree : ℕ}
    (character : RankOneCharacter) (side : Side) (flag : Flags side)
    (primitive : cochains rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) side) 1) :
    evaluateFlagCochain character side flag 2
      (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        primitive) =
      differentialOne (flagArithmeticStabilizer side flag)
        (rationalCoefficientComponent degree character)
        (evaluateFlagCochain character side flag 1 primitive) := rfl

def evaluateFlagCycle {degree : ℕ} (character : RankOneCharacter)
    (side : Side) (flag : Flags side) :
    MaximalCycles degree character side →ₗ[ℂ]
      cocycles (flagArithmeticStabilizer side flag)
        (rationalCoefficientComponent degree character) where
  toFun cycle := ⟨evaluateFlagCochain character side flag 2 cycle.val, by
    funext vertices
    exact congrFun (congrFun cycle.property vertices) flag⟩
  map_add' first second := rfl
  map_smul' scalar cycle := rfl

theorem evaluateFlagCycle_boundaryMap {degree : ℕ}
    (character : RankOneCharacter) (side : Side) (flag : Flags side)
    (primitive : cochains rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) side) 1) :
    evaluateFlagCycle character side flag
      (boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        primitive) =
      boundaryMap (flagArithmeticStabilizer side flag)
        (rationalCoefficientComponent degree character)
        (evaluateFlagCochain character side flag 1 primitive) := rfl

def flagRestriction {degree : ℕ} (character : RankOneCharacter)
    (side : Side) (flag : Flags side) :
    StratumH2 degree character side →ₗ[ℂ]
      H2 (flagArithmeticStabilizer side flag)
        (rationalCoefficientComponent degree character) :=
  (LinearMap.range (boundaryMap rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree character) side))).liftQ
    ((classOf (flagArithmeticStabilizer side flag)
      (rationalCoefficientComponent degree character)).comp
      (evaluateFlagCycle character side flag)) (by
        rintro cycle ⟨primitive, rfl⟩
        change classOf (flagArithmeticStabilizer side flag)
          (rationalCoefficientComponent degree character)
          (evaluateFlagCycle character side flag
            (boundaryMap rationalLevel
              (flagRepresentation (rationalCoefficientComponent degree character) side)
              primitive)) = 0
        apply (classOf_eq_zero_iff _ _ _).mpr
        exact ⟨evaluateFlagCochain character side flag 1 primitive, rfl⟩)

theorem flagRestriction_classOf {degree : ℕ}
    (character : RankOneCharacter) (side : Side) (flag : Flags side)
    (cycle : MaximalCycles degree character side) :
    flagRestriction character side flag
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        cycle) =
      classOf (flagArithmeticStabilizer side flag)
        (rationalCoefficientComponent degree character)
        (evaluateFlagCycle character side flag cycle) := rfl

theorem vanishesOnGood_restricted_class_zero {degree : ℕ}
    (character : RankOneCharacter) (side : Side)
    (cycle : MaximalCycles degree character side)
    (vanishing : VanishesOnGood degree character side
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        cycle))
    (flag : Flags side) (good : GoodFlag side flag) :
    classOf (flagArithmeticStabilizer side flag)
      (rationalCoefficientComponent degree character)
      (evaluateFlagCycle character side flag cycle) = 0 := by
  rcases (vanishesOnGood_iff_for_representative character side cycle).mp vanishing with
    ⟨primitive, coboundary⟩
  apply (classOf_eq_zero_iff _ _ _).mpr
  refine ⟨evaluateFlagCochain character side flag 1 primitive, ?_⟩
  rw [← evaluateFlagCochain_differentialOne]
  apply Subtype.ext
  funext vertices
  exact (coboundary vertices flag good).symm

theorem vanishesOnGood_flagRestriction_zero {degree : ℕ}
    (character : RankOneCharacter) (side : Side)
    (coordinate : StratumH2 degree character side)
    (vanishing : VanishesOnGood degree character side coordinate)
    (flag : Flags side) (good : GoodFlag side flag) :
    flagRestriction character side flag coordinate = 0 := by
  obtain ⟨cycle, represents, primitive, coboundary⟩ := vanishing
  rw [← represents, flagRestriction_classOf]
  exact vanishesOnGood_restricted_class_zero character side cycle
    ⟨cycle, rfl, primitive, coboundary⟩ flag good

end TernaryPeriodPolynomials.SphericalDetection.Helpers
