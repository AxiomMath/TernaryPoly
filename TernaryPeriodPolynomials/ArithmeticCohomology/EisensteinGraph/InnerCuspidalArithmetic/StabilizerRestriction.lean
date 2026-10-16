module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Helpers

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {X : Type} [MulAction RationalGL3 X]

def fixedPointLevel (level : Subgroup RationalGL3) (point : X) :
    Subgroup RationalGL3 :=
  level ⊓ MulAction.stabilizer RationalGL3 point

def fixedPointCochain (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (point : X) (degree : ℕ) :
    cochains level (functionRepresentation representation X) degree →ₗ[ℂ]
      cochains (fixedPointLevel level point) representation degree where
  toFun cochain := ⟨fun vertices => cochain.val vertices point, by
    intro element vertices
    have equivariance := congrFun
      (cochain.property ⟨element.val, element.property.1⟩ vertices) point
    have fixed : element.val⁻¹ • point = point :=
      MulAction.mem_stabilizer_iff.mp
        ((MulAction.stabilizer RationalGL3 point).inv_mem element.property.2)
    change cochain.val (fun index => element.val * vertices index) point =
      representation element.val (cochain.val vertices (element.val⁻¹ • point))
      at equivariance
    simpa only [fixed] using equivariance⟩
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

theorem fixedPointCochain_differentialOne (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (point : X)
    (primitive : cochains level (functionRepresentation representation X) 1) :
    fixedPointCochain level representation point 2
        (differentialOne level (functionRepresentation representation X) primitive) =
      differentialOne (fixedPointLevel level point) representation
        (fixedPointCochain level representation point 1 primitive) := rfl

def fixedPointCycle (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (point : X) :
    cocycles level (functionRepresentation representation X) →ₗ[ℂ]
      cocycles (fixedPointLevel level point) representation where
  toFun cycle := ⟨fixedPointCochain level representation point 2 cycle.val, by
    change differentialTwo (fixedPointLevel level point) representation _ = 0
    funext vertices
    have vanishing : differentialTwo level
        (functionRepresentation representation X) cycle.val = 0 := cycle.property
    exact congrFun (congrFun vanishing vertices) point⟩
  map_add' first second := rfl
  map_smul' scalar cycle := rfl

theorem fixedPointCycle_boundaryMap (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (point : X)
    (primitive : cochains level (functionRepresentation representation X) 1) :
    fixedPointCycle level representation point
        (boundaryMap level (functionRepresentation representation X) primitive) =
      boundaryMap (fixedPointLevel level point) representation
        (fixedPointCochain level representation point 1 primitive) := rfl

def fixedPointH2 (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (point : X) :
    H2 level (functionRepresentation representation X) →ₗ[ℂ]
      H2 (fixedPointLevel level point) representation :=
  (LinearMap.range (boundaryMap level (functionRepresentation representation X))).mapQ
    (LinearMap.range (boundaryMap (fixedPointLevel level point) representation))
    (fixedPointCycle level representation point) (by
      rintro cycle ⟨primitive, rfl⟩
      exact ⟨fixedPointCochain level representation point 1 primitive, rfl⟩)

theorem fixedPointH2_classOf (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (point : X)
    (cycle : cocycles level (functionRepresentation representation X)) :
    fixedPointH2 level representation point
        (classOf level (functionRepresentation representation X) cycle) =
      classOf (fixedPointLevel level point) representation
        (fixedPointCycle level representation point cycle) := rfl

theorem vanishesOnGood_fixedPointH2 {degree : ℕ} {character : RankOneCharacter}
    {side : Side} {coordinate : StratumH2 degree character side}
    (vanishing : VanishesOnGood degree character side coordinate)
    (flag : Flags side) (good : GoodFlag side flag) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent degree character) flag
      coordinate = 0 := by
  obtain ⟨cycle, sameClass, primitive, restriction⟩ := vanishing
  rw [← sameClass]
  change classOf (fixedPointLevel rationalLevel flag)
    (rationalCoefficientComponent degree character)
    (fixedPointCycle rationalLevel (rationalCoefficientComponent degree character) flag
      cycle) = 0
  have boundary : fixedPointCycle rationalLevel
      (rationalCoefficientComponent degree character) flag cycle =
      boundaryMap (fixedPointLevel rationalLevel flag)
        (rationalCoefficientComponent degree character)
        (fixedPointCochain rationalLevel
          (rationalCoefficientComponent degree character) flag 1 primitive) := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    exact restriction vertices flag good
  rw [boundary]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

def endpointCycles (degree : ℕ) (character : RankOneCharacter) (side : Side) :
    MaximalCycles degree character side →ₗ[ℂ]
      cocycles rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree character) Edges) where
  toFun cycle := ⟨endpointCochain degree character side 2 cycle.val, by
    change differentialTwo rationalLevel
      (functionRepresentation (rationalCoefficientComponent degree character) Edges) _ = 0
    funext vertices edge
    have vanishing : differentialTwo rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        cycle.val = 0 := cycle.property
    exact congrFun (congrFun vanishing vertices) (endpoint side edge)⟩
  map_add' first second := rfl
  map_smul' scalar cycle := rfl

def endpointH2 (degree : ℕ) (character : RankOneCharacter) (side : Side) :
    StratumH2 degree character side →ₗ[ℂ]
      H2 rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree character) Edges) :=
  (LinearMap.range (boundaryMap rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree character) side))).mapQ
    (LinearMap.range (boundaryMap rationalLevel
      (functionRepresentation (rationalCoefficientComponent degree character) Edges)))
    (endpointCycles degree character side) (by
      rintro cycle ⟨primitive, rfl⟩
      exact ⟨endpointCochain degree character side 1 primitive, rfl⟩)

theorem innerBoundary_iff_endpointH2 {degree : ℕ} {character : RankOneCharacter}
    {side : Side} (coordinate : StratumH2 degree character side) :
    InnerBoundary degree character side coordinate ↔
      endpointH2 degree character side coordinate = 0 := by
  constructor
  · rintro ⟨cycle, sameClass, primitive, restriction⟩
    rw [← sameClass]
    change classOf rationalLevel
      (functionRepresentation (rationalCoefficientComponent degree character) Edges)
      (endpointCycles degree character side cycle) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨primitive, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext vertices edge
    exact (restriction vertices edge).symm
  · refine Quotient.inductionOn' coordinate ?_
    intro cycle zeroClass
    change classOf rationalLevel
      (functionRepresentation (rationalCoefficientComponent degree character) Edges)
      (endpointCycles degree character side cycle) = 0 at zeroClass
    obtain ⟨primitive, boundary⟩ := (Submodule.Quotient.mk_eq_zero _).mp zeroClass
    refine ⟨cycle, rfl, primitive, ?_⟩
    intro vertices edge
    exact (congrArg (fun restricted => restricted.val.val vertices edge) boundary).symm

theorem innerBoundary_edge_fixedPointH2 {degree : ℕ} {character : RankOneCharacter}
    {side : Side} {coordinate : StratumH2 degree character side}
    (inner : InnerBoundary degree character side coordinate) (edge : Edges) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent degree character) edge
      (endpointH2 degree character side coordinate) = 0 := by
  rw [(innerBoundary_iff_endpointH2 coordinate).mp inner, map_zero]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
