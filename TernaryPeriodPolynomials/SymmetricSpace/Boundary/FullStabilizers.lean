module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullDescent
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Completion
public import Mathlib.GroupTheory.DoubleCoset

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory ModThreeGoodAction IntegralGL3Congruence OrdinaryIncidence
open SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryMV RelativeOrbitCompletion
open RelativeStabilizerCoordinates OrdinaryParabolicGroups

instance fullLineAction : MulAction IntegralGL Line where
  smul g L := OrdinaryFullAction.lineAction (OrdinaryFullAction.integral g) L
  one_smul L := by
    apply Subtype.ext
    change OrdinaryFullAction.subspaceAction (OrdinaryFullAction.integral 1) L.val = L.val
    rw [map_one,OrdinaryFullAction.subspaceAction_one]
  mul_smul g h L := by
    apply Subtype.ext
    change OrdinaryFullAction.subspaceAction (OrdinaryFullAction.integral (g*h)) L.val = _
    rw [map_mul]
    exact OrdinaryFullAction.subspaceAction_mul _ _ _

instance fullPlaneAction : MulAction IntegralGL Plane where
  smul g P := OrdinaryFullAction.planeAction (OrdinaryFullAction.integral g) P
  one_smul P := by
    apply Subtype.ext
    change OrdinaryFullAction.subspaceAction (OrdinaryFullAction.integral 1) P.val = P.val
    rw [map_one,OrdinaryFullAction.subspaceAction_one]
  mul_smul g h P := by
    apply Subtype.ext
    change OrdinaryFullAction.subspaceAction (OrdinaryFullAction.integral (g*h)) P.val = _
    rw [map_mul]
    exact OrdinaryFullAction.subspaceAction_mul _ _ _

instance fullFlagAction : MulAction IntegralGL Flag where
  smul g F := ⟨(g • F.val.1,g • F.val.2),
    (OrdinaryFullAction.incidence_action_iff (OrdinaryFullAction.integral g) _ _).mpr F.property⟩
  one_smul F := Subtype.ext (Prod.ext (one_smul IntegralGL F.val.1) (one_smul IntegralGL F.val.2))
  mul_smul g h F := Subtype.ext (Prod.ext (mul_smul g h F.val.1) (mul_smul g h F.val.2))

abbrev standardFlag : Flag := ⟨(standardLine,standardPlane),standard_incident⟩

/-- The line stabilizer is the entire integral Q, including both determinant signs. -/
theorem standardLine_stabilizer : MulAction.stabilizer IntegralGL standardLine = Q := by
  ext g
  change (g • standardLine = standardLine) ↔ Stabilizes g L0
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

/-- The plane stabilizer is the entire integral P. -/
theorem standardPlane_stabilizer : MulAction.stabilizer IntegralGL standardPlane = P := by
  ext g
  change (g • standardPlane = standardPlane) ↔ Stabilizes g P0
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

/-- The actual full-flag stabilizer is precisely B=P∩Q. -/
theorem standardFlag_stabilizer : MulAction.stabilizer IntegralGL standardFlag = B := by
  ext g
  change (g • standardFlag = standardFlag) ↔ g ∈ P ∧ g ∈ Q
  rw [← standardLine_stabilizer,← standardPlane_stabilizer]
  change (g • standardFlag = standardFlag) ↔
    g • standardPlane = standardPlane ∧ g • standardLine = standardLine
  constructor
  · intro h
    exact ⟨congrArg (fun F : Flag => F.val.2) h,congrArg (fun F : Flag => F.val.1) h⟩
  · rintro ⟨hP,hL⟩
    exact Subtype.ext (Prod.ext hL hP)

/-- Integral flag completion proves transitivity on every rational boundary flag. -/
theorem fullFlag_transitive (F : Flag) : ∃ g : IntegralGL, g • standardFlag = F := by
  obtain ⟨g,hL,hP⟩ := flag_completion F.val.1.val F.val.2.val
    F.val.1.property.1 F.val.2.property.1 F.property.le
  exact ⟨g,Subtype.ext (Prod.ext (Subtype.ext hL) (Subtype.ext hP))⟩

theorem fullPlane_transitive (R : Plane) : ∃ g : IntegralGL, g • standardPlane = R := by
  obtain ⟨g,hg⟩ := plane_completion R.val R.property.1
  exact ⟨g,Subtype.ext hg⟩

theorem fullLine_transitive (L : Line) : ∃ g : IntegralGL, g • standardLine = L := by
  obtain ⟨g,hg⟩ := RationalLineBasis.rationalLine_eq_augmentedLine ⟨L.val,L.property.1⟩
  exact ⟨g,Subtype.ext ((mapSpace_L0 g).trans (congrArg Subtype.val hg))⟩

/-- The principal-six actions are the literal restrictions of the full actions. -/
theorem fullLine_restrict (g : principalSix) (L : Line) : (g.val : IntegralGL) • L = g • L := rfl
theorem fullPlane_restrict (g : principalSix) (R : Plane) : (g.val : IntegralGL) • R = g • R := rfl
theorem fullFlag_restrict (g : principalSix) (F : Flag) : (g.val : IntegralGL) • F = g • F := rfl

/-- Actual principal-six standard stabilizers are subgroup preimages, never full parabolics. -/
theorem coverLine_stabilizer : MulAction.stabilizer principalSix standardLine =
    Q.comap principalSix.subtype := by
  ext g
  change (g • standardLine = standardLine) ↔ g.val ∈ Q
  rw [← standardLine_stabilizer]
  rfl

theorem coverPlane_stabilizer : MulAction.stabilizer principalSix standardPlane =
    P.comap principalSix.subtype := by
  ext g
  change (g • standardPlane = standardPlane) ↔ g.val ∈ P
  rw [← standardPlane_stabilizer]
  rfl

theorem coverFlag_stabilizer : MulAction.stabilizer principalSix standardFlag =
    B.comap principalSix.subtype := by
  ext g
  change (g • standardFlag = standardFlag) ↔ g.val ∈ B
  rw [← standardFlag_stabilizer]
  rfl

end TernaryPoly.SymmetricSpaceBoundaryFull
