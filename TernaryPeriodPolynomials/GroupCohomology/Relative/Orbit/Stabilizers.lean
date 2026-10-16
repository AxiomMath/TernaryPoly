module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Transport

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeOrbitStabilizers
open ModThreeGoodAction RelativePermutationIndices RelativeOrbitTransport
open RelativeStabilizerCoordinates RelativeStabilizerConjugacy RelativeStabilizerConsumer

/-- The point actions are the literal complementary index permutations. -/
instance badLineMulAction : MulAction K BadLine where
  smul := fun g L => badLineAction g L
  one_smul L := by apply Subtype.ext; apply Subtype.ext; exact act_one _
  mul_smul g h L := by apply Subtype.ext; apply Subtype.ext; exact act_mul g h _
instance badPlaneMulAction : MulAction K BadPlane where
  smul := fun g P => badPlaneAction g P
  one_smul P := by apply Subtype.ext; apply Subtype.ext; exact act_one _
  mul_smul g h P := by apply Subtype.ext; apply Subtype.ext; exact act_mul g h _
instance bbMulAction : MulAction K BB where
  smul := fun g e => bbAction g e
  one_smul e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> exact act_one _
  mul_smul g h e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> exact act_mul g h _
instance bgMulAction : MulAction K BG where
  smul := fun g e => bgAction g e
  one_smul e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> exact act_one _
  mul_smul g h e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> exact act_mul g h _

instance badLinePretransitive : MulAction.IsPretransitive K BadLine :=
  MulAction.IsPretransitive.of_orbit badLine_transitive
instance badPlanePretransitive : MulAction.IsPretransitive K BadPlane :=
  MulAction.IsPretransitive.of_orbit badPlane_transitive
instance bbPretransitive : MulAction.IsPretransitive K BB :=
  MulAction.IsPretransitive.of_orbit bb_transitive
instance bgPretransitive : MulAction.IsPretransitive K BG :=
  MulAction.IsPretransitive.of_orbit bg_transitive

/-- The exact named row-e3 subgroup transported into the original K. -/
def conjugateGroup (H : Subgroup IntegralGL) : Subgroup K :=
  (H.comap K3.subtype).map K3EquivK.toMonoidHom

theorem mem_conjugateGroup (H : Subgroup IntegralGL) (g : K3) :
    K3EquivK g ∈ conjugateGroup H ↔ g.val ∈ H := by
  constructor
  · rintro ⟨h,hh,he⟩
    have heq := K3EquivK.injective he
    subst h
    exact hh
  · intro h
    exact ⟨g,h,rfl⟩

def HL : Subgroup K := conjugateGroup HLGroup
def HP : Subgroup K := conjugateGroup HPGroup
def HBB : Subgroup K := conjugateGroup HBBGroup
def HBG : Subgroup K := conjugateGroup HBGGroup

theorem line_fixed_iff (g : K) : g • baseLine = baseLine ↔ act g (changeSpace L0) = changeSpace L0 := by
  constructor
  · intro h
    exact congrArg (fun L : BadLine => L.val.val) h
  · intro h
    exact Subtype.ext (Subtype.ext h)
theorem plane_fixed_iff (g : K) : g • basePlane = basePlane ↔ act g (changeSpace P0) = changeSpace P0 := by
  constructor
  · intro h
    exact congrArg (fun P : BadPlane => P.val.val) h
  · intro h
    exact Subtype.ext (Subtype.ext h)
theorem bb_fixed_iff (g : K) : g • baseBB = baseBB ↔
    act g (changeSpace L0) = changeSpace L0 ∧ act g (changeSpace P0) = changeSpace P0 := by
  constructor
  · intro h
    exact ⟨congrArg (fun e : BB => e.val.val.1.val) h,congrArg (fun e : BB => e.val.val.2.val) h⟩
  · intro h
    exact Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)))
theorem bg_fixed_iff (g : K) : g • baseBG = baseBG ↔
    act g (changeSpace L0) = changeSpace L0 ∧ act g (changeSpace P1) = changeSpace P1 := by
  constructor
  · intro h
    exact ⟨congrArg (fun e : BG => e.val.val.1.val) h,congrArg (fun e : BG => e.val.val.2.val) h⟩
  · intro h
    exact Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)))

/-- Each base-point stabilizer is exactly the corresponding parameterized integral subgroup. -/
theorem stabilizer_line : MulAction.stabilizer K baseLine = HL := by
  ext k
  obtain ⟨g,rfl⟩ := K3EquivK.surjective k
  rw [MulAction.mem_stabilizer_iff,line_fixed_iff]
  change Stabilizes (K3EquivK g).val (changeSpace L0) ↔ K3EquivK g ∈ conjugateGroup HLGroup
  rw [stabilizes_changeSpace_iff,mem_conjugateGroup,mem_HLGroup]
  exact ⟨fun h => ⟨g.property,h⟩,And.right⟩

theorem stabilizer_plane : MulAction.stabilizer K basePlane = HP := by
  ext k
  obtain ⟨g,rfl⟩ := K3EquivK.surjective k
  rw [MulAction.mem_stabilizer_iff,plane_fixed_iff]
  change Stabilizes (K3EquivK g).val (changeSpace P0) ↔ K3EquivK g ∈ conjugateGroup HPGroup
  rw [stabilizes_changeSpace_iff,mem_conjugateGroup,mem_HPGroup]
  exact ⟨fun h => ⟨g.property,h⟩,And.right⟩

theorem stabilizer_bb : MulAction.stabilizer K baseBB = HBB := by
  ext k
  obtain ⟨g,rfl⟩ := K3EquivK.surjective k
  rw [MulAction.mem_stabilizer_iff,bb_fixed_iff]
  change (Stabilizes (K3EquivK g).val (changeSpace L0) ∧
    Stabilizes (K3EquivK g).val (changeSpace P0)) ↔ K3EquivK g ∈ conjugateGroup HBBGroup
  rw [stabilizes_changeSpace_iff,stabilizes_changeSpace_iff,mem_conjugateGroup,mem_HBBGroup]
  exact ⟨fun h => ⟨g.property,h⟩,And.right⟩

theorem stabilizer_bg : MulAction.stabilizer K baseBG = HBG := by
  ext k
  obtain ⟨g,rfl⟩ := K3EquivK.surjective k
  rw [MulAction.mem_stabilizer_iff,bg_fixed_iff]
  change (Stabilizes (K3EquivK g).val (changeSpace L0) ∧
    Stabilizes (K3EquivK g).val (changeSpace P1)) ↔ K3EquivK g ∈ conjugateGroup HBGGroup
  rw [stabilizes_changeSpace_iff,stabilizes_changeSpace_iff,mem_conjugateGroup,mem_HBGGroup]
  exact ⟨fun h => ⟨g.property,h⟩,And.right⟩

end TernaryPoly.RelativeOrbitStabilizers
