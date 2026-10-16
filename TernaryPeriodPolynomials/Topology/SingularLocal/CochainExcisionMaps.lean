module

public import TernaryPeriodPolynomials.Topology.SingularLocal.RestrictionSurjective
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisLocalMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCochainExcision
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open EquivariantSingularSmall EquivariantSingularMayerVietoris SingularLocalCoefficient SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- Actual relative cochains for the ambient pair (B,A). -/
abbrev relativeCochains (A : Set B) := kernel (localRestriction p A V)

/-- Actual relative cochains for the neighborhood pair (D,A∩D). -/
abbrev neighborhoodCochains (A D : Set B) :=
  kernel (nestedLocalRestriction p (A ∩ D) D Set.inter_subset_right V)

/-- The two actual restrictions from ambient cochains to the intersection coincide. -/
theorem restriction_square (A D : Set B) :
    localRestriction p A V ≫ nestedLocalRestriction p (A ∩ D) A Set.inter_subset_left V =
      localRestriction p D V ≫ nestedLocalRestriction p (A ∩ D) D Set.inter_subset_right V := by
  rw [localRestriction_nested,localRestriction_nested]

/-- The genuine cochain excision map is the actual kernel map of restriction to the neighborhood. -/
def cochainExcisionMap (A D : Set B) : relativeCochains p V A ⟶ neighborhoodCochains p V A D :=
  kernel.map _ _ (localRestriction p D V)
    (nestedLocalRestriction p (A ∩ D) A Set.inter_subset_left V) (restriction_square p V A D)

/-- The actual relative restriction preserves its ambient cochain representative. -/
theorem cochainExcisionMap_inclusion (A D : Set B) :
    cochainExcisionMap p V A D ≫ kernel.ι (nestedLocalRestriction p (A ∩ D) D Set.inter_subset_right V) =
      kernel.ι (localRestriction p A V) ≫ localRestriction p D V := by
  exact kernel.lift_ι _ _ _

variable (A D : Opens B) (hAD : A ⊔ D = ⊤)

/-- Restriction of actual small cochains to the left member of the cover. -/
abbrev smallLeft : homCochains (localCoverChains p A D hAD) V ⟶
    localCochains (restrictedProjection p A) (restrictedQuotientCovering p A) V := (localSmallSequence p A D hAD V).f ≫ biprod.fst

/-- Restriction of actual small cochains to the right member of the cover. -/
abbrev smallRight : homCochains (localCoverChains p A D hAD) V ⟶
    localCochains (restrictedProjection p D) (restrictedQuotientCovering p D) V := (localSmallSequence p A D hAD V).f ≫ biprod.snd

/-- Ambient-to-small comparison retains the actual left restriction. -/
theorem localToSmall_left : localToSmall p A D hAD V ≫ smallLeft p V A D hAD =
    localRestriction p A V := by
  unfold smallLeft
  erw [← Category.assoc,localSmallSequence_f,biprod.lift_fst]

/-- Ambient-to-small comparison retains the actual right restriction. -/
theorem localToSmall_right : localToSmall p A D hAD V ≫ smallRight p V A D hAD =
    localRestriction p D V := by
  unfold smallRight
  erw [← Category.assoc,localSmallSequence_f,biprod.lift_snd]

/-- Restriction of actual small cochains to the left cover member is an epimorphism. -/
instance smallLeft_epi : Epi (smallLeft p V A D hAD) :=
  epi_of_epi_fac (localToSmall_left p V A D hAD)

/-- The actual small cochain restrictions agree on the intersection. -/
theorem small_square : smallRight p V A D hAD ≫
      nestedLocalRestriction p ((A : Set B) ∩ (D : Set B)) D Set.inter_subset_right V =
    smallLeft p V A D hAD ≫
      nestedLocalRestriction p ((A : Set B) ∩ (D : Set B)) A Set.inter_subset_left V := by
  have hz := (localSmallSequence p A D hAD V).zero
  rw [localSmallSequence_g] at hz
  have hf : (localSmallSequence p A D hAD V).f =
      biprod.lift (smallLeft p V A D hAD) (smallRight p V A D hAD) := by
    apply biprod.hom_ext
    · erw [biprod.lift_fst]; rfl
    · erw [biprod.lift_snd]; rfl
  rw [hf] at hz
  erw [biprod.lift_desc,Preadditive.comp_neg,← sub_eq_add_neg,sub_eq_zero] at hz
  exact hz.symm

end TernaryPoly.SingularLocalCochainExcision
