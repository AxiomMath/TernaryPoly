module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.Cochains
public import TernaryPeriodPolynomials.Topology.SingularLocal.RestrictionVanishing

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSection
open CategoryTheory Limits HomologicalComplex
open CoveringSingularOrbits SingularLocalCoefficient SingularLocalConstant SingularLocalSupport
open EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
    (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (V : Rep.{0} ℚ G)

local instance : Fact (IsQuotientCoveringMap (𝟙 B) Unit) := ⟨identityCover B⟩

/-- Section trivialization preserves genuine vanishing of restriction to any base subset. -/
theorem cochainIso_hom_restriction_zero (A : Set B) (a : ℕ) (φ : (localCochains p hp.out V).X a)
    (hφ : (localRestriction p A V).f a φ = 0) :
    (localRestriction (𝟙 B) A (constantRep (ModuleCat.of ℚ V))).f a
      ((cochainIso p hp.out s hs V).hom.f a φ) = 0 := by
  apply (localRestriction_zero_iff (𝟙 B) (constantRep (ModuleCat.of ℚ V)) A a _).2
  intro σ
  have hz := (localRestriction_zero_iff p V A a φ).1 hφ σ
  change constantFiberEquiv p hp.out s hs V _ (φ _) = 0
  erw [hz,map_zero]

/-- Inverse section trivialization preserves the same actual restriction kernels. -/
theorem cochainIso_inv_restriction_zero (A : Set B) (a : ℕ)
    (φ : (localCochains (𝟙 B) (identityCover B) (constantRep (ModuleCat.of ℚ V))).X a)
    (hφ : (localRestriction (𝟙 B) A (constantRep (ModuleCat.of ℚ V))).f a φ = 0) :
    (localRestriction p A V).f a ((cochainIso p hp.out s hs V).inv.f a φ) = 0 := by
  apply (localRestriction_zero_iff p V A a _).2
  intro σ
  have hz := (localRestriction_zero_iff (𝟙 B) (constantRep (ModuleCat.of ℚ V)) A a φ).1 hφ σ
  change (constantFiberEquiv p hp.out s hs V _).symm (φ _) = 0
  erw [hz,map_zero]

/-- The actual section cochain map descends to the literal fixed-support kernels. -/
def supportHom (K : Set B) : supportCochains p V K ⟶
    supportCochains (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K :=
  kernel.lift _ (supportInclusion p V K ≫ (cochainIso p hp.out s hs V).hom) (by
    apply HomologicalComplex.hom_ext
    intro a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact cochainIso_hom_restriction_zero p s hs V Kᶜ a _
      (congrArg (fun f => f.f a φ) (kernel.condition (localRestriction p Kᶜ V))))

/-- The inverse section cochain map likewise descends to fixed supports. -/
def supportInv (K : Set B) : supportCochains (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K ⟶
    supportCochains p V K :=
  kernel.lift _ (supportInclusion (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K ≫
      (cochainIso p hp.out s hs V).inv) (by
    apply HomologicalComplex.hom_ext
    intro a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact cochainIso_inv_restriction_zero p s hs V Kᶜ a _
      (congrArg (fun f => f.f a φ)
        (kernel.condition (localRestriction (𝟙 B) Kᶜ (constantRep (ModuleCat.of ℚ V))))))

theorem supportHom_inclusion (K : Set B) : supportHom p s hs V K ≫
    supportInclusion (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K =
      supportInclusion p V K ≫ (cochainIso p hp.out s hs V).hom := kernel.lift_ι _ _ _

theorem supportInv_inclusion (K : Set B) : supportInv p s hs V K ≫ supportInclusion p V K =
    supportInclusion (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K ≫
      (cochainIso p hp.out s hs V).inv := kernel.lift_ι _ _ _

/-- A genuine support cochain isomorphism, preserving the literal ambient cochain. -/
def supportIso (K : Set B) : supportCochains p V K ≅
    supportCochains (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K where
  hom := supportHom p s hs V K
  inv := supportInv p s hs V K
  hom_inv_id := by
    apply (cancel_mono (supportInclusion p V K)).mp
    rw [Category.assoc,supportInv_inclusion,← Category.assoc,supportHom_inclusion,
      Category.assoc,Iso.hom_inv_id,Category.comp_id,Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (supportInclusion (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K)).mp
    rw [Category.assoc,supportHom_inclusion,← Category.assoc,supportInv_inclusion,
      Category.assoc,Iso.inv_hom_id,Category.comp_id,Category.id_comp]

/-- Section trivialization commutes with actual enlargement of compact supports. -/
theorem supportIso_natural (K L : Set B) (hKL : K ⊆ L) :
    supportMap p V K L hKL ≫ (supportIso p s hs V L).hom =
      (supportIso p s hs V K).hom ≫ supportMap (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K L hKL := by
  apply (cancel_mono (supportInclusion (𝟙 B) (constantRep (ModuleCat.of ℚ V)) L)).mp
  change (supportMap p V K L hKL ≫ supportHom p s hs V L) ≫ _ =
    (supportHom p s hs V K ≫ supportMap (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K L hKL) ≫ _
  rw [Category.assoc,supportHom_inclusion,← Category.assoc,supportMap_inclusion,
    Category.assoc,supportMap_inclusion,supportHom_inclusion]

end TernaryPoly.SingularLocalSection
