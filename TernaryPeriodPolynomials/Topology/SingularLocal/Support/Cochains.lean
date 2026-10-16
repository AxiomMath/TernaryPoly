module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallRestrictedNaturality
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex SingularLocalCoefficient
open EquivariantSingularSmall EquivariantSingularMayerVietoris

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The actual geometric local-cochain restrictions compose for nested base subsets. -/
theorem localRestriction_nested (A D : Set B) (hAD : A ⊆ D) :
    localRestriction p D V ≫ nestedLocalRestriction p A D hAD V = localRestriction p A V := by
  apply (cancel_epi (cochainIso p hp.out V).hom).mp
  rw [← Category.assoc,← subordinateLocalIso_restriction p D V,Category.assoc,
    ← subordinateLocalIso_naturality p A D hAD V,← Category.assoc,← homPullback_comp]
  have he : subordinateMap G E (p ⁻¹' A) (p ⁻¹' D)
      (preimage_invariant p A) (preimage_invariant p D) (Set.preimage_mono hAD) ≫
        subordinateInclusion G E (p ⁻¹' D) (preimage_invariant p D) =
      subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A) := by
    apply HomologicalComplex.hom_ext
    intro k
    ext c
    rfl
  rw [he,subordinateLocalIso_restriction]

/-- Local cochains supported on K are the actual kernel of restriction to its complement. -/
abbrev supportCochains (K : Set B) : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  kernel (localRestriction p Kᶜ V)

/-- The literal inclusion of fixed-support local cochains into ambient local cochains. -/
abbrev supportInclusion (K : Set B) : supportCochains p V K ⟶ localCochains p hp.out V :=
  kernel.ι (localRestriction p Kᶜ V)

/-- Enlargement of support is the actual inclusion between the restriction kernels. -/
def supportMap (K L : Set B) (hKL : K ⊆ L) : supportCochains p V K ⟶ supportCochains p V L :=
  kernel.lift (localRestriction p Lᶜ V) (supportInclusion p V K) (by
    rw [← localRestriction_nested p V Lᶜ Kᶜ (Set.compl_subset_compl.mpr hKL),← Category.assoc,
      kernel.condition,zero_comp])

/-- Support enlargement retains the same actual ambient cochain. -/
@[simp] theorem supportMap_inclusion (K L : Set B) (hKL : K ⊆ L) :
    supportMap p V K L hKL ≫ supportInclusion p V L = supportInclusion p V K :=
  kernel.lift_ι _ _ _

/-- Equal supports induce the identity on the actual relative local-cochain complex. -/
@[simp] theorem supportMap_self (K : Set B) : supportMap p V K K (Set.Subset.refl K) = 𝟙 _ := by
  apply (cancel_mono (supportInclusion p V K)).mp
  simp

/-- Actual support-enlargement maps compose. -/
theorem supportMap_comp (K L M : Set B) (hKL : K ⊆ L) (hLM : L ⊆ M) :
    supportMap p V K L hKL ≫ supportMap p V L M hLM = supportMap p V K M (hKL.trans hLM) := by
  apply (cancel_mono (supportInclusion p V M)).mp
  simp [Category.assoc]

end TernaryPoly.SingularLocalSupport
