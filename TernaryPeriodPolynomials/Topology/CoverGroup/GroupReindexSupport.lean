module

public import TernaryPeriodPolynomials.Topology.CoverGroup.GroupReindexRestriction
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Cohomology

@[expose] public section

/-! Group reindexing preserves the genuine support kernels and directed compact-support diagrams. -/
noncomputable section
namespace TernaryPoly.CoverGroupReindex
open CategoryTheory Limits HomologicalComplex TopologicalSpace EquivariantSingularSmall
  SingularLocalCoefficient SingularLocalSupport

variable {G H : Type} [Group G] [Group H] (e : H ≃* G)
  {E B : TopCat.{0}} [MulAction H E] [MulAction G E]
  [ContinuousConstSMul H E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hH : Fact (IsQuotientCoveringMap p H)] [hG : Fact (IsQuotientCoveringMap p G)]
  (hact : ∀ (h : H) (x : E), h • x = e h • x) (V : Rep.{0} ℚ G)

/-- The actual restriction kernels are transported by the existing categorical kernel isomorphism. -/
def supportIso (K : Set B) : supportCochains p V K ≅ supportCochains p (Rep.res e.toMonoidHom V) K :=
  kernel.mapIso (localRestriction p Kᶜ V) (localRestriction p Kᶜ (Rep.res e.toMonoidHom V))
    (cochainIso e p hH.out hG.out hact V) (restrictedCochainIso e p hact V Kᶜ)
    (cochainIso_restriction e p hact V Kᶜ).symm

theorem supportIso_inclusion (K : Set B) :
    (supportIso e p hact V K).hom ≫ supportInclusion p (Rep.res e.toMonoidHom V) K =
      supportInclusion p V K ≫ (cochainIso e p hH.out hG.out hact V).hom := by
  unfold supportIso
  erw [kernel.lift_ι]

theorem supportIso_natural (K L : Set B) (hKL : K ⊆ L) :
    supportMap p V K L hKL ≫ (supportIso e p hact V L).hom =
      (supportIso e p hact V K).hom ≫ supportMap p (Rep.res e.toMonoidHom V) K L hKL := by
  apply (cancel_mono (supportInclusion p (Rep.res e.toMonoidHom V) L)).mp
  rw [Category.assoc, supportIso_inclusion, ← Category.assoc, supportMap_inclusion,
    Category.assoc, supportMap_inclusion, supportIso_inclusion]

def compactDiagramIso (k : ℕ) : compactCohomologyDiagram p V k ≅
    compactCohomologyDiagram p (Rep.res e.toMonoidHom V) k :=
  NatIso.ofComponents (fun K => (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) k).mapIso
    (supportIso e p hact V (K : Set B))) (fun {K L} f => by
      change homologyMap (supportMap p V K L (leOfHom f)) k ≫
        homologyMap (supportIso e p hact V L).hom k =
          homologyMap (supportIso e p hact V K).hom k ≫
            homologyMap (supportMap p (Rep.res e.toMonoidHom V) K L (leOfHom f)) k
      rw [← homologyMap_comp, ← homologyMap_comp, supportIso_natural])

/-- The directed colimits are the original compactly supported local cohomology groups. -/
def compactIso (k : ℕ) : compactCohomology p V k ≅ compactCohomology p (Rep.res e.toMonoidHom V) k :=
  colim.mapIso (compactDiagramIso e p hact V k)

theorem compactIso_classMap (K : Compacts B) (k : ℕ) :
    compactClassMap p V K k ≫ (compactIso e p hact V k).hom =
      homologyMap (supportIso e p hact V K).hom k ≫ compactClassMap p (Rep.res e.toMonoidHom V) K k := by
  unfold compactIso compactClassMap
  erw [Functor.mapIso_hom, colim_map, ι_colimMap]
  rfl

end TernaryPoly.CoverGroupReindex
