module

public import TernaryPeriodPolynomials.Topology.CoverGroup.GroupReindexSupport
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryForget

@[expose] public section


/-! Honest deck-group reindexing preserves the literal compact-support-forgetting map. -/
noncomputable section
namespace TernaryPoly.CoverGroupReindex
open CategoryTheory Limits HomologicalComplex TopologicalSpace EquivariantSingularSmall
  SingularLocalCoefficient SingularLocalSupport CompactInteriorRelativeBoundary

variable {G H : Type} [Group G] [Group H] (e : H ≃* G)
  {E B : TopCat.{0}} [MulAction H E] [MulAction G E]
  [ContinuousConstSMul H E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hH : Fact (IsQuotientCoveringMap p H)] [hG : Fact (IsQuotientCoveringMap p G)]
  (hact : ∀ (h : H) (x : E), h • x = e h • x) (V : Rep.{0} ℚ G)

def ordinaryIso (k : ℕ) : (localCochains p hG.out V).homology k ≅
    (localCochains p hH.out (Rep.res e.toMonoidHom V)).homology k :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) k).mapIso
    (cochainIso e p hH.out hG.out hact V)

theorem compactIso_forget (k : ℕ) :
    (compactIso e p hact V k).hom ≫ compactForget p (Rep.res e.toMonoidHom V) k =
      compactForget p V k ≫ (ordinaryIso e p hact V k).hom := by
  apply colimit.hom_ext
  intro K
  change compactClassMap p V K k ≫ _ = compactClassMap p V K k ≫ _
  erw [← Category.assoc, compactIso_classMap, Category.assoc, compactForget_classMap,
    ← Category.assoc, compactForget_classMap]
  change homologyMap (supportIso e p hact V K).hom k ≫
      homologyMap (supportInclusion p (Rep.res e.toMonoidHom V) K) k =
    homologyMap (supportInclusion p V K) k ≫ homologyMap (cochainIso e p hH.out hG.out hact V).hom k
  rw [← homologyMap_comp, ← homologyMap_comp, supportIso_inclusion]

include hact in
theorem compactForget_eq_zero_iff (k : ℕ) :
    compactForget p (Rep.res e.toMonoidHom V) k = 0 ↔ compactForget p V k = 0 := by
  constructor
  · intro hz
    apply (cancel_mono (ordinaryIso e p hact V k).hom).mp
    rw [zero_comp, ← compactIso_forget, hz, comp_zero]
  · intro hz
    apply (cancel_epi (compactIso e p hact V k).hom).mp
    rw [comp_zero, compactIso_forget, hz, zero_comp]

end TernaryPoly.CoverGroupReindex
