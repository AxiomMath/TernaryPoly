module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionCompactIso
public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionHomologyIso

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits

/-- A commuting square of actual colimit comparison maps transfers a pointwise
isomorphism of diagrams to an isomorphism of their actual ambient targets. -/
theorem isIso_of_colimit_square {F G : ℕ ⥤ ModuleCat.{0} ℚ} (α : F ⟶ G)
    (hα : ∀ i, IsIso (α.app i)) {M N : ModuleCat.{0} ℚ}
    (u : colimit F ⟶ M) (v : colimit G ⟶ N) (f : M ⟶ N)
    [IsIso u] [IsIso v] (hsquare : u ≫ f = colim.map α ≫ v) : IsIso f := by
  have : ∀ i, IsIso (α.app i) := hα
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact IsIso.of_isIso_fac_left hsquare

/-- Exact agreement of the actual maps on every stage supplies the required colimit
square; no unrelated rank isomorphism is used. -/
theorem isIso_of_stage_square {F G : ℕ ⥤ ModuleCat.{0} ℚ} (α : F ⟶ G)
    (hα : ∀ i, IsIso (α.app i)) {M N : ModuleCat.{0} ℚ}
    (u : colimit F ⟶ M) (v : colimit G ⟶ N) (f : M ⟶ N)
    [IsIso u] [IsIso v]
    (hstage : ∀ i, colimit.ι F i ≫ u ≫ f = α.app i ≫ colimit.ι G i ≫ v) : IsIso f := by
  apply isIso_of_colimit_square α hα u v f
  apply colimit.hom_ext
  intro i
  simpa only [colim_map,ι_colimMap_assoc] using hstage i

end TernaryPoly.SingularLocalOpenUnion
