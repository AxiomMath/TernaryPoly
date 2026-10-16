module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopyCochains
public import TernaryPeriodPolynomials.Topology.Singular.CoverPullbackComposition

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall
open EquivariantSingularPairHomotopy SingularCoverNaturality
variable {G : Type} [Group G] {E E' E'' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
  [MulAction G E''] [ContinuousConstSMul G E'']
  (S : Set E) [Fact (InvariantSet G E S)] (T : Set E') [Fact (InvariantSet G E' T)]
  (U : Set E'') [Fact (InvariantSet G E'' U)]

/-- Actual equivariant relative chain maps respect the literal composition of pair maps. -/
theorem pairRelativeMap_comp (F : E ⟶ E') (H : E' ⟶ E'')
    (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hH : ∀ (g : G) (x : E'), H (g • x) = g • H x)
    (hST : Set.MapsTo F S T) (hTU : Set.MapsTo H T U) :
    relativeMap S T F hF hST ≫ relativeMap T U H hH hTU =
      relativeMap S U (F ≫ H) (fun g x => by change H (F (g • x)) = g • H (F x); rw [hF,hH])
        (fun _ hx => hTU (hST hx)) := by
  apply (cancel_epi (cokernel.π (inclusion G E S))).mp
  simp only [relativeMap,cokernel.map,Category.assoc,cokernel.π_desc_assoc,cokernel.π_desc]
  erw [← Category.assoc,← chainMap_comp]

/-- The literal identity pair map induces the identity on actual equivariant relative chains. -/
theorem pairRelativeMap_id : relativeMap S S (𝟙 E) (fun _ _ => rfl) (fun _ hx => hx) =
    𝟙 (relativeChains G E S) := by
  apply (cancel_epi (cokernel.π (inclusion G E S))).mp
  simp [relativeMap,cokernel.map,chainMap_id]

/-- The actual contravariant Hom pullback preserves identities. -/
theorem relativeHomPullback_id (V : Rep.{0} ℚ G) :
    relativeHomPullback S S (𝟙 E) (fun _ _ => rfl) (fun _ hx => hx) V =
      𝟙 (relativeHomCochains G E S V) := by
  unfold relativeHomPullback
  rw [pairRelativeMap_id]
  ext k c
  change (𝟙 _) ≫ c = c
  exact Category.id_comp c

/-- The actual relative Hom pullback respects contravariant composition of genuine pair maps. -/
theorem relativeHomPullback_comp (F : E ⟶ E') (H : E' ⟶ E'')
    (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hH : ∀ (g : G) (x : E'), H (g • x) = g • H x)
    (hST : Set.MapsTo F S T) (hTU : Set.MapsTo H T U) (V : Rep.{0} ℚ G) :
    relativeHomPullback T U H hH hTU V ≫ relativeHomPullback S T F hF hST V =
      relativeHomPullback S U (F ≫ H)
        (fun g x => by change H (F (g • x)) = g • H (F x); rw [hF,hH]) (fun _ hx => hTU (hST hx)) V := by
  unfold relativeHomPullback
  rw [← homPullback_comp,pairRelativeMap_comp]

end TernaryPoly.CompactInteriorRelativeBoundary
