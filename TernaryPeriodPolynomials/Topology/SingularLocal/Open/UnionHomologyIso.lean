module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionHomologyRepresentatives

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalHomology SingularLocalExcision EquivariantSingularSmall
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  (U : ℕ → Opens B) (hU : Monotone U) (hcover : (⋃ i, (U i : Set B)) = Set.univ)
include hcover

/-- Genuine compact finite cycle carriers make the actual homology colimit map surjective. -/
theorem homologyColimitMap_surjective (b : ℕ) :
    Function.Surjective (homologyColimitMap p V U hU b) := by
  intro x
  obtain ⟨i,z,hz⟩ := homology_stage_exists p V U hU hcover b x
  exact ⟨colimit.ι (homologyDiagram p V U hU b) i z,
    (congrArg (fun f => f z) (homologyColimitMap_ι p V U hU b i)).trans hz⟩

/-- Genuine compact finite bounding-chain carriers make the actual homology colimit
map injective: every ambient relation is realized in one later open stage. -/
theorem homologyColimitMap_injective (b : ℕ) :
    Function.Injective (homologyColimitMap p V U hU b) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  obtain ⟨i,z,rfl⟩ := Concrete.colimit_exists_rep (homologyDiagram p V U hU b) x
  have hx' : homologyColimitMap p V U hU b (colimit.ι (homologyDiagram p V U hU b) i z) = 0 := hx
  have hz : homologyMap (localInclusion p (U i) V) b z = 0 :=
    (congrArg (fun f => f z) (homologyColimitMap_ι p V U hU b i)).symm.trans hx'
  obtain ⟨j,hij,hzj⟩ := homology_stage_zero p V U hU hcover b i z hz
  have h := congrArg (fun f => f z) (colimit.w (homologyDiagram p V U hU b) (homOfLE hij))
  change colimit.ι (homologyDiagram p V U hU b) j
      (homologyMap (nestedLocalInclusion p (U i) (U j) (hU hij) V) b z) =
    colimit.ι (homologyDiagram p V U hU b) i z at h
  exact h.symm.trans ((congrArg (colimit.ι (homologyDiagram p V U hU b) j) hzj).trans (map_zero _))

/-- The actual comparison from increasing-open local homology to ambient local homology
is an isomorphism for every rational coefficient representation. -/
theorem homologyColimitMap_isIso (b : ℕ) : IsIso (homologyColimitMap p V U hU b) := by
  let e := LinearEquiv.ofBijective (homologyColimitMap p V U hU b).hom
    ⟨homologyColimitMap_injective p V U hU hcover b, homologyColimitMap_surjective p V U hU hcover b⟩
  change IsIso e.toModuleIso.hom
  infer_instance

/-- Ordinary local-coefficient homology commutes with an increasing open union through
the canonical map induced by actual restricted-cover chain inclusions. -/
def homologyColimitIso (b : ℕ) : colimit (homologyDiagram p V U hU b) ≅
    (localChains p hp.out V).homology b := by
  have := homologyColimitMap_isIso p V U hU hcover b
  exact asIso (homologyColimitMap p V U hU b)

/-- The homology continuity isomorphism has exactly the actual inclusion-induced map. -/
theorem homologyColimitIso_hom (b : ℕ) :
    (homologyColimitIso p V U hU hcover b).hom = homologyColimitMap p V U hU b := rfl

end TernaryPoly.SingularLocalOpenUnion
