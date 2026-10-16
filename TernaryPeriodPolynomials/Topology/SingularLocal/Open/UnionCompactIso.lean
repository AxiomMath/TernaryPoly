module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionCompactRepresentatives

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport EquivariantSingularSmall
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]
  (U : ℕ → Opens B) (hU : Monotone U) (hcover : (⋃ i, (U i : Set B)) = Set.univ)
include hcover

/-- Every actual ambient compact-support class is the extension of a class at one stage. -/
theorem compactColimitMap_surjective (a : ℕ) :
    Function.Surjective (compactColimitMap p V U hU a) := by
  intro x
  obtain ⟨K,z,rfl⟩ := compactClass_exists_rep p V a x
  obtain ⟨i,hKi⟩ := compact_subset_stage U hU hcover K K.isCompact
  refine ⟨colimit.ι (compactDiagram p V U hU a) i (classInOpen p V (U i) K hKi a z),?_⟩
  have hi := congrArg (fun f => f (classInOpen p V (U i) K hKi a z)) (compactColimitMap_ι p V U hU a i)
  exact hi.trans (congrArg (fun f => f z) (classInOpen_extension p V (U i) K hKi a))

/-- No new compact-support relation appears after taking the increasing-open union:
a vanishing ambient image already vanishes at a later stage. -/
theorem compactColimitMap_injective (a : ℕ) :
    Function.Injective (compactColimitMap p V U hU a) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  obtain ⟨i,z,rfl⟩ := Concrete.colimit_exists_rep (compactDiagram p V U hU a) x
  have hx' : compactColimitMap p V U hU a (colimit.ι (compactDiagram p V U hU a) i z) = 0 := hx
  have hz : openExtension p V (U i) a z = 0 :=
    (congrArg (fun f => f z) (compactColimitMap_ι p V U hU a i)).symm.trans hx'
  obtain ⟨j,hij,hzj⟩ := compact_stage_zero p V U hU hcover a i z hz
  have h := congrArg (fun f => f z) (colimit.w (compactDiagram p V U hU a) (homOfLE hij))
  change colimit.ι (compactDiagram p V U hU a) j
      (openExtensionBetween p V (U i) (U j) (hU hij) a z) =
    colimit.ι (compactDiagram p V U hU a) i z at h
  exact h.symm.trans ((congrArg (colimit.ι (compactDiagram p V U hU a) j) hzj).trans (map_zero _))

/-- The canonical map from actual compact-support cohomology over an increasing open
cover to ambient compact-support cohomology is an isomorphism. -/
theorem compactColimitMap_isIso (a : ℕ) : IsIso (compactColimitMap p V U hU a) := by
  let e := LinearEquiv.ofBijective (compactColimitMap p V U hU a).hom
    ⟨compactColimitMap_injective p V U hU hcover a, compactColimitMap_surjective p V U hU hcover a⟩
  change IsIso e.toModuleIso.hom
  infer_instance

/-- Actual compact-support cohomology commutes with an increasing union of open sets. -/
def compactColimitIso (a : ℕ) : colimit (compactDiagram p V U hU a) ≅ compactCohomology p V a := by
  have := compactColimitMap_isIso p V U hU hcover a
  exact asIso (compactColimitMap p V U hU a)

/-- The continuity isomorphism uses exactly the canonical map induced by actual open extensions. -/
theorem compactColimitIso_hom (a : ℕ) :
    (compactColimitIso p V U hU hcover a).hom = compactColimitMap p V U hU a := rfl

end TernaryPoly.SingularLocalOpenUnion
