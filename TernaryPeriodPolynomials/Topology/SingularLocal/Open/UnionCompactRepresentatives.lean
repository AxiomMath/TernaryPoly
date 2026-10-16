module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionCompactDiagram

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport EquivariantSingularSmall
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]

/-- Every actual compact-cohomology class in an open set has an ambient compact support
and an actual ambient support class restricting to it. -/
theorem classInOpen_exists_rep (D : Opens B) (a : ℕ)
    (x : compactCohomology (restrictedProjection p D) V a) :
    ∃ (K : Compacts B) (hKD : (K : Set B) ⊆ D)
      (z : (supportCochains p V (K : Set B)).homology a), classInOpen p V D K hKD a z = x := by
  obtain ⟨K,z,rfl⟩ := compactClass_exists_rep (restrictedProjection p D) V a x
  refine ⟨openCompactImage D K,openCompactImage_subset D K,(openSupportIso p V D K a).inv z,?_⟩
  rw [classInOpen_image]
  change compactClassMap (restrictedProjection p D) V K a
    ((openSupportIso p V D K a).hom ((openSupportIso p V D K a).inv z)) = _
  exact congrArg (compactClassMap (restrictedProjection p D) V K a)
    (congrArg (fun f => f z) (openSupportIso p V D K a).inv_hom_id)

variable (U : ℕ → Opens B) (hU : Monotone U)
  (hcover : (⋃ i, (U i : Set B)) = Set.univ)
include hcover

/-- An actual open-stage class vanishing after extension to the ambient space vanishes
at a later stage of the increasing open cover. -/
theorem compact_stage_zero (a i : ℕ)
    (x : compactCohomology (restrictedProjection p (U i)) V a)
    (hx : openExtension p V (U i) a x = 0) :
    ∃ (j : ℕ) (hij : i ≤ j), openExtensionBetween p V (U i) (U j) (hU hij) a x = 0 := by
  obtain ⟨K,hKi,z,rfl⟩ := classInOpen_exists_rep p V (U i) a x
  have hz : compactClassMap p V K a z = 0 := by
    have h := congrArg (fun f => f z) (classInOpen_extension p V (U i) K hKi a)
    exact h.symm.trans hx
  obtain ⟨L,hKL,hzL⟩ := (compactClass_zero_iff p V a K z).mp hz
  obtain ⟨j,hLj⟩ := compact_subset_stage U hU hcover L L.isCompact
  let m := max i j
  have him : i ≤ m := le_max_left _ _
  have hLm : (L : Set B) ⊆ U j := hLj
  have hL : (L : Set B) ⊆ U m := hLm.trans (hU (le_max_right i j))
  refine ⟨m,him,?_⟩
  have hi := congrArg (fun f => f z) (classInOpen_between p V (U i) (U m) (hU him) K hKi a)
  change openExtensionBetween p V (U i) (U m) (hU him) a (classInOpen p V (U i) K hKi a z) = 0
  simp only [ModuleCat.comp_apply] at hi
  rw [hi]
  have h := congrArg (fun f => f z) (classInOpen_natural p V (U m) K L hKL hL a)
  exact h.symm.trans ((congrArg (classInOpen p V (U m) L hL a) hzL).trans (map_zero _))

end TernaryPoly.SingularLocalOpenUnion
