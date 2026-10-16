module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Cohomology
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section

noncomputable section
namespace TernaryPoly.CompactOrdinaryCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCoefficient EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The canonical compact-support-to-ordinary map, defined on every genuine support representative. -/
def compactToOrdinary (k : ℕ) :
    compactCohomology p V k ⟶ (localCochains p hp.out V).homology k :=
  compactCohomologyDesc p V k _
    (fun K => homologyMap (supportInclusion p V (K : Set B)) k)
    (fun K L hKL => by
      rw [← homologyMap_comp]
      exact congrArg (fun f => homologyMap f k) (supportMap_inclusion p V (K : Set B) (L : Set B) hKL))

/-- The compact-support-to-ordinary map is exactly support forgetting on each fixed-support class. -/
theorem compactToOrdinary_classMap (K : Compacts B) (k : ℕ) :
    compactClassMap p V K k ≫ compactToOrdinary p V k =
      homologyMap (supportInclusion p V (K : Set B)) k :=
  compactCohomologyDesc_ι p V k _ _ _ K

/-- The exact representative formula, without changing the underlying local cochain. -/
theorem compactToOrdinary_apply (K : Compacts B) (k : ℕ)
    (x : (supportCochains p V (K : Set B)).homology k) :
    compactToOrdinary p V k (compactClassMap p V K k x) =
      homologyMap (supportInclusion p V (K : Set B)) k x :=
  congrArg (fun f => f x) (compactToOrdinary_classMap p V K k)

/-- Restriction to the actual empty base subset is zero. -/
theorem restriction_empty_zero : localRestriction p (∅ : Set B) V = 0 := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext σ
  exact False.elim (isEmptyElim (CoveringSingularOrbits.atVertex σ))

/-- At the whole-space support the literal support inclusion is already a cochain isomorphism. -/
instance supportInclusion_univ_isIso : IsIso (supportInclusion p V Set.univ) := by
  change IsIso (kernel.ι (localRestriction p (Set.univ : Set B)ᶜ V))
  rw [Set.compl_univ, restriction_empty_zero]
  infer_instance

/-- Actual whole-support cochains equal ordinary local cochains through their literal inclusion. -/
def topSupportIso : supportCochains p V Set.univ ≅ localCochains p hp.out V :=
  asIso (supportInclusion p V Set.univ)

@[simp] theorem topSupportIso_hom : (topSupportIso p V).hom = supportInclusion p V Set.univ := rfl

/-- The corresponding whole-support homology isomorphism retains the actual cochain inclusion. -/
def topSupportHomologyIso (k : ℕ) :
    (supportCochains p V Set.univ).homology k ≅ (localCochains p hp.out V).homology k :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) k).mapIso (topSupportIso p V)

@[simp] theorem topSupportHomologyIso_hom (k : ℕ) :
    (topSupportHomologyIso p V k).hom = homologyMap (supportInclusion p V Set.univ) k := rfl

variable [CompactSpace B]

/-- On an actual compact base, its top compact support is terminal and its genuine colimit map
is an isomorphism. No replacement compact-cohomology definition is used. -/
instance compactClassTop_isIso (k : ℕ) : IsIso (compactClassMap p V (⊤ : Compacts B) k) :=
  (colimit.isColimit (compactCohomologyDiagram p V k)).isIso_ι_app_of_isTerminal
    (⊤ : Compacts B) isTerminalTop

/-- The actual support-forgetting map is an isomorphism on every compact base. -/
instance compactToOrdinary_isIso (k : ℕ) : IsIso (compactToOrdinary p V k) := by
  have : IsIso (compactClassMap p V (⊤ : Compacts B) k ≫ compactToOrdinary p V k) := by
    rw [compactToOrdinary_classMap]
    change IsIso (homologyMap (supportInclusion p V Set.univ) k)
    infer_instance
  exact IsIso.of_isIso_comp_left (compactClassMap p V (⊤ : Compacts B) k) (compactToOrdinary p V k)

/-- The canonical compact-to-ordinary comparison with its literal support-forgetting forward map. -/
def compactOrdinaryIso (k : ℕ) :
    compactCohomology p V k ≅ (localCochains p hp.out V).homology k :=
  asIso (compactToOrdinary p V k)

@[simp] theorem compactOrdinaryIso_hom (k : ℕ) :
    (compactOrdinaryIso p V k).hom = compactToOrdinary p V k := rfl

/-- The inverse comparison is precisely the genuine top-support representative map. -/
theorem compactOrdinaryIso_inv_top (k : ℕ) :
    (compactOrdinaryIso p V k).inv =
      (topSupportHomologyIso p V k).inv ≫ compactClassMap p V (⊤ : Compacts B) k := by
  apply (cancel_epi (topSupportHomologyIso p V k).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  change homologyMap (supportInclusion p V ((⊤ : Compacts B) : Set B)) k ≫
    (compactOrdinaryIso p V k).inv = _
  rw [← compactToOrdinary_classMap p V (⊤ : Compacts B) k]
  change (compactClassMap p V (⊤ : Compacts B) k ≫ (compactOrdinaryIso p V k).hom) ≫
    (compactOrdinaryIso p V k).inv = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end TernaryPoly.CompactOrdinaryCap
