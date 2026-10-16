module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory HomologicalComplex EquivariantSingularSmall

variable {G : Type} [Group G] (C : ChainComplex (Rep.{0} ℚ G) ℕ)
  (W : Rep.{0} ℚ G) (n : ℕ)

/-- The literal equivariant cochain represented by an actual cocycle. -/
def cocycleValue (x : (homCochains C W).cycles n) : C.X n ⟶ W :=
  (homCochains C W).iCycles n x

/-- An actual Hom cocycle annihilates the incoming chain boundary. -/
theorem cocycleValue_boundary (x : (homCochains C W).cycles n) :
    C.d (n + 1) n ≫ cocycleValue C W n x = 0 := by
  exact congrArg (fun f => f x) ((homCochains C W).iCycles_d n (n + 1))

/-- An actual equivariant cocycle descends on cycles to actual equivariant homology. -/
def cocycleEvaluation (x : (homCochains C W).cycles n) : C.homology n ⟶ W :=
  (C.sc n).descHomology (C.iCycles n ≫ cocycleValue C W n x) (by
    change (C.sc n).toCycles ≫ ((C.sc n).iCycles ≫ _) = 0
    erw [← Category.assoc, ShortComplex.toCycles_i]
    change C.d ((ComplexShape.down ℕ).prev n) n ≫ _ = 0
    rw [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
    exact cocycleValue_boundary C W n x)

/-- The descended functional evaluates a represented homology class by the original cochain. -/
theorem cocycleEvaluation_projection (x : (homCochains C W).cycles n) :
    C.homologyπ n ≫ cocycleEvaluation C W n x = C.iCycles n ≫ cocycleValue C W n x :=
  (C.sc n).π_descHomology _ _

/-- Descent of actual equivariant cocycles is rational-linear. -/
def cocycleEvaluationMap : (homCochains C W).cycles n ⟶
    ModuleCat.of ℚ (C.homology n ⟶ W) :=
  ModuleCat.ofHom {
    toFun := cocycleEvaluation C W n
    map_add' := fun x y => by
      apply (cancel_epi (C.homologyπ n)).mp
      erw [Preadditive.comp_add, cocycleEvaluation_projection C W n (x + y),
        cocycleEvaluation_projection C W n x, cocycleEvaluation_projection C W n y]
      dsimp [cocycleValue]
      erw [map_add, Preadditive.comp_add]
    map_smul' := fun r x => by
      apply (cancel_epi (C.homologyπ n)).mp
      erw [Linear.comp_smul, cocycleEvaluation_projection C W n (r • x),
        cocycleEvaluation_projection C W n x]
      dsimp [cocycleValue]
      erw [map_smul, Linear.comp_smul] }

/-- Coboundaries induce the zero equivariant homology functional. -/
theorem cocycleEvaluationMap_boundary :
    ((homCochains C W).sc n).toCycles ≫ cocycleEvaluationMap C W n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change cocycleEvaluation C W n (((homCochains C W).sc n).toCycles x) = 0
  apply (cancel_epi (C.homologyπ n)).mp
  erw [cocycleEvaluation_projection C W n (((homCochains C W).sc n).toCycles x), Limits.comp_zero]
  have h := congrArg (fun f => f x) (((homCochains C W).sc n).toCycles_i)
  change cocycleValue C W n (((homCochains C W).sc n).toCycles x) =
    C.d n ((ComplexShape.up ℕ).prev n) ≫ x at h
  erw [h, ← Category.assoc, C.iCycles_d, Limits.zero_comp]

/-- Canonical evaluation of actual Hom cohomology on actual chain homology.
This construction uses no exactness or projectivity assumption on equivariant Hom. -/
def homologyEvaluation : (homCochains C W).homology n ⟶
    ModuleCat.of ℚ (C.homology n ⟶ W) :=
  ((homCochains C W).sc n).descHomology (cocycleEvaluationMap C W n)
    (cocycleEvaluationMap_boundary C W n)

/-- The canonical homology evaluation retains the exact cocycle representative. -/
theorem homologyEvaluation_projection :
    (homCochains C W).homologyπ n ≫ homologyEvaluation C W n =
      cocycleEvaluationMap C W n :=
  ((homCochains C W).sc n).π_descHomology _ _

/-- Literal cochain-on-cycle evaluation, with neither scalar nor sign renormalization. -/
theorem homologyEvaluation_apply (x : (homCochains C W).cycles n) (z : C.cycles n) :
    (homologyEvaluation C W n ((homCochains C W).homologyπ n x)).hom
        (C.homologyπ n z) =
      (cocycleValue C W n x).hom (C.iCycles n z) := by
  have h := congrArg (fun f => f x) (homologyEvaluation_projection C W n)
  change homologyEvaluation C W n ((homCochains C W).homologyπ n x) =
    cocycleEvaluation C W n x at h
  erw [h]
  exact congrArg (fun f => f.hom z) (cocycleEvaluation_projection C W n x)

end TernaryPoly.OrdinaryTopBoundaryComparison
