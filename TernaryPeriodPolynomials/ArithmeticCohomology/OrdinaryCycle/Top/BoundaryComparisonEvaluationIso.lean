module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonSplitting

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall

variable {G : Type} [Group G] (C : ChainComplex (Rep.{0} ℚ G) ℕ)
  (W : Rep.{0} ℚ G)

/-- The actual cocycle represented by a degree-two equivariant cochain annihilating boundaries. -/
def degreeTwoCocycle (c : C.X 2 ⟶ W) (hc : C.d 3 2 ≫ c = 0) :
    (homCochains C W).cycles 2 :=
  ((homCochains C W).sc 2).cyclesMk c (by
    change C.d ((ComplexShape.up ℕ).next 2) 2 ≫ c = 0
    erw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
    exact hc)

/-- The constructed cocycle retains precisely the supplied cochain. -/
theorem degreeTwoCocycle_value (c : C.X 2 ⟶ W) (hc : C.d 3 2 ≫ c = 0) :
    cocycleValue C W 2 (degreeTwoCocycle C W c hc) = c :=
  ((homCochains C W).sc 2).i_cyclesMk _ _

variable (s : (cycleSequence C 1).Splitting)

/-- The cycle retraction sends an actual incoming boundary to its actual cycle-valued boundary. -/
theorem degreeTwoRetraction_boundary : C.d 3 2 ≫ s.r = C.toCycles 3 2 := by
  have hr : C.iCycles 2 ≫ s.r = 𝟙 _ := s.f_r
  erw [← C.toCycles_i 3 2, Category.assoc, hr, Category.comp_id]

/-- Extend an equivariant functional on actual H2 to an actual degree-two cochain. -/
def extendedHomologyFunctional (φ : C.homology 2 ⟶ W) : C.X 2 ⟶ W :=
  s.r ≫ C.homologyπ 2 ≫ φ

/-- This extension is an actual cocycle because the original homology projection kills boundaries. -/
theorem extendedHomologyFunctional_boundary (φ : C.homology 2 ⟶ W) :
    C.d 3 2 ≫ extendedHomologyFunctional C W s φ = 0 := by
  dsimp only [extendedHomologyFunctional]
  erw [← Category.assoc, degreeTwoRetraction_boundary, ← Category.assoc,
    toCycles_comp_homologyπ, zero_comp]

/-- Evaluation of the extended cocycle recovers the supplied homology functional exactly. -/
theorem extendedHomologyFunctional_evaluation (φ : C.homology 2 ⟶ W) :
    cocycleEvaluation C W 2 (degreeTwoCocycle C W (extendedHomologyFunctional C W s φ)
      (extendedHomologyFunctional_boundary C W s φ)) = φ := by
  apply (cancel_epi (C.homologyπ 2)).mp
  erw [cocycleEvaluation_projection, degreeTwoCocycle_value]
  change C.iCycles 2 ≫ (s.r ≫ C.homologyπ 2 ≫ φ) = _
  have hr : C.iCycles 2 ≫ s.r = 𝟙 _ := s.f_r
  erw [← Category.assoc, hr, Category.id_comp]

include s in
/-- A split cycle inclusion makes canonical degree-two evaluation surjective. -/
theorem homologyEvaluationTwo_surjective : Function.Surjective (homologyEvaluation C W 2) := by
  intro φ
  let x := degreeTwoCocycle C W (extendedHomologyFunctional C W s φ)
    (extendedHomologyFunctional_boundary C W s φ)
  refine ⟨(homCochains C W).homologyπ 2 x, ?_⟩
  have h := congrArg (fun f => f x) (homologyEvaluation_projection C W 2)
  exact h.trans (extendedHomologyFunctional_evaluation C W s φ)

variable (r : C.X 1 ⟶ C.cycles 1) (hr : C.iCycles 1 ≫ r = 𝟙 _)

include hr in
/-- An actual cochain vanishing on degree-two cycles is an explicit actual coboundary. -/
theorem vanishedCycleFunctional_coboundary (c : C.X 2 ⟶ W) (hc : C.iCycles 2 ≫ c = 0) :
    C.d 2 1 ≫ (r ≫ s.s ≫ c) = c := by
  have hid : (s.r ≫ C.iCycles 2 : C.X 2 ⟶ C.X 2) + (C.toCycles 2 1 ≫ s.s : C.X 2 ⟶ C.X 2) = 𝟙 (C.X 2) := s.id
  have hr' : C.d 2 1 ≫ r = C.toCycles 2 1 := by
    erw [← C.toCycles_i 2 1, Category.assoc, hr, Category.comp_id]
  have hvan : (s.r ≫ C.iCycles 2) ≫ c = 0 := by
    erw [Category.assoc, hc, comp_zero]
  have h : ((s.r ≫ C.iCycles 2 : C.X 2 ⟶ C.X 2) + (C.toCycles 2 1 ≫ s.s : C.X 2 ⟶ C.X 2)) ≫ c = c := by rw [hid, Category.id_comp]
  erw [Preadditive.add_comp, hvan, zero_add, Category.assoc] at h
  erw [← Category.assoc, hr']
  exact h

include s r hr in
/-- A cocycle with zero canonical functional is an actual coboundary and has zero class. -/
theorem homologyEvaluationTwo_zero (x : (homCochains C W).cycles 2)
    (hx : cocycleEvaluation C W 2 x = 0) : (homCochains C W).homologyπ 2 x = 0 := by
  have hc : C.iCycles 2 ≫ cocycleValue C W 2 x = 0 := by
    erw [← cocycleEvaluation_projection C W 2 x, hx, comp_zero]
  let b := r ≫ s.s ≫ cocycleValue C W 2 x
  have hb : C.d 2 1 ≫ b = cocycleValue C W 2 x :=
    vanishedCycleFunctional_coboundary C W s r hr _ hc
  have he : (homCochains C W).toCycles 1 2 b = x := by
    apply (ModuleCat.mono_iff_injective ((homCochains C W).iCycles 2)).mp inferInstance
    exact (congrArg (fun f => f b) ((homCochains C W).toCycles_i 1 2)).trans hb
  erw [← he]
  exact congrArg (fun f => f b) ((homCochains C W).toCycles_comp_homologyπ 1 2)

include s r hr in
/-- With the actual low-degree splittings, canonical evaluation is injective. -/
theorem homologyEvaluationTwo_injective : Function.Injective (homologyEvaluation C W 2) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective ((homCochains C W).homologyπ 2)).mp
    inferInstance y
  apply homologyEvaluationTwo_zero C W s r hr x
  have h := congrArg (fun f => f x) (homologyEvaluation_projection C W 2)
  exact h.symm.trans hy

include s r hr in
/-- The canonical evaluation itself is an isomorphism under low-degree splittings.
The splittings prove bijectivity; they do not replace or normalize the canonical map. -/
theorem homologyEvaluationTwo_isIso : IsIso (homologyEvaluation C W 2) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨homologyEvaluationTwo_injective C W s r hr, homologyEvaluationTwo_surjective C W s⟩

end TernaryPoly.OrdinaryTopBoundaryComparison
