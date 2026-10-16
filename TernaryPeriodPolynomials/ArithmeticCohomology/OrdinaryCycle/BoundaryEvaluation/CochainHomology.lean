module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonNaturality
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall OrdinaryTopBoundaryComparison

variable {G : Type} [Group G] (C : ChainComplex (Rep.{0} ℚ G) ℕ)
  (W : Rep.{0} ℚ G) (n : ℕ)

/-- An actual equivariant cochain annihilating incoming boundaries gives a canonical cocycle. -/
def cocycleOfBoundary (c : C.X n ⟶ W) (hc : C.d (n + 1) n ≫ c = 0) :
    (homCochains C W).cycles n :=
  ((homCochains C W).sc n).cyclesMk c (by
    change C.d ((ComplexShape.up ℕ).next n) n ≫ c = 0
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]
    exact hc)

/-- The canonical cocycle retains the supplied actual cochain. -/
theorem cocycleOfBoundary_value (c : C.X n ⟶ W) (hc : C.d (n + 1) n ≫ c = 0) :
    cocycleValue C W n (cocycleOfBoundary C W n c hc) = c :=
  ((homCochains C W).sc n).i_cyclesMk _ _

/-- Literal equivariant cochain evaluation on actual homology. -/
def evaluationOfCochain (c : C.X n ⟶ W) (hc : C.d (n + 1) n ≫ c = 0) :
    C.homology n ⟶ W := cocycleEvaluation C W n (cocycleOfBoundary C W n c hc)

/-- Evaluation of actual represented cycles has the original cochain value. -/
theorem evaluationOfCochain_projection (c : C.X n ⟶ W) (hc : C.d (n + 1) n ≫ c = 0) :
    C.homologyπ n ≫ evaluationOfCochain C W n c hc = C.iCycles n ≫ c := by
  rw [evaluationOfCochain, cocycleEvaluation_projection, cocycleOfBoundary_value]

/-- Actual homology evaluation is natural for literal chain maps and literal cochain compatibility. -/
theorem evaluationOfCochain_natural {D : ChainComplex (Rep.{0} ℚ G) ℕ} (f : C ⟶ D)
    (c : C.X n ⟶ W) (d : D.X n ⟶ W)
    (hc : C.d (n + 1) n ≫ c = 0) (hd : D.d (n + 1) n ≫ d = 0)
    (h : f.f n ≫ d = c) :
    homologyMap f n ≫ evaluationOfCochain D W n d hd = evaluationOfCochain C W n c hc := by
  apply (cancel_epi (C.homologyπ n)).mp
  rw [← Category.assoc, homologyπ_naturality, Category.assoc,
    evaluationOfCochain_projection, ← Category.assoc, cyclesMap_i, Category.assoc,
    h, evaluationOfCochain_projection]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
