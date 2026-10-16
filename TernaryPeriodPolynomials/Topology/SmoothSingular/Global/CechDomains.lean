module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.PartitionLinear

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Filter Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Topology ContDiff Manifold
variable {ι : Type*} (U : ι → Set OrbitSpace)

/-- The actual quotient open intersection indexed by an ordered Čech tuple, including the
empty intersection for the augmented global term. -/
def cechDomain {k : ℕ} (t : Fin k → ι) : Set OrbitSpace := ⋂ a, U (t a)

/-- Ordered Čech intersections of open quotient domains are genuinely open. -/
theorem cechDomain_isOpen (hU : ∀ i, IsOpen (U i)) {k : ℕ} (t : Fin k → ι) :
    IsOpen (cechDomain U t) := isOpen_iInter_of_finite (fun a => hU (t a))

/-- The augmented empty tuple is the actual full quotient domain. -/
theorem cechDomain_empty (t : Fin 0 → ι) : cechDomain U t = Set.univ := by
  simp [cechDomain]

/-- Passing from a Čech tuple to any tuple of its selected entries enlarges the actual domain. -/
theorem cechDomain_select_subset {p q : ℕ} (f : Fin p → Fin q) (t : Fin q → ι) :
    cechDomain U t ⊆ cechDomain U (t ∘ f) := by
  intro x hx
  exact mem_iInter.mpr (fun a => mem_iInter.mp hx (f a))

/-- Prepending a Čech index is the literal intersection with its cover member. -/
theorem cechDomain_cons {k : ℕ} (i : ι) (t : Fin k → ι) :
    cechDomain U (Fin.cons i t) = U i ∩ cechDomain U t := by
  ext x
  simp [cechDomain, Fin.forall_fin_succ]

/-- A literal overlap lies in the corresponding prepended Čech domain. -/
theorem cechDomain_subset_cons {k : ℕ} (i : ι) (t : Fin k → ι) :
    U i ∩ cechDomain U t ⊆ cechDomain U (Fin.cons i t) := by
  rw [cechDomain_cons]

end TernaryPoly.SmoothSingularGlobal
