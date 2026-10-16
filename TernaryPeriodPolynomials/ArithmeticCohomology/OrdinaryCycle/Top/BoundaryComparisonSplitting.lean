module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonEvaluation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory Limits HomologicalComplex

variable {G : Type} [Group G] (C : ChainComplex (Rep.{0} ℚ G) ℕ)

/-- The actual cycle inclusion followed by the boundary with codomain restricted to cycles. -/
def cycleSequence (n : ℕ) : ShortComplex (Rep.{0} ℚ G) :=
  ShortComplex.mk (C.iCycles (n + 1)) (C.toCycles (n + 1) n) (by
    apply (cancel_mono (C.iCycles n)).mp
    rw [Category.assoc, toCycles_i, iCycles_d, zero_comp])

/-- The cycle inclusion is the actual kernel of the cycle-valued boundary. -/
theorem cycleSequence_exact (n : ℕ) : (cycleSequence C n).Exact := by
  apply (cycleSequence C n).exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι (C.iCycles (n + 1)) (cycleSequence C n).zero
    (fun k hk => C.liftCycles k n (by simp) (by
      change k ≫ C.toCycles (n + 1) n = 0 at hk
      rw [← C.toCycles_i (n + 1) n, ← Category.assoc, hk, zero_comp]))
    (fun k hk => C.liftCycles_i k n (by simp) _)
  intro A k hk b hb
  apply (cancel_mono (C.iCycles (n + 1))).mp
  exact hb.trans (C.liftCycles_i k n (by simp) _).symm

/-- Vanishing homology in degree n makes the actual cycle-valued incoming boundary epic. -/
theorem cycleBoundary_epi (n : ℕ) (h : C.ExactAt n) : Epi (C.toCycles (n + 1) n) := by
  have he := (HomologicalComplex.exactAt_iff C n).mp h
  have hp := he.epi_toCycles
  have hprev : (ComplexShape.down ℕ).prev n = n + 1 :=
    (ComplexShape.down ℕ).prev_eq' rfl
  change Epi ((C.sc n).toCycles) at hp
  change Epi (C.toCycles ((ComplexShape.down ℕ).prev n) n) at hp
  rwa [hprev] at hp

/-- Projectivity of the target cycles splits the genuine low-degree boundary sequence. -/
def cycleSequenceSplitting (n : ℕ) (h : C.ExactAt n) [Projective (C.cycles n)] :
    (cycleSequence C n).Splitting := by
  let : Epi (cycleSequence C n).g := cycleBoundary_epi C n h
  let : Projective (cycleSequence C n).X₃ := inferInstanceAs (Projective (C.cycles n))
  let : Mono (cycleSequence C n).f := inferInstanceAs (Mono (C.iCycles (n + 1)))
  exact ShortComplex.Splitting.ofExactOfSection (cycleSequence C n) (cycleSequence_exact C n)
    (Projective.factorThru (𝟙 _) (cycleSequence C n).g)
    (Projective.factorThru_comp _ _) inferInstance

/-- Projectivity passes from actual adjacent chain and cycle groups to the next cycle group. -/
theorem cycleProjective_next (n : ℕ) (h : C.ExactAt n)
    [Projective (C.cycles n)] [Projective (C.X (n + 1))] : Projective (C.cycles (n + 1)) where
  factors {A B} u e _ := by
    let s := cycleSequenceSplitting C n h
    let : Projective (cycleSequence C n).X₂ := inferInstanceAs (Projective (C.X (n + 1)))
    obtain ⟨l, hl⟩ := Projective.factors (s.r ≫ u) e
    refine ⟨C.iCycles (n + 1) ≫ l, ?_⟩
    erw [Category.assoc, hl, ← Category.assoc]
    change ((cycleSequence C n).f ≫ s.r) ≫ u = u
    erw [s.f_r, Category.id_comp]

end TernaryPoly.OrdinaryTopBoundaryComparison
