module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.InnerBadLineSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtForm

@[expose] public section


/-!
# The interfaces of the direct route

* `MemberRealized n hn D`: for one cohomological cuspidal datum `D`, every level-three weight vector
  of `D` has a cusp form (its classical form) whose period class is realized (the Eichler cocycle of
  the vector, its line source, the edge identity of the bad-line coordinate and the bad-line cutoff).
* `ModelCoversForms n`: the cusp forms of the level-three weight vectors of cohomological cuspidal
  data span all cusp forms of weight `n + 3` for `Γ₁(3)` (the Bergman model of the adelic lifts, its
  decomposition into compression-simple constituents, and the Eichler-integral witness of
  `Cohomological` for each constituent).

`periodsRealized_of` combines them.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open GeneralEisenstein
open Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.Automorphic.Contracts

open TernaryPeriodPolynomials.Automorphic.DirectRoute
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.EvenLevelThree

/-- The rotation weight `-(n + 3)` of the level-three weight vectors. -/
abbrev wtOf (n : ℕ) : ℤ := -((n : ℤ) + 3)

/-- **Contract for the source side (EV, D).**  For the cohomological cuspidal datum
`D`, every classical level-three vector of rotation weight `-(n + 3)` has its cusp form among the
realized period classes. -/
def MemberRealized (n : ℕ) (hn : 0 < n) (D : CohomologicalCuspData n) : Prop :=
  ∀ w : levelThreeClassicalVectorsWt D.cusp (wtOf n),
    ∃ f : S (n + 1),
      (⇑f : UpperHalfPlane → ℂ) = cuspScalarWeightedLinearWt D.cusp (wtOf n) 1 w.1 ∧
        f ∈ periodRealized n hn

/-- **Contract for the model side (R1).**  Every cusp form of weight `n + 3` for
`Γ₁(3)` is a finite sum of the cusp forms of classical level-three weight vectors of cohomological
cuspidal data. -/
def ModelCoversForms (n : ℕ) : Prop :=
  ∀ f : S (n + 1),
    ∃ l : List (Σ D : CohomologicalCuspData n, levelThreeClassicalVectorsWt D.cusp (wtOf n)),
      (⇑f : UpperHalfPlane → ℂ) =
        (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (wtOf n) 1 p.2.1).sum

/-- The period classes are realized, given the two contracts. -/
theorem periodsRealized_of (n : ℕ) (hn : 0 < n) (hm : ∀ D : CohomologicalCuspData n, MemberRealized n hn D)
    (hc : ModelCoversForms n) : PeriodsRealized n hn := by
  have key : ∀ l : List (Σ D : CohomologicalCuspData n, levelThreeClassicalVectorsWt D.cusp (wtOf n)),
      ∃ f : S (n + 1),
        (⇑f : UpperHalfPlane → ℂ) =
          (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (wtOf n) 1 p.2.1).sum ∧
          f ∈ periodRealized n hn := by
    intro l
    induction l with
    | nil => exact ⟨0, by simp, Submodule.zero_mem _⟩
    | cons p l ih =>
      obtain ⟨g, hg, hgmem⟩ := ih
      obtain ⟨f, hf, hfmem⟩ := hm p.1 p.2
      refine ⟨f + g, ?_, Submodule.add_mem _ hfmem hgmem⟩
      simp only [List.map_cons, List.sum_cons]
      rw [← hg, ← hf]
      rfl
  apply eq_top_iff.mpr
  intro f _
  obtain ⟨l, hl⟩ := hc f
  obtain ⟨g, hg, hgmem⟩ := key l
  have hfg : f = g := DFunLike.coe_injective (hl.trans hg.symm)
  rw [hfg]
  exact hgmem

end TernaryPeriodPolynomials.Automorphic.Contracts
