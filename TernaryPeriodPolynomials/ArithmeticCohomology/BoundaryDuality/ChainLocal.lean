module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainPairing

@[expose] public section


/-!
# The chain value is a sum of local values at the line cusps

Every complete flag of the chain data has its line endpoint at one of the representative lines,
so the chain value of a line cocycle `z` with edge primitive `w` and a plane cocycle `y` splits as a
sum over the representative lines `v̄` (`chainValue_eq_sum`). The summand at `v̄` (`lineValue`)
only involves the values of `z` at `v̄`, of `y` at the dual plane of `v̄`, and of `w` at the
representative complete flags above `v̄` (`lineValue_congr`): these are the Shapiro coordinates of
the three cochains at the line cusp, so the nondegeneracy of the boundary pairing is a statement
about the cohomology of the line stabilizers.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.ChainLocal

open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainPairing

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  (Θ : TraceData ι L P) {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- The local value at the representative line `v̄`: the edge terms of the complete flags above
`v̄` minus the filling term at `v̄`. -/
def lineValue (v : L) (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (y : MaximalCycles n χ .plane) : ℂ :=
  (∑ i ∈ Finset.univ.filter (fun i => Θ.lineOf i = v),
      Finsupp.linearCombination ℂ (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (Θ.lineRep v)))) (Θ.chain i)) -
    Finsupp.linearCombination ℂ (fun x => T.B (z.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) (Θ.lineFill v)

/-- **Localization.** The chain value is the sum of the local values at the representative
lines. -/
theorem chainValue_eq_sum (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (y : MaximalCycles n χ .plane) :
    chainValue Θ T z w y = ∑ v, lineValue Θ T v z w y := by
  unfold chainValue lineValue
  rw [Finset.sum_sub_distrib, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ) (g := Θ.lineOf) (fun i _ => Finset.mem_univ (Θ.lineOf i))]
  congr 1
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i hi => ?_
  rw [Θ.line_endpoint i, (Finset.mem_filter.mp hi).2]

/-- The local value at `v̄` only depends on the values of the cochains at `v̄`, at its dual plane
and at the complete flags above it. -/
theorem lineValue_congr (v : L) {z z' : MaximalCycles n χ .line} {w w' : EdgeCochains n χ 1}
    {y y' : MaximalCycles n χ .plane}
    (hz : ∀ x, z.val.val x (Θ.lineRep v) = z'.val.val x (Θ.lineRep v))
    (hw : ∀ i, Θ.lineOf i = v → ∀ x, w.val x (Θ.edge i) = w'.val x (Θ.edge i))
    (hy : ∀ x, y.val.val x (T.dualFlag (Θ.lineRep v)) = y'.val.val x (T.dualFlag (Θ.lineRep v))) :
    lineValue Θ T v z w y = lineValue Θ T v z' w' y' := by
  unfold lineValue
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hv := (Finset.mem_filter.mp hi).2
    simp only [hw i hv, hy]
  · simp only [hz, hy]

end TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
