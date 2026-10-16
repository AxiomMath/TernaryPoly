module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainLocal

@[expose] public section


/-!
# The local value without the filling chain

The local value at a representative line `v̄` is
`Σ_e ⟨(w ⌣ y^φ)(·)(ē), C_e⟩ − ⟨(z ⌣ y^φ)(·)(v̄), D_v⟩`, where the filling chain `D_v` satisfies
`Σ_e C_e ≡ ∂D_v` modulo the stabilizer `Γ_v` of `v̄`. If the four-cocycle `(z ⌣ y^φ)(·)(v̄)` is
the coboundary of a `Γ_v`-invariant three-cochain `K` (which is always the case when
`H⁴(Γ_v, ℂ) = 0`), then `⟨dK, D_v⟩ = ⟨K, ∂D_v⟩ = ⟨K, Σ_e C_e⟩`, so

  `lineValue = Σ_e ⟨(w ⌣ y^φ)(·)(ē), C_e⟩ − ⟨K, Σ_e C_e⟩`

and the filling chain disappears (`lineValue_eq_of_primitive`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberFill

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  (Θ : TraceData ι L P) {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- **The local value without the filling chain**, given an invariant primitive `K` of the
four-cocycle `(z ⌣ y^φ)(·)(v̄)`. -/
theorem lineValue_eq_of_primitive (v : L) (z : MaximalCycles n χ .line)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) (K : (Fin 4 → RationalGL3) → ℂ)
    (hK : ∀ (γ : levelStabilizer (Θ.lineRep v)) x, K (fun i => γ.val * x i) = K x)
    (hdK : ∀ x, differentialThreeRaw K x = T.B (z.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) :
    lineValue Θ T v z w y =
      (∑ i ∈ Finset.univ.filter (fun i => Θ.lineOf i = v),
        Finsupp.linearCombination ℂ (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (Θ.lineRep v))))
          (Θ.chain i)) -
      Finsupp.linearCombination ℂ K
        (∑ i ∈ Finset.univ.filter (fun i => Θ.lineOf i = v), Θ.chain i) := by
  unfold lineValue
  congr 1
  have hfill : (fun x => T.B (z.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) =
      differentialThreeRaw K := funext fun x => (hdK x).symm
  rw [hfill, eval_differentialThree]
  have hnull := eval_null K hK (Θ.line_filled v)
  rw [map_sub, sub_eq_zero] at hnull
  exact hnull.symm

end TernaryPeriodPolynomials.BoundaryDuality.FiberFill
