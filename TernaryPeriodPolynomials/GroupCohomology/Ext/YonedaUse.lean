module

public import TernaryPeriodPolynomials.GroupCohomology.Ext.YonedaPushout
public import TernaryPeriodPolynomials.GroupCohomology.Ext.Segment

@[expose] public section


/-!
# The paper's use of extensions: the boundary functional extends iff the obstruction in `Ext¹(Q₀, E)` vanishes

Apply the generalities of `ExtYoneda` / `ExtYonedaPushout` to the sequence `0 → St† → St → Q₀ → 0` of the restricted and full graphs
(`cycleSequence`, in the library's coordinates the Good cycles, the ordinary cycles and their quotient, in `Rep ℚ K`).

* `boundary_functional_extends_iff`: a `K`-equivariant functional `f` on the restricted-graph cycles with values in `E` extends to the full graph **iff its obstruction
  `δf ∈ Ext¹(Q₀, E)` vanishes iff the pushout extension `0 → E → (E ⊕ St)/St† → Q₀ → 0` splits**.
* `extends_of_obstruction_subsingleton`: if `Ext¹(Q₀, E) = 0` every functional extends and every such pushout extension splits.
* `alternating_even_extension`: for `E = Sym^n((ℚ³)*)`, `n` even, `Ext¹_{K†}(Q₀, E) = 0` (the four stabilizer vanishings, `ExtSegment.ext_Q0_vanishing_via_segment`),
  hence the extension of every functional exists and the corresponding extensions split ("signs kill the extension obstruction").

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.ExtYoneda

open CategoryTheory CategoryTheory.Abelian TernaryPoly TernaryPoly.RelativeExtObstructionSequences TernaryPoly.RelativeExtObstruction

/-- **The boundary functional extends iff the obstruction in `Ext¹(Q₀, E)` vanishes iff the pushout extension splits.** -/
theorem boundary_functional_extends_iff (E : Rep.{0} ℚ K) (f : GoodCyclesRep ⟶ E) :
    (∃ F : OrdinaryCyclesRep ⟶ E, goodCycleInclusion ≫ F = f) ↔
      obstruction cycleSequence_shortExact f = 0 :=
  extends_iff_obstruction_eq_zero cycleSequence_shortExact f

theorem boundary_functional_extends_iff_split (E : Rep.{0} ℚ K) (f : GoodCyclesRep ⟶ E) :
    (∃ F : OrdinaryCyclesRep ⟶ E, goodCycleInclusion ≫ F = f) ↔
      Splits (pushoutExtension cycleSequence f cycleSequence_shortExact).sc :=
  extends_iff_pushout_splits cycleSequence f cycleSequence_shortExact

/-- If `Ext¹(Q₀, E)` vanishes, every functional on the Good cycles extends and every pushout extension splits. -/
theorem extends_of_obstruction_subsingleton (E : Rep.{0} ℚ K)
    (h : Subsingleton (Ext.{1} QuotientCyclesRep E 1)) (f : GoodCyclesRep ⟶ E) :
    (∃ F : OrdinaryCyclesRep ⟶ E, goodCycleInclusion ≫ F = f) ∧
      Splits (pushoutExtension cycleSequence f cycleSequence_shortExact).sc := by
  have h0 : obstruction cycleSequence_shortExact f = 0 := @Subsingleton.elim _ h _ _
  exact ⟨(boundary_functional_extends_iff E f).mpr h0, (boundary_functional_extends_iff_split E f).mp
    ((boundary_functional_extends_iff E f).mpr h0)⟩

/-- **Alternating even degree**: for `E = Sym^n((ℚ³)*)`, `n` even, every functional on the Good cycles extends to the full graph, because
`Ext¹_{K†}(Q₀, E) = 0`; equivalently every pushout extension splits. -/
theorem alternating_even_extension (n : ℕ) (hn : Even n)
    (f : GoodCyclesRep ⟶ coefficientRep n) :
    (∃ F : OrdinaryCyclesRep ⟶ coefficientRep n, goodCycleInclusion ≫ F = f) ∧
      Splits (pushoutExtension cycleSequence f cycleSequence_shortExact).sc :=
  extends_of_obstruction_subsingleton _ (ExtSegment.ext_Q0_vanishing_via_segment n hn) f

end TernaryPeriodPolynomials.Argument.Identities.ExtYoneda
