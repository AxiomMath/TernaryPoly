module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceQuotient
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingNondegenerate
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.TraceDetects
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PerfectEven

@[expose] public section


/-!
# S2: the boundary trace is nonzero on a level-invariant closed edge three-cochain

The boundary cup product `w ⌣ y^φ - γ` of an anchor (`FacePairingAnchor`: a line cocycle `z` with edge
primitive `w`, a plane cocycle `y`, a vertex primitive `γ` of `z ⌣ y^φ`) is an invariant closed scalar
three-cochain on complete flags (`boundaryValue_mem_closed`), and its trace is the (nonzero) anchor
value.  An anchor exists for `n = 6` because the inner line classes of degree six form a space of
dimension two (`finrank_innerClasses_line_even`).  Hence `traceDataL2.trace` does not vanish on
`closedEdgeCochains rationalLevel` (`exists_closed_levelTrace_ne_zero`): the quotient `Q_level` of
`TraceQuotient` is nonzero.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainPairing
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue chainValue_eq_sum)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing
  (lineCupExact)
open TernaryPeriodPolynomials.Argument.FacePairing

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- The edge cup product `w ⌣ y^φ` of an edge one-cochain with a plane two-cocycle read at the dual
of the line endpoint. -/
theorem edgeCupOneTwo_mem (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) :
    (fun (x : Fin 4 → RationalGL3) (e : Edges) =>
        T.B (w.val ![x 0, x 1] e)
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e)))) ∈
      cochains rationalLevel (functionRepresentation scalarTrivial Edges) 3 := by
  intro g x
  funext e
  have dual : T.φ g.val ∈ rationalLevel := T.level g.val g.property
  change T.B (w.val ![g.val * x 0, g.val * x 1] e)
      (y.val.val ![T.φ (g.val * x 1), T.φ (g.val * x 2), T.φ (g.val * x 3)]
        (T.dualFlag (endpoint .line e))) =
    T.B (w.val ![x 0, x 1] (g.val⁻¹ • e))
      (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line (g.val⁻¹ • e))))
  rw [congrFun (cochain_pair w g (x 0) (x 1)) e, map_mul, map_mul, map_mul,
    cochain_triple y.val ⟨T.φ g.val, dual⟩]
  change T.B (rationalCoefficientComponent n χ g.val (w.val ![x 0, x 1] (g.val⁻¹ • e)))
      (rationalCoefficientComponent n χ (T.φ g.val)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)]
          ((T.φ g.val)⁻¹ • T.dualFlag (endpoint .line e)))) = _
  rw [T.invariant g.val g.property, ← map_inv T.φ g.val, ← T.dualFlag_smul, ← endpoint_smul]

/-- **The boundary cup product of an edge primitive, a plane cocycle and a vertex primitive is an
invariant closed three-cochain on complete flags.** -/
theorem boundaryValue_mem_closed {z : MaximalCycles n χ .line} {w : EdgeCochains n χ 1}
    {y : MaximalCycles n χ .plane} {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hw : EdgePrimitive z w) (hγ : VertexPrimitive T z y γ) :
    boundaryValue T w y γ ∈ closedEdgeCochains rationalLevel := by
  refine ⟨?_, fun x => ?_⟩
  · have hγm : (fun x (e : Edges) => γ x (endpoint .line e)) ∈
        cochains rationalLevel (functionRepresentation scalarTrivial Edges) 3 := by
      intro g x
      funext e
      have := congrFun (hγ.1 g x) (endpoint .line e)
      change γ (fun i => g.val * x i) (endpoint .line e) =
        scalarTrivial g.val (γ x (endpoint .line (g.val⁻¹ • e)))
      rw [endpoint_smul]
      exact this
    exact sub_mem (edgeCupOneTwo_mem T w y) hγm
  · funext e
    have cocycle : IsCocycleTwo (fun x' => y.val.val x' (T.dualFlag (endpoint .line e))) := fun x' =>
      congrFun (isCocycleTwo_of_mem y x') (T.dualFlag (endpoint .line e))
    have leibniz := differentialThreeRaw_cupOneTwo T.B T.φ (fun x' => w.val x' e) cocycle x
    have hprim : differentialOneRaw (fun x' => w.val x' e) ![x 0, x 1, x 2] =
        z.val.val ![x 0, x 1, x 2] (endpoint .line e) := by
      have := hw ![x 0, x 1, x 2] e
      exact this.symm
    have hdγ := hγ.2 x (endpoint .line e)
    have split : differentialThreeRaw (boundaryValue T w y γ) x e =
        differentialThreeRaw (cupOneTwo T.B T.φ (fun x' => w.val x' e)
          (fun x' => y.val.val x' (T.dualFlag (endpoint .line e)))) x -
        differentialThreeRaw γ x (endpoint .line e) := by
      simp only [differentialThreeRaw, boundaryValue, cupOneTwo, Pi.sub_apply, Pi.add_apply]
      abel
    rw [split, leibniz]
    simp only [cupTwoTwo]
    rw [hprim, hdγ, sub_self]
    rfl

/-- There is a nonzero inner line class in degree six. -/
theorem exists_nonzero_inner_line_class : ∃ b : innerClasses 6 .line, b.val ≠ 0 := by
  have h := finrank_innerClasses_line_even 6 (by norm_num) ⟨3, by norm_num⟩
  have := finiteDimensional_innerClasses_line_even 6 (by norm_num) ⟨3, by norm_num⟩
  have hpos : 0 < Module.finrank ℂ (innerClasses 6 .line) := by omega
  obtain ⟨b, hb⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  exact ⟨b, fun h0 => hb (Subtype.ext h0)⟩

/-- **The boundary trace is nonzero on a level-invariant closed edge three-cochain.** -/
theorem exists_closed_levelTrace_ne_zero :
    ∃ f : closedEdgeCochains rationalLevel, levelTrace f ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_nonzero_inner_line_class
  obtain ⟨z₀, w₀, ξ, y₀, hz₀, hw₀, hy₀, hflat₀, hsum⟩ := exists_anchor 6 b.property hb
  obtain ⟨γ, hγ⟩ := lineCupExact (dualityData 6 trivialCharacter) z₀ y₀
  refine ⟨⟨boundaryValue (dualityData 6 trivialCharacter) w₀ y₀ γ,
    boundaryValue_mem_closed _ hw₀ hγ⟩, ?_⟩
  rw [levelTrace_apply]
  change traceDataL2.trace (boundaryValue (dualityData 6 trivialCharacter) w₀ y₀ γ) ≠ 0
  rw [trace_eq_chainValue traceDataL2 (dualityData 6 trivialCharacter) hγ,
    chainValue_eq_sum traceDataL2 (dualityData 6 trivialCharacter) z₀ w₀ y₀]
  exact hsum

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
