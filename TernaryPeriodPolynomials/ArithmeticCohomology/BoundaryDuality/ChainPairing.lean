module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceRepresentatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceChains

@[expose] public section


/-!
# The trace of the boundary cup product without vertex primitives

For a trace given by chain data (`TraceChains.TraceData`: three-chains `C_e` at representative
complete flags `ē`, four-chains `D_v` filling them at the representative lines `v̄`), the trace of
the boundary cup product `w ⌣ y^φ - γ` does not involve the vertex primitive `γ`:

  `τ(w ⌣ y^φ - γ) = Σ_e ⟨(w ⌣ y^φ)(·)(ē), C_e⟩ - Σ_v ⟨(z ⌣ y^φ)(·)(v̄), D_v⟩`,

because `Σ_{e at v} C_e ≡ ∂D_v` modulo the stabilizer of `v̄`, and `dγ = z ⌣ y^φ`
(`trace_eq_chainValue`). Combined with the independence of representatives, boundary duality on the
associate pair follows from one triple `(z, w, y)` per nonzero line class with nonzero chain value;
no vertex primitive needs to exist (`associatePairDuality_of_chainWitness`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.ChainPairing

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary)

section Regroup

variable {X : Type} [MulAction RationalGL3 X]

/-- Grouping the edges by an endpoint: the sum of the chains at each vertex is the boundary of the
filling chain modulo null chains, so an invariant three-cochain at the vertices pairs with the
chains as its differential pairs with the fillings. -/
theorem sum_eval_regroup {ι L : Type} [Fintype ι] [Fintype L] [DecidableEq L] (rep : L → X)
    (endpointOf : ι → L) (chain : ι → (Fin 4 → RationalGL3) →₀ ℂ)
    (fill : L → (Fin 5 → RationalGL3) →₀ ℂ)
    (filled : ∀ v, (∑ i ∈ Finset.univ.filter (fun i => endpointOf i = v), chain i) -
      homogeneousBoundary 4 (fill v) ∈ NullChains (levelStabilizer (rep v)) 3)
    (κ : (Fin 4 → RationalGL3) → X → ℂ)
    (hκ : κ ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) 3) :
    ∑ i, Finsupp.linearCombination ℂ (fun x => κ x (rep (endpointOf i))) (chain i) =
      ∑ v, Finsupp.linearCombination ℂ (fun x => differentialThreeRaw κ x (rep v)) (fill v) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := endpointOf)
    (fun i _ => Finset.mem_univ (endpointOf i))]
  refine Finset.sum_congr rfl fun v _ => ?_
  have regroup : ∑ i ∈ Finset.univ.filter (fun i => endpointOf i = v),
      Finsupp.linearCombination ℂ (fun x => κ x (rep (endpointOf i))) (chain i) =
      Finsupp.linearCombination ℂ (fun x => κ x (rep v))
        (∑ i ∈ Finset.univ.filter (fun i => endpointOf i = v), chain i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  refine regroup.trans ?_
  have hnull := eval_null (fun x => κ x (rep v)) (cochain_invariant κ hκ (rep v)) (filled v)
  rw [map_sub, sub_eq_zero] at hnull
  rw [hnull, ← eval_differentialThree]
  rfl

end Regroup

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  (Θ : TraceData ι L P) {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- The chain value of a line cocycle `z` with edge primitive `w` and a plane cocycle `y`:
`Σ_e ⟨(w ⌣ y^φ)(·)(ē), C_e⟩ - Σ_v ⟨(z ⌣ y^φ)(·)(v̄), D_v⟩`. -/
def chainValue (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (y : MaximalCycles n χ .plane) : ℂ :=
  (∑ i, Finsupp.linearCombination ℂ (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
      (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line (Θ.edge i)))))
      (Θ.chain i)) -
    ∑ v, Finsupp.linearCombination ℂ (fun x => T.B (z.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) (Θ.lineFill v)

/-- **The trace without the vertex primitive.** -/
theorem trace_eq_chainValue {z : MaximalCycles n χ .line} {w : EdgeCochains n χ 1}
    {y : MaximalCycles n χ .plane} {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hγ : VertexPrimitive T z y γ) :
    Θ.trace (boundaryValue T w y γ) = chainValue Θ T z w y := by
  rw [TraceData.trace_apply]
  have split : ∀ i, Finsupp.linearCombination ℂ (fun x => boundaryValue T w y γ x (Θ.edge i))
      (Θ.chain i) = Finsupp.linearCombination ℂ (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line (Θ.edge i)))))
        (Θ.chain i) -
      Finsupp.linearCombination ℂ (fun x => γ x (Θ.lineRep (Θ.lineOf i))) (Θ.chain i) := by
    intro i
    rw [← Θ.line_endpoint i]
    simp only [Finsupp.linearCombination_apply, boundaryValue, smul_sub, Finsupp.sum_sub]
  rw [Finset.sum_congr rfl fun i _ => split i, Finset.sum_sub_distrib,
    sum_eval_regroup Θ.lineRep Θ.lineOf Θ.chain Θ.lineFill Θ.line_filled γ hγ.1]
  show _ - _ = _ - _
  congr 1
  exact Finset.sum_congr rfl fun v _ =>
    congrArg (fun f => Finsupp.linearCombination ℂ f (Θ.lineFill v))
      (funext fun x => hγ.2 x (Θ.lineRep v))

section Summand

variable {D : InducingData n}

/-- One triple per nonzero line summand class with nonzero chain value: a plane summand class, a
representative of each, and an edge primitive of the line representative. -/
def ChainWitness (D : InducingData n) (T : DualityData n D.chi) : Prop :=
  ∀ b ∈ boundarySummand D .line, b ≠ 0 → ∃ ξ ∈ boundarySummand D .plane,
    ∃ (z : MaximalCycles n D.chi .line) (w : EdgeCochains n D.chi 1)
      (y : MaximalCycles n D.chi .plane),
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z =
        b ∧
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y =
        ξ ∧
      EdgePrimitive z w ∧ chainValue Θ T z w y ≠ 0

/-- A chain witness detects every nonzero line class for all representatives and primitives. -/
theorem traceDetects_of_chainWitness (T : DualityData n D.chi) (witness : ChainWitness Θ D T) :
    TraceDetects D T.φ T.dualFlag T.B Θ.trace.toAddMonoidHom := by
  intro b hb hne
  obtain ⟨ξ, hξ, z₀, w₀, y₀, hz₀, hy₀, hw₀, hval⟩ := witness b hb hne
  refine ⟨ξ, hξ, fun z hz w hw y hy γ hγ hdγ => ?_⟩
  have hτ := Θ.isBoundaryTrace_trace
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp (hz₀.trans hz.symm))
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp (hy₀.trans hy.symm))
  obtain rfl : z₀ = z + boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .line) u := by
    rw [hu]; abel
  obtain rfl : y₀ = y + boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) s := by
    rw [hs]; abel
  have flat : PlaneEdgeExact (y + boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) s) :=
    planeEdgeExact_of_mem (D := D) _ (by rw [hy₀]; exact hξ)
  obtain ⟨hγ₁, step₁⟩ := plane_coboundary T hτ hw (And.intro hγ hdγ) s
  obtain ⟨hw₂, hγ₂, step₂⟩ := line_coboundary T hw hγ₁ u
  have key : Θ.trace.toAddMonoidHom (boundaryValue T w y γ) =
      Θ.trace.toAddMonoidHom (boundaryValue T w₀ (y + boundaryMap rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) s)
        (γ + lineCupTwoOne T z s + lineCupOneTwo T u (y + boundaryMap rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) s))) := by
    rw [← step₁, ← step₂, trace_edge_eq T hτ hw₂ hw₀ flat]
  intro hzero
  apply hval
  rw [← trace_eq_chainValue Θ T hγ₂]
  exact key.symm.trans hzero

/-- Boundary duality from chain data and a chain witness. -/
theorem associateDuality_of_chainWitness (T : DualityData n D.chi)
    (witness : ChainWitness Θ D T) : AssociateDuality D T.φ T.dualFlag T.B :=
  associateDuality_of_trace D T.φ T.dualFlag T.B Θ.isBoundaryTrace_trace
    (traceDetects_of_chainWitness Θ T witness)

end Summand

/-- **Boundary duality on the associate pair from chain data and a chain witness**, for the
concrete involution, flag maps and apolar pairing. -/
theorem associatePairDuality_of_chainWitness (D : InducingData n)
    (witness : ChainWitness Θ D (dualityData n D.chi)) : AssociatePairDuality D :=
  associateDuality_of_chainWitness Θ (dualityData n D.chi) witness

end TernaryPeriodPolynomials.BoundaryDuality.ChainPairing
