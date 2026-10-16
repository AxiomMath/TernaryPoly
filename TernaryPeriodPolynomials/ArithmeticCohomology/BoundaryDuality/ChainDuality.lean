module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainCalculus

@[expose] public section


/-!
# Boundaries modulo a subgroup, detected by invariant cocycles

A three-chain is a boundary modulo the `Λ`-null chains exactly when every `Λ`-invariant scalar
three-cocycle vanishes on it (`mem_bdryChains_iff`): one direction is `⟨κ, n + ∂d⟩ = ⟨dκ, d⟩ = 0`,
the other separates a chain outside the subspace by a linear functional, which is the pairing with
an invariant cocycle (its values on basis chains). So the filling four-chains of a trace need not be
written down: `TraceData.ofBdry` builds the chain data from memberships in `BdryChains`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.ChainDuality

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing
  (homogeneousBoundary lin_ext_single differentialThreeRaw_eq)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus

variable {G : Type} [Group G]

/-- **Duality.** A three-chain is a boundary modulo `Λ`-null chains iff every `Λ`-invariant scalar
three-cocycle vanishes on it. -/
theorem mem_bdryChains_iff (Λ : Subgroup G) (c : Chains G 3) :
    c ∈ BdryChains Λ 3 ↔ ∀ κ : (Fin 4 → G) → ℂ, (∀ (γ : Λ) x, κ (fun i => γ.val * x i) = κ x) →
      (∀ x, differentialThreeRaw κ x = 0) → Finsupp.linearCombination ℂ κ c = 0 := by
  constructor
  · intro hc κ hκ closed
    obtain ⟨n, hn, d, hd, rfl⟩ := Submodule.mem_sup.mp hc
    obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hd
    rw [map_add, eval_null κ hκ hn, zero_add, ← eval_differentialThree]
    have zero : differentialThreeRaw κ = 0 := funext closed
    rw [zero]
    simp
  · intro h
    by_contra hc
    obtain ⟨f, hfc, hle⟩ := Submodule.exists_le_ker_of_notMem hc
    have hf : Finsupp.linearCombination ℂ (fun x => f (Finsupp.single x 1)) = f :=
      lin_ext_single fun x => by rw [Finsupp.linearCombination_single, one_smul]
    have hnull : NullChains Λ 3 ≤ LinearMap.ker f := le_trans le_sup_left hle
    have hrange : LinearMap.range (homogeneousBoundary (G := G) 4) ≤ LinearMap.ker f :=
      le_trans le_sup_right hle
    apply hfc
    rw [← hf]
    refine h _ (fun γ x => ?_) (fun x => ?_)
    · have hmem : Finsupp.single (fun i => γ.val * x i) (1 : ℂ) - Finsupp.single x 1 ∈
          NullChains Λ 3 := Submodule.subset_span ⟨γ, x, rfl⟩
      have := LinearMap.mem_ker.mp (hnull hmem)
      rw [map_sub, sub_eq_zero] at this
      exact this
    · rw [differentialThreeRaw_eq, hf]
      exact LinearMap.mem_ker.mp (hrange (LinearMap.mem_range_self _ _))

/-- A boundary modulo null chains has a filling chain. -/
theorem exists_fill {Λ : Subgroup G} {c : Chains G 3} (hc : c ∈ BdryChains Λ 3) :
    ∃ D : Chains G 4, c - homogeneousBoundary 4 D ∈ NullChains Λ 3 := by
  obtain ⟨n, hn, d, hd, rfl⟩ := Submodule.mem_sup.mp hc
  obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hd
  exact ⟨e, by rwa [add_sub_cancel_right]⟩

/-- Chain data for a boundary trace from memberships in `BdryChains`: the filling four-chains are
chosen. -/
def TraceData.ofBdry {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L]
    [DecidableEq P] (edge : ι → Edges) (chain : ι → Chains RationalGL3 3)
    (lineRep : L → Flags .line) (lineOf : ι → L)
    (line_endpoint : ∀ i, endpoint .line (edge i) = lineRep (lineOf i))
    (planeRep : P → Flags .plane) (planeOf : ι → P)
    (plane_endpoint : ∀ i, endpoint .plane (edge i) = planeRep (planeOf i))
    (edge_closed : ∀ i, homogeneousBoundary 3 (chain i) ∈ NullChains (levelStabilizer (edge i)) 2)
    (line_bdry : ∀ v, (∑ i ∈ Finset.univ.filter (fun i => lineOf i = v), chain i) ∈
      BdryChains (levelStabilizer (lineRep v)) 3)
    (plane_bdry : ∀ v, (∑ i ∈ Finset.univ.filter (fun i => planeOf i = v), chain i) ∈
      BdryChains (levelStabilizer (planeRep v)) 3) :
    TraceData ι L P where
  edge := edge
  chain := chain
  lineRep := lineRep
  lineOf := lineOf
  line_endpoint := line_endpoint
  lineFill v := Classical.choose (exists_fill (line_bdry v))
  planeRep := planeRep
  planeOf := planeOf
  plane_endpoint := plane_endpoint
  planeFill v := Classical.choose (exists_fill (plane_bdry v))
  edge_closed := edge_closed
  line_filled v := Classical.choose_spec (exists_fill (line_bdry v))
  plane_filled v := Classical.choose_spec (exists_fill (plane_bdry v))

end TernaryPeriodPolynomials.BoundaryDuality.ChainDuality
