module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Homogeneous

@[expose] public section


/-!
# Boundary traces from chains

A boundary trace can be written down from finitely many homogeneous chains: for each orbit of
complete flags a representative `ē` and a rational three-chain `C_e`, and

  `τ f = Σ_e ⟨f(·)(ē), C_e⟩`.

The three conditions of `IsBoundaryTrace` become identities of chains modulo left translation by
the stabilizers in the arithmetic level (`NullChains`):
* `∂C_e ≡ 0` modulo the stabilizer of `ē` (then `τ` kills coboundaries, since `⟨dg, C⟩ = ⟨g, ∂C⟩`);
* for every line (plane) orbit with representative `v̄`, the sum of the `C_e` over the edges whose
  line (plane) endpoint is `v̄` is `≡ ∂D_v` for a four-chain `D_v`, modulo the stabilizer of `v̄`
  (then `τ` kills pullbacks of three-cocycles, since `⟨κ, ∂D⟩ = ⟨dκ, D⟩ = 0`).

`TraceData` packages such chains and `isBoundaryTrace_trace` proves the trace conditions.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.TraceChains

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
open TernaryPeriodPolynomials.TopVanishing
  (homogeneousBoundary homogeneousBoundary_single lin_ext_single differentialThreeRaw_eq)

section Chains

variable {G : Type} [Group G]

/-- The alternating homogeneous differential of a function of three vertices. -/
def differentialTwoRaw {M : Type} [AddCommGroup M] (g : (Fin 3 → G) → M) (x : Fin 4 → G) : M :=
  g ![x 1, x 2, x 3] - g ![x 0, x 2, x 3] + g ![x 0, x 1, x 3] - g ![x 0, x 1, x 2]

omit [Group G] in
/-- The degree-two differential is dual to the face boundary of chains. -/
theorem differentialTwoRaw_eq (g : (Fin 3 → G) → ℂ) (x : Fin 4 → G) :
    differentialTwoRaw g x =
      Finsupp.linearCombination ℂ g (homogeneousBoundary 3 (Finsupp.single x 1)) := by
  have h0 : x ∘ Fin.succAbove (0 : Fin 4) = ![x 1, x 2, x 3] := by
    funext j; fin_cases j <;> rfl
  have h1 : x ∘ Fin.succAbove (1 : Fin 4) = ![x 0, x 2, x 3] := by
    funext j; fin_cases j <;> rfl
  have h2 : x ∘ Fin.succAbove (2 : Fin 4) = ![x 0, x 1, x 3] := by
    funext j; fin_cases j <;> rfl
  have h3 : x ∘ Fin.succAbove (3 : Fin 4) = ![x 0, x 1, x 2] := by
    funext j; fin_cases j <;> rfl
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  unfold differentialTwoRaw
  rw [homogeneousBoundary_single, map_sum, Fin.sum_univ_four]
  simp only [map_smul, Finsupp.linearCombination_single, smul_eq_mul,
    h0, h1, h2, h3, v0, v1, v2, v3]
  ring

omit [Group G] in
/-- Pairing the differential of a two-cochain with a chain is pairing the cochain with the
boundary. -/
theorem eval_differentialTwo (g : (Fin 3 → G) → ℂ) (c : (Fin 4 → G) →₀ ℂ) :
    Finsupp.linearCombination ℂ (differentialTwoRaw g) c =
      Finsupp.linearCombination ℂ g (homogeneousBoundary 3 c) := by
  have h : Finsupp.linearCombination ℂ (differentialTwoRaw g) =
      (Finsupp.linearCombination ℂ g) ∘ₗ homogeneousBoundary 3 :=
    lin_ext_single fun x => by
      rw [LinearMap.comp_apply, ← differentialTwoRaw_eq, Finsupp.linearCombination_single,
        one_smul]
  exact LinearMap.congr_fun h c

omit [Group G] in
/-- Pairing the differential of a three-cochain with a chain is pairing the cochain with the
boundary. -/
theorem eval_differentialThree (θ : (Fin 4 → G) → ℂ) (c : (Fin 5 → G) →₀ ℂ) :
    Finsupp.linearCombination ℂ (differentialThreeRaw θ) c =
      Finsupp.linearCombination ℂ θ (homogeneousBoundary 4 c) := by
  have h : Finsupp.linearCombination ℂ (differentialThreeRaw θ) =
      (Finsupp.linearCombination ℂ θ) ∘ₗ homogeneousBoundary 4 :=
    lin_ext_single fun x => by
      rw [LinearMap.comp_apply, ← differentialThreeRaw_eq, Finsupp.linearCombination_single,
        one_smul]
  exact LinearMap.congr_fun h c

/-- Chains that are zero modulo left translation by `Λ`: the span of the differences
`(γ x) - x`. -/
def NullChains (Λ : Subgroup G) (k : ℕ) : Submodule ℂ ((Fin (k + 1) → G) →₀ ℂ) :=
  Submodule.span ℂ {c | ∃ (γ : Λ) (x : Fin (k + 1) → G),
    c = Finsupp.single (fun i => γ.val * x i) 1 - Finsupp.single x 1}

/-- A `Λ`-invariant function pairs to zero with every null chain. -/
theorem eval_null {Λ : Subgroup G} {k : ℕ} (f : (Fin (k + 1) → G) → ℂ)
    (hf : ∀ (γ : Λ) x, f (fun i => γ.val * x i) = f x) {c : (Fin (k + 1) → G) →₀ ℂ}
    (hc : c ∈ NullChains Λ k) : Finsupp.linearCombination ℂ f c = 0 := by
  have hle : NullChains Λ k ≤ LinearMap.ker (Finsupp.linearCombination ℂ f) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Finsupp.linearCombination_single,
      one_smul, hf, sub_self]
  exact LinearMap.mem_ker.mp (hle hc)

/-- An invariant two-cochain has zero coboundary on a chain whose boundary is null. -/
theorem eval_boundary_null {Λ : Subgroup G} (g : (Fin 3 → G) → ℂ)
    (hg : ∀ (γ : Λ) x, g (fun i => γ.val * x i) = g x) (c : (Fin 4 → G) →₀ ℂ)
    (hc : homogeneousBoundary 3 c ∈ NullChains Λ 2) :
    Finsupp.linearCombination ℂ (differentialTwoRaw g) c = 0 := by
  rw [eval_differentialTwo]
  exact eval_null g hg hc

/-- An invariant three-cocycle vanishes on a chain which is a boundary modulo null chains. -/
theorem eval_cocycle_of_filled {Λ : Subgroup G} (κ : (Fin 4 → G) → ℂ)
    (hκ : ∀ (γ : Λ) x, κ (fun i => γ.val * x i) = κ x) (closed : ∀ x, differentialThreeRaw κ x = 0)
    (c : (Fin 4 → G) →₀ ℂ) (D : (Fin 5 → G) →₀ ℂ)
    (filled : c - homogeneousBoundary 4 D ∈ NullChains Λ 3) :
    Finsupp.linearCombination ℂ κ c = 0 := by
  have h₁ := eval_null κ hκ filled
  rw [map_sub] at h₁
  have h₂ : Finsupp.linearCombination ℂ κ (homogeneousBoundary 4 D) = 0 := by
    rw [← eval_differentialThree]
    have zero : differentialThreeRaw κ = 0 := funext closed
    rw [zero]
    simp
  rw [h₂, sub_zero] at h₁
  exact h₁

end Chains

section Stabilizers

variable {X : Type} [MulAction RationalGL3 X]

/-- The stabilizer of a point in the arithmetic level. -/
def levelStabilizer (p : X) : Subgroup RationalGL3 :=
  rationalLevel ⊓ MulAction.stabilizer RationalGL3 p

/-- The value at a point of an invariant scalar cochain is invariant under the stabilizer of the
point. -/
theorem cochain_invariant {k : ℕ} (f : (Fin (k + 1) → RationalGL3) → X → ℂ)
    (hf : f ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) k) (p : X) :
    ∀ (γ : levelStabilizer p) x, f (fun i => γ.val * x i) p = f x p := by
  intro γ x
  have level : γ.val ∈ rationalLevel := (Subgroup.mem_inf.mp γ.property).1
  have fixed : γ.val • p = p := (Subgroup.mem_inf.mp γ.property).2
  have h := congrFun (hf ⟨γ.val, level⟩ x) p
  change f (fun i => γ.val * x i) p = f x (γ.val⁻¹ • p) at h
  rw [h, inv_smul_eq_iff.mpr fixed.symm]

/-- Grouping the edges by an endpoint: if the chains at each vertex fill up to null chains, every
invariant three-cocycle at the vertices pairs to zero with the sum of the chains. -/
theorem sum_eval_filled {ι L : Type} [Fintype ι] [Fintype L] [DecidableEq L] (rep : L → X)
    (endpointOf : ι → L) (chain : ι → (Fin 4 → RationalGL3) →₀ ℂ)
    (fill : L → (Fin 5 → RationalGL3) →₀ ℂ)
    (filled : ∀ v, (∑ i ∈ Finset.univ.filter (fun i => endpointOf i = v), chain i) -
      homogeneousBoundary 4 (fill v) ∈ NullChains (levelStabilizer (rep v)) 3)
    (κ : (Fin 4 → RationalGL3) → X → ℂ)
    (hκ : κ ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) 3)
    (closed : ∀ x, differentialThreeRaw κ x = 0) :
    ∑ i, Finsupp.linearCombination ℂ (fun x => κ x (rep (endpointOf i))) (chain i) = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := endpointOf)
    (fun i _ => Finset.mem_univ (endpointOf i))]
  refine Finset.sum_eq_zero fun v _ => ?_
  have regroup : ∑ i ∈ Finset.univ.filter (fun i => endpointOf i = v),
      Finsupp.linearCombination ℂ (fun x => κ x (rep (endpointOf i))) (chain i) =
      Finsupp.linearCombination ℂ (fun x => κ x (rep v))
        (∑ i ∈ Finset.univ.filter (fun i => endpointOf i = v), chain i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  exact regroup.trans (eval_cocycle_of_filled (fun x => κ x (rep v))
    (cochain_invariant κ hκ (rep v)) (fun x => congrFun (closed x) (rep v)) _ _ (filled v))

end Stabilizers

/-- Chain data for a boundary trace: representatives of the orbits of complete flags with
three-chains, representatives of the line and plane orbits containing their endpoints, and
four-chains filling the chains at each vertex modulo the stabilizers. -/
structure TraceData (ι L P : Type) [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L]
    [DecidableEq P] where
  /-- The representative complete flag of each edge orbit. -/
  edge : ι → Edges
  /-- The three-chain at each edge. -/
  chain : ι → (Fin 4 → RationalGL3) →₀ ℂ
  /-- The representative line flags. -/
  lineRep : L → Flags .line
  /-- The line orbit of each edge. -/
  lineOf : ι → L
  line_endpoint : ∀ i, endpoint .line (edge i) = lineRep (lineOf i)
  /-- The four-chain filling the chains at each line. -/
  lineFill : L → (Fin 5 → RationalGL3) →₀ ℂ
  /-- The representative plane flags. -/
  planeRep : P → Flags .plane
  /-- The plane orbit of each edge. -/
  planeOf : ι → P
  plane_endpoint : ∀ i, endpoint .plane (edge i) = planeRep (planeOf i)
  /-- The four-chain filling the chains at each plane. -/
  planeFill : P → (Fin 5 → RationalGL3) →₀ ℂ
  edge_closed : ∀ i, homogeneousBoundary 3 (chain i) ∈ NullChains (levelStabilizer (edge i)) 2
  line_filled : ∀ v, (∑ i ∈ Finset.univ.filter (fun i => lineOf i = v), chain i) -
    homogeneousBoundary 4 (lineFill v) ∈ NullChains (levelStabilizer (lineRep v)) 3
  plane_filled : ∀ v, (∑ i ∈ Finset.univ.filter (fun i => planeOf i = v), chain i) -
    homogeneousBoundary 4 (planeFill v) ∈ NullChains (levelStabilizer (planeRep v)) 3

namespace TraceData

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  (Θ : TraceData ι L P)

/-- The trace of the chain data: `f ↦ Σ_e ⟨f(·)(ē), C_e⟩`. -/
def trace : ((Fin 4 → RationalGL3) → Edges → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ i, Finsupp.linearCombination ℂ (fun x => f x (Θ.edge i)) (Θ.chain i)
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finsupp.linearCombination_apply, Pi.add_apply, smul_add, Finsupp.sum_add]
  map_smul' c f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finsupp.linearCombination_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finsupp.mul_sum]
    exact Finsupp.sum_congr fun x _ => by ring

theorem trace_apply (f : (Fin 4 → RationalGL3) → Edges → ℂ) :
    Θ.trace f = ∑ i, Finsupp.linearCombination ℂ (fun x => f x (Θ.edge i)) (Θ.chain i) :=
  rfl

/-- **The chain data define a boundary trace.** -/
theorem isBoundaryTrace_trace : IsBoundaryTrace Θ.trace.toAddMonoidHom := by
  refine ⟨fun g => ?_, fun κ hκ closed => ?_, fun κ hκ closed => ?_⟩
  · change Θ.trace (differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges) g) = 0
    rw [trace_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact eval_boundary_null (fun y => g.val y (Θ.edge i))
      (cochain_invariant g.val g.property (Θ.edge i)) (Θ.chain i) (Θ.edge_closed i)
  · change Θ.trace (fun x e => κ x (endpoint .plane e)) = 0
    rw [trace_apply]
    have hsum : (∑ i, Finsupp.linearCombination ℂ (fun x => κ x (endpoint .plane (Θ.edge i)))
        (Θ.chain i)) = ∑ i, Finsupp.linearCombination ℂ
          (fun x => κ x (Θ.planeRep (Θ.planeOf i))) (Θ.chain i) :=
      Finset.sum_congr rfl fun i _ => by rw [Θ.plane_endpoint i]
    exact hsum.trans (sum_eval_filled Θ.planeRep Θ.planeOf Θ.chain Θ.planeFill Θ.plane_filled κ
      hκ closed)
  · change Θ.trace (fun x e => κ x (endpoint .line e)) = 0
    rw [trace_apply]
    have hsum : (∑ i, Finsupp.linearCombination ℂ (fun x => κ x (endpoint .line (Θ.edge i)))
        (Θ.chain i)) = ∑ i, Finsupp.linearCombination ℂ
          (fun x => κ x (Θ.lineRep (Θ.lineOf i))) (Θ.chain i) :=
      Finset.sum_congr rfl fun i _ => by rw [Θ.line_endpoint i]
    exact hsum.trans (sum_eval_filled Θ.lineRep Θ.lineOf Θ.chain Θ.lineFill Θ.line_filled κ
      hκ closed)

end TraceData

end TernaryPeriodPolynomials.BoundaryDuality.TraceChains
