module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceRepresentatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineTranslateInvariance

@[expose] public section


/-!
# The boundary trace pairing on the associate pair

Let `τ` be a linear boundary trace. Line summand classes have exact edge pullback (stabilizer
exactness of the line source cocycles), so every representative `z` has an edge primitive `w`. If
every twisted cup product `z ⌣ y^φ` of a line and a plane two-cocycle is exact on lines
(`LineCupExact`, the vanishing of `H⁴(Γ, Fun(Lines, ℂ))` on cup products), every pair of classes has
admissible representatives and primitives; the trace of the boundary cup product `w ⌣ y^φ - γ` does
not depend on them and is additive and homogeneous in each class. This defines the bilinear trace
pairing

  `tracePairing : boundarySummand D .line →ₗ[ℂ] boundarySummand D .plane →ₗ[ℂ] ℂ`,

and boundary duality on the associate pair follows from its left nondegeneracy
(`associatePairDuality_of_pairing`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.TracePairing

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives

section Algebra

variable {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- Every twisted cup product of a line and a plane two-cocycle has an invariant vertex primitive on
lines: `H⁴(Γ, Fun(Lines, ℂ)) = 0` on cup products. -/
def LineCupExact : Prop :=
  ∀ (z : MaximalCycles n χ .line) (y : MaximalCycles n χ .plane), ∃ γ, VertexPrimitive T z y γ

/-- The degree-three differential is homogeneous. -/
theorem differentialThreeRaw_smul {G M : Type} [AddCommGroup M] [Module ℂ M] (c : ℂ)
    (f : (Fin 4 → G) → M) (x : Fin 5 → G) :
    differentialThreeRaw (c • f) x = c • differentialThreeRaw f x := by
  simp only [differentialThreeRaw, Pi.smul_apply, smul_sub, smul_add]

/-- Edge primitives add. -/
theorem edge_add {z₁ z₂ : MaximalCycles n χ .line} {w₁ w₂ : EdgeCochains n χ 1}
    (h₁ : EdgePrimitive z₁ w₁) (h₂ : EdgePrimitive z₂ w₂) :
    EdgePrimitive (z₁ + z₂) (w₁ + w₂) := by
  intro x e
  change z₁.val.val x (endpoint .line e) + z₂.val.val x (endpoint .line e) =
    differentialOneRaw (w₁.val + w₂.val) x e
  rw [h₁ x e, h₂ x e]
  simp only [differentialOneRaw, Pi.add_apply, Pi.sub_apply]
  abel

/-- Edge primitives scale. -/
theorem edge_smul (c : ℂ) {z : MaximalCycles n χ .line} {w : EdgeCochains n χ 1}
    (h : EdgePrimitive z w) : EdgePrimitive (c • z) (c • w) := by
  intro x e
  change c • z.val.val x (endpoint .line e) = differentialOneRaw (c • w.val) x e
  rw [h x e]
  simp only [differentialOneRaw, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_sub, smul_add]

/-- Vertex primitives add in the line cocycle. -/
theorem vertex_add_left {z₁ z₂ : MaximalCycles n χ .line} {y : MaximalCycles n χ .plane}
    {γ₁ γ₂ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (h₁ : VertexPrimitive T z₁ y γ₁) (h₂ : VertexPrimitive T z₂ y γ₂) :
    VertexPrimitive T (z₁ + z₂) y (γ₁ + γ₂) := by
  refine ⟨add_mem h₁.1 h₂.1, fun x F => ?_⟩
  rw [differentialThreeRaw_add, Pi.add_apply, h₁.2 x F, h₂.2 x F]
  change _ = T.B (z₁.val.val ![x 0, x 1, x 2] F + z₂.val.val ![x 0, x 1, x 2] F)
    (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))
  rw [map_add, LinearMap.add_apply]

/-- Vertex primitives add in the plane cocycle. -/
theorem vertex_add_right {z : MaximalCycles n χ .line} {y₁ y₂ : MaximalCycles n χ .plane}
    {γ₁ γ₂ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (h₁ : VertexPrimitive T z y₁ γ₁) (h₂ : VertexPrimitive T z y₂ γ₂) :
    VertexPrimitive T z (y₁ + y₂) (γ₁ + γ₂) := by
  refine ⟨add_mem h₁.1 h₂.1, fun x F => ?_⟩
  rw [differentialThreeRaw_add, Pi.add_apply, h₁.2 x F, h₂.2 x F]
  change _ = T.B (z.val.val ![x 0, x 1, x 2] F)
    (y₁.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F) +
      y₂.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))
  rw [map_add]

/-- Vertex primitives scale with the line cocycle. -/
theorem vertex_smul_left (c : ℂ) {z : MaximalCycles n χ .line} {y : MaximalCycles n χ .plane}
    {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ} (h : VertexPrimitive T z y γ) :
    VertexPrimitive T (c • z) y (c • γ) := by
  refine ⟨Submodule.smul_mem _ c h.1, fun x F => ?_⟩
  rw [differentialThreeRaw_smul, Pi.smul_apply, h.2 x F]
  change _ = T.B (c • z.val.val ![x 0, x 1, x 2] F)
    (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))
  rw [map_smul, LinearMap.smul_apply]

/-- Vertex primitives scale with the plane cocycle. -/
theorem vertex_smul_right (c : ℂ) {z : MaximalCycles n χ .line} {y : MaximalCycles n χ .plane}
    {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ} (h : VertexPrimitive T z y γ) :
    VertexPrimitive T z (c • y) (c • γ) := by
  refine ⟨Submodule.smul_mem _ c h.1, fun x F => ?_⟩
  rw [differentialThreeRaw_smul, Pi.smul_apply, h.2 x F]
  change _ = T.B (z.val.val ![x 0, x 1, x 2] F)
    (c • y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))
  rw [map_smul]

/-- The boundary value is additive in the line data. -/
theorem boundaryValue_add_left (w₁ w₂ : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (γ₁ γ₂ : (Fin 4 → RationalGL3) → Flags .line → ℂ) :
    boundaryValue T (w₁ + w₂) y (γ₁ + γ₂) =
      boundaryValue T w₁ y γ₁ + boundaryValue T w₂ y γ₂ := by
  funext x e
  change T.B (w₁.val ![x 0, x 1] e + w₂.val ![x 0, x 1] e)
      (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      (γ₁ x (endpoint .line e) + γ₂ x (endpoint .line e)) =
    (T.B (w₁.val ![x 0, x 1] e)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      γ₁ x (endpoint .line e)) +
    (T.B (w₂.val ![x 0, x 1] e)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      γ₂ x (endpoint .line e))
  rw [map_add, LinearMap.add_apply]
  abel

/-- The boundary value is additive in the plane data. -/
theorem boundaryValue_add_right (w : EdgeCochains n χ 1) (y₁ y₂ : MaximalCycles n χ .plane)
    (γ₁ γ₂ : (Fin 4 → RationalGL3) → Flags .line → ℂ) :
    boundaryValue T w (y₁ + y₂) (γ₁ + γ₂) =
      boundaryValue T w y₁ γ₁ + boundaryValue T w y₂ γ₂ := by
  funext x e
  change T.B (w.val ![x 0, x 1] e)
      (y₁.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e)) +
        y₂.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      (γ₁ x (endpoint .line e) + γ₂ x (endpoint .line e)) =
    (T.B (w.val ![x 0, x 1] e)
        (y₁.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      γ₁ x (endpoint .line e)) +
    (T.B (w.val ![x 0, x 1] e)
        (y₂.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      γ₂ x (endpoint .line e))
  rw [map_add]
  abel

/-- The boundary value is homogeneous in the line data. -/
theorem boundaryValue_smul_left (c : ℂ) (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ) :
    boundaryValue T (c • w) y (c • γ) = c • boundaryValue T w y γ := by
  funext x e
  change T.B (c • w.val ![x 0, x 1] e)
      (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      c • γ x (endpoint .line e) =
    c • (T.B (w.val ![x 0, x 1] e)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      γ x (endpoint .line e))
  rw [map_smul, LinearMap.smul_apply, smul_sub]

/-- The boundary value is homogeneous in the plane data. -/
theorem boundaryValue_smul_right (c : ℂ) (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ) :
    boundaryValue T w (c • y) (c • γ) = c • boundaryValue T w y γ := by
  funext x e
  change T.B (w.val ![x 0, x 1] e)
      (c • y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      c • γ x (endpoint .line e) =
    c • (T.B (w.val ![x 0, x 1] e)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
      γ x (endpoint .line e))
  rw [map_smul, smul_sub]

/-- Admissible data for a pair of classes: representatives of both, an edge primitive of the line
representative and a vertex primitive of the twisted cup product. -/
structure Admissible (b : StratumH2 n χ .line) (ξ : StratumH2 n χ .plane) where
  /-- The line representative. -/
  z : MaximalCycles n χ .line
  /-- Its edge primitive. -/
  w : EdgeCochains n χ 1
  /-- The plane representative. -/
  y : MaximalCycles n χ .plane
  /-- The vertex primitive on lines. -/
  γ : (Fin 4 → RationalGL3) → Flags .line → ℂ
  class_z : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z = b
  class_y : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y =
    ξ
  edge : EdgePrimitive z w
  vertex : VertexPrimitive T z y γ

open Classical in
/-- The trace of the boundary cup product of two classes, computed on any admissible data (zero if
there is none). -/
def pairingValue (τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →ₗ[ℂ] ℂ) (b : StratumH2 n χ .line)
    (ξ : StratumH2 n χ .plane) : ℂ :=
  if h : Nonempty (Admissible T b ξ) then
    τ (boundaryValue T h.some.w h.some.y h.some.γ)
  else 0

/-- The pairing value is the trace computed on any admissible data. -/
theorem pairingValue_eq {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →ₗ[ℂ] ℂ}
    (hτ : IsBoundaryTrace τ.toAddMonoidHom) {b : StratumH2 n χ .line} {ξ : StratumH2 n χ .plane}
    (flat : ∀ y : MaximalCycles n χ .plane,
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y = ξ →
        PlaneEdgeExact y)
    {z : MaximalCycles n χ .line} {w : EdgeCochains n χ 1} {y : MaximalCycles n χ .plane}
    {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z = b)
    (hy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y =
      ξ)
    (hw : EdgePrimitive z w) (hγ : VertexPrimitive T z y γ) :
    pairingValue T τ b ξ = τ (boundaryValue T w y γ) := by
  have h : Nonempty (Admissible T b ξ) := ⟨⟨z, w, y, γ, hz, hy, hw, hγ⟩⟩
  rw [pairingValue, dite_eq_left h]
  exact trace_eq T hτ h.some.edge h.some.vertex hw hγ (h.some.class_z.trans hz.symm)
    (h.some.class_y.trans hy.symm) (flat y hy)

end Algebra

section Summand

variable {n : ℕ} {D : InducingData n} (T : DualityData n D.chi)

/-- Line summand classes have exact edge pullback, for every representative: this is the
stabilizer exactness of the line source cocycles. -/
theorem exists_edgePrimitive_of_mem (z : MaximalCycles n D.chi .line)
    (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
      z ∈ boundarySummand D .line) :
    ∃ w, EdgePrimitive z w := by
  have hker := GraphPieces.EndpointReduction.boundarySummand_le_ker D .line
    (fun source isSource flag => FlagExactness.line_flagExact D source isSource flag) hz
  rw [LinearMap.mem_ker, GraphPieces.BoundaryExactness.endpointPullH2_realizes] at hker
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hker)
  exact ⟨w, fun x e =>
    (congrFun (congrFun (congrArg Subtype.val (congrArg Subtype.val hw)) x) e).symm⟩

/-- Plane exactness for every representative of a plane summand class. -/
theorem flat_of_mem {ξ : StratumH2 n D.chi .plane} (hξ : ξ ∈ boundarySummand D .plane)
    (y : MaximalCycles n D.chi .plane)
    (hy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      y = ξ) :
    PlaneEdgeExact y :=
  planeEdgeExact_of_mem (D := D) y (by rw [hy]; exact hξ)

/-- Every class has a representative. -/
theorem exists_rep {s : Side} (b : StratumH2 n D.chi s) :
    ∃ z : MaximalCycles n D.chi s,
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) s) z = b :=
  Submodule.mkQ_surjective _ b

variable {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →ₗ[ℂ] ℂ}

/-- Additivity of the pairing in the line class. -/
theorem pairingValue_add_left (hτ : IsBoundaryTrace τ.toAddMonoidHom) (hcup : LineCupExact T)
    {b₁ b₂ : StratumH2 n D.chi .line} (hb₁ : b₁ ∈ boundarySummand D .line)
    (hb₂ : b₂ ∈ boundarySummand D .line) {ξ : StratumH2 n D.chi .plane}
    (hξ : ξ ∈ boundarySummand D .plane) :
    pairingValue T τ (b₁ + b₂) ξ = pairingValue T τ b₁ ξ + pairingValue T τ b₂ ξ := by
  obtain ⟨y, hy⟩ := exists_rep ξ
  obtain ⟨z₁, hz₁⟩ := exists_rep b₁
  obtain ⟨z₂, hz₂⟩ := exists_rep b₂
  obtain ⟨w₁, hw₁⟩ := exists_edgePrimitive_of_mem (D := D) z₁ (by rw [hz₁]; exact hb₁)
  obtain ⟨w₂, hw₂⟩ := exists_edgePrimitive_of_mem (D := D) z₂ (by rw [hz₂]; exact hb₂)
  obtain ⟨γ₁, hγ₁⟩ := hcup z₁ y
  obtain ⟨γ₂, hγ₂⟩ := hcup z₂ y
  have hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
      (z₁ + z₂) = b₁ + b₂ := by rw [map_add, hz₁, hz₂]
  rw [pairingValue_eq T hτ (flat_of_mem hξ) hz hy (edge_add hw₁ hw₂) (vertex_add_left T hγ₁ hγ₂),
    pairingValue_eq T hτ (flat_of_mem hξ) hz₁ hy hw₁ hγ₁,
    pairingValue_eq T hτ (flat_of_mem hξ) hz₂ hy hw₂ hγ₂, boundaryValue_add_left, map_add]

/-- Homogeneity of the pairing in the line class. -/
theorem pairingValue_smul_left (hτ : IsBoundaryTrace τ.toAddMonoidHom) (hcup : LineCupExact T)
    (c : ℂ) {b : StratumH2 n D.chi .line} (hb : b ∈ boundarySummand D .line)
    {ξ : StratumH2 n D.chi .plane} (hξ : ξ ∈ boundarySummand D .plane) :
    pairingValue T τ (c • b) ξ = c • pairingValue T τ b ξ := by
  obtain ⟨y, hy⟩ := exists_rep ξ
  obtain ⟨z, hz⟩ := exists_rep b
  obtain ⟨w, hw⟩ := exists_edgePrimitive_of_mem (D := D) z (by rw [hz]; exact hb)
  obtain ⟨γ, hγ⟩ := hcup z y
  have hcz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
      (c • z) = c • b := by rw [map_smul, hz]
  rw [pairingValue_eq T hτ (flat_of_mem hξ) hcz hy (edge_smul c hw) (vertex_smul_left T c hγ),
    pairingValue_eq T hτ (flat_of_mem hξ) hz hy hw hγ, boundaryValue_smul_left, map_smul]

/-- Additivity of the pairing in the plane class. -/
theorem pairingValue_add_right (hτ : IsBoundaryTrace τ.toAddMonoidHom) (hcup : LineCupExact T)
    {b : StratumH2 n D.chi .line} (hb : b ∈ boundarySummand D .line)
    {ξ₁ ξ₂ : StratumH2 n D.chi .plane} (hξ₁ : ξ₁ ∈ boundarySummand D .plane)
    (hξ₂ : ξ₂ ∈ boundarySummand D .plane) :
    pairingValue T τ b (ξ₁ + ξ₂) = pairingValue T τ b ξ₁ + pairingValue T τ b ξ₂ := by
  obtain ⟨z, hz⟩ := exists_rep b
  obtain ⟨y₁, hy₁⟩ := exists_rep ξ₁
  obtain ⟨y₂, hy₂⟩ := exists_rep ξ₂
  obtain ⟨w, hw⟩ := exists_edgePrimitive_of_mem (D := D) z (by rw [hz]; exact hb)
  obtain ⟨γ₁, hγ₁⟩ := hcup z y₁
  obtain ⟨γ₂, hγ₂⟩ := hcup z y₂
  have hy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      (y₁ + y₂) = ξ₁ + ξ₂ := by rw [map_add, hy₁, hy₂]
  rw [pairingValue_eq T hτ (flat_of_mem (add_mem hξ₁ hξ₂)) hz hy hw (vertex_add_right T hγ₁ hγ₂),
    pairingValue_eq T hτ (flat_of_mem hξ₁) hz hy₁ hw hγ₁,
    pairingValue_eq T hτ (flat_of_mem hξ₂) hz hy₂ hw hγ₂, boundaryValue_add_right, map_add]

/-- Homogeneity of the pairing in the plane class. -/
theorem pairingValue_smul_right (hτ : IsBoundaryTrace τ.toAddMonoidHom) (hcup : LineCupExact T)
    (c : ℂ) {b : StratumH2 n D.chi .line} (hb : b ∈ boundarySummand D .line)
    {ξ : StratumH2 n D.chi .plane} (hξ : ξ ∈ boundarySummand D .plane) :
    pairingValue T τ b (c • ξ) = c • pairingValue T τ b ξ := by
  obtain ⟨z, hz⟩ := exists_rep b
  obtain ⟨y, hy⟩ := exists_rep ξ
  obtain ⟨w, hw⟩ := exists_edgePrimitive_of_mem (D := D) z (by rw [hz]; exact hb)
  obtain ⟨γ, hγ⟩ := hcup z y
  have hcy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      (c • y) = c • ξ := by rw [map_smul, hy]
  rw [pairingValue_eq T hτ (flat_of_mem (Submodule.smul_mem _ c hξ)) hz hcy hw
      (vertex_smul_right T c hγ),
    pairingValue_eq T hτ (flat_of_mem hξ) hz hy hw hγ, boundaryValue_smul_right, map_smul]

/-- **The trace pairing** on the associate pair: line summand × plane summand → ℂ, the trace of
the boundary cup product of representatives. -/
def tracePairing (hτ : IsBoundaryTrace τ.toAddMonoidHom) (hcup : LineCupExact T) :
    boundarySummand D .line →ₗ[ℂ] boundarySummand D .plane →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun b ξ => pairingValue T τ b.val ξ.val)
    (fun b₁ b₂ ξ => pairingValue_add_left T hτ hcup b₁.2 b₂.2 ξ.2)
    (fun c b ξ => pairingValue_smul_left T hτ hcup c b.2 ξ.2)
    (fun b ξ₁ ξ₂ => pairingValue_add_right T hτ hcup b.2 ξ₁.2 ξ₂.2)
    (fun c b ξ => pairingValue_smul_right T hτ hcup c b.2 ξ.2)

/-- The trace pairing is the trace computed on any admissible data. -/
theorem tracePairing_eq (hτ : IsBoundaryTrace τ.toAddMonoidHom) (hcup : LineCupExact T)
    (b : boundarySummand D .line) (ξ : boundarySummand D .plane)
    {z : MaximalCycles n D.chi .line} {w : EdgeCochains n D.chi 1}
    {y : MaximalCycles n D.chi .plane} {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
      z = b.val)
    (hy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      y = ξ.val)
    (hw : EdgePrimitive z w) (hγ : VertexPrimitive T z y γ) :
    tracePairing T hτ hcup b ξ = τ (boundaryValue T w y γ) :=
  pairingValue_eq T hτ (flat_of_mem ξ.2) hz hy hw hγ

/-- **Boundary duality from the trace pairing.** A linear boundary trace whose pairing is left
nondegenerate on the associate pair gives `AssociateDuality`, given `LineCupExact`. -/
theorem associateDuality_of_pairing (hτ : IsBoundaryTrace τ.toAddMonoidHom)
    (hcup : LineCupExact T)
    (nondeg : ∀ b : boundarySummand D .line, b ≠ 0 →
      ∃ ξ : boundarySummand D .plane, tracePairing T hτ hcup b ξ ≠ 0) :
    AssociateDuality D T.φ T.dualFlag T.B := by
  apply associateDuality_of_witness T hτ
  intro b hb hne
  obtain ⟨ξ, hξ⟩ := nondeg ⟨b, hb⟩ fun h => hne (congrArg Subtype.val h)
  obtain ⟨z, hz⟩ := exists_rep b
  obtain ⟨y, hy⟩ := exists_rep ξ.val
  obtain ⟨w, hw⟩ := exists_edgePrimitive_of_mem (D := D) z (by rw [hz]; exact hb)
  obtain ⟨γ, hγ⟩ := hcup z y
  refine ⟨ξ.val, ξ.2, z, w, y, γ, hz, hy, hw, hγ, fun hzero => hξ ?_⟩
  rw [tracePairing_eq T hτ hcup ⟨b, hb⟩ ξ hz hy hw hγ]
  exact hzero

end Summand

/-- **Boundary duality on the associate pair from the trace pairing**, for the concrete involution,
flag maps and apolar pairing. -/
theorem associatePairDuality_of_pairing {n : ℕ} (D : InducingData n)
    {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →ₗ[ℂ] ℂ} (hτ : IsBoundaryTrace τ.toAddMonoidHom)
    (hcup : LineCupExact (dualityData n D.chi))
    (nondeg : ∀ b : boundarySummand D .line, b ≠ 0 →
      ∃ ξ : boundarySummand D .plane, tracePairing (dualityData n D.chi) hτ hcup b ξ ≠ 0) :
    AssociatePairDuality D :=
  associateDuality_of_pairing (dualityData n D.chi) hτ hcup nondeg

end TernaryPeriodPolynomials.BoundaryDuality.TracePairing
