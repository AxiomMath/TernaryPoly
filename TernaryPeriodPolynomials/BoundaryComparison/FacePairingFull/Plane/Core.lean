module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceRepresentatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.FlagShapiro
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerVanishing

@[expose] public section


/-!
# Plane trace calculus: the face pairing `⟨ , ⟩_P` on the plane side

Mirror, under the exchange of the line and plane sides, of the trace calculus of
`AxiomCodeBoundaryDuality` (`TraceRepresentatives`, `ChainPairing`, `ChainLocal`, `FlagShapiro`)
that underlies the line pairing `⟨ , ⟩_Q`. Here `z` is a PLANE cocycle of `E` with an edge
primitive `w` (`z ∘ endpoint = dw`), `y` is a LINE cocycle moved to planes by `φ` and the flag map
`dualPlaneFlag`, and `γ` is a vertex primitive of the twisted cup product on plane flags. The
boundary trace `IsBoundaryTrace` is symmetric under the exchange (its two pullback clauses are the
plane and the line one), so every argument of the line side carries over verbatim:

* `trace_vertex_eqP`, `trace_edge_eqP`, `line_coboundaryP`, `plane_coboundaryP`, `trace_eqP`:
  independence of the trace of the boundary cup product of all choices;
* `chainValueP`, `trace_eq_chainValueP`, `chainValue_eq_sumP`: the trace without the vertex
  primitive is the sum over the plane cusps of the local values `planeValueP`;
* `planeCupExact_of_topVanishingP`: existence of plane vertex primitives from `H⁴` vanishing of
  the plane stabilizers.

The file is the mechanical image of the line-side files; every declaration carries the suffix `P`
(and the exchange of `line` and `plane` in its name).

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.ChainPairing
open TernaryPeriodPolynomials.TopVanishing (IsTopVanishing homogeneousBoundary)
open TernaryPeriodPolynomials.GraphPieces.EdgeOrbitAssembly
open TernaryPeriodPolynomials.BoundaryDuality.FlagShapiro
  (exists_primitive pointStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing
  (topVanishing_pointStabilizer_unconditional)




/-- The data moving line classes onto planes: a level-preserving endomorphism `φ` of `GL₃(ℚ)`, a
pairing `B` of the coefficients with their `φ`-twist invariant under the level, and maps from plane
flags to line flags and from complete flags to complete flags, equivariant along `φ` and compatible
with the endpoints. -/
structure DualityDataP (n : ℕ) (χ : RankOneCharacter) where
  /-- The endomorphism of `GL₃(ℚ)`. -/
  φ : RationalGL3 →* RationalGL3
  /-- `φ` preserves the arithmetic level. -/
  level : ∀ g ∈ rationalLevel, φ g ∈ rationalLevel
  /-- The pairing of the coefficients with their `φ`-twist. -/
  B : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ
  /-- Invariance of the pairing under the level. -/
  invariant : ∀ g ∈ rationalLevel, ∀ v w,
    B (rationalCoefficientComponent n χ g v) (rationalCoefficientComponent n χ (φ g) w) = B v w
  /-- The map from plane flags to line flags. -/
  dualFlag : Flags .plane → Flags .line
  /-- The flag map is equivariant along `φ`. -/
  dualFlag_smul : ∀ g F, dualFlag (g • F) = φ g • dualFlag F
  /-- The map on complete flags. -/
  dualEdge : Edges → Edges
  /-- The complete flag map is equivariant along `φ`. -/
  dualEdge_smul : ∀ g e, dualEdge (g • e) = φ g • dualEdge e
  /-- The line endpoint of the dual complete flag is the dual of the plane endpoint. -/
  endpoint_dualEdge : ∀ e, endpoint .line (dualEdge e) = dualFlag (endpoint .plane e)

variable {n : ℕ} {χ : RankOneCharacter} (T : DualityDataP n χ)

/-- The boundary cup product `w ⌣ y^φ - γ` on complete flags. -/
def boundaryValueP (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .line)
    (γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ) : (Fin 4 → RationalGL3) → Edges → ℂ :=
  fun x e => T.B (w.val ![x 0, x 1] e) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)]
    (T.dualFlag (endpoint .plane e))) - γ x (endpoint .plane e)

/-- `w` is an edge primitive of the plane two-cocycle `z`: `z ∘ endpoint = dw`. -/
def EdgePrimitiveP (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1) : Prop :=
  ∀ x e, z.val.val x (endpoint .plane e) = differentialOneRaw w.val x e

/-- `γ` is an invariant vertex primitive of the twisted cup product `z ⌣ y^φ` on planes. -/
def VertexPrimitiveP (z : MaximalCycles n χ .plane) (y : MaximalCycles n χ .line)
    (γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ) : Prop :=
  γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3 ∧
    ∀ x F, differentialThreeRaw γ x F =
      T.B (z.val.val ![x 0, x 1, x 2] F)
        (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))

/-- The pullback of the line two-cocycle `y` to complete flags is exact. -/
def LineEdgeExactP (y : MaximalCycles n χ .line) : Prop :=
  ∃ s : EdgeCochains n χ 1, ∀ x e,
    y.val.val x (endpoint .line e) = differentialOneRaw s.val x e

/-- The scalar plane three-cochain `u ⌣ y^φ`. -/
def planeCupOneTwoP (u : MaximalCochains n χ .plane 1) (y : MaximalCycles n χ .line) :
    (Fin 4 → RationalGL3) → Flags .plane → ℂ :=
  fun x F => T.B (u.val ![x 0, x 1] F)
    (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag F))

/-- The scalar plane three-cochain `z ⌣ s^φ`. -/
def planeCupTwoOneP (z : MaximalCycles n χ .plane) (s : MaximalCochains n χ .line 1) :
    (Fin 4 → RationalGL3) → Flags .plane → ℂ :=
  fun x F => T.B (z.val.val ![x 0, x 1, x 2] F) (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag F))

theorem planeCupOneTwo_memP (u : MaximalCochains n χ .plane 1) (y : MaximalCycles n χ .line) :
    planeCupOneTwoP T u y ∈
      cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3 := by
  intro g x
  funext F
  have dual : T.φ g.val ∈ rationalLevel := T.level g.val g.property
  change T.B (u.val ![g.val * x 0, g.val * x 1] F)
      (y.val.val ![T.φ (g.val * x 1), T.φ (g.val * x 2), T.φ (g.val * x 3)] (T.dualFlag F)) =
    T.B (u.val ![x 0, x 1] (g.val⁻¹ • F))
      (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (g.val⁻¹ • F)))
  rw [congrFun (cochain_pair u g (x 0) (x 1)) F, map_mul, map_mul, map_mul,
    cochain_triple y.val ⟨T.φ g.val, dual⟩]
  change T.B (rationalCoefficientComponent n χ g.val (u.val ![x 0, x 1] (g.val⁻¹ • F)))
      (rationalCoefficientComponent n χ (T.φ g.val)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] ((T.φ g.val)⁻¹ • T.dualFlag F))) = _
  rw [T.invariant g.val g.property, ← map_inv T.φ g.val, ← T.dualFlag_smul]

theorem planeCupTwoOne_memP (z : MaximalCycles n χ .plane) (s : MaximalCochains n χ .line 1) :
    planeCupTwoOneP T z s ∈
      cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3 := by
  intro g x
  funext F
  have dual : T.φ g.val ∈ rationalLevel := T.level g.val g.property
  change T.B (z.val.val ![g.val * x 0, g.val * x 1, g.val * x 2] F)
      (s.val ![T.φ (g.val * x 2), T.φ (g.val * x 3)] (T.dualFlag F)) =
    T.B (z.val.val ![x 0, x 1, x 2] (g.val⁻¹ • F))
      (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag (g.val⁻¹ • F)))
  rw [congrFun (cochain_triple z.val g (x 0) (x 1) (x 2)) F, map_mul, map_mul,
    congrFun (cochain_pair s ⟨T.φ g.val, dual⟩ (T.φ (x 2)) (T.φ (x 3))) (T.dualFlag F)]
  change T.B (rationalCoefficientComponent n χ g.val (z.val.val ![x 0, x 1, x 2] (g.val⁻¹ • F)))
      (rationalCoefficientComponent n χ (T.φ g.val)
        (s.val ![T.φ (x 2), T.φ (x 3)] ((T.φ g.val)⁻¹ • T.dualFlag F))) = _
  rw [T.invariant g.val g.property, ← map_inv T.φ g.val, ← T.dualFlag_smul]

/-- Leibniz rule for `u ⌣ y^φ`: its differential is `du ⌣ y^φ`. -/
theorem planeCupOneTwo_differentialP (u : MaximalCochains n χ .plane 1)
    (y : MaximalCycles n χ .line) (x : Fin 5 → RationalGL3) (F : Flags .plane) :
    differentialThreeRaw (planeCupOneTwoP T u y) x F =
      T.B (differentialOneRaw u.val ![x 0, x 1, x 2] F)
        (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F)) := by
  have cocycle : IsCocycleTwo (fun x' => y.val.val x' (T.dualFlag F)) := fun x' =>
    congrFun (isCocycleTwo_of_mem y x') (T.dualFlag F)
  exact differentialThreeRaw_cupOneTwo T.B T.φ (fun x' => u.val x' F) cocycle x

/-- Leibniz rule for `z ⌣ s^φ`: its differential is `z ⌣ (ds)^φ`. -/
theorem planeCupTwoOne_differentialP (z : MaximalCycles n χ .plane)
    (s : MaximalCochains n χ .line 1) (x : Fin 5 → RationalGL3) (F : Flags .plane) :
    differentialThreeRaw (planeCupTwoOneP T z s) x F =
      T.B (z.val.val ![x 0, x 1, x 2] F)
        (differentialOneRaw s.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F)) := by
  have cocycle : IsCocycleTwo (fun x' => z.val.val x' F) := fun x' =>
    congrFun (isCocycleTwo_of_mem z x') F
  exact differentialThreeRaw_cupTwoOne T.B T.φ cocycle (fun x' => s.val x' (T.dualFlag F)) x

/-- The scalar edge two-cochain `a ⌣ s^φ` for an edge one-cochain `s` read at the dual complete
flag. -/
def edgeDualCupP (a s : EdgeCochains n χ 1) :
    cochains rationalLevel (functionRepresentation scalarTrivial Edges) 2 :=
  ⟨fun x e => T.B (a.val ![x 0, x 1] e) (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualEdge e)), by
    intro g x
    funext e
    have dual : T.φ g.val ∈ rationalLevel := T.level g.val g.property
    change T.B (a.val ![g.val * x 0, g.val * x 1] e)
        (s.val ![T.φ (g.val * x 1), T.φ (g.val * x 2)] (T.dualEdge e)) =
      T.B (a.val ![x 0, x 1] (g.val⁻¹ • e))
        (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualEdge (g.val⁻¹ • e)))
    rw [congrFun (cochain_pair a g (x 0) (x 1)) e, map_mul, map_mul,
      congrFun (cochain_pair s ⟨T.φ g.val, dual⟩ (T.φ (x 1)) (T.φ (x 2))) (T.dualEdge e)]
    change T.B (rationalCoefficientComponent n χ g.val (a.val ![x 0, x 1] (g.val⁻¹ • e)))
        (rationalCoefficientComponent n χ (T.φ g.val)
          (s.val ![T.φ (x 1), T.φ (x 2)] ((T.φ g.val)⁻¹ • T.dualEdge e))) = _
    rw [T.invariant g.val g.property, ← map_inv T.φ g.val, ← T.dualEdge_smul]⟩

/-- The scalar edge two-cochain `a ⌣ s^φ` for a line one-cochain `s` moved to planes. -/
def edgePlaneCupP (a : EdgeCochains n χ 1) (s : MaximalCochains n χ .line 1) :
    cochains rationalLevel (functionRepresentation scalarTrivial Edges) 2 :=
  ⟨fun x e => T.B (a.val ![x 0, x 1] e)
      (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualFlag (endpoint .plane e))), by
    intro g x
    funext e
    have dual : T.φ g.val ∈ rationalLevel := T.level g.val g.property
    change T.B (a.val ![g.val * x 0, g.val * x 1] e)
        (s.val ![T.φ (g.val * x 1), T.φ (g.val * x 2)] (T.dualFlag (endpoint .plane e))) =
      T.B (a.val ![x 0, x 1] (g.val⁻¹ • e))
        (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualFlag (endpoint .plane (g.val⁻¹ • e))))
    rw [congrFun (cochain_pair a g (x 0) (x 1)) e, map_mul, map_mul,
      congrFun (cochain_pair s ⟨T.φ g.val, dual⟩ (T.φ (x 1)) (T.φ (x 2)))
        (T.dualFlag (endpoint .plane e))]
    change T.B (rationalCoefficientComponent n χ g.val (a.val ![x 0, x 1] (g.val⁻¹ • e)))
        (rationalCoefficientComponent n χ (T.φ g.val)
          (s.val ![T.φ (x 1), T.φ (x 2)] ((T.φ g.val)⁻¹ • T.dualFlag (endpoint .plane e)))) = _
    rw [T.invariant g.val g.property, ← map_inv T.φ g.val, ← T.dualFlag_smul, ← endpoint_smul]⟩

section Steps

variable {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ}

/-- Two vertex primitives give the same trace: they differ by a plane three-cocycle. -/
theorem trace_vertex_eqP (hτ : IsBoundaryTrace τ) {z : MaximalCycles n χ .plane}
    {y : MaximalCycles n χ .line} (w : EdgeCochains n χ 1)
    {γ γ' : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hγ : VertexPrimitiveP T z y γ) (hγ' : VertexPrimitiveP T z y γ') :
    τ (boundaryValueP T w y γ) = τ (boundaryValueP T w y γ') := by
  have closed : ∀ x, differentialThreeRaw (γ' - γ) x = 0 := by
    intro x
    funext F
    simp only [differentialThreeRaw_sub, Pi.sub_apply, hγ'.2 x F, hγ.2 x F, sub_self,
      Pi.zero_apply]
  have split : boundaryValueP T w y γ =
      boundaryValueP T w y γ' + fun x e => (γ' - γ) x (endpoint .plane e) := by
    funext x e
    simp only [boundaryValueP, Pi.add_apply, Pi.sub_apply]
    abel
  rw [split, map_add, hτ.2.1 (γ' - γ) (sub_mem hγ'.1 hγ.1) closed, add_zero]

/-- Two edge primitives give the same trace when the edge pullback of `y` is exact: they differ by
an edge one-cocycle `η`, and `η ⌣ y^φ = -d(η ⌣ s^φ)` for `y ∘ endpoint = ds`. -/
theorem trace_edge_eqP (hτ : IsBoundaryTrace τ) {z : MaximalCycles n χ .plane}
    {w w' : EdgeCochains n χ 1} {y : MaximalCycles n χ .line}
    {γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hw : EdgePrimitiveP z w) (hw' : EdgePrimitiveP z w') (flat : LineEdgeExactP y) :
    τ (boundaryValueP T w y γ) = τ (boundaryValueP T w' y γ) := by
  obtain ⟨s, hs⟩ := flat
  have key : boundaryValueP T w y γ = boundaryValueP T w' y γ -
      differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges)
        (edgeDualCupP T (w - w') s) := by
    funext x e
    have hY : y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e)) =
        s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge e) -
          s.val ![T.φ (x 1), T.φ (x 3)] (T.dualEdge e) +
          s.val ![T.φ (x 1), T.φ (x 2)] (T.dualEdge e) := by
      rw [← T.endpoint_dualEdge e]
      exact hs ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualEdge e)
    have h₁ : z.val.val ![x 0, x 1, x 2] (endpoint .plane e) =
        w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e :=
      hw ![x 0, x 1, x 2] e
    have h₂ : z.val.val ![x 0, x 1, x 2] (endpoint .plane e) =
        w'.val ![x 1, x 2] e - w'.val ![x 0, x 2] e + w'.val ![x 0, x 1] e :=
      hw' ![x 0, x 1, x 2] e
    have h₁₂ : w.val ![x 1, x 2] e = w'.val ![x 1, x 2] e - w'.val ![x 0, x 2] e +
        w'.val ![x 0, x 1] e + w.val ![x 0, x 2] e - w.val ![x 0, x 1] e := by
      rw [← h₂, h₁]; abel
    change T.B (w.val ![x 0, x 1] e) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)]
          (T.dualFlag (endpoint .plane e))) - γ x (endpoint .plane e) =
        (T.B (w'.val ![x 0, x 1] e) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)]
          (T.dualFlag (endpoint .plane e))) - γ x (endpoint .plane e)) -
        (T.B (w.val ![x 1, x 2] e - w'.val ![x 1, x 2] e)
            (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge e)) -
          T.B (w.val ![x 0, x 2] e - w'.val ![x 0, x 2] e)
            (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge e)) +
          T.B (w.val ![x 0, x 1] e - w'.val ![x 0, x 1] e)
            (s.val ![T.φ (x 1), T.φ (x 3)] (T.dualEdge e)) -
          T.B (w.val ![x 0, x 1] e - w'.val ![x 0, x 1] e)
            (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualEdge e)))
    rw [hY, h₁₂]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    abel
  rw [key, map_sub, hτ.1, sub_zero]

/-- Changing the plane cocycle `z` by the coboundary `du` is absorbed by the primitives
`w + u ∘ endpoint` and `γ + u ⌣ y^φ`, with literally the same boundary value. -/
theorem plane_coboundaryP {z : MaximalCycles n χ .plane} {w : EdgeCochains n χ 1}
    {y : MaximalCycles n χ .line} {γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hw : EdgePrimitiveP z w) (hγ : VertexPrimitiveP T z y γ) (u : MaximalCochains n χ .plane 1) :
    EdgePrimitiveP (z + boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .plane) u)
      (w + TernaryPeriodPolynomials.GraphPieces.BoundaryExactness.endpointPullCochain n χ .plane 1 u) ∧
    VertexPrimitiveP T (z + boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .plane) u) y
      (γ + planeCupOneTwoP T u y) ∧
    boundaryValueP T (w + TernaryPeriodPolynomials.GraphPieces.BoundaryExactness.endpointPullCochain n χ .plane 1 u) y
        (γ + planeCupOneTwoP T u y) = boundaryValueP T w y γ := by
  refine ⟨fun x e => ?_, And.intro (add_mem hγ.1 (planeCupOneTwo_memP T u y)) fun x F => ?_, ?_⟩
  · have h : z.val.val x (endpoint .plane e) =
        w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e := hw x e
    change z.val.val x (endpoint .plane e) +
        (u.val ![x 1, x 2] (endpoint .plane e) - u.val ![x 0, x 2] (endpoint .plane e) +
          u.val ![x 0, x 1] (endpoint .plane e)) =
      (w.val ![x 1, x 2] e + u.val ![x 1, x 2] (endpoint .plane e)) -
        (w.val ![x 0, x 2] e + u.val ![x 0, x 2] (endpoint .plane e)) +
        (w.val ![x 0, x 1] e + u.val ![x 0, x 1] (endpoint .plane e))
    rw [h]
    abel
  · rw [differentialThreeRaw_add, Pi.add_apply, hγ.2 x F, planeCupOneTwo_differentialP]
    change _ = T.B (z.val.val ![x 0, x 1, x 2] F + differentialOneRaw u.val ![x 0, x 1, x 2] F)
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))
    rw [map_add, LinearMap.add_apply]
  · funext x e
    change T.B (w.val ![x 0, x 1] e + u.val ![x 0, x 1] (endpoint .plane e))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e))) -
        (γ x (endpoint .plane e) + T.B (u.val ![x 0, x 1] (endpoint .plane e))
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e)))) =
      T.B (w.val ![x 0, x 1] e)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e))) -
        γ x (endpoint .plane e)
    rw [map_add, LinearMap.add_apply]
    abel

/-- Changing the line cocycle `y` by the coboundary `ds` is absorbed by the vertex primitive
`γ + z ⌣ s^φ`; the boundary value changes by the coboundary `-d(w ⌣ s^φ)`. -/
theorem line_coboundaryP (hτ : IsBoundaryTrace τ) {z : MaximalCycles n χ .plane}
    {w : EdgeCochains n χ 1} {y : MaximalCycles n χ .line}
    {γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hw : EdgePrimitiveP z w) (hγ : VertexPrimitiveP T z y γ) (s : MaximalCochains n χ .line 1) :
    VertexPrimitiveP T z (y + boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .line) s)
      (γ + planeCupTwoOneP T z s) ∧
    τ (boundaryValueP T w (y + boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .line) s)
      (γ + planeCupTwoOneP T z s)) = τ (boundaryValueP T w y γ) := by
  refine ⟨And.intro (add_mem hγ.1 (planeCupTwoOne_memP T z s)) fun x F => ?_, ?_⟩
  · rw [differentialThreeRaw_add, Pi.add_apply, hγ.2 x F, planeCupTwoOne_differentialP]
    change _ = T.B (z.val.val ![x 0, x 1, x 2] F)
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F) +
        differentialOneRaw s.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))
    rw [map_add]
  · have key : boundaryValueP T w (y + boundaryMap rationalLevel
          (flagRepresentation (rationalCoefficientComponent n χ) .line) s)
          (γ + planeCupTwoOneP T z s) = boundaryValueP T w y γ -
        differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges)
          (edgePlaneCupP T w s) := by
      funext x e
      have h₁ : z.val.val ![x 0, x 1, x 2] (endpoint .plane e) =
          w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e :=
        hw ![x 0, x 1, x 2] e
      change T.B (w.val ![x 0, x 1] e)
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e)) +
            (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e)) -
              s.val ![T.φ (x 1), T.φ (x 3)] (T.dualFlag (endpoint .plane e)) +
              s.val ![T.φ (x 1), T.φ (x 2)] (T.dualFlag (endpoint .plane e)))) -
          (γ x (endpoint .plane e) + T.B (z.val.val ![x 0, x 1, x 2] (endpoint .plane e))
            (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e)))) =
        (T.B (w.val ![x 0, x 1] e)
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e))) -
            γ x (endpoint .plane e)) -
        (T.B (w.val ![x 1, x 2] e) (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e))) -
          T.B (w.val ![x 0, x 2] e)
            (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e))) +
          T.B (w.val ![x 0, x 1] e)
            (s.val ![T.φ (x 1), T.φ (x 3)] (T.dualFlag (endpoint .plane e))) -
          T.B (w.val ![x 0, x 1] e)
            (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualFlag (endpoint .plane e))))
      rw [h₁]
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
      abel
    rw [key, map_sub, hτ.1, sub_zero]

end Steps

/-- **Independence of representatives.** The trace of the boundary cup product depends only on the
classes of the plane and line cocycles, provided the edge pullback of the line cocycle is exact. -/
theorem trace_eqP {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ} (hτ : IsBoundaryTrace τ)
    {z z' : MaximalCycles n χ .plane} {w w' : EdgeCochains n χ 1}
    {y y' : MaximalCycles n χ .line} {γ γ' : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hw : EdgePrimitiveP z w) (hγ : VertexPrimitiveP T z y γ)
    (hw' : EdgePrimitiveP z' w') (hγ' : VertexPrimitiveP T z' y' γ')
    (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) z =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) z')
    (hy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) y =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) y')
    (flat : LineEdgeExactP y') :
    τ (boundaryValueP T w y γ) = τ (boundaryValueP T w' y' γ') := by
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp hz.symm)
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp hy.symm)
  obtain rfl : z' = z + boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) .plane) u := by
    rw [hu]; abel
  obtain rfl : y' = y + boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) .line) s := by
    rw [hs]; abel
  obtain ⟨hγ₁, step₁⟩ := line_coboundaryP T hτ hw hγ s
  obtain ⟨hw₂, hγ₂, step₂⟩ := plane_coboundaryP T hw hγ₁ u
  rw [← step₁, ← step₂, trace_edge_eqP T hτ hw₂ hw' flat, trace_vertex_eqP T hτ w' hγ₂ hγ']


/-- The concrete duality data: the involution `g ↦ a (g⁻¹)ᵀ a⁻¹`, its flag maps, and the apolar
pairing. -/
def dualityDataP (n : ℕ) (χ : RankOneCharacter) : DualityDataP n χ where
  φ := dualInvolution
  level := fun _ h => dualInvolution_mem_rationalLevel h
  B := dualPairing n
  invariant := fun g _ v w => dualPairing_invariant n χ g v w
  dualFlag := TernaryPeriodPolynomials.Duality.dualPlaneFlag
  dualFlag_smul := TernaryPeriodPolynomials.Duality.dualPlaneFlag_smul
  dualEdge := TernaryPeriodPolynomials.Duality.dualEdge
  dualEdge_smul := TernaryPeriodPolynomials.Duality.dualEdge_smul
  endpoint_dualEdge := TernaryPeriodPolynomials.Duality.endpoint_line_dualEdge

section ChainValueSec

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  (Θ : TraceData ι L P) {n : ℕ} {χ : RankOneCharacter} (T : DualityDataP n χ)

/-- The chain value of a plane cocycle `z` with edge primitive `w` and a line cocycle `y`:
`Σ_e ⟨(w ⌣ y^φ)(·)(ē), C_e⟩ - Σ_v ⟨(z ⌣ y^φ)(·)(v̄), D_v⟩`. -/
def chainValueP (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1)
    (y : MaximalCycles n χ .line) : ℂ :=
  (∑ i, Finsupp.linearCombination ℂ (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
      (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane (Θ.edge i)))))
      (Θ.chain i)) -
    ∑ v, Finsupp.linearCombination ℂ (fun x => T.B (z.val.val ![x 0, x 1, x 2] (Θ.planeRep v))
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.planeRep v)))) (Θ.planeFill v)

/-- **The trace without the vertex primitive.** -/
theorem trace_eq_chainValueP {z : MaximalCycles n χ .plane} {w : EdgeCochains n χ 1}
    {y : MaximalCycles n χ .line} {γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hγ : VertexPrimitiveP T z y γ) :
    Θ.trace (boundaryValueP T w y γ) = chainValueP Θ T z w y := by
  rw [TraceData.trace_apply]
  have split : ∀ i, Finsupp.linearCombination ℂ (fun x => boundaryValueP T w y γ x (Θ.edge i))
      (Θ.chain i) = Finsupp.linearCombination ℂ (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane (Θ.edge i)))))
        (Θ.chain i) -
      Finsupp.linearCombination ℂ (fun x => γ x (Θ.planeRep (Θ.planeOf i))) (Θ.chain i) := by
    intro i
    rw [← Θ.plane_endpoint i]
    simp only [Finsupp.linearCombination_apply, boundaryValueP, smul_sub, Finsupp.sum_sub]
  rw [Finset.sum_congr rfl fun i _ => split i, Finset.sum_sub_distrib,
    sum_eval_regroup Θ.planeRep Θ.planeOf Θ.chain Θ.planeFill Θ.plane_filled γ hγ.1]
  show _ - _ = _ - _
  congr 1
  exact Finset.sum_congr rfl fun v _ =>
    congrArg (fun f => Finsupp.linearCombination ℂ f (Θ.planeFill v))
      (funext fun x => hγ.2 x (Θ.planeRep v))

end ChainValueSec

section ChainLocalSec

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  (Θ : TraceData ι L P) {n : ℕ} {χ : RankOneCharacter} (T : DualityDataP n χ)

/-- The local value at the representative plane `v̄`: the edge terms of the complete flags above
`v̄` minus the filling term at `v̄`. -/
def planeValueP (v : P) (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1)
    (y : MaximalCycles n χ .line) : ℂ :=
  (∑ i ∈ Finset.univ.filter (fun i => Θ.planeOf i = v),
      Finsupp.linearCombination ℂ (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (Θ.planeRep v)))) (Θ.chain i)) -
    Finsupp.linearCombination ℂ (fun x => T.B (z.val.val ![x 0, x 1, x 2] (Θ.planeRep v))
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.planeRep v)))) (Θ.planeFill v)

/-- **Localization.** The chain value is the sum of the local values at the representative
planes. -/
theorem chainValue_eq_sumP (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1)
    (y : MaximalCycles n χ .line) :
    chainValueP Θ T z w y = ∑ v, planeValueP Θ T v z w y := by
  unfold chainValueP planeValueP
  rw [Finset.sum_sub_distrib, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ) (g := Θ.planeOf) (fun i _ => Finset.mem_univ (Θ.planeOf i))]
  congr 1
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i hi => ?_
  rw [Θ.plane_endpoint i, (Finset.mem_filter.mp hi).2]


end ChainLocalSec

section PlaneCup

variable {n : ℕ} {χ : RankOneCharacter} (T : DualityDataP n χ)

/-- The twisted cup product `z ⌣ y^φ` of a plane and a line two-cocycle, a scalar four-cochain on
planes. -/
def planeCupP (z : MaximalCycles n χ .plane) (y : MaximalCycles n χ .line) :
    (Fin 5 → RationalGL3) → Flags .plane → ℂ :=
  fun x F => T.B (z.val.val ![x 0, x 1, x 2] F)
    (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))

theorem planeCup_memP (z : MaximalCycles n χ .plane) (y : MaximalCycles n χ .line) :
    planeCupP T z y ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 4 := by
  intro g x
  funext F
  have dual : T.φ g.val ∈ rationalLevel := T.level g.val g.property
  change T.B (z.val.val ![g.val * x 0, g.val * x 1, g.val * x 2] F)
      (y.val.val ![T.φ (g.val * x 2), T.φ (g.val * x 3), T.φ (g.val * x 4)] (T.dualFlag F)) =
    T.B (z.val.val ![x 0, x 1, x 2] (g.val⁻¹ • F))
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (g.val⁻¹ • F)))
  rw [congrFun (cochain_triple z.val g (x 0) (x 1) (x 2)) F, map_mul, map_mul, map_mul,
    cochain_triple y.val ⟨T.φ g.val, dual⟩]
  change T.B (rationalCoefficientComponent n χ g.val (z.val.val ![x 0, x 1, x 2] (g.val⁻¹ • F)))
      (rationalCoefficientComponent n χ (T.φ g.val)
        (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] ((T.φ g.val)⁻¹ • T.dualFlag F))) = _
  rw [T.invariant g.val g.property, ← map_inv T.φ g.val, ← T.dualFlag_smul]

theorem planeCup_closedP (z : MaximalCycles n χ .plane) (y : MaximalCycles n χ .line)
    (x : Fin 6 → RationalGL3) : differentialFourRaw (planeCupP T z y) x = 0 := by
  funext F
  have hz : IsCocycleTwo (fun x' => z.val.val x' F) := fun x' =>
    congrFun (isCocycleTwo_of_mem z x') F
  have hy : IsCocycleTwo (fun x' => y.val.val x' (T.dualFlag F)) := fun x' =>
    congrFun (isCocycleTwo_of_mem y x') (T.dualFlag F)
  exact differentialFourRaw_cupTwoTwo T.B T.φ hz hy x

/-- **Vertex primitives from the plane stabilizers.** If `H⁴` of the stabilizer of every plane flag
vanishes, every twisted cup product of a plane and a line two-cocycle has an invariant vertex
primitive on planes. -/
theorem planeCupExact_of_topVanishingP
    (stab : ∀ F : Flags .plane, IsTopVanishing (pointStabilizer F))
    (z : MaximalCycles n χ .plane) (y : MaximalCycles n χ .line) :
    ∃ γ, VertexPrimitiveP T z y γ := by
  obtain ⟨θ, hθ, hdθ⟩ := exists_primitive (planeCupP T z y) (planeCup_memP T z y)
    (planeCup_closedP T z y) stab
  exact ⟨θ, hθ, fun x F => congrFun (hdθ x) F⟩

end PlaneCup
/-- Plane vertex primitives exist unconditionally (`H⁴` of every point stabilizer vanishes). -/
theorem planeCupExact_unconditionalP {n : ℕ} {χ : RankOneCharacter} (T : DualityDataP n χ)
    (z : MaximalCycles n χ .plane) (y : MaximalCycles n χ .line) :
    ∃ γ, VertexPrimitiveP T z y γ :=
  planeCupExact_of_topVanishingP T (fun F => topVanishing_pointStabilizer_unconditional F) z y

end TernaryPeriodPolynomials.Argument.FacePairingFull.Plane
