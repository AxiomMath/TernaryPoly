module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.PairingSymm
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.EdgeInvolution
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.InnerReversal
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Plane.Pairing

@[expose] public section


/-!
# The swap relation between the plane and line face pairings

For an inner plane class `A` and an inner line class `B`,
`facePairing n (revInner B) (revInner A) = a * facePairingP n A B` with `a = 1` or `a = -1`; since
`revInner = -1` (`revInner_eq_neg`) this is the swap relation `⟨B, A⟩_Q = a ⟨A, B⟩_P`
(`facePairing_swap`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace
  (traceDataL2 isBoundaryTrace_traceDataL2)
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Swap

variable {n : ℕ}

/-- The edge two-cochain `(x₀, x₁, x₂; e) ↦ ⟨w(φx₂, φx₁; ē*), s(x₁, x₀; e)⟩` whose coboundary is the
difference of the boundary values. -/
def swapEdgeCochain (w s : EdgeCochains n trivialCharacter 1) :
    cochains rationalLevel (functionRepresentation scalarTrivial Edges) 2 :=
  ⟨fun x e => dualPairing n (w.val ![dualInvolution (x 2), dualInvolution (x 1)] (dualEdge e))
      (s.val ![x 1, x 0] e), by
    intro g x
    funext e
    have dual : dualInvolution g.val ∈ rationalLevel := dualInvolution_mem_rationalLevel g.property
    change dualPairing n (w.val ![dualInvolution (g.val * x 2), dualInvolution (g.val * x 1)]
          (dualEdge e)) (s.val ![g.val * x 1, g.val * x 0] e) =
      dualPairing n (w.val ![dualInvolution (x 2), dualInvolution (x 1)]
          (dualEdge (g.val⁻¹ • e))) (s.val ![x 1, x 0] (g.val⁻¹ • e))
    rw [map_mul, map_mul, congrFun (cochain_pair w ⟨dualInvolution g.val, dual⟩
      (dualInvolution (x 2)) (dualInvolution (x 1))) (dualEdge e),
      congrFun (cochain_pair s g (x 1) (x 0)) e]
    change dualPairing n (rationalCoefficientComponent n trivialCharacter (dualInvolution g.val)
        (w.val ![dualInvolution (x 2), dualInvolution (x 1)]
          ((dualInvolution g.val)⁻¹ • dualEdge e)))
        (rationalCoefficientComponent n trivialCharacter g.val
          (s.val ![x 1, x 0] (g.val⁻¹ • e))) = _
    have := dualPairing_invariant n trivialCharacter (dualInvolution g.val)
      (w.val ![dualInvolution (x 2), dualInvolution (x 1)] ((dualInvolution g.val)⁻¹ • dualEdge e))
      (s.val ![x 1, x 0] (g.val⁻¹ • e))
    rw [dualInvolution_involutive] at this
    rw [this, ← map_inv dualInvolution g.val, ← dualEdge_smul]⟩

theorem redge_boundaryValueP {z : MaximalCycles n trivialCharacter .plane}
    {w s : EdgeCochains n trivialCharacter 1} {y : MaximalCycles n trivialCharacter .line}
    {γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hw : EdgePrimitiveP z w)
    (hs : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e) :
    Redge (boundaryValueP (dualityDataP n trivialCharacter) w y γ) =
      boundaryValue (dualityData n trivialCharacter) (rev1 _ _ s) (revCocycle _ _ z)
        (transport3 dualFlag γ) +
      differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges)
        (swapEdgeCochain w s) := by
  funext x e
  have h1 := hs ![x 2, x 1, x 0] e
  have h2 := hw ![dualInvolution (x 3), dualInvolution (x 2), dualInvolution (x 1)] (dualEdge e)
  rw [endpoint_plane_dualEdge] at h2
  change dualPairing n (w.val ![dualInvolution (x 3), dualInvolution (x 2)] (dualEdge e))
      (y.val.val ![dualInvolution (dualInvolution (x 2)), dualInvolution (dualInvolution (x 1)),
        dualInvolution (dualInvolution (x 0))]
        (dualPlaneFlag (endpoint .plane (dualEdge e)))) -
      γ ![dualInvolution (x 3), dualInvolution (x 2), dualInvolution (x 1), dualInvolution (x 0)]
        (endpoint .plane (dualEdge e)) = _
  rw [endpoint_plane_dualEdge, Dual.dualPlaneFlag_dualFlag]
  simp only [Pi.add_apply, Pi.sub_apply, boundaryValue, differentialTwo, LinearMap.coe_mk, AddHom.coe_mk,
    swapEdgeCochain, rev1_apply, revCocycle_val, rev2_apply, transport3]
  simp only [dualInvolution_involutive]
  simp only [dualityData]
  simp only [differentialOneRaw] at h1 h2 ⊢
  simp at h1 h2 ⊢
  rw [h1, h2]
  simp only [map_add, map_sub]
  rw [dualPairing_comm n (s.val ![x 1, x 0] e) (w.val ![dualInvolution (x 2), dualInvolution (x 1)]
      (dualEdge e)),
    dualPairing_comm n (s.val ![x 1, x 0] e) (w.val ![dualInvolution (x 3), dualInvolution (x 1)]
      (dualEdge e)),
    dualPairing_comm n (s.val ![x 1, x 0] e) (w.val ![dualInvolution (x 3), dualInvolution (x 2)]
      (dualEdge e))]
  ring

theorem edgePrimitive_rev
    {s : EdgeCochains n trivialCharacter 1} {y : MaximalCycles n trivialCharacter .line}
    (hs : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e) :
    EdgePrimitive (revCocycle _ _ y) (rev1 _ _ s) := by
  intro x e
  have h1 := hs ![x 2, x 1, x 0] e
  simp only [differentialOneRaw] at h1 ⊢
  simp at h1 ⊢
  rw [h1]
  abel

theorem vertexPrimitive_rev {z : MaximalCycles n trivialCharacter .plane}
    {y : MaximalCycles n trivialCharacter .line}
    {γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hγ : VertexPrimitiveP (dualityDataP n trivialCharacter) z y γ) :
    VertexPrimitive (dualityData n trivialCharacter) (revCocycle _ _ y) (revCocycle _ _ z)
      (transport3 dualFlag γ) := by
  refine ⟨transport3_mem dualFlag dualFlag_smul hγ.1, fun x F => ?_⟩
  rw [differentialThreeRaw_transport3]
  have h := hγ.2 ![dualInvolution (x 4), dualInvolution (x 3), dualInvolution (x 2),
    dualInvolution (x 1), dualInvolution (x 0)] (dualFlag F)
  change _ = dualPairing n (y.val.val ![x 2, x 1, x 0] F)
    (z.val.val ![dualInvolution (x 4), dualInvolution (x 3), dualInvolution (x 2)] (dualFlag F))
  change _ = dualPairing n (z.val.val ![dualInvolution (x 4), dualInvolution (x 3),
      dualInvolution (x 2)] (dualFlag F))
    (y.val.val ![dualInvolution (dualInvolution (x 2)), dualInvolution (dualInvolution (x 1)),
      dualInvolution (dualInvolution (x 0))] (dualPlaneFlag (dualFlag F))) at h
  simp only [dualInvolution_involutive, Dual.dualPlaneFlag_dualFlag] at h
  rw [h, dualPairing_comm]

section Closed

variable {χ : RankOneCharacter} (T : DualityDataP n χ)

theorem edgeCupOneTwoP_mem (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .line) :
    (fun (x : Fin 4 → RationalGL3) (e : Edges) =>
        T.B (w.val ![x 0, x 1] e)
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e)))) ∈
      cochains rationalLevel (functionRepresentation scalarTrivial Edges) 3 := by
  intro g x
  funext e
  have dual : T.φ g.val ∈ rationalLevel := T.level g.val g.property
  change T.B (w.val ![g.val * x 0, g.val * x 1] e)
      (y.val.val ![T.φ (g.val * x 1), T.φ (g.val * x 2), T.φ (g.val * x 3)]
        (T.dualFlag (endpoint .plane e))) =
    T.B (w.val ![x 0, x 1] (g.val⁻¹ • e))
      (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane (g.val⁻¹ • e))))
  rw [congrFun (cochain_pair w g (x 0) (x 1)) e, map_mul, map_mul, map_mul,
    cochain_triple y.val ⟨T.φ g.val, dual⟩]
  change T.B (rationalCoefficientComponent n χ g.val (w.val ![x 0, x 1] (g.val⁻¹ • e)))
      (rationalCoefficientComponent n χ (T.φ g.val)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)]
          ((T.φ g.val)⁻¹ • T.dualFlag (endpoint .plane e)))) = _
  rw [T.invariant g.val g.property, ← map_inv T.φ g.val, ← T.dualFlag_smul, ← endpoint_smul]

/-- The boundary cup product of the plane pairing is an invariant closed three-cochain on complete
flags. -/
theorem boundaryValueP_mem_closed {z : MaximalCycles n χ .plane} {w : EdgeCochains n χ 1}
    {y : MaximalCycles n χ .line} {γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hw : EdgePrimitiveP z w) (hγ : VertexPrimitiveP T z y γ) :
    boundaryValueP T w y γ ∈ closedEdgeCochains rationalLevel := by
  refine ⟨?_, fun x => ?_⟩
  · have hγm : (fun x (e : Edges) => γ x (endpoint .plane e)) ∈
        cochains rationalLevel (functionRepresentation scalarTrivial Edges) 3 := by
      intro g x
      funext e
      have := congrFun (hγ.1 g x) (endpoint .plane e)
      change γ (fun i => g.val * x i) (endpoint .plane e) =
        scalarTrivial g.val (γ x (endpoint .plane (g.val⁻¹ • e)))
      rw [endpoint_smul]
      exact this
    exact sub_mem (edgeCupOneTwoP_mem T w y) hγm
  · funext e
    have cocycle : IsCocycleTwo (fun x' => y.val.val x' (T.dualFlag (endpoint .plane e))) :=
      fun x' => congrFun (isCocycleTwo_of_mem y x') (T.dualFlag (endpoint .plane e))
    have leibniz := differentialThreeRaw_cupOneTwo T.B T.φ (fun x' => w.val x' e) cocycle x
    have hprim : differentialOneRaw (fun x' => w.val x' e) ![x 0, x 1, x 2] =
        z.val.val ![x 0, x 1, x 2] (endpoint .plane e) := by
      have := hw ![x 0, x 1, x 2] e
      exact this.symm
    have hdγ := hγ.2 x (endpoint .plane e)
    have split : differentialThreeRaw (boundaryValueP T w y γ) x e =
        differentialThreeRaw (cupOneTwo T.B T.φ (fun x' => w.val x' e)
          (fun x' => y.val.val x' (T.dualFlag (endpoint .plane e)))) x -
        differentialThreeRaw γ x (endpoint .plane e) := by
      simp only [differentialThreeRaw, boundaryValueP, cupOneTwo, Pi.sub_apply, Pi.add_apply]
      abel
    rw [split, leibniz]
    simp only [cupTwoTwo]
    rw [hprim, hdγ, sub_self]
    rfl

end Closed

/-- The swap relation on representatives: the line pairing of the reversed representatives is `a`
times the plane pairing. -/
theorem traceValue_rev_eq {a : ℂ}
    (ha : ∀ f : closedEdgeCochains rationalLevel, levelTrace (Rclosed f) = a * levelTrace f)
    {z : MaximalCycles n trivialCharacter .plane} {w s : EdgeCochains n trivialCharacter 1}
    {y : MaximalCycles n trivialCharacter .line} {γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ}
    (hw : EdgePrimitiveP z w)
    (hs : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e)
    (hγ : VertexPrimitiveP (dualityDataP n trivialCharacter) z y γ) :
    traceValue (revCocycle _ _ y) (rev1 _ _ s) (revCocycle _ _ z) = a * traceValueP z w y := by
  rw [← trace_boundaryValue_eq_traceValue (vertexPrimitive_rev hγ),
    ← trace_boundaryValue_eq_traceValueP hγ]
  have key : boundaryValue (dualityData n trivialCharacter) (rev1 _ _ s) (revCocycle _ _ z)
      (transport3 dualFlag γ) =
      Redge (boundaryValueP (dualityDataP n trivialCharacter) w y γ) -
        differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges)
          (swapEdgeCochain w s) := by
    rw [redge_boundaryValueP hw hs]
    abel
  have h0 : traceDataL2.trace (differentialTwo rationalLevel
      (functionRepresentation scalarTrivial Edges) (swapEdgeCochain w s)) = 0 :=
    isBoundaryTrace_traceDataL2.1 (swapEdgeCochain w s)
  have hR := ha ⟨boundaryValueP (dualityDataP n trivialCharacter) w y γ,
    boundaryValueP_mem_closed _ hw hγ⟩
  rw [key, map_sub, h0, sub_zero]
  exact hR

theorem exists_reps_plane (A : innerClasses n .plane) :
    ∃ (z : MaximalCycles n trivialCharacter .plane) (w : EdgeCochains n trivialCharacter 1),
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z = A.val ∧
      EdgePrimitiveP z w := by
  have hA : InnerBoundary n trivialCharacter .plane A.val := A.property
  obtain ⟨z, hz, w, hw'⟩ := hA
  exact ⟨z, w, hz, fun x e => hw' x e⟩

theorem exists_reps_line (B : innerClasses n .line) :
    ∃ (y : MaximalCycles n trivialCharacter .line) (s : EdgeCochains n trivialCharacter 1),
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y = B.val ∧
      ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e := by
  have hB : InnerBoundary n trivialCharacter .line B.val := B.property
  obtain ⟨y, hy, s, hs⟩ := hB
  exact ⟨y, s, hy, fun x e => hs x e⟩

theorem classOf_rev_line (y : MaximalCycles n trivialCharacter .line)
    (B : innerClasses n .line)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y = B.val) :
    classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
      (revCocycle _ _ y) = (revInner n .line B).val := by
  rw [revInner_val, ← hy]
  exact (revH2_classOf _ _ y).symm

theorem classOf_rev_plane (z : MaximalCycles n trivialCharacter .plane)
    (A : innerClasses n .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z = A.val) :
    classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
      (revCocycle _ _ z) = (revInner n .plane A).val := by
  rw [revInner_val, ← hz]
  exact (revH2_classOf _ _ z).symm

theorem facePairing_rev_eq_of_reps {a : ℂ}
    (ha : ∀ f : closedEdgeCochains rationalLevel, levelTrace (Rclosed f) = a * levelTrace f)
    (A : innerClasses n .plane) (B : innerClasses n .line)
    {z : MaximalCycles n trivialCharacter .plane} {w s : EdgeCochains n trivialCharacter 1}
    {y : MaximalCycles n trivialCharacter .line}
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z = A.val)
    (hw : EdgePrimitiveP z w)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y = B.val)
    (hs' : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e) :
    facePairing n (revInner n .line B) (revInner n .plane A) = a * facePairingP n A B := by
  have e1 : facePairingP n A B = traceValueP z w y := facePairing_apply_eqP hz hw hy
  have e2 : facePairing n (revInner n .line B) (revInner n .plane A) =
      traceValue (revCocycle _ _ y) (rev1 _ _ s) (revCocycle _ _ z) :=
    facePairing_apply_eq (classOf_rev_line y B hy) (edgePrimitive_rev hs') (classOf_rev_plane z A hz)
  exact e2.trans ((planeCupExact_unconditionalP (dualityDataP n trivialCharacter) z y).elim
    fun _ hγ => (traceValue_rev_eq ha hw hs' hγ).trans (congrArg (fun t => a * t) e1.symm))

/-- **The swap relation on inner classes.** -/
theorem facePairing_rev_eq {a : ℂ}
    (ha : ∀ f : closedEdgeCochains rationalLevel, levelTrace (Rclosed f) = a * levelTrace f)
    (A : innerClasses n .plane) (B : innerClasses n .line) :
    facePairing n (revInner n .line B) (revInner n .plane A) = a * facePairingP n A B :=
  (exists_reps_plane A).elim fun _ h1 => h1.elim fun _ h2 =>
    (exists_reps_line B).elim fun _ h3 => h3.elim fun _ h4 =>
      facePairing_rev_eq_of_reps ha A B h2.1 h2.2 h4.1 h4.2

/-- **The swap relation `⟨B, A⟩_Q = a ⟨A, B⟩_P`** on inner classes, with `a = 1` or `a = -1`. -/
theorem facePairing_swap {a : ℂ}
    (ha : ∀ f : closedEdgeCochains rationalLevel, levelTrace (Rclosed f) = a * levelTrace f)
    (A : innerClasses n .plane) (B : innerClasses n .line) :
    facePairing n B A = a * facePairingP n A B := by
  have e1 : facePairing n (revInner n .line B) (revInner n .plane A) = facePairing n B A :=
    (congrArg₂ (fun u v => facePairing n u v) (revInner_eq_neg n .line B)
      (revInner_eq_neg n .plane A)).trans (by simp)
  exact e1.symm.trans (facePairing_rev_eq ha A B)

/-- **The swap relation, uniformly in `n`:** there is a sign `a = ±1` with `⟨B, A⟩_Q = a ⟨A, B⟩_P` for
every `n` and every pair of inner classes. -/
theorem exists_swap_relation :
    ∃ a : ℂ, (a = 1 ∨ a = -1) ∧ ∀ (n : ℕ) (A : innerClasses n .plane) (B : innerClasses n .line),
      facePairing n B A = a * facePairingP n A B :=
  exists_trace_transport.elim fun a h =>
    ⟨a, h.1, fun n A B => facePairing_swap (n := n) h.2 A B⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
