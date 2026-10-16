module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceEvaluation
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceNonvanishing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Flags

@[expose] public section


/-!
# The reversal-and-dualization involution on closed edge three-cochains

`transport3 ψ f (x) (y) = f (φ x₃, φ x₂, φ x₁, φ x₀) (ψ y)` for `φ = dualInvolution` and an
equivariant map `ψ` of flag varieties. For `ψ = dualEdge` it is an involution of the invariant closed
scalar three-cochains on complete flags (`Rclosed`) that preserves boundary-exact cochains
(`boundaryExactAt_transport`). By the uniqueness of boundary traces
(`Comparison.boundaryTrace_unique`) `levelTrace ∘ Rclosed` is a multiple of `levelTrace`, and the
multiple `a` is nonzero because `Rclosed` is an involution and `levelTrace` is nonzero
(`exists_trace_transport`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Swap

/-- Reverse the four vertices, apply `φ = dualInvolution`, and evaluate at `ψ y`. -/
def transport3 {X Y : Type} (ψ : Y → X) (f : (Fin 4 → RationalGL3) → X → ℂ) :
    (Fin 4 → RationalGL3) → Y → ℂ :=
  fun x y => f ![dualInvolution (x 3), dualInvolution (x 2), dualInvolution (x 1),
    dualInvolution (x 0)] (ψ y)

/-- The same for a three-vertex cochain. -/
def transport2 {X Y : Type} (ψ : Y → X) (f : (Fin 3 → RationalGL3) → X → ℂ) :
    (Fin 3 → RationalGL3) → Y → ℂ :=
  fun x y => f ![dualInvolution (x 2), dualInvolution (x 1), dualInvolution (x 0)] (ψ y)

theorem transport3_mem {X Y : Type} [MulAction RationalGL3 X] [MulAction RationalGL3 Y]
    (ψ : Y → X) (hψ : ∀ g y, ψ (g • y) = dualInvolution g • ψ y)
    {f : (Fin 4 → RationalGL3) → X → ℂ}
    (hf : f ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) 3) :
    transport3 ψ f ∈ cochains rationalLevel (functionRepresentation scalarTrivial Y) 3 := by
  intro g x
  funext y
  have dual : dualInvolution g.val ∈ rationalLevel := dualInvolution_mem_rationalLevel g.property
  have ht : (fun i => dualInvolution g.val * ![dualInvolution (x 3), dualInvolution (x 2),
      dualInvolution (x 1), dualInvolution (x 0)] i) =
      ![dualInvolution (g.val * x 3), dualInvolution (g.val * x 2), dualInvolution (g.val * x 1),
        dualInvolution (g.val * x 0)] := by
    funext i
    fin_cases i <;> simp
  have h : f (fun i => dualInvolution g.val * ![dualInvolution (x 3), dualInvolution (x 2),
      dualInvolution (x 1), dualInvolution (x 0)] i) (ψ y) =
      f ![dualInvolution (x 3), dualInvolution (x 2), dualInvolution (x 1),
        dualInvolution (x 0)] ((dualInvolution g.val)⁻¹ • ψ y) :=
    congrFun (hf ⟨dualInvolution g.val, dual⟩ ![dualInvolution (x 3),
      dualInvolution (x 2), dualInvolution (x 1), dualInvolution (x 0)]) (ψ y)
  rw [ht] at h
  change f ![dualInvolution (g.val * x 3), dualInvolution (g.val * x 2),
      dualInvolution (g.val * x 1), dualInvolution (g.val * x 0)] (ψ y) =
    f ![dualInvolution (x 3), dualInvolution (x 2), dualInvolution (x 1),
      dualInvolution (x 0)] (ψ (g.val⁻¹ • y))
  rw [hψ, map_inv]
  simpa only [map_mul] using h

theorem transport2_mem {X Y : Type} [MulAction RationalGL3 X] [MulAction RationalGL3 Y]
    (ψ : Y → X) (hψ : ∀ g y, ψ (g • y) = dualInvolution g • ψ y)
    {f : (Fin 3 → RationalGL3) → X → ℂ}
    (hf : f ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) 2) :
    transport2 ψ f ∈ cochains rationalLevel (functionRepresentation scalarTrivial Y) 2 := by
  intro g x
  funext y
  have dual : dualInvolution g.val ∈ rationalLevel := dualInvolution_mem_rationalLevel g.property
  have ht : (fun i => dualInvolution g.val * ![dualInvolution (x 2), dualInvolution (x 1),
      dualInvolution (x 0)] i) =
      ![dualInvolution (g.val * x 2), dualInvolution (g.val * x 1),
        dualInvolution (g.val * x 0)] := by
    funext i
    fin_cases i <;> simp
  have h : f (fun i => dualInvolution g.val * ![dualInvolution (x 2), dualInvolution (x 1),
      dualInvolution (x 0)] i) (ψ y) =
      f ![dualInvolution (x 2), dualInvolution (x 1), dualInvolution (x 0)]
        ((dualInvolution g.val)⁻¹ • ψ y) :=
    congrFun (hf ⟨dualInvolution g.val, dual⟩ ![dualInvolution (x 2),
      dualInvolution (x 1), dualInvolution (x 0)]) (ψ y)
  rw [ht] at h
  change f ![dualInvolution (g.val * x 2), dualInvolution (g.val * x 1),
      dualInvolution (g.val * x 0)] (ψ y) =
    f ![dualInvolution (x 2), dualInvolution (x 1), dualInvolution (x 0)] (ψ (g.val⁻¹ • y))
  rw [hψ, map_inv]
  simpa only [map_mul] using h

theorem differentialThreeRaw_transport3 {X Y : Type} (ψ : Y → X)
    (f : (Fin 4 → RationalGL3) → X → ℂ) (x : Fin 5 → RationalGL3) (y : Y) :
    differentialThreeRaw (transport3 ψ f) x y =
      differentialThreeRaw f ![dualInvolution (x 4), dualInvolution (x 3), dualInvolution (x 2),
        dualInvolution (x 1), dualInvolution (x 0)] (ψ y) := by
  simp only [differentialThreeRaw, transport3, Pi.sub_apply, Pi.add_apply]
  simp
  abel

theorem transport3_closed {X Y : Type} (ψ : Y → X) {f : (Fin 4 → RationalGL3) → X → ℂ}
    (hf : ∀ x, differentialThreeRaw f x = 0) (x : Fin 5 → RationalGL3) :
    differentialThreeRaw (transport3 ψ f) x = 0 := by
  funext y
  rw [differentialThreeRaw_transport3, hf]
  rfl

theorem transport3_transport3 {X Y : Type} (ψ : Y → X) (ψ' : X → Y) (h : ∀ a, ψ (ψ' a) = a)
    (f : (Fin 4 → RationalGL3) → X → ℂ) : transport3 ψ' (transport3 ψ f) = f := by
  funext x y
  have hx : (![dualInvolution (dualInvolution (x 0)), dualInvolution (dualInvolution (x 1)),
      dualInvolution (dualInvolution (x 2)), dualInvolution (dualInvolution (x 3))] :
        Fin 4 → RationalGL3) = x := by
    funext i
    fin_cases i <;> simp [dualInvolution_involutive]
  change f ![dualInvolution (dualInvolution (x 0)), dualInvolution (dualInvolution (x 1)),
      dualInvolution (dualInvolution (x 2)), dualInvolution (dualInvolution (x 3))] (ψ (ψ' y)) =
    f x y
  rw [hx, h]

/-- The involution `f ↦ transport3 dualEdge f` on scalar three-cochains on complete flags. -/
abbrev Redge (f : (Fin 4 → RationalGL3) → Edges → ℂ) : (Fin 4 → RationalGL3) → Edges → ℂ :=
  transport3 dualEdge f

theorem Redge_Redge (f : (Fin 4 → RationalGL3) → Edges → ℂ) : Redge (Redge f) = f :=
  transport3_transport3 dualEdge dualEdge Dual.dualEdge_dualEdge f

/-- `Redge` preserves the invariant closed scalar three-cochains on complete flags. -/
def Rclosed : closedEdgeCochains rationalLevel →ₗ[ℂ] closedEdgeCochains rationalLevel where
  toFun f := ⟨Redge f.val, transport3_mem dualEdge dualEdge_smul f.property.1,
    transport3_closed dualEdge f.property.2⟩
  map_add' f g := by
    apply Subtype.ext
    funext x e
    rfl
  map_smul' a f := by
    apply Subtype.ext
    funext x e
    rfl

theorem Rclosed_Rclosed (f : closedEdgeCochains rationalLevel) : Rclosed (Rclosed f) = f :=
  Subtype.ext (Redge_Redge f.val)

theorem transport3_differentialTwo
    (g : cochains rationalLevel (functionRepresentation scalarTrivial Edges) 2)
    (x : Fin 4 → RationalGL3) (e : Edges) :
    transport3 dualEdge (differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges) g)
        x e =
      -differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges)
        ⟨transport2 dualEdge g.val, transport2_mem dualEdge dualEdge_smul g.property⟩ x e := by
  simp only [differentialTwo, LinearMap.coe_mk, AddHom.coe_mk, transport3, transport2,
    Pi.sub_apply, Pi.add_apply]
  simp
  abel

theorem differentialThreeRaw_neg {X : Type} (f : (Fin 4 → RationalGL3) → X → ℂ)
    (x : Fin 5 → RationalGL3) : differentialThreeRaw (-f) x = -differentialThreeRaw f x := by
  simp only [differentialThreeRaw, Pi.neg_apply]
  abel

theorem transport3_neg {X Y : Type} (ψ : Y → X) (f : (Fin 4 → RationalGL3) → X → ℂ) :
    transport3 ψ (-f) = -transport3 ψ f := rfl

/-- `Redge` preserves boundary-exact cochains. -/
theorem boundaryExactAt_transport {value : (Fin 4 → RationalGL3) → Edges → ℂ}
    (h : BoundaryExactAt rationalLevel value) : BoundaryExactAt rationalLevel (Redge value) := by
  obtain ⟨edge, plane, line, hpm, hlm, hpc, hlc, heq⟩ := h
  refine ⟨-⟨transport2 dualEdge edge.val, transport2_mem dualEdge dualEdge_smul edge.property⟩,
    -transport3 dualPlaneFlag line, -transport3 dualFlag plane, ?_, ?_, ?_, ?_, ?_⟩
  · exact neg_mem (transport3_mem dualPlaneFlag dualPlaneFlag_smul hlm)
  · exact neg_mem (transport3_mem dualFlag dualFlag_smul hpm)
  · intro x
    have := transport3_closed dualPlaneFlag hlc x
    rw [differentialThreeRaw_neg, this, neg_zero]
  · intro x
    have := transport3_closed dualFlag hpc x
    rw [differentialThreeRaw_neg, this, neg_zero]
  · intro x e
    have h1 := heq ![dualInvolution (x 3), dualInvolution (x 2), dualInvolution (x 1),
      dualInvolution (x 0)] (dualEdge e)
    have h0 := transport3_differentialTwo edge x e
    rw [endpoint_plane_dualEdge, endpoint_line_dualEdge] at h1
    have e1 : Redge value x e = value ![dualInvolution (x 3), dualInvolution (x 2),
      dualInvolution (x 1), dualInvolution (x 0)] (dualEdge e) := rfl
    have e2 : transport3 dualEdge (differentialTwo rationalLevel
        (functionRepresentation scalarTrivial Edges) edge) x e =
        differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges) edge
          ![dualInvolution (x 3), dualInvolution (x 2), dualInvolution (x 1),
      dualInvolution (x 0)] (dualEdge e) := rfl
    rw [e1, h1, ← e2, h0]
    simp only [map_neg, Pi.neg_apply, transport3]
    ring

/-- **The trace is invariant up to a sign under `Rclosed`:** `levelTrace ∘ Rclosed = a • levelTrace` with
`a = 1` or `a = -1` (`Rclosed` is an involution, and `levelTrace` is nonzero). -/
theorem exists_trace_transport :
    ∃ a : ℂ, (a = 1 ∨ a = -1) ∧ ∀ f : closedEdgeCochains rationalLevel,
      levelTrace (Rclosed f) = a * levelTrace f := by
  obtain ⟨a, ha⟩ := boundaryTrace_unique (levelTrace.comp Rclosed) (fun f hf =>
    levelTrace_eq_zero_of_boundaryExactAt (boundaryExactAt_transport hf))
  refine ⟨a, ?_, fun f => ha f⟩
  obtain ⟨f₀, hf₀⟩ := exists_closed_levelTrace_ne_zero
  have h1 : levelTrace (Rclosed (Rclosed f₀)) = a * levelTrace (Rclosed f₀) := ha (Rclosed f₀)
  have h2 : levelTrace (Rclosed f₀) = a * levelTrace f₀ := ha f₀
  rw [Rclosed_Rclosed, h2] at h1
  have h3 : (a * a - 1) * levelTrace f₀ = 0 := by linear_combination -h1
  have h4 : a * a = 1 := by
    have := (mul_eq_zero.mp h3).resolve_right hf₀
    linear_combination this
  exact mul_self_eq_one_iff.mp h4

end TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
