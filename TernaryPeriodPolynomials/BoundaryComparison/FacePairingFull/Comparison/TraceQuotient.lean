module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Trace
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Isotropy

@[expose] public section


/-!
# S1: closed edge three-cochains modulo boundary-exact ones, and the trace on them

For a subgroup `Γ ≤ GL₃(ℚ)` the invariant closed scalar three-cochains on complete flags are
`closedEdgeCochains Γ`.  A value is *boundary exact at `Γ`* (`BoundaryExactAt Γ`) when it is an
invariant coboundary of an edge two-cochain plus the pullback of a closed plane three-cochain minus the
pullback of a closed line three-cochain: this is `Duality.BoundaryExact` for an arbitrary group
instead of `rationalLevel` (`boundaryExactAt_level_iff`).  The quotient of `closedEdgeCochains Γ` by the
exact ones is the space `Q_Γ` of the whole-boundary trace comparison.  The boundary trace
`traceDataL2.trace` restricts to the level-invariant closed cochains as `levelTrace` and kills the exact
ones (`levelTrace_eq_zero_of_boundaryExactAt`), i.e. it is a linear functional on `Q_{rationalLevel}`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
  (differentialThreeRaw_add differentialThreeRaw_sub)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2 isBoundaryTrace_traceDataL2)

/-- Invariant closed scalar three-cochains on complete flags, for the group `Γ`. -/
def closedEdgeCochains (Γ : Subgroup RationalGL3) :
    Submodule ℂ ((Fin 4 → RationalGL3) → Edges → ℂ) where
  carrier := {f | f ∈ cochains Γ (functionRepresentation scalarTrivial Edges) 3 ∧
    ∀ x, differentialThreeRaw f x = 0}
  zero_mem' := ⟨Submodule.zero_mem _, fun x => by simp [differentialThreeRaw]⟩
  add_mem' := fun {f g} hf hg => ⟨Submodule.add_mem _ hf.1 hg.1, fun x => by
    rw [differentialThreeRaw_add, hf.2 x, hg.2 x, add_zero]⟩
  smul_mem' := fun a f hf => ⟨Submodule.smul_mem _ a hf.1, fun x => by
    simp only [differentialThreeRaw, Pi.smul_apply, ← smul_sub, ← smul_add]
    have := hf.2 x
    simp only [differentialThreeRaw] at this
    rw [this, smul_zero]⟩

/-- A scalar three-cochain on complete flags is *boundary exact at `Γ`*: an invariant coboundary of an
edge two-cochain plus the pullback of a closed plane three-cochain minus the pullback of a closed
line three-cochain. -/
def BoundaryExactAt (Γ : Subgroup RationalGL3) (value : (Fin 4 → RationalGL3) → Edges → ℂ) : Prop :=
  ∃ (edge : cochains Γ (functionRepresentation scalarTrivial Edges) 2)
    (plane : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
    (line : (Fin 4 → RationalGL3) → Flags .line → ℂ),
    plane ∈ cochains Γ (functionRepresentation scalarTrivial (Flags .plane)) 3 ∧
    line ∈ cochains Γ (functionRepresentation scalarTrivial (Flags .line)) 3 ∧
    (∀ x, differentialThreeRaw plane x = 0) ∧ (∀ x, differentialThreeRaw line x = 0) ∧
    ∀ x e, value x e = differentialTwo Γ (functionRepresentation scalarTrivial Edges) edge x e +
      plane x (endpoint .plane e) - line x (endpoint .line e)

theorem boundaryExactAt_level_iff (value : (Fin 4 → RationalGL3) → Edges → ℂ) :
    BoundaryExactAt rationalLevel value ↔ BoundaryExact value := Iff.rfl

/-- The boundary trace of the level on the level-invariant closed edge three-cochains. -/
def levelTrace : closedEdgeCochains rationalLevel →ₗ[ℂ] ℂ where
  toFun f := traceDataL2.trace f.val
  map_add' f g := map_add traceDataL2.trace.toAddMonoidHom f.val g.val
  map_smul' a f := by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact traceDataL2.trace.map_smul a f.val

theorem levelTrace_apply (f : closedEdgeCochains rationalLevel) :
    levelTrace f = traceDataL2.trace f.val := rfl

/-- The level boundary trace kills boundary-exact closed cochains: it descends to `Q`. -/
theorem levelTrace_eq_zero_of_boundaryExactAt {f : closedEdgeCochains rationalLevel}
    (h : BoundaryExactAt rationalLevel f.val) : levelTrace f = 0 := by
  obtain ⟨edge, plane, line, hplane, hline, pc, lc, eq⟩ := h
  have hvalue : f.val = differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges) edge +
      (fun x e => plane x (endpoint .plane e)) - (fun x e => line x (endpoint .line e)) := by
    funext x e
    exact eq x e
  have hτ := isBoundaryTrace_traceDataL2
  rw [levelTrace_apply, hvalue]
  have e1 : traceDataL2.trace.toAddMonoidHom (differentialTwo rationalLevel
      (functionRepresentation scalarTrivial Edges) edge) = 0 := hτ.1 edge
  have e2 := hτ.2.1 plane hplane pc
  have e3 := hτ.2.2 line hline lc
  change traceDataL2.trace.toAddMonoidHom _ = 0
  rw [map_sub, map_add, e1, e2, e3]
  simp

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
