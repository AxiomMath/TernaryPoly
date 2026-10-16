module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Interface

@[expose] public section


/-!
# Boundary duality through a trace on the boundary building

`BoundaryExact` says a scalar three-cochain of complete flags is a coboundary plus the pullbacks of a
plane and a line three-cocycle.  An additive functional on such cochains which kills coboundaries and
both kinds of pullbacks (`IsBoundaryTrace`, the trace `H⁴(∂) → ℂ` read on cochains) detects
non-exactness; `associateDuality_of_trace` reduces `AssociateDuality` to the non-vanishing of one such
functional on the boundary cup product of every nonzero line class with a suitable plane class.  The
construction of the trace (the fundamental classes of the Heisenberg lattices, with the vertex relations
of the Levi modular curves) and the non-vanishing (Levi Poincaré duality) are the inputs.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.TraceReduction

open TernaryPeriodPolynomials.Duality

/-- An additive functional on scalar three-cochains of complete flags vanishing on coboundaries of
edge two-cochains and on pullbacks of plane and line three-cocycles. -/
def IsBoundaryTrace (τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ) : Prop :=
  (∀ edge : cochains rationalLevel (functionRepresentation scalarTrivial Edges) 2,
    τ (differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges) edge) = 0) ∧
  (∀ plane : (Fin 4 → RationalGL3) → Flags .plane → ℂ,
    plane ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3 →
    (∀ x, differentialThreeRaw plane x = 0) →
    τ (fun x e => plane x (endpoint .plane e)) = 0) ∧
  (∀ line : (Fin 4 → RationalGL3) → Flags .line → ℂ,
    line ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 →
    (∀ x, differentialThreeRaw line x = 0) →
    τ (fun x e => line x (endpoint .line e)) = 0)

/-- A trace which does not vanish on a cochain proves it is not exact. -/
theorem not_boundaryExact_of_trace {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ}
    (hτ : IsBoundaryTrace τ) {value : (Fin 4 → RationalGL3) → Edges → ℂ} (h : τ value ≠ 0) :
    ¬ BoundaryExact value := by
  rintro ⟨edge, plane, line, hplane, hline, pcocycle, lcocycle, eq⟩
  apply h
  have hvalue : value = differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges) edge +
      (fun x e => plane x (endpoint .plane e)) - (fun x e => line x (endpoint .line e)) := by
    funext x e
    exact eq x e
  rw [hvalue, map_sub, map_add, hτ.1 edge, hτ.2.1 plane hplane pcocycle,
    hτ.2.2 line hline lcocycle]
  all_goals simp

/-- The trace is nonzero on the boundary cup product of every nonzero line class with some plane class,
for every choice of representatives and primitives. -/
def TraceDetects {n : ℕ} (D : InducingData n) (φ : RationalGL3 → RationalGL3)
    (dualFlag : Flags .line → Flags .plane)
    (B : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ)
    (τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ) : Prop :=
  ∀ b ∈ boundarySummand D .line, b ≠ 0 → ∃ ξ ∈ boundarySummand D .plane,
    ∀ z : MaximalCycles n D.chi .line,
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z =
        b →
    ∀ w : EdgeCochains n D.chi 1,
      (∀ x e, z.val.val x (endpoint .line e) = differentialOneRaw w.val x e) →
    ∀ y : MaximalCycles n D.chi .plane,
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
        y = ξ →
    ∀ γ : (Fin 4 → RationalGL3) → Flags .line → ℂ,
      γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 →
      (∀ x F, differentialThreeRaw γ x F =
        B (z.val.val ![x 0, x 1, x 2] F)
          (y.val.val ![φ (x 2), φ (x 3), φ (x 4)] (dualFlag F))) →
      τ (fun x e =>
        B (w.val ![x 0, x 1] e) (y.val.val ![φ (x 1), φ (x 2), φ (x 3)]
          (dualFlag (endpoint .line e))) - γ x (endpoint .line e)) ≠ 0

/-- **Reduction of boundary duality to a trace.**  If one trace is nonzero on the boundary cup product of
every nonzero line class with some plane class (for every choice of representatives and primitives),
`AssociateDuality` holds. -/
theorem associateDuality_of_trace {n : ℕ} (D : InducingData n) (φ : RationalGL3 → RationalGL3)
    (dualFlag : Flags .line → Flags .plane)
    (B : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ)
    {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ} (hτ : IsBoundaryTrace τ)
    (detects : TraceDetects D φ dualFlag B τ) : AssociateDuality D φ dualFlag B := by
  intro b hb hne
  obtain ⟨ξ, hξ, H⟩ := detects b hb hne
  refine ⟨ξ, hξ, ?_⟩
  intro z hz w hw y hy γ hγ hγd
  exact not_boundaryExact_of_trace hτ (H z hz w hw y hy γ hγ hγd)

/-- The plug-in for the half-dimension interface: a trace detecting the concrete boundary pairing gives
`AssociatePairDuality D`. -/
theorem associatePairDuality_of_trace {n : ℕ} (D : InducingData n)
    {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ} (hτ : IsBoundaryTrace τ)
    (detects : TraceDetects D dualInvolution dualFlag (dualPairing n) τ) :
    AssociatePairDuality D :=
  associateDuality_of_trace D dualInvolution dualFlag (dualPairing n) hτ detects

end TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
