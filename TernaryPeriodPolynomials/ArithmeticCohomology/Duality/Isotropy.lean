module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.HeckeLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.CupProduct

@[expose] public section


/-!
# Isotropy of the global boundary image

Let `φ` be an endomorphism of `GL₃(ℚ)` preserving the arithmetic level and `B` a pairing of the
coefficient system with its `φ`-twist, invariant under the level. For global two-cocycles `ω`, `ω'`
the twisted cup product `ω ⌣ ω'^φ` is an invariant scalar four-cocycle. If every such four-cocycle
is a coboundary (`GlobalTopVanishing`, i.e. `H⁴(Γ, ℂ) = 0`), and the plane restriction of `ω`
vanishes, then the boundary cup product of the line restriction of `ω` with the plane restriction
of `ω'` is exact in the boundary building: on complete flags it is the pullback of a plane
three-cocycle. `AssociateDuality` asserts that this boundary cup product detects every nonzero
class of the line summand; together they show that no global class restricts to `(0, b)` with
`b ≠ 0` in the line summand.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.Duality

open TernaryPeriodPolynomials.GraphPieces

/-- The trivial one-dimensional representation of `GL₃(ℚ)`. -/
abbrev scalarTrivial : Representation ℂ RationalGL3 ℂ := Representation.trivial ℂ RationalGL3 ℂ

/-- Every invariant scalar homogeneous four-cocycle of the level is a coboundary: `H⁴(Γ, ℂ) = 0`. -/
def GlobalTopVanishing : Prop :=
  ∀ f : (Fin 5 → RationalGL3) → ℂ, f ∈ cochains rationalLevel scalarTrivial 4 →
    (∀ x, differentialFourRaw f x = 0) →
    ∃ θ ∈ cochains rationalLevel scalarTrivial 3, ∀ x, differentialThreeRaw θ x = f x

/-- A scalar three-cochain on complete flags is exact in the boundary building: it is a
coboundary plus the pullbacks of a plane and a line three-cocycle. -/
def BoundaryExact (value : (Fin 4 → RationalGL3) → Edges → ℂ) : Prop :=
  ∃ (edge : cochains rationalLevel (functionRepresentation scalarTrivial Edges) 2)
    (plane : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
    (line : (Fin 4 → RationalGL3) → Flags .line → ℂ),
    plane ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3 ∧
    line ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 ∧
    (∀ x, differentialThreeRaw plane x = 0) ∧ (∀ x, differentialThreeRaw line x = 0) ∧
    ∀ x e, value x e = differentialTwo rationalLevel
        (functionRepresentation scalarTrivial Edges) edge x e +
      plane x (endpoint .plane e) - line x (endpoint .line e)

/-- Boundary duality on the associate pair: every nonzero class `b` of the line summand has a
plane summand class `ξ` whose boundary cup product with `b` is not exact in the boundary building,
for every choice of representatives and primitives. The boundary cup product of `b = [z]` (with
edge primitive `z ∘ endpoint = dw`) and `ξ = [y]` (moved to lines by `dualFlag`) is
`w ⌣ y^φ - γ`, where `dγ = z ⌣ y^φ` on lines. -/
def AssociateDuality {n : ℕ} (D : InducingData n) (φ : RationalGL3 → RationalGL3)
    (dualFlag : Flags .line → Flags .plane)
    (B : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ) : Prop :=
  ∀ b ∈ boundarySummand D .line, b ≠ 0 → ∃ ξ ∈ boundarySummand D .plane,
    ∀ z : MaximalCycles n D.chi .line,
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z =
        b →
    ∀ w : EdgeCochains n D.chi 1,
      (∀ x e, z.val.val x (endpoint .line e) = differentialOneRaw w.val x e) →
    ∀ y : MaximalCycles n D.chi .plane,
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y =
        ξ →
    ∀ γ : (Fin 4 → RationalGL3) → Flags .line → ℂ,
      γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 →
      (∀ x F, differentialThreeRaw γ x F =
        B (z.val.val ![x 0, x 1, x 2] F) (y.val.val ![φ (x 2), φ (x 3), φ (x 4)] (dualFlag F))) →
      ¬ BoundaryExact (fun x e =>
        B (w.val ![x 0, x 1] e) (y.val.val ![φ (x 1), φ (x 2), φ (x 3)]
          (dualFlag (endpoint .line e))) - γ x (endpoint .line e))

section Isotropy

variable {n : ℕ} (D : InducingData n)

/-- The restriction of a global class is the pair of classes of its constant restrictions. -/
theorem globalRestriction_classOf
    (c : cocycles rationalLevel (rationalCoefficientComponent n D.chi)) :
    globalRestriction n D.chi (classOf rationalLevel (rationalCoefficientComponent n D.chi) c) =
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
          (restrictionCocycle n D.chi .plane c),
        classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
          (restrictionCocycle n D.chi .line c)) :=
  Helpers.canonicalCoordinates_restriction n D.chi c

omit D in
/-- A degree-two cocycle satisfies the raw cocycle identity. -/
theorem isCocycleTwo_of_mem {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} (c : cocycles rationalLevel ρ) :
    IsCocycleTwo c.val.val := fun x => congrFun c.property x

omit D in
/-- Equivariance of a two-cochain at a displayed triple of vertices. -/
theorem cochain_triple {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} (c : cochains rationalLevel ρ 2) (γ : rationalLevel)
    (a b d : RationalGL3) :
    c.val ![γ.val * a, γ.val * b, γ.val * d] = ρ γ.val (c.val ![a, b, d]) := by
  have vertices : (fun i => γ.val * ![a, b, d] i) = ![γ.val * a, γ.val * b, γ.val * d] := by
    funext i
    fin_cases i <;> rfl
  simpa only [vertices] using c.property γ ![a, b, d]

omit D in
/-- Equivariance of a one-cochain at a displayed pair of vertices. -/
theorem cochain_pair {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} (c : cochains rationalLevel ρ 1) (γ : rationalLevel)
    (a b : RationalGL3) :
    c.val ![γ.val * a, γ.val * b] = ρ γ.val (c.val ![a, b]) := by
  have vertices : (fun i => γ.val * ![a, b] i) = ![γ.val * a, γ.val * b] := by
    funext i
    fin_cases i <;> rfl
  simpa only [vertices] using c.property γ ![a, b]

variable (φ : RationalGL3 →* RationalGL3) (level : ∀ g ∈ rationalLevel, φ g ∈ rationalLevel)
  (B : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ)
  (invariant : ∀ g ∈ rationalLevel, ∀ v w,
    B (rationalCoefficientComponent n D.chi g v)
      (rationalCoefficientComponent n D.chi (φ g) w) = B v w)

include level invariant in
/-- The twisted cup product of two global two-cocycles is an invariant scalar cochain. -/
theorem cupTwoTwo_mem (c c' : cocycles rationalLevel (rationalCoefficientComponent n D.chi)) :
    cupTwoTwo B φ c.val.val c'.val.val ∈ cochains rationalLevel scalarTrivial 4 := by
  intro γ x
  have dual : φ γ.val ∈ rationalLevel := level γ.val γ.property
  change B (c.val.val ![γ.val * x 0, γ.val * x 1, γ.val * x 2])
      (c'.val.val ![φ (γ.val * x 2), φ (γ.val * x 3), φ (γ.val * x 4)]) =
    B (c.val.val ![x 0, x 1, x 2]) (c'.val.val ![φ (x 2), φ (x 3), φ (x 4)])
  rw [map_mul, map_mul, map_mul, cochain_triple c.val γ,
    cochain_triple c'.val ⟨φ γ.val, dual⟩]
  exact invariant γ.val γ.property _ _

/-- The pullback of a plane one-cochain to complete flags. -/
def planeEdgeCochain (u : MaximalCochains n D.chi .plane 1) : EdgeCochains n D.chi 1 :=
  ⟨fun x e => u.val x (endpoint .plane e), by
    intro γ x
    funext e
    have equivariant := congrFun (u.property γ x) (endpoint .plane e)
    change u.val (fun i => γ.val * x i) (endpoint .plane e) = _
    rw [equivariant]
    change rationalCoefficientComponent n D.chi γ.val
        (u.val x (γ.val⁻¹ • endpoint .plane e)) =
      rationalCoefficientComponent n D.chi γ.val (u.val x (endpoint .plane (γ.val⁻¹ • e)))
    rw [endpoint_smul]⟩

/-- The part of `H⁴(Γ, ℂ) = 0` that is used: the twisted cup product of any two global
two-cocycles is a coboundary of an invariant scalar three-cochain. -/
def CupProductExactness : Prop :=
  ∀ c c' : cocycles rationalLevel (rationalCoefficientComponent n D.chi),
    ∃ θ ∈ cochains rationalLevel scalarTrivial 3,
      ∀ x, differentialThreeRaw θ x = cupTwoTwo B φ c.val.val c'.val.val x

include level invariant in
/-- `H⁴(Γ, ℂ) = 0` gives exactness of all twisted cup products of global two-cocycles. -/
theorem cupProductExactness_of_globalTopVanishing (top : GlobalTopVanishing) :
    CupProductExactness D φ B := fun c c' =>
  top (cupTwoTwo B φ c.val.val c'.val.val) (cupTwoTwo_mem D φ level B invariant c c')
    (differentialFourRaw_cupTwoTwo B φ (isCocycleTwo_of_mem c) (isCocycleTwo_of_mem c'))

include level invariant in
/-- Isotropy: if the plane restriction of the global class `[c]` vanishes, the boundary cup product
of its line restriction with the plane restriction of any global class `[c']` is exact in the
boundary building, for the representatives and primitives coming from the global cocycles. -/
theorem boundaryExact_of_plane_zero (exactness : CupProductExactness D φ B)
    (dualFlag : Flags .line → Flags .plane)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n D.chi))
    (u : MaximalCochains n D.chi .plane 1)
    (primitive : boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) u =
        restrictionCocycle n D.chi .plane c) :
    ∃ γ : (Fin 4 → RationalGL3) → Flags .line → ℂ,
      γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 ∧
      (∀ x F, differentialThreeRaw γ x F =
        B ((restrictionCocycle n D.chi .line c).val.val ![x 0, x 1, x 2] F)
          ((restrictionCocycle n D.chi .plane c').val.val ![φ (x 2), φ (x 3), φ (x 4)]
            (dualFlag F))) ∧
      BoundaryExact (fun x e =>
        B ((planeEdgeCochain D u).val ![x 0, x 1] e)
          ((restrictionCocycle n D.chi .plane c').val.val ![φ (x 1), φ (x 2), φ (x 3)]
            (dualFlag (endpoint .line e))) - γ x (endpoint .line e)) := by
  obtain ⟨θ, θmem, θprimitive⟩ := exactness c c'
  have constantMem (X : Type) [MulAction RationalGL3 X] :
      (fun x (_ : X) => θ x) ∈
        cochains rationalLevel (functionRepresentation scalarTrivial X) 3 := by
    intro γ x
    funext F
    exact θmem γ x
  refine ⟨fun x _ => θ x, constantMem (Flags .line), fun x F => θprimitive x, ?_⟩
  -- The plane three-cocycle `u ⌣ c'^φ - θ`.
  let κ : (Fin 4 → RationalGL3) → Flags .plane → ℂ := fun x P =>
    cupOneTwo B φ (fun x => u.val x P) c'.val.val x - θ x
  have κmem : κ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3 := by
    intro γ x
    funext P
    have dual : φ γ.val ∈ rationalLevel := level γ.val γ.property
    have pair := congrFun (cochain_pair u γ (x 0) (x 1)) P
    change B (u.val ![γ.val * x 0, γ.val * x 1] P)
        (c'.val.val ![φ (γ.val * x 1), φ (γ.val * x 2), φ (γ.val * x 3)]) -
          θ (fun i => γ.val * x i) =
      B (u.val ![x 0, x 1] (γ.val⁻¹ • P)) (c'.val.val ![φ (x 1), φ (x 2), φ (x 3)]) - θ x
    rw [pair, map_mul, map_mul, map_mul, cochain_triple c'.val ⟨φ γ.val, dual⟩, θmem γ x]
    change B (rationalCoefficientComponent n D.chi γ.val (u.val ![x 0, x 1] (γ.val⁻¹ • P)))
        (rationalCoefficientComponent n D.chi (φ γ.val) (c'.val.val ![φ (x 1), φ (x 2), φ (x 3)])) -
          θ x = _
    rw [invariant γ.val γ.property]
  have κcocycle : ∀ x, differentialThreeRaw κ x = 0 := by
    intro x
    funext P
    have leibniz := differentialThreeRaw_cupOneTwo B φ (fun x => u.val x P)
      (isCocycleTwo_of_mem c') x
    have restricted : ∀ x' : Fin 3 → RationalGL3,
        differentialOneRaw (fun x => u.val x P) x' = c.val.val x' := by
      intro x'
      exact congrFun (congrArg (fun z => z.val.val x') primitive) P
    have product : cupTwoTwo B φ (differentialOneRaw (fun x => u.val x P)) c'.val.val x =
        cupTwoTwo B φ c.val.val c'.val.val x := by
      unfold cupTwoTwo
      rw [restricted]
    have split : differentialThreeRaw κ x P =
        differentialThreeRaw (cupOneTwo B φ (fun x => u.val x P) c'.val.val) x -
          differentialThreeRaw θ x := by
      simp only [differentialThreeRaw, κ, Pi.sub_apply, Pi.add_apply]
      abel
    rw [split, leibniz, product, θprimitive, sub_self]
    rfl
  refine ⟨0, κ, fun _ _ => 0, κmem, ?_, κcocycle, ?_, ?_⟩
  · intro γ x
    rfl
  · intro x
    funext F
    simp [differentialThreeRaw]
  · intro x e
    rw [map_zero]
    change _ = (0 : (Fin 4 → RationalGL3) → Edges → ℂ) x e + κ x (endpoint .plane e) - 0
    rw [Pi.zero_apply, Pi.zero_apply, zero_add, sub_zero]
    rfl

end Isotropy

end TernaryPeriodPolynomials.Duality
