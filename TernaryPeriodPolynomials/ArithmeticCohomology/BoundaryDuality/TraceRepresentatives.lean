module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.EndpointReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.PlaneTranslateInvariance

@[expose] public section


/-!
# The boundary trace does not depend on representatives

Let `τ` be a boundary trace: an additive functional on scalar three-cochains of complete flags
vanishing on coboundaries and on the pullbacks of plane and line three-cocycles. Let `z` be a line
two-cocycle with edge primitive `w` (`z ∘ endpoint = dw`), `y` a plane two-cocycle moved to lines by
`φ` and the flag map, and `γ` a vertex primitive of the twisted cup product on lines
(`dγ = z ⌣ y^φ`). The boundary cup product is `w ⌣ y^φ - γ`. Its trace depends only on the classes
of `z` and `y`, as soon as the edge pullback of `y` is exact:
* another vertex primitive changes the value by the pullback of a line three-cocycle;
* another edge primitive changes it by `η ⌣ y^φ` with `dη = 0`, which is the coboundary `-d(η ⌣ s^φ)`
  when `y ∘ endpoint = ds`;
* `z ↦ z + du` is absorbed by `w ↦ w + u ∘ endpoint`, `γ ↦ γ + u ⌣ y^φ`, with the same value;
* `y ↦ y + ds` is absorbed by `γ ↦ γ + z ⌣ s^φ`, which changes the value by `-d(w ⌣ s^φ)`.

Plane summand classes have exact edge pullback (stabilizer exactness of the source cocycles), so
boundary duality on the associate pair needs one witness per line class instead of a statement about
all representatives (`associatePairDuality_of_witness`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction

section CupProduct

variable {G V W M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]

/-- The cup product of a two-cochain with a one-cochain whose vertices are moved by `ψ`. -/
def cupTwoOne (B : V →ₗ[ℂ] W →ₗ[ℂ] M) (ψ : G → G) (f : (Fin 3 → G) → V)
    (t : (Fin 2 → G) → W) (x : Fin 4 → G) : M :=
  B (f ![x 0, x 1, x 2]) (t ![ψ (x 2), ψ (x 3)])

/-- Leibniz rule: the differential of `f ⌣ t` for a cocycle `f` is `f ⌣ dt`. -/
theorem differentialThreeRaw_cupTwoOne (B : V →ₗ[ℂ] W →ₗ[ℂ] M) (ψ : G → G)
    {f : (Fin 3 → G) → V} (hf : IsCocycleTwo f) (t : (Fin 2 → G) → W) (x : Fin 5 → G) :
    differentialThreeRaw (cupTwoOne B ψ f t) x =
      B (f ![x 0, x 1, x 2]) (differentialOneRaw t ![ψ (x 2), ψ (x 3), ψ (x 4)]) := by
  have first : f ![x 1, x 2, x 3] - f ![x 0, x 2, x 3] + f ![x 0, x 1, x 3] -
      f ![x 0, x 1, x 2] = 0 := hf ![x 0, x 1, x 2, x 3]
  have first' : f ![x 1, x 2, x 3] = f ![x 0, x 2, x 3] - f ![x 0, x 1, x 3] +
      f ![x 0, x 1, x 2] := by
    rw [← sub_eq_zero, ← first]; abel
  change B (f ![x 1, x 2, x 3]) (t ![ψ (x 3), ψ (x 4)]) -
      B (f ![x 0, x 2, x 3]) (t ![ψ (x 3), ψ (x 4)]) +
      B (f ![x 0, x 1, x 3]) (t ![ψ (x 3), ψ (x 4)]) -
      B (f ![x 0, x 1, x 2]) (t ![ψ (x 2), ψ (x 4)]) +
      B (f ![x 0, x 1, x 2]) (t ![ψ (x 2), ψ (x 3)]) =
    B (f ![x 0, x 1, x 2])
      (t ![ψ (x 3), ψ (x 4)] - t ![ψ (x 2), ψ (x 4)] + t ![ψ (x 2), ψ (x 3)])
  rw [first']
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

omit [Module ℂ M] in
/-- The degree-three differential is additive. -/
theorem differentialThreeRaw_add (f g : (Fin 4 → G) → M) (x : Fin 5 → G) :
    differentialThreeRaw (f + g) x = differentialThreeRaw f x + differentialThreeRaw g x := by
  simp only [differentialThreeRaw, Pi.add_apply]
  abel

omit [Module ℂ M] in
/-- The degree-three differential commutes with subtraction. -/
theorem differentialThreeRaw_sub (f g : (Fin 4 → G) → M) (x : Fin 5 → G) :
    differentialThreeRaw (f - g) x = differentialThreeRaw f x - differentialThreeRaw g x := by
  simp only [differentialThreeRaw, Pi.sub_apply]
  abel

end CupProduct

/-- The data moving plane classes onto lines: a level-preserving endomorphism `φ` of `GL₃(ℚ)`, a
pairing `B` of the coefficients with their `φ`-twist invariant under the level, and maps from line
flags to plane flags and from complete flags to complete flags, equivariant along `φ` and compatible
with the endpoints. -/
structure DualityData (n : ℕ) (χ : RankOneCharacter) where
  /-- The endomorphism of `GL₃(ℚ)`. -/
  φ : RationalGL3 →* RationalGL3
  /-- `φ` preserves the arithmetic level. -/
  level : ∀ g ∈ rationalLevel, φ g ∈ rationalLevel
  /-- The pairing of the coefficients with their `φ`-twist. -/
  B : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ
  /-- Invariance of the pairing under the level. -/
  invariant : ∀ g ∈ rationalLevel, ∀ v w,
    B (rationalCoefficientComponent n χ g v) (rationalCoefficientComponent n χ (φ g) w) = B v w
  /-- The map from line flags to plane flags. -/
  dualFlag : Flags .line → Flags .plane
  /-- The flag map is equivariant along `φ`. -/
  dualFlag_smul : ∀ g F, dualFlag (g • F) = φ g • dualFlag F
  /-- The map on complete flags. -/
  dualEdge : Edges → Edges
  /-- The complete flag map is equivariant along `φ`. -/
  dualEdge_smul : ∀ g e, dualEdge (g • e) = φ g • dualEdge e
  /-- The plane endpoint of the dual complete flag is the dual of the line endpoint. -/
  endpoint_dualEdge : ∀ e, endpoint .plane (dualEdge e) = dualFlag (endpoint .line e)

variable {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- The boundary cup product `w ⌣ y^φ - γ` on complete flags. -/
def boundaryValue (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ) : (Fin 4 → RationalGL3) → Edges → ℂ :=
  fun x e => T.B (w.val ![x 0, x 1] e) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)]
    (T.dualFlag (endpoint .line e))) - γ x (endpoint .line e)

/-- `w` is an edge primitive of the line two-cocycle `z`: `z ∘ endpoint = dw`. -/
def EdgePrimitive (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) : Prop :=
  ∀ x e, z.val.val x (endpoint .line e) = differentialOneRaw w.val x e

/-- `γ` is an invariant vertex primitive of the twisted cup product `z ⌣ y^φ` on lines. -/
def VertexPrimitive (z : MaximalCycles n χ .line) (y : MaximalCycles n χ .plane)
    (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ) : Prop :=
  γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 ∧
    ∀ x F, differentialThreeRaw γ x F =
      T.B (z.val.val ![x 0, x 1, x 2] F)
        (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))

/-- The pullback of the plane two-cocycle `y` to complete flags is exact. -/
def PlaneEdgeExact (y : MaximalCycles n χ .plane) : Prop :=
  ∃ s : EdgeCochains n χ 1, ∀ x e,
    y.val.val x (endpoint .plane e) = differentialOneRaw s.val x e

/-- The scalar line three-cochain `u ⌣ y^φ`. -/
def lineCupOneTwo (u : MaximalCochains n χ .line 1) (y : MaximalCycles n χ .plane) :
    (Fin 4 → RationalGL3) → Flags .line → ℂ :=
  fun x F => T.B (u.val ![x 0, x 1] F)
    (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag F))

/-- The scalar line three-cochain `z ⌣ s^φ`. -/
def lineCupTwoOne (z : MaximalCycles n χ .line) (s : MaximalCochains n χ .plane 1) :
    (Fin 4 → RationalGL3) → Flags .line → ℂ :=
  fun x F => T.B (z.val.val ![x 0, x 1, x 2] F) (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag F))

theorem lineCupOneTwo_mem (u : MaximalCochains n χ .line 1) (y : MaximalCycles n χ .plane) :
    lineCupOneTwo T u y ∈
      cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 := by
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

theorem lineCupTwoOne_mem (z : MaximalCycles n χ .line) (s : MaximalCochains n χ .plane 1) :
    lineCupTwoOne T z s ∈
      cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 := by
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
theorem lineCupOneTwo_differential (u : MaximalCochains n χ .line 1)
    (y : MaximalCycles n χ .plane) (x : Fin 5 → RationalGL3) (F : Flags .line) :
    differentialThreeRaw (lineCupOneTwo T u y) x F =
      T.B (differentialOneRaw u.val ![x 0, x 1, x 2] F)
        (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F)) := by
  have cocycle : IsCocycleTwo (fun x' => y.val.val x' (T.dualFlag F)) := fun x' =>
    congrFun (isCocycleTwo_of_mem y x') (T.dualFlag F)
  exact differentialThreeRaw_cupOneTwo T.B T.φ (fun x' => u.val x' F) cocycle x

/-- Leibniz rule for `z ⌣ s^φ`: its differential is `z ⌣ (ds)^φ`. -/
theorem lineCupTwoOne_differential (z : MaximalCycles n χ .line)
    (s : MaximalCochains n χ .plane 1) (x : Fin 5 → RationalGL3) (F : Flags .line) :
    differentialThreeRaw (lineCupTwoOne T z s) x F =
      T.B (z.val.val ![x 0, x 1, x 2] F)
        (differentialOneRaw s.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F)) := by
  have cocycle : IsCocycleTwo (fun x' => z.val.val x' F) := fun x' =>
    congrFun (isCocycleTwo_of_mem z x') F
  exact differentialThreeRaw_cupTwoOne T.B T.φ cocycle (fun x' => s.val x' (T.dualFlag F)) x

/-- The scalar edge two-cochain `a ⌣ s^φ` for an edge one-cochain `s` read at the dual complete
flag. -/
def edgeDualCup (a s : EdgeCochains n χ 1) :
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

/-- The scalar edge two-cochain `a ⌣ s^φ` for a plane one-cochain `s` moved to lines. -/
def edgeLineCup (a : EdgeCochains n χ 1) (s : MaximalCochains n χ .plane 1) :
    cochains rationalLevel (functionRepresentation scalarTrivial Edges) 2 :=
  ⟨fun x e => T.B (a.val ![x 0, x 1] e)
      (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualFlag (endpoint .line e))), by
    intro g x
    funext e
    have dual : T.φ g.val ∈ rationalLevel := T.level g.val g.property
    change T.B (a.val ![g.val * x 0, g.val * x 1] e)
        (s.val ![T.φ (g.val * x 1), T.φ (g.val * x 2)] (T.dualFlag (endpoint .line e))) =
      T.B (a.val ![x 0, x 1] (g.val⁻¹ • e))
        (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualFlag (endpoint .line (g.val⁻¹ • e))))
    rw [congrFun (cochain_pair a g (x 0) (x 1)) e, map_mul, map_mul,
      congrFun (cochain_pair s ⟨T.φ g.val, dual⟩ (T.φ (x 1)) (T.φ (x 2)))
        (T.dualFlag (endpoint .line e))]
    change T.B (rationalCoefficientComponent n χ g.val (a.val ![x 0, x 1] (g.val⁻¹ • e)))
        (rationalCoefficientComponent n χ (T.φ g.val)
          (s.val ![T.φ (x 1), T.φ (x 2)] ((T.φ g.val)⁻¹ • T.dualFlag (endpoint .line e)))) = _
    rw [T.invariant g.val g.property, ← map_inv T.φ g.val, ← T.dualFlag_smul, ← endpoint_smul]⟩

section Steps

variable {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ}

/-- Two vertex primitives give the same trace: they differ by a line three-cocycle. -/
theorem trace_vertex_eq (hτ : IsBoundaryTrace τ) {z : MaximalCycles n χ .line}
    {y : MaximalCycles n χ .plane} (w : EdgeCochains n χ 1)
    {γ γ' : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hγ : VertexPrimitive T z y γ) (hγ' : VertexPrimitive T z y γ') :
    τ (boundaryValue T w y γ) = τ (boundaryValue T w y γ') := by
  have closed : ∀ x, differentialThreeRaw (γ' - γ) x = 0 := by
    intro x
    funext F
    simp only [differentialThreeRaw_sub, Pi.sub_apply, hγ'.2 x F, hγ.2 x F, sub_self,
      Pi.zero_apply]
  have split : boundaryValue T w y γ =
      boundaryValue T w y γ' + fun x e => (γ' - γ) x (endpoint .line e) := by
    funext x e
    simp only [boundaryValue, Pi.add_apply, Pi.sub_apply]
    abel
  rw [split, map_add, hτ.2.2 (γ' - γ) (sub_mem hγ'.1 hγ.1) closed, add_zero]

/-- Two edge primitives give the same trace when the edge pullback of `y` is exact: they differ by
an edge one-cocycle `η`, and `η ⌣ y^φ = -d(η ⌣ s^φ)` for `y ∘ endpoint = ds`. -/
theorem trace_edge_eq (hτ : IsBoundaryTrace τ) {z : MaximalCycles n χ .line}
    {w w' : EdgeCochains n χ 1} {y : MaximalCycles n χ .plane}
    {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hw : EdgePrimitive z w) (hw' : EdgePrimitive z w') (flat : PlaneEdgeExact y) :
    τ (boundaryValue T w y γ) = τ (boundaryValue T w' y γ) := by
  obtain ⟨s, hs⟩ := flat
  have key : boundaryValue T w y γ = boundaryValue T w' y γ -
      differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges)
        (edgeDualCup T (w - w') s) := by
    funext x e
    have hY : y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e)) =
        s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge e) -
          s.val ![T.φ (x 1), T.φ (x 3)] (T.dualEdge e) +
          s.val ![T.φ (x 1), T.φ (x 2)] (T.dualEdge e) := by
      rw [← T.endpoint_dualEdge e]
      exact hs ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualEdge e)
    have h₁ : z.val.val ![x 0, x 1, x 2] (endpoint .line e) =
        w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e :=
      hw ![x 0, x 1, x 2] e
    have h₂ : z.val.val ![x 0, x 1, x 2] (endpoint .line e) =
        w'.val ![x 1, x 2] e - w'.val ![x 0, x 2] e + w'.val ![x 0, x 1] e :=
      hw' ![x 0, x 1, x 2] e
    have h₁₂ : w.val ![x 1, x 2] e = w'.val ![x 1, x 2] e - w'.val ![x 0, x 2] e +
        w'.val ![x 0, x 1] e + w.val ![x 0, x 2] e - w.val ![x 0, x 1] e := by
      rw [← h₂, h₁]; abel
    change T.B (w.val ![x 0, x 1] e) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)]
          (T.dualFlag (endpoint .line e))) - γ x (endpoint .line e) =
        (T.B (w'.val ![x 0, x 1] e) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)]
          (T.dualFlag (endpoint .line e))) - γ x (endpoint .line e)) -
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

/-- Changing the line cocycle `z` by the coboundary `du` is absorbed by the primitives
`w + u ∘ endpoint` and `γ + u ⌣ y^φ`, with literally the same boundary value. -/
theorem line_coboundary {z : MaximalCycles n χ .line} {w : EdgeCochains n χ 1}
    {y : MaximalCycles n χ .plane} {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hw : EdgePrimitive z w) (hγ : VertexPrimitive T z y γ) (u : MaximalCochains n χ .line 1) :
    EdgePrimitive (z + boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .line) u)
      (w + GraphPieces.BoundaryExactness.endpointPullCochain n χ .line 1 u) ∧
    VertexPrimitive T (z + boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .line) u) y
      (γ + lineCupOneTwo T u y) ∧
    boundaryValue T (w + GraphPieces.BoundaryExactness.endpointPullCochain n χ .line 1 u) y
        (γ + lineCupOneTwo T u y) = boundaryValue T w y γ := by
  refine ⟨fun x e => ?_, And.intro (add_mem hγ.1 (lineCupOneTwo_mem T u y)) fun x F => ?_, ?_⟩
  · have h : z.val.val x (endpoint .line e) =
        w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e := hw x e
    change z.val.val x (endpoint .line e) +
        (u.val ![x 1, x 2] (endpoint .line e) - u.val ![x 0, x 2] (endpoint .line e) +
          u.val ![x 0, x 1] (endpoint .line e)) =
      (w.val ![x 1, x 2] e + u.val ![x 1, x 2] (endpoint .line e)) -
        (w.val ![x 0, x 2] e + u.val ![x 0, x 2] (endpoint .line e)) +
        (w.val ![x 0, x 1] e + u.val ![x 0, x 1] (endpoint .line e))
    rw [h]
    abel
  · rw [differentialThreeRaw_add, Pi.add_apply, hγ.2 x F, lineCupOneTwo_differential]
    change _ = T.B (z.val.val ![x 0, x 1, x 2] F + differentialOneRaw u.val ![x 0, x 1, x 2] F)
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))
    rw [map_add, LinearMap.add_apply]
  · funext x e
    change T.B (w.val ![x 0, x 1] e + u.val ![x 0, x 1] (endpoint .line e))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
        (γ x (endpoint .line e) + T.B (u.val ![x 0, x 1] (endpoint .line e))
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e)))) =
      T.B (w.val ![x 0, x 1] e)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
        γ x (endpoint .line e)
    rw [map_add, LinearMap.add_apply]
    abel

/-- Changing the plane cocycle `y` by the coboundary `ds` is absorbed by the vertex primitive
`γ + z ⌣ s^φ`; the boundary value changes by the coboundary `-d(w ⌣ s^φ)`. -/
theorem plane_coboundary (hτ : IsBoundaryTrace τ) {z : MaximalCycles n χ .line}
    {w : EdgeCochains n χ 1} {y : MaximalCycles n χ .plane}
    {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hw : EdgePrimitive z w) (hγ : VertexPrimitive T z y γ) (s : MaximalCochains n χ .plane 1) :
    VertexPrimitive T z (y + boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .plane) s)
      (γ + lineCupTwoOne T z s) ∧
    τ (boundaryValue T w (y + boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) .plane) s)
      (γ + lineCupTwoOne T z s)) = τ (boundaryValue T w y γ) := by
  refine ⟨And.intro (add_mem hγ.1 (lineCupTwoOne_mem T z s)) fun x F => ?_, ?_⟩
  · rw [differentialThreeRaw_add, Pi.add_apply, hγ.2 x F, lineCupTwoOne_differential]
    change _ = T.B (z.val.val ![x 0, x 1, x 2] F)
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F) +
        differentialOneRaw s.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))
    rw [map_add]
  · have key : boundaryValue T w (y + boundaryMap rationalLevel
          (flagRepresentation (rationalCoefficientComponent n χ) .plane) s)
          (γ + lineCupTwoOne T z s) = boundaryValue T w y γ -
        differentialTwo rationalLevel (functionRepresentation scalarTrivial Edges)
          (edgeLineCup T w s) := by
      funext x e
      have h₁ : z.val.val ![x 0, x 1, x 2] (endpoint .line e) =
          w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e :=
        hw ![x 0, x 1, x 2] e
      change T.B (w.val ![x 0, x 1] e)
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e)) +
            (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e)) -
              s.val ![T.φ (x 1), T.φ (x 3)] (T.dualFlag (endpoint .line e)) +
              s.val ![T.φ (x 1), T.φ (x 2)] (T.dualFlag (endpoint .line e)))) -
          (γ x (endpoint .line e) + T.B (z.val.val ![x 0, x 1, x 2] (endpoint .line e))
            (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e)))) =
        (T.B (w.val ![x 0, x 1] e)
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
            γ x (endpoint .line e)) -
        (T.B (w.val ![x 1, x 2] e) (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
          T.B (w.val ![x 0, x 2] e)
            (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line e))) +
          T.B (w.val ![x 0, x 1] e)
            (s.val ![T.φ (x 1), T.φ (x 3)] (T.dualFlag (endpoint .line e))) -
          T.B (w.val ![x 0, x 1] e)
            (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualFlag (endpoint .line e))))
      rw [h₁]
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
      abel
    rw [key, map_sub, hτ.1, sub_zero]

end Steps

/-- **Independence of representatives.** The trace of the boundary cup product depends only on the
classes of the line and plane cocycles, provided the edge pullback of the plane cocycle is exact. -/
theorem trace_eq {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ} (hτ : IsBoundaryTrace τ)
    {z z' : MaximalCycles n χ .line} {w w' : EdgeCochains n χ 1}
    {y y' : MaximalCycles n χ .plane} {γ γ' : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hw : EdgePrimitive z w) (hγ : VertexPrimitive T z y γ)
    (hw' : EdgePrimitive z' w') (hγ' : VertexPrimitive T z' y' γ')
    (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z')
    (hy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y')
    (flat : PlaneEdgeExact y') :
    τ (boundaryValue T w y γ) = τ (boundaryValue T w' y' γ') := by
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp hz.symm)
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp hy.symm)
  obtain rfl : z' = z + boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) .line) u := by
    rw [hu]; abel
  obtain rfl : y' = y + boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) .plane) s := by
    rw [hs]; abel
  obtain ⟨hγ₁, step₁⟩ := plane_coboundary T hτ hw hγ s
  obtain ⟨hw₂, hγ₂, step₂⟩ := line_coboundary T hw hγ₁ u
  rw [← step₁, ← step₂, trace_edge_eq T hτ hw₂ hw' flat, trace_vertex_eq T hτ w' hγ₂ hγ']

section Summand

variable {D : InducingData n}

/-- Plane summand classes have exact edge pullback, for every representative: this is the
stabilizer exactness of the plane source cocycles. -/
theorem planeEdgeExact_of_mem (y : MaximalCycles n D.chi .plane)
    (hy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      y ∈ boundarySummand D .plane) :
    PlaneEdgeExact y := by
  have hker := GraphPieces.EndpointReduction.boundarySummand_le_ker D .plane
    (fun source isSource flag => FlagExactness.plane_flagExact D source isSource flag) hy
  rw [LinearMap.mem_ker, GraphPieces.BoundaryExactness.endpointPullH2_realizes] at hker
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hker)
  exact ⟨s, fun x e =>
    (congrFun (congrFun (congrArg Subtype.val (congrArg Subtype.val hs)) x) e).symm⟩

/-- One witness per nonzero line summand class: a plane summand class and SOME representatives and
primitives whose boundary cup product has nonzero trace. -/
def TraceWitness (D : InducingData n) (T : DualityData n D.chi)
    (τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ) : Prop :=
  ∀ b ∈ boundarySummand D .line, b ≠ 0 → ∃ ξ ∈ boundarySummand D .plane,
    ∃ (z : MaximalCycles n D.chi .line) (w : EdgeCochains n D.chi 1)
      (y : MaximalCycles n D.chi .plane) (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ),
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z =
        b ∧
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y =
        ξ ∧
      EdgePrimitive z w ∧ VertexPrimitive T z y γ ∧ τ (boundaryValue T w y γ) ≠ 0

/-- A witness for every nonzero line summand class detects it for all representatives. -/
theorem traceDetects_of_witness (T : DualityData n D.chi)
    {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ} (hτ : IsBoundaryTrace τ)
    (witness : TraceWitness D T τ) : TraceDetects D T.φ T.dualFlag T.B τ := by
  intro b hb hne
  obtain ⟨ξ, hξ, z₀, w₀, y₀, γ₀, hz₀, hy₀, hw₀, hγ₀, hτ₀⟩ := witness b hb hne
  refine ⟨ξ, hξ, fun z hz w hw y hy γ hγ hdγ => ?_⟩
  have hmem : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y ∈
        boundarySummand D .plane := by
    rw [hy]; exact hξ
  have equal := trace_eq T hτ hw₀ hγ₀ hw (And.intro hγ hdγ) (hz₀.trans hz.symm)
    (hy₀.trans hy.symm) (planeEdgeExact_of_mem y hmem)
  intro hzero
  exact hτ₀ (equal.trans hzero)

/-- Boundary duality from a trace and one witness per nonzero line summand class. -/
theorem associateDuality_of_witness (T : DualityData n D.chi)
    {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ} (hτ : IsBoundaryTrace τ)
    (witness : TraceWitness D T τ) : AssociateDuality D T.φ T.dualFlag T.B :=
  associateDuality_of_trace D T.φ T.dualFlag T.B hτ (traceDetects_of_witness T hτ witness)

end Summand

/-- The concrete duality data: the involution `g ↦ a (g⁻¹)ᵀ a⁻¹`, its flag maps, and the apolar
pairing. -/
def dualityData (n : ℕ) (χ : RankOneCharacter) : DualityData n χ where
  φ := dualInvolution
  level := fun _ h => dualInvolution_mem_rationalLevel h
  B := dualPairing n
  invariant := fun g _ v w => dualPairing_invariant n χ g v w
  dualFlag := TernaryPeriodPolynomials.Duality.dualFlag
  dualFlag_smul := TernaryPeriodPolynomials.Duality.dualFlag_smul
  dualEdge := TernaryPeriodPolynomials.Duality.dualEdge
  dualEdge_smul := TernaryPeriodPolynomials.Duality.dualEdge_smul
  endpoint_dualEdge := TernaryPeriodPolynomials.Duality.endpoint_plane_dualEdge

/-- **Boundary duality on the associate pair from one witness per class.** A boundary trace, and for
every nonzero line summand class a plane summand class with one choice of representatives and
primitives of nonzero trace, give `AssociatePairDuality D`. -/
theorem associatePairDuality_of_witness (D : InducingData n)
    {τ : ((Fin 4 → RationalGL3) → Edges → ℂ) →+ ℂ} (hτ : IsBoundaryTrace τ)
    (witness : TraceWitness D (dualityData n D.chi) τ) : AssociatePairDuality D :=
  associateDuality_of_witness (dualityData n D.chi) hτ witness

end TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
