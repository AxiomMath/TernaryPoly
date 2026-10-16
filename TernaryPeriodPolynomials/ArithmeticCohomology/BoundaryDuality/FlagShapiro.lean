module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceRepresentatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.EdgeOrbitAssembly

@[expose] public section


/-!
# Shapiro's lemma in degree four and the line cup products

Let `Y` be a `GL₃(ℚ)`-set. If `H⁴(Γ_y, ℂ) = 0` for the stabilizer `Γ_y` in the arithmetic level of
every point `y` (`IsTopVanishing`), then every invariant scalar four-cocycle on `Y` is the coboundary
of an invariant scalar three-cochain: the local primitives at orbit representatives are transported
along the orbits (`exists_primitive`). Applied to line flags and the twisted cup product
`z ⌣ y^φ` of a line and a plane two-cocycle, this gives the vertex primitives of the boundary cup
product from the vanishing of `H⁴` of the line stabilizers (`lineCupExact_of_topVanishing`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.FlagShapiro

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (IsTopVanishing)
open TernaryPeriodPolynomials.GraphPieces.EdgeOrbitAssembly
  (representative transport transport_spec representative_smul)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives

section Shapiro

variable {Y : Type} [MulAction RationalGL3 Y]

/-- The stabilizer of a point in the arithmetic level. -/
def pointStabilizer (y : Y) : Subgroup RationalGL3 :=
  rationalLevel ⊓ MulAction.stabilizer RationalGL3 y

variable (f : (Fin 5 → RationalGL3) → Y → ℂ)
  (hf : f ∈ cochains rationalLevel (functionRepresentation scalarTrivial Y) 4)
  (closed : ∀ x, differentialFourRaw f x = 0)
  (stab : ∀ y : Y, IsTopVanishing (pointStabilizer y))

include hf in
/-- The value of an invariant cochain at a point is invariant under the stabilizer of the point. -/
theorem point_invariant (r : Y) (γ : pointStabilizer r) (x : Fin 5 → RationalGL3) :
    f (fun i => γ.val * x i) r = f x r := by
  have level : γ.val ∈ rationalLevel := (Subgroup.mem_inf.mp γ.property).1
  have fixed : γ.val • r = r := (Subgroup.mem_inf.mp γ.property).2
  have h := congrFun (hf ⟨γ.val, level⟩ x) r
  change f (fun i => γ.val * x i) r = f x (γ.val⁻¹ • r) at h
  rw [h]
  congr 1
  rw [inv_smul_eq_iff, fixed]

/-- The local primitive at a point: a stabilizer-invariant scalar three-cochain whose differential is
the value of `f` at the point. -/
def pointPrimitive (r : Y) : (Fin 4 → RationalGL3) → ℂ :=
  Classical.choose (stab r (fun x => f x r) (point_invariant f hf r) fun x => congrFun (closed x) r)

theorem pointPrimitive_invariant (r : Y) (γ : pointStabilizer r) (x : Fin 4 → RationalGL3) :
    pointPrimitive f hf closed stab r (fun i => γ.val * x i) = pointPrimitive f hf closed stab r x :=
  (Classical.choose_spec
    (stab r (fun x => f x r) (point_invariant f hf r) fun x => congrFun (closed x) r)).1 γ x

theorem pointPrimitive_differential (r : Y) (x : Fin 5 → RationalGL3) :
    differentialThreeRaw (pointPrimitive f hf closed stab r) x = f x r :=
  (Classical.choose_spec
    (stab r (fun x => f x r) (point_invariant f hf r) fun x => congrFun (closed x) r)).2 x

/-- The assembled primitive: the local primitive at the orbit representative, transported to the
point. -/
def assembledPrimitive (x : Fin 4 → RationalGL3) (y : Y) : ℂ :=
  pointPrimitive f hf closed stab (representative rationalLevel y)
    (fun i => (transport rationalLevel y).val⁻¹ * x i)

theorem assembledPrimitive_mem :
    assembledPrimitive f hf closed stab ∈
      cochains rationalLevel (functionRepresentation scalarTrivial Y) 3 := by
  intro γ x
  funext y
  change assembledPrimitive f hf closed stab (fun i => γ.val * x i) y =
    assembledPrimitive f hf closed stab x (γ.val⁻¹ • y)
  have sameRep : representative rationalLevel (γ.val⁻¹ • y) = representative rationalLevel y := by
    have : γ.val⁻¹ • y = (γ⁻¹ : rationalLevel).val • y := by simp
    rw [this, representative_smul]
  have haSpec := transport_spec rationalLevel y
  have ha'Spec := transport_spec rationalLevel (γ.val⁻¹ • y)
  rw [sameRep] at ha'Spec
  unfold assembledPrimitive
  rw [sameRep]
  beta_reduce
  generalize transport rationalLevel y = a at haSpec ⊢
  generalize transport rationalLevel (γ.val⁻¹ • y) = a' at ha'Spec ⊢
  generalize representative rationalLevel y = r at haSpec ha'Spec ⊢
  have fixed : (a⁻¹ * γ * a').val • r = r := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ha'Spec, smul_inv_smul]
    rw [← haSpec, inv_smul_smul]
  have vertices : (fun i => a.val⁻¹ * (γ.val * x i)) =
      (fun i => (a⁻¹ * γ * a').val * (a'.val⁻¹ * x i)) := by
    funext i
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [vertices]
  exact pointPrimitive_invariant f hf closed stab r
    ⟨(a⁻¹ * γ * a').val, Subgroup.mem_inf.mpr ⟨(a⁻¹ * γ * a').property, fixed⟩⟩
    (fun i => a'.val⁻¹ * x i)

theorem assembledPrimitive_differential (x : Fin 5 → RationalGL3) :
    differentialThreeRaw (assembledPrimitive f hf closed stab) x = f x := by
  funext y
  have haSpec := transport_spec rationalLevel y
  have face : ∀ p q s t : RationalGL3, assembledPrimitive f hf closed stab ![p, q, s, t] y =
      pointPrimitive f hf closed stab (representative rationalLevel y)
        ![(transport rationalLevel y).val⁻¹ * p, (transport rationalLevel y).val⁻¹ * q,
          (transport rationalLevel y).val⁻¹ * s, (transport rationalLevel y).val⁻¹ * t] := by
    intro p q s t
    unfold assembledPrimitive
    congr 1
    funext i
    fin_cases i <;> rfl
  have equiv : f (fun i => (transport rationalLevel y).val⁻¹ * x i)
      (representative rationalLevel y) = f x y := by
    have h := congrFun (hf (transport rationalLevel y)⁻¹ x) (representative rationalLevel y)
    change f (fun i => (transport rationalLevel y).val⁻¹ * x i) (representative rationalLevel y) =
      f x ((transport rationalLevel y).val⁻¹⁻¹ • representative rationalLevel y) at h
    rw [h, inv_inv, haSpec]
  change assembledPrimitive f hf closed stab ![x 1, x 2, x 3, x 4] y -
      assembledPrimitive f hf closed stab ![x 0, x 2, x 3, x 4] y +
      assembledPrimitive f hf closed stab ![x 0, x 1, x 3, x 4] y -
      assembledPrimitive f hf closed stab ![x 0, x 1, x 2, x 4] y +
      assembledPrimitive f hf closed stab ![x 0, x 1, x 2, x 3] y = f x y
  rw [face, face, face, face, face]
  change differentialThreeRaw (pointPrimitive f hf closed stab (representative rationalLevel y))
      (fun i => (transport rationalLevel y).val⁻¹ * x i) = f x y
  rw [pointPrimitive_differential, equiv]

include hf closed stab in
/-- **Shapiro's lemma in degree four.** If `H⁴` of every point stabilizer vanishes, every invariant
scalar four-cocycle on `Y` is the coboundary of an invariant scalar three-cochain. -/
theorem exists_primitive :
    ∃ θ ∈ cochains rationalLevel (functionRepresentation scalarTrivial Y) 3,
      ∀ x, differentialThreeRaw θ x = f x :=
  ⟨assembledPrimitive f hf closed stab, assembledPrimitive_mem f hf closed stab,
    assembledPrimitive_differential f hf closed stab⟩

end Shapiro

section LineCup

variable {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- The twisted cup product `z ⌣ y^φ` of a line and a plane two-cocycle, a scalar four-cochain on
lines. -/
def lineCup (z : MaximalCycles n χ .line) (y : MaximalCycles n χ .plane) :
    (Fin 5 → RationalGL3) → Flags .line → ℂ :=
  fun x F => T.B (z.val.val ![x 0, x 1, x 2] F)
    (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))

theorem lineCup_mem (z : MaximalCycles n χ .line) (y : MaximalCycles n χ .plane) :
    lineCup T z y ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 4 := by
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

theorem lineCup_closed (z : MaximalCycles n χ .line) (y : MaximalCycles n χ .plane)
    (x : Fin 6 → RationalGL3) : differentialFourRaw (lineCup T z y) x = 0 := by
  funext F
  have hz : IsCocycleTwo (fun x' => z.val.val x' F) := fun x' =>
    congrFun (isCocycleTwo_of_mem z x') F
  have hy : IsCocycleTwo (fun x' => y.val.val x' (T.dualFlag F)) := fun x' =>
    congrFun (isCocycleTwo_of_mem y x') (T.dualFlag F)
  exact differentialFourRaw_cupTwoTwo T.B T.φ hz hy x

/-- **Vertex primitives from the line stabilizers.** If `H⁴` of the stabilizer of every line flag
vanishes, every twisted cup product of a line and a plane two-cocycle has an invariant vertex
primitive on lines. -/
theorem lineCupExact_of_topVanishing
    (stab : ∀ F : Flags .line, IsTopVanishing (pointStabilizer F))
    (z : MaximalCycles n χ .line) (y : MaximalCycles n χ .plane) :
    ∃ γ, VertexPrimitive T z y γ := by
  obtain ⟨θ, hθ, hdθ⟩ := exists_primitive (lineCup T z y) (lineCup_mem T z y)
    (lineCup_closed T z y) stab
  exact ⟨θ, hθ, fun x F => congrFun (hdθ x) F⟩

end LineCup

end TernaryPeriodPolynomials.BoundaryDuality.FlagShapiro
