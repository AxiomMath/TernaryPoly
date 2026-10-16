module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreLocal
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2

@[expose] public section


/-!
# Cup primitives exist where the second cohomology with trivial coefficients vanishes

Let `ρ`, `ρ'` be representations of a group `G` on `V`, `W` with an invariant pairing `B`, and
let `X`, `Y` be crossed homomorphisms.  The scalar cochain

  `c (g, h) = B (X g) (g • Y h)`

is a two-cocycle of `G` with trivial coefficients `ℂ`: invariance of `B` gives
`c (g h, k) + c (g, h) = c (h, k) + c (g, h k)`.  A function `θ : G → ℂ` with
`θ g + θ h - θ (g h) = c (g, h)` is a primitive of this cocycle, and such a primitive exists as soon
as the class of `c` in `H²(G, ℂ)` vanishes.

* `cupCochain_mem_cocycles₂` records that the cup cochain is a two-cocycle.
* `exists_isCupPrimitive_of_H2` produces a cup primitive whenever `H²(G, ℂ) = 0`.
* `exists_isCupPrimitive_subgroup` and `exists_isCupPrimitive_modular` specialise to every
  subgroup of `SL₂(ℤ)` and to `SL₂(ℤ)` itself, whose second cohomology with complex coefficients
  vanishes.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open CocycleBridge

/-- The scalar cup cochain `(g, h) ↦ B (X g) (g • Y h)` of two crossed homomorphisms. -/
def cupCochain {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (ρ' : Representation ℂ G W) (X : G → V) (Y : G → W) :
    G × G → ℂ :=
  fun p => B (X p.1) (ρ' p.1 (Y p.2))

/-- **The cup cochain of two crossed homomorphisms is a two-cocycle** with trivial coefficients,
for an invariant pairing. -/
theorem cupCochain_mem_cocycles₂ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {X : G → V} {Y : G → W}
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y) :
    cupCochain B ρ' X Y ∈ groupCohomology.cocycles₂ (Rep.trivial ℂ G ℂ) := by
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g h k
  show B (X (g * h)) (ρ' (g * h) (Y k)) + B (X g) (ρ' g (Y h)) =
    B (X h) (ρ' h (Y k)) + B (X g) (ρ' g (Y (h * k)))
  rw [hX g h, hY h k]
  simp only [map_mul, Module.End.mul_apply, map_add, LinearMap.add_apply, hinv]
  ring

/-- **Existence of cup primitives from vanishing of `H²(G, ℂ)`.**  If every class in the second
cohomology of `G` with trivial complex coefficients vanishes, then for every invariant pairing
`B` and crossed homomorphisms `X`, `Y` there is `θ : G → ℂ` with
`θ g + θ h - θ (g h) = B (X g) (g • Y h)`. -/
theorem exists_isCupPrimitive_of_H2 {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {X : G → V} {Y : G → W}
    (hvan : ∀ x : groupCohomology.H2 (Rep.trivial ℂ G ℂ), x = 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y) :
    ∃ θ : G → ℂ, IsCupPrimitive B ρ' X Y θ := by
  have zero := hvan (groupCohomology.H2π (Rep.trivial ℂ G ℂ)
    ⟨cupCochain B ρ' X Y, cupCochain_mem_cocycles₂ hinv hX hY⟩)
  rw [groupCohomology.H2π_eq_zero_iff] at zero
  obtain ⟨f, hf⟩ := zero
  refine ⟨f, fun a b => ?_⟩
  have value := congrFun hf (a, b)
  change f b - f (a * b) + f a = B (X a) (ρ' a (Y b)) at value
  linear_combination value

/-- **Cup primitives on a subgroup of `SL₂(ℤ)`.**  For every subgroup `H` of `SL₂(ℤ)`, every
invariant pairing and every pair of crossed homomorphisms on `H` have a cup primitive. -/
theorem exists_isCupPrimitive_subgroup {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    {ρ : Representation ℂ H V} {ρ' : Representation ℂ H W}
    {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {X : H → V} {Y : H → W}
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y) :
    ∃ θ : H → ℂ, IsCupPrimitive B ρ' X Y θ :=
  exists_isCupPrimitive_of_H2
    (Spectral.ModularH2.modularSubgroupH2_zero H (Rep.trivial ℂ H ℂ)) hinv hX hY

/-- **Cup primitives on `SL₂(ℤ)`.** -/
theorem exists_isCupPrimitive_modular {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) V}
    {ρ' : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) W}
    {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {X : Matrix.SpecialLinearGroup (Fin 2) ℤ → V}
    {Y : Matrix.SpecialLinearGroup (Fin 2) ℤ → W}
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y) :
    ∃ θ : Matrix.SpecialLinearGroup (Fin 2) ℤ → ℂ, IsCupPrimitive B ρ' X Y θ :=
  exists_isCupPrimitive_of_H2
    (Spectral.ModularH2.modularH2_zero (Rep.trivial ℂ _ ℂ)) hinv hX hY

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
