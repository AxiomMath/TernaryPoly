module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityCochain

@[expose] public section


/-!
# Compactly supported cohomology of a punctured sphere group and the cup pairing (relative cocycles)

Formalized by Claude Sonnet 5.5.

Algebra of the cusp-relative first cohomology `H¹_c` for a group `Γ` with a homomorphism `ι : N → Γ` and two elements `a, g₂ ∈ N`
(`g₃ = (a g₂)⁻¹`, so that `a g₂ g₃ = 1`: the fundamental group of the three-punctured sphere), as in the triple model
(`BoundaryDuality.TripleModel`).

* `relCocycles`: relative one-cocycles `(Z, v)`: a crossed homomorphism `Z` of `Γ` together with primitives `v = (v₁, v₂, v₃)` of
  its values at `a`, `g₂`, `g₃` (the cone of the restriction map to the three cyclic subgroups: `Z a = (a-1) v₁`, ...);
* `relBoundaries`: relative coboundaries `(g ↦ ρ g u - u, (u, u, u) + f)`, `f` in an ignored subspace `F` of fixed vectors of the
  elliptic (non-cusp) special elements;
* `Hc`: the quotient, the cusp-relative (compactly supported) cohomology `H¹_c`; the map to `H¹` forgets the primitives;
* `pdRaw`: the Poincare-Lefschetz cup formula `(Z ∪ Z')[a | g₂] + (Z ∪ Z')[a g₂ | g₃] - ∑ᵢ B (vᵢ, Z' gᵢ)` of a relative cocycle with
  an arbitrary crossed homomorphism of the dual system; it vanishes on relative coboundaries (`pdRaw_boundary_left`) and on
  coboundaries of the dual system (`pdRaw_boundary_right`);
* `tripleForm_skew`: the skew-symmetry `⟨v, v'⟩ + ⟨v', v⟩ = 0` of the triple cup form on constrained triples, which makes
  the transpose of `j : H¹_c → H¹` the corresponding map for the dual system.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL

open TernaryPeriodPolynomials.BoundaryDuality
open TripleModel LinearDuality CocycleBridge EpsilonSplit ParabolicDuality

section Skew

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- Quadratic identity for an invariant pairing: `⟨(g-1)x,(g-1)y⟩ + ⟨x,(g-1)y⟩ + ⟨(g-1)x,y⟩ = 0`. -/
theorem quad_identity (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (g : G) (x : V) (y : W) :
    B ((ρ g - 1) x) ((ρ' g - 1) y) + B x ((ρ' g - 1) y) + B ((ρ g - 1) x) y = 0 := by
  have h := hinv g x y
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, LinearMap.sub_apply]
  linear_combination h

theorem tripleForm_skew (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (a g₂ : G)
    {v : V × V × V} {v' : W × W × W} (hv : v ∈ tripleCycles ρ a g₂)
    (hv' : v' ∈ tripleCycles ρ' a g₂) :
    tripleForm B ρ' a g₂ v v' + tripleForm B.flip ρ a g₂ v' v = 0 := by
  have hC : constraint ρ a g₂ v = 0 := LinearMap.mem_ker.1 hv
  have hC' : constraint ρ' a g₂ v' = 0 := LinearMap.mem_ker.1 hv'
  rw [constraint_apply] at hC hC'
  have eb : ∀ x : V, ρ (a * g₂) x = ρ a (ρ g₂ x) := fun x => rep_mul_apply ρ a g₂ x
  have eb' : ∀ y : W, ρ' (a * g₂) y = ρ' a (ρ' g₂ y) := fun y => rep_mul_apply ρ' a g₂ y
  -- U = (b-1) v₃ = (a-1) v₁ + a ((g₂-1) v₂)
  have hU : (ρ (a * g₂) - 1) v.2.2 = (ρ a - 1) v.1 + ρ a ((ρ g₂ - 1) v.2.1) := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, eb] at hC ⊢
    linear_combination (norm := module) (-1 : ℂ) • hC
  have hU' : (ρ' (a * g₂) - 1) v'.2.2 = (ρ' a - 1) v'.1 + ρ' a ((ρ' g₂ - 1) v'.2.1) := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, eb'] at hC' ⊢
    linear_combination (norm := module) (-1 : ℂ) • hC'
  have Qb := quad_identity hinv (a * g₂) v.2.2 v'.2.2
  have Qa := quad_identity hinv a v.1 v'.1
  have Qg := quad_identity hinv g₂ v.2.1 v'.2.1
  have I4 := hinv a v.1 ((ρ' g₂ - 1) v'.2.1)
  have I5 := hinv a ((ρ g₂ - 1) v.2.1) v'.1
  have I6 := hinv a ((ρ g₂ - 1) v.2.1) ((ρ' g₂ - 1) v'.2.1)
  rw [hU, hU'] at Qb
  rw [tripleForm_apply, tripleForm_apply, hU', hU]
  simp only [LinearMap.flip_apply, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
    map_sub, map_add, eb, eb'] at Qb Qa Qg I4 I5 I6 ⊢
  linear_combination Qb - Qa - I4 - I5 - Qg - I6

end Skew

section Relative

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] (ι : N →* Γ) (ρ : Representation ℂ Γ V) (a g₂ : N)

/-- **Relative one-cocycles** of `Γ` with coefficients in `ρ` relative to the three cyclic subgroups `⟨a⟩`, `⟨g₂⟩`,
`⟨(a g₂)⁻¹⟩` of `N`: a crossed homomorphism `Z` together with primitives `v₁, v₂, v₃` of its values at the three
special elements. -/
def relCocycles : Submodule ℂ ((Γ → V) × (V × V × V)) where
  carrier := {x | IsCocycle ρ x.1 ∧ IsPrimitive (ρ.comp ι) a g₂ (fun n => x.1 (ι n)) x.2}
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g h
      simp
    all_goals simp
  add_mem' := by
    rintro x y ⟨hx, px⟩ ⟨hy, py⟩
    exact ⟨isCocycle_add hx hy, isPrimitive_add (z := fun n => x.1 (ι n)) (z' := fun n => y.1 (ι n)) px py⟩
  smul_mem' := by
    rintro c x ⟨hx, px⟩
    exact ⟨isCocycle_smul hx c, isPrimitive_smul (z := fun n => x.1 (ι n)) px c⟩

variable {ι ρ a g₂}

theorem mem_relCocycles {x : (Γ → V) × (V × V × V)} :
    x ∈ relCocycles ι ρ a g₂ ↔
      IsCocycle ρ x.1 ∧ IsPrimitive (ρ.comp ι) a g₂ (fun n => x.1 (ι n)) x.2 := Iff.rfl

variable (ι ρ a g₂)

/-- **Relative coboundaries**: the coboundaries `(g ↦ ρ g u - u, (u, u, u) + f)` of a vector `u` and an element `f` of
the ignored subspace `F` (the fixed vectors of the torsion special elements, i.e. the points of the orbifold which are not
cusps). -/
def relBoundaries (F : Submodule ℂ (V × V × V)) : Submodule ℂ (relCocycles ι ρ a g₂) where
  carrier := {x | ∃ u : V, ∃ f ∈ F, x.1.1 = (fun g => ρ g u - u) ∧ x.1.2 = (u, u, u) + f}
  zero_mem' := ⟨0, 0, F.zero_mem, by funext g; simp, by ext <;> simp⟩
  add_mem' := by
    rintro x y ⟨u, f, hf, hx1, hx2⟩ ⟨u', f', hf', hy1, hy2⟩
    refine ⟨u + u', f + f', F.add_mem hf hf', ?_, ?_⟩
    · funext g
      show x.1.1 g + y.1.1 g = _
      rw [hx1, hy1]
      simp only [map_add]
      abel
    · show x.1.2 + y.1.2 = _
      rw [hx2, hy2]
      ext <;> simp <;> abel
  smul_mem' := by
    rintro c x ⟨u, f, hf, hx1, hx2⟩
    refine ⟨c • u, c • f, F.smul_mem c hf, ?_, ?_⟩
    · funext g
      show c • x.1.1 g = _
      rw [hx1]
      simp only [map_smul, smul_sub]
    · show c • x.1.2 = _
      rw [hx2]
      ext <;> simp

/-- **Compactly supported (cusp-relative) first cohomology** `H¹_c`, the relative cohomology of `Γ` relative to the
cyclic subgroups of the three special elements, modulo the ignored fixed vectors `F`. -/
abbrev Hc (F : Submodule ℂ (V × V × V)) : Type := relCocycles ι ρ a g₂ ⧸ relBoundaries ι ρ a g₂ F

end Relative


section Pairing

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
  (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)

/-- The raw Poincare-Lefschetz pairing of a relative cocycle `(Z, v)` with a crossed homomorphism `Z'`: the cup formula
`(Z ∪ Z')[a | g₂] + (Z ∪ Z')[a g₂ | g₃] - ∑ᵢ B (vᵢ, Z' gᵢ)` of the restrictions along `ι`. -/
def pdRaw : relCocycles ι ρ a g₂ →ₗ[ℂ] (Γ → W) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun x Z' => cupFormula B (ρ'.comp ι) a g₂ (fun n => x.1.1 (ι n)) (fun n => Z' (ι n)) x.1.2)
    (by
      intro x y Z'
      simp only [cupFormula, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add,
        LinearMap.add_apply]
      ring)
    (by
      intro c x Z'
      simp only [cupFormula, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul]
      ring)
    (by
      intro x Z Z'
      simp only [cupFormula, Pi.add_apply, map_add]
      ring)
    (by
      intro c x Z'
      simp only [cupFormula, Pi.smul_apply, map_smul, smul_eq_mul]
      ring)

theorem pdRaw_apply (x : relCocycles ι ρ a g₂) (Z' : Γ → W) :
    pdRaw ι ρ ρ' B a g₂ x Z' =
      cupFormula B (ρ'.comp ι) a g₂ (fun n => x.1.1 (ι n)) (fun n => Z' (ι n)) x.1.2 := rfl

end Pairing


section Descent

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {ι : N →* Γ} {ρ : Representation ℂ Γ V} {ρ' : Representation ℂ Γ W}
  {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {a g₂ : N}

/-- The relative cocycle pairs trivially with a coboundary of the dual system (the primitive of the relative cocycle is
constrained). -/
theorem pdRaw_boundary_right (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w)
    (x : relCocycles ι ρ a g₂) (w : W) :
    pdRaw ι ρ ρ' B a g₂ x (fun g => ρ' g w - w) = 0 := by
  have hinv' : ∀ (n : N) (x : V) (y : W), B ((ρ.comp ι) n x) ((ρ'.comp ι) n y) = B x y := hinv
  have hz : IsCocycle (ρ.comp ι) (fun n => x.1.1 (ι n)) := isCocycle_comp x.2.1 ι
  have hp := x.2.2
  have e := cupFormula_eq_tripleForm hinv' hz hp (isPrimitive_boundary (ρ'.comp ι) a g₂ w)
  rw [pdRaw_apply]
  refine e.trans ?_
  rw [tripleForm_diag' hinv' a g₂ x.1.2 w]
  have hc : constraint (ρ.comp ι) a g₂ x.1.2 = 0 := LinearMap.mem_ker.1 (hp.mem_tripleCycles hz)
  rw [hc, map_zero, LinearMap.zero_apply]

/-- The coboundaries (modulo the ignored vectors) pair trivially with every crossed homomorphism of the dual system. -/
theorem pdRaw_boundary_left (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w)
    {F : Submodule ℂ (V × V × V)}
    (hF : ∀ f ∈ F, ∀ Z' : Γ → W, IsCocycle ρ' Z' →
      B f.1 (Z' (ι a)) + B f.2.1 (Z' (ι g₂)) + B f.2.2 (Z' (ι (a * g₂)⁻¹)) = 0)
    {x : relCocycles ι ρ a g₂} (hx : x ∈ relBoundaries ι ρ a g₂ F) {Z' : Γ → W}
    (hZ' : IsCocycle ρ' Z') : pdRaw ι ρ ρ' B a g₂ x Z' = 0 := by
  obtain ⟨u, f, hf, hx1, hx2⟩ := hx
  have hy : IsCocycle (ρ'.comp ι) (fun n => Z' (ι n)) := isCocycle_comp hZ' ι
  have h1 : Z' (ι (a * g₂)) = Z' (ι a) + ρ' (ι a) (Z' (ι g₂)) := hy a g₂
  have h0 : Z' (ι ((a * g₂) * (a * g₂)⁻¹)) = 0 := by
    rw [mul_inv_cancel, map_one]
    exact hZ'.map_one
  have h2 : Z' (ι (a * g₂)) + ρ' (ι (a * g₂)) (Z' (ι (a * g₂)⁻¹)) = 0 :=
    (hy (a * g₂) (a * g₂)⁻¹).symm.trans h0
  have h3 : ρ' (ι (a * g₂)) (Z' (ι (a * g₂)⁻¹)) = -(Z' (ι a) + ρ' (ι a) (Z' (ι g₂))) := by
    rw [← h1]
    exact eq_neg_of_add_eq_zero_right h2
  have kf := hF f hf Z' hZ'
  have e1 : B (ρ (ι a) u) (ρ' (ι a) (Z' (ι g₂))) = B u (Z' (ι g₂)) := hinv a u _
  have e2 : B (ρ (ι (a * g₂)) u) (ρ' (ι (a * g₂)) (Z' (ι (a * g₂)⁻¹))) =
      B u (Z' (ι (a * g₂)⁻¹)) := hinv (a * g₂) u _
  rw [pdRaw_apply, hx1, hx2]
  simp only [cupFormula]
  rw [h3] at e2
  simp only [MonoidHom.comp_apply, h3, map_sub, map_neg, LinearMap.sub_apply, Prod.fst_add, Prod.snd_add,
    map_add, LinearMap.add_apply] at e2 ⊢
  linear_combination e1 + e2 - kf

end Descent

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL
