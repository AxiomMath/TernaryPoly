module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CupProduct

@[expose] public section


/-!
# Cochain-level invariance of the flag cochain (the algebraic core of M3a(ii))

Formalized by Claude Sonnet 5.5.

For a subgroup `B ≤ G` and data `(w : G → V, z' : G → G → W, γ : G → G → G → T)` the flag cochain is
`flagCup B w z' γ = cup12 (w|_B) (z'|_B) - γ|_B : B³ → T`.

* `leibniz21`: `d(α ∪ w) = α ∪ dw` for a two-cocycle `α` (the missing Leibniz rule for `(2,1)`);
* `flagCup_kappa`: `w ↦ w + κ`, `z ↦ z + dκ`, `γ ↦ γ + κ ∪ z'` leaves `flagCup` unchanged and preserves `dγ = z ∪ z'`;
* `flagCup_eps`: changing `w|_B` by a one-cocycle `ε` of `B` changes `flagCup` by a coboundary `dψ` (when `z'|_B` is a coboundary);
* `flagCup_kappa'`: `z' ↦ z' + dκ'`, `γ ↦ γ + z ∪ κ'` changes `flagCup` by the coboundary `-d(w|_B ∪ κ'|_B)` (when `dw|_B = z|_B`), and preserves `dγ = z ∪ z'`;
* `flagCup_xi`: `γ ↦ γ + ξ` changes `flagCup` by `-ξ|_B`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section Rel

variable {k : Type} [CommRing k] {G : Type} [Group G] {V W T : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup T] [Module k T] {ρ : Representation k G V} {ρ' : Representation k G W} {e : V →ₗ[k] W →ₗ[k] T}

theorem dd3T_add (c c' : G → G → G → T) : dd3T (c + c') = dd3T c + dd3T c' := by
  funext g1 g2 g3 g4
  simp only [dd3T, Pi.add_apply]
  abel

theorem cup12_add_left (u u' : G → V) (β : G → G → W) :
    cup12 ρ' e (u + u') β = cup12 ρ' e u β + cup12 ρ' e u' β := by
  funext g1 g2 g3
  simp [cup12, map_add, LinearMap.add_apply]

theorem cup12_add_right (u : G → V) (β β' : G → G → W) :
    cup12 ρ' e u (β + β') = cup12 ρ' e u β + cup12 ρ' e u β' := by
  funext g1 g2 g3
  simp [cup12, map_add]

theorem cup22_add_left (α α' : G → G → V) (β : G → G → W) :
    cup22 ρ' e (α + α') β = cup22 ρ' e α β + cup22 ρ' e α' β := by
  funext g1 g2 g3 g4
  simp [cup22, map_add, LinearMap.add_apply]

theorem cup22_add_right (α : G → G → V) (β β' : G → G → W) :
    cup22 ρ' e α (β + β') = cup22 ρ' e α β + cup22 ρ' e α β' := by
  funext g1 g2 g3 g4
  simp [cup22, map_add]

theorem cup13_zero (u : G → V) : cup13 ρ' e u (0 : G → G → G → W) = 0 := by
  funext g1 g2 g3 g4
  simp [cup13]

section Leib

variable (he : ∀ (g : G) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w)
include he

/-- **Leibniz rule for `(2,1)`**: for a two-cocycle `α`, `d(α ∪ w) = α ∪ dw`. -/
theorem leibniz21 (α : G → G → V) (hα : dd2 ρ α = 0) (w : G → W) :
    dd3T (cup21 ρ' e α w) = cup22 ρ' e α (dd1 ρ' w) := by
  funext g1 g2 g3 g4
  have h0 := congrFun (congrFun (congrFun hα g1) g2) g3
  simp only [dd2, Pi.zero_apply] at h0
  have h2 : ρ g1 (α g2 g3) = α (g1 * g2) g3 - α g1 (g2 * g3) + α g1 g2 := by
    linear_combination (norm := module) h0
  have h1 := he g1 (α g2 g3) (ρ' (g2 * g3) (w g4))
  rw [h2] at h1
  simp only [dd3T, cup21, cup22, dd1, map_mul, Module.End.mul_apply, map_sub, map_add, LinearMap.sub_apply,
    LinearMap.add_apply, mul_assoc] at h1 ⊢
  rw [← h1]
  abel

end Leib

/-- The flag cochain `cup12 (w|_B) (z'|_B) - γ|_B` of the subgroup `B`. -/
def flagCup (ρ' : Representation k G W) (e : V →ₗ[k] W →ₗ[k] T) (B : Subgroup G) (w : G → V) (z' : G → G → W)
    (γ : G → G → G → T) : B → B → B → T :=
  fun a b c => cup12 (ρ'.comp B.subtype) e (w ∘ B.subtype) (fun a b => z' a b) a b c - γ a b c

/-- **(4) The `γ`-side**: `γ ↦ γ + ξ` changes the flag cochain by `-ξ|_B`. -/
theorem flagCup_xi (B : Subgroup G) (w : G → V) (z' : G → G → W) (γ ξ : G → G → G → T) (a b c : B) :
    flagCup ρ' e B w z' (γ + ξ) a b c = flagCup ρ' e B w z' γ a b c - ξ a b c := by
  simp only [flagCup, Pi.add_apply]
  abel

/-- **(1) Change of the primitive `w ↦ w + κ`** (with `z ↦ z + dκ`, `γ ↦ γ + κ ∪ z'`): the flag cochain is unchanged and `dγ = z ∪ z'` persists. -/
theorem flagCup_kappa (B : Subgroup G) (w : G → V) (κ : G → V) (z' : G → G → W) (γ : G → G → G → T)
    (a b c : B) :
    flagCup ρ' e B (w + κ) z' (γ + cup12 ρ' e κ z') a b c = flagCup ρ' e B w z' γ a b c := by
  simp only [flagCup, Pi.add_apply, cup12, map_add, LinearMap.add_apply, Function.comp, MonoidHom.comp_apply, Subgroup.coe_subtype]
  abel

section Kappa

variable (he : ∀ (g : G) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w)
include he

theorem dd3T_kappa (κ : G → V) (z : G → G → V) (z' : G → G → W) (γ : G → G → G → T)
    (hz' : dd2 ρ' z' = 0) (hγ : dd3T γ = cup22 ρ' e z z') :
    dd3T (γ + cup12 ρ' e κ z') = cup22 ρ' e (z + dd1 ρ κ) z' := by
  rw [dd3T_add, hγ, leibniz12 he, hz', cup13_zero, cup22_add_left]
  funext g1 g2 g3 g4
  simp

/-- **(3) Change of the primitive `z' ↦ z' + dκ'`** (with `γ ↦ γ + z ∪ κ'`, `z` a two-cocycle, `dw|_B = z|_B`): the flag cochain changes by the
coboundary `-d(w|_B ∪ κ'|_B)`. -/
theorem flagCup_kappa' (B : Subgroup G) (w : G → V) (z : G → G → V) (z' : G → G → W) (γ : G → G → G → T) (κ' : G → W)
    (hw : dd1 (ρ.comp B.subtype) (w ∘ B.subtype) = fun a b : B => z a b) :
    flagCup ρ' e B w (z' + dd1 ρ' κ') (γ + cup21 ρ' e z κ') =
      fun a b c => flagCup ρ' e B w z' γ a b c -
        dd2T (cup11 (ρ'.comp B.subtype) e (w ∘ B.subtype) (κ' ∘ B.subtype)) a b c := by
  funext a b c
  have hB : ∀ (g : B) (v : V) (w' : W), e ((ρ.comp B.subtype) g v) ((ρ'.comp B.subtype) g w') = e v w' := fun g v w' => he _ v w'
  have hl := congrFun (congrFun (congrFun (leibniz11 hB (w ∘ B.subtype) (κ' ∘ B.subtype)) a) b) c
  rw [hw] at hl
  simp only [flagCup, cup12, cup21, Pi.add_apply, map_add, dd2T, cup11, dd1, Function.comp, MonoidHom.comp_apply, Subgroup.coe_subtype,
    map_mul, Module.End.mul_apply, map_sub] at hl ⊢
  linear_combination (norm := module) hl

theorem dd3T_kappa' (κ' : G → W) (z : G → G → V) (z' : G → G → W) (γ : G → G → G → T)
    (hz : dd2 ρ z = 0) (hγ : dd3T γ = cup22 ρ' e z z') :
    dd3T (γ + cup21 ρ' e z κ') = cup22 ρ' e z (z' + dd1 ρ' κ') := by
  rw [dd3T_add, hγ, leibniz21 he z hz, cup22_add_right]

/-- **(2) Change of `w|_B` by a one-cocycle `ε` of `B`**: if `z'|_B = d w'_B` the flag cochain changes by a coboundary. -/
theorem flagCup_eps (B : Subgroup G) (w₁ w₂ : G → V) (z' : G → G → W) (γ : G → G → G → T) (w'B : B → W)
    (hε : dd1 (ρ.comp B.subtype) (w₂ ∘ B.subtype - w₁ ∘ B.subtype) = 0)
    (hz' : (fun a b : B => z' a b) = dd1 (ρ'.comp B.subtype) w'B) :
    ∃ ψ : B → B → T, (fun a b c => flagCup ρ' e B w₂ z' γ a b c - flagCup ρ' e B w₁ z' γ a b c) = dd2T ψ := by
  have hB : ∀ (g : B) (v : V) (w' : W), e ((ρ.comp B.subtype) g v) ((ρ'.comp B.subtype) g w') = e v w' := fun g v w' => he _ v w'
  refine ⟨-cup11 (ρ'.comp B.subtype) e (w₂ ∘ B.subtype - w₁ ∘ B.subtype) w'B, ?_⟩
  have h := cup12_coboundary_right hB (w₂ ∘ B.subtype - w₁ ∘ B.subtype) w'B hε
  rw [← hz'] at h
  funext a b c
  have h' := congrFun (congrFun (congrFun h a) b) c
  simp only [flagCup, Pi.sub_apply, Pi.neg_apply, cup12, dd2T, Function.comp, MonoidHom.comp_apply, Subgroup.coe_subtype, map_sub,
    LinearMap.sub_apply] at h' ⊢
  linear_combination (norm := module) h' 

end Kappa

end Rel

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
