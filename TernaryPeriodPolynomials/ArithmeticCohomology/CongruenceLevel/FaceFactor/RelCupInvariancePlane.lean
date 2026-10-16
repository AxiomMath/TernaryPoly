module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.RelCupInvariance

@[expose] public section


/-!
# Cochain-level invariance of the plane flag cochain (the plane analogue of `RelCupInvariance`)

Formalized by Claude Sonnet 5.5.

For a subgroup `B ≤ G` and data `(z : G → G → V, w' : G → W, γ : G → G → G → T)` the plane flag cochain is
`flagCupP B z w' γ = cup21 (z|_B) (-w'|_B) + γ|_B : B³ → T`, with `dγ = z ∪ z'` and `z'|_B = dw'|_B`.

* `cup21_coboundary_left`: `(dv) ∪ ε = d(v ∪ ε)` for a one-cocycle `ε`;
* `flagCupP_kappa'`: `w' ↦ w' + κ'` (with `z' ↦ z' + dκ'`, `γ ↦ γ + z ∪ κ'`) leaves `flagCupP` unchanged and preserves `dγ = z ∪ z'`;
* `flagCupP_kappa`: `z ↦ z + dκ` (with `γ ↦ γ + κ ∪ z'`) changes `flagCupP` by the coboundary `-d(κ|_B ∪ w'|_B)` (when `dw'|_B = z'|_B`), and preserves `dγ = z ∪ z'`;
* `flagCupP_eps`: changing `w'|_B` by a one-cocycle `ε` of `B` changes `flagCupP` by a coboundary (when `z|_B` is a coboundary);
* `flagCupP_xi`: `γ ↦ γ + ξ` changes `flagCupP` by `+ξ|_B`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section RelPlane

variable {k : Type} [CommRing k] {G : Type} [Group G] {V W T : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup T] [Module k T] {ρ : Representation k G V} {ρ' : Representation k G W} {e : V →ₗ[k] W →ₗ[k] T}

theorem cup21_add_right (α : G → G → V) (w w' : G → W) :
    cup21 ρ' e α (w + w') = cup21 ρ' e α w + cup21 ρ' e α w' := by
  funext g1 g2 g3
  simp [cup21, map_add]

theorem cup21_add_left (α α' : G → G → V) (w : G → W) :
    cup21 ρ' e (α + α') w = cup21 ρ' e α w + cup21 ρ' e α' w := by
  funext g1 g2 g3
  simp [cup21, map_add, LinearMap.add_apply]

theorem cup21_neg_right (α : G → G → V) (w : G → W) : cup21 ρ' e α (-w) = - cup21 ρ' e α w := by
  funext g1 g2 g3
  simp [cup21]

/-- The plane flag cochain `cup21 (z|_B) (-w'|_B) + γ|_B` of the subgroup `B`. -/
def flagCupP (ρ' : Representation k G W) (e : V →ₗ[k] W →ₗ[k] T) (B : Subgroup G) (z : G → G → V) (w' : G → W)
    (γ : G → G → G → T) : B → B → B → T :=
  fun a b c => cup21 (ρ'.comp B.subtype) e (fun a b => z a b) (-(w' ∘ B.subtype)) a b c + γ a b c

/-- **(4)** `γ ↦ γ + ξ` changes the plane flag cochain by `+ξ|_B`. -/
theorem flagCupP_xi (B : Subgroup G) (z : G → G → V) (w' : G → W) (γ ξ : G → G → G → T) (a b c : B) :
    flagCupP ρ' e B z w' (γ + ξ) a b c = flagCupP ρ' e B z w' γ a b c + ξ a b c := by
  simp only [flagCupP, Pi.add_apply]
  abel

/-- **Shift of the primitive `w' ↦ w' + κ'`** (with `γ ↦ γ + z ∪ κ'`): the plane flag cochain is unchanged. -/
theorem flagCupP_kappa' (B : Subgroup G) (z : G → G → V) (w' κ' : G → W) (γ : G → G → G → T) (a b c : B) :
    flagCupP ρ' e B z (w' + κ') (γ + cup21 ρ' e z κ') a b c = flagCupP ρ' e B z w' γ a b c := by
  simp only [flagCupP, cup21, Pi.add_apply, Pi.neg_apply, Function.comp, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul,
    map_add, map_neg]
  abel

section Kappa

variable (he : ∀ (g : G) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w)
include he

theorem dd3T_kappa'P (κ' : G → W) (z : G → G → V) (z' : G → G → W) (γ : G → G → G → T)
    (hz : dd2 ρ z = 0) (hγ : dd3T γ = cup22 ρ' e z z') :
    dd3T (γ + cup21 ρ' e z κ') = cup22 ρ' e z (z' + dd1 ρ' κ') := by
  rw [dd3T_add, hγ, leibniz21 he z hz, cup22_add_right]

/-- **`(dv) ∪ ε = d(v ∪ ε)` for a one-cocycle `ε`.** -/
theorem cup21_coboundary_left (v : G → V) (ε : G → W) (hε : dd1 ρ' ε = 0) :
    cup21 ρ' e (dd1 ρ v) ε = dd2T (cup11 ρ' e v ε) := by
  rw [leibniz11 he, hε]
  funext g1 g2 g3
  simp [cup12]

/-- **Shift of `z` by a coboundary `z ↦ z + dκ`** (with `γ ↦ γ + κ ∪ z'`, `dw'|_B = z'|_B`): the plane flag cochain changes by the coboundary `-d(κ|_B ∪ w'|_B)`. -/
theorem flagCupP_kappa (B : Subgroup G) (κ : G → V) (z : G → G → V) (w' : G → W) (z' : G → G → W) (γ : G → G → G → T)
    (hw' : dd1 (ρ'.comp B.subtype) (w' ∘ B.subtype) = fun a b : B => z' a b) :
    flagCupP ρ' e B (z + dd1 ρ κ) w' (γ + cup12 ρ' e κ z') =
      fun a b c => flagCupP ρ' e B z w' γ a b c -
        dd2T (cup11 (ρ'.comp B.subtype) e (κ ∘ B.subtype) (w' ∘ B.subtype)) a b c := by
  funext a b c
  have hB : ∀ (g : B) (v : V) (w'' : W), e ((ρ.comp B.subtype) g v) ((ρ'.comp B.subtype) g w'') = e v w'' := fun g v w'' => he _ v w''
  have hl := congrFun (congrFun (congrFun (leibniz11 hB (κ ∘ B.subtype) (w' ∘ B.subtype)) a) b) c
  rw [hw'] at hl
  simp only [flagCupP, cup12, cup21, Pi.add_apply, Pi.neg_apply, map_add, map_neg, dd2T, cup11, dd1, Function.comp,
    MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, Module.End.mul_apply, map_sub, LinearMap.add_apply] at hl ⊢
  linear_combination (norm := module) hl

/-- **Change of `w'|_B` by a one-cocycle `ε` of `B`**: if `z|_B = d v_B` the plane flag cochain changes by a coboundary. -/
theorem flagCupP_eps (B : Subgroup G) (z : G → G → V) (w'₁ w'₂ : G → W) (γ : G → G → G → T) (vB : B → V)
    (hε : dd1 (ρ'.comp B.subtype) (w'₂ ∘ B.subtype - w'₁ ∘ B.subtype) = 0)
    (hz : (fun a b : B => z a b) = dd1 (ρ.comp B.subtype) vB) :
    ∃ ψ : B → B → T, (fun a b c => flagCupP ρ' e B z w'₂ γ a b c - flagCupP ρ' e B z w'₁ γ a b c) = dd2T ψ := by
  have hB : ∀ (g : B) (v : V) (w'' : W), e ((ρ.comp B.subtype) g v) ((ρ'.comp B.subtype) g w'') = e v w'' := fun g v w'' => he _ v w''
  refine ⟨-cup11 (ρ'.comp B.subtype) e vB (w'₂ ∘ B.subtype - w'₁ ∘ B.subtype), ?_⟩
  have h := cup21_coboundary_left hB vB (w'₂ ∘ B.subtype - w'₁ ∘ B.subtype) hε
  rw [← hz] at h
  funext a b c
  have h' := congrFun (congrFun (congrFun h a) b) c
  simp only [flagCupP, Pi.sub_apply, Pi.neg_apply, cup21, dd2T, Function.comp, MonoidHom.comp_apply, Subgroup.coe_subtype, map_sub,
    map_neg] at h' ⊢
  linear_combination (norm := module) -h'

end Kappa

end RelPlane

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
