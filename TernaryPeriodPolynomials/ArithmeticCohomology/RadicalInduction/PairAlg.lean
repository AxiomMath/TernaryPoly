module

public import Mathlib

@[expose] public section


/-!
# The Koszul value of a pair of commuting translations

Formalized by Claude Sonnet 5.5.

For a commutative group `N` acting on `E`, `E'` with an invariant pairing `e`, and two elements `u, v`, the Koszul value `AP(a₁, a₂; b₁, b₂) = e(a₁, ρ'(u) b₂) - e(a₂, ρ'(v) b₁)`
of the values of two cocycles at `u, v`.  `Rel ρ u v a₁ a₂` is the cocycle relation `c(uv) = c(vu)` for the pair of values; the value is unchanged by
adding coboundaries (`AP_cob_left`, `AP_cob_right`) to a pair satisfying the relation and by translating by an element of `N` (`AP_shift`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

section Pair

variable {N : Type} [CommGroup N] {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  (ρ : Representation ℂ N E) (ρ' : Representation ℂ N E') (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ) (u v : N)

/-- The Koszul value of a pair of generator values. -/
def AP (a₁ a₂ : E) (b₁ b₂ : E') : ℂ := e a₁ (ρ' u b₂) - e a₂ (ρ' v b₁)

/-- The cocycle relation `c(uv) = c(vu)` for the values `a₁ = c(u)`, `a₂ = c(v)`. -/
def Rel {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ N V) (a₁ a₂ : V) : Prop :=
  σ u a₂ + a₁ = σ v a₁ + a₂

theorem comm_apply {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ N V) (x y : N) (a : V) :
    σ x (σ y a) = σ y (σ x a) := by
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

theorem AP_add_left (a₁ a₂ c₁ c₂ : E) (b₁ b₂ : E') :
    AP ρ' e u v (a₁ + c₁) (a₂ + c₂) b₁ b₂ = AP ρ' e u v a₁ a₂ b₁ b₂ + AP ρ' e u v c₁ c₂ b₁ b₂ := by
  simp only [AP, map_add, LinearMap.add_apply]; ring

theorem AP_add_right (a₁ a₂ : E) (b₁ b₂ d₁ d₂ : E') :
    AP ρ' e u v a₁ a₂ (b₁ + d₁) (b₂ + d₂) = AP ρ' e u v a₁ a₂ b₁ b₂ + AP ρ' e u v a₁ a₂ d₁ d₂ := by
  simp only [AP, map_add]; ring

theorem Rel_add {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ N V) {a₁ a₂ c₁ c₂ : V}
    (h : Rel u v σ a₁ a₂) (h' : Rel u v σ c₁ c₂) : Rel u v σ (a₁ + c₁) (a₂ + c₂) := by
  unfold Rel at *
  rw [map_add, map_add]
  have := congrArg₂ (· + ·) h h'
  convert this using 1 <;> abel

theorem Rel_map {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ N V) (k : N) {a₁ a₂ : V}
    (h : Rel u v σ a₁ a₂) : Rel u v σ (σ k a₁) (σ k a₂) := by
  unfold Rel at *
  rw [comm_apply σ u k, comm_apply σ v k, ← map_add, ← map_add, h]

theorem Rel_cob {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ N V) (w : V) :
    Rel u v σ (σ u w - w) (σ v w - w) := by
  unfold Rel
  rw [map_sub, map_sub, comm_apply σ u v w]
  abel

variable {ρ ρ' e}

/-- Coboundaries in the first slot pair to zero with a cocycle pair. -/
theorem AP_cob_left (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b) (w : E) {b₁ b₂ : E'} (h : Rel u v ρ' b₁ b₂) :
    AP ρ' e u v (ρ u w - w) (ρ v w - w) b₁ b₂ = 0 := by
  unfold AP
  have h1 : e (ρ u w) (ρ' u b₂) = e w b₂ := he u w b₂
  have h2 : e (ρ v w) (ρ' v b₁) = e w b₁ := he v w b₁
  have h3 : e w (ρ' u b₂ + b₁) = e w (ρ' v b₁ + b₂) := by rw [h]
  simp only [map_sub, LinearMap.sub_apply, map_add] at h1 h2 h3 ⊢
  linear_combination h1 - h2 - h3

/-- Coboundaries in the second slot pair to zero with a cocycle pair. -/
theorem AP_cob_right (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b) (w' : E') {a₁ a₂ : E} (h : Rel u v ρ a₁ a₂) :
    AP ρ' e u v a₁ a₂ (ρ' u w' - w') (ρ' v w' - w') = 0 := by
  set z := ρ' u (ρ' v w') with hz
  have hc' : ρ' v (ρ' u w') = z := (comm_apply ρ' u v w').symm
  have h1 : e (ρ v a₁) z = e a₁ (ρ' u w') := by rw [← hc']; exact he v a₁ _
  have h2 : e (ρ u a₂) z = e a₂ (ρ' v w') := he u a₂ _
  have h3 : e (ρ u a₂ + a₁) z = e (ρ v a₁ + a₂) z := by rw [h]
  simp only [map_add, LinearMap.add_apply] at h3
  unfold AP
  simp only [map_sub]
  rw [hc']
  linear_combination h3 + h1 - h2

/-- Translation by `k` preserves the Koszul value. -/
theorem AP_map (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b) (k : N) (a₁ a₂ : E) (b₁ b₂ : E') :
    AP ρ' e u v (ρ k a₁) (ρ k a₂) (ρ' k b₁) (ρ' k b₂) = AP ρ' e u v a₁ a₂ b₁ b₂ := by
  unfold AP
  rw [comm_apply ρ' u k, comm_apply ρ' v k, he, he]

/-- **Shift lemma**: adding coboundaries and translating by `k` does not change the Koszul value of a pair of values satisfying the relations. -/
theorem AP_shift (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b) (k : N) {a₁ a₂ : E} {b₁ b₂ : E'}
    (hR : Rel u v ρ a₁ a₂) (hR' : Rel u v ρ' b₁ b₂) (w : E) (w' : E') :
    AP ρ' e u v (ρ k a₁ + (ρ u w - w)) (ρ k a₂ + (ρ v w - w)) (ρ' k b₁ + (ρ' u w' - w')) (ρ' k b₂ + (ρ' v w' - w')) =
      AP ρ' e u v a₁ a₂ b₁ b₂ := by
  have hRk : Rel u v ρ (ρ k a₁) (ρ k a₂) := Rel_map u v ρ k hR
  have hRk' : Rel u v ρ' (ρ' k b₁) (ρ' k b₂) := Rel_map u v ρ' k hR'
  have hsum' : Rel u v ρ' (ρ' k b₁ + (ρ' u w' - w')) (ρ' k b₂ + (ρ' v w' - w')) :=
    Rel_add u v ρ' hRk' (Rel_cob u v ρ' w')
  rw [AP_add_left, AP_cob_left u v he w hsum', AP_add_right, AP_cob_right u v he w' hRk, AP_map u v he]
  ring

end Pair

end TernaryPeriodPolynomials.Argument.RadicalInduction
