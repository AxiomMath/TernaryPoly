module

public import Mathlib

@[expose] public section


/-!
# Descent of a perfect pairing to the invariants (isotypic parts) of a finite group

Formalized by Claude Sonnet 5.5.

Let `G` be a finite group acting on complex vector spaces `V`, `W` and let `e : V × W → ℂ` be a pairing with `e (g v) (g w) = ε(g) e v w` for a character `ε`.
For characters `χ`, `ψ` with `χ ψ = ε`, the `χ`-isotypic part of `V` and the `ψ`-isotypic part of `W` are paired perfectly if `e` is (`isotypic_left`, `isotypic_right`): the
averaging projections `isoProj` onto the isotypic parts are exact (the order of `G` is invertible in `ℂ`).  For `ε = 1` and `χ = ψ = 1` this is the descent to the invariants (`invariants_left`, `invariants_right`).
If `ε` is non-trivial the pairing vanishes on the invariants (`pairing_zero_of_char_ne_one`), which is why the orientation characters must multiply to the (trivial) orientation of the face.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open scoped BigOperators

section Proj

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- The `χ`-isotypic part `{v | g v = χ(g) v}` of a representation. -/
def isoSub (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : Submodule ℂ V where
  carrier := {v | ∀ g, ρ g v = (χ g : ℂ) • v}
  add_mem' := fun ha hb g => by simp [map_add, ha g, hb g, smul_add]
  zero_mem' := fun g => by simp
  smul_mem' := fun c v hv g => by
    show ρ g (c • v) = (χ g : ℂ) • c • v
    rw [map_smul, hv g, smul_comm]

theorem mem_isoSub {ρ : Representation ℂ G V} {χ : G →* ℂˣ} {v : V} : v ∈ isoSub ρ χ ↔ ∀ g, ρ g v = (χ g : ℂ) • v := Iff.rfl

variable [Fintype G]

/-- The averaging projection onto the `χ`-isotypic part. -/
def isoProj (ρ : Representation ℂ G V) (χ : G →* ℂˣ) (v : V) : V :=
  ((Fintype.card G : ℂ)⁻¹) • ∑ g : G, ((χ g)⁻¹ : ℂˣ).val • ρ g v

theorem card_ne_zero : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero

theorem isoProj_mem (ρ : Representation ℂ G V) (χ : G →* ℂˣ) (v : V) : isoProj ρ χ v ∈ isoSub ρ χ := by
  intro h
  unfold isoProj
  rw [map_smul, map_sum]
  have : ∑ g : G, ρ h (((χ g)⁻¹ : ℂˣ).val • ρ g v) = (χ h : ℂ) • ∑ g : G, ((χ g)⁻¹ : ℂˣ).val • ρ g v := by
    rw [Finset.smul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_))
    simp only [Equiv.coe_mulLeft, map_smul, ← Module.End.mul_apply, ← map_mul, smul_smul]
    congr 1
    rw [map_mul, mul_inv]
    simp
  rw [this, smul_comm]

theorem isoProj_of_mem (ρ : Representation ℂ G V) (χ : G →* ℂˣ) {v : V} (hv : v ∈ isoSub ρ χ) : isoProj ρ χ v = v := by
  unfold isoProj
  have : ∀ g : G, ((χ g)⁻¹ : ℂˣ).val • ρ g v = v := fun g => by
    rw [hv g, smul_smul]
    simp
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ card_ne_zero, one_smul]

end Proj

section Pairing

variable {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (ε χ ψ : G →* ℂˣ)

omit [Fintype G] in
theorem pair_right_act (hχψ : ∀ g, (χ g : ℂ) * ψ g = ε g) (hε : ∀ g v w, e (ρ g v) (σ g w) = (ε g : ℂ) * e v w)
    {v : V} (hv : v ∈ isoSub ρ χ) (g : G) (w : W) : e v (σ g w) = (ψ g : ℂ) * e v w := by
  have h := hε g v w
  rw [hv g, map_smul, LinearMap.smul_apply, smul_eq_mul, ← hχψ g] at h
  have hne : (χ g : ℂ) ≠ 0 := (χ g).ne_zero
  have : (χ g : ℂ) * (e v (σ g w) - (ψ g : ℂ) * e v w) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hne
  · linear_combination h0

omit [Fintype G] in
theorem pair_left_act (hχψ : ∀ g, (χ g : ℂ) * ψ g = ε g) (hε : ∀ g v w, e (ρ g v) (σ g w) = (ε g : ℂ) * e v w)
    {w : W} (hw : w ∈ isoSub σ ψ) (g : G) (v : V) : e (ρ g v) w = (χ g : ℂ) * e v w := by
  have h := hε g v w
  rw [hw g, map_smul, smul_eq_mul, ← hχψ g] at h
  have hne : (ψ g : ℂ) ≠ 0 := (ψ g).ne_zero
  have : (ψ g : ℂ) * (e (ρ g v) w - (χ g : ℂ) * e v w) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hne
  · linear_combination h0

/-- **The pairing of the isotypic parts is left nondegenerate** (`χ ψ = ε`). -/
theorem isotypic_left (hχψ : ∀ g, (χ g : ℂ) * ψ g = ε g) (hε : ∀ g v w, e (ρ g v) (σ g w) = (ε g : ℂ) * e v w)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) {v : V} (hv : v ∈ isoSub ρ χ) (h : ∀ w ∈ isoSub σ ψ, e v w = 0) : v = 0 := by
  apply hL
  intro w
  have h1 := h (isoProj σ ψ w) (isoProj_mem σ ψ w)
  have h2 : e v (isoProj σ ψ w) = e v w := by
    unfold isoProj
    rw [map_smul, map_sum]
    simp only [map_smul, pair_right_act e ε χ ψ hχψ hε hv, smul_eq_mul]
    have : ∀ g : G, ((ψ g)⁻¹ : ℂˣ).val * ((ψ g : ℂ) * e v w) = e v w := fun g => by
      rw [← mul_assoc]; simp
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [card_ne_zero (G := G)]
  rw [← h2]; exact h1

/-- **The pairing of the isotypic parts is right nondegenerate** (`χ ψ = ε`). -/
theorem isotypic_right (hχψ : ∀ g, (χ g : ℂ) * ψ g = ε g) (hε : ∀ g v w, e (ρ g v) (σ g w) = (ε g : ℂ) * e v w)
    (hR : ∀ w, (∀ v, e v w = 0) → w = 0) {w : W} (hw : w ∈ isoSub σ ψ) (h : ∀ v ∈ isoSub ρ χ, e v w = 0) : w = 0 := by
  apply hR
  intro v
  have h1 := h (isoProj ρ χ v) (isoProj_mem ρ χ v)
  have h2 : e (isoProj ρ χ v) w = e v w := by
    unfold isoProj
    rw [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, pair_left_act e ε χ ψ hχψ hε hw, smul_eq_mul]
    have : ∀ g : G, ((χ g)⁻¹ : ℂˣ).val * ((χ g : ℂ) * e v w) = e v w := fun g => by
      rw [← mul_assoc]; simp
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [card_ne_zero (G := G)]
  rw [← h2]; exact h1

/-- **Descent to the invariants, left**: for a `G`-invariant pairing (`ε = 1`) which is left nondegenerate, the restriction to the invariants is left nondegenerate. -/
theorem invariants_left (hinv : ∀ g v w, e (ρ g v) (σ g w) = e v w) (hL : ∀ v, (∀ w, e v w = 0) → v = 0) {v : V}
    (hv : v ∈ isoSub ρ 1) (h : ∀ w ∈ isoSub σ 1, e v w = 0) : v = 0 :=
  isotypic_left e 1 1 1 (fun g => by simp) (fun g v w => by simpa using hinv g v w) hL hv h

/-- **Descent to the invariants, right.** -/
theorem invariants_right (hinv : ∀ g v w, e (ρ g v) (σ g w) = e v w) (hR : ∀ w, (∀ v, e v w = 0) → w = 0) {w : W}
    (hw : w ∈ isoSub σ 1) (h : ∀ v ∈ isoSub ρ 1, e v w = 0) : w = 0 :=
  isotypic_right e 1 1 1 (fun g => by simp) (fun g v w => by simpa using hinv g v w) hR hw h

omit [Fintype G] in
/-- **If the character is non-trivial the pairing vanishes on the invariants**: the orientation characters must multiply to the (trivial) face orientation. -/
theorem pairing_zero_of_char_ne_one (hε : ∀ g v w, e (ρ g v) (σ g w) = (ε g : ℂ) * e v w) (g₀ : G) (hg₀ : (ε g₀ : ℂ) ≠ 1)
    {v : V} (hv : v ∈ isoSub ρ 1) {w : W} (hw : w ∈ isoSub σ 1) : e v w = 0 := by
  have h := hε g₀ v w
  rw [hv g₀, hw g₀] at h
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h
  have : ((ε g₀ : ℂ) - 1) * e v w = 0 := by linear_combination -h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd (sub_eq_zero.1 h0) hg₀
  · exact h0

/-- The restriction of the pairing to the `χ`-isotypic part of `V` and the `ψ`-isotypic part of `W`. -/
def isoPairing : isoSub ρ χ →ₗ[ℂ] isoSub σ ψ →ₗ[ℂ] ℂ :=
  e.compl₁₂ (isoSub ρ χ).subtype (isoSub σ ψ).subtype

/-- **The descended pairing is perfect** (`χ ψ = ε`, `e` perfect and `ε`-equivariant): left kernel trivial. -/
theorem isoPairing_left (hχψ : ∀ g, (χ g : ℂ) * ψ g = ε g) (hε : ∀ g v w, e (ρ g v) (σ g w) = (ε g : ℂ) * e v w)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (v : isoSub ρ χ) (h : ∀ w, isoPairing (ρ := ρ) (σ := σ) e χ ψ v w = 0) : v = 0 :=
  Subtype.ext (isotypic_left e ε χ ψ hχψ hε hL v.2 fun w hw => h ⟨w, hw⟩)

/-- Right kernel trivial. -/
theorem isoPairing_right (hχψ : ∀ g, (χ g : ℂ) * ψ g = ε g) (hε : ∀ g v w, e (ρ g v) (σ g w) = (ε g : ℂ) * e v w)
    (hR : ∀ w, (∀ v, e v w = 0) → w = 0) (w : isoSub σ ψ) (h : ∀ v, isoPairing (ρ := ρ) (σ := σ) e χ ψ v w = 0) : w = 0 :=
  Subtype.ext (isotypic_right e ε χ ψ hχψ hε hR w.2 fun v hv => h ⟨v, hv⟩)

/-- **The isotypic parts have the same dimension** and the induced maps to the duals are bijective. -/
theorem isoPairing_finrank_eq [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (hχψ : ∀ g, (χ g : ℂ) * ψ g = ε g)
    (hε : ∀ g v w, e (ρ g v) (σ g w) = (ε g : ℂ) * e v w) (hL : ∀ v, (∀ w, e v w = 0) → v = 0)
    (hR : ∀ w, (∀ v, e v w = 0) → w = 0) :
    Module.finrank ℂ (isoSub ρ χ) = Module.finrank ℂ (isoSub σ ψ) := by
  have hi : Function.Injective (isoPairing (ρ := ρ) (σ := σ) e χ ψ) :=
    (injective_iff_map_eq_zero _).2 fun v hv => isoPairing_left e ε χ ψ hχψ hε hL v (fun w => LinearMap.congr_fun hv w)
  have hj : Function.Injective (isoPairing (ρ := ρ) (σ := σ) e χ ψ).flip :=
    (injective_iff_map_eq_zero _).2 fun w hw => isoPairing_right e ε χ ψ hχψ hε hR w (fun v => LinearMap.congr_fun hw v)
  have h1 := LinearMap.finrank_le_finrank_of_injective hi
  have h2 := LinearMap.finrank_le_finrank_of_injective hj
  rw [Subspace.dual_finrank_eq] at h1 h2
  omega

end Pairing

end TernaryPeriodPolynomials.Argument.FaceDescent
