module

public import Mathlib

@[expose] public section


/-!
# Fibres of the passage between the faces of `Γ(M)` and `Γ(N)`: group-theoretic counting

Formalized by Claude Sonnet 5.5.

For a group `G`, subgroups `B` (the stabilizer of the cusp type) and normal finite-index subgroups `Γ' ≤ Γ`, the faces are the orbits `h ~ q h γ` (`q ∈ B`, `γ ∈ Γ`), i.e. the `B`-orbits on `G/Γ`.
`face_sum`: for a function `Φ` on the faces of `Γ`,
`[B ∩ Γ : B ∩ Γ'] · ∑_{faces of Γ'} Φ(image) = [Γ : Γ'] · ∑_{faces of Γ} Φ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceFibre

theorem sum_fibre {X Y : Type} [Fintype X] [Fintype Y] (p : X → Y) (n : ℕ)
    (hp : ∀ y, Nat.card {x // p x = y} = n) (g : Y → ℂ) :
    ∑ x, g (p x) = n * ∑ y, g y := by
  classical
  have h1 : ∀ y, ∑ x ∈ Finset.univ.filter (fun x => p x = y), g (p x) = n * g y := by
    intro y
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2] :
      ∀ x ∈ Finset.univ.filter (fun x => p x = y), g (p x) = g y), Finset.sum_const, nsmul_eq_mul]
    congr 1
    have := hp y
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    exact_mod_cast this
  rw [← Finset.sum_fiberwise Finset.univ p (fun x => g (p x))]
  simp_rw [h1]
  rw [Finset.mul_sum]

variable {G : Type} [Group G]

theorem ncard_orbit_quot (S Δ : Subgroup G) [Δ.Normal] (g : G) :
    (MulAction.orbit S (QuotientGroup.mk g : G ⧸ Δ)).ncard = Δ.relIndex S := by
  rw [← MulAction.index_stabilizer]
  have : MulAction.stabilizer S (QuotientGroup.mk g : G ⧸ Δ) = Δ.subgroupOf S := by
    ext q
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk (q.1 * g) : G ⧸ Δ) = QuotientGroup.mk g ↔ _
    rw [QuotientGroup.eq]
    have e : (q.1 * g)⁻¹ * g = g⁻¹ * q.1⁻¹ * g := by group
    rw [e]
    constructor
    · intro h
      have := (inferInstance : Δ.Normal).conj_mem _ h g
      have e2 : g * (g⁻¹ * q.1⁻¹ * g) * g⁻¹ = q.1⁻¹ := by group
      rw [e2] at this
      simpa using Δ.inv_mem this
    · intro h
      have := (inferInstance : Δ.Normal).conj_mem _ (Δ.inv_mem h) g⁻¹
      simpa using this
  rw [this]
  rfl



section Faces

variable (B Γ Γ' : Subgroup G) [Γ.Normal] [Γ'.Normal]

omit [Γ'.Normal] in
/-- The fibres of `G/Γ' → G/Γ` are the `Γ`-orbits. -/
theorem fibre_quot (hle : Γ' ≤ Γ) (g : G) :
    {x : G ⧸ Γ' | Subgroup.quotientMapOfLE hle x = QuotientGroup.mk g} =
      MulAction.orbit Γ (QuotientGroup.mk g : G ⧸ Γ') := by
  ext x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [Set.mem_ofPred_eq, Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq,
    MulAction.mem_orbit_iff]
  constructor
  · intro h
    have h1 : a * g⁻¹ ∈ Γ := by
      have h' : g⁻¹ * a ∈ Γ := by simpa using Γ.inv_mem h
      have := (inferInstance : Γ.Normal).conj_mem _ h' g
      have e : g * (g⁻¹ * a) * g⁻¹ = a * g⁻¹ := by group
      rwa [e] at this
    refine ⟨⟨a * g⁻¹, h1⟩, ?_⟩
    change (QuotientGroup.mk (a * g⁻¹ * g) : G ⧸ Γ') = _
    congr 1
    group
  · rintro ⟨γ, hγ⟩
    change (QuotientGroup.mk (γ.1 * g) : G ⧸ Γ') = _ at hγ
    have h1 := hle (QuotientGroup.eq.mp hγ)
    have e : g⁻¹ * a = (g⁻¹ * γ.1 * g) * ((γ.1 * g)⁻¹ * a) := by group
    have key : g⁻¹ * a ∈ Γ := by
      rw [e]
      refine Γ.mul_mem ?_ h1
      have := (inferInstance : Γ.Normal).conj_mem _ γ.2 g⁻¹
      simpa [mul_assoc] using this
    simpa using Γ.inv_mem key

omit [Γ.Normal] in
/-- The fibres of `G/Γ → faces` are the `B`-orbits. -/
theorem fibre_face {F : Type} (s : G → F)
    (hs : ∀ a b, s a = s b ↔ ∃ q ∈ B, ∃ γ ∈ Γ, b = q * a * γ)
    (σ : G ⧸ Γ → F) (hσ : ∀ a, σ (QuotientGroup.mk a) = s a) (h : G) :
    {x : G ⧸ Γ | σ x = s h} = MulAction.orbit B (QuotientGroup.mk h : G ⧸ Γ) := by
  ext x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [Set.mem_ofPred_eq, hσ, MulAction.mem_orbit_iff]
  rw [eq_comm, hs]
  constructor
  · rintro ⟨q, hq, γ, hγ, rfl⟩
    refine ⟨⟨q, hq⟩, ?_⟩
    change (QuotientGroup.mk (q * h) : G ⧸ Γ) = _
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hγ
  · rintro ⟨q, hq⟩
    change (QuotientGroup.mk (q.1 * h) : G ⧸ Γ) = _ at hq
    refine ⟨q.1, q.2, (q.1 * h)⁻¹ * a, QuotientGroup.eq.mp hq, by group⟩

theorem card_fibre_eq {X Y : Type} (f : X → Y) (y : Y) (S : Set X) (hS : {x | f x = y} = S) :
    Nat.card {x // f x = y} = S.ncard := by
  rw [← hS]
  exact Nat.card_coe_set_eq _

/-- **Regrouping the faces of `Γ'` over the faces of `Γ`.** -/
theorem face_sum [Γ.FiniteIndex] [Γ'.FiniteIndex] (hle : Γ' ≤ Γ) {F F' : Type} [Fintype F] [Fintype F']
    (s : G → F) (s' : G → F')
    (hs : ∀ a b, s a = s b ↔ ∃ q ∈ B, ∃ γ ∈ Γ, b = q * a * γ)
    (hs' : ∀ a b, s' a = s' b ↔ ∃ q ∈ B, ∃ γ ∈ Γ', b = q * a * γ)
    (hsurj : Function.Surjective s) (hsurj' : Function.Surjective s')
    (π : F' → F) (hπ : ∀ h, π (s' h) = s h) (Φ : F → ℂ) :
    (((Γ' ⊓ B).relIndex (Γ ⊓ B) : ℕ) : ℂ) * ∑ i, Φ (π i) = ((Γ'.relIndex Γ : ℕ) : ℂ) * ∑ j, Φ j := by
  classical
  let _ : Fintype (G ⧸ Γ) := Fintype.ofFinite _
  let _ : Fintype (G ⧸ Γ') := Fintype.ofFinite _
  let σ : G ⧸ Γ → F := Quotient.lift s (fun a b hab =>
    (hs a b).2 ⟨1, B.one_mem, a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩)
  let σ' : G ⧸ Γ' → F' := Quotient.lift s' (fun a b hab =>
    (hs' a b).2 ⟨1, B.one_mem, a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩)
  have hσ : ∀ a, σ (QuotientGroup.mk a) = s a := fun _ => rfl
  have hσ' : ∀ a, σ' (QuotientGroup.mk a) = s' a := fun _ => rfl
  have cσ : ∀ i, Nat.card {x // σ x = i} = Γ.relIndex B := by
    intro i
    obtain ⟨h, rfl⟩ := hsurj i
    rw [card_fibre_eq σ _ _ (fibre_face B Γ s hs σ hσ h)]
    exact ncard_orbit_quot B Γ h
  have cσ' : ∀ i, Nat.card {x // σ' x = i} = Γ'.relIndex B := by
    intro i
    obtain ⟨h, rfl⟩ := hsurj' i
    rw [card_fibre_eq σ' _ _ (fibre_face B Γ' s' hs' σ' hσ' h)]
    exact ncard_orbit_quot B Γ' h
  have cp : ∀ y, Nat.card {x // Subgroup.quotientMapOfLE hle x = y} = Γ'.relIndex Γ := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [card_fibre_eq _ _ _ (fibre_quot Γ Γ' hle g)]
    exact ncard_orbit_quot Γ Γ' g
  have compat : ∀ x, π (σ' x) = σ (Subgroup.quotientMapOfLE hle x) := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hσ', Subgroup.quotientMapOfLE_apply_mk, hσ, hπ]
  have h1 := sum_fibre σ' (Γ'.relIndex B) cσ' (fun i => Φ (π i))
  have h2 := sum_fibre (Subgroup.quotientMapOfLE hle) (Γ'.relIndex Γ) cp (fun y => Φ (σ y))
  have h3 := sum_fibre σ (Γ.relIndex B) cσ Φ
  simp_rw [compat] at h1
  have hmul : (Γ' ⊓ B).relIndex (Γ ⊓ B) * Γ.relIndex B = Γ'.relIndex B := by
    have := Subgroup.relIndex_mul_relIndex (Γ' ⊓ B) (Γ ⊓ B) B (inf_le_inf_right B hle) inf_le_right
    rwa [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at this
  have hb : Γ.relIndex B ≠ 0 := by
    have : Γ.IsFiniteRelIndex B := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  have key : (Γ.relIndex B : ℂ) * ((((Γ' ⊓ B).relIndex (Γ ⊓ B) : ℕ) : ℂ) * ∑ i, Φ (π i)) =
      (Γ.relIndex B : ℂ) * (((Γ'.relIndex Γ : ℕ) : ℂ) * ∑ j, Φ j) := by
    have e : ((Γ'.relIndex B : ℕ) : ℂ) = ((Γ' ⊓ B).relIndex (Γ ⊓ B) : ℂ) * (Γ.relIndex B : ℂ) := by
      rw [← hmul]; push_cast; ring
    have h4 : ((Γ'.relIndex B : ℕ) : ℂ) * ∑ i, Φ (π i) =
        ((Γ'.relIndex Γ : ℕ) : ℂ) * ((Γ.relIndex B : ℕ) * ∑ j, Φ j) := by
      rw [← h1, h2, h3]
    rw [e] at h4
    linear_combination h4
  exact mul_left_cancel₀ (by exact_mod_cast hb) key

end Faces

end TernaryPeriodPolynomials.Argument.FaceFibre
