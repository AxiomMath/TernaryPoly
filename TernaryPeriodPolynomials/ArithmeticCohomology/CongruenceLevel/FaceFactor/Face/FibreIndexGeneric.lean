module

public import Mathlib

@[expose] public section


/-!
# The index of a subgroup of a split extension

Formalized by Claude Sonnet 5.5.

`index_split`: for a split extension `R → E → L` and a subgroup `E'` of `E` with `E' ≤ rightHom⁻¹ L'`, containing the Levi section of `L'`, and meeting the radical `R` in `S`, one has `[E : E'] = [L : L'] · [R : S]`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceFibre

variable {R E L : Type} [Group R] [Group E] [Group L]

theorem index_split (ext : GroupExtension R E L) (s : ext.Splitting) (E' : Subgroup E) (L' : Subgroup L)
    (S : Subgroup R) (h1 : ∀ l ∈ L', s l ∈ E') (h2 : ∀ e ∈ E', ext.rightHom e ∈ L')
    (h3 : ∀ r, ext.inl r ∈ E' ↔ r ∈ S) : E'.index = L'.index * S.index := by
  let K1 : Subgroup E := L'.comap ext.rightHom
  have hle : E' ≤ K1 := fun e he => h2 e he
  have hK1 : K1.index = L'.index := Subgroup.index_comap_of_surjective _ ext.rightHom_surjective
  have hrel : E'.relIndex K1 = S.index := by
    let f : R →* K1 := ext.inl.codRestrict K1 (fun r => by
      show ext.rightHom (ext.inl r) ∈ L'
      rw [GroupExtension.rightHom_inl]; exact L'.one_mem)
    have hf : ∀ a b : R, (f a)⁻¹ * f b ∈ E'.subgroupOf K1 ↔ a⁻¹ * b ∈ S := by
      intro a b
      rw [Subgroup.mem_subgroupOf, ← h3]
      simp [f]
    let g : R ⧸ S → K1 ⧸ E'.subgroupOf K1 := Quotient.map' f (fun a b hab => by
      have := (hf a b).2 (QuotientGroup.leftRel_apply.mp hab)
      exact QuotientGroup.leftRel_apply.mpr this)
    have hg : Function.Bijective g := by
      constructor
      · intro x y hxy
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        have : (QuotientGroup.mk (f a) : K1 ⧸ E'.subgroupOf K1) = QuotientGroup.mk (f b) := hxy
        rw [QuotientGroup.eq, hf] at this
        exact QuotientGroup.eq.mpr this
      · intro y
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
        have hk : ext.rightHom (k.1 * (s (ext.rightHom k.1))⁻¹) = 1 := by
          have e1 : ext.rightHom (s (ext.rightHom k.1)) = ext.rightHom k.1 := s.rightInverse_rightHom _
          rw [map_mul, map_inv, e1]; simp
        have hmem : k.1 * (s (ext.rightHom k.1))⁻¹ ∈ ext.inl.range := by
          rw [ext.range_inl_eq_ker_rightHom]; exact hk
        obtain ⟨r, hr⟩ := hmem
        refine ⟨QuotientGroup.mk r, ?_⟩
        show (QuotientGroup.mk (f r) : K1 ⧸ E'.subgroupOf K1) = QuotientGroup.mk k
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have e : ((f r)⁻¹ * k).1 = s (ext.rightHom k.1) := by
          have : (f r).1 = ext.inl r := rfl
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, this, hr]
          group
        rw [e]
        exact h1 _ k.2
    unfold Subgroup.relIndex Subgroup.index
    exact (Nat.card_congr (Equiv.ofBijective g hg)).symm
  rw [← Subgroup.relIndex_mul_index hle, hrel, hK1, mul_comm]

end TernaryPeriodPolynomials.Argument.FaceFibre
