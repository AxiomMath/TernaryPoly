module

public import Mathlib

@[expose] public section


/-!
# Separation of Hecke eigencharacters by a polynomial projector (pure linear algebra)

Let `V` be a complex vector space, `W ⊆ V` a submodule, `𝒯 j : V →ₗ V` (`j ∈ J`) operators preserving `W`, and
`v i ∈ V` (`i ∈ S`, `S` finite) eigenvectors, `𝒯 j (v i) = ch i j • v i`.  If `∑_{i ∈ S} v i ∈ W`, then for every
`i₀` the partial sum over the eigencharacter class `{i ∈ S | ch i = ch i₀}` lies in `W` (`cluster_mem`).

Proof: for each character `ψ ≠ ch i₀` among the finitely many occurring, choose `j_ψ` with `ψ j_ψ ≠ ch i₀ j_ψ` and
put `A_ψ = (ch i₀ j_ψ - ψ j_ψ)⁻¹ • (𝒯 j_ψ - ψ j_ψ)`.  Each `A_ψ` acts on every eigenvector `v i` by a scalar, which is `1`
for `ch i = ch i₀` and `0` for `ch i = ψ`; the product `Q` of the `A_ψ` therefore fixes the class of `i₀` and kills
every other eigenvector, while preserving `W` as a composite of operators preserving `W`.  No spectral theory,
no isotypical-projector existence theorem is used (this replaces the `PortedAssociateProjector` input of
`clustered_vanishing`).

`sum_eq_zero_of_classwise_zero'`: if all character-class partial sums of a finite family vanish, so does the total.

Formalized by Claude Sonnet 5.5.
-/

open scoped BigOperators

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries

section Cluster

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ι J : Type*}

/-- A product of operators acting by scalars on a vector acts by the product of the scalars. -/
theorem list_prod_apply_of_scalars {κ : Type*} (v : V) (A : κ → Module.End ℂ V) (s : κ → ℂ) :
    ∀ l : List κ, (∀ ψ ∈ l, A ψ v = s ψ • v) → (l.map A).prod v = (l.map s).prod • v := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons ψ l ih =>
    intro h
    have hA : A ψ v = s ψ • v := h ψ (by simp)
    have hL := ih (fun ψ' hψ' => h ψ' (by simp [hψ']))
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, hL, map_smul, hA,
      smul_smul, mul_comm]

/-- A product of operators preserving a submodule preserves it. -/
theorem list_prod_mem {κ : Type*} (W : Submodule ℂ V) (A : κ → Module.End ℂ V)
    (h : ∀ ψ, ∀ x ∈ W, A ψ x ∈ W) :
    ∀ l : List κ, ∀ x ∈ W, (l.map A).prod x ∈ W := by
  intro l
  induction l with
  | nil => intro x hx; simpa using hx
  | cons ψ l ih =>
    intro x hx
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact h ψ _ (ih x hx)

open Classical in
/-- **Character classes of a sum in a stable submodule stay in it.** -/
theorem cluster_mem (W : Submodule ℂ V) (𝒯 : J → Module.End ℂ V) (hW : ∀ j, ∀ x ∈ W, 𝒯 j x ∈ W)
    (S : Finset ι) (v : ι → V) (ch : ι → J → ℂ) (heig : ∀ i ∈ S, ∀ j, 𝒯 j (v i) = ch i j • v i)
    (hsum : ∑ i ∈ S, v i ∈ W) (i₀ : ι) :
    ∑ i ∈ S.filter (fun i => ch i = ch i₀), v i ∈ W := by
  by_cases hJ : Nonempty J
  swap
  · have hall : S.filter (fun i => ch i = ch i₀) = S := by
      apply Finset.filter_true_of_mem
      intro i _
      funext j
      exact (hJ ⟨j⟩).elim
    rw [hall]
    exact hsum
  -- the other characters occurring
  set Ψ : Finset (J → ℂ) := (S.image ch).erase (ch i₀) with hΨ
  -- separating operators
  have hsep : ∀ ψ ∈ Ψ, ∃ j, ψ j ≠ ch i₀ j := by
    intro ψ hψ
    by_contra h
    push Not at h
    exact (Finset.mem_erase.mp hψ).1 (funext h)
  choose! jψ hjψ using hsep
  let a : (J → ℂ) → ℂ := fun ψ => (ch i₀ (jψ ψ) - ψ (jψ ψ))⁻¹
  let A : (J → ℂ) → Module.End ℂ V := fun ψ => a ψ • (𝒯 (jψ ψ) - ψ (jψ ψ) • (1 : Module.End ℂ V))
  let sc : (J → ℂ) → ι → ℂ := fun ψ i => a ψ * (ch i (jψ ψ) - ψ (jψ ψ))
  have hA : ∀ ψ ∈ Ψ, ∀ i ∈ S, A ψ (v i) = sc ψ i • v i := by
    intro ψ hψ i hi
    simp only [A, sc, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, heig i hi, ← sub_smul,
      smul_smul]
  have hAW : ∀ ψ, ∀ x ∈ W, A ψ x ∈ W := by
    intro ψ x hx
    simp only [A, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact W.smul_mem _ (W.sub_mem (hW _ x hx) (W.smul_mem _ hx))
  set L := Ψ.toList with hL
  have hQ : ∀ i ∈ S, (L.map A).prod (v i) = (L.map (fun ψ => sc ψ i)).prod • v i := by
    intro i hi
    refine list_prod_apply_of_scalars (v i) A (fun ψ => sc ψ i) L (fun ψ hψ => ?_)
    exact hA ψ (Finset.mem_toList.mp hψ) i hi
  have hsum' : (L.map A).prod (∑ i ∈ S, v i) = ∑ i ∈ S.filter (fun i => ch i = ch i₀), v i := by
    rw [map_sum, ← Finset.sum_filter_add_sum_filter_not S (fun i => ch i = ch i₀)]
    have h1 : ∑ i ∈ S.filter (fun i => ch i = ch i₀), (L.map A).prod (v i) =
        ∑ i ∈ S.filter (fun i => ch i = ch i₀), v i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hQ i hi.1]
      have : (L.map (fun ψ => sc ψ i)).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hx
        have hψΨ := Finset.mem_toList.mp hψ
        simp only [sc, hi.2]
        have hne : ch i₀ (jψ ψ) - ψ (jψ ψ) ≠ 0 := sub_ne_zero.mpr (hjψ ψ hψΨ).symm
        simp only [a]
        exact inv_mul_cancel₀ hne
      rw [this, one_smul]
    have h2 : ∑ i ∈ S.filter (fun i => ¬ ch i = ch i₀), (L.map A).prod (v i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hQ i hi.1]
      have hmem : ch i ∈ Ψ := by
        rw [hΨ, Finset.mem_erase]
        exact ⟨hi.2, Finset.mem_image_of_mem _ hi.1⟩
      have : (L.map (fun ψ => sc ψ i)).prod = 0 := by
        apply List.prod_eq_zero
        refine List.mem_map.mpr ⟨ch i, Finset.mem_toList.mpr hmem, ?_⟩
        simp [sc]
      rw [this, zero_smul]
    rw [h1, h2, add_zero]
  rw [← hsum']
  exact list_prod_mem W A hAW L _ hsum

/-- Fiberwise vanishing implies total vanishing. -/
theorem sum_eq_zero_of_classwise_zero' {M κ : Type*} [AddCommMonoid M] [DecidableEq κ] (S : Finset ι)
    (ch : ι → κ) (h : ι → M)
    (hclass : ∀ i₀ ∈ S, ∑ i ∈ S.filter (fun i => ch i = ch i₀), h i = 0) : ∑ i ∈ S, h i = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image ch) (g := ch)
    (fun i hi => Finset.mem_image_of_mem _ hi)]
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hk
  exact hclass i₀ hi₀

end Cluster

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
