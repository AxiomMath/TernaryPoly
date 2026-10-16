module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.Descent

@[expose] public section


/-!
# Level descent including the radical condition

Paper: Lemma C.3 (`ar:lem:seed`).

* `radical_zero_of_flag`: a class of `H²(E, ρ)` vanishing on the preimage `E_B` of one subgroup `B` of
  the Levi has zero radical restriction (the radical lies in `E_B`).
* `CuspH2`: the classes with zero radical restriction and Hochschild--Serre edge in the cuspidal
  subspace for a family `B` of cusp subgroups; `cuspH2_iff_flags`: this is the vanishing on all flag
  stabilizers `E_{B i}` (for `Nonempty` families with `H²(B i, ·) = 0`).
* `cuspH2_descent`: level descent of `CuspH2` along an injective morphism of split extensions with
  normal finite-index image, **with no hypothesis on the radical restriction**.  The converse
  radical-restriction statement (zero radical restriction of the restriction to the small group
  implies that of the class) therefore needs no separate injectivity of
  `H²(ℤ², E) → H²(Nℤ², E)`: it is a consequence of vanishing on the flag stabilizers.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

namespace LocallyInner

variable {N E L : Type} [Group N] [Group E] [Group L] {ext : GroupExtension N E L}
  (ρ : Rep ℂ E) (B : Subgroup L)

/-- A class vanishing on the preimage of a subgroup of the Levi vanishes on the radical. -/
theorem radical_zero_of_flag (y : groupCohomology.H2 ρ)
    (h : twoCohomologyRestriction (incl ext B) ρ y = 0) :
    twoCohomologyRestriction ext.inl ρ y = 0 := by
  have e1 : EdgeNat.h2Map (incl ext B) ρ (resRep ext ρ B) LinearMap.id (hT ρ B) y =
      twoCohomologyRestriction (incl ext B) ρ y := by
    obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective ρ y
    rw [twoCohomologyRestriction_apply]
    rw [EdgeNat.h2Map_π]
    rfl
  have e2 := EdgeNat.restriction_h2Map (incl ext B) ρ (resRep ext ρ B) LinearMap.id (hT ρ B)
    ext.inl (extRestrict ext B).inl (MonoidHom.id N) (hinl ext B) y
  rw [e1, h, map_zero] at e2
  have hinj := EdgeNat.h2Map_injective (MonoidHom.id N) (Rep.res ext.inl ρ)
    (Rep.res (extRestrict ext B).inl (resRep ext ρ B)) LinearMap.id
    (EdgeNat.hT_res (incl ext B) ρ (resRep ext ρ B) LinearMap.id (hT ρ B) ext.inl
      (extRestrict ext B).inl (MonoidHom.id N) (hinl ext B))
    Function.bijective_id Function.bijective_id
  apply hinj
  rw [map_zero]
  exact e2.symm

/-- The classes of `H²(E, ρ)` with zero radical restriction whose Hochschild--Serre edge lies in the
cuspidal subspace for the family `B` of cusp subgroups of the Levi. -/
def CuspH2 (s : ext.Splitting) {ι : Type} (B : ι → Subgroup L) (y : groupCohomology.H2 ρ) : Prop :=
  ∃ hy : twoCohomologyRestriction ext.inl ρ y = 0,
    splitCohomologyEdge s ρ ⟨y, hy⟩ ∈ cuspidalFamily B (splitRadicalH1Representation s ρ)

/-- **`CuspH2` is vanishing on the flag stabilizers**, with no hypothesis on the radical. -/
theorem cuspH2_iff_flags (s : ext.Splitting) {ι : Type} [Nonempty ι] (B : ι → Subgroup L)
    (hB : ∀ i (V : Rep ℂ (B i)) (x : groupCohomology.H2 V), x = 0) (y : groupCohomology.H2 ρ) :
    CuspH2 ρ s B y ↔ ∀ i, twoCohomologyRestriction (incl ext (B i)) ρ y = 0 := by
  constructor
  · rintro ⟨hy, h⟩
    exact (edge_mem_cuspidalFamily_iff s ρ B hB y hy).mp h
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hy := radical_zero_of_flag ρ (B i) y (h i)
    exact ⟨hy, (edge_mem_cuspidalFamily_iff s ρ B hB y hy).mpr h⟩

end LocallyInner

section Descent2

open LocallyInner

variable {N₁ N₂ E₁ E₂ L₁ L₂ : Type} [Group N₁] [Group N₂] [Group E₁] [Group E₂] [Group L₁]
  [Group L₂] {ext₁ : GroupExtension N₁ E₁ L₁} {ext₂ : GroupExtension N₂ E₂ L₂}
  (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (j : E₂ →* E₁) (σ : L₂ →* L₁) (τ : N₂ →* N₁)
  (hinl : ∀ r, j (ext₂.inl r) = ext₁.inl (τ r)) (hsplit : ∀ m, j (s₂ m) = s₁ (σ m))
  (hjinj : Function.Injective j) (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ →ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (j g) v) = ρ₂.ρ g (T v)) (hTb : Function.Bijective T)

include s₁ s₂ τ hinl hsplit hjinj hTb in
/-- **Degree-two level descent of the mixed cuspidal classes, including the radical condition.**
Under the hypotheses of `edge_mem_cuspidalFamily_descent`, a class `y` of `H²(E₁, ρ₁)` is in
`CuspH2` for the family `B` iff its transport is in `CuspH2` for the preimages `σ⁻¹(B i)`.  No
hypothesis on the radical restriction of `y` is needed: it is implied by the vanishing on the flag
stabilizers. -/
theorem cuspH2_descent [j.range.Normal] [j.range.FiniteIndex] {ι : Type} [Nonempty ι]
    (B : ι → Subgroup L₁)
    (hB₁ : ∀ i (V : Rep ℂ (B i)) (x : groupCohomology.H2 V), x = 0)
    (hB₂ : ∀ i (V : Rep ℂ ((B i).comap σ)) (x : groupCohomology.H2 V), x = 0)
    (y : groupCohomology.H2 ρ₁) :
    CuspH2 ρ₁ s₁ B y ↔
      CuspH2 ρ₂ s₂ (fun i => (B i).comap σ) (EdgeNat.h2Map j ρ₁ ρ₂ T hT y) := by
  rw [cuspH2_iff_flags ρ₁ s₁ B hB₁, cuspH2_iff_flags ρ₂ s₂ (fun i => (B i).comap σ) hB₂]
  exact forall_congr' fun i => restriction_flag_iff s₁ s₂ j σ τ hinl hsplit hjinj ρ₁ ρ₂ T hT hTb
    (B i) y

end Descent2

end TernaryPeriodPolynomials.Argument.SeedC3S4c
