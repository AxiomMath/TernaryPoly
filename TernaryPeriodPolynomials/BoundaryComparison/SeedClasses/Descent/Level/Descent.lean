module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.Bridge
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.FrameChange
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FlagStabilizers
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge

@[expose] public section


/-!
# Degree-two level descent of the mixed cuspidal condition

Paper: Lemma C.3 (`ar:lem:seed`),
 ("the finite reflection projection supplies the full-level statement").

* `resMathlib_injective`: restriction of Mathlib's `H²(·, ρ)` (complex coefficients) to a normal
  subgroup of finite index is injective (from `Statements.LevelTransfer`);
* `EdgeNat.rightHom_nat`: a morphism of split extensions is compatible with the Levi projections;
* `restriction_flag_iff`, `edge_mem_cuspidalFamily_descent`: for an injective morphism `j : E₂ → E₁`
  of split extensions with normal finite-index image and bijective coefficient comparison, a class of
  `H²(E₁, ρ₁)` with zero radical restriction has Hochschild--Serre edge in the cuspidal subspace for
  a family `B` of cusp subgroups of the Levi of `E₁` iff its transport to `E₂` has edge in the
  cuspidal subspace for the preimages `σ⁻¹(B i)`.  The proof goes through the restrictions to the
  stabilizers of the flags (`FlagStabilizers.edge_mem_cuspidalFamily_iff`), which are compared on
  the normal finite-index subgroup `C ⊓ j(E₂)` of the stabilizer `C`; the radical `H¹` is never
  compared, so no splitting of the restriction `H¹(N₁, ρ) → H¹(N₂, ρ)` is needed.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section H2Injective

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  {N S : Subgroup G}

/-- **Restriction of `H²` to a normal finite-index subgroup is injective** (Mathlib's
`groupCohomology`, complex coefficients), from the level transfer. -/
theorem resMathlib_injective (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N)
    [Fintype (S ⧸ N.subgroupOf S)] :
    Function.Injective (LevelTransfer.resMathlib ρ hNS) := by
  intro a b h
  obtain ⟨x, rfl⟩ := (LevelTransfer.bridge ρ S).surjective a
  obtain ⟨y, rfl⟩ := (LevelTransfer.bridge ρ S).surjective b
  have h1 := LevelTransfer.bridge_res ρ hNS x
  have h2 := LevelTransfer.bridge_res ρ hNS y
  have h3 : LevelTransfer.bridge ρ N (LevelTransfer.resH2 ρ hNS x) =
      LevelTransfer.bridge ρ N (LevelTransfer.resH2 ρ hNS y) := by
    rw [← h1, ← h2]; exact h
  have h4 := (LevelTransfer.bridge ρ N).injective h3
  rw [LevelTransfer.resH2_injective ρ hNS hnorm h4]

end H2Injective

namespace EdgeNat

variable {N₁ N₂ E₁ E₂ L₁ L₂ : Type} [Group N₁] [Group N₂] [Group E₁] [Group E₂] [Group L₁]
  [Group L₂] {ext₁ : GroupExtension N₁ E₁ L₁} {ext₂ : GroupExtension N₂ E₂ L₂}
  (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (j : E₂ →* E₁) (σ : L₂ →* L₁) (τ : N₂ →* N₁)
  (hinl : ∀ r, j (ext₂.inl r) = ext₁.inl (τ r)) (hsplit : ∀ m, j (s₂ m) = s₁ (σ m))

include hinl hsplit in
/-- A morphism of split extensions is compatible with the projections to the Levi. -/
theorem rightHom_nat (e : E₂) : ext₁.rightHom (j e) = σ (ext₂.rightHom e) := by
  have hk : e * (s₂ (ext₂.rightHom e))⁻¹ ∈ ext₂.inl.range := by
    rw [ext₂.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv]
    show ext₂.rightHom e * (ext₂.rightHom (s₂ (ext₂.rightHom e)))⁻¹ = 1
    have h0 : ext₂.rightHom (s₂ (ext₂.rightHom e)) = ext₂.rightHom e :=
      s₂.rightInverse_rightHom _
    rw [h0, mul_inv_cancel]
  obtain ⟨r, hr⟩ := hk
  have h : e = ext₂.inl r * s₂ (ext₂.rightHom e) := by rw [hr]; group
  conv_lhs => rw [h]
  rw [map_mul, hinl, hsplit, map_mul, GroupExtension.rightHom_inl, one_mul]
  exact s₁.rightInverse_rightHom _

end EdgeNat

section Descent

variable {N₁ N₂ E₁ E₂ L₁ L₂ : Type} [Group N₁] [Group N₂] [Group E₁] [Group E₂] [Group L₁]
  [Group L₂] {ext₁ : GroupExtension N₁ E₁ L₁} {ext₂ : GroupExtension N₂ E₂ L₂}
  (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (j : E₂ →* E₁) (σ : L₂ →* L₁) (τ : N₂ →* N₁)
  (hinl : ∀ r, j (ext₂.inl r) = ext₁.inl (τ r)) (hsplit : ∀ m, j (s₂ m) = s₁ (σ m))
  (hjinj : Function.Injective j) (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ →ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (j g) v) = ρ₂.ρ g (T v)) (hTb : Function.Bijective T)

include s₁ s₂ τ hinl hsplit hjinj hTb in
/-- The restriction to the preimage of a subgroup of the Levi vanishes iff that of the transported
class does, for a normal finite-index embedding `j`. -/
theorem restriction_flag_iff [j.range.Normal] [j.range.FiniteIndex] (B : Subgroup L₁)
    (y : groupCohomology.H2 ρ₁) :
    twoCohomologyRestriction (LocallyInner.incl ext₁ B) ρ₁ y = 0 ↔
      twoCohomologyRestriction (LocallyInner.incl ext₂ (B.comap σ)) ρ₂
        (EdgeNat.h2Map j ρ₁ ρ₂ T hT y) = 0 := by
  set C : Subgroup E₁ := B.comap ext₁.rightHom with hC
  set K : Subgroup E₂ := (B.comap σ).comap ext₂.rightHom with hK
  set N' : Subgroup E₁ := C ⊓ j.range with hN'
  have hNS : N' ≤ C := inf_le_left
  have hKmem : ∀ k : K, j k ∈ N' := by
    intro k
    refine ⟨?_, ⟨k, rfl⟩⟩
    change ext₁.rightHom (j k) ∈ B
    rw [EdgeNat.rightHom_nat s₁ s₂ j σ τ hinl hsplit]
    exact k.2
  let κ : K →* N' := (j.comp K.subtype).codRestrict N' hKmem
  have hκ : ∀ k : K, j (K.subtype k) = N'.subtype (κ k) := fun k => rfl
  have hκb : Function.Bijective κ := by
    constructor
    · intro a b h
      exact Subtype.ext (hjinj (congrArg Subtype.val h))
    · rintro ⟨x, hxC, e, rfl⟩
      refine ⟨⟨e, ?_⟩, rfl⟩
      change σ (ext₂.rightHom e) ∈ B
      rw [← EdgeNat.rightHom_nat s₁ s₂ j σ τ hinl hsplit]
      exact hxC
  have step2 := EdgeNat.restriction_h2Map_eq_zero_iff j ρ₁ ρ₂ T hT N'.subtype K.subtype κ hκ hκb
    hTb y
  refine Iff.trans ?_ step2.symm
  have hfin : (N'.subgroupOf C).FiniteIndex := by
    rw [hN', Subgroup.inf_subgroupOf_left]; infer_instance
  let _ : Fintype (C ⧸ N'.subgroupOf C) := Subgroup.fintypeQuotientOfFiniteIndex
  have hnorm : ∀ s ∈ C, ∀ n ∈ N', s⁻¹ * n * s ∈ N' := by
    intro s hs n hn
    refine ⟨C.mul_mem (C.mul_mem (C.inv_mem hs) hn.1) hs, ?_⟩
    have := (inferInstance : j.range.Normal).conj_mem n hn.2 s⁻¹
    simpa using this
  have hinj := resMathlib_injective ρ₁.ρ hNS hnorm
  have hfun : twoCohomologyRestriction N'.subtype ρ₁ y =
      LevelTransfer.resMathlib ρ₁.ρ hNS (twoCohomologyRestriction C.subtype ρ₁ y) := by
    obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective ρ₁ y
    rw [twoCohomologyRestriction_apply, twoCohomologyRestriction_apply]
    change _ = (groupCohomology.map (Subgroup.inclusion hNS) (LevelTransfer.resRep ρ₁.ρ hNS) 2).hom
      (groupCohomology.H2π _ _)
    rw [groupCohomology.H2π_comp_map_apply]
    congr 1
  constructor
  · intro h0
    rw [hfun, h0, map_zero]
  · intro h0
    apply hinj
    rw [map_zero, ← hfun]
    exact h0

include s₁ s₂ τ hinl hsplit hjinj hTb in
/-- **Level descent of the mixed cuspidal condition (degree two).** Let `j : E₂ → E₁` be an
injective morphism of split extensions with normal finite-index image and bijective coefficient
comparison `T`.  Suppose the cusp subgroups `B i` of the Levi of `E₁` and their preimages under the
Levi map `σ` have vanishing `H²`.  Then a class `y ∈ H²(E₁, ρ₁)` with zero radical restriction has
Hochschild--Serre edge in the cuspidal subspace for `B` iff its transport to `E₂` has edge in the
cuspidal subspace for the preimages `σ⁻¹(B i)`. -/
theorem edge_mem_cuspidalFamily_descent [j.range.Normal] [j.range.FiniteIndex] {ι : Type}
    (B : ι → Subgroup L₁)
    (hB₁ : ∀ i (V : Rep ℂ (B i)) (x : groupCohomology.H2 V), x = 0)
    (hB₂ : ∀ i (V : Rep ℂ ((B i).comap σ)) (x : groupCohomology.H2 V), x = 0)
    (y : groupCohomology.H2 ρ₁) (hy : twoCohomologyRestriction ext₁.inl ρ₁ y = 0) :
    splitCohomologyEdge s₁ ρ₁ ⟨y, hy⟩ ∈ cuspidalFamily B (splitRadicalH1Representation s₁ ρ₁) ↔
      splitCohomologyEdge s₂ ρ₂ (EdgeNat.kerMap j τ hinl ρ₁ ρ₂ T hT ⟨y, hy⟩) ∈
        cuspidalFamily (fun i => (B i).comap σ) (splitRadicalH1Representation s₂ ρ₂) := by
  rw [LocallyInner.edge_mem_cuspidalFamily_iff s₁ ρ₁ B hB₁ y hy]
  have h2 := LocallyInner.edge_mem_cuspidalFamily_iff s₂ ρ₂ (fun i => (B i).comap σ) hB₂
    (EdgeNat.h2Map j ρ₁ ρ₂ T hT y) (EdgeNat.h2Map_ker j τ hinl ρ₁ ρ₂ T hT y hy)
  have h3 : EdgeNat.kerMap j τ hinl ρ₁ ρ₂ T hT ⟨y, hy⟩ =
      ⟨EdgeNat.h2Map j ρ₁ ρ₂ T hT y, EdgeNat.h2Map_ker j τ hinl ρ₁ ρ₂ T hT y hy⟩ := rfl
  rw [h3, h2]
  exact forall_congr' fun i => restriction_flag_iff s₁ s₂ j σ τ hinl hsplit hjinj ρ₁ ρ₂ T hT hTb
    (B i) y

end Descent

end TernaryPeriodPolynomials.Argument.SeedC3S4c
