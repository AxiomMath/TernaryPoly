module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.TwoGenerator

@[expose] public section


/-!
# Parabolic `H¹` of a reflection extension of a two-generator group

Let `G = ⟨T, L, ε⟩` with `E = T L⁻¹` of order dividing three and an involution `ε` inverting
`T` and `L` (`εTε = T⁻¹`, `εLε = L⁻¹`); e.g. `Γ₁'(3) = Γ₁(3) ⋊ ⟨diag(-1,1)⟩`. Put `σ = L ε` (an
involution with `σ E σ = E⁻¹`) and `K = ker (1 + E + E²)`, `K⁻ = K ∩ ker (σ + 1)`.

* `finrank_Kminus_add_le`: `2 dim K⁻ ≤ dim K` (`v ↦ Ev - E²v` embeds `K⁻` into `K⁺`);
* `finrank_parabolicH1_reflection_le`: if `V^T ∩ V^L = 0`, then
  `dim H¹_par(G, V) + dim (V^T ∩ V^ε) ≤ dim ((L - 1)V ∩ K⁻)`.

Together these give the Eichler–Shimura value `dim S_k(Γ₁(3))` (one eigenspace of the reflection)
as an upper bound for the parabolic cohomology of `Γ₁'(3)` (`SharpBounds`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.ReflectionBound

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TwoGenerator Module

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The `-1`-eigenspace of one element. -/
def antiFixed (g : G) : Submodule ℂ V := LinearMap.ker (ρ g + 1)

theorem mem_antiFixed {g : G} {v : V} : v ∈ antiFixed ρ g ↔ ρ g v = -v := by
  simp [antiFixed, add_eq_zero_iff_eq_neg]

variable {ρ}

theorem rho_mul_apply (g h : G) (v : V) : ρ (g * h) v = ρ g (ρ h v) := by
  rw [map_mul, Module.End.mul_apply]

section Relations

variable {T L ε : G}

theorem sigma_sq (hεL : ε * L * ε = L⁻¹) : L * ε * (L * ε) = 1 := by
  calc L * ε * (L * ε) = L * (ε * L * ε) := by group
    _ = 1 := by rw [hεL, mul_inv_cancel]

theorem sigma_mul_elliptic (hεT : ε * T * ε = T⁻¹) (hεL : ε * L * ε = L⁻¹)
    (cube : (T * L⁻¹) ^ 3 = 1) :
    L * ε * (T * L⁻¹) = (T * L⁻¹) * (T * L⁻¹) * (L * ε) := by
  have hsq := sigma_sq hεL
  -- σ E σ = E⁻¹ = E², hence σ E = E² σ
  have conj : L * ε * (T * L⁻¹) * (L * ε) = (T * L⁻¹)⁻¹ := by
    calc L * ε * (T * L⁻¹) * (L * ε) = L * (ε * T * ε) := by group
      _ = (T * L⁻¹)⁻¹ := by rw [hεT]; group
  have inverse : (T * L⁻¹)⁻¹ = (T * L⁻¹) * (T * L⁻¹) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ', cube]
  calc L * ε * (T * L⁻¹) = L * ε * (T * L⁻¹) * (L * ε) * (L * ε) := by
        rw [mul_assoc (L * ε * (T * L⁻¹)), hsq, mul_one]
    _ = (T * L⁻¹) * (T * L⁻¹) * (L * ε) := by rw [conj, inverse]

end Relations

section Halving

variable {T L ε : G}

/-- `K = ker (1 + E + E²)`. -/
abbrev kernelE (T L : G) : Submodule ℂ V := LinearMap.ker (norm3 ρ (T * L⁻¹))

/-- `K⁻ = K ∩ ker (σ + 1)`, `σ = L ε`. -/
abbrev kernelMinus (T L ε : G) : Submodule ℂ V := kernelE (ρ := ρ) T L ⊓ antiFixed ρ (L * ε)

/-- `K⁺ = K ∩ ker (σ - 1)`. -/
abbrev kernelPlus (T L ε : G) : Submodule ℂ V := kernelE (ρ := ρ) T L ⊓ fixed ρ (L * ε)

variable (hεT : ε * T * ε = T⁻¹) (hεL : ε * L * ε = L⁻¹) (cube : (T * L⁻¹) ^ 3 = 1)
include hεT hεL cube

theorem sigma_elliptic_apply (v : V) :
    ρ (L * ε) (ρ (T * L⁻¹) v) = ρ (T * L⁻¹) (ρ (T * L⁻¹) (ρ (L * ε) v)) := by
  rw [← rho_mul_apply, sigma_mul_elliptic hεT hεL cube, rho_mul_apply, rho_mul_apply]

omit hεT hεL in
theorem elliptic_cube_apply (v : V) :
    ρ (T * L⁻¹) (ρ (T * L⁻¹) (ρ (T * L⁻¹) v)) = v := by
  rw [← rho_mul_apply, ← rho_mul_apply, show T * L⁻¹ * (T * L⁻¹) * (T * L⁻¹) =
    (T * L⁻¹) ^ 3 by rw [pow_succ, pow_two], cube, map_one, Module.End.one_apply]

/-- `σ` commutes with the norm `1 + E + E²`. -/
theorem norm3_sigma (v : V) :
    norm3 ρ (T * L⁻¹) (ρ (L * ε) v) = ρ (L * ε) (norm3 ρ (T * L⁻¹) v) := by
  have h1 := sigma_elliptic_apply (ρ := ρ) hεT hεL cube v
  have h2 : ρ (L * ε) (ρ (T * L⁻¹) (ρ (T * L⁻¹) v)) = ρ (T * L⁻¹) (ρ (L * ε) v) := by
    rw [sigma_elliptic_apply hεT hεL cube, sigma_elliptic_apply hεT hεL cube,
      elliptic_cube_apply cube]
  rw [norm3_apply, norm3_apply, map_add, map_add, h1, h2]
  abel

/-- `y - σ y ∈ K⁻` for `y ∈ K`. -/
theorem sub_sigma_mem_kernelMinus {y : V} (hy : y ∈ kernelE (ρ := ρ) T L) :
    y - ρ (L * ε) y ∈ kernelMinus (ρ := ρ) T L ε := by
  rw [LinearMap.mem_ker] at hy
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, norm3_sigma hεT hεL cube, hy, map_zero,
      sub_zero]
  · rw [SetLike.mem_coe, mem_antiFixed, map_sub, ← rho_mul_apply, sigma_sq hεL, map_one,
      Module.End.one_apply, neg_sub]

/-- `v ↦ Ev - E²v`, from `K⁻` to `K⁺`. -/
def halving : kernelMinus (ρ := ρ) T L ε →ₗ[ℂ] kernelPlus (ρ := ρ) T L ε where
  toFun v := ⟨ρ (T * L⁻¹) v.val - ρ (T * L⁻¹) (ρ (T * L⁻¹) v.val), by
    obtain ⟨hK, hσ⟩ := v.property
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hK
    rw [SetLike.mem_coe, mem_antiFixed] at hσ
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, norm3_rho cube, norm3_rho cube, norm3_rho cube,
        sub_self]
    · rw [SetLike.mem_coe, mem_fixed]
      have h3 : ρ (T * L⁻¹) (ρ (T * L⁻¹) (ρ (T * L⁻¹) v.val)) = v.val := by
        rw [← rho_mul_apply, ← rho_mul_apply, show T * L⁻¹ * (T * L⁻¹) * (T * L⁻¹) =
          (T * L⁻¹) ^ 3 by rw [pow_succ, pow_two], cube, map_one, Module.End.one_apply]
      have hσE : ρ (L * ε) (ρ (T * L⁻¹) v.val) = -ρ (T * L⁻¹) (ρ (T * L⁻¹) v.val) := by
        rw [sigma_elliptic_apply hεT hεL cube, hσ, map_neg, map_neg]
      have hσE2 : ρ (L * ε) (ρ (T * L⁻¹) (ρ (T * L⁻¹) v.val)) = -ρ (T * L⁻¹) v.val := by
        rw [sigma_elliptic_apply hεT hεL cube, hσE, map_neg, map_neg, h3]
      rw [map_sub, hσE, hσE2]
      abel⟩
  map_add' v w := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    abel
  map_smul' c v := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul, RingHom.id_apply, smul_sub]

theorem halving_injective : Function.Injective (halving (ρ := ρ) hεT hεL cube) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have h := congrArg Subtype.val hv
  change ρ (T * L⁻¹) v.val - ρ (T * L⁻¹) (ρ (T * L⁻¹) v.val) = 0 at h
  rw [sub_eq_zero] at h
  have h3 : ∀ w : V, ρ (T * L⁻¹) (ρ (T * L⁻¹) (ρ (T * L⁻¹) w)) = w := by
    intro w
    rw [← rho_mul_apply, ← rho_mul_apply, show T * L⁻¹ * (T * L⁻¹) * (T * L⁻¹) =
      (T * L⁻¹) ^ 3 by rw [pow_succ, pow_two], cube, map_one, Module.End.one_apply]
  have fixedE : ρ (T * L⁻¹) v.val = v.val := by
    have := congrArg (fun w => ρ (T * L⁻¹) (ρ (T * L⁻¹) w)) h
    simp only [h3] at this
    exact this.symm
  have hK := v.property.1
  rw [SetLike.mem_coe, LinearMap.mem_ker, norm3_apply, fixedE, fixedE] at hK
  have three : (3 : ℂ) • v.val = 0 := by
    rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    exact hK
  apply Subtype.ext
  exact (smul_eq_zero.mp three).resolve_left (by norm_num)

/-- **`2 dim K⁻ ≤ dim K`**. -/
theorem finrank_Kminus_add_le [FiniteDimensional ℂ V] :
    finrank ℂ (kernelMinus (ρ := ρ) T L ε) + finrank ℂ (kernelMinus (ρ := ρ) T L ε) ≤
      finrank ℂ (kernelE (ρ := ρ) T L) := by
  have inj := LinearMap.finrank_le_finrank_of_injective (halving_injective (ρ := ρ) hεT hεL cube)
  have disjoint : kernelPlus (ρ := ρ) T L ε ⊓ kernelMinus (ρ := ρ) T L ε = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨_, hplus⟩, ⟨_, hminus⟩⟩
    rw [SetLike.mem_coe, mem_fixed] at hplus
    rw [SetLike.mem_coe, mem_antiFixed, hplus] at hminus
    rw [Submodule.mem_bot]
    have two : (2 : ℂ) • v = 0 := by rw [two_smul]; nth_rewrite 1 [hminus]; exact neg_add_cancel v
    exact (smul_eq_zero.mp two).resolve_left (by norm_num)
  have sup_inf := Submodule.finrank_sup_add_finrank_inf_eq (kernelPlus (ρ := ρ) T L ε)
    (kernelMinus (ρ := ρ) T L ε)
  rw [disjoint, finrank_bot] at sup_inf
  have le : kernelPlus (ρ := ρ) T L ε ⊔ kernelMinus (ρ := ρ) T L ε ≤ kernelE (ρ := ρ) T L :=
    sup_le inf_le_left inf_le_left
  have := Submodule.finrank_mono le
  omega

end Halving

section Parabolic

variable (ρ) (T L ε : G)

/-- Cocycles with `z T = 0`, `z ε = 0`, `z L ∈ (L - 1)V`. -/
def reflectionNormalized : Submodule ℂ (crossedCocycles ρ) where
  carrier := {z | z.val T = 0 ∧ z.val ε = 0 ∧ z.val L ∈ moved ρ L}
  zero_mem' := ⟨rfl, rfl, Submodule.zero_mem _⟩
  add_mem' := by
    intro z w hz hw
    refine ⟨?_, ?_, Submodule.add_mem _ hz.2.2 hw.2.2⟩
    · change z.val T + w.val T = 0
      rw [hz.1, hw.1, add_zero]
    · change z.val ε + w.val ε = 0
      rw [hz.2.1, hw.2.1, add_zero]
  smul_mem' := by
    intro c z hz
    refine ⟨?_, ?_, Submodule.smul_mem _ c hz.2.2⟩
    · change c • z.val T = 0
      rw [hz.1, smul_zero]
    · change c • z.val ε = 0
      rw [hz.2.1, smul_zero]

variable {ρ T L ε}

theorem mkQ_boundary' (v : V) : (crossedBoundaries ρ).mkQ (crossedBoundary ρ v) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨v, rfl⟩

theorem parabolicH1_le_reflectionNormalized (hεε : ε * ε = 1) (hεT : ε * T * ε = T⁻¹) :
    parabolicH1 ρ T L ≤ (reflectionNormalized ρ T L ε).map (crossedBoundaries ρ).mkQ := by
  rintro _ ⟨z, ⟨⟨a, ha⟩, hL⟩, rfl⟩
  -- first make the value at `T` vanish
  let z₁ : crossedCocycles ρ := z - crossedBoundary ρ a
  have z₁T : z₁.val T = 0 := by
    change z.val T - (ρ T a - a) = 0
    rw [← ha, LinearMap.sub_apply, Module.End.one_apply, sub_self]
  have z₁L : z₁.val L ∈ moved ρ L := by
    change z.val L - (ρ L a - a) ∈ moved ρ L
    exact Submodule.sub_mem _ hL (sub_mem_moved ρ L a)
  set b := z₁.val ε with hb
  -- `b` is `ε`-anti-invariant and `T`-invariant
  have bε : ρ ε b = -b := by
    have h := cocycle_mul z₁ ε ε
    rw [hεε, cocycle_one, ← hb] at h
    exact (eq_neg_of_add_eq_zero_right h.symm)
  have bT : ρ T b = b := by
    have h := cocycle_mul z₁ (ε * T) ε
    rw [hεT, cocycle_inv, z₁T, map_zero, neg_zero, cocycle_mul, z₁T, map_zero, add_zero,
      ← hb, rho_mul_apply] at h
    -- h : 0 = b + ρ ε (ρ T b)
    have h' : ρ ε (ρ T b) = -b := eq_neg_of_add_eq_zero_right h.symm
    have := congrArg (ρ ε) h'
    rw [← rho_mul_apply, hεε, map_one, Module.End.one_apply, map_neg, bε, neg_neg] at this
    exact this
  -- then make the value at `ε` vanish, keeping the value at `T`
  let z₂ : crossedCocycles ρ := z₁ - crossedBoundary ρ (-(2 : ℂ)⁻¹ • b)
  refine ⟨z₂, ⟨?_, ?_, ?_⟩, ?_⟩
  · change z₁.val T - (ρ T (-(2 : ℂ)⁻¹ • b) - -(2 : ℂ)⁻¹ • b) = 0
    rw [map_smul, bT, z₁T, sub_self, sub_zero]
  · change z₁.val ε - (ρ ε (-(2 : ℂ)⁻¹ • b) - -(2 : ℂ)⁻¹ • b) = 0
    rw [map_smul, bε, ← hb]
    module
  · change z₁.val L - (ρ L (-(2 : ℂ)⁻¹ • b) - -(2 : ℂ)⁻¹ • b) ∈ moved ρ L
    exact Submodule.sub_mem _ z₁L (sub_mem_moved ρ L _)
  · change (crossedBoundaries ρ).mkQ (z - crossedBoundary ρ a - crossedBoundary ρ (-(2 : ℂ)⁻¹ • b)) =
      (crossedBoundaries ρ).mkQ z
    rw [map_sub, map_sub, mkQ_boundary', mkQ_boundary', sub_zero, sub_zero]

theorem reflectionNormalized_value_mem (hεL : ε * L * ε = L⁻¹) (cube : (T * L⁻¹) ^ 3 = 1)
    (z : reflectionNormalized ρ T L ε) :
    z.val.val L ∈ moved ρ L ⊓ kernelMinus (ρ := ρ) T L ε := by
  obtain ⟨hT, hε, hL⟩ := z.property
  refine ⟨hL, ⟨?_, ?_⟩⟩
  · exact (normalized_value_mem cube ⟨z.val, hT, hL⟩).2
  · rw [SetLike.mem_coe, mem_antiFixed]
    have hσ : z.val.val (L * ε) = z.val.val L := by
      rw [cocycle_mul, hε, map_zero, add_zero]
    have h := cocycle_mul z.val (L * ε) (L * ε)
    rw [sigma_sq hεL, cocycle_one, hσ] at h
    exact eq_neg_of_add_eq_zero_right h.symm

/-- `z ↦ z L` on reflection-normalized cocycles. -/
def reflectionValue (hεL : ε * L * ε = L⁻¹) (cube : (T * L⁻¹) ^ 3 = 1) :
    reflectionNormalized ρ T L ε →ₗ[ℂ]
      (moved ρ L ⊓ kernelMinus (ρ := ρ) T L ε : Submodule ℂ V) :=
  ((evalAt ρ L).comp (reflectionNormalized ρ T L ε).subtype).codRestrict _
    (reflectionNormalized_value_mem hεL cube)

theorem reflectionValue_injective (gen : Subgroup.closure ({T, L, ε} : Set G) = ⊤)
    (hεL : ε * L * ε = L⁻¹) (cube : (T * L⁻¹) ^ 3 = 1) :
    Function.Injective (reflectionValue (ρ := ρ) hεL cube) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have hL : z.val.val L = 0 := congrArg Subtype.val hz
  apply Subtype.ext
  apply cocycle_ext_of_closure gen
  intro s hs
  rcases hs with rfl | rfl | rfl
  · exact z.property.1
  · exact hL
  · exact z.property.2.1

/-- **Parabolic bound for the reflection extension**:
`dim H¹_par + dim (V^T ∩ V^ε) ≤ dim ((L - 1)V ∩ K⁻)`. -/
theorem finrank_parabolicH1_reflection_le [FiniteDimensional ℂ V]
    (gen : Subgroup.closure ({T, L, ε} : Set G) = ⊤) (hεε : ε * ε = 1) (hεT : ε * T * ε = T⁻¹)
    (hεL : ε * L * ε = L⁻¹) (cube : (T * L⁻¹) ^ 3 = 1)
    (invariants : fixed ρ T ⊓ fixed ρ L = ⊥) :
    finrank ℂ (parabolicH1 ρ T L) + finrank ℂ (fixed ρ T ⊓ fixed ρ ε : Submodule ℂ V) ≤
      finrank ℂ (moved ρ L ⊓ kernelMinus (ρ := ρ) T L ε : Submodule ℂ V) := by
  have : FiniteDimensional ℂ (reflectionNormalized ρ T L ε) :=
    Module.Finite.of_injective _ (reflectionValue_injective (ρ := ρ) gen hεL cube)
  have : IsNoetherian ℂ (reflectionNormalized ρ T L ε) :=
    (IsNoetherian.iff_fg (K := ℂ) (V := reflectionNormalized ρ T L ε)).mpr this
  let classes : reflectionNormalized ρ T L ε →ₗ[ℂ] CrossedH1 ρ :=
    (crossedBoundaries ρ).mkQ.comp (reflectionNormalized ρ T L ε).subtype
  have range_eq : LinearMap.range classes =
      (reflectionNormalized ρ T L ε).map (crossedBoundaries ρ).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let boundaryT : (fixed ρ T ⊓ fixed ρ ε : Submodule ℂ V) →ₗ[ℂ] reflectionNormalized ρ T L ε :=
    LinearMap.codRestrict (reflectionNormalized ρ T L ε)
      ((crossedBoundary ρ).comp (fixed ρ T ⊓ fixed ρ ε).subtype) (by
        intro v
        refine ⟨?_, ?_, sub_mem_moved ρ L v.val⟩
        · change ρ T v.val - v.val = 0
          rw [(mem_fixed ρ).mp v.property.1, sub_self]
        · change ρ ε v.val - v.val = 0
          rw [(mem_fixed ρ).mp v.property.2, sub_self])
  have range_le : LinearMap.range boundaryT ≤ LinearMap.ker classes := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    exact mkQ_boundary' v.val
  have boundaryT_injective : Function.Injective boundaryT := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have zero : crossedBoundary ρ v.val = 0 := congrArg (fun w => w.val) hv
    rw [boundary_eq_zero_iff] at zero
    have member : v.val ∈ fixed ρ T ⊓ fixed ρ L :=
      ⟨(mem_fixed ρ).mpr (zero T), (mem_fixed ρ).mpr (zero L)⟩
    rw [invariants, Submodule.mem_bot] at member
    exact Subtype.ext member
  have kernel_bound : finrank ℂ (fixed ρ T ⊓ fixed ρ ε : Submodule ℂ V) ≤
      finrank ℂ (LinearMap.ker classes) := by
    have : Module.Finite ℂ (LinearMap.ker classes) :=
      Module.Finite.of_injective (LinearMap.ker classes).subtype
        (LinearMap.ker classes).injective_subtype
    rw [← LinearMap.finrank_range_of_inj boundaryT_injective]
    exact Submodule.finrank_mono range_le
  have rank_nullity := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
    (V := reflectionNormalized ρ T L ε) (V₂ := CrossedH1 ρ) classes
  rw [range_eq] at rank_nullity
  have parabolic_le := Submodule.finrank_mono
    (parabolicH1_le_reflectionNormalized (ρ := ρ) (L := L) hεε hεT)
  have normalized_le :=
    LinearMap.finrank_le_finrank_of_injective (reflectionValue_injective (ρ := ρ) gen hεL cube)
  omega

end Parabolic

end TernaryPeriodPolynomials.LevelThree.ReflectionBound
