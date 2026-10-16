module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.PartitionOfUnity

@[expose] public section


/-!
# Cusp representatives and the cocycle at a cusp

Foundation for step 1 of the unconditional Eichler--Shimura route: for a finite-index subgroup `Γ` of `SL(2, ℤ)` not containing `-1`,
* `CuspRel Γ` is the equivalence relation "the cusps `g ∞`, `g' ∞` are `Γ`-equivalent", and
  `exists_cuspReps` provides a finite set of representatives of the classes;
* a `1`-cocycle `c` of `Γ` with values in a representation `ρ` that is a coboundary on every
  parabolic element is the coboundary of one vector `v` on the whole stabiliser of each cusp
  (`exists_cusp_vector`), because the set of `γ` with `c γ = ρ γ v - v` is a subgroup
  (`coboundaryAt`).

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularGroup Complex
open scoped Modular MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport

open TernaryPeriodPolynomials.Argument.ESFoundations

open TernaryPeriodPolynomials.Argument.ESFoundations

/-- Cusp equivalence for `Γ`: `g` and `g'` have `Γ`-equivalent cusps `g ∞`, `g' ∞`. -/
def CuspRel (Γ : Subgroup SL(2, ℤ)) (g g' : SL(2, ℤ)) : Prop :=
  ∃ γ ∈ Γ, g'⁻¹ * γ * g ∈ stabInfty

theorem cuspRel_refl (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : CuspRel Γ g g :=
  ⟨1, Γ.one_mem, by simp⟩

theorem cuspRel_symm {Γ : Subgroup SL(2, ℤ)} {g g' : SL(2, ℤ)} (h : CuspRel Γ g g') :
    CuspRel Γ g' g := by
  obtain ⟨γ, hγ, hs⟩ := h
  refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
  have := stabInfty.inv_mem hs
  simp only [mul_inv_rev, inv_inv, mul_assoc] at this
  simpa [mul_assoc] using this

theorem cuspRel_trans {Γ : Subgroup SL(2, ℤ)} {g g' g'' : SL(2, ℤ)} (h : CuspRel Γ g g')
    (h' : CuspRel Γ g' g'') : CuspRel Γ g g'' := by
  obtain ⟨γ, hγ, hs⟩ := h
  obtain ⟨γ', hγ', hs'⟩ := h'
  refine ⟨γ' * γ, Γ.mul_mem hγ' hγ, ?_⟩
  have := stabInfty.mul_mem hs' hs
  convert this using 1
  group

def cuspSetoid (Γ : Subgroup SL(2, ℤ)) : Setoid SL(2, ℤ) where
  r := CuspRel Γ
  iseqv := ⟨cuspRel_refl Γ, cuspRel_symm, cuspRel_trans⟩

/-- Right coset representatives of a finite-index subgroup. -/
theorem exists_rightCosetReps (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ R : Finset SL(2, ℤ), ∀ g : SL(2, ℤ), ∃ r ∈ R, ∃ γ ∈ Γ, g = γ * r := by
  classical
  obtain ⟨R, hR⟩ := Partition.exists_cosetReps Γ
  refine ⟨R.image (·⁻¹), fun g => ?_⟩
  obtain ⟨r, hr, γ, hγ, hg⟩ := hR g⁻¹
  refine ⟨r⁻¹, Finset.mem_image.mpr ⟨r, hr, rfl⟩, γ⁻¹, Γ.inv_mem hγ, ?_⟩
  rw [← inv_inv g, hg]
  group

/-- A finite set of representatives of the `Γ`-classes of cusps. -/
theorem exists_cuspReps (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ G : Finset SL(2, ℤ),
      (∀ g ∈ G, ∀ g' ∈ G, CuspRel Γ g g' → g = g') ∧
      ∀ g : SL(2, ℤ), ∃ g₀ ∈ G, CuspRel Γ g g₀ := by
  classical
  obtain ⟨R, hR⟩ := exists_rightCosetReps Γ
  let s := cuspSetoid Γ
  refine ⟨R.image fun r => Quotient.out (s := s) (Quotient.mk s r), ?_, ?_⟩
  · intro g hg g' hg' hrel
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨r', -, rfl⟩ := Finset.mem_image.mp hg'
    have h1 : Quotient.mk s (Quotient.out (s := s) (Quotient.mk s r)) = Quotient.mk s r :=
      Quotient.out_eq _
    have h2 : Quotient.mk s (Quotient.out (s := s) (Quotient.mk s r')) = Quotient.mk s r' :=
      Quotient.out_eq _
    have h3 : Quotient.mk s r = Quotient.mk s r' := by
      rw [← h1, ← h2]
      exact Quotient.sound hrel
    rw [h3]
  · intro g
    obtain ⟨r, hr, γ, hγ, rfl⟩ := hR g
    refine ⟨Quotient.out (s := s) (Quotient.mk s r), Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
    have hr1 : CuspRel Γ (γ * r) r := ⟨γ⁻¹, Γ.inv_mem hγ, by
      simp [mul_assoc]⟩
    have hr2 : CuspRel Γ r (Quotient.out (s := s) (Quotient.mk s r)) :=
      Quotient.exact (Quotient.out_eq (s := s) (Quotient.mk s r)).symm
    exact cuspRel_trans hr1 hr2




/-- Parabolic elements of `SL₂(ℤ)`: `±` conjugates of `T^k`. -/
def IsParabolicElt (γ : SL(2, ℤ)) : Prop :=
  ∃ (g : SL(2, ℤ)) (k : ℤ),
    γ = g * ModularGroup.T ^ k * g⁻¹ ∨ γ = -(g * ModularGroup.T ^ k * g⁻¹)

variable {Γ : Subgroup SL(2, ℤ)} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (ρ : Γ →* (W →ₗ[ℝ] W)) (c : Γ → W)

theorem cocycle_one (hc : ∀ δ γ : Γ, c (δ * γ) = c δ + ρ δ (c γ)) : c 1 = 0 := by
  have := hc 1 1
  rw [mul_one, map_one, Module.End.one_apply] at this
  have h2 : c 1 + c 1 = c 1 + 0 := by rw [← this, add_zero]
  exact add_left_cancel h2

/-- The elements of `Γ` on which the cocycle `c` is the coboundary of `u`. -/
def coboundaryAt (hc : ∀ δ γ : Γ, c (δ * γ) = c δ + ρ δ (c γ)) (u : W) : Subgroup Γ where
  carrier := {γ | c γ = ρ γ u - u}
  one_mem' := by
    simp [cocycle_one ρ c hc]
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [hc, ha, hb, map_mul, Module.End.mul_apply, map_sub]
    abel
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h1 := hc a⁻¹ a
    have h2 : ρ a⁻¹ (ρ a u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [inv_mul_cancel, cocycle_one ρ c hc, ha, map_sub, h2] at h1
    have : c a⁻¹ = -(u - ρ a⁻¹ u) := by
      have h4 : c a⁻¹ + (u - ρ a⁻¹ u) = 0 := h1.symm
      exact eq_neg_of_add_eq_zero_left h4
    rw [this]; abel

/-- **The cocycle is a coboundary on each cusp stabiliser.** -/
theorem exists_cusp_vector [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∉ Γ)
    (hc : ∀ δ γ : Γ, c (δ * γ) = c δ + ρ δ (c γ))
    (hpar : ∀ γ : Γ, IsParabolicElt γ.1 → ∃ u : W, c γ = ρ γ u - u) (g : SL(2, ℤ)) :
    ∃ γ₀ ∈ cuspStab Γ g, 0 < transLen (g⁻¹ * γ₀ * g) ∧ cuspStab Γ g = Subgroup.zpowers γ₀ ∧
      ∃ v : W, ∀ γ : Γ, (γ : SL(2, ℤ)) ∈ cuspStab Γ g → c γ = ρ γ v - v := by
  obtain ⟨γ₀, hγ₀, hpos, hz, ε, hε, hform⟩ := cuspStab_eq_zpowers Γ hneg g
  have hγ₀Γ : γ₀ ∈ Γ := ((mem_cuspStab_iff Γ g γ₀).mp hγ₀).1
  have hpara : IsParabolicElt γ₀ := by
    rcases hε with rfl | rfl
    · exact ⟨g, _, Or.inl (by rw [hform, one_mul])⟩
    · exact ⟨g, _, Or.inr (by rw [hform, neg_one_mul, mul_neg, neg_mul])⟩
  obtain ⟨u, hu⟩ := hpar ⟨γ₀, hγ₀Γ⟩ hpara
  refine ⟨γ₀, hγ₀, hpos, hz, u, fun γ hγ => ?_⟩
  have hmem : (⟨γ₀, hγ₀Γ⟩ : Γ) ∈ coboundaryAt ρ c hc u := hu
  have hle := Subgroup.zpowers_le.mpr hmem
  rw [hz, Subgroup.mem_zpowers_iff] at hγ
  obtain ⟨k, hk⟩ := hγ
  have : γ = (⟨γ₀, hγ₀Γ⟩ : Γ) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
  rw [this]
  exact hle (Subgroup.zpow_mem_zpowers _ k)


end TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport
