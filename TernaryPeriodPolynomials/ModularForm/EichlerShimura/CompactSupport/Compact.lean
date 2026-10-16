module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.PartitionOfUnity

@[expose] public section


/-!
# Cocompactness of the complement of the height-two horoballs

For a finite-index subgroup `Γ` of `SL(2, ℤ)`, every point of the upper half plane at which
`Im (g⁻¹ z) ≤ 2` for all `g ∈ SL(2, ℤ)` has a `Γ`-translate in one fixed compact set
(`exists_compact_height_two`; `exists_compact_height_two_complex` states it for functions on `ℂ`
through the Möbius action `mob`).  This is the height-two analogue of
`exists_compact_complement_horoballs`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularGroup Complex
open scoped Modular MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport

open TernaryPeriodPolynomials.Argument.ESFoundations
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)

/-- The compact box `|Re z| ≤ 1/2`, `1/2 ≤ Im z ≤ 2`. -/
def box₂ : Set ℍ := {z | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ 2}

theorem isCompact_box₂ : IsCompact box₂ := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.isCompact_iff]
  have himage : ((↑) : ℍ → ℂ) '' box₂ =
      {w : ℂ | |w.re| ≤ 1 / 2 ∧ 1 / 2 ≤ w.im ∧ w.im ≤ 2} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨w, by linarith⟩, ⟨h1, h2, h3⟩, rfl⟩
  rw [himage]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact ((isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨3, fun w ⟨h1, h2, h3⟩ => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 3 := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w.im)]; linarith

/-- **Cocompactness of the complement of the height-two horoballs.** -/
theorem exists_compact_height_two (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ K : Set ℍ, IsCompact K ∧
      ∀ z : ℍ, (∀ g : SL(2, ℤ), (g⁻¹ • z).im ≤ 2) → ∃ γ ∈ Γ, ∃ k ∈ K, z = γ • k := by
  classical
  have : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨⋃ q : SL(2, ℤ) ⧸ Γ, (fun z => (Quotient.out q)⁻¹ • z) '' box₂,
    isCompact_iUnion fun q => isCompact_box₂.image (continuous_smul_SL _), ?_⟩
  intro z hz
  obtain ⟨s, hs⟩ := exists_smul_mem_fd z
  have hbox : s • z ∈ box₂ := by
    have hle : (s • z).im ≤ 2 := by
      have := hz s⁻¹
      rwa [inv_inv] at this
    have h34 := three_le_four_mul_im_sq_of_mem_fd hs
    have hpos := (s • z).im_pos
    refine ⟨hs.2, ?_, hle⟩
    nlinarith
  set r := Quotient.out (QuotientGroup.mk s : SL(2, ℤ) ⧸ Γ) with hr
  have hmem : r⁻¹ * s ∈ Γ := by
    have : (QuotientGroup.mk r : SL(2, ℤ) ⧸ Γ) = QuotientGroup.mk s := by
      rw [hr]; exact QuotientGroup.out_eq' _
    exact QuotientGroup.eq.mp this
  refine ⟨(r⁻¹ * s)⁻¹, Γ.inv_mem hmem, r⁻¹ • s • z, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨QuotientGroup.mk s, ⟨s • z, hbox, rfl⟩⟩
  · rw [← mul_smul, ← mul_smul, show (r⁻¹ * s)⁻¹ * r⁻¹ * s = 1 by group, one_smul]

/-- The compact set in `ℂ`: every point outside the height-two horoballs has a `Γ`-translate in it. -/
theorem exists_compact_height_two_complex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ ∀ z ∈ U, (∀ g : SL(2, ℤ), (mob g⁻¹ z).im ≤ 2) →
      ∃ γ : Γ, mob (γ : SL(2, ℤ)) z ∈ K := by
  obtain ⟨K, hK, hKz⟩ := exists_compact_height_two Γ
  refine ⟨((↑) : ℍ → ℂ) '' K, hK.image UpperHalfPlane.continuous_coe, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.im_pos
  · intro z hz hg
    have hgz : ∀ g : SL(2, ℤ), (g⁻¹ • (⟨z, hz⟩ : ℍ)).im ≤ 2 := by
      intro g
      have := hg g
      have e : mob g⁻¹ z = ((g⁻¹ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := by
        rw [mob, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rw [e] at this
      exact this
    obtain ⟨γ, hγ, k, hk, hzk⟩ := hKz ⟨z, hz⟩ hgz
    refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, k, hk, ?_⟩
    have e : mob γ⁻¹ z = ((γ⁻¹ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := by
      rw [mob, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    show ((k : ℍ) : ℂ) = mob γ⁻¹ z
    rw [e, hzk, inv_smul_smul]

end TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport
