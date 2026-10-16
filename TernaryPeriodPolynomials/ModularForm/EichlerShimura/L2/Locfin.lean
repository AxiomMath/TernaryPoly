module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Measure

@[expose] public section


/-!
# Local finiteness for the action of `Γ`

For compact subsets `C`, `K` of the upper half plane only finitely many elements of `Γ` move a
point of `C` into `K` (`finite_moving`), and the number of elements `γ` with `γ⁻¹ w ∈ K` is bounded
uniformly in `w` (`exists_mult_bound`).  The weights `ϑ ∘ γ` sum to `1` (`tsum_theta_comp`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)

variable {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}

theorem exists_cutoff_ne_zero' (hR : IsCover Γ R) {z : ℂ} (hz : z ∈ U) :
    ∃ γ : Γ, cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  have := Partition.finsum_cutoff (Γ := Γ) (R := R) hR hz
  simp [h] at this

/-- Only finitely many elements of `Γ` move a point of a compact set `C ⊆ U` into a compact
set `K ⊆ U`. -/
theorem finite_moving (hR : IsCover Γ R) {C K : Set ℂ} (hC : IsCompact C) (hCU : C ⊆ U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    {γ : Γ | ∃ z ∈ C, mob (γ : SL(2, ℤ)) z ∈ K}.Finite := by
  have h1 := Partition.finite_translates_of_isCompact Γ R hC hCU
  have h2 := Partition.finite_translates_of_isCompact Γ R hK hKU
  refine (Set.Finite.image2 (fun a b : Γ => a * b⁻¹) h2 h1).subset ?_
  rintro γ ⟨z, hz, hk⟩
  obtain ⟨γ₁, hγ₁⟩ := exists_cutoff_ne_zero' hR (hKU hk)
  refine ⟨γ₁, ⟨_, hk, hγ₁⟩, γ⁻¹ * γ₁, ⟨z, hz, ?_⟩, by group⟩
  have e : mob (((γ⁻¹ * γ₁ : Γ) : SL(2, ℤ))⁻¹) z = mob ((γ₁ : SL(2, ℤ))⁻¹) (mob (γ : SL(2, ℤ)) z) := by
    rw [← mob_mul]
    congr 1
    simp [mul_inv_rev]
  rw [e]
  exact hγ₁

/-- A uniform bound on the number of translates of a compact set containing a given point. -/
theorem exists_mult_bound (hR : IsCover Γ R) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ N : ℕ, ∀ w : ℂ, {γ : Γ | mob (γ : SL(2, ℤ))⁻¹ w ∈ K}.Finite ∧
      {γ : Γ | mob (γ : SL(2, ℤ))⁻¹ w ∈ K}.ncard ≤ N := by
  have hF := finite_moving hR hK hKU hK hKU
  refine ⟨hF.toFinset.card, fun w => ?_⟩
  by_cases hne : {γ : Γ | mob (γ : SL(2, ℤ))⁻¹ w ∈ K}.Nonempty
  · obtain ⟨γ₀, hγ₀⟩ := hne
    have hsub : {γ : Γ | mob (γ : SL(2, ℤ))⁻¹ w ∈ K} ⊆ (fun f : Γ => γ₀ * f⁻¹) '' {γ : Γ | ∃ z ∈ K, mob (γ : SL(2, ℤ)) z ∈ K} := by
      intro γ hγ
      refine ⟨γ⁻¹ * γ₀, ⟨mob ((γ₀ : SL(2, ℤ))⁻¹) w, hγ₀, ?_⟩, by group⟩
      rw [← mob_mul]
      simpa [mul_assoc] using hγ
    have hfin : {γ : Γ | mob (γ : SL(2, ℤ))⁻¹ w ∈ K}.Finite := (hF.image _).subset hsub
    refine ⟨hfin, ?_⟩
    calc {γ : Γ | mob (γ : SL(2, ℤ))⁻¹ w ∈ K}.ncard ≤ ((fun f : Γ => γ₀ * f⁻¹) '' {γ : Γ | ∃ z ∈ K, mob (γ : SL(2, ℤ)) z ∈ K}).ncard :=
          Set.ncard_le_ncard hsub (hF.image _)
      _ ≤ {γ : Γ | ∃ z ∈ K, mob (γ : SL(2, ℤ)) z ∈ K}.ncard := Set.ncard_image_le hF
      _ = hF.toFinset.card := (Set.ncard_eq_toFinset_card _ hF)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

section Theta

variable {a : Γ → ℝ}

theorem ennreal_tsum_cutoff (hR : IsCover Γ R) {z : ℂ} (hz : z ∈ U) :
    ∑' γ : Γ, ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z)) = 1 := by
  have hfs := Partition.hasFiniteSupport_cutoff Γ R hz
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun γ => cutoff_nonneg Γ R _)
    (summable_of_hasFiniteSupport hfs), tsum_eq_finsum hfs, Partition.finsum_cutoff (Γ := Γ) (R := R) hR hz]
  simp

theorem ennreal_tsum_cutoff_mul (hR : IsCover Γ R) (δ : Γ) {w : ℂ} (hw : w ∈ U) :
    ∑' γ : Γ, ENNReal.ofReal (cutoff Γ R (mob (δ : SL(2, ℤ))⁻¹ (mob (γ : SL(2, ℤ)) w))) = 1 := by
  have e : ∀ γ : Γ, mob (δ : SL(2, ℤ))⁻¹ (mob (γ : SL(2, ℤ)) w) = mob ((δ⁻¹ * γ : Γ) : SL(2, ℤ)) w := by
    intro γ
    rw [← mob_mul]
    simp
  simp_rw [e]
  have h1 := (Equiv.mulLeft δ⁻¹).tsum_eq
    (fun γ : Γ => ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ)) w)))
  have h2 := (Equiv.inv Γ).tsum_eq
    (fun γ : Γ => ENNReal.ofReal (cutoff Γ R (mob (γ : SL(2, ℤ)) w)))
  simp only [Equiv.coe_mulLeft, Equiv.inv_apply] at h1 h2
  rw [h1, ← h2]
  simpa [Subgroup.coe_inv] using ennreal_tsum_cutoff hR hw

/-- The weights `ϑ ∘ γ` sum to `1`. -/
theorem ennreal_tsum_theta_comp (hR : IsCover Γ R) (ha : ∀ γ, 0 < a γ) (hs : HasSum a 1) {w : ℂ}
    (hw : w ∈ U) : ∑' γ : Γ, ENNReal.ofReal (theta Γ R a (mob (γ : SL(2, ℤ)) w)) = 1 := by
  have h1 : ∀ γ : Γ, ENNReal.ofReal (theta Γ R a (mob (γ : SL(2, ℤ)) w)) =
      ∑' δ : Γ, ENNReal.ofReal (a δ) *
        ENNReal.ofReal (cutoff Γ R (mob (δ : SL(2, ℤ))⁻¹ (mob (γ : SL(2, ℤ)) w))) := by
    intro γ
    unfold theta
    rw [ENNReal.ofReal_tsum_of_nonneg (fun δ => mul_nonneg (ha δ).le (cutoff_nonneg Γ R _))
      (summable_theta hR ha hs _)]
    refine tsum_congr fun δ => ?_
    rw [ENNReal.ofReal_mul (ha δ).le]
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, ennreal_tsum_cutoff_mul hR _ hw, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun δ => (ha δ).le) hs.summable, hs.tsum_eq]
  simp

theorem hasSum_theta_comp (hR : IsCover Γ R) (ha : ∀ γ, 0 < a γ) (hs : HasSum a 1) {w : ℂ}
    (hw : w ∈ U) : HasSum (fun γ : Γ => theta Γ R a (mob (γ : SL(2, ℤ)) w)) 1 := by
  have h := ennreal_tsum_theta_comp hR ha hs hw
  have hsum : Summable fun γ : Γ => theta Γ R a (mob (γ : SL(2, ℤ)) w) := by
    refine ENNReal.summable_toReal (f := fun γ : Γ => ENNReal.ofReal (theta Γ R a (mob (γ : SL(2, ℤ)) w))) (by rw [h]; exact ENNReal.one_ne_top) |>.congr fun γ => ?_
    exact ENNReal.toReal_ofReal (theta_nonneg ha _)
  convert hsum.hasSum using 1
  have := ENNReal.tsum_toReal_eq (f := fun γ : Γ => ENNReal.ofReal (theta Γ R a (mob (γ : SL(2, ℤ)) w))) (fun γ => ENNReal.ofReal_ne_top)
  rw [h] at this
  simp only [ENNReal.toReal_ofReal (theta_nonneg ha _)] at this
  have ht : ∑' γ : Γ, theta Γ R a (mob (γ : SL(2, ℤ)) w) = 1 := by simpa using this.symm
  rw [← ht]

end Theta

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
