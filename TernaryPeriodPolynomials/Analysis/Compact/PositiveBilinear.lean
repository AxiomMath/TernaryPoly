module

public import TernaryPeriodPolynomials.Analysis.PositiveBilinearFinite

@[expose] public section


/-! Uniform norm comparison for a genuine continuous family of positive bilinear forms. -/
namespace TernaryPoly.PositiveBilinearFinite
open Metric
variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Positive definite bilinear forms dominate a single positive multiple of the norm on a compact base. -/
theorem compact_pos_lower_bound (B : X → E →L[ℝ] E →L[ℝ] ℝ)
    {K : Set X} (hK : IsCompact K) (hB : ContinuousOn B K)
    (hp : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : E, c * ‖v‖ ^ 2 ≤ B x v v := by
  by_cases hE : Subsingleton E
  · let := hE
    exact ⟨1, zero_lt_one, fun x _ v => by simp [Subsingleton.elim v 0]⟩
  have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  by_cases hne : K.Nonempty
  · have hs : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    have hc : ContinuousOn (fun p : X × E => B p.1 p.2 p.2) (K ×ˢ sphere (0 : E) 1) :=
      ((hB.comp continuousOn_fst (fun _ h => h.1)).clm_apply continuousOn_snd).clm_apply continuousOn_snd
    obtain ⟨p, hpK, hmin⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn (hne.prod hs) hc
    have hpn : ‖p.2‖ = 1 := by simpa using hpK.2
    have hp0 : p.2 ≠ 0 := by intro h; simp [h] at hpn
    refine ⟨B p.1 p.2 p.2, hp p.1 hpK.1 p.2 hp0, fun x hx v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hz : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
      simpa using norm_smul_inv_norm (𝕜 := ℝ) hv
    have hh := mul_le_mul_of_nonneg_right (hmin (show (x, ‖v‖⁻¹ • v) ∈ K ×ˢ sphere (0 : E) 1 from ⟨hx, hz⟩)) (sq_nonneg ‖v‖)
    calc
      _ ≤ B x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) * ‖v‖ ^ 2 := hh
      _ = B x v v := by simp [map_smul, smul_eq_mul, field]
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

/-- The same family admits a uniform quadratic upper bound on a compact base. -/
theorem compact_upper_bound (B : X → E →L[ℝ] E →L[ℝ] ℝ)
    {K : Set X} (hK : IsCompact K) (hB : ContinuousOn B K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ v : E, |B x v v| ≤ C * ‖v‖ ^ 2 := by
  by_cases hE : Subsingleton E
  · let := hE
    exact ⟨0, le_rfl, fun x _ v => by simp [Subsingleton.elim v 0]⟩
  have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  by_cases hne : K.Nonempty
  · have hs : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    have hc : ContinuousOn (fun p : X × E => |B p.1 p.2 p.2|) (K ×ˢ sphere (0 : E) 1) :=
      (((hB.comp continuousOn_fst (fun _ h => h.1)).clm_apply continuousOn_snd).clm_apply continuousOn_snd).abs
    obtain ⟨p, _, hmax⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_isMaxOn (hne.prod hs) hc
    refine ⟨|B p.1 p.2 p.2|, abs_nonneg _, fun x hx v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hz : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
      simpa using norm_smul_inv_norm (𝕜 := ℝ) hv
    have heq : B x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) * ‖v‖ ^ 2 = B x v v := by
      simp [map_smul, smul_eq_mul, field]
    calc
      |B x v v| = |B x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) * ‖v‖ ^ 2| := congrArg abs heq.symm
      _ = |B x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v)| * ‖v‖ ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg ‖v‖)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmax (show (x, ‖v‖⁻¹ • v) ∈ K ×ˢ sphere (0 : E) 1 from ⟨hx, hz⟩)) (sq_nonneg _)
  · exact ⟨0, le_rfl, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

end TernaryPoly.PositiveBilinearFinite
