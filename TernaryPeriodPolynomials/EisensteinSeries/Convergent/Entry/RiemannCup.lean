module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CupBridge

@[expose] public section


/-!
# Riemann sums of the cup pairing along a segment

`tendsto_riemann_cup`, `tendsto_cupEdge`: for `a` continuous and `l` of class `C¹` along a segment `[x, y]`, the
Riemann sums `∑ᵢ β(a(γ(i/N)) - a x)(l(γ((i+1)/N)) - l(γ(i/N)))` of the cup pairing converge to the edge integral
`cupEdge β a l x y`.  Used to derive the invariance laws of the edge cochain from those of the cup cocycle.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

section Riemann

variable {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
  [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace B] [CompleteSpace F]

/-- **Riemann sums of the cup pairing converge to the edge integral**: for `A'` continuous and `ψ` of class `C¹` on
`[0,1]`, `∑ᵢ β(A'(i/N)) (ψ((i+1)/N) - ψ(i/N)) → ∫₀¹ β(A' t)(ψ' t) dt`. -/
theorem tendsto_riemann_cup (β : A →L[ℝ] B →L[ℝ] F) (A' : ℝ → A) (ψ ψ' : ℝ → B)
    (hA : ContinuousOn A' (Icc 0 1)) (hψ' : ContinuousOn ψ' (Icc 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt ψ (ψ' t) t) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      β (A' ((i : ℝ) / N)) (ψ (((i : ℝ) + 1) / N) - ψ ((i : ℝ) / N))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, β (A' t) (ψ' t))) := by
  have hK : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have hAu : UniformContinuousOn A' (Icc 0 1) := hK.uniformContinuousOn_of_continuous hA
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ‖ψ' t‖ ≤ C := hK.exists_bound_of_continuousOn hψ'
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hint : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → IntervalIntegrable ψ' volume a b := by
    intro a b ha hb
    exact (hψ'.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hmem : ∀ (N i : ℕ), i < N → ((i : ℝ) / N ∈ Icc (0 : ℝ) 1 ∧ ((i : ℝ) + 1) / N ∈ Icc (0 : ℝ) 1) := by
    intro N i hi
    have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hi)
    have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    exact ⟨⟨by positivity, (div_le_one hN).mpr (by linarith)⟩, ⟨by positivity, (div_le_one hN).mpr hi'⟩⟩
  have hterm : ∀ N i : ℕ, i < N → β (A' ((i : ℝ) / N)) (ψ (((i : ℝ) + 1) / N) - ψ ((i : ℝ) / N)) =
      ∫ s in ((i : ℝ) / N)..(((i : ℝ) + 1) / N), β (A' ((i : ℝ) / N)) (ψ' s) := by
    intro N i hi
    obtain ⟨h1, h2⟩ := hmem N i hi
    have hF : ∫ s in ((i : ℝ) / N)..(((i : ℝ) + 1) / N), ψ' s = ψ (((i : ℝ) + 1) / N) - ψ ((i : ℝ) / N) :=
      integral_eq_sub_of_hasDerivAt (fun x hx => hd x (uIcc_subset_Icc h1 h2 hx)) (hint _ _ h1 h2)
    rw [← hF]
    exact ((β (A' ((i : ℝ) / N))).intervalIntegral_comp_comm (hint _ _ h1 h2)).symm
  have hcont : ContinuousOn (fun t => β (A' t) (ψ' t)) (Icc 0 1) :=
    (β.continuous.comp_continuousOn hA).clm_apply hψ'
  have hI : ∀ N : ℕ, 0 < N → ∫ t in (0 : ℝ)..1, β (A' t) (ψ' t) =
      ∑ i ∈ Finset.range N, ∫ s in ((i : ℝ) / N)..(((i : ℝ) + 1) / N), β (A' s) (ψ' s) := by
    intro N hN
    have h := sum_integral_adjacent_intervals (f := fun t => β (A' t) (ψ' t)) (μ := volume)
      (a := fun k : ℕ => (k : ℝ) / N) (n := N) (fun k hk => by
        obtain ⟨h1, h2⟩ := hmem N k hk
        have h2' : (((k + 1 : ℕ) : ℝ)) / N ∈ Icc (0 : ℝ) 1 := by push_cast; exact h2
        exact (hcont.mono (uIcc_subset_Icc h1 h2')).intervalIntegrable)
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [Nat.cast_zero, zero_div, div_self hNr] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rfl
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := ‖β‖ * C + 1 with hM
  have hMpos : 0 < M := by positivity
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp hAu (ε / (2 * M)) (by positivity)
  obtain ⟨N0, hN0⟩ := exists_nat_one_div_lt hδ
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : 1 / (N : ℝ) < δ := by
    refine lt_of_le_of_lt ?_ hN0
    rw [one_div, one_div]
    apply inv_anti₀ (by positivity)
    exact_mod_cast (by omega : N0 + 1 ≤ N)
  rw [dist_eq_norm, hI N hNpos, ← Finset.sum_sub_distrib]
  have hbound : ∀ i ∈ Finset.range N, ‖β (A' ((i : ℝ) / N)) (ψ (((i : ℝ) + 1) / N) - ψ ((i : ℝ) / N)) -
      ∫ s in ((i : ℝ) / N)..(((i : ℝ) + 1) / N), β (A' s) (ψ' s)‖ ≤ ε / (2 * M) * M / N := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    obtain ⟨h1, h2⟩ := hmem N i hi'
    rw [hterm N i hi']
    have hint2 : IntervalIntegrable (fun s => β (A' ((i : ℝ) / N)) (ψ' s)) volume ((i : ℝ) / N)
        (((i : ℝ) + 1) / N) :=
      ((β (A' ((i : ℝ) / N))).continuous.comp_continuousOn
        (hψ'.mono (uIcc_subset_Icc h1 h2))).intervalIntegrable
    have hint3 : IntervalIntegrable (fun s => β (A' s) (ψ' s)) volume ((i : ℝ) / N) (((i : ℝ) + 1) / N) :=
      (hcont.mono (uIcc_subset_Icc h1 h2)).intervalIntegrable
    rw [← integral_sub hint2 hint3]
    have hlen : |((i : ℝ) + 1) / N - (i : ℝ) / N| = 1 / N := by
      rw [← sub_div]; simp [abs_of_pos hNr]
    have := norm_integral_le_of_norm_le_const (a := (i : ℝ) / N) (b := ((i : ℝ) + 1) / N)
      (C := ε / (2 * M) * M) (f := fun s => β (A' ((i : ℝ) / N)) (ψ' s) - β (A' s) (ψ' s)) (fun s hs => ?_)
    · rw [hlen] at this
      calc _ ≤ ε / (2 * M) * M * (1 / N) := this
        _ = _ := by ring
    · have hle : (i : ℝ) / N ≤ ((i : ℝ) + 1) / N := by
        rw [div_le_div_iff_of_pos_right hNr]; linarith
      have hs2 : s ∈ Ioc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := by
        rwa [uIoc_of_le hle] at hs
      have hs' : s ∈ Icc (0 : ℝ) 1 :=
        uIcc_subset_Icc h1 h2 (Ioc_subset_Icc_self.trans Icc_subset_uIcc hs2)
      have hsd : dist ((i : ℝ) / N) s < δ := by
        rw [Real.dist_eq, abs_lt]
        have e : ((i : ℝ) + 1) / N = (i : ℝ) / N + 1 / N := by ring
        constructor
        · linarith [hs2.2, e, hN1]
        · linarith [hs2.1, hδ]
      have hdist := hδu _ h1 _ hs' hsd
      rw [dist_eq_norm] at hdist
      calc ‖β (A' ((i : ℝ) / N)) (ψ' s) - β (A' s) (ψ' s)‖
          = ‖β (A' ((i : ℝ) / N) - A' s) (ψ' s)‖ := by rw [map_sub, sub_apply]
        _ ≤ ‖β‖ * ‖A' ((i : ℝ) / N) - A' s‖ * ‖ψ' s‖ := by
            refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
            exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖β‖ * (ε / (2 * M)) * C := by
            gcongr
            exact hC s hs'
        _ ≤ ε / (2 * M) * M := by
            have : ‖β‖ * C ≤ M := by rw [hM]; linarith
            calc ‖β‖ * (ε / (2 * M)) * C = ε / (2 * M) * (‖β‖ * C) := by ring
              _ ≤ _ := by gcongr
  calc ‖∑ i ∈ Finset.range N, (β (A' ((i : ℝ) / N)) (ψ (((i : ℝ) + 1) / N) - ψ ((i : ℝ) / N)) -
        ∫ s in ((i : ℝ) / N)..(((i : ℝ) + 1) / N), β (A' s) (ψ' s))‖
      ≤ ∑ i ∈ Finset.range N, ε / (2 * M) * M / N := norm_sum_le_of_le _ hbound
    _ = ε / (2 * M) * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by
        have : ε / (2 * M) * M = ε / 2 := by field_simp
        rw [this]; linarith

/-- **Riemann sums of the cup along a segment converge to the edge integral `cupEdge`**: for `a` continuous and `l` of
class `C¹` on an open set containing the segment `[x, y]`,
`∑ᵢ β(a(γ(i/N)) - a(x)) (l(γ((i+1)/N)) - l(γ(i/N))) → cupEdge β a l x y`, `γ(t) = x + t (y - x)`. -/
theorem tendsto_cupEdge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (β : A →L[ℝ] B →L[ℝ] F) (a : E → A) (l : E → B) (U : Set E) (hU : IsOpen U)
    (ha : ContinuousOn a U) (hl : ContDiffOn ℝ 1 l U) (x y : E)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      β (a (x + ((i : ℝ) / N) • (y - x)) - a x)
        (l (x + (((i : ℝ) + 1) / N) • (y - x)) - l (x + ((i : ℝ) / N) • (y - x)))) atTop
      (𝓝 (cupEdge β a l x y)) := by
  have hγ : Continuous (fun t : ℝ => x + t • (y - x)) := by fun_prop
  have hdl : ContinuousOn (fun z => fderiv ℝ l z) U := hl.continuousOn_fderiv_of_isOpen hU le_rfl
  have hca : ContinuousOn (fun t : ℝ => a (x + t • (y - x)) - a x) (Icc 0 1) :=
    (ha.comp hγ.continuousOn hseg).sub continuousOn_const
  have hcd : ContinuousOn (fun t : ℝ => fderiv ℝ l (x + t • (y - x)) (y - x)) (Icc 0 1) :=
    ((hdl.comp hγ.continuousOn hseg).clm_apply continuousOn_const)
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => l (x + t • (y - x)))
      (fderiv ℝ l (x + t • (y - x)) (y - x)) t := by
    intro t ht
    have hxt : x + t • (y - x) ∈ U := hseg t ht
    have h1 : HasFDerivAt l (fderiv ℝ l (x + t • (y - x))) (x + t • (y - x)) :=
      ((hl.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hxt)).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact h1.comp_hasDerivAt t h2
  exact tendsto_riemann_cup β (fun t => a (x + t • (y - x)) - a x) (fun t => l (x + t • (y - x)))
    (fun t => fderiv ℝ l (x + t • (y - x)) (y - x)) hca hcd hd

end Riemann

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
