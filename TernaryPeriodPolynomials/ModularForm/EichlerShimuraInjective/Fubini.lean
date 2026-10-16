module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Region

@[expose] public section


/-!
# Fubini on the truncated fundamental domain

Iterated integrals over `regionF T` in either order, and interval integrability of the inner integral of a continuous function.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open scoped ComplexConjugate


/-- The cut-off integrand. -/
def Fcut (G : ℝ → ℝ → ℂ) (T : ℝ) : ℝ × ℝ → ℂ := (regionF T).indicator (fun p => G p.1 p.2)

theorem integrable_Fcut (G : ℝ → ℝ → ℂ) (T : ℝ)
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (regionF T)) : Integrable (Fcut G T) :=
  (integrable_indicator_iff (regionF_closed T).measurableSet).2 (hG.integrableOn_compact (regionF_compact T))

theorem slice_x (G : ℝ → ℝ → ℂ) (T : ℝ) (hT : 1 ≤ T) (x : ℝ) :
    ∫ y, Fcut G T (x, y) = if x ∈ Icc (-1 / 2 : ℝ) (1 / 2) then ∫ y in arcY x..T, G x y else 0 := by
  by_cases hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2)
  · rw [ite_eq_left hx]
    have hfun : (fun y => Fcut G T (x, y)) = (Icc (arcY x) T).indicator (fun y => G x y) := by
      funext y
      unfold Fcut regionF
      by_cases hy : y ∈ Icc (arcY x) T
      · rw [indicator_of_mem hy, indicator_of_mem]
        exact ⟨hx.1, hx.2, hy.1, hy.2⟩
      · rw [indicator_of_notMem hy, indicator_of_notMem]
        rintro ⟨-, -, h3, h4⟩
        exact hy ⟨h3, h4⟩
    rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc,
      intervalIntegral.integral_of_le ((arcY_le_one x).trans hT), integral_Icc_eq_integral_Ioc]
  · rw [ite_eq_right hx]
    have : (fun y => Fcut G T (x, y)) = fun _ => 0 := by
      funext y
      unfold Fcut regionF
      rw [indicator_of_notMem]
      rintro ⟨h1, h2, -, -⟩
      exact hx ⟨h1, h2⟩
    rw [this]; simp


theorem slice_y (G : ℝ → ℝ → ℂ) (T : ℝ)
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (regionF T)) (y : ℝ) :
    ∫ x, Fcut G T (x, y) = if y ∈ Icc (Real.sqrt 3 / 2) T then
      (∫ x in (-1 / 2 : ℝ)..(-arcX y), G x y) + ∫ x in arcX y..(1 / 2), G x y else 0 := by
  by_cases hy : y ∈ Icc (Real.sqrt 3 / 2) T
  · rw [ite_eq_left hy]
    have hy0 : 0 ≤ y := le_trans (by positivity) hy.1
    have hr := arcX_nonneg y
    have hr2 := arcX_le_half hy.1
    set r := arcX y with hr_def
    have hset : {x : ℝ | (x, y) ∈ regionF T} = Icc (-1 / 2 : ℝ) (-r) ∪ Icc r (1 / 2) := by
      ext x
      simp only [regionF, mem_ofPred_eq, mem_union, mem_Icc, arcY_le_iff hy0]
      constructor
      · rintro ⟨h1, h2, h3, -⟩
        rcases le_abs'.mp h3 with h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨h, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨h1, by linarith, ?_, hy.2⟩
          exact le_abs'.mpr (Or.inl h2)
        · refine ⟨by linarith, h2, ?_, hy.2⟩
          exact le_abs'.mpr (Or.inr h1)
    have hfun : (fun x => Fcut G T (x, y)) = ({x : ℝ | (x, y) ∈ regionF T}).indicator (fun x => G x y) := by
      funext x
      unfold Fcut
      by_cases hx : (x, y) ∈ regionF T
      · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ {x : ℝ | (x, y) ∈ regionF T} from hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ {x : ℝ | (x, y) ∈ regionF T} from hx)]
    have hmeas : MeasurableSet {x : ℝ | (x, y) ∈ regionF T} := by
      rw [hset]; exact measurableSet_Icc.union measurableSet_Icc
    -- continuity of the slice on the closed set
    have hGy : ContinuousOn (fun x => G x y) ({x : ℝ | (x, y) ∈ regionF T}) := by
      have : ContinuousOn (fun x : ℝ => (x, y)) {x : ℝ | (x, y) ∈ regionF T} :=
        (continuous_id.prodMk continuous_const).continuousOn
      exact hG.comp this (fun x hx => hx)
    have hcpt : IsCompact {x : ℝ | (x, y) ∈ regionF T} := by
      rw [hset]; exact isCompact_Icc.union isCompact_Icc
    have hA : IntegrableOn (fun x => G x y) (Icc (-1 / 2 : ℝ) (-r)) := by
      refine (hGy.mono ?_).integrableOn_compact isCompact_Icc
      intro x hx
      have : x ∈ Icc (-1 / 2 : ℝ) (-r) ∪ Icc r (1 / 2) := Or.inl hx
      rw [← hset] at this; exact this
    have hB : IntegrableOn (fun x => G x y) (Icc r (1 / 2 : ℝ)) := by
      refine (hGy.mono ?_).integrableOn_compact isCompact_Icc
      intro x hx
      have : x ∈ Icc (-1 / 2 : ℝ) (-r) ∪ Icc r (1 / 2) := Or.inr hx
      rw [← hset] at this; exact this
    rw [hfun, MeasureTheory.integral_indicator hmeas, hset]
    rw [setIntegral_union₀ _ measurableSet_Icc.nullMeasurableSet hA hB]
    · rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
        integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
    · -- a.e. disjoint
      refine measure_mono_null ?_ (measure_singleton (0 : ℝ))
      intro x hx
      have h1 : x ≤ -r := hx.1.2
      have h2 : r ≤ x := hx.2.1
      show x = 0
      linarith
  · rw [ite_eq_right hy]
    have : (fun x => Fcut G T (x, y)) = fun _ => 0 := by
      funext x
      unfold Fcut regionF
      rw [indicator_of_notMem]
      rintro ⟨h1, h2, h3, h4⟩
      apply hy
      exact ⟨le_trans (sqrt3_div_two_le_arcY (abs_le.mpr ⟨by linarith [h1], h2⟩)) h3, h4⟩
    rw [this]; simp

/-- **Fubini on the truncated fundamental domain.** -/
theorem swap_region (G : ℝ → ℝ → ℂ) (T : ℝ) (hT : 1 ≤ T)
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (regionF T)) :
    ∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T, G x y =
      ∫ y in (Real.sqrt 3 / 2)..T,
        ((∫ x in (-1 / 2 : ℝ)..(-arcX y), G x y) + ∫ x in arcX y..(1 / 2), G x y) := by
  have hint := integrable_Fcut G T hG
  have h1 := integral_prod (Fcut G T) (μ := volume) (ν := volume) hint
  have h2 := integral_prod_symm (Fcut G T) (μ := volume) (ν := volume) hint
  have hL : ∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T, G x y = ∫ x, ∫ y, Fcut G T (x, y) := by
    simp_rw [slice_x G T hT]
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
      ← MeasureTheory.integral_indicator measurableSet_Icc]
    congr 1
    funext x
    by_cases hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2)
    · rw [indicator_of_mem hx, ite_eq_left hx]
    · rw [indicator_of_notMem hx, ite_eq_right hx]
  have hR : ∫ y in (Real.sqrt 3 / 2)..T,
        ((∫ x in (-1 / 2 : ℝ)..(-arcX y), G x y) + ∫ x in arcX y..(1 / 2), G x y) =
      ∫ y, ∫ x, Fcut G T (x, y) := by
    simp_rw [slice_y G T hG]
    have hle : Real.sqrt 3 / 2 ≤ T := by
      have : Real.sqrt 3 ≤ 2 := by
        rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    rw [intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc,
      ← MeasureTheory.integral_indicator measurableSet_Icc]
    congr 1
    funext y
    by_cases hy : y ∈ Icc (Real.sqrt 3 / 2) T
    · rw [indicator_of_mem hy, ite_eq_left hy]
    · rw [indicator_of_notMem hy, ite_eq_right hy]
  rw [hL, hR, ← h1, ← h2]


theorem intervalIntegrable_inner (G : ℝ → ℝ → ℂ) (T : ℝ) (hT : 1 ≤ T)
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (regionF T)) :
    IntervalIntegrable (fun x => ∫ y in arcY x..T, G x y) volume (-1 / 2) (1 / 2) := by
  have hint := (integrable_Fcut G T hG).integral_prod_left
  have : (fun x => ∫ y, Fcut G T (x, y)) =
      (Icc (-1 / 2 : ℝ) (1 / 2)).indicator (fun x => ∫ y in arcY x..T, G x y) := by
    funext x
    rw [slice_x G T hT x]
    by_cases hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2)
    · rw [ite_eq_left hx, indicator_of_mem hx]
    · rw [ite_eq_right hx, indicator_of_notMem hx]
  rw [this] at hint
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  exact (integrable_indicator_iff measurableSet_Icc).1 hint

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
