module

public import Mathlib

@[expose] public section


/-!
# Tiling of the plane by unit squares: the integral over `ℝ²` is the sum of the integrals over the
integer translates of the unit square

Paper: ("the integrated radical
quotient is compact, so Fubini applies"; unfolding the free orbits of the radical lattice `ℤ²` to the real
integral `∫_{𝔸²}`).

`tiling_prod`: a continuous function on `ℝ × ℝ` dominated on the translates `(ℓ₁, ℓ₂) + [0,1]²` by a
summable family is integrable, and its integral is the sum over `ℓ ∈ ℤ²` of the iterated integrals over the
translated unit squares. `tiling_pi`: the same for `Fin 2 → ℝ`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

theorem Ioc_int_disjoint {k k' : ℤ} (h : k ≠ k') :
    Disjoint (Ioc (k : ℝ) (k + 1)) (Ioc (k' : ℝ) (k' + 1)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hx'
  have a1 : (k : ℝ) < k' + 1 := lt_of_lt_of_le h1 h4
  have a2 : (k' : ℝ) < k + 1 := lt_of_lt_of_le h3 h2
  have b1 : k < k' + 1 := by exact_mod_cast a1
  have b2 : k' < k + 1 := by exact_mod_cast a2
  exact h (by omega)

theorem tiling_prod {g : ℝ × ℝ → ℂ} (hg : Continuous g) (B : ℤ × ℤ → ℝ) (hB : Summable B)
    (hgB : ∀ (ℓ : ℤ × ℤ) (a b : ℝ), a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      ‖g ((ℓ.1 : ℝ) + a, (ℓ.2 : ℝ) + b)‖ ≤ B ℓ) :
    Integrable g ∧ ∫ z, g z =
      ∑' ℓ : ℤ × ℤ, ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, g ((ℓ.1 : ℝ) + a, (ℓ.2 : ℝ) + b) := by
  set s : ℤ × ℤ → Set (ℝ × ℝ) := fun ℓ => Ioc (ℓ.1 : ℝ) (ℓ.1 + 1) ×ˢ Ioc (ℓ.2 : ℝ) (ℓ.2 + 1) with hs
  have hm : ∀ ℓ, MeasurableSet (s ℓ) := fun ℓ => measurableSet_Ioc.prod measurableSet_Ioc
  have hU : ⋃ ℓ, s ℓ = univ := by
    apply Set.eq_univ_of_forall
    intro z
    refine Set.mem_iUnion.2 ⟨(⌈z.1⌉ - 1, ⌈z.2⌉ - 1), ?_⟩
    simp only [hs, Set.mem_prod, Set.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := Int.ceil_lt_add_one z.1
      push_cast; linarith
    · have := Int.le_ceil z.1
      push_cast; linarith
    · have := Int.ceil_lt_add_one z.2
      push_cast; linarith
    · have := Int.le_ceil z.2
      push_cast; linarith
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro ℓ ℓ' hne
    simp only [Function.onFun, hs]
    rw [Set.disjoint_prod]
    by_cases h1 : ℓ.1 = ℓ'.1
    · right
      have h2 : ℓ.2 ≠ ℓ'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact Ioc_int_disjoint h2
    · left
      exact Ioc_int_disjoint h1
  have hbound : ∀ ℓ, ∀ z ∈ s ℓ, ‖g z‖ ≤ B ℓ := by
    intro ℓ z hz
    simp only [hs, Set.mem_prod, Set.mem_Ioc] at hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    have := hgB ℓ (z.1 - ℓ.1) (z.2 - ℓ.2) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    simpa using this
  have hint : ∀ ℓ, IntegrableOn g (s ℓ) := by
    intro ℓ
    refine (hg.continuousOn.integrableOn_compact
      ((isCompact_Icc (a := (ℓ.1 : ℝ)) (b := ℓ.1 + 1)).prod
        (isCompact_Icc (a := (ℓ.2 : ℝ)) (b := ℓ.2 + 1)))).mono_set ?_
    exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hvol : ∀ ℓ, volume (s ℓ) = 1 := by
    intro ℓ
    simp [hs, Measure.volume_eq_prod, Measure.prod_prod]
  have hnorm : ∀ ℓ, ∫ z in s ℓ, ‖g z‖ ≤ B ℓ := by
    intro ℓ
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := s ℓ) (f := fun z => ‖g z‖)
      (C := B ℓ) (by rw [hvol]; simp) (fun z hz => by simpa using hbound ℓ z hz)
    refine le_trans (le_abs_self _) (le_trans (by simpa using this) ?_)
    simp [Measure.real, hvol]
  have hsum : Summable fun ℓ => ∫ z in s ℓ, ‖g z‖ :=
    Summable.of_nonneg_of_le (fun ℓ => integral_nonneg fun z => norm_nonneg _) hnorm hB
  have hIU := integrableOn_iUnion_of_summable_integral_norm hint hsum
  rw [hU, integrableOn_univ] at hIU
  refine ⟨hIU, ?_⟩
  have hIU' : IntegrableOn g (⋃ ℓ, s ℓ) := by rw [hU, integrableOn_univ]; exact hIU
  have h1 := integral_iUnion hm hd hIU'
  rw [hU, Measure.restrict_univ] at h1
  rw [h1]
  refine tsum_congr fun ℓ => ?_
  have h2 : ∫ z in s ℓ, g z = ∫ x in Ioc (ℓ.1 : ℝ) (ℓ.1 + 1), ∫ y in Ioc (ℓ.2 : ℝ) (ℓ.2 + 1), g (x, y) := by
    have := setIntegral_prod g (μ := volume) (ν := volume) (s := Ioc (ℓ.1 : ℝ) (ℓ.1 + 1))
      (t := Ioc (ℓ.2 : ℝ) (ℓ.2 + 1)) (by simpa [hs, Measure.volume_eq_prod] using hint ℓ)
    simpa [hs, Measure.volume_eq_prod] using this
  rw [h2]
  simp only [← intervalIntegral.integral_of_le (by linarith : (ℓ.1 : ℝ) ≤ ℓ.1 + 1),
    ← intervalIntegral.integral_of_le (by linarith : (ℓ.2 : ℝ) ≤ ℓ.2 + 1)]
  have e1 : ∀ (F : ℝ → ℂ) (c : ℝ), ∫ x in c..(c + 1), F x = ∫ a in (0 : ℝ)..1, F (c + a) := by
    intro F c
    have := intervalIntegral.integral_comp_add_left F c (a := 0) (b := 1)
    simp only [add_zero] at this
    exact this.symm
  rw [e1 (fun x => ∫ y in (ℓ.2 : ℝ)..(ℓ.2 + 1), g (x, y)) (ℓ.1 : ℝ)]
  refine intervalIntegral.integral_congr fun a _ => ?_
  exact e1 (fun y => g ((ℓ.1 : ℝ) + a, y)) (ℓ.2 : ℝ)

theorem tiling_pi {g : (Fin 2 → ℝ) → ℂ} (hg : Continuous g) (B : (Fin 2 → ℤ) → ℝ)
    (hB : Summable B)
    (hgB : ∀ (ℓ : Fin 2 → ℤ) (a b : ℝ), a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      ‖g ![(ℓ 0 : ℝ) + a, (ℓ 1 : ℝ) + b]‖ ≤ B ℓ) :
    Integrable g ∧ ∫ v, g v =
      ∑' ℓ : Fin 2 → ℤ, ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, g ![(ℓ 0 : ℝ) + a, (ℓ 1 : ℝ) + b] := by
  let e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have he : MeasurePreserving e volume volume := volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  let g' : ℝ × ℝ → ℂ := fun z => g ![z.1, z.2]
  have hg'e : ∀ v, g' (e v) = g v := by
    intro v
    simp only [g', e, MeasurableEquiv.piFinTwo_apply]
    congr 1
    funext i; fin_cases i <;> rfl
  have hg' : Continuous g' := by
    refine hg.comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  let eqv : ℤ × ℤ ≃ (Fin 2 → ℤ) := (finTwoArrowEquiv ℤ).symm
  let B' : ℤ × ℤ → ℝ := fun ℓ => B (eqv ℓ)
  have hB' : Summable B' := (eqv.summable_iff).2 hB
  have hgB' : ∀ (ℓ : ℤ × ℤ) (a b : ℝ), a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      ‖g' ((ℓ.1 : ℝ) + a, (ℓ.2 : ℝ) + b)‖ ≤ B' ℓ := by
    intro ℓ a b ha hb
    have := hgB (eqv ℓ) a b ha hb
    simpa [g', B', eqv] using this
  obtain ⟨hint, hval⟩ := tiling_prod hg' B' hB' hgB'
  refine ⟨?_, ?_⟩
  · have : Integrable (g' ∘ e) volume := (he.integrable_comp_emb e.measurableEmbedding).2 hint
    convert this using 1
    funext v; exact (hg'e v).symm
  · have h1 : ∫ v, g v = ∫ v, g' (e v) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => (hg'e v).symm)
    rw [h1, he.integral_comp', hval]
    rw [← eqv.tsum_eq]
    refine tsum_congr fun ℓ => ?_
    simp [g', eqv]


end TernaryPeriodPolynomials.Argument.EisensteinClass
