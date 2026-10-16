module

public import Mathlib

@[expose] public section


/-!
# Integral of a function that is constant on the cells of a finite disjoint cover

Formalized by Claude Haiku 5.5.

If `S` is covered by finitely many disjoint measurable cells `F i` (`i ∈ T`) of finite measure,
each contained in `S`, and `f` is constant (`= c i`) on `F i`, then `f` is integrable on `S` and
`∫_S f = ∑ i ∈ T, μ(F i).toReal • c i`. No measurability of `f` is needed.
-/

open MeasureTheory

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellFibreSum

theorem fibre_sum_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) {S : Set α}
    {ι : Type*} (T : Finset ι) (F : ι → Set α) (c : ι → ℂ) (f : α → ℂ)
    (hS : MeasurableSet S) (hF : ∀ i ∈ T, MeasurableSet (F i))
    (hsub : ∀ i ∈ T, F i ⊆ S)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (F i) (F j))
    (hcov : S ⊆ ⋃ i ∈ T, F i) (hfin : ∀ i ∈ T, μ (F i) ≠ ⊤)
    (hc : ∀ i ∈ T, ∀ x ∈ F i, f x = c i) :
    IntegrableOn f S μ ∧ ∫ x in S, f x ∂μ = ∑ i ∈ T, μ.real (F i) • c i := by
  have hpt : S.indicator f = fun x => ∑ i ∈ T, (F i).indicator (fun _ => c i) x := by
    funext x
    by_cases hx : x ∈ S
    · obtain ⟨j, hjT, hxj⟩ := Set.mem_iUnion₂.1 (hcov hx)
      rw [Set.indicator_of_mem hx, Finset.sum_eq_single j]
      · rw [Set.indicator_of_mem hxj, hc j hjT x hxj]
      · intro i hiT hij
        rw [Set.indicator_of_notMem]
        intro hxi
        exact Set.disjoint_left.1 (hdisj i hiT j hjT hij) hxi hxj
      · intro hjT'
        exact absurd hjT hjT'
    · rw [Set.indicator_of_notMem hx]
      symm
      apply Finset.sum_eq_zero
      intro i hiT
      rw [Set.indicator_of_notMem (fun hxi => hx (hsub i hiT hxi))]
  have hint : ∀ i ∈ T, Integrable (fun x => (F i).indicator (fun _ => c i) x) μ :=
    fun i hi => (integrable_indicator_iff (hF i hi)).2 (integrableOn_const (hfin i hi))
  have hIS : IntegrableOn f S μ := by
    rw [← integrable_indicator_iff hS, hpt]
    exact integrable_finsetSum T hint
  refine ⟨hIS, ?_⟩
  rw [← integral_indicator hS, hpt, integral_finsetSum T hint]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_indicator_const (c i) (hF i hi)

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellFibreSum
