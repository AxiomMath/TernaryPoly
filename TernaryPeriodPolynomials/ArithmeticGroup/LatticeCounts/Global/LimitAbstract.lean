module

public import Mathlib

@[expose] public section


open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Global limit: abstract measure-theoretic lemmas

* `exhaust_integrable_tendsto`: if `f` is measurable and the integrals of `‖f‖` over an increasing, covering family `U S` indexed by finite subsets of a countable set are bounded, then `f` is
  integrable and `∫_{U S} f → ∫ f` along finite sets (`AECover`).
* `lintegral_fintype_prod_eq_prod`: Fubini for `ℝ≥0∞`-valued products of functions of single coordinates, for `Measure.pi` over a finite index type (the `lintegral` analogue of
  Mathlib's `integral_fintype_prod_eq_prod`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitAbstract

/-- **Exhaustion by an increasing family indexed by finite sets** (monotone convergence for the bound, dominated convergence for
the limit): if `f` is measurable, the sets `U S` are measurable, increasing in `S` and cover the space, and the integrals of `‖f‖` over `U S`
are bounded, then `f` is integrable and `∫_{U S} f → ∫ f` along finite sets. -/
theorem exhaust_integrable_tendsto {α ι E : Type*} [MeasurableSpace α] (μ : Measure α) [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Finset ι → Set α) (hmeas : ∀ S, MeasurableSet (U S))
    (hmono : Monotone U) (hcover : ∀ x, ∃ S, x ∈ U S) (f : α → E) (hf : AEStronglyMeasurable f μ) (B : ℝ≥0)
    (hB : ∀ S, ∫⁻ x in U S, ‖f x‖ₑ ∂μ ≤ B) :
    Integrable f μ ∧ Tendsto (fun S => ∫ x in U S, f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hcov : AECover μ (atTop : Filter (Finset ι)) U :=
    { ae_eventually_mem := ae_of_all _ fun x => by
        obtain ⟨S, hS⟩ := hcover x
        exact (eventually_ge_atTop S).mono fun T hT => hmono hT hS
      measurableSet := hmeas }
  have hint : Integrable f μ :=
    hcov.integrable_of_lintegral_enorm_bounded' B hf (Eventually.of_forall hB)
  exact ⟨hint, hcov.integral_tendsto_of_countably_generated hint⟩

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf _)]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf _)

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitAbstract
