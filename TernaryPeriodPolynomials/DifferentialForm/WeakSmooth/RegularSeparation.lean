module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularCurrent

@[expose] public section


/-! Faithfulness of genuine continuous scalar currents on actual open coordinate domains. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory Measure
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ]

/-- A continuous local coefficient whose genuine scalar test current vanishes is zero on its
actual open domain. This is literal test separation, including support inside the domain. -/
theorem scalarRegularCurrent_eq_zero_iff (Ω : TopologicalSpace.Opens E) (f : E → ℝ)
    (hf : ContinuousOn f Ω) : scalarRegularCurrent μ Ω f hf = 0 ↔ EqOn f 0 Ω := by
  constructor
  · intro h
    have hae := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn Ω.isOpen.measurableSet (μ := μ)) ?_
    · apply eqOn_open_of_ae_eq ((ae_restrict_iff' Ω.isOpen.measurableSet).2 hae)
        Ω.isOpen hf continuousOn_const
    · intro g hg hgc hgs
      let φ : 𝓓(Ω, ℝ) := ⟨g, hg, hgc, hgs⟩
      have hh := LinearMap.congr_fun h φ
      change (∫ x, f x * g x ∂μ) = 0 at hh
      simpa only [smul_eq_mul, mul_comm] using hh
  · intro h
    exact (scalarRegularCurrent_congr μ Ω hf continuousOn_const h).trans
      (scalarRegularCurrent_zero μ Ω)

/-- Genuine continuous scalar currents agree precisely when their coefficients agree on the
actual test domain. -/
theorem scalarRegularCurrent_eq_iff (Ω : TopologicalSpace.Opens E) (f g : E → ℝ)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω) :
    scalarRegularCurrent μ Ω f hf = scalarRegularCurrent μ Ω g hg ↔ EqOn f g Ω := by
  constructor
  · intro h
    have hdiff : scalarRegularCurrent μ Ω (f + (-1 : ℝ) • g)
        (hf.add (hg.const_smul (-1))) = 0 := by
      rw [scalarRegularCurrent_add μ Ω f ((-1 : ℝ) • g) hf (hg.const_smul _),
        scalarRegularCurrent_smul μ Ω (-1) g hg, h]
      module
    have hz := (scalarRegularCurrent_eq_zero_iff μ Ω _ _).mp hdiff
    intro x hx
    have hh := hz hx
    change f x + (-1) * g x = 0 at hh
    linarith
  · exact scalarRegularCurrent_congr μ Ω hf hg

/-- On a nonempty actual domain the genuine Haar mass current is nonzero. -/
theorem scalarRegularCurrent_one_ne_zero (Ω : TopologicalSpace.Opens E)
    (hΩ : (Ω : Set E).Nonempty) :
    scalarRegularCurrent μ Ω (fun _ => 1) continuousOn_const ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := hΩ
  have hh := (scalarRegularCurrent_eq_zero_iff μ Ω _ continuousOn_const).mp h hx
  norm_num at hh

end TernaryPoly.PolynomialFormWeakSmooth
