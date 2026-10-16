module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.VariablePrimitive
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.PrimitiveSupport
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.IntervalBounds

@[expose] public section


/-! Genuine compact support of a fiberwise zero-mass test antiderivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Vanishing fiber integral gives a compact primitive whose support stays in the same cylinder. -/
theorem fiberTestPrimitiveRaw_support (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) (hz : fiberTestIntegral Ω f = 0) :
    HasCompactSupport (fiberTestPrimitiveRaw f) ∧
      tsupport (fiberTestPrimitiveRaw f) ⊆ (testCylinder Ω : Set (E × ℝ)) := by
  rcases (tsupport f).eq_empty_or_nonempty with he | hn
  · have hf : ∀ p, f p = 0 := fun p => image_eq_zero_of_notMem_tsupport (by rw [he]; simp)
    have hp : fiberTestPrimitiveRaw f = 0 := by
      funext p
      simp [fiberTestPrimitiveRaw, hf]
    rw [hp]
    exact ⟨HasCompactSupport.zero, by simp⟩
  · obtain ⟨a, b, hab, hi⟩ := compact_subset_open_convex_interval
      (f.hasCompactSupport.image continuous_snd) (hn.image Prod.snd) isOpen_Ioo (convex_Ioo 0 1)
      (by rintro _ ⟨p, hp, rfl⟩; exact (f.tsupport_subset hp).2)
    have ha : 0 ≤ a := by
      obtain ⟨p, hp⟩ := hn
      have ht := hab ⟨p, hp, rfl⟩
      exact (hi ⟨le_rfl, (ht.1.trans ht.2).le⟩).1.le
    have hscalar (x : E) : Function.support (fun t => f (x, t)) ⊆ Ioo a b := by
      intro t ht
      exact hab ⟨(x, t), subset_tsupport f ht, rfl⟩
    have hint (x : E) : ∫ t, f (x, t) = 0 := by
      have hfi : Function.support (fun t => f (x, t)) ⊆ Ioc 0 1 := by
        intro t ht
        exact Ioo_subset_Ioc_self (f.tsupport_subset (subset_tsupport f ht)).2
      rw [← intervalIntegral.integral_eq_integral_of_support_subset hfi]
      exact congrArg (fun g : 𝓓(Ω, ℝ) => g x) hz
    have hts : tsupport (fiberTestPrimitiveRaw f) ⊆
        (Prod.fst '' tsupport f) ×ˢ Icc a b := by
      apply closure_minimal _ ((f.hasCompactSupport.image continuous_fst).isClosed.prod isClosed_Icc)
      intro p hp
      refine ⟨?_, ?_⟩
      · by_contra hfst
        have hf (t : ℝ) : f (p.1, t) = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hfst ⟨(p.1, t), ht, rfl⟩)
        apply hp
        simp [fiberTestPrimitiveRaw, hf]
      · exact scalarTestPrimitive_tsupport_of_le ha (hscalar p.1) (hint p.1)
          (subset_tsupport (scalarTestPrimitive 0 (fun t => f (p.1, t))) hp)
    refine ⟨((f.hasCompactSupport.image continuous_fst).prod isCompact_Icc).of_isClosed_subset
      (isClosed_tsupport _) hts, ?_⟩
    intro p hp
    obtain ⟨x, hx, he⟩ := (hts hp).1
    exact ⟨he ▸ (f.tsupport_subset hx).1, hi (hts hp).2⟩

end TernaryPoly.PolynomialFormWeakSmooth
