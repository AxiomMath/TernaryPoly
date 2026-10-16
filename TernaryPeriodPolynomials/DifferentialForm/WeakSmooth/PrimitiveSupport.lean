module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.Primitive

@[expose] public section


/-! Support control for an antiderivative based anywhere to the left of the test support. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory

/-- Zero total mass permits the same compact support bound for any basepoint to the left. -/
theorem scalarTestPrimitive_tsupport_of_le {c a b : ℝ} {f : ℝ → ℝ} (hca : c ≤ a)
    (hs : Function.support f ⊆ Ioo a b) (hz : ∫ x, f x = 0) :
    tsupport (scalarTestPrimitive c f) ⊆ Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  rw [mem_Icc, not_and_or] at h
  rcases h with h | h
  · have hxa : x < a := lt_of_not_ge h
    apply hx
    change (∫ t in c..x, f t) = 0
    calc
      _ = ∫ t in c..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        have hta : t < a := ht.2.trans_le (max_le hca hxa.le)
        by_contra hft
        exact (not_lt_of_ge (hs hft).1.le) hta
      _ = 0 := by simp
  · have hbx : b < x := lt_of_not_ge h
    apply hx
    change (∫ t in c..x, f t) = 0
    exact (intervalIntegral.integral_eq_integral_of_support_subset
      (fun t ht => ⟨hca.trans_lt (hs ht).1, (hs ht).2.le.trans hbx.le⟩)).trans hz

end TernaryPoly.PolynomialFormWeakSmooth
