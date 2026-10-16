module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.UnitTest
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamParametricIntegral

@[expose] public section


/-! Actual compact-test integration along a product interval. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory SmoothLocalDeRham
open scoped ContDiff Distributions

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def testCylinder (Ω : TopologicalSpace.Opens E) : TopologicalSpace.Opens (E × ℝ) :=
  ⟨(Ω : Set E) ×ˢ Ioo 0 1, Ω.isOpen.prod isOpen_Ioo⟩

/-- The genuine integral over the compact interval in the last coordinate. -/
def fiberTestIntegralRaw (f : E × ℝ → ℝ) (x : E) : ℝ :=
  ∫ t in (0 : ℝ)..1, f (x, t)

/-- Integrating a genuine jointly smooth function along this fixed compact interval is smooth. -/
theorem fiberTestIntegralRaw_contDiff {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fiberTestIntegralRaw f) := by
  have h := parameterIntegral_smooth isOpen_univ hf.contDiffOn
  have he : sliceDomain (univ : Set (E × ℝ)) = univ := by ext; simp [sliceDomain]
  rw [he, contDiffOn_univ] at h
  exact h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Fiber integration has support contained in the projection of the original compact support. -/
theorem fiberTestIntegralRaw_tsupport {f : E × ℝ → ℝ} (hf : HasCompactSupport f) :
    tsupport (fiberTestIntegralRaw f) ⊆ Prod.fst '' tsupport f := by
  apply closure_minimal _ (hf.image continuous_fst).isClosed
  intro x hx
  by_contra hn
  have hz (t : ℝ) : f (x, t) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hn ⟨(x, t), ht, rfl⟩)
  apply hx
  change (∫ t in (0 : ℝ)..1, f (x, t)) = 0
  simp only [hz, intervalIntegral.integral_zero]

/-- Fiber integration is an actual map between actual compact smooth test spaces. -/
def fiberTestIntegral (Ω : TopologicalSpace.Opens E) :
    𝓓(testCylinder Ω, ℝ) →ₗ[ℝ] 𝓓(Ω, ℝ) where
  toFun f :=
    { toFun := fiberTestIntegralRaw f
      contDiff' := fiberTestIntegralRaw_contDiff f.contDiff
      hasCompactSupport' := (f.hasCompactSupport.image continuous_fst).of_isClosed_subset
        (isClosed_tsupport _) (fiberTestIntegralRaw_tsupport f.hasCompactSupport)
      tsupport_subset' := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := fiberTestIntegralRaw_tsupport f.hasCompactSupport hx
        exact (f.tsupport_subset hp).1 }
  map_add' f g := by
    apply TestFunction.ext
    intro x
    exact intervalIntegral.integral_add
      ((f.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
      ((g.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
  map_smul' c f := by
    apply TestFunction.ext
    intro x
    exact intervalIntegral.integral_smul c (fun t => f (x, t))

@[simp] theorem fiberTestIntegral_apply (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) (x : E) :
    fiberTestIntegral Ω f x = ∫ t in (0 : ℝ)..1, f (x, t) := rfl

end TernaryPoly.PolynomialFormWeakSmooth
