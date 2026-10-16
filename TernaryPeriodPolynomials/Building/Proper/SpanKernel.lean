module

public import TernaryPeriodPolynomials.Building.Proper.SpanProjection
public import TernaryPeriodPolynomials.Building.Proper.PlaneFilling
public import TernaryPeriodPolynomials.Building.Span.ComparisonExactness

@[expose] public section


noncomputable section
namespace TernaryPoly.ProperSpanKernel
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains
open SpanChainComparison ProperPlaneComplex ProperSpanProjection

/-- Each actual exact-plane component has a proper-Good triangle filling. -/
theorem component_filling (hplane : PerPlaneFilling) (P : RationalSubspace)
    {z : Chain RationalLine} (hz : z ∈ chains good 2) (he : edgeMap z = 0) :
    ∃ q : Chain RationalLine, q ∈ chains properGood 3 ∧ boundary q = planeProjection P z := by
  by_cases hP : Module.finrank ℚ P = 2
  · obtain ⟨q,hq,hdq⟩ := hplane P hP (planeProjection P z)
      (planeProjection_mem P 2 hz) (planeProjection_cycle P hz he)
    exact ⟨q,chains_mono (planeComplex_le_properGood P hP.le) 3 hq,hdq⟩
  · exact ⟨0,(chains properGood 3).zero_mem,by rw [map_zero,planeProjection_zero_of_not_two P hP hz]⟩

/-- Finite exact-plane decomposition and actual flag coefficient extraction fill the entire kernel. -/
theorem fill_edgeMap_kernel (hplane : PerPlaneFilling)
    {z : Chain RationalLine} (hz : z ∈ chains good 2) (he : edgeMap z = 0) :
    ∃ q : Chain RationalLine, q ∈ chains properGood 3 ∧ boundary q = z := by
  classical
  obtain ⟨S,hS⟩ := exists_plane_decomposition z
  choose q hq hdq using (fun P => component_filling hplane P hz he)
  refine ⟨∑ P ∈ S,q P,(chains properGood 3).sum_mem (fun P _ => hq P),?_⟩
  simpa only [map_sum,hdq] using hS

/-- The exact remaining proper-span kernel hypothesis follows solely from actual per-plane H1. -/
theorem proper_kernel_filling (hplane : PerPlaneFilling) : SpanComparisonExactness.ProperKernelFilling := by
  intro z hz _ he
  exact fill_edgeMap_kernel hplane hz he

/-- The existing actual relative comparison consumes the proved proper-kernel assembly. -/
theorem comparison_injective (hplane : PerPlaneFilling) : Function.Injective comparison :=
  SpanComparisonExactness.comparison_injective (proper_kernel_filling hplane)

/-- Actual rank-two Good filling discharges the proper-span kernel input. -/
theorem proper_kernel_filling_actual : SpanComparisonExactness.ProperKernelFilling :=
  proper_kernel_filling ProperPlaneFilling.perPlaneFilling

/-- The actual relative-to-building comparison is injective. -/
theorem comparison_injective_actual : Function.Injective comparison :=
  comparison_injective ProperPlaneFilling.perPlaneFilling

end TernaryPoly.ProperSpanKernel
