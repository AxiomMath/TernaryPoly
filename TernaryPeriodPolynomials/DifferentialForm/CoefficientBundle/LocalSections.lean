module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Sections

@[expose] public section


/-! Smooth sections on quotient open sets, using canonical zero extension outside the open set. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold SymmetricSpaceCharts
open Set Filter Topology Bundle Manifold
open scoped ContDiff Manifold

def IsSmoothSectionOn (n : ℕ) (U : Set OrbitSpace) (s : Section n) : Prop :=
  ContMDiffOn 𝓘(ℝ, Coordinates) (𝓘(ℝ, Coordinates).prod 𝓘(ℝ, Coefficients n)) ∞ (sectionMap n s) U

theorem smoothOn_sectionFunction (n : ℕ) {U : Set OrbitSpace} (hU : IsOpen U)
    (s : Section n) (hs : IsSmoothSectionOn n U s) :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n) ∞ (sectionFunction n s) (quotientProjection ⁻¹' U) := by
  intro S hS
  have hq := ((chart n S).contMDiffAt_section_iff (IB := 𝓘(ℝ, Coordinates))
    (self_mem_localLift S)).mp ((hs _ hS).contMDiffAt (hU.mem_nhds hS))
  have h := hq.comp S (quotientProjection_contMDiff S)
  apply ContMDiffAt.contMDiffWithinAt
  apply h.congr_of_eventuallyEq
  have hm : S ∈ (localLift S).target := by
    simpa only [localLift_self] using (localLift S).map_source (self_mem_localLift S)
  filter_upwards [(localLift S).open_target.mem_nhds hm] with R hR
  exact sectionFunction_chart n s S R hR

theorem smoothOn_functionSection (n : ℕ) {U : Set OrbitSpace} (hU : IsOpen U)
    (f : Space → Coefficients n) (hf : IsEquivariantFunction n f)
    (hs : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n) ∞ f (quotientProjection ⁻¹' U)) :
    IsSmoothSectionOn n U (functionSection n f) := by
  intro b hbU
  let S := chosenLift b
  have hb : b ∈ (localLift S).source := (bundleCore n).mem_baseSet_at b
  have hlU : localLift S b ∈ quotientProjection ⁻¹' U := by
    change quotientProjection (localLift S b) ∈ U
    rw [projection_localLift S hb]
    exact hbU
  apply ContMDiffAt.contMDiffWithinAt
  apply ((chart n S).contMDiffAt_section_iff (IB := 𝓘(ℝ, Coordinates)) hb).mpr
  have hf' := (hs _ hlU).contMDiffAt
    ((hU.preimage quotientProjection_covering.continuous).mem_nhds hlU)
  have h := hf'.comp b ((localLift_contMDiffOn S).contMDiffAt ((localLift S).open_source.mem_nhds hb))
  apply h.congr_of_eventuallyEq
  filter_upwards [(localLift S).open_source.mem_nhds hb] with c hc
  exact functionSection_chart n f hf S hc

def SmoothSectionOn (n : ℕ) (U : Set OrbitSpace) :=
  {s : Section n // IsSmoothSectionOn n U s ∧ ∀ b ∉ U, s b = 0}

theorem sectionFunction_outside (n : ℕ) {U : Set OrbitSpace} (s : Section n)
    (hs : ∀ b ∉ U, s b = 0) {S : Space} (hS : quotientProjection S ∉ U) :
    sectionFunction n s S = 0 := by
  change coefficientAction n _ (s (quotientProjection S)) = 0
  have hz : s (quotientProjection S) = (0 : Coefficients n) := hs _ hS
  rw [hz]
  exact map_zero _

theorem functionSection_outside (n : ℕ) {U : Set OrbitSpace} (f : Space → Coefficients n)
    (hf : ∀ S, quotientProjection S ∉ U → f S = 0) {b : OrbitSpace} (hb : b ∉ U) :
    functionSection n f b = 0 := by
  apply hf
  simpa only [chosenLift_projection] using hb

end TernaryPoly.PolynomialCoefficientBundle
