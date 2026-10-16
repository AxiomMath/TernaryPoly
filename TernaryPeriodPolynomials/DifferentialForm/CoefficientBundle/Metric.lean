module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Core
public import TernaryPeriodPolynomials.Analysis.PositiveBilinearFinite
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

@[expose] public section

/-! The admissible coefficient metric as a smooth metric on the actual glued bundle. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold SymmetricSpaceCharts
open Set Filter Topology Bundle Manifold ContinuousLinearMap
open scoped ContDiff Manifold

def fiberMetric (n : ℕ) (b : OrbitSpace) : Fiber n b →L[ℝ] Fiber n b →L[ℝ] ℝ :=
  coefficientMetric n (chosenLift b)

@[simp] theorem fiberMetric_apply (n : ℕ) (b : OrbitSpace) (p q : Fiber n b) :
    fiberMetric n b p q = coefficientMetric n (chosenLift b) p q := rfl

theorem fiberMetric_symm (n : ℕ) (b : OrbitSpace) (p q : Fiber n b) :
    fiberMetric n b p q = fiberMetric n b q p := coefficientMetric_symmetric n _ p q

theorem fiberMetric_pos (n : ℕ) (b : OrbitSpace) (p : Fiber n b) (hp : p ≠ 0) :
    0 < fiberMetric n b p p := coefficientMetric_positive n _ p hp

theorem fiberMetric_chart_symm (n : ℕ) (S : Space) {b : OrbitSpace}
    (hb : b ∈ (localLift S).source) (p q : Coefficients n) :
    fiberMetric n b ((chart n S).symm b p) ((chart n S).symm b q) =
      coefficientMetric n (localLift S b) p q := by
  change coefficientMetric n (chosenLift b)
    (((bundleCore n).localTriv S).symm b p) (((bundleCore n).localTriv S).symm b q) = _
  rw [VectorBundleCore.localTriv_symm_apply _ S hb p,
    VectorBundleCore.localTriv_symm_apply _ S hb q]
  change coefficientMetric n (chosenLift b) (coefficientAction n (transitionDeck S (chosenLift b) b) p)
    (coefficientAction n (transitionDeck S (chosenLift b) b) q) = _
  have hs := transitionDeck_spec S (chosenLift b) hb ((bundleCore n).mem_baseSet_at b)
  rw [chosenLift_localLift] at hs
  have h := coefficientMetric_deck_invariant n (transitionDeck S (chosenLift b) b) (localLift S b) p q
  rw [hs] at h
  exact h

theorem fiberMetric_inCoordinates (n : ℕ) (a b : OrbitSpace)
    (hb : b ∈ (localLift (chosenLift a)).source) :
    inCoordinates (Coefficients n) (Fiber n) (Coefficients n →L[ℝ] ℝ)
      (fun b => Fiber n b →L[ℝ] ℝ) a b a b (fiberMetric n b) =
        coefficientMetric n (localLift (chosenLift a) b) := by
  have hb' : b ∈ (trivializationAt (Coefficients n) (Fiber n) a).baseSet := hb
  ext p q
  rw [inCoordinates_apply_eq₂ hb' hb' (by simp)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  exact fiberMetric_chart_symm n (chosenLift a) hb p q

theorem contMDiffOn_chart_metric (n : ℕ) (S : Space) :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ) ∞
      (fun b => coefficientMetric n (localLift S b)) (localLift S).source :=
  (contMDiff_coefficientMetric n).comp_contMDiffOn (localLift_contMDiffOn S)

theorem contMDiff_fiberMetric (n : ℕ) :
    ContMDiff 𝓘(ℝ, Coordinates)
      (𝓘(ℝ, Coordinates).prod 𝓘(ℝ, Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ)) ∞
      (fun b => TotalSpace.mk' (Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ) b (fiberMetric n b)) := by
  intro a
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  have h := (contMDiffOn_chart_metric n (chosenLift a)).contMDiffAt
    ((localLift (chosenLift a)).open_source.mem_nhds ((bundleCore n).mem_baseSet_at a))
  apply h.congr_of_eventuallyEq
  filter_upwards [(localLift (chosenLift a)).open_source.mem_nhds ((bundleCore n).mem_baseSet_at a)] with b hb
  exact fiberMetric_inCoordinates n a b hb

def bundleContMDiffRiemannianMetric (n : ℕ) :
    ContMDiffRiemannianMetric 𝓘(ℝ, Coordinates) ∞ (Coefficients n) (Fiber n) where
  inner := fiberMetric n
  symm := fiberMetric_symm n
  pos := fiberMetric_pos n
  isVonNBounded b := PositiveBilinearFinite.isVonNBounded_unitBall
    (coefficientMetric n (chosenLift b)) (coefficientMetric_positive n (chosenLift b))
  contMDiff := contMDiff_fiberMetric n

end TernaryPoly.PolynomialCoefficientBundle
