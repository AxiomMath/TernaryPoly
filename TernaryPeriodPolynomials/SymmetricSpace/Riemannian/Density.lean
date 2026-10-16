module

public import TernaryPeriodPolynomials.Analysis.BilinearVolumeDensity
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricContinuousBilinear
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricQuotientInvariant

@[expose] public section


/-! The genuine positive trace metric has the correct smooth coordinate volume density. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian

open Matrix SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- The Gram matrix of the actual trace metric in the five coordinates. -/
def coordinateGram (x : Coordinates) : Matrix (Fin 5) (Fin 5) ℝ :=
  LinearMap.BilinForm.toMatrix' (coordinateBilin x)

@[simp] theorem coordinateGram_apply (x : Coordinates) (i j : Fin 5) :
    coordinateGram x i j = coordinatePair x (Pi.single i 1) (Pi.single j 1) := rfl

theorem coordinateGram_posDef (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    (coordinateGram x).PosDef :=
  BilinearVolumeDensity.gram_posDef (coordinateBilin x) (coordinatePair_comm x)
    (coordinatePair_pos x hx)

/-- Coordinate density for the actual intrinsic Riemannian metric. -/
def coordinateDensity (x : Coordinates) : ℝ := Real.sqrt (coordinateGram x).det

theorem coordinateDensity_pos (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    0 < coordinateDensity x := Real.sqrt_pos.mpr (coordinateGram_posDef x hx).det_pos

theorem contDiffOn_coordinateGram : ContDiffOn ℝ ∞ coordinateGram positiveCoordinates := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  change ContDiffOn ℝ ∞ (fun x => coordinateContinuousBilin x (Pi.single i 1) (Pi.single j 1)) _
  exact (contDiffOn_coordinateContinuousBilin.clm_apply contDiffOn_const).clm_apply contDiffOn_const

theorem contDiffOn_coordinateGram_det :
    ContDiffOn ℝ ∞ (fun x => (coordinateGram x).det) positiveCoordinates := by
  simp only [det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply ContDiffOn.mul contDiffOn_const
  apply contDiffOn_prod
  intro i _
  exact contDiffOn_pi.mp (contDiffOn_pi.mp contDiffOn_coordinateGram (σ i)) i

theorem contDiffOn_coordinateDensity : ContDiffOn ℝ ∞ coordinateDensity positiveCoordinates :=
  contDiffOn_coordinateGram_det.sqrt (fun x hx => ne_of_gt (coordinateGram_posDef x hx).det_pos)

/-- The density transforms by the absolute Jacobian of the literal quotient-chart transition. -/
theorem coordinateDensity_quotientChart (S T : Space) (x : Coordinates)
    (hx : x ∈ ((quotientChart S).symm.trans (quotientChart T)).source) :
    coordinateDensity x =
      |(fderiv ℝ ((quotientChart S).symm.trans (quotientChart T)) x).toLinearMap.det| *
        coordinateDensity (((quotientChart S).symm.trans (quotientChart T)) x) := by
  let L := (fderiv ℝ ((quotientChart S).symm.trans (quotientChart T)) x).toLinearMap
  have h : LinearMap.BilinForm.comp (coordinateBilin (((quotientChart S).symm.trans (quotientChart T)) x)) L L =
      coordinateBilin x := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact coordinatePair_quotientChart_invariant S T x hx v w
  change BilinearVolumeDensity.density (coordinateBilin x) = _
  rw [← h, BilinearVolumeDensity.density_comp]
  rfl

/-- The density law applies to every pair of actual atlas charts. -/
theorem coordinateDensity_atlas (e e' : OpenPartialHomeomorph OrbitSpace Coordinates)
    (he : e ∈ atlas Coordinates OrbitSpace) (he' : e' ∈ atlas Coordinates OrbitSpace)
    (x : Coordinates) (hx : x ∈ (e.symm.trans e').source) :
    coordinateDensity x = |(fderiv ℝ (e.symm.trans e') x).toLinearMap.det| *
      coordinateDensity ((e.symm.trans e') x) := by
  obtain ⟨S, rfl⟩ := he
  obtain ⟨T, rfl⟩ := he'
  exact coordinateDensity_quotientChart S T x hx

end TernaryPoly.SymmetricSpaceRiemannian
