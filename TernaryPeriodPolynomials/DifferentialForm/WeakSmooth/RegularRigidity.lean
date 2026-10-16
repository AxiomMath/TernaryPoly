module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularSeparation
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularDerivative
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.BoxNeighborhood

@[expose] public section

/-! Actual zero-gradient rigidity with genuine Haar-integral constant currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory Measure
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rigidity does not require a prescribed normalization of its nonzero mass current. -/
theorem scalarWeakZeroRigid_replace (Ω : TopologicalSpace.Opens E) (I J : ScalarWeak Ω)
    (hI : ScalarWeakZeroRigid Ω I) (hJ : HasZeroWeakDerivative Ω J) (hJ0 : J ≠ 0) :
    ScalarWeakZeroRigid Ω J := by
  obtain ⟨c, hc⟩ := hI J hJ
  have hc0 : c ≠ 0 := by
    intro hz
    apply hJ0
    simpa only [hz, zero_smul] using hc
  intro T hT
  obtain ⟨d, hd⟩ := hI T hT
  refine ⟨d / c, ?_⟩
  rw [hc, smul_smul, div_mul_cancel₀ d hc0]
  exact hd

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsAddHaarMeasure μ]

/-- The genuine constant-current embedding agrees with scalar multiplication of the mass current. -/
theorem scalarRegularCurrent_const (Ω : TopologicalSpace.Opens E) (c : ℝ) :
    scalarRegularCurrent μ Ω (fun _ => c) continuousOn_const =
      c • scalarRegularCurrent μ Ω (fun _ => 1) continuousOn_const := by
  apply LinearMap.ext
  intro φ
  change (∫ x, c * φ x ∂μ) = c * ∫ x, 1 * φ x ∂μ
  simp only [one_mul, integral_const_mul]

/-- Genuine Haar constant currents have zero weak derivative on every actual open domain. -/
theorem scalarRegularCurrent_const_closed (Ω : TopologicalSpace.Opens E) (c : ℝ) :
    HasZeroWeakDerivative Ω (scalarRegularCurrent μ Ω (fun _ => c) continuousOn_const) := by
  intro v
  rw [scalarRegularCurrent_derivative μ Ω (fun _ => c) contDiffOn_const v]
  apply (scalarRegularCurrent_eq_zero_iff μ Ω _ _).mpr
  intro x _
  simp

/-- Whenever actual algebraic-current rigidity has been proved and the domain is nonempty,
its constant line is exactly the line of genuine Haar-integral constant functions. -/
theorem scalarWeakZeroRigid_regular (Ω : TopologicalSpace.Opens E) (I : ScalarWeak Ω)
    (hI : ScalarWeakZeroRigid Ω I) (hΩ : (Ω : Set E).Nonempty) :
    ScalarWeakZeroRigid Ω (scalarRegularCurrent μ Ω (fun _ => 1) continuousOn_const) :=
  scalarWeakZeroRigid_replace Ω I _ hI (scalarRegularCurrent_const_closed μ Ω 1)
    (scalarRegularCurrent_one_ne_zero μ Ω hΩ)

/-- Every actual zero-gradient current on an affine coordinate box is represented by an actual
constant function with respect to the coordinate Haar measure. No chosen determinant convention
is needed to identify this line. -/
theorem coordinateTestBox_zeroGradient_regular
    (ν : Measure SymmetricSpaceCharts.Coordinates) [IsAddHaarMeasure ν]
    (e : WeakCubeFive ≃L[ℝ] SymmetricSpaceCharts.Coordinates) (a : SymmetricSpaceCharts.Coordinates)
    (T : ScalarWeak (coordinateTestBox e a)) (hT : HasZeroWeakDerivative (coordinateTestBox e a) T) :
    ∃ c : ℝ, T = scalarRegularCurrent ν (coordinateTestBox e a) (fun _ => c) continuousOn_const := by
  have hn : (coordinateTestBox e a : Set SymmetricSpaceCharts.Coordinates).Nonempty := by
    rw [coordinateTestBox_eq_image]
    exact ⟨_, ⟨weakCubeCenter, weakCubeCenter_mem, rfl⟩⟩
  obtain ⟨c, hc⟩ := scalarWeakZeroRigid_regular ν (coordinateTestBox e a)
    (coordinateTestBoxMass e a) (coordinateTestBoxMass_rigid e a) hn T hT
  exact ⟨c, hc.trans (scalarRegularCurrent_const ν (coordinateTestBox e a) c).symm⟩

end TernaryPoly.PolynomialFormWeakSmooth
