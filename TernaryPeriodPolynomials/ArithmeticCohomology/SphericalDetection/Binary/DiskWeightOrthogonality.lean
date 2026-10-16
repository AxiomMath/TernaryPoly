module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.DiskFourierCoefficients
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderNorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspRotationWeight_inner_distinct (cusp : CuspidalRepresentation)
    (first second : cusp.H) (firstWeight secondWeight : ℤ) (distinct : firstWeight ≠ secondWeight)
    (first_rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) first =
      (angle : ℂ) ^ firstWeight • first)
    (second_rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) second =
      (angle : ℂ) ^ secondWeight • second) : inner ℂ first second = 0 := by
  let angle := rotationSeparatingCircle
  have unit_phase : (starRingEnd ℂ) ((angle : ℂ) ^ firstWeight) * (angle : ℂ) ^ firstWeight = 1 := by
    rw [← Circle.coe_zpow, mul_comm, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have equality := cuspUnitary_inner cusp (atInfinity (binaryRotations angle)) first second
  rw [first_rotation, second_rotation, inner_smul_left, inner_smul_right] at equality
  have split : secondWeight = firstWeight + (secondWeight - firstWeight) := by omega
  rw [split, zpow_add₀ (Circle.coe_ne_zero angle)] at equality
  have scaled : (angle : ℂ) ^ (secondWeight - firstWeight) * inner ℂ first second = inner ℂ first second := by
    calc
      _ = ((starRingEnd ℂ) ((angle : ℂ) ^ firstWeight) * (angle : ℂ) ^ firstWeight) *
          (angle : ℂ) ^ (secondWeight - firstWeight) * inner ℂ first second := by rw [unit_phase, one_mul]
      _ = _ := by convert equality using 1; ring
  have annihilates : ((angle : ℂ) ^ (secondWeight - firstWeight) - 1) * inner ℂ first second = 0 := by
    linear_combination scaled
  exact (mul_eq_zero.mp annihilates).resolve_left
    (sub_ne_zero.mpr (rotationSeparationPhase_zpow_ne_one _ (by omega)))

theorem cuspDiskOrbit_inner_above_weight (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (test : cusp.H) (testWeight : ℤ) (above : 2 * halfWeight < testWeight)
    (test_rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) test =
      (angle : ℂ) ^ testWeight • test)
    (point : ℂ) (inside : ‖point‖ < 1) :
    inner ℂ test (cuspDiskOrbit cusp halfWeight vector point) = 0 := by
  obtain ⟨series, expansion, _, weights⟩ := cuspDiskOrbit_exists_taylor cusp halfWeight vector rotation holomorphic
  let radius : NNReal := ⟨(‖point‖ + 1) / 2, by positivity⟩
  have radius_positive : 0 < radius := by change 0 < (‖point‖ + 1) / 2; positivity
  have radius_small : radius < 1 := by change (‖point‖ + 1) / 2 < 1; linarith
  have inside_radius : point ∈ Metric.eball (0 : ℂ) (radius : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    apply ENNReal.coe_lt_coe.mpr
    change ‖point‖ < (‖point‖ + 1) / 2
    linarith
  have sum := (cuspDiskTaylorSeries_onBall cusp halfWeight vector holomorphic series expansion
    radius radius_positive radius_small).hasSum inside_radius
  have mapped := (innerSL ℂ test).hasSum sum
  have zero_term (index : ℕ) : inner ℂ test ((series index) (fun _ => point)) = 0 := by
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, inner_smul_right,
      cuspRotationWeight_inner_distinct cusp test (series.coeff index) testWeight
        (2 * halfWeight - 2 * (index : ℤ)) (by omega) test_rotation (weights index), mul_zero]
  simp only [zero_add, innerSL_apply_apply, zero_term] at mapped
  exact mapped.unique hasSum_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
