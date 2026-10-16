module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtFactor
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointPeriod

@[expose] public section


/-!
# Weight-generic holomorphic endpoint form

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of the `halfWeight` results of `BinaryEndpointHolomorphic`, `BinaryEndpointForm`,
`BinaryEndpointFormAnalytic` and `BinaryEndpointPeriod` for an arbitrary integer rotation weight
`wt` with `wt = -(degree + 3)`, with the real factor `height ^ (halfWeight + 1)` replaced by
`wtFactor wt height * height`.  In particular the odd weights of even degree are covered.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

theorem binaryAffineRootWeightWt (degree : ℕ) (wt : ℤ)
    (weight : wt = -((degree : ℤ) + 3)) (height : ℝ) (positive : 0 < height) :
    (1 / (Real.sqrt height : ℂ)) ^ (degree + 1) = ((wtFactor wt height * height : ℝ) : ℂ) := by
  have root_ne : Real.sqrt height ≠ 0 := (Real.sqrt_pos.mpr positive).ne'
  have real_equality : (1 / Real.sqrt height) ^ (degree + 1) = wtFactor wt height * height := by
    calc
      _ = Real.sqrt height ^ (-((degree + 1 : ℕ) : ℤ)) := by
        simp only [one_div, inv_pow, zpow_neg, zpow_natCast]
      _ = Real.sqrt height ^ (wt + 2) := by
        congr 1
        omega
      _ = Real.sqrt height ^ wt * Real.sqrt height ^ (2 : ℤ) := zpow_add₀ root_ne wt 2
      _ = _ := by
        rw [← wtFactor_eq_sqrt_zpow wt positive, zpow_ofNat, Real.sq_sqrt positive.le]
  exact_mod_cast real_equality

/-- The height factors cancel exactly at the cohomological weight. -/
theorem binaryAffineOrbitVector_single_weightedWt (cusp : CuspidalRepresentation) (degree : ℕ)
    (wt : ℤ) (weight : wt = -((degree : ℤ) + 3))
    (vector : cusp.H) (point : ℂ) (positive : 0 < point.im) (position : Fin (degree + 2)) :
    point.im⁻¹ •
        binaryAffineOrbitVector cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point position =
      (binaryWeightBasis (degree + 1)).coord position (binaryPointPower (degree + 1) point) •
        cuspWeightedAffineOrbitWt cusp wt vector point := by
  rw [binaryAffineOrbitVector_single_zero cusp degree vector point positive,
    binaryAffineRootWeightWt degree wt weight point.im positive, mul_smul,
    Complex.coe_smul,
    smul_comm (wtFactor wt point.im * point.im), smul_comm point.im⁻¹, smul_smul]
  have cancel : point.im⁻¹ * (wtFactor wt point.im * point.im) = wtFactor wt point.im := by
    calc
      _ = wtFactor wt point.im * (point.im⁻¹ * point.im) := by ring
      _ = _ := by rw [inv_mul_cancel₀ positive.ne', mul_one]
  rw [cancel]
  rfl

def binaryEndpointHolomorphicFormWt (cusp : CuspidalRepresentation) (degree : ℕ)
    (wt : ℤ) (vector : cusp.H) (point : ℂ) : Fin (degree + 2) → cusp.H :=
  fun position => (binaryWeightBasis (degree + 1)).coord position (binaryPointPower (degree + 1) point) •
    cuspWeightedAffineOrbitWt cusp wt vector point

theorem binaryEndpointHolomorphicForm_eqWt (cusp : CuspidalRepresentation) (degree : ℕ)
    (wt : ℤ) (weight : wt = -((degree : ℤ) + 3))
    (vector : cusp.H) (point : ℂ) (positive : 0 < point.im) :
    point.im⁻¹ • binaryAffineOrbitVector cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point =
      binaryEndpointHolomorphicFormWt cusp degree wt vector point := by
  funext position
  exact binaryAffineOrbitVector_single_weightedWt cusp degree wt weight vector point positive position

theorem binaryEndpointHolomorphicForm_holomorphicWt (cusp : CuspidalRepresentation)
    (degree : ℕ) (wt : ℤ) (vector : cusp.H)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector)
      UpperHalfPlane.upperHalfPlaneSet) :
    DifferentiableOn ℂ (binaryEndpointHolomorphicFormWt cusp degree wt vector)
      UpperHalfPlane.upperHalfPlaneSet := by
  intro point member
  apply differentiableWithinAt_pi.mpr
  intro position
  exact (binaryPointPower_functional_analytic (degree + 1)
    ((binaryWeightBasis (degree + 1)).coord position) point).differentiableAt.differentiableWithinAt.smul
      (holomorphic point member)

def binaryEndpointPeriodWt (cusp : CuspidalRepresentation) (degree : ℕ)
    (wt : ℤ) (vector : cusp.H) (point : ℂ) : Fin (degree + 2) → cusp.H :=
  ∫ parameter : ℝ in 0..1, (point - Complex.I) •
    binaryEndpointHolomorphicFormWt cusp degree wt vector
      (Complex.I + parameter • (point - Complex.I))

theorem binaryEndpointHolomorphicForm_continuousOnWt (cusp : CuspidalRepresentation)
    (degree : ℕ) (wt : ℤ) (vector : cusp.H) :
    ContinuousOn (binaryEndpointHolomorphicFormWt cusp degree wt vector)
      UpperHalfPlane.upperHalfPlaneSet := by
  apply continuousOn_pi.mpr
  intro position
  exact (continuous_iff_continuousAt.mpr (fun point =>
    (binaryPointPower_functional_analytic (degree + 1)
      ((binaryWeightBasis (degree + 1)).coord position) point).continuousAt)).continuousOn.smul
        (cuspWeightedAffineOrbit_continuousOnWt cusp wt vector)

theorem binaryEndpointPeriod_integrableWt (cusp : CuspidalRepresentation) (degree : ℕ)
    (wt : ℤ) (vector : cusp.H) (point : ℂ) (positive : 0 < point.im) :
    IntervalIntegrable (fun parameter : ℝ => (point - Complex.I) •
      binaryEndpointHolomorphicFormWt cusp degree wt vector
        (Complex.I + parameter • (point - Complex.I))) volume 0 1 := by
  have path_continuous : Continuous (fun parameter : ℝ => Complex.I + parameter • (point - Complex.I)) := by
    fun_prop
  exact ((continuousOn_const (c := point - Complex.I)).smul
    ((binaryEndpointHolomorphicForm_continuousOnWt cusp degree wt vector).comp
      path_continuous.continuousOn (fun _ member => upperHalfPlane_straightPath ⟨point, positive⟩ member))).intervalIntegrable_of_Icc
        zero_le_one

end TernaryPeriodPolynomials.EvenLevelThree
