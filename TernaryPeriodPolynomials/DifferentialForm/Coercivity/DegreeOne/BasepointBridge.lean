module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.CasimirOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ZeroExterior
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseContraction
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseMetric
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Exterior
public import TernaryPeriodPolynomials.DifferentialForm.Metric.Normalization
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Coercive

@[expose] public section



/-! # Basepoint bridge and real-frame transport, exterior degree one

Identifies the basepoint-coordinates geometric picture
(`formPairing`/`symmetricContraction n 0`/`symmetricExterior n 1`) with the algebraic layer
of `Algebra.lean`/`Coercive.lean`/`CasimirOne.lean`, then transports the resulting
basepoint coercivity bound to every point of `positiveCoordinates` via the already-generic
real-frame machinery (`exists_normalized_real_frame`, `realFormPullback`,
`symmetricContraction_real`, `symmetricExterior_real`, `formPairing_real`), mirroring
`TernaryPoly.PolynomialFormGeometricEnergy.symmetric_energy_coercive`'s proof verbatim one
exterior degree down. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.CoercivityOne

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPeriodPolynomials.Argument.Coercivity (formPairing_basepoint_zero)

/-- The algebraic degree-one contraction, read off at the basepoint, is half the geometric
`symmetricContraction`'s basepoint value, mirroring `symmetricExterior_one_basepoint`. -/
theorem symmetricContraction_one_basepoint (n : ℕ) (a : FormValue n 1) :
    (symmetricContraction n 0 (coordinateChart basepoint) a ![]).val =
      (1/2 : ℝ) • contractionOne (baseOneCoordinates a) := by
  rw [symmetricContraction_basepoint_apply n 0 a ![]]
  simp only [Submodule.coe_sum, Submodule.coe_smul, coefficientInfinitesimal_apply,
    contractionOne, baseOneCoordinates, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  module

/-- Basepoint coercivity of the degree-one geometric energy, identifying the geometric
`formPairing`/`symmetricContraction`/`symmetricExterior` picture with the algebraic layer
(`homogeneousHodgeOne_coercive`). -/
theorem oneForm_energy_basepoint_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : FormValue n 1,
      c * formPairing n 1 (coordinateChart basepoint) a a ≤
        formPairing n 0 (coordinateChart basepoint)
          (symmetricContraction n 0 (coordinateChart basepoint) a)
          (symmetricContraction n 0 (coordinateChart basepoint) a) +
        formPairing n 2 (coordinateChart basepoint)
          (symmetricExterior n 1 (coordinateChart basepoint) a)
          (symmetricExterior n 1 (coordinateChart basepoint) a) := by
  obtain ⟨c₀, hc₀, hcoerc⟩ := homogeneousHodgeOne_coercive hn
  refine ⟨c₀ / 4, by positivity, fun a => ?_⟩
  have hmem : baseOneCoordinates a ∈ homogeneousOneForms n := fun i => (a ![baseFrame i]).property
  have hb := hcoerc ⟨baseOneCoordinates a, hmem⟩
  rw [homogeneousHodgeOne_apply, algebraicHodgeOne_energy] at hb
  have hY : baseTwoCoordinates (symmetricExterior n 1 (coordinateChart basepoint) a) =
      (1/2 : ℝ) • exteriorOne (baseOneCoordinates a) := by
    funext i j
    exact symmetricExterior_one_basepoint n a i j
  rw [formPairing_basepoint_one, formPairing_basepoint_zero, formPairing_basepoint_two,
    symmetricContraction_one_basepoint, hY]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, twoPairing_smul_left,
    twoPairing_smul_right]
  nlinarith [hb]

/-- The basepoint constant works everywhere, by proved real-frame transport, mirroring
`TernaryPoly.PolynomialFormGeometricEnergy.symmetric_energy_coercive` one exterior degree
down. -/
theorem symmetric_energy_coercive_one {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ a : FormValue n 1,
      c * formPairing n 1 x a a ≤
        formPairing n 0 x (symmetricContraction n 0 x a) (symmetricContraction n 0 x a) +
        formPairing n 2 x (symmetricExterior n 1 x a) (symmetricExterior n 1 x a) := by
  obtain ⟨c, hc, h⟩ := oneForm_energy_basepoint_coercive hn
  refine ⟨c, hc, fun x hx a => ?_⟩
  obtain ⟨g, hg, he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let b := realFormPullback n 1 g y a
  have hb := realFormPullback_spec n 1 g y a
  have hC := symmetricContraction_real n 0 g hg y hy a b hb
  have hE := symmetricExterior_real n 1 g hg y hy a b hb
  rw [formPairing_real n 1 g hg y hy a a b b hb hb,
    formPairing_real n 0 g hg y hy _ _ _ _ hC hC,
    formPairing_real n 2 g hg y hy _ _ _ _ hE hE]
  exact h b

end TernaryPeriodPolynomials.Argument.CoercivityOne
