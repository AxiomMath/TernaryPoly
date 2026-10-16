module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AlgebraicHodgeFourCoercive
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AlgebraicHodgeFourEnergy
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AdjointThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AdjointFour
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseAdjoint

@[expose] public section



/-! Degree-4 basepoint coercivity for the SUM of the two "Symmetric" pieces
(`symmetricExterior n 4`, raising 4 to 5, and `symmetricContraction n 3`, lowering 4 to 3), and
its transport to every point of the positive cone. Mirrors `CoerciveTransportThree.lean` one degree
up: the basepoint bound is built from `algebraicHodgeFour_coercive` via `algebraicHodgeFour_energy`'s
split into a `threePairing (contractionFour ·) (contractionFour ·)` term and a
`factorialPairing (exteriorFour ·) (exteriorFour ·)` term.

Formalized by Claude Sonnet 5.5. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive

theorem tangentWeight_prod_eq : (∏ j : Fin 5, tangentWeight j) = 1 / 96 := by
  simp [Fin.prod_univ_five, tangentWeight]
  norm_num

/-- The five sector frames are the base frames omitting one index. -/
theorem sectorFrame_zero_eq :
    sectorFrame 0 = ![baseFrame 1, baseFrame 2, baseFrame 3, baseFrame 4] := by
  funext r; fin_cases r <;> rfl

theorem sectorFrame_one_eq :
    sectorFrame 1 = ![baseFrame 0, baseFrame 2, baseFrame 3, baseFrame 4] := by
  funext r; fin_cases r <;> rfl

theorem sectorFrame_two_eq :
    sectorFrame 2 = ![baseFrame 0, baseFrame 1, baseFrame 3, baseFrame 4] := by
  funext r; fin_cases r <;> rfl

theorem sectorFrame_three_eq :
    sectorFrame 3 = ![baseFrame 0, baseFrame 1, baseFrame 2, baseFrame 4] := by
  funext r; fin_cases r <;> rfl

theorem sectorFrame_four_eq :
    sectorFrame 4 = ![baseFrame 0, baseFrame 1, baseFrame 2, baseFrame 3] := by
  funext r; fin_cases r <;> rfl

/-- The value of `symmetricExterior n 4` at the basepoint on `baseFrame` is one half of the
algebraic `exteriorFour` of the base-frame coordinates. -/
theorem symmetricExterior_four_baseFrame_val (n : ℕ) (a : FormValue n 4) :
    (symmetricExterior n 4 (coordinateChart basepoint) a baseFrame).val =
      (1 / 2 : ℝ) • exteriorFour (baseFourCoordinates a) := by
  rw [symmetricExterior_four_basepoint, Fin.sum_univ_five, sectorFrame_zero_eq,
    sectorFrame_one_eq, sectorFrame_two_eq, sectorFrame_three_eq, sectorFrame_four_eq]
  have h3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have h4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  simp only [exteriorFour, baseFourCoordinates, Fin.val_zero, Fin.val_one, Fin.val_two, h3, h4]
  module

/-- Basepoint coercivity for the degree-4 sum of Symmetric pieces. -/
theorem symmetric_energy_basepoint_coercive_degree_four {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : FormValue n 4,
      c * formPairing n 4 (coordinateChart basepoint) a a ≤
        formPairing n 5 (coordinateChart basepoint)
          (symmetricExterior n 4 (coordinateChart basepoint) a)
          (symmetricExterior n 4 (coordinateChart basepoint) a) +
        formPairing n 3 (coordinateChart basepoint)
          (symmetricContraction n 3 (coordinateChart basepoint) a)
          (symmetricContraction n 3 (coordinateChart basepoint) a) := by
  obtain ⟨c, hc, h⟩ := algebraicHodgeFour_coercive hn
  refine ⟨c / 4, by positivity, fun a => ?_⟩
  have hb_alt : IsAlternatingFour (baseFourCoordinates a) := baseFourCoordinates_alternating a
  have hb_hom : ∀ i j k l, (baseFourCoordinates a i j k l).IsHomogeneous n := fun i j k l => by
    show (a ![baseFrame i, baseFrame j, baseFrame k, baseFrame l]).val.IsHomogeneous n
    exact (MvPolynomial.mem_homogeneousSubmodule n _).mp
      (a ![baseFrame i, baseFrame j, baseFrame k, baseFrame l]).2
  have hraw := h (baseFourCoordinates a) hb_alt hb_hom
  have hsplit := algebraicHodgeFour_energy (baseFourCoordinates a) hb_alt
  have hL : formPairing n 4 (coordinateChart basepoint) a a =
      fourPairing (baseFourCoordinates a) (baseFourCoordinates a) :=
    formPairing_basepoint_four_coords n a a
  have hR1 : formPairing n 5 (coordinateChart basepoint)
      (symmetricExterior n 4 (coordinateChart basepoint) a)
      (symmetricExterior n 4 (coordinateChart basepoint) a) =
      (1 / 4 : ℝ) * ((1 / 96 : ℝ) *
        factorialPairing (exteriorFour (baseFourCoordinates a))
          (exteriorFour (baseFourCoordinates a))) := by
    rw [formPairing_basepoint_five, symmetricExterior_four_baseFrame_val, tangentWeight_prod_eq]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hR2 : formPairing n 3 (coordinateChart basepoint)
      (symmetricContraction n 3 (coordinateChart basepoint) a)
      (symmetricContraction n 3 (coordinateChart basepoint) a) =
      (1 / 4 : ℝ) * threePairing (contractionFour (baseFourCoordinates a))
        (contractionFour (baseFourCoordinates a)) := by
    rw [formPairing_basepoint_three, baseThreeCoordinates_symmetricContraction,
      threePairing_smul_left, threePairing_smul_right]
    ring
  rw [hL, hR1, hR2]
  nlinarith [hraw, hsplit]

/-- Transport of the degree-4 basepoint sum-coercivity bound to every point of the positive cone. -/
theorem symmetric_energy_coercive_degree_four {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ w : FormValue n 4,
      c * formPairing n 4 x w w ≤
        formPairing n 5 x (symmetricExterior n 4 x w) (symmetricExterior n 4 x w) +
        formPairing n 3 x (symmetricContraction n 3 x w) (symmetricContraction n 3 x w) := by
  obtain ⟨c, hc, hbase⟩ := symmetric_energy_basepoint_coercive_degree_four hn
  refine ⟨c, hc, fun x hx w => ?_⟩
  obtain ⟨g, hg, he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let b := realFormPullback n 4 g y w
  have hb := realFormPullback_spec n 4 g y w
  have hE1 := symmetricExterior_real n 4 g hg y hy w b hb
  have hE2 := symmetricContraction_real n 3 g hg y hy w b hb
  rw [formPairing_real n 4 g hg y hy w w b b hb hb,
    formPairing_real n 5 g hg y hy _ _ _ _ hE1 hE1,
    formPairing_real n 3 g hg y hy _ _ _ _ hE2 hE2]
  exact hbase b

end TernaryPeriodPolynomials.Argument.Coercivity
