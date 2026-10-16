module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeThreeCoercive
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AdjointThree
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseAdjoint
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ContractionBound

@[expose] public section



/-! Degree-3 basepoint coercivity for the SUM of the two "Symmetric" pieces
(`symmetricExterior n 3`, raising 3→4, and `symmetricContraction n 2`, lowering 3→2), and its
transport to every point of the positive cone. Mirrors `ContractionBound.lean` +
`CoerciveTransportFour.lean` one degree down, but for an interior degree with TWO adjacent
Symmetric pieces instead of one boundary piece: the basepoint bound is built directly from
`algebraicHodgeThree_coercive` (piece B) via `algebraicHodgeThree_energy`'s own split into a
`twoPairing (contractionThree ·) (contractionThree ·)` term and a
`fourPairing (exteriorThree ·) (exteriorThree ·)` term, each a basepoint-coordinate image (up to
the `1/2` factor) of `symmetricContraction n 2 basepoint`/`symmetricExterior n 3 basepoint`
respectively (`baseTwoCoordinates_symmetricContraction`/`baseFourCoordinates_symmetricExterior`).
The transport step pulls back both pieces simultaneously via `symmetricExterior_real`/
`symmetricContraction_real`, following `CoerciveTransportFour.lean`'s pattern. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive

/-- Basepoint coercivity for the degree-3 sum of Symmetric pieces, built from
`algebraicHodgeThree_coercive` (piece B) via `algebraicHodgeThree_energy`'s split and the two
basepoint-coordinate bridge lemmas for `symmetricExterior n 3`/`symmetricContraction n 2`. -/
theorem symmetric_energy_basepoint_coercive_three {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : FormValue n 3,
      c * formPairing n 3 (coordinateChart basepoint) a a ≤
        formPairing n 4 (coordinateChart basepoint)
          (symmetricExterior n 3 (coordinateChart basepoint) a)
          (symmetricExterior n 3 (coordinateChart basepoint) a) +
        formPairing n 2 (coordinateChart basepoint)
          (symmetricContraction n 2 (coordinateChart basepoint) a)
          (symmetricContraction n 2 (coordinateChart basepoint) a) := by
  obtain ⟨c, hc, h⟩ := algebraicHodgeThree_coercive hn
  refine ⟨c / 4, by positivity, fun a => ?_⟩
  have hb_alt : IsAlternatingThree (baseThreeCoordinates a) := baseThreeCoordinates_alternating a
  have hb_hom : ∀ i j k, (baseThreeCoordinates a i j k).IsHomogeneous n := fun i j k => by
    show (a ![baseFrame i, baseFrame j, baseFrame k]).val.IsHomogeneous n
    exact (MvPolynomial.mem_homogeneousSubmodule n _).mp (a ![baseFrame i, baseFrame j, baseFrame k]).2
  have hraw := h (baseThreeCoordinates a) hb_alt hb_hom
  have hsplit : threePairing (algebraicHodgeThree (baseThreeCoordinates a)) (baseThreeCoordinates a) =
      twoPairing (contractionThree (baseThreeCoordinates a)) (contractionThree (baseThreeCoordinates a)) +
        fourPairing (exteriorThree (baseThreeCoordinates a)) (exteriorThree (baseThreeCoordinates a)) :=
    algebraicHodgeThree_energy (baseThreeCoordinates a) hb_alt
  have hL : formPairing n 3 (coordinateChart basepoint) a a =
      threePairing (baseThreeCoordinates a) (baseThreeCoordinates a) := formPairing_basepoint_three n a a
  have hR1 : formPairing n 4 (coordinateChart basepoint)
      (symmetricExterior n 3 (coordinateChart basepoint) a)
      (symmetricExterior n 3 (coordinateChart basepoint) a) =
      (1 / 4 : ℝ) * fourPairing (exteriorThree (baseThreeCoordinates a)) (exteriorThree (baseThreeCoordinates a)) := by
    rw [formPairing_basepoint_four_coords, baseFourCoordinates_symmetricExterior,
      fourPairing_smul_left, fourPairing_smul_right]
    ring
  have hR2 : formPairing n 2 (coordinateChart basepoint)
      (symmetricContraction n 2 (coordinateChart basepoint) a)
      (symmetricContraction n 2 (coordinateChart basepoint) a) =
      (1 / 4 : ℝ) * twoPairing (contractionThree (baseThreeCoordinates a)) (contractionThree (baseThreeCoordinates a)) := by
    rw [formPairing_basepoint_two, baseTwoCoordinates_symmetricContraction,
      twoPairing_smul_left, twoPairing_smul_right]
    ring
  rw [hL, hR1, hR2]
  nlinarith [hraw, hsplit]

/-- Transport of the degree-3 basepoint sum-coercivity bound to every point of the positive cone,
mirroring `symmetric_energy_coercive_four`'s transport argument, pulling back both Symmetric
pieces simultaneously via `symmetricExterior_real`/`symmetricContraction_real`. -/
theorem symmetric_energy_coercive_three {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Coordinates, x ∈ positiveCoordinates → ∀ w : FormValue n 3,
      c * formPairing n 3 x w w ≤
        formPairing n 4 x (symmetricExterior n 3 x w) (symmetricExterior n 3 x w) +
        formPairing n 2 x (symmetricContraction n 2 x w) (symmetricContraction n 2 x w) := by
  obtain ⟨c, hc, hbase⟩ := symmetric_energy_basepoint_coercive_three hn
  refine ⟨c, hc, fun x hx w => ?_⟩
  obtain ⟨g, hg, he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let b := realFormPullback n 3 g y w
  have hb := realFormPullback_spec n 3 g y w
  have hE1 := symmetricExterior_real n 3 g hg y hy w b hb
  have hE2 := symmetricContraction_real n 2 g hg y hy w b hb
  rw [formPairing_real n 3 g hg y hy w w b b hb hb,
    formPairing_real n 4 g hg y hy _ _ _ _ hE1 hE1,
    formPairing_real n 2 g hg y hy _ _ _ _ hE2 hE2]
  exact hbase b

end TernaryPeriodPolynomials.Argument.Coercivity
