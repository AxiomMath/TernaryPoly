module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SectorCombinatorics
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CasimirBound

@[expose] public section



/-! The basepoint coercivity bound for `symmetricContraction n 4`, the top-degree analogue of
`CasimirBound.lean`'s degree-0 bound for `symmetricExterior n 0`. For `w : FormValue n 5`, the
value `symmetricContraction n 4 (basepoint) w (sectorFrame i0)` collapses (via
`formValue_five_vecCons_sectorFrame_eq_zero`) to the single `i = i0` term of the defining sum,
and that term is `tangentWeight i0 • (1/2) • infinitesimal (tangentFrame i0)` applied to a signed
copy of `(w baseFrame).val` (the sign coming from the cyclic rearrangement
`vecCons (baseFrame i0) (sectorFrame i0) = baseFrame ∘ moveFrontEquiv i0`). Squaring cancels the
sign, and the same finite-dimensional Casimir bound `tangentFrame_energy_lower` used at degree 0
gives the same constant `n(n+9)/24`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive

/-- `symmetricContraction n 4` at the basepoint, evaluated on a sector frame, collapses to the
single `i = i0` term of the defining sum: every other term has a repeated `baseFrame` argument. -/
theorem symmetricContraction_basepoint_sector (n : ℕ) (w : FormValue n 5) (i0 : Fin 5) :
    symmetricContraction n 4 (coordinateChart basepoint) w (sectorFrame i0) =
      tangentWeight i0 • (1/2 : ℝ) • coefficientInfinitesimal n (tangentFrame i0)
        (Equiv.Perm.sign (moveFrontEquiv i0) • w baseFrame) := by
  rw [symmetricContraction_basepoint_apply,
    Finset.sum_eq_single_of_mem i0 (Finset.mem_univ i0)
      (fun i _ hi => by rw [formValue_five_vecCons_sectorFrame_eq_zero n w i0 i hi]; simp)]
  have hperm : w (Matrix.vecCons (baseFrame i0) (sectorFrame i0)) =
      Equiv.Perm.sign (moveFrontEquiv i0) • w baseFrame := by
    have heq2 : Matrix.vecCons (baseFrame i0) (sectorFrame i0) = baseFrame ∘ (moveFrontEquiv i0) :=
      vecCons_sectorFrame i0
    rw [heq2]
    have := AlternatingMap.map_perm w.toAlternatingMap baseFrame (moveFrontEquiv i0)
    simpa using this
  rw [hperm]

/-- The `.val` (bare-polynomial) version of `symmetricContraction_basepoint_sector`. -/
theorem symmetricContraction_basepoint_sector_val (n : ℕ) (w : FormValue n 5) (i0 : Fin 5) :
    (symmetricContraction n 4 (coordinateChart basepoint) w (sectorFrame i0)).val =
      tangentWeight i0 • (1/2 : ℝ) • infinitesimal (tangentFrame i0)
        (Equiv.Perm.sign (moveFrontEquiv i0) • (w baseFrame).val) := by
  have hv : (Equiv.Perm.sign (moveFrontEquiv i0) • w baseFrame).val =
      Equiv.Perm.sign (moveFrontEquiv i0) • (w baseFrame).val := by simp
  rw [symmetricContraction_basepoint_sector]
  simp only [Submodule.coe_smul, coefficientInfinitesimal_apply, hv]

/-- The product of `tangentWeight` over a sector, times the missing weight, is the full product. -/
theorem tangentWeight_sectorFrameIndex_prod_mul (i0 : Fin 5) :
    (∏ r : Fin 4, tangentWeight (sectorFrameIndex i0 r)) * tangentWeight i0 =
      ∏ j : Fin 5, tangentWeight j := by
  have himg : ∏ r : Fin 4, tangentWeight (sectorFrameIndex i0 r) =
      ∏ j ∈ Finset.univ.erase i0, tangentWeight j := by
    rw [← sectorFrameIndex_image i0,
      Finset.prod_image (fun r _ s _ h => sectorFrameIndex_injective i0 h)]
  rw [himg, Finset.prod_erase_mul Finset.univ tangentWeight (Finset.mem_univ i0)]

/-- Squared self-pairing of a sector value of `symmetricContraction n 4`, in terms of the pure
Casimir energy summand `factorialPairing (infinitesimal (tangentFrame i0) p) (infinitesimal
(tangentFrame i0) p)` for `p := (w baseFrame).val`. -/
theorem symmetricContraction_sector_self_pairing (n : ℕ) (w : FormValue n 5) (i0 : Fin 5) :
    factorialPairing (symmetricContraction n 4 (coordinateChart basepoint) w (sectorFrame i0)).val
        (symmetricContraction n 4 (coordinateChart basepoint) w (sectorFrame i0)).val =
      (tangentWeight i0) ^ 2 * (1 / 4 : ℝ) *
        factorialPairing (infinitesimal (tangentFrame i0) (w baseFrame).val)
          (infinitesimal (tangentFrame i0) (w baseFrame).val) := by
  rw [symmetricContraction_basepoint_sector_val]
  have hcomm : infinitesimal (tangentFrame i0)
      (Equiv.Perm.sign (moveFrontEquiv i0) • (w baseFrame).val) =
      Equiv.Perm.sign (moveFrontEquiv i0) • infinitesimal (tangentFrame i0) (w baseFrame).val := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (moveFrontEquiv i0)) with h | h <;> simp [h]
  rw [hcomm]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [factorialPairing_sign_smul_self]
  ring

/-- Basepoint-level degree-5 (`k = 4`) coercivity, with the same constant `c = n(n+9)/24` as
degree 0: `c * formPairing w w ≤ formPairing (symmetricContraction n 4 w) (symmetricContraction
n 4 w)` at the basepoint. The top-degree mirror of `symmetric_energy_basepoint_coercive_zero`. -/
theorem symmetric_energy_basepoint_coercive_four (n : ℕ) (w : FormValue n 5) :
    (n : ℝ) * (n + 9) / 24 * formPairing n 5 (coordinateChart basepoint) w w ≤
      formPairing n 4 (coordinateChart basepoint)
        (symmetricContraction n 4 (coordinateChart basepoint) w)
        (symmetricContraction n 4 (coordinateChart basepoint) w) := by
  have hp : (w baseFrame).val.IsHomogeneous n :=
    (MvPolynomial.mem_homogeneousSubmodule n (w baseFrame).val).mp (w baseFrame).2
  rw [formPairing_basepoint_four, formPairing_basepoint_five]
  have heq : ∑ i0 : Fin 5, (∏ r : Fin 4, tangentWeight (sectorFrameIndex i0 r)) *
      factorialPairing (symmetricContraction n 4 (coordinateChart basepoint) w (sectorFrame i0)).val
        (symmetricContraction n 4 (coordinateChart basepoint) w (sectorFrame i0)).val =
      (∏ j : Fin 5, tangentWeight j) * (1 / 4 : ℝ) *
        (∑ i0 : Fin 5, tangentWeight i0 * factorialPairing
          (infinitesimal (tangentFrame i0) (w baseFrame).val)
          (infinitesimal (tangentFrame i0) (w baseFrame).val)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i0 _
    rw [symmetricContraction_sector_self_pairing]
    have hprod := tangentWeight_sectorFrameIndex_prod_mul i0
    linear_combination (tangentWeight i0 * (1 / 4 : ℝ) * factorialPairing
      (infinitesimal (tangentFrame i0) (w baseFrame).val)
      (infinitesimal (tangentFrame i0) (w baseFrame).val)) * hprod
  rw [heq]
  have hlower := tangentFrame_energy_lower hp
  have hpos : (0:ℝ) ≤ ∏ j : Fin 5, tangentWeight j := by
    apply Finset.prod_nonneg
    intro i _
    exact le_of_lt (tangentWeight_pos i)
  nlinarith [hlower, hpos]

end TernaryPeriodPolynomials.Argument.Coercivity
