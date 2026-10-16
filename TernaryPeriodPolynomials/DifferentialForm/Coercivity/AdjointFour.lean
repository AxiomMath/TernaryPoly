module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SectorCombinatorics
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ContractionBound
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Adjoint

@[expose] public section



/-! Degree-4 basepoint adjointness between `symmetricExterior n 4` and `symmetricContraction n 4`,
the top-degree mirror of `Adjoint.lean`'s degree-0 statement. Two combinatorial facts are needed
first: that `Fin.removeNth i0 baseFrame` (the tuple `symmetricExterior_apply`'s defining sum feeds
into `a`) is exactly `sectorFrame i0`, and that the sign `(-1)^i0` from that same defining sum
matches `Equiv.Perm.sign (moveFrontEquiv i0)` (the sign already used by
`symmetricContraction_basepoint_sector_val`).

-/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive

/-- `i0.succAbove` on `Fin 4` agrees with `sectorFrameIndex i0`.
-/
theorem succAbove_eq_sectorFrameIndex (i0 : Fin 5) (r : Fin 4) :
    i0.succAbove r = sectorFrameIndex i0 r := by
  show i0.succAbove r = moveFrontEquiv i0 r.succ
  rw [moveFrontEquiv_apply]
  revert i0 r
  decide

/-- Removing the `i0`-th entry from `baseFrame` gives exactly `sectorFrame i0`. -/
theorem removeNth_baseFrame_eq_sectorFrame (i0 : Fin 5) :
    Fin.removeNth i0 baseFrame = sectorFrame i0 := by
  funext r
  rw [Fin.removeNth_apply, succAbove_eq_sectorFrameIndex, sectorFrame_eq_sectorFrameIndex]

/-- A fully computable rebuild of `moveFrontEquiv i0`, agreeing with the real (noncomputable)
`moveFrontEquiv i0` on every input.


-/
def moveFrontEquivC (i0 : Fin 5) : Equiv.Perm (Fin 5) where
  toFun := moveFrontTable i0
  invFun := (![![0,1,2,3,4], ![1,0,2,3,4], ![1,2,0,3,4], ![1,2,3,0,4], ![1,2,3,4,0]] :
    Fin 5 → Fin 5 → Fin 5) i0
  left_inv := by revert i0; decide
  right_inv := by revert i0; decide

theorem moveFrontEquiv_eq_moveFrontEquivC (i0 : Fin 5) :
    moveFrontEquiv i0 = moveFrontEquivC i0 := by
  apply Equiv.ext
  intro r
  rw [moveFrontEquiv_apply]
  rfl

/-- The sign of `moveFrontEquiv i0`, as a unit, is `(-1)^i0`. -/
theorem sign_moveFrontEquiv (i0 : Fin 5) :
    Equiv.Perm.sign (moveFrontEquiv i0) = (-1 : ℤˣ) ^ (i0 : ℕ) := by
  rw [moveFrontEquiv_eq_moveFrontEquivC]
  revert i0
  decide

/-- The real-scalar smul form of `sign_moveFrontEquiv`, matching the sign convention `(-1)^i0` of
`symmetricExterior_apply`'s defining alternating sum. -/
theorem sign_moveFrontEquiv_smul (i0 : Fin 5) (z : Poly) :
    Equiv.Perm.sign (moveFrontEquiv i0) • z = (-1 : ℝ) ^ (i0 : ℕ) • z := by
  rw [sign_moveFrontEquiv]
  rcases Nat.even_or_odd (i0 : ℕ) with he | ho
  · rw [he.neg_one_pow, he.neg_one_pow, one_smul, one_smul]
  · rw [ho.neg_one_pow, ho.neg_one_pow]
    simp

/-- The value of `symmetricExterior n 4` at the basepoint, applied to `baseFrame`, expanded as a
signed sum over the sectors, mirroring `symmetricExterior_zero_basepoint`. -/
theorem symmetricExterior_four_basepoint (n : ℕ) (a : FormValue n 4) :
    (symmetricExterior n 4 (coordinateChart basepoint) a baseFrame).val =
      ∑ i : Fin 5, (-1 : ℝ) ^ (i : ℕ) •
        ((1 / 2 : ℝ) • infinitesimal (tangentFrame i) (a (sectorFrame i)).val) := by
  rw [symmetricExterior_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [removeNth_baseFrame_eq_sectorFrame, symmetricPart_baseFrame]
  rcases Nat.even_or_odd (i : ℕ) with he | ho
  · rw [he.neg_one_pow, he.neg_one_pow, one_smul, one_smul]
    simp only [_root_.smul_apply, infinitesimalCLM_apply, Submodule.coe_smul,
      coefficientInfinitesimal_apply]
  · rw [ho.neg_one_pow, ho.neg_one_pow, neg_one_smul, neg_one_smul]
    simp only [_root_.smul_apply, infinitesimalCLM_apply, Submodule.coe_neg, Submodule.coe_smul,
      coefficientInfinitesimal_apply]

/-- Basepoint adjointness between the degree-4 symmetric exterior derivative and the degree-4
symmetric contraction, the top-degree mirror of `symmetricExterior_zero_basepoint_adjoint`. -/
theorem symmetricExterior_four_basepoint_adjoint (n : ℕ) (a : FormValue n 4) (b : FormValue n 5) :
    formPairing n 5 (coordinateChart basepoint) (symmetricExterior n 4 (coordinateChart basepoint) a) b =
      formPairing n 4 (coordinateChart basepoint) a (symmetricContraction n 4 (coordinateChart basepoint) b) := by
  rw [formPairing_basepoint_five, formPairing_basepoint_four, symmetricExterior_four_basepoint,
    map_sum, LinearMap.sum_apply]
  have hL : ∀ i : Fin 5, factorialPairing
      ((-1 : ℝ) ^ (i : ℕ) • (1 / 2 : ℝ) • infinitesimal (tangentFrame i) (a (sectorFrame i)).val)
      (b baseFrame).val =
      (-1 : ℝ) ^ (i : ℕ) * (1 / 2 : ℝ) *
        factorialPairing (a (sectorFrame i)).val (infinitesimal (tangentFrame i) (b baseFrame).val) := by
    intro i
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [infinitesimal_symmetric_adjoint (tangentFrame i) (tangentFrame_mem i).1]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hL i)]
  have hR : ∀ i0 : Fin 5, (∏ r : Fin 4, tangentWeight (sectorFrameIndex i0 r)) *
      factorialPairing (a (sectorFrame i0)).val
        (symmetricContraction n 4 (coordinateChart basepoint) b (sectorFrame i0)).val =
      (∏ j : Fin 5, tangentWeight j) * (1 / 2 : ℝ) * ((-1 : ℝ) ^ (i0 : ℕ) *
        factorialPairing (a (sectorFrame i0)).val (infinitesimal (tangentFrame i0) (b baseFrame).val)) := by
    intro i0
    rw [symmetricContraction_basepoint_sector_val]
    have hsmul : factorialPairing (a (sectorFrame i0)).val
        (tangentWeight i0 • (1 / 2 : ℝ) • infinitesimal (tangentFrame i0)
          (Equiv.Perm.sign (moveFrontEquiv i0) • (b baseFrame).val)) =
        tangentWeight i0 * (1 / 2 : ℝ) * ((-1 : ℝ) ^ (i0 : ℕ) *
          factorialPairing (a (sectorFrame i0)).val (infinitesimal (tangentFrame i0) (b baseFrame).val)) := by
      rw [show (Equiv.Perm.sign (moveFrontEquiv i0) • (b baseFrame).val) =
          (-1 : ℝ) ^ (i0 : ℕ) • (b baseFrame).val from sign_moveFrontEquiv_smul i0 _]
      have hcomm : infinitesimal (tangentFrame i0) ((-1 : ℝ) ^ (i0 : ℕ) • (b baseFrame).val) =
          (-1 : ℝ) ^ (i0 : ℕ) • infinitesimal (tangentFrame i0) (b baseFrame).val := by
        rcases Nat.even_or_odd (i0 : ℕ) with he | ho
        · rw [he.neg_one_pow, one_smul, one_smul]
        · rw [ho.neg_one_pow, neg_one_smul, neg_one_smul, map_neg]
      rw [hcomm]
      simp only [map_smul, smul_eq_mul]
      ring
    rw [hsmul]
    have hprod := tangentWeight_sectorFrameIndex_prod_mul i0
    linear_combination (1/2 * ((-1:ℝ)^(i0:ℕ) * factorialPairing (a (sectorFrame i0)).val
      (infinitesimal (tangentFrame i0) (b baseFrame).val))) * hprod
  rw [Finset.sum_congr rfl (fun i0 _ => hR i0), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Transport of the degree-4 adjointness from the basepoint to every point of the positive
cone, mirroring `symmetricExterior_zero_adjoint`'s proof via the generic real-frame transport
machinery. -/
theorem symmetricExterior_four_adjoint (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a : FormValue n 4) (b : FormValue n 5) :
    formPairing n 5 x (symmetricExterior n 4 x a) b =
      formPairing n 4 x a (symmetricContraction n 4 x b) := by
  obtain ⟨g, hg, he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let c := realFormPullback n 4 g y a
  let d := realFormPullback n 5 g y b
  have hc := realFormPullback_spec n 4 g y a
  have hd := realFormPullback_spec n 5 g y b
  calc
    formPairing n 5 (coordinateAction g y) (symmetricExterior n 4 (coordinateAction g y) a) b =
        formPairing n 5 y (symmetricExterior n 4 y c) d :=
      formPairing_real n 5 g hg y hy _ _ _ _ (symmetricExterior_real n 4 g hg y hy a c hc) hd
    _ = formPairing n 4 y c (symmetricContraction n 4 y d) :=
      symmetricExterior_four_basepoint_adjoint n c d
    _ = formPairing n 4 (coordinateAction g y) a (symmetricContraction n 4 (coordinateAction g y) b) :=
      (formPairing_real n 4 g hg y hy _ _ _ _ hc
        (symmetricContraction_real n 4 g hg y hy b d hd)).symm

end TernaryPeriodPolynomials.Argument.Coercivity
