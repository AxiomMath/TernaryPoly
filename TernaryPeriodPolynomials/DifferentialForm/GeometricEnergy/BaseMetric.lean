module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseCoercive

@[expose] public section


/-! The adjacent exterior metrics in the actual base frame. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open SL3PolynomialCoercivity PolynomialCoefficientMetric PolynomialFormMetric
open SymmetricSpaceCharts SymmetricSpaceCovering

def baseOneCoordinates {n : ℕ} (a : FormValue n 1) : OneCoordinates :=
  fun i => (a ![baseFrame i]).val

def threeArrowEquiv (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun a := (a 0, a 1, a 2)
  invFun a := ![a.1, a.2.1, a.2.2]
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv a := rfl

theorem formPairing_basepoint_one (n : ℕ) (a b : FormValue n 1) :
    formPairing n 1 (coordinateChart basepoint) a b =
      onePairing (baseOneCoordinates a) (baseOneCoordinates b) := by
  rw [formPairing_basepoint_frame]
  have he := (Equiv.funUnique (Fin 1) (Fin 5)).symm.sum_comp
    (fun I : Fin 1 → Fin 5 => (∏ r, tangentWeight (I r)) *
      factorialPairing (a (fun r => baseFrame (I r))).val (b (fun r => baseFrame (I r))).val)
  rw [← he]
  norm_num only [Nat.factorial, Nat.cast_one, inv_one, one_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hv : (fun r : Fin 1 => baseFrame ((Equiv.funUnique (Fin 1) (Fin 5)).symm i r)) = ![baseFrame i] := by
    funext r; fin_cases r; rfl
  rw [hv]
  simp only [Fin.prod_univ_one]
  rfl

theorem formPairing_basepoint_three (n : ℕ) (a b : FormValue n 3) :
    formPairing n 3 (coordinateChart basepoint) a b =
      threePairing (baseThreeCoordinates a) (baseThreeCoordinates b) := by
  rw [formPairing_basepoint_frame]
  have he := (threeArrowEquiv (Fin 5)).symm.sum_comp
    (fun I : Fin 3 → Fin 5 => (∏ r, tangentWeight (I r)) *
      factorialPairing (a (fun r => baseFrame (I r))).val (b (fun r => baseFrame (I r))).val)
  rw [← he, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  unfold threePairing baseThreeCoordinates
  apply congrArg ((1/6 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hv : (fun r : Fin 3 => baseFrame ((threeArrowEquiv (Fin 5)).symm (i,j,k) r)) =
      ![baseFrame i, baseFrame j, baseFrame k] := by
    funext r; fin_cases r <;> rfl
  rw [hv]
  change (∏ r : Fin 3, tangentWeight (![i,j,k] r)) * _ = _
  simp [Fin.prod_univ_succ, mul_assoc]

end TernaryPoly.PolynomialFormGeometricEnergy
