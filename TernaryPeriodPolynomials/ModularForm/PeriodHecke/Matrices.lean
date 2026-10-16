module

public import TernaryPeriodPolynomials.ModularForm.Symbol.RationalMobius
public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.AlternativeSymbols

@[expose] public section


noncomputable section
open Complex Matrix
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspSymbol
open BinaryRationalHeckePrime BinaryCuspHeckeEndomorphism

@[simp] theorem adjugate_det (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (adjugateRepresentative p i).det.val = (p : ℚ) := by
  change (adjugateRepresentative p i).val.det = _
  rw [adjugateRepresentative_matrix]
  cases i <;> simp [Matrix.det_fin_two]

/-- The inverse matrices of the actual adjugate representatives. -/
theorem adjugate_inv_matrix (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (adjugateRepresentative p i)⁻¹.val = match i with
      | .inl b => !![(1 : ℚ)/p,(b.val : ℚ)/p;0,1]
      | .inr _ => !![(1 : ℚ),0;0,1/p] := by
  let M : Matrix (Fin 2) (Fin 2) ℚ := match i with
    | .inl b => !![1/(p : ℚ),(b.val : ℚ)/p;0,1]
    | .inr _ => !![(1 : ℚ),0;0,1/p]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hm : (adjugateRepresentative p i).val * M = 1 := by
    rw [adjugateRepresentative_matrix]
    cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, hp0]
    field_simp
    ring
  have h := congrArg (fun N => (adjugateRepresentative p i).inv * N) hm
  rw [←mul_assoc, (adjugateRepresentative p i).inv_val, one_mul, mul_one] at h
  exact h.symm

theorem adjugate_inv_det_pos (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    0 < ((adjugateRepresentative p i)⁻¹).det.val := by
  simp only [map_inv, Units.val_inv_eq_inv_val, adjugate_det]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)

theorem adjugate_inv_mobius_finite (p : ℕ) [Fact p.Prime] (b : ZMod p)
    {z : ℂ} (hz : 0 < z.im) :
    rationalMobius (adjugateRepresentative p (.inl b))⁻¹ z = (z+b.val)/p := by
  rw [rationalMobius_fraction _ (adjugate_inv_det_pos p (.inl b)) hz]
  rw [adjugate_inv_matrix]
  simp
  simp only [ZMod.cast_eq_val]
  push_cast
  ring

theorem adjugate_inv_mobius_infinity (p : ℕ) [Fact p.Prime]
    {z : ℂ} (hz : 0 < z.im) :
    rationalMobius (adjugateRepresentative p (.inr ()))⁻¹ z = p*z := by
  rw [rationalMobius_fraction _ (adjugate_inv_det_pos p (.inr ())) hz]
  rw [adjugate_inv_matrix]
  simp [mul_comm]

/-- The complex inverse coordinates of every finite actual transfer representative. -/
theorem adjugate_inv_coordinates_finite (p : ℕ) [Fact p.Prime] (b : ZMod p) (v : Coordinates) :
    ((complexify (adjugateRepresentative p (.inl b)))⁻¹).val.mulVec v =
      ![(v 0+b.val*v 1)/p,v 1] := by
  rw [←map_inv]
  change (((adjugateRepresentative p (.inl b))⁻¹).val.map (algebraMap ℚ ℂ)).mulVec v = _
  rw [adjugate_inv_matrix]
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct]
  simp only [ZMod.cast_eq_val]
  push_cast
  ring

/-- The complex inverse coordinates of the exceptional actual transfer representative. -/
theorem adjugate_inv_coordinates_infinity (p : ℕ) [Fact p.Prime] (v : Coordinates) :
    ((complexify (adjugateRepresentative p (.inr ())))⁻¹).val.mulVec v = ![v 0,v 1/p] := by
  rw [←map_inv]
  change (((adjugateRepresentative p (.inr ()))⁻¹).val.map (algebraMap ℚ ℂ)).mulVec v = _
  rw [adjugate_inv_matrix]
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, div_eq_mul_inv, mul_comm]

end TernaryPoly.BinaryCuspSymbol
