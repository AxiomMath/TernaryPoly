module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Levi
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneLocalOp

@[expose] public section


/-!
# The sign dictionary on the good-line representatives

`GoodLineEdge` is stated for an arbitrary coefficient representation, so `heckeTwoL`, `edgeL`,
`edgeL_heckeTwoL` and `heckeTwoL_relative` apply verbatim to the sign-twisted representation
`rationalCoefficientComponent n χ`.  What changes is the value of the representation on the
elements entering the formula.  On the Levi representatives `ℓ_j = diag(B_j, 1)` (determinant `p`)
and on the lower radical (determinant one) the twisted and the untwisted representations agree;
on the radical representatives `τ_c = Q(3c, 1, εp)` the twisted one is `sgnP p` times the
untwisted one; on the arithmetic Levi elements `Qint 0 ν`, `ν ∈ GL₂(ℤ)`, it is `det ν` times the
untwisted one.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets
open TernaryPeriodPolynomials.Spectral.LineCoordinates
open TernaryPeriodPolynomials.Spectral.GoodLineCosets
open TernaryPeriodPolynomials.Spectral.GoodLineEdge

namespace LH

/-- The determinant of `Q(c, B, d)`. -/
theorem det_Q (c : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    (Q c B d).val.det = B.val.det * (d : ℚ) := by
  rw [Q_val]
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  ring

/-- The Levi representatives `ℓ_j` have determinant `p`. -/
theorem det_rExpl_inl (p : Nat.Primes) (j : Option (Fin p.val)) :
    (rExpl p (.inl j)).val.det = (p.val : ℚ) := by
  change (Q 0 (BGL p j) 1).val.det = _
  rw [det_Q, BGL_val, Bmat_det]
  simp

/-- The radical representatives `τ_c` have determinant `εp`. -/
theorem det_rExpl_inr (p : Nat.Primes) (c : Fin p.val × Fin p.val) :
    (rExpl p (.inr c)).val.det = (epsP p : ℚ) := by
  change (Q ((3 : ℚ) • icast (cvec p c)) 1 (epsU p)).val.det = _
  rw [det_Q, epsU_val]
  simp

/-- For `χ(-1_∞) = -1` the sign of `τ_c` is `sgnP p`. -/
theorem detSign_rExpl_inr (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (p : Nat.Primes) (c : Fin p.val × Fin p.val) :
    detSign χ (rExpl p (.inr c)) = ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) := by
  rw [detSign_odd hχ, det_rExpl_inr]
  have hp : (0 : ℚ) < (p.val : ℚ) := by exact_mod_cast p.property.pos
  by_cases h : (p.val : ℤ) % 3 = 1
  · have he : epsP p = (p.val : ℤ) := by simp [epsP, h]
    have hs : IdentityPlaneLocalOp.sgnP p = 1 := by simp [IdentityPlaneLocalOp.sgnP, h]
    have hc : (0 : ℚ) < ((epsP p : ℤ) : ℚ) := by rw [he]; exact_mod_cast hp
    rw [ite_eq_left hc, hs]
    try norm_num
  · have he : epsP p = -(p.val : ℤ) := by simp [epsP, h]
    have hs : IdentityPlaneLocalOp.sgnP p = -1 := by simp [IdentityPlaneLocalOp.sgnP, h]
    have hc : ¬ (0 : ℚ) < ((epsP p : ℤ) : ℚ) := by
      rw [he]
      exact not_lt.mpr (by push_cast; linarith)
    rw [ite_eq_right hc, hs]
    try norm_num

/-- The twisted representation agrees with the untwisted one on the Levi representatives. -/
theorem rho_rExpl_inl (n : ℕ) (χ : RankOneCharacter) (p : Nat.Primes) (j : Option (Fin p.val)) :
    rationalCoefficientComponent n χ (rExpl p (.inl j)) =
      rationalCoefficientComponent n trivialCharacter (rExpl p (.inl j)) :=
  rho_eq_of_pos n χ (by rw [det_rExpl_inl]; exact_mod_cast p.property.pos)

/-- On the radical representatives the twisted representation is `sgnP p` times the untwisted. -/
theorem rho_rExpl_inr (n : ℕ) (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (p : Nat.Primes) (c : Fin p.val × Fin p.val) :
    rationalCoefficientComponent n χ (rExpl p (.inr c)) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) •
        rationalCoefficientComponent n trivialCharacter (rExpl p (.inr c)) := by
  rw [rho_eq_detSign_smul, detSign_rExpl_inr χ hχ]

/-- The arithmetic Levi element `diag(ν, 1)` as `Qint 0 ν`. -/
theorem arithmeticLevi_eq_Qint (ν : GL (Fin 2) ℤ) : arithmeticLevi ν = Qint 0 ν :=
  congrArg Subtype.val (splitting1_eq ν)

/-- On `Qint 0 ν` the twisted representation is `det ν` times the untwisted. -/
theorem rho_Qint_zero (n : ℕ) (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (ν : GL (Fin 2) ℤ) :
    rationalCoefficientComponent n χ (Qint 0 ν) =
      (((GeneralLinearGroup.det ν : ℤˣ) : ℤ) : ℂ) •
        rationalCoefficientComponent n trivialCharacter (Qint 0 ν) := by
  rw [← arithmeticLevi_eq_Qint ν, rho_eq_detSign_smul, detSign_arithmeticLevi_odd hχ]

/-- The twisted and untwisted representations agree on `Qint u 1`. -/
theorem rho_Qint_one (n : ℕ) (χ : RankOneCharacter) (u : ℤ × ℤ) :
    rationalCoefficientComponent n χ (Qint u 1) =
      rationalCoefficientComponent n trivialCharacter (Qint u 1) := by
  have h : Qint u 1 = lowerRadicalLattice (Multiplicative.ofAdd u) :=
    (congrArg Subtype.val (inl1_eq (Multiplicative.ofAdd u))).symm
  rw [h]
  exact rho_lowerRadicalLattice n χ _

/-- The determinants of `m` and `m⁻¹` multiply to one. -/
theorem det_mul_det_inv (m : GL (Fin 2) ℤ) :
    (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) * (((GeneralLinearGroup.det m⁻¹ : ℤˣ) : ℤ) : ℂ) = 1 := by
  have h : ((GeneralLinearGroup.det m : ℤˣ) : ℤ) * ((GeneralLinearGroup.det m⁻¹ : ℤˣ) : ℤ) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  exact_mod_cast h

end LH

end TernaryPeriodPolynomials.Twisted
