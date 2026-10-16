module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.CentralCharacter
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.RepUnfolding

@[expose] public section


/-!
# Corollary 1.4, Step 1: `ρ(S) (ρ(S) x) = x` on the even-degree summand

`ModularGroup.S` casts, after squaring, to `-1` as a complex matrix; substituting `-1` is exactly
negating every variable, which fixes an even-degree homogeneous polynomial
(`bind₁_neg_X_of_isHomogeneous_even`, `CentralCharacter.lean`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open Matrix Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup MvPolynomial
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein.Binary (substitute substitute_comp linearForm HomogeneousPoly Poly GL2)

/-- `S * S` is `-1` as an integer matrix. -/
private theorem S_mul_S_matrix :
    ((ModularGroup.S * ModularGroup.S : SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 0; 0, -1] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]

/-- `S * S` is an involution: `(S * S)⁻¹ = S * S`. -/
private theorem S_mul_S_inv :
    (ModularGroup.S * ModularGroup.S)⁻¹ = ModularGroup.S * ModularGroup.S := by
  apply inv_eq_of_mul_eq_one_right
  have h4 : ModularGroup.S ^ 4 =
      ModularGroup.S * ModularGroup.S * ModularGroup.S * ModularGroup.S := by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
  have h5 : ModularGroup.S * ModularGroup.S * (ModularGroup.S * ModularGroup.S) =
      ModularGroup.S ^ 4 := by
    rw [h4]
    exact (mul_assoc (ModularGroup.S * ModularGroup.S) ModularGroup.S ModularGroup.S).symm
  rw [h5, modularOrderFour]

/-- The complex cast of an integer `SpecialLinearGroup` element, entrywise (local re-derivation
of `RepUnfolding.lean`'s private `castSL_apply`, which is not visible from this file). -/
private theorem castSL_entry (g : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g) :
        Matrix (Fin 2) (Fin 2) ℂ) i j = ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℂ) := by
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

/-- The product `(cast S⁻¹) * (cast S⁻¹)` is `-1` as a complex matrix, where the product is taken
in `Matrix (Fin 2) (Fin 2) ℂ` (matching how it naturally arises from `substitute_comp`, whose
arguments are plain matrices, not `GL2` elements). -/
private theorem castS_inv_mul_castS_inv :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) :
        Matrix (Fin 2) (Fin 2) ℂ) *
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) :
        Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  have e0 : (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) :
        Matrix (Fin 2) (Fin 2) ℂ) *
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      ((GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) *
          GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) :
          GL2) : Matrix (Fin 2) (Fin 2) ℂ) :=
    (Units.val_mul _ _).symm
  have e1 : GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) *
      GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) =
      GeneralLinearGroup.map (Int.castRingHom ℂ)
        (SpecialLinearGroup.toGL (ModularGroup.S * ModularGroup.S)) := by
    rw [← map_mul, ← map_mul, ← _root_.mul_inv_rev, S_mul_S_inv]
  rw [e0, e1]
  ext i j
  rw [castSL_entry, S_mul_S_matrix]
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

/-- Negating every variable is substitution by `-1`. -/
private theorem linearForm_neg_one (i : Fin 2) :
    linearForm (-1 : Matrix (Fin 2) (Fin 2) ℂ) i = -X i := by
  fin_cases i <;> simp [linearForm, Matrix.neg_apply, Matrix.one_apply]

private theorem substitute_neg_one (p : Poly) :
    substitute (-1 : Matrix (Fin 2) (Fin 2) ℂ) p = bind₁ (fun i => -X i) p := by
  show bind₁ (linearForm (-1 : Matrix (Fin 2) (Fin 2) ℂ)) p = bind₁ (fun i => -X i) p
  rw [funext linearForm_neg_one]

/-- **Corollary A4.** `ρ(S) (ρ(S) x) = x` for `x` in the even-degree homogeneous summand. -/
theorem modularBinaryRep_S_S_apply {n : ℕ} (twist : ℤ) (hn : Even n) (x : HomogeneousPoly n) :
    (modularBinaryRep n twist).ρ ModularGroup.S ((modularBinaryRep n twist).ρ ModularGroup.S x) =
      x := by
  apply Subtype.ext
  have e1 := modularBinaryRep_apply n twist ModularGroup.S x
  have e2 := modularBinaryRep_apply n twist ModularGroup.S
    ((modularBinaryRep n twist).ρ ModularGroup.S x)
  rw [e2, e1]
  have hpt := DFunLike.congr_fun
    (substitute_comp
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹))
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹)))
    (x : Poly)
  rw [AlgHom.comp_apply] at hpt
  rw [hpt, castS_inv_mul_castS_inv, substitute_neg_one]
  exact bind₁_neg_X_of_isHomogeneous_even
    ((MvPolynomial.mem_homogeneousSubmodule n (x : Poly)).mp x.2) hn

end TernaryPeriodPolynomials.Argument.Corollary14
