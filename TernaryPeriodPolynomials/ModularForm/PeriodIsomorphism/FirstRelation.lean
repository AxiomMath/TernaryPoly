module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.RepUnfolding
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH1
public import TernaryPeriodPolynomials.Polynomial.Definitions

@[expose] public section


/-!
# Corollary 1.4, Step 1: the first relation `(-P, S) ^ 4 = 1`

`PeriodRelations.two_term` says `P + ρ(S⁻¹) P = 0`; applying `ρ(S)` and using the functoriality
of `ρ` gives `ρ(S) P = -P`. Packaging `P` into the semidirect product
`Semidirect (modularBinaryRep n twist) := TwoCocycleExtension (modularBinaryRep n twist)
(zeroCycle _) (zeroCycle_unit _)` (reused verbatim from
`TernaryPeriodPolynomials/ArithmeticCohomology/Spectral/ModularH1.lean`, which already builds this
exact group generically for every representation of `SL₂(ℤ)`) as `first := ⟨-P, S⟩`, this gives
`first ^ 4 = 1` (`first_pow_four`), one of the two relations `modularLiftSection` needs.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open Matrix Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup MvPolynomial
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH1
open GeneralEisenstein.Binary (substitute linearForm HomogeneousPoly Poly)
open TernaryPoly.Paper (PeriodRelations)

/-- The complex cast of an integer `SpecialLinearGroup` element, entrywise (local re-derivation;
`RepUnfolding.lean`'s private `castSL_apply` is not visible from this file). -/
private theorem castSL_entry (g : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g) :
        Matrix (Fin 2) (Fin 2) ℂ) i j = ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℂ) := by
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

/-- `S` casts to `!![0,-1;1,0]` as a complex matrix. -/
private theorem castS_matrix :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, 0] := by
  ext i j
  rw [castSL_entry]
  fin_cases i <;> fin_cases j <;> norm_num [ModularGroup.coe_S]

/-- The substitution linear form of `cast S` is `![-X 1, X 0]`. -/
private theorem linearForm_castS :
    linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S) :
      Matrix (Fin 2) (Fin 2) ℂ) = ![-X 1, X 0] := by
  rw [castS_matrix]
  funext i
  fin_cases i <;> simp [linearForm, Fin.sum_univ_two]

private theorem substitute_castS (p : Poly) :
    substitute (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S) :
      Matrix (Fin 2) (Fin 2) ℂ) p = bind₁ ![-X 1, X 0] p := by
  show bind₁ (linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL ModularGroup.S) : Matrix (Fin 2) (Fin 2) ℂ)) p = bind₁ ![-X 1, X 0] p
  rw [linearForm_castS]

/-- `ρ(S⁻¹)` unfolds to the raw substitution `bind₁ ![-X 1, X 0]`, matching
`PeriodRelations.two_term`'s own expression exactly. -/
private theorem modularBinaryRep_S_inv_apply {n : ℕ} (twist : ℤ) (f : HomogeneousPoly n) :
    ((modularBinaryRep n twist).ρ ModularGroup.S⁻¹ f).1 = bind₁ ![-X 1, X 0] (f : Poly) := by
  rw [modularBinaryRep_apply, inv_inv, substitute_castS]

/-- **Corollary A1.** `ρ(S) P = -P` for any `P` satisfying `PeriodRelations`'s `two_term`
identity (no parity hypothesis is needed). -/
theorem modularBinaryRep_S_apply_eq_neg {n : ℕ} (twist : ℤ) {P : HomogeneousPoly n}
    (hP : PeriodRelations (P : Poly)) :
    (modularBinaryRep n twist).ρ ModularGroup.S P = -P := by
  have hunfold := modularBinaryRep_S_inv_apply twist P
  have hkey : (modularBinaryRep n twist).ρ ModularGroup.S⁻¹ P = -P := by
    apply Subtype.ext
    show ((modularBinaryRep n twist).ρ ModularGroup.S⁻¹ P).1 = -(P : Poly)
    rw [hunfold]
    exact eq_neg_of_add_eq_zero_right hP.two_term
  have hcomp : (modularBinaryRep n twist).ρ ModularGroup.S
      ((modularBinaryRep n twist).ρ ModularGroup.S⁻¹ P) = P := by
    have hrr := rho_rho (modularBinaryRep n twist) ModularGroup.S ModularGroup.S⁻¹ P
    rw [mul_inv_cancel, map_one] at hrr
    rw [hrr]
    exact Module.End.one_apply P
  rw [hkey] at hcomp
  have hmapneg : (modularBinaryRep n twist).ρ ModularGroup.S (-P) =
      -((modularBinaryRep n twist).ρ ModularGroup.S P) := map_neg _ P
  rw [hmapneg] at hcomp
  have hfin := congrArg (fun x => -x) hcomp
  simp only [neg_neg] at hfin
  exact hfin

/-- **The first relation.** Packaging `P` as `first := ⟨-P, S⟩` in the semidirect product
`Semidirect (modularBinaryRep n twist)` (reused from `ModularH1.lean`) gives `first ^ 4 = 1`. -/
theorem first_pow_four {n : ℕ} (twist : ℤ) {P : HomogeneousPoly n}
    (hP : PeriodRelations (P : Poly)) :
    (⟨-P, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) ^ 4 = 1 := by
  have hA1 := modularBinaryRep_S_apply_eq_neg twist hP
  have hA1' : (modularBinaryRep n twist).ρ ModularGroup.S (-P) = P := by
    have hmapneg : (modularBinaryRep n twist).ρ ModularGroup.S (-P) =
        -((modularBinaryRep n twist).ρ ModularGroup.S P) := map_neg _ P
    rw [hmapneg, hA1]
    exact neg_neg P
  have hsq : (⟨-P, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) ^ 2 =
      ⟨0, ModularGroup.S ^ 2⟩ := by
    rw [pow_two]
    apply TwoCocycleExtension.ext
    · apply Subtype.ext
      show (-(P : Poly)) + ((modularBinaryRep n twist).ρ ModularGroup.S (-P)).1 +
          (zeroCycle (modularBinaryRep n twist) (ModularGroup.S, ModularGroup.S)).1 = (0 : Poly)
      rw [hA1', zeroCycle_apply]
      show -(P : Poly) + (P : Poly) + (0 : Poly) = (0 : Poly)
      ring
    · exact (pow_two ModularGroup.S).symm
  have h4eq : (4 : ℕ) = 2 * 2 := by norm_num
  calc (⟨-P, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) ^ 4
      = (⟨-P, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) ^ (2 * 2) := by rw [h4eq]
    _ = ((⟨-P, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) ^ 2) ^ 2 := by
        rw [pow_mul]
    _ = (⟨0, ModularGroup.S ^ 2⟩ : Semidirect (modularBinaryRep n twist)) ^ 2 := by rw [hsq]
    _ = ((⟨0, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) ^ 2) ^ 2 := by
        rw [pure_pow (modularBinaryRep n twist) ModularGroup.S 2]
    _ = (⟨0, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) ^ (2 * 2) := by
        rw [← pow_mul]
    _ = (⟨0, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) ^ 4 := by rw [← h4eq]
    _ = 1 := pureS_fourth (modularBinaryRep n twist)

end TernaryPeriodPolynomials.Argument.Corollary14
