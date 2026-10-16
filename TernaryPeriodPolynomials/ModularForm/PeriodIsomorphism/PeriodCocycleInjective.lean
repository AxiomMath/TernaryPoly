module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.TFixedSpace
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.PeriodCocycleLinear

@[expose] public section


/-!
# Corollary 1.4, Step 1b: injectivity of `P ↦ [periodCocycle P]`

If the `H1π`-class of `periodCocycle P` vanishes then `P = 0`.

**Proof idea.** Unfold `H1π ... = 0` (`groupCohomology.H1π_eq_zero_iff`) to get a coboundary
primitive `v` with `ρ(g) v - v = periodCocycle P g` for every `g`. Specializing at `g = T` and
using `periodCocycle_T = 0` gives `ρ(T) v = v`, so `TFixedSpace.lean`'s
`eq_smul_binaryStandardBasis_zero_of_T_fixed` gives `v = c • binaryStandardBasis n 0`.
Specializing at `g = S` and using `periodCocycle_S = -P` together with the `S`-image computation
`rho_S_basis_zero` (`ρ(S)` sends the pure `X1^n` monomial to the pure `X0^n` monomial, for even
`n`) expresses `P` as `c • binaryStandardBasis n 0 - c • binaryStandardBasis n (Fin.last n)`.
Finally, `PeriodRelations.axis_first` says `P`'s pure-`X1^n` coefficient vanishes; evaluating the
displayed form of `P` at `(X 0, X 1) = (0,1)` reads off exactly that coefficient as `c`, forcing
`c = 0` and hence `P = 0` (using `n ≠ 0` so the `X0^n`-term's evaluation at `X0 = 0` vanishes).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open Matrix Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup MvPolynomial
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein.Binary (substitute linearForm HomogeneousPoly Poly)
open TernaryPoly.Paper (PeriodRelations)

variable {n : ℕ} (twist : ℤ) {P : HomogeneousPoly n}

/-- The complex cast of an integer `SpecialLinearGroup` element, entrywise (local re-derivation,
as in `TFixedSpace.lean`). -/
private theorem castSL_entry (g : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g) :
        Matrix (Fin 2) (Fin 2) ℂ) i j = ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℂ) := by
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

/-- `S⁻¹` is `!![0,1;-1,0]` as an integer matrix (local re-derivation). -/
private theorem coe_modularS_inv :
    ((ModularGroup.S⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![0, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `S⁻¹` casts to `!![0,1;-1,0]` as a complex matrix. -/
private theorem castS_inv_matrix :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := by
  ext i j
  rw [castSL_entry]
  fin_cases i <;> fin_cases j <;> norm_num [coe_modularS_inv]

/-- The substitution linear form of `cast S⁻¹` is `![X 1, -X 0]`. -/
private theorem linearForm_castS_inv :
    linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL ModularGroup.S⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) =
      ![X 1, -X 0] := by
  rw [castS_inv_matrix]
  funext i
  fin_cases i <;> simp [linearForm, Fin.sum_univ_two]

private theorem substitute_castS_inv (p : Poly) :
    substitute (GeneralLinearGroup.map (Int.castRingHom ℂ)
        (SpecialLinearGroup.toGL ModularGroup.S⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) p =
      bind₁ ![X 1, -X 0] p := by
  show bind₁ (linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL ModularGroup.S⁻¹) : Matrix (Fin 2) (Fin 2) ℂ)) p =
    bind₁ ![X 1, -X 0] p
  rw [linearForm_castS_inv]

private theorem binaryStandardBasis_zero_coe (degree : ℕ) :
    (binaryStandardBasis degree 0 : Poly) = X 1 ^ degree := by
  rw [binaryStandardBasis_coe]
  simp

private theorem binaryStandardBasis_last_coe (degree : ℕ) :
    (binaryStandardBasis degree (Fin.last degree) : Poly) = X 0 ^ degree := by
  rw [binaryStandardBasis_coe]
  simp

/-- `ρ(S)` sends the pure `X 1 ^ n` monomial to the pure `X 0 ^ n` monomial, for even `n`. -/
private theorem rho_S_basis_zero (hn : Even n) :
    (modularBinaryRep n twist).ρ ModularGroup.S (binaryStandardBasis n 0) =
      binaryStandardBasis n (Fin.last n) := by
  apply Subtype.ext
  rw [modularBinaryRep_apply, binaryStandardBasis_zero_coe, substitute_castS_inv]
  show bind₁ ![X 1, -X 0] (X 1 ^ n) = (binaryStandardBasis n (Fin.last n) : Poly)
  rw [binaryStandardBasis_last_coe]
  simp [hn.neg_pow]

/-- **Step 1b.** `P ↦ [periodCocycle P]` is injective: if the cocycle's `H1π`-class vanishes,
`P = 0`. -/
theorem eq_zero_of_periodCocycle_H1_zero (hn0 : n ≠ 0) (hn : Even n)
    (hP : PeriodRelations (P : Poly))
    (hzero : groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hP) = 0) :
    P = 0 := by
  rw [groupCohomology.H1π_eq_zero_iff] at hzero
  obtain ⟨v, hv⟩ := hzero
  have hTeq := congrFun hv ModularGroup.T
  have hSeq := congrFun hv ModularGroup.S
  rw [periodCocycle_T] at hTeq
  rw [periodCocycle_S] at hSeq
  have hTv : (modularBinaryRep n twist).ρ ModularGroup.T v = v := sub_eq_zero.mp hTeq
  have hSeq' : (modularBinaryRep n twist).ρ ModularGroup.S v - v = -P := hSeq
  obtain ⟨c, hc⟩ := eq_smul_binaryStandardBasis_zero_of_T_fixed twist v hTv








  set v' : HomogeneousPoly n := v
  have hv_poly : (v' : Poly) = c • (X 1 : Poly) ^ n := by
    have h3 := congrArg (fun x : HomogeneousPoly n => (x : Poly)) hc
    simpa [binaryStandardBasis_zero_coe] using h3
  have hSv_poly : ((modularBinaryRep n twist).ρ ModularGroup.S v').1 = c • (X 0 : Poly) ^ n := by
    rw [modularBinaryRep_apply, hv_poly, substitute_castS_inv]
    simp [bind₁_X_right, hn.neg_pow, map_smul, map_pow]
  have hSeq_poly : (c • (X 0 : Poly) ^ n) - c • (X 1 : Poly) ^ n = -(P : Poly) := by








    have h4 := congrArg (fun x : HomogeneousPoly n => (x : Poly)) hSeq'
    have h4' : ((modularBinaryRep n twist).ρ ModularGroup.S v').1 - (v' : Poly) = -(P : Poly) :=
      h4
    rw [hSv_poly, hv_poly] at h4'
    exact h4'
  have hPolyEq : (P : Poly) = c • (X 1 : Poly) ^ n - c • (X 0 : Poly) ^ n := by
    have h5 := congrArg Neg.neg hSeq_poly
    simp only [neg_neg, neg_sub] at h5
    exact h5.symm
  have haxis : aeval (![0, 1] : Fin 2 → ℂ) (P : Poly) = 0 := by
    have hcomp := aeval_bind₁ (f := (![0, 1] : Fin 2 → ℂ))
      (g := (![0, X 1] : Fin 2 → Poly)) (φ := (P : Poly))
    have hinner : (fun i : Fin 2 => aeval (![0, 1] : Fin 2 → ℂ) ((![0, X 1] : Fin 2 → Poly) i)) =
        (![0, 1] : Fin 2 → ℂ) := by
      funext i
      fin_cases i <;> simp
    rw [hinner] at hcomp
    rw [← hcomp, hP.1]
    simp
  rw [hPolyEq] at haxis
  simp only [map_sub, map_smul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul, one_pow, mul_one, zero_pow hn0, mul_zero, sub_zero] at haxis
  have hPzero : (P : Poly) = 0 := by rw [hPolyEq, haxis]; simp
  exact Subtype.ext hPzero

end TernaryPeriodPolynomials.Argument.Corollary14
