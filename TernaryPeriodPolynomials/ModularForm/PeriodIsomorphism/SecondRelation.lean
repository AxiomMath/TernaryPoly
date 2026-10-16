module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.FirstRelation
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.SquareInvolution

@[expose] public section


/-!
# Corollary 1.4, Step 1: the second relation `second ^ 3 = first ^ 2`

`PeriodRelations.three_term` says `q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0`.
The two substitution matrices are exactly `VElt * VElt` and `VElt`, where
`VElt := T * S⁻¹` is the order-three element of `SL₂(ℤ)` with
`VElt = S*S*(S*modularOrderSix*S⁻¹)` (`VElt_conj`, a direct matrix identity). Combined with the
global involution `ρ(S)(ρ(S) x) = x` (corollary A4, `SquareInvolution.lean`) and corollary A1
`ρ(S) P = -P` (`FirstRelation.lean`), this operator identity converts the polynomial relation into
`P + ρ(U) P + ρ(U*U) P = 0` where `U := modularOrderSix` (`secondCubeTest`), and from there into
`second ^ 3 = first ^ 2` for `first := ⟨-P, S⟩`, `second := ⟨-P, U⟩` in the semidirect product
`Semidirect (modularBinaryRep n twist)` (`second_pow_three_eq_first_pow_two`), the other relation
`modularLiftSection` needs.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open Matrix Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup MvPolynomial
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH1
open GeneralEisenstein.Binary (substitute linearForm HomogeneousPoly Poly)
open TernaryPoly.Paper (PeriodRelations)

/-! ## Part (a): the order-three element `VElt := T * S⁻¹` -/

private def VElt : SpecialLinearGroup (Fin 2) ℤ := ModularGroup.T * ModularGroup.S⁻¹

/-- `S⁻¹ = S*S*S`, avoiding any direct computation of `S⁻¹`'s matrix. -/
private theorem S_inv_eq_cube :
    (ModularGroup.S⁻¹ : SpecialLinearGroup (Fin 2) ℤ) =
      ModularGroup.S * ModularGroup.S * ModularGroup.S := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

/-- `VElt` casts to `!![-1,1;-1,0]` as an integer matrix. -/
private theorem VElt_matrix :
    (VElt : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 1; -1, 0] := by
  have hV : VElt = ModularGroup.T * (ModularGroup.S * ModularGroup.S * ModularGroup.S) := by
    rw [VElt, S_inv_eq_cube]
  rw [hV]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- `VElt * VElt` casts to `!![0,-1;1,-1]` as an integer matrix. -/
private theorem VElt_sq_matrix :
    ((VElt * VElt : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![0, -1; 1, -1] := by
  show (VElt : Matrix (Fin 2) (Fin 2) ℤ) * (VElt : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, -1]
  rw [VElt_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `VElt` has order three. -/
private theorem VElt_cube : VElt * (VElt * VElt) = 1 := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [SpecialLinearGroup.coe_mul, VElt_matrix, VElt_sq_matrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

private theorem VElt_cube' : VElt * VElt * VElt = 1 := by
  rw [mul_assoc]; exact VElt_cube

private theorem VElt_inv_eq_sq : VElt⁻¹ = VElt * VElt := inv_eq_of_mul_eq_one_right VElt_cube

private theorem VElt_sq_inv_eq : (VElt * VElt)⁻¹ = VElt := inv_eq_of_mul_eq_one_right VElt_cube'

/-- The conjugation identity underlying the operator relation: `VElt = S*S*(S*U*S⁻¹)`, where
`U := modularOrderSix`, checked directly as a matrix identity. -/
private theorem VElt_conj :
    VElt = ModularGroup.S * ModularGroup.S *
      (ModularGroup.S * modularOrderSix * ModularGroup.S⁻¹) := by
  apply Subtype.ext
  rw [S_inv_eq_cube]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [VElt_matrix, SpecialLinearGroup.coe_mul, ModularGroup.coe_S, modularOrderSix,
      ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Part (b): translating `ρ(VElt)` and `ρ(VElt*VElt)` into raw substitutions -/

/-- The complex cast of an integer `SpecialLinearGroup` element, entrywise (local re-derivation;
`RepUnfolding.lean`'s private `castSL_apply`, and `FirstRelation.lean`/`SquareInvolution.lean`'s
own private `castSL_entry` copies, are not visible from this file). -/
private theorem castSL_entry (g : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g) :
        Matrix (Fin 2) (Fin 2) ℂ) i j = ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℂ) := by
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

private theorem castVEltSq_matrix :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL (VElt * VElt)) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, -1] := by
  ext i j
  rw [castSL_entry]
  fin_cases i <;> fin_cases j <;>
    norm_num [SpecialLinearGroup.coe_mul, VElt_matrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem castVElt_matrix :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL VElt) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![-1, 1; -1, 0] := by
  ext i j
  rw [castSL_entry]
  fin_cases i <;> fin_cases j <;> norm_num [VElt_matrix]

private theorem linearForm_castVEltSq :
    linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
        (SpecialLinearGroup.toGL (VElt * VElt)) : Matrix (Fin 2) (Fin 2) ℂ) =
      ![-X 1, X 0 - X 1] := by
  rw [castVEltSq_matrix]
  funext i
  fin_cases i <;> simp [linearForm, Fin.sum_univ_two]; ring

private theorem linearForm_castVElt :
    linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL VElt) :
      Matrix (Fin 2) (Fin 2) ℂ) = ![X 1 - X 0, -X 0] := by
  rw [castVElt_matrix]
  funext i
  fin_cases i <;> simp [linearForm, Fin.sum_univ_two]; ring

private theorem substitute_castVEltSq (p : Poly) :
    substitute (GeneralLinearGroup.map (Int.castRingHom ℂ)
        (SpecialLinearGroup.toGL (VElt * VElt)) : Matrix (Fin 2) (Fin 2) ℂ) p =
      bind₁ ![-X 1, X 0 - X 1] p := by
  show bind₁ (linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL (VElt * VElt)) : Matrix (Fin 2) (Fin 2) ℂ)) p =
    bind₁ ![-X 1, X 0 - X 1] p
  rw [linearForm_castVEltSq]

private theorem substitute_castVElt (p : Poly) :
    substitute (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL VElt) :
      Matrix (Fin 2) (Fin 2) ℂ) p = bind₁ ![X 1 - X 0, -X 0] p := by
  show bind₁ (linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL VElt) : Matrix (Fin 2) (Fin 2) ℂ)) p =
    bind₁ ![X 1 - X 0, -X 0] p
  rw [linearForm_castVElt]

/-- `ρ(VElt)` unfolds to the raw substitution `bind₁ ![-X 1, X 0 - X 1]`, matching
`PeriodRelations.three_term`'s first substitution term exactly. -/
private theorem modularBinaryRep_VElt_apply {n : ℕ} (twist : ℤ) (f : HomogeneousPoly n) :
    ((modularBinaryRep n twist).ρ VElt f).1 = bind₁ ![-X 1, X 0 - X 1] (f : Poly) := by
  rw [modularBinaryRep_apply, VElt_inv_eq_sq, substitute_castVEltSq]

/-- `ρ(VElt*VElt)` unfolds to the raw substitution `bind₁ ![X 1 - X 0, -X 0]`, matching
`PeriodRelations.three_term`'s second substitution term exactly. -/
private theorem modularBinaryRep_VElt_sq_apply {n : ℕ} (twist : ℤ) (f : HomogeneousPoly n) :
    ((modularBinaryRep n twist).ρ (VElt * VElt) f).1 = bind₁ ![X 1 - X 0, -X 0] (f : Poly) := by
  rw [modularBinaryRep_apply, VElt_sq_inv_eq, substitute_castVElt]

/-! ## Part (c): the operator identity `ρ(VElt) = ρ(S) ∘ ρ(U) ∘ ρ(S⁻¹)` -/

private theorem modularBinaryRep_VElt_rho_apply {n : ℕ} (twist : ℤ) (hn : Even n)
    (w : HomogeneousPoly n) :
    (modularBinaryRep n twist).ρ VElt w =
      (modularBinaryRep n twist).ρ ModularGroup.S
        ((modularBinaryRep n twist).ρ modularOrderSix
          ((modularBinaryRep n twist).ρ ModularGroup.S⁻¹ w)) := by
  have hSS : ∀ x : modularBinaryRep n twist, (modularBinaryRep n twist).ρ ModularGroup.S
      ((modularBinaryRep n twist).ρ ModularGroup.S x) = x := modularBinaryRep_S_S_apply twist hn
  rw [VElt_conj]
  have step1 := rho_rho (modularBinaryRep n twist) (ModularGroup.S * ModularGroup.S)
    (ModularGroup.S * modularOrderSix * ModularGroup.S⁻¹) w
  rw [← step1]
  have step2 := rho_rho (modularBinaryRep n twist) ModularGroup.S ModularGroup.S
    ((modularBinaryRep n twist).ρ (ModularGroup.S * modularOrderSix * ModularGroup.S⁻¹) w)
  rw [← step2, hSS]
  have step3 := rho_rho (modularBinaryRep n twist) (ModularGroup.S * modularOrderSix)
    ModularGroup.S⁻¹ w
  rw [← step3]
  have step4 := rho_rho (modularBinaryRep n twist) ModularGroup.S modularOrderSix
    ((modularBinaryRep n twist).ρ ModularGroup.S⁻¹ w)
  rw [← step4]

/-! ## Part (d): the second-relation polynomial fact -/

/-- **The second-relation polynomial fact.** `P + ρ(U) P + ρ(U*U) P = 0`, where
`U := modularOrderSix`. -/
theorem secondCubeTest {n : ℕ} (twist : ℤ) {P : HomogeneousPoly n} (hn : Even n)
    (hP : PeriodRelations (P : Poly)) :
    Add.add (Add.add P ((modularBinaryRep n twist).ρ modularOrderSix P : HomogeneousPoly n))
      ((modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) P : HomogeneousPoly n) =
      0 := by
  have hSS : ∀ x : modularBinaryRep n twist, (modularBinaryRep n twist).ρ ModularGroup.S
      ((modularBinaryRep n twist).ρ ModularGroup.S x) = x := modularBinaryRep_S_S_apply twist hn
  have hA1 : (modularBinaryRep n twist).ρ ModularGroup.S P = -P :=
    modularBinaryRep_S_apply_eq_neg twist hP
  have hSinv : (modularBinaryRep n twist).ρ ModularGroup.S
      ((modularBinaryRep n twist).ρ ModularGroup.S⁻¹ P) = P := by
    have hrr := rho_rho (modularBinaryRep n twist) ModularGroup.S ModularGroup.S⁻¹ P
    rw [mul_inv_cancel, map_one] at hrr
    rw [hrr]
    exact Module.End.one_apply P
  have htwo : (modularBinaryRep n twist).ρ ModularGroup.S⁻¹ P = -P := by
    have hthis := hSS ((modularBinaryRep n twist).ρ ModularGroup.S⁻¹ P)
    rw [hSinv] at hthis
    exact hthis.symm.trans hA1
  have hthree : Add.add (Add.add P ((modularBinaryRep n twist).ρ VElt P : HomogeneousPoly n))
      ((modularBinaryRep n twist).ρ (VElt * VElt) P : HomogeneousPoly n) = 0 := by
    apply Subtype.ext
    show (P : Poly) + ((modularBinaryRep n twist).ρ VElt P).1 +
        ((modularBinaryRep n twist).ρ (VElt * VElt) P).1 = (0 : Poly)
    rw [modularBinaryRep_VElt_apply, modularBinaryRep_VElt_sq_apply]
    exact hP.three_term
  have hop := modularBinaryRep_VElt_rho_apply twist hn
  have hop' : ∀ w : modularBinaryRep n twist, (modularBinaryRep n twist).ρ VElt w =
      (modularBinaryRep n twist).ρ ModularGroup.S
        ((modularBinaryRep n twist).ρ modularOrderSix
          ((modularBinaryRep n twist).ρ ModularGroup.S⁻¹ w)) :=
    modularBinaryRep_VElt_rho_apply twist hn
  have h1 : (modularBinaryRep n twist).ρ VElt P =
      -((modularBinaryRep n twist).ρ ModularGroup.S
          ((modularBinaryRep n twist).ρ modularOrderSix P)) := by
    rw [hop, htwo]
    have e1 : (modularBinaryRep n twist).ρ modularOrderSix (-P) =
        -((modularBinaryRep n twist).ρ modularOrderSix P) := map_neg _ P
    rw [e1]
    exact map_neg _ _
  have h2 : (modularBinaryRep n twist).ρ (VElt * VElt) P =
      -((modularBinaryRep n twist).ρ ModularGroup.S
          ((modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) P)) := by
    have e1 := rho_rho (modularBinaryRep n twist) VElt VElt P
    rw [← e1, h1]
    have e2 : (modularBinaryRep n twist).ρ VElt
        (-((modularBinaryRep n twist).ρ ModularGroup.S
          ((modularBinaryRep n twist).ρ modularOrderSix P))) =
        -((modularBinaryRep n twist).ρ VElt
          ((modularBinaryRep n twist).ρ ModularGroup.S
            ((modularBinaryRep n twist).ρ modularOrderSix P))) := map_neg _ _
    rw [e2, hop']
    have e3 : (modularBinaryRep n twist).ρ ModularGroup.S⁻¹
        ((modularBinaryRep n twist).ρ ModularGroup.S
          ((modularBinaryRep n twist).ρ modularOrderSix P)) =
        (modularBinaryRep n twist).ρ modularOrderSix P := by
      have e4 := rho_rho (modularBinaryRep n twist) ModularGroup.S⁻¹ ModularGroup.S
        ((modularBinaryRep n twist).ρ modularOrderSix P)
      rw [inv_mul_cancel, map_one, Module.End.one_apply] at e4
      exact e4
    rw [e3]
    have e5 := rho_rho (modularBinaryRep n twist) modularOrderSix modularOrderSix P
    rw [← e5]
  rw [h1, h2] at hthree
  have hstep : P = (modularBinaryRep n twist).ρ ModularGroup.S
      ((modularBinaryRep n twist).ρ modularOrderSix P +
        (modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) P) := by
    rw [map_add]
    set X : HomogeneousPoly n := (modularBinaryRep n twist).ρ ModularGroup.S
      ((modularBinaryRep n twist).ρ modularOrderSix P) with hXdef
    set Y : HomogeneousPoly n := (modularBinaryRep n twist).ρ ModularGroup.S
      ((modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) P) with hYdef
    show P = X + Y
    have hthree' : P + (-X) + (-Y) = (0 : HomogeneousPoly n) := hthree
    linear_combination (norm := module) hthree'
  have hstep2 : (modularBinaryRep n twist).ρ ModularGroup.S P =
      (modularBinaryRep n twist).ρ modularOrderSix P +
        (modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) P := by
    conv_lhs => rw [hstep]
    rw [hSS]
  rw [hstep2] at hA1
  set X : HomogeneousPoly n := (modularBinaryRep n twist).ρ modularOrderSix P with hXdef
  set Y : HomogeneousPoly n := (modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) P
    with hYdef
  show P + X + Y = (0 : HomogeneousPoly n)
  have hA1' : X + Y = (-P : HomogeneousPoly n) := hA1
  linear_combination (norm := module) hA1'

/-! ## Part (e): semidirect-product helpers -/

private theorem semidirect_mul {n : ℕ} (twist : ℤ) (a b : HomogeneousPoly n)
    (g h : SpecialLinearGroup (Fin 2) ℤ) :
    (⟨a, g⟩ : Semidirect (modularBinaryRep n twist)) * ⟨b, h⟩ =
      ⟨(Add.add a ((modularBinaryRep n twist).ρ g b) : HomogeneousPoly n), g * h⟩ := by
  apply TwoCocycleExtension.ext
  · show Add.add (Add.add a ((modularBinaryRep n twist).ρ g b))
        (zeroCycle (modularBinaryRep n twist) (g, h)) =
      Add.add a ((modularBinaryRep n twist).ρ g b)
    rw [zeroCycle_apply]
    exact add_zero _
  · rfl

private theorem semidirect_sq {n : ℕ} (twist : ℤ) (a : HomogeneousPoly n)
    (g : SpecialLinearGroup (Fin 2) ℤ) :
    (⟨a, g⟩ : Semidirect (modularBinaryRep n twist)) ^ 2 =
      ⟨(Add.add a ((modularBinaryRep n twist).ρ g a) : HomogeneousPoly n), g ^ 2⟩ := by
  rw [pow_two (⟨a, g⟩ : Semidirect (modularBinaryRep n twist)), semidirect_mul, pow_two g]

private theorem semidirect_cube {n : ℕ} (twist : ℤ) (a : HomogeneousPoly n)
    (g : SpecialLinearGroup (Fin 2) ℤ) :
    (⟨a, g⟩ : Semidirect (modularBinaryRep n twist)) ^ 3 =
      ⟨(Add.add (Add.add a ((modularBinaryRep n twist).ρ g a))
          ((modularBinaryRep n twist).ρ (g * g) a) :
        HomogeneousPoly n), g ^ 3⟩ := by
  have h3 : (3 : ℕ) = 2 + 1 := by norm_num
  rw [h3, pow_succ (⟨a, g⟩ : Semidirect (modularBinaryRep n twist)) 2, semidirect_sq,
    pow_succ g 2, semidirect_mul, pow_two g]

/-! ## Part (f): the second relation -/

/-- **The second relation.** Packaging `P` as `second := ⟨-P, modularOrderSix⟩` in the semidirect
product `Semidirect (modularBinaryRep n twist)` gives `second ^ 3 = first ^ 2`, where
`first := ⟨-P, S⟩`. -/
theorem second_pow_three_eq_first_pow_two {n : ℕ} (twist : ℤ) {P : HomogeneousPoly n}
    (hn : Even n) (hP : PeriodRelations (P : Poly)) :
    (⟨-P, modularOrderSix⟩ : Semidirect (modularBinaryRep n twist)) ^ 3 =
      (⟨-P, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) ^ 2 := by
  have hA1 := modularBinaryRep_S_apply_eq_neg twist hP
  have hA1' : (modularBinaryRep n twist).ρ ModularGroup.S (-P) = P := by
    have hmapneg : (modularBinaryRep n twist).ρ ModularGroup.S (-P) =
        -((modularBinaryRep n twist).ρ ModularGroup.S P) := map_neg _ P
    rw [hmapneg, hA1]
    exact neg_neg P
  have hcube := secondCubeTest twist hn hP
  have hcubeNeg : (Add.add (Add.add (-P) ((modularBinaryRep n twist).ρ modularOrderSix (-P)))
      ((modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) (-P)) :
      HomogeneousPoly n) = 0 := by
    have e1 : (modularBinaryRep n twist).ρ modularOrderSix (-P) =
        -((modularBinaryRep n twist).ρ modularOrderSix P) := map_neg _ P
    have e2 : (modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) (-P) =
        -((modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) P) := map_neg _ P
    rw [e1, e2]
    set X : HomogeneousPoly n := (modularBinaryRep n twist).ρ modularOrderSix P with hXdef
    set Y : HomogeneousPoly n := (modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) P
      with hYdef
    show (-P) + (-X) + (-Y) = (0 : HomogeneousPoly n)
    have hcube' : P + X + Y = (0 : HomogeneousPoly n) := hcube
    linear_combination (norm := module) -hcube'
  rw [semidirect_cube, semidirect_sq, hA1']
  apply TwoCocycleExtension.ext
  · show (Add.add (Add.add (-P) ((modularBinaryRep n twist).ρ modularOrderSix (-P)))
        ((modularBinaryRep n twist).ρ (modularOrderSix * modularOrderSix) (-P)) :
        HomogeneousPoly n) = (-P) + P
    linear_combination (norm := module) hcubeNeg
  · exact modularOrderSix_cube

end TernaryPeriodPolynomials.Argument.Corollary14
