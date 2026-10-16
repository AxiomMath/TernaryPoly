module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.PeriodCocycleMap
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.CentralCharacter
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneESDimension

@[expose] public section


/-!
# Corollary 1.4, even side, Step (c), eigenvalue sub-lemma

`reflectionH1 n twist` (`LevelOneESDimension.lean`) is the reflection involution on
`H1 (modularBinaryRep n twist)` used to split the parabolic subspace `H_par` by eigenvalue
(`E_{+1}`/`E_{-1}` in the written argument). This file shows `Φ(evenPeriodSpace ℂ n) ⊆ E_{+1}`:
for `P` in the even-parity locus (`bind₁ ![-X 0, X 1] (P:Poly) = (P:Poly)`, the condition defining
`evenPeriodSpace`), `reflectionH1 n twist` fixes `periodClass twist hn hP` -- not merely up to a
coboundary, but because the pullback cocycle underlying `reflectionH1` agrees with
`periodCocycle twist hn hP` **as a cocycle on the nose**, checked at the two generators
`cocycle_ext` needs (`ModularGroup.S` and `modularOrderSix = S * T`).

Both of those values come out to `-P` (`periodCocycle_S`, `periodCocycle_U`), and
`binaryParityReflection` fixes `-P` because it fixes `P`: `binaryParityReflection`'s underlying
substitution (negate the *second* coordinate) agrees with the substitution defining
`evenPeriodSpace` (negate the *first* coordinate) on even-homogeneous polynomials, since both
differ from "negate everything" by one further negation of the other variable, and negating
everything fixes an even-homogeneous polynomial (`bind₁_neg_X_of_isHomogeneous_even`,
`CentralCharacter.lean`). The local re-derivation of that fact below is otherwise identical to
`EvenInjectivity.lean`'s own private helpers of the same name (file-private there, so not visible
here).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.ModularH1
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open Matrix Matrix.SpecialLinearGroup
open GeneralEisenstein.Binary (HomogeneousPoly Poly substitute substitute_comp substitute_X
  linearForm)
open TernaryPoly.Paper (PeriodRelations)
open MvPolynomial

/-! ## Local re-derivation of the even-homogeneous reflection fixed-point fact
(mirrors `EvenInjectivity.lean`'s private helpers of the same name, not visible from this file) -/

private theorem substitute_one (p : Poly) :
    substitute (1 : Matrix (Fin 2) (Fin 2) ℂ) p = p := by
  have hid : substitute (1 : Matrix (Fin 2) (Fin 2) ℂ) = AlgHom.id ℂ Poly := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [substitute_X]
    fin_cases i <;> simp [linearForm, Matrix.one_apply]
  rw [hid, AlgHom.id_apply]

private theorem linearForm_neg_one (i : Fin 2) :
    linearForm (-1 : Matrix (Fin 2) (Fin 2) ℂ) i = -X i := by
  fin_cases i <;> simp [linearForm, Matrix.neg_apply, Matrix.one_apply]

private theorem substitute_neg_one (p : Poly) :
    substitute (-1 : Matrix (Fin 2) (Fin 2) ℂ) p = bind₁ (fun i => -X i) p := by
  show bind₁ (linearForm (-1 : Matrix (Fin 2) (Fin 2) ℂ)) p = bind₁ (fun i => -X i) p
  rw [funext linearForm_neg_one]

private theorem substitute_negateSecond_eq_negateFirst {n : ℕ} (hn : Even n) {P : Poly}
    (hP : P.IsHomogeneous n) :
    substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) P =
      substitute (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) P := by
  have hτσ : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![-1, 0; 0, 1] = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hσσ : (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![-1, 0; 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have step1 : substitute (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
      (substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) P) = P := by
    rw [← AlgHom.comp_apply, substitute_comp, hτσ, substitute_neg_one]
    exact bind₁_neg_X_of_isHomogeneous_even hP hn
  have step2 : substitute (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
      (substitute (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
        (substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) P)) =
      substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) P := by
    rw [← AlgHom.comp_apply, substitute_comp, hσσ, substitute_one]
  rw [step1] at step2
  exact step2.symm

private theorem binaryParityReflection_val {n : ℕ} (x : HomogeneousPoly n) :
    (binaryParityReflection n x : Poly) =
      substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) (x : Poly) := rfl

/-- The even-homogeneous reflection fixed-point fact: if `bind₁ ![-X 0, X 1] (Q:Poly) = (Q:Poly)`
(the `evenPeriodSpace`-defining condition), then `binaryParityReflection n Q = Q`. -/
private theorem binaryParityReflection_fixed {n : ℕ} (hn : Even n) (Q : HomogeneousPoly n)
    (hQ : bind₁ ![-X 0, X 1] (Q : Poly) = (Q : Poly)) :
    binaryParityReflection n Q = Q := by
  apply Subtype.ext
  rw [binaryParityReflection_val,
    substitute_negateSecond_eq_negateFirst hn ((mem_homogeneousSubmodule n (Q : Poly)).mp Q.2)]
  show bind₁ (linearForm (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)) (Q : Poly) = (Q : Poly)
  rw [show linearForm (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) = ![-X 0, X 1] from by
    funext i; fin_cases i <;> simp [linearForm, Fin.sum_univ_two]]
  exact hQ

/-- `modularReflection` sends `modularOrderSix = S * T` to `S⁻¹ * T⁻¹`: `modularReflection` is a
`MonoidHom`, and `modularReflection_S`/`modularReflection_T` give the two factors
(`ModularReflection.lean`). -/
private theorem modularReflection_U :
    modularReflection modularOrderSix = ModularGroup.S⁻¹ * ModularGroup.T⁻¹ := by
  show modularReflection (ModularGroup.S * ModularGroup.T) = _
  rw [map_mul, modularReflection_S, modularReflection_T]

variable {n : ℕ} (twist : ℤ)

/-- **Step (c), eigenvalue sub-lemma.** For `P` in the even-parity locus
(`bind₁ ![-X 0, X 1] (P:Poly) = (P:Poly)`, the condition defining `evenPeriodSpace`), the
reflection involution `reflectionH1 n twist` fixes `periodClass twist hn hP`. -/
theorem reflectionH1_periodClass (hn : Even n) {P : HomogeneousPoly n}
    (hP : PeriodRelations (P : Poly))
    (hPeven : bind₁ ![-X 0, X 1] (P : Poly) = (P : Poly)) :
    reflectionH1 n twist (periodClass twist hn hP) = periodClass twist hn hP := by
  have hnegPeven : bind₁ ![-X 0, X 1] (((-P : HomogeneousPoly n) : Poly)) =
      ((-P : HomogeneousPoly n) : Poly) := by
    have hcoe : ((-P : HomogeneousPoly n) : Poly) = -(P : Poly) := by simp
    rw [hcoe, map_neg, hPeven]
  have hcocycle : oneCocyclePullback (modularBinaryRep n twist) (modularBinaryRep n twist)
      modularReflection (binaryParityReflection n) (reflection_intertwines n twist)
      (periodCocycle twist hn hP) = periodCocycle twist hn hP := by
    apply cocycle_ext (modularBinaryRep n twist)
    · show binaryParityReflection n (periodCocycle twist hn hP (modularReflection ModularGroup.S)) =
        periodCocycle twist hn hP ModularGroup.S
      rw [modularReflection_S, periodCocycle_S_inv, periodCocycle_S]
      exact binaryParityReflection_fixed hn (-P) hnegPeven
    · have hTinv : periodCocycle twist hn hP ModularGroup.T⁻¹ = 0 := by
        rw [cocycle_inv, periodCocycle_T, map_zero, neg_zero]
      have hU : periodCocycle twist hn hP (ModularGroup.S⁻¹ * ModularGroup.T⁻¹) = -P := by
        rw [cocycle_mul, hTinv, map_zero, zero_add, periodCocycle_S_inv, periodCocycle_S]
      show binaryParityReflection n
          (periodCocycle twist hn hP (modularReflection modularOrderSix)) =
        periodCocycle twist hn hP modularOrderSix
      rw [modularReflection_U, hU, periodCocycle_U]
      exact binaryParityReflection_fixed hn (-P) hnegPeven
  show reflectionH1 n twist
      (groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hP)) =
    groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hP)
  rw [show reflectionH1 n twist
        (groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hP)) =
      groupCohomology.H1π (modularBinaryRep n twist)
        (oneCocyclePullback (modularBinaryRep n twist) (modularBinaryRep n twist) modularReflection
          (binaryParityReflection n) (reflection_intertwines n twist) (periodCocycle twist hn hP))
      from oneCocyclePullbackH1_apply _ _ _ _ _ (periodCocycle twist hn hP), hcocycle]

end TernaryPeriodPolynomials.Argument.Corollary14
