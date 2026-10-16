module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.SecondRelation

@[expose] public section


/-!
# Corollary 1.4, Step 1: the period cocycle `periodCocycle P` on `SL₂(ℤ)`

Packaging `P` (satisfying `PeriodRelations`) as `first := ⟨-P, S⟩` and
`second := ⟨-P, modularOrderSix⟩` in `Semidirect (modularBinaryRep n twist)`
(`first_pow_four`/`second_pow_three_eq_first_pow_two`, `FirstRelation.lean`/`SecondRelation.lean`),
`modularLiftSection` (`ModularLifting.lean`) gives a group hom
`periodLift : SL₂(ℤ) →* Semidirect (modularBinaryRep n twist)` with `periodLift S = first`,
`periodLift U = second` (`modularLiftSection_first`/`_second`, `ModularH1.lean`). The map
`g ↦ (periodLift g).coefficient` is then a 1-cocycle (`periodCocycle`), with
`periodCocycle P S = -P` (`periodCocycle_S`) and, since `S * T = modularOrderSix` is the
definition of `modularOrderSix`, `periodCocycle P T = 0` (`periodCocycle_T`, via the cancellation
`periodLift S * periodLift T = periodLift U = periodLift S * ⟨0,T⟩`) and
`periodCocycle P S⁻¹ = periodCocycle P S` (`periodCocycle_S_inv`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open Matrix Matrix.SpecialLinearGroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH1
open GeneralEisenstein.Binary (HomogeneousPoly Poly)
open TernaryPoly.Paper (PeriodRelations)

variable {n : ℕ} (twist : ℤ) {P : HomogeneousPoly n}

/-- Semidirect-product multiplication (local re-derivation; `SecondRelation.lean`'s private
`semidirect_mul` is not visible from this file). -/
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

/-! ## Part (a): the lift of `P`'s two relations to a group hom on `SL₂(ℤ)` -/

theorem periodFirst_projection (P : HomogeneousPoly n) :
    twoCocycleExtensionProjection (modularBinaryRep n twist) (zeroCycle (modularBinaryRep n twist))
        (zeroCycle_unit (modularBinaryRep n twist))
      (⟨-P, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) = ModularGroup.S := rfl

theorem periodSecond_projection (P : HomogeneousPoly n) :
    twoCocycleExtensionProjection (modularBinaryRep n twist) (zeroCycle (modularBinaryRep n twist))
        (zeroCycle_unit (modularBinaryRep n twist))
      (⟨-P, modularOrderSix⟩ : Semidirect (modularBinaryRep n twist)) = modularOrderSix := rfl

/-- The group hom `SL₂(ℤ) →* Semidirect (modularBinaryRep n twist)` sending `S ↦ ⟨-P,S⟩`,
`modularOrderSix ↦ ⟨-P,modularOrderSix⟩`. -/
def periodLift (hn : Even n) (hP : PeriodRelations (P : Poly)) :
    SpecialLinearGroup (Fin 2) ℤ →* Semidirect (modularBinaryRep n twist) :=
  modularLiftSection
    (twoCocycleExtensionProjection (modularBinaryRep n twist) (zeroCycle (modularBinaryRep n twist))
      (zeroCycle_unit (modularBinaryRep n twist)))
    ⟨-P, ModularGroup.S⟩ ⟨-P, modularOrderSix⟩ (periodFirst_projection twist P)
    (periodSecond_projection twist P) (first_pow_four twist hP)
    (second_pow_three_eq_first_pow_two twist hn hP)

theorem periodLift_S (hn : Even n) (hP : PeriodRelations (P : Poly)) :
    periodLift twist hn hP ModularGroup.S = ⟨-P, ModularGroup.S⟩ :=
  modularLiftSection_first _ _ _ (periodFirst_projection twist P) (periodSecond_projection twist P)
    (first_pow_four twist hP) (second_pow_three_eq_first_pow_two twist hn hP)

theorem periodLift_U (hn : Even n) (hP : PeriodRelations (P : Poly)) :
    periodLift twist hn hP modularOrderSix = ⟨-P, modularOrderSix⟩ :=
  modularLiftSection_second _ _ _ (periodFirst_projection twist P) (periodSecond_projection twist P)
    (first_pow_four twist hP) (second_pow_three_eq_first_pow_two twist hn hP)

theorem periodLift_element (hn : Even n) (hP : PeriodRelations (P : Poly))
    (g : SpecialLinearGroup (Fin 2) ℤ) : (periodLift twist hn hP g).element = g :=
  modularLiftSection_projection _ _ _ (periodFirst_projection twist P) (periodSecond_projection twist P)
    (first_pow_four twist hP) (second_pow_three_eq_first_pow_two twist hn hP) g

/-! ## Part (b): the associated 1-cocycle -/

/-- The 1-cocycle `g ↦ (periodLift ... g).coefficient` associated to `P`'s period relations. -/
def periodCocycle (hn : Even n) (hP : PeriodRelations (P : Poly)) :
    groupCohomology.cocycles₁ (modularBinaryRep n twist) :=
  ⟨fun g => (periodLift twist hn hP g).coefficient, by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    have equation := congrArg TwoCocycleExtension.coefficient ((periodLift twist hn hP).map_mul g h)
    change (periodLift twist hn hP (g * h)).coefficient =
      (periodLift twist hn hP g).coefficient +
        (modularBinaryRep n twist).ρ (periodLift twist hn hP g).element
          (periodLift twist hn hP h).coefficient +
        (zeroCycle (modularBinaryRep n twist))
          ((periodLift twist hn hP g).element, (periodLift twist hn hP h).element) at equation
    rw [periodLift_element, periodLift_element] at equation
    change (periodLift twist hn hP (g * h)).coefficient =
      (modularBinaryRep n twist).ρ g (periodLift twist hn hP h).coefficient +
        (periodLift twist hn hP g).coefficient
    rw [equation, zeroCycle_apply, add_zero, add_comm]⟩

theorem periodCocycle_S (hn : Even n) (hP : PeriodRelations (P : Poly)) :
    periodCocycle twist hn hP ModularGroup.S = -P := by
  change (periodLift twist hn hP ModularGroup.S).coefficient = -P
  rw [periodLift_S]

theorem periodCocycle_U (hn : Even n) (hP : PeriodRelations (P : Poly)) :
    periodCocycle twist hn hP modularOrderSix = -P := by
  change (periodLift twist hn hP modularOrderSix).coefficient = -P
  rw [periodLift_U]

/-! ## Part (c): the vanishing fact `periodCocycle P T = 0` -/

/-- `S * T = modularOrderSix`: the defining equation of `modularOrderSix`. -/
private theorem S_mul_T_eq_U : ModularGroup.S * ModularGroup.T = modularOrderSix := rfl

theorem periodCocycle_T (hn : Even n) (hP : PeriodRelations (P : Poly)) :
    periodCocycle twist hn hP ModularGroup.T = 0 := by
  have hmulRHS : (⟨(Add.add (-P) ((modularBinaryRep n twist).ρ ModularGroup.S 0) :
      HomogeneousPoly n), ModularGroup.S * ModularGroup.T⟩ :
      Semidirect (modularBinaryRep n twist)) = ⟨-P, modularOrderSix⟩ := by
    apply TwoCocycleExtension.ext
    · show Add.add (-P : HomogeneousPoly n) ((modularBinaryRep n twist).ρ ModularGroup.S 0) = -P
      rw [map_zero]
      exact add_zero _
    · exact S_mul_T_eq_U
  have hmul : periodLift twist hn hP ModularGroup.S *
      (⟨0, ModularGroup.T⟩ : Semidirect (modularBinaryRep n twist)) =
      periodLift twist hn hP modularOrderSix := by
    rw [periodLift_S, periodLift_U]
    exact (semidirect_mul twist (-P) 0 ModularGroup.S ModularGroup.T).trans hmulRHS
  have hmul2 : periodLift twist hn hP ModularGroup.S * periodLift twist hn hP ModularGroup.T =
      periodLift twist hn hP modularOrderSix := by
    rw [← (periodLift twist hn hP).map_mul, S_mul_T_eq_U]
  have hcancel := mul_left_cancel (hmul2.trans hmul.symm)
  change (periodLift twist hn hP ModularGroup.T).coefficient = (0 : HomogeneousPoly n)
  exact congrArg TwoCocycleExtension.coefficient hcancel

/-! ## Part (d): the symmetry fact `periodCocycle P S⁻¹ = periodCocycle P S` -/

theorem periodCocycle_S_inv (hn : Even n) (hP : PeriodRelations (P : Poly)) :
    periodCocycle twist hn hP ModularGroup.S⁻¹ = periodCocycle twist hn hP ModularGroup.S := by
  have hSnegP : (modularBinaryRep n twist).ρ ModularGroup.S (-P) = P := by
    have hneg : (modularBinaryRep n twist).ρ ModularGroup.S (-P) =
        -((modularBinaryRep n twist).ρ ModularGroup.S P) := map_neg _ P
    have hA1 : (modularBinaryRep n twist).ρ ModularGroup.S P = -P :=
      modularBinaryRep_S_apply_eq_neg twist hP
    rw [hneg, hA1]
    exact neg_neg P
  have honeRHS : (⟨(Add.add (-P) ((modularBinaryRep n twist).ρ ModularGroup.S (-P)) :
      HomogeneousPoly n), ModularGroup.S * ModularGroup.S⁻¹⟩ :
      Semidirect (modularBinaryRep n twist)) = 1 := by
    apply TwoCocycleExtension.ext
    · show Add.add (-P : HomogeneousPoly n) ((modularBinaryRep n twist).ρ ModularGroup.S (-P)) = 0
      rw [hSnegP]
      show (-P : HomogeneousPoly n) + P = 0
      abel
    · exact mul_inv_cancel ModularGroup.S
  have hone : (⟨-P, ModularGroup.S⟩ : Semidirect (modularBinaryRep n twist)) *
      (⟨-P, ModularGroup.S⁻¹⟩ : Semidirect (modularBinaryRep n twist)) = 1 :=
    (semidirect_mul twist (-P) (-P) ModularGroup.S ModularGroup.S⁻¹).trans honeRHS
  have hinv : periodLift twist hn hP ModularGroup.S⁻¹ =
      (⟨-P, ModularGroup.S⁻¹⟩ : Semidirect (modularBinaryRep n twist)) := by
    rw [map_inv, periodLift_S]
    exact inv_eq_of_mul_eq_one_right hone
  change (periodLift twist hn hP ModularGroup.S⁻¹).coefficient =
    (periodLift twist hn hP ModularGroup.S).coefficient
  rw [hinv, periodLift_S]

end TernaryPeriodPolynomials.Argument.Corollary14
