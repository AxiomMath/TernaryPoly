module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.CocycleConstruction
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.PeriodCocycleLinear
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.PeriodCocycleInjective
public import TernaryPeriodPolynomials.Polynomial.Definitions

@[expose] public section


/-!
# Corollary 1.4, Step 1 (bundling): the period-class linear map







This file packages the already-established facts about `periodCocycle` (`CocycleConstruction.lean`),
its additivity/homogeneity in `P` (`periodCocycle_add`/`periodCocycle_smul`,
`PeriodCocycleLinear.lean`), and the injectivity of its `H1π`-class
(`eq_zero_of_periodCocycle_H1_zero`, `PeriodCocycleInjective.lean`) into a single genuine
`LinearMap`

  `periodCocycleMap twist hn : periodSpace ℂ n →ₗ[ℂ] groupCohomology.H1 (modularBinaryRep n twist)`

together with its injectivity (`periodCocycleMap_injective`). `periodSpace ℂ n`
(`TernaryPeriodPolynomials/Polynomial/Definitions.lean`) is the ambient space
`homogeneousSubmodule (Fin 2) ℂ n ⊓ periods ℂ` of homogeneous degree-`n` binary polynomials
satisfying `PeriodRelations`; `evenPeriodSpace ℂ n` is a further sub-`Submodule` of it (the
`+1`-eigenspace of the `X 0 ↦ -X 0` involution), so this map and its injectivity restrict to
`evenPeriodSpace ℂ n` immediately (precompose with the inclusion
`Submodule.subtype`/`Submodule.inclusion` given by `evenPeriodSpace ℂ n ≤ periodSpace ℂ n`), with
no further work.

**This file is only the bundling step.** The dimension bound for `evenPeriodSpace ℂ n` is obtained
elsewhere: the image of this map lies in the parabolic subspace `ker β` (`ParabolicSubspace.lean`)
and in the `+1`-eigenspace of the reflection (`ReflectionEigenvalue.lean`); the cusp-form period maps
of the opposite twist (`OtherTwistPeriods.lean`) fill the `-1`-eigenspace of `ker β` with at least
`d` dimensions, while `dim ker β ≤ 2d` (`ParabolicDimension.lean`); hence the `+1`-eigenspace of
`ker β` has dimension at most `d` (`ParabolicIndependence.lean`), and `EvenBijection.lean` combines
this with the injectivity proved here.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open Matrix Matrix.SpecialLinearGroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH1
open GeneralEisenstein.Binary (HomogeneousPoly Poly)
open TernaryPoly.Paper (PeriodRelations periodSpace periods mem_periodSpace)
open MvPolynomial

variable {n : ℕ} (twist : ℤ)

/-! ## Repackaging `q ∈ periodSpace ℂ n` as a `HomogeneousPoly n` term -/

theorem periodSpace_mem_homogeneous {q : Poly} (hq : q ∈ periodSpace ℂ n) :
    q ∈ homogeneousSubmodule (Fin 2) ℂ n :=
  (mem_homogeneousSubmodule n q).mpr ((mem_periodSpace n q).mp hq).1

/-- The `HomogeneousPoly n` term underlying `q ∈ periodSpace ℂ n`. -/
def periodSpaceToHomogeneous {q : Poly} (hq : q ∈ periodSpace ℂ n) : HomogeneousPoly n :=
  ⟨q, periodSpace_mem_homogeneous hq⟩

@[simp] theorem periodSpaceToHomogeneous_coe {q : Poly} (hq : q ∈ periodSpace ℂ n) :
    (periodSpaceToHomogeneous hq : Poly) = q := rfl





theorem periodSpaceToHomogeneous_periodRelations {q : Poly} (hq : q ∈ periodSpace ℂ n) :
    PeriodRelations ((periodSpaceToHomogeneous hq : HomogeneousPoly n) : Poly) :=
  ((mem_periodSpace n q).mp hq).2

/-! ## The period-class map, as a function of a `HomogeneousPoly n` term -/

/-- The period cocycle's `H1π`-class. Matches `periodCocycle`'s own signature exactly, so
`periodClass_add`/`periodClass_smul` below are direct corollaries of `periodCocycle_add`/
`periodCocycle_smul` (`PeriodCocycleLinear.lean`), with no further bridging needed. -/
def periodClass (hn : Even n) {P : HomogeneousPoly n} (hP : PeriodRelations (P : Poly)) :
    groupCohomology.H1 (modularBinaryRep n twist) :=
  groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hP)

theorem periodClass_add (hn : Even n) {P Q : HomogeneousPoly n}
    (hP : PeriodRelations (P : Poly)) (hQ : PeriodRelations (Q : Poly))
    (hPQ : PeriodRelations ((P + Q : HomogeneousPoly n) : Poly)) :
    periodClass twist hn hPQ = periodClass twist hn hP + periodClass twist hn hQ :=
  calc periodClass twist hn hPQ
      = groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hPQ) := rfl
    _ = groupCohomology.H1π (modularBinaryRep n twist)
          (periodCocycle twist hn hP + periodCocycle twist hn hQ) := by
        rw [periodCocycle_add twist hn hP hQ hPQ]
    _ = groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hP) +
          groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hQ) :=







        map_add _ _ _
    _ = periodClass twist hn hP + periodClass twist hn hQ := rfl

theorem periodClass_smul (hn : Even n) (c : ℂ) {P : HomogeneousPoly n}
    (hP : PeriodRelations (P : Poly))
    (hcP : PeriodRelations ((c • P : HomogeneousPoly n) : Poly)) :
    periodClass twist hn hcP = c • periodClass twist hn hP :=
  calc periodClass twist hn hcP
      = groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hcP) := rfl
    _ = groupCohomology.H1π (modularBinaryRep n twist) (c • periodCocycle twist hn hP) := by
        rw [periodCocycle_smul twist hn c hP hcP]
    _ = c • groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hP) :=

        map_smul _ _ _
    _ = c • periodClass twist hn hP := rfl

/-! ## Step 1 (bundling): a genuine `LinearMap` on `periodSpace ℂ n`, and its injectivity -/

/-- `periodClass` only depends on `P : HomogeneousPoly n` up to equality of `P` itself: any two
`PeriodRelations` proofs for equal `P`'s give the same class.


-/
theorem periodClass_congr (hn : Even n) {P P' : HomogeneousPoly n} (hPP' : P = P')
    (hP : PeriodRelations (P : Poly)) (hP' : PeriodRelations (P' : Poly)) :
    periodClass twist hn hP = periodClass twist hn hP' := by
  subst hPP'
  rfl

/-- **Step 1 (bundling).** The period-class map, as a `LinearMap` out of `periodSpace ℂ n`. -/
def periodCocycleMap (hn : Even n) :
    periodSpace ℂ n →ₗ[ℂ] groupCohomology.H1 (modularBinaryRep n twist) where
  toFun q := periodClass twist hn (periodSpaceToHomogeneous_periodRelations q.2)
  map_add' p q := by
    show periodClass twist hn (periodSpaceToHomogeneous_periodRelations (p + q).2) =
      periodClass twist hn (periodSpaceToHomogeneous_periodRelations p.2) +
        periodClass twist hn (periodSpaceToHomogeneous_periodRelations q.2)
    have hAB : periodSpaceToHomogeneous (p + q).2 =
        periodSpaceToHomogeneous p.2 + periodSpaceToHomogeneous q.2 := by
      apply Subtype.ext
      simp
    have hPQ : PeriodRelations
        ((periodSpaceToHomogeneous p.2 + periodSpaceToHomogeneous q.2 : HomogeneousPoly n) :
          Poly) :=
      hAB ▸ periodSpaceToHomogeneous_periodRelations (p + q).2
    calc periodClass twist hn (periodSpaceToHomogeneous_periodRelations (p + q).2)
        = periodClass twist hn hPQ := periodClass_congr twist hn hAB _ _
      _ = periodClass twist hn (periodSpaceToHomogeneous_periodRelations p.2) +
            periodClass twist hn (periodSpaceToHomogeneous_periodRelations q.2) :=
          periodClass_add twist hn _ _ hPQ
  map_smul' c q := by
    show periodClass twist hn (periodSpaceToHomogeneous_periodRelations (c • q).2) =
      c • periodClass twist hn (periodSpaceToHomogeneous_periodRelations q.2)
    have hcq : periodSpaceToHomogeneous (c • q).2 = c • periodSpaceToHomogeneous q.2 := by
      apply Subtype.ext
      simp
    have hcP : PeriodRelations ((c • periodSpaceToHomogeneous q.2 : HomogeneousPoly n) : Poly) :=
      hcq ▸ periodSpaceToHomogeneous_periodRelations (c • q).2
    calc periodClass twist hn (periodSpaceToHomogeneous_periodRelations (c • q).2)
        = periodClass twist hn hcP := periodClass_congr twist hn hcq _ _
      _ = c • periodClass twist hn (periodSpaceToHomogeneous_periodRelations q.2) :=
          periodClass_smul twist hn c _ hcP

/-- **Step 1 (bundling), injectivity.** Immediate from `eq_zero_of_periodCocycle_H1_zero`
(`PeriodCocycleInjective.lean`). -/
theorem periodCocycleMap_injective (hn0 : n ≠ 0) (hn : Even n) :
    Function.Injective (periodCocycleMap twist hn) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨q, hq⟩ hzero
  have hzero' : groupCohomology.H1π (modularBinaryRep n twist)
      (periodCocycle twist hn (periodSpaceToHomogeneous_periodRelations hq)) = 0 := hzero
  apply Subtype.ext
  show q = 0
  have hP0 : (periodSpaceToHomogeneous hq : HomogeneousPoly n) = 0 :=
    eq_zero_of_periodCocycle_H1_zero twist hn0 hn
      (periodSpaceToHomogeneous_periodRelations hq) hzero'
  simpa using congrArg (fun x : HomogeneousPoly n => (x : Poly)) hP0

end TernaryPeriodPolynomials.Argument.Corollary14
