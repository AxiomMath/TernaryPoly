module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.PeriodCocycleMap
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.BoundaryFunctional

@[expose] public section


/-!
# Corollary 1.4, even side, Step (a): the period map lands in the parabolic subspace

`H_par := LinearMap.ker (beta n twist)` is the subspace of `H1 (modularBinaryRep n twist)`
consisting of classes with a cocycle representative vanishing on `T` (`beta_H1π`). Every class in
the image of `periodCocycleMap` has such a representative directly: `periodCocycle twist hn hP`
itself vanishes on `T` (`periodCocycle_T`), by construction. Hence the whole image of
`periodCocycleMap twist hn` (and in particular of its restriction to `evenPeriodSpace ℂ n`) lies in
`H_par`, with no further hypothesis on `P`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein.Binary (HomogeneousPoly Poly)
open TernaryPoly.Paper (PeriodRelations periodSpace)

variable {n : ℕ} (twist : ℤ)

/-- **Step (a).** `periodClass`'s value lies in `ker (beta n twist)`: its canonical cocycle
representative `periodCocycle twist hn hP` vanishes on `T` (`periodCocycle_T`), so `beta_H1π`
reduces the claim to `ell n 0 = 0`. -/
theorem beta_periodClass_eq_zero (hn : Even n) {P : HomogeneousPoly n}
    (hP : PeriodRelations (P : Poly)) :
    beta n twist (periodClass twist hn hP) = 0 := by
  show beta n twist (groupCohomology.H1π (modularBinaryRep n twist) (periodCocycle twist hn hP)) =
    0
  rw [beta_H1π, periodCocycle_T]
  exact map_zero (ell n)

/-- **Step (a), bundled.** The image of `periodCocycleMap twist hn` lies in the parabolic
subspace `ker (beta n twist)` (`H_par` in the written argument). -/
theorem periodCocycleMap_mem_ker_beta (hn : Even n) (q : periodSpace ℂ n) :
    beta n twist (periodCocycleMap twist hn q) = 0 :=
  beta_periodClass_eq_zero twist hn (periodSpaceToHomogeneous_periodRelations q.2)

end TernaryPeriodPolynomials.Argument.Corollary14
