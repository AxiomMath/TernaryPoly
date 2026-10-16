module

public import TernaryPeriodPolynomials.ModularForm.Period.InjectiveDimension
public import TernaryPeriodPolynomials.ModularForm.PeriodDetection.Intertwining
public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResidueDetectionActual
public import TernaryPeriodPolynomials.Polynomial.RestrictionEquiv
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenCuspBridge

@[expose] public section


/-!
# Corollary 1.4, first conjunct, symmetric half: the odd-period bijection

For every even `n`, the cusp-to-period map `Forms n → BinaryComplexPeriod.space ℂ n` is
bijective, unconditionally. The chain:

* `TernaryPoly.BinaryLiftableResidueDetection.actualIntertwining n hn` gives the Hecke
  intertwining witness unconditionally for every even `n`.
* `TernaryPoly.BinaryCuspPeriodDetection.kernelStable_of_intertwines` turns that into
  `KernelStable n hn`.
* `TernaryPoly.BinaryCuspPeriodInjective.periodEquivOfKernelStable` turns kernel stability
  (plus the known dimension match `periodMap_finrank_eq`) into the actual `LinearEquiv`.

Composing with `TernaryPoly.Paper.oddPeriodSpaceEquiv` and `TernaryPeriodPolynomials.Argument.RouteIndependent.symmetricRestrictionEquiv`
transports this to a bijection `Forms n ≃ₗ[ℂ] symmetricSolutionSpace ℂ n` whose coercion is
`cyclicLift (oddPeriodPart n f)`, matching the first conjunct of `period_isomorphisms_and_finrank`'s symmetric
half.
-/

open MvPolynomial TernaryPoly.Paper TernaryPoly.BinaryCuspPeriod
  TernaryPoly.BinaryCuspPeriodInjective TernaryPoly.BinaryCuspPeriodDetection

namespace TernaryPeriodPolynomials.Argument.Corollary14

open TernaryPeriodPolynomials.Argument.RouteIndependent

/-- The odd-period map's kernel is Hecke-stable for every even `n`: this is unconditional,
via the Hecke-detection chain in `TernaryPoly.BinaryLiftableResidueDetection`. -/
theorem kernelStable (n : ℕ) (hn : Even n) : KernelStable n hn :=
  kernelStable_of_intertwines n hn _ _
    (TernaryPoly.BinaryLiftableResidueDetection.actualIntertwining n hn)

/-- **Corollary 1.4, first conjunct, symmetric half.** For every even `n`, `Forms n` is linearly
isomorphic to `symmetricSolutionSpace ℂ n` via the odd period map followed by the cyclic-lift
identification. -/
noncomputable def oddBijection (n : ℕ) (hn : Even n) :
    Forms n ≃ₗ[ℂ] symmetricSolutionSpace ℂ n :=
  (periodEquivOfKernelStable n hn (kernelStable n hn)).trans
    ((oddPeriodSpaceEquiv ℂ n).symm.trans (TernaryPeriodPolynomials.Argument.RouteIndependent.symmetricRestrictionEquiv ℂ n).symm)

theorem oddPeriodSpaceEquiv_symm_apply_coe (n : ℕ)
    (w : TernaryPoly.BinaryComplexPeriod.space ℂ n) :
    (((oddPeriodSpaceEquiv ℂ n).symm w : oddPeriodSpace ℂ n) : MvPolynomial (Fin 2) ℂ) =
      w.val :=
  rfl

/-- The bijection's coercion matches the paper's explicit formula. -/
theorem oddBijection_coe (n : ℕ) (hn : Even n) (f : Forms n) :
    ((oddBijection n hn f : symmetricSolutionSpace ℂ n) : MvPolynomial (Fin 3) ℂ) =
      cyclicLift (TernaryPeriodPolynomials.Argument.oddPeriodPart n f) := by
  show (((TernaryPeriodPolynomials.Argument.RouteIndependent.symmetricRestrictionEquiv ℂ n).symm ((oddPeriodSpaceEquiv ℂ n).symm
      (periodEquivOfKernelStable n hn (kernelStable n hn) f))) :
      MvPolynomial (Fin 3) ℂ) = _
  rw [symmetricRestrictionEquiv_new_symm_apply, oddPeriodSpaceEquiv_symm_apply_coe,
    periodEquivOfKernelStable_apply, periodMap_coe, oddPeriod_eq_oddPeriodPart]

end TernaryPeriodPolynomials.Argument.Corollary14
