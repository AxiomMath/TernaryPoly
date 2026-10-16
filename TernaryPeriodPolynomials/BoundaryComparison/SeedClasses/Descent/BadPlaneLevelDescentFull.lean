module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneLevelDescent
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.DescentRadical

@[expose] public section


/-!
# Level descent at the identity plane without a hypothesis on the radical

Paper: Lemma C.3 (`ar:lem:seed`).

`badPlane_level_descent_full`, `badPlane_locallyInner_level_descent_full`: for every class
`z ∈ H²(Λ₀, E_n)` (no hypothesis on its radical restriction, any `n`), `z` is in `CuspH2` (zero radical
restriction and edge in `badPlaneCuspidal n`), equivalently has locally inner image, iff its restriction
to the plane group of `Γ(N)` lies in `gammaNCuspidalInH2 N n`.  This is `BadPlaneLevelDescent` with the
hypothesis `hz` removed, using `LevelDescentRadical.cuspH2_descent`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- **Level descent at the identity plane, no hypothesis on the radical restriction.** -/
theorem badPlane_level_descent_full (N n : ℕ) [NeZero N]
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    LocallyInner.CuspH2 (identityPlaneCoefficientRep n) identityPlaneSplitting cuspGL z ↔
      EdgeNat.h2Map (gammaNToStab N) (identityPlaneCoefficientRep n) (gammaNRep N n)
        LinearMap.id (coeff_hT N n) z ∈ gammaNCuspidalInH2 N n := by
  rw [mem_gammaNCuspidalInH2_iff]
  exact cuspH2_descent identityPlaneSplitting (gammaNSplitting N) (gammaNToStab N) (leviIncl N)
    (radScale N) (gammaNToStab_inl N) (gammaNToStab_split N) (gammaNToStab_injective N)
    (identityPlaneCoefficientRep n) (gammaNRep N n) LinearMap.id (coeff_hT N n)
    Function.bijective_id cuspGL (fun F V x => hB_GL F V x) (fun F V x => hB_Gamma N F V x) z

/-- **Locally inner classes at the identity plane, every class, every `n`.** -/
theorem badPlane_locallyInner_level_descent_full (N n : ℕ) [NeZero N]
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    badPlaneH2Equiv n z ∈ locallyInnerClasses n trivialCharacter .plane
        FacePairingFull.Face.badPlaneFlag ↔
      EdgeNat.h2Map (gammaNToStab N) (identityPlaneCoefficientRep n) (gammaNRep N n)
        LinearMap.id (coeff_hT N n) z ∈ gammaNCuspidalInH2 N n :=
  (badPlaneH2Equiv_mem_locallyInner_iff_general n z).trans (badPlane_level_descent_full N n z)

end TernaryPeriodPolynomials.Argument.SeedC3S4c
