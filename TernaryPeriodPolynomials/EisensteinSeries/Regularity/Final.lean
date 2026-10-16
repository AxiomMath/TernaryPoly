module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.LiftModel
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.LevelFinite
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Assembly

@[expose] public section


/-!
# The holomorphic model of the lifts, unconditionally

`liftLevelFinite` discharges the finite-dimensionality hypothesis of `liftModel`, so every set `S`
of weight-`k` cusp forms on `Γ₁(3)` has a finite-adelic model `lifts S : FiniteModel k` realizing
each adelic lift `adelicLift f`, `f ∈ S`. For `k ≥ 6` the holomorphic model `bergmanRep (lifts S)`
carries the realization `realization (lifts S) hk`, and the lower lowest weight vector of the
vector realizing `adelicLift f` realizes to `reproConst k • adelicLift f`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
open TernaryPeriodPolynomials.Automorphic.SubRepresentation
open TernaryPeriodPolynomials.CuspIntegral
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (binaryRealGammaOneThree)

namespace TernaryPeriodPolynomials.Regularity

variable {k : ℕ} (S : Set (CuspForm binaryRealGammaOneThree (k : ℤ)))

/-- The finite-adelic model of the lifts of the cusp forms in `S`. -/
def lifts : FiniteModel k :=
  liftModel S (liftLevelFinite S)

/-- Every adelic lift of a cusp form in `S` is realized by a smooth vector of `lifts S`. -/
theorem lifts_ε_lift {f : CuspForm binaryRealGammaOneThree (k : ℤ)} (hf : f ∈ S) :
    ∃ e, (lifts S).ε e = adelicLift f :=
  liftModel_ε_lift S (liftLevelFinite S) hf

/-- The realization of the holomorphic model of the lifts (`k ≥ 6`). -/
def liftsRealization (hk : 6 ≤ k) :
    Realization (bergmanRep (lifts S)) (bergmanRep_unitary (lifts S)) :=
  realization (lifts S) hk

end TernaryPeriodPolynomials.Regularity

end
