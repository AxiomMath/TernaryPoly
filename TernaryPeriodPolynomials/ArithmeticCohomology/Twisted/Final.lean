module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Sign
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly

@[expose] public section


/-!
# Level-one local multiplicity one for the odd quadratic character of conductor three

For `χ ≠ trivialCharacter` with `ConductorThree χ` (so `χ(-1_∞) = -1`), `3 ≤ n` and a nonzero
associate pair, the pair character has local multiplicity one at the identity plane and at the
good line (`levelOneLocalMultiplicityOne_of_conductorThree`).  The proof carries the trivial
character chain over to the sign-twisted coefficient system:

* `Sign.lean`: `χ(sAd 2) = -1`, hence `‖c(T₂) + 1‖ ≤ 3/4` for the pair character;
* `PlaneBound.lean`, `LineBound.lean`: `dim localJoint ≤ 1` at the two level-one cusps for every
  character `c` of the away-three Hecke algebra with `‖c(T₂) + 1‖ ≤ 3/4`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.Twisted

variable {n : ℕ}

/-- **Level-one local multiplicity one for a nontrivial character of conductor dividing three.** -/
theorem levelOneLocalMultiplicityOne_of_conductorThree (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi ≠ trivialCharacter) (h3 : LevelOneNontrivial.ConductorThree D.chi) :
    LevelOneLocalMultiplicityOne D hecke hhecke := by
  intro hne
  have hneg := LevelOneNontrivial.chi_realNegOne_eq_neg_one hχ h3
  have hc := pairCharacter_two_add_one_norm_le D h3 hneg hecke hhecke hn hne
  exact ⟨localMultiplicityOne_of_localUpperBound_one D.chi _ .plane false
      (localJoint_identityPlane_twisted_finite_le_one (by omega) D.chi hneg _ hc),
    localMultiplicityOne_of_localUpperBound_one D.chi _ .line true
      (localJoint_goodLine_twisted_finite_le_one (by omega) D.chi hneg _ hc)⟩

end TernaryPeriodPolynomials.Twisted
