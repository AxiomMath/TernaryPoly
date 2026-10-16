module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTLineCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Lift

@[expose] public section


/-!
# The two embeddings of a flag group into the line group agree

Formalized by Claude Sonnet 5.5.

`flagToQ` (`NFTLineCore`) and `flagIota` (`FlagLift`) are both the inverse of `lineEmb h` on the stabilizer of a flag over the line of `h`; `flagToQ_eq_flagIota` identifies them for `F = flagAt h w`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces

theorem flagToQ_eq_flagIota (i : LineFaces 6) (w : Prim2) :
    flagToQ i (flagAt i.rep w) (flagLineOf_flagAt i.rep w) = flagIota i.rep w :=
  MonoidHom.ext fun s => lineEmb_injective i.rep (by rw [lineEmb_flagToQ, lineEmb_flagIota])

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
