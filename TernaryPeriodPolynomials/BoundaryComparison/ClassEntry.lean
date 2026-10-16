module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.ClassLevelPaper

@[expose] public section


/-!
# The class-level entry comparison for the bad plane and the good line (ML4b/ML5, Appendix C.5)

Exports of `Revision/Proofs/ConvergentEisenstein/Entry/ClassLevel*`.  For the finite spherical datum `S` of the
level-one eigenform `h` (`SphericalEntryData`, `4 ≤ n`), the Eichler input `I` of the same vector, and any map `T`
realizing the standard operator (`RealizesStandardConv`):

* `class_level_badPlane_eichler`: the good-line component of `T[badPlaneWeight · planeSource]` is
  `entryScalar n S.rBad = -S.printedScalar` times that of `goodLineWeight · lineSource` (library line source);
* `class_level_paper`: the same with the paper's line section `σ_h` (`cSigmaPaper`: the line seed with the datum of the
  same sign as the plane seed) and the printed scalar `-2πi/(9(n+1)) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1) ≠ 0` of
  `ar:eq:globalentry`; the library line source is minus the paper's line section (`cSigmaPaper_eq_neg`);
* `class_level_paper_of_spherical`: the same for the actual datum (existence of `S`, `I` from N2's
  `exists_sphericalEntryPackage`).

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.ClassEntry

open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

alias class_level_badPlane_eichler := Entry.classLevel_badPlane_eichler
alias class_level_paper := Entry.classLevel_paper
alias class_level_paper_of_spherical := Entry.classLevel_paper_of_spherical
alias c_sigma_paper_eq_neg := Entry.cSigmaPaper_eq_neg

end TernaryPeriodPolynomials.Argument.Statements.ClassEntry
