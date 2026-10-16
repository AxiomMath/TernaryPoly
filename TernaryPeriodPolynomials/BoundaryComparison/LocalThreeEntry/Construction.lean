module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.LocalThreeEntry

@[expose] public section


/-! This is a direct restatement of the existing library proof
`TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.local_three_bad_plane_entry`, which
already discharges `GeneralEisenstein.LocalBadPlaneEntry` unconditionally. -/

open GeneralEisenstein

namespace TernaryPeriodPolynomials.Argument.Classification

theorem local_three_entry : LocalBadPlaneEntry :=
  TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.local_three_bad_plane_entry

end TernaryPeriodPolynomials.Argument.Classification
