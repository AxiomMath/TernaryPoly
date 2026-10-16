module

public import TernaryPeriodPolynomials.BoundaryComparison.EntryDictionary.Dictionary
public import TernaryPeriodPolynomials.BoundaryComparison.EntryDictionary.FaceOrientation

@[expose] public section


/-!
# The orientation/normalization dictionary of the Appendix C entries

Formalized by Claude Sonnet 5.5.

**(i) Plane/line scalars.**  `entry_dictionary`: for the finite spherical datum `S` of a level-one eigenform and the Eichler input `I`
of the same weight and vector, and any `T` realizing the standard operator, the paper's bad-plane section equals `λ_pl = 1` times the
library's `ι_{PK₁} · planeSource`, the paper's good-line section (line seed `σ_h` built from the SAME `h`) equals `λ_li = -1`
times the library's `goodLineWeight · lineSource`, and `(λ_pl / λ_li) · entryScalar n r_print = printedScalar
= -2πi/(9(n+1)) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` (`eq:globalentry`).  The sign is the datum sign `(-1)^{n+1}` versus `(-1)ⁿ`
(`datum_sign`), a normalization of the library's line source ("Changing orientation or period normalization rescales this
nonzero entry"); `scalar_covariance` is the general convention statement.  The finite factor `1/9` and the Euler factors carry no sign
(`rBad_eq_rPrint`, `printedScalar_frozen`), `c_∞ = -2πi/(n+1)` is the quotient of the real entry by the line seed value
(`real_entry_ratio`).

**(ii) Face orientations.**  `face_orientation_dictionary`: with the glue constants `(c, -c)` of `facePairing_glue` the oriented model
pairings `c⁻¹ ⟨ , ⟩_Q`, `(-c)⁻¹ ⟨ , ⟩_P` satisfy the paper's Stokes relation (`oriented_stokes`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.EntryDictionary

open TernaryPeriodPolynomials.Argument

alias lamPl := EntryDictionary.lamPl
alias lamLi := EntryDictionary.lamLi
alias datum_sign := EntryDictionary.datum_sign
alias scalar_covariance := EntryDictionary.scalar_covariance
alias entry_dictionary := EntryDictionary.entry_dictionary
alias oriented_stokes := EntryDictionary.oriented_stokes
alias face_orientation_dictionary := EntryDictionary.face_orientation_dictionary

/-- The real entry `c_∞ = -2πi/(n+1)` as the quotient of the real intertwining integral of the plane seed by the line seed value. -/
alias real_entry_ratio := TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization.real_entry_ratio

/-- `entryScalar n r = -(r c_∞)`. -/
alias entryScalar_eq_neg := ConvergentEisenstein.Entry.entryScalar_eq_neg

/-- `entryScalar n r_print = -printedScalar`. -/
alias entryScalar_rPrint := ConvergentEisenstein.Entry.SphericalEntryData.entryScalar_rPrint

/-- The printed scalar in the paper's form, with the `L^{(3)}` ratio. -/
alias printedScalar_frozen := ConvergentEisenstein.Entry.SphericalEntryData.printedScalar_frozen

end TernaryPeriodPolynomials.Argument.Statements.EntryDictionary
