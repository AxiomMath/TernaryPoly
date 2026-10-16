module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.AnalyticHecke

@[expose] public section


/-!
# The analytic period Hecke dictionary

Export of `TernaryPeriodPolynomials.Argument.FiberModel.AnalyticHecke`.  Paper
the paper, Appendix A.3, after the proof of
`eq:Hecke-formula`: "It remains to check that this binary correspondence has the standard analytic
Hecke normalization on period polynomials. Put `d = n+1`, and let `h` be a cusp form of weight `d+2`.
For a matrix `g = (a b; c e)` of positive determinant `m`, the fractional-linear action gives
`((gzY-X) | g) = m(zY-X)/(cz+e)`, `d(gz) = m dz/(cz+e)^2`. Hence the differential `h(z)(zY-X)^d dz`
transforms with the usual weight `d+2` Hecke factor. The homological correspondence above is the
standard Hecke operator on the period polynomial of `h`."

Clause by clause:

* "`((gzY-X) | g) = m(zY-X)/(cz+e)`": `mobius_linear`.
* "`d(gz) = m dz/(cz+e)^2`": `mobius_hasDerivAt`.
* "the differential `h(z)(zY-X)^d dz` transforms with the usual weight `d+2` Hecke factor":
  `slash_differential` (Mathlib's weight `d+2` slash action) and `periodIntegrand_hecke_sum` (the
  differential of the standard operator `T_p` is the sum of the transported differentials of `h`
  over the `p+1` representatives).
* "the homological correspondence is the standard Hecke operator on the period polynomial of `h`":
  NOT established here. `hecke_dictionary_cusp`, `hecke_dictionary_cusp_of_period` are statements
  about the library's exponent-`+1` Hom-model operator on modular symbols of the binary Steinberg
  module: `p^d · res_H(T₃(p,1) F) = p² · φ_{T_p f} + p^{d+2} · φ_f` for that model operator, under the
  visible hypothesis identifying the residue symbol with `oddHom f`; equivalently, in that model,
  `T₂^{(+1)}(p) = p^{1-d} T_p`. That Hom-model operator has NOT been identified with the
  paper's homology correspondence (the H₃→Hom/period comparison, transpose and coefficient
  transport at rational prime correspondences are not established: `HomologyHomBridge` in
  `Proofs/HeckeNormalization/Bridge.lean`), so these results neither prove nor refute the printed
  sentence; the paper verdict is UNDETERMINED until that bridge is proved. `T_p` is the
  library's `BinaryCuspHeckeEndomorphism.T`, and `φ_f = oddHom f` is the analytic modular symbol of
  `f` built from the Eichler integral of `f(z)(zy-x)^d dz`.

Scope: level one (all that the residue argument uses: "the odd Eichler-Shimura correspondence
identifies the Hecke action on `B_d ⊗ ℂ` with the usual action on level-one cusp forms").

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.AnalyticPeriodHecke

open TernaryPeriodPolynomials.Argument.FiberModel.AnalyticHecke

export TernaryPeriodPolynomials.Argument.FiberModel.AnalyticHecke
  (mobius_linear mobius_hasDerivAt slash_differential periodIntegrand_hecke_sum
    binary_hecke_twist hecke_dictionary_cusp hecke_dictionary_cusp_of_period)

end TernaryPeriodPolynomials.Argument.Statements.AnalyticPeriodHecke
