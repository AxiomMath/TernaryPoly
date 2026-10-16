module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Norms

@[expose] public section


/-!
# The away-from-three value of a Hecke character through its three-adic component

For a positive rational unit `q`, automorphy (`rational`) and triviality on the positive reals
(`positiveReal`) of a rank-one character `χ` give
`χ(sAd q) · χ(threeUnit q) = 1`, i.e. the away-from-three value is determined by the
three-adic component.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

theorem chi_sAd_mul_three (χ : RankOneCharacter) {q : ℚˣ} (hq : 0 < (q : ℚ)) :
    χ.toMonoidHom (sAd q) *
        χ.toMonoidHom (SphericalDetection.Helpers.finiteAdeleUnit (threeUnit q)) = 1 := by
  have h := χ.rational q
  rw [rational_split, map_mul, unitF_split, finiteAdeleUnit_mul, map_mul,
    χ.positiveReal _ (by simpa [Units.coe_map] using hq), one_mul] at h
  exact h

theorem chi_sAd_eq_inv_three (χ : RankOneCharacter) {q : ℚˣ} (hq : 0 < (q : ℚ)) :
    χ.toMonoidHom (sAd q) =
        (χ.toMonoidHom (SphericalDetection.Helpers.finiteAdeleUnit (threeUnit q)))⁻¹ :=
  eq_inv_of_mul_eq_one_left (chi_sAd_mul_three χ hq)

end TernaryPeriodPolynomials.HeckeEigen.Satake
