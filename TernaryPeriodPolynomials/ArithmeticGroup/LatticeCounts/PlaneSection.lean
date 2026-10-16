module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REVector

@[expose] public section


/-!
# The plane section at an arbitrary plane-parabolic decomposition (part 3)

For `g = p * ι(k)` with `p` in the upper plane parabolic and `k` integral, and a character trivial on the
integral units (`hχ`), the plane-induced vector at `g` is the determinant weight of the `GL₂` block of `p`
times the translate of the spherical vector by that block.  The corner factor `χ(p₂₂)` is trivial by
class number one (`character_finite_eq_one`), so no further normalization enters.

Formalized by Claude Haiku 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry (character_finite_eq_one normPower_zero')

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection

variable {σ : CuspidalRepresentation}

/-- **The plane section at a decomposed element.** -/
theorem finitePlaneVector_eq_block (χ : RankOneCharacter) (b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ) {g p : FiniteGL} (hp : p ∈ planeParabolic FiniteAdeles)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (hg : g = p * GeneralLinearGroup.map integralEmbedding k) :
    finitePlaneVector σ χ 0 b g vec =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (planeBlockGL p hp))) b •
        σ.π (atFinite (planeBlockGL p hp)) vec := by
  rw [finitePlaneVector_eq χ 0 b hχ hsph hp k hg]
  have hχ' := character_finite_eq_one χ hχ
  unfold finitePlaneFactor
  rw [hχ', normPower_zero', one_mul, one_mul]

end TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection

end
