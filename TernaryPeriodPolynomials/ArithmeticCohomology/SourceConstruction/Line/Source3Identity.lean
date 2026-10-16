module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationLine

@[expose] public section


/-!
# The level-three line source at the identity adele (the bad-line cusp point)

The bad-line cusp point is `rationalGroup (lineCuspElement false)⁻¹ = 1`, whose finite part is the
identity.  The identity-cell finite vector takes the value `v` at the identity
(`badLineVector_one`), so the finite factors `cFin3, bFin3` disappear at any adele with trivial
finite part and the level-three line source is the difference of the radicals of the Iwasawa factors
of the vertices applied to the difference of the Levi cocycles of the `GL₂` blocks.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.Separation (lineCuspElement)

namespace TernaryPeriodPolynomials.SourceConstruction

section Identity3

variable {n : ℕ}

/-- **The level-three line source at an adele with trivial finite part.** -/
theorem lineSourceAt3_of_finiteGroup_one (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g : AdelicGL) (hg : finiteGroup g = 1) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    lineSourceAt3 D E y g x =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        ((lineRadical n D.chi (iwPLine (realGroup g * y 2)) -
            lineRadical n D.chi (iwPLine (realGroup g * y 1)))
          (E.α (iwALine (realGroup g * y 1)) x - E.α (iwALine (realGroup g * y 0)) x)) := by
  unfold lineSourceAt3 cFLine3 bFLine3
  rw [hg, smul_sub, twist3_one D E hχ, twist3_one D E hχ]

/-- **The level-three line source at the identity adele.** -/
theorem lineSource3_identity (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (y : Fin 3 → RealGL3) :
    lineSource3 D E y 1 =
      (lineRadical n D.chi (iwPLine (y 2)) - lineRadical n D.chi (iwPLine (y 1)))
        (E.α (iwALine (y 1)) 1 - E.α (iwALine (y 0)) 1) := by
  unfold lineSource3
  rw [lineSourceAt3_of_finiteGroup_one D E hχ 1 (map_one _) y 1]
  simp only [map_one, inv_one, one_mul, Module.End.one_apply]

/-- The bad-line cusp point is the identity adele. -/
theorem rationalGroup_lineCuspElement_false : rationalGroup (lineCuspElement false)⁻¹ = 1 := by
  simp [lineCuspElement]

/-- **The level-three line source at the bad-line cusp point and rational vertices**, as it
enters the evaluation `Evaluates` of a source cocycle at the bad-line flag. -/
theorem lineSource3_rational_identity (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (x : Fin 3 → RationalGL3) :
    lineSource3 D E (fun i => GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (lineCuspElement false)⁻¹) =
      (lineRadical n D.chi (iwPLine (GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 2))) -
          lineRadical n D.chi (iwPLine (GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 1))))
        (E.α (iwALine (GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 1))) 1 -
          E.α (iwALine (GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 0))) 1) := by
  rw [rationalGroup_lineCuspElement_false]
  exact lineSource3_identity D E hχ _

end Identity3

end TernaryPeriodPolynomials.SourceConstruction

end
