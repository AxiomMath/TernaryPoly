module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceFinite
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceAlgebra

@[expose] public section


/-!
# The line source at an integral finite adele

At an adele whose finite part is integral the finite factors `cFLine` and `bFLine` disappear (the
finite line vector of an integral element is the vector itself), so the line source is the
difference of the radicals of the Iwasawa factors of the vertices applied to the difference of the
Levi cocycles of the `GL₂` blocks:

`lineSource y g = ρ(g_∞)⁻¹ ((l(b(g_∞ y₂)) - l(b(g_∞ y₁))) (α(A(g_∞ y₁)) 1 - α(A(g_∞ y₀)) 1))`.

This applies at the good-line point `rationalGroup (rational referenceIntegral)⁻¹`, whose finite part
is the integral matrix `(goodLineFrame ℤ̂)⁻¹`, and in particular at rational vertices.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit (referenceIntegral)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

namespace TernaryPeriodPolynomials.SourceConstruction

section Identity

variable {n : ℕ}

/-- **The line source at an adele with integral finite part.** -/
theorem lineSourceAt_integral (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g : AdelicGL) (k : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (hk : finiteGroup g = GeneralLinearGroup.map integralEmbedding k)
    (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    lineSourceAt D E y g x =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        ((lineRadical n D.chi (iwPLine (realGroup g * y 2)) -
            lineRadical n D.chi (iwPLine (realGroup g * y 1)))
          (E.α (iwALine (realGroup g * y 1)) x - E.α (iwALine (realGroup g * y 0)) x)) := by
  unfold lineSourceAt cFLine bFLine
  rw [hk, smul_sub, twistLine_integral D E hχ k, twistLine_integral D E hχ k]

/-- The finite part of the good-line point is an integral matrix. -/
theorem finiteGroup_goodLinePoint :
    ∃ k : GeneralLinearGroup (Fin 3) IntegralAdeles,
      finiteGroup (rationalGroup (rational referenceIntegral)⁻¹) =
        GeneralLinearGroup.map integralEmbedding k :=
  ⟨_, (finiteGroup_rational _).trans rationalFinite_goodLine_inv⟩

theorem realGroup_goodLinePoint :
    realGroup (rationalGroup (rational referenceIntegral)⁻¹) =
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (rational referenceIntegral))⁻¹ := by
  rw [realGroup_rationalGroup, _root_.map_inv]

/-- **The line source at the good-line point and rational vertices**, as it enters the evaluation
`Evaluates` of a source cocycle at the good-line flag. -/
theorem lineSource_rational_goodLine (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (x : Fin 3 → RationalGL3) :
    lineSource D E (fun i => GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (rational referenceIntegral)⁻¹) =
      realCoefficientComponent n D.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (rational referenceIntegral))
        ((lineRadical n D.chi
              (iwPLine ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (rational referenceIntegral))⁻¹ *
                GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 2))) -
            lineRadical n D.chi
              (iwPLine ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (rational referenceIntegral))⁻¹ *
                GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 1))))
          (E.α (iwALine ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (rational referenceIntegral))⁻¹ *
              GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 1))) 1 -
            E.α (iwALine ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (rational referenceIntegral))⁻¹ *
              GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 0))) 1)) := by
  obtain ⟨k, hk⟩ := finiteGroup_goodLinePoint
  unfold lineSource
  rw [lineSourceAt_integral D E hχ _ k hk, realGroup_goodLinePoint, _root_.inv_inv]

end Identity

end TernaryPeriodPolynomials.SourceConstruction

end
