module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceFinite

@[expose] public section


/-!
# The plane source at the identity adele

At the identity adele the finite factors `cF` and `bF` disappear (the finite plane vector of an
integral element is the vector itself), so the plane source is the difference of the radicals of the
Iwasawa factors of the vertices applied to the difference of the Levi cocycles of the `GL₂` blocks:

`planeSource y 1 = (l(b(y₂)) - l(b(y₁))) (α(A(y₁)) 1 - α(A(y₀)) 1)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

section Identity

variable {n : ℕ}

theorem realGroup_one_adelic : realGroup (1 : AdelicGL) = 1 := map_one _

theorem finiteGroup_one_adelic : finiteGroup (1 : AdelicGL) = 1 := map_one _

theorem cF_one (D : InducingData n) : cF D 1 = cFin D 1 := by
  unfold cF
  rw [finiteGroup_one_adelic]

theorem bF_one : bF 1 = bFin 1 := by
  unfold bF
  rw [finiteGroup_one_adelic]

/-- At the identity finite adele the finite twist is trivial. -/
theorem twist_one (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFin D 1 • E.α h (x * bFin 1) = E.α h x := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  have hfpv : finitePlaneVector D.cusp D.chi 0 (((n : ℂ) + 3) / 2) (1 : FiniteGL)
      (E.lift ν h).val = (E.lift ν h).val := by
    have := finitePlaneVector_integral D.chi 0 (((n : ℂ) + 3) / 2) hχ (E.spherical ν h)
      (1 : GeneralLinearGroup (Fin 3) IntegralAdeles)
    rwa [map_one] at this
  rw [twist_coeff D E 1 h x ν, hfpv, rz_lift]

/-- **The plane source at the identity adele.** -/
theorem planeSourceAt_one (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    planeSourceAt D E y 1 x =
      (planeRadical n D.chi (iwP (y 2)) - planeRadical n D.chi (iwP (y 1)))
        (E.α (iwA (y 1)) x - E.α (iwA (y 0)) x) := by
  unfold planeSourceAt
  rw [cF_one, bF_one, realGroup_one_adelic, smul_sub, twist_one D E hχ, twist_one D E hχ]
  simp only [_root_.inv_one, one_mul, map_one, Module.End.one_apply]

/-- **The plane source at the identity adele and rational vertices**, as it enters the evaluation
`Evaluates` of a source cocycle at the trivial flag. -/
theorem planeSource_rational_identity (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (x : Fin 3 → RationalGL3) :
    planeSource D E (fun i => GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (1 : RationalGL3)⁻¹) =
      (planeRadical n D.chi (iwP (GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 2))) -
          planeRadical n D.chi (iwP (GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 1))))
        (E.α (iwA (GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 1))) 1 -
          E.α (iwA (GeneralLinearGroup.map (algebraMap ℚ ℝ) (x 0))) 1) := by
  rw [_root_.inv_one, map_one]
  exact planeSourceAt_one D E hχ _ 1

end Identity

end TernaryPeriodPolynomials.SourceConstruction
