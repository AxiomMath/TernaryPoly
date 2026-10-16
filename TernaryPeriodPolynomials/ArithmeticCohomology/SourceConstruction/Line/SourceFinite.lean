module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceData
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceFinite

@[expose] public section


/-!
# The finite law of the line source

The coefficients of `cFLine g • α h (x * bFLine g)` are realizations of the spherical finite line
vector `finiteLineVector (g_f) (lift ν h)`.  Left equivariance under the finite line parabolic and
right invariance under the finite level of the finite line vector therefore give the finite
transformation laws of the line source.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## The realization of the finite line vector -/

section Rz

variable {σ : CuspidalRepresentation}

theorem rz_finiteLineVector (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) {v : σ.H}
    (hv : v ∈ σ.smooth) (x : BinaryAdelicGL) :
    rz σ (finiteLineVector σ χ a b g v) x =
      finiteLineFactor χ a b (finiteLineParabolic g) (finiteLineParabolic_mem g) *
        rz σ v (x * atFinite (lineBlockGL (finiteLineParabolic g) (finiteLineParabolic_mem g))) := by
  unfold finiteLineVector
  rw [rz_smul (σ.smooth_stable _ _ hv), rz_pi hv]

end Rz

/-! ## The finite twist -/

section Twist

variable {n : ℕ}

theorem rz_cFinLine (D : InducingData n) (f : FiniteGL) {v : D.cusp.H} (hv : v ∈ D.cusp.smooth)
    (x : BinaryAdelicGL) :
    rz D.cusp (finiteLineVector D.cusp D.chi 2 (lineBeta n) f v) x =
      cFinLine D f * rz D.cusp v (x * bFinLine f) :=
  rz_finiteLineVector D.chi 2 (lineBeta n) f hv x

theorem rz_liftLine {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n) (ν : Fin 2 →₀ ℕ)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    rz σ (E.lift ν h).val x = (E.α h x).val.coeff ν := by
  rw [rz_of_mem (E.lift ν h).property]
  exact E.lift_realize ν h x

theorem twistLine_coeff (D : InducingData n) (E : LineLeviCocycleData D.cusp n) (f : FiniteGL)
    (h : BinaryRealGL) (x : BinaryAdelicGL) (ν : Fin 2 →₀ ℕ) :
    cFinLine D f * (E.α h (x * bFinLine f)).val.coeff ν =
      rz D.cusp (finiteLineVector D.cusp D.chi 2 (lineBeta n) f (E.lift ν h).val) x := by
  rw [rz_cFinLine D f (E.lift ν h).property, rz_liftLine]

/-- **Left equivariance of the finite twist** under the finite line parabolic. -/
theorem twistLine_left (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (f f' fp : FiniteGL) (hfp : fp ∈ lineParabolic FiniteAdeles) (hf' : f' = fp * f)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFinLine D f' • E.α h (x * bFinLine f') =
      finiteLineFactor D.chi 2 (lineBeta n) fp hfp •
        (cFinLine D f • E.α h (x * atFinite (lineBlockGL fp hfp) * bFinLine f)) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  have hv : (E.lift ν h).val ∈ D.cusp.smooth := (E.lift ν h).property
  have hvf := finiteLineVector_smooth (σ := D.cusp) D.chi 2 (lineBeta n) f hv
  have e1 := twistLine_coeff D E f' h x ν
  have e2 := twistLine_coeff D E f h (x * atFinite (lineBlockGL fp hfp)) ν
  have e3 : rz D.cusp (finiteLineVector D.cusp D.chi 2 (lineBeta n) f' (E.lift ν h).val) x =
      finiteLineFactor D.chi 2 (lineBeta n) fp hfp *
        rz D.cusp (finiteLineVector D.cusp D.chi 2 (lineBeta n) f (E.lift ν h).val)
          (x * atFinite (lineBlockGL fp hfp)) := by
    rw [hf', finiteLineVector_mul D.chi 2 (lineBeta n) hχ (E.spherical ν h) hfp f,
      rz_smul (D.cusp.smooth_stable _ _ hvf), rz_pi hvf]
  rw [e1, e2, e3]

/-- **Right invariance of the finite twist** under the finite level. -/
theorem twistLine_level (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (f : FiniteGL) (k : finiteLevel) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFinLine D (f * k.val) • E.α h (x * bFinLine (f * k.val)) =
      cFinLine D f • E.α h (x * bFinLine f) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [twistLine_coeff D E (f * k.val) h x ν, twistLine_coeff D E f h x ν,
    finiteLineVector_mul_level D.chi 2 (lineBeta n) hχ (E.spherical ν h) f k]

/-- **The finite twist at an integral point is trivial.** -/
theorem twistLine_integral (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFinLine D (GeneralLinearGroup.map integralEmbedding k) •
        E.α h (x * bFinLine (GeneralLinearGroup.map integralEmbedding k)) = E.α h x := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [twistLine_coeff D E _ h x ν,
    finiteLineVector_integral D.chi 2 (lineBeta n) hχ (E.spherical ν h) k, rz_liftLine]

end Twist

end TernaryPeriodPolynomials.SourceConstruction

end
