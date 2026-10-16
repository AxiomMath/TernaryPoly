module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Data

@[expose] public section


/-!
# The finite law of the level-three line source

The coefficients of `cFin3 f • α h (x * bFin3 f)` are realizations of the identity-cell finite vector
`badLineVector f (lift ν h)`, which vanishes off the cell.  Left equivariance under the finite line
parabolic and right invariance under the finite level of `badLineVector` therefore give the finite
transformation laws of the level-three line source, and `badLineVector_one` its value at the
identity.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

section Twist3

variable {n : ℕ}

theorem rz_zero3 (σ : CuspidalRepresentation) (x : BinaryAdelicGL) : rz σ 0 x = 0 := by
  have h := rz_smul (σ := σ) (σ.smooth.zero_mem) (0 : ℂ) x
  rw [smul_zero, zero_mul] at h
  exact h

theorem rz_lift3 {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n) (ν : Fin 2 →₀ ℕ)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    rz σ (E.lift ν h).val x = (E.α h x).val.coeff ν := by
  rw [rz_of_mem (E.lift ν h).property]
  exact E.lift_realize ν h x

/-- **The coefficients of the finite twist** are realizations of the identity-cell finite vector. -/
theorem twist3_coeff (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n) (f : FiniteGL)
    (h : BinaryRealGL) (x : BinaryAdelicGL) (ν : Fin 2 →₀ ℕ) :
    cFin3 D f * (E.α h (x * bFin3 f)).val.coeff ν =
      rz D.cusp (badLineVector D.cusp D.chi 2 (lineBeta n) f (E.lift ν h).val) x := by
  have hv : (E.lift ν h).val ∈ D.cusp.smooth := (E.lift ν h).property
  by_cases hcell : InBadCell f
  · rw [cFin3_of_cell D hcell, bFin3_of_cell hcell, badLineVector_of_cell hcell,
      badCellValue_of_mem (inBadCell_choose_mem hcell),
      rz_smul (D.cusp.smooth_stable _ _ hv), rz_pi hv, rz_lift3]
  · rw [cFin3_of_not_cell D hcell, zero_mul, badLineVector_of_not_cell hcell, rz_zero3]

/-- **Left equivariance of the finite twist** under the finite line parabolic. -/
theorem twist3_left (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (f f' fp : FiniteGL) (hfp : fp ∈ lineParabolic FiniteAdeles) (hf' : f' = fp * f)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFin3 D f' • E.α h (x * bFin3 f') =
      finiteLineFactor D.chi 2 (lineBeta n) fp hfp •
        (cFin3 D f • E.α h (x * atFinite (lineBlockGL fp hfp) * bFin3 f)) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  have hv : (E.lift ν h).val ∈ D.cusp.smooth := (E.lift ν h).property
  have hvf := badLineVector_smooth (σ := D.cusp) D.chi 2 (lineBeta n) f hv
  have e1 := twist3_coeff D E f' h x ν
  have e2 := twist3_coeff D E f h (x * atFinite (lineBlockGL fp hfp)) ν
  have e3 : rz D.cusp (badLineVector D.cusp D.chi 2 (lineBeta n) f' (E.lift ν h).val) x =
      finiteLineFactor D.chi 2 (lineBeta n) fp hfp *
        rz D.cusp (badLineVector D.cusp D.chi 2 (lineBeta n) f (E.lift ν h).val)
          (x * atFinite (lineBlockGL fp hfp)) := by
    rw [hf', badLineVector_mul D.chi 2 (lineBeta n) hχ (E.levelFixed ν h) hfp f,
      rz_smul (D.cusp.smooth_stable _ _ hvf), rz_pi hvf]
  rw [e1, e2, e3]

/-- **Right invariance of the finite twist** under the finite level. -/
theorem twist3_level (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (f : FiniteGL) (k : finiteLevel) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFin3 D (f * k.val) • E.α h (x * bFin3 (f * k.val)) = cFin3 D f • E.α h (x * bFin3 f) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [twist3_coeff D E (f * k.val) h x ν, twist3_coeff D E f h x ν,
    badLineVector_mul_level D.chi 2 (lineBeta n) hχ (E.levelFixed ν h) f k]

/-- **The finite twist at the identity is trivial.** -/
theorem twist3_one (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFin3 D 1 • E.α h (x * bFin3 1) = E.α h x := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [twist3_coeff D E 1 h x ν,
    badLineVector_one D.chi 2 (lineBeta n) hχ (E.levelFixed ν h), rz_lift3]

/-- The finite translation commutes with real translations. -/
theorem bFin3_comm_atInfinity (f : FiniteGL) (r : BinaryRealGL) :
    bFin3 f * atInfinity r = atInfinity r * bFin3 f := by
  by_cases hcell : InBadCell f
  · rw [bFin3_of_cell hcell]
    exact atFinite_mul_atInfinity_comm _ _
  · rw [bFin3_of_not_cell hcell, one_mul, mul_one]

end Twist3

end TernaryPeriodPolynomials.SourceConstruction

end
