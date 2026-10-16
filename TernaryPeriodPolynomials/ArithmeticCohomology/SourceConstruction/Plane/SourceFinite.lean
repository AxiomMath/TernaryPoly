module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceData

@[expose] public section


/-!
# The finite law of the plane source

The coefficients of `cF g • α h (x * bF g)` are realizations of the spherical finite plane vector
`finitePlaneVector (g_f) (lift ν h)`. Left equivariance under the finite plane parabolic and right
invariance under the finite level of the finite plane vector therefore give the finite
transformation laws of the plane source.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## The realization of an arbitrary vector -/

open Classical in
/-- The realization of a vector of the Hilbert space, zero off the smooth vectors. -/
def rz (σ : CuspidalRepresentation) (w : σ.H) (x : BinaryAdelicGL) : ℂ :=
  if h : w ∈ σ.smooth then σ.realize ⟨w, h⟩ x else 0

section Rz

variable {σ : CuspidalRepresentation}

theorem rz_of_mem {w : σ.H} (hw : w ∈ σ.smooth) (x : BinaryAdelicGL) :
    rz σ w x = σ.realize ⟨w, hw⟩ x := by
  unfold rz
  rw [dite_eq_left hw]

theorem rz_pi {w : σ.H} (hw : w ∈ σ.smooth) (g x : BinaryAdelicGL) :
    rz σ (σ.π g w) x = rz σ w (x * g) := by
  rw [rz_of_mem (σ.smooth_stable g w hw), rz_of_mem hw]
  exact σ.equivariant g ⟨w, hw⟩ x

theorem rz_smul {w : σ.H} (hw : w ∈ σ.smooth) (c : ℂ) (x : BinaryAdelicGL) :
    rz σ (c • w) x = c * rz σ w x := by
  rw [rz_of_mem (σ.smooth.smul_mem c hw), rz_of_mem hw]
  have h : (⟨c • w, σ.smooth.smul_mem c hw⟩ : σ.smooth) = c • (⟨w, hw⟩ : σ.smooth) :=
    Subtype.ext rfl
  rw [h, map_smul, Pi.smul_apply, smul_eq_mul]

theorem rz_sub {w w' : σ.H} (hw : w ∈ σ.smooth) (hw' : w' ∈ σ.smooth) (x : BinaryAdelicGL) :
    rz σ (w - w') x = rz σ w x - rz σ w' x := by
  rw [rz_of_mem (σ.smooth.sub_mem hw hw'), rz_of_mem hw, rz_of_mem hw']
  have h : (⟨w - w', σ.smooth.sub_mem hw hw'⟩ : σ.smooth) = ⟨w, hw⟩ - ⟨w', hw'⟩ :=
    Subtype.ext rfl
  rw [h, map_sub, Pi.sub_apply]

theorem rz_finitePlaneVector (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) {v : σ.H}
    (hv : v ∈ σ.smooth) (x : BinaryAdelicGL) :
    rz σ (finitePlaneVector σ χ a b g v) x =
      finitePlaneFactor χ a b (finitePlaneParabolic g) (finitePlaneParabolic_mem g) *
        rz σ v (x * atFinite (planeBlockGL (finitePlaneParabolic g) (finitePlaneParabolic_mem g))) := by
  unfold finitePlaneVector
  rw [rz_smul (σ.smooth_stable _ _ hv), rz_pi hv]

end Rz

/-! ## The finite twist -/

section Twist

variable {n : ℕ}

theorem rz_cFin (D : InducingData n) (f : FiniteGL) {v : D.cusp.H} (hv : v ∈ D.cusp.smooth)
    (x : BinaryAdelicGL) :
    rz D.cusp (finitePlaneVector D.cusp D.chi 0 (((n : ℂ) + 3) / 2) f v) x =
      cFin D f * rz D.cusp v (x * bFin f) :=
  rz_finitePlaneVector D.chi 0 (((n : ℂ) + 3) / 2) f hv x

theorem rz_lift {σ : CuspidalRepresentation} (E : LeviCocycleData σ n) (ν : Fin 2 →₀ ℕ)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    rz σ (E.lift ν h).val x = (E.α h x).val.coeff ν := by
  rw [rz_of_mem (E.lift ν h).property]
  exact E.lift_realize ν h x

theorem twist_coeff (D : InducingData n) (E : LeviCocycleData D.cusp n) (f : FiniteGL)
    (h : BinaryRealGL) (x : BinaryAdelicGL) (ν : Fin 2 →₀ ℕ) :
    cFin D f * (E.α h (x * bFin f)).val.coeff ν =
      rz D.cusp (finitePlaneVector D.cusp D.chi 0 (((n : ℂ) + 3) / 2) f (E.lift ν h).val) x := by
  rw [rz_cFin D f (E.lift ν h).property, rz_lift]

/-- **Left equivariance of the finite twist** under the finite plane parabolic. -/
theorem twist_left (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (f f' fp : FiniteGL) (hfp : fp ∈ planeParabolic FiniteAdeles) (hf' : f' = fp * f)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFin D f' • E.α h (x * bFin f') =
      finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) fp hfp •
        (cFin D f • E.α h (x * atFinite (planeBlockGL fp hfp) * bFin f)) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  have hv : (E.lift ν h).val ∈ D.cusp.smooth := (E.lift ν h).property
  have hvf := finitePlaneVector_smooth (σ := D.cusp) D.chi 0 (((n : ℂ) + 3) / 2) f hv
  have e1 := twist_coeff D E f' h x ν
  have e2 := twist_coeff D E f h (x * atFinite (planeBlockGL fp hfp)) ν
  have e3 : rz D.cusp (finitePlaneVector D.cusp D.chi 0 (((n : ℂ) + 3) / 2) f' (E.lift ν h).val) x =
      finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) fp hfp *
        rz D.cusp (finitePlaneVector D.cusp D.chi 0 (((n : ℂ) + 3) / 2) f (E.lift ν h).val)
          (x * atFinite (planeBlockGL fp hfp)) := by
    rw [hf', finitePlaneVector_mul D.chi 0 (((n : ℂ) + 3) / 2) hχ (E.spherical ν h) hfp f,
      rz_smul (D.cusp.smooth_stable _ _ hvf), rz_pi hvf]
  rw [e1, e2, e3]

/-- **Right invariance of the finite twist** under the finite level. -/
theorem twist_level (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (f : FiniteGL) (k : finiteLevel) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFin D (f * k.val) • E.α h (x * bFin (f * k.val)) = cFin D f • E.α h (x * bFin f) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [twist_coeff D E (f * k.val) h x ν, twist_coeff D E f h x ν,
    finitePlaneVector_mul_level D.chi 0 (((n : ℂ) + 3) / 2) hχ (E.spherical ν h) f k]

end Twist

/-! ## Real and finite parts of products -/

theorem finiteGroup_mul_atInfinity (g : AdelicGL) (z : RealGL3) :
    finiteGroup (g * atInfinity z) = finiteGroup g := by
  rw [map_mul, finiteGroup_eq_finitePart (atInfinity z), finitePart_atInfinity, mul_one]

theorem realGroup_mul_atInfinity (g : AdelicGL) (z : RealGL3) :
    realGroup (g * atInfinity z) = realGroup g * z := by
  rw [map_mul, realGroup_eq_realPart (atInfinity z), realPart_atInfinity]

theorem realGroup_mul_atFinite (g : AdelicGL) (f : FiniteGL) :
    realGroup (g * atFinite f) = realGroup g := by
  rw [map_mul, realGroup_eq_realPart (atFinite f), realPart_atFinite, mul_one]

theorem finiteGroup_mul_atFinite (g : AdelicGL) (f : FiniteGL) :
    finiteGroup (g * atFinite f) = finiteGroup g * f := by
  rw [map_mul, finiteGroup_eq_finitePart (atFinite f), finitePart_atFinite]

end TernaryPeriodPolynomials.SourceConstruction
