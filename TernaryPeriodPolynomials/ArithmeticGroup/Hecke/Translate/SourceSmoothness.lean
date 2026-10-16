/-
  Smoothness (the first `IsInduced` clause of `IsSourceCocycle`) for the
  finite-coset Hecke translate `translateSource`.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HeckeInvariance
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothTransport
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.PolyExpansion
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Homogeneous Matrix MvPolynomial
open scoped Matrix.Norms.Elementwise


noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.SourceSmoothness

/-- The coefficient functional `coeff m` as a linear map `Poly →ₗ ℂ`. -/
def coeffLM (m : Fin 3 →₀ ℕ) : Poly →ₗ[ℂ] ℂ where
  toFun := fun p => p.coeff m
  map_add' := fun a b => rfl
  map_smul' := fun a b => by
    simp only [MvPolynomial.coeff_smul, RingHom.id_apply, smul_eq_mul]

/-- The `m`-th coefficient of a homogeneous polynomial. -/
abbrev coeffVal {n : ℕ} (m : Fin 3 →₀ ℕ) (W : HomogeneousPoly n) : ℂ :=
  W.val.coeff m

/-- **Coefficient expansion of the component representation.** -/
theorem coeff_realCoefficientComponent {n : ℕ} (χ : RankOneCharacter)
    (g₀ : RealGL3) (W : HomogeneousPoly n) (m : Fin 3 →₀ ℕ) :
    ((realCoefficientComponent n χ g₀ W).val).coeff m
      = componentCharacter χ g₀ *
        ∑ d ∈ PolyExpansion.degreeMonomials n,
          W.val.coeff d *
            (action (-1)
              (GeneralLinearGroup.map (algebraMap ℝ ℂ) g₀) (MvPolynomial.monomial d 1)).coeff m := by
  rw [show realCoefficientComponent n χ g₀ W
        = componentCharacter χ g₀ • realCoefficient n g₀ W from rfl]
  rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  congr 1
  rw [show realCoefficient n g₀ W
        = homogeneousAction n (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) g₀) W from rfl,
    homogeneousAction_coe]
  exact PolyExpansion.linear_apply_eq_sum
    ((coeffLM m).comp (action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) g₀))) W

/-! ## Elementary `Smooth` closure lemmas -/

theorem smooth_finset_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin 1 → RealGL3) → ℂ)
    (h : ∀ i ∈ s, Smooth (f i)) :
    Smooth (fun u => ∑ i ∈ s, f i u) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
      ∑ i ∈ s, f i (fun j => invertibleMatrix (A j))) {A | ∀ i, (A i).det ≠ 0}
  exact ContDiffOn.sum (fun i hi => by
    have := h i hi
    show ContDiffOn ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
      f i (fun j => invertibleMatrix (A j))) {A | ∀ i, (A i).det ≠ 0}
    exact this)

theorem smooth_const_mul (c : ℂ) {f : (Fin 1 → RealGL3) → ℂ} (hf : Smooth f) :
    Smooth (fun u => c * f u) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
      c * f (fun j => invertibleMatrix (A j))) {A | ∀ i, (A i).det ≠ 0}
  have := hf
  show ContDiffOn ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
      c * f (fun j => invertibleMatrix (A j))) {A | ∀ i, (A i).det ≠ 0}
  simpa only [smul_eq_mul] using this.const_smul c

theorem smooth_congr {f g : (Fin 1 → RealGL3) → ℂ} (hf : Smooth f)
    (h : ∀ u, g u = f u) : Smooth g := by
  show ContDiffOn ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
      g (fun j => invertibleMatrix (A j))) {A | ∀ i, (A i).det ≠ 0}
  have hf' := hf
  show ContDiffOn ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
      g (fun j => invertibleMatrix (A j))) {A | ∀ i, (A i).det ≠ 0}
  refine hf'.congr (fun A _ => ?_)
  exact h _

/-- The matrix conjugate of `u` is the group conjugate `(map r)⁻¹ · u · (map r)`. -/
theorem invertibleMatrix_conj_eq (r : RationalGL3) (u : RealGL3) :
    invertibleMatrix (((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val * u.val *
        ((((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val)⁻¹))
      = (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * u *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) r := by
  have hG : IsUnit ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r).val.det) :=
    isUnit_iff_ne_zero.mpr (GeneralLinearGroup.det_ne_zero _)
  apply Units.ext
  rw [SmoothTransport.invertibleMatrix_val]
  · rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inv,
      Matrix.nonsing_inv_nonsing_inv _ hG]
  · rw [Matrix.det_mul, Matrix.det_mul, GeneralLinearGroup.coe_inv]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact (Matrix.isUnit_nonsing_inv_det _ hG).ne_zero
    · exact GeneralLinearGroup.det_ne_zero u
    · rw [Matrix.nonsing_inv_nonsing_inv _ hG]
      exact GeneralLinearGroup.det_ne_zero _

/-- Archimedean smoothness of a single source coordinate after the variable
change `u ↦ (map r)⁻¹ · u · (map r)`. -/
theorem smooth_coord_term {n : ℕ} {D : InducingData n} {side : Side}
    {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (r : RationalGL3) (x : Fin 3 → RealGL3) (G : AdelicGL) (d : Fin 3 →₀ ℕ) :
    Smooth (fun u : Fin 1 → RealGL3 => coeffVal d
      (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
        (G * rationalGroup r * atInfinity
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (u 0) *
            GeneralLinearGroup.map (algebraMap ℚ ℝ) r)))) := by
  have hsrc := (hc.1 (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i) d).1
    (G * rationalGroup r)
  have hcomp := SmoothTransport.Smooth.comp_conj
    (F := fun u' : Fin 1 → RealGL3 => coeffVal d
      (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
        ((G * rationalGroup r) * atInfinity (u' 0))))
    hsrc (((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val)
    (GeneralLinearGroup.det_ne_zero _)
  refine smooth_congr hcomp (fun u => ?_)
  have h0 : (fun i : Fin 1 => invertibleMatrix
      ((((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val) * (u i).val *
        ((((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val)⁻¹)))
      = (fun i : Fin 1 => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (u i) *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) r) := by
    funext i; exact invertibleMatrix_conj_eq r (u i)
  rw [h0]

/-- Smoothness of a single Hecke representative term of the translate. -/
theorem smooth_representative_term {n : ℕ} {D : InducingData n} {side : Side}
    {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (r : RationalGL3) (x : Fin 3 → RealGL3) (G : AdelicGL) (m : Fin 3 →₀ ℕ) :
    Smooth (fun u : Fin 1 → RealGL3 => coeffVal m
      (realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
        (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
          (G * rationalGroup r * atInfinity
            ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (u 0) *
              GeneralLinearGroup.map (algebraMap ℚ ℝ) r))))) := by
  have hfun : (fun u : Fin 1 → RealGL3 => coeffVal m
        (realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
          (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
            (G * rationalGroup r * atInfinity
              ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (u 0) *
                GeneralLinearGroup.map (algebraMap ℚ ℝ) r)))))
      = fun u => ∑ d ∈ PolyExpansion.degreeMonomials n,
          componentCharacter D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) *
            (coeffVal d
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (G * rationalGroup r * atInfinity
                  ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (u 0) *
                    GeneralLinearGroup.map (algebraMap ℚ ℝ) r))) *
            (action (-1)
              (GeneralLinearGroup.map (algebraMap ℝ ℂ)
                (GeneralLinearGroup.map (algebraMap ℚ ℝ) r))
              (MvPolynomial.monomial d 1)).coeff m) := by
    funext u
    rw [show coeffVal m
        (realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
          (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
            (G * rationalGroup r * atInfinity
              ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (u 0) *
                GeneralLinearGroup.map (algebraMap ℚ ℝ) r))))
        = componentCharacter D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) *
          ∑ d ∈ PolyExpansion.degreeMonomials n,
            coeffVal d
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (G * rationalGroup r * atInfinity
                  ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (u 0) *
                    GeneralLinearGroup.map (algebraMap ℚ ℝ) r))) *
            (action (-1)
              (GeneralLinearGroup.map (algebraMap ℝ ℂ)
                (GeneralLinearGroup.map (algebraMap ℚ ℝ) r))
              (MvPolynomial.monomial d 1)).coeff m
        from coeff_realCoefficientComponent D.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) _ m]
    rw [Finset.mul_sum]
  rw [hfun]
  apply smooth_finset_sum
  intro d hd
  refine smooth_congr (smooth_const_mul
    (componentCharacter D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) *
      (action (-1)
        (GeneralLinearGroup.map (algebraMap ℝ ℂ)
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)) (MvPolynomial.monomial d 1)).coeff m)
    (smooth_coord_term hc r x G d)) (fun u => ?_)
  ring

/-- **The archimedean smoothness clause for `translateSource`.** -/
theorem translateSource_smooth_clause {n : ℕ} {D : InducingData n} {side : Side}
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (x : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (G : AdelicGL) :
    Smooth (fun u : Fin 1 → RealGL3 => coeffVal m
      (HeckeInvariance.translateSource D t c x (G * atInfinity (u 0)))) := by
  have hstep1 : ∀ u : Fin 1 → RealGL3,
      (HeckeInvariance.translateSource D t c x (G * atInfinity (u 0))).val
        = (∑ r ∈ t.representatives, realCoefficientComponent n D.chi
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              ((G * atInfinity (u 0)) * rationalGroup r))).val := by
    intro u; rw [HeckeInvariance.translateSource]
  have hfun : (fun u : Fin 1 → RealGL3 => coeffVal m
        (HeckeInvariance.translateSource D t c x (G * atInfinity (u 0))))
      = fun u => ∑ r ∈ t.representatives, coeffVal m
          (realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              (G * rationalGroup r * atInfinity
                ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (u 0) *
                  GeneralLinearGroup.map (algebraMap ℚ ℝ) r)))) := by
    funext u
    show (HeckeInvariance.translateSource D t c x (G * atInfinity (u 0))).val.coeff m = _
    rw [hstep1 u]
    rw [show (∑ r ∈ t.representatives, realCoefficientComponent n D.chi
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              ((G * atInfinity (u 0)) * rationalGroup r))).val
        = ∑ r ∈ t.representatives, (realCoefficientComponent n D.chi
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              ((G * atInfinity (u 0)) * rationalGroup r))).val
        from map_sum (Submodule.subtype (homogeneousSubmodule (Fin 3) ℂ n)) _ _]
    rw [show (∑ r ∈ t.representatives, (realCoefficientComponent n D.chi
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              ((G * atInfinity (u 0)) * rationalGroup r))).val).coeff m
        = ∑ r ∈ t.representatives, ((realCoefficientComponent n D.chi
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              ((G * atInfinity (u 0)) * rationalGroup r))).val).coeff m
        from map_sum (coeffLM m) _ _]
    apply Finset.sum_congr rfl
    intro r hr
    have hmul : (G * atInfinity (u 0)) * rationalGroup r
        = G * rationalGroup r * atInfinity
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (u 0) *
            GeneralLinearGroup.map (algebraMap ℚ ℝ) r) := by
      rw [mul_assoc, HeckeInvariance.atInfinity_mul_rationalGroup]
      group
    rw [hmul]
  rw [hfun]
  apply smooth_finset_sum
  intro r hr
  exact smooth_representative_term hc r x G m

end TernaryPeriodPolynomials.HeckeTranslate.SourceSmoothness

end
