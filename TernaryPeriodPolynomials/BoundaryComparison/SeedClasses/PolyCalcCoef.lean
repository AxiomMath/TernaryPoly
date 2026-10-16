module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PolyCalc
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.CoefSpace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section


/-!
# Differentiation of coefficient-space valued polynomial families

Lifting of the scalar chain rule of `PolyCalc` to the normed coefficient space `Coef m` of
homogeneous polynomials of degree `m`, through the coordinate isometry.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3.Calc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The homogeneous component of degree `m`, as an element of the normed model of `E_m`. -/
def toCoef (m : ℕ) (P : MvPolynomial (Fin 3) ℂ) : Coef m :=
  (⟨homogeneousComponent m P, homogeneousComponent_mem m P⟩ : GeneralEisenstein.HomogeneousPoly m)

theorem toCoef_add (m : ℕ) (P Q : MvPolynomial (Fin 3) ℂ) :
    toCoef m (P + Q) = toCoef m P + toCoef m Q := by
  apply Subtype.ext
  simp [toCoef, map_add]
  rfl

@[simp] theorem toPoly_toCoef (m : ℕ) (P : MvPolynomial (Fin 3) ℂ) :
    Coef.toPoly (toCoef m P) = homogeneousComponent m P := rfl

theorem toPoly_toCoef_of_isHomogeneous (m : ℕ) {P : MvPolynomial (Fin 3) ℂ}
    (hP : P.IsHomogeneous m) : Coef.toPoly (toCoef m P) = P := by
  rw [toPoly_toCoef]
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule m P).mpr hP), ite_eq_left rfl]

theorem coefVec_toCoef (m : ℕ) (P : MvPolynomial (Fin 3) ℂ) (e : Fin 3 → Fin (m + 1)) :
    Coef.vec m (toCoef m P) e =
      if (Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))).degree = m then
        P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))) else 0 := by
  show (homogeneousComponent m P).coeff (Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))) = _
  rw [coeff_homogeneousComponent]

/-- The coordinate map of `E_m` as a continuous real-linear map. -/
def vecCLM (m : ℕ) : Coef m →L[ℝ] ((Fin 3 → Fin (m + 1)) → ℂ) :=
  LinearMap.toContinuousLinearMap ((Coef.vec m).restrictScalars ℝ)

@[simp] theorem vecCLM_apply (m : ℕ) (q : Coef m) : vecCLM m q = Coef.vec m q := rfl

theorem norm_eq_vec (m : ℕ) (q : Coef m) : ‖q‖ = ‖Coef.vec m q‖ := rfl

/-- **Coordinate criterion for differentiability** with values in `E_m`. -/
theorem hasFDerivAt_of_vec (m : ℕ) {f : E → Coef m} {D : E →L[ℝ] Coef m} {x : E}
    (h : HasFDerivAt (fun y => Coef.vec m (f y)) ((vecCLM m).comp D) x) : HasFDerivAt f D x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h ⊢
  refine h.congr_left fun y => ?_
  simp [norm_eq_vec, map_sub]

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- **Chain rule for `E_m`-valued polynomial families.** -/
theorem hasFDerivAt_toCoef_spec (m : ℕ) (s : σ → E → ℂ) (Ds : σ → E →L[ℝ] ℂ) (x : E)
    (hs : ∀ a, HasFDerivAt (s a) (Ds a) x) (Q : MvPolynomial (Fin 3 ⊕ σ) ℂ) :
    HasFDerivAt (fun y => toCoef m (spec (fun a => s a y) Q))
      (∑ a, (Ds a).smulRight (toCoef m (spec (fun a => s a x) (pderiv (Sum.inr a) Q)))) x := by
  apply hasFDerivAt_of_vec
  rw [hasFDerivAt_pi']
  intro e
  set d : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ)) with hd
  have hcoQ : ∀ P : MvPolynomial (Fin 3) ℂ, Coef.vec m (toCoef m P) e =
      if d.degree = m then P.coeff d else 0 := fun P => by
    rw [coefVec_toCoef]
  by_cases hdeg : d.degree = m
  · simp only [hcoQ, hdeg, ite_true]
    refine (hasFDerivAt_coeff_spec s Ds x hs Q d).congr_fderiv ?_
    ext v
    simp [hcoQ, hdeg]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  · simp only [hcoQ, hdeg, ite_false]
    refine (hasFDerivAt_const (0 : ℂ) x).congr_fderiv ?_
    ext v
    simp [hcoQ, hdeg]

omit [Fintype σ] [DecidableEq σ] in
/-- A map into `E_m` is smooth as soon as its coordinate vector is. -/
theorem contDiffOn_of_vec (m : ℕ) {U : Set E} {f : E → Coef m}
    (h : ContDiffOn ℝ ∞ (fun y => Coef.vec m (f y)) U) : ContDiffOn ℝ ∞ f U := by
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Coef.vec m) (by
    rw [LinearMap.ker_eq_bot]; exact Coef.vec_injective m)
  let LC : ((Fin 3 → Fin (m + 1)) → ℂ) →L[ℝ] Coef m :=
    LinearMap.toContinuousLinearMap (L.restrictScalars ℝ)
  have : f = fun y => LC (Coef.vec m (f y)) := by
    funext y
    change f y = L (Coef.vec m (f y))
    exact (LinearMap.congr_fun hL (f y)).symm
  rw [this]
  exact LC.contDiff.comp_contDiffOn h

omit [Fintype σ] [DecidableEq σ] in
/-- Smoothness of `E_m`-valued polynomial families in smooth parameters. -/
theorem contDiffOn_toCoef_spec (m : ℕ) (U : Set E) (s : σ → E → ℂ)
    (hs : ∀ a, ContDiffOn ℝ ∞ (s a) U) (Q : MvPolynomial (Fin 3 ⊕ σ) ℂ) :
    ContDiffOn ℝ ∞ (fun y => toCoef m (spec (fun a => s a y) Q)) U := by
  apply contDiffOn_of_vec
  rw [contDiffOn_pi]
  intro e
  by_cases hdeg : (Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))).degree = m
  · have := contDiffOn_coeff_spec U s hs Q (Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ)))
    simpa [coefVec_toCoef, hdeg] using this
  · simpa [coefVec_toCoef, hdeg] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) U)

end TernaryPeriodPolynomials.Argument.SeedC3.Calc
