module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.EichlerClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.BinaryCocycle

@[expose] public section


/-!
# The library's holomorphic period cocycle is the Eichler cocycle of Lemma C.3

The library's `classicalBinaryCocycle f d` is the value at `g·i` of the `i`-normalized primitive of
`f(τ)(X − τY)^d dτ` (`classicalBinaryPrimitive`); `eichlerCocycle n G γ` (S3 of Lemma C.3,
`ar:lem:seed`) is the value at `γ·i` of the `i`-normalized primitive `eichlerPoly n G` of
`f(τ)(τY − X)^{n+1}`. They agree up to the sign `(-1)^{n+1}` (`classicalBinaryPrimitive_eq_eichlerPoly`,
`classicalBinaryCocycle_eq_eichlerCocycle`). Used to compare the de Rham class of the seed with the
library's period classes (S4c).

Written by Claude Opus 5.5.
-/

open GeneralEisenstein Matrix MvPolynomial UpperHalfPlane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3

/-- Evaluation of a binary homogeneous form at a point, as a linear functional. -/
def evalFunctional (d : ℕ) (v : Fin 2 → ℂ) : Binary.HomogeneousPoly d →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval v).toLinearMap.comp (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ d).subtype

private theorem evalFunctional_apply (d : ℕ) (v : Fin 2 → ℂ) (P : Binary.HomogeneousPoly d) :
    evalFunctional d v P = MvPolynomial.eval v (P : MvPolynomial (Fin 2) ℂ) := by
  simp [evalFunctional]

/-- **The two `i`-normalized primitives agree** (up to the sign of `(X − τY)^{n+1}` versus
`(τY − X)^{n+1}`). -/
theorem classicalBinaryPrimitive_eq_eichlerPoly {weight : ℤ}
    (f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight) (n : ℕ)
    (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z)
    {z : ℂ} (hz : 0 < z.im) :
    ((classicalBinaryPrimitive f (n + 1) z : Binary.HomogeneousPoly (n + 1)) :
        MvPolynomial (Fin 2) ℂ) = C ((-1 : ℂ) ^ (n + 1)) * eichlerPoly n G z := by
  apply MvPolynomial.funext
  intro v
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hconn : IsPreconnected {u : ℂ | 0 < u.im} := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  let F₁ : ℂ → ℂ := fun w => evalFunctional (n + 1) v (classicalBinaryPrimitive f (n + 1) w)
  let F₂ : ℂ → ℂ := fun w => (-1 : ℂ) ^ (n + 1) * MvPolynomial.eval v (eichlerPoly n G w)
  have h₁ : ∀ w, 0 < w.im → HasDerivAt F₁
      (evalFunctional (n + 1) v (classicalBinaryForm f (n + 1) w)) w := fun w hw =>
    classicalBinaryPrimitive_hasDerivAt f (n + 1) (evalFunctional (n + 1) v) w hw
  have h₂ : ∀ w, 0 < w.im → HasDerivAt F₂
      ((-1 : ℂ) ^ (n + 1) * binaryIntegrand n (fun u => f (ofComplex u)) v w) w := fun w hw =>
    (eichlerPoly_hasDerivAt n (fun u => f (ofComplex u)) G hG v hw).const_mul _
  have hderiv : ∀ w, 0 < w.im →
      evalFunctional (n + 1) v (classicalBinaryForm f (n + 1) w) =
        (-1 : ℂ) ^ (n + 1) * binaryIntegrand n (fun u => f (ofComplex u)) v w := by
    intro w _
    have hform : evalFunctional (n + 1) v (classicalBinaryForm f (n + 1) w) =
        f (ofComplex w) * (v 0 - w * v 1) ^ (n + 1) := by
      rw [evalFunctional_apply]
      simp [classicalBinaryForm, binaryPointPower]
    have hint : binaryIntegrand n (fun u => f (ofComplex u)) v w =
        f (ofComplex w) * (-(v 0 - w * v 1)) ^ (n + 1) := by
      unfold binaryIntegrand
      rw [show w * v 1 - v 0 = -(v 0 - w * v 1) by ring]
    have hs : ((-1 : ℂ)) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hform, hint, neg_pow (v 0 - w * v 1) (n + 1)]
    linear_combination (-(f (ofComplex w) * (v 0 - w * v 1) ^ (n + 1))) * hs
  have heq : Set.EqOn F₁ F₂ {u : ℂ | 0 < u.im} := by
    refine hopen.eqOn_of_deriv_eq hconn (fun w hw => (h₁ w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (h₂ w hw).differentiableAt.differentiableWithinAt) (fun w hw => ?_)
      (show (0 : ℝ) < Complex.I.im by simp) ?_
    · rw [(h₁ w hw).deriv, (h₂ w hw).deriv, hderiv w hw]
    · change evalFunctional (n + 1) v (classicalBinaryPrimitive f (n + 1) Complex.I) =
        (-1 : ℂ) ^ (n + 1) * MvPolynomial.eval v (eichlerPoly n G Complex.I)
      rw [classicalBinaryPrimitive_basepoint, eichlerPoly_base n G hG0, map_zero, map_zero, mul_zero]
  have := heq hz
  change evalFunctional (n + 1) v _ = _ at this
  rw [evalFunctional_apply] at this
  rw [this, MvPolynomial.eval_mul, MvPolynomial.eval_C]

/-- **The library's holomorphic period cocycle is `(-1)^{n+1}` times D's Eichler cocycle.** -/
theorem classicalBinaryCocycle_eq_eichlerCocycle {weight : ℤ}
    (f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight) (n : ℕ)
    (weight_eq : weight = ((n + 1 : ℕ) : ℤ) + 2) (twist : ℤ)
    (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z)
    (m : SpecialLinearGroup (Fin 2) ℤ) :
    (show Binary.HomogeneousPoly (n + 1) from classicalBinaryCocycle f (n + 1) weight_eq twist m).val =
      C ((-1 : ℂ) ^ (n + 1)) * eichlerCocycle n G (SpecialLinearGroup.mapGL ℝ m) := by
  have hpos : 0 < (SpecialLinearGroup.mapGL ℝ m : GL (Fin 2) ℝ).det.val := by
    simp [SpecialLinearGroup.mapGL]
  have hmob : mob (SpecialLinearGroup.mapGL ℝ m) Complex.I =
      ((SpecialLinearGroup.mapGL ℝ m • UpperHalfPlane.I : ℍ) : ℂ) := by
    have := mob_eq_smul (SpecialLinearGroup.mapGL ℝ m) hpos UpperHalfPlane.I
    simpa using this
  change ((classicalBinaryPrimitive f (n + 1)
      ((SpecialLinearGroup.mapGL ℝ m • UpperHalfPlane.I : ℍ) : ℂ) : Binary.HomogeneousPoly (n + 1)) :
        MvPolynomial (Fin 2) ℂ) = _
  rw [eichlerCocycle, hmob]
  exact classicalBinaryPrimitive_eq_eichlerPoly f n G hG0 hG (UpperHalfPlane.im_pos _)

end TernaryPeriodPolynomials.Argument.SeedC3S4c
