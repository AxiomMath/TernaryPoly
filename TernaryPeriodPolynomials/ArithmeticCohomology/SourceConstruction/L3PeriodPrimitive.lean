module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.Regularity

@[expose] public section


/-!
# The pointwise Eichler period is the level-three holomorphic primitive

For a holomorphic function `f` on the upper half plane and a family `F` of holomorphic functions on
the upper half plane with `F h w = f w`, the pointwise Eichler period
`∫_i^z F h w (X₀ - w X₁)^{n+1} dw` (`eichlerPeriod`) is the holomorphic primitive of
`f(w) (X₀ - w X₁)^{n+1} dw` vanishing at `i` (`LevelThreePeriodPrimitive.primitive`).  This is the
level-three counterpart of `eichlerPeriod_cuspForm`, which only treats cusp forms for `SL₂(ℤ)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.LevelThree

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The straight-line Eichler period of a holomorphic family is a primitive of the polynomial
valued form `f(w) (X₀ - w X₁)^{n+1}`. -/
theorem l3p_eichlerPeriod_isPrimitive (n : ℕ) {f : UpperHalfPlane → ℂ}
    (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (h : BinaryAdelicGL)
    (hF : ∀ w : ℂ, 0 < w.im → F h w = f (UpperHalfPlane.ofComplex w)) :
    LevelThreePeriodPrimitive.IsPrimitive (n + 1) f (fun w => eichlerPeriod n F w h) := by
  intro ℓ w hw
  have expand : ∀ P : Binary.HomogeneousPoly (n + 1), ℓ P =
      ∑ j, (binaryWeightBasis (n + 1)).coord j P * ℓ (binaryWeightBasis (n + 1) j) := by
    intro P
    conv_lhs => rw [← (binaryWeightBasis (n + 1)).sum_repr P]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
  have values : (fun w' => ℓ (eichlerPeriod n F w' h)) = fun w' =>
      ∑ j, (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w' h) *
        ℓ (binaryWeightBasis (n + 1) j) := funext fun w' => expand _
  show HasDerivAt (fun w' => ℓ (eichlerPeriod n F w' h))
    (ℓ (LevelThreePeriodPrimitive.pointForm (n + 1) f w)) w
  rw [values, expand (LevelThreePeriodPrimitive.pointForm (n + 1) f w)]
  apply HasDerivAt.fun_sum
  intro j _
  refine ((hasDerivAt_coord_eichlerPeriod F holomorphic hw h j).mul_const _).congr_deriv ?_
  simp only [LevelThreePeriodPrimitive.pointForm, map_smul, smul_eq_mul, hF w hw]

/-- **The Eichler period of a holomorphic function is the holomorphic primitive.** -/
theorem l3p_eichlerPeriod_eq_primitive (n : ℕ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (h : BinaryAdelicGL)
    (hF : ∀ w : ℂ, 0 < w.im → F h w = f (UpperHalfPlane.ofComplex w)) {z : ℂ} (hz : 0 < z.im) :
    eichlerPeriod n F z h = LevelThreePeriodPrimitive.primitive (n + 1) f z := by
  have key : eichlerPeriod n F z h = LevelThreePeriodPrimitive.primitive (n + 1) f z +
      eichlerPeriod n F Complex.I h :=
    LevelThreePeriodPrimitive.eq_primitive_add (n + 1) hf (fun w => eichlerPeriod n F w h)
      (l3p_eichlerPeriod_isPrimitive n F holomorphic h hF) z hz
  have zero : eichlerPeriod n F Complex.I h = 0 := by
    have := congrFun (eichlerPeriod_I_eq_zero (n := n) F) h
    simpa using this
  rw [zero, add_zero] at key
  exact key

end TernaryPeriodPolynomials.SourceConstruction

end
