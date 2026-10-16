module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.PrimitiveInterface

@[expose] public section


/-!
# The mixed radical derivative of the transfer of the Eichler normal form

For the pointwise Eichler normal form `N = eichlerNormal n F`, the mixed derivative
`∂_{Y₁ = eᵢ} ∂_{Y₂ = eⱼ}` at the origin of the radical section
`Y₁, Y₂ ↦ ℓ(t(e^{Y₁}, e^{Y₁ + Y₂}))` of the real good-line transfer is the scalar test of
`TS(u) · k⁻¹ ⋆ dμ(ξ(k Rⱼ)) N'(ż(k Rᵢ))`, where `k = k(u)` is the orthogonal Iwasawa factor of the
good-line argument, `Rᵢ = E₂ᵢ`, `ξ` and `ż` are the derivatives of the radical coordinate and of
the Levi point at `k`, `N'` is the derivative of the pointwise normal form at `i` and `dμ` the
derivative of the upper binary value at `0`. Only the first vertex moves the normal form, and the
radical difference of the two vertices is linear to first order.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial Filter Topology

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

namespace RadicalLie

open EdgeExplicit

/-- The vertex matrix `k(u) (1 + s Rᵢ + r Rⱼ)` of the radical pair. -/
def radicalCurve (u : ℝ × ℝ) (i j : Fin 2) (s r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  axisCurve u i s + r • (gsOrthMatrix u * axisVelocity j)

theorem lineVertex_radical_pair (u : ℝ × ℝ) (i j : Fin 2) (s r : ℝ) :
    (gsOrth u * lineMatrix (lineRadicalElement (s • Pi.single i 1 + r • Pi.single j 1))).val =
      radicalCurve u i j s r := by
  rw [Units.val_mul, lineMatrix_val_eq, gsOrth_val]
  rw [show radicalCurve u i j s r =
      gsOrthMatrix u * (1 + s • axisVelocity i + r • axisVelocity j) by
    simp only [radicalCurve, axisCurve, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [lineRadicalElement, planeBlock, axisVelocity, Matrix.mul_apply, Fin.sum_univ_three]

theorem axisCurve_eq (u : ℝ × ℝ) (i : Fin 2) (s : ℝ) :
    (gsOrth u * lineMatrix (lineRadicalElement (s • Pi.single i 1))).val = axisCurve u i s :=
  lineVertex_radical u i s

theorem det_axisCurve_ne_zero (u : ℝ × ℝ) (i : Fin 2) (s : ℝ) : (axisCurve u i s).det ≠ 0 := by
  rw [← axisCurve_eq]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _) |>.ne_zero

theorem axisCurve_at_zero (u : ℝ × ℝ) (i : Fin 2) : axisCurve u i 0 = gsOrthMatrix u :=
  axisCurve_zero u i

/-- **The radical section of the Eichler normal form through the symmetric projection.** -/
theorem radicalSection_eichlerNormal (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (i j : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s r : ℝ) :
    radicalSection (eichlerNormal n F) u h functional (s • Pi.single i 1) (r • Pi.single j 1) =
      movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (axisCurve u i s)))
        (realUpperBinaryValue n (Multiplicative.ofAdd
            (symmetricRadical (radicalCurve u i j s r) - symmetricRadical (axisCurve u i s)))
          (eichlerPointNormal n F (symmetricPoint (axisCurve u i s)) (movedPoint u h)))) := by
  rw [radicalSection, relativeIntegrand_eichlerNormal, axisCurve_eq, lineVertex_radical_pair]
  rfl

/-- The radical velocity `dξ_{k(1 + s Rᵢ)}(k Rⱼ)` along the second axis. -/
def pairVelocity (u : ℝ × ℝ) (i j : Fin 2) (s : ℝ) : Fin 2 → ℝ :=
  fderiv ℝ symmetricRadical (axisCurve u i s) (gsOrthMatrix u * axisVelocity j)

theorem hasDerivAt_pairRadical (u : ℝ × ℝ) (i j : Fin 2) (s : ℝ) :
    HasDerivAt (fun r => symmetricRadical (radicalCurve u i j s r) -
      symmetricRadical (axisCurve u i s)) (pairVelocity u i j s) 0 := by
  have smooth := ((contDiffAt_symmetricRadical_of 1 (det_axisCurve_ne_zero u i s)).differentiableAt
    (by norm_num)).hasFDerivAt
  have line : HasDerivAt (fun r : ℝ => axisCurve u i s + r • (gsOrthMatrix u * axisVelocity j))
      (gsOrthMatrix u * axisVelocity j) 0 := by
    refine (((hasDerivAt_id' (0 : ℝ)).smul_const (gsOrthMatrix u * axisVelocity j)).const_add
      (axisCurve u i s)).congr_deriv ?_
    rw [one_smul]
  exact (smooth.comp_hasDerivAt_of_eq 0 line (by rw [zero_smul, add_zero])).sub_const _

theorem continuousAt_pairVelocity (u : ℝ × ℝ) (i j : Fin 2) :
    ContinuousAt (pairVelocity u i j) 0 := by
  have smooth : ContinuousAt (fderiv ℝ symmetricRadical) (axisCurve u i 0) :=
    ((contDiffAt_symmetricRadical_of 1 (det_axisCurve_ne_zero u i 0)).fderiv_right (m := 0)
      (by norm_num)).continuousAt
  exact (ContinuousAt.comp (f := axisCurve u i) smooth
    (continuous_axisCurve u i).continuousAt).clm_apply continuousAt_const

theorem pairVelocity_zero (u : ℝ × ℝ) (i j : Fin 2) :
    pairVelocity u i j 0 = radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity j) := by
  rw [pairVelocity, axisCurve_at_zero,
    (hasFDerivAt_symmetricRadical (gsOrthMatrix_transpose_mul u)).fderiv]

/-- The radical derivative of the radical section, for fixed `s`. -/
theorem hasDerivAt_radicalSection (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (i j : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => radicalSection (eichlerNormal n F) u h functional
        (s • Pi.single i 1) (r • Pi.single j 1))
      (movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (axisCurve u i s)))
        (muDeriv n (pairVelocity u i j s)
          (eichlerPointNormal n F (symmetricPoint (axisCurve u i s)) (movedPoint u h))))) 0 := by
  have base : symmetricRadical (radicalCurve u i j s 0) - symmetricRadical (axisCurve u i s) =
      0 := by
    rw [radicalCurve, zero_smul, add_zero, sub_self]
  have derived := hasDerivAt_functional_realUpperBinaryValue (movedTest u functional ∘ₗ
    (realUpperRadicalRep n).ρ (Multiplicative.ofAdd (symmetricRadical (axisCurve u i s))))
    (eichlerPointNormal n F (symmetricPoint (axisCurve u i s)) (movedPoint u h))
    base (hasDerivAt_pairRadical u i j s)
  simp only [LinearMap.comp_apply] at derived
  simp only [radicalSection_eichlerNormal]
  exact derived

variable (F : BinaryAdelicGL → ℂ → ℂ)
  (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})

include holomorphic in
/-- The derivative along the first axis of the radical derivative of the radical section. -/
theorem hasDerivAt_radicalSection_axis (u : ℝ × ℝ) (i j : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    HasDerivAt (fun s => movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (axisCurve u i s)))
        (muDeriv n (pairVelocity u i j s)
          (eichlerPointNormal n F (symmetricPoint (axisCurve u i s)) (movedPoint u h)))))
      (movedTest u functional
        (muDeriv n (radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity j))
          (normalDerivVector n F (movedPoint u h)
            (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i))))) 0 := by
  have derived := hasDerivAt_apply_of_eq_zero (binaryWeightBasis (n + 1))
    (fun s => (movedTest u functional ∘ₗ (realUpperRadicalRep n).ρ (Multiplicative.ofAdd
      (symmetricRadical (axisCurve u i s)))) ∘ₗ muDeriv n (pairVelocity u i j s))
    (fun s => eichlerPointNormal n F (symmetricPoint (axisCurve u i s)) (movedPoint u h))
    (fun k => eichlerPointNormalDeriv n F Complex.I (movedPoint u h) k
      (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i)))
    (fun w => by
      simp only [LinearMap.comp_apply]
      exact continuousAt_functional_muDeriv (continuous_symmetricRadical_axis u i)
        (continuousAt_pairVelocity u i j) w _)
    (by
      change eichlerPointNormal n F (symmetricPoint (axisCurve u i 0)) (movedPoint u h) = 0
      rw [axisCurve_at_zero, symmetricPoint_gsOrthMatrix, eichlerPointNormal_at_I])
    (fun k => hasDerivAt_coord_normal_axis F holomorphic u i (movedPoint u h) k)
  simp only [LinearMap.comp_apply, axisCurve_at_zero, symmetricRadical_gsOrthMatrix,
    pairVelocity_zero, ofAdd_zero, map_one, Module.End.one_apply] at derived
  exact derived

include holomorphic in
/-- **The mixed radical derivative of the Eichler normal form** is the scalar test of
`TS(u) · k⁻¹ ⋆ dμ(ξ(k Rⱼ)) N'(ż(k Rᵢ))`. -/
theorem radicalMixed_eichlerNormal (u : ℝ × ℝ) (i j : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    radicalMixed (eichlerNormal n F) u i j h functional =
      movedTest u functional
        (muDeriv n (radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity j))
          (normalDerivVector n F (movedPoint u h)
            (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i)))) := by
  have inner : (fun s : ℝ => deriv (fun r : ℝ => radicalSection (eichlerNormal n F) u h functional
      (s • Pi.single i 1) (r • Pi.single j 1)) 0) = fun s => movedTest u functional
        ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd (symmetricRadical (axisCurve u i s)))
          (muDeriv n (pairVelocity u i j s)
            (eichlerPointNormal n F (symmetricPoint (axisCurve u i s)) (movedPoint u h)))) :=
    funext fun s => (hasDerivAt_radicalSection F u i j h functional s).deriv
  rw [radicalMixed, inner]
  exact (hasDerivAt_radicalSection_axis F holomorphic u i j h functional).deriv

end RadicalLie

end TernaryPeriodPolynomials.AnalyticClasses
