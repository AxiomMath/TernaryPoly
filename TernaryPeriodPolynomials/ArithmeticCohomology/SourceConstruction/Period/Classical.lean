module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.PeriodClassCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.ArithmeticPrimitive

@[expose] public section


/-!
# The arithmetic period cocycle is the classical Eichler–Shimura cocycle

Let `I` be an Eichler input whose vector realizes a level one cusp form `f`, i.e.
`f = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector`.  The Eichler cocycle evaluated at the
identity of `GL₂(𝔸)` is

  `α A 1 = ½ (P (A i) - R (P (-conj (A i))))`,

where `P = classicalBinaryPrimitive f (n + 1)` is the holomorphic primitive of `f (X - z Y)^(n+1)`
vanishing at `i` and `R` is the reflection `Y ↦ -Y`: the holomorphic part is the Eichler period of
`f`, and in the antiholomorphic part the real reflection `J` fixes the (spherical) cusp function.
This is the classical parity cocycle `classicalArithmeticCocycle f (n + 1) _ _ (-1) 1 _` pointwise
on `GL₂(ℤ)` (`EichlerInput.arithmeticPeriodCocycle_eq_classical`), so the class of
`arithmeticPeriodCocycle` is the classical Eichler–Shimura class of `f`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

/-- The sign condition for the determinant twist `-1` and the odd parity. -/
theorem periodSign_eq : (-1 : ℂ) ^ (-1 : ℤ) = (-1 : ℂ) ^ (1 : Fin 2).val := by
  norm_num

section Scalar

variable (σ : CuspidalRepresentation) (halfWeight : ℤ) (v : σ.smooth)

/-- At the identity, the scalar weighted realization of the vector is the cusp form. -/
theorem periodScalar_one_eq_form {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (hform : (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ halfWeight 1 v)
    {w : ℂ} (hz : 0 < w.im) :
    cuspScalarWeightedRealization σ halfWeight v 1 w = form (UpperHalfPlane.ofComplex w) := by
  have value := congrFun hform (UpperHalfPlane.ofComplex w)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at value
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  exact value.symm

/-- Spherical vectors have scalar realization invariant under the real reflection `J`. -/
theorem periodScalar_J (spherical : v.val ∈ cuspSphericalValues σ) (w : ℂ) :
    cuspScalarWeightedRealization σ halfWeight v (1 * atInfinity UpperHalfPlane.J) w =
      cuspScalarWeightedRealization σ halfWeight v 1 w := by
  unfold cuspScalarWeightedRealization cuspScalarAffineRealization
  simp only [one_mul]
  rw [← atInfinity_mul, cuspSpherical_realize_J_mul σ v spherical]

end Scalar

/-- **The Eichler period of the scalar realization is the classical holomorphic primitive.** -/
theorem eichlerPeriod_eq_primitive {n : ℕ} {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    {z : ℂ} (hz : 0 < z.im) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL)
    (hF : ∀ w : ℂ, 0 < w.im → F h w = form (UpperHalfPlane.ofComplex w)) :
    eichlerPeriod n F z h = classicalBinaryPrimitive form (n + 1) z := by
  refine Eq.trans ?_ (eichlerPeriod_cuspForm (n := n) form hz h)
  unfold eichlerPeriod
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have positive : 0 < (eichlerPath z t).im := upperHalfPlane_straightPath ⟨z, hz⟩ ht
  simp only [eichlerIntegrand]
  rw [hF _ positive]

namespace EichlerInput

variable {σ : CuspidalRepresentation} {n : ℕ} (I : EichlerInput σ n)

/-- **The Eichler cocycle at the identity in terms of the classical primitive.** -/
theorem eichlerCocycle_one_eq_formula (stages : AnalyticScalar.ContinuousStages σ) {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (hform : (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (even : Even (n + 1)) (A : BinaryRealGL) :
    I.eichlerCocycle A 1 = (2 : ℂ)⁻¹ • (classicalBinaryPrimitive form (n + 1) (basePoint A) -
      binaryParityReflection (n + 1)
        (classicalBinaryPrimitive form (n + 1) (binaryComplexReflection (basePoint A)))) := by
  have unimodular : |(UpperHalfPlane.J : BinaryRealGL).val.det| = 1 := by
    rw [det_upperJ]
    norm_num
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first : eichlerPeriod n (endpointScalar σ I.halfWeight I.vector) (basePoint A) 1 =
      classicalBinaryPrimitive form (n + 1) (basePoint A) :=
    eichlerPeriod_eq_primitive form positive _ 1
      (fun w hz => periodScalar_one_eq_form σ I.halfWeight I.vector form hform hz)
  have second : eichlerPeriod n (endpointScalar σ I.halfWeight I.vector)
      (binaryComplexReflection (basePoint A)) (1 * atInfinity UpperHalfPlane.J) =
        classicalBinaryPrimitive form (n + 1) (binaryComplexReflection (basePoint A)) :=
    eichlerPeriod_eq_primitive form reflected_positive _ _
      (fun w hz => (periodScalar_J σ I.halfWeight I.vector I.vector_spherical w).trans
        (periodScalar_one_eq_form σ I.halfWeight I.vector form hform hz))
  rw [congrFun (I.eichlerCocycle_eq_eichlerNormal stages A) 1, eichlerNormal_def,
    binaryAmbientRepresentation_apply_of_unimodular unimodular, first, second,
    binaryCoefficient_J_apply even, ← sub_eq_add_neg]

/-- **The arithmetic period cocycle is the classical arithmetic cocycle**, pointwise on `GL₂(ℤ)`. -/
theorem eichlerCocycle_one_eq_classical (stages : AnalyticScalar.ContinuousStages σ)
    {form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * I.halfWeight)}
    (hform : (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (weight_eq : -2 * I.halfWeight = ((n + 1 : ℕ) : ℤ) + 2) (even : Even (n + 1))
    (γ : GeneralLinearGroup (Fin 2) ℤ) :
    I.eichlerCocycle (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) 1 =
      classicalArithmeticCocycle form (n + 1) weight_eq even (-1) (1 : Fin 2).val periodSign_eq γ := by
  have base : ((GeneralLinearGroup.map (Int.castRingHom ℝ) γ • UpperHalfPlane.I :
      UpperHalfPlane) : ℂ) = basePoint (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) := rfl
  have parity : (-1 : ℂ) ^ (1 : Fin 2).val = -1 := by
    norm_num
  rw [classicalArithmeticCocycle_apply, classicalParityPrimitive, base,
    I.eichlerCocycle_one_eq_formula stages form hform even, parity]
  congr 1
  rw [sub_eq_add_neg]
  congr 1
  exact (neg_one_smul ℂ _).symm

/-- **The arithmetic period cocycle of an Eichler input realizing a cusp form is the classical
arithmetic cocycle of that form.** -/
theorem arithmeticPeriodCocycle_eq_classical (stages : AnalyticScalar.ContinuousStages σ)
    {form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * I.halfWeight)}
    (hform : (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (weight_eq : -2 * I.halfWeight = ((n + 1 : ℕ) : ℤ) + 2) (even : Even (n + 1)) :
    I.arithmeticPeriodCocycle stages =
      classicalArithmeticCocycle form (n + 1) weight_eq even (-1) (1 : Fin 2).val periodSign_eq := by
  apply groupCohomology.cocycles₁_ext
  intro γ
  exact I.eichlerCocycle_one_eq_classical stages hform weight_eq even γ

end EichlerInput

end TernaryPeriodPolynomials.SourceConstruction

end
