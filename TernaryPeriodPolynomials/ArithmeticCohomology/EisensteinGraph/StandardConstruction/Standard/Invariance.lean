module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ContinuationUniqueness

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardInvariance

theorem integrand_lineRadical (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (argument : AdelicGL) (first second : Adeles) (coordinates : Adeles × Adeles) :
    standardIntegrand extension parameter (lineUnipotent first second * argument)
        coordinates =
      standardIntegrand extension parameter argument (coordinates + (first, second)) := by
  unfold standardIntegrand
  rw [← mul_assoc, mul_assoc (weyl⁻¹ : AdelicGL), ← lineUnipotent_add]
  rfl

theorem integral_lineRadical (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (argument : AdelicGL) (first second : Adeles) :
    (∫ coordinates, standardIntegrand extension parameter
      (lineUnipotent first second * argument) coordinates ∂radicalMeasure) =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates
        ∂radicalMeasure := by
  simp_rw [integrand_lineRadical]
  exact integral_add_right_eq_self _ (first, second)

theorem continuation_lineRadical (extension continuation : ℂ → AdelicGL → ℂ)
    (continues : IsStandardContinuation extension continuation) (point : ℂ)
    (regular : ∀ argument,
      AnalyticAt ℂ (fun parameter => continuation parameter argument) point)
    (first second : Adeles) (argument : AdelicGL) :
    continuation point (lineUnipotent first second * argument) =
      continuation point argument := by
  obtain ⟨threshold, integrals⟩ := continues.2
  apply ContinuationUniqueness.meromorphic_halfPlane_unique _ _
    (continues.1 (lineUnipotent first second * argument)) (continues.1 argument)
    threshold _ point (regular _) (regular _)
  intro parameter membership
  rw [(integrals parameter membership _).2, (integrals parameter membership argument).2]
  exact integral_lineRadical extension parameter argument first second

theorem continuation_finite {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation) (point : ℂ)
    (regular : ∀ argument,
      AnalyticAt ℂ (fun parameter => continuation parameter argument) point)
    (levelElement : finiteLevel) (argument : AdelicGL) :
    continuation point (argument * atFinite levelElement.val) =
      continuation point argument := by
  obtain ⟨threshold, integrals⟩ := continues.2
  apply ContinuationUniqueness.meromorphic_halfPlane_unique _ _
    (continues.1 (argument * atFinite levelElement.val)) (continues.1 argument)
    threshold _ point (regular _) (regular _)
  intro parameter membership
  rw [(integrals parameter membership _).2, (integrals parameter membership argument).2]
  apply integral_congr_ae
  filter_upwards [] with coordinates
  unfold standardIntegrand
  rw [← mul_assoc, (flat.1 parameter).2.1 levelElement]

theorem polynomialContinuation_lineRadical {degree : ℕ}
    (extension continuation :
      ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (continues : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (extension parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (continuation parameter vertices argument).val.coeff monomial))
    (point : ℂ) (regular : ∀ vertices argument monomial,
      AnalyticAt ℂ (fun parameter => (continuation parameter vertices argument).val.coeff monomial) point)
    (vertices : Fin 3 → RealGL3) (first second : Adeles) (argument : AdelicGL) :
    continuation point vertices (lineUnipotent first second * argument) =
      continuation point vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact continuation_lineRadical _ _ (continues vertices monomial) point
    (fun argument => regular vertices argument monomial) first second argument

theorem polynomialContinuation_finite {degree : ℕ} (data : InducingData degree)
    (extension continuation :
      ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (flat : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (extension parameter vertices argument).val.coeff monomial))
    (continues : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (extension parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (continuation parameter vertices argument).val.coeff monomial))
    (point : ℂ) (regular : ∀ vertices argument monomial,
      AnalyticAt ℂ (fun parameter => (continuation parameter vertices argument).val.coeff monomial) point)
    (vertices : Fin 3 → RealGL3) (levelElement : finiteLevel) (argument : AdelicGL) :
    continuation point vertices (argument * atFinite levelElement.val) =
      continuation point vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact continuation_finite data _ _ (flat vertices monomial)
    (continues vertices monomial) point (fun argument => regular vertices argument monomial)
    levelElement argument

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardInvariance
