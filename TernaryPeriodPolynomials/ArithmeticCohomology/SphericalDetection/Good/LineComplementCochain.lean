module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.ArchimedeanIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The good-line family after removing the proved local factor at three. -/
def goodLineComplementFamily {degree : ℕ} (standard : ℂ → SourceCochain degree)
    (parameter : ℂ) (vertices : Fin 3 → RealGL3) : HomogeneousPoly degree :=
  (9 : ℂ) • standard parameter vertices (rationalGroup rationalGoodLine)

theorem goodLineComplementFamily_coeff {degree : ℕ} (standard : ℂ → SourceCochain degree)
    (parameter : ℂ) (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
    (goodLineComplementFamily standard parameter vertices).val.coeff monomial =
      (9 : ℂ) * (standard parameter vertices (rationalGroup rationalGoodLine)).val.coeff monomial := by
  simp [goodLineComplementFamily]

/-- This family's coefficients continue the actual complementary real-and-finite integral. -/
theorem goodLineComplementFamily_continuation {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat standard : ℂ → SourceCochain degree)
    (flat_sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (flat cohomologicalPoint vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
    (∀ parameter, MeromorphicAt
      (fun parameter => (goodLineComplementFamily standard parameter vertices).val.coeff monomial)
      parameter) ∧
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (standardGoodLineArchimedeanIntegral
        (fun parameter argument => (flat parameter vertices argument).val.coeff monomial) parameter)
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      (goodLineComplementFamily standard parameter vertices).val.coeff monomial =
        ∫ finite, standardGoodLineArchimedeanIntegral
          (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
          parameter finite ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  constructor
  · intro parameter
    simp only [goodLineComplementFamily_coeff]
    exact analyticAt_const.meromorphicAt.mul
      ((continuations vertices monomial).1 (rationalGroup rationalGoodLine) parameter)
  · obtain ⟨threshold, formula⟩ := standardContinuation_goodLine_archimedean_finite local_entry data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial)
      (flat_sections vertices monomial) (endpoint_support vertices monomial) (continuations vertices monomial)
    refine ⟨threshold, ?_⟩
    intro parameter beyond
    obtain ⟨integrable, value⟩ := formula parameter beyond
    refine ⟨integrable, ?_⟩
    rw [goodLineComplementFamily_coeff, value]
    ring

theorem goodLineComplementFamily_analytic {degree : ℕ} (standard : ℂ → SourceCochain degree)
    (analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (standard parameter vertices argument).val.coeff monomial)
      cohomologicalPoint) (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
    AnalyticAt ℂ
      (fun parameter => (goodLineComplementFamily standard parameter vertices).val.coeff monomial)
      cohomologicalPoint := by
  simp only [goodLineComplementFamily_coeff]
  exact analyticAt_const.mul (analytic vertices (rationalGroup rationalGoodLine) monomial)

/-- The supplied good-line primitive also gives a primitive for the complementary continuation. -/
theorem goodLineComplementFamily_coboundary {degree : ℕ} (data : InducingData degree)
    (standard : ℂ → SourceCochain degree)
    (primitive : cochains (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent degree data.chi) 1)
    (coboundary : ∀ vertices : Fin 3 → RationalGL3,
      standard cohomologicalPoint
        (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
        (rationalGroup rationalGoodLine) =
      (differentialOne (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree data.chi) primitive).val vertices) :
    ∀ vertices : Fin 3 → RationalGL3,
      goodLineComplementFamily standard cohomologicalPoint
        (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index)) =
      (differentialOne (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree data.chi) ((9 : ℂ) • primitive)).val vertices := by
  intro vertices
  rw [goodLineComplementFamily, coboundary, map_smul]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
