module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.NilpotentSmoothAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.RealRadicalH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorSmoothCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem realNilpotentExponential_contDiff_top {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (operator : Module.End ℂ E) (continuous : Continuous operator) (cutoff : ℕ)
    (nilpotent : operator ^ cutoff = 0) :
    ContDiff ℝ ⊤ (fun point : ℝ × E => IsNilpotent.exp ((point.1 : ℂ) • operator) point.2) := by
  have powers (power : ℕ) : Continuous (operator ^ power : Module.End ℂ E) := by
    induction power with
    | zero => exact continuous_id
    | succ power hypothesis =>
      rw [pow_succ]
      exact hypothesis.comp continuous
  have term (power : ℕ) : ContDiff ℝ ⊤
      (fun point : ℝ × E => (point.1 ^ power / (power.factorial : ℝ)) • (operator ^ power) point.2) := by
    let linear : E →L[ℝ] E :=
      (⟨operator ^ power, powers power⟩ : E →L[ℂ] E).restrictScalars ℝ
    exact ((contDiff_fst.pow power).div_const (power.factorial : ℝ)).smul (linear.contDiff.comp contDiff_snd)
  have sum := ContDiff.sum (s := Finset.range cutoff) (fun power _ => term power)
  convert sum using 1
  funext point
  exact nilpotentExponential_real_parameter operator cutoff nilpotent point.1 point.2

theorem basisHilbertCoefficient_translation {V index : Type} [AddCommGroup V] [Module ℂ V] [Fintype index]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V) (linear : Module.End ℂ V)
    (element : BinaryAdelicGL) (vectors : index → cusp.H) :
    binaryHilbertTranslation cusp element (basisHilbertCoefficient cusp basis linear vectors) =
      basisHilbertCoefficient cusp basis linear (binaryHilbertTranslation cusp element vectors) := by
  funext position
  simp only [binaryHilbertTranslation_apply, basisHilbertCoefficient_apply, map_sum, map_smul]

theorem realUpperCuspidalAxisAction_orbital_analyticAt {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (coordinate : Fin 2) (scalar : P → ℝ) (values : P → cuspidalTensorValues cusp (HomogeneousPoly degree)) (center : P)
    (scalar_analytic : AnalyticAt ℝ scalar center)
    (values_analytic : AnalyticAt ℝ (fun point : BinaryRealMatrix × P =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2))) (1, center)) :
    AnalyticAt ℝ (fun point : BinaryRealMatrix × P =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis
          (cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
            ((realUpperRadicalRep degree).ρ (realRadicalAxis coordinate (scalar point.2))) (values point.2)))) (1, center) := by
  have input_analytic : AnalyticAt ℝ (fun point : BinaryRealMatrix × P =>
      (scalar point.2, binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2)))) (1, center) :=
    (scalar_analytic.comp (f := fun point : BinaryRealMatrix × P => point.2) (x := (1, center)) analyticAt_snd).prod values_analytic
  have regular := realNilpotentExponential_contDiff_top (realUpperHilbertGenerator degree cusp basis coordinate)
    (basisHilbertCoefficient cusp basis (upperRadicalGenerator degree coordinate)).continuous
    (degree + 1) (realUpperHilbertGenerator_nilpotent degree cusp basis coordinate)
  have composed := regular.contDiffAt.analyticAt.comp (f := fun point : BinaryRealMatrix × P =>
      (scalar point.2, binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2)))) input_analytic
  convert composed using 1
  funext point
  rw [cuspidalTensorHilbertEmbedding_map, basisHilbertCoefficient_translation]
  exact LinearMap.congr_fun (realUpperHilbertRep_axis degree cusp basis coordinate (scalar point.2)) _

theorem cuspidalTensorFamily_contDiff_of_orbital {V index P : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype index] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V) (values : P → cuspidalTensorValues cusp V)
    (analytic : ∀ center, AnalyticAt ℝ (fun point : BinaryRealMatrix × P =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2))) (1, center)) :
    ContDiff ℝ ⊤ (fun point => cuspidalTensorHilbertEmbedding cusp basis (values point)) := by
  rw [contDiff_iff_contDiffAt]
  intro center
  have composed := (analytic center).comp (f := fun point : P => ((1 : BinaryRealMatrix), point))
    (x := center) (analyticAt_const.prod analyticAt_id)
  have value (point : P) : binaryHilbertTranslation cusp (atInfinity (invertibleMatrix (1 : BinaryRealMatrix)))
      (cuspidalTensorHilbertEmbedding cusp basis (values point)) = cuspidalTensorHilbertEmbedding cusp basis (values point) := by
    rw [show invertibleMatrix (1 : BinaryRealMatrix) = (1 : BinaryRealGL) from invertibleMatrix_coe 1, atInfinity_one]
    funext position
    rw [binaryHilbertTranslation_apply, map_one, Module.End.one_apply]
  change AnalyticAt ℝ (fun point : P => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix (1 : BinaryRealMatrix)))
    (cuspidalTensorHilbertEmbedding cusp basis (values point))) center at composed
  simp only [value] at composed
  exact composed.contDiffAt

end TernaryPeriodPolynomials.SphericalDetection.Helpers
