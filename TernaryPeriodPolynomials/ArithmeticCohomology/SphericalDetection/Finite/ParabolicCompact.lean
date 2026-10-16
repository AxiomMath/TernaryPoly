module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PrincipalPlaneFrames
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PrimeReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteIntegers_isPrincipal (place : FinitePlace) :
    IsPrincipalIdealRing (place.adicCompletionIntegers ℚ) := by
  let prime := Rat.HeightOneSpectrum.primesEquiv place
  let : Fact prime.val.Prime := ⟨prime.property⟩
  let : Algebra ℤ (place.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  let equivalence : place.adicCompletionIntegers ℚ ≃+* ℤ_[prime.val] :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv place).toAlgEquiv.toRingEquiv
  exact IsPrincipalIdealRing.of_surjective equivalence.symm equivalence.symm.surjective

def integralGLFromLocal (matrices : ∀ place : FinitePlace,
    GeneralLinearGroup (Fin 3) (place.adicCompletionIntegers ℚ)) :
    GeneralLinearGroup (Fin 3) IntegralAdeles where
  val := fun row column place => (matrices place).val row column
  inv := fun row column place => (matrices place)⁻¹.val row column
  val_inv := by
    funext row column place
    change (∑ index : Fin 3, (fun place : FinitePlace =>
      (matrices place).val row index * (matrices place)⁻¹.val index column)) place = _
    rw [Finset.sum_apply]
    have equality := congrArg (fun matrix => matrix row column) (matrices place).mul_inv
    simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply, ite_apply,
      Pi.one_apply, Pi.zero_apply] using equality
  inv_val := by
    funext row column place
    change (∑ index : Fin 3, (fun place : FinitePlace =>
      (matrices place)⁻¹.val row index * (matrices place).val index column)) place = _
    rw [Finset.sum_apply]
    have equality := congrArg (fun matrix => matrix row column) (matrices place).inv_mul
    simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply, ite_apply,
      Pi.one_apply, Pi.zero_apply] using equality

theorem integralGLFromLocal_eval (matrices : ∀ place : FinitePlace,
    GeneralLinearGroup (Fin 3) (place.adicCompletionIntegers ℚ)) (place : FinitePlace) :
    GeneralLinearGroup.map (finiteEvaluation place)
      (GeneralLinearGroup.map integralEmbedding (integralGLFromLocal matrices)) =
    GeneralLinearGroup.map (algebraMap (place.adicCompletionIntegers ℚ) (place.adicCompletion ℚ))
      (matrices place) := by
  apply Units.ext
  funext row column
  rfl

/-- The finite adelic plane Iwasawa decomposition, with actual integral compact factor. -/
theorem finiteGL_parabolic_compact_factorization (matrix : FiniteGL) :
    ∃ (parabolic : planeParabolic FiniteAdeles) (compact : GeneralLinearGroup (Fin 3) IntegralAdeles),
      matrix = parabolic.val * GeneralLinearGroup.map integralEmbedding compact := by
  have local_frame (place : FinitePlace) :
      ∃ frame : GeneralLinearGroup (Fin 3) (place.adicCompletionIntegers ℚ),
        GeneralLinearGroup.map (finiteEvaluation place) matrix *
          GeneralLinearGroup.map (algebraMap (place.adicCompletionIntegers ℚ) (place.adicCompletion ℚ)) frame ∈
        planeParabolic (place.adicCompletion ℚ) := by
    let : IsPrincipalIdealRing (place.adicCompletionIntegers ℚ) := finiteIntegers_isPrincipal place
    exact fractionGL_exists_parabolic_integral (GeneralLinearGroup.map (finiteEvaluation place) matrix)
  choose frames frame_parabolic using local_frame
  let compact := integralGLFromLocal frames
  let parabolic := matrix * GeneralLinearGroup.map integralEmbedding compact
  have parabolic_member : parabolic ∈ planeParabolic FiniteAdeles := by
    have entry_zero (column : Fin 2) : parabolic.val 2 column.castSucc = 0 := by
      apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
      intro place
      have evaluated : GeneralLinearGroup.map (finiteEvaluation place) parabolic =
          GeneralLinearGroup.map (finiteEvaluation place) matrix *
            GeneralLinearGroup.map (algebraMap (place.adicCompletionIntegers ℚ) (place.adicCompletion ℚ))
              (frames place) := by
        dsimp only [parabolic, compact]
        rw [map_mul, integralGLFromLocal_eval]
      change finiteEvaluation place (parabolic.val 2 column.castSucc) = 0
      rw [← GeneralLinearGroup.map_apply, evaluated]
      fin_cases column
      · exact (frame_parabolic place).1
      · exact (frame_parabolic place).2
    exact ⟨entry_zero 0, entry_zero 1⟩
  refine ⟨⟨parabolic, parabolic_member⟩, compact⁻¹, ?_⟩
  change matrix = (matrix * GeneralLinearGroup.map integralEmbedding compact) * _
  rw [map_inv, mul_inv_cancel_right]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
