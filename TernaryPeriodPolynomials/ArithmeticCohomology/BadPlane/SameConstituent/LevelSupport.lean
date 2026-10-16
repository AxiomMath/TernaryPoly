module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.LocalSupport

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers

noncomputable section

theorem completion_hom_apply
    (equivalence : placeThree.adicCompletion ℚ ≃A[ℚ] ℚ_[3])
    (value : placeThree.adicCompletion ℚ) :
    equivalence.toRingHom value = equivalence value := by
  rfl

theorem integral_hom_apply
    (equivalence : placeThree.adicCompletionIntegers ℚ ≃+* ℤ_[3])
    (value : placeThree.adicCompletionIntegers ℚ) :
    equivalence.toRingHom value = equivalence value := by
  rfl

theorem padic_hom_apply (value : ℤ_[3]) :
    PadicInt.Coe.ringHom value = (value : ℚ_[3]) := by
  rfl

theorem integral_three_entry (value : IntegralAdeles) :
    threeCompletionEquiv.toRingHom ((finiteEvaluation placeThree) (integralEmbedding value)) =
      PadicInt.Coe.ringHom (integralThree value) := by
  rw [integralEmbedding_at, completion_hom_apply]
  unfold integralThree
  rw [RingHom.comp_apply, Pi.evalRingHom_apply, integral_hom_apply, padic_hom_apply]
  exact (threeIntegral_coe (value placeThree)).symm

theorem local_three_integral (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    localThree (atFinite (GeneralLinearGroup.map integralEmbedding matrix)) =
      GeneralLinearGroup.map PadicInt.Coe.ringHom (GeneralLinearGroup.map integralThree matrix) := by
  apply GeneralLinearGroup.ext
  intro row column
  simp only [localThree, GeneralLinearGroup.map_apply, RingHom.comp_apply,
    RingHom.coe_snd, atFinite, combineGL, pairMatrix]
  exact integral_three_entry (matrix.val row column)

theorem integral_three_reduction (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    GeneralLinearGroup.map PadicInt.toZMod (GeneralLinearGroup.map integralThree matrix) =
      GeneralLinearGroup.map integralReduction matrix := by
  rw [← MonoidHom.comp_apply, ← GeneralLinearGroup.map_comp]
  rfl

theorem adelic_good_finite (compact : finiteLevel) (base : AdelicGL) :
    AdelicGood (base * atFinite compact.val) ↔ AdelicGood base := by
  obtain ⟨integral, integral_membership, integral_equality⟩ := compact.property
  have row : lastRow ᵥ*
      (GeneralLinearGroup.map PadicInt.toZMod (GeneralLinearGroup.map integralThree integral)).val =
        lastRow := by
    rw [integral_three_reduction]
    exact integral_membership
  simp only [AdelicGood, map_mul]
  rw [← integral_equality, local_three_integral]
  exact local_good_integral row (localThree base)

end

end TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers
