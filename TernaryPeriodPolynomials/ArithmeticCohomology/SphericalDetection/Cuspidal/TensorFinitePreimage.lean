module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorExactness
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorPolynomial

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspidalTensorMap_exists_finiteLevel_preimage {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (cusp : CuspidalRepresentation) (linear : V →ₗ[ℂ] W) (values : cuspidalTensorValues cusp W)
    (fixed : values ∈ cuspidalTensorFiniteLevel cusp W)
    (member : ∀ argument, values.val argument ∈ linear.range) :
    ∃ preimage : cuspidalTensorValues cusp V,
      cuspidalTensorMap cusp linear preimage = values ∧ preimage ∈ cuspidalTensorFiniteLevel cusp V := by
  let rangeValues : BinaryAdelicGL → linear.range := fun argument => ⟨values.val argument, member argument⟩
  have cuspidal : rangeValues ∈ cuspidalTensorValues cusp linear.range :=
    (cuspidalTensorValues_iff_of_injective cusp linear.range.subtype Subtype.val_injective rangeValues).mpr values.property
  let rangeTensor : cuspidalTensorValues cusp linear.range := ⟨rangeValues, cuspidal⟩
  have rangeFixed : rangeTensor ∈ cuspidalTensorFiniteLevel cusp linear.range := by
    intro matrix argument
    apply Subtype.ext
    exact fixed matrix argument
  have surjective : Function.Surjective linear.rangeRestrict := by
    rintro ⟨value, preimage, equality⟩
    exact ⟨preimage, Subtype.ext equality⟩
  obtain ⟨sectionMap, section_law⟩ := linear.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr surjective)
  refine ⟨cuspidalTensorMap cusp sectionMap rangeTensor, ?_,
    cuspidalTensorMap_finiteLevel cusp sectionMap rangeTensor rangeFixed⟩
  apply Subtype.ext
  funext argument
  exact congrArg Subtype.val (LinearMap.congr_fun section_law (rangeValues argument))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
