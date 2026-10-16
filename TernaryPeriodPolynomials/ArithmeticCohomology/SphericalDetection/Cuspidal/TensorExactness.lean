module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorArithmetic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (cusp : CuspidalRepresentation)
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem cuspidalTensorValues_iff_of_injective (linear : V →ₗ[ℂ] W) (injective : Function.Injective linear)
    (values : BinaryAdelicGL → V) :
    values ∈ cuspidalTensorValues cusp V ↔ (fun argument => linear (values argument)) ∈ cuspidalTensorValues cusp W := by
  constructor
  · intro member functional
    exact member (functional.comp linear)
  · intro member
    obtain ⟨retraction, retracts⟩ := linear.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr injective)
    intro functional
    have scalar := member (functional.comp retraction)
    have equality (argument : BinaryAdelicGL) : retraction (linear (values argument)) = values argument :=
      LinearMap.congr_fun retracts (values argument)
    simpa only [LinearMap.comp_apply, equality] using scalar

theorem cuspidalTensorMap_injective (linear : V →ₗ[ℂ] W) (injective : Function.Injective linear) :
    Function.Injective (cuspidalTensorMap cusp linear) := by
  intro first second equality
  apply Subtype.ext
  funext argument
  apply injective
  exact congrArg (fun values : cuspidalTensorValues cusp W => values.val argument) equality

theorem cuspidalTensorMap_surjective (linear : V →ₗ[ℂ] W) (surjective : Function.Surjective linear) :
    Function.Surjective (cuspidalTensorMap cusp linear) := by
  obtain ⟨sectionMap, section_law⟩ := linear.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surjective)
  intro values
  refine ⟨cuspidalTensorMap cusp sectionMap values, ?_⟩
  apply Subtype.ext
  funext argument
  exact LinearMap.congr_fun section_law (values.val argument)

theorem cuspidalTensorMap_mem_range (linear : V →ₗ[ℂ] W) (values : cuspidalTensorValues cusp W) :
    values ∈ (cuspidalTensorMap cusp linear).range ↔ ∀ argument, values.val argument ∈ linear.range := by
  constructor
  · rintro ⟨preimage, rfl⟩ argument
    exact ⟨preimage.val argument, rfl⟩
  · intro member
    let rangeValues : BinaryAdelicGL → linear.range := fun argument => ⟨values.val argument, member argument⟩
    have cuspidal : rangeValues ∈ cuspidalTensorValues cusp linear.range :=
      (cuspidalTensorValues_iff_of_injective cusp linear.range.subtype Subtype.val_injective rangeValues).mpr values.property
    have surjective : Function.Surjective linear.rangeRestrict := by
      rintro ⟨value, preimage, equality⟩
      exact ⟨preimage, Subtype.ext equality⟩
    obtain ⟨preimage, equality⟩ := cuspidalTensorMap_surjective cusp linear.rangeRestrict surjective ⟨rangeValues, cuspidal⟩
    refine ⟨preimage, ?_⟩
    apply Subtype.ext
    funext argument
    exact congrArg (fun vector : cuspidalTensorValues cusp linear.range => (vector.val argument).val) equality

theorem cuspidalTensorMap_exact {U : Type} [AddCommGroup U] [Module ℂ U]
    (first : U →ₗ[ℂ] V) (second : V →ₗ[ℂ] W) (exactness : first.range = second.ker) :
    (cuspidalTensorMap cusp first).range = (cuspidalTensorMap cusp second).ker := by
  ext values
  rw [cuspidalTensorMap_mem_range]
  simp only [exactness, LinearMap.mem_ker]
  constructor
  · intro zero
    apply Subtype.ext
    funext argument
    exact zero argument
  · intro zero argument
    exact congrArg (fun vector : cuspidalTensorValues cusp W => vector.val argument) zero

def cuspidalTensorPair (first : cuspidalTensorValues cusp V) (second : cuspidalTensorValues cusp W) :
    cuspidalTensorValues cusp (V × W) :=
  ⟨fun argument => (first.val argument, second.val argument), by
    intro functional
    have first_member := first.property (functional.comp (LinearMap.inl ℂ V W))
    have second_member := second.property (functional.comp (LinearMap.inr ℂ V W))
    have sum_member : (fun argument => functional (first.val argument, 0) + functional (0, second.val argument)) ∈
        cuspFunctions cusp := (cuspFunctions cusp).add_mem first_member second_member
    have equality (argument : BinaryAdelicGL) :
        functional (first.val argument, second.val argument) =
          functional (first.val argument, 0) + functional (0, second.val argument) := by
      rw [← map_add]
      simp
    simpa only [equality] using sum_member⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
