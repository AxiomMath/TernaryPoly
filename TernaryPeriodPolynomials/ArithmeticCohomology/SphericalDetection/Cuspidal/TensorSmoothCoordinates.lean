module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.HilbertCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneFiniteLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

def cuspidalTensorFromSmoothCoordinates (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (vectors : index → cusp.smooth) : cuspidalTensorValues cusp V :=
  ⟨fun argument => basis.equivFun.symm (fun position => cusp.realize (vectors position) argument), by
    classical
    intro functional
    have expansion : (fun argument => functional
        (basis.equivFun.symm (fun position => cusp.realize (vectors position) argument))) =
        ∑ position, functional (basis position) • cusp.realize (vectors position) := by
      funext argument
      simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro position _
      exact mul_comm _ _
    rw [expansion]
    exact (cuspFunctions cusp).sum_mem (fun position _ =>
      (cuspFunctions cusp).smul_mem _ ⟨vectors position, rfl⟩)⟩

theorem cuspidalTensorHilbertEmbedding_fromSmoothCoordinates (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ V) (vectors : index → cusp.smooth) :
    cuspidalTensorHilbertEmbedding cusp basis (cuspidalTensorFromSmoothCoordinates cusp basis vectors) =
      fun position => (vectors position).val := by
  funext position
  have coordinate : cuspidalTensorFunctional cusp (basis.coord position)
      (cuspidalTensorFromSmoothCoordinates cusp basis vectors) = vectors position := by
    apply cusp.injective
    funext argument
    rw [cuspidalTensorFunctional_realize]
    exact Module.Basis.coord_equivFun_symm basis position _
  exact congrArg Subtype.val coordinate

theorem cuspidalTensorHilbertEmbedding_mem_range (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ V) (vectors : index → cusp.H) :
    vectors ∈ Set.range (cuspidalTensorHilbertEmbedding cusp basis) ↔ ∀ position, vectors position ∈ cusp.smooth := by
  constructor
  · rintro ⟨values, rfl⟩ position
    exact (cuspidalTensorFunctional cusp (basis.coord position) values).property
  · intro smooth
    exact ⟨cuspidalTensorFromSmoothCoordinates cusp basis (fun position => ⟨vectors position, smooth position⟩),
      cuspidalTensorHilbertEmbedding_fromSmoothCoordinates cusp basis _⟩

omit [Fintype index] in
theorem cuspidalTensorHilbertEmbedding_translation (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ V) (element : BinaryAdelicGL) (values : cuspidalTensorValues cusp V) :
    cuspidalTensorHilbertEmbedding cusp basis (cuspidalTensorTranslation cusp element values) =
      binaryHilbertTranslation cusp element (cuspidalTensorHilbertEmbedding cusp basis values) := by
  funext position
  have equality : cuspidalTensorFunctional cusp (basis.coord position) (cuspidalTensorTranslation cusp element values) =
      ⟨cusp.π element (cuspidalTensorFunctional cusp (basis.coord position) values).val,
        cusp.smooth_stable element _ (cuspidalTensorFunctional cusp (basis.coord position) values).property⟩ := by
    apply cusp.injective
    funext argument
    rw [cusp.equivariant, cuspidalTensorFunctional_realize, cuspidalTensorFunctional_realize]
    rfl
  exact congrArg Subtype.val equality

omit [Fintype index] in
theorem cuspidalTensorFiniteLevel_iff_hilbert (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ V) (values : cuspidalTensorValues cusp V) :
    values ∈ cuspidalTensorFiniteLevel cusp V ↔
      ∀ position, cuspidalTensorHilbertEmbedding cusp basis values position ∈ cuspSphericalValues cusp := by
  constructor
  · intro fixed position integral
    have values_fixed : cuspidalTensorTranslation cusp
        (atFinite (GeneralLinearGroup.map integralEmbedding integral)) values = values := by
      apply Subtype.ext
      funext argument
      exact fixed integral argument
    have equality := congrArg (cuspidalTensorHilbertEmbedding cusp basis) values_fixed
    rw [cuspidalTensorHilbertEmbedding_translation] at equality
    exact congrFun equality position
  · intro fixed integral argument
    have equality : cuspidalTensorTranslation cusp
        (atFinite (GeneralLinearGroup.map integralEmbedding integral)) values = values := by
      apply cuspidalTensorHilbertEmbedding_injective cusp basis
      rw [cuspidalTensorHilbertEmbedding_translation]
      funext position
      exact fixed position integral
    exact congrArg (fun value : cuspidalTensorValues cusp V => value.val argument) equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
