module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Representation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryPolynomialBasis (degree : ℕ) :
    Module.Basis (Fin (Module.finrank ℂ (Binary.HomogeneousPoly degree))) ℂ
      (Binary.HomogeneousPoly degree) := by
  let : FiniteDimensional ℂ (Binary.HomogeneousPoly degree) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ degree)
  exact Module.finBasis ℂ (Binary.HomogeneousPoly degree)

def binarySmoothCoordinate {degree : ℕ} (cusp : CuspidalRepresentation)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    binaryCuspidalValues cusp degree →ₗ[ℂ] cusp.smooth := by
  let pullback : binaryCuspidalValues cusp degree →ₗ[ℂ] cuspFunctions cusp :=
    { toFun := fun values =>
        ⟨fun argument => functional (values.val argument),
          binaryValues_functional cusp values.val values.property functional⟩
      map_add' := by
        intro first second
        apply Subtype.ext
        funext argument
        exact map_add functional _ _
      map_smul' := by
        intro scalar values
        apply Subtype.ext
        funext argument
        exact map_smul functional scalar _ }
  exact (LinearEquiv.ofInjective cusp.realize cusp.injective).symm.toLinearMap.comp pullback

theorem binarySmoothCoordinate_realize {degree : ℕ} (cusp : CuspidalRepresentation)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (values : binaryCuspidalValues cusp degree) (argument : BinaryAdelicGL) :
    cusp.realize (binarySmoothCoordinate cusp functional values) argument =
      functional (values.val argument) := by
  exact congrFun (LinearEquiv.ofInjective_symm_apply cusp.realize (h := cusp.injective)
    ⟨fun argument => functional (values.val argument),
      binaryValues_functional cusp values.val values.property functional⟩) argument

variable {degree : ℕ} {index : Type} [Fintype index]

def binarySmoothCoordinates (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    binaryCuspidalValues cusp degree →ₗ[ℂ] (index → cusp.smooth) :=
  LinearMap.pi (fun position => binarySmoothCoordinate cusp (basis.coord position))

omit [Fintype index] in
theorem binarySmoothCoordinates_injective (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    Function.Injective (binarySmoothCoordinates cusp basis) := by
  intro first second equality
  apply Subtype.ext
  funext argument
  apply basis.repr.injective
  ext position
  change basis.coord position (first.val argument) = basis.coord position (second.val argument)
  rw [← binarySmoothCoordinate_realize cusp _ first argument,
    ← binarySmoothCoordinate_realize cusp _ second argument]
  exact congrArg (fun vector => cusp.realize vector argument) (congrFun equality position)

theorem binaryValues_fromSmoothCoordinates (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vectors : index → cusp.smooth) :
    BinaryValues cusp degree
      (fun argument => basis.equivFun.symm (fun position => cusp.realize (vectors position) argument)) := by
  classical
  intro monomial
  have expansion :
      (fun argument => (basis.equivFun.symm (fun position => cusp.realize (vectors position) argument)).val.coeff monomial) =
      ∑ position, (basis position).val.coeff monomial • cusp.realize (vectors position) := by
    funext argument
    simp only [Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul,
      coeff_sum, coeff_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro position _
    exact mul_comm _ _
  rw [expansion]
  exact (cuspFunctions cusp).sum_mem (fun position _ =>
    (cuspFunctions cusp).smul_mem _ ⟨vectors position, rfl⟩)

theorem binarySmoothCoordinates_surjective (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    Function.Surjective (binarySmoothCoordinates cusp basis) := by
  intro vectors
  refine ⟨⟨fun argument => basis.equivFun.symm
      (fun position => cusp.realize (vectors position) argument),
    binaryValues_fromSmoothCoordinates cusp basis vectors⟩, ?_⟩
  funext position
  apply cusp.injective
  funext argument
  change cusp.realize (binarySmoothCoordinate cusp (basis.coord position) _) argument = _
  rw [binarySmoothCoordinate_realize, Module.Basis.coord_equivFun_symm]

def binarySmoothCoordinatesEquiv (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    binaryCuspidalValues cusp degree ≃ₗ[ℂ] (index → cusp.smooth) :=
  LinearEquiv.ofBijective (binarySmoothCoordinates cusp basis)
    ⟨binarySmoothCoordinates_injective cusp basis, binarySmoothCoordinates_surjective cusp basis⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
