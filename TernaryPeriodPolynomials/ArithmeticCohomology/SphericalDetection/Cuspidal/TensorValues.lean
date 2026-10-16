module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SmoothCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (cusp : CuspidalRepresentation) (V : Type) [AddCommGroup V] [Module ℂ V]

/-- Cusp-function-valued coefficients, tested by every algebraic linear functional. -/
def cuspidalTensorValues : Submodule ℂ (BinaryAdelicGL → V) where
  carrier := {values | ∀ functional : V →ₗ[ℂ] ℂ,
    (fun argument => functional (values argument)) ∈ cuspFunctions cusp}
  zero_mem' := by
    intro functional
    change (fun _ => functional (0 : V)) ∈ cuspFunctions cusp
    simp only [map_zero]
    exact (cuspFunctions cusp).zero_mem
  add_mem' {first second} first_mem second_mem := by
    intro functional
    have member : (fun argument => functional (first argument) + functional (second argument)) ∈ cuspFunctions cusp :=
      (cuspFunctions cusp).add_mem (first_mem functional) (second_mem functional)
    simpa only [Pi.add_apply, map_add] using member
  smul_mem' scalar values member := by
    intro functional
    have scaled : (fun argument => scalar • functional (values argument)) ∈ cuspFunctions cusp :=
      (cuspFunctions cusp).smul_mem scalar (member functional)
    simpa only [Pi.smul_apply, map_smul] using scaled

variable {V} {W : Type} [AddCommGroup W] [Module ℂ W]

def cuspidalTensorMap (linear : V →ₗ[ℂ] W) :
    cuspidalTensorValues cusp V →ₗ[ℂ] cuspidalTensorValues cusp W where
  toFun values := ⟨fun argument => linear (values.val argument), fun functional => values.property (functional.comp linear)⟩
  map_add' first second := by
    apply Subtype.ext
    funext argument
    exact map_add linear _ _
  map_smul' scalar values := by
    apply Subtype.ext
    funext argument
    exact map_smul linear scalar _

def cuspidalTensorTranslation (element : BinaryAdelicGL) :
    Module.End ℂ (cuspidalTensorValues cusp V) where
  toFun values := ⟨fun argument => values.val (argument * element), by
    intro functional
    obtain ⟨vector, realizes⟩ := values.property functional
    refine ⟨⟨cusp.π element vector.val, cusp.smooth_stable element vector.val vector.property⟩, ?_⟩
    funext argument
    rw [cusp.equivariant, realizes]
    ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cuspidalTensorFunctional (functional : V →ₗ[ℂ] ℂ) :
    cuspidalTensorValues cusp V →ₗ[ℂ] cusp.smooth := by
  let pullback : cuspidalTensorValues cusp V →ₗ[ℂ] cuspFunctions cusp :=
    { toFun := fun values => ⟨fun argument => functional (values.val argument), values.property functional⟩
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

theorem cuspidalTensorFunctional_realize (functional : V →ₗ[ℂ] ℂ)
    (values : cuspidalTensorValues cusp V) (argument : BinaryAdelicGL) :
    cusp.realize (cuspidalTensorFunctional cusp functional values) argument = functional (values.val argument) :=
  congrFun (LinearEquiv.ofInjective_symm_apply cusp.realize (h := cusp.injective)
    ⟨fun argument => functional (values.val argument), values.property functional⟩) argument

theorem cuspidalTensorValues_binary_iff (degree : ℕ)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) :
    values ∈ cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)) ↔ BinaryValues cusp degree values := by
  constructor
  · intro member monomial
    exact member (binaryPolynomialCoefficient (degree + 1) monomial)
  · intro member
    exact binaryValues_functional cusp values member

variable {G : Type} [Group G]

def cuspidalTensorOperator (coefficient : Representation ℂ G V) (input : G →* BinaryAdelicGL)
    (twist : G →* ℂ) (element : G) : Module.End ℂ (cuspidalTensorValues cusp V) :=
  twist element • (cuspidalTensorMap cusp (coefficient element)).comp (cuspidalTensorTranslation cusp (input element))

theorem cuspidalTensorOperator_apply (coefficient : Representation ℂ G V) (input : G →* BinaryAdelicGL)
    (twist : G →* ℂ) (element : G) (values : cuspidalTensorValues cusp V) (argument : BinaryAdelicGL) :
    (cuspidalTensorOperator cusp coefficient input twist element values).val argument =
      twist element • coefficient element (values.val (argument * input element)) := rfl

def cuspidalTensorRepresentation (coefficient : Representation ℂ G V) (input : G →* BinaryAdelicGL)
    (twist : G →* ℂ) : Representation ℂ G (cuspidalTensorValues cusp V) where
  toFun := cuspidalTensorOperator cusp coefficient input twist
  map_one' := by
    apply LinearMap.ext
    intro values
    apply Subtype.ext
    funext argument
    simp only [cuspidalTensorOperator_apply, map_one, mul_one, Module.End.one_apply, one_smul]
  map_mul' first second := by
    apply LinearMap.ext
    intro values
    apply Subtype.ext
    funext argument
    change (cuspidalTensorOperator cusp coefficient input twist (first * second) values).val argument =
      (cuspidalTensorOperator cusp coefficient input twist first
        (cuspidalTensorOperator cusp coefficient input twist second values)).val argument
    simp only [cuspidalTensorOperator_apply, map_mul, Module.End.mul_apply, map_smul, smul_smul, mul_assoc]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
