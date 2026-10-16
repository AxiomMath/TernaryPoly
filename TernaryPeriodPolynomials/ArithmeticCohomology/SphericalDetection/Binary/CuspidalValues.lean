module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralAction
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryPolynomialCoefficient (degree : ℕ) (monomial : Fin 2 →₀ ℕ) :
    Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ monomial).comp (homogeneousSubmodule (Fin 2) ℂ degree).subtype

theorem binaryPolynomialDual_mem_span_coefficients {degree : ℕ}
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    functional ∈ Submodule.span ℂ (Set.range (binaryPolynomialCoefficient degree)) := by
  let : FiniteDimensional ℂ (Binary.HomogeneousPoly degree) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ degree)
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro polynomial kernels
  have polynomial_zero : polynomial = 0 := by
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    have member := (iInf_le (fun monomial =>
      LinearMap.ker (binaryPolynomialCoefficient degree monomial)) monomial) kernels
    change binaryPolynomialCoefficient degree monomial polynomial = 0 at member
    simpa only [binaryPolynomialCoefficient, LinearMap.comp_apply, Submodule.subtype_apply,
      MvPolynomial.lcoeff_apply, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using member
  rw [polynomial_zero]
  exact Submodule.zero_mem _

theorem binaryValues_functional {degree : ℕ} (cusp : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : BinaryValues cusp degree values)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    (fun argument => functional (values argument)) ∈ cuspFunctions cusp := by
  let pullback : (Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) →ₗ[ℂ]
      (BinaryAdelicGL → ℂ) :=
    { toFun := fun linear argument => linear (values argument)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have coefficients_mem : Submodule.span ℂ
      (Set.range (binaryPolynomialCoefficient (degree + 1))) ≤
        (cuspFunctions cusp).comap pullback := by
    apply Submodule.span_le.mpr
    rintro _ ⟨monomial, rfl⟩
    exact cuspidal monomial
  exact coefficients_mem (binaryPolynomialDual_mem_span_coefficients functional)

theorem binaryValues_comp_linear {degree : ℕ} (cusp : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : BinaryValues cusp degree values)
    (linear : Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) :
    BinaryValues cusp degree (fun argument => linear (values argument)) := by
  intro monomial
  exact binaryValues_functional cusp values cuspidal
    ((binaryPolynomialCoefficient (degree + 1) monomial).comp linear)

theorem binaryValues_right_translate {degree : ℕ} (cusp : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : BinaryValues cusp degree values) (matrix : BinaryAdelicGL) :
    BinaryValues cusp degree (fun argument => values (argument * matrix)) := by
  intro monomial
  rcases cuspidal monomial with ⟨vector, realizes⟩
  refine ⟨⟨cusp.π matrix vector.val,
    cusp.smooth_stable matrix vector.val vector.property⟩, ?_⟩
  funext argument
  rw [cusp.equivariant, realizes]

theorem binaryValues_cohomologicalAction {degree : ℕ} (cusp : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : BinaryValues cusp degree values) (matrix : BinaryRealGL) :
    BinaryValues cusp degree (binaryCohomologicalAction degree matrix values) :=
  binaryValues_smul cusp _
    (binaryValues_comp_linear cusp _
      (binaryValues_right_translate cusp values cuspidal (atInfinity matrix))
      (binaryCoefficient degree matrix)) _

def binaryCuspidalValues (cusp : CuspidalRepresentation) (degree : ℕ) :
    Submodule ℂ (BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) where
  carrier := {values | BinaryValues cusp degree values}
  zero_mem' := by
    intro monomial
    change (fun _ => (0 : Binary.Poly).coeff monomial) ∈ cuspFunctions cusp
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact (cuspFunctions cusp).zero_mem
  add_mem' {first second} first_mem second_mem := by
    intro monomial
    have member : (fun argument => (first argument).val.coeff monomial +
        (second argument).val.coeff monomial) ∈ cuspFunctions cusp :=
      (cuspFunctions cusp).add_mem (first_mem monomial) (second_mem monomial)
    simpa only [Pi.add_apply, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using member
  smul_mem' scalar values cuspidal := binaryValues_smul cusp values cuspidal scalar

end TernaryPeriodPolynomials.SphericalDetection.Helpers
