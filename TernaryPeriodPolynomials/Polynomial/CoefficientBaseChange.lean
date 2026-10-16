module

public import TernaryPeriodPolynomials.Polynomial.Definitions
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.Nilpotent.Defs

@[expose] public section


/-! # Natural scalar extension of the polynomial solution spaces

The proof uses flatness over `ℚ` and the literal linear defect maps. Thus the
coefficient algebra may have zero divisors or nilpotent elements.
-/


open MvPolynomial TensorProduct
noncomputable section
namespace TernaryPoly.Paper

variable {R A : Type*} [CommRing R] [CommRing A]

private theorem map_vec2 {σ : Type*} (φ : R →+* A) (a b : MvPolynomial σ R) :
    (fun i => map φ (![a,b] i)) = ![map φ a, map φ b] := by
  funext i
  fin_cases i <;> rfl

private theorem map_vec3 {σ : Type*} (φ : R →+* A) (a b c : MvPolynomial σ R) :
    (fun i => map φ (![a,b,c] i)) = ![map φ a, map φ b, map φ c] := by
  funext i
  fin_cases i <;> rfl

/-- A rational algebra has torsion-free additive group, even when it has nilpotents. -/
instance (priority := 50) rationalAlgebra_isAddTorsionFree [Algebra ℚ R] : IsAddTorsionFree R := by
  exact IsAddTorsionFree.of_isTorsionFree ℚ R

/-- Coefficient extension commutes with restriction to the coordinate plane. -/
theorem map_coordinateRestriction (φ : R →+* A) (f : Ternary R) :
    map φ (bind₁ (![X 0, X 1, 0] : Fin 3 → Binary R) f) =
      bind₁ (![X 0, X 1, 0] : Fin 3 → Binary A) (map φ f) := by
  simp only [map_bind₁, map_vec3, map_X, map_zero]

/-- Coefficient extension commutes with the literal cyclic binary sum. -/
theorem map_cyclicSum (φ : R →+* A) (q : Binary R) :
    map φ (bind₁ (![X 0, X 1] : Fin 2 → Ternary R) q +
      bind₁ ![X 1, X 2] q + bind₁ ![X 2, X 0] q) =
      bind₁ (![X 0, X 1] : Fin 2 → Ternary A) (map φ q) +
        bind₁ ![X 1, X 2] (map φ q) + bind₁ ![X 2, X 0] (map φ q) := by
  simp only [map_add, map_bind₁, map_vec2, map_X]

/-- Homogeneous components commute with every coefficient ring homomorphism. -/
theorem map_homogeneousComponent (φ : R →+* A) {σ : Type*} (n : ℕ)
    (f : MvPolynomial σ R) :
    map φ (homogeneousComponent n f) = homogeneousComponent n (map φ f) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/-- Solutions are preserved by every coefficient ring homomorphism. -/
theorem Solution.map {f : Ternary R} (hf : Solution f) (φ : R →+* A) :
    Solution (map φ f) := by
  constructor
  · have h := congrArg (MvPolynomial.map φ) hf.1
    simpa only [map_bind₁, map_vec3, map_X] using h
  · have h := congrArg (MvPolynomial.map φ) hf.2
    simpa only [map_add, map_bind₁, map_vec3, map_X, map_neg, map_sub, map_zero] using h

/-- The complete normalized period equations are preserved by coefficient maps. -/
theorem PeriodRelations.map {q : Binary R} (hq : PeriodRelations q) (φ : R →+* A) :
    PeriodRelations (map φ q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_bind₁, map_vec2, map_X, map_zero] using congrArg (MvPolynomial.map φ) hq.1
  · simpa only [map_bind₁, map_vec2, map_X, map_zero] using congrArg (MvPolynomial.map φ) hq.2.1
  · simpa only [map_add, map_bind₁, map_vec2, map_X, map_neg, map_zero]
      using congrArg (MvPolynomial.map φ) hq.2.2.1
  · simpa only [map_add, map_bind₁, map_vec2, map_X, map_neg, map_sub, map_zero]
      using congrArg (MvPolynomial.map φ) hq.2.2.2

/-- The two defects defining unrestricted ternary solutions. -/
def solutionDefect (R : Type*) [CommRing R] : Ternary R →ₗ[R] (Fin 2 → Ternary R) :=
  LinearMap.pi ![(bind₁ ![X 1, X 2, X 0]).toLinearMap - LinearMap.id,
    LinearMap.id + (bind₁ ![-X 1, X 0 - X 1, X 2]).toLinearMap +
      (bind₁ ![X 1 - X 0, -X 0, X 2]).toLinearMap]

/-- Homogeneity together with both ternary equations, as a single linear map. -/
def homogeneousSolutionDefect (R : Type*) [CommRing R] (n : ℕ) :
    Ternary R →ₗ[R] (Fin 3 → Ternary R) :=
  LinearMap.pi ![LinearMap.id - homogeneousComponent n,
    (bind₁ ![X 1, X 2, X 0]).toLinearMap - LinearMap.id,
    LinearMap.id + (bind₁ ![-X 1, X 0 - X 1, X 2]).toLinearMap +
      (bind₁ ![X 1 - X 0, -X 0, X 2]).toLinearMap]

/-- Homogeneity and all four full normalized binary relations. -/
def normalizedPeriodDefect (R : Type*) [CommRing R] (n : ℕ) :
    Binary R →ₗ[R] (Fin 5 → Binary R) :=
  LinearMap.pi ![LinearMap.id - homogeneousComponent n,
    (bind₁ ![0, X 1]).toLinearMap, (bind₁ ![X 0, 0]).toLinearMap,
    LinearMap.id + (bind₁ ![-X 1, X 0]).toLinearMap,
    LinearMap.id + (bind₁ ![-X 1, X 0 - X 1]).toLinearMap +
      (bind₁ ![X 1 - X 0, -X 0]).toLinearMap]

private theorem homogeneous_defect_zero {σ : Type*} (n : ℕ) (f : MvPolynomial σ R) :
    f = homogeneousComponent n f ↔ f.IsHomogeneous n := by
  constructor
  · intro h
    rw [h]
    exact homogeneousComponent_isHomogeneous n f
  · intro h
    rw [homogeneousComponent_eq_self h]

@[simp] theorem ker_solutionDefect : (solutionDefect R).ker = solutions R := by
  ext f
  change solutionDefect R f = 0 ↔ Solution f
  simp [solutionDefect, Solution, funext_iff, Fin.forall_fin_succ, sub_eq_zero]

@[simp] theorem ker_homogeneousSolutionDefect (n : ℕ) :
    (homogeneousSolutionDefect R n).ker = solutionSpace R n := by
  ext f
  change homogeneousSolutionDefect R n f = 0 ↔ f.IsHomogeneous n ∧ Solution f
  simp only [homogeneousSolutionDefect, LinearMap.pi_apply, funext_iff, Pi.zero_apply,
    Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply,
    sub_eq_zero, homogeneous_defect_zero, Solution]
  simp


@[simp] theorem ker_normalizedPeriodDefect (n : ℕ) :
    (normalizedPeriodDefect R n).ker = periodSpace R n := by
  ext f
  change normalizedPeriodDefect R n f = 0 ↔ f.IsHomogeneous n ∧ PeriodRelations f
  simp only [normalizedPeriodDefect, LinearMap.pi_apply, funext_iff, Pi.zero_apply,
    Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply,
    sub_eq_zero, homogeneous_defect_zero, PeriodRelations]
  simp


theorem solutionDefect_map (φ : R →+* A) (f : Ternary R) (i : Fin 2) :
    solutionDefect A (map φ f) i = map φ (solutionDefect R f i) := by
  fin_cases i <;>
    simp [solutionDefect, map_bind₁, map_vec3]

theorem homogeneousSolutionDefect_map (φ : R →+* A) (n : ℕ) (f : Ternary R) (i : Fin 3) :
    homogeneousSolutionDefect A n (map φ f) i = map φ (homogeneousSolutionDefect R n f i) := by
  fin_cases i <;>
    simp [homogeneousSolutionDefect, map_bind₁, map_vec3, map_homogeneousComponent]

theorem normalizedPeriodDefect_map (φ : R →+* A) (n : ℕ) (f : Binary R) (i : Fin 5) :
    normalizedPeriodDefect A n (map φ f) i = map φ (normalizedPeriodDefect R n f i) := by
  fin_cases i <;>
    simp [normalizedPeriodDefect, map_bind₁, map_vec2, map_homogeneousComponent]

section Tensor
variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The natural coefficient extension of the full polynomial module. -/
def polynomialTensorEquiv (σ : Type*) :
    A ⊗[ℚ] MvPolynomial σ ℚ ≃ₗ[A] MvPolynomial σ A :=
  (MvPolynomial.algebraTensorAlgEquiv ℚ A).toLinearEquiv

@[simp] theorem polynomialTensorEquiv_tmul (σ : Type*) (a : A) (f : MvPolynomial σ ℚ) :
    polynomialTensorEquiv A σ (a ⊗ₜ[ℚ] f) = a • map (algebraMap ℚ A) f :=
  MvPolynomial.algebraTensorAlgEquiv_tmul ℚ A a f

/-- Scalar extension in every coordinate of a finite tuple of polynomial defects. -/
def polynomialTupleTensorEquiv (σ : Type*) (k : ℕ) :
    A ⊗[ℚ] (Fin k → MvPolynomial σ ℚ) ≃ₗ[A] (Fin k → MvPolynomial σ A) :=
  (TensorProduct.piRight ℚ A A (fun _ : Fin k => MvPolynomial σ ℚ)).trans
    (LinearEquiv.piCongrRight fun _ => polynomialTensorEquiv A σ)

@[simp] theorem polynomialTupleTensorEquiv_tmul (σ : Type*) (k : ℕ) (a : A)
    (f : Fin k → MvPolynomial σ ℚ) (i : Fin k) :
    polynomialTupleTensorEquiv A σ k (a ⊗ₜ[ℚ] f) i = a • map (algebraMap ℚ A) (f i) := by
  simp [polynomialTupleTensorEquiv]

variable {σ : Type*} {k : ℕ}
variable (dQ : MvPolynomial σ ℚ →ₗ[ℚ] (Fin k → MvPolynomial σ ℚ))
variable (dA : MvPolynomial σ A →ₗ[A] (Fin k → MvPolynomial σ A))
variable (commutes : ∀ (f : MvPolynomial σ ℚ) (i : Fin k),
  dA (map (algebraMap ℚ A) f) i = map (algebraMap ℚ A) (dQ f i))

include commutes

private theorem tensor_defect_commutes :
    (polynomialTupleTensorEquiv A σ k).toLinearMap.comp (AlgebraTensorModule.lTensor A A dQ) =
      dA.comp (polynomialTensorEquiv A σ).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro a f
  apply funext
  intro i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgebraTensorModule.lTensor_tmul,
    polynomialTupleTensorEquiv_tmul, polynomialTensorEquiv_tmul, map_smul, Pi.smul_apply,
    commutes]

theorem tensor_defect_apply (f : A ⊗[ℚ] MvPolynomial σ ℚ) :
    polynomialTupleTensorEquiv A σ k (AlgebraTensorModule.lTensor A A dQ f) =
      dA (polynomialTensorEquiv A σ f) :=
  LinearMap.congr_fun (tensor_defect_commutes A dQ dA commutes) f

/-- The tensor of a rational polynomial kernel is the literal kernel over `A`. -/
def coefficientKernelEquiv : A ⊗[ℚ] dQ.ker ≃ₗ[A] dA.ker :=
  (LinearMap.tensorKerEquiv A A dQ).trans
    { toFun := fun f => ⟨polynomialTensorEquiv A σ f.val, by
        change dA (polynomialTensorEquiv A σ f.val) = 0
        rw [← tensor_defect_apply A dQ dA commutes, f.property, map_zero]⟩
      invFun := fun f => ⟨(polynomialTensorEquiv A σ).symm f.val, by
        change AlgebraTensorModule.lTensor A A dQ ((polynomialTensorEquiv A σ).symm f.val) = 0
        apply (polynomialTupleTensorEquiv A σ k).injective
        rw [tensor_defect_apply A dQ dA commutes, LinearEquiv.apply_symm_apply, f.property,
          map_zero]⟩
      left_inv := fun f => by
        apply Subtype.ext
        exact (polynomialTensorEquiv A σ).symm_apply_apply f.val
      right_inv := fun f => by
        apply Subtype.ext
        exact (polynomialTensorEquiv A σ).apply_symm_apply f.val
      map_add' := fun f g => by apply Subtype.ext; exact map_add _ _ _
      map_smul' := fun a f => by apply Subtype.ext; exact map_smul _ _ _ }

@[simp] theorem coefficientKernelEquiv_tmul (a : A) (f : dQ.ker) :
    (coefficientKernelEquiv A dQ dA commutes (a ⊗ₜ[ℚ] f)).val =
      a • map (algebraMap ℚ A) f.val := by
  change polynomialTensorEquiv A σ (a ⊗ₜ[ℚ] f.val) = _
  exact polynomialTensorEquiv_tmul A σ a f.val

omit commutes

/-- Base change for all ternary solutions, including nonhomogeneous ones. -/
def solutions_baseChangeEquiv : A ⊗[ℚ] solutions ℚ ≃ₗ[A] solutions A :=
  (AlgebraTensorModule.congr (LinearEquiv.refl A A)
    (LinearEquiv.ofEq _ _ (ker_solutionDefect (R := ℚ)).symm)).trans
    ((coefficientKernelEquiv A (solutionDefect ℚ) (solutionDefect A)
      (solutionDefect_map (algebraMap ℚ A))).trans
        (LinearEquiv.ofEq _ _ (ker_solutionDefect (R := A))))

/-- The natural homogeneous solution base-change isomorphism from the paper. -/
def solution_baseChangeEquiv (n : ℕ) : A ⊗[ℚ] solutionSpace ℚ n ≃ₗ[A] solutionSpace A n :=
  (AlgebraTensorModule.congr (LinearEquiv.refl A A)
    (LinearEquiv.ofEq _ _ (ker_homogeneousSolutionDefect (R := ℚ) n).symm)).trans
    ((coefficientKernelEquiv A (homogeneousSolutionDefect ℚ n) (homogeneousSolutionDefect A n)
      (homogeneousSolutionDefect_map (algebraMap ℚ A) n)).trans
        (LinearEquiv.ofEq _ _ (ker_homogeneousSolutionDefect (R := A) n)))

/-- The natural full normalized binary period base-change isomorphism. -/
def normalizedPeriod_baseChangeEquiv (n : ℕ) :
    A ⊗[ℚ] periodSpace ℚ n ≃ₗ[A] periodSpace A n :=
  (AlgebraTensorModule.congr (LinearEquiv.refl A A)
    (LinearEquiv.ofEq _ _ (ker_normalizedPeriodDefect (R := ℚ) n).symm)).trans
    ((coefficientKernelEquiv A (normalizedPeriodDefect ℚ n) (normalizedPeriodDefect A n)
      (normalizedPeriodDefect_map (algebraMap ℚ A) n)).trans
        (LinearEquiv.ofEq _ _ (ker_normalizedPeriodDefect (R := A) n)))

@[simp] theorem solutions_baseChangeEquiv_tmul (a : A) (f : solutions ℚ) :
    (solutions_baseChangeEquiv A (a ⊗ₜ[ℚ] f)).val = a • map (algebraMap ℚ A) f.val := by
  simp only [solutions_baseChangeEquiv, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.coe_ofEq_apply, coefficientKernelEquiv_tmul]

@[simp] theorem solution_baseChangeEquiv_tmul (n : ℕ) (a : A) (f : solutionSpace ℚ n) :
    (solution_baseChangeEquiv A n (a ⊗ₜ[ℚ] f)).val = a • map (algebraMap ℚ A) f.val := by
  simp only [solution_baseChangeEquiv, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.coe_ofEq_apply, coefficientKernelEquiv_tmul]

@[simp] theorem normalizedPeriod_baseChangeEquiv_tmul (n : ℕ) (a : A) (q : periodSpace ℚ n) :
    (normalizedPeriod_baseChangeEquiv A n (a ⊗ₜ[ℚ] q)).val = a • map (algebraMap ℚ A) q.val := by
  simp only [normalizedPeriod_baseChangeEquiv, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.coe_ofEq_apply, coefficientKernelEquiv_tmul]

end Tensor

/-- Add one further linear equation to an existing finite polynomial defect. -/
def extendedDefect {σ : Type*} {k : ℕ}
    (d : MvPolynomial σ R →ₗ[R] (Fin k → MvPolynomial σ R))
    (e : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) :
    MvPolynomial σ R →ₗ[R] (Fin (k + 1) → MvPolynomial σ R) :=
  LinearMap.pi (Fin.cons e fun i => (LinearMap.proj i).comp d)

@[simp] theorem ker_extendedDefect {σ : Type*} {k : ℕ}
    (d : MvPolynomial σ R →ₗ[R] (Fin k → MvPolynomial σ R))
    (e : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) :
    (extendedDefect d e).ker = d.ker ⊓ e.ker := by
  ext f
  simp [extendedDefect, Fin.forall_fin_succ, funext_iff, and_comm, LinearMap.mem_ker]

/-- Scalar extension of a literal kernel after identifying it with the named submodule. -/
def coefficientSubmoduleEquiv (A : Type*) [CommRing A] [Algebra ℚ A]
    {σ : Type*} {k : ℕ}
    (dQ : MvPolynomial σ ℚ →ₗ[ℚ] (Fin k → MvPolynomial σ ℚ))
    (dA : MvPolynomial σ A →ₗ[A] (Fin k → MvPolynomial σ A))
    (commutes : ∀ f i, dA (map (algebraMap ℚ A) f) i = map (algebraMap ℚ A) (dQ f i))
    (sQ : Submodule ℚ (MvPolynomial σ ℚ)) (sA : Submodule A (MvPolynomial σ A))
    (hQ : dQ.ker = sQ) (hA : dA.ker = sA) : A ⊗[ℚ] sQ ≃ₗ[A] sA :=
  (AlgebraTensorModule.congr (LinearEquiv.refl A A) (LinearEquiv.ofEq _ _ hQ.symm)).trans
    ((coefficientKernelEquiv A dQ dA commutes).trans (LinearEquiv.ofEq _ _ hA))

@[simp] theorem coefficientSubmoduleEquiv_tmul (A : Type*) [CommRing A] [Algebra ℚ A]
    {σ : Type*} {k : ℕ}
    (dQ : MvPolynomial σ ℚ →ₗ[ℚ] (Fin k → MvPolynomial σ ℚ))
    (dA : MvPolynomial σ A →ₗ[A] (Fin k → MvPolynomial σ A))
    (commutes : ∀ f i, dA (map (algebraMap ℚ A) f) i = map (algebraMap ℚ A) (dQ f i))
    (sQ : Submodule ℚ (MvPolynomial σ ℚ)) (sA : Submodule A (MvPolynomial σ A))
    (hQ : dQ.ker = sQ) (hA : dA.ker = sA) (a : A) (f : sQ) :
    (coefficientSubmoduleEquiv A dQ dA commutes sQ sA hQ hA (a ⊗ₜ[ℚ] f)).val =
      a • map (algebraMap ℚ A) f.val := by
  simp only [coefficientSubmoduleEquiv, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.coe_ofEq_apply, coefficientKernelEquiv_tmul]

/-- The literal linear defect for the `symmetricSolutionSpace` sector. -/
def symmetricSolutionDefect (R : Type*) [CommRing R] (n : ℕ) :
    Ternary R →ₗ[R] (Fin 4 → Ternary R) :=
  extendedDefect (homogeneousSolutionDefect R n)
    ((bind₁ ![X 1, X 0, X 2]).toLinearMap - LinearMap.id)

@[simp] theorem ker_symmetricSolutionDefect (n : ℕ) :
    (symmetricSolutionDefect R n).ker = symmetricSolutionSpace R n := by
  simp only [symmetricSolutionDefect, ker_extendedDefect, ker_homogeneousSolutionDefect, symmetricSolutionSpace]

theorem symmetricSolutionDefect_map (φ : R →+* A) (n : ℕ) (f : Ternary R) (i : Fin 4) :
    symmetricSolutionDefect A n (map φ f) i = map φ (symmetricSolutionDefect R n f i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [symmetricSolutionDefect, extendedDefect, map_bind₁, map_vec3]
  · simpa only [symmetricSolutionDefect, extendedDefect, LinearMap.pi_apply, Fin.cons_succ,
      LinearMap.comp_apply, LinearMap.proj_apply] using homogeneousSolutionDefect_map φ n f i

/-- Natural base change for the `symmetricSolutionSpace` sector over any commutative rational algebra. -/
def symmetricSolution_baseChangeEquiv (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    A ⊗[ℚ] symmetricSolutionSpace ℚ n ≃ₗ[A] symmetricSolutionSpace A n :=
  coefficientSubmoduleEquiv A (symmetricSolutionDefect ℚ n) (symmetricSolutionDefect A n)
    (symmetricSolutionDefect_map (algebraMap ℚ A) n) _ _
    (ker_symmetricSolutionDefect n) (ker_symmetricSolutionDefect n)

@[simp] theorem symmetricSolution_baseChangeEquiv_tmul (A : Type*) [CommRing A] [Algebra ℚ A]
    (n : ℕ) (a : A) (f : symmetricSolutionSpace ℚ n) :
    (symmetricSolution_baseChangeEquiv A n (a ⊗ₜ[ℚ] f)).val = a • map (algebraMap ℚ A) f.val := by
  exact coefficientSubmoduleEquiv_tmul A _ _ _ _ _ _ _ a f

/-- The literal linear defect for the `alternatingSolutionSpace` sector. -/
def alternatingSolutionDefect (R : Type*) [CommRing R] (n : ℕ) :
    Ternary R →ₗ[R] (Fin 4 → Ternary R) :=
  extendedDefect (homogeneousSolutionDefect R n)
    ((bind₁ ![X 1, X 0, X 2]).toLinearMap + LinearMap.id)

@[simp] theorem ker_alternatingSolutionDefect (n : ℕ) :
    (alternatingSolutionDefect R n).ker = alternatingSolutionSpace R n := by
  simp only [alternatingSolutionDefect, ker_extendedDefect, ker_homogeneousSolutionDefect, alternatingSolutionSpace]

theorem alternatingSolutionDefect_map (φ : R →+* A) (n : ℕ) (f : Ternary R) (i : Fin 4) :
    alternatingSolutionDefect A n (map φ f) i = map φ (alternatingSolutionDefect R n f i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [alternatingSolutionDefect, extendedDefect, map_bind₁, map_vec3]
  · simpa only [alternatingSolutionDefect, extendedDefect, LinearMap.pi_apply, Fin.cons_succ,
      LinearMap.comp_apply, LinearMap.proj_apply] using homogeneousSolutionDefect_map φ n f i

/-- Natural base change for the `alternatingSolutionSpace` sector over any commutative rational algebra. -/
def alternatingSolution_baseChangeEquiv (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    A ⊗[ℚ] alternatingSolutionSpace ℚ n ≃ₗ[A] alternatingSolutionSpace A n :=
  coefficientSubmoduleEquiv A (alternatingSolutionDefect ℚ n) (alternatingSolutionDefect A n)
    (alternatingSolutionDefect_map (algebraMap ℚ A) n) _ _
    (ker_alternatingSolutionDefect n) (ker_alternatingSolutionDefect n)

@[simp] theorem alternatingSolution_baseChangeEquiv_tmul (A : Type*) [CommRing A] [Algebra ℚ A]
    (n : ℕ) (a : A) (f : alternatingSolutionSpace ℚ n) :
    (alternatingSolution_baseChangeEquiv A n (a ⊗ₜ[ℚ] f)).val = a • map (algebraMap ℚ A) f.val := by
  exact coefficientSubmoduleEquiv_tmul A _ _ _ _ _ _ _ a f

/-- The literal linear defect for the `evenPeriodSpace` sector. -/
def evenPeriodDefect (R : Type*) [CommRing R] (n : ℕ) :
    Binary R →ₗ[R] (Fin 6 → Binary R) :=
  extendedDefect (normalizedPeriodDefect R n)
    ((bind₁ ![-X 0, X 1]).toLinearMap - LinearMap.id)

@[simp] theorem ker_evenPeriodDefect (n : ℕ) :
    (evenPeriodDefect R n).ker = evenPeriodSpace R n := by
  simp only [evenPeriodDefect, ker_extendedDefect, ker_normalizedPeriodDefect, evenPeriodSpace]

theorem evenPeriodDefect_map (φ : R →+* A) (n : ℕ) (f : Binary R) (i : Fin 6) :
    evenPeriodDefect A n (map φ f) i = map φ (evenPeriodDefect R n f i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [evenPeriodDefect, extendedDefect, map_bind₁, map_vec2]
  · simpa only [evenPeriodDefect, extendedDefect, LinearMap.pi_apply, Fin.cons_succ,
      LinearMap.comp_apply, LinearMap.proj_apply] using normalizedPeriodDefect_map φ n f i

/-- Natural base change for the `evenPeriodSpace` sector over any commutative rational algebra. -/
def evenPeriod_baseChangeEquiv (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    A ⊗[ℚ] evenPeriodSpace ℚ n ≃ₗ[A] evenPeriodSpace A n :=
  coefficientSubmoduleEquiv A (evenPeriodDefect ℚ n) (evenPeriodDefect A n)
    (evenPeriodDefect_map (algebraMap ℚ A) n) _ _
    (ker_evenPeriodDefect n) (ker_evenPeriodDefect n)

@[simp] theorem evenPeriod_baseChangeEquiv_tmul (A : Type*) [CommRing A] [Algebra ℚ A]
    (n : ℕ) (a : A) (f : evenPeriodSpace ℚ n) :
    (evenPeriod_baseChangeEquiv A n (a ⊗ₜ[ℚ] f)).val = a • map (algebraMap ℚ A) f.val := by
  exact coefficientSubmoduleEquiv_tmul A _ _ _ _ _ _ _ a f

/-- The literal linear defect for the `oddPeriodSpace` sector. -/
def oddPeriodDefect (R : Type*) [CommRing R] (n : ℕ) :
    Binary R →ₗ[R] (Fin 6 → Binary R) :=
  extendedDefect (normalizedPeriodDefect R n)
    ((bind₁ ![-X 0, X 1]).toLinearMap + LinearMap.id)

@[simp] theorem ker_oddPeriodDefect (n : ℕ) :
    (oddPeriodDefect R n).ker = oddPeriodSpace R n := by
  simp only [oddPeriodDefect, ker_extendedDefect, ker_normalizedPeriodDefect, oddPeriodSpace]

theorem oddPeriodDefect_map (φ : R →+* A) (n : ℕ) (f : Binary R) (i : Fin 6) :
    oddPeriodDefect A n (map φ f) i = map φ (oddPeriodDefect R n f i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [oddPeriodDefect, extendedDefect, map_bind₁, map_vec2]
  · simpa only [oddPeriodDefect, extendedDefect, LinearMap.pi_apply, Fin.cons_succ,
      LinearMap.comp_apply, LinearMap.proj_apply] using normalizedPeriodDefect_map φ n f i

/-- Natural base change for the `oddPeriodSpace` sector over any commutative rational algebra. -/
def oddPeriod_baseChangeEquiv (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    A ⊗[ℚ] oddPeriodSpace ℚ n ≃ₗ[A] oddPeriodSpace A n :=
  coefficientSubmoduleEquiv A (oddPeriodDefect ℚ n) (oddPeriodDefect A n)
    (oddPeriodDefect_map (algebraMap ℚ A) n) _ _
    (ker_oddPeriodDefect n) (ker_oddPeriodDefect n)

@[simp] theorem oddPeriod_baseChangeEquiv_tmul (A : Type*) [CommRing A] [Algebra ℚ A]
    (n : ℕ) (a : A) (f : oddPeriodSpace ℚ n) :
    (oddPeriod_baseChangeEquiv A n (a ⊗ₜ[ℚ] f)).val = a • map (algebraMap ℚ A) f.val := by
  exact coefficientSubmoduleEquiv_tmul A _ _ _ _ _ _ _ a f
/-- The rational `solutionSpace` is finite dimensional, since it consists of homogeneous polynomials. -/
instance solutionSpace_rational_finite (n : ℕ) : Module.Finite ℚ (solutionSpace ℚ n) := by
  let : Module.Finite ℚ (homogeneousSubmodule (Fin 3) ℚ n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 3) ℚ n)
  exact Submodule.finiteDimensional_of_le
    (show solutionSpace ℚ n ≤ homogeneousSubmodule (Fin 3) ℚ n from inf_le_left)

/-- Every rational-algebra coefficient extension is free, including nonreduced algebras. -/
instance (priority := 50) solutionSpace_free (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Free A (solutionSpace A n) :=
  Module.Free.of_equiv (solution_baseChangeEquiv A n)

/-- The homogeneous coefficient extension remains finite over an arbitrary rational algebra. -/
instance (priority := 50) solutionSpace_finite (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Finite A (solutionSpace A n) :=
  Module.Finite.of_surjective (solution_baseChangeEquiv A n).toLinearMap
    (solution_baseChangeEquiv A n).surjective

/-- The rank is unchanged under any nonzero commutative rational coefficient algebra. -/
theorem solution_finrank_baseChange (A : Type*) [CommRing A] [Algebra ℚ A] [Nontrivial A]
    (n : ℕ) : Module.finrank A (solutionSpace A n) = Module.finrank ℚ (solutionSpace ℚ n) := by
  rw [← (solution_baseChangeEquiv A n).finrank_eq, Module.finrank_baseChange]

/-- The rational `periodSpace` is finite dimensional, since it consists of homogeneous polynomials. -/
instance periodSpace_rational_finite (n : ℕ) : Module.Finite ℚ (periodSpace ℚ n) := by
  let : Module.Finite ℚ (homogeneousSubmodule (Fin 2) ℚ n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 2) ℚ n)
  exact Submodule.finiteDimensional_of_le
    (show periodSpace ℚ n ≤ homogeneousSubmodule (Fin 2) ℚ n from inf_le_left)

/-- Every rational-algebra coefficient extension is free, including nonreduced algebras. -/
instance (priority := 50) periodSpace_free (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Free A (periodSpace A n) :=
  Module.Free.of_equiv (normalizedPeriod_baseChangeEquiv A n)

/-- The homogeneous coefficient extension remains finite over an arbitrary rational algebra. -/
instance (priority := 50) periodSpace_finite (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Finite A (periodSpace A n) :=
  Module.Finite.of_surjective (normalizedPeriod_baseChangeEquiv A n).toLinearMap
    (normalizedPeriod_baseChangeEquiv A n).surjective

/-- The rank is unchanged under any nonzero commutative rational coefficient algebra. -/
theorem normalizedPeriod_finrank_baseChange (A : Type*) [CommRing A] [Algebra ℚ A] [Nontrivial A]
    (n : ℕ) : Module.finrank A (periodSpace A n) = Module.finrank ℚ (periodSpace ℚ n) := by
  rw [← (normalizedPeriod_baseChangeEquiv A n).finrank_eq, Module.finrank_baseChange]

/-- The rational `symmetricSolutionSpace` is finite dimensional, since it consists of homogeneous polynomials. -/
instance symmetricSolutionSpace_rational_finite (n : ℕ) : Module.Finite ℚ (symmetricSolutionSpace ℚ n) := by
  let : Module.Finite ℚ (homogeneousSubmodule (Fin 3) ℚ n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 3) ℚ n)
  exact Submodule.finiteDimensional_of_le
    (show symmetricSolutionSpace ℚ n ≤ homogeneousSubmodule (Fin 3) ℚ n from inf_le_left.trans inf_le_left)

/-- Every rational-algebra coefficient extension is free, including nonreduced algebras. -/
instance (priority := 50) symmetricSolutionSpace_free (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Free A (symmetricSolutionSpace A n) :=
  Module.Free.of_equiv (symmetricSolution_baseChangeEquiv A n)

/-- The homogeneous coefficient extension remains finite over an arbitrary rational algebra. -/
instance (priority := 50) symmetricSolutionSpace_finite (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Finite A (symmetricSolutionSpace A n) :=
  Module.Finite.of_surjective (symmetricSolution_baseChangeEquiv A n).toLinearMap
    (symmetricSolution_baseChangeEquiv A n).surjective

/-- The rank is unchanged under any nonzero commutative rational coefficient algebra. -/
theorem symmetricSolution_finrank_baseChange (A : Type*) [CommRing A] [Algebra ℚ A] [Nontrivial A]
    (n : ℕ) : Module.finrank A (symmetricSolutionSpace A n) = Module.finrank ℚ (symmetricSolutionSpace ℚ n) := by
  rw [← (symmetricSolution_baseChangeEquiv A n).finrank_eq, Module.finrank_baseChange]

/-- The rational `alternatingSolutionSpace` is finite dimensional, since it consists of homogeneous polynomials. -/
instance alternatingSolutionSpace_rational_finite (n : ℕ) : Module.Finite ℚ (alternatingSolutionSpace ℚ n) := by
  let : Module.Finite ℚ (homogeneousSubmodule (Fin 3) ℚ n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 3) ℚ n)
  exact Submodule.finiteDimensional_of_le
    (show alternatingSolutionSpace ℚ n ≤ homogeneousSubmodule (Fin 3) ℚ n from inf_le_left.trans inf_le_left)

/-- Every rational-algebra coefficient extension is free, including nonreduced algebras. -/
instance (priority := 50) alternatingSolutionSpace_free (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Free A (alternatingSolutionSpace A n) :=
  Module.Free.of_equiv (alternatingSolution_baseChangeEquiv A n)

/-- The homogeneous coefficient extension remains finite over an arbitrary rational algebra. -/
instance (priority := 50) alternatingSolutionSpace_finite (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Finite A (alternatingSolutionSpace A n) :=
  Module.Finite.of_surjective (alternatingSolution_baseChangeEquiv A n).toLinearMap
    (alternatingSolution_baseChangeEquiv A n).surjective

/-- The rank is unchanged under any nonzero commutative rational coefficient algebra. -/
theorem alternatingSolution_finrank_baseChange (A : Type*) [CommRing A] [Algebra ℚ A] [Nontrivial A]
    (n : ℕ) : Module.finrank A (alternatingSolutionSpace A n) = Module.finrank ℚ (alternatingSolutionSpace ℚ n) := by
  rw [← (alternatingSolution_baseChangeEquiv A n).finrank_eq, Module.finrank_baseChange]

/-- The rational `evenPeriodSpace` is finite dimensional, since it consists of homogeneous polynomials. -/
instance evenPeriodSpace_rational_finite (n : ℕ) : Module.Finite ℚ (evenPeriodSpace ℚ n) := by
  let : Module.Finite ℚ (homogeneousSubmodule (Fin 2) ℚ n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 2) ℚ n)
  exact Submodule.finiteDimensional_of_le
    (show evenPeriodSpace ℚ n ≤ homogeneousSubmodule (Fin 2) ℚ n from inf_le_left.trans inf_le_left)

/-- Every rational-algebra coefficient extension is free, including nonreduced algebras. -/
instance (priority := 50) evenPeriodSpace_free (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Free A (evenPeriodSpace A n) :=
  Module.Free.of_equiv (evenPeriod_baseChangeEquiv A n)

/-- The homogeneous coefficient extension remains finite over an arbitrary rational algebra. -/
instance (priority := 50) evenPeriodSpace_finite (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Finite A (evenPeriodSpace A n) :=
  Module.Finite.of_surjective (evenPeriod_baseChangeEquiv A n).toLinearMap
    (evenPeriod_baseChangeEquiv A n).surjective

/-- The rank is unchanged under any nonzero commutative rational coefficient algebra. -/
theorem evenPeriod_finrank_baseChange (A : Type*) [CommRing A] [Algebra ℚ A] [Nontrivial A]
    (n : ℕ) : Module.finrank A (evenPeriodSpace A n) = Module.finrank ℚ (evenPeriodSpace ℚ n) := by
  rw [← (evenPeriod_baseChangeEquiv A n).finrank_eq, Module.finrank_baseChange]

/-- The rational `oddPeriodSpace` is finite dimensional, since it consists of homogeneous polynomials. -/
instance oddPeriodSpace_rational_finite (n : ℕ) : Module.Finite ℚ (oddPeriodSpace ℚ n) := by
  let : Module.Finite ℚ (homogeneousSubmodule (Fin 2) ℚ n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 2) ℚ n)
  exact Submodule.finiteDimensional_of_le
    (show oddPeriodSpace ℚ n ≤ homogeneousSubmodule (Fin 2) ℚ n from inf_le_left.trans inf_le_left)

/-- Every rational-algebra coefficient extension is free, including nonreduced algebras. -/
instance (priority := 50) oddPeriodSpace_free (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Free A (oddPeriodSpace A n) :=
  Module.Free.of_equiv (oddPeriod_baseChangeEquiv A n)

/-- The homogeneous coefficient extension remains finite over an arbitrary rational algebra. -/
instance (priority := 50) oddPeriodSpace_finite (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    Module.Finite A (oddPeriodSpace A n) :=
  Module.Finite.of_surjective (oddPeriod_baseChangeEquiv A n).toLinearMap
    (oddPeriod_baseChangeEquiv A n).surjective

/-- The rank is unchanged under any nonzero commutative rational coefficient algebra. -/
theorem oddPeriod_finrank_baseChange (A : Type*) [CommRing A] [Algebra ℚ A] [Nontrivial A]
    (n : ℕ) : Module.finrank A (oddPeriodSpace A n) = Module.finrank ℚ (oddPeriodSpace ℚ n) := by
  rw [← (oddPeriod_baseChangeEquiv A n).finrank_eq, Module.finrank_baseChange]

end TernaryPoly.Paper
