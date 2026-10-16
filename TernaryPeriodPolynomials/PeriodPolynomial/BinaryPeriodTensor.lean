module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodDefect
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Module.SnakeLemma

@[expose] public section

open MvPolynomial TensorProduct
noncomputable section
namespace TernaryPoly.BinaryComplexPeriod

/-- Actual scalar extension of the full binary polynomial module. -/
def polyTensorEquiv : ℂ ⊗[ℚ] Poly ℚ ≃ₗ[ℂ] Poly ℂ :=
  (MvPolynomial.algebraTensorAlgEquiv ℚ ℂ).toLinearEquiv

@[simp] theorem polyTensorEquiv_tmul (a : ℂ) (p : Poly ℚ) :
    polyTensorEquiv (a ⊗ₜ[ℚ] p)=a • map (algebraMap ℚ ℂ) p :=
  MvPolynomial.algebraTensorAlgEquiv_tmul ℚ ℂ a p

/-- Scalar extension of the five defect coordinates. -/
def fiveTensorEquiv : ℂ ⊗[ℚ] (Fin 5 → Poly ℚ) ≃ₗ[ℂ] (Fin 5 → Poly ℂ) :=
  (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin 5 => Poly ℚ)).trans
    (LinearEquiv.piCongrRight (fun _ => polyTensorEquiv))

@[simp] theorem fiveTensorEquiv_tmul (a : ℂ) (p : Fin 5 → Poly ℚ) (i : Fin 5) :
    fiveTensorEquiv (a ⊗ₜ[ℚ] p) i=a • map (algebraMap ℚ ℂ) (p i) := by
  simp [fiveTensorEquiv,polyTensorEquiv_tmul]

/-- Flat scalar extension of the actual rational defect. -/
def tensorDefect (d : ℕ) := AlgebraTensorModule.lTensor ℂ ℂ (defect ℚ d)

/-- The complex defect is precisely the base change of the rational one. -/
theorem tensor_defect_commutes (d : ℕ) :
    fiveTensorEquiv.toLinearMap.comp (tensorDefect d)=
      (defect ℂ d).comp polyTensorEquiv.toLinearMap := by
  apply AlgebraTensorModule.ext
  intro a p
  ext i
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,tensorDefect,
    AlgebraTensorModule.lTensor_tmul,fiveTensorEquiv_tmul,polyTensorEquiv_tmul,
    map_smul,Pi.smul_apply,defect_map]

theorem tensor_defect_apply (d : ℕ) (p : ℂ ⊗[ℚ] Poly ℚ) :
    fiveTensorEquiv (tensorDefect d p)=defect ℂ d (polyTensorEquiv p) :=
  LinearMap.congr_fun (tensor_defect_commutes d) p

/-- The actual polynomial tensor equivalence identifies the two actual defect kernels. -/
def tensorDefectKernelEquiv (d : ℕ) : (tensorDefect d).ker ≃ₗ[ℂ] space ℂ d where
  toFun p := ⟨polyTensorEquiv p.val,by
    rw [←ker_defect]
    change defect ℂ d (polyTensorEquiv p.val)=0
    rw [←tensor_defect_apply,p.property,map_zero]⟩
  invFun p := ⟨polyTensorEquiv.symm p.val,by
    change tensorDefect d (polyTensorEquiv.symm p.val)=0
    apply fiveTensorEquiv.injective
    rw [tensor_defect_apply,polyTensorEquiv.apply_symm_apply,map_zero]
    change p.val ∈ (defect ℂ d).ker
    simpa only [ker_defect] using p.property⟩
  left_inv p := by apply Subtype.ext; exact polyTensorEquiv.symm_apply_apply p.val
  right_inv p := by apply Subtype.ext; exact polyTensorEquiv.apply_symm_apply p.val
  map_add' p q := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a p := by apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem tensorDefectKernelEquiv_coe (d : ℕ) (p : (tensorDefect d).ker) :
    (tensorDefectKernelEquiv d p).val=polyTensorEquiv p.val := rfl

/-- The literal period subtype and the literal defect kernel have identical polynomial values. -/
def periodKernelEquiv (K : Type*) [Field K] (d : ℕ) : space K d ≃ₗ[K] (defect K d).ker where
  toFun p := ⟨p.val,by simpa only [ker_defect] using p.property⟩
  invFun p := ⟨p.val,by simpa only [ker_defect] using p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem periodKernelEquiv_coe (K : Type*) [Field K] (d : ℕ) (p : space K d) :
    (periodKernelEquiv K d p).val=p.val := rfl

/-- Scalar extension of the literal rational period space equals the whole actual complex space. -/
def tensorPeriodEquiv (d : ℕ) : ℂ ⊗[ℚ] space ℚ d ≃ₗ[ℂ] space ℂ d :=
  (AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
    (periodKernelEquiv ℚ d)).trans
    ((LinearMap.tensorKerEquiv ℂ ℂ (defect ℚ d)).trans (tensorDefectKernelEquiv d))

@[simp] theorem tensorPeriodEquiv_tmul (d : ℕ) (a : ℂ) (q : space ℚ d) :
    tensorPeriodEquiv d (a ⊗ₜ[ℚ] q)=a • extend (algebraMap ℚ ℂ) d q := by
  apply Subtype.ext
  change polyTensorEquiv (a ⊗ₜ[ℚ] q.val)=a • MvPolynomial.map (algebraMap ℚ ℂ) q.val
  exact polyTensorEquiv_tmul a q.val

/-- Complex and rational literal period spaces have exactly the same finite dimension. -/
theorem complex_finrank_eq (d : ℕ) : Module.finrank ℂ (space ℂ d)=Module.finrank ℚ (space ℚ d) := by
  rw [←(tensorPeriodEquiv d).finrank_eq,Module.finrank_baseChange]

end TernaryPoly.BinaryComplexPeriod
