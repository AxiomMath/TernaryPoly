module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.Helpers

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.Relations

noncomputable section

def normMatrix {ring : Type*} [CommRing ring] :
    GeneralLinearGroup (Fin 3) ring :=
  ⟨!![0,-1,0;1,-1,0;0,0,1], !![-1,1,0;-1,0,0;0,0,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem normMatrix_cubed {ring : Type*} [CommRing ring] :
    (normMatrix : GeneralLinearGroup (Fin 3) ring) ^ 3 = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [normMatrix, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem normMatrix_inverse : (normMatrix : GL3)⁻¹ = normMatrix ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', normMatrix_cubed]

theorem normMatrix_det :
    (GeneralLinearGroup.det (normMatrix : GL3) : ℂ) = 1 := by
  simp [GeneralLinearGroup.val_det_apply, normMatrix, Matrix.det_fin_three]

theorem substitute_normMatrix :
    substitute (normMatrix : GL3).val = bind₁ ![-X 1, X 0 - X 1, X 2] := by
  apply MvPolynomial.algHom_ext
  intro index
  fin_cases index <;>
    simp [substitute_X, linearForm, normMatrix, Fin.sum_univ_three, sub_eq_add_neg,
      add_comm]

theorem substitute_normMatrix_square :
    substitute (normMatrix ^ 2 : GL3).val = bind₁ ![X 1 - X 0, -X 0, X 2] := by
  apply MvPolynomial.algHom_ext
  intro index
  fin_cases index <;>
    simp [substitute_X, linearForm, normMatrix, pow_two,
      Fin.sum_univ_three, sub_eq_add_neg, add_comm]

theorem action_normMatrix (polynomial : Poly) :
    action (-1) normMatrix polynomial = bind₁ ![X 1 - X 0, -X 0, X 2] polynomial := by
  rw [action_apply, normMatrix_inverse, substitute_normMatrix_square]
  change (GeneralLinearGroup.det (normMatrix : GL3) : ℂ) ^ (-1 : ℤ) • _ = _
  rw [normMatrix_det]
  simp

theorem action_normMatrix_square (polynomial : Poly) :
    action (-1) (normMatrix ^ 2) polynomial =
      bind₁ ![-X 1, X 0 - X 1, X 2] polynomial := by
  rw [action_apply]
  have inverseSquare : (normMatrix ^ 2 : GL3)⁻¹ = normMatrix := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ, normMatrix_cubed]
  rw [inverseSquare, substitute_normMatrix]
  change (GeneralLinearGroup.det (normMatrix ^ 2 : GL3) : ℂ) ^ (-1 : ℤ) • _ = _
  rw [map_pow, Units.val_pow_eq_pow_val, normMatrix_det]
  simp

theorem polynomial_norm_relation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (solution : SymmetricSolution polynomial) :
    polynomial + homogeneousAction degree (-1) normMatrix polynomial +
      homogeneousAction degree (-1) (normMatrix ^ 2) polynomial = 0 := by
  apply Subtype.ext
  change polynomial.val + action (-1) normMatrix polynomial.val +
    action (-1) (normMatrix ^ 2) polynomial.val = 0
  rw [action_normMatrix, action_normMatrix_square]
  convert solution.2 using 1; abel

def swapMatrix {ring : Type*} [CommRing ring] :
    GeneralLinearGroup (Fin 3) ring :=
  ⟨!![0,1,0;1,0,0;0,0,1], !![0,1,0;1,0,0;0,0,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem swapMatrix_inverse {ring : Type*} [CommRing ring] :
    (swapMatrix : GeneralLinearGroup (Fin 3) ring)⁻¹ = swapMatrix := rfl

theorem swapMatrix_det :
    (GeneralLinearGroup.det (swapMatrix : GL3) : ℂ) = -1 := by
  simp [GeneralLinearGroup.val_det_apply, swapMatrix, Matrix.det_fin_three]

theorem substitute_swapMatrix :
    substitute (swapMatrix : GL3).val =
      bind₁ (fun index => X (Equiv.swap (0 : Fin 3) 1 index)) := by
  apply MvPolynomial.algHom_ext
  intro index
  fin_cases index <;>
    simp [substitute_X, linearForm, swapMatrix, Fin.sum_univ_three, Equiv.swap_apply_def]

theorem polynomial_swap_relation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (solution : SymmetricSolution polynomial) :
    homogeneousAction degree (-1) swapMatrix polynomial = -polynomial := by
  apply Subtype.ext
  change action (-1) swapMatrix polynomial.val = -polynomial.val
  rw [action_apply, swapMatrix_inverse, substitute_swapMatrix, solution.1]
  change (GeneralLinearGroup.det (swapMatrix : GL3) : ℂ) ^ (-1 : ℤ) • _ = _
  rw [swapMatrix_det]
  simp

def cyclePermutation : Equiv.Perm (Fin 3) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 2)

theorem weyl_inverse {ring : Type*} [CommRing ring] :
    (Adelic.weyl : GeneralLinearGroup (Fin 3) ring)⁻¹ = Adelic.weyl ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  have cube : (Adelic.weyl : GeneralLinearGroup (Fin 3) ring) ^ 3 = 1 := by
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Adelic.weyl, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  rw [← pow_succ', cube]

theorem weyl_det : (GeneralLinearGroup.det (Adelic.weyl : GL3) : ℂ) = 1 := by
  simp [GeneralLinearGroup.val_det_apply, Adelic.weyl, Matrix.det_fin_three]

theorem substitute_weyl_inverse :
    substitute (Adelic.weyl : GL3)⁻¹.val =
      bind₁ (fun index => X (cyclePermutation index)) := by
  apply MvPolynomial.algHom_ext
  intro index
  fin_cases index <;>
    simp [substitute_X, linearForm, Adelic.weyl, cyclePermutation, Equiv.swap_apply_def,
      Fin.sum_univ_three]

theorem polynomial_cycle_relation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (solution : SymmetricSolution polynomial) :
    homogeneousAction degree (-1) Adelic.weyl polynomial = polynomial := by
  apply Subtype.ext
  change action (-1) Adelic.weyl polynomial.val = polynomial.val
  rw [action_apply, substitute_weyl_inverse, solution.1]
  change (GeneralLinearGroup.det (Adelic.weyl : GL3) : ℂ) ^ (-1 : ℤ) • _ = _
  rw [weyl_det]
  simp

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.Relations
