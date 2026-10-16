module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.PermSums

@[expose] public section





open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

/-- The three images of the identity permutation. -/
theorem perm_refl_0 : (Equiv.refl (Fin 3)) 0 = 0 := rfl
theorem perm_refl_1 : (Equiv.refl (Fin 3)) 1 = 1 := rfl
theorem perm_refl_2 : (Equiv.refl (Fin 3)) 2 = 2 := rfl

theorem perm_swap01_0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
theorem perm_swap01_1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
theorem perm_swap01_2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide

theorem perm_swap02_0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
theorem perm_swap02_1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
theorem perm_swap02_2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide

theorem perm_swap12_0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
theorem perm_swap12_1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
theorem perm_swap12_2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide

theorem perm_cyc1_0 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
theorem perm_cyc1_1 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) 1 = 0 := by decide
theorem perm_cyc1_2 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) 2 = 1 := by decide

theorem perm_cyc2_0 : (Equiv.swap (0 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
theorem perm_cyc2_1 : (Equiv.swap (0 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) 1 = 2 := by decide
theorem perm_cyc2_2 : (Equiv.swap (0 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) 2 = 0 := by decide

/-- Extracting the third (index `2`) component of an explicit length-three vector. -/
theorem cons_val_two {α : Type*} (x y z : α) : (![x, y, z] : Fin 3 → α) 2 = z := rfl

/-- Extracting components of an explicit length-eight vector (indices `0,1` are already
covered generically by `Matrix.cons_val_zero`/`Matrix.cons_val_one`/`Matrix.head_cons`). -/
theorem cons_val8_2 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) :
    (![x0, x1, x2, x3, x4, x5, x6, x7] : Fin 8 → α) 2 = x2 := rfl
theorem cons_val8_3 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) :
    (![x0, x1, x2, x3, x4, x5, x6, x7] : Fin 8 → α) 3 = x3 := rfl
theorem cons_val8_4 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) :
    (![x0, x1, x2, x3, x4, x5, x6, x7] : Fin 8 → α) 4 = x4 := rfl
theorem cons_val8_5 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) :
    (![x0, x1, x2, x3, x4, x5, x6, x7] : Fin 8 → α) 5 = x5 := rfl
theorem cons_val8_6 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) :
    (![x0, x1, x2, x3, x4, x5, x6, x7] : Fin 8 → α) 6 = x6 := rfl
theorem cons_val8_7 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) :
    (![x0, x1, x2, x3, x4, x5, x6, x7] : Fin 8 → α) 7 = x7 := rfl

end TernaryPeriodPolynomials.Argument.CharTwoKernel
