module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.SlotPermutation

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel





variable {g : Poly2}

theorem hg_id_fact (_hg : g.IsSymmetric) : (bind₁ (X : Fin 3 → Poly2)) g = g := by
  rw [MvPolynomial.bind₁_X_left]; rfl


theorem hpairB_0 (hg : g.IsSymmetric) : bind₁ (![X 0, X 1, X 2] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.refl (Fin 3)) 0 0 0) g :=
  vec_perm_bind hg (![X 0, X 1, X 2] : Fin 3 → Poly2) (projectorSubstitution (Equiv.refl (Fin 3)) 0 0 0) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, 
        map_zero
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_1 (hg : g.IsSymmetric) : bind₁ (![X 0, X 2, X 1] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 1 2) 0 0 0) g :=
  vec_perm_bind hg (![X 0, X 2, X 1] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 1 2) 0 0 0) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_zero
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_2 (hg : g.IsSymmetric) : bind₁ (![X 1, X 2, X 0] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 1) 0 0 0) g :=
  vec_perm_bind hg (![X 1, X 2, X 0] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 1) 0 0 0) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_3 (hg : g.IsSymmetric) : g = bind₁ (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 0 0) g :=
  (hg_id_fact hg).symm.trans (vec_perm_bind hg (X : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 0 0) (Equiv.swap 0 1 * Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero
        ]) <;>
      (try simp (config := { decide := true }))))


theorem hpairB_4 (hg : g.IsSymmetric) : bind₁ (projectorSubstitution (Equiv.swap 0 2) 0 0 0) g = bind₁ (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 0 0) g :=
  vec_perm_bind hg (projectorSubstitution (Equiv.swap 0 2) 0 0 0) (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 0 0) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_5 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 1, X 2, X 0] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.refl (Fin 3)) 0 0 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 1, X 2, X 0] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.refl (Fin 3)) 0 0 1) (Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_6 (hg : g.IsSymmetric) : bind₁ (![X 0, X 1 + X 2, X 2] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 1) 0 1 0) g :=
  vec_perm_bind hg (![X 0, X 1 + X 2, X 2] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 1) 0 1 0) (Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_7 (hg : g.IsSymmetric) : bind₁ (![X 0, X 2, X 1 + X 2] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 1 0 0) g :=
  vec_perm_bind hg (![X 0, X 2, X 1 + X 2] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 1 0 0) (Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_8 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 2, X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.refl (Fin 3)) 0 1 0) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 2, X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.refl (Fin 3)) 0 1 0) (Equiv.swap 0 1 * Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_9 (hg : g.IsSymmetric) : bind₁ (![X 0 + X 2, X 1, X 2] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 1 2) 1 0 0) g :=
  vec_perm_bind hg (![X 0 + X 2, X 1, X 2] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 1 2) 1 0 0) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_10 (hg : g.IsSymmetric) : bind₁ (![X 2, X 1, X 0 + X 2] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 1) 0 0 1) g :=
  vec_perm_bind hg (![X 2, X 1, X 0 + X 2] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 1) 0 0 1) (Equiv.swap 0 1 * Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_11 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 2, X 1, X 0 + X 2] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.refl (Fin 3)) 0 1 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 2, X 1, X 0 + X 2] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.refl (Fin 3)) 0 1 1) (Equiv.swap 0 2 * Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))

end TernaryPeriodPolynomials.Argument.CharTwoKernel
