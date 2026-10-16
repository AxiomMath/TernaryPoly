module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Identity.B_P0

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel





variable {g : Poly2}


theorem hpairB_12 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 2, X 1 + X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 1) 0 1 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 2, X 1 + X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 0 1) 0 1 1) (Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_13 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 1, X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.refl (Fin 3)) 1 0 0) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 1, X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.refl (Fin 3)) 1 0 0) (Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_14 (hg : g.IsSymmetric) : bind₁ (![X 0 + X 1, X 2, X 1] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 1 2) 0 1 0) g :=
  vec_perm_bind hg (![X 0 + X 1, X 2, X 1] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 1 2) 0 1 0) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_15 (hg : g.IsSymmetric) : bind₁ (![X 1, X 2, X 0 + X 1] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 0 1) g :=
  vec_perm_bind hg (![X 1, X 2, X 0 + X 1] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 0 1) (Equiv.swap 0 1 * Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_16 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 1, X 2, X 0 + X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.refl (Fin 3)) 1 0 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 1, X 2, X 0 + X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.refl (Fin 3)) 1 0 1) (Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_17 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 2, X 1, X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.refl (Fin 3)) 1 1 0) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 2, X 1, X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.refl (Fin 3)) 1 1 0) (Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_18 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 2, X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 1 2) 1 1 0) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 2, X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 1 2) 1 1 0) (Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_19 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 1 + X 2, X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.refl (Fin 3)) 1 1 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 1 + X 2, X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.refl (Fin 3)) 1 1 1) (Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_20 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 1, X 2, X 0] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 1 2) 0 0 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 1, X 2, X 0] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 1 2) 0 0 1) (Equiv.swap 0 2 * Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_21 (hg : g.IsSymmetric) : bind₁ (![X 0, X 1 + X 2, X 1] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 1 0) g :=
  vec_perm_bind hg (![X 0, X 1 + X 2, X 1] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 1 0) (Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_22 (hg : g.IsSymmetric) : bind₁ (![X 0, X 1, X 1 + X 2] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 2) 1 0 0) g :=
  vec_perm_bind hg (![X 0, X 1, X 1 + X 2] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 2) 1 0 0) (Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_23 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 1, X 2, X 0 + X 1] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 1 2) 0 1 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 1, X 2, X 0 + X 1] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 1 2) 0 1 1) (Equiv.swap 0 2 * Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))

end TernaryPeriodPolynomials.Argument.CharTwoKernel
