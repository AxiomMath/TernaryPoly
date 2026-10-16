module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Identity.B_P1

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel





variable {g : Poly2}


theorem hpairB_24 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 1, X 1 + X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 1 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 1, X 1 + X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 1 1) (Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_25 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 2, X 1, X 0 + X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 1 2) 1 0 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 2, X 1, X 0 + X 2] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 1 2) 1 0 1) (Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairB_26 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 1 + X 2, X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 1 2) 1 1 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 1 + X 2, X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 1 2) 1 1 1) (Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_one
        ]) <;>
      (try simp (config := { decide := true })) <;>
      (try ring_nf))


theorem hpairB_27 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 1, X 2] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 1) 1 0 0) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 1, X 2] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 0 1) 1 0 0) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_28 (hg : g.IsSymmetric) : bind₁ (![X 0 + X 1, X 2, X 0] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 1 0) g :=
  vec_perm_bind hg (![X 0 + X 1, X 2, X 0] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 1 0) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_29 (hg : g.IsSymmetric) : bind₁ (![X 0, X 2, X 0 + X 1] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 2) 0 0 1) g :=
  vec_perm_bind hg (![X 0, X 2, X 0 + X 1] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 2) 0 0 1) (Equiv.swap 0 1 * Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_30 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 2, X 0 + X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 1) 1 0 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 2, X 0 + X 1] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 0 1) 1 0 1) (Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_31 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 1 + X 2, X 2] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 1) 1 1 0) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 1 + X 2, X 2] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 0 1) 1 1 0) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_32 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 2, X 0] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 1 1 0) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 2, X 0] : Fin 3 → Poly2)) ((![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 1 1 0) (Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_33 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 2, X 1, X 2] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 1) 1 1 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 2, X 1, X 2] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 0 1) 1 1 1) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.swap_apply_def,
        map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_34 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0, X 2, X 1] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 0 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0, X 2, X 1] : Fin 3 → Poly2)) ((![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) i)) (projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 0 1) (Equiv.swap 0 2 * Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))


theorem hpairB_35 (hg : g.IsSymmetric) : bind₁ (![X 1, X 0 + X 2, X 0] : Fin 3 → Poly2) g = bind₁ (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 0 0) g :=
  vec_perm_bind hg (![X 1, X 0 + X 2, X 0] : Fin 3 → Poly2) (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 0 0) (Equiv.swap 0 1 * Equiv.swap 0 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf))

end TernaryPeriodPolynomials.Argument.CharTwoKernel
