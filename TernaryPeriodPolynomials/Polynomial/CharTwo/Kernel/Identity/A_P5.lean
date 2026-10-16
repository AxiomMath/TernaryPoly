module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Identity.A_P4

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel





variable {g : Poly2}


theorem hpairA_60 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 0 1) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 1 0) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 0 1) i)) (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 1 0) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })) <;>
      (try ring_nf);
      (try simp [ofNat_mod2']))


theorem hpairA_61 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 1 0 1) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 2) 1 1 0) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 1 0 1) i)) (projectorSubstitution (Equiv.swap 0 2) 1 1 0) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })) <;>
      (try ring_nf);
      (try simp [ofNat_mod2']))


theorem hpairA_62 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 0 1 1) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 1 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 0 1 1) i)) (projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 1 1) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })) <;>
      (try ring_nf);
      (try simp [ofNat_mod2']))


theorem hpairA_63 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 1 1) i)) g = bind₁ (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 1 2) 0 0 1) i)) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 1 1) i)) (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 1 2) 0 0 1) i)) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf);
      (try simp [ofNat_mod2']))


theorem hpairA_64 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 1 0 0) i)) g = bind₁ (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 1 0) i)) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 1 0 0) i)) (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 1 0) i)) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })))


theorem hpairA_65 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 1 1 0) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 2) 1 0 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 1 1 0) i)) (projectorSubstitution (Equiv.swap 0 2) 1 0 1) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })) <;>
      (try ring_nf);
      (try simp [ofNat_mod2']))


theorem hpairA_66 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 1 0) i)) g = bind₁ (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 0 1) i)) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 1 0) i)) (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 0 1) i)) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })) <;>
      (try ring_nf) <;>
      (try simp [ofNat_mod2']))


theorem hpairA_67 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 0 1 0) i)) g = bind₁ (projectorSubstitution (Equiv.swap 0 2) 1 1 1) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2) 0 1 0) i)) (projectorSubstitution (Equiv.swap 0 2) 1 1 1) (Equiv.swap 1 2) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true })) <;>
      (try ring_nf))


theorem hpairA_68 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 0 0) i)) g = bind₁ (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 1 2) 0 1 1) i)) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 1 0 0) i)) (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 1 2) 0 1 1) i)) (Equiv.swap 0 2 * Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf);
      (try simp [ofNat_mod2']))


theorem hpairA_69 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 0 1) i)) g = bind₁ (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 1 1) i)) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 0 0 1) i)) (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 1 * Equiv.swap 0 2) 0 1 1) i)) (Equiv.swap 0 1) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf);
      (try simp [ofNat_mod2']))


theorem hpairA_70 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 1 1 1) i)) g = bind₁ (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 1 2) 1 0 1) i)) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 1 1 1) i)) (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 1 2) 1 0 1) i)) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf);
      (try simp [ofNat_mod2']))


theorem hpairA_71 (hg : g.IsSymmetric) : bind₁ (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 1 0 1) i)) g = bind₁ (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 1 2) 1 1 1) i)) g :=
  vec_perm_bind hg (fun i => (bind₁ (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 0 2 * Equiv.swap 0 1) 1 0 1) i)) (fun i => (bind₁ (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2)) ((projectorSubstitution (Equiv.swap 1 2) 1 1 1) i)) (Equiv.refl (Fin 3)) (by
    intro i; fin_cases i <;>
      (try simp (config := { decide := true }) only [projectorSubstitution,
        Equiv.refl_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        map_zero, map_one
        ]) <;>
      (try simp (config := { decide := true }));
      (try ring_nf);
      (try simp [ofNat_mod2']))

end TernaryPeriodPolynomials.Argument.CharTwoKernel
