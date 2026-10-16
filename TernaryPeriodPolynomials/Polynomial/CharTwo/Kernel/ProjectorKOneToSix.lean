module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.ProjectorKZero

@[expose] public section









open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

private theorem ofNat_mod2 (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly2) = ((n % 2 : ℕ) : Poly2) :=
  CharP.cast_eq_mod Poly2 2 n

theorem projector_K1 :
    substitutionProjector (projectedSource 1) = TernaryPoly.CharTwoNorm.generator 1 := by
  unfold substitutionProjector projectedSource
  rw [sum_univ_perm3]
  simp only [sum_univ_zmod2, projectorSubstitution,
    perm_refl_0, perm_refl_1, perm_refl_2,
    perm_swap01_0, perm_swap01_1, perm_swap01_2,
    perm_swap02_0, perm_swap02_1, perm_swap02_2,
    perm_swap12_0, perm_swap12_1, perm_swap12_2,
    perm_cyc1_0, perm_cyc1_1, perm_cyc1_2,
    perm_cyc2_0, perm_cyc2_1, perm_cyc2_2,
    map_add, map_mul, map_pow, map_zero, map_one,
    MvPolynomial.bind₁_X_right, 
    Matrix.cons_val_zero, Matrix.cons_val_one, 
    cons_val_two, 
    TernaryPoly.CharTwoNorm.generator, TernaryPoly.CharTwoNorm.basis,
    TernaryPoly.CharTwoNorm.a, TernaryPoly.CharTwoNorm.b, TernaryPoly.CharTwoNorm.c,
    TernaryPoly.CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod2]
  norm_num

theorem projector_K2 :
    substitutionProjector (projectedSource 2) = TernaryPoly.CharTwoNorm.generator 2 := by
  unfold substitutionProjector projectedSource
  rw [sum_univ_perm3]
  simp only [sum_univ_zmod2, projectorSubstitution,
    perm_refl_0, perm_refl_1, perm_refl_2,
    perm_swap01_0, perm_swap01_1, perm_swap01_2,
    perm_swap02_0, perm_swap02_1, perm_swap02_2,
    perm_swap12_0, perm_swap12_1, perm_swap12_2,
    perm_cyc1_0, perm_cyc1_1, perm_cyc1_2,
    perm_cyc2_0, perm_cyc2_1, perm_cyc2_2,
    map_add, map_mul, map_pow, map_zero, map_one,
    MvPolynomial.bind₁_X_right, 
    Matrix.cons_val_zero, Matrix.cons_val_one, 
    cons_val_two, cons_val8_2, 
    TernaryPoly.CharTwoNorm.generator, TernaryPoly.CharTwoNorm.basis,
    TernaryPoly.CharTwoNorm.a, TernaryPoly.CharTwoNorm.b, TernaryPoly.CharTwoNorm.c,
    TernaryPoly.CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod2]
  norm_num

theorem projector_K3 :
    substitutionProjector (projectedSource 3) = TernaryPoly.CharTwoNorm.generator 3 := by
  unfold substitutionProjector projectedSource
  rw [sum_univ_perm3]
  simp only [sum_univ_zmod2, projectorSubstitution,
    perm_refl_0, perm_refl_1, perm_refl_2,
    perm_swap01_0, perm_swap01_1, perm_swap01_2,
    perm_swap02_0, perm_swap02_1, perm_swap02_2,
    perm_swap12_0, perm_swap12_1, perm_swap12_2,
    perm_cyc1_0, perm_cyc1_1, perm_cyc1_2,
    perm_cyc2_0, perm_cyc2_1, perm_cyc2_2,
    map_add, map_mul, map_pow, map_zero, map_one,
    MvPolynomial.bind₁_X_right, 
    Matrix.cons_val_zero, Matrix.cons_val_one, 
    cons_val_two, cons_val8_3, 
    TernaryPoly.CharTwoNorm.generator, TernaryPoly.CharTwoNorm.basis,
    TernaryPoly.CharTwoNorm.a, TernaryPoly.CharTwoNorm.b, TernaryPoly.CharTwoNorm.c,
    TernaryPoly.CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod2]
  norm_num

theorem projector_K4 :
    substitutionProjector (projectedSource 4) = TernaryPoly.CharTwoNorm.generator 4 := by
  unfold substitutionProjector projectedSource
  rw [sum_univ_perm3]
  simp only [sum_univ_zmod2, projectorSubstitution,
    perm_refl_0, perm_refl_1, perm_refl_2,
    perm_swap01_0, perm_swap01_1, perm_swap01_2,
    perm_swap02_0, perm_swap02_1, perm_swap02_2,
    perm_swap12_0, perm_swap12_1, perm_swap12_2,
    perm_cyc1_0, perm_cyc1_1, perm_cyc1_2,
    perm_cyc2_0, perm_cyc2_1, perm_cyc2_2,
    map_add, map_mul, map_pow, map_zero, map_one,
    MvPolynomial.bind₁_X_right, 
    Matrix.cons_val_zero, Matrix.cons_val_one, 
    cons_val_two, cons_val8_4, 
    TernaryPoly.CharTwoNorm.generator, TernaryPoly.CharTwoNorm.basis,
    TernaryPoly.CharTwoNorm.a, TernaryPoly.CharTwoNorm.b, TernaryPoly.CharTwoNorm.c,
    TernaryPoly.CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod2]
  norm_num

theorem projector_K5 :
    substitutionProjector (projectedSource 5) = TernaryPoly.CharTwoNorm.generator 5 := by
  unfold substitutionProjector projectedSource
  rw [sum_univ_perm3]
  simp only [sum_univ_zmod2, projectorSubstitution,
    perm_refl_0, perm_refl_1, perm_refl_2,
    perm_swap01_0, perm_swap01_1, perm_swap01_2,
    perm_swap02_0, perm_swap02_1, perm_swap02_2,
    perm_swap12_0, perm_swap12_1, perm_swap12_2,
    perm_cyc1_0, perm_cyc1_1, perm_cyc1_2,
    perm_cyc2_0, perm_cyc2_1, perm_cyc2_2,
    map_add, map_mul, map_pow, map_zero, map_one,
    MvPolynomial.bind₁_X_right, 
    Matrix.cons_val_zero, Matrix.cons_val_one, 
    cons_val_two, cons_val8_5, 
    TernaryPoly.CharTwoNorm.generator, TernaryPoly.CharTwoNorm.basis,
    TernaryPoly.CharTwoNorm.a, TernaryPoly.CharTwoNorm.b, TernaryPoly.CharTwoNorm.c,
    TernaryPoly.CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod2]
  norm_num

theorem projector_K6 :
    substitutionProjector (projectedSource 6) = TernaryPoly.CharTwoNorm.generator 6 := by
  unfold substitutionProjector projectedSource
  rw [sum_univ_perm3]
  simp only [sum_univ_zmod2, projectorSubstitution,
    perm_refl_0, perm_refl_1, perm_refl_2,
    perm_swap01_0, perm_swap01_1, perm_swap01_2,
    perm_swap02_0, perm_swap02_1, perm_swap02_2,
    perm_swap12_0, perm_swap12_1, perm_swap12_2,
    perm_cyc1_0, perm_cyc1_1, perm_cyc1_2,
    perm_cyc2_0, perm_cyc2_1, perm_cyc2_2,
    map_mul, map_pow, map_zero, map_one,
    MvPolynomial.bind₁_X_right, 
    Matrix.cons_val_zero, Matrix.cons_val_one, 
    cons_val_two, cons_val8_6, 
    TernaryPoly.CharTwoNorm.generator, TernaryPoly.CharTwoNorm.basis,
    TernaryPoly.CharTwoNorm.a, TernaryPoly.CharTwoNorm.b, TernaryPoly.CharTwoNorm.c,
    TernaryPoly.CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod2]
  norm_num

theorem projector_K7 :
    substitutionProjector (projectedSource 7) = TernaryPoly.CharTwoNorm.generator 7 := by
  unfold substitutionProjector projectedSource
  rw [sum_univ_perm3]
  simp only [sum_univ_zmod2, projectorSubstitution,
    perm_refl_0, perm_refl_1, perm_refl_2,
    perm_swap01_0, perm_swap01_1, perm_swap01_2,
    perm_swap02_0, perm_swap02_1, perm_swap02_2,
    perm_swap12_0, perm_swap12_1, perm_swap12_2,
    perm_cyc1_0, perm_cyc1_1, perm_cyc1_2,
    perm_cyc2_0, perm_cyc2_1, perm_cyc2_2,
    map_add, map_mul, map_pow, map_zero, map_one,
    MvPolynomial.bind₁_X_right, 
    Matrix.cons_val_zero, Matrix.cons_val_one, 
    cons_val_two, cons_val8_7,
    TernaryPoly.CharTwoNorm.generator, TernaryPoly.CharTwoNorm.basis,
    TernaryPoly.CharTwoNorm.a, TernaryPoly.CharTwoNorm.b, TernaryPoly.CharTwoNorm.c,
    TernaryPoly.CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod2]
  norm_num

end TernaryPeriodPolynomials.Argument.CharTwoKernel
