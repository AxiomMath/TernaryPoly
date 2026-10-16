module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section


/-! Proof pieces for the positive-characteristic counterexample. Feeds
`TernaryPeriodPolynomials.positive_characteristic_counterexample`.

Strategy: `Π := nonzeroLinearFormProduct p K` (product of all nonzero linear forms over `𝔽_p`
in three variables) is invariant under the cyclic permutation and under the two "norm"
substitutions defining `Solution`, because each of those substitutions acts on the finite set of
nonzero vectors `Fin 3 → ZMod p` by a coefficient-space bijection fixing `0`. Combined with
`G := symmetricTenSolution K` already being a `Solution` (via `cyclicLift_solution`), `Π * G` is
again a `Solution`. Homogeneity is additive under product. Nonvanishing is a product of
nonvanishing linear forms times a nonvanishing cyclic lift. Support positivity follows since `Π`
is divisible by `X0*X1*X2` (the three standard basis vectors are among the nonzero vectors). -/


open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument

/-- The number of nonzero vectors in `Fin 3 → ZMod p` is `p^3 - 1`. -/
theorem card_nonzero_fin3_zmod (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun v : Fin 3 → ZMod p => v ≠ 0).card = p ^ 3 - 1 := by
  have h1 : (Finset.univ.filter fun v : Fin 3 → ZMod p => v ≠ 0)
      = ({(0 : Fin 3 → ZMod p)} : Finset (Fin 3 → ZMod p))ᶜ := by
    ext v
    simp [Finset.mem_compl]
  rw [h1, Finset.card_compl, Finset.card_singleton, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- General invariance helper: if `g` substitution induces a coefficient-space bijection `T` (with
inverse `Tinv`) fixing `0` on nonzero vectors `Fin 3 → ZMod p`, then `bind₁ g` fixes
`nonzeroLinearFormProduct p K`. -/
private theorem nonzeroLinearFormProduct_invariant (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [CharP K p] (g : Fin 3 → MvPolynomial (Fin 3) K) (T Tinv : (Fin 3 → ZMod p) → (Fin 3 → ZMod p))
    (hTinvT : ∀ v, Tinv (T v) = v) (hTTinv : ∀ v, T (Tinv v) = v) (hT0 : T 0 = 0)
    (hg : ∀ v : Fin 3 → ZMod p,
        bind₁ g (∑ i : Fin 3, C (ZMod.castHom (dvd_refl p) K (v i)) * X i) =
          ∑ i : Fin 3, C (ZMod.castHom (dvd_refl p) K (T v i)) * X i) :
    bind₁ g (nonzeroLinearFormProduct p K) = nonzeroLinearFormProduct p K := by
  have hTinv0 : Tinv 0 = 0 := by have h := hTinvT 0; rwa [hT0] at h
  simp only [nonzeroLinearFormProduct, map_prod]
  refine Finset.prod_nbij' T Tinv (fun v hv => ?_) (fun v hv => ?_) (fun v _ => hTinvT v)
    (fun v _ => hTTinv v) (fun v _ => hg v)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    intro h0
    exact hv (by rw [← hTinvT v, h0, hTinv0])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    intro h0
    exact hv (by rw [← hTTinv v, h0, hT0])

/-- `Π` is invariant under the cyclic substitution `![X1,X2,X0]`. -/
theorem nonzeroLinearFormProduct_cyclic (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [CharP K p] : bind₁ (![X 1, X 2, X 0] : Fin 3 → MvPolynomial (Fin 3) K)
      (nonzeroLinearFormProduct p K) = nonzeroLinearFormProduct p K :=
  nonzeroLinearFormProduct_invariant p K _ (fun v => ![v 2, v 0, v 1]) (fun w => ![w 1, w 2, w 0])
    (fun v => by funext i; fin_cases i <;> simp)
    (fun v => by funext i; fin_cases i <;> simp)
    (by funext i; fin_cases i <;> simp)
    (fun v => by
      simp only [Fin.sum_univ_three, map_add, map_mul, bind₁_X_right, bind₁_C_right,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      ring)

/-- `Π` is invariant under the first norm substitution `![-X1,X0-X1,X2]`. -/
theorem nonzeroLinearFormProduct_normA (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    bind₁ (![-X 1, X 0 - X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) K)
      (nonzeroLinearFormProduct p K) = nonzeroLinearFormProduct p K :=
  nonzeroLinearFormProduct_invariant p K _
    (fun v => ![v 1, -(v 0 + v 1), v 2]) (fun w => ![-(w 0 + w 1), w 0, w 2])
    (fun v => by funext i; fin_cases i <;> simp)
    (fun v => by funext i; fin_cases i <;> simp)
    (by funext i; fin_cases i <;> simp)
    (fun v => by
      simp only [Fin.sum_univ_three, map_add, map_mul, map_neg, bind₁_X_right,
        bind₁_C_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      ring)

/-- `Π` is invariant under the second norm substitution `![X1-X0,-X0,X2]`. -/
theorem nonzeroLinearFormProduct_normA2 (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    bind₁ (![X 1 - X 0, -X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) K)
      (nonzeroLinearFormProduct p K) = nonzeroLinearFormProduct p K :=
  nonzeroLinearFormProduct_invariant p K _
    (fun v => ![-(v 0 + v 1), v 0, v 2]) (fun w => ![w 1, -(w 0 + w 1), w 2])
    (fun v => by funext i; fin_cases i <;> simp)
    (fun v => by funext i; fin_cases i <;> simp)
    (by funext i; fin_cases i <;> simp)
    (fun v => by
      simp only [Fin.sum_univ_three, map_add, map_mul, map_neg, bind₁_X_right,
        bind₁_C_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      ring)

/-- `4` as a constant polynomial, for `Fin 2`-indexed `MvPolynomial`. -/
theorem four_eq_C_fin2 {R : Type*} [CommRing R] :
    (4 : MvPolynomial (Fin 2) R) = C (4 : R) := by
  rw [map_ofNat (MvPolynomial.C (σ := Fin 2)) 4]

/-- `symmetricTenPeriod` is homogeneous of degree ten. -/
theorem symmetricTenPeriod_isHomogeneous_pc (K) [CommRing K] :
    (symmetricTenPeriod K).IsHomogeneous 10 := by
  have h0 := MvPolynomial.isHomogeneous_X K (0 : Fin 2)
  have h1 := MvPolynomial.isHomogeneous_X K (1 : Fin 2)
  simp only [symmetricTenPeriod]
  have hA : (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) K).IsHomogeneous 2 := by
    have hh := (h0.pow 2).sub (h1.pow 2); norm_num at hh; exact hh
  have hA2 : ((X 0 ^ 2 - X 1 ^ 2) ^ 2 : MvPolynomial (Fin 2) K).IsHomogeneous 4 := by
    have hh := hA.pow 2; norm_num at hh; exact hh
  have hB : (X 0 ^ 2 - 4 * X 1 ^ 2 : MvPolynomial (Fin 2) K).IsHomogeneous 2 := by
    rw [four_eq_C_fin2]
    have hh := (h0.pow 2).sub ((MvPolynomial.isHomogeneous_C (Fin 2) (4 : K)).mul (h1.pow 2))
    norm_num at hh; exact hh
  have hC : (4 * X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) K).IsHomogeneous 2 := by
    rw [four_eq_C_fin2]
    have hh := ((MvPolynomial.isHomogeneous_C (Fin 2) (4 : K)).mul (h0.pow 2)).sub (h1.pow 2)
    norm_num at hh; exact hh
  have hfinal := ((((h0.mul h1).mul hA2).mul hB).mul hC)
  norm_num at hfinal
  exact hfinal

/-- `symmetricTenPeriod` is nonzero over any field. -/
theorem symmetricTenPeriod_ne_zero {K : Type*} [Field K] : symmetricTenPeriod K ≠ 0 := by
  have e1 : (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) K) ≠ 0 := by
    intro h
    have h' := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → K)) h
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X,
      map_zero, Matrix.cons_val_zero, Matrix.cons_val_one] at h'
    norm_num at h'
  have e2 : (X 0 ^ 2 - 4 * X 1 ^ 2 : MvPolynomial (Fin 2) K) ≠ 0 := by
    intro h
    have h' := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → K)) h
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, map_ofNat, map_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h'
    norm_num at h'
  have e3 : (4 * X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) K) ≠ 0 := by
    intro h
    have h' := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → K)) h
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, map_ofNat, map_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h'
    norm_num at h'
  simp only [symmetricTenPeriod]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1))
    (pow_ne_zero 2 e1)) e2) e3

/-- `symmetricTenPeriod` satisfies all four period relations, over any commutative ring. -/
theorem symmetricTenPeriod_periodRelations_pc (K : Type*) [CommRing K] :
    PeriodRelations (symmetricTenPeriod K) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, bind₁_X_right, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring1
  · simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, bind₁_X_right, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring1
  · simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, map_ofNat,
      bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring1
  · simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, map_ofNat,
      bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring1

/-- `symmetricTenSolution` is nonzero over any field. -/
theorem symmetricTenSolution_ne_zero (K : Type*) [Field K] : symmetricTenSolution K ≠ 0 := by
  simp only [symmetricTenSolution]
  intro h
  have hrest := congrArg restriction h
  rw [restriction_cyclicLift (symmetricTenPeriod_periodRelations_pc K)] at hrest
  simp only [restriction, map_zero] at hrest
  exact symmetricTenPeriod_ne_zero hrest

/-- `symmetricTenSolution` is homogeneous of degree ten, via the cyclic lift of a degree-ten
binary period. -/
theorem symmetricTenSolution_isHomogeneous (K : Type*) [CommRing K] :
    (symmetricTenSolution K).IsHomogeneous 10 :=
  cyclicLift_homogeneous (symmetricTenPeriod_isHomogeneous_pc K)

/-- `symmetricTenSolution` is a `Solution`, via the cyclic lift of a period-relation-satisfying
binary period. -/
theorem symmetricTenSolution_solution (K : Type*) [CommRing K] : Solution (symmetricTenSolution K) :=
  cyclicLift_solution (symmetricTenPeriod_periodRelations_pc K)

/-- A nonzero linear form (indexed by a nonzero vector `v : Fin 3 → ZMod p`) is nonzero as a
polynomial. -/
private theorem linearForm_ne_zero (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (v : Fin 3 → ZMod p) (hv : v ≠ 0) :
    (∑ i : Fin 3, C (ZMod.castHom (dvd_refl p) K (v i)) * X i : MvPolynomial (Fin 3) K) ≠ 0 := by
  intro h
  apply hv
  have h0 := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → K)) h
  have h1 := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → K)) h
  have h2 := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → K)) h
  simp only [Fin.sum_univ_three, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, map_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    mul_zero, mul_one, add_zero, zero_add] at h0 h1 h2
  funext i
  fin_cases i
  · exact (ZMod.castHom_injective K) (by simpa using h0)
  · exact (ZMod.castHom_injective K) (by simpa using h1)
  · exact (ZMod.castHom_injective K) (by simpa using h2)

/-- `Π = nonzeroLinearFormProduct p K` is nonzero: it is a product of nonzero linear forms. -/
theorem nonzeroLinearFormProduct_ne_zero (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [CharP K p] : nonzeroLinearFormProduct p K ≠ 0 := by
  simp only [nonzeroLinearFormProduct]
  exact Finset.prod_ne_zero_iff.mpr
    (fun v hv => linearForm_ne_zero p K v (Finset.mem_filter.mp hv).2)

/-- Each linear form `L(v) = ∑ C(cast(v i)) * X i` is homogeneous of degree one. -/
private theorem linearForm_isHomogeneous (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [CharP K p] (v : Fin 3 → ZMod p) :
    (∑ i : Fin 3, C (ZMod.castHom (dvd_refl p) K (v i)) * X i :
      MvPolynomial (Fin 3) K).IsHomogeneous 1 := by
  rw [Fin.sum_univ_three]
  have h0 := MvPolynomial.isHomogeneous_X K (0 : Fin 3)
  have h1 := MvPolynomial.isHomogeneous_X K (1 : Fin 3)
  have h2 := MvPolynomial.isHomogeneous_X K (2 : Fin 3)
  have hh := (((MvPolynomial.isHomogeneous_C (Fin 3) (ZMod.castHom (dvd_refl p) K (v 0))).mul
      h0).add
    ((MvPolynomial.isHomogeneous_C (Fin 3) (ZMod.castHom (dvd_refl p) K (v 1))).mul h1)).add
    ((MvPolynomial.isHomogeneous_C (Fin 3) (ZMod.castHom (dvd_refl p) K (v 2))).mul h2)
  norm_num at hh
  exact hh

/-- `Π = nonzeroLinearFormProduct p K` is homogeneous of degree `p^3 - 1`: it is a product of
`p^3-1` linear forms, each homogeneous of degree one. -/
theorem nonzeroLinearFormProduct_isHomogeneous (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [CharP K p] : (nonzeroLinearFormProduct p K).IsHomogeneous (p ^ 3 - 1) := by
  simp only [nonzeroLinearFormProduct]
  rw [← card_nonzero_fin3_zmod p, Finset.card_eq_sum_ones]
  exact MvPolynomial.IsHomogeneous.prod _ _ _ (fun v _ => linearForm_isHomogeneous p K v)

/-- `Π = nonzeroLinearFormProduct p K` factors as `X0*X1*X2*rest`: the three standard basis
vectors `(1,0,0), (0,1,0), (0,0,1)` are among the nonzero vectors, contributing `X0,X1,X2`
themselves as three of `Π`'s linear-form factors. -/
theorem nonzeroLinearFormProduct_factor (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [CharP K p] :
    ∃ rest : MvPolynomial (Fin 3) K, nonzeroLinearFormProduct p K = X 0 * X 1 * X 2 * rest := by
  have he0 : (![1, 0, 0] : Fin 3 → ZMod p) ∈
      Finset.univ.filter fun v : Fin 3 → ZMod p => v ≠ 0 := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h; have h0 := congrFun h 0; simp at h0
  have he1 : (![0, 1, 0] : Fin 3 → ZMod p) ∈
      (Finset.univ.filter fun v : Fin 3 → ZMod p => v ≠ 0).erase ![1, 0, 0] := by
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h; have h0 := congrFun h 0; simp at h0
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h; have h1 := congrFun h 1; simp at h1
  have he2 : (![0, 0, 1] : Fin 3 → ZMod p) ∈
      ((Finset.univ.filter fun v : Fin 3 → ZMod p => v ≠ 0).erase ![1, 0, 0]).erase
        ![0, 1, 0] := by
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, ?_⟩
    · intro h; have h1 := congrFun h 1; simp at h1
    · intro h; have h0 := congrFun h 0; simp at h0
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h; have h2 := congrFun h 2; simp at h2
  refine ⟨(∏ v ∈ Finset.erase (Finset.erase (Finset.erase
      (Finset.univ.filter (fun v : Fin 3 → ZMod p => v ≠ 0)) ![1, 0, 0]) ![0, 1, 0])
      ![0, 0, 1], ∑ i : Fin 3, C (ZMod.castHom (dvd_refl p) K (v i)) * X i), ?_⟩
  simp only [nonzeroLinearFormProduct]
  rw [← Finset.mul_prod_erase _ _ he0, ← Finset.mul_prod_erase _ _ he1,
    ← Finset.mul_prod_erase _ _ he2]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_one, map_zero, zero_mul, add_zero,
    zero_add, one_mul]
  ring

/-- `Π * G` is homogeneous of degree `p^3 + 9`. -/
theorem positiveChar_isHomogeneous (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    (nonzeroLinearFormProduct p K * symmetricTenSolution K).IsHomogeneous (p ^ 3 + 9) := by
  have hProd := nonzeroLinearFormProduct_isHomogeneous p K
  have hG : (symmetricTenSolution K).IsHomogeneous 10 := symmetricTenSolution_isHomogeneous K
  have hh := hProd.mul hG
  have hp1 : 1 ≤ p ^ 3 := Nat.one_le_pow 3 p (Fact.out (p := p.Prime)).pos
  have heq : p ^ 3 - 1 + 10 = p ^ 3 + 9 := by omega
  rwa [heq] at hh

/-- `Π * G` is a `Solution`. -/
theorem positiveChar_solution (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    Solution (nonzeroLinearFormProduct p K * symmetricTenSolution K) := by
  have hG : Solution (symmetricTenSolution K) := symmetricTenSolution_solution K
  constructor
  · rw [map_mul, nonzeroLinearFormProduct_cyclic, hG.cyclic]
  · rw [map_mul, map_mul, nonzeroLinearFormProduct_normA, nonzeroLinearFormProduct_normA2]
    linear_combination nonzeroLinearFormProduct p K * hG.norm

/-- Every monomial of `Π * G` has all three exponents positive: `Π` is divisible by `X0*X1*X2`,
and multiplying by `X0`, then `X1`, then `X2` shifts every exponent of the remaining factor up by
one in each respective coordinate. -/
theorem positiveChar_support_pos (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    ∀ d ∈ (nonzeroLinearFormProduct p K * symmetricTenSolution K).support, ∀ i, 0 < d i := by
  obtain ⟨rest, hrest⟩ := nonzeroLinearFormProduct_factor p K
  intro d hd i
  rw [hrest, mul_assoc, mul_assoc, mul_assoc, MvPolynomial.support_X_mul, Finset.mem_map] at hd
  obtain ⟨d1, hd1, he1⟩ := hd
  rw [MvPolynomial.support_X_mul, Finset.mem_map] at hd1
  obtain ⟨d2, hd2, he2⟩ := hd1
  rw [MvPolynomial.support_X_mul, Finset.mem_map] at hd2
  obtain ⟨d3, -, he3⟩ := hd2
  rw [addLeftEmbedding_apply] at he1 he2 he3
  subst he1; subst he2; subst he3
  fin_cases i <;> simp [Finsupp.add_apply]

/-- `Π * G` is not `Pairwise`: it is nonzero, and every monomial in its (nonempty) support has
all-positive exponents, directly contradicting the defining property of `Pairwise`. -/
theorem positiveChar_not_pairwise (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (hne : nonzeroLinearFormProduct p K * symmetricTenSolution K ≠ 0)
    (hpos : ∀ d ∈ (nonzeroLinearFormProduct p K * symmetricTenSolution K).support, ∀ i, 0 < d i) :
    ¬ Pairwise (nonzeroLinearFormProduct p K * symmetricTenSolution K) := by
  intro hP
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
  exact (MvPolynomial.mem_support_iff.mp hd) (hP d (hpos d hd))

/-- The full assembled positive-characteristic counterexample. -/
theorem positiveChar_assembled (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    Solution (nonzeroLinearFormProduct p K * symmetricTenSolution K) ∧
    nonzeroLinearFormProduct p K * symmetricTenSolution K ≠ 0 ∧
    (nonzeroLinearFormProduct p K * symmetricTenSolution K).IsHomogeneous (p ^ 3 + 9) ∧
    (∀ d ∈ (nonzeroLinearFormProduct p K * symmetricTenSolution K).support, ∀ i, 0 < d i) ∧
    ¬ Pairwise (nonzeroLinearFormProduct p K * symmetricTenSolution K) := by
  have hne := mul_ne_zero (nonzeroLinearFormProduct_ne_zero p K) (symmetricTenSolution_ne_zero K)
  have hpos := positiveChar_support_pos p K
  exact ⟨positiveChar_solution p K, hne, positiveChar_isHomogeneous p K, hpos,
    positiveChar_not_pairwise p K hne hpos⟩

end TernaryPeriodPolynomials.Argument
