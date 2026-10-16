module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Polynomial
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Homogeneous

@[expose] public section


/-! Identify the new literal Bernoulli formula with the original rational Todd
scalar. This is a proved comparison of formulas, not another external input. -/

noncomputable section
namespace TernaryPeriodPolynomials
open MvPolynomial TernaryPoly

private theorem finSucc_iterate (k : ℕ) (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (((pderiv 0 : TernaryPolynomial → TernaryPolynomial)^[k]) f) =
      ((Polynomial.derivative : Polynomial (MvPolynomial (Fin 2) ℚ) → _)^[k])
        (finSuccEquiv ℚ 2 f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', finSuccEquiv_pderiv_zero, ih]

/-- Ordinary and Hasse differentiation give the same finite Bernoulli sum. -/
theorem iterate_pderiv_eq_factorial_hasse (k : ℕ) (f : TernaryPolynomial) :
    ((pderiv 0 : TernaryPolynomial → TernaryPolynomial)^[k]) f =
      (k.factorial : ℚ) • ternaryHasse k f := by
  apply (finSuccEquiv ℚ 2).injective
  rw [finSucc_iterate, map_smul, ternaryHasse, AlgEquiv.apply_symm_apply]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv
    (R := MvPolynomial (Fin 2) ℚ) (k := k)) (finSuccEquiv ℚ 2 f)
  simpa only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul] using h.symm

/-- The original Todd operator expressed with ordinary partial derivatives. -/
theorem ternaryTodd_eq_derivative_sum {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (u : MvPolynomial (Fin 2) ℚ) :
    ternaryTodd u f = ∑ k ∈ Finset.range (n + 1),
      MvPolynomial.C (bernoulli k / (k.factorial : ℚ)) *
        (-(rename Fin.succ u)) ^ k *
          ((pderiv 0 : TernaryPolynomial → TernaryPolynomial)^[k]) f := by
  rw [ternaryTodd_eq_hasse_sum hf u]
  apply Finset.sum_congr rfl
  intro k _
  rw [iterate_pderiv_eq_factorial_hasse]
  have hfac : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp only [map_pow, map_neg, smul_eq_C_mul]
  rw [← mul_assoc, mul_right_comm _ _ (MvPolynomial.C (k.factorial : ℚ)),
    ← map_mul, div_mul_cancel₀ _ hfac]

/-- Coefficient extension commutes with every iterate of the first derivative. -/
theorem map_iterate_pderiv (k : ℕ) (f : TernaryPolynomial) :
    MvPolynomial.map (algebraMap ℚ ℂ)
      (((pderiv 0 : TernaryPolynomial → TernaryPolynomial)^[k]) f) =
    ((pderiv 0 : GeneralEisenstein.Poly → GeneralEisenstein.Poly)^[k])
      (MvPolynomial.map (algebraMap ℚ ℂ) f) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ← pderiv_map, ih]

/-- Exact compatibility of the finite Bernoulli operator under ℚ → ℂ. -/
theorem map_ternaryTodd {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (u : MvPolynomial (Fin 2) ℚ) :
    MvPolynomial.map (algebraMap ℚ ℂ) (ternaryTodd u f) =
      GeneralEisenstein.bernoulliOperator n
        (MvPolynomial.map (algebraMap ℚ ℂ) (rename Fin.succ u))
        (MvPolynomial.map (algebraMap ℚ ℂ) f) := by
  rw [ternaryTodd_eq_derivative_sum hf u, GeneralEisenstein.bernoulliOperator]
  simp only [map_sum, map_mul, map_pow, map_neg, map_C, map_iterate_pderiv]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  simp

private theorem map_substitute3 (f a b c : TernaryPolynomial) :
    MvPolynomial.map (algebraMap ℚ ℂ) (substitute3 f a b c) =
      bind₁ ![MvPolynomial.map (algebraMap ℚ ℂ) a,
        MvPolynomial.map (algebraMap ℚ ℂ) b,
        MvPolynomial.map (algebraMap ℚ ℂ) c]
        (MvPolynomial.map (algebraMap ℚ ℂ) f) := by
  rw [substitute3, map_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- Equality of the new obstruction with the mapped original Todd expression. -/
theorem map_symmetricTodd {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    MvPolynomial.map (algebraMap ℚ ℂ) (symmetricTodd f) =
      GeneralEisenstein.bernoulliObstruction
        (⟨MvPolynomial.map (algebraMap ℚ ℂ) f, hf.map (algebraMap ℚ ℂ)⟩ :
          GeneralEisenstein.HomogeneousPoly n) := by
  rw [symmetricTodd, map_sub, map_mul, map_mul,
    map_ternaryTodd (symmetricFrame1_homogeneous hf),
    map_ternaryTodd (symmetricFrame2_homogeneous hf)]
  simp only [map_X, rename_X]
  simp only [symmetricFrame1, symmetricFrame2, map_sub, map_add,
    map_substitute3, map_X, map_sub, map_mul, map_neg, map_ofNat,
    GeneralEisenstein.bernoulliObstruction]
  rfl

/-- The two generating symmetries imply every permutation symmetry. -/
theorem all_permutations {f : TernaryPolynomial} (hc : TernaryPoly.C f = f) (hs : S f = f)
    (σ : Equiv.Perm (Fin 3)) : bind₁ (fun i => X (σ i)) f = f := by
  have h120 := SymmetricCertificate.value_cyclic hc (X 0 : TernaryPolynomial) (X 1) (X 2)
  have h10 := SymmetricCertificate.value_swap hs (X 0 : TernaryPolynomial) (X 1) (X 2)
  have h201 := (SymmetricCertificate.value_cyclic hc (X 1 : TernaryPolynomial) (X 2) (X 0)).trans h120
  have h021 := (SymmetricCertificate.value_cyclic hc (X 1 : TernaryPolynomial) (X 0) (X 2)).trans h10
  have h210 := (SymmetricCertificate.value_swap hs (X 1 : TernaryPolynomial) (X 2) (X 0)).trans h120
  have hi : SymmetricCertificate.value f (X 0) (X 1) (X 2) = f := by
    have hv : (![X 0, X 1, X 2] : Fin 3 → TernaryPolynomial) = X := by
      funext i
      fin_cases i <;> rfl
    simp only [SymmetricCertificate.value, hv, bind₁_X_left, AlgHom.id_apply]
  rw [hi] at h10 h120 h201 h021 h210
  have h01 : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h)
  have h02 : σ 0 ≠ σ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (σ.injective h)
  have h12 : σ 1 ≠ σ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h)
  have hv : (fun i => X (σ i) : Fin 3 → TernaryPolynomial) =
      ![X (σ 0), X (σ 1), X (σ 2)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  generalize h0 : σ 0 = i0 at *
  generalize h1 : σ 1 = i1 at *
  generalize h2 : σ 2 = i2 at *
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
    simp_all [SymmetricCertificate.value]

/-- The rational solution maps to exactly the new symmetric-solution predicate. -/
theorem mapped_symmetricSolution {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hrel : PeriodRelations f) (hs : S f = f) :
    GeneralEisenstein.SymmetricSolution
      (⟨MvPolynomial.map (algebraMap ℚ ℂ) f, hf.map (algebraMap ℚ ℂ)⟩ :
        GeneralEisenstein.HomogeneousPoly n) := by
  constructor
  · intro σ
    have h := congrArg (MvPolynomial.map (algebraMap ℚ ℂ)) (all_permutations hrel.1 hs σ)
    simpa only [map_bind₁, map_X] using h
  · have h := congrArg (MvPolynomial.map (algebraMap ℚ ℂ)) hrel.2
    change MvPolynomial.map (algebraMap ℚ ℂ)
      (f + substitute3 f (-X 1) (X 0 - X 1) (X 2) +
        substitute3 f (X 1 - X 0) (-X 0) (X 2)) =
          MvPolynomial.map (algebraMap ℚ ℂ) 0 at h
    simpa only [map_add, map_zero, map_substitute3, map_X, map_neg, map_sub] using h

end TernaryPeriodPolynomials
