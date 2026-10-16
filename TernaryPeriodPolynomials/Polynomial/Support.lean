module

public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange
public import TernaryPeriodPolynomials.Polynomial.OriginalSupportBridge
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Group.Torsion

@[expose] public section


/-! # Support over arbitrary commutative rational algebras

The deep input is the supplied rational support theorem. Exact natural
scalar extension transports it to rings with nilpotents as well as fields.
-/

open MvPolynomial TensorProduct
noncomputable section
namespace TernaryPoly.Paper
variable {R : Type*} [CommRing R]

@[simp] theorem pairwise_zero : Pairwise (0 : Ternary R) := by
  intro d hd
  rfl

theorem Pairwise.add {f g : Ternary R}
    (hf : Pairwise f) (hg : Pairwise g) : Pairwise (f + g) := by
  intro d hd
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf d hd, hg d hd, add_zero]

theorem Pairwise.neg {f : Ternary R}
    (hf : Pairwise f) : Pairwise (-f) := by
  intro d hd
  simp only [coeff_neg, hf d hd, neg_zero]

theorem Pairwise.smul {f : Ternary R}
    (hf : Pairwise f) (a : R) : Pairwise (a • f) := by
  intro d hd
  simp only [coeff_smul, hf d hd, smul_zero]

theorem pairwise_sum {ι : Type*} (s : Finset ι)
    (f : ι → Ternary R) (hf : ∀ i ∈ s, Pairwise (f i)) :
    Pairwise (∑ i ∈ s, f i) := by
  intro d hd
  simp only [coeff_sum]
  exact Finset.sum_eq_zero fun i hi => hf i hi d hd

private def HasPairwiseRepresentation (f : Ternary R) : Prop :=
  ∃ p q r : Binary R,
    f = rename (![0, 1] : Fin 2 → Fin 3) p +
      rename (![1, 2] : Fin 2 → Fin 3) q +
      rename (![0, 2] : Fin 2 → Fin 3) r

private theorem representation_zero : HasPairwiseRepresentation (0 : Ternary R) := by
  exact ⟨0, 0, 0, by simp⟩

private theorem representation_add {f g : Ternary R}
    (hf : HasPairwiseRepresentation f) (hg : HasPairwiseRepresentation g) :
    HasPairwiseRepresentation (f + g) := by
  obtain ⟨p, q, r, rfl⟩ := hf
  obtain ⟨p', q', r', rfl⟩ := hg
  exact ⟨p + p', q + q', r + r', by simp only [map_add]; ac_rfl⟩

private theorem monomial_representation (d : Fin 3 →₀ ℕ) (a : R)
    (hd : ∃ i, d i = 0) : HasPairwiseRepresentation (monomial d a) := by
  classical
  by_cases ha : a = 0
  · subst a
    simpa using representation_zero
  obtain ⟨i, hi⟩ := hd
  fin_cases i
  · obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range
      (monomial d a) (![1, 2] : Fin 2 → Fin 3) (by decide) (by
        rw [vars_monomial ha]
        intro j hj
        have hj' : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
        fin_cases j
        · exact (hj' hi).elim
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩)
    exact ⟨0, q, 0, by simpa using hq.symm⟩
  · obtain ⟨r, hr⟩ := exists_rename_eq_of_vars_subset_range
      (monomial d a) (![0, 2] : Fin 2 → Fin 3) (by decide) (by
        rw [vars_monomial ha]
        intro j hj
        have hj' : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
        fin_cases j
        · exact ⟨0, rfl⟩
        · exact (hj' hi).elim
        · exact ⟨1, rfl⟩)
    exact ⟨0, 0, r, by simpa using hr.symm⟩
  · obtain ⟨p, hp⟩ := exists_rename_eq_of_vars_subset_range
      (monomial d a) (![0, 1] : Fin 2 → Fin 3) (by decide) (by
        rw [vars_monomial ha]
        intro j hj
        have hj' : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
        fin_cases j
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact (hj' hi).elim)
    exact ⟨p, 0, 0, by simpa using hp.symm⟩

theorem Pairwise.exists_rename {f : Ternary R} (hf : Pairwise f) :
    ∃ p q r : Binary R,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![0, 2] : Fin 2 → Fin 3) r := by
  classical
  change HasPairwiseRepresentation f
  rw [← support_sum_monomial_coeff f]
  apply Finset.sum_induction
  · intro p q hp hq
    exact representation_add hp hq
  · exact representation_zero
  · intro d hd
    apply monomial_representation
    by_contra h
    have hall : ∀ i, 0 < d i := by
      intro i
      exact Nat.pos_of_ne_zero fun hi => h ⟨i, hi⟩
    exact (mem_support_iff.mp hd) (hf d hall)

private theorem pairwise_rename_of_omits (ι : Fin 2 → Fin 3) (i : Fin 3)
    (hi : i ∉ Set.range ι) (p : Binary R) : Pairwise (rename ι p) := by
  intro d hd
  apply coeff_rename_eq_zero
  intro u hu
  have hz : d i = 0 := by
    rw [← hu]
    exact Finsupp.mapDomain_of_notMem_range u i hi
  exact (Nat.ne_of_gt (hd i) hz).elim

theorem pairwise_iff_exists_rename (f : Ternary R) :
    Pairwise f ↔ ∃ p q r : Binary R,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![0, 2] : Fin 2 → Fin 3) r := by
  constructor
  · exact Pairwise.exists_rename
  · rintro ⟨p, q, r, rfl⟩
    exact ((pairwise_rename_of_omits _ 2 (by decide) p).add
      (pairwise_rename_of_omits _ 0 (by decide) q)).add
      (pairwise_rename_of_omits _ 1 (by decide) r)


/-- Coefficient extension preserves the omission of fully mixed monomials. -/
theorem Pairwise.map {A : Type*} [CommRing A] {f : Ternary R}
    (hf : Pairwise f) (φ : R →+* A) : Pairwise (map φ f) := by
  intro d hd
  rw [coeff_map, hf d hd, map_zero]

/-- Fully mixed support is excluded over every commutative `ℚ`-algebra. -/
theorem solution_pairwise [Algebra ℚ R] (f : Ternary R) (hf : Solution f) : Pairwise f := by
  obtain ⟨t, ht⟩ := (solutions_baseChangeEquiv R).surjective ⟨f, hf⟩
  have h : ∀ t : R ⊗[ℚ] solutions ℚ,
      Pairwise (solutions_baseChangeEquiv R t).val := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a g =>
      rw [solutions_baseChangeEquiv_tmul]
      exact ((rational_solution_pairwise g.val g.property).map (algebraMap ℚ R)).smul a
    | add a b ha hb =>
      simpa only [map_add, AddMemClass.coe_add] using ha.add hb
  simpa only [ht] using h t

/-- The pairwise decomposition holds over every commutative `ℚ`-algebra. -/
theorem solution_exists_pairwise [Algebra ℚ R] (f : Ternary R) (hf : Solution f) :
    ∃ p q r : Binary R,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![0, 2] : Fin 2 → Fin 3) r := by
  exact (solution_pairwise f hf).exists_rename

/-- The decomposition in the cyclic coordinate order used in the paper. -/
theorem Pairwise.exists_cyclic_rename {f : Ternary R} (hf : Pairwise f) :
    ∃ p q r : Binary R,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q + rename (![2, 0] : Fin 2 → Fin 3) r := by
  obtain ⟨p, q, r, h⟩ := hf.exists_rename
  refine ⟨p, q, rename (![1, 0] : Fin 2 → Fin 2) r, ?_⟩
  have hr : rename (![2, 0] : Fin 2 → Fin 3) (rename (![1, 0] : Fin 2 → Fin 2) r) =
      rename (![0, 2] : Fin 2 → Fin 3) r := by
    rw [rename_rename]
    have hv : (![2, 0] : Fin 2 → Fin 3) ∘ (![1, 0] : Fin 2 → Fin 2) = ![0, 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
  rw [hr]
  exact h

/-- The paper's support theorem, explicitly quantified over every characteristic-zero field. -/
theorem ternary_period_polynomial_pairwise {F : Type*} [Field F] [CharZero F]
    (f : Ternary F)
    (hcyclic : bind₁ ![X 1, X 2, X 0] f = f)
    (hnorm : f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) :
    ∃ p q r : Binary F,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q + rename (![2, 0] : Fin 2 → Fin 3) r :=
  (solution_pairwise f ⟨hcyclic, hnorm⟩).exists_cyclic_rename

/-- The mixed derivative selects exactly the fully mixed monomials. -/
theorem coeff_mixed_derivative (f : Ternary R) (d : Fin 3 →₀ ℕ) :
    (pderiv 0 (pderiv 1 (pderiv 2 f))).coeff d =
      f.coeff (d + Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) *
        ((d 2 : R) + 1) * ((d 1 : R) + 1) * ((d 0 : R) + 1) := by
  simp [coeff_pderiv]

/-- Support and mixed-derivative vanishing agree over every torsion-free coefficient ring. -/
theorem pairwise_iff_mixed_derivative_eq_zero [IsAddTorsionFree R] (f : Ternary R) :
    Pairwise f ↔ pderiv 0 (pderiv 1 (pderiv 2 f)) = 0 := by
  constructor
  · intro hf
    ext d
    rw [coeff_mixed_derivative, hf]
    · simp
    · intro i
      fin_cases i <;> simp
  · intro hf d hd
    let m : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => d i - 1)
    have hm : m + Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 = d := by
      ext i
      fin_cases i <;> simp [m, Nat.sub_add_cancel (hd _)]
    have hc := congrArg (·.coeff m) hf
    rw [coeff_mixed_derivative, hm, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    have cancel (a : R) (n : ℕ) (h : a * ((n : R) + 1) = 0) : a = 0 := by
      apply IsAddTorsionFree.nsmul_right_injective (Nat.succ_ne_zero n)
      simpa [nsmul_eq_mul, mul_comm, Nat.cast_add, Nat.cast_one] using h
    exact cancel _ _ (cancel _ _ (cancel _ _ hc))

/-- In particular, solutions over characteristic-zero fields have zero mixed third derivative. -/
theorem solution_mixed_derivative_eq_zero [Algebra ℚ R]
    (f : Ternary R) (hf : Solution f) : pderiv 0 (pderiv 1 (pderiv 2 f)) = 0 :=
  (pairwise_iff_mixed_derivative_eq_zero f).mp (solution_pairwise f hf)

end TernaryPoly.Paper
