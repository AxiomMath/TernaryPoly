module

public import TernaryPeriodPolynomials.SymmetricSolution.NormalDescent

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- A finite tower in odd degree, with genuine polynomial quotients and exact binary degrees. -/
theorem symmetric_odd_period_tower {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hJ : symmetricTodd f=0) :
    ∃ k : ℕ, ∃ q : Fin k → MvPolynomial (Fin 2) ℚ, ∃ l : Fin k → TernaryPolynomial,
      (∀ i, SymmetricBinaryPeriodRelations (q i) ∧
        (q i).IsHomogeneous (n+1-2*(i:ℕ)) ∧
        binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i) ∧
      f=∑ i : Fin k, (X 0+X 1+X 2)^(2*(i:ℕ))*l i := by
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    obtain ⟨l,g,hfg,hl,hgh,hgc,hgs,hgj,hge⟩ := symmetric_normal_step hf hodd hc hs hJ
    have hq := extractedSymmetricBinaryPeriod_relations hf hodd hc hs hJ
    have hqh : (extractedSymmetricBinaryPeriod n f).IsHomogeneous (n+1) :=
      symmetricBinaryPeriodPrimitive_isHomogeneous hf hodd
    by_cases hg0 : g=0
    · refine ⟨1,(fun _ => extractedSymmetricBinaryPeriod n f),(fun _ => l),?_,?_⟩
      · intro i
        have hi : i=0 := Subsingleton.elim _ _
        subst i
        exact ⟨hq,by simpa using hqh,hl⟩
      · simpa [hg0] using hfg
    · have hn2 := hge hg0
      obtain ⟨k,q,ls,hqs,he⟩ := ih (n-2) (by omega) hgh
        (Nat.Odd.sub_even hn2 hodd (by decide : Even (2 : ℕ))) hgc hgs hgj
      refine ⟨k+1,Fin.cons (extractedSymmetricBinaryPeriod n f) q,Fin.cons l ls,?_,?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ⟨hq,by simpa using hqh,hl⟩
        · obtain ⟨hqr,hqd,hql⟩ := hqs j
          refine ⟨hqr,?_,hql⟩
          simpa only [Fin.cons_succ,Fin.val_succ,
            show n-2+1-2*(j:ℕ)=n+1-2*((j:ℕ)+1) by omega] using hqd
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ,Fin.val_zero,Fin.val_succ,
          Nat.mul_zero,pow_zero,one_mul]
        rw [hfg,he]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_assoc,← pow_add]
        congr 2
        omega


/-- Positive even-degree norm solutions in the whole Todd kernel have a polynomial numerator tower. -/
theorem symmetric_even_period_tower {f : TernaryPolynomial} {n : ℕ}
    (hn : 0<n) (he : Even n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ k : ℕ, ∃ q : Fin k → MvPolynomial (Fin 2) ℚ,
      (∀ i, SymmetricBinaryPeriodRelations (q i) ∧
        (q i).IsHomogeneous (n-2*(i:ℕ))) ∧
      f=∑ i : Fin k, (X 0+X 1+X 2)^(2*(i:ℕ))*binaryPeriodLift (q i) := by
  obtain ⟨v,hv⟩ : (X 0+X 1+X 2 : TernaryPolynomial) ∣ f :=
    dvd_trans (dvd_mul_right _ _)
      (homogeneous_symmetric_total_pair_sum_product_dvd hrel hs hf he)
  have hvh : v.IsHomogeneous (n-1) :=
    isHomogeneous_quotient coordinate_sum_isHomogeneous coordinate_sum_ne_zero (by rwa [← hv])
  have hvc : C v=v := cyclic_of_coordinate_sum_pow_mul 1 (by simpa [pow_one,← hv] using hrel.1)
  have hvs : S v=v := symmetric_of_coordinate_sum_pow_mul 1 (by simpa [pow_one,← hv] using hs)
  have hvJ : symmetricTodd v=0 :=
    symmetricTodd_of_coordinate_sum_pow_mul 1 (by simpa [pow_one,← hv] using hJ)
  obtain ⟨k,q,l,hql,hl⟩ := symmetric_odd_period_tower hvh
    (Nat.Even.sub_odd hn he (by decide : Odd (1 : ℕ))) hvc hvs hvJ
  refine ⟨k,q,?_,?_⟩
  · intro i
    exact ⟨(hql i).1,by simpa only [Nat.sub_add_cancel hn] using (hql i).2.1⟩
  · rw [hv,hl,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hql i).2.2]
    ring

/-- Finite sums commute with the actual symmetric Todd operator. -/
theorem symmetricTodd_sum {ι : Type*} (s : Finset ι) (f : ι → TernaryPolynomial) :
    symmetricTodd (∑ i ∈ s,f i)=∑ i ∈ s,symmetricTodd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha,symmetricTodd_add,ih]

/-- Every finite polynomial quotient tower is in the entire symmetric Todd kernel. -/
theorem symmetric_period_tower_Todd_zero {k : ℕ}
    (q : Fin k → MvPolynomial (Fin 2) ℚ) (l : Fin k → TernaryPolynomial)
    (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (hl : ∀ i, binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i) :
    symmetricTodd (∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)=0 := by
  rw [symmetricTodd_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hz : symmetricTodd (l i)=0 := by
    apply symmetricTodd_of_coordinate_sum_pow_mul 1
    simpa only [pow_one,← hl i] using symmetricTodd_binaryPeriodLift_eq_zero (hq i)
  rw [symmetricTodd_W_pow_mul,hz,mul_zero]

end TernaryPoly
