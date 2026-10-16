module

public import TernaryPeriodPolynomials.SymmetricSolution.PeriodSeeds
public import TernaryPeriodPolynomials.SymmetricSolution.PeriodTower

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The polynomial seed stabilizers and mixed identities, before deriving the Q norm. -/
structure SymmetricSeedData (f P Q : TernaryPolynomial) : Prop where
  q_swap : S Q=Q
  q_odd : bind₁ ![X 0,X 1,-X 2] Q= -Q
  p_swap : bind₁ ![X 0,X 2,X 1] P=P
  p_odd_first : bind₁ ![X 0,-X 1,X 2] P= -P
  p_odd_second : bind₁ ![X 0,X 1,-X 2] P= -P
  p_norm : P+bind₁ ![X 0,-X 2,X 1-X 2] P+bind₁ ![X 0,X 2-X 1,-X 1] P=0
  mixedQ : bind₁ ![X 0,X 1,X 2+X 0] Q-Q=bind₁ ![X 0+X 2,-X 2,X 1] f
  mixedP : bind₁ ![(X 0 : TernaryPolynomial),X 2+X 0,X 1] P-bind₁ ![X 0,X 2,X 1] P=
    bind₁ ![-X 2,X 0+X 2,X 1] Q

private theorem substitute3_self (f : TernaryPolynomial) :
    substitute3 f (X 0) (X 1) (X 2)=f := by
  have hv : (![X 0,X 1,X 2] : Fin 3 → TernaryPolynomial)=X := by
    funext i
    fin_cases i <;> rfl
  simp [substitute3,hv]

/-- Each nonnegative binary-period layer gives genuine polynomial seed data. -/
theorem symmetricPeriodSeed_data (r : ℕ) {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    SymmetricSeedData ((X 0+X 1+X 2)^r*binaryPeriodLift q)
      (symmetricPeriodSeedP r q) (symmetricPeriodSeedQ r q) := by
  obtain ⟨hps,hp1,hp2⟩ := symmetricPeriodSeedP_symmetries r hq
  refine ⟨symmetricPeriodSeedQ_swap r q,symmetricPeriodSeedQ_odd r hq,hps,hp1,hp2,?_,?_,?_⟩
  · have h := symmetricPeriodSeedP_norm r hq (X 0) (X 1) (X 2)
    rwa [substitute3_self] at h
  · have h := symmetricPeriodSeedQ_mixed r hq (X 0) (X 1) (X 2)
    rwa [substitute3_self] at h
  · simpa only [substitute3] using symmetricPeriodSeedP_mixed r hq (X 0) (X 1) (X 2)

/-- Seed data are closed under addition, with literal polynomial sums. -/
theorem SymmetricSeedData.add {f P Q g R T : TernaryPolynomial}
    (h : SymmetricSeedData f P Q) (k : SymmetricSeedData g R T) :
    SymmetricSeedData (f+g) (P+R) (Q+T) := by
  constructor
  · rw [map_add,h.q_swap,k.q_swap]
  · rw [map_add,h.q_odd,k.q_odd,neg_add]
  · rw [map_add,h.p_swap,k.p_swap]
  · rw [map_add,h.p_odd_first,k.p_odd_first,neg_add]
  · rw [map_add,h.p_odd_second,k.p_odd_second,neg_add]
  · simp only [map_add]
    linear_combination h.p_norm+k.p_norm
  · simp only [map_add]
    linear_combination h.mixedQ+k.mixedQ
  · simp only [map_add]
    linear_combination h.mixedP+k.mixedP

/-- Zero polynomials give the zero seed triple. -/
theorem SymmetricSeedData.zero : SymmetricSeedData 0 0 0 := by
  constructor <;> simp

/-- All seed equations pass to actual finite sums. -/
theorem SymmetricSeedData.sum {ι : Type*} (s : Finset ι) (f P Q : ι → TernaryPolynomial)
    (h : ∀ i∈s, SymmetricSeedData (f i) (P i) (Q i)) :
    SymmetricSeedData (∑ i∈s,f i) (∑ i∈s,P i) (∑ i∈s,Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SymmetricSeedData.zero
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Every positive even homogeneous symmetric norm solution in the Todd kernel has polynomial seeds. -/
theorem symmetric_even_polynomial_seeds {f : TernaryPolynomial} {n : ℕ}
    (hn : 0<n) (he : Even n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ P Q : TernaryPolynomial, SymmetricSeedData f P Q := by
  obtain ⟨k,q,hq,hf⟩ := symmetric_even_period_tower hn he hf hrel hs hJ
  refine ⟨∑ i : Fin k,symmetricPeriodSeedP (2*(i:ℕ)) (q i),
    ∑ i : Fin k,symmetricPeriodSeedQ (2*(i:ℕ)) (q i),?_⟩
  rw [hf]
  exact SymmetricSeedData.sum Finset.univ _ _ _
    (fun i _ => symmetricPeriodSeed_data (2*(i:ℕ)) (hq i).1)

end TernaryPoly
