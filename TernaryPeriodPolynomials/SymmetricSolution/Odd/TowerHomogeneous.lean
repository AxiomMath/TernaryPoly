module

public import TernaryPeriodPolynomials.SymmetricSolution.Odd.RationalTower
public import TernaryPeriodPolynomials.Topology.HomogeneousQuotient

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricOddRationalTower
open SymmetricOddRationalSeed

variable {k : ℕ}

theorem binary_period_degree_zero {q : BP} (hq : SymmetricBinaryPeriodRelations q)
    (hd : q.IsHomogeneous 0) : q=0 := by
  have he : q=MvPolynomial.C (q.coeff 0) := by
    rw [←homogeneousComponent_zero]
    simp [homogeneousComponent_of_mem hd]
  have h := hq.odd_first
  rw [he] at h
  have hc := congrArg (·.coeff 0) h
  simp only [bind₁_C_right,coeff_C,ite_true,coeff_neg] at hc
  have hz : q.coeff 0=0 := by linarith
  rw [he,hz,map_zero]

theorem binaryLiftEval_homogeneous {q : BP} {d : ℕ} (hq : q.IsHomogeneous d)
    {a b : TP} (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1) :
    (binaryLiftEval q a b).IsHomogeneous d := by
  apply isHomogeneous_bind₁_linear hq
  intro i
  fin_cases i
  · exact ha
  · exact hb

theorem lowest_homogeneous {n : ℕ} (q : Fin k → BP)
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) : (lowest q).IsHomogeneous (n+1) := by
  apply IsHomogeneous.sum
  intro i _
  by_cases hi : (i:ℕ)=0
  · simpa only [hi,Nat.mul_zero,Nat.sub_zero,ite_true] using hd i
  · simp only [ite_eq_right hi]
    exact isHomogeneous_zero _ _ _

theorem numerator_homogeneous {n : ℕ} (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    {a b c : TP} (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1) (hc : c.IsHomogeneous 1) :
    (numerator q a b c).IsHomogeneous (n+1) := by
  apply IsHomogeneous.sum
  intro i _
  by_cases hi : 2*(i:ℕ)≤n
  · have he : 2*(i:ℕ)+(n+1-2*(i:ℕ))=n+1 := by omega
    simpa only [Nat.one_mul,he] using (ha.pow (2*(i:ℕ))).mul (binaryLiftEval_homogeneous (hd i) hb hc)
  · have hz : q i=0 := binary_period_degree_zero (hq i) (by simpa [show n+1-2*(i:ℕ)=0 by omega] using hd i)
    simp only [hz,binaryLiftEval,map_zero,mul_zero]
    exact isHomogeneous_zero _ _ _

theorem oddSeedQ_homogeneous {q : BP} (hq : SymmetricBinaryPeriodRelations q)
    {d : ℕ} (hd : q.IsHomogeneous d) : (symmetricOddSeedQ q hq).IsHomogeneous (d-1) := by
  have hs : (X 0+X 1 : TP).IsHomogeneous 1 := (isHomogeneous_X ℚ 0).add (isHomogeneous_X ℚ 1)
  have hn : (X 0+X 1 : TP)≠0 := by
    intro h
    have h' := congrArg (eval (![1,0,0] : Fin 3 → ℚ)) h
    norm_num at h'
  apply isHomogeneous_quotient hs hn
  rw [symmetricOddSeedQ_mul]
  simp only [symmetricPeriodSeedQ,pow_zero,one_mul]
  exact (binaryLiftEval_homogeneous hd (isHomogeneous_X ℚ 0) (isHomogeneous_X ℚ 2)).add
    (binaryLiftEval_homogeneous hd (isHomogeneous_X ℚ 1) (isHomogeneous_X ℚ 2))

theorem oddSeedQ_zero (hq : SymmetricBinaryPeriodRelations (0 : BP)) : symmetricOddSeedQ 0 hq=0 := by
  have h := Q_mul 0 hq (X 0) (X 1) (X 2)
  have hn : (X 0+X 1 : TP)≠0 := by
    intro h
    have h' := congrArg (eval (![1,0,0] : Fin 3 → ℚ)) h
    norm_num at h'
  have hs : Q 0 hq (X 0) (X 1) (X 2)=symmetricOddSeedQ 0 hq := by
    have hv : (![X 0,X 1,X 2] : Fin 3 → TP)=X := by funext i; fin_cases i <;> rfl
    simp only [Q,substitute3,hv,bind₁_X_left,AlgHom.id_apply]
  rw [hs] at h
  simpa only [binaryLiftEval,map_zero,add_zero,mul_eq_zero,hn,false_or] using h

theorem qPolynomial_homogeneous {n : ℕ} (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) :
    (qPolynomial q hq).IsHomogeneous n := by
  apply IsHomogeneous.sum
  intro i _
  by_cases hi : 2*(i:ℕ)≤n
  · have he : 2*(i:ℕ)+(n+1-2*(i:ℕ)-1)=n := by omega
    simpa only [Nat.one_mul,he] using
      (((isHomogeneous_X ℚ 0).add (isHomogeneous_X ℚ 1)).pow (2*(i:ℕ))).mul
        (oddSeedQ_homogeneous (hq i) (hd i))
  · have hz : q i=0 := binary_period_degree_zero (hq i) (by simpa [show n+1-2*(i:ℕ)=0 by omega] using hd i)
    simp only [hz,oddSeedQ_zero,mul_zero]
    exact isHomogeneous_zero _ _ _


theorem regular_homogeneous {n : ℕ} (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    {a b c : TP} (ha : a.IsHomogeneous 1) (ha0 : a≠0)
    (hb : b.IsHomogeneous 1) (hc : c.IsHomogeneous 1) :
    (regular q a b c).IsHomogeneous n := by
  have he : a*regular q a b c=numerator q a b c-binaryLiftEval (lowest q) b c := by
    rw [numerator_split,add_sub_cancel_right]
  have hh := (numerator_homogeneous q hq hd ha hb hc).sub
    (binaryLiftEval_homogeneous (lowest_homogeneous q hd) hb hc)
  rw [←he] at hh
  simpa only [Nat.add_sub_cancel] using isHomogeneous_quotient ha ha0 hh

end TernaryPoly.SymmetricOddRationalTower
