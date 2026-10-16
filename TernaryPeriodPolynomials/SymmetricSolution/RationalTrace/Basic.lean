module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Rational.FiberSigned
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Rational.FiberNorm

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricRationalTrace
open SymmetricOddRationalSeed SymmetricOddRationalTower OrdinaryRationalFiber
open OrdinaryCovectors OrdinaryCovectorOrbits OrdinaryFiberPermutations OrdinarySignedFibers

/-- Literal finite trace over all26 nonzero covectors. -/
def fiberTrace (F : Covector → Frac) : Frac := ∑ r : NonzeroCovector,F r.val

/-- The trace contains exactly26 summands. -/
theorem trace_cardinality : Fintype.card NonzeroCovector=26 := card_nonzeroCovector

/-- Extend the26-term trace by the zero covector when its coefficient vanishes. -/
theorem fiberTrace_eq_sum (F : Covector → Frac) (h0 : F 0=0) :
    fiberTrace F=∑ r : Covector,F r := by
  have he := Fintype.sum_subtype_add_sum_subtype (fun r : Covector => r≠0) F
  have hz : (∑ r : {r : Covector // ¬r≠0},F r.val)=0 := by
    apply Finset.sum_eq_zero
    intro r _
    rw [not_not.mp r.property,h0]
  change fiberTrace F+_= _ at he
  simpa only [hz,add_zero] using he

def nonzeroEquiv (e : Covector ≃ Covector) (h0 : e 0=0) :
    NonzeroCovector ≃ NonzeroCovector := e.subtypeEquiv (by
  intro r
  constructor
  · intro hr he
    apply hr
    apply e.injective
    exact he.trans h0.symm
  · intro hr he
    apply hr
    rw [he,h0])

/-- Reindexing uses an actual equivalence of the26 nonzero covectors. -/
theorem fiberTrace_reindex (e : Covector ≃ Covector) (h0 : e 0=0) (F : Covector → Frac) :
    fiberTrace (fun r => F (e r))=fiberTrace F :=
  (nonzeroEquiv e h0).sum_comp (fun r => F r.val)

def permutationEquiv (π : Equiv.Perm (Fin 3)) : Covector ≃ Covector where
  toFun := permuteRow π
  invFun := permuteRow π⁻¹
  left_inv r := by funext i; simp [permuteRow]
  right_inv r := by funext i; simp [permuteRow]

def signEquiv (s : Finset (Fin 3)) : Covector ≃ Covector where
  toFun := signRow s
  invFun := signRow s
  left_inv r := by funext i; by_cases hi : i∈s <;> simp [signRow,hi]
  right_inv r := by funext i; by_cases hi : i∈s <;> simp [signRow,hi]

def stepEquiv : Covector ≃ Covector where
  toFun := stepA
  invFun := fun r => stepA (stepA r)
  left_inv := stepA_cube
  right_inv := stepA_cube

theorem sum_permute (F : Covector → Frac) (π : Equiv.Perm (Fin 3)) :
    fiberTrace (fun r => F (permuteRow π r))=fiberTrace F :=
  fiberTrace_reindex (permutationEquiv π) rfl F

theorem sum_sign (F : Covector → Frac) (s : Finset (Fin 3)) :
    fiberTrace (fun r => F (signRow s r))=fiberTrace F :=
  fiberTrace_reindex (signEquiv s) (by funext i; simp [signEquiv,signRow]) F

theorem sum_step (F : Covector → Frac) :
    fiberTrace (fun r => F (stepA r))=fiberTrace F :=
  fiberTrace_reindex stepEquiv (by funext i; fin_cases i <;> simp [stepEquiv,stepA]) F

/-- Finite trace commutes with every actual rational linear substitution. -/
theorem fiberTrace_map (F : Covector → Frac) (g : Frac →ₗ[ℚ] Frac) :
    fiberTrace (fun r => g (F r))=g (fiberTrace F) := (map_sum g _ _).symm

theorem fiberTrace_permutation (F : Covector → Frac)
    (hp : ∀ π r,F (permuteRow π r)=fracPerm π (F r)) (π : Equiv.Perm (Fin 3)) :
    fracPerm π (fiberTrace F)=fiberTrace F := by
  change (linearAction (fracPerm π)) (fiberTrace F)=fiberTrace F
  rw [←fiberTrace_map F (linearAction (fracPerm π))]
  exact (congrArg fiberTrace (funext (hp π))).symm.trans (sum_permute F π)

theorem fiberTrace_sign (F : Covector → Frac)
    (hs : ∀ s r,F (signRow s r)=(-1 : ℚ)^s.card • fracSign s (F r))
    (s : Finset (Fin 3)) :
    (-1 : ℚ)^s.card • fracSign s (fiberTrace F)=fiberTrace F := by
  change (((-1 : ℚ)^s.card) • (linearAction (fracSign s))) (fiberTrace F)=fiberTrace F
  rw [←fiberTrace_map F (((-1 : ℚ)^s.card) • (linearAction (fracSign s)))]
  exact (congrArg fiberTrace (funext (hs s))).symm.trans (sum_sign F s)

/-- Summing the actual26 norms and reindexing both cyclic translates gives norm zero. -/
theorem fiberTrace_norm (F : Covector → Frac)
    (hn : ∀ r,r≠0 → fiberNorm F r=0) :
    fiberTrace F+fracA (fiberTrace F)+fracA2 (fiberTrace F)=0 := by
  have hsum : (∑ r : NonzeroCovector,fiberNorm F r.val)=0 :=
    Finset.sum_eq_zero (fun r _ => hn r.val r.property)
  change fiberTrace (fun r => F r+fracA (F (stepA (stepA r)))+fracA2 (F (stepA r)))=0 at hsum
  simp only [fiberTrace,Finset.sum_add_distrib,←map_sum] at hsum
  change fiberTrace F+fracA (fiberTrace (fun r => F (stepA (stepA r))))+
    fracA2 (fiberTrace (fun r => F (stepA r)))=0 at hsum
  rw [sum_step (fun r => F (stepA r)),sum_step F] at hsum
  exact hsum

variable {k : ℕ}

def trace (f : TP) (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i)) : Frac :=
  fiberTrace (seedValue f q hq)

theorem trace_permutation (f : TP) (q : Fin k → BP) (hq)
    (hc : C f=f) (hs : S f=f) (π : Equiv.Perm (Fin 3)) :
    fracPerm π (trace f q hq)=trace f q hq :=
  fiberTrace_permutation _ (seedValue_permutation f q hq hc hs) π

theorem trace_sign (f : TP) (q : Fin k → BP) (hq)
    (hc : C f=f) (hs : S f=f) (s : Finset (Fin 3)) :
    (-1 : ℚ)^s.card • fracSign s (trace f q hq)=trace f q hq :=
  fiberTrace_sign _ (OrdinaryRationalFiber.sign_equivariance _
    (OrdinaryRationalFiber.flip_equivariance _ (seedValue_permutation f q hq hc hs)
      (seedValue_sign3 f q hq))) s

theorem trace_separately_odd (f : TP) (q : Fin k → BP) (hq)
    (hc : C f=f) (hs : S f=f) (i : Fin 3) :
    fracSign {i} (trace f q hq)= -trace f q hq := by
  have he := trace_sign f q hq hc hs {i}
  rw [Finset.card_singleton,pow_one,neg_one_smul ℚ (fracSign {i} (trace f q hq))] at he
  simpa only [neg_neg] using congrArg Neg.neg he

theorem trace_norm (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (f : TP) (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hf : PeriodRelations f) (hs : S f=f) :
    trace f q hq+fracA (trace f q hq)+fracA2 (trace f q hq)=0 :=
  fiberTrace_norm _ (seedValue_all_norms q hq l hl f he hf hs)

end TernaryPoly.SymmetricRationalTrace
