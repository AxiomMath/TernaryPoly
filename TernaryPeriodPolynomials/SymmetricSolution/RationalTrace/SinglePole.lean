module

public import TernaryPeriodPolynomials.SymmetricSolution.RationalTrace.Consumer
public import TernaryPeriodPolynomials.SymmetricSolution.Odd.SinglePole

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricRationalTrace
open SymmetricOddRationalSeed SymmetricOddRationalTower OrdinaryRationalFiber OrdinaryCovectors

/-- Arbitrary literal linear substitutions preserve the homogeneous degree. -/
theorem substitute_homogeneous {n : ℕ} {f a b c : TP} (hf : f.IsHomogeneous n)
    (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1) (hc : c.IsHomogeneous 1) :
    (substitute3 f a b c).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hf
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- Embedded homogeneous seed evaluations belong to the actual single-pole module. -/
theorem fValue_mem_singlePole {n : ℕ} {f a b c : TP} (hf : f.IsHomogeneous n)
    (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1) (hc : c.IsHomogeneous 1) :
    fValue f a b c ∈ SinglePole.singlePole n := by
  simpa only [fValue,SinglePole.polynomialInclusion_val] using
    (SinglePole.polynomialInclusion n ⟨substitute3 f a b c,substitute_homogeneous hf ha hb hc⟩).property

theorem qValue_mem_singlePole {n k : ℕ} (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    {a b c : TP} (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1) (hc : c.IsHomogeneous 1) :
    qValue q hq a b c ∈ SinglePole.singlePole n :=
  fValue_mem_singlePole (qPolynomial_homogeneous q hq hd) ha hb hc

/-- Every entry of the actual rational26-fiber system has the exact homogeneous degree. -/
theorem seedValue_mem_singlePole {n k : ℕ} (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) (r : Covector) :
    seedValue f q hq r ∈ SinglePole.singlePole n := by
  have hr : r=![r 0,r 1,r 2] := by funext i; fin_cases i <;> rfl
  rw [hr]
  generalize r 0=a,r 1=b,r 2=c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exact (SinglePole.singlePole n).zero_mem
  · change pValue q (X 2) (X 0) (X 1) ∈ SinglePole.singlePole n
    simpa only [pValue_odd_first,neg_neg] using pValue_coordinates_mem_singlePole q hq hd 2 0 1
  · change -(pValue q (-X 2) (X 0) (X 1)) ∈ SinglePole.singlePole n
    simpa only [pValue_odd_first,neg_neg] using pValue_coordinates_mem_singlePole q hq hd 2 0 1
  · change pValue q (X 1) (X 0) (X 2) ∈ SinglePole.singlePole n
    simpa only [pValue_odd_first,neg_neg] using pValue_coordinates_mem_singlePole q hq hd 1 0 2
  · change qValue q hq (X 1) (X 2) (X 0) ∈ SinglePole.singlePole n
    exact qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 1)) ((isHomogeneous_X ℚ 2)) (isHomogeneous_X ℚ 0)
  · change -(qValue q hq (X 1) (-X 2) (X 0)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 1)) ((isHomogeneous_X ℚ 2).neg) (isHomogeneous_X ℚ 0))
  · change -(pValue q (-X 1) (X 0) (X 2)) ∈ SinglePole.singlePole n
    simpa only [pValue_odd_first,neg_neg] using pValue_coordinates_mem_singlePole q hq hd 1 0 2
  · change -(qValue q hq (-X 1) (X 2) (X 0)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 1).neg) ((isHomogeneous_X ℚ 2)) (isHomogeneous_X ℚ 0))
  · change qValue q hq (-X 1) (-X 2) (X 0) ∈ SinglePole.singlePole n
    exact qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 1).neg) ((isHomogeneous_X ℚ 2).neg) (isHomogeneous_X ℚ 0)
  · change pValue q (X 0) (X 1) (X 2) ∈ SinglePole.singlePole n
    simpa only [pValue_odd_first,neg_neg] using pValue_coordinates_mem_singlePole q hq hd 0 1 2
  · change qValue q hq (X 0) (X 2) (X 1) ∈ SinglePole.singlePole n
    exact qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 0)) ((isHomogeneous_X ℚ 2)) (isHomogeneous_X ℚ 1)
  · change -(qValue q hq (X 0) (-X 2) (X 1)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 0)) ((isHomogeneous_X ℚ 2).neg) (isHomogeneous_X ℚ 1))
  · change qValue q hq (X 0) (X 1) (X 2) ∈ SinglePole.singlePole n
    exact qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 0)) ((isHomogeneous_X ℚ 1)) (isHomogeneous_X ℚ 2)
  · change fValue f (X 0) (X 1) (X 2) ∈ SinglePole.singlePole n
    exact fValue_mem_singlePole hf ((isHomogeneous_X ℚ 0)) ((isHomogeneous_X ℚ 1)) ((isHomogeneous_X ℚ 2))
  · change -(fValue f (X 0) (X 1) (-X 2)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (fValue_mem_singlePole hf ((isHomogeneous_X ℚ 0)) ((isHomogeneous_X ℚ 1)) ((isHomogeneous_X ℚ 2).neg))
  · change -(qValue q hq (X 0) (-X 1) (X 2)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 0)) ((isHomogeneous_X ℚ 1).neg) (isHomogeneous_X ℚ 2))
  · change -(fValue f (X 0) (-X 1) (X 2)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (fValue_mem_singlePole hf ((isHomogeneous_X ℚ 0)) ((isHomogeneous_X ℚ 1).neg) ((isHomogeneous_X ℚ 2)))
  · change fValue f (X 0) (-X 1) (-X 2) ∈ SinglePole.singlePole n
    exact fValue_mem_singlePole hf ((isHomogeneous_X ℚ 0)) ((isHomogeneous_X ℚ 1).neg) ((isHomogeneous_X ℚ 2).neg)
  · change -(pValue q (-X 0) (X 1) (X 2)) ∈ SinglePole.singlePole n
    simpa only [pValue_odd_first,neg_neg] using pValue_coordinates_mem_singlePole q hq hd 0 1 2
  · change -(qValue q hq (-X 0) (X 2) (X 1)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 0).neg) ((isHomogeneous_X ℚ 2)) (isHomogeneous_X ℚ 1))
  · change qValue q hq (-X 0) (-X 2) (X 1) ∈ SinglePole.singlePole n
    exact qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 0).neg) ((isHomogeneous_X ℚ 2).neg) (isHomogeneous_X ℚ 1)
  · change -(qValue q hq (-X 0) (X 1) (X 2)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 0).neg) ((isHomogeneous_X ℚ 1)) (isHomogeneous_X ℚ 2))
  · change -(fValue f (-X 0) (X 1) (X 2)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (fValue_mem_singlePole hf ((isHomogeneous_X ℚ 0).neg) ((isHomogeneous_X ℚ 1)) ((isHomogeneous_X ℚ 2)))
  · change fValue f (-X 0) (X 1) (-X 2) ∈ SinglePole.singlePole n
    exact fValue_mem_singlePole hf ((isHomogeneous_X ℚ 0).neg) ((isHomogeneous_X ℚ 1)) ((isHomogeneous_X ℚ 2).neg)
  · change qValue q hq (-X 0) (-X 1) (X 2) ∈ SinglePole.singlePole n
    exact qValue_mem_singlePole q hq hd ((isHomogeneous_X ℚ 0).neg) ((isHomogeneous_X ℚ 1).neg) (isHomogeneous_X ℚ 2)
  · change fValue f (-X 0) (-X 1) (X 2) ∈ SinglePole.singlePole n
    exact fValue_mem_singlePole hf ((isHomogeneous_X ℚ 0).neg) ((isHomogeneous_X ℚ 1).neg) ((isHomogeneous_X ℚ 2))
  · change -(fValue f (-X 0) (-X 1) (-X 2)) ∈ SinglePole.singlePole n
    exact (SinglePole.singlePole n).neg_mem (fValue_mem_singlePole hf ((isHomogeneous_X ℚ 0).neg) ((isHomogeneous_X ℚ 1).neg) ((isHomogeneous_X ℚ 2).neg))

/-- The actual finite trace belongs to the homogeneous single-pole coefficient module. -/
theorem trace_mem_singlePole {n k : ℕ} (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) :
    trace f q hq ∈ SinglePole.singlePole n := by
  unfold trace fiberTrace
  apply (SinglePole.singlePole n).sum_mem
  intro r _
  exact seedValue_mem_singlePole f hf q hq hd r.val

/-- The literal rational trace as an actual degree-n single-pole coefficient. -/
def homogeneousTrace {n k : ℕ} (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) : SinglePole.singlePole n :=
  ⟨trace f q hq,trace_mem_singlePole f hf q hq hd⟩

@[simp] theorem homogeneousTrace_val {n k : ℕ} (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) :
    (homogeneousTrace f hf q hq hd).val=trace f q hq := rfl

end TernaryPoly.SymmetricRationalTrace
