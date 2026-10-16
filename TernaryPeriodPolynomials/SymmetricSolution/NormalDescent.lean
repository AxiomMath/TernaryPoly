module

public import TernaryPeriodPolynomials.SymmetricSolution.FirstJet.Jet
public import TernaryPeriodPolynomials.SymmetricSolution.PeriodExtraction.Recovery
public import TernaryPeriodPolynomials.SymmetricSolution.BinaryPeriodQuotient
public import TernaryPeriodPolynomials.SymmetricSolution.NormalAlgebra

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The binary period extracted from the actual symmetric first-plane data. -/
def extractedSymmetricBinaryPeriod (n : ℕ) (f : TernaryPolynomial) :
    MvPolynomial (Fin 2) ℚ := binaryPeriodPrimitive n (binaryFirstJetPrimitive f)

/-- Entire Todd vanishing supplies every relation of the extracted symmetric binary period. -/
theorem extractedSymmetricBinaryPeriod_relations {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hJ : symmetricTodd f=0) : SymmetricBinaryPeriodRelations (extractedSymmetricBinaryPeriod n f) :=
  symmetricBinaryPeriodPrimitive_relations hf hodd hc hs
    (symmetricBinaryFirstJetPrimitive_difference hf hodd hc hs hJ)

/-- The extracted lift has the same degree and first-plane primitive as its source. -/
theorem extractedSymmetricBinaryPeriod_lift_data {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hJ : symmetricTodd f=0) :
    ∃ l : TernaryPolynomial,
      binaryPeriodLift (extractedSymmetricBinaryPeriod n f)=(X 0+X 1+X 2)*l ∧
      l.IsHomogeneous n ∧ C l=l ∧ S l=l ∧ symmetricTodd l=0 ∧
      binaryFirstJetPrimitive (f-l)=0 := by
  have hdiff := symmetricBinaryFirstJetPrimitive_difference hf hodd hc hs hJ
  have hq := extractedSymmetricBinaryPeriod_relations hf hodd hc hs hJ
  obtain ⟨l,hl,hlc,hls,hlj,_⟩ := symmetricBinaryPeriod_quotient_data hq
  have hld : l.IsHomogeneous n := by
    simpa only [Nat.add_sub_cancel] using symmetricBinaryLift_quotient_isHomogeneous
      (symmetricBinaryPeriodPrimitive_isHomogeneous hf hodd) l hl
  refine ⟨l,hl,hld,hlc,hls,hlj,?_⟩
  have hsub : binaryFirstJetPrimitive (f-l)=binaryFirstJetPrimitive f-binaryFirstJetPrimitive l := by
    simp only [binaryFirstJetPrimitive,map_sub,binaryBoundary]
    rw [show pderiv 0 f-pderiv 0 l+(pderiv 1 f-pderiv 1 l)=
      (pderiv 0 f+pderiv 1 f)-(pderiv 0 l+pderiv 1 l) by abel]
    simp only [map_sub,neg_sub_neg,neg_sub]
  rw [hsub,symmetricBinaryFirstJetPrimitive_lift_quotient hq l hl]
  change binaryFirstJetPrimitive f - -pderiv 1
    (binaryPeriodPrimitive n (binaryFirstJetPrimitive f))=0
  rw [symmetricBinaryPeriodPrimitive_pderiv hf hodd hc hs hdiff,neg_neg,sub_self]

/-- A symmetric kernel element is a period lift plus a lower-degree double-plane multiple. -/
theorem symmetric_normal_step {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hJ : symmetricTodd f=0) :
    ∃ l g : TernaryPolynomial,
      f=l+(X 0+X 1+X 2)^2*g ∧
      binaryPeriodLift (extractedSymmetricBinaryPeriod n f)=(X 0+X 1+X 2)*l ∧
      g.IsHomogeneous (n-2) ∧ C g=g ∧ S g=g ∧ symmetricTodd g=0 ∧
      (g≠0 → 2≤n) := by
  obtain ⟨l,hl,hld,hlc,hls,hlj,hlp⟩ := extractedSymmetricBinaryPeriod_lift_data hf hodd hc hs hJ
  have hrc : C (f-l)=f-l := by rw [map_sub,hc,hlc]
  have hrs : S (f-l)=f-l := by rw [map_sub,hs,hls]
  have hrj : symmetricTodd (f-l)=0 := by rw [symmetricTodd_sub,hJ,hlj,sub_self]
  obtain ⟨g,hg⟩ := coordinateSum_sq_dvd_of_binaryFirstJetPrimitive_eq_zero
    (hf.sub hld) hodd.pos hrc hlp
  obtain ⟨hgh,hgc,hgs,hgj,hge⟩ := symmetric_normal_quotient_data
    (hf.sub hld) hrc hrs hrj g hg
  refine ⟨l,g,?_,hl,hgh,hgc,hgs,hgj,hge⟩
  rw [← hg]
  abel

/-- All odd homogeneous symmetric kernel elements are built by finitely many period-lift steps. -/
theorem symmetric_normal_induction (P : TernaryPolynomial → Prop)
    (hzero : P 0)
    (hlift : ∀ q : MvPolynomial (Fin 2) ℚ, SymmetricBinaryPeriodRelations q →
      ∀ l : TernaryPolynomial, binaryPeriodLift q=(X 0+X 1+X 2)*l → P l)
    (hstep : ∀ l g : TernaryPolynomial, P l → P g → P (l+(X 0+X 1+X 2)^2*g))
    {n : ℕ} {f : TernaryPolynomial} (hf : f.IsHomogeneous n) (hodd : Odd n)
    (hc : C f=f) (hs : S f=f) (hJ : symmetricTodd f=0) : P f := by
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    obtain ⟨l,g,hfg,hl,hgh,hgc,hgs,hgj,hge⟩ := symmetric_normal_step hf hodd hc hs hJ
    rw [hfg]
    apply hstep l g
    · exact hlift _ (extractedSymmetricBinaryPeriod_relations hf hodd hc hs hJ) l hl
    · by_cases hg0 : g=0
      · simpa only [hg0] using hzero
      · have hge := hge hg0
        apply ih (n-2) (by omega) hgh
        · exact Nat.Odd.sub_even hge hodd (by decide : Even (2 : ℕ))
        · exact hgc
        · exact hgs
        · exact hgj

end TernaryPoly
