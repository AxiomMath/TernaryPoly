module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Rational.FiberActions
public import TernaryPeriodPolynomials.SymmetricSolution.ToddCertificate

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryRationalFiber
open SymmetricOddRationalSeed SymmetricOddRationalTower
open OrdinaryCovectors OrdinaryCovectorOrbits OrdinaryPolynomialNorm
open OrdinarySeedEquivariance OrdinarySignedFibers

/-- Actual embedded evaluation of a polynomial seed. -/
def fValue (f a b c : TP) : Frac := embed (substitute3 f a b c)

def qValue {k : ℕ} (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (a b c : TP) : Frac := fValue (qPolynomial q hq) a b c

def seedValue {k : ℕ} (f : TP) (q : Fin k → BP)
    (hq : ∀ i, SymmetricBinaryPeriodRelations (q i)) (r : Covector) : Frac :=
  (![![![0, (pValue q (X 2) (X 0) (X 1)), -(pValue q (-X 2) (X 0) (X 1))],
      ![(pValue q (X 1) (X 0) (X 2)), (qValue q hq (X 1) (X 2) (X 0)), -(qValue q hq (X 1) (-X 2) (X 0))],
      ![-(pValue q (-X 1) (X 0) (X 2)), -(qValue q hq (-X 1) (X 2) (X 0)), (qValue q hq (-X 1) (-X 2) (X 0))]],
    ![![(pValue q (X 0) (X 1) (X 2)), (qValue q hq (X 0) (X 2) (X 1)), -(qValue q hq (X 0) (-X 2) (X 1))],
      ![(qValue q hq (X 0) (X 1) (X 2)), (fValue f (X 0) (X 1) (X 2)), -(fValue f (X 0) (X 1) (-X 2))],
      ![-(qValue q hq (X 0) (-X 1) (X 2)), -(fValue f (X 0) (-X 1) (X 2)), (fValue f (X 0) (-X 1) (-X 2))]],
    ![![-(pValue q (-X 0) (X 1) (X 2)), -(qValue q hq (-X 0) (X 2) (X 1)), (qValue q hq (-X 0) (-X 2) (X 1))],
      ![-(qValue q hq (-X 0) (X 1) (X 2)), -(fValue f (-X 0) (X 1) (X 2)), (fValue f (-X 0) (X 1) (-X 2))],
      ![(qValue q hq (-X 0) (-X 1) (X 2)), (fValue f (-X 0) (-X 1) (X 2)), -(fValue f (-X 0) (-X 1) (-X 2))]]] (r 0) (r 1) (r 2))


variable {k : ℕ}

theorem fValue_self (f : TP) : fValue f (X 0) (X 1) (X 2)=embed f := by
  have he : (![X 0,X 1,X 2] : Fin 3 → TP)=X := by funext i; fin_cases i <;> rfl
  simp [fValue,substitute3,he]

theorem seedValue_one (f : TP) (q : Fin k → BP) (hq) :
    seedValue f q hq ![1,0,0]=pValue q (X 0) (X 1) (X 2) := rfl

theorem seedValue_two (f : TP) (q : Fin k → BP) (hq) :
    seedValue f q hq ![1,1,0]=embed (qPolynomial q hq) := fValue_self _

theorem seedValue_three (f : TP) (q : Fin k → BP) (hq) :
    seedValue f q hq ![1,1,1]=embed f := fValue_self _

theorem qValue_swap (q : Fin k → BP) (hq) (a b c : TP) :
    qValue q hq b a c=qValue q hq a b c :=
  congrArg embed (symmetric_substitute3_swap (qPolynomial_swap q hq) a b c)

theorem qValue_odd_third (q : Fin k → BP) (hq) (a b c : TP) :
    qValue q hq a b (-c)= -qValue q hq a b c := by
  have he := congrArg (fun p => substitute3 p a b c) (qPolynomial_odd q hq)
  change substitute3 (substitute3 (qPolynomial q hq) (X 0) (X 1) (-X 2)) a b c = _ at he
  rw [substitute3_substitute3] at he
  have hp : substitute3 (qPolynomial q hq) a b (-c)= -substitute3 (qPolynomial q hq) a b c := by
    simpa [substitute3] using he
  change embed _ = -embed _
  rw [hp,map_neg]

theorem fValue_swap {f : TP} (hs : S f=f) (a b c : TP) :
    fValue f b a c=fValue f a b c :=
  congrArg embed (symmetric_substitute3_swap hs a b c)

theorem fValue_swap_last {f : TP} (hc : C f=f) (hs : S f=f) (a b c : TP) :
    fValue f a c b=fValue f a b c :=
  congrArg embed (symmetric_substitute3_swap_last hc hs a b c)

/-- Fraction-field automorphisms transport literal polynomial seed values. -/
theorem extend_fValue (e : TP ≃ₐ[ℚ] TP) (f a b c : TP) :
    extend e (fValue f a b c)=fValue f (e a) (e b) (e c) := by
  rw [fValue,extend_embed]
  exact congrArg embed (map_substitute e.toAlgHom f a b c)

theorem fracS_P (q : Fin k → BP) (a b c : TP) :
    fracS (pValue q a b c)=pValue q (S a) (S b) (S c) := extend_pValue _ _ _ _ _
theorem fracC_P (q : Fin k → BP) (a b c : TP) :
    fracC (pValue q a b c)=pValue q (C a) (C b) (C c) := extend_pValue _ _ _ _ _
theorem fracA_P (q : Fin k → BP) (a b c : TP) :
    fracA (pValue q a b c)=pValue q (A a) (A b) (A c) := extend_pValue _ _ _ _ _
theorem fracA2_P (q : Fin k → BP) (a b c : TP) :
    fracA2 (pValue q a b c)=pValue q (A2 a) (A2 b) (A2 c) := by
  change fracA (fracA (pValue q a b c))=_
  rw [fracA_P,fracA_P,A_A,A_A,A_A]

theorem fracS_F (f a b c : TP) : fracS (fValue f a b c)=fValue f (S a) (S b) (S c) :=
  extend_fValue _ _ _ _ _
theorem fracC_F (f a b c : TP) : fracC (fValue f a b c)=fValue f (C a) (C b) (C c) :=
  extend_fValue _ _ _ _ _
theorem fracA_F (f a b c : TP) : fracA (fValue f a b c)=fValue f (A a) (A b) (A c) :=
  extend_fValue _ _ _ _ _
theorem fracA2_F (f a b c : TP) : fracA2 (fValue f a b c)=fValue f (A2 a) (A2 b) (A2 c) := by
  change fracA (fracA (fValue f a b c))=_
  rw [fracA_F,fracA_F,A_A,A_A,A_A]

theorem fracD12_P (q : Fin k → BP) (a b c : TP) :
    fracD12 (pValue q a b c)=pValue q (D12 a) (D12 b) (D12 c) := by
  have h := extend_pValue (signPolyEquiv {0,1}) q a b c
  change fracD12 (pValue q a b c)=pValue q (signPoly {0,1} a) (signPoly {0,1} b) (signPoly {0,1} c) at h
  rwa [signPoly_pair] at h

theorem fracD3_P (q : Fin k → BP) (a b c : TP) :
    fracD3 (pValue q a b c)=pValue q (D3 a) (D3 b) (D3 c) := by
  have h := extend_pValue (signPolyEquiv {2}) q a b c
  change fracD3 (pValue q a b c)=pValue q (signPoly {2} a)
    (signPoly {2} b) (signPoly {2} c) at h
  simpa only [signPoly_third] using h

theorem fracD12_F (f a b c : TP) :
    fracD12 (fValue f a b c)=fValue f (D12 a) (D12 b) (D12 c) := by
  have h := extend_fValue (signPolyEquiv {0,1}) f a b c
  change fracD12 (fValue f a b c)=fValue f (signPoly {0,1} a) (signPoly {0,1} b) (signPoly {0,1} c) at h
  rwa [signPoly_pair] at h

theorem fracD3_F (f a b c : TP) :
    fracD3 (fValue f a b c)=fValue f (D3 a) (D3 b) (D3 c) := by
  have h := extend_fValue (signPolyEquiv {2}) f a b c
  change fracD3 (fValue f a b c)=fValue f (signPoly {2} a) (signPoly {2} b) (signPoly {2} c) at h
  rwa [signPoly_third] at h

theorem fracS_Q (q : Fin k → BP) (hq) (a b c : TP) :
    fracS (qValue q hq a b c)=qValue q hq (S a) (S b) (S c) :=
  fracS_F _ _ _ _

theorem fracC_Q (q : Fin k → BP) (hq) (a b c : TP) :
    fracC (qValue q hq a b c)=qValue q hq (C a) (C b) (C c) :=
  fracC_F _ _ _ _

theorem fracA_Q (q : Fin k → BP) (hq) (a b c : TP) :
    fracA (qValue q hq a b c)=qValue q hq (A a) (A b) (A c) :=
  fracA_F _ _ _ _

theorem fracA2_Q (q : Fin k → BP) (hq) (a b c : TP) :
    fracA2 (qValue q hq a b c)=qValue q hq (A2 a) (A2 b) (A2 c) :=
  fracA2_F _ _ _ _

theorem fracD12_Q (q : Fin k → BP) (hq) (a b c : TP) :
    fracD12 (qValue q hq a b c)=qValue q hq (D12 a) (D12 b) (D12 c) :=
  fracD12_F _ _ _ _

theorem fracD3_Q (q : Fin k → BP) (hq) (a b c : TP) :
    fracD3 (qValue q hq a b c)=qValue q hq (D3 a) (D3 b) (D3 c) :=
  fracD3_F _ _ _ _

end TernaryPoly.OrdinaryRationalFiber
