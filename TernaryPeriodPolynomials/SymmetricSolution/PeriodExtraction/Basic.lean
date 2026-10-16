module

public import TernaryPeriodPolynomials.SymmetricSolution.PeriodExtraction.Equation
public import TernaryPeriodPolynomials.SymmetricSolution.BinaryPeriodLift
public import TernaryPeriodPolynomials.Analysis.CoordinateSumQuotient
public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.SquareDivisibility

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly
namespace SymmetricPeriodExtraction
local notation "BP" => MvPolynomial (Fin 2) ℚ

 theorem boundary_axis {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f) :
    bind₁ (![0,X 1] : Fin 2 → BP) (binaryBoundary f)=0 := by
  have he : bs 0 (X 1) (binaryBoundary (C f))=bs (X 1) 0 (binaryBoundary f) := by
    simp only [bs,binaryBoundary,C,bind₁_bind₁]
    congr 2
    funext i
    fin_cases i <;> simp
  rw [hc] at he
  have h := congrArg (bs 0 (X 1)) (boundary_swap hf hodd hs)
  change bs 0 (X 1) (bs (X 1) (X 0) (binaryBoundary f))=_ at h
  rw [bs_comp] at h
  have ht : bs (X 1) 0 (binaryBoundary f)= -bs 0 (X 1) (binaryBoundary f) := by
    simpa [bs] using h
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp (he.trans ht))

 theorem primitive_diagonal {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hdiff : bind₁ ![X 0-X 1,X 1] (binaryFirstJetPrimitive f)-binaryFirstJetPrimitive f=
      binaryBoundary f) :
    bind₁ (![X 0,X 0] : Fin 2 → BP) (binaryFirstJetPrimitive f)=0 := by
  have h := congrArg (bs 0 (X 0)) hdiff
  change bs 0 (X 0) (bs (X 0-X 1) (X 1) (binaryFirstJetPrimitive f)-binaryFirstJetPrimitive f)=_ at h
  rw [map_sub,bs_comp] at h
  have hpaxis : bs 0 (X 0) (binaryFirstJetPrimitive f)=0 := by
    have ht := congrArg (bs (X 1) (X 0)) (binaryFirstJetPrimitive_axis_first f)
    change bs (X 1) (X 0) (bs 0 (X 1) (binaryFirstJetPrimitive f))=_ at ht
    rw [bs_comp] at ht
    simpa [bs] using ht
  have hhaxis : bs 0 (X 0) (binaryBoundary f)=0 := by
    have ht := congrArg (bs (X 1) (X 0)) (boundary_axis hf hodd hc hs)
    change bs (X 1) (X 0) (bs 0 (X 1) (binaryBoundary f))=_ at ht
    rw [bs_comp] at ht
    simpa [bs] using ht
  have ht : bs (-X 0) (X 0) (binaryFirstJetPrimitive f)=0 := by
    simp only [bs] at hpaxis hhaxis
    simpa [bs,hpaxis,hhaxis] using h
  rw [bs_odd_first (primitive_odd_first hc hs hdiff),neg_eq_zero] at ht
  exact ht

 theorem periodPrimitive_diagonal {p : BP} (n : ℕ)
    (hy : bind₁ ![X 0,-X 1] p=p) (hd : bind₁ (![X 0,X 0] : Fin 2 → BP) p=0) :
    bind₁ (![X 0,X 0] : Fin 2 → BP) (binaryPeriodPrimitive n p)=0 := by
  change bs (X 0) (X 0) (binaryPeriodPrimitive n p)=0
  rw [primitive_substitute,bs_even_second hy,show bs (X 0) (X 0) p=0 from hd]
  simp

end SymmetricPeriodExtraction

/-- The exact first-plane difference equation extracts a symmetric, separately odd binary period. -/
theorem symmetricBinaryPeriodPrimitive_relations {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hdiff : bind₁ ![X 0-X 1,X 1] (binaryFirstJetPrimitive f)-binaryFirstJetPrimitive f=
      binaryBoundary f) :
    SymmetricBinaryPeriodRelations (binaryPeriodPrimitive n (binaryFirstJetPrimitive f)) := by
  have hx := SymmetricPeriodExtraction.primitive_odd_first hc hs hdiff
  have hy := SymmetricPeriodExtraction.primitive_even_second hf hodd hc hs hdiff
  have hswap := SymmetricPeriodExtraction.periodPrimitive_swap n hy
  refine ⟨hswap,SymmetricPeriodExtraction.periodPrimitive_odd_first n hx hy,
    SymmetricPeriodExtraction.periodPrimitive_odd_second n hx hy,?_⟩
  exact SymmetricPeriodExtraction.period_equation _ _ _ hswap hx
    (binaryPeriodPrimitive_pderiv (binaryFirstJetPrimitive_isHomogeneous hf hodd)
      (SymmetricPeriodExtraction.primitive_rotation_deriv hf hodd hc hs hdiff))
    (SymmetricPeriodExtraction.boundary_swap hf hodd hs) hdiff
    (SymmetricPeriodExtraction.periodPrimitive_diagonal n hy
      (SymmetricPeriodExtraction.primitive_diagonal hf hodd hc hs hdiff))

/-- The extracted binary period has the expected degree. -/
theorem symmetricBinaryPeriodPrimitive_isHomogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) :
    (binaryPeriodPrimitive n (binaryFirstJetPrimitive f)).IsHomogeneous (n+1) :=
  binaryPeriodPrimitive_isHomogeneous (binaryFirstJetPrimitive_isHomogeneous hf hodd)

/-- Its second partial recovers minus the actual first-jet primitive. -/
theorem symmetricBinaryPeriodPrimitive_pderiv {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hdiff : bind₁ ![X 0-X 1,X 1] (binaryFirstJetPrimitive f)-binaryFirstJetPrimitive f=
      binaryBoundary f) :
    pderiv 1 (binaryPeriodPrimitive n (binaryFirstJetPrimitive f))= -binaryFirstJetPrimitive f :=
  binaryPeriodPrimitive_pderiv (binaryFirstJetPrimitive_isHomogeneous hf hodd)
    (SymmetricPeriodExtraction.primitive_rotation_deriv hf hodd hc hs hdiff)

/-- In the same positive cyclic degree, zero first jet is exactly a double total-plane factor. -/
theorem symmetricBinaryFirstJetPrimitive_zero_iff {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) :
    binaryFirstJetPrimitive f=0 ↔ (X 0+X 1+X 2)^2 ∣ f :=
  binaryFirstJetPrimitive_eq_zero_iff_coordinateSum_sq_dvd hf hodd.pos hc

/-- The extracted period vanishes exactly when the ternary source has a double total-plane factor. -/
theorem symmetricBinaryPeriodPrimitive_zero_iff {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hdiff : bind₁ ![X 0-X 1,X 1] (binaryFirstJetPrimitive f)-binaryFirstJetPrimitive f=
      binaryBoundary f) :
    binaryPeriodPrimitive n (binaryFirstJetPrimitive f)=0 ↔ (X 0+X 1+X 2)^2 ∣ f := by
  rw [← symmetricBinaryFirstJetPrimitive_zero_iff hf hodd hc]
  constructor
  · intro hq
    have hd := symmetricBinaryPeriodPrimitive_pderiv hf hodd hc hs hdiff
    rw [hq,map_zero] at hd
    exact neg_eq_zero.mp hd.symm
  · intro hp
    simp [hp,binaryPeriodPrimitive,binaryRotation]

end TernaryPoly
