module

public import TernaryPeriodPolynomials.SymmetricSolution.Odd.SeedData
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.SignedFibers
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Action

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryRationalFiber
open SymmetricOddRationalSeed SymmetricOddRationalTower
open OrdinaryPolynomialNorm OrdinaryFiberPermutations OrdinarySignedFibers

/-- Equality of actual fraction-field algebra maps is detected on the polynomial subring. -/
theorem fraction_ext (g h : Frac →ₐ[ℚ] Frac)
    (he : ∀ p : TP, g (embed p)=h (embed p)) : g=h := by
  have hh : g.toRingHom=h.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := TP)
    exact he
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun hh x

/-- The unique actual fraction-field extension of a polynomial automorphism. -/
def extend (e : TP ≃ₐ[ℚ] TP) : Frac ≃ₐ[ℚ] Frac :=
  IsFractionRing.algEquivOfAlgEquiv e

@[simp] theorem extend_embed (e : TP ≃ₐ[ℚ] TP) (p : TP) :
    extend e (embed p)=embed (e p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ p

/-- This is the same extension used by the genuine rational GL3 coefficient action. -/
theorem extend_singlePole (g : PolynomialGLAction.GL3) (x : Frac) :
    extend (SinglePole.polynomialEquiv g) x=SinglePole.fractionEquiv g x := rfl

def normPolyEquiv : TP ≃ₐ[ℚ] TP := AlgEquiv.ofAlgHom A A2 A_comp_A2 (by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [A,A2,AlgHom.comp_apply])

def cyclePolyEquiv : TP ≃ₐ[ℚ] TP := AlgEquiv.ofAlgHom C (C.comp C)
  C_comp_C_comp_C (by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [C,AlgHom.comp_apply])

def swapPolyEquiv : TP ≃ₐ[ℚ] TP := AlgEquiv.ofAlgHom S S S_comp_S S_comp_S

def permutationPolyEquiv (π : Equiv.Perm (Fin 3)) : TP ≃ₐ[ℚ] TP :=
  AlgEquiv.ofAlgHom (permutePoly π) (permutePoly π⁻¹)
    (by rw [permutePoly_mul,inv_mul_cancel,permutePoly_one])
    (by rw [permutePoly_mul,mul_inv_cancel,permutePoly_one])

def signPolyEquiv (s : Finset (Fin 3)) : TP ≃ₐ[ℚ] TP :=
  AlgEquiv.ofAlgHom (signPoly s) (signPoly s)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      by_cases hi : i∈s <;> simp [signPoly,hi,AlgHom.comp_apply])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      by_cases hi : i∈s <;> simp [signPoly,hi,AlgHom.comp_apply])

def fracA : Frac ≃ₐ[ℚ] Frac := extend normPolyEquiv
def fracA2 : Frac ≃ₐ[ℚ] Frac := fracA.trans fracA
def fracC : Frac ≃ₐ[ℚ] Frac := extend cyclePolyEquiv
def fracS : Frac ≃ₐ[ℚ] Frac := extend swapPolyEquiv
def fracPerm (π : Equiv.Perm (Fin 3)) : Frac ≃ₐ[ℚ] Frac := extend (permutationPolyEquiv π)
def fracSign (s : Finset (Fin 3)) : Frac ≃ₐ[ℚ] Frac := extend (signPolyEquiv s)
def fracD12 : Frac ≃ₐ[ℚ] Frac := fracSign {0,1}
def fracD3 : Frac ≃ₐ[ℚ] Frac := fracSign {2}

@[simp] theorem fracA_embed (p : TP) : fracA (embed p)=embed (A p) := extend_embed _ p
@[simp] theorem fracA2_embed (p : TP) : fracA2 (embed p)=embed (A2 p) := by
  change fracA (fracA (embed p))=embed (A2 p)
  rw [fracA_embed,fracA_embed,A_A]
@[simp] theorem fracC_embed (p : TP) : fracC (embed p)=embed (C p) := extend_embed _ p
@[simp] theorem fracS_embed (p : TP) : fracS (embed p)=embed (S p) := extend_embed _ p
@[simp] theorem fracPerm_embed (π : Equiv.Perm (Fin 3)) (p : TP) :
    fracPerm π (embed p)=embed (permutePoly π p) := extend_embed _ p
@[simp] theorem fracSign_embed (s : Finset (Fin 3)) (p : TP) :
    fracSign s (embed p)=embed (signPoly s p) := extend_embed _ p

theorem signPoly_pair : signPoly {0,1}=D12 := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [signPoly,D12]

theorem signPoly_third : signPoly {2}=D3 := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [signPoly,D3]

@[simp] theorem fracD12_embed (p : TP) : fracD12 (embed p)=embed (D12 p) :=
  (fracSign_embed {0,1} p).trans (congrArg embed (DFunLike.congr_fun signPoly_pair p))

@[simp] theorem fracD3_embed (p : TP) : fracD3 (embed p)=embed (D3 p) :=
  (fracSign_embed {2} p).trans (congrArg embed (DFunLike.congr_fun signPoly_third p))

/-- Actual fraction-field automorphisms inherit the cubic identity. -/
theorem fracA_cube (x : Frac) : fracA (fracA (fracA x))=x := by
  have he : fracA.toAlgHom.comp (fracA.toAlgHom.comp fracA.toAlgHom)=AlgHom.id ℚ Frac := by
    apply fraction_ext
    intro p
    change fracA (fracA (fracA (embed p)))=embed p
    rw [fracA_embed,fracA_embed,fracA_embed,A_A_A]
  exact DFunLike.congr_fun he x

theorem fracA_D12 (x : Frac) : fracA (fracD12 x)=fracD12 (fracA x) := by
  have he : fracA.toAlgHom.comp fracD12.toAlgHom=fracD12.toAlgHom.comp fracA.toAlgHom := by
    apply fraction_ext
    intro p
    change fracA (fracD12 (embed p))=fracD12 (fracA (embed p))
    rw [fracD12_embed,fracA_embed,fracA_embed,fracD12_embed,A_D12]
  exact DFunLike.congr_fun he x

theorem fracA_D3 (x : Frac) : fracA (fracD3 x)=fracD3 (fracA x) := by
  have he : fracA.toAlgHom.comp fracD3.toAlgHom=fracD3.toAlgHom.comp fracA.toAlgHom := by
    apply fraction_ext
    intro p
    change fracA (fracD3 (embed p))=fracD3 (fracA (embed p))
    rw [fracD3_embed,fracA_embed,fracA_embed,fracD3_embed,A_D3]
  exact DFunLike.congr_fun he x

/-- Polynomial algebra maps commute with literal binary evaluation. -/
theorem map_binaryEval (e : TP →ₐ[ℚ] TP) (q : BP) (a b : TP) :
    e (binaryLiftEval q a b)=binaryLiftEval q (e a) (e b) := by
  induction q using MvPolynomial.induction_on with
  | C r => simp [binaryLiftEval]
  | add p q hp hq => simp only [binaryLiftEval,map_add] at *; rw [hp,hq]
  | mul_X p i hp =>
    simp only [binaryLiftEval,map_mul,bind₁_X_right] at *
    rw [hp]
    fin_cases i <;> rfl

/-- The full rational tower obeys actual fraction-field substitution. -/
theorem extend_pValue {k : ℕ} (e : TP ≃ₐ[ℚ] TP) (q : Fin k → BP) (a b c : TP) :
    extend e (pValue q a b c)=pValue q (e a) (e b) (e c) := by
  have he (p : BP) (a b : TP) : e (binaryLiftEval p a b)=binaryLiftEval p (e a) (e b) :=
    map_binaryEval e.toAlgHom p a b
  simp only [pValue,numerator,map_div₀,extend_embed,map_sum,map_mul,map_pow,he]

/-- Polynomial seed evaluations also commute with arbitrary actual polynomial automorphisms. -/
theorem map_substitute (e : TP →ₐ[ℚ] TP) (p a b c : TP) :
    e (substitute3 p a b c)=substitute3 p (e a) (e b) (e c) := by
  have he : e.comp (bind₁ ![a,b,c])=bind₁ ![e a,e b,e c] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  exact DFunLike.congr_fun he p

end TernaryPoly.OrdinaryRationalFiber
