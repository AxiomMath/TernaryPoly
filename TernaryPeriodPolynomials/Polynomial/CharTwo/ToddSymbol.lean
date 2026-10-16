module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.CoefficientRestriction
public import TernaryPeriodPolynomials.Polynomial.CharTwo.SquaredCoefficients
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoToddSymbol

abbrev Poly := CharTwoNorm.Poly

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
abbrev x : Poly := X 0
abbrev y : Poly := X 1
abbrev z : Poly := X 2

def alpha : Poly := y+z
def U : Poly := y*alpha^2*(x+z)*(x+y+z)
def V : Poly := z*alpha*(x+y)*(x+y+z)
def W : Poly := x*y^2*(x+y)*alpha

/-- Evaluation in elementary source coordinates of the first ordered triple. -/
def evalU : Poly →ₐ[ZMod 2] Poly := bind₁ ![alpha,x^2+x*y+y*z,z*x*(x+y)]
/-- Evaluation in elementary source coordinates of the second ordered triple. -/
def evalV : Poly →ₐ[ZMod 2] Poly := bind₁ ![alpha,x^2+x*z+y*z,x*y*(x+z)]
/-- Evaluation in elementary source coordinates of the third ordered triple. -/
def evalW : Poly →ₐ[ZMod 2] Poly := bind₁ ![alpha,x^2+x*y+z^2,z*(x+z)*(x+y+z)]

/-- The formal common coefficient ring, with all three Dickson invariants squared. -/
def formalSquaredInvariantEval : Poly →ₐ[ZMod 2] Poly :=
  bind₁ ![CharTwoFormal.d4^2,CharTwoFormal.d6^2,CharTwoFormal.d7^2]

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) :=
  CharP.cast_eq_mod Poly 2 n

/-- The U evaluation fixes the d4 Dickson invariant. -/
theorem evalU_d4 : evalU CharTwoFormal.d4 = CharTwoNorm.d4 := by
  simp [evalU, CharTwoFormal.d4, CharTwoFormal.a, CharTwoFormal.b, CharTwoFormal.c,
    alpha, x, y, z, CharTwoNorm.d4, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The U evaluation fixes the d6 Dickson invariant. -/
theorem evalU_d6 : evalU CharTwoFormal.d6 = CharTwoNorm.d6 := by
  simp [evalU, CharTwoFormal.d6, CharTwoFormal.a, CharTwoFormal.b, CharTwoFormal.c,
    alpha, x, y, z, CharTwoNorm.d6, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The U evaluation fixes the d7 Dickson invariant. -/
theorem evalU_d7 : evalU CharTwoFormal.d7 = CharTwoNorm.d7 := by
  simp [evalU, CharTwoFormal.d7, CharTwoFormal.a, CharTwoFormal.b, CharTwoFormal.c,
    alpha, x, y, z, CharTwoNorm.d7, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c,
    CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The V evaluation fixes the d4 Dickson invariant. -/
theorem evalV_d4 : evalV CharTwoFormal.d4 = CharTwoNorm.d4 := by
  simp [evalV, CharTwoFormal.d4, CharTwoFormal.a, CharTwoFormal.b, CharTwoFormal.c,
    alpha, x, y, z, CharTwoNorm.d4, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The V evaluation fixes the d6 Dickson invariant. -/
theorem evalV_d6 : evalV CharTwoFormal.d6 = CharTwoNorm.d6 := by
  simp [evalV, CharTwoFormal.d6, CharTwoFormal.a, CharTwoFormal.b, CharTwoFormal.c,
    alpha, x, y, z, CharTwoNorm.d6, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The V evaluation fixes the d7 Dickson invariant. -/
theorem evalV_d7 : evalV CharTwoFormal.d7 = CharTwoNorm.d7 := by
  simp [evalV, CharTwoFormal.d7, CharTwoFormal.a, CharTwoFormal.b, CharTwoFormal.c,
    alpha, x, y, z, CharTwoNorm.d7, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c,
    CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The W evaluation fixes the d4 Dickson invariant. -/
theorem evalW_d4 : evalW CharTwoFormal.d4 = CharTwoNorm.d4 := by
  simp [evalW, CharTwoFormal.d4, CharTwoFormal.a, CharTwoFormal.b, CharTwoFormal.c,
    alpha, x, y, z, CharTwoNorm.d4, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The W evaluation fixes the d6 Dickson invariant. -/
theorem evalW_d6 : evalW CharTwoFormal.d6 = CharTwoNorm.d6 := by
  simp [evalW, CharTwoFormal.d6, CharTwoFormal.a, CharTwoFormal.b, CharTwoFormal.c,
    alpha, x, y, z, CharTwoNorm.d6, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The W evaluation fixes the d7 Dickson invariant. -/
theorem evalW_d7 : evalW CharTwoFormal.d7 = CharTwoNorm.d7 := by
  simp [evalW, CharTwoFormal.d7, CharTwoFormal.a, CharTwoFormal.b, CharTwoFormal.c,
    alpha, x, y, z, CharTwoNorm.d7, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c,
    CharTwoNorm.cplus]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem eval_squared_coefficients (t : Poly →ₐ[ZMod 2] Poly)
    (h4 : t CharTwoFormal.d4 = CharTwoNorm.d4)
    (h6 : t CharTwoFormal.d6 = CharTwoNorm.d6)
    (h7 : t CharTwoFormal.d7 = CharTwoNorm.d7) (q : Poly) :
    t (formalSquaredInvariantEval q) = CharTwoNorm.squaredInvariantEval q := by
  have he : t.comp formalSquaredInvariantEval = CharTwoNorm.squaredInvariantEval := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [formalSquaredInvariantEval, CharTwoNorm.squaredInvariantEval, h4,h6,h7]
  exact DFunLike.congr_fun he q

/-- Every formal square-invariant coefficient evaluates identically at the first triple. -/
theorem evalU_formalSquaredInvariantEval (q : Poly) :
    evalU (formalSquaredInvariantEval q) = CharTwoNorm.squaredInvariantEval q :=
  eval_squared_coefficients evalU evalU_d4 evalU_d6 evalU_d7 q

/-- Every formal square-invariant coefficient evaluates identically at the second triple. -/
theorem evalV_formalSquaredInvariantEval (q : Poly) :
    evalV (formalSquaredInvariantEval q) = CharTwoNorm.squaredInvariantEval q :=
  eval_squared_coefficients evalV evalV_d4 evalV_d6 evalV_d7 q

/-- Every formal square-invariant coefficient evaluates identically at the third triple. -/
theorem evalW_formalSquaredInvariantEval (q : Poly) :
    evalW (formalSquaredInvariantEval q) = CharTwoNorm.squaredInvariantEval q :=
  eval_squared_coefficients evalW evalW_d4 evalW_d6 evalW_d7 q

private theorem pderiv_squaredEval_zero (u v w q : Poly) (i : Fin 3) :
    pderiv i ((bind₁ ![u^2,v^2,w^2]) q) = 0 := by
  induction q using MvPolynomial.induction_on with
  | C t => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f j hf =>
    rw [map_mul,pderiv_mul,hf,zero_mul,zero_add]
    fin_cases j <;> simp [CharTwo.two_eq_zero]

/-- All formal derivatives of a square-invariant coefficient vanish. -/
theorem pderiv_formalSquaredInvariantEval_zero (q : Poly) (i : Fin 3) :
    pderiv i (formalSquaredInvariantEval q) = 0 :=
  pderiv_squaredEval_zero _ _ _ q i

/-- All target derivatives of an actual square-invariant coefficient vanish. -/
theorem pderiv_squaredInvariantEval_zero (q : Poly) (i : Fin 3) :
    pderiv i (CharTwoNorm.squaredInvariantEval q) = 0 :=
  pderiv_squaredEval_zero _ _ _ q i

/-- The reduced first-order symbol, as an explicit operator on formal source polynomials. -/
def reducedSymbol (H : Poly) : Poly :=
  y*U^2*(evalU (pderiv 1 H)+z*evalU (pderiv 2 H)) +
    y*z*alpha*V^2*(evalV (pderiv 1 H)+y*evalV (pderiv 2 H)) +
    alpha*W^2*(evalW (pderiv 1 H)+z*evalW (pderiv 2 H))

/-- The full first-order symbol, including its nonzero linear factor. -/
def jSymbol (H : Poly) : Poly := (x+y)*reducedSymbol H

/-- The first differential row of the reduced symbol. -/
def symbolP (H : Poly) : Poly := pderiv 1 (reducedSymbol H)
/-- The second differential row of the reduced symbol. -/
def symbolQ (H : Poly) : Poly := pderiv 2 (reducedSymbol H)

theorem reducedSymbol_zero : reducedSymbol 0 = 0 := by simp [reducedSymbol]

theorem reducedSymbol_add (H K : Poly) :
    reducedSymbol (H+K) = reducedSymbol H+reducedSymbol K := by
  simp only [reducedSymbol,map_add]
  ring

theorem reducedSymbol_sum {ι : Type*} (s : Finset ι) (H : ι → Poly) :
    reducedSymbol (∑ i ∈ s, H i) = ∑ i ∈ s, reducedSymbol (H i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reducedSymbol_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,reducedSymbol_add,ih]

/-- Squared invariant coefficients factor out of the first-order symbol. -/
theorem reducedSymbol_squaredInvariant_mul (q H : Poly) :
    reducedSymbol (formalSquaredInvariantEval q*H) =
      CharTwoNorm.squaredInvariantEval q*reducedSymbol H := by
  have hd (i : Fin 3) : pderiv i (formalSquaredInvariantEval q*H) =
      formalSquaredInvariantEval q*pderiv i H := by
    rw [pderiv_mul,pderiv_formalSquaredInvariantEval_zero,zero_mul,zero_add]
  simp only [reducedSymbol,hd,map_mul,evalU_formalSquaredInvariantEval,
    evalV_formalSquaredInvariantEval,evalW_formalSquaredInvariantEval]
  ring

/-- Every square is killed by the reduced first-order symbol. -/
theorem reducedSymbol_square (H : Poly) : reducedSymbol (H^2) = 0 := by
  simp [reducedSymbol,CharTwo.two_eq_zero]

theorem jSymbol_add (H K : Poly) : jSymbol (H+K) = jSymbol H+jSymbol K := by
  simp only [jSymbol,reducedSymbol_add,mul_add]

theorem jSymbol_sum {ι : Type*} (s : Finset ι) (H : ι → Poly) :
    jSymbol (∑ i ∈ s, H i) = ∑ i ∈ s, jSymbol (H i) := by
  simp only [jSymbol,reducedSymbol_sum,Finset.mul_sum]

theorem jSymbol_squaredInvariant_mul (q H : Poly) :
    jSymbol (formalSquaredInvariantEval q*H) = CharTwoNorm.squaredInvariantEval q*jSymbol H := by
  simp only [jSymbol,reducedSymbol_squaredInvariant_mul]
  ring

theorem symbolP_add (H K : Poly) : symbolP (H+K) = symbolP H+symbolP K := by
  simp only [symbolP,reducedSymbol_add,map_add]
theorem symbolQ_add (H K : Poly) : symbolQ (H+K) = symbolQ H+symbolQ K := by
  simp only [symbolQ,reducedSymbol_add,map_add]

theorem symbolP_sum {ι : Type*} (s : Finset ι) (H : ι → Poly) :
    symbolP (∑ i ∈ s, H i) = ∑ i ∈ s, symbolP (H i) := by
  simp only [symbolP,reducedSymbol_sum,map_sum]
theorem symbolQ_sum {ι : Type*} (s : Finset ι) (H : ι → Poly) :
    symbolQ (∑ i ∈ s, H i) = ∑ i ∈ s, symbolQ (H i) := by
  simp only [symbolQ,reducedSymbol_sum,map_sum]

/-- Differentiation preserves square-invariant coefficient linearity of the first row. -/
theorem symbolP_squaredInvariant_mul (q H : Poly) :
    symbolP (formalSquaredInvariantEval q*H) = CharTwoNorm.squaredInvariantEval q*symbolP H := by
  simp only [symbolP,reducedSymbol_squaredInvariant_mul,pderiv_mul,
    pderiv_squaredInvariantEval_zero,zero_mul,zero_add]

/-- Differentiation preserves square-invariant coefficient linearity of the second row. -/
theorem symbolQ_squaredInvariant_mul (q H : Poly) :
    symbolQ (formalSquaredInvariantEval q*H) = CharTwoNorm.squaredInvariantEval q*symbolQ H := by
  simp only [symbolQ,reducedSymbol_squaredInvariant_mul,pderiv_mul,
    pderiv_squaredInvariantEval_zero,zero_mul,zero_add]

private theorem x_add_y_ne_zero : x+y ≠ 0 := by
  intro h
  have he := congrArg (eval (![1,0,0] : Fin 3 → ZMod 2)) h
  norm_num [x,y] at he

/-- Cancelling the nonzero prefactor turns a zero full symbol into a zero reduced symbol. -/
theorem reducedSymbol_zero_of_jSymbol_zero {H : Poly} (h : jSymbol H = 0) :
    reducedSymbol H = 0 := by
  exact (mul_eq_zero.mp h).resolve_left x_add_y_ne_zero

/-- A zero full symbol forces both differential rows to vanish. -/
theorem rows_zero_of_jSymbol_zero {H : Poly} (h : jSymbol H = 0) :
    symbolP H = 0 ∧ symbolQ H = 0 := by
  have hz := reducedSymbol_zero_of_jSymbol_zero h
  simp [symbolP,symbolQ,hz]

end TernaryPoly.CharTwoToddSymbol
