module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Polynomial

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueGeneral
open OrdinaryResiduePolynomial

/-- The residue symmetries, before imposing the binary period relation. -/
structure SymmetricOdd (q : BP) : Prop where
  swap : bind₁ ![X 1,X 0] q=q
  odd_first : bind₁ ![-X 0,X 1] q= -q
  odd_second : bind₁ ![X 0,-X 1] q= -q

theorem of_period {q : BP} (h : SymmetricBinaryPeriodRelations q) : SymmetricOdd q :=
  ⟨h.swap,h.odd_first,h.odd_second⟩

private theorem bind_vec2 (u v : BP) (a b : TP) :
    (fun i => bind₁ ![a,b] (![u,v] i))=![bind₁ ![a,b] u,bind₁ ![a,b] v] := by
  funext i
  fin_cases i <;> rfl

theorem eval_swap {q : BP} (h : SymmetricOdd q) (a b : TP) :
    binaryLiftEval q b a=binaryLiftEval q a b := by
  have he := congrArg (fun p => binaryLiftEval p a b) h.swap
  simpa [binaryLiftEval,bind₁_bind₁,bind_vec2] using he

theorem eval_neg_first {q : BP} (h : SymmetricOdd q) (a b : TP) :
    binaryLiftEval q (-a) b= -binaryLiftEval q a b := by
  have he := congrArg (fun p => binaryLiftEval p a b) h.odd_first
  simpa [binaryLiftEval,bind₁_bind₁,bind_vec2] using he

theorem eval_neg_second {q : BP} (h : SymmetricOdd q) (a b : TP) :
    binaryLiftEval q a (-b)= -binaryLiftEval q a b := by
  have he := congrArg (fun p => binaryLiftEval p a b) h.odd_second
  simpa [binaryLiftEval,bind₁_bind₁,bind_vec2] using he

/-- The binary relation is retained as a genuine polynomial until norm cancellation proves it. -/
def periodDefect (q : BP) : BP := q-bind₁ ![X 0-X 1,X 1] q+bind₁ ![X 0,X 0-X 1] q

theorem periodDefect_eval (q : BP) (a b : TP) :
    binaryLiftEval (periodDefect q) a b=
      binaryLiftEval q a b-binaryLiftEval q (a-b) b+binaryLiftEval q a (a-b) := by
  simp [periodDefect,binaryLiftEval,bind₁_bind₁,bind_vec2]

theorem period_iff {q : BP} (h : SymmetricOdd q) :
    periodDefect q=0 ↔ SymmetricBinaryPeriodRelations q := by
  constructor
  · exact fun hp => ⟨h.swap,h.odd_first,h.odd_second,hp⟩
  · exact fun hp => hp.period

private theorem bind_binary (q : BP) (x y a b c : TP) :
    bind₁ ![a,b,c] (binaryLiftEval q x y)=
      binaryLiftEval q (bind₁ ![a,b,c] x) (bind₁ ![a,b,c] y) := by
  exact binaryLiftEval_substitute3 q x y a b c

private theorem numerator_substitute (q : BP) (a b c : TP) :
    substitute3 (numerator q) a b c=
      a^2*binaryLiftEval q a c-b^2*binaryLiftEval q b c-(a-b)^2*binaryLiftEval q (a-b) c := by
  simp only [numerator,substitute3,map_sub,map_mul,map_pow,bind_binary,
    bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

/-- Polynomial denominator cancellation uses only oddness, not the binary norm relation. -/
theorem denominator_dvd_general (q : BP) (h : SymmetricOdd q) : denominator ∣ numerator q := by
  have h0v : Function.update (X : Fin 3 → TP) 0 0=![0,X 1,X 2] := by
    funext i; fin_cases i <;> simp
  have h1v : Function.update (X : Fin 3 → TP) 1 0=![X 0,0,X 2] := by
    funext i; fin_cases i <;> simp
  have hdv : Function.update (X : Fin 3 → TP) 0 (X 1)=![X 1,X 1,X 2] := by
    funext i; fin_cases i <;> simp
  have hz0 : bind₁ (Function.update X 0 (0 : TP)) (numerator q)=0 := by
    rw [h0v]
    change substitute3 (numerator q) 0 (X 1) (X 2)=0
    rw [numerator_substitute,zero_sub,eval_neg_first h]
    ring
  have hz1 : bind₁ (Function.update X 1 (0 : TP)) (numerator q)=0 := by
    rw [h1v]
    change substitute3 (numerator q) (X 0) 0 (X 2)=0
    rw [numerator_substitute]
    simp
  have hzd : bind₁ (Function.update X 0 (X 1 : TP)) (numerator q)=0 := by
    rw [hdv]
    change substitute3 (numerator q) (X 1) (X 1) (X 2)=0
    rw [numerator_substitute]
    simp
  have h0 : (X 0 : TP)∣numerator q := by
    simpa only [sub_zero] using linear_factor_dvd_of_substitution_zero (numerator q) 0 0 hz0
  have h1 : (X 0*X 1 : TP)∣numerator q := by
    have he := mul_linear_factor_dvd_of_substitution_zero (numerator q) (X 0) 1 0 h0 hz1
      (by simpa only [h1v,bind₁_X_right,Matrix.cons_val_zero] using X_ne_zero (R := ℚ) (0 : Fin 3))
    simpa only [sub_zero] using he
  apply mul_linear_factor_dvd_of_substitution_zero (numerator q) (X 0*X 1) 0 (X 1) h1 hzd
  simpa only [hdv,map_mul,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one] using
    mul_ne_zero (X_ne_zero (R := ℚ) (1 : Fin 3)) (X_ne_zero (R := ℚ) (1 : Fin 3))

def polynomialDefect (q : BP) (h : SymmetricOdd q) : TP :=
  Classical.choose (denominator_dvd_general q h)

theorem numerator_eq (q : BP) (h : SymmetricOdd q) :
    numerator q=denominator*polynomialDefect q h := Classical.choose_spec (denominator_dvd_general q h)

end TernaryPoly.OrdinaryResidueGeneral
