module

public import TernaryPeriodPolynomials.SymmetricSolution.BinaryPeriodLift

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The polynomial support-two seed of a nonnegative period layer. -/
def symmetricPeriodSeedQ (r : ℕ) (q : MvPolynomial (Fin 2) ℚ) : TernaryPolynomial :=
  (X 0+X 1)^r*(binaryLiftEval q (X 0) (X 2)+binaryLiftEval q (X 1) (X 2))

/-- The polynomial support-one seed of a nonnegative period layer. -/
def symmetricPeriodSeedP (r : ℕ) (q : MvPolynomial (Fin 2) ℚ) : TernaryPolynomial :=
  X 0^r*binaryLiftEval q (X 1) (X 2)

/-- The binary period relation in its addition form. -/
theorem symmetricBinaryEval_addition {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (a b : TernaryPolynomial) :
    binaryLiftEval q a b=binaryLiftEval q (a+b) b+binaryLiftEval q a (a+b) := by
  have h := symmetricBinaryEval_period hq (a+b) b
  rw [add_sub_cancel_right,symmetricBinaryEval_swap hq a (a+b)] at h
  linear_combination -h

/-- Literal substitution formula for the support-two seed. -/
theorem symmetricPeriodSeedQ_substitute (r : ℕ) (q : MvPolynomial (Fin 2) ℚ)
    (a b c : TernaryPolynomial) :
    substitute3 (symmetricPeriodSeedQ r q) a b c=
      (a+b)^r*(binaryLiftEval q a c+binaryLiftEval q b c) := by
  simp only [symmetricPeriodSeedQ,substitute3,map_mul,map_pow,map_add,bind₁_X_right,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  change (a+b)^r*(substitute3 (binaryLiftEval q (X 0) (X 2)) a b c+
    substitute3 (binaryLiftEval q (X 1) (X 2)) a b c)=_
  rw [binaryLiftEval_substitute3,binaryLiftEval_substitute3]
  simp [substitute3]

/-- Literal substitution formula for the support-one seed. -/
theorem symmetricPeriodSeedP_substitute (r : ℕ) (q : MvPolynomial (Fin 2) ℚ)
    (a b c : TernaryPolynomial) :
    substitute3 (symmetricPeriodSeedP r q) a b c=a^r*binaryLiftEval q b c := by
  simp only [symmetricPeriodSeedP,substitute3,map_mul,map_pow,bind₁_X_right,Matrix.cons_val_zero]
  change a^r*substitute3 (binaryLiftEval q (X 1) (X 2)) a b c=_
  rw [binaryLiftEval_substitute3]
  simp [substitute3]

/-- The support-two seed is symmetric in its first two arguments. -/
theorem symmetricPeriodSeedQ_swap (r : ℕ) (q : MvPolynomial (Fin 2) ℚ) :
    S (symmetricPeriodSeedQ r q)=symmetricPeriodSeedQ r q := by
  change substitute3 (symmetricPeriodSeedQ r q) (X 1) (X 0) (X 2)=_
  rw [symmetricPeriodSeedQ_substitute,symmetricPeriodSeedQ]
  simp only [add_comm]

/-- The support-two seed is odd in its unsupported coordinate. -/
theorem symmetricPeriodSeedQ_odd (r : ℕ) {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ ![X 0,X 1,-X 2] (symmetricPeriodSeedQ r q)= -symmetricPeriodSeedQ r q := by
  change substitute3 (symmetricPeriodSeedQ r q) (X 0) (X 1) (-X 2)=_
  rw [symmetricPeriodSeedQ_substitute,symmetricPeriodSeedQ,
    symmetricBinaryEval_neg_second hq,symmetricBinaryEval_neg_second hq]
  ring

/-- The support-one seed has the exact swap and separate-oddness stabilizer signs. -/
theorem symmetricPeriodSeedP_symmetries (r : ℕ) {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ ![X 0,X 2,X 1] (symmetricPeriodSeedP r q)=symmetricPeriodSeedP r q ∧
    bind₁ ![X 0,-X 1,X 2] (symmetricPeriodSeedP r q)= -symmetricPeriodSeedP r q ∧
    bind₁ ![X 0,X 1,-X 2] (symmetricPeriodSeedP r q)= -symmetricPeriodSeedP r q := by
  change substitute3 (symmetricPeriodSeedP r q) (X 0) (X 2) (X 1)=_ ∧
    substitute3 (symmetricPeriodSeedP r q) (X 0) (-X 1) (X 2)=_ ∧
    substitute3 (symmetricPeriodSeedP r q) (X 0) (X 1) (-X 2)=_
  simp only [symmetricPeriodSeedP_substitute]
  simp only [symmetricPeriodSeedP,
    symmetricBinaryEval_swap hq (X 1) (X 2),symmetricBinaryEval_neg_first hq,
    symmetricBinaryEval_neg_second hq,mul_neg,and_self]

/-- Every nonnegative layer satisfies the first exact mixed equation. -/
theorem symmetricPeriodSeedQ_mixed (r : ℕ) {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (a b c : TernaryPolynomial) :
    substitute3 (symmetricPeriodSeedQ r q) a b (c+a)-
      substitute3 (symmetricPeriodSeedQ r q) a b c=
      substitute3 ((X 0+X 1+X 2)^r*binaryPeriodLift q) (a+c) (-c) b := by
  rw [symmetricPeriodSeedQ_substitute,symmetricPeriodSeedQ_substitute,
    substitute3_W_pow_mul,binaryPeriodLift_substitute3]
  rw [show a+c+-c+b=a+b by ring,symmetricBinaryEval_neg_second hq,
    symmetricBinaryEval_neg_first hq,symmetricBinaryEval_swap hq b c]
  have h := symmetricBinaryEval_addition hq a c
  rw [show c+a=a+c by ring]
  linear_combination -(a+b)^r*h

/-- Every nonnegative layer satisfies the second exact mixed equation. -/
theorem symmetricPeriodSeedP_mixed (r : ℕ) {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (a b c : TernaryPolynomial) :
    substitute3 (symmetricPeriodSeedP r q) a (c+a) b-
      substitute3 (symmetricPeriodSeedP r q) a c b=
      substitute3 (symmetricPeriodSeedQ r q) (-c) (a+c) b := by
  rw [symmetricPeriodSeedP_substitute,symmetricPeriodSeedP_substitute,
    symmetricPeriodSeedQ_substitute,symmetricBinaryEval_neg_first hq]
  rw [show -c+(a+c)=a by ring,show c+a=a+c by ring]
  ring

/-- The pure norm on the last two variables of P is exactly the binary period norm. -/
theorem symmetricPeriodSeedP_norm (r : ℕ) {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (a b c : TernaryPolynomial) :
    substitute3 (symmetricPeriodSeedP r q) a b c+
      substitute3 (symmetricPeriodSeedP r q) a (-c) (b-c)+
      substitute3 (symmetricPeriodSeedP r q) a (c-b) (-b)=0 := by
  rw [symmetricPeriodSeedP_substitute,symmetricPeriodSeedP_substitute,
    symmetricPeriodSeedP_substitute,show c-b=-(b-c) by ring]
  simp only [symmetricBinaryEval_neg_first hq,symmetricBinaryEval_neg_second hq,neg_neg]
  rw [symmetricBinaryEval_swap hq (b-c) c,symmetricBinaryEval_swap hq b (b-c)]
  have h := symmetricBinaryEval_period hq b c
  linear_combination a^r*h

end TernaryPoly
