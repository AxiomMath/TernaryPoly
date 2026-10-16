module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodLift
public import TernaryPeriodPolynomials.SymmetricSolution.ToddBoundary

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The symmetric, separately odd binary periods in the symmetric zero-scalar tower. -/
structure SymmetricBinaryPeriodRelations (q : MvPolynomial (Fin 2) ℚ) : Prop where
  swap : bind₁ ![X 1,X 0] q = q
  odd_first : bind₁ ![-X 0,X 1] q = -q
  odd_second : bind₁ ![X 0,-X 1] q = -q
  period : q - bind₁ ![X 0-X 1,X 1] q + bind₁ ![X 0,X 0-X 1] q = 0

private theorem symmetric_bind_vec2 (u v : MvPolynomial (Fin 2) ℚ) (a b : TernaryPolynomial) :
    (fun i => bind₁ ![a,b] (![u,v] i)) = ![bind₁ ![a,b] u,bind₁ ![a,b] v] := by
  funext i
  fin_cases i <;> rfl

theorem symmetricBinaryEval_swap {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (a b : TernaryPolynomial) :
    binaryLiftEval q b a = binaryLiftEval q a b := by
  have h := congrArg (fun g => binaryLiftEval g a b) hq.swap
  simpa [binaryLiftEval,bind₁_bind₁,symmetric_bind_vec2] using h

theorem symmetricBinaryEval_neg_first {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (a b : TernaryPolynomial) :
    binaryLiftEval q (-a) b = -binaryLiftEval q a b := by
  have h := congrArg (fun g => binaryLiftEval g a b) hq.odd_first
  simpa [binaryLiftEval,bind₁_bind₁,symmetric_bind_vec2] using h

theorem symmetricBinaryEval_neg_second {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (a b : TernaryPolynomial) :
    binaryLiftEval q a (-b) = -binaryLiftEval q a b := by
  have h := congrArg (fun g => binaryLiftEval g a b) hq.odd_second
  simpa [binaryLiftEval,bind₁_bind₁,symmetric_bind_vec2] using h

theorem symmetricBinaryEval_period {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (a b : TernaryPolynomial) :
    binaryLiftEval q a b - binaryLiftEval q (a-b) b + binaryLiftEval q a (a-b) = 0 := by
  have h := congrArg (fun g => binaryLiftEval g a b) hq.period
  simpa [binaryLiftEval,bind₁_bind₁,symmetric_bind_vec2] using h

/-- The same cyclic lift is fully symmetric for symmetric binary periods. -/
theorem symmetricBinaryLift_symmetric {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) : S (binaryPeriodLift q) = binaryPeriodLift q := by
  change substitute3 (binaryPeriodLift q) (X 1) (X 0) (X 2) = _
  rw [binaryPeriodLift_substitute3,symmetricBinaryEval_swap hq (X 0) (X 1),
    symmetricBinaryEval_swap hq (X 2) (X 0),symmetricBinaryEval_swap hq (X 1) (X 2)]
  unfold binaryPeriodLift
  abel

/-- The three ternary norm terms reduce to the exact binary period identity. -/
theorem symmetricBinaryLift_norm {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) : N (binaryPeriodLift q) = 0 := by
  change binaryPeriodLift q +
    substitute3 (binaryPeriodLift q) (-X 1) (X 0-X 1) (X 2) +
    substitute3 (binaryPeriodLift q) (X 1-X 0) (-X 0) (X 2) = 0
  rw [binaryPeriodLift_substitute3,binaryPeriodLift_substitute3,
    show (X 1-X 0 : TernaryPolynomial) = -(X 0-X 1) by ring]
  simp only [symmetricBinaryEval_neg_first hq,symmetricBinaryEval_neg_second hq,neg_neg]
  rw [symmetricBinaryEval_swap hq (X 0-X 1) (X 1),
    symmetricBinaryEval_swap hq (X 0) (X 0-X 1),
    symmetricBinaryEval_swap hq (X 1) (X 2),symmetricBinaryEval_swap hq (X 2) (X 0),
    symmetricBinaryEval_swap hq (X 2) (X 0-X 1)]
  unfold binaryPeriodLift
  have h := symmetricBinaryEval_period hq (X 0) (X 1)
  linear_combination h

/-- The cyclic numerator of a symmetric binary period vanishes on the total plane. -/
theorem symmetricBinaryLift_sum_plane_zero {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ (![X 0,X 1,-X 0-X 1] : Fin 3 → TernaryPolynomial) (binaryPeriodLift q) = 0 := by
  change substitute3 (binaryPeriodLift q) (X 0) (X 1) (-X 0-X 1) = 0
  rw [binaryPeriodLift_substitute3,show (-X 0-X 1 : TernaryPolynomial) = -(X 0+X 1) by ring,
    symmetricBinaryEval_neg_second hq,symmetricBinaryEval_neg_first hq,
    symmetricBinaryEval_swap hq (X 0+X 1) (X 1)]
  have h := symmetricBinaryEval_period hq (X 0+X 1) (X 1)
  simp only [add_sub_cancel_right] at h
  linear_combination -h

/-- The apparent denominator in the symmetric period lift is an actual polynomial divisor. -/
theorem coordinate_sum_dvd_symmetricBinaryLift {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) : (X 0+X 1+X 2) ∣ binaryPeriodLift q := by
  have hz := symmetricBinaryLift_sum_plane_zero hq
  have hv : Function.update (X : Fin 3 → TernaryPolynomial) 2 (-X 0-X 1) =
      ![X 0,X 1,-X 0-X 1] := by
    funext i
    fin_cases i <;> simp
  have h := linear_factor_dvd_of_substitution_zero (binaryPeriodLift q) 2 (-X 0-X 1)
    (by simpa only [hv] using hz)
  convert h using 1
  ring

private theorem symmetric_first_frame_eval {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (x y z : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) (z-2*y) (-x) (x-y) =
      (binaryLiftEval q x y-binaryLiftEval q x (z-2*y)) -
        (binaryLiftEval q (x-y) y-binaryLiftEval q (x-y) (z-2*y)) := by
  rw [binaryPeriodLift_substitute3,symmetricBinaryEval_neg_second hq,
    symmetricBinaryEval_neg_first hq,symmetricBinaryEval_swap hq x (z-2*y)]
  have h := symmetricBinaryEval_period hq x y
  linear_combination -h

private theorem symmetric_middle_frame_eval {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) (a b y : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) (-b) a (-y) =
      -((binaryLiftEval q a y-binaryLiftEval q a (a-b)) -
        (binaryLiftEval q b y-binaryLiftEval q b (a-b))) := by
  rw [binaryPeriodLift_substitute3,symmetricBinaryEval_neg_first hq,
    symmetricBinaryEval_neg_second hq,symmetricBinaryEval_neg_first hq,
    symmetricBinaryEval_neg_second hq,symmetricBinaryEval_swap hq a b,
    symmetricBinaryEval_swap hq b y]
  have h := symmetricBinaryEval_period hq a (a-b)
  simp only [sub_sub_cancel] at h
  linear_combination -h

/-- The first corrected symmetric frame is the Y-difference of a polynomial primitive. -/
theorem symmetricFrame1_binaryPeriodLift {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    symmetricFrame1 (binaryPeriodLift q) =
      binaryLiftFramePrimitive q - symmetricShift (X 1) (binaryLiftFramePrimitive q) := by
  have ht : symmetricShift (X 1) (binaryLiftFramePrimitive q) =
      binaryLiftEval q (X 0-X 1) (X 1)-binaryLiftEval q (X 0-X 1) (X 2-2*X 1) :=
    binaryLiftFramePrimitive_substitute3 q (X 0-X 1) (X 1) (X 2)
  rw [symmetricFrame1,symmetric_first_frame_eval hq,ht,binaryLiftFramePrimitive]

/-- The negative middle-frame sign gives the Z-difference of the same primitive. -/
theorem symmetricFrame2_binaryPeriodLift {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    symmetricFrame2 (binaryPeriodLift q) =
      binaryLiftFramePrimitive q - symmetricShift (X 2) (binaryLiftFramePrimitive q) := by
  have hm := symmetric_middle_frame_eval hq (X 0-2*X 1) (X 0-X 2) (X 1)
  rw [show -(X 0-X 2 : TernaryPolynomial) = X 2-X 0 by ring,
    show (X 0-2*X 1)-(X 0-X 2 : TernaryPolynomial) = X 2-2*X 1 by ring] at hm
  have hl := symmetric_first_frame_eval hq (X 0-X 1) (X 1) (X 2)
  rw [show -(X 0-X 1 : TernaryPolynomial) = X 1-X 0 by ring,
    show (X 0-X 1)-(X 1 : TernaryPolynomial) = X 0-2*X 1 by ring] at hl
  have ht : symmetricShift (X 2) (binaryLiftFramePrimitive q) =
      binaryLiftEval q (X 0-X 2) (X 1)-binaryLiftEval q (X 0-X 2) (X 2-2*X 1) :=
    binaryLiftFramePrimitive_substitute3 q (X 0-X 2) (X 1) (X 2)
  rw [symmetricFrame2,symmetricFrame1,symmetric_first_frame_eval hq,hm,hl,ht,binaryLiftFramePrimitive]
  abel

private theorem symmetric_todd_reverse_difference {R : Type*} [CommRing R] [Algebra ℚ R]
    (u : R) (p : Polynomial R) :
    todd u (p-Polynomial.taylor (-u) p) = u • Polynomial.derivative p := by
  rw [show p-Polynomial.taylor (-u) p = -(Polynomial.taylor (-u) p-p) by abel,
    map_neg,todd_difference]
  simp

/-- Every symmetric binary period lift lies in the whole corrected Todd kernel. -/
theorem symmetricTodd_binaryPeriodLift_eq_zero {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) : symmetricTodd (binaryPeriodLift q) = 0 := by
  apply (finSuccEquiv ℚ 2).injective
  rw [map_zero,finSuccEquiv_symmetricTodd,symmetricFrame1_binaryPeriodLift hq,
    symmetricFrame2_binaryPeriodLift hq]
  simp only [map_sub (finSuccEquiv ℚ 2),symmetricShift,finSuccEquiv_shift_Y,finSuccEquiv_shift_Z]
  rw [symmetric_todd_reverse_difference,symmetric_todd_reverse_difference]
  simp only [smul_smul,mul_comm (X (1 : Fin 2)) (X 0),sub_self]

/-- Dividing the cyclic numerator by W gives a genuine polynomial in the same whole Todd kernel. -/
theorem symmetricBinaryLift_exists_quotient {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    ∃ g : TernaryPolynomial, binaryPeriodLift q = (X 0+X 1+X 2)*g ∧ symmetricTodd g = 0 := by
  obtain ⟨g,hg⟩ := coordinate_sum_dvd_symmetricBinaryLift hq
  refine ⟨g,hg,?_⟩
  have hz := symmetricTodd_binaryPeriodLift_eq_zero hq
  rw [hg,show (X 0+X 1+X 2)*g = (X 0+X 1+X 2)^1*g by simp,
    symmetricTodd_W_pow_mul,pow_one] at hz
  have hlin : (X 2-3*X 1 : TernaryPolynomial) ≠ 0 := by
    intro he
    have ht := congrArg (bind₁ (![0,0,1] : Fin 3 → TernaryPolynomial)) he
    simp at ht
  exact (mul_eq_zero.mp hz).resolve_left hlin

end TernaryPoly
