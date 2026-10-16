module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd
public import TernaryPeriodPolynomials.Polynomial.Divisibility
public import Mathlib.Tactic.LinearCombination

@[expose] public section


open MvPolynomial

noncomputable section
namespace TernaryPoly

/-- The exact binary period-polynomial relations used by the cyclic lift. -/
structure BinaryPeriodRelations (q : MvPolynomial (Fin 2) ℚ) : Prop where
  swap : bind₁ ![X 1, X 0] q = -q
  even_first : bind₁ ![-X 0, X 1] q = q
  even_second : bind₁ ![X 0, -X 1] q = q
  axis_first : bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0
  axis_second : bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0
  period : q - bind₁ ![X 0 - X 1, X 1] q - bind₁ ![X 0, X 0 - X 1] q = 0

/-- Evaluate the binary polynomial in two ternary polynomial arguments. -/
def binaryLiftEval (q : MvPolynomial (Fin 2) ℚ) (a b : TernaryPolynomial) :
    TernaryPolynomial := bind₁ ![a,b] q

private theorem bind_vec2 (u v : MvPolynomial (Fin 2) ℚ) (a b : TernaryPolynomial) :
    (fun i => bind₁ ![a,b] (![u,v] i)) = ![bind₁ ![a,b] u, bind₁ ![a,b] v] := by
  funext i
  fin_cases i <;> rfl

/-- Alternation persists after arbitrary polynomial substitution. -/
theorem binaryLiftEval_swap {q : MvPolynomial (Fin 2) ℚ} (hq : BinaryPeriodRelations q)
    (a b : TernaryPolynomial) : binaryLiftEval q b a = -binaryLiftEval q a b := by
  have h := congrArg (fun g => binaryLiftEval g a b) hq.swap
  simpa [binaryLiftEval, bind₁_bind₁, bind_vec2] using h

/-- Evenness in the first variable persists after substitution. -/
theorem binaryLiftEval_neg_first {q : MvPolynomial (Fin 2) ℚ} (hq : BinaryPeriodRelations q)
    (a b : TernaryPolynomial) : binaryLiftEval q (-a) b = binaryLiftEval q a b := by
  have h := congrArg (fun g => binaryLiftEval g a b) hq.even_first
  simpa [binaryLiftEval, bind₁_bind₁, bind_vec2] using h

/-- Evenness in the second variable persists after substitution. -/
theorem binaryLiftEval_neg_second {q : MvPolynomial (Fin 2) ℚ} (hq : BinaryPeriodRelations q)
    (a b : TernaryPolynomial) : binaryLiftEval q a (-b) = binaryLiftEval q a b := by
  have h := congrArg (fun g => binaryLiftEval g a b) hq.even_second
  simpa [binaryLiftEval, bind₁_bind₁, bind_vec2] using h

/-- The period identity persists after arbitrary polynomial substitution. -/
theorem binaryLiftEval_period {q : MvPolynomial (Fin 2) ℚ} (hq : BinaryPeriodRelations q)
    (a b : TernaryPolynomial) :
    binaryLiftEval q a b - binaryLiftEval q (a-b) b - binaryLiftEval q a (a-b) = 0 := by
  have h := congrArg (fun g => binaryLiftEval g a b) hq.period
  simpa [binaryLiftEval, bind₁_bind₁, bind_vec2] using h

/-- Compatibility of binary evaluation with ternary substitution. -/
theorem binaryLiftEval_substitute3 (q : MvPolynomial (Fin 2) ℚ)
    (a b x y z : TernaryPolynomial) :
    substitute3 (binaryLiftEval q a b) x y z =
      binaryLiftEval q (substitute3 a x y z) (substitute3 b x y z) := by
  simp only [substitute3, binaryLiftEval, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- The literal cyclic lift of a binary polynomial. -/
def binaryPeriodLift (q : MvPolynomial (Fin 2) ℚ) : TernaryPolynomial :=
  binaryLiftEval q (X 0) (X 1) + binaryLiftEval q (X 1) (X 2) +
    binaryLiftEval q (X 2) (X 0)

/-- The cyclic lift evaluated on an arbitrary triple. -/
theorem binaryPeriodLift_substitute3 (q : MvPolynomial (Fin 2) ℚ)
    (a b c : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) a b c =
      binaryLiftEval q a b + binaryLiftEval q b c + binaryLiftEval q c a := by
  simp only [binaryPeriodLift, substitute3, map_add]
  change substitute3 (binaryLiftEval q (X 0) (X 1)) a b c +
    substitute3 (binaryLiftEval q (X 1) (X 2)) a b c +
    substitute3 (binaryLiftEval q (X 2) (X 0)) a b c = _
  simp only [binaryLiftEval_substitute3]
  simp [substitute3]

/-- The cyclic lift vanishes identically on the coordinate-sum plane. -/
theorem binaryPeriodLift_sum_plane_zero {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) :
    bind₁ (![X 0, X 1, -X 0-X 1] : Fin 3 → TernaryPolynomial) (binaryPeriodLift q) = 0 := by
  change substitute3 (binaryPeriodLift q) (X 0) (X 1) (-X 0-X 1) = 0
  rw [binaryPeriodLift_substitute3, show (-X 0-X 1 : TernaryPolynomial) = -(X 0+X 1) by ring,
    binaryLiftEval_neg_second hq, binaryLiftEval_neg_first hq,
    binaryLiftEval_swap hq (X 0+X 1) (X 1)]
  have h := binaryLiftEval_period hq (X 0+X 1) (X 1)
  simp only [add_sub_cancel_right] at h
  linear_combination -h

/-- The coordinate sum divides the lift, with no bound on the binary degree. -/
theorem coordinate_sum_dvd_binaryPeriodLift {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) : (X 0+X 1+X 2) ∣ binaryPeriodLift q := by
  have hz := binaryPeriodLift_sum_plane_zero hq
  have hv : Function.update (X : Fin 3 → TernaryPolynomial) 2 (-X 0-X 1) =
      ![X 0, X 1, -X 0-X 1] := by
    funext i
    fin_cases i <;> simp
  have h := linear_factor_dvd_of_substitution_zero (binaryPeriodLift q) 2 (-X 0-X 1)
    (by simpa only [hv] using hz)
  convert h using 1; ring

/-- The literal primitive producing both frames of the cyclic lift. -/
def binaryLiftFramePrimitive (q : MvPolynomial (Fin 2) ℚ) : TernaryPolynomial :=
  binaryLiftEval q (X 0) (X 1) - binaryLiftEval q (X 0) (X 2-2*X 1)

/-- The primitive evaluated after a ternary substitution. -/
theorem binaryLiftFramePrimitive_substitute3 (q : MvPolynomial (Fin 2) ℚ)
    (a b c : TernaryPolynomial) :
    substitute3 (binaryLiftFramePrimitive q) a b c =
      binaryLiftEval q a b - binaryLiftEval q a (c-2*b) := by
  simp only [binaryLiftFramePrimitive, substitute3, map_sub]
  change substitute3 (binaryLiftEval q (X 0) (X 1)) a b c -
    substitute3 (binaryLiftEval q (X 0) (X 2-2*X 1)) a b c = _
  simp only [binaryLiftEval_substitute3]
  simp [substitute3, map_ofNat]

private theorem first_frame_eval {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) (x y z : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) (z-2*y) (-x) (x-y) =
      (binaryLiftEval q x y - binaryLiftEval q x (z-2*y)) -
        (binaryLiftEval q (x-y) y - binaryLiftEval q (x-y) (z-2*y)) := by
  rw [binaryPeriodLift_substitute3, binaryLiftEval_neg_second hq,
    binaryLiftEval_neg_first hq, binaryLiftEval_swap hq x (z-2*y)]
  have h := binaryLiftEval_period hq x y
  linear_combination -h

private theorem middle_frame_eval {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) (a b y : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) (-b) a (-y) =
      (binaryLiftEval q a y - binaryLiftEval q a (a-b)) -
        (binaryLiftEval q b y - binaryLiftEval q b (a-b)) := by
  rw [binaryPeriodLift_substitute3, binaryLiftEval_neg_first hq,
    binaryLiftEval_neg_second hq, binaryLiftEval_neg_first hq,
    binaryLiftEval_neg_second hq, binaryLiftEval_swap hq a b,
    binaryLiftEval_swap hq b y]
  have h := binaryLiftEval_period hq a (a-b)
  simp only [sub_sub_cancel] at h
  linear_combination h

/-- The first frame of the lift is the literal `Y`-difference of its primitive. -/
theorem alternatingFrame1_binaryPeriodLift {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) :
    alternatingFrame1 (binaryPeriodLift q) =
      binaryLiftFramePrimitive q - alternatingShift (X 1) (binaryLiftFramePrimitive q) := by
  have ht : alternatingShift (X 1) (binaryLiftFramePrimitive q) =
      binaryLiftEval q (X 0-X 1) (X 1) - binaryLiftEval q (X 0-X 1) (X 2-2*X 1) := by
    exact binaryLiftFramePrimitive_substitute3 q (X 0-X 1) (X 1) (X 2)
  rw [alternatingFrame1, first_frame_eval hq, ht, binaryLiftFramePrimitive]

/-- The second frame of the lift is the literal `Z`-difference of the same primitive. -/
theorem alternatingFrame2_binaryPeriodLift {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) :
    alternatingFrame2 (binaryPeriodLift q) =
      binaryLiftFramePrimitive q - alternatingShift (X 2) (binaryLiftFramePrimitive q) := by
  have hm := middle_frame_eval hq (X 0-2*X 1) (X 0-X 2) (X 1)
  rw [show -(X 0-X 2 : TernaryPolynomial) = X 2-X 0 by ring,
    show (X 0-2*X 1)-(X 0-X 2 : TernaryPolynomial) = X 2-2*X 1 by ring] at hm
  have hl := first_frame_eval hq (X 0-X 1) (X 1) (X 2)
  rw [show -(X 0-X 1 : TernaryPolynomial) = X 1-X 0 by ring,
    show (X 0-X 1)-(X 1 : TernaryPolynomial) = X 0-2*X 1 by ring] at hl
  have ht : alternatingShift (X 2) (binaryLiftFramePrimitive q) =
      binaryLiftEval q (X 0-X 2) (X 1) - binaryLiftEval q (X 0-X 2) (X 2-2*X 1) := by
    exact binaryLiftFramePrimitive_substitute3 q (X 0-X 2) (X 1) (X 2)
  rw [alternatingFrame2, alternatingFrame1, first_frame_eval hq, hm, hl,
    ht, binaryLiftFramePrimitive]
  abel

private theorem todd_reverse_difference {R : Type*} [CommRing R] [Algebra ℚ R]
    (u : R) (p : Polynomial R) :
    todd u (p - Polynomial.taylor (-u) p) = u • Polynomial.derivative p := by
  rw [show p - Polynomial.taylor (-u) p = -(Polynomial.taylor (-u) p-p) by abel,
    map_neg, todd_difference]
  simp

/-- The entire alternating Todd expression vanishes on every binary period lift. -/
theorem alternatingTodd_binaryPeriodLift_eq_zero {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) : alternatingTodd (binaryPeriodLift q) = 0 := by
  apply (finSuccEquiv ℚ 2).injective
  rw [map_zero, finSuccEquiv_alternatingTodd, alternatingFrame1_binaryPeriodLift hq,
    alternatingFrame2_binaryPeriodLift hq]
  simp only [map_sub (finSuccEquiv ℚ 2), alternatingShift,
    finSuccEquiv_shift_Y, finSuccEquiv_shift_Z]
  rw [todd_reverse_difference, todd_reverse_difference]
  simp only [smul_smul, mul_comm (X (1 : Fin 2)) (X 0), sub_self]

end TernaryPoly
