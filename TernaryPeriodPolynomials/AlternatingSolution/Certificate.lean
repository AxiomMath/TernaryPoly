module

public import TernaryPeriodPolynomials.Polynomial.Operators
public import Mathlib.Tactic.Ring

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

/-- Evaluate a ternary polynomial at three ternary polynomials by substitution. -/
def substitute3 (f a b c : TernaryPolynomial) : TernaryPolynomial :=
  bind₁ ![a, b, c] f

private theorem bind₁_vec3 (a b c x y z : TernaryPolynomial) :
    (fun i => bind₁ ![x, y, z] (![a, b, c] i)) =
      ![bind₁ ![x, y, z] a, bind₁ ![x, y, z] b, bind₁ ![x, y, z] c] := by
  funext i
  fin_cases i <;> rfl

theorem substitute3_substitute3 (f a b c x y z : TernaryPolynomial) :
    substitute3 (substitute3 f a b c) x y z =
      substitute3 f (substitute3 a x y z) (substitute3 b x y z)
        (substitute3 c x y z) := by
  simp only [substitute3, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem substitute3_cyclic {f : TernaryPolynomial} (hc : C f = f)
    (a b c : TernaryPolynomial) : substitute3 f b c a = substitute3 f a b c := by
  have h := congrArg (fun g => substitute3 g a b c) hc
  simpa [C, substitute3, bind₁_bind₁, bind₁_vec3] using h

theorem substitute3_swap {f : TernaryPolynomial} (hs : S f = -f)
    (a b c : TernaryPolynomial) : substitute3 f b a c = -substitute3 f a b c := by
  have h := congrArg (fun g => substitute3 g a b c) hs
  simpa [S, substitute3, bind₁_bind₁, bind₁_vec3] using h

theorem substitute3_swap_last {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = -f) (a b c : TernaryPolynomial) :
    substitute3 f a c b = -substitute3 f a b c := by
  rw [substitute3_cyclic hc b a c, substitute3_swap hs a b c]

theorem substitute3_reverse {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = -f) (a b c : TernaryPolynomial) :
    substitute3 f c b a = -substitute3 f a b c := by
  rw [substitute3_swap hs b c a, substitute3_cyclic hc a b c]

theorem substitute3_norm (f a b c : TernaryPolynomial) :
    substitute3 (N f) a b c = substitute3 f a b c +
      substitute3 f (-b) (a-b) c + substitute3 f (b-a) (-a) c := by
  simp [N_apply, A, A2, substitute3, bind₁_bind₁, bind₁_vec3]

/-- The four-term defect whose translates give the alternating curl. -/
def alternatingDefect (f r s t : TernaryPolynomial) : TernaryPolynomial :=
  substitute3 f (r+s+t) (-s-t) s - substitute3 f (r+t) (-t) s +
    substitute3 f (r+s+t) (-r-t) r - substitute3 f (s+t) (-t) r

/-- An exact certificate expressing the alternating defect as four norms. -/
theorem alternating_four_norm {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = -f) (r s t : TernaryPolynomial) :
    alternatingDefect f r s t =
      substitute3 (N f) (-r-t) (-r) (s+t) +
      substitute3 (N f) (-s-t) (-s) (r+t) +
      substitute3 (N f) (-r-s-t) (-s-t) (-r-t) +
      substitute3 (N f) s (r+s+t) (-s-t) := by
  have h1 := substitute3_reverse hc hs (-r-t) (-r) (s+t)
  have h2 := substitute3_reverse hc hs (-s-t) (-s) (r+t)
  have h3 := substitute3_swap_last hc hs t (r+t) (s+t)
  have h4 := substitute3_swap_last hc hs (-r-s-t) (-s-t) (-r-t)
  have h5 := substitute3_reverse hc hs (s+t) (-t) r
  have h6 := substitute3_reverse hc hs (r+t) (-t) s
  have h7 := substitute3_cyclic hc r (r+s+t) (-r-t)
  have h8 := substitute3_cyclic hc s (r+s+t) (-s-t)
  have n1 : substitute3 (N f) (-r-t) (-r) (s+t) =
      substitute3 f (-r-t) (-r) (s+t) + substitute3 f r (-t) (s+t) +
        substitute3 f t (r+t) (s+t) := by
    rw [substitute3_norm]
    congr 3 <;> abel
  have n2 : substitute3 (N f) (-s-t) (-s) (r+t) =
      substitute3 f (-s-t) (-s) (r+t) + substitute3 f s (-t) (r+t) +
        substitute3 f t (s+t) (r+t) := by
    rw [substitute3_norm]
    congr 3 <;> abel
  have n3 : substitute3 (N f) (-r-s-t) (-s-t) (-r-t) =
      substitute3 f (-r-s-t) (-s-t) (-r-t) +
        substitute3 f (s+t) (-r) (-r-t) +
        substitute3 f r (r+s+t) (-r-t) := by
    rw [substitute3_norm]
    congr 3 <;> abel
  have n4 : substitute3 (N f) s (r+s+t) (-s-t) =
      substitute3 f s (r+s+t) (-s-t) +
        substitute3 f (-r-s-t) (-r-t) (-s-t) +
        substitute3 f (r+t) (-s) (-s-t) := by
    rw [substitute3_norm]
    congr 3 <;> abel
  rw [n1, n2, n3, n4, h1, h2, h3, h4, h5, h6, ← h7, ← h8]
  unfold alternatingDefect
  abel

/-- Translation in the first coordinate by a polynomial parameter. -/
def alternatingShift (u : TernaryPolynomial) :
    TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![X 0 - u, X 1, X 2]

/-- The first untwisted alternating frame. -/
def alternatingFrame1 (f : TernaryPolynomial) : TernaryPolynomial :=
  substitute3 f (X 2 - 2 * X 1) (-X 0) (X 0 - X 1)

/-- The second untwisted alternating frame; all three signs are positive. -/
def alternatingFrame2 (f : TernaryPolynomial) : TernaryPolynomial :=
  alternatingFrame1 f + substitute3 f (X 2 - X 0) (X 0 - 2 * X 1) (-X 1) +
    substitute3 f (X 2 - 2 * X 1) (X 1 - X 0) (X 0 - 2 * X 1)

private theorem alternatingShift_substitute3 (u f a b c : TernaryPolynomial) :
    alternatingShift u (substitute3 f a b c) = substitute3 f
      (alternatingShift u a) (alternatingShift u b) (alternatingShift u c) := by
  exact substitute3_substitute3 f a b c (X 0-u) (X 1) (X 2)

private theorem alternatingShift_frame1 (f : TernaryPolynomial) :
    alternatingShift (X 1) (alternatingFrame1 f) =
      substitute3 f (X 2 - 2 * X 1) (X 1 - X 0) (X 0 - 2 * X 1) := by
  rw [alternatingFrame1, alternatingShift_substitute3]
  simp only [alternatingShift, map_sub, map_mul, map_ofNat, map_neg,
    bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  congr 1 <;> ring

/-- The curl of the two literal alternating frames. -/
def alternatingCurl (f : TernaryPolynomial) : TernaryPolynomial :=
  (alternatingShift (X 1) (alternatingFrame2 f) - alternatingFrame2 f) -
    (alternatingShift (X 2) (alternatingFrame1 f) - alternatingFrame1 f)

private theorem alternatingCurl_expand (f : TernaryPolynomial) :
    alternatingCurl f =
      substitute3 f (X 2-X 0+X 1) (X 0-3*X 1) (-X 1) +
      substitute3 f (X 2-2*X 1) (2*X 1-X 0) (X 0-3*X 1) -
      substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1) -
      substitute3 f (X 2-2*X 1) (X 2-X 0) (X 0-X 1-X 2) := by
  have h1 : alternatingShift (X 1)
      (substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1)) =
      substitute3 f (X 2-X 0+X 1) (X 0-3*X 1) (-X 1) := by
    rw [alternatingShift_substitute3]
    simp only [alternatingShift, map_sub, map_mul, map_ofNat, map_neg,
      bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    congr 1 <;> ring
  have h2 : alternatingShift (X 1)
      (substitute3 f (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1)) =
      substitute3 f (X 2-2*X 1) (2*X 1-X 0) (X 0-3*X 1) := by
    rw [alternatingShift_substitute3]
    simp only [alternatingShift, map_sub, map_mul, map_ofNat,
      bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    congr 1 <;> ring
  have h3 : alternatingShift (X 2) (alternatingFrame1 f) =
      substitute3 f (X 2-2*X 1) (X 2-X 0) (X 0-X 1-X 2) := by
    rw [alternatingFrame1, alternatingShift_substitute3]
    simp only [alternatingShift, map_sub, map_mul, map_ofNat, map_neg,
      bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    congr 1 <;> ring
  unfold alternatingCurl
  rw [alternatingFrame2, map_add, map_add, alternatingShift_frame1, h1, h2, h3]
  abel

/-- Substitution of the certificate variables gives the literal frame curl. -/
theorem alternatingCurl_eq_defect {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = -f) : alternatingCurl f =
      alternatingDefect f (X 2-X 0) (X 0-3*X 1) (X 1) := by
  have hd : alternatingDefect f (X 2-X 0) (X 0-3*X 1) (X 1) =
      substitute3 f (X 2-2*X 1) (2*X 1-X 0) (X 0-3*X 1) -
      substitute3 f (X 2-X 0+X 1) (-X 1) (X 0-3*X 1) +
      substitute3 f (X 2-2*X 1) (X 0-X 1-X 2) (X 2-X 0) -
      substitute3 f (X 0-2*X 1) (-X 1) (X 2-X 0) := by
    have e1 : (X 2-X 0)+(X 0-3*X 1)+X 1 =
        (X 2-2*X 1 : TernaryPolynomial) := by ring
    have e2 : -(X 0-3*X 1)-X 1 =
        (2*X 1-X 0 : TernaryPolynomial) := by ring
    have e3 : -(X 2-X 0)-X 1 =
        (X 0-X 1-X 2 : TernaryPolynomial) := by ring
    have e4 : (X 0-3*X 1)+X 1 =
        (X 0-2*X 1 : TernaryPolynomial) := by ring
    simp only [alternatingDefect, e1, e2, e3, e4]
  have h1 := substitute3_swap_last hc hs (X 2-X 0+X 1) (-X 1) (X 0-3*X 1)
  have h2 := substitute3_swap_last hc hs (X 2-2*X 1) (X 2-X 0) (X 0-X 1-X 2)
  have h3 := substitute3_cyclic hc (X 2-X 0) (X 0-2*X 1) (-X 1)
  rw [alternatingCurl_expand, hd, h1, h2, h3]
  abel

/-- Alternating period polynomials have zero curl in the untwisted frames. -/
theorem alternatingCurl_eq_zero {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = -f) (hn : N f = 0) : alternatingCurl f = 0 := by
  rw [alternatingCurl_eq_defect hc hs, alternating_four_norm hc hs, hn]
  simp [substitute3]

/-- The zero-curl certificate with the two frame differences exposed. -/
theorem alternating_frames_curl_eq_zero {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = -f) (hn : N f = 0) :
    (alternatingShift (X 1) (alternatingFrame2 f) - alternatingFrame2 f) -
      (alternatingShift (X 2) (alternatingFrame1 f) - alternatingFrame1 f) = 0 :=
  alternatingCurl_eq_zero hc hs hn

end TernaryPoly
