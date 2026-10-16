module

public import TernaryPeriodPolynomials.AlternatingSolution.Certificate
public import TernaryPeriodPolynomials.SymmetricSolution.Certificate

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

theorem symmetric_substitute3_swap {f : TernaryPolynomial} (hs : S f = f)
    (a b c : TernaryPolynomial) : substitute3 f b a c = substitute3 f a b c := by
  exact SymmetricCertificate.value_swap hs a b c

theorem symmetric_substitute3_swap_last {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = f) (a b c : TernaryPolynomial) :
    substitute3 f a c b = substitute3 f a b c := by
  rw [substitute3_cyclic hc b a c, symmetric_substitute3_swap hs a b c]

theorem symmetric_substitute3_reverse {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = f) (a b c : TernaryPolynomial) :
    substitute3 f c b a = substitute3 f a b c := by
  rw [symmetric_substitute3_swap hs b c a, substitute3_cyclic hc a b c]

/-- The four-term defect whose translates give the symmetric curl. -/
def symmetricDefect (f r s t : TernaryPolynomial) : TernaryPolynomial :=
  substitute3 f (r+s+t) (-s-t) s - substitute3 f (r+t) (-t) s -
    substitute3 f (r+s+t) (-r-t) r + substitute3 f (s+t) (-t) r

/-- An exact certificate expressing the symmetric defect as four norms. -/
theorem symmetric_four_norm {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = f) (r s t : TernaryPolynomial) :
    symmetricDefect f r s t =
      substitute3 (N f) (-r-t) (-r) (s+t) -
      substitute3 (N f) (-s-t) (-s) (r+t) -
      substitute3 (N f) (-r-s-t) (-s-t) (-r-t) +
      substitute3 (N f) s (r+s+t) (-s-t) := by
  have h1 := symmetric_substitute3_reverse hc hs (-r-t) (-r) (s+t)
  have h2 := symmetric_substitute3_reverse hc hs (-s-t) (-s) (r+t)
  have h3 := symmetric_substitute3_swap_last hc hs t (r+t) (s+t)
  have h4 := symmetric_substitute3_swap_last hc hs (-r-s-t) (-s-t) (-r-t)
  have h5 := symmetric_substitute3_reverse hc hs (s+t) (-t) r
  have h6 := symmetric_substitute3_reverse hc hs (r+t) (-t) s
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
  unfold symmetricDefect
  abel

/-- Translation in the first coordinate by a polynomial parameter. -/
def symmetricShift (u : TernaryPolynomial) :
    TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![X 0 - u, X 1, X 2]

/-- The first untwisted symmetric frame. -/
def symmetricFrame1 (f : TernaryPolynomial) : TernaryPolynomial :=
  substitute3 f (X 2 - 2 * X 1) (-X 0) (X 0 - X 1)

/-- The second symmetric frame, with the corrected negative middle sign. -/
def symmetricFrame2 (f : TernaryPolynomial) : TernaryPolynomial :=
  symmetricFrame1 f - substitute3 f (X 2 - X 0) (X 0 - 2 * X 1) (-X 1) +
    substitute3 f (X 2 - 2 * X 1) (X 1 - X 0) (X 0 - 2 * X 1)

private theorem symmetricShift_substitute3 (u f a b c : TernaryPolynomial) :
    symmetricShift u (substitute3 f a b c) = substitute3 f
      (symmetricShift u a) (symmetricShift u b) (symmetricShift u c) := by
  exact substitute3_substitute3 f a b c (X 0-u) (X 1) (X 2)

private theorem symmetricShift_frame1 (f : TernaryPolynomial) :
    symmetricShift (X 1) (symmetricFrame1 f) =
      substitute3 f (X 2 - 2 * X 1) (X 1 - X 0) (X 0 - 2 * X 1) := by
  rw [symmetricFrame1, symmetricShift_substitute3]
  simp only [symmetricShift, map_sub, map_mul, map_ofNat, map_neg,
    bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  congr 1 <;> ring

/-- The curl of the two literal symmetric frames. -/
def symmetricCurl (f : TernaryPolynomial) : TernaryPolynomial :=
  (symmetricShift (X 1) (symmetricFrame2 f) - symmetricFrame2 f) -
    (symmetricShift (X 2) (symmetricFrame1 f) - symmetricFrame1 f)

private theorem symmetricCurl_expand (f : TernaryPolynomial) :
    symmetricCurl f =
      -substitute3 f (X 2-X 0+X 1) (X 0-3*X 1) (-X 1) +
      substitute3 f (X 2-2*X 1) (2*X 1-X 0) (X 0-3*X 1) +
      substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1) -
      substitute3 f (X 2-2*X 1) (X 2-X 0) (X 0-X 1-X 2) := by
  have h1 : symmetricShift (X 1)
      (substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1)) =
      substitute3 f (X 2-X 0+X 1) (X 0-3*X 1) (-X 1) := by
    rw [symmetricShift_substitute3]
    simp only [symmetricShift, map_sub, map_mul, map_ofNat, map_neg,
      bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    congr 1 <;> ring
  have h2 : symmetricShift (X 1)
      (substitute3 f (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1)) =
      substitute3 f (X 2-2*X 1) (2*X 1-X 0) (X 0-3*X 1) := by
    rw [symmetricShift_substitute3]
    simp only [symmetricShift, map_sub, map_mul, map_ofNat,
      bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    congr 1 <;> ring
  have h3 : symmetricShift (X 2) (symmetricFrame1 f) =
      substitute3 f (X 2-2*X 1) (X 2-X 0) (X 0-X 1-X 2) := by
    rw [symmetricFrame1, symmetricShift_substitute3]
    simp only [symmetricShift, map_sub, map_mul, map_ofNat, map_neg,
      bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    congr 1 <;> ring
  unfold symmetricCurl
  rw [symmetricFrame2, map_add, map_sub, symmetricShift_frame1, h1, h2, h3]
  abel

/-- Substitution of the certificate variables gives the literal frame curl. -/
theorem symmetricCurl_eq_defect {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = f) : symmetricCurl f =
      symmetricDefect f (X 2-X 0) (X 0-3*X 1) (X 1) := by
  have hd : symmetricDefect f (X 2-X 0) (X 0-3*X 1) (X 1) =
      substitute3 f (X 2-2*X 1) (2*X 1-X 0) (X 0-3*X 1) -
      substitute3 f (X 2-X 0+X 1) (-X 1) (X 0-3*X 1) -
      substitute3 f (X 2-2*X 1) (X 0-X 1-X 2) (X 2-X 0) +
      substitute3 f (X 0-2*X 1) (-X 1) (X 2-X 0) := by
    have e1 : (X 2-X 0)+(X 0-3*X 1)+X 1 =
        (X 2-2*X 1 : TernaryPolynomial) := by ring
    have e2 : -(X 0-3*X 1)-X 1 =
        (2*X 1-X 0 : TernaryPolynomial) := by ring
    have e3 : -(X 2-X 0)-X 1 =
        (X 0-X 1-X 2 : TernaryPolynomial) := by ring
    have e4 : (X 0-3*X 1)+X 1 =
        (X 0-2*X 1 : TernaryPolynomial) := by ring
    simp only [symmetricDefect, e1, e2, e3, e4]
  have h1 := symmetric_substitute3_swap_last hc hs (X 2-X 0+X 1) (-X 1) (X 0-3*X 1)
  have h2 := symmetric_substitute3_swap_last hc hs (X 2-2*X 1) (X 2-X 0) (X 0-X 1-X 2)
  have h3 := substitute3_cyclic hc (X 2-X 0) (X 0-2*X 1) (-X 1)
  rw [symmetricCurl_expand, hd, h1, h2, h3]
  abel

/-- Symmetric period polynomials have zero curl in the untwisted frames. -/
theorem symmetricCurl_eq_zero {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = f) (hn : N f = 0) : symmetricCurl f = 0 := by
  rw [symmetricCurl_eq_defect hc hs, symmetric_four_norm hc hs, hn]
  simp [substitute3]

/-- The zero-curl certificate with the two frame differences exposed. -/
theorem symmetric_frames_curl_eq_zero {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = f) (hn : N f = 0) :
    (symmetricShift (X 1) (symmetricFrame2 f) - symmetricFrame2 f) -
      (symmetricShift (X 2) (symmetricFrame1 f) - symmetricFrame1 f) = 0 :=
  symmetricCurl_eq_zero hc hs hn

end TernaryPoly
