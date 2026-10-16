module

public import TernaryPeriodPolynomials.SymmetricSolution.ToddCertificate
public import TernaryPeriodPolynomials.AlternatingSolution.FirstDerivativeFrames

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-! Literal symmetric first jets. The generic boundary polynomial and its partials
are the same definitions as in the alternating development; only frame signs differ. -/

private theorem substitute3_neg_odd {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (a b c : TernaryPolynomial) :
    substitute3 f (-a) (-b) (-c) = -substitute3 f a b c := by
  have h := congrArg (fun g => substitute3 g a b c) (homogeneous_bind_neg_odd hf hn)
  change substitute3 (substitute3 f (-X 0) (-X 1) (-X 2)) a b c =
    substitute3 (-f) a b c at h
  rw [substitute3_substitute3] at h
  simpa [substitute3] using h

private theorem alternatingPlaneH_shift (f u : TernaryPolynomial) :
    alternatingShift u (alternatingPlaneH f) =
      substitute3 f (-X 1) (X 0-u) (X 1-(X 0-u)) := by
  change substitute3 (substitute3 f (-X 1) (X 0) (X 1-X 0))
    (X 0-u) (X 1) (X 2) = _
  rw [substitute3_substitute3]
  simp [substitute3]

theorem symmetricFrame1_odd_plane {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) :
    bind₁ ![X 0,X 1,3*X 1] (symmetricFrame1 f) = -alternatingPlaneH f :=
  alternatingFrame1_plane hf hn

/-- The second frame restricts to minus three consecutive translates of the boundary polynomial. -/
theorem symmetricFrame2_plane {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = f) :
    bind₁ ![X 0, X 1, 3*X 1] (symmetricFrame2 f) =
      -(alternatingPlaneH f + alternatingShift (X 1) (alternatingPlaneH f) +
        alternatingShift (2*X 1) (alternatingPlaneH f)) := by
  have hmiddle : bind₁ ![X 0, X 1, 3*X 1]
      (substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1)) =
      alternatingShift (2*X 1) (alternatingPlaneH f) := by
    change substitute3 (substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1))
      (X 0) (X 1) (3*X 1) = _
    rw [substitute3_substitute3, alternatingPlaneH_shift]
    have h := symmetric_substitute3_reverse hc hs (-X 1) (X 0-2*X 1) (3*X 1-X 0)
    have he : X 1-(X 0-2*X 1) = (3*X 1-X 0 : TernaryPolynomial) := by ring
    simpa [substitute3, map_ofNat, he] using h
  have hlast : bind₁ ![X 0, X 1, 3*X 1]
      (substitute3 f (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1)) =
      -alternatingShift (X 1) (alternatingPlaneH f) := by
    change substitute3 (substitute3 f (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1))
      (X 0) (X 1) (3*X 1) = _
    rw [substitute3_substitute3, alternatingPlaneH_shift]
    have h := substitute3_neg_odd hf hn (-X 1) (X 0-X 1) (X 1-(X 0-X 1))
    have he1 : 3*X 1-2*X 1 = (X 1 : TernaryPolynomial) := by ring
    have he2 : X 0-X 1-X 1 = (X 0-2*X 1 : TernaryPolynomial) := by ring
    simpa [substitute3, map_ofNat, he1, he2] using h
  rw [symmetricFrame2, map_add, map_sub, symmetricFrame1_odd_plane hf hn,
    hmiddle, hlast]
  abel

private theorem substitute3_id (f : TernaryPolynomial) :
    substitute3 f (X 0) (X 1) (X 2) = f := by
  have ht : (![X 0, X 1, X 2] : Fin 3 → TernaryPolynomial) = X := by
    funext i
    fin_cases i <;> rfl
  simp [substitute3, ht]

private theorem substitute3_pderiv_neg_even {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (i : Fin 3) (a b c : TernaryPolynomial) :
    substitute3 (pderiv i f) (-a) (-b) (-c) = substitute3 (pderiv i f) a b c := by
  have he : Even (n-1) := Nat.Odd.sub_odd hn (by decide : Odd (1 : ℕ))
  have h := congrArg (fun g => substitute3 g a b c)
    (homogeneous_bind_neg_even (hf.pderiv (i := i)) he)
  change substitute3 (substitute3 (pderiv i f) (-X 0) (-X 1) (-X 2)) a b c =
    substitute3 (pderiv i f) a b c at h
  rw [substitute3_substitute3] at h
  simpa [substitute3] using h

/-- Reversal exchanges the first and third derivatives of a symmetric polynomial. -/
theorem symmetric_substitute3_pderiv_reverse {f : TernaryPolynomial} (hc : C f = f)
    (hs : S f = f) (a b c : TernaryPolynomial) :
    substitute3 (pderiv 0 f) c b a = substitute3 (pderiv 2 f) a b c := by
  have hr := symmetric_substitute3_reverse hc hs (X 0) (X 1) (X 2)
  rw [substitute3_id] at hr
  have hd := congrArg (pderiv (2 : Fin 3)) hr
  have hchain : pderiv 2 (substitute3 f (X 2) (X 1) (X 0)) =
      substitute3 (pderiv 0 f) (X 2) (X 1) (X 0) := by
    apply pderiv_bind₁_coordinate _ 2 0 _ f
    intro k
    fin_cases k <;> simp
  rw [hchain] at hd
  have h := congrArg (fun g => substitute3 g a b c) hd
  rw [substitute3_substitute3] at h
  simpa [substitute3] using h

private theorem pderiv_two (i : Fin 3) : pderiv i (2 : TernaryPolynomial) = 0 := by
  have h : pderiv i (MvPolynomial.C (2 : ℚ)) = 0 := pderiv_C
  simpa only [map_ofNat] using h

private theorem pderiv_frame1 (f : TernaryPolynomial) :
    pderiv 2 (alternatingFrame1 f) = alternatingFrame1 (pderiv 0 f) := by
  apply pderiv_bind₁_coordinate _ 2 0 _ f
  intro k
  fin_cases k <;> simp [pderiv_two]

private theorem pderiv_frame_middle (f : TernaryPolynomial) :
    pderiv 2 (substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1)) =
      substitute3 (pderiv 0 f) (X 2-X 0) (X 0-2*X 1) (-X 1) := by
  apply pderiv_bind₁_coordinate _ 2 0 _ f
  intro k
  fin_cases k <;> simp [pderiv_two]

private theorem pderiv_frame_last (f : TernaryPolynomial) :
    pderiv 2 (substitute3 f (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1)) =
      substitute3 (pderiv 0 f) (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1) := by
  apply pderiv_bind₁_coordinate _ 2 0 _ f
  intro k
  fin_cases k <;> simp [pderiv_two]

private theorem planeH_shift (f u : TernaryPolynomial) :
    alternatingShift u (alternatingPlaneH f) =
      substitute3 f (-X 1) (X 0-u) (X 1-(X 0-u)) := by
  change substitute3 (substitute3 f (-X 1) (X 0) (X 1-X 0))
    (X 0-u) (X 1) (X 2) = _
  rw [substitute3_substitute3]
  simp [substitute3]

theorem symmetricFrame1_first_derivative_plane {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) :
    bind₁ ![X 0,X 1,3*X 1] (pderiv 2 (symmetricFrame1 f)) = alternatingPlaneA1 f :=
  alternatingFrame1_first_derivative_plane hf hn

/-- The first normal derivative of the second frame is the stated signed combination of translates. -/
theorem symmetricFrame2_first_derivative_plane {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = f) :
    bind₁ ![X 0, X 1, 3*X 1] (pderiv 2 (symmetricFrame2 f)) =
      alternatingPlaneA1 f + alternatingShift (X 1) (alternatingPlaneA1 f) -
        alternatingShift (2*X 1) (alternatingPlaneD1 f) := by
  have hmiddle : bind₁ ![X 0, X 1, 3*X 1]
      (substitute3 (pderiv 0 f) (X 2-X 0) (X 0-2*X 1) (-X 1)) =
      alternatingShift (2*X 1) (alternatingPlaneD1 f) := by
    change substitute3 (substitute3 (pderiv 0 f) (X 2-X 0) (X 0-2*X 1) (-X 1))
      (X 0) (X 1) (3*X 1) = _
    rw [substitute3_substitute3, alternatingPlaneD1, planeH_shift]
    have h := symmetric_substitute3_pderiv_reverse hc hs (-X 1) (X 0-2*X 1) (3*X 1-X 0)
    have he : X 1-(X 0-2*X 1) = (3*X 1-X 0 : TernaryPolynomial) := by ring
    simpa [substitute3, map_ofNat, he] using h
  have hlast : bind₁ ![X 0, X 1, 3*X 1]
      (substitute3 (pderiv 0 f) (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1)) =
      alternatingShift (X 1) (alternatingPlaneA1 f) := by
    change substitute3 (substitute3 (pderiv 0 f) (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1))
      (X 0) (X 1) (3*X 1) = _
    rw [substitute3_substitute3, alternatingPlaneA1, planeH_shift]
    have h := substitute3_pderiv_neg_even hf hn 0 (-X 1) (X 0-X 1)
      (X 1-(X 0-X 1))
    have he1 : 3*X 1-2*X 1 = (X 1 : TernaryPolynomial) := by ring
    have he2 : X 0-X 1-X 1 = (X 0-2*X 1 : TernaryPolynomial) := by ring
    simpa [substitute3, map_ofNat, he1, he2] using h
  simp only [symmetricFrame2, map_add, map_sub, pderiv_frame_middle, pderiv_frame_last]
  rw [symmetricFrame1_first_derivative_plane hf hn, hmiddle, hlast]
  abel


end TernaryPoly
