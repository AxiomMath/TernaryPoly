module

public import TernaryPeriodPolynomials.Polynomial.Parity
public import TernaryPeriodPolynomials.AlternatingSolution.Certificate

@[expose] public section

open MvPolynomial

noncomputable section

namespace TernaryPoly

/-- The binary boundary polynomial, viewed in the ternary polynomial ring. -/
def alternatingPlaneH (f : TernaryPolynomial) : TernaryPolynomial :=
  substitute3 f (-X 1) (X 0) (X 1-X 0)

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

private theorem plane_frame1_expand (f : TernaryPolynomial) :
    bind₁ ![X 0, X 1, 3*X 1] (alternatingFrame1 f) =
      substitute3 f (X 1) (-X 0) (X 0-X 1) := by
  change substitute3 (substitute3 f (X 2-2*X 1) (-X 0) (X 0-X 1))
    (X 0) (X 1) (3*X 1) = _
  rw [substitute3_substitute3]
  have h : substitute3 (X 2-2*X 1) (X 0) (X 1) (3*X 1) = X 1 := by
    simp [substitute3, map_ofNat]
    ring
  rw [h]
  simp [substitute3]

/-- Odd parity determines the first frame on the plane `Z = 3Y`. -/
theorem alternatingFrame1_plane {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) :
    bind₁ ![X 0, X 1, 3*X 1] (alternatingFrame1 f) = -alternatingPlaneH f := by
  rw [plane_frame1_expand]
  have h := substitute3_neg_odd hf hn (-X 1) (X 0) (X 1-X 0)
  simpa [alternatingPlaneH] using h

/-- The second frame restricts to minus three consecutive translates of the boundary polynomial. -/
theorem alternatingFrame2_plane {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = -f) :
    bind₁ ![X 0, X 1, 3*X 1] (alternatingFrame2 f) =
      -(alternatingPlaneH f + alternatingShift (X 1) (alternatingPlaneH f) +
        alternatingShift (2*X 1) (alternatingPlaneH f)) := by
  have hmiddle : bind₁ ![X 0, X 1, 3*X 1]
      (substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1)) =
      -alternatingShift (2*X 1) (alternatingPlaneH f) := by
    change substitute3 (substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1))
      (X 0) (X 1) (3*X 1) = _
    rw [substitute3_substitute3, alternatingPlaneH_shift]
    have h := substitute3_reverse hc hs (-X 1) (X 0-2*X 1) (3*X 1-X 0)
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
  rw [alternatingFrame2, map_add, map_add, alternatingFrame1_plane hf hn,
    hmiddle, hlast]
  abel

/-- Odd alternating ternary polynomials give a symmetric binary boundary polynomial. -/
theorem alternatingPlaneH_swap {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hs : S f = -f) :
    S (alternatingPlaneH f) = alternatingPlaneH f := by
  have hneg := substitute3_neg_odd hf hn (-X 1) (X 0) (X 1-X 0)
  have hswap := substitute3_swap hs (X 1) (-X 0) (X 0-X 1)
  change substitute3 (substitute3 f (-X 1) (X 0) (X 1-X 0))
    (X 1) (X 0) (X 2) = _
  rw [substitute3_substitute3]
  have hspec : substitute3 f (substitute3 (-X 1) (X 1) (X 0) (X 2))
      (substitute3 (X 0) (X 1) (X 0) (X 2))
      (substitute3 (X 1-X 0) (X 1) (X 0) (X 2)) =
      substitute3 f (-X 0) (X 1) (X 0-X 1) := by simp [substitute3]
  rw [hspec, hswap]
  simpa [alternatingPlaneH] using congrArg Neg.neg hneg

end TernaryPoly
