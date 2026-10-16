module

public import TernaryPeriodPolynomials.Polynomial.Operators
public import Mathlib.Tactic.LinearCombination

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly.SymmetricCertificate

abbrev BinaryPolynomial := MvPolynomial (Fin 2) ℚ

/-- Substitute three polynomials into a ternary polynomial. -/
def value {σ : Type*} (f : TernaryPolynomial) (a b c : MvPolynomial σ ℚ) :
    MvPolynomial σ ℚ := bind₁ ![a, b, c] f

variable {σ : Type*} {f : TernaryPolynomial}

lemma value_bind (p : Fin 3 → TernaryPolynomial) (a b c : MvPolynomial σ ℚ) :
    value (bind₁ p f) a b c =
      value f (value (p 0) a b c) (value (p 1) a b c) (value (p 2) a b c) := by
  unfold value
  rw [bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

lemma value_cyclic (hc : C f = f) (a b c : MvPolynomial σ ℚ) :
    value f b c a = value f a b c := by
  have h := congrArg (fun q => value q a b c) hc
  rw [C, value_bind] at h
  simpa [value] using h

lemma value_swap (hs : S f = f) (a b c : MvPolynomial σ ℚ) :
    value f b a c = value f a b c := by
  have h := congrArg (fun q => value q a b c) hs
  rw [S, value_bind] at h
  simpa [value] using h

lemma value_neg (ν : ℚ) (hn : bind₁ ![-X 0, -X 1, -X 2] f = ν • f)
    (a b c : MvPolynomial σ ℚ) :
    value f (-a) (-b) (-c) = ν • value f a b c := by
  have h := congrArg (fun q => value q a b c) hn
  rw [value_bind] at h
  simpa [value] using h

lemma value_norm12 (hn : N f = 0) (a b c : MvPolynomial σ ℚ) :
    value f a b c + value f (-b) (a-b) c + value f (b-a) (-a) c = 0 := by
  have h := congrArg (fun q => value q a b c) hn
  change bind₁ ![a, b, c] (f + A f + A2 f) = bind₁ ![a, b, c] 0 at h
  simp only [map_add, map_zero] at h
  change value f a b c + value (A f) a b c + value (A2 f) a b c = 0 at h
  rw [A, A2, value_bind, value_bind] at h
  simpa [value] using h

lemma value_norm23 (hc : C f = f) (hn : N f = 0)
    (a b c : MvPolynomial σ ℚ) :
    value f a b c + value f a (-c) (b-c) + value f a (c-b) (-b) = 0 := by
  have h := value_norm12 hn b c a
  rw [value_cyclic hc a b c, value_cyclic hc a (-c) (b-c),
    value_cyclic hc a (c-b) (-b)] at h
  exact h

lemma value_norm13 (hc : C f = f) (hs : S f = f) (hn : N f = 0)
    (a b c : MvPolynomial σ ℚ) :
    value f a b c + value f (-c) b (a-c) + value f (c-a) b (-a) = 0 := by
  have h := value_norm23 hc hn b a c
  rw [value_swap hs a b c, value_swap hs (-c) b (a-c),
    value_swap hs (c-a) b (-a)] at h
  exact h

lemma value_swap23 (hc : C f = f) (hs : S f = f)
    (a b c : MvPolynomial σ ℚ) :
    value f a c b = value f a b c := by
  calc
    value f a c b = value f c b a := (value_cyclic hc a c b).symm
    _ = value f b c a := value_swap hs b c a
    _ = value f a b c := value_cyclic hc a b c

/-- The four-norm certificate on the opposite-coordinate plane. -/
lemma opposite_translation (hc : C f = f) (hs : S f = f) (hn : N f = 0)
    (ν : ℚ) (hν : ν ≠ 0) (hp : bind₁ ![-X 0, -X 1, -X 2] f = ν • f)
    (s t : MvPolynomial σ ℚ) :
    value f (s+t) (-(s+t)) t = value f s (-s) t := by
  have n1 := value_norm23 hc hn (-s) (-t) s
  have n2 := value_norm23 hc hn (-(s+t)) (-t) s
  have n3 := value_norm23 hc hn (-(s+t)) (-s) (-s)
  have n4 := value_norm12 hn (-(s+t)) 0 s
  have p1 : value f (-s) (-t) s = ν • value f s (-s) t := by
    rw [value_swap23 hc hs (-s) s (-t)]
    simpa using value_neg ν hp s (-s) t
  have p2 := value_cyclic hc (-(s+t)) (-s) (-s)
  have p3 : value f (-s) (s+t) t = ν • value f (-(s+t)) (-t) s := by
    rw [← value_cyclic hc (-s) (s+t) t]
    simpa using value_neg ν hp (-(s+t)) (-t) s
  have p4 : value f (s+t) (s+t) s = ν • value f (-(s+t)) (-s) (-(s+t)) := by
    rw [value_swap23 hc hs (s+t) s (s+t)]
    simpa using value_neg ν hp (-(s+t)) (-s) (-(s+t))
  have p5 := value_swap hs (s+t) (-(s+t)) t
  have p6 := value_cyclic hc 0 (-(s+t)) s
  have he : ν • (value f (s+t) (-(s+t)) t - value f s (-s) t) = 0 := by
    simp only [Algebra.smul_def] at p1 p3 p4 ⊢
    simp only [sub_eq_add_neg, neg_neg, neg_zero, neg_add, add_zero,
      add_neg_cancel, add_comm, add_assoc]
      at n1 n2 n3 n4 p1 p2 p3 p4 p5 p6 ⊢
    linear_combination -n1 + (algebraMap ℚ (MvPolynomial σ ℚ) ν) * n2 + n3 - n4 +
      p1 + p2 + p3 + p4 - (algebraMap ℚ (MvPolynomial σ ℚ) ν) * p5 - p6
  exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left hν)

lemma value_swap13 (hc : C f = f) (hs : S f = f)
    (a b c : MvPolynomial σ ℚ) :
    value f c b a = value f a b c := by
  calc
    value f c b a = value f b c a := value_swap hs b c a
    _ = value f a b c := value_cyclic hc a b c

/-- The first two-norm certificate on the total-coordinate plane. -/
lemma total_translation_first (hc : C f = f) (hs : S f = f) (hn : N f = 0)
    (hp : bind₁ ![-X 0, -X 1, -X 2] f = f)
    (s t : MvPolynomial σ ℚ) :
    value f (s+t) t (-(s+t)-t) = value f s t (-(s+t)) := by
  have hp' : bind₁ ![-X 0, -X 1, -X 2] f = (1 : ℚ) • f := by simpa using hp
  have n1 := value_norm12 hn (-(s+t)) t s
  have n2 := value_norm23 hc hn (-(s+t+t)) (-t) s
  have p1 := value_swap13 hc hs s t (-(s+t))
  have p2 := value_swap hs (-(s+t+t)) (-t) s
  have p3 : value f (s+t+t) (s+t) s = value f (-(s+t+t)) (-s) (-(s+t)) := by
    rw [value_swap23 hc hs (s+t+t) s (s+t)]
    simpa using (value_neg 1 hp' (s+t+t) s (s+t)).symm
  have p4 := (value_cyclic hc (-(s+t+t)) (s+t) t).symm
  simp only [sub_eq_add_neg, neg_neg, neg_add, add_comm, add_left_comm]
    at n1 n2 p1 p2 p3 p4 ⊢
  linear_combination -n1 + n2 + p1 + p2 + p3 - p4

/-- The second two-norm certificate on the total-coordinate plane. -/
lemma total_translation_second (hc : C f = f) (hs : S f = f) (hn : N f = 0)
    (hp : bind₁ ![-X 0, -X 1, -X 2] f = f)
    (s t : MvPolynomial σ ℚ) :
    value f s (s+t) (-s-(s+t)) = value f s t (-(s+t)) := by
  have hp' : bind₁ ![-X 0, -X 1, -X 2] f = (1 : ℚ) • f := by simpa using hp
  have n1 := value_norm13 hc hs hn (-(s+t)) t s
  have n2 := value_norm23 hc hn (-(s+s+t)) (-s) t
  have p1 := value_swap13 hc hs s t (-(s+t))
  have p2 := value_cyclic hc (-(s+s+t)) (-s) t
  have p3 : value f (s+s+t) t (s+t) = value f (-(s+s+t)) (-t) (-(s+t)) := by
    simpa using (value_neg 1 hp' (s+s+t) t (s+t)).symm
  have p4 := value_swap13 hc hs s (s+t) (-(s+s+t))
  simp only [sub_eq_add_neg, neg_neg, neg_add, add_comm, add_left_comm]
    at n1 n2 p1 p2 p3 p4 ⊢
  linear_combination -n1 + n2 + p1 + p2 + p3 - p4

end TernaryPoly.SymmetricCertificate
