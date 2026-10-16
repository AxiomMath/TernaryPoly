module

public import TernaryPeriodPolynomials.Polynomial.Restriction
public import TernaryPeriodPolynomials.PeriodPolynomial.ComplexPeriod.Space

@[expose] public section


/-! # Symmetry sectors and the existing odd binary period space

The comparison maps retain the underlying formal polynomial. In particular, the
existing analytic odd-period theorem can be reused with the paper's space.
-/


open MvPolynomial

noncomputable section
namespace TernaryPoly.Paper

variable {R : Type*} [CommRing R]

/-- Separate oddness persists under substitution. -/
theorem binaryEval_odd_first {σ : Type*} {q : Binary R}
    (hq : bind₁ ![-X 0, X 1] q = -q) (a b : MvPolynomial σ R) :
    binaryEval q (-a) b = -binaryEval q a b := by
  have h := congrArg (fun p => binaryEval p a b) hq
  simpa [binaryEval, bind₁_bind₁, bind_vec2] using h

/-- Separate evenness persists under substitution. -/
theorem binaryEval_even_first {σ : Type*} {q : Binary R}
    (hq : bind₁ ![-X 0, X 1] q = q) (a b : MvPolynomial σ R) :
    binaryEval q (-a) b = binaryEval q a b := by
  have h := congrArg (fun p => binaryEval p a b) hq
  simpa [binaryEval, bind₁_bind₁, bind_vec2] using h

/-- In the full period space, odd first-variable parity means binary symmetry. -/
theorem PeriodRelations.eval_swap_of_odd {σ : Type*} {q : Binary R}
    (hq : PeriodRelations q) (ho : bind₁ ![-X 0, X 1] q = -q)
    (a b : MvPolynomial σ R) : binaryEval q b a = binaryEval q a b := by
  have h := hq.identities.eval_two_term a b
  rw [binaryEval_odd_first ho] at h
  linear_combination -h

/-- In the full period space, even first-variable parity means binary alternation. -/
theorem PeriodRelations.eval_swap_of_even {σ : Type*} {q : Binary R}
    (hq : PeriodRelations q) (he : bind₁ ![-X 0, X 1] q = q)
    (a b : MvPolynomial σ R) : binaryEval q b a = -binaryEval q a b := by
  have h := hq.identities.eval_two_term a b
  rw [binaryEval_even_first he] at h
  linear_combination h

/-- Odd normalized periods lift into the symmetric ternary sector. -/
theorem cyclicLift_symmetric {q : Binary R} (hq : PeriodRelations q)
    (ho : bind₁ ![-X 0, X 1] q = -q) :
    bind₁ ![X 1, X 0, X 2] (cyclicLift q) = cyclicLift q := by
  rw [bind_cyclicLift, cyclicLift,
    hq.eval_swap_of_odd ho (X 0) (X 1),
    hq.eval_swap_of_odd ho (X 2) (X 0),
    hq.eval_swap_of_odd ho (X 1) (X 2)]
  abel

/-- Even normalized periods lift into the alternating ternary sector. -/
theorem cyclicLift_alternating {q : Binary R} (hq : PeriodRelations q)
    (he : bind₁ ![-X 0, X 1] q = q) :
    bind₁ ![X 1, X 0, X 2] (cyclicLift q) = -cyclicLift q := by
  rw [bind_cyclicLift, cyclicLift,
    hq.eval_swap_of_even he (X 0) (X 1),
    hq.eval_swap_of_even he (X 2) (X 0),
    hq.eval_swap_of_even he (X 1) (X 2)]
  abel

/-- Both binary parity conventions agree with the original odd-period model. -/
theorem odd_relations_iff {F : Type*} [Field F] [CharZero F] (q : Binary F) :
    (PeriodRelations q ∧ bind₁ ![-X 0, X 1] q = -q) ↔
      BinaryComplexPeriod.Relations F q := by
  constructor
  · rintro ⟨hq, ho⟩
    have hs : bind₁ ![X 1, X 0] q = q := by
      have h := hq.eval_swap_of_odd ho (X 0 : Binary F) (X 1)
      rw [binaryEval_X] at h
      exact h
    have hy : bind₁ ![X 0, -X 1] q = -q := by
      have h := hq.identities.eval_neg_neg (X 0 : Binary F) (-X 1)
      simp only [neg_neg] at h
      rw [binaryEval_odd_first ho, binaryEval_X] at h
      exact h.symm
    refine ⟨hs, ho, hy, ?_⟩
    have hn := hq.identities.eval_three_term (X 0 : Binary F) (X 1)
    rw [binaryEval_X, binaryEval_odd_first ho,
      hq.eval_swap_of_odd ho (X 0-X 1) (X 1)] at hn
    have hl : binaryEval q (X 1-X 0 : Binary F) (-X 0) = binaryEval q (X 0) (X 0-X 1) := by
      rw [show (X 1-X 0 : Binary F) = -(X 0-X 1) by ring,
        hq.identities.eval_neg_neg, hq.eval_swap_of_odd ho]
    rw [hl] at hn
    simpa [sub_eq_add_neg, binaryEval] using hn
  · rintro ⟨hs, hx, hy, hn⟩
    have hswap (a b : Binary F) :
        binaryEval q b a = binaryEval q a b := by
      have h := congrArg (fun p => binaryEval p a b) hs
      simpa [binaryEval, bind₁_bind₁, bind_vec2] using h
    have hodd_y (a b : Binary F) :
        binaryEval q a (-b) = -binaryEval q a b := by
      have h := congrArg (fun p => binaryEval p a b) hy
      simpa [binaryEval, bind₁_bind₁, bind_vec2] using h
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hx⟩
    · have h := binaryEval_odd_first hx (0 : Binary F) (X 1)
      simp only [neg_zero] at h
      exact CharZero.eq_neg_self_iff.mp h
    · have h := hodd_y (X 0 : Binary F) 0
      simp only [neg_zero] at h
      exact CharZero.eq_neg_self_iff.mp h
    · change q + binaryEval q (-X 1) (X 0) = 0
      rw [binaryEval_odd_first hx, hswap, binaryEval_X, add_neg_cancel]
    · change q + binaryEval q (-X 1) (X 0-X 1) +
        binaryEval q (X 1-X 0) (-X 0) = 0
      rw [binaryEval_odd_first hx, hswap (X 0-X 1) (X 1),
        show (X 1-X 0 : Binary F) = -(X 0-X 1) by ring,
        binaryEval_odd_first hx, hodd_y, neg_neg, hswap (X 0) (X 0-X 1)]
      simpa [binaryEval, sub_eq_add_neg] using hn

/-- Equality of the paper odd sector and the supplied odd period subspace. -/
theorem oddPeriodSpace_eq (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    oddPeriodSpace F n = BinaryComplexPeriod.space F n := by
  ext q
  change ((q.IsHomogeneous n ∧ PeriodRelations q) ∧
    bind₁ ![-X 0, X 1] q + q = 0) ↔
      q.IsHomogeneous n ∧ BinaryComplexPeriod.Relations F q
  rw [add_eq_zero_iff_eq_neg]
  constructor
  · rintro ⟨⟨hh, hq⟩, ho⟩
    exact ⟨hh, (odd_relations_iff q).mp ⟨hq, ho⟩⟩
  · rintro ⟨hh, hq⟩
    obtain ⟨hp, ho⟩ := (odd_relations_iff q).mpr hq
    exact ⟨⟨hh, hp⟩, ho⟩

/-- Identity on polynomials identifies the two exact odd period models. -/
def oddPeriodSpaceEquiv (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    oddPeriodSpace F n ≃ₗ[F] BinaryComplexPeriod.space F n :=
  LinearEquiv.ofEq _ _ (oddPeriodSpace_eq F n)

@[simp] theorem oddPeriodSpaceEquiv_apply (F : Type*) [Field F] [CharZero F]
    (n : ℕ) (q : oddPeriodSpace F n) :
    (oddPeriodSpaceEquiv F n q).val = q.val := rfl

end TernaryPoly.Paper
