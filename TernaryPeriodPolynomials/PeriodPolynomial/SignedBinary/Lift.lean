module

public import TernaryPeriodPolynomials.PeriodPolynomial.SignedBinary.SignedBinary
public import TernaryPeriodPolynomials.SymmetricSolution.BinaryPeriodQuotient
public import TernaryPeriodPolynomials.Analysis.CoordinateSumQuotient

@[expose] public section


/-!
# The polynomial lift `L(q) = Φ(q)/(x+y+z)` of the signed binary relations (MR-5)

Formalized by Claude Sonnet 5.5.

For `q ∈ 𝓑_d^ε` (`ε = ±1`, `d > 0`) the coordinate sum
`w = x+y+z` divides the cyclic sum `Φ(q) = q(x,y)+q(y,z)+q(z,x)` (`TernaryPoly.Paper.cyclicLift`), and `L(q) = Φ(q)/w` is homogeneous of degree
`d-1`, cyclically invariant and has symmetry `ε` (`L(q)(y,x,z) = ε L(q)(x,y,z)`).

* `ε = 1` reuses `TernaryPoly.symmetricBinaryPeriod_quotient_data` / `symmetricBinaryLift_quotient_isHomogeneous` (`SymmetricBinaryPeriodQuotient`);
* `ε = -1` reuses `TernaryPoly.coordinate_sum_dvd_binaryPeriodLift`, `binaryPeriodLift_alternating` (`BinaryPeriodLift`, `CoordinateSumQuotient`).

The ternary norm equation is not used.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPoly.Paper

open Classical in
/-- **The polynomial lift** `L(q) = Φ(q)/(x+y+z)` (and `L(q) = 0` when `w` does not divide `Φ(q)`). -/
def polynomialLift (q : Binary ℚ) : Ternary ℚ :=
  if h : (X 0 + X 1 + X 2 : Ternary ℚ) ∣ cyclicLift q then h.choose else 0

theorem mul_polynomialLift {q : Binary ℚ} (h : (X 0 + X 1 + X 2 : Ternary ℚ) ∣ cyclicLift q) :
    (X 0 + X 1 + X 2 : Ternary ℚ) * polynomialLift q = cyclicLift q := by
  rw [polynomialLift, dite_eq_left h]
  exact h.choose_spec.symm

theorem polynomialLift_eq_of {q : Binary ℚ} {g : Ternary ℚ}
    (h : cyclicLift q = (X 0 + X 1 + X 2 : Ternary ℚ) * g) : polynomialLift q = g :=
  mul_left_cancel₀ TernaryPoly.coordinate_sum_ne_zero ((mul_polynomialLift ⟨g, h⟩).trans h)

theorem polynomialLift_zero : polynomialLift 0 = 0 :=
  polynomialLift_eq_of (by simp [cyclicLift, binaryEval])

/-- The data of the lift for the symmetric sign. -/
theorem lift_data_one {d : ℕ} {q : Binary ℚ} (hq : q ∈ signedBinary 1 d) :
    ∃ g : Ternary ℚ, cyclicLift q = (X 0 + X 1 + X 2 : Ternary ℚ) * g ∧ g.IsHomogeneous (d - 1) ∧
      bind₁ ![X 1, X 2, X 0] g = g ∧ bind₁ ![X 1, X 0, X 2] g = (1 : ℚ) • g := by
  obtain ⟨hh, hrel⟩ := (mem_signedBinary).1 hq
  obtain ⟨hp, ho⟩ := (signedRelations_iff (by norm_num : (1 : ℚ) * 1 = 1)).1 hrel
  rw [neg_smul, one_smul] at ho
  obtain ⟨hs, hx, hy, hn⟩ := (odd_relations_iff q).1 ⟨hp, ho⟩
  have hsym : TernaryPoly.SymmetricBinaryPeriodRelations q := ⟨hs, hx, hy, hn⟩
  obtain ⟨g, hg, hc, hsw, -, -⟩ := TernaryPoly.symmetricBinaryPeriod_quotient_data hsym
  have hh' : q.IsHomogeneous d := (mem_homogeneousSubmodule _ _).1 hh
  exact ⟨g, hg, TernaryPoly.symmetricBinaryLift_quotient_isHomogeneous hh' g hg, hc, by rw [one_smul]; exact hsw⟩

/-- The relations of `TernaryPoly.BinaryPeriodRelations` from the alternating sign. -/
theorem binaryPeriodRelations_of_neg_one {d : ℕ} {q : Binary ℚ} (hq : q ∈ signedBinary (-1) d) :
    TernaryPoly.BinaryPeriodRelations q := by
  obtain ⟨-, hrel⟩ := (mem_signedBinary).1 hq
  obtain ⟨hp, he⟩ := (signedRelations_iff (by norm_num : (-1 : ℚ) * -1 = 1)).1 hrel
  rw [neg_neg, one_smul] at he
  obtain ⟨hs, -, hy, ha, hb, -⟩ := hrel
  rw [neg_one_smul] at hs
  rw [neg_neg, one_smul] at hy
  refine ⟨hs, he, hy, ha, hb, ?_⟩
  have hn := hp.identities.eval_three_term (X 0 : Binary ℚ) (X 1)
  rw [binaryEval_X, binaryEval_even_first he] at hn
  have hsw : ∀ a b : Binary ℚ, binaryEval q b a = -binaryEval q a b := fun a b =>
    hp.eval_swap_of_even he a b
  have hl : binaryEval q (X 1 - X 0 : Binary ℚ) (-X 0) = binaryEval q (X 0 - X 1) (X 0) := by
    rw [show (X 1 - X 0 : Binary ℚ) = -(X 0 - X 1) by ring, hp.identities.eval_neg_neg]
  rw [hl, hsw (X 0 - X 1 : Binary ℚ) (X 1), hsw (X 0 : Binary ℚ) (X 0 - X 1)] at hn
  simp only [binaryEval] at hn
  linear_combination hn

/-- The data of the lift for the alternating sign. -/
theorem lift_data_neg_one {d : ℕ} {q : Binary ℚ} (hq : q ∈ signedBinary (-1) d) :
    ∃ g : Ternary ℚ, cyclicLift q = (X 0 + X 1 + X 2 : Ternary ℚ) * g ∧ g.IsHomogeneous (d - 1) ∧
      bind₁ ![X 1, X 2, X 0] g = g ∧ bind₁ ![X 1, X 0, X 2] g = (-1 : ℚ) • g := by
  have hr := binaryPeriodRelations_of_neg_one hq
  obtain ⟨hh, -⟩ := (mem_signedBinary).1 hq
  have hh' : q.IsHomogeneous d := (mem_homogeneousSubmodule _ _).1 hh
  obtain ⟨g, hg⟩ := TernaryPoly.coordinate_sum_dvd_binaryPeriodLift hr
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · apply TernaryPoly.isHomogeneous_quotient TernaryPoly.coordinate_sum_isHomogeneous
      TernaryPoly.coordinate_sum_ne_zero
    rw [← hg]
    exact TernaryPoly.binaryPeriodLift_isHomogeneous hh'
  · apply TernaryPoly.cyclic_of_coordinate_sum_pow_mul 1
    simpa only [pow_one, ← hg] using TernaryPoly.binaryPeriodLift_cyclic q
  · rw [neg_one_smul]
    apply TernaryPoly.alternating_of_coordinate_sum_pow_mul 1
    simpa only [pow_one, ← hg] using TernaryPoly.binaryPeriodLift_alternating hr

/-- **MR-5**: for `q ∈ 𝓑_d^ε` with `d > 0` and `ε = ±1`, `w = x+y+z` divides `Φ(q)` and `L(q) = Φ(q)/w` is homogeneous of degree `d-1`,
cyclically invariant, and has symmetry `ε`. -/
theorem signedBinary_lift {ε : ℚ} (hε : ε = 1 ∨ ε = -1) {d : ℕ} (hd : 0 < d) {q : Binary ℚ}
    (hq : q ∈ signedBinary ε d) :
    (X 0 + X 1 + X 2 : Ternary ℚ) ∣ cyclicLift q ∧
      cyclicLift q = (X 0 + X 1 + X 2 : Ternary ℚ) * polynomialLift q ∧
      (polynomialLift q).IsHomogeneous (d - 1) ∧
      bind₁ ![X 1, X 2, X 0] (polynomialLift q) = polynomialLift q ∧
      bind₁ ![X 1, X 0, X 2] (polynomialLift q) = ε • polynomialLift q := by
  have _ := hd
  obtain ⟨g, hg, hh, hc, hs⟩ : ∃ g : Ternary ℚ, cyclicLift q = (X 0 + X 1 + X 2 : Ternary ℚ) * g ∧
      g.IsHomogeneous (d - 1) ∧ bind₁ ![X 1, X 2, X 0] g = g ∧ bind₁ ![X 1, X 0, X 2] g = ε • g := by
    rcases hε with rfl | rfl
    · exact lift_data_one hq
    · exact lift_data_neg_one hq
  have hL := polynomialLift_eq_of hg
  rw [hL]
  exact ⟨⟨g, hg⟩, hg, hh, hc, hs⟩

end TernaryPeriodPolynomials.Argument.Identities
