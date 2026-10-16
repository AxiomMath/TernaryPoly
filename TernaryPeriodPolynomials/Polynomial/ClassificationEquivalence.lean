module

public import TernaryPeriodPolynomials.Polynomial.Classification
public import TernaryPeriodPolynomials.Polynomial.RestrictionRecovery
public import TernaryPeriodPolynomials.Polynomial.PeriodNormalization
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

@[expose] public section


/-! # Complete restriction equivalences in both symmetry sectors

The sector maps are the literal coordinate-plane restriction and cyclic sum.
The symmetric classification below assumes symmetry under every permutation.
-/


open MvPolynomial
noncomputable section
namespace TernaryPoly.Paper

variable {R : Type*} [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
/-- Restriction intertwines the transposition of the first two coordinates. -/
theorem restriction_swap (f : Ternary R) :
    restriction (bind₁ ![X 1,X 0,X 2] f) = bind₁ ![X 1,X 0] (restriction f) := by
  simp only [restriction, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The symmetric ternary sector restricts exactly to odd binary periods. -/
theorem restriction_symmetric_iff {f : Ternary R} (hf : Solution f) :
    bind₁ ![X 1,X 0,X 2] f = f ↔
      bind₁ ![-X 0,X 1] (restriction f) = -restriction f := by
  constructor
  · intro hs
    have hswap : bind₁ ![X 1,X 0] (restriction f) = restriction f := by
      rw [← restriction_swap, hs]
    have hn := (restriction_periodRelations hf).identities.eval_two_term
      (X 1 : Binary R) (X 0)
    change bind₁ ![X 1,X 0] (restriction f) +
      bind₁ ![-X 0,X 1] (restriction f) = 0 at hn
    rw [hswap] at hn
    exact eq_neg_of_add_eq_zero_right hn
  · intro ho
    rw [← cyclicLift_restriction hf]
    exact cyclicLift_symmetric (restriction_periodRelations hf) ho

/-- The alternating ternary sector restricts exactly to even binary periods. -/
theorem restriction_alternating_iff {f : Ternary R} (hf : Solution f) :
    bind₁ ![X 1,X 0,X 2] f = -f ↔
      bind₁ ![-X 0,X 1] (restriction f) = restriction f := by
  constructor
  · intro hs
    have hswap : bind₁ ![X 1,X 0] (restriction f) = -restriction f := by
      rw [← restriction_swap, hs]
      exact map_neg _ _
    have hn := (restriction_periodRelations hf).identities.eval_two_term
      (X 1 : Binary R) (X 0)
    change bind₁ ![X 1,X 0] (restriction f) +
      bind₁ ![-X 0,X 1] (restriction f) = 0 at hn
    rw [hswap] at hn
    linear_combination hn
  · intro he
    rw [← cyclicLift_restriction hf]
    exact cyclicLift_alternating (restriction_periodRelations hf) he

/-- The explicit symmetric-to-odd restriction equivalence. -/
def symmetricRestrictionEquiv (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    symmetricSolutionSpace R n ≃ₗ[R] oddPeriodSpace R n where
  toFun f := ⟨restriction f.val, by
    refine ⟨⟨restriction_homogeneous f.property.1.1,
      restriction_periodRelations f.property.1.2⟩, ?_⟩
    change bind₁ ![-X 0,X 1] (restriction f.val) + restriction f.val = 0
    rw [(restriction_symmetric_iff f.property.1.2).mp (sub_eq_zero.mp f.property.2)]
    exact neg_add_cancel _⟩
  invFun q := ⟨cyclicLift q.val, by
    refine ⟨⟨cyclicLift_homogeneous q.property.1.1,
      cyclicLift_solution q.property.1.2⟩, ?_⟩
    change bind₁ ![X 1,X 0,X 2] (cyclicLift q.val) - cyclicLift q.val = 0
    rw [cyclicLift_symmetric q.property.1.2 (eq_neg_of_add_eq_zero_left q.property.2), sub_self]⟩
  left_inv f := Subtype.ext (cyclicLift_restriction f.property.1.2)
  right_inv q := Subtype.ext (restriction_cyclicLift q.property.1.2)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The explicit alternating-to-even restriction equivalence. -/
def alternatingRestrictionEquiv (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    alternatingSolutionSpace R n ≃ₗ[R] evenPeriodSpace R n where
  toFun f := ⟨restriction f.val, by
    refine ⟨⟨restriction_homogeneous f.property.1.1,
      restriction_periodRelations f.property.1.2⟩, ?_⟩
    change bind₁ ![-X 0,X 1] (restriction f.val) - restriction f.val = 0
    rw [(restriction_alternating_iff f.property.1.2).mp
      (eq_neg_of_add_eq_zero_left f.property.2), sub_self]⟩
  invFun q := ⟨cyclicLift q.val, by
    refine ⟨⟨cyclicLift_homogeneous q.property.1.1,
      cyclicLift_solution q.property.1.2⟩, ?_⟩
    change bind₁ ![X 1,X 0,X 2] (cyclicLift q.val) + cyclicLift q.val = 0
    rw [cyclicLift_alternating q.property.1.2 (sub_eq_zero.mp q.property.2), neg_add_cancel]⟩
  left_inv f := Subtype.ext (cyclicLift_restriction f.property.1.2)
  right_inv q := Subtype.ext (restriction_cyclicLift q.property.1.2)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem symmetricRestrictionEquiv_apply (n : ℕ) (f : symmetricSolutionSpace R n) :
    (symmetricRestrictionEquiv R n f).val = restriction f.val := rfl

@[simp] theorem symmetricRestrictionEquiv_symm_apply (n : ℕ) (q : oddPeriodSpace R n) :
    ((symmetricRestrictionEquiv R n).symm q).val = cyclicLift q.val := rfl

@[simp] theorem alternatingRestrictionEquiv_apply (n : ℕ) (f : alternatingSolutionSpace R n) :
    (alternatingRestrictionEquiv R n f).val = restriction f.val := rfl

@[simp] theorem alternatingRestrictionEquiv_symm_apply (n : ℕ) (q : evenPeriodSpace R n) :
    ((alternatingRestrictionEquiv R n).symm q).val = cyclicLift q.val := rfl

omit [Algebra ℚ R] in
/-- The full permutation-symmetry hypothesis implies the defining cyclic equation. -/
theorem IsSymmetric.cyclic {f : Ternary R} (hf : f.IsSymmetric) :
    bind₁ ![X 1,X 2,X 0] f = f := by
  let e : Equiv.Perm (Fin 3) :=
    ⟨![1,2,0], ![2,0,1], by intro i; fin_cases i <;> rfl,
      by intro i; fin_cases i <;> rfl⟩
  have he : rename e = (bind₁ ![X 1,X 2,X 0] : Ternary R →ₐ[R] Ternary R) := by
    ext i
    fin_cases i <;> simp [e]
  rw [← he]
  exact hf e

omit [Algebra ℚ R] in
/-- Full permutation symmetry implies the displayed transposition equation. -/
theorem IsSymmetric.swap {f : Ternary R} (hf : f.IsSymmetric) :
    bind₁ ![X 1,X 0,X 2] f = f := by
  have he : rename (Equiv.swap (0 : Fin 3) 1) =
      (bind₁ ![X 1,X 0,X 2] : Ternary R →ₐ[R] Ternary R) := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [← he]
  exact hf _

/-- The paper's symmetric classification, including the unique literal restriction. -/
theorem symmetric_classification {F : Type*} [Field F] [CharZero F]
    {f : Ternary F} {n : ℕ} (hh : f.IsHomogeneous n) (hs : f.IsSymmetric) :
    (f + bind₁ ![-X 1,X 0-X 1,X 2] f + bind₁ ![X 1-X 0,-X 0,X 2] f = 0) ↔
      ∃! q : Binary F, q.IsHomogeneous n ∧ BinaryComplexPeriod.Relations F q ∧
        f = cyclicLift q := by
  constructor
  · intro hn
    have hf : Solution f := ⟨IsSymmetric.cyclic hs, hn⟩
    refine ⟨restriction f, ⟨restriction_homogeneous hh,
      (odd_relations_iff _).mp ⟨restriction_periodRelations hf,
        (restriction_symmetric_iff hf).mp (IsSymmetric.swap hs)⟩,
      (cyclicLift_restriction hf).symm⟩, ?_⟩
    intro q hq
    have hrel := ((odd_relations_iff q).mpr hq.2.1).1
    rw [hq.2.2, restriction_cyclicLift hrel]
  · rintro ⟨q, ⟨_, hq, rfl⟩, _⟩
    exact cyclicLift_norm ((odd_relations_iff q).mpr hq).1

/-- The supplied symmetric binary convention is exactly the paper's three-term convention. -/
theorem symmetric_binary_relations_literal {F : Type*} [Field F] [CharZero F] (q : Binary F) :
    BinaryComplexPeriod.Relations F q ↔
      bind₁ ![X 1,X 0] q = q ∧ bind₁ ![-X 0,X 1] q = -q ∧
      bind₁ ![X 0,-X 1] q = -q ∧
      q + bind₁ ![-X 1,X 0-X 1] q + bind₁ ![X 1-X 0,-X 0] q = 0 := by
  constructor
  · intro hq
    exact ⟨hq.1, hq.2.1, hq.2.2.1, ((odd_relations_iff q).mpr hq).1.three_term⟩
  · rintro ⟨hs,hx,hy,hn⟩
    apply (odd_relations_iff q).mp
    refine ⟨⟨?_, ?_, ?_, hn⟩, hx⟩
    · have h := binaryEval_odd_first hx (0 : Binary F) (X 1)
      simp only [neg_zero] at h
      exact CharZero.eq_neg_self_iff.mp h
    · have h := congrArg (fun p : Binary F => binaryEval p (X 0 : Binary F) 0) hy
      simp [binaryEval, bind₁_bind₁, bind_vec2] at h
      exact CharZero.eq_neg_self_iff.mp h
    · have h := congrArg (fun p : Binary F => binaryEval p (X 1 : Binary F) (X 0)) hx
      simp [binaryEval, bind₁_bind₁, bind_vec2] at h
      change q + binaryEval q (-X 1) (X 0) = 0
      change binaryEval q (-X 1) (X 0) = -binaryEval q (X 1) (X 0) at h
      rw [h, show binaryEval q (X 1 : Binary F) (X 0) = q from hs, add_neg_cancel]

/-- Literal paper statement: the unique binary polynomial is symmetric, separately odd,
homogeneous of the same degree, and satisfies the displayed three-term relation. -/
theorem symmetric_classification_literal {F : Type*} [Field F] [CharZero F]
    {f : Ternary F} {n : ℕ} (hh : f.IsHomogeneous n) (hs : f.IsSymmetric) :
    (f + bind₁ ![-X 1,X 0-X 1,X 2] f + bind₁ ![X 1-X 0,-X 0,X 2] f = 0) ↔
      ∃! q : Binary F, q.IsHomogeneous n ∧
        (bind₁ ![X 1,X 0] q = q ∧ bind₁ ![-X 0,X 1] q = -q ∧
          bind₁ ![X 0,-X 1] q = -q ∧
          q + bind₁ ![-X 1,X 0-X 1] q + bind₁ ![X 1-X 0,-X 0] q = 0) ∧
        f = cyclicLift q := by
  simpa only [symmetric_binary_relations_literal] using symmetric_classification hh hs

/-- The unique polynomial in the classification is exactly coordinate restriction. -/
theorem symmetric_classification_restriction {F : Type*} [Field F] [CharZero F]
    {f : Ternary F} {q : Binary F} (hq : BinaryComplexPeriod.Relations F q)
    (h : f = cyclicLift q) : restriction f = q := by
  rw [h, restriction_cyclicLift ((odd_relations_iff q).mpr hq).1]

/-- The zero-degree ternary solution space is zero. -/
theorem solution_degree_zero_eq_zero {f : Ternary R} (hh : f.IsHomogeneous 0)
    (hf : Solution f) : f = 0 := by
  have hq := period_zero_eq_zero (restriction_homogeneous hh) (restriction_periodRelations hf)
  rw [← cyclicLift_restriction hf, hq]
  simp [cyclicLift]

/-- Every odd homogeneous ternary solution over a characteristic-zero field vanishes. -/
theorem solution_odd_eq_zero {F : Type*} [Field F] [CharZero F] {f : Ternary F} {n : ℕ}
    (hh : f.IsHomogeneous n) (hf : Solution f) (hn : Odd n) : f = 0 := by
  have hq := period_odd_eq_zero (restriction_homogeneous hh)
    (restriction_periodRelations hf).identities hn
  rw [← cyclicLift_restriction hf, hq]
  simp [cyclicLift]

end TernaryPoly.Paper
