module

public import TernaryPeriodPolynomials.Polynomial.Classification.Restriction
public import TernaryPeriodPolynomials.Polynomial.Classification
public import TernaryPeriodPolynomials.Polynomial.ClassificationEquivalence

@[expose] public section



/-!
# Restriction equivalences

Restriction `f ↦ f(X, Y, 0)` is an `R`-linear equivalence from the degree-`n` solutions onto the
normalized binary period polynomials, with inverse the cyclic sum `Φ`, and it identifies the
symmetric and alternating sectors with the odd and even period polynomials. These are proved from
the restriction results of `Argument.Classification`, which rest on Theorem 1.1.
-/

open MvPolynomial TernaryPoly.Paper
open TernaryPeriodPolynomials.Argument.Classification

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RouteIndependent

variable {R : Type*} [CommRing R]

/-- The alternating ternary sector restricts exactly to even binary periods. -/
theorem restriction_alternating_iff [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    bind₁ ![X 1,X 0,X 2] f = -f ↔
      bind₁ ![-X 0,X 1] (restriction f) = restriction f := by
  constructor
  · intro hs
    have hswap : bind₁ ![X 1,X 0] (restriction f) = -restriction f := by
      rw [← restriction_swap, hs]
      exact map_neg _ _
    have hn := (TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hf).identities.eval_two_term
      (X 1 : Binary R) (X 0)
    change bind₁ ![X 1,X 0] (restriction f) +
      bind₁ ![-X 0,X 1] (restriction f) = 0 at hn
    rw [hswap] at hn
    linear_combination hn
  · intro he
    rw [← TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hf]
    exact cyclicLift_alternating (TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hf) he

/-- Restriction as a linear map into the full normalized homogeneous period space. -/
def restrictionLinear (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    solutionSpace R n →ₗ[R] periodSpace R n where
  toFun f := ⟨restriction f, restriction_homogeneous f.property.1,
    TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations f.property.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The full restriction equivalence, with the literal cyclic-sum inverse. -/
def restrictionEquiv (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    solutionSpace R n ≃ₗ[R] periodSpace R n where
  toLinearMap := restrictionLinear R n
  invFun := cyclicLiftLinear R n
  left_inv f := Subtype.ext (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction f.property.2)
  right_inv q := Subtype.ext (restriction_cyclicLift q.property.2)

@[simp] theorem restrictionEquiv_new_apply (R : Type*) [CommRing R] [Algebra ℚ R]
    (n : ℕ) (f : solutionSpace R n) :
    (restrictionEquiv R n f).val = restriction f.val := rfl

@[simp] theorem restrictionEquiv_new_symm_apply (R : Type*) [CommRing R] [Algebra ℚ R]
    (n : ℕ) (q : periodSpace R n) :
    ((restrictionEquiv R n).symm q).val = cyclicLift q.val := rfl

/-- The explicit symmetric-to-odd restriction equivalence. -/
def symmetricRestrictionEquiv (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    symmetricSolutionSpace R n ≃ₗ[R] oddPeriodSpace R n where
  toFun f := ⟨restriction f.val, by
    refine ⟨⟨restriction_homogeneous f.property.1.1,
      TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations f.property.1.2⟩, ?_⟩
    change bind₁ ![-X 0,X 1] (restriction f.val) + restriction f.val = 0
    rw [(TernaryPeriodPolynomials.Argument.Classification.restriction_symmetric_iff f.property.1.2).mp (sub_eq_zero.mp f.property.2)]
    exact neg_add_cancel _⟩
  invFun q := ⟨cyclicLift q.val, by
    refine ⟨⟨cyclicLift_homogeneous q.property.1.1,
      cyclicLift_solution q.property.1.2⟩, ?_⟩
    change bind₁ ![X 1,X 0,X 2] (cyclicLift q.val) - cyclicLift q.val = 0
    rw [cyclicLift_symmetric q.property.1.2 (eq_neg_of_add_eq_zero_left q.property.2), sub_self]⟩
  left_inv f := Subtype.ext (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction f.property.1.2)
  right_inv q := Subtype.ext (restriction_cyclicLift q.property.1.2)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The explicit alternating-to-even restriction equivalence. -/
def alternatingRestrictionEquiv (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    alternatingSolutionSpace R n ≃ₗ[R] evenPeriodSpace R n where
  toFun f := ⟨restriction f.val, by
    refine ⟨⟨restriction_homogeneous f.property.1.1,
      TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations f.property.1.2⟩, ?_⟩
    change bind₁ ![-X 0,X 1] (restriction f.val) - restriction f.val = 0
    rw [(restriction_alternating_iff f.property.1.2).mp
      (eq_neg_of_add_eq_zero_left f.property.2), sub_self]⟩
  invFun q := ⟨cyclicLift q.val, by
    refine ⟨⟨cyclicLift_homogeneous q.property.1.1,
      cyclicLift_solution q.property.1.2⟩, ?_⟩
    change bind₁ ![X 1,X 0,X 2] (cyclicLift q.val) + cyclicLift q.val = 0
    rw [cyclicLift_alternating q.property.1.2 (sub_eq_zero.mp q.property.2), neg_add_cancel]⟩
  left_inv f := Subtype.ext (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction f.property.1.2)
  right_inv q := Subtype.ext (restriction_cyclicLift q.property.1.2)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem symmetricRestrictionEquiv_new_apply [Algebra ℚ R] (n : ℕ)
    (f : symmetricSolutionSpace R n) :
    (symmetricRestrictionEquiv R n f).val = restriction f.val := rfl

@[simp] theorem symmetricRestrictionEquiv_new_symm_apply [Algebra ℚ R] (n : ℕ)
    (q : oddPeriodSpace R n) :
    ((symmetricRestrictionEquiv R n).symm q).val = cyclicLift q.val := rfl

@[simp] theorem alternatingRestrictionEquiv_new_apply [Algebra ℚ R] (n : ℕ)
    (f : alternatingSolutionSpace R n) :
    (alternatingRestrictionEquiv R n f).val = restriction f.val := rfl

@[simp] theorem alternatingRestrictionEquiv_new_symm_apply [Algebra ℚ R] (n : ℕ)
    (q : evenPeriodSpace R n) :
    ((alternatingRestrictionEquiv R n).symm q).val = cyclicLift q.val := rfl

/-- A solution is uniquely determined by its restriction to one coordinate plane. -/
theorem restriction_injective_on_solutions [Algebra ℚ R] {f g : Ternary R}
    (hf : Solution f) (hg : Solution g) (h : restriction f = restriction g) : f = g := by
  rw [← TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hf, ← TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hg, h]

/-- The cyclic-sum representation by a normalized binary period is unique. -/
theorem unique_normalized_restriction [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    ∃! q : Binary R, PeriodRelations q ∧ f = cyclicLift q := by
  refine ⟨restriction f, ⟨TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hf,
    (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hf).symm⟩, ?_⟩
  intro q hq
  rw [hq.2, restriction_cyclicLift hq.1]

/-- The zero-degree ternary solution space is zero. -/
theorem solution_degree_zero_eq_zero [Algebra ℚ R] {f : Ternary R}
    (hh : f.IsHomogeneous 0) (hf : Solution f) : f = 0 := by
  have hq := period_zero_eq_zero (restriction_homogeneous hh) (TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hf)
  rw [← TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hf, hq]
  simp [cyclicLift]

/-- The paper's symmetric classification, including the unique literal restriction. -/
theorem symmetric_classification {F : Type*} [Field F] [CharZero F]
    {f : Ternary F} {n : ℕ} (hh : f.IsHomogeneous n) (hs : f.IsSymmetric) :
    (f + bind₁ ![-X 1,X 0-X 1,X 2] f + bind₁ ![X 1-X 0,-X 0,X 2] f = 0) ↔
      ∃! q : Binary F, q.IsHomogeneous n ∧ TernaryPoly.BinaryComplexPeriod.Relations F q ∧
        f = cyclicLift q := by
  constructor
  · intro hn
    have hf : Solution f := ⟨IsSymmetric.cyclic hs, hn⟩
    refine ⟨restriction f, ⟨restriction_homogeneous hh,
      (odd_relations_iff _).mp ⟨TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hf,
        (TernaryPeriodPolynomials.Argument.Classification.restriction_symmetric_iff hf).mp (IsSymmetric.swap hs)⟩,
      (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hf).symm⟩, ?_⟩
    intro q hq
    have hrel := ((odd_relations_iff q).mpr hq.2.1).1
    rw [hq.2.2, restriction_cyclicLift hrel]
  · rintro ⟨q, ⟨_, hq, rfl⟩, _⟩
    exact cyclicLift_norm ((odd_relations_iff q).mpr hq).1

end TernaryPeriodPolynomials.Argument.RouteIndependent
