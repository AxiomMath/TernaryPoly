module

public import TernaryPeriodPolynomials.Polynomial.Restriction
public import TernaryPeriodPolynomials.Polynomial.Support
public import TernaryPeriodPolynomials.Polynomial.FullPeriodDefect

@[expose] public section


/-! # Recovering a solution from one coordinate plane

Pairwise support and the original ternary equations give the literal cyclic-sum
reconstruction; the norm then removes the binary reflection defect.
-/


open MvPolynomial

noncomputable section
namespace TernaryPoly.Paper

variable {R : Type*} [CommRing R]

/-- Evaluate a ternary polynomial in arbitrary polynomial arguments. -/
def ternaryEval {σ : Type*} (f : Ternary R) (a b c : MvPolynomial σ R) :
    MvPolynomial σ R := bind₁ ![a,b,c] f

@[simp] theorem ternaryEval_add {σ : Type*} (f g : Ternary R)
    (a b c : MvPolynomial σ R) :
    ternaryEval (f+g) a b c = ternaryEval f a b c + ternaryEval g a b c := map_add _ _ _

theorem bind_vec3 {σ : Type*} (u v w : Ternary R) (a b c : MvPolynomial σ R) :
    (fun i => bind₁ ![a,b,c] (![u,v,w] i)) =
      ![bind₁ ![a,b,c] u, bind₁ ![a,b,c] v, bind₁ ![a,b,c] w] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem ternaryEval_X (f : Ternary R) :
    ternaryEval f (X 0) (X 1) (X 2) = f := by
  have hv : (![X 0,X 1,X 2] : Fin 3 → Ternary R) = X := by
    funext i
    fin_cases i <;> rfl
  rw [ternaryEval, hv, bind₁_X_left, AlgHom.id_apply]

/-- The original cyclic equation holds after every polynomial substitution. -/
theorem Solution.eval_cyclic {σ : Type*} {f : Ternary R} (hf : Solution f)
    (a b c : MvPolynomial σ R) : ternaryEval f b c a = ternaryEval f a b c := by
  have h := congrArg (fun p => ternaryEval p a b c) hf.cyclic
  simpa [ternaryEval, bind₁_bind₁, bind_vec3] using h

/-- The original norm equation holds after every polynomial substitution. -/
theorem Solution.eval_norm {σ : Type*} {f : Ternary R} (hf : Solution f)
    (a b c : MvPolynomial σ R) :
    ternaryEval f a b c + ternaryEval f (-b) (a-b) c +
      ternaryEval f (b-a) (-a) c = 0 := by
  have h := congrArg (fun p => ternaryEval p a b c) hf.norm
  simpa [ternaryEval, bind₁_bind₁, bind_vec3] using h

/-- The norm on an axis is three times the axis restriction. -/
theorem Solution.axis_zero [Algebra ℚ R] {σ : Type*} {f : Ternary R}
    (hf : Solution f) (c : MvPolynomial σ R) : ternaryEval f 0 0 c = 0 := by
  have h := hf.eval_norm 0 0 c
  simp only [neg_zero, sub_zero] at h
  have hs : (3 : ℚ) • ternaryEval f 0 0 c = 0 := by
    simpa only [show (3 : ℚ) = (3 : ℕ) by norm_num, Nat.cast_smul_eq_nsmul,
      succ_nsmul, zero_nsmul, zero_add] using h
  exact (smul_eq_zero.mp hs).resolve_left (by norm_num)

/-- Binary restriction and evaluation compose literally. -/
theorem binaryEval_restriction {σ : Type*} (f : Ternary R)
    (a b : MvPolynomial σ R) : binaryEval (restriction f) a b = ternaryEval f a b 0 := by
  simp only [restriction, binaryEval, ternaryEval, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp

private theorem ternaryEval_rename {σ : Type*} (p : Binary R) (i j : Fin 3)
    (a b c : MvPolynomial σ R) :
    ternaryEval (rename ![i,j] p) a b c = binaryEval p (![a,b,c] i) (![a,b,c] j) := by
  simp only [ternaryEval, binaryEval, bind₁_rename]
  congr 2
  funext k
  fin_cases k <;> rfl

/-- Pairwise support gives the exact inclusion-exclusion identity on coordinate planes. -/
theorem Pairwise.inclusion_exclusion {σ : Type*} {f : Ternary R} (hf : Pairwise f)
    (a b c : MvPolynomial σ R) :
    ternaryEval f a b c = ternaryEval f a b 0 + ternaryEval f 0 b c +
      ternaryEval f a 0 c - ternaryEval f a 0 0 - ternaryEval f 0 b 0 -
      ternaryEval f 0 0 c + ternaryEval f 0 0 0 := by
  obtain ⟨p,q,r,rfl⟩ := hf.exists_rename
  simp only [ternaryEval_add, ternaryEval_rename]
  dsimp
  abel

/-- Every solution is the cyclic sum of its literal binary restriction. -/
theorem cyclicLift_restriction [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    cyclicLift (restriction f) = f := by
  have h := (solution_pairwise f hf).inclusion_exclusion (X 0 : Ternary R) (X 1) (X 2)
  have h₀ : ternaryEval f (X 0 : Ternary R) 0 0 = 0 :=
    (hf.eval_cyclic (X 0) 0 0).symm.trans (hf.axis_zero (X 0))
  have h₁ : ternaryEval f (0 : Ternary R) (X 1) 0 = 0 :=
    (hf.eval_cyclic 0 0 (X 1)).trans (hf.axis_zero (X 1))
  rw [ternaryEval_X, h₀, h₁, hf.axis_zero, hf.axis_zero, sub_zero, sub_zero,
    sub_zero, add_zero] at h
  rw [cyclicLift, binaryEval_restriction, binaryEval_restriction, binaryEval_restriction]
  rw [hf.eval_cyclic 0 (X 1) (X 2), ← hf.eval_cyclic (X 2) (X 0) 0]
  exact h.symm

/-- The coordinate-plane restriction has zero horizontal axis. -/
theorem restriction_axis_second [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    bind₁ (![X 0, 0] : Fin 2 → Binary R) (restriction f) = 0 := by
  change binaryEval (restriction f) (X 0) 0 = 0
  rw [binaryEval_restriction, ← hf.eval_cyclic (X 0) 0 0, hf.axis_zero]

/-- The coordinate-plane restriction has zero vertical axis. -/
theorem restriction_axis_first [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    bind₁ (![0, X 1] : Fin 2 → Binary R) (restriction f) = 0 := by
  change binaryEval (restriction f) 0 (X 1) = 0
  rw [binaryEval_restriction, hf.eval_cyclic 0 0 (X 1), hf.axis_zero]

/-- Restriction preserves the full binary order-three relation. -/
theorem restriction_three_term {f : Ternary R} (hf : Solution f) :
    restriction f + bind₁ ![-X 1,X 0-X 1] (restriction f) +
      bind₁ ![X 1-X 0,-X 0] (restriction f) = 0 := by
  have h := hf.eval_norm (X 0 : Binary R) (X 1) 0
  simp only [← binaryEval_restriction] at h
  rw [binaryEval_X] at h
  exact h

/-- The ternary norm makes the binary reflection defect additive, hence doubling. -/
theorem restriction_defect_doubling [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    bind₁ ![2*X 0, X 1] (reflectionDefect (restriction f)) =
      2 * reflectionDefect (restriction f) := by
  let q := restriction f
  have hF : Solution (cyclicLift q) := by
    simpa only [q, cyclicLift_restriction hf] using hf
  have hN (a b : Binary R) :
      binaryEval q a b + binaryEval q (-b) (a-b) + binaryEval q (b-a) (-a) = 0 := by
    have h := congrArg (fun p : Binary R => binaryEval p a b) (restriction_three_term hf)
    simpa [q, binaryEval, bind₁_bind₁, bind_vec2] using h
  have hres (a b c : Binary R) :
      binaryEval (reflectionDefect q) b c + binaryEval (reflectionDefect q) (a-b) c +
        binaryEval (reflectionDefect q) (-a) c = 0 := by
    have h := hF.eval_norm a b c
    simp only [ternaryEval, bind_cyclicLift] at h
    have hn := hN a b
    simp only [reflectionDefect, binaryEval_add]
    simp only [binaryEval, bind₁_bind₁, bind_vec2, map_neg, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one, neg_neg]
    simp only [binaryEval] at h hn
    have he : -(a-b)=b-a := by ring
    rw [he]
    linear_combination h - hn
  have hzero (c : Binary R) : binaryEval (reflectionDefect q) 0 c = 0 := by
    have h₀ := congrArg (fun p : Binary R => binaryEval p 0 c) (restriction_axis_first hf)
    have h₁ := congrArg (fun p : Binary R => binaryEval p c 0) (restriction_axis_second hf)
    simp [binaryEval, bind₁_bind₁, bind_vec2] at h₀ h₁
    simp [reflectionDefect, q, binaryEval, bind₁_bind₁, bind_vec2, h₀, h₁]
  have h₁ := hres (2*X 0) (X 0) (X 1)
  have h₂ := hres (2*X 0) (2*X 0) (X 1)
  have he : (2*X 0-X 0 : Binary R) = X 0 := by ring
  rw [he] at h₁
  rw [sub_self, hzero, add_zero] at h₂
  change binaryEval (reflectionDefect q) (2*X 0) (X 1) = 2 * reflectionDefect q
  have hh : binaryEval (reflectionDefect q) (2*X 0 : Binary R) (X 1) =
      2 * binaryEval (reflectionDefect q) (X 0) (X 1) := by
    linear_combination h₂ - h₁
  simpa only [binaryEval_X] using hh

/-- Every ternary solution restricts to the full normalized period relations. -/
theorem restriction_periodRelations [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    PeriodRelations (restriction f) := by
  refine ⟨restriction_axis_first hf, restriction_axis_second hf, ?_, restriction_three_term hf⟩
  exact two_term_of_defect_doubling (restriction f) (restriction_axis_first hf)
    (restriction_axis_second hf) (restriction_three_term hf) (restriction_defect_doubling hf)

/-- Restriction as a linear map into the full normalized homogeneous period space. -/
def restrictionLinear (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    solutionSpace R n →ₗ[R] periodSpace R n where
  toFun f := ⟨restriction f, restriction_homogeneous f.property.1,
    restriction_periodRelations f.property.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The full restriction equivalence, with the paper's literal cyclic-sum inverse. -/
def restrictionEquiv (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    solutionSpace R n ≃ₗ[R] periodSpace R n where
  toLinearMap := restrictionLinear R n
  invFun := cyclicLiftLinear R n
  left_inv f := Subtype.ext (cyclicLift_restriction f.property.2)
  right_inv q := Subtype.ext (restriction_cyclicLift q.property.2)

@[simp] theorem restrictionEquiv_apply (R : Type*) [CommRing R] [Algebra ℚ R]
    (n : ℕ) (f : solutionSpace R n) :
    (restrictionEquiv R n f).val = restriction f.val := rfl

@[simp] theorem restrictionEquiv_symm_apply (R : Type*) [CommRing R] [Algebra ℚ R]
    (n : ℕ) (q : periodSpace R n) :
    ((restrictionEquiv R n).symm q).val = cyclicLift q.val := rfl

/-- A solution is uniquely determined by its restriction to one coordinate plane. -/
theorem restriction_injective_on_solutions [Algebra ℚ R] {f g : Ternary R}
    (hf : Solution f) (hg : Solution g) (h : restriction f = restriction g) : f = g := by
  rw [← cyclicLift_restriction hf, ← cyclicLift_restriction hg, h]

/-- The cyclic-sum representation by a normalized binary period is unique. -/
theorem unique_normalized_restriction [Algebra ℚ R] {f : Ternary R} (hf : Solution f) :
    ∃! q : Binary R, PeriodRelations q ∧ f = cyclicLift q := by
  refine ⟨restriction f, ⟨restriction_periodRelations hf, (cyclicLift_restriction hf).symm⟩, ?_⟩
  intro q hq
  rw [hq.2, restriction_cyclicLift hq.1]

end TernaryPoly.Paper
