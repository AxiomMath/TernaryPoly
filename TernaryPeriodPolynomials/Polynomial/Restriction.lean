module

public import TernaryPeriodPolynomials.Polynomial.PeriodSubstitution
public import TernaryPeriodPolynomials.Polynomial.Homogeneous

@[expose] public section


/-! # The literal restriction and cyclic-sum maps

The inverse construction is valid for the full normalized binary period space,
without choosing a parity sector.
-/


open MvPolynomial

noncomputable section
namespace TernaryPoly.Paper

variable {R : Type*} [CommRing R]

/-- Restriction to the coordinate plane `z = 0`. -/
def restriction (f : Ternary R) : Binary R := bind₁ ![X 0, X 1, 0] f

/-- The explicit cyclic-sum inverse from the paper. -/
def cyclicLift (q : Binary R) : Ternary R :=
  binaryEval q (X 0) (X 1) + binaryEval q (X 1) (X 2) + binaryEval q (X 2) (X 0)

/-- Substitution in the cyclic lift is evaluation at its three pairs. -/
theorem bind_cyclicLift {σ : Type*} (q : Binary R) (a b c : MvPolynomial σ R) :
    bind₁ ![a, b, c] (cyclicLift q) =
      binaryEval q a b + binaryEval q b c + binaryEval q c a := by
  simp [cyclicLift, bind_binaryEval]

/-- Axis normalization makes restriction a left inverse to the cyclic sum. -/
theorem restriction_cyclicLift {q : Binary R} (hq : PeriodRelations q) :
    restriction (cyclicLift q) = q := by
  rw [restriction, bind_cyclicLift, hq.eval_zero_second, hq.eval_zero_first,
    add_zero, add_zero, binaryEval_X]

/-- Every cyclic sum is invariant under the cyclic permutation. -/
theorem cyclicLift_cyclic (q : Binary R) :
    bind₁ ![X 1, X 2, X 0] (cyclicLift q) = cyclicLift q := by
  rw [bind_cyclicLift, cyclicLift]
  abel

/-- The full two-term and three-term relations imply the ternary norm. -/
theorem cyclicLift_norm {q : Binary R} (hq : PeriodRelations q) :
    cyclicLift q + bind₁ ![-X 1, X 0-X 1, X 2] (cyclicLift q) +
      bind₁ ![X 1-X 0, -X 0, X 2] (cyclicLift q) = 0 := by
  rw [bind_cyclicLift, bind_cyclicLift, cyclicLift]
  have h₁ := hq.identities.eval_three_term (X 0 : Ternary R) (X 1)
  have h₂ := hq.identities.eval_two_term (X 2 : Ternary R) (X 0)
  have h₃ := hq.identities.eval_two_term (X 2 : Ternary R) (-X 1)
  have h₄ := hq.identities.eval_two_term (X 2 : Ternary R) (X 1-X 0)
  simp only [neg_neg, neg_sub] at h₃ h₄
  linear_combination h₁ + h₂ + h₃ + h₄


/-- The cyclic lift of every full normalized period is a ternary solution. -/
theorem cyclicLift_solution {q : Binary R} (hq : PeriodRelations q) :
    Solution (cyclicLift q) := ⟨cyclicLift_cyclic q, cyclicLift_norm hq⟩

/-- Restriction preserves homogeneous degree. -/
theorem restriction_homogeneous {f : Ternary R} {n : ℕ} (hf : f.IsHomogeneous n) :
    (restriction f).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hf
  intro i
  fin_cases i
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_zero _ _ _

/-- The cyclic sum preserves homogeneous degree. -/
theorem cyclicLift_homogeneous {q : Binary R} {n : ℕ} (hq : q.IsHomogeneous n) :
    (cyclicLift q).IsHomogeneous n := by
  have h (i j : Fin 3) : (binaryEval q (X i) (X j) : Ternary R).IsHomogeneous n := by
    apply isHomogeneous_bind₁_linear hq
    intro k
    fin_cases k <;> exact isHomogeneous_X _ _
  exact ((h 0 1).add (h 1 2)).add (h 2 0)

/-- The cyclic sum as a linear map into the homogeneous ternary solutions. -/
def cyclicLiftLinear (R : Type*) [CommRing R] (n : ℕ) :
    periodSpace R n →ₗ[R] solutionSpace R n where
  toFun q := ⟨cyclicLift q, cyclicLift_homogeneous q.property.1,
    cyclicLift_solution q.property.2⟩
  map_add' q r := by
    apply Subtype.ext
    simp only [cyclicLift, Submodule.coe_add, binaryEval_add]
    abel
  map_smul' a q := by
    apply Subtype.ext
    simp [cyclicLift, binaryEval, smul_add]

/-- The cyclic inverse is injective, witnessed by literal restriction. -/
theorem cyclicLiftLinear_injective (R : Type*) [CommRing R] (n : ℕ) :
    Function.Injective (cyclicLiftLinear R n) := by
  intro q r h
  apply Subtype.ext
  have h' := congrArg (fun f : solutionSpace R n => restriction f.val) h
  simpa only [cyclicLiftLinear, LinearMap.coe_mk, AddHom.coe_mk,
    restriction_cyclicLift q.property.2, restriction_cyclicLift r.property.2] using h'

end TernaryPoly.Paper
