module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AffineNilpotent
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.CocycleExtension

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def nilpotentExpEquiv (operator : Module.End ℂ V) (nilpotent : IsNilpotent operator) :
    V ≃ₗ[ℂ] V where
  toLinearMap := IsNilpotent.exp operator
  invFun vector := IsNilpotent.exp (-operator) vector
  left_inv vector := by
    change (IsNilpotent.exp (-operator) * IsNilpotent.exp operator) vector = vector
    rw [IsNilpotent.exp_neg_mul_exp_self nilpotent, Module.End.one_apply]
  right_inv vector := by
    change (IsNilpotent.exp operator * IsNilpotent.exp (-operator)) vector = vector
    rw [IsNilpotent.exp_mul_exp_neg_self nilpotent, Module.End.one_apply]

theorem nilpotentExpEquiv_apply (operator : Module.End ℂ V) (nilpotent : IsNilpotent operator)
    (vector : V) : nilpotentExpEquiv operator nilpotent vector = IsNilpotent.exp operator vector := rfl

def latticeInfinitesimal (first second : Module.End ℂ V) (element : RadicalLattice) :
    Module.End ℂ V :=
  (element.toAdd.1 : ℂ) • first + (element.toAdd.2 : ℂ) • second

theorem latticeInfinitesimal_one (first second : Module.End ℂ V) :
    latticeInfinitesimal first second 1 = 0 := by simp [latticeInfinitesimal]

theorem latticeInfinitesimal_mul (first second : Module.End ℂ V) (left right : RadicalLattice) :
    latticeInfinitesimal first second (left * right) =
      latticeInfinitesimal first second left + latticeInfinitesimal first second right := by
  change ((left.toAdd.1 + right.toAdd.1 : ℤ) : ℂ) • first +
    ((left.toAdd.2 + right.toAdd.2 : ℤ) : ℂ) • second = _
  simp only [latticeInfinitesimal, Int.cast_add, add_smul]
  abel

theorem latticeInfinitesimal_first (first second : Module.End ℂ V) :
    latticeInfinitesimal first second radicalLatticeFirst = first := by
  simp [latticeInfinitesimal, radicalLatticeFirst]

theorem latticeInfinitesimal_second (first second : Module.End ℂ V) :
    latticeInfinitesimal first second radicalLatticeSecond = second := by
  simp [latticeInfinitesimal, radicalLatticeSecond]

theorem latticeInfinitesimal_commute (first second : Module.End ℂ V)
    (commute : Commute first second) (left right : RadicalLattice) :
    Commute (latticeInfinitesimal first second left) (latticeInfinitesimal first second right) := by
  apply Commute.add_left <;> apply Commute.add_right
  · exact ((Commute.refl first).smul_left _).smul_right _
  · exact (commute.smul_left _).smul_right _
  · exact (commute.symm.smul_left _).smul_right _
  · exact ((Commute.refl second).smul_left _).smul_right _

theorem latticeInfinitesimal_nilpotent (first second : Module.End ℂ V)
    (commute : Commute first second) (first_nilpotent : IsNilpotent first)
    (second_nilpotent : IsNilpotent second) (element : RadicalLattice) :
    IsNilpotent (latticeInfinitesimal first second element) :=
  ((commute.smul_left _).smul_right _).isNilpotent_add
    (first_nilpotent.smul (element.toAdd.1 : ℂ)) (second_nilpotent.smul (element.toAdd.2 : ℂ))

/-- Exponentiate two commuting nilpotent operators on the full integer lattice. -/
def nilpotentLatticeAction (first second : Module.End ℂ V) (commute : Commute first second)
    (first_nilpotent : IsNilpotent first) (second_nilpotent : IsNilpotent second) :
    RadicalLattice →* (V ≃ₗ[ℂ] V) where
  toFun element := nilpotentExpEquiv (latticeInfinitesimal first second element)
    (latticeInfinitesimal_nilpotent first second commute first_nilpotent second_nilpotent element)
  map_one' := by
    apply LinearEquiv.ext
    intro vector
    change IsNilpotent.exp (latticeInfinitesimal first second 1) vector = vector
    rw [latticeInfinitesimal_one, IsNilpotent.exp_zero, Module.End.one_apply]
  map_mul' left right := by
    apply LinearEquiv.ext
    intro vector
    change IsNilpotent.exp (latticeInfinitesimal first second (left * right)) vector =
      (IsNilpotent.exp (latticeInfinitesimal first second left) *
        IsNilpotent.exp (latticeInfinitesimal first second right)) vector
    rw [latticeInfinitesimal_mul, IsNilpotent.exp_add_of_commute
      (latticeInfinitesimal_commute first second commute left right)
      (latticeInfinitesimal_nilpotent first second commute first_nilpotent second_nilpotent left)
      (latticeInfinitesimal_nilpotent first second commute first_nilpotent second_nilpotent right)]

theorem nilpotentLatticeAction_apply (first second : Module.End ℂ V) (commute : Commute first second)
    (first_nilpotent : IsNilpotent first) (second_nilpotent : IsNilpotent second)
    (element : RadicalLattice) (vector : V) :
    nilpotentLatticeAction first second commute first_nilpotent second_nilpotent element vector =
      IsNilpotent.exp (latticeInfinitesimal first second element) vector := rfl

theorem latticeInfinitesimal_affine (first second : Module.End ℂ V) (alpha beta : V)
    (element : RadicalLattice) :
    latticeInfinitesimal (affineInfinitesimal first alpha) (affineInfinitesimal second beta) element =
      affineInfinitesimal (latticeInfinitesimal first second element)
        ((element.toAdd.1 : ℂ) • alpha + (element.toAdd.2 : ℂ) • beta) := by
  simp only [latticeInfinitesimal, affineInfinitesimal_add, affineInfinitesimal_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
