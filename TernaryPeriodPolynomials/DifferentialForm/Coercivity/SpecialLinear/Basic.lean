module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.HodgeMetric
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.GroupMetric
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.SpectralArithmetic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section


/-! Concrete finite-dimensional coefficient and exterior-degree-two algebraic operator.
Strict positive coercivity and the Casimir spectral comparison are not proved here. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

instance homogeneousPoly_finite (n : ℕ) :
    FiniteDimensional ℝ (homogeneousSubmodule (Fin 3) ℝ n) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 3) ℝ n)

/-- The exterior-coordinate space embeds into finitely many homogeneous coefficient spaces. -/
def homogeneousTwoCoordinateMap (n : ℕ) : homogeneousTwoForms n →ₗ[ℝ]
    (Fin 5 → Fin 5 → homogeneousSubmodule (Fin 3) ℝ n) where
  toFun a i j := ⟨a.val i j, a.property.2 i j⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem homogeneousTwoCoordinateMap_injective (n : ℕ) :
    Function.Injective (homogeneousTwoCoordinateMap n) := by
  intro a b h
  apply Subtype.ext
  funext i j
  exact congrArg Subtype.val (congrFun (congrFun h i) j)

instance homogeneousTwoForms_finite (n : ℕ) : FiniteDimensional ℝ (homogeneousTwoForms n) :=
  FiniteDimensional.of_injective (homogeneousTwoCoordinateMap n)
    (homogeneousTwoCoordinateMap_injective n)

/-- Bundled algebraic Hodge operator on actual homogeneous alternating two-forms. -/
def homogeneousHodgeTwo (n : ℕ) : Module.End ℝ (homogeneousTwoForms n) where
  toFun a := ⟨algebraicHodgeTwo a.val, algebraicHodgeTwo_mem a.val a.property⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    funext i j
    change algebraicHodgeTwo (a.val + b.val) i j =
      algebraicHodgeTwo a.val i j + algebraicHodgeTwo b.val i j
    simp only [algebraicHodgeTwo_expansion, Pi.add_apply, map_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    module
  map_smul' := by
    intro c a
    apply Subtype.ext
    funext i j
    change algebraicHodgeTwo (c • a.val) i j = c • algebraicHodgeTwo a.val i j
    simp only [algebraicHodgeTwo_expansion, Pi.smul_apply, Derivation.map_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    module

@[simp] theorem homogeneousHodgeTwo_apply (n : ℕ) (a : homogeneousTwoForms n) :
    (homogeneousHodgeTwo n a).val = algebraicHodgeTwo a.val := rfl

theorem homogeneousHodgeTwo_nonneg (n : ℕ) (a : homogeneousTwoForms n) :
    0 ≤ twoPairing (homogeneousHodgeTwo n a).val a.val :=
  algebraicHodgeTwo_nonneg a.val a.property.1

end TernaryPoly.SL3PolynomialCoercivity
