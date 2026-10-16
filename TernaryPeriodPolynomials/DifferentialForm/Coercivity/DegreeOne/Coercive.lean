module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.Algebra
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.InjectivityOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Basic
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.StrictEnergy

@[expose] public section



/-! # Bundled degree-one Hodge operator and its coercivity at `n = 1`

Mirrors `TernaryPoly.SL3PolynomialCoercivity`'s bundled `homogeneousTwoCoordinateMap` /
`homogeneousHodgeTwo` / `homogeneousTwoInnerCore` apparatus and
`TernaryPoly.SL3PolynomialCoercivityStrictEnergy`'s `homogeneousHodgeTwo_coercive_of_kernel`,
one exterior degree down, specialized at the end to the `n = 1` case using
`exteriorOne_injective_of_isHomogeneous_one` directly. -/

noncomputable section
open TernaryPoly.SL3PolynomialCoercivity MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CoercivityOne

/-- Coordinates of a homogeneous degree-one element, bundled into the product of
homogeneous-polynomial submodules. -/
def homogeneousOneCoordinateMap (n : ℕ) : homogeneousOneForms n →ₗ[ℝ]
    (Fin 5 → homogeneousSubmodule (Fin 3) ℝ n) where
  toFun a i := ⟨a.val i, a.property i⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem homogeneousOneCoordinateMap_injective (n : ℕ) :
    Function.Injective (homogeneousOneCoordinateMap n) := by
  intro a b h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

instance homogeneousOneForms_finite (n : ℕ) : FiniteDimensional ℝ (homogeneousOneForms n) :=
  FiniteDimensional.of_injective (homogeneousOneCoordinateMap n)
    (homogeneousOneCoordinateMap_injective n)

/-- The algebraic Hodge operator in exterior degree one, bundled as an endomorphism of the
homogeneous-degree-`n` submodule. -/
def homogeneousHodgeOne (n : ℕ) : Module.End ℝ (homogeneousOneForms n) where
  toFun a := ⟨algebraicHodgeOne a.val, algebraicHodgeOne_mem a.val a.property⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    funext i
    change algebraicHodgeOne (a.val + b.val) i =
      algebraicHodgeOne a.val i + algebraicHodgeOne b.val i
    simp only [algebraicHodgeOne_expansion, Pi.add_apply, map_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    module
  map_smul' := by
    intro c a
    apply Subtype.ext
    funext i
    change algebraicHodgeOne (c • a.val) i = c • algebraicHodgeOne a.val i
    simp only [algebraicHodgeOne_expansion, Pi.smul_apply, Derivation.map_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    module

@[simp] theorem homogeneousHodgeOne_apply (n : ℕ) (a : homogeneousOneForms n) :
    (homogeneousHodgeOne n a).val = algebraicHodgeOne a.val := rfl

theorem homogeneousHodgeOne_nonneg (n : ℕ) (a : homogeneousOneForms n) :
    0 ≤ onePairing (homogeneousHodgeOne n a).val a.val :=
  algebraicHodgeOne_nonneg a.val

/-- The `onePairing` inner-product core on homogeneous degree-`n` `OneCoordinates`, mirroring
`homogeneousTwoInnerCore`. -/
@[instance_reducible] def homogeneousOneInnerCore (n : ℕ) :
    InnerProductSpace.Core ℝ (homogeneousOneForms n) where
  inner := fun a b => onePairing a.val b.val
  conj_inner_symm := fun a b => by simpa using onePairing_symmetric b.val a.val
  re_inner_nonneg := fun a => onePairing_self_nonneg a.val
  add_left := by intros; apply onePairing_add_left
  smul_left := by intros; simp [onePairing, Finset.mul_sum, mul_left_comm]
  definite := fun a h => Subtype.ext ((onePairing_self_eq_zero a.val).mp h)

/-- Coercivity of the degree-one algebraic Hodge operator at `n = 1`, where the Casimir +
Cauchy-Schwarz bound planned for `n ≥ 2` fails but `exteriorOne` alone is already injective
(`exteriorOne_injective_of_isHomogeneous_one`). -/
theorem homogeneousHodgeOne_coercive_degree_one :
    ∃ c : ℝ, 0 < c ∧ ∀ a : homogeneousOneForms 1,
      c * onePairing a.val a.val ≤ onePairing (homogeneousHodgeOne 1 a).val a.val := by
  let : InnerProductSpace.Core ℝ (homogeneousOneForms 1) := homogeneousOneInnerCore 1
  let : NormedAddCommGroup (homogeneousOneForms 1) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ (homogeneousOneForms 1) :=
    InnerProductSpace.ofCore (homogeneousOneInnerCore 1).toCore
  apply finite_inner_coercivity (homogeneousHodgeOne 1)
  intro a ha
  change 0 < onePairing (algebraicHodgeOne a.val) a.val
  apply lt_of_le_of_ne (algebraicHodgeOne_nonneg a.val)
  intro hz
  apply ha
  apply Subtype.ext
  show a.val = 0
  apply exteriorOne_injective_of_isHomogeneous_one a.val a.property
  have hz' := hz.symm
  rw [algebraicHodgeOne_energy] at hz'
  have h2 : twoPairing (exteriorOne a.val) (exteriorOne a.val) ≤ 0 := by
    linarith [factorialPairing_self_nonneg (contractionOne a.val)]
  have h3 : twoPairing (exteriorOne a.val) (exteriorOne a.val) = 0 :=
    le_antisymm h2 (twoPairing_self_nonneg _)
  exact (twoPairing_self_eq_zero _).mp h3

end TernaryPeriodPolynomials.Argument.CoercivityOne
