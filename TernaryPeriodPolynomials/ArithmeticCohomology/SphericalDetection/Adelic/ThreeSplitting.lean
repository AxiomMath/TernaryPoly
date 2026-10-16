module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.ThreeLevelEmbedding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open Filter TopologicalSpace MeasureTheory
open scoped RestrictedProduct

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance threeSplitDecidableEq : DecidableEq FinitePlace := Classical.decEq _

theorem restrictedProduct_continuous_single {ι : Type*} {R : ι → Type*}
    {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, Zero (R i)]
    [∀ i, ZeroMemClass (S i) (R i)] [∀ i, TopologicalSpace (R i)]
    [DecidableEq ι] (A : ∀ i, S i) (i : ι) :
    Continuous (RestrictedProduct.single A i) := by
  let B : ∀ j, Set (R j) := fun j => A j
  let sectionMap (x : R i) : Πʳ j, [R j, B j]_[Filter.principal ({i}ᶜ)] :=
    ⟨Pi.single i x, Filter.eventually_principal.mpr (by
      intro j hj
      rw [Pi.single_eq_of_ne (by simpa using hj)]
      exact zero_mem (A j))⟩
  have section_continuous : Continuous sectionMap := by
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    intro j
    change Continuous (fun x : R i => Pi.single i x j)
    by_cases same : j = i
    · subst j
      simp only [Pi.single_eq_same]
      exact continuous_id
    · simp only [Pi.single_eq_of_ne same]
      exact continuous_const
  have cofinite_le : Filter.cofinite ≤ Filter.principal ({i}ᶜ : Set ι) :=
    Filter.le_principal_iff.mpr (Set.finite_singleton i).compl_mem_cofinite
  exact (RestrictedProduct.continuous_inclusion (R := R) (A := B) cofinite_le).comp
    section_continuous

theorem finiteAtThreeScalar_continuous : Continuous finiteAtThreeScalar := by
  exact (restrictedProduct_continuous_single
    (fun place : FinitePlace => place.adicCompletionIntegers ℚ) placeThree).comp
      threeCompletionEquiv.symm.continuous

def finiteAtThreeAdd : ℚ_[3] →+ FiniteAdeles where
  toFun := finiteAtThreeScalar
  map_zero' := by
    dsimp [finiteAtThreeScalar]
    rw [map_zero, RestrictedProduct.single_zero]
    rfl
  map_add' first second := by
    dsimp [finiteAtThreeScalar]
    rw [map_add, RestrictedProduct.single_add]
    rfl

theorem finiteThree_continuous : Continuous finiteThree :=
  threeCompletionEquiv.continuous.comp (RestrictedProduct.continuous_eval placeThree)

abbrev FiniteAwayThree := finiteThree.toAddMonoidHom.ker

def finiteAwayThree (value : FiniteAdeles) : FiniteAwayThree :=
  ⟨value - finiteAtThreeAdd (finiteThree value), by
    change finiteThree (value - finiteAtThreeScalar (finiteThree value)) = 0
    rw [map_sub, finiteAtThreeScalar_three, sub_self]⟩

def finiteThreeSplit : FiniteAdeles ≃ₜ+ (ℚ_[3] × FiniteAwayThree) where
  toFun value := (finiteThree value, finiteAwayThree value)
  invFun pair := finiteAtThreeAdd pair.1 + pair.2.val
  left_inv value := by
    change finiteAtThreeAdd (finiteThree value) + (value - finiteAtThreeAdd (finiteThree value)) = value
    abel
  right_inv pair := by
    obtain ⟨localValue, awayValue, awayZero⟩ := pair
    have away_eq : finiteThree awayValue = 0 := awayZero
    have three_eq : finiteThree (finiteAtThreeAdd localValue + awayValue) = localValue := by
      rw [map_add, away_eq, add_zero]
      exact finiteAtThreeScalar_three _
    apply Prod.ext three_eq
    apply Subtype.ext
    change finiteAtThreeAdd localValue + awayValue -
      finiteAtThreeAdd (finiteThree (finiteAtThreeAdd localValue + awayValue)) = awayValue
    rw [three_eq]
    abel
  map_add' first second := by
    apply Prod.ext (map_add finiteThree first second)
    apply Subtype.ext
    change first + second - finiteAtThreeAdd (finiteThree (first + second)) =
      (first - finiteAtThreeAdd (finiteThree first)) + (second - finiteAtThreeAdd (finiteThree second))
    rw [map_add, map_add]
    abel
  continuous_toFun := finiteThree_continuous.prodMk
    ((continuous_id.sub (finiteAtThreeScalar_continuous.comp finiteThree_continuous)).subtype_mk _)
  continuous_invFun := (finiteAtThreeScalar_continuous.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)

theorem finiteThreeSplit_fst (value : FiniteAdeles) :
    (finiteThreeSplit value).1 = finiteThree value := rfl

theorem finiteThreeSplit_symm (pair : ℚ_[3] × FiniteAwayThree) :
    finiteThreeSplit.symm pair = finiteAtThreeScalar pair.1 + pair.2.val := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
