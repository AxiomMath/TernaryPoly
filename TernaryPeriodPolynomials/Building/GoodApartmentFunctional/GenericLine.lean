module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.Incidence
public import Mathlib.Algebra.Module.Submodule.Union

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases TernaryPeriodPolynomials.GoodApartmentFunctional.Incidence

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.GenericLine

noncomputable section

theorem finite_subspaces_integral_direction
    (subspaces : Finset (Submodule ℚ (Fin 3 → ℚ)))
    (proper : ∀ subspace ∈ subspaces, subspace ≠ ⊤) :
    ∃ vector : Fin 3 → ℤ,
      ∀ subspace ∈ subspaces, integerVectorMap vector ∉ subspace := by
  classical
  obtain ⟨rational, outside⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun subspace : subspaces => subspace.val) (fun subspace => proper _ subspace.property)
  obtain ⟨scalar, integral, nonzero, equality⟩ := rationalVector_has_integral_multiple rational
  refine ⟨integral, ?_⟩
  intro subspace membership contained
  apply outside ⟨subspace, membership⟩
  rw [← equality] at contained
  exact (subspace.smul_mem_iff (Int.cast_ne_zero.mpr nonzero : (scalar : ℚ) ≠ 0)).mp contained

def affineIntegralVector (direction : Fin 3 → ℤ) (parameter : ℤ) : Fin 3 → ℤ :=
  fun coordinate => ![0, 0, 1] coordinate + 3 * parameter * direction coordinate

theorem affineIntegralVector_normalized (direction : Fin 3 → ℤ) (parameter : ℤ) :
    ((affineIntegralVector direction parameter) 2 : ZMod 3) = 1 := by
  change ((1 + 3 * parameter * direction 2 : ℤ) : ZMod 3) = 1
  rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
  rw [show ((3 : ℤ) : ZMod 3) = 0 from rfl]
  simp

theorem affineIntegralVector_sub (direction : Fin 3 → ℤ) (first second : ℤ) :
    integerVectorMap (affineIntegralVector direction first) -
      integerVectorMap (affineIntegralVector direction second) =
        (3 * ((first : ℚ) - second)) • integerVectorMap direction := by
  ext coordinate
  change ((![0, 0, 1] coordinate + 3 * first * direction coordinate : ℤ) : ℚ) -
    ((![0, 0, 1] coordinate + 3 * second * direction coordinate : ℤ) : ℚ) =
      3 * ((first : ℚ) - second) * (direction coordinate : ℚ)
  push_cast
  ring

theorem affineIntegralVector_exception_subsingleton
    (subspace : Submodule ℚ (Fin 3 → ℚ)) (direction : Fin 3 → ℤ)
    (outside : integerVectorMap direction ∉ subspace) :
    Set.Subsingleton
      {parameter : ℤ | integerVectorMap (affineIntegralVector direction parameter) ∈ subspace} := by
  intro first firstMem second secondMem
  by_contra distinct
  have coefficientNonzero : 3 * ((first : ℚ) - second) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact sub_ne_zero.mpr (fun equality => distinct (Int.cast_injective equality))
  apply outside
  have difference := subspace.sub_mem firstMem secondMem
  rw [affineIntegralVector_sub] at difference
  exact (subspace.smul_mem_iff coefficientNonzero).mp difference

theorem finite_subspaces_normalized_integral_vector
    (subspaces : Finset (Submodule ℚ (Fin 3 → ℚ)))
    (proper : ∀ subspace ∈ subspaces, subspace ≠ ⊤) :
    ∃ vector : Fin 3 → ℤ, (vector 2 : ZMod 3) = 1 ∧
      ∀ subspace ∈ subspaces, integerVectorMap vector ∉ subspace := by
  classical
  obtain ⟨direction, outside⟩ := finite_subspaces_integral_direction subspaces proper
  have exceptionsFinite :
      (⋃ subspace ∈ subspaces,
        {parameter : ℤ | integerVectorMap (affineIntegralVector direction parameter) ∈
          subspace}).Finite := by
    apply subspaces.finite_toSet.biUnion
    intro subspace membership
    exact (affineIntegralVector_exception_subsingleton subspace direction
      (outside subspace membership)).finite
  obtain ⟨parameter, avoids⟩ := exceptionsFinite.exists_notMem
  refine ⟨affineIntegralVector direction parameter,
    affineIntegralVector_normalized direction parameter, ?_⟩
  intro subspace membership contained
  apply avoids
  exact Set.mem_iUnion.mpr ⟨subspace, Set.mem_iUnion.mpr ⟨membership, contained⟩⟩

theorem vector_extends_rational_frame (vector : Fin 3 → ℚ) (nonzero : vector ≠ 0) :
    ∃ frame : RationalGL3, frame.val.col 0 = vector := by
  have proper : Submodule.span ℚ {vector} ≠ ⊤ := by
    intro equality
    have rank := finrank_span_singleton (K := ℚ) nonzero
    rw [equality] at rank
    norm_num at rank
  obtain ⟨second, outside⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun _index : Fin 1 => Submodule.span ℚ {vector}) (fun _index => proper)
  have independent : LinearIndependent ℚ ![vector, second] := by
    apply (LinearIndependent.pair_iff' nonzero).mpr
    intro scalar equality
    apply outside 0
    rw [← equality]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self vector)
  obtain ⟨frame, firstColumn, _secondColumn⟩ := pair_extends_rational_frame vector second independent
  exact ⟨frame, firstColumn⟩

theorem good_line_avoiding_finite_planes (planes : Finset (Flags .plane)) :
    ∃ line : Flags .line, GoodFlag .line line ∧
      ∀ plane ∈ planes, ¬flagSubspace .line line ≤ flagSubspace .plane plane := by
  classical
  let subspaces := planes.image (flagSubspace .plane)
  have proper : ∀ subspace ∈ subspaces, subspace ≠ ⊤ := by
    intro subspace membership
    obtain ⟨plane, _planeMem, rfl⟩ := Finset.mem_image.mp membership
    intro equality
    have rank := flagSubspace_finrank .plane plane
    rw [equality] at rank
    norm_num at rank
  obtain ⟨vector, normalized, outside⟩ :=
    finite_subspaces_normalized_integral_vector subspaces proper
  have nonzero : integerVectorMap vector ≠ 0 := by
    intro zero
    have coordinate : (vector 2 : ℚ) = 0 := congrFun zero 2
    have integralZero : vector 2 = 0 := Int.cast_eq_zero.mp coordinate
    rw [integralZero, Int.cast_zero] at normalized
    exact zero_ne_one normalized
  obtain ⟨frame, firstColumn⟩ := vector_extends_rational_frame (integerVectorMap vector) nonzero
  refine ⟨QuotientGroup.mk frame, ?_, ?_⟩
  · rw [goodFlag_iff, flagSubspace_mk, line_frame_subspace, firstColumn]
    exact ⟨vector, Submodule.mem_span_singleton_self _, normalized ▸ one_ne_zero⟩
  · intro plane membership incidence
    apply outside (flagSubspace .plane plane) (Finset.mem_image.mpr ⟨plane, membership, rfl⟩)
    apply incidence
    rw [flagSubspace_mk, line_frame_subspace, firstColumn]
    exact Submodule.mem_span_singleton_self _

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.GenericLine
