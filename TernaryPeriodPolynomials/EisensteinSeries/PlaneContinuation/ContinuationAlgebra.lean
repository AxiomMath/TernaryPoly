module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Helpers
public import Mathlib.Analysis.Meromorphic.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ContinuationAlgebra

theorem add {first second firstContinuation secondContinuation : ℂ → AdelicGL → ℂ}
    (firstContinues : IsEisensteinContinuation first firstContinuation)
    (secondContinues : IsEisensteinContinuation second secondContinuation) :
    IsEisensteinContinuation (fun parameter point => first parameter point + second parameter point)
      (fun parameter point => firstContinuation parameter point + secondContinuation parameter point) := by
  refine ⟨fun point parameter => (firstContinues.1 point parameter).add (secondContinues.1 point parameter), ?_⟩
  obtain ⟨firstBound, firstEquality⟩ := firstContinues.2
  obtain ⟨secondBound, secondEquality⟩ := secondContinues.2
  refine ⟨max firstBound secondBound, fun parameter halfPlane point => ?_⟩
  exact (firstEquality parameter (lt_of_le_of_lt (le_max_left _ _) halfPlane) point).add
    (secondEquality parameter (lt_of_le_of_lt (le_max_right _ _) halfPlane) point)

theorem multiply {sectionFunction continuation : ℂ → AdelicGL → ℂ}
    (continues : IsEisensteinContinuation sectionFunction continuation)
    (factor : ℂ → ℂ) (meromorphic : ∀ parameter, MeromorphicAt factor parameter) :
    IsEisensteinContinuation (fun parameter point => factor parameter * sectionFunction parameter point)
      (fun parameter point => factor parameter * continuation parameter point) := by
  refine ⟨fun point parameter => (meromorphic parameter).mul (continues.1 point parameter), ?_⟩
  obtain ⟨bound, equality⟩ := continues.2
  exact ⟨bound, fun parameter halfPlane point => (equality parameter halfPlane point).mul_left (factor parameter)⟩

theorem finset_sum {Index : Type*} (indices : Finset Index)
    (sections continuations : Index → ℂ → AdelicGL → ℂ)
    (continues : ∀ index ∈ indices, IsEisensteinContinuation (sections index) (continuations index)) :
    IsEisensteinContinuation (fun parameter point => ∑ index ∈ indices, sections index parameter point)
      (fun parameter point => ∑ index ∈ indices, continuations index parameter point) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Helpers.zero_eisensteinContinuation
  | @insert index indices outside induction =>
    have result := add (continues index (Finset.mem_insert_self _ _))
      (induction (fun other membership => continues other (Finset.mem_insert_of_mem membership)))
    simpa only [Finset.sum_insert outside] using result

theorem transfer {first second continuation : ℂ → AdelicGL → ℂ}
    (continues : IsEisensteinContinuation first continuation) (bound : ℝ)
    (equal : ∀ parameter : ℂ, bound < parameter.re → ∀ point, first parameter point = second parameter point) :
    IsEisensteinContinuation second continuation := by
  refine ⟨continues.1, ?_⟩
  obtain ⟨originalBound, summed⟩ := continues.2
  refine ⟨max originalBound bound, fun parameter halfPlane point => ?_⟩
  apply (summed parameter (lt_of_le_of_lt (le_max_left _ _) halfPlane) point).congr_fun
  intro flag
  exact (equal parameter (lt_of_le_of_lt (le_max_right _ _) halfPlane) _).symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ContinuationAlgebra
