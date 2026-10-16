/-
  Zero and finite-sum closure of `IsInduced`, used to assemble the Hecke
  translate's coefficients from the source cocycle's `IsInduced` clauses.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HasSmoothCuspLiftClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInducedClosure

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.IsInducedAssembly

variable {n : ℕ} {D : InducingData n} {side : Side} {s : ℂ}

theorem isInduced_zero : IsInduced D side s (fun _ : AdelicGL => (0 : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G
    simpa only [Pi.zero_apply] using SmoothClosure.smooth_zero (k := 1) (E := ℂ)
  · intro k G; rfl
  · intro a
    refine ⟨fun _ => 0, ?_, ?_⟩
    · simpa only [Submodule.coe_zero] using SmoothClosure.smooth_zero (k := 0 + 1) (E := D.cusp.H)
    · intro x A; rw [map_zero]; simp
  · cases side with
    | plane =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G; rfl
      · intro t G; ring
      · intro G
        have hz : (fun A : BinaryAdelicGL =>
              normPower (GeneralLinearGroup.det A)
                (-(((n : ℂ) + 3) / 2 + inductionExponent .plane s)) *
              (fun _ : AdelicGL => (0 : ℂ)) (planeLevi A 1 * G)) = 0 := by
          funext A; simp
        rw [hz]; exact Submodule.zero_mem _
    | line =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G; rfl
      · intro t G; ring
      · intro G
        have hz : (fun A : BinaryAdelicGL =>
              normPower (GeneralLinearGroup.det A)
                (-(((n : ℂ) + 3) / 2 - inductionExponent .line s)) *
              (fun _ : AdelicGL => (0 : ℂ)) (lineLevi 1 A * G)) = 0 := by
          funext A; simp
        rw [hz]; exact Submodule.zero_mem _

theorem isInduced_finset_sum {ι : Type*} (S : Finset ι) (f : ι → AdelicGL → ℂ)
    (h : ∀ i ∈ S, IsInduced D side s (f i)) :
    IsInduced D side s (fun g => ∑ i ∈ S, f i g) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simpa only [Finset.sum_empty] using (isInduced_zero (D := D) (side := side) (s := s))
  · intro a S ha ih h
    have he : (fun g => ∑ i ∈ insert a S, f i g) = fun g => f a g + ∑ i ∈ S, f i g := by
      funext g; rw [Finset.sum_insert ha]
    rw [he]
    exact IsInducedClosure.isInduced_add (h a (Finset.mem_insert_self a S))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end TernaryPeriodPolynomials.HeckeTranslate.IsInducedAssembly

end
