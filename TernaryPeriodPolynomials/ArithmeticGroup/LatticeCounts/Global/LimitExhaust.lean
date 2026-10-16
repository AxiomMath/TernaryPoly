module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitShape

@[expose] public section


/-!
# Global limit: the exhaustion of `FiniteAwayThree²` by the regions `U_S`

`S` ranges over finite sets of primes `p ≠ 3` (`PIdx`), embedded in the places by `embP` (`p ↦ primesEquiv.symm p`).  `Uex S = UregionS (S.map embP)`
is measurable, increasing in `S`, and covers `FiniteAwayThree²` (every finite adele is integral at almost all places; the place three is integral on `FiniteAwayThree` by definition).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit

open Classical

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitExhaust

/-- Primes different from three. -/
abbrev PIdx : Type := {p : Nat.Primes // p.val ≠ 3}

/-- The place of a prime `≠ 3`. -/
def embP : PIdx ↪ FinitePlace :=
  ⟨fun p => Rat.HeightOneSpectrum.primesEquiv.symm p.1, fun _ _ h =>
    Subtype.ext ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective h)⟩

theorem embP_ne (p : PIdx) : embP p ≠ placeThree := by
  intro h
  have := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective h
  exact p.2 (congrArg Subtype.val this)

/-- The finite set of places attached to a finite set of primes. -/
def SEP (T : Finset PIdx) : Finset FinitePlace := T.map embP

theorem SEP_ne (T : Finset PIdx) : ∀ p ∈ SEP T, p ≠ placeThree := by
  intro p hp
  obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hp
  exact embP_ne q

/-- The exhausting regions. -/
def Uex (T : Finset PIdx) : Set (FiniteAwayThree × FiniteAwayThree) := UregionS (SEP T)

theorem Uex_measurable (T : Finset PIdx) : MeasurableSet (Uex T) :=
  UregionS_measurable (SEP T) (SEP_ne T)

theorem Uex_mono : Monotone Uex := by
  intro S T hST z hz w hw
  refine hz w fun hw' => hw ?_
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hw'
  exact Finset.mem_map.2 ⟨q, hST hq, rfl⟩

theorem eval_three_mem (x : FiniteAwayThree) : finiteEvaluation placeThree x.val ∈ OS placeThree := by
  have h : finiteThree x.val = 0 := x.2
  have h0 : finiteEvaluation placeThree x.val = 0 := by
    have : threeCompletionEquiv (finiteEvaluation placeThree x.val) = 0 := h
    exact (map_eq_zero_iff _ threeCompletionEquiv.injective).1 this
  rw [h0]
  exact (OS placeThree).zero_mem

theorem Uex_cover (z : FiniteAwayThree × FiniteAwayThree) : ∃ T : Finset PIdx, z ∈ Uex T := by
  have h1 : {w : FinitePlace | ¬ finiteEvaluation w (awayVal z.1) ∈ OS w}.Finite :=
    Filter.eventually_cofinite.1 (awayVal z.1).2
  have h2 : {w : FinitePlace | ¬ finiteEvaluation w (awayVal z.2) ∈ OS w}.Finite :=
    Filter.eventually_cofinite.1 (awayVal z.2).2
  have hF := h1.union h2
  have hfin : {q : PIdx | embP q ∈ {w : FinitePlace | ¬ finiteEvaluation w (awayVal z.1) ∈ OS w} ∪
      {w : FinitePlace | ¬ finiteEvaluation w (awayVal z.2) ∈ OS w}}.Finite :=
    hF.preimage (embP.injective.injOn)
  refine ⟨hfin.toFinset, fun w hw => ?_⟩
  by_cases h3 : w = placeThree
  · subst h3
    exact ⟨eval_three_mem z.1, eval_three_mem z.2⟩
  · by_contra hcon
    apply hw
    have hq : (Rat.HeightOneSpectrum.primesEquiv w).val ≠ 3 := by
      intro h
      apply h3
      have h' : Rat.HeightOneSpectrum.primesEquiv w = primeThree := Subtype.ext h
      calc w = Rat.HeightOneSpectrum.primesEquiv.symm (Rat.HeightOneSpectrum.primesEquiv w) :=
            (Equiv.symm_apply_apply _ _).symm
        _ = placeThree := by rw [h']; rfl
    have hemb : embP ⟨Rat.HeightOneSpectrum.primesEquiv w, hq⟩ = w := Equiv.symm_apply_apply _ _
    refine Finset.mem_map.2 ⟨⟨Rat.HeightOneSpectrum.primesEquiv w, hq⟩, ?_, hemb⟩
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hemb]
    by_contra hn
    apply hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    exact hn

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitExhaust
