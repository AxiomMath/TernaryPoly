module

public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperTransport
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperDiscrete
public import Mathlib.Order.Northcott

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceSiegelReduction
open Matrix SymmetricSpacePositive SymmetricSpaceArithmeticProper

abbrev IntVector := Fin 3 → ℤ

def realVector (v : IntVector) : Vector := fun i => (v i : ℝ)

def energy (S : Space) (v : IntVector) : ℝ := quadratic S.val (realVector v)

theorem finite_integer_box (R : ℝ) : {v : IntVector | ∀ i, |(v i : ℝ)|≤R}.Finite := by
  let N : ℤ := ⌈R⌉
  have hb : {v : IntVector | ∀ i, v i∈Set.Icc (-N) N}.Finite :=
    Set.Finite.pi' (fun _ => Set.finite_Icc (-N) N)
  apply hb.subset
  intro v hv i
  have h := abs_le.mp ((hv i).trans (Int.le_ceil R))
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- The actual real positive form has finite integer-vector sublevels. -/
theorem finite_energy_sublevel (S : Space) (R : ℝ) : {v : IntVector | energy S v≤R}.Finite := by
  obtain ⟨ε,hε,hbound⟩ := compact_uniform_coercivity {S} isCompact_singleton
  apply (finite_integer_box (max 1 (R/ε))).subset
  intro v hv i
  have hsq : ε*‖realVector v‖^2≤R :=
    (hbound S (Set.mem_singleton S) (realVector v)).trans hv
  have hn : ‖realVector v‖≤max 1 (R/ε) := by
    by_cases h : ‖realVector v‖≤1
    · exact h.trans (le_max_left _ _)
    · have hs : ‖realVector v‖^2≤R/ε := (le_div_iff₀ hε).mpr (by nlinarith)
      have hl : 1<‖realVector v‖ := lt_of_not_ge h
      apply le_trans _ (le_max_right _ _)
      nlinarith
  exact (show |(v i : ℝ)|≤‖realVector v‖ from norm_le_pi_norm (realVector v) i).trans hn

/-- Minimization can be performed on any nonempty set of admissible integral vectors. -/
theorem exists_min_energy (S : Space) (s : Set IntVector) (hs : s.Nonempty) :
    ∃ v∈s, ∀ w∈s, energy S v≤energy S w := by
  let : Northcott (energy S) := ⟨finite_energy_sublevel S⟩
  exact Northcott.exists_min_image (energy S) s hs

/-- Only finiteness of the attained values below one witness is needed for a minimum. -/
theorem exists_min_of_finite_values {α : Type*} (f : α → ℝ) (s : Set α)
    (hs : s.Nonempty) (hfin : ∀ R, (f '' {x∈s | f x≤R}).Finite) :
    ∃ x∈s, ∀ y∈s, f x≤f y := by
  obtain ⟨x,hx⟩ := hs
  obtain ⟨r,⟨z,⟨hz,hzx⟩,rfl⟩,hmin⟩ :=
    Set.exists_min_image (f '' {y∈s | f y≤f x}) id (hfin (f x))
      ⟨f x,⟨x,⟨hx,le_rfl⟩,rfl⟩⟩
  refine ⟨z,hz,?_⟩
  intro y hy
  by_cases h : f y≤f x
  · exact hmin (f y) ⟨y,⟨hy,h⟩,rfl⟩
  · exact hzx.trans (le_of_not_ge h)

end TernaryPoly.SymmetricSpaceSiegelReduction
