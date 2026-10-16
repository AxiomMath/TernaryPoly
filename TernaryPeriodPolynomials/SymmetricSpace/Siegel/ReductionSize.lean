module

public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionMinimal
public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionUpper

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceSiegelReduction
open Matrix SymmetricSpacePositive SymmetricSpaceArithmeticProper SymmetricSpaceFlagCoordinates

def ldlCoordinates (S : Space) (g : IntegralGL) : LDLParameters :=
  ldlHomeomorph (act (realIntegral g) S)

theorem ldlCoordinates_upper (S : Space) (g : IntegralGL) (m n k : ℤ) :
    ldlCoordinates S (upperIntegral m n k*g)=upperCoordinates m n k (ldlCoordinates S g) := by
  unfold ldlCoordinates
  rw [map_mul,act_mul,ldlHomeomorph_act_upper]

theorem MinimalFlag.upper (S : Space) {g : IntegralGL} (hg : MinimalFlag S g) (m n k : ℤ) :
    MinimalFlag S (upperIntegral m n k*g) := by
  apply MinimalFlag.of_same_data S hg (row_upper_two m n k g)
  rw [row_upper_one]
  exact projectedEnergy_add_smul S (row g 2) (row g 1) n (ne_of_gt (energy_row_pos S g 2))

theorem exists_integer_shift (x : ℝ) : ∃ n : ℤ, |x+(n : ℝ)|≤1/2 := by
  refine ⟨-round x,?_⟩
  simpa only [Int.cast_neg,sub_eq_add_neg] using abs_sub_round x

/-- A single actual integer upper matrix bounds all three unipotent coordinates and preserves
both minimizing conditions. -/
theorem exists_size_reduced_flag (S : Space) {g : IntegralGL} (hg : MinimalFlag S g) :
    ∃ h : IntegralGL, MinimalFlag S h ∧ ∀ i, |(ldlCoordinates S h).1 i|≤1/2 := by
  obtain ⟨m,hm⟩ := exists_integer_shift ((ldlCoordinates S g).1 0)
  obtain ⟨n,hn⟩ := exists_integer_shift ((ldlCoordinates S g).1 1)
  obtain ⟨k,hk⟩ := exists_integer_shift ((ldlCoordinates S g).1 2+m*(ldlCoordinates S g).1 1)
  refine ⟨upperIntegral m n k*g,hg.upper S m n k,?_⟩
  intro i
  rw [ldlCoordinates_upper]
  fin_cases i
  · exact hm
  · exact hn
  · exact hk

end TernaryPoly.SymmetricSpaceSiegelReduction
