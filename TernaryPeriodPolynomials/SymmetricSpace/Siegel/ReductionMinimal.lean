module

public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionProjection

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceSiegelReduction
open Matrix SymmetricSpacePositive SymmetricSpaceArithmeticProper

/-- An actual integral flag with two successive minimal squared lengths. -/
def MinimalFlag (S : Space) (g : IntegralGL) : Prop :=
  (∀ h : IntegralGL, energy S (row g 2)≤energy S (row h 2)) ∧
  ∀ h : IntegralGL, row h 2=row g 2 →
    projectedEnergy S (row g 2) (row g 1)≤projectedEnergy S (row g 2) (row h 1)

/-- Projected-energy values are locally finite after reduction along the fixed last row. -/
theorem finite_projected_values (S : Space) (v : IntVector) (hv : 0<energy S v) (R : ℝ) :
    ((fun g : IntegralGL => projectedEnergy S v (row g 1)) ''
      {g | row g 2=v ∧ projectedEnergy S v (row g 1)≤R}).Finite := by
  apply ((finite_energy_sublevel S (R+energy S v/4)).image (projectedEnergy S v)).subset
  rintro r ⟨g,⟨_,hg⟩,rfl⟩
  obtain ⟨n,_,hn⟩ := exists_reduced_projection S v (row g 1) hv
  refine ⟨row g 1+n • v,?_,projectedEnergy_add_smul S v (row g 1) n (ne_of_gt hv)⟩
  change energy S (row g 1+n • v)≤R+energy S v/4
  linarith

/-- Both minimizations are over actual unimodular bases; no completion theorem is assumed. -/
theorem exists_minimal_flag (S : Space) : ∃ g : IntegralGL, MinimalFlag S g := by
  obtain ⟨g,hg⟩ := exists_minimal_last_row S
  obtain ⟨h,hh,hmin⟩ := exists_min_of_finite_values
    (fun h : IntegralGL => projectedEnergy S (row g 2) (row h 1))
    {h | row h 2=row g 2} ⟨g,rfl⟩
    (finite_projected_values S (row g 2) (energy_row_pos S g 2))
  refine ⟨h,?_,?_⟩
  · intro k
    rw [hh]
    exact hg k
  · intro k hk
    rw [hh]
    exact hmin k (hk.trans hh)

/-- Integer size reduction preserves the minimal flag whenever it preserves these two data. -/
theorem MinimalFlag.of_same_data (S : Space) {g h : IntegralGL} (hg : MinimalFlag S g)
    (hlast : row h 2=row g 2)
    (hsecond : projectedEnergy S (row g 2) (row h 1)=projectedEnergy S (row g 2) (row g 1)) :
    MinimalFlag S h := by
  constructor
  · intro k
    rw [hlast]
    exact hg.1 k
  · intro k hk
    rw [hlast,hsecond]
    exact hg.2 k (hk.trans hlast)

end TernaryPoly.SymmetricSpaceSiegelReduction
