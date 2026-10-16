module

public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionCoordinates
public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionScalarBounds
public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionCompact

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceSiegelReduction
open Matrix SymmetricSpacePositive SymmetricSpaceArithmeticProper SymmetricSpaceFlagCoordinates

/-- Swapping actual integral basis rows gives the two successive minimum inequalities. -/
theorem minimum_coordinate_inequalities (S : Space) {g : IntegralGL} (hg : MinimalFlag S g) :
    1≤(ldlCoordinates S g).2.2.val+((ldlCoordinates S g).1 1)^2 ∧
    (ldlCoordinates S g).2.2.val≤(ldlCoordinates S g).2.1.val+
      ((ldlCoordinates S g).1 0)^2*(ldlCoordinates S g).2.2.val := by
  obtain ⟨c,hc,he2,he1,hd1,hd0⟩ := flag_energy_data S g
  constructor
  · have h := hg.1 (swap12*g)
    rw [row_swap12_two,he2,he1] at h
    apply (mul_le_mul_iff_right₀ hc).mp
    simpa only [mul_one] using h
  · have h := hg.2 (swap01*g) (row_swap01_two g)
    rw [row_swap01_one,hd1,hd0] at h
    exact (mul_le_mul_iff_right₀ hc).mp h

/-- Actual uniform Siegel reduction: one integral basis gives bounded unipotent and positive
simple-root coordinates, with the explicit universal bounds one half and two. -/
theorem exists_reduced_integral_basis (S : Space) :
    ∃ g : IntegralGL,
      (∀ i, |(rootHomeomorph (act (realIntegral g) S)).1 i|≤1/2) ∧
      (rootHomeomorph (act (realIntegral g) S)).2.1.val≤2 ∧
      (rootHomeomorph (act (realIntegral g) S)).2.2.val≤2 := by
  obtain ⟨g,hg⟩ := exists_minimal_flag S
  obtain ⟨h,hh,hsize⟩ := exists_size_reduced_flag S hg
  obtain ⟨hlast,hsecond⟩ := minimum_coordinate_inequalities S hh
  have hb := root_bounds_of_minimum_inequalities
    ((ldlCoordinates S h).1 0) ((ldlCoordinates S h).1 1)
    (ldlCoordinates S h).2.1.val (ldlCoordinates S h).2.2.val
    (ldlCoordinates S h).2.1.property (ldlCoordinates S h).2.2.property
    (hsize 0) (hsize 1) hlast hsecond
  exact ⟨h,hsize,hb⟩

/-- The same uniform theorem with both strict positivity conditions written explicitly. -/
theorem exists_siegel_reduction (S : Space) :
    ∃ g : IntegralGL,
      (∀ i, |(rootHomeomorph (act (realIntegral g) S)).1 i|≤1/2) ∧
      (0<(rootHomeomorph (act (realIntegral g) S)).2.1.val ∧
        (rootHomeomorph (act (realIntegral g) S)).2.1.val≤2) ∧
      (0<(rootHomeomorph (act (realIntegral g) S)).2.2.val ∧
        (rootHomeomorph (act (realIntegral g) S)).2.2.val≤2) := by
  obtain ⟨g,hg,h1,h2⟩ := exists_reduced_integral_basis S
  exact ⟨g,hg,⟨(rootHomeomorph (act (realIntegral g) S)).2.1.property,h1⟩,
    ⟨(rootHomeomorph (act (realIntegral g) S)).2.2.property,h2⟩⟩

/-- The actual integral orbit meets the positive locus in one fixed compact corner box. -/
theorem exists_orbit_representative_in_compact_box (S : Space) :
    ∃ g : IntegralGL,
      cornerEmbedding (act (realIntegral g) S)∈cornerBox (1/2) 2 ∩ cornerInterior := by
  obtain ⟨g,hg⟩ := exists_reduced_integral_basis S
  exact ⟨g,hg,(cornerHomeomorph (act (realIntegral g) S)).property⟩

/-- A concrete compact subset of the closed flag corner covers all actual interior orbits. -/
theorem compact_corner_representatives :
    ∃ K : Set Corner, IsCompact K ∧ ∀ S : Space, ∃ g : IntegralGL,
      cornerEmbedding (act (realIntegral g) S)∈K ∩ cornerInterior :=
  ⟨cornerBox (1/2) 2,isCompact_cornerBox _ _,exists_orbit_representative_in_compact_box⟩

end TernaryPoly.SymmetricSpaceSiegelReduction
