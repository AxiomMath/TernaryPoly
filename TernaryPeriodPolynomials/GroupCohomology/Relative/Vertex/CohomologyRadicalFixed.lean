module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologyPolynomial

@[expose] public section


open CategoryTheory
noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open RadicalFirstCohomologyLattice RadicalTopCohomology LowDegreeHochschildSerre

theorem planeRadical_fixed_zero (n : ℕ)
    (v : groupCohomology (radicalRep planeAction (planePolynomial n)) 2)
    (hv : ∀ q, (cohomologyRep planeAction (planePolynomial n) 2).ρ q v = v) : v = 0 := by
  apply (ModuleCat.mono_iff_injective (planeRadicalIso n 2).hom).mp inferInstance
  rw [map_zero]
  apply planeSubgroupH2_fixed_zero
  intro M
  change groupCohomology.map _ _ 2 ((planeRadicalIso n 2).hom v) = _
  rw [← planeRadicalIso_action,hv]

theorem lineRadical_fixed_zero (n : ℕ)
    (v : groupCohomology (radicalRep lineAction (linePolynomial n)) 2)
    (hv : ∀ q, (cohomologyRep lineAction (linePolynomial n) 2).ρ q v = v) : v = 0 := by
  apply (ModuleCat.mono_iff_injective (lineRadicalIso n 2).hom).mp inferInstance
  rw [map_zero]
  apply lineSubgroupH2_fixed_zero
  intro ε
  change groupCohomology.map _ _ 2 ((lineRadicalIso n 2).hom v) = _
  rw [← lineRadicalIso_action,hv]

end TernaryPoly.RelativeVertexCohomology
