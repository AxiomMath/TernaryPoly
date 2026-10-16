module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologyPolynomial
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologySubgroups
public import TernaryPeriodPolynomials.GroupCohomology.CentralSignCohomology

@[expose] public section


open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open RelativeStabilizerParameters RadicalFirstCohomologyLattice RadicalTopCohomology
open RadicalFirstCohomology LowDegreeHochschildSerre

/-- The plane central sign acts by minus identity on actual HS radical H¹ in even degree. -/
theorem planeCross_sign (n : ℕ) (hn : Even n)
    (v : groupCohomology (radicalRep planeAction (planePolynomial n)) 1) :
    (cohomologyRep planeAction (planePolynomial n) 1).ρ (-1) v = -v := by
  apply (ModuleCat.mono_iff_injective (planeRadicalIso n 1).hom).mp inferInstance
  rw [map_neg,planeRadicalIso_action]
  change planeSubgroupH1Action n (-1) ((planeRadicalIso n 1).hom v) = _
  rw [planeSubgroupH1_sign n hn]
  rfl

/-- The independent line sign acts by minus identity on actual HS radical H¹. -/
theorem lineCross_sign (n : ℕ)
    (v : groupCohomology (radicalRep lineAction (linePolynomial n)) 1) :
    (cohomologyRep lineAction (linePolynomial n) 1).ρ (-1,1) v = -v := by
  apply (ModuleCat.mono_iff_injective (lineRadicalIso n 1).hom).mp inferInstance
  rw [map_neg,← lineDiagonal_sign,lineRadicalIso_action]
  change lineSubgroupH1Action n (-1,1) ((lineRadicalIso n 1).hom v) = _
  rw [lineSubgroupH1_sign]
  rfl

theorem planeCross_H1_zero (n : ℕ) (hn : Even n) :
    IsZero (groupCohomology (cohomologyRep planeAction (planePolynomial n) 1) 1) :=
  CentralSignCohomology.isZero_groupCohomology _ (-1) (fun M => by simp)
    (planeCross_sign n hn) 1

theorem lineCross_H1_zero (n : ℕ) :
    IsZero (groupCohomology (cohomologyRep lineAction (linePolynomial n) 1) 1) :=
  CentralSignCohomology.isZero_groupCohomology _ (-1,1) (fun q => by
    apply Prod.ext
    · exact mul_comm _ _
    · simp)
    (lineCross_sign n) 1

end TernaryPoly.RelativeVertexCohomology
