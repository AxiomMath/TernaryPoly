module

public import TernaryPeriodPolynomials.SymmetricSpace.Covering

@[expose] public section


noncomputable section
open Topology Set
namespace TernaryPoly.SymmetricSpaceCovering
open SymmetricSpacePositive SymmetricSpaceCharts

abbrev OrbitFiber (S : Space) := quotientProjection ⁻¹' {quotientProjection S}

instance orbitFiberNonempty (S : Space) : Nonempty (OrbitFiber S) := ⟨⟨S,rfl⟩⟩

instance orbitFiberDiscrete (S : Space) : DiscreteTopology (OrbitFiber S) :=
  (quotientProjection_covering (quotientProjection S)).1

/-- An actual covering trivialization over a neighborhood of the orbit of S. -/
def coveringTrivialization (S : Space) : Bundle.Trivialization (OrbitFiber S) quotientProjection :=
  (quotientProjection_covering (quotientProjection S)).toTrivialization

theorem self_mem_coveringTrivialization (S : Space) :
    quotientProjection S∈(coveringTrivialization S).baseSet :=
  (quotientProjection_covering (quotientProjection S)).mem_toTrivialization_baseSet

/-- The local inverse of the projection, restricted inside a genuine evenly covered neighborhood. -/
def localLift (S : Space) : OpenPartialHomeomorph OrbitSpace Space :=
  (quotientProjection_covering.isLocalHomeomorph.localInverseAt S).restr
    (coveringTrivialization S).baseSet

@[simp] theorem localLift_source (S : Space) :
    (localLift S).source=
      (quotientProjection_covering.isLocalHomeomorph.localInverseAt S).source ∩
        (coveringTrivialization S).baseSet := by
  simp only [localLift,OpenPartialHomeomorph.restr_source,
    (coveringTrivialization S).open_baseSet.interior_eq]

@[simp] theorem localLift_self (S : Space) : localLift S (quotientProjection S)=S :=
  quotientProjection_covering.isLocalHomeomorph.localInverseAt_apply_self

theorem self_mem_localLift (S : Space) : quotientProjection S∈(localLift S).source := by
  rw [localLift_source]
  exact ⟨quotientProjection_covering.isLocalHomeomorph.apply_self_mem_localInverseAt_source,
    self_mem_coveringTrivialization S⟩

/-- The actual quotient chart is the local orbit lift followed by the five explicit coordinates. -/
def quotientChart (S : Space) : OpenPartialHomeomorph OrbitSpace Coordinates :=
  (localLift S).trans coordinateChart

@[simp] theorem quotientChart_source (S : Space) : (quotientChart S).source=(localLift S).source := by
  simp only [quotientChart,OpenPartialHomeomorph.trans_source,coordinateChart_source,
    Set.preimage_univ,Set.inter_univ]

@[simp] theorem quotientChart_apply (S : Space) (x : OrbitSpace) :
    quotientChart S x=extract (localLift S x).val := rfl

@[simp] theorem quotientChart_self (S : Space) : quotientChart S (quotientProjection S)=extract S.val := by
  rw [quotientChart_apply,localLift_self]

theorem self_mem_quotientChart (S : Space) : quotientProjection S∈(quotientChart S).source := by
  rw [quotientChart_source]
  exact self_mem_localLift S

/-- Every chart target is an actual open subset of the explicit positivity domain in R^5. -/
theorem quotientChart_target_subset (S : Space) : (quotientChart S).target⊆positiveCoordinates := by
  rw [quotientChart,OpenPartialHomeomorph.trans_target,coordinateChart_target]
  exact Set.inter_subset_left

/-- The inverse quotient chart projects the exact reconstructed trace-one positive matrix. -/
theorem quotientChart_inverse (S : Space) (x : Coordinates) (hx : x∈(quotientChart S).target) :
    (quotientChart S).symm x=
      quotientProjection ⟨reconstruct x,reconstruct_mem x (quotientChart_target_subset S hx)⟩ := by
  change (quotientProjection_covering.isLocalHomeomorph.localInverseAt S).symm
    (coordinateChart.symm x)=_
  rw [quotientProjection_covering.isLocalHomeomorph.localInverseAt_symm]
  congr 1
  exact Subtype.ext (coordinateChart_inverse x (quotientChart_target_subset S hx))

/-- A trivialization over precisely the quotient-chart source certifies that this chart
is transported through an evenly covered neighborhood. -/
def chartTrivialization (S : Space) : Bundle.Trivialization (OrbitFiber S) quotientProjection :=
  (coveringTrivialization S).restrOpen (quotientChart S).source (quotientChart S).open_source

theorem chartTrivialization_baseSet (S : Space) :
    (chartTrivialization S).baseSet=(quotientChart S).source := by
  change (coveringTrivialization S).baseSet ∩ (quotientChart S).source=(quotientChart S).source
  apply Set.inter_eq_right.mpr
  rw [quotientChart_source,localLift_source]
  exact Set.inter_subset_right

/-- The actual open five-coordinate charts cover every point of the actual arithmetic quotient. -/
theorem quotientCharts_cover (x : OrbitSpace) : ∃ S : Space,x∈(quotientChart S).source := by
  obtain ⟨S,rfl⟩ := quotientProjection_surjective x
  exact ⟨S,self_mem_quotientChart S⟩

end TernaryPoly.SymmetricSpaceCovering
