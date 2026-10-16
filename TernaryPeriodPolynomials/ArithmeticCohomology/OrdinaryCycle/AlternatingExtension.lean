module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.RelativeVertexCohomology
public import TernaryPeriodPolynomials.SymmetricSolution.CycleLifting

@[expose] public section

noncomputable section
namespace TernaryPoly

/-- Every even homogeneous alternating solution is the literal reference value of
an actual equivariant ordinary-cycle functional. -/
theorem alternating_ordinary_extension {n : ℕ} {g : TernaryPolynomial}
    (hn : Even n) (hg : g.IsHomogeneous n) (hrel : PeriodRelations g)
    (hswap : S g= -g) :
    ∃ F : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ k z, F (OrdinaryIncidenceChains.complex.cyclesAction k z)=
        GoodChainComplex.coefficientAction n 0 k (F z)) ∧
      (F (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment)).val=g := by
  let f : PolynomialGLAction.HomogeneousPoly n := ⟨g,hg⟩
  let φ := CycleLifting.alternatingCycleMap f hrel hswap
  obtain ⟨F,hF,hcomp⟩ := RelativeVertexCohomology.homogeneous_extension n hn φ
  refine ⟨F,hF,?_⟩
  have h := LinearMap.congr_fun hcomp GoodUnimodularOrbit.referenceApartment
  change F (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment)=
    (CycleLifting.alternatingCycleMap f hrel hswap).map GoodUnimodularOrbit.referenceApartment at h
  rw [CycleLifting.alternatingCycleMap_reference] at h
  exact congrArg Subtype.val h

end TernaryPoly
