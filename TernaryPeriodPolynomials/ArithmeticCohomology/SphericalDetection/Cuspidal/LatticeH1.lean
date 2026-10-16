module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.LatticeCocycles
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.H1Levi

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def oneCocycleBoundaryMap {G : Type} [Group G] (representation : Rep ℂ G) :
    representation →ₗ[ℂ] groupCohomology.cocycles₁ representation :=
  (groupCohomology.d₀₁ representation).hom.codRestrict _ groupCohomology.d₀₁_apply_mem_cocycles₁

theorem oneCocycleBoundaryMap_range {G : Type} [Group G] (representation : Rep ℂ G) :
    (oneCocycleBoundaryMap representation).range = (groupCohomology.H1π representation).hom.ker := by
  ext cycle
  rw [LinearMap.mem_ker, groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨potential, rfl⟩
    exact ⟨potential, rfl⟩
  · rintro ⟨potential, equality⟩
    exact ⟨potential, Subtype.ext equality⟩

def cuspidalLatticeH1Cycle (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice) :
    groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation) →ₗ[ℂ]
      cuspidalTensorValues cusp (groupCohomology.H1 representation) :=
  (cuspidalTensorMap cusp (groupCohomology.H1π representation).hom).comp
    (cuspidalLatticeCocycleFamily cusp representation)

theorem cuspidalLatticeH1Cycle_apply (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation)) (argument : BinaryAdelicGL) :
    (cuspidalLatticeH1Cycle cusp representation cycle).val argument =
      groupCohomology.H1π representation (cuspidalTensorCocycleEvaluation cusp representation argument cycle) := by
  change groupCohomology.H1π representation ((cuspidalLatticeCocycleFamily cusp representation cycle).val argument) = _
  rw [cuspidalLatticeCocycleFamily_apply]

theorem cuspidalLatticeH1Cycle_surjective (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice) :
    Function.Surjective (cuspidalLatticeH1Cycle cusp representation) :=
  (cuspidalTensorMap_surjective cusp (groupCohomology.H1π representation).hom (oneCocycle_H1_surjective representation)).comp
    (cuspidalLatticeCocycleEquiv cusp representation).surjective

theorem cuspidalLatticeH1Cycle_zero_iff (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation)) :
    cuspidalLatticeH1Cycle cusp representation cycle = 0 ↔
      groupCohomology.H1π (cuspidalTensorPointwiseRep cusp representation) cycle = 0 := by
  constructor
  · intro zero
    have member : cuspidalLatticeCocycleFamily cusp representation cycle ∈
        (cuspidalTensorMap cusp (oneCocycleBoundaryMap representation)).range := by
      rw [cuspidalTensorMap_mem_range, oneCocycleBoundaryMap_range]
      intro argument
      exact congrArg (fun values : cuspidalTensorValues cusp (groupCohomology.H1 representation) => values.val argument) zero
    obtain ⟨potential, boundary⟩ := member
    rw [groupCohomology.H1π_eq_zero_iff]
    refine ⟨potential, ?_⟩
    funext element
    apply Subtype.ext
    funext argument
    have equality := congrArg (fun values : cuspidalTensorValues cusp (groupCohomology.cocycles₁ representation) =>
      values.val argument element) boundary
    rw [cuspidalLatticeCocycleFamily_apply, cuspidalTensorCocycleEvaluation_apply] at equality
    exact equality
  · intro zero
    rw [groupCohomology.H1π_eq_zero_iff] at zero
    obtain ⟨potential, boundary⟩ := zero
    apply Subtype.ext
    funext argument
    rw [cuspidalLatticeH1Cycle_apply]
    change groupCohomology.H1π representation (cuspidalTensorCocycleEvaluation cusp representation argument cycle) = 0
    rw [groupCohomology.H1π_eq_zero_iff]
    refine ⟨potential.val argument, ?_⟩
    funext element
    exact congrArg (fun values : cuspidalTensorPointwiseRep cusp representation => values.val argument)
      (congrFun boundary element)

def cuspidalLatticeH1Equiv (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice) :
    groupCohomology.H1 (cuspidalTensorPointwiseRep cusp representation) ≃ₗ[ℂ]
      cuspidalTensorValues cusp (groupCohomology.H1 representation) :=
  surjectiveLinearCoordinateEquiv (groupCohomology.H1π (cuspidalTensorPointwiseRep cusp representation)).hom
    (oneCocycle_H1_surjective _) (cuspidalLatticeH1Cycle cusp representation)
    (cuspidalLatticeH1Cycle_surjective cusp representation) (by
      intro first second
      simpa only [map_sub, sub_eq_zero] using
        (cuspidalLatticeH1Cycle_zero_iff cusp representation (first - second)).symm)

theorem cuspidalLatticeH1Equiv_apply (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation)) :
    cuspidalLatticeH1Equiv cusp representation
        (groupCohomology.H1π (cuspidalTensorPointwiseRep cusp representation) cycle) =
      cuspidalLatticeH1Cycle cusp representation cycle :=
  surjectiveLinearCoordinateEquiv_apply _ _ _ _ _ cycle

def cuspidalTensorLinearEquiv (cusp : CuspidalRepresentation) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (equivalence : V ≃ₗ[ℂ] W) :
    cuspidalTensorValues cusp V ≃ₗ[ℂ] cuspidalTensorValues cusp W :=
  LinearEquiv.ofBijective (cuspidalTensorMap cusp equivalence.toLinearMap)
    ⟨cuspidalTensorMap_injective cusp equivalence.toLinearMap equivalence.injective,
      cuspidalTensorMap_surjective cusp equivalence.toLinearMap equivalence.surjective⟩

def upperRadicalCuspidalH1 (degree : ℕ) (cusp : CuspidalRepresentation) :
    groupCohomology.H1 (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)) ≃ₗ[ℂ]
      cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)) :=
  (cuspidalLatticeH1Equiv cusp (upperRadicalLatticeRep degree)).trans
    (cuspidalTensorLinearEquiv cusp (upperRadicalH1Coordinate degree))

theorem upperRadicalCuspidalH1_apply (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)))
    (argument : BinaryAdelicGL) :
    (upperRadicalCuspidalH1 degree cusp
        (groupCohomology.H1π (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)) cycle)).val argument =
      upperRadicalCocycleCoordinate degree (cuspidalTensorCocycleEvaluation cusp (upperRadicalLatticeRep degree) argument cycle) := by
  change upperRadicalH1Coordinate degree
    ((cuspidalLatticeH1Equiv cusp (upperRadicalLatticeRep degree)
      (groupCohomology.H1π (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)) cycle)).val argument) = _
  rw [cuspidalLatticeH1Equiv_apply, cuspidalLatticeH1Cycle_apply, upperRadicalH1Coordinate_apply]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
