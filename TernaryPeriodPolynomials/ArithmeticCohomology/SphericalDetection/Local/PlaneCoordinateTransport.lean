module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PlaneIntegralSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem planeLevi_map {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S)
    (block : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ) :
    GeneralLinearGroup.map hom (planeLevi block scalar) =
      planeLevi (GeneralLinearGroup.map hom block) (Units.map hom.toMonoidHom scalar) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, GeneralLinearGroup.map_apply]

def localPlanePivotCoordinates_map {K L : Type*} [Field K] [Field L]
    {source : Subring K} {target : Subring L}
    (fieldMap : K →+* L) (integralMap : source →+* target)
    (compatible : ∀ integer : source, fieldMap integer.val = (integralMap integer).val)
    {first second : K} (coordinates : LocalPlanePivotCoordinates source first second) :
    LocalPlanePivotCoordinates target (fieldMap first) (fieldMap second) where
  radicalFirst := fieldMap coordinates.radicalFirst
  radicalSecond := fieldMap coordinates.radicalSecond
  scalar := Units.map fieldMap.toMonoidHom coordinates.scalar
  block := GeneralLinearGroup.map fieldMap coordinates.block
  compact := GeneralLinearGroup.map integralMap coordinates.compact
  factorization := by
    have equality := congrArg (GeneralLinearGroup.map fieldMap) coordinates.factorization
    rw [planeOppositeStandardMatrix_map, map_mul, map_mul, map_mul, map_planeUnipotent,
      planeLevi_map, planeLevi_map, map_one, map_one,
      generalLinearGroup_map_square source.subtype fieldMap integralMap target.subtype compatible] at equality
    exact equality

def localPlanePivotCoordinates_transport {K L : Type*} [Field K] [Field L]
    {source : Subring K} {target : Subring L}
    (fieldEquiv : K ≃+* L) (integralEquiv : source ≃+* target)
    (compatible : ∀ integer : source, fieldEquiv integer.val = (integralEquiv integer).val)
    (first second : L) (coordinates : LocalPlanePivotCoordinates source
      (fieldEquiv.symm first) (fieldEquiv.symm second)) :
    LocalPlanePivotCoordinates target first second :=
  let mapped := localPlanePivotCoordinates_map fieldEquiv.toRingHom integralEquiv.toRingHom compatible coordinates
  { radicalFirst := mapped.radicalFirst
    radicalSecond := mapped.radicalSecond
    scalar := mapped.scalar
    block := mapped.block
    compact := mapped.compact
    factorization := by
      have equality := mapped.factorization
      simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] using equality }

theorem localPlanePivotCoordinates_transport_block {K L : Type*} [Field K] [Field L]
    {source : Subring K} {target : Subring L}
    (fieldEquiv : K ≃+* L) (integralEquiv : source ≃+* target)
    (compatible : ∀ integer : source, fieldEquiv integer.val = (integralEquiv integer).val)
    (first second : L) (coordinates : LocalPlanePivotCoordinates source
      (fieldEquiv.symm first) (fieldEquiv.symm second)) :
    (localPlanePivotCoordinates_transport fieldEquiv integralEquiv compatible first second coordinates).block =
      GeneralLinearGroup.map fieldEquiv.toRingHom coordinates.block := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
