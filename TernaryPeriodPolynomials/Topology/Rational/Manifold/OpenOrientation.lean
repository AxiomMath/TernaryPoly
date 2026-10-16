module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactOpen

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalLocalOrientation RationalLocalChartHomology RationalRelativeExcision

variable {X H : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace H] [ChartedSpace H X]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) X) (D : Opens X)

/-- The actual point orientation induced on an open subspace by inverse point excision. -/
def openOrientationGenerator (x : D) : (RationalLocalChartHomology.localChains x).homology (n+2) :=
  (pointLocalHomologyIso x.val D x.property (n+2)).inv (o.generator x.val)

/-- The induced open point generator maps to the given ambient orientation generator. -/
theorem openOrientationGenerator_map (x : D) :
    homologyMap (pointExcisionMap x.val (D : Set X) x.property) (n+2)
      (openOrientationGenerator n o D x) = o.generator x.val := by
  exact (pointLocalHomologyIso x.val D x.property (n+2)).inv_hom_id_apply (o.generator x.val)

include e in
/-- The induced generators on the open subspace are represented by genuine support classes. -/
theorem openOrientationGenerator_locallyRepresented :
    LocallyRepresented (n+2) (openOrientationGenerator n o D) := by
  let : LocallyCompactSpace H := e.isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace H X
  intro x
  obtain ⟨K,hK,hx,hKD⟩ := exists_compact_subset D.isOpen x.property
  let I := RationalLocalOrientation.supportExcisionIso K hK.isClosed D hKD (n+2)
  let c := I.inv (compactFundamentalClass n e o K hK)
  refine ⟨⟨Subtype.val ⁻¹' interior K,isOpen_interior.preimage continuous_subtype_val⟩,
    Subtype.val ⁻¹' K,hx,(fun y hy => show y.val ∈ K from interior_subset (show y.val ∈ interior K from hy)),c,?_⟩
  intro y _hy hyK
  apply (ModuleCat.mono_iff_injective (pointLocalHomologyIso y.val D y.property (n+2)).hom).mp inferInstance
  change homologyMap (pointExcisionMap y.val (D : Set X) y.property) (n+2)
    (homologyMap (supportPointMap (Subtype.val ⁻¹' K) y hyK) (n+2) c) = _
  rw [pointLocalHomologyIso_hom,openOrientationGenerator_map]
  have h := congrArg (fun f => homologyMap f (n+2))
    (supportExcisionMap_point K (D : Set X) y.val hyK y.property)
  rw [homologyMap_comp,homologyMap_comp] at h
  change (homologyMap (supportPointMap (Subtype.val ⁻¹' K) y hyK) (n+2) ≫
    homologyMap (pointExcisionMap y.val (D : Set X) y.property) (n+2)) c = _
  erw [← h]
  change homologyMap (supportPointMap K y.val hyK) (n+2) (I.hom (I.inv _)) = _
  rw [Iso.inv_hom_id_apply,compactFundamentalClass_at_point]

/-- Every genuine homological orientation restricts to an actual homological orientation on
an open submanifold, with local support representatives provided by compact fundamental classes. -/
def openOrientation : Orientation (n+2) D where
  generator := openOrientationGenerator n o D
  nonzero x := by
    intro hx
    have h := openOrientationGenerator_map n o D x
    rw [hx,map_zero] at h
    exact o.nonzero x.val h.symm
  locallyRepresented := openOrientationGenerator_locallyRepresented n e o D

/-- The canonical orientation of an open submanifold agrees with its ambient orientation. -/
theorem openOrientation_compatible [ChartedSpace H D] :
    OpenOrientationCompatible n o D (openOrientation n e o D) :=
  openOrientationGenerator_map n o D

end TernaryPoly.RationalManifoldCompact
