module

public import TernaryPeriodPolynomials.Topology.Euclidean.Convex.LocalRadial

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanConvexLocal
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology RationalRelativeSingular
open RationalSingularAugmentation EuclideanLocalHomology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual relative chain complex supported on a subset of Euclidean space. -/
abbrev supportChains (K : Set E) := relativeChains Kᶜ

/-- The actual restriction to local homology at a point of the support. -/
def pointMap (K : Set E) (x : E) (hx : x ∈ K) : supportChains K ⟶ localChainsAt d x :=
  relativeMap (ContinuousMap.id E) Kᶜ {x}ᶜ (complement_avoids K x hx)

/-- The exact relative chain projection equation for the actual point map. -/
theorem pointMap_projection (K : Set E) (x : E) (hx : x ∈ K) :
    cokernel.π (inclusion Kᶜ) ≫ pointMap K x hx = cokernel.π (inclusion ({x}ᶜ : Set E)) := by
  simp [pointMap, relativeMap, cokernel.map, chainMap]

/-- The literal complement inclusion induces an actual singular-chain quasi-isomorphism. -/
theorem complementInclusion_quasiIso (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (x : E) (hx : x ∈ K) : QuasiIso (chainMap (complementInclusion K x hx)) := by
  rw [← complementHomotopyEquiv_toFun K hK hconv x hx]
  change QuasiIso (chainHomotopyEquiv (complementHomotopyEquiv K hK hconv x hx)).hom
  infer_instance

/-- The actual point restriction for a compact convex support is a quasi-isomorphism in every degree. -/
theorem pointMap_quasiIso (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (x : E) (hx : x ∈ K) : QuasiIso (pointMap K x hx) := by
  have hsource : QuasiIso (chainMap (subspaceMap (ContinuousMap.id E) Kᶜ {x}ᶜ
      (complement_avoids K x hx))) := complementInclusion_quasiIso K hK hconv x hx
  have htarget : QuasiIso (chainMap (ContinuousMap.id E)) := by
    change QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (𝟙 (TopCat.of E)))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  exact @RelativeExcisionAlgebra.cokernel_map_quasiIso _ _ _ _
    (inclusion Kᶜ) (inclusion ({x}ᶜ : Set E)) inferInstance inferInstance
    (chainMap (subspaceMap (ContinuousMap.id E) Kᶜ {x}ᶜ (complement_avoids K x hx)))
    (chainMap (ContinuousMap.id E))
    (inclusion_naturality (ContinuousMap.id E) Kᶜ {x}ᶜ (complement_avoids K x hx)) hsource htarget

/-- Every point of a compact convex support gives the genuine local homology isomorphism. -/
def pointHomologyIso (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (x : E) (hx : x ∈ K) (k : ℕ) : (supportChains K).homology k ≅ (localChainsAt d x).homology k := by
  have := pointMap_quasiIso K hK hconv x hx
  exact asIso (homologyMap (pointMap K x hx) k)

/-- The comparison isomorphism is induced by the actual point restriction. -/
theorem pointHomologyIso_hom (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (x : E) (hx : x ∈ K) (k : ℕ) : (pointHomologyIso K hK hconv x hx k).hom =
      homologyMap (pointMap K x hx) k := rfl

/-- A nonempty compact convex support has no actual relative homology away from top degree. -/
theorem supportHomology_isZero (n k : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) (hk : k ≠ n+2) :
    IsZero ((supportChains K).homology k) :=
  (localAt_isZero_of_ne n k hne.some hk).of_iso
    (pointHomologyIso K hK hconv hne.some hne.some_mem k)

/-- Empty support gives an actual zero relative chain complex. -/
theorem emptySupport_isZero : IsZero (supportChains (∅ : Set E)) := by
  have : IsIso (inclusion (Set.univ : Set E)) :=
    (show IsIso (chainHomeomorphIso (Homeomorph.Set.univ E)).hom from inferInstance)
  change IsZero (cokernel (inclusion ((∅ : Set E)ᶜ)))
  rw [Set.compl_empty]
  exact isZero_cokernel_of_epi (inclusion (Set.univ : Set E))

/-- Every homology group with empty support vanishes. -/
theorem emptySupportHomology_isZero (k : ℕ) : IsZero ((supportChains (∅ : Set E)).homology k) :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) k).map_isZero emptySupport_isZero

end TernaryPoly.EuclideanConvexLocal
