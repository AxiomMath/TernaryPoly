module

public import TernaryPeriodPolynomials.Topology.Euclidean.Convex.LocalClasses

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanConvexLocal
open CategoryTheory Limits HomologicalComplex RationalRelativeSingular

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The literal relative pair map restricts a supported class from K to a subset L. -/
def supportRestriction (K L : Set E) (h : L ⊆ K) : supportChains K ⟶ supportChains L :=
  relativeMap (ContinuousMap.id E) Kᶜ Lᶜ (fun _ hz hl => hz (h hl))

/-- The actual support restriction retains the precise chain projection square. -/
theorem supportRestriction_projection (K L : Set E) (h : L ⊆ K) :
    cokernel.π (inclusion Kᶜ) ≫ supportRestriction K L h = cokernel.π (inclusion Lᶜ) := by
  simp [supportRestriction, relativeMap, cokernel.map, RationalSingularAugmentation.chainMap]

/-- Actual supported restriction followed by a local value equals the direct point restriction. -/
theorem supportRestriction_pointMap (K L : Set E) (h : L ⊆ K) (x : E) (hx : x ∈ L) :
    supportRestriction K L h ≫ pointMap L x hx = pointMap K x (h hx) := by
  rw [supportRestriction, pointMap, pointMap]
  erw [RationalRelativeExcision.relativeMap_comp]
  rfl

/-- The actual restrictions between nonempty compact convex supports preserve canonical classes. -/
theorem supportRestriction_generator (n : ℕ) (K L : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hL : IsCompact L) (hconvK : Convex ℝ K) (hconvL : Convex ℝ L)
    (hne : L.Nonempty) (h : L ⊆ K) :
    homologyMap (supportRestriction K L h) (n+2) (convexGenerator n K hK hconvK (hne.mono h)) =
      convexGenerator n L hL hconvL hne := by
  apply convexGenerator_unique n L hL hconvL hne
  change (homologyMap (supportRestriction K L h) (n+2) ≫
    homologyMap (pointMap L hne.some hne.some_mem) (n+2)) _ = _
  rw [← homologyMap_comp, supportRestriction_pointMap]
  exact convexGenerator_at_point n K hK hconvK (hne.mono h) hne.some (h hne.some_mem)

/-- Actual support restrictions compose under nested set inclusions. -/
theorem supportRestriction_comp (K L M : Set E) (hLK : L ⊆ K) (hML : M ⊆ L) :
    supportRestriction K L hLK ≫ supportRestriction L M hML =
      supportRestriction K M (hML.trans hLK) := by
  rw [supportRestriction, supportRestriction, supportRestriction]
  erw [RationalRelativeExcision.relativeMap_comp]
  rfl

end TernaryPoly.EuclideanConvexLocal
