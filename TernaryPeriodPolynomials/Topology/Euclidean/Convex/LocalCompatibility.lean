module

public import TernaryPeriodPolynomials.Topology.Euclidean.Convex.LocalHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanConvexLocal
open CategoryTheory Limits HomologicalComplex RationalRelativeSingular EuclideanLocalHomology
open EuclideanBallLocal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Translation by a point of the support sends the whole complement into the punctured space. -/
theorem complement_translation_punctured (K : Set E) (x : E) (hx : x ∈ K) :
    Set.MapsTo (Homeomorph.subRight x).toHomotopyEquiv.toFun Kᶜ ({0}ᶜ : Set E) := by
  intro z hz
  change z-x ≠ 0
  exact sub_ne_zero.mpr (complement_avoids K x hx hz)

/-- The actual point map followed by canonical translation is the literal translated pair map. -/
theorem pointMap_translation (K : Set E) (x : E) (hx : x ∈ K) :
    pointMap K x hx ≫ (translateLocalIso d x).hom =
      relativeMap (Homeomorph.subRight x).toHomotopyEquiv.toFun Kᶜ {0}ᶜ
        (complement_translation_punctured K x hx) := by
  rw [pointMap, translateLocalIso, relativeHomeomorphIso_hom]
  erw [RationalRelativeExcision.relativeMap_comp]
  rfl

/-- Convexity keeps the entire centering homotopy punctured on the complement, including
when its endpoint centers are boundary points of a lower-dimensional support. -/
theorem centeringHomotopy_punctured (K : Set E) (hK : Convex ℝ K) (x y : E)
    (hx : x ∈ K) (hy : y ∈ K) :
    ∀ t z, z ∈ Kᶜ → centeringHomotopy x y (t,z) ∈ ({0}ᶜ : Set E) := by
  intro t z hz
  change z-x-(t : ℝ) • (y-x) ≠ 0
  intro he
  have he' := sub_eq_zero.mp he
  have hm := hK hx hy (sub_nonneg.mpr t.property.2) t.property.1
    (sub_add_cancel (1:ℝ) (t:ℝ))
  have hez : z = (1-(t:ℝ)) • x + (t:ℝ) • y := by
    calc
      z = (z-x)+x := by abel
      _ = (t:ℝ) • (y-x)+x := congrArg (fun a => a+x) he'
      _ = (1-(t:ℝ)) • x + (t:ℝ) • y := by module
  rw [← hez] at hm
  exact hz hm

/-- The actual point restrictions at any two points of a convex support agree after the
canonical translations, by the explicit segment homotopy on the full complement. -/
theorem pointMap_homology_translation (K : Set E) (hK : Convex ℝ K) (x y : E)
    (hx : x ∈ K) (hy : y ∈ K) (k : ℕ) (hk : k ≠ 0) :
    homologyMap (pointMap K x hx) (k+1) ≫ (translateLocalHomologyIso d x (k+1)).hom =
      homologyMap (pointMap K y hy) (k+1) ≫ (translateLocalHomologyIso d y (k+1)).hom := by
  change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
  rw [← homologyMap_comp, ← homologyMap_comp, pointMap_translation, pointMap_translation]
  exact relativeHomologyMap_eq_of_homotopy _ _ Kᶜ {0}ᶜ
    (complement_translation_punctured K x hx) (complement_translation_punctured K y hy)
    (centeringHomotopy x y) (centeringHomotopy_punctured K hK x y hx hy) k hk

end TernaryPoly.EuclideanConvexLocal
