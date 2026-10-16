module

public import TernaryPeriodPolynomials.Topology.Euclidean.Local.Orientation

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanLocalHomology
open HomologicalComplex RationalRelativeSingular

/-- The isotopy generator theorem with an explicitly specified image point and literal pair map. -/
theorem pairMap_generator (n : ℕ)
    (f : C(EuclideanSpace ℝ (Fin (n+2)),EuclideanSpace ℝ (Fin (n+2))))
    (hf : Function.Injective f) (H : ContinuousMap.Homotopy (ContinuousMap.id _) f)
    (hH : ∀ t, Function.Injective (fun z => H (t,z)))
    (x y : EuclideanSpace ℝ (Fin (n+2))) (hy : f x = y)
    (hmap : Set.MapsTo f ({x}ᶜ : Set _) ({y}ᶜ : Set _)) :
    homologyMap (relativeMap f {x}ᶜ {y}ᶜ hmap) (n+2) (localGenerator n x) =
      localGenerator n y := by
  subst y
  exact pointLocalMap_generator n f hf H hH x

end TernaryPoly.EuclideanLocalHomology
