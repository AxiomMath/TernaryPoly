module

public import TernaryPeriodPolynomials.Topology.Euclidean.Convex.LocalCompatibility

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanConvexLocal
open CategoryTheory Limits HomologicalComplex RationalRelativeSingular EuclideanLocalHomology

/-- The actual canonical relative class supported on a nonempty compact convex Euclidean set. -/
def convexGenerator (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    (supportChains K).homology (n+2) :=
  (pointHomologyIso K hK hconv hne.some hne.some_mem (n+2)).inv (localGenerator n hne.some)

/-- The actual class has the specified canonical local value at its construction point. -/
theorem convexGenerator_anchor (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    homologyMap (pointMap K hne.some hne.some_mem) (n+2) (convexGenerator n K hK hconv hne) =
      localGenerator n hne.some := by
  rw [← pointHomologyIso_hom K hK hconv hne.some hne.some_mem (n+2)]
  simp [convexGenerator]

/-- The actual local value at the construction point determines the compact-convex class uniquely. -/
theorem convexGenerator_unique (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (c : (supportChains K).homology (n+2))
    (hc : homologyMap (pointMap K hne.some hne.some_mem) (n+2) c = localGenerator n hne.some) :
    c = convexGenerator n K hK hconv hne := by
  apply (ModuleCat.mono_iff_injective (pointHomologyIso K hK hconv hne.some hne.some_mem (n+2)).hom).mp
    inferInstance
  rw [pointHomologyIso_hom, hc, convexGenerator_anchor]

/-- The compact-convex canonical class is nonzero, including for singleton supports. -/
theorem convexGenerator_ne_zero (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    convexGenerator n K hK hconv hne ≠ 0 := by
  intro h
  have he := convexGenerator_anchor n K hK hconv hne
  rw [h, map_zero] at he
  exact localGenerator_ne_zero n hne.some he.symm

/-- The actual canonical relative class maps to the fixed Euclidean generator at EVERY point
of its compact convex support, including boundary and lower-dimensional points. -/
theorem convexGenerator_at_point (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (x : EuclideanSpace ℝ (Fin (n+2))) (hx : x ∈ K) :
    homologyMap (pointMap K x hx) (n+2) (convexGenerator n K hK hconv hne) = localGenerator n x := by
  apply (ModuleCat.mono_iff_injective (localTopAtIso n x).hom).mp inferInstance
  have h := pointMap_homology_translation K hconv hne.some x hne.some_mem hx (n+1) (by omega)
  have hh := congrArg (fun f => f ≫ (localTopIso n).hom) h
  have hmaps : homologyMap (pointMap K hne.some hne.some_mem) (n+2) ≫ (localTopAtIso n hne.some).hom =
      homologyMap (pointMap K x hx) (n+2) ≫ (localTopAtIso n x).hom := by
    simpa [localTopAtIso, Category.assoc] using hh
  have hv := congrArg (fun f => f (convexGenerator n K hK hconv hne)) hmaps
  change (localTopAtIso n hne.some).hom
      (homologyMap (pointMap K hne.some hne.some_mem) (n+2) (convexGenerator n K hK hconv hne)) =
    (localTopAtIso n x).hom
      (homologyMap (pointMap K x hx) (n+2) (convexGenerator n K hK hconv hne)) at hv
  rw [convexGenerator_anchor] at hv
  simpa [localGenerator] using hv.symm

/-- There is exactly one actual relative class giving the canonical local value at every support point. -/
theorem existsUnique_convexGenerator (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    ∃! c : (supportChains K).homology (n+2),
      ∀ (x : EuclideanSpace ℝ (Fin (n+2))) (hx : x ∈ K),
        homologyMap (pointMap K x hx) (n+2) c = localGenerator n x := by
  refine ⟨convexGenerator n K hK hconv hne, convexGenerator_at_point n K hK hconv hne, ?_⟩
  intro c hc
  exact convexGenerator_unique n K hK hconv hne c (hc hne.some hne.some_mem)

/-- Every compact convex support, empty or nonempty, has vanishing relative homology outside top degree. -/
theorem supportHomology_isZero_of_ne (n k : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hk : k ≠ n+2) :
    IsZero ((supportChains K).homology k) := by
  rcases Set.eq_empty_or_nonempty K with rfl | hne
  · exact emptySupportHomology_isZero k
  · exact supportHomology_isZero n k K hK hconv hne hk

end TernaryPoly.EuclideanConvexLocal
