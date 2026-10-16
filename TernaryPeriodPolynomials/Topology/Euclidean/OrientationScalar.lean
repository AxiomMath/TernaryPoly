module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapOrientation

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanOrientationScalar
open CategoryTheory HomologicalComplex
open RationalLocalOrientation RationalManifoldCompact
open EuclideanLocalHomology EuclideanCompactClasses EuclideanCompactCap

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- Every actual top class on a nonempty compact-convex Euclidean support is a scalar multiple
of the fixed compact fundamental generator. -/
theorem compact_class_smul (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (c : (supportChains K).homology (n+2)) : ∃ q : ℚ, c = q • compactGenerator n K hK := by
  let e := convexHomologyCoordinate n K hK hconv hne
  refine ⟨e c,?_⟩
  rw [← convexHomologyCoordinate_generator n K hK hconv hne]
  change c = e c • e.symm 1
  rw [← map_smul,smul_eq_mul,mul_one,LinearEquiv.symm_apply_apply]

/-- The scalar of an actual Euclidean homological orientation in the fixed origin coordinate. -/
def orientationScalar (o : Orientation (n+2) E) : ℚ := (localTopAtIso n 0).hom (o.generator 0)

/-- The scalar of a genuine orientation is nonzero. -/
theorem orientationScalar_ne_zero (o : Orientation (n+2) E) : orientationScalar n o ≠ 0 := by
  intro h
  apply o.nonzero 0
  apply (ModuleCat.mono_iff_injective (localTopAtIso n 0).hom).mp inferInstance
  exact h.trans (map_zero (localTopAtIso n 0).hom.hom).symm

/-- Every genuine Euclidean orientation is one globally fixed nonzero rational multiple of
the canonical local generators. Compact-convex fundamental classes compare any two points. -/
theorem orientation_generator (o : Orientation (n+2) E) (x : E) :
    o.generator x = orientationScalar n o • localGenerator n x := by
  let K : Set E := Metric.closedBall 0 (‖x‖+1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hconv : Convex ℝ K := convex_closedBall _ _
  have h0 : (0:E) ∈ K := by
    change dist (0:E) 0 ≤ ‖x‖+1
    simp only [dist_self]
    positivity
  have hx : x ∈ K := by
    change dist x 0 ≤ ‖x‖+1
    rw [dist_zero_right]
    linarith
  obtain ⟨q,hq⟩ := compact_class_smul n K hK hconv ⟨0,h0⟩
    (compactFundamentalClass n (Homeomorph.refl E) o K hK)
  have point (y : E) (hy : y ∈ K) : o.generator y = q • localGenerator n y := by
    have h := compactFundamentalClass_at_point n (Homeomorph.refl E) o K hK y hy
    rw [hq,map_smul] at h
    have hg : homologyMap (supportPointMap K y hy) (n+2) (compactGenerator n K hK) = localGenerator n y :=
      compactGenerator_at_point n K hK y hy
    rw [hg] at h
    exact h.symm
  have hq0 : orientationScalar n o = q := by
    unfold orientationScalar
    rw [point 0 h0,map_smul]
    simp [localGenerator]
  rw [point x hx,hq0]

end TernaryPoly.EuclideanOrientationScalar
