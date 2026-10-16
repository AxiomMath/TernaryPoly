module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactClasses
public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationHomeomorph

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCapHomeomorph
open CategoryTheory HomologicalComplex
open RationalLocalOrientation RationalManifoldCompact

variable {X Y HX HY : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y] [TopologicalSpace HX] [TopologicalSpace HY]
  [ChartedSpace HX X] [ChartedSpace HY Y]
  (h : X ≃ₜ Y) (n : ℕ)
  (eX : HX ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (eY : HY ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
  (oX : Orientation (n+2) X) (oY : Orientation (n+2) Y)

/-- Compatibility is stated using the actual point-pair homology map. -/
def OrientationCompatible : Prop :=
  ∀ x : X, (pointHomologyIso h x (n+2)).hom (oX.generator x) = oY.generator (h x)

omit [T2Space X] [T2Space Y] in
/-- The genuine pullback orientation has exactly the required actual local generators. -/
theorem pullbackOrientation_compatible :
    OrientationCompatible h n (Orientation.pullback h (n+2) oY) oY := by
  intro x
  simp [Orientation.pullback,pullbackGenerator]

/-- Actual homeomorphism transport takes compact fundamental classes to the supplied
compatible compact fundamental classes, with no rank-based identification. -/
theorem compactFundamentalClass_transport
    (ho : OrientationCompatible h n oX oY) (K : Set Y) (hK : IsCompact K) :
    homologyMap (supportPullbackIso h K).hom (n+2)
      (compactFundamentalClass n eX oX (h ⁻¹' K) (h.isCompact_preimage.mpr hK)) =
      compactFundamentalClass n eY oY K hK := by
  let I := (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) (n+2)).mapIso
    (supportPullbackIso h K)
  have hi : I.inv (compactFundamentalClass n eY oY K hK) =
      compactFundamentalClass n eX oX (h ⁻¹' K) (h.isCompact_preimage.mpr hK) := by
    apply compactFundamentalClass_unique n eX oX (h ⁻¹' K) (h.isCompact_preimage.mpr hK)
    intro x hx
    apply (ModuleCat.mono_iff_injective (pointHomologyIso h x (n+2)).hom).mp inferInstance
    have hm := congrArg (fun f => homologyMap f (n+2)) (supportPullbackIso_point h K x hx)
    rw [homologyMap_comp,homologyMap_comp] at hm
    have hv := congrArg (fun f => f (I.inv (compactFundamentalClass n eY oY K hK))) hm
    change homologyMap (supportPointMap K (h x) hx) (n+2)
        (I.hom (I.inv (compactFundamentalClass n eY oY K hK))) =
      (pointHomologyIso h x (n+2)).hom
        (homologyMap (supportPointMap (h ⁻¹' K) x hx) (n+2)
          (I.inv (compactFundamentalClass n eY oY K hK))) at hv
    have hc : I.hom (I.inv (compactFundamentalClass n eY oY K hK)) =
        compactFundamentalClass n eY oY K hK := by
      change (I.inv ≫ I.hom) _ = _
      rw [I.inv_hom_id]
      rfl
    rw [hc,compactFundamentalClass_at_point] at hv
    exact hv.symm.trans (ho x).symm
  change I.hom _ = _
  rw [← hi]
  change (I.inv ≫ I.hom) _ = _
  rw [I.inv_hom_id]
  rfl

end TernaryPoly.SingularLocalCapHomeomorph
