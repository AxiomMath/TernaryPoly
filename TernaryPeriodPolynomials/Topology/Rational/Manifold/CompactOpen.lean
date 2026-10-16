module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactClasses
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionSupport

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalLocalOrientation RationalLocalChartHomology RationalRelativeExcision

variable {X H : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace H] [ChartedSpace H X]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) X)
  (D : Opens X) [ChartedSpace H D] (oD : Orientation (n+2) D)

/-- Compatibility of genuine local orientations means that the actual point-excision map
carries each generator in the open subspace to the corresponding ambient generator. -/
def OpenOrientationCompatible : Prop :=
  ∀ x : D, homologyMap (pointExcisionMap x.val (D : Set X) x.property) (n+2) (oD.generator x) = o.generator x.val

/-- Actual excision carries the compact-subset fundamental class in an oriented open subspace
to the ambient compact-subset fundamental class, provided their point orientations agree. -/
theorem compactFundamentalClass_open (hcompat : OpenOrientationCompatible n o D oD)
    (K : Compacts X) (hKD : (K : Set X) ⊆ D) :
    homologyMap (supportExcisionMap (K : Set X) (D : Set X)) (n+2)
      (compactFundamentalClass n e oD (Subtype.val ⁻¹' (K : Set X))
        (SingularLocalSupport.compactWithinOpen (B := TopCat.of X) D K hKD).isCompact) =
      compactFundamentalClass n e o (K : Set X) K.isCompact := by
  apply compactFundamentalClass_unique
  intro x hx
  have h := congrArg (fun f => homologyMap f (n+2))
    (supportExcisionMap_point (K : Set X) (D : Set X) x hx (hKD hx))
  rw [homologyMap_comp,homologyMap_comp] at h
  change (homologyMap (supportExcisionMap (K : Set X) (D : Set X)) (n+2) ≫
    homologyMap (supportPointMap (K : Set X) x hx) (n+2)) _ = _
  rw [h]
  change homologyMap (pointExcisionMap x (D : Set X) (hKD hx)) (n+2)
    (homologyMap (supportPointMap (Subtype.val ⁻¹' (K : Set X)) (⟨x,hKD hx⟩ : D) hx) (n+2) _) = _
  exact (congrArg (fun c => homologyMap (pointExcisionMap x (D : Set X) (hKD hx)) (n+2) c)
    (compactFundamentalClass_at_point n e oD (Subtype.val ⁻¹' (K : Set X))
      (SingularLocalSupport.compactWithinOpen (B := TopCat.of X) D K hKD).isCompact
      (⟨x,hKD hx⟩ : D) hx)).trans (hcompat ⟨x,hKD hx⟩)

end TernaryPoly.RationalManifoldCompact
