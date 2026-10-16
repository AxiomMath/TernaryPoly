module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionNaturality
public import TernaryPeriodPolynomials.Topology.Euclidean.Local.HomologyAtPoint
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalLocalChartHomology
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalRelativeExcision
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]

/-- Genuine local chains at a specified point of an arbitrary topological space. -/
abbrev localChains (x : X) := relativeChains ({x}ᶜ : Set X)

/-- A homeomorphism induces the actual isomorphism of local chain complexes at its image point. -/
def homeomorphLocalIso (e : X ≃ₜ Y) (x : X) : localChains x ≅ localChains (e x) :=
  relativeHomeomorphIso e {x}ᶜ {e x}ᶜ (by
    intro z
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, e.injective.eq_iff])

/-- Actual local homology can be computed in any chart, by two literal point-excision maps
and the actual homeomorphism between the chart source and target. -/
def chartLocalHomologyIso (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source) (k : ℕ) :
    (localChains x).homology k ≅ (localChains (e x)).homology k :=
  (pointLocalHomologyIso x ⟨e.source,e.open_source⟩ hx k).symm ≪≫
    (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso
      (homeomorphLocalIso e.toHomeomorphSourceTarget ⟨x,hx⟩) ≪≫
        pointLocalHomologyIso (e x) ⟨e.target,e.open_target⟩ (e.map_source hx) k

/-- The genuine local top homology at a Euclidean-chart point is one-dimensional. -/
def euclideanChartLocalTopIso (n : ℕ)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (n+2))))
    (x : X) (hx : x ∈ e.source) :
    (localChains x).homology (n+2) ≅ ModuleCat.of ℚ ℚ :=
  chartLocalHomologyIso e x hx (n+2) ≪≫ EuclideanLocalHomology.localTopAtIso n (e x)

/-- Every other actual point-local homology group vanishes at a Euclidean-chart point. -/
theorem euclideanChartLocal_isZero (n k : ℕ)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (n+2))))
    (x : X) (hx : x ∈ e.source) (hk : k ≠ n+2) :
    IsZero ((localChains x).homology k) :=
  (EuclideanLocalHomology.localAt_isZero_of_ne n k (e x) hk).of_iso
    (chartLocalHomologyIso e x hx k)

end TernaryPoly.RationalLocalChartHomology
