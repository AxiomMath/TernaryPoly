module

public import TernaryPeriodPolynomials.Topology.Rational.Local.ChartHomology
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Homotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalLocalOrientation
open CategoryTheory HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalLocalChartHomology
variable {X : Type} [TopologicalSpace X]

/-- The actual support-to-point map is the identity map of the ambient space as a map of pairs. -/
def supportPointMap (K : Set X) (x : X) (hx : x ∈ K) :
    relativeChains Kᶜ ⟶ localChains x :=
  relativeMap (ContinuousMap.id X) Kᶜ {x}ᶜ (by
    intro z hz he
    change z = x at he
    subst z
    exact hz hx)

/-- A family of actual local homology classes is locally represented when one genuine
relative class supplies all its values throughout a neighborhood of each point. -/
def LocallyRepresented (k : ℕ) (o : ∀ x : X, (localChains x).homology k) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (K : Set X), x ∈ U ∧ (U : Set X) ⊆ K ∧
    ∃ c : (relativeChains Kᶜ).homology k,
      ∀ (y : X) (_hy : y ∈ U) (hK : y ∈ K), homologyMap (supportPointMap K y hK) k c = o y

/-- Homological orientation data with actual local representability. The rank and manifold
hypotheses needed for Poincare duality are separate mathematical obligations. -/
structure Orientation (k : ℕ) (X : Type) [TopologicalSpace X] where
  generator : ∀ x : X, (localChains x).homology k
  nonzero : ∀ x, generator x ≠ 0
  locallyRepresented : LocallyRepresented k generator

end TernaryPoly.RationalLocalOrientation
