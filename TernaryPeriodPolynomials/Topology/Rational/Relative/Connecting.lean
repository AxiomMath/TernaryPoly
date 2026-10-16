module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.Naturality
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSingular
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalSingularAugmentation
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The literal morphism between the short exact chain sequences of two pairs. -/
def pairSequenceMap (f : C(X,Y)) (S : Set X) (T : Set Y) (h : Set.MapsTo f S T) :
    RelativeChainSequence.sequence (inclusion S) ⟶
      RelativeChainSequence.sequence (inclusion T) where
  τ₁ := chainMap (subspaceMap f S T h)
  τ₂ := chainMap f
  τ₃ := relativeMap f S T h
  comm₁₂ := (inclusion_naturality f S T h).symm
  comm₂₃ := by simp [RelativeChainSequence.sequence, relativeMap, cokernel.map]

/-- The genuine relative connecting map is natural for actual continuous maps of pairs. -/
theorem connecting_naturality (f : C(X,Y)) (S : Set X) (T : Set Y)
    (h : Set.MapsTo f S T) (k : ℕ) :
    connecting S k ≫ homologyMap (chainMap (subspaceMap f S T h)) k =
      homologyMap (relativeMap f S T h) (k+1) ≫ connecting T k :=
  HomologySequence.δ_naturality (pairSequenceMap f S T h)
    (RelativeChainSequence.shortExact (inclusion S))
    (RelativeChainSequence.shortExact (inclusion T)) (k+1) k rfl

/-- On contractible ambient spaces the actual relative connecting isomorphisms commute
with the maps of the literal subspaces. -/
theorem relativeSuccIso_naturality [ContractibleSpace X] [ContractibleSpace Y]
    (f : C(X,Y)) (S : Set X) (T : Set Y) (h : Set.MapsTo f S T)
    (k : ℕ) (hk : k ≠ 0) :
    (relativeSuccIso S k hk).hom ≫ homologyMap (chainMap (subspaceMap f S T h)) k =
      homologyMap (relativeMap f S T h) (k+1) ≫ (relativeSuccIso T k hk).hom :=
  connecting_naturality f S T h k

end TernaryPoly.RationalRelativeSingular
