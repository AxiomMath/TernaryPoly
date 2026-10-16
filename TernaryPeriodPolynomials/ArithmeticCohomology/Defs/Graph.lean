module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Induction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.FullBoundary

@[expose] public section


/-!
# The complete general Eisenstein graph assertion

All maps in `GraphConclusion` are constructed in the conclusion and are tied
to explicit formulas. The only theorem hypotheses are independent cuspidal,
cohomological inducing data and holomorphy of the actual plane Eisenstein
operator. In particular, no half-dimension assertion, spanning assertion,
graph inclusion, or boundary projector is assumed.
-/

noncomputable section
namespace GeneralEisenstein
open Homogeneous

/-- The full associate-pair summand in maximal-stratum coordinates. -/
def associatePair {n : ℕ} (D : InducingData n) :
    Submodule ℂ (BoundaryCoordinates n D.chi) :=
  (boundarySummand D .plane).prod (boundarySummand D .line)

/-- The direct-sum action of the same finite Hecke correspondence on both sides. -/
def pairHecke {n : ℕ} (D : InducingData n)
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (t : HeckeCorrespondence) : Module.End ℂ (BoundaryCoordinates n D.chi) :=
  (T .plane t).prodMap (T .line t)

/-- The Hecke-isotypical projector is characterized by range, identity on that
range, and commutation with every actual double-coset correspondence. -/
def IsIsotypicalProjection {n : ℕ} (D : InducingData n)
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (p : Module.End ℂ (BoundaryCoordinates n D.chi)) : Prop :=
  LinearMap.range p = associatePair D ∧
  (∀ x ∈ associatePair D, p x = x) ∧
  ∀ t, p.comp (pairHecke D T t) = (pairHecke D T t).comp p

/-- The whole projected global image is the graph of the standard cohomological
intertwiner. Existence and uniqueness of the genuine spectral projection,
well-definedness of all finite-coset actions and restriction, and descent of the
standard integral are part of the requested conclusion.

Global restriction first lands in the cohomology of the whole rational boundary
building, including complete flags. The map q then takes maximal-stratum
coordinates; the unique Hecke-isotypical projector p selects the associate pair.
The requirement associatePair ≤ range q also constructs both full-boundary
summands, independently of the projected global image.
-/
def GraphConclusion {n : ℕ} (D : InducingData n) : Prop :=
  SourceComparisonExists D ∧
  ∃ (r : WholeGlobalH2 n D.chi →ₗ[ℂ] FullBoundaryH2 n D.chi)
    (q : FullBoundaryH2 n D.chi →ₗ[ℂ] BoundaryCoordinates n D.chi)
    (hecke : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (p : Module.End ℂ (BoundaryCoordinates n D.chi))
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line),
    RealizesFullRestriction n D.chi r ∧
    RealizesBoundaryCoordinates n D.chi q ∧
    associatePair D ≤ LinearMap.range q ∧
    (∀ side, RealizesHecke (flagRepresentation (rationalCoefficientComponent n D.chi) side)
      (hecke side)) ∧
    IsIsotypicalProjection D hecke p ∧
    (∀ p', IsIsotypicalProjection D hecke p' → p' = p) ∧
    RealizesStandard D T ∧
    (LinearMap.range (p.comp (q.comp r)) : Set (BoundaryCoordinates n D.chi)) =
      {y | ∃ ξ : boundarySummand D .plane, y = (ξ.val, (T ξ).val)}

end GeneralEisenstein

end
