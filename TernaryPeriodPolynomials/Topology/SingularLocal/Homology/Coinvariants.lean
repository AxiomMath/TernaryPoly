module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionExactness
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory Limits HomologicalComplex
open EquivariantSingularResolution FreeActionLinearization

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- The actual coinvariant singular chain complex, obtained from Mathlib's genuine tensor-coinvariant
functor applied to the actual equivariant singular chains. -/
abbrev coinvariantChains (V : Rep ℚ G) : ChainComplex (ModuleCat ℚ) ℕ :=
  (equivariantChains G E).coinvariantsTensorObj V

variable [ContractibleSpace E] [IsCancelSMul G E]

/-- The genuine singular projective resolution computes group homology via Mathlib's Tor comparison. -/
def groupHomologyIsoViaTor (V : Rep ℚ G) (n : ℕ) :
    groupHomology V n ≅ (coinvariantChains G E V).homology n := by
  classical
  exact _root_.groupHomologyIso V n (projectiveResolution G E)

/-- The augmentation-compatible homotopy equivalence between the actual singular and bar resolutions. -/
def resolutionHomotopyEquiv :
    _root_.HomotopyEquiv (equivariantChains G E) (Rep.barComplex ℚ G) :=
  (projectiveResolution G E).homotopyEquiv (Rep.barResolution ℚ G)

/-- Applying the actual tensor-coinvariant functor preserves the explicit resolution homotopies. -/
def coinvariantResolutionHomotopyEquiv (V : Rep ℚ G) :
    _root_.HomotopyEquiv (coinvariantChains G E V)
      ((Rep.barComplex ℚ G).coinvariantsTensorObj V) :=
  ((Rep.coinvariantsTensor ℚ G).obj V).mapHomotopyEquiv (resolutionHomotopyEquiv G E)

/-- The literal group-homology chain complex maps to actual singular coinvariant chains through
Mathlib's inhomogeneous/bar isomorphism and the actual resolution comparison. -/
def comparisonMap (V : Rep ℚ G) :
    groupHomology.inhomogeneousChains V ⟶ coinvariantChains G E V := by
  classical
  exact (groupHomology.inhomogeneousChainsIso V).hom ≫
    (coinvariantResolutionHomotopyEquiv G E V).inv

/-- The concrete comparison map is a genuine quasi-isomorphism. -/
instance comparisonMap_quasiIso (V : Rep ℚ G) : QuasiIso (comparisonMap G E V) := by
  classical
  exact inferInstanceAs (QuasiIso ((groupHomology.inhomogeneousChainsIso V).hom ≫
    (coinvariantResolutionHomotopyEquiv G E V).inv))

/-- The actual map just constructed induces the group-homology comparison in every degree. -/
def groupCoinvariantHomologyIso (V : Rep ℚ G) (n : ℕ) :
    groupHomology V n ≅ (coinvariantChains G E V).homology n :=
  isoOfQuasiIsoAt (comparisonMap G E V) n

end TernaryPoly.SingularLocalHomology
