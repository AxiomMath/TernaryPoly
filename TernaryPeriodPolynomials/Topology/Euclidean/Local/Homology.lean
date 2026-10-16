module

public import TernaryPeriodPolynomials.Topology.Rational.PuncturedSpace
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Connected

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanLocalHomology
open CategoryTheory Limits ContractibleSingularHomology RationalSphere RationalRelativeSingular

/-- Actual local rational singular chains of Euclidean space at the origin. -/
abbrev localChains (d : ℕ) := relativeChains (Punctured d)

instance punctured_pathConnected (n : ℕ) : PathConnectedSpace (Punctured (n+2)) := by
  have : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1,by norm_num⟩
  exact (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (n+2)))).symm.surjective.pathConnectedSpace
    (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (n+2)))).symm.continuous

/-- The local top homology of actual Euclidean (n+2)-space is one-dimensional. -/
def localTopIso (n : ℕ) : (localChains (n+2)).homology (n+2) ≅ ModuleCat.of ℚ ℚ :=
  relativeSuccIso (Punctured (n+2)) (n+1) (by omega) ≪≫
    puncturedHomologyIso (n+1) (n+1) ≪≫ topHomologyIso (n+1) (by omega)

/-- The genuine local homology vanishes in every other degree, including 0 and 1. -/
theorem local_isZero_of_ne (n k : ℕ) (hkn : k ≠ n+2) :
    IsZero ((localChains (n+2)).homology k) := by
  cases k with
  | zero => exact relative_zero_isZero (Punctured (n+2))
  | succ k =>
    cases k with
    | zero => exact relative_one_isZero (Punctured (n+2))
    | succ k =>
      exact (homology_isZero_of_ne (n+1) (k+1) (by omega) (by omega)).of_iso
        (relativeSuccIso (Punctured (n+2)) (k+1) (by omega) ≪≫
          puncturedHomologyIso (n+1) (k+1))

/-- The exact five-dimensional local homology input for the arithmetic manifold. -/
def localFiveIso : (localChains 5).homology 5 ≅ ModuleCat.of ℚ ℚ := localTopIso 3

/-- Every other genuine local homology group of five-space vanishes. -/
theorem localFive_isZero (k : ℕ) (hk : k ≠ 5) : IsZero ((localChains 5).homology k) :=
  local_isZero_of_ne 3 k hk

end TernaryPoly.EuclideanLocalHomology
