module

public import TernaryPeriodPolynomials.Topology.Rational.Sphere.HomologyComplete
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalSphere
open CategoryTheory Limits ContractibleSingularHomology

/-- The literal punctured Euclidean space. -/
abbrev Punctured (d : ℕ) := ({0}ᶜ : Set (EuclideanSpace ℝ (Fin d)))

/-- The actual punctured Euclidean space retracts homotopically to its unit sphere,
using the radial product homeomorphism and contractibility of the positive radius. -/
def puncturedHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (Punctured (n+1)) (Sphere n) := by
  have : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace (by exact ⟨1, by norm_num⟩)
  exact (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (n+1)))).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl (Sphere n)).prodCongr
      (ContractibleSpace.hequiv_unit (Set.Ioi (0 : ℝ))).some) |>.trans
        (Homeomorph.prodUnique (Sphere n) Unit).toHomotopyEquiv

/-- The forward equivalence is literally radial normalization. -/
theorem puncturedHomotopyEquiv_apply (n : ℕ) (x : Punctured (n+1)) :
    ((puncturedHomotopyEquiv n).toFun x).val = ‖x.val‖⁻¹ • x.val :=
  homeomorphUnitSphereProd_apply_fst_coe (EuclideanSpace ℝ (Fin (n+1))) x

/-- Genuine rational homology of punctured Euclidean space. -/
def puncturedHomologyIso (n k : ℕ) :
    (chains (Punctured (n+1))).homology k ≅ (chains (Sphere n)).homology k :=
  (chainHomotopyEquiv (puncturedHomotopyEquiv n)).toHomologyIso k

end TernaryPoly.RationalSphere
