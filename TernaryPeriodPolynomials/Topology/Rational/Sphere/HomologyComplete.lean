module

public import TernaryPeriodPolynomials.Topology.Rational.Sphere.Homology
public import TernaryPeriodPolynomials.Topology.Rational.Sphere.Zero
public import TernaryPeriodPolynomials.Topology.Rational.MayerVietorisH1
public import TernaryPeriodPolynomials.Topology.Rational.SingularConnected
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalSphere
open CategoryTheory Limits ContractibleSingularHomology RationalSingularAugmentation

/-- Positive-dimensional literal Euclidean spheres are path connected. -/
instance sphere_positive_pathConnected (n : ℕ) : PathConnectedSpace (Sphere (n+1)) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank]
  simp only [finrank_euclideanSpace_fin]
  exact_mod_cast (show 1 < n+1+1 by omega)

/-- The band homotopy equivalence identifies the actual reduced H0 groups. -/
def bandReducedIso (n : ℕ) : kernel (augmentation (sphereBand n)) ≅
    kernel (augmentation (Sphere n)) :=
  kernelIsoOfEq (homotopyEquiv_naturality (sphereBandHomotopyEquiv n)).symm ≪≫
    kernelIsIsoComp (bandHomologyIso n 0).hom _

/-- The degree-one sphere recurrence uses reduced H0, including the disconnected zero-sphere. -/
def firstHomologyIso (n : ℕ) : (chains (Sphere (n+1))).homology 1 ≅
    kernel (augmentation (Sphere n)) :=
  RationalMayerVietoris.homologyOneReducedIso (upperOpens n) (lowerOpens n)
    (upperOpens_sup_lowerOpens n) ≪≫ bandReducedIso n

/-- The genuine rational first homology of the circle is one-dimensional. -/
def circleHomologyIso : (chains (Sphere 1)).homology 1 ≅ ModuleCat.of ℚ ℚ :=
  firstHomologyIso 0 ≪≫ zeroReducedHomologyIso

/-- First homology vanishes on every sphere of dimension at least two. -/
theorem firstHomology_isZero (n : ℕ) : IsZero ((chains (Sphere (n+2))).homology 1) := by
  have := augmentation_isIso_of_pathConnected (Sphere (n+1))
  have hz : IsZero (kernel (augmentation (Sphere (n+1)))) := isZero_kernel_of_mono _
  exact hz.of_iso (firstHomologyIso (n+1))

/-- All positive-dimensional spheres have their actual top rational homology equal to ℚ. -/
def topHomologyIso (n : ℕ) (hn : n ≠ 0) :
    (chains (Sphere n)).homology n ≅ ModuleCat.of ℚ ℚ := by
  induction n with
  | zero => exact (hn rfl).elim
  | succ n ih =>
    cases n with
    | zero => exact circleHomologyIso
    | succ n => exact suspensionIso (n+1) (n+1) (by omega) ≪≫ ih (by omega)

/-- Actual positive rational homology of a sphere vanishes outside its dimension. -/
theorem homology_isZero_of_ne (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero ((chains (Sphere n)).homology k) := by
  induction n generalizing k with
  | zero => exact zeroSphere_homology_isZero k hk
  | succ n ih =>
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      cases k with
      | zero =>
        cases n with
        | zero => exact (hkn rfl).elim
        | succ n => exact firstHomology_isZero n
      | succ k =>
        exact (ih (k+1) (by omega) (by omega)).of_iso
          (suspensionIso n (k+1) (by omega))

end TernaryPoly.RationalSphere
