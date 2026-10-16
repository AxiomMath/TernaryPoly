module

public import TernaryPeriodPolynomials.Topology.Rational.Sphere.Geometry
public import TernaryPeriodPolynomials.Topology.Rational.SingularAugmentation
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DirectSum.Finite

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalSphere
open CategoryTheory Limits AlgebraicTopology ContractibleSingularHomology
open RationalSingularAugmentation

/-- The two actual points of the zero-sphere. -/
def zeroPole (positive : Bool) : Sphere 0 :=
  ⟨EuclideanSpace.single 0 (if positive then (1 : ℝ) else -1), by cases positive <;> simp⟩

/-- Every point of the zero-sphere has coordinate +1 or -1. -/
theorem zero_coordinate (x : Sphere 0) : x.val 0 = 1 ∨ x.val 0 = -1 := by
  have h := congrArg (fun t : ℝ => t^2) (mem_sphere_zero_iff_norm.mp x.property)
  have hsq : (x.val 0)^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq] at h
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, one_pow] using h
  exact sq_eq_one_iff.mp hsq

/-- The literal zero-sphere is equivalent to two points. -/
def zeroEquivBool : Sphere 0 ≃ Bool :=
  Equiv.ofBijective (fun x => decide (x.val 0 = 1)) (by
    constructor
    · intro x y h
      apply Subtype.ext
      ext i
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      rcases zero_coordinate x with hx | hx <;>
        rcases zero_coordinate y with hy | hy <;> simp_all
    · intro b
      exact ⟨zeroPole b, by cases b <;> norm_num [zeroPole]⟩)

instance : Finite (Sphere 0) := Finite.of_equiv Bool zeroEquivBool.symm
instance : Nonempty (Sphere 0) := ⟨zeroPole true⟩

/-- Actual positive singular homology of the two-point sphere vanishes. -/
theorem zeroSphere_homology_isZero (k : ℕ) (hk : k ≠ 0) :
    IsZero ((chains (Sphere 0)).homology k) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{0} ℚ) k
    (ModuleCat.of.{0} ℚ ℚ) (TopCat.of (Sphere 0)) hk

/-- Zeroth homology of the literal zero-sphere is the free module on its two points. -/
def zeroHomologyIso : (chains (Sphere 0)).homology 0 ≅
    ModuleCat.of ℚ (DirectSum (Sphere 0) (fun _ => ℚ)) :=
  singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{0} ℚ)
    (ModuleCat.of.{0} ℚ ℚ) (TopCat.of (Sphere 0)) ≪≫ ModuleCat.coprodIsoDirectSum _

instance : Module.Finite ℚ ((chains (Sphere 0)).homology 0) := by
  let _ := Fintype.ofFinite (Sphere 0)
  exact Module.Finite.equiv (zeroHomologyIso.toLinearEquiv.symm)

/-- The zero-sphere has exactly two independent H0 classes. -/
theorem zeroHomology_finrank : Module.finrank ℚ ((chains (Sphere 0)).homology 0) = 2 := by
  let _ := Fintype.ofFinite (Sphere 0)
  rw [zeroHomologyIso.toLinearEquiv.finrank_eq]
  simp [Module.finrank_directSum, Fintype.card_congr zeroEquivBool]

/-- The reduced zeroth homology of the actual zero-sphere is one-dimensional. -/
def zeroReducedHomologyIso : kernel (augmentation (Sphere 0)) ≅ ModuleCat.of ℚ ℚ := by
  have hsurj := augmentation_surjective (Sphere 0)
  have hdim := (augmentation (Sphere 0)).hom.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    zeroHomology_finrank] at hdim
  have hk : Module.finrank ℚ (LinearMap.ker (augmentation (Sphere 0)).hom) = 1 := by omega
  exact ModuleCat.kernelIsoKer _ ≪≫
    (LinearEquiv.ofFinrankEq _ _ (by simpa using hk)).toModuleIso

end TernaryPoly.RationalSphere
