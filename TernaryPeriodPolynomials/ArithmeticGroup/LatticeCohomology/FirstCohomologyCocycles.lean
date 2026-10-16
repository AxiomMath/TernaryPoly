module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.FirstCohomology
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix

@[expose] public section

open CategoryTheory
noncomputable section
namespace TernaryPoly.LatticeFirstCohomology
open LatticeTopCohomology groupCohomology

variable (A : Rep ℚ Lattice)

/-- The zero set of a crossed homomorphism is a genuine subgroup. -/
def cocycleKernel (c : cocycles₁ A) : Subgroup Lattice where
  carrier := {g | c g=0}
  one_mem' := cocycles₁_map_one c
  mul_mem' := by
    intro g h hg hh
    change c (g*h)=0
    change c g=0 at hg
    change c h=0 at hh
    rw [(mem_cocycles₁_iff c).mp c.property g h,hg,hh,map_zero,zero_add]
  inv_mem' := by
    intro g hg
    have h := cocycles₁_map_inv c g⁻¹
    rw [inv_inv,hg,map_zero] at h
    exact neg_eq_zero.mp h.symm

/-- The two displayed lattice generators generate every integral pair, including negative powers. -/
theorem generators_decomposition (g : Lattice) : first ^ g.toAdd.1 * second ^ g.toAdd.2=g := by
  change (first ^ g.toAdd.1 * second ^ g.toAdd.2).toAdd=g.toAdd
  simp [first,second]

/-- Actual crossed homomorphisms on the lattice are determined by the two generator values. -/
theorem cocycle_eq_zero_of_generators (c : cocycles₁ A) (h₀ : c first=0) (h₁ : c second=0) : c=0 := by
  apply cocycles₁_ext
  intro g
  have h : g ∈ cocycleKernel A c := by
    rw [← generators_decomposition g]
    exact (cocycleKernel A c).mul_mem
      ((cocycleKernel A c).zpow_mem h₀ _) ((cocycleKernel A c).zpow_mem h₁ _)
  exact h

theorem cocycle_eq_of_generators (c d : cocycles₁ A)
    (h₀ : c first=d first) (h₁ : c second=d second) : c=d := by
  apply sub_eq_zero.mp
  apply cocycle_eq_zero_of_generators A
  · exact sub_eq_zero.mpr h₀
  · exact sub_eq_zero.mpr h₁

/-- The common-difference cocycle is an actual low-degree group coboundary. -/
def coboundary (v : A) : cocycles₁ A := ⟨d₀₁ A v,d₀₁_apply_mem_cocycles₁ v⟩

@[simp] theorem coboundary_apply (v : A) (g : Lattice) : coboundary A v g=A.ρ g v-v := rfl

/-- A closed pair that is a pair of common differences gives a global coboundary, with no comparison assumed. -/
theorem cocycle_is_coboundary_of_generators (c : cocycles₁ A) (v : A)
    (h₀ : c first=A.ρ first v-v) (h₁ : c second=A.ρ second v-v) :
    c=coboundary A v :=
  cocycle_eq_of_generators A c (coboundary A v) h₀ h₁

/-- A test for the actual induced first-cohomology map to be minus identity. -/
theorem map_H1_eq_neg_id (σ : Lattice →* Lattice) (φ : Rep.res σ A ⟶ A)
    (hexact : ∀ c : cocycles₁ A, ∃ v : A,
      (mapCocycles₁ σ φ c+c) first=A.ρ first v-v ∧
      (mapCocycles₁ σ φ c+c) second=A.ρ second v-v) :
    groupCohomology.map σ φ 1= -𝟙 (groupCohomology A 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine H1_induction_on x ?_
  intro c
  obtain ⟨v,h₀,h₁⟩ := hexact c
  have he := cocycle_is_coboundary_of_generators A (mapCocycles₁ σ φ c+c) v h₀ h₁
  have hz : H1π A (mapCocycles₁ σ φ c+c)=0 := by
    rw [H1π_eq_zero_iff,he]
    exact ⟨v,rfl⟩
  rw [map_add] at hz
  have hh := eq_neg_of_add_eq_zero_left hz
  change groupCohomology.map σ φ 1 (H1π A c)= -H1π A c
  simpa only [H1π_comp_map_apply] using hh

end TernaryPoly.LatticeFirstCohomology
