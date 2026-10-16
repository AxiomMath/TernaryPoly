module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyQuotient
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
namespace TernaryPoly.LatticeTopCohomology

variable (A : Rep ℚ Lattice)
abbrev quotientMap : A →ₗ[ℚ] A ⧸ relations A := (relations A).mkQ

def quotientTrivialSubgroup : Subgroup Lattice where
  carrier := {g | ∀ v : A, quotientMap A (A.ρ g v) = quotientMap A v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh v
    simp only [map_mul, Module.End.mul_apply]
    rw [hg, hh]
  inv_mem' := by
    intro g hg v
    have h := hg (A.ρ g⁻¹ v)
    simpa using h.symm

theorem quotientMap_ρ_generator (g : Lattice)
    (hg : LinearMap.range (A.ρ g - LinearMap.id) ≤ relations A) (v : A) :
    quotientMap A (A.ρ g v) = quotientMap A v := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero (relations A)).mpr
  exact hg ⟨v,rfl⟩

theorem lattice_decomposition (g : Lattice) : first ^ g.toAdd.1 * second ^ g.toAdd.2 = g := by
  apply Multiplicative.toAdd.injective
  simp [first, second, Prod.smul_def, Prod.add_def]

/-- Every lattice action becomes trivial in the quotient by the two generator differences. -/
theorem quotientMap_ρ (g : Lattice) (v : A) : quotientMap A (A.ρ g v) = quotientMap A v := by
  have hx : first ∈ quotientTrivialSubgroup A :=
    quotientMap_ρ_generator A first le_sup_left
  have hy : second ∈ quotientTrivialSubgroup A :=
    quotientMap_ρ_generator A second le_sup_right
  have hg := (quotientTrivialSubgroup A).mul_mem
    ((quotientTrivialSubgroup A).zpow_mem hx g.toAdd.1)
    ((quotientTrivialSubgroup A).zpow_mem hy g.toAdd.2)
  rw [lattice_decomposition] at hg
  exact hg v

/-- The antisymmetric value of an actual two-cocycle in lattice coinvariants. -/
def alternatingValue (c : groupCohomology.cocycles₂ A) (g h : Lattice) : A ⧸ relations A :=
  quotientMap A (c (g,h) - c (h,g))

theorem quotient_cocycle (c : groupCohomology.cocycles₂ A) (g h j : Lattice) :
    quotientMap A (c (g,h)) + quotientMap A (c (g*h,j)) =
      quotientMap A (c (g,h*j)) + quotientMap A (c (h,j)) := by
  have hc := congrArg (quotientMap A) ((groupCohomology.mem_cocycles₂_iff c).mp c.property g h j)
  simpa only [map_add, quotientMap_ρ, add_comm] using hc

theorem alternatingValue_swap (c : groupCohomology.cocycles₂ A) (g h : Lattice) :
    alternatingValue A c g h = -alternatingValue A c h g := by
  simp [alternatingValue, map_sub]

theorem alternatingValue_self (c : groupCohomology.cocycles₂ A) (g : Lattice) :
    alternatingValue A c g g = 0 := by simp [alternatingValue]

theorem alternatingValue_mul_right (c : groupCohomology.cocycles₂ A) (g h j : Lattice) :
    alternatingValue A c g (h*j) = alternatingValue A c g h + alternatingValue A c g j := by
  have h₁ := quotient_cocycle A c g h j
  have h₂ := quotient_cocycle A c h g j
  have h₃ := quotient_cocycle A c h j g
  rw [mul_comm g h] at h₁
  rw [mul_comm j g] at h₃
  simp only [alternatingValue, map_sub]
  linear_combination (norm := module) h₂ - h₁ - h₃

theorem alternatingValue_mul_left (c : groupCohomology.cocycles₂ A) (g h j : Lattice) :
    alternatingValue A c (g*h) j = alternatingValue A c g j + alternatingValue A c h j := by
  rw [alternatingValue_swap A c (g*h) j, alternatingValue_mul_right]
  rw [alternatingValue_swap A c j g, alternatingValue_swap A c j h]
  abel

theorem alternatingValue_one_right (c : groupCohomology.cocycles₂ A) (g : Lattice) :
    alternatingValue A c g 1 = 0 := by
  have h := alternatingValue_mul_right A c g 1 1
  have e : alternatingValue A c g 1 + 0 =
      alternatingValue A c g 1 + alternatingValue A c g 1 := by simpa using h
  exact (add_left_cancel e).symm

theorem alternatingValue_inv_right (c : groupCohomology.cocycles₂ A) (g h : Lattice) :
    alternatingValue A c g h⁻¹ = -alternatingValue A c g h := by
  have e := alternatingValue_mul_right A c g h h⁻¹
  rw [mul_inv_cancel, alternatingValue_one_right] at e
  exact eq_neg_of_add_eq_zero_right e.symm

def alternatingCharacter (c : groupCohomology.cocycles₂ A) (g : Lattice) :
    Lattice →* Multiplicative (A ⧸ relations A) where
  toFun h := Multiplicative.ofAdd (alternatingValue A c g h)
  map_one' := alternatingValue_one_right A c g
  map_mul' h j := alternatingValue_mul_right A c g h j

theorem alternatingValue_zpow_right (c : groupCohomology.cocycles₂ A) (g h : Lattice) (n : ℤ) :
    alternatingValue A c g (h^n) = n • alternatingValue A c g h :=
  congrArg Multiplicative.toAdd ((alternatingCharacter A c g).map_zpow h n)

theorem alternatingValue_zpow_left (c : groupCohomology.cocycles₂ A) (g h : Lattice) (n : ℤ) :
    alternatingValue A c (g^n) h = n • alternatingValue A c g h := by
  rw [alternatingValue_swap A c (g^n) h, alternatingValue_zpow_right,
    alternatingValue_swap A c h g, smul_neg, neg_neg]

/-- The determinant is the actual root-dual factor on top cocycles in coinvariants. -/
theorem alternatingValue_determinant (c : groupCohomology.cocycles₂ A) (g h : Lattice) :
    alternatingValue A c g h =
      (g.toAdd.1 * h.toAdd.2 - g.toAdd.2 * h.toAdd.1) • alternatingValue A c first second := by
  calc
    alternatingValue A c g h = alternatingValue A c
        (first ^ g.toAdd.1 * second ^ g.toAdd.2)
        (first ^ h.toAdd.1 * second ^ h.toAdd.2) := by rw [lattice_decomposition, lattice_decomposition]
    _ = _ := by
      simp only [alternatingValue_mul_left, alternatingValue_mul_right,
        alternatingValue_zpow_left, alternatingValue_zpow_right, alternatingValue_self,
        smul_zero, zero_add, add_zero]
      rw [alternatingValue_swap A c second first]
      simp only [smul_neg, smul_smul]
      module

end TernaryPoly.LatticeTopCohomology
