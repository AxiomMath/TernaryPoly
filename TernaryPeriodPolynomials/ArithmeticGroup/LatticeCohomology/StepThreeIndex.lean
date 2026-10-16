module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalScalingMatrices
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open LatticeTopCohomology

/-- Reduction of the actual two integral radical parameters modulo three. -/
def latticeModThree : Lattice →* Multiplicative (ZMod 3 × ZMod 3) where
  toFun g := Multiplicative.ofAdd ((g.toAdd.1 : ZMod 3),(g.toAdd.2 : ZMod 3))
  map_one' := by simp
  map_mul' g h := by
    change (((g.toAdd.1+h.toAdd.1 : ℤ) : ZMod 3),
      ((g.toAdd.2+h.toAdd.2 : ℤ) : ZMod 3)) =
      ((g.toAdd.1 : ZMod 3)+(h.toAdd.1 : ZMod 3),
       (g.toAdd.2 : ZMod 3)+(h.toAdd.2 : ZMod 3))
    simp only [Int.cast_add]

/-- Multiplication by three embeds the integral lattice. -/
theorem scaleLattice_three_injective : Function.Injective (scaleLattice 3) := by
  intro g h he
  have h1 := congrArg (fun x : Lattice => x.toAdd.1) he
  have h2 := congrArg (fun x : Lattice => x.toAdd.2) he
  change (3 : ℤ)*g.toAdd.1=3*h.toAdd.1 at h1
  change (3 : ℤ)*g.toAdd.2=3*h.toAdd.2 at h2
  have he1 : g.toAdd.1=h.toAdd.1 := by omega
  have he2 : g.toAdd.2=h.toAdd.2 := by omega
  exact Prod.ext he1 he2

/-- The step-three subgroup is exactly the kernel of the literal finite reduction. -/
theorem scaleLattice_three_range : (scaleLattice 3).range=latticeModThree.ker := by
  ext g
  change (∃ h,scaleLattice 3 h=g) ↔ latticeModThree g=1
  constructor
  · rintro ⟨h,rfl⟩
    change (((3*h.toAdd.1 : ℤ) : ZMod 3),((3*h.toAdd.2 : ℤ) : ZMod 3))=(0,0)
    simp only [Int.cast_mul]
    change ((3 : ZMod 3)*(h.toAdd.1 : ZMod 3),
      (3 : ZMod 3)*(h.toAdd.2 : ZMod 3))=(0,0)
    rw [show (3 : ZMod 3)=0 from rfl,zero_mul,zero_mul]
  · intro hg
    have h1 := congrArg (fun x : Multiplicative (ZMod 3 × ZMod 3) => x.toAdd.1) hg
    have h2 := congrArg (fun x : Multiplicative (ZMod 3 × ZMod 3) => x.toAdd.2) hg
    change (g.toAdd.1 : ZMod 3)=0 at h1
    change (g.toAdd.2 : ZMod 3)=0 at h2
    obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd g.toAdd.1 3).mp h1
    obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd g.toAdd.2 3).mp h2
    refine ⟨Multiplicative.ofAdd (a,b),?_⟩
    exact Prod.ext ha.symm hb.symm

/-- Finite index holds for the actual range used by radical restriction. -/
instance scaleLattice_three_finiteIndex : (scaleLattice 3).range.FiniteIndex := by
  rw [scaleLattice_three_range]
  infer_instance

/-- The literal parameterization of the step-three subgroup. -/
def scaleLatticeThreeEquiv : Lattice ≃* (scaleLattice 3).range :=
  MonoidHom.ofInjective scaleLattice_three_injective

@[simp] theorem scaleLatticeThreeEquiv_val (g : Lattice) :
    (scaleLatticeThreeEquiv g).val=scaleLattice 3 g := rfl

end TernaryPoly.OrdinaryFaceRadical
