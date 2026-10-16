module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyPlane

@[expose] public section


open CategoryTheory MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice RadicalFirstCohomology
open LatticeTopCohomology LatticeFirstCohomology groupCohomology

/-- A linear functional invariant under the two lattice generators is invariant under every element. -/
theorem linearMap_invariant_of_generators {V : Type*} [AddCommGroup V] [Module ℚ V]
    (A : Rep ℚ Lattice) (E : A →ₗ[ℚ] V)
    (h0 : ∀ v,E (A.ρ first v)=E v) (h1 : ∀ v,E (A.ρ second v)=E v)
    (g : Lattice) (v : A) : E (A.ρ g v)=E v := by
  let K : Subgroup Lattice := {
    carrier := {g | ∀ v,E (A.ρ g v)=E v}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro g h hg hh v
      rw [map_mul,Module.End.mul_apply,hg,hh]
    inv_mem' := by
      intro g hg v
      have h := hg (A.ρ g⁻¹ v)
      rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one] at h
      exact h.symm }
  have hg : g∈K := by
    rw [←generators_decomposition g]
    exact K.mul_mem (K.zpow_mem h0 _) (K.zpow_mem h1 _)
  exact hg v

/-- The actual plane-radical action is trivial after evaluation on its binary face. -/
theorem planeEval_radical (n : ℕ) (g : Lattice) (v : H n) :
    planeEval n ((planeRep n).ρ g v)=planeEval n v := by
  apply linearMap_invariant_of_generators (planeRep n) (planeEval n) _ _ g v
  · intro w
    apply Subtype.ext
    rw [planeRep_first]
    exact planeEval_shear 0 w
  · intro w
    apply Subtype.ext
    rw [planeRep_second]
    exact planeEval_shear 1 w

/-- Erasure turns every actual crossed homomorphism into a literal additive lattice map. -/
def erasedPlaneCocycle (n : ℕ) (c : cocycles₁ (planeRep n)) :
    cocycles₁ (Rep.trivial ℚ Lattice (BinaryH n)) :=
  ⟨fun g => planeEval n (c g),by
    apply (mem_cocycles₁_iff _).mpr
    intro g h
    rw [(mem_cocycles₁_iff c).mp c.property g h,map_add,planeEval_radical]
    rfl⟩

/-- The two erased generator values determine all erased cocycle values by integral linearity. -/
theorem planeEval_cocycle_coordinates (n : ℕ) (c : cocycles₁ (planeRep n)) (g : Lattice) :
    planeEval n (c g)=g.toAdd.1 • planeEval n (c first)+g.toAdd.2 • planeEval n (c second) := by
  let d : cocycles₁ (Rep.trivial ℚ Lattice (BinaryH n)) :=
    ⟨fun g => g.toAdd.1 • planeEval n (c first)+g.toAdd.2 • planeEval n (c second),by
      apply (mem_cocycles₁_iff _).mpr
      intro g h
      change (g.toAdd.1+h.toAdd.1) • planeEval n (c first)+
        (g.toAdd.2+h.toAdd.2) • planeEval n (c second)=_
      simp only [add_zsmul]
      change _=h.toAdd.1 • planeEval n (c first)+h.toAdd.2 • planeEval n (c second)+
        (g.toAdd.1 • planeEval n (c first)+g.toAdd.2 • planeEval n (c second))
      abel⟩
  have he : erasedPlaneCocycle n c=d := by
    apply cocycle_eq_of_generators
    · change planeEval n (c first)=1 • planeEval n (c first)+(0 : ℤ) • planeEval n (c second)
      simp
    · change planeEval n (c second)=(0 : ℤ) • planeEval n (c first)+1 • planeEval n (c second)
      simp
  exact congrArg (fun c => c g) he

end TernaryPoly.OrdinaryFaceRadical
