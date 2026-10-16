module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.EdgeOrbitAssembly

@[expose] public section


/-!
# Shapiro-type assembly of primitives over the points of a set

A `Γ`-equivariant homogeneous two-cocycle with values in functions on a `GL₃(ℚ)`-set `X` is the
differential of an equivariant one-cochain as soon as, for every point `x`, its `x`-component is
the differential of an equivariant one-cochain for `Γ ⊓ stabilizer x`. This is the orbit-by-orbit
assembly `GraphPieces.EdgeOrbitAssembly.exists_primitive`, restated with the stabilizer
cochains of the `Γ`-action written as cochains of the subgroup `Γ ⊓ stabilizer x`.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open TernaryPeriodPolynomials.GraphPieces

/-- The local exactness hypothesis of the orbit assembly, from stabilizer cochains. -/
theorem locallyExact_of_stabilizer {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) {X : Type} [MulAction RationalGL3 X]
    (Γ : Subgroup RationalGL3) (D : (Fin 3 → RationalGL3) → X → V) (x : X)
    (Px : cochains (Γ ⊓ MulAction.stabilizer RationalGL3 x) ρ 1)
    (hPx : ∀ y : Fin 3 → RationalGL3,
      (differentialOne (Γ ⊓ MulAction.stabilizer RationalGL3 x) ρ Px).val y = D y x) :
    EdgeOrbitAssembly.LocallyExact Γ ρ D x := by
  refine ⟨Px.val, ?_, ?_⟩
  · intro γ hγ w
    have hmem : γ.val ∈ Γ ⊓ MulAction.stabilizer RationalGL3 x :=
      Subgroup.mem_inf.mpr ⟨γ.property, MulAction.mem_stabilizer_iff.mpr hγ⟩
    exact Px.property ⟨γ.val, hmem⟩ w
  · intro w
    exact (hPx w).symm

/-- **Shapiro assembly.** If every point-component of a `Γ`-equivariant two-cocycle with values
in functions on `X` is a coboundary of a `Γ ⊓ stabilizer x`-equivariant one-cochain, then the
cocycle is the differential of a `Γ`-equivariant one-cochain with values in functions on `X`. -/
theorem exists_primitive_of_stabilizers {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (X : Type) [MulAction RationalGL3 X]
    (Γ : Subgroup RationalGL3) (D : cochains Γ (functionRepresentation ρ X) 2)
    (stab : ∀ x : X, ∃ Px : cochains (Γ ⊓ MulAction.stabilizer RationalGL3 x) ρ 1,
      ∀ y : Fin 3 → RationalGL3,
        (differentialOne (Γ ⊓ MulAction.stabilizer RationalGL3 x) ρ Px).val y = D.val y x) :
    ∃ P : cochains Γ (functionRepresentation ρ X) 1,
      ∀ y : Fin 3 → RationalGL3,
        (differentialOne Γ (functionRepresentation ρ X) P).val y = D.val y := by
  have localExact : ∀ x : X, EdgeOrbitAssembly.LocallyExact Γ ρ D.val x := by
    intro x
    obtain ⟨Px, hPx⟩ := stab x
    exact locallyExact_of_stabilizer ρ Γ D.val x Px hPx
  obtain ⟨P, hP⟩ := EdgeOrbitAssembly.exists_primitive Γ ρ D localExact
  exact ⟨P, fun y => by rw [hP]⟩

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

end
