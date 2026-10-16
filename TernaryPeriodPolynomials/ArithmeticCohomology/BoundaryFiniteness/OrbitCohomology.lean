module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.FlagCoinduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.ProductCohomology
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section


open GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryFiniteness.OrbitCohomology

noncomputable section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable (X : Type) [MulAction G X]

abbrev Orbits := Quotient (MulAction.orbitRel G X)

def stabilizer (orbit : Orbits (G := G) X) : Subgroup G := MulAction.stabilizer G orbit.out

def orbitEquiv : X ≃ (orbit : Orbits (G := G) X) × G ⧸ stabilizer (G := G) X orbit :=
  MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X

theorem orbitEquiv_symm (orbit : Orbits (G := G) X) (coset : G ⧸ stabilizer (G := G) X orbit) :
    (orbitEquiv (G := G) X).symm ⟨orbit, coset⟩ = MulAction.ofQuotientStabilizer G orbit.out coset := rfl

theorem orbitEquiv_symm_smul (orbit : Orbits (G := G) X) (coset : G ⧸ stabilizer (G := G) X orbit) (element : G) :
    (orbitEquiv (G := G) X).symm ⟨orbit, element • coset⟩ = element • (orbitEquiv (G := G) X).symm ⟨orbit, coset⟩ :=
  MulAction.ofQuotientStabilizer_smul G orbit.out element coset

def coefficientEquiv : (X → V) ≃ₗ[ℂ] ∀ orbit : Orbits (G := G) X, G ⧸ stabilizer (G := G) X orbit → V where
  toFun function orbit coset := function ((orbitEquiv (G := G) X).symm ⟨orbit, coset⟩)
  invFun function input := function ((orbitEquiv (G := G) X) input).1 ((orbitEquiv (G := G) X) input).2
  left_inv function := by funext input; simp
  right_inv function := by
    funext orbit coset
    exact congrArg (fun pair => function pair.1 pair.2)
      ((orbitEquiv (G := G) X).apply_symm_apply ⟨orbit, coset⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientEquiv_intertwines (action : Representation ℂ G V) (element : G) :
    (coefficientEquiv (G := G) X).toLinearMap.comp (FlagCoinduction.functionAction action X element) =
      (ProductCohomology.productAction
        (fun orbit : Orbits (G := G) X => FlagCoinduction.functionAction action (G ⧸ stabilizer (G := G) X orbit)) element).comp
          (coefficientEquiv (G := G) X).toLinearMap := by
  ext function orbit coset
  change action element (function (element⁻¹ • (orbitEquiv (G := G) X).symm ⟨orbit, coset⟩)) =
    action element (function ((orbitEquiv (G := G) X).symm ⟨orbit, element⁻¹ • coset⟩))
  rw [orbitEquiv_symm_smul]

def cohomologyEquiv (action : Representation ℂ G V) :
    H2 ⊤ (FlagCoinduction.functionAction action X) ≃ₗ[ℂ]
      ∀ orbit : Orbits (G := G) X, groupCohomology.H2 (Rep.of (action.comp (stabilizer (G := G) X orbit).subtype)) :=
  (OrdinaryCohomology.groupEquiv (FlagCoinduction.functionAction action X)).trans
    ((groupCohomology.mapIso (MulEquiv.refl G) (coefficientEquiv (G := G) X)
      (coefficientEquiv_intertwines X action) 2).toLinearEquiv.trans
      ((OrdinaryCohomology.groupEquiv (ProductCohomology.productAction
        (fun orbit : Orbits (G := G) X => FlagCoinduction.functionAction action (G ⧸ stabilizer (G := G) X orbit)))).symm.trans
        ((ProductCohomology.cohomologyEquiv ⊤
          (fun orbit : Orbits (G := G) X => FlagCoinduction.functionAction action (G ⧸ stabilizer (G := G) X orbit))).trans
          (LinearEquiv.piCongrRight fun orbit =>
            (OrdinaryCohomology.groupEquiv (FlagCoinduction.functionAction action (G ⧸ stabilizer (G := G) X orbit))).trans
              (FlagCoinduction.cohomologyEquiv (stabilizer (G := G) X orbit) action)))))

theorem finiteDimensional_of_stabilizers (action : Representation ℂ G V)
    [Finite (Orbits (G := G) X)]
    [∀ orbit : Orbits (G := G) X, FiniteDimensional ℂ
      (groupCohomology.H2 (Rep.of (action.comp (stabilizer (G := G) X orbit).subtype)))] :
    FiniteDimensional ℂ (H2 ⊤ (FlagCoinduction.functionAction action X)) :=
  FiniteDimensional.of_injective (cohomologyEquiv X action).toLinearMap (cohomologyEquiv X action).injective

end

end TernaryPeriodPolynomials.BoundaryFiniteness.OrbitCohomology
