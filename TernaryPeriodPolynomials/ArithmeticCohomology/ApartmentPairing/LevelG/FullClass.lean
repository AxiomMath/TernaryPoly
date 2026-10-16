module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Core
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33Diagram
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.SectorInduction

@[expose] public section


/-!
# Lemma 3.3 at level `G`: full-level boundary classes, the level-`G` diagram, and the cellular reading

Formalized by Claude Sonnet 5.5.

Paper: Lemma 3.3 at level `G`:
(`M = Ind_K^G E_{n,t}`, "take coinvariants in homology and invariants in cohomology under the finite covering group.
Rational averaging is exact").

The cohomology `H¹(∂X̄_G; M)` is `(fullBoundaryCochains n e).homology 1` (the cohomology of `G`-equivariant cochains of the
full boundary chains, the library), the library's invariants.  Rational averaging identifies it with the coinvariants; the
homology side `H₃(∂X̄_G; 𝓜)` is realized as the subspace `H3boundaryG` of the neat-level boundary homology that is Poincaré
dual to it (`resToBoundary`, `PDG`).  The group `G` DOES act geometrically on the boundary of the universal bordification (`fullBoundaryChains` carries the genuine
`IntegralGL`-action `integralBoundaryAction`); what was absent from the library, and is built in `BoundaryAction.lean`, is the induced
`G/Γ(6)`-action on the quotient local-coefficient homology `boundaryLocalChains W`.  `BoundaryCap.lean` proves that boundary Poincaré duality is
equivariant for this action (`PDboundary_equivariant`), `Fixed.lean` identifies `H3boundaryG` with its invariants and
`Coinvariants.lean` with the honest coinvariant homology; what is proved here is the diagram on `H3boundaryG` and, in `Descent.lean`,
its averaged form.

* `fullClass_ordinary`, `fullClass_frame`, `fullClass_fullEquivariant`: the Steinberg functional of `j_* PD⁻¹ res ω` is
  `G`-equivariant for every level-`G` cohomology class `ω`.
* `fullBoundaryPairing`: the bottom arrow `ω ↦ ⟨ω, ∂a⟩ ∈ M`; `fullBoundaryClassToG`: `ω ↦ Cor(j_* PD⁻¹ res ω)`;
  `topEvaluationG`: the right arrow `z ↦ F_z(ℓ)` (value of `Θ^G z` on the identity apartment).
* `levelG_diagram`, `levelG_diagram_PD`: `F_{j^G_* c}(ℓ) = ⟨PD_∂ c, ∂a⟩`; `flatBoundaryPairing_PDG`, `PDG_restrict`: agreement
  with the neat-level `flatBoundaryPairing` and `PDboundary`.
* `levelG_cellular`: the same equals the coefficient of a cellular top cycle against the normalized top-cell generator.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.OrdinaryApartmentPresentation
  TernaryPoly.OrdinaryBoundaryCone

open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.AppendixBResidue

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

variable (n : ℕ) (e : ℤ)

/-- The neat-level functional of the boundary class attached to a full-level cocycle is the ordinary evaluation of its
restriction. -/
theorem fullClass_ordinary (x : (fullBoundaryCochains n e).cycles 1) :
    (groupOrdinaryIso (restrictedCoefficients n e)).hom
        (fullBoundaryClassToGroup n e ((fullBoundaryCochains n e).homologyπ 1 x)) =
      boundaryOrdinaryEvaluation (restrictedCoefficients n e)
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1
          (cyclesMap (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1 x)) := by
  let r := restriction principalSix fullBoundaryChains (actualCoefficients n e)
  have hn := congrArg (fun f => f x) (homologyπ_naturality r 1)
  have hmap : homologyMap (boundaryRestriction n e) 1 ((fullBoundaryCochains n e).homologyπ 1 x) =
      (boundaryCohomologyIso (restrictedCoefficients n e)).hom
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 (cyclesMap r 1 x)) := by
    rw [boundaryRestriction, homologyMap_comp]
    exact congrArg (fun y => (boundaryCohomologyIso (restrictedCoefficients n e)).hom y) hn
  change (groupOrdinaryIso (restrictedCoefficients n e)).hom
    (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3
      ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom
        (homologyMap (boundaryRestriction n e) 1 ((fullBoundaryCochains n e).homologyπ 1 x)))) = _
  rw [hmap]
  exact cappedBoundary_ordinary_apply (restrictedCoefficients n e) _

/-- The finite apartment chain of the full boundary complex, the cycle `∂a` of the coordinate apartment. -/
abbrev apartmentChainFull : (fullBoundaryChains.X 1) :=
  (canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain

/-- The value of the ordinary functional of a full-level cocycle on the frame `g` is `ρ(g)` of its value on `∂a`. -/
theorem fullClass_frame (x : (fullBoundaryCochains n e).cycles 1) (g : IntegralGL) :
    (boundaryOrdinaryEvaluation (restrictedCoefficients n e)
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1
          (cyclesMap (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1 x))).hom
        (frameCycle g) =
      (actualCoefficients n e).ρ g
        ((cocycleValue fullBoundaryChains (actualCoefficients n e) 1 x).hom apartmentChainFull) := by
  refine (boundaryOrdinaryEvaluation_frame (restrictedCoefficients n e)
    (cyclesMap (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1 x) g).trans ?_
  rw [restriction_boundary_cocycle_value]
  exact Rep.hom_comm_apply (cocycleValue fullBoundaryChains (actualCoefficients n e) 1 x) g apartmentChainFull

/-- **Full-level boundary classes have `G`-equivariant Steinberg functionals** (the invariants of the boundary
cohomology map to `G`-equivariant functionals; O-G1 for `j_* ∘ PD_∂⁻¹` restricted to invariants). -/
theorem fullClass_fullEquivariant (x : (fullBoundaryCochains n e).cycles 1) :
    ordinaryFunctionalFullEquivariant n e
      (boundaryOrdinaryEvaluation (restrictedCoefficients n e)
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1
          (cyclesMap (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1 x))) := by
  intro g c
  set φ := boundaryOrdinaryEvaluation (restrictedCoefficients n e)
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1
          (cyclesMap (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1 x)) with hφ
  have key : (φ.hom.toLinearMap ∘ₗ (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g))) =
      ((actualCoefficients n e).ρ g ∘ₗ φ.hom.toLinearMap) := by
    apply cycle_functional_ext
    intro a
    have h1 : φ.hom (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g) (frameCycle a)) =
        (actualCoefficients n e).ρ g (φ.hom (frameCycle a)) := by
      rw [OrdinaryFullAction.frameCycle_equivariant, hφ, fullClass_frame, fullClass_frame,
        map_mul, Module.End.mul_apply]
    exact h1
  exact LinearMap.congr_fun key c

local instance : HasForget₂ (Rep.{0} ℚ IntegralGL) Ab :=
  HasForget₂.trans (Rep ℚ IntegralGL) (ModuleCat ℚ) Ab
local instance : (forget₂ (Rep.{0} ℚ IntegralGL) Ab).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ IntegralGL) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)
local instance : (forget₂ (Rep.{0} ℚ IntegralGL) Ab).PreservesHomology :=
  inferInstanceAs ((forget₂ (Rep ℚ IntegralGL) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

/-- `∂a` is a cycle of the full boundary chains. -/
theorem apartmentChainFull_boundary : (fullBoundaryChains.d 1 0).hom apartmentChainFull = 0 := by
  have h := congrArg (fun f => f.hom finiteApartmentChain) (canonicalBoundaryEquiv.inv.comm 1 0)
  change (fullBoundaryChains.d 1 0).hom ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain) =
    (canonicalBoundaryEquiv.inv.f 0).hom (canonicalFaceCone.d 1 0 finiteApartmentChain) at h
  rw [h, finiteApartmentChain_boundary, map_zero]

/-- The cycle `∂a` in the full boundary chains. -/
def apartmentCycleFull : fullBoundaryChains.cycles 1 :=
  fullBoundaryChains.cyclesMk apartmentChainFull 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)) apartmentChainFull_boundary

/-- The homology class of the coordinate apartment in `H₁(∂X̄_G)` (full boundary chains). -/
def apartmentClassFull : fullBoundaryChains.homology 1 :=
  fullBoundaryChains.homologyπ 1 apartmentCycleFull

/-- **The bottom arrow at level `G`**: `ω ↦ ⟨ω, ∂a⟩ ∈ M` for `ω ∈ H¹(∂X̄_G; M) = H¹(Hom_G(C_*(∂X̄), M))`. -/
def fullBoundaryPairing : (fullBoundaryCochains n e).homology 1 ⟶ ModuleCat.of ℚ (actualCoefficients n e) :=
  homologyEvaluation fullBoundaryChains (actualCoefficients n e) 1 ≫
    ModuleCat.ofHom
      { toFun := fun f => f.hom apartmentClassFull
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }

theorem fullBoundaryPairing_cocycle (x : (fullBoundaryCochains n e).cycles 1) :
    fullBoundaryPairing n e ((fullBoundaryCochains n e).homologyπ 1 x) =
      (cocycleValue fullBoundaryChains (actualCoefficients n e) 1 x).hom apartmentChainFull := by
  change (homologyEvaluation fullBoundaryChains (actualCoefficients n e) 1
    ((fullBoundaryCochains n e).homologyπ 1 x)).hom apartmentClassFull = _
  rw [apartmentClassFull, homologyEvaluation_apply]
  congr 1
  exact HomologicalComplex.i_cyclesMk fullBoundaryChains apartmentChainFull 0 _ apartmentChainFull_boundary

/-- The corestriction `H₃(Γ(6), Res M) → H₃(G, M)` for the full-level coefficients. -/
def corG : groupHomology (restrictedCoefficients n e) 3 ⟶ groupHomology (actualCoefficients n e) 3 :=
  ModuleCat.ofHom (corN principalSix (actualCoefficients n e) 3)

/-- The map `j^G_*∘PD_∂⁻¹ : H¹(∂X̄_G; M) → H₃(X̄_G; M) = H₃(G, M)`: restriction to the neat cover, boundary
Poincaré duality, inclusion of the boundary, corestriction. -/
def fullBoundaryClassToG : (fullBoundaryCochains n e).homology 1 ⟶ groupHomology (actualCoefficients n e) 3 :=
  fullBoundaryClassToGroup n e ≫ corG n e

/-- **The right arrow at level `G`**: `z ↦ F_z(ℓ)`, the value of the Steinberg functional `Θ^G(z)` on the identity
apartment. -/
def topEvaluationG (M : Rep.{0} ℚ IntegralGL) : groupHomology M 3 →ₗ[ℚ] M :=
  (LinearMap.applyₗ (OrdinaryTopBoundaryComparison.identityApartment : OrdinaryIncidenceChains.Cycles)) ∘ₗ
    (homKGen stG M).subtype ∘ₗ (thetaG M).toLinearMap

theorem topEvaluationG_apply (M : Rep.{0} ℚ IntegralGL) (z : groupHomology M 3) :
    topEvaluationG M z = (thetaG M z : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) identityApartment := rfl

/-- The neat-level functional of the boundary image of a full-level class is `G`-equivariant. -/
theorem fullClass_isEquivOn (ω : (fullBoundaryCochains n e).homology 1) :
    IsEquivOn stG (actualCoefficients n e).ρ ⊤
      (psiGen principalSix (MulEquiv.refl principalSix) (actualCoefficients n e)
        (fullBoundaryClassToGroup n e ω)) := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective ((fullBoundaryCochains n e).homologyπ 1)).mp inferInstance ω
  intro g _ z
  rw [psiGen_apply, psiGen_apply, fullClass_ordinary]
  exact fullClass_fullEquivariant n e x g z

/-- **`G`-level duality of the boundary image**: `Θ^G(j^G_* ω)` is the neat-level functional of `j_* PD⁻¹ res ω`. -/
theorem levelG_functional (ω : (fullBoundaryCochains n e).homology 1) :
    (thetaG (actualCoefficients n e) (fullBoundaryClassToG n e ω) :
        OrdinaryIncidenceChains.Cycles →ₗ[ℚ] actualCoefficients n e) =
      psiGen principalSix (MulEquiv.refl principalSix) (actualCoefficients n e)
        (fullBoundaryClassToGroup n e ω) :=
  thetaG_corN_of_equivariant _ _ (fullClass_isEquivOn n e ω)

/-- **Lemma 3.3 at level `G`** (`eq:apartment-boundary-diagram`): for `ω ∈ H¹(∂X̄_G; M)`, the value `F_z(ℓ)` of the
top class `z = j^G_* PD_∂⁻¹ ω ∈ H₃(X̄_G; M)` on the identity apartment is the boundary pairing `⟨ω, ∂a⟩`. -/
theorem levelG_diagram (ω : (fullBoundaryCochains n e).homology 1) :
    topEvaluationG (actualCoefficients n e) (fullBoundaryClassToG n e ω) = fullBoundaryPairing n e ω := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective ((fullBoundaryCochains n e).homologyπ 1)).mp inferInstance ω
  rw [topEvaluationG_apply, levelG_functional, psiGen_apply, fullBoundaryPairing_cocycle]
  exact fullBoundaryClassToGroup_cocycle_evaluation n e x

/-! ### The level-`G` boundary homology as a subspace of the neat-level boundary homology -/

/-- Restriction of a level-`G` boundary class to the neat cover followed by boundary Poincaré duality:
`H¹(∂X̄_G; M) → H₃(∂X̄_Γ; M)`. -/
def resToBoundary : (fullBoundaryCochains n e).homology 1 ⟶
    (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3 :=
  homologyMap (boundaryRestriction n e) 1 ≫
    (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
      SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom

theorem fullBoundaryClassToGroup_eq :
    fullBoundaryClassToGroup n e = resToBoundary n e ≫
      SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 := rfl

theorem resToBoundary_injective : Function.Injective (resToBoundary n e).hom := by
  intro a b h
  apply boundaryRestriction_injective n e 1
  have := congrArg (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
    SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv.hom h
  have e1 : ∀ w, (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
      SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv.hom ((resToBoundary n e).hom w) =
      (homologyMap (boundaryRestriction n e) 1).hom w := fun w =>
    Iso.hom_inv_id_apply (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
      SymmetricSpaceBoundaryOrientation.boundaryOrientation) _
  rwa [e1, e1] at this

/-- **`H₃(∂X̄_G; 𝓜)`**: the subspace of neat-level boundary homology that is Poincaré dual to the invariant cohomology
`H¹(∂X̄_G; M)` (rational averaging identifies invariants and coinvariants). -/
def H3boundaryG : Submodule ℚ
    ((SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3) :=
  LinearMap.range (resToBoundary n e).hom

/-- **Boundary Poincaré duality at level `G`**: `PD_∂ : H₃(∂X̄_G; 𝓜) ≃ H¹(∂X̄_G; M)`. -/
def PDG : H3boundaryG n e ≃ₗ[ℚ] (fullBoundaryCochains n e).homology 1 :=
  (LinearEquiv.ofInjective (resToBoundary n e).hom (resToBoundary_injective n e)).symm

theorem PDG_symm_apply (ω : (fullBoundaryCochains n e).homology 1) :
    ((PDG n e).symm ω).1 = resToBoundary n e ω := rfl

/-- **Lemma 3.3 at level `G`, diagram form**: for `c ∈ H₃(∂X̄_G; 𝓜)`, `F_{j_* c}(ℓ) = ⟨PD_∂ c, ∂a⟩ ∈ M`. -/
theorem levelG_diagram_PD (c : H3boundaryG n e) :
    topEvaluationG (actualCoefficients n e)
        (corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 c.1)) =
      fullBoundaryPairing n e (PDG n e c) := by
  obtain ⟨ω, hω⟩ := c.2
  have hc : c = (PDG n e).symm ω := Subtype.ext hω.symm
  subst hc
  rw [LinearEquiv.apply_symm_apply]
  exact levelG_diagram n e ω

/-- The level-`G` Poincaré dual restricts to the neat-level Poincaré dual `PDboundary`. -/
theorem PDG_restrict (c : H3boundaryG n e) :
    (boundaryCohomologyIso (restrictedCoefficients n e)).hom
        (TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram.PDboundary (restrictedCoefficients n e) c.1) =
      homologyMap (boundaryRestriction n e) 1 (PDG n e c) := by
  obtain ⟨ω, hω⟩ := c.2
  have hc : c = (PDG n e).symm ω := Subtype.ext hω.symm
  subst hc
  rw [LinearEquiv.apply_symm_apply, PDG_symm_apply]
  change (boundaryCohomologyIso (restrictedCoefficients n e)).hom
    ((boundaryCohomologyIso (restrictedCoefficients n e)).inv
      ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv (resToBoundary n e ω))) = _
  rw [Iso.inv_hom_id_apply]
  change ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv
        ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom
          (homologyMap (boundaryRestriction n e) 1 ω))) = _
  rw [Iso.hom_inv_id_apply]

/-- The level-`G` value `F_z(ℓ)` of the corestriction of a full-level boundary image is its neat-level top evaluator. -/
theorem topEvaluationG_fullClass (ω : (fullBoundaryCochains n e).homology 1) :
    topEvaluationG (actualCoefficients n e) (fullBoundaryClassToG n e ω) =
      groupApartmentEvaluation (restrictedCoefficients n e) (fullBoundaryClassToGroup n e ω) := by
  rw [topEvaluationG_apply, levelG_functional, psiGen_apply]
  rfl

/-- The neat-level bottom arrow and the level-`G` bottom arrow agree on `H₃(∂X̄_G; 𝓜)`:
`⟨PD_∂ c, ∂a⟩` (library's `flatBoundaryPairing`) `= ⟨PD_∂^G c, ∂a⟩`. -/
theorem flatBoundaryPairing_PDG (c : H3boundaryG n e) :
    TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram.flatBoundaryPairing (restrictedCoefficients n e)
        (TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram.PDboundary (restrictedCoefficients n e) c.1) =
      fullBoundaryPairing n e (PDG n e c) := by
  rw [← TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram.diagram_apply]
  obtain ⟨ω, hω⟩ := c.2
  have hc : c = (PDG n e).symm ω := Subtype.ext hω.symm
  subst hc
  rw [LinearEquiv.apply_symm_apply, PDG_symm_apply]
  change groupApartmentEvaluation (restrictedCoefficients n e) (fullBoundaryClassToGroup n e ω) = _
  rw [← topEvaluationG_fullClass]
  exact levelG_diagram n e ω

open TernaryPeriodPolynomials.Argument.Lemma33.Retract in
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized in
/-- **Lemma 3.3 at level `G`, with the paper's normalization and the literal top-cell coefficient**: every
`ω ∈ H¹(∂X̄_G; M)` has a cellular top cycle `z` of the neat-level cell complex with coefficients in `Res M` such that
`j_* PD_∂⁻¹ ω = [z]` and `F_{j^G_* ω}(ℓ) = ⟨ω, ∂a⟩` is the coefficient of `z` against the normalized top-cell
generator `coeffAtT0Norm`.  This normalization uses the library's rational scale `normScalar = -d₅⁻¹`, a scale artefact, NOT the
paper's geometric local intersection number `+1`; the geometric statement is `levelG_cellular_geo` (constant `-1`, only
the sign of `T₀` free). -/
theorem levelG_cellular (ω : (fullBoundaryCochains n e).homology 1) :
    ∃ (z : (cellCoinv (restrictedCoefficients n e)).X 3)
      (hz : ((cellCoinv (restrictedCoefficients n e)).d 3 2).hom z = 0),
      fullBoundaryClassToGroup n e ω =
          cellGroupHomologyMap (restrictedCoefficients n e) 3 (cellClass (restrictedCoefficients n e) z hz) ∧
        topEvaluationG (actualCoefficients n e) (fullBoundaryClassToG n e ω) =
          (coeffAtT0Norm (restrictedCoefficients n e)).hom z ∧
        fullBoundaryPairing n e ω = (coeffAtT0Norm (restrictedCoefficients n e)).hom z := by
  obtain ⟨y, hy⟩ := cellGroupHomologyMap_surjective (restrictedCoefficients n e) (fullBoundaryClassToGroup n e ω)
  obtain ⟨z, hz, rfl⟩ := exists_cellClass (restrictedCoefficients n e) y
  have h1 : groupApartmentEvaluation (restrictedCoefficients n e) (fullBoundaryClassToGroup n e ω) =
      (coeffAtT0Norm (restrictedCoefficients n e)).hom z := by
    rw [← hy]
    exact eval_eq_coeffAtT0Norm (restrictedCoefficients n e) z hz
  refine ⟨z, hz, hy.symm, ?_, ?_⟩
  · rw [topEvaluationG_fullClass, h1]
  · rw [← levelG_diagram, topEvaluationG_fullClass, h1]

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
