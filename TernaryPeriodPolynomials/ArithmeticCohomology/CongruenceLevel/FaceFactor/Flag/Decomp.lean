module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.FunctionalDecomp
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ShapiroProductS
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ClsS
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Stab

@[expose] public section


/-!
# Decomposition of the corner functional over the flag orbits (item (i))

Formalized by Claude Sonnet 5.5.

Let `x` be a 3-chain of the flag complex `A = prodComplex Γ(6) RationalGL3 Flag` whose boundary pairs to zero with every 2-cochain (this holds for the corner chain `pA 3 v` of a coinvariant cycle, by
`PushCone.corner_cycle`).  Then the functional `θ ↦ θ(x)` on 3-cocycles factors through the cohomology, which is the product over the flag orbits `o` of the groups `H³(Stab o.out; W)`
(the degree-three Shapiro bijection), hence is the sum of functionals `φ_o` on the factors: `θ(x) = ∑_o φ_o (faceCoord_o [θ])` (`corner_functional_decomp`).
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.EquivariantSingularSmall
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

variable (W : Rep.{0} ℚ Γ6)

/-- The product of the degree-three Shapiro coordinates over the flag orbits, as a linear map. -/
def flagCoordPi : (homCochains (prodComplex Γ6 RationalGL3 Flag) W).homology 3 →ₗ[ℚ]
    (∀ o : labelOrbits Γ6 Flag, groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype W) 3) :=
  LinearMap.pi fun o => (faceCoord (stabilizer Γ6 o.out) W (1 : RationalGL3) o.out (fun g => g.2) 3).hom

theorem flagCoordPi_bijective : Function.Bijective (flagCoordPi W) :=
  faceCoord_product_bijective_succ 2 (1 : RationalGL3) vertexAction_free' W

/-- **The corner functional decomposes over the flag orbits.** -/
theorem corner_functional_decomp [Fintype (labelOrbits Γ6 Flag)]
    (x : (prodComplex Γ6 RationalGL3 Flag).X 3)
    (hx : ∀ φ : (prodComplex Γ6 RationalGL3 Flag).X 2 ⟶ 𝟙_ (Rep.{0} ℚ Γ6),
      φ.hom ((prodComplex Γ6 RationalGL3 Flag).d 3 2 x) = 0) :
    ∃ φ : ∀ o : labelOrbits Γ6 Flag, groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 →ₗ[ℚ] ℚ,
      ∀ (θ : (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))).X (2 + 1))
        (hθ : ((homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))).d (2 + 1) (2 + 1 + 1)).hom θ = 0),
        θ.hom x = ∑ o, φ o (flagCoordPi (𝟙_ (Rep.{0} ℚ Γ6)) (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag)
          (𝟙_ (Rep.{0} ℚ Γ6))) θ hθ) o) := by
  classical
  set K := homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)) with hK
  let Z : Submodule ℚ (K.X (2 + 1)) := LinearMap.ker (K.d (2 + 1) (2 + 1 + 1)).hom
  let cl : Z →ₗ[ℚ] K.homology (2 + 1) :=
    { toFun := fun a => clsS K a.1 (LinearMap.mem_ker.mp a.2)
      map_add' := fun a b => clsS_add K a.1 b.1 (LinearMap.mem_ker.mp a.2) (LinearMap.mem_ker.mp b.2) _
      map_smul' := fun r a => clsS_smul K r a.1 (LinearMap.mem_ker.mp a.2) _ }
  let ev : K.X (2 + 1) →ₗ[ℚ] ℚ :=
    { toFun := fun θ => θ.hom x
      map_add' := fun a b => rfl
      map_smul' := fun r a => rfl }
  let T : Z →ₗ[ℚ] ℚ := ev.comp Z.subtype
  have hsurj : Function.Surjective cl := by
    intro y
    obtain ⟨a, ha, hy⟩ := exists_clsS K y
    exact ⟨⟨a, LinearMap.mem_ker.mpr ha⟩, hy⟩
  have hker : LinearMap.ker cl ≤ LinearMap.ker T := by
    intro a ha
    have h0 : clsS K a.1 (LinearMap.mem_ker.mp a.2) = 0 := ha
    obtain ⟨b, hb⟩ := (clsS_eq_zero_iff K a.1 (LinearMap.mem_ker.mp a.2)).1 h0
    show a.1.hom x = 0
    rw [← hb]
    exact hx b
  let Ψ : K.homology (2 + 1) →ₗ[ℚ] ℚ :=
    ((LinearMap.ker cl).liftQ T hker).comp (cl.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hΨ : ∀ a : Z, Ψ (cl a) = T a := by
    intro a
    simp only [Ψ, LinearMap.comp_apply]
    have : (cl.quotKerEquivOfSurjective hsurj).symm (cl a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp [this]
  let e := LinearEquiv.ofBijective (flagCoordPi (𝟙_ (Rep.{0} ℚ Γ6))) (flagCoordPi_bijective _)
  let Φ : (∀ o : labelOrbits Γ6 Flag, groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3) →ₗ[ℚ] ℚ :=
    Ψ.comp e.symm.toLinearMap
  refine ⟨fun o => Φ.comp (LinearMap.single ℚ (fun o : labelOrbits Γ6 Flag =>
    groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3) o), fun θ hθ => ?_⟩
  have h1 : θ.hom x = Φ (flagCoordPi (𝟙_ (Rep.{0} ℚ Γ6)) (clsS K θ hθ)) := by
    have : Φ (flagCoordPi (𝟙_ (Rep.{0} ℚ Γ6)) (clsS K θ hθ)) = Ψ (clsS K θ hθ) := by
      simp [Φ, e]
    rw [this]
    exact (hΨ ⟨θ, LinearMap.mem_ker.mpr hθ⟩).symm
  rw [h1]
  refine (pi_functional_decomp Φ _).trans ?_
  rfl

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
