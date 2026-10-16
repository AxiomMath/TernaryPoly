module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ShapiroCut
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.DiagCup
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.StabilizerRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ClsS

@[expose] public section


/-!
# The nerve-versus-bar comparison for the Shapiro coordinate `faceCoord` (all degrees `m + 1`)

Formalized by Claude Sonnet 5.5.

`faceCoord_clsS_eq`: for a cocycle `θ` of the Hom complex of the permutation resolution `prodComplex Γ V Z`, the Shapiro coordinate at a `T`-fixed label `z` of `[θ]` is the class
`groupCohomology.π` of the inhomogeneous cocycle `x ↦ θ[((x₁⋯xᵢ) v₀)ᵢ ; z]` of `T` (`barCochain`; `barCochain_cocycle` is the cocycle property).  This is the bridge between the
flag 3-cochains of the corner evaluation (`GammaNFaceFactor.CornerAuto`) and explicit inhomogeneous cochains of the flag stabilizers, where the cup products of `CupProduct`/`DiagCup12` live.
-/

open CategoryTheory Finsupp
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.EquivariantSingularSmall

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

theorem inhomIso_inv_apply {G : Type} [Group G] (A : Rep.{0} ℚ G) (k : ℕ)
    (c : (Rep.barComplex ℚ G).X k ⟶ A) (x : Fin k → G) :
    ((groupCohomology.inhomogeneousCochainsIso A).inv.f k).hom c x =
      c.hom (single x (MonoidAlgebra.single 1 1)) := by
  rfl

theorem gisoBar_inv_eq {G : Type} [Group G] (A : Rep.{0} ℚ G) (n : ℕ) :
    (gisoBar A n).inv =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).inv n :=
  Iso.inv_ext (by
    erw [gisoBar_hom, ← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id,
      HomologicalComplex.homologyMap_id]
    rfl)

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (T : Subgroup Γ)
  (W : Rep.{0} ℚ Γ) (v₀ : V) (z : Z) (hz : ∀ g : T, g • z = z)

include hz

theorem stabCoord_inhom_apply {k : ℕ} (θ : (prodComplex Γ V Z).X k ⟶ W) (x : Fin k → T) :
    ((groupCohomology.inhomogeneousCochainsIso (Rep.res T.subtype W)).inv.f k).hom
        (((stabCoord T W v₀ z hz).f k).hom θ) x = barCochain T v₀ z θ x := by
  exact (inhomIso_inv_apply (Rep.res T.subtype W) k _ x).trans (stabCoord_single T W v₀ z hz k θ x)

/-- The bar cochain of a cocycle is an inhomogeneous cocycle. -/
theorem barCochain_cocycle {m : ℕ} (θ : (prodComplex Γ V Z).X (m + 1) ⟶ W)
    (hθ : ((homCochains (prodComplex Γ V Z) W).d (m + 1) (m + 1 + 1)).hom θ = 0) :
    inhomogeneousCochains.d (Rep.res T.subtype W) (m + 1)
      (fun x => barCochain T v₀ z θ x) = 0 := by
  let φ := stabCoord T W v₀ z hz
  let ψ := (groupCohomology.inhomogeneousCochainsIso (Rep.res T.subtype W)).inv
  have h1 := mapS_cocycle (homCochains (prodComplex Γ V Z) W) (φ ≫ ψ) θ hθ
  have h2 : ((φ ≫ ψ).f (m + 1)).hom θ = fun x => barCochain T v₀ z θ x := by
    funext x
    exact stabCoord_inhom_apply T W v₀ z hz θ x
  rw [h2] at h1
  simpa using h1

/-- **The nerve-versus-bar comparison in degree `m + 1`.**  The Shapiro coordinate at `z` of the class of a cocycle `θ` of the permutation resolution is the
class of the inhomogeneous cocycle `x ↦ θ [((x₁⋯xᵢ) v₀)ᵢ ; z]` of the stabilizer. -/
theorem faceCoord_clsS_eq {m : ℕ} (θ : (prodComplex Γ V Z).X (m + 1) ⟶ W)
    (hθ : ((homCochains (prodComplex Γ V Z) W).d (m + 1) (m + 1 + 1)).hom θ = 0) :
    (faceCoord T W v₀ z hz (m + 1)).hom (clsS (homCochains (prodComplex Γ V Z) W) θ hθ) =
      (groupCohomology.π (Rep.res T.subtype W) (m + 1)).hom
        (groupCohomology.cocyclesMk (fun x => barCochain T v₀ z θ x)
          (barCochain_cocycle T W v₀ z hz θ hθ)) := by
  have hc1 := mapS_cocycle (homCochains (prodComplex Γ V Z) W) (stabCoord T W v₀ z hz) θ hθ
  have hc2 := mapS_cocycle (homCochains (Rep.barComplex ℚ T) (Rep.res T.subtype W))
    (groupCohomology.inhomogeneousCochainsIso (Rep.res T.subtype W)).inv _ hc1
  have h1 := clsS_map (homCochains (prodComplex Γ V Z) W) (stabCoord T W v₀ z hz) θ hθ hc1
  have h3 := clsS_map (homCochains (Rep.barComplex ℚ T) (Rep.res T.subtype W))
    (groupCohomology.inhomogeneousCochainsIso (Rep.res T.subtype W)).inv _ hc1 hc2
  rw [faceCoord_eq_homologyMap_stabCoord, ModuleCat.hom_comp, LinearMap.comp_apply, gisoBar_inv_eq, h1]
  refine h3.trans ?_
  have e1 : (((groupCohomology.inhomogeneousCochainsIso (Rep.res T.subtype W)).inv.f (m + 1)).hom
      (((stabCoord T W v₀ z hz).f (m + 1)).hom θ)) = fun x => barCochain T v₀ z θ x := by
    funext x
    exact stabCoord_inhom_apply T W v₀ z hz θ x
  unfold clsS
  congr 1
  apply iCyclesS_injective
  rw [iCycles_cycleS]
  refine e1.trans ?_
  exact (groupCohomology.iCocycles_mk (G := T) (A := Rep.res T.subtype W) (fun x => barCochain T v₀ z θ x) (barCochain_cocycle T W v₀ z hz θ hθ)).symm

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
