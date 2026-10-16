module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.ResolutionZ
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Assembly
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.HSIso

@[expose] public section


/-!
# The Hochschild-Serre isomorphism `hsFarey`, read on an arbitrary projective resolution

Formalized by Claude Sonnet 5.5.

`hsFarey_apply`: `hsFarey` unfolds to the composite of `groupHomologyZIso`, `thmAEquiv (ZP U A)`, `kerNatEquiv`, `kerInflEquiv`
and `H1Iso`.  `hsFarey_apply_ZR`: the same value is obtained from `thmAEquiv (ZR U R A)` for any projective resolution `R` of the
trivial `P`-module, applied to `groupHomologyZIsoR`, with `e` transported to `H₂(Z_R)` by `eR` (naturality of `thmAEquiv`,
`thmAEquiv_natural`, and compatibility `groupHomologyZIso_compat` of the two identifications with `H_3(P, A)`).
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)

theorem hsFarey_apply (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π)
    (hker : (π.ker : Set (P ⧸ U)).Finite)
    [Projective (Rep.res π P1)] [Projective (Rep.res π P0)]
    (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : (ZP U A).homology 2 ≅ Rep.res π D) (x : groupHomology A 3) :
    hsFarey U A π hπ hker hU3 D e x =
      (H1Iso D).toLinearEquiv.symm
        (kerInflEquiv π hπ d1 D
          (kerNatEquiv (FXmap (Rep.resMap π d1)) e
            (thmAEquiv (ZP U A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
              (ZP_projective U A) (sesQ_shortExact π) (isZero_ZP_homology U A 3 hU3)
              ((groupHomologyZIso U A 3).hom.hom x)))) := by
  rfl

variable (R : ProjectiveResolution (Rep.trivial ℚ P ℚ))

/-- `e` transported to `H₂(Z_R)`. -/
def eR {Γ : Type} [Group Γ] (π : P ⧸ U →* Γ) (D : Rep.{0} ℚ Γ) (e : (ZP U A).homology 2 ≅ Rep.res π D) :
    (ZR U R A).homology 2 ≅ Rep.res π D :=
  (asIso (HomologicalComplex.homologyMap (fZ U R A) 2)).symm ≪≫ e

theorem kerNat_eR {Γ : Type} [Group Γ] (π : P ⧸ U →* Γ) (D : Rep.{0} ℚ Γ)
    (e : (ZP U A).homology 2 ≅ Rep.res π D) {X Y : Rep.{0} ℚ (P ⧸ U)} (d : X ⟶ Y)
    (w : LinearMap.ker ((FXmap d).app ((ZP U A).homology 2)).hom) :
    ((kerNatEquiv (FXmap d) (eR U A R π D e)
        (homologyKerMap (fZ U R A) X Y d w) : LinearMap.ker ((FXmap d).app (Rep.res π D)).hom) :
          (FX X).obj (Rep.res π D)) =
      (kerNatEquiv (FXmap d) e w : LinearMap.ker ((FXmap d).app (Rep.res π D)).hom) := by
  change ((FX X).map (eR U A R π D e).hom).hom (((FX X).map (HomologicalComplex.homologyMap (fZ U R A) 2)).hom
      (w : (FX X).obj ((ZP U A).homology 2))) = ((FX X).map e.hom).hom (w : (FX X).obj ((ZP U A).homology 2))
  rw [← ModuleCat.comp_apply, ← Functor.map_comp]
  congr 2
  simp [eR]

theorem hsFarey_apply_ZR (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π)
    (hker : (π.ker : Set (P ⧸ U)).Finite)
    [Projective (Rep.res π P1)] [Projective (Rep.res π P0)]
    (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (D : Rep.{0} ℚ IntegralGL)
    (e : (ZP U A).homology 2 ≅ Rep.res π D) (x : groupHomology A 3) :
    hsFarey U A π hπ hker hU3 D e x =
      (H1Iso D).toLinearEquiv.symm
        (kerInflEquiv π hπ d1 D
          (kerNatEquiv (FXmap (Rep.resMap π d1)) (eR U A R π D e)
            (thmAEquiv (ZR U R A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π)
              (resD1_epsQ π) (ZR_projective U R A) (sesQ_shortExact π)
              (isZero_ZR_homology_of_group U R A 3 hU3)
              ((groupHomologyZIsoR U R A 3).hom.hom x)))) := by
  rw [hsFarey_apply]
  congr 2
  apply Subtype.ext
  have hc := congrArg (fun m => m.hom x) (groupHomologyZIso_compat U R A 3)
  change (HomologicalComplex.homologyMap (CxMapZ (fZ U R A) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))) 3).hom
      ((groupHomologyZIso U A 3).hom.hom x) = (groupHomologyZIsoR U R A 3).hom.hom x at hc
  rw [← hc]
  have hn := thmAEquiv_natural (fZ U R A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π)
    (resD1_epsQ π) (sesQ_shortExact π) (ZP_projective U A) (ZR_projective U R A)
    (isZero_ZP_homology U A 3 hU3) (isZero_ZR_homology_of_group U R A 3 hU3)
    ((groupHomologyZIso U A 3).hom.hom x)
  have hn' : thmAEquiv (ZR U R A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π)
      (resD1_epsQ π) (ZR_projective U R A) (sesQ_shortExact π)
      (isZero_ZR_homology_of_group U R A 3 hU3)
      ((HomologicalComplex.homologyMap (CxMapZ (fZ U R A) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))) 3).hom
        ((groupHomologyZIso U A 3).hom.hom x)) =
      homologyKerMap (fZ U R A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1)
        (thmAEquiv (ZP U A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π)
          (resD1_epsQ π) (ZP_projective U A) (sesQ_shortExact π) (isZero_ZP_homology U A 3 hU3)
          ((groupHomologyZIso U A 3).hom.hom x)) := Subtype.ext hn
  rw [hn']
  exact (kerNat_eR U A R π D e (Rep.resMap π d1) _).symm

end TernaryPeriodPolynomials.Argument.HochschildSerre
