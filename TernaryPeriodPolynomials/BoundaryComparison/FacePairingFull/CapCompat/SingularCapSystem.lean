module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.CapSystem
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SingularLeibniz

@[expose] public section


/-!
# The cap system of the equivariant singular chains of a `Γ`-space

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
open TernaryPoly.FreeActionLinearization
open TernaryPeriodPolynomials.Argument.TopHomology
open SphereOddDegree.AlexanderWhitney
open scoped Simplicial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {G : Type} [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- The augmentation of the singular chains: every vertex has weight one. -/
def singEps : chainRep G E 0 ⟶ 𝟙_ (Rep.{0} ℚ G) :=
  (degreeRepIso G E 0).inv ≫ ofMulActionLift (SingularSimplex E 0) (𝟙_ (Rep.{0} ℚ G))
    (fun _ => (1 : ℚ)) (fun γ _ => by simp)

theorem singEps_chainElement (σ : SingularSimplex E 0) :
    (singEps (G := G) E).hom (chainElement G E 0 σ) = (1 : ℚ) := by
  have h1 : (singEps (G := G) E).hom (chainElement G E 0 σ) =
      ((degreeRepIso G E 0).hom ≫ singEps (G := G) E).hom (MonoidAlgebra.single σ 1) := by
    rw [← degreeRepIso_hom_single]; rfl
  rw [h1]
  unfold singEps
  rw [Iso.hom_inv_id_assoc]
  exact ofMulActionLift_single _ _ _ _ σ

theorem singEps_d : equivariantD G E 1 0 ≫ singEps (G := G) E = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply chainRep_linear_ext E
  intro σ
  change (singEps (G := G) E).hom ((equivariantD G E 1 0).hom (chainElement G E 1 σ)) = 0
  rw [chainElement_d]
  simp only [map_sum, map_zsmul]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_smul]
  erw [singEps_chainElement (G := G) E, singEps_chainElement (G := G) E]
  simp

theorem singEps_counit (V : Rep.{0} ℚ G) (a : ℕ) (f : chainRep G E a ⟶ V) :
    capE E V a 0 f ≫ (V ◁ singEps (G := G) E) ≫ (ρ_ V).hom = f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply chainRep_linear_ext E
  intro σ
  have hf : frontSimplex E a 0 σ = σ := by
    unfold frontSimplex
    have : frontFace a 0 = 𝟙 (⦋a⦌ : SimplexCategory) := by ext x : 3; rfl
    rw [this]
    simp
  change (ρ_ V).hom.hom ((V ◁ singEps (G := G) E).hom ((capE E V a 0 f).hom (chainElement G E (a+0) σ))) =
    f.hom (chainElement G E a σ)
  rw [capE_chainElement]
  unfold capElem
  rw [hf]
  rw [Rep.hom_whiskerLeft, Representation.IntertwiningMap.lTensor_apply, singEps_chainElement]
  simp [rightUnitor]

/-- The Alexander-Whitney cap system of the equivariant singular chains. -/
def singCapSystem : CapSystem (equivariantChains G E) where
  cap {W} a b _hb q := capE E W a q b
  intertwine {W} a b hb q := capE_intertwine E W a q b hb
  eps := singEps E
  eps_d := singEps_d E
  counit {W} a b _hb := singEps_counit E W a b

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
