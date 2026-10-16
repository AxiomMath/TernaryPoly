module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Shapiro
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.ThetaEquivariance

@[expose] public section


/-!
# The geometric action of `GL₃(ℤ)` on the local chains of the boundary, and equivariance of `j_*`

Formalized by Claude Sonnet 5.5.

Paper: "take coinvariants in homology and invariants in cohomology under the finite covering group".

For a `GL₃(ℤ)`-representation `V₀` and `W = Res_{Γ(6)} V₀`, the geometric local chains of the boundary of the neat cover,
`boundaryLocalChains W`, are isomorphic (`ibd`) to the `Γ(6)`-coinvariants `(W ⊗ Sing(∂X̃))_{Γ(6)}` of the `G`-complex
`Ybd V₀ = V₀ ⊗ Sing(∂X̃)`.  `bAct g` is the diagonal action of `g` (on simplices of the boundary cover and on coefficients),
transported along `ibd`: the deck-group action of `G/Γ(6)` on the singular chains of the boundary of the neat cover with
transport of the coefficient system.  It is a chain action (`bAct_mul`, `bAct_one`) on which `Γ(6)` acts trivially
(`bAct_of_mem`), the inclusion of the boundary is equivariant for it and for the action `gAct` on the chains of the bordification
(`boundaryInclusionMap_equivariant`), and `j_* = boundaryToGroup` intertwines it with Mathlib's conjugation action on group
homology (`boundaryToGroup_equivariant`).
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.ModThreeGoodAction TernaryPoly.SingularLocalHomology TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.EquivariantSingularResolution
open TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceBordifiedQuotient
open TernaryPeriodPolynomials.Argument.DualityEquivariance
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

variable (V₀ : Rep.{0} ℚ IntegralGL)

/-- The `G`-complex `M ⊗ Sing(∂X̃)` whose `Γ(6)`-coinvariants are the geometric local chains of the boundary and whose
`G`-coinvariants are the equivariant chains of `∂X̄_G` with coefficients in `M`. -/
abbrev Ybd : ChainComplex (Rep.{0} ℚ IntegralGL) ℕ := Ygeo (TopCat.of BoundaryCover) V₀

/-- **The geometric action of `g ∈ GL₃(ℤ)` on the local chains of the boundary of the neat cover**: transported along
`chainIso` from the diagonal action (`g` on simplices of the boundary cover, `ρ(g)` on coefficients). -/
def ibd : boundaryLocalChains (Rep.res principalSix.subtype V₀) ≅
    coinvariantChains principalSix (TopCat.of BoundaryCover) (Rep.res principalSix.subtype V₀) :=
  (chainIso boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀)).symm

/-- The bordification analogue of `ibd`. -/
def ibord : bordifiedLocalChains (Rep.res principalSix.subtype V₀) ≅
    coinvariantChains principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) :=
  (chainIso wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀)).symm

/-- The diagonal action on the coinvariant chains of the boundary cover. -/
def GYb (g : IntegralGL) : coinvariantChains principalSix (TopCat.of BoundaryCover) (Rep.res principalSix.subtype V₀) ⟶
    coinvariantChains principalSix (TopCat.of BoundaryCover) (Rep.res principalSix.subtype V₀) :=
  GY principalSix (Ybd V₀) g

/-- The diagonal action on the coinvariant chains of the bordification. -/
def GYg (g : IntegralGL) : coinvariantChains principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) ⟶
    coinvariantChains principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) :=
  GY principalSix (Ygeo (TopCat.of Glued) V₀) g

def bAct (g : IntegralGL) : boundaryLocalChains (Rep.res principalSix.subtype V₀) ⟶
    boundaryLocalChains (Rep.res principalSix.subtype V₀) :=
  (ibd V₀).hom ≫ GYb V₀ g ≫ (ibd V₀).inv

section GYlemmas

variable {K : Type} [Group K] (N : Subgroup K) [N.Normal] (Y : ChainComplex (Rep.{0} ℚ K) ℕ)

theorem GY_mul' (g h : K) : GY N Y (g * h) = GY N Y h ≫ GY N Y g := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  simp only [GY, NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f, gamNat]
  rw [gamMap_mul]
  rfl

theorem GY_one' : GY N Y 1 = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  simp only [GY, NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f, gamNat,
    ModuleCat.hom_id]
  exact gamMap_of_mem N (Y.X i).ρ ⟨1, N.one_mem⟩

theorem GY_of_mem' (n : N) : GY N Y n.1 = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  simp only [GY, NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f, gamNat,
    ModuleCat.hom_id]
  exact gamMap_of_mem N (Y.X i).ρ n

end GYlemmas

theorem bAct_mul (g h : IntegralGL) : bAct V₀ (g * h) = bAct V₀ h ≫ bAct V₀ g := by
  unfold bAct
  have : GYb V₀ (g * h) = GYb V₀ h ≫ GYb V₀ g := GY_mul' _ _ _ _
  rw [this]
  simp

theorem bAct_one : bAct V₀ 1 = 𝟙 _ := by
  unfold bAct
  have : GYb V₀ 1 = 𝟙 _ := GY_one' _ _
  rw [this]
  simp

/-- The deck group `Γ(6)` acts trivially on the coinvariant chains. -/
theorem bAct_of_mem (γ : principalSix) : bAct V₀ γ.1 = 𝟙 _ := by
  unfold bAct
  have : GYb V₀ γ.1 = 𝟙 _ := GY_of_mem' _ _ γ
  rw [this]
  simp

/-- The geometric action on the local chains of the bordification (the one of `conj_S1`). -/
def gAct (g : IntegralGL) : bordifiedLocalChains (Rep.res principalSix.subtype V₀) ⟶
    bordifiedLocalChains (Rep.res principalSix.subtype V₀) :=
  epsLoc g V₀ ≫ Lspace g (Rep.res principalSix.subtype V₀)

/-- The inclusion of the boundary is equivariant for the geometric actions. -/
theorem boundaryInclusionMap_equivariant (g : IntegralGL) :
    boundaryInclusionMap (Rep.res principalSix.subtype V₀) ≫ gAct V₀ g =
      bAct V₀ g ≫ boundaryInclusionMap (Rep.res principalSix.subtype V₀) := by
  have h := epsLoc_Lspace_eq g V₀
  have hGY : coinvariantSpaceMap boundaryInclusion boundaryInclusion_equivariant
        (Rep.res principalSix.subtype V₀) ≫ GYg V₀ g =
      GYb V₀ g ≫ coinvariantSpaceMap boundaryInclusion boundaryInclusion_equivariant
        (Rep.res principalSix.subtype V₀) :=
    by
    apply HomologicalComplex.hom_ext
    intro n
    apply Rep.coinvariantsTensor_hom_ext
    ext v c
    let V := Rep.res principalSix.subtype V₀
    have key := Rep.hom_comm_apply
      ((SingularCoverNaturality.chainMap (G := IntegralGL) boundaryInclusion
        (fun g x => rfl)).f n) g c
    change Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of Glued) n) (V₀.ρ g v)
        (chainAction IntegralGL (TopCat.of Glued) n g
          (((SingularCoverNaturality.chainMap boundaryInclusion boundaryInclusion_equivariant).f n).hom c)) =
      Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of Glued) n) (V₀.ρ g v)
        (((SingularCoverNaturality.chainMap boundaryInclusion boundaryInclusion_equivariant).f n).hom
          (chainAction IntegralGL (TopCat.of ↑BoundaryCover) n g c))
    exact congrArg _ key.symm
  have hI : boundaryInclusionMap (Rep.res principalSix.subtype V₀) = (ibd V₀).hom ≫
      coinvariantSpaceMap boundaryInclusion boundaryInclusion_equivariant (Rep.res principalSix.subtype V₀) ≫
        (ibord V₀).inv := rfl
  have hG : gAct V₀ g = (ibord V₀).hom ≫ diagCo g V₀ ≫ (ibord V₀).inv := h
  rw [hI, hG]
  unfold bAct
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have : diagCo g V₀ = GYg V₀ g := rfl
  rw [this]
  have hGY' : coinvariantSpaceMap boundaryInclusion boundaryInclusion_equivariant
        (Rep.res principalSix.subtype V₀) ≫ GYg V₀ g ≫ (ibord V₀).inv =
      GYb V₀ g ≫ coinvariantSpaceMap boundaryInclusion boundaryInclusion_equivariant
        (Rep.res principalSix.subtype V₀) ≫ (ibord V₀).inv := by
    rw [← Category.assoc, hGY, Category.assoc]
  rw [hGY']

/-- **Equivariance of `j_* : H₃(∂X̄_Γ; W) → H₃(Γ(6), W)`**: the map `boundaryToGroup` intertwines the geometric action `bAct`
of `GL₃(ℤ)` on boundary homology with Mathlib's conjugation action `c_g` on group homology. -/
theorem boundaryToGroup_equivariant (g : IntegralGL) :
    homologyMap (bAct V₀ g) 3 ≫
        SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3 =
      SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype V₀) 3 ≫
        groupHomology.map (conjN principalSix g) (conjRep principalSix V₀ g) 3 := by
  have hc := conj_S1 g V₀
  have hinv : homologyMap (gAct V₀ g) 3 ≫
      (bordifiedGroupLocalHomologyIso (Rep.res principalSix.subtype V₀) 3).inv =
      (bordifiedGroupLocalHomologyIso (Rep.res principalSix.subtype V₀) 3).inv ≫
        groupHomology.map (conjN principalSix g) (conjRep principalSix V₀ g) 3 := by
    have hc' : groupHomology.map (conjN principalSix g) (conjRep principalSix V₀ g) 3 ≫
        (bordifiedGroupLocalHomologyIso (Rep.res principalSix.subtype V₀) 3).hom =
        (bordifiedGroupLocalHomologyIso (Rep.res principalSix.subtype V₀) 3).hom ≫
          homologyMap (gAct V₀ g) 3 := hc
    have e := (Iso.eq_comp_inv (bordifiedGroupLocalHomologyIso (Rep.res principalSix.subtype V₀) 3)).mpr hc'
    rw [e]
    simp
  unfold SymmetricSpaceBoundaryDuality.boundaryToGroup
  rw [← Category.assoc, ← homologyMap_comp, ← boundaryInclusionMap_equivariant, homologyMap_comp,
    Category.assoc, hinv, Category.assoc]

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
