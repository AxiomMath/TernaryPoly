module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.FiniteIndex
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.AbsCoinv
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Coinvariants

@[expose] public section


/-!
# The paper's equivariant quotient `∂X̄_H` for an intermediate level `Γ(6) ≤ H ≤ GL₃(ℤ)`: chain-level coinvariants

Formalized by Claude Sonnet 5.5.

Geometry at the neat level `Γ(6)`, then coinvariants in homology under the finite covering group.  For a
`GL₃(ℤ)`-module `V₀` and a subgroup `H ≥ Γ(6)`, `QbdH H V₀ = H₃((V₀ ⊗ Sing ∂X̃)_H)` is the homology of the `H`-coinvariants of the
singular boundary chains (`YH` is `Ybd V₀` restricted to `H`).  `trCx` identifies the `Γ(6)`-in-`H` coinvariant complex with the `Γ(6)`-coinvariant complex (same quotient of the same module), `qBdH` is the quotient map from the neat-level boundary homology,
`qBdH_surjective`, `qBdH_ker` (kernel = kernel of the `H/Γ(6)`-average `avgBdH` of the geometric action `bAct`), `qBdH_bAct`.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.RationalCohomologyDescent
  TernaryPoly.SingularLocalHomology TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryCone
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open Representation
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Transport

variable (H : Subgroup IntegralGL) (V₀ : Rep.{0} ℚ IntegralGL)

/-- The boundary chains `V₀ ⊗ Sing ∂X̃` restricted to the level `H`. -/
abbrev YH : ChainComplex (Rep.{0} ℚ ↥H) ℕ :=
  ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Ybd V₀)

theorem ker_NH_eq (hH : principalSix ≤ H) (Y : Rep.{0} ℚ IntegralGL) :
    Coinvariants.ker ((Y.ρ.comp H.subtype).comp (NH H).subtype) =
      Coinvariants.ker (Y.ρ.comp principalSix.subtype) := by
  unfold Coinvariants.ker
  congr 1
  ext x
  constructor
  · rintro ⟨⟨g, v⟩, rfl⟩
    exact ⟨(eH H hH g, v), rfl⟩
  · rintro ⟨⟨γ, v⟩, rfl⟩
    exact ⟨((eH H hH).symm γ, v), rfl⟩

/-- The coinvariants of `Y` for `Γ(6)`-in-`H` and for `Γ(6)` are the same quotient. -/
def trObj (hH : principalSix ≤ H) (Y : Rep.{0} ℚ IntegralGL) :
    (cN (NH H)).obj ((Rep.resFunctor H.subtype).obj Y) ≅ (cN principalSix).obj Y :=
  (Submodule.quotEquivOfEq _ _ (ker_NH_eq H hH Y)).toModuleIso

theorem trObj_mk (hH : principalSix ≤ H) (Y : Rep.{0} ℚ IntegralGL) (v : Y) :
    (trObj H hH Y).hom (Coinvariants.mk _ v) = Coinvariants.mk _ v := rfl

/-- **The `Γ(6)`-in-`H` coinvariant complex of `Res_H(V₀ ⊗ Sing ∂X̃)` is the `Γ(6)`-coinvariant complex.** -/
def trCx (hH : principalSix ≤ H) : CxN (NH H) (YH H V₀) ≅ CxN principalSix (Ybd V₀) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => trObj H hH ((Ybd V₀).X n)) fun i j _ => by
    apply ModuleCat.hom_ext
    apply Coinvariants.hom_ext
    apply LinearMap.ext
    intro v
    rfl

theorem trCx_mk (hH : principalSix ≤ H) (n : ℕ) (v : (Ybd V₀).X n) :
    ((trCx H V₀ hH).hom.f n).hom (Coinvariants.mk _ v) = Coinvariants.mk _ v := rfl

theorem trCx_GY (hH : principalSix ≤ H) (g : ↥H) :
    GY principalSix (Ybd V₀) g.1 ≫ (trCx H V₀ hH).inv =
      (trCx H V₀ hH).inv ≫ GY (NH H) (YH H V₀) g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Coinvariants.hom_ext
  apply LinearMap.ext
  intro v
  rfl

end Transport

section Objects

variable (H : Subgroup IntegralGL) (hH : principalSix ≤ H) (V₀ : Rep.{0} ℚ IntegralGL)

/-- **The paper's `H₃(∂X̄_H; 𝓜)`**: the homology of the `H`-coinvariants of `V₀ ⊗ Sing(∂X̃)`
(`H` acting diagonally on the simplices of the boundary cover and on the coefficients). -/
abbrev QbdH : ModuleCat ℚ := (CxK (YH H V₀)).homology 3

/-- `ibd` with its target displayed as the `Γ(6)`-coinvariant complex of `Ybd V₀`. -/
def ibdC : boundaryLocalChains (Rep.res principalSix.subtype V₀) ≅ CxN principalSix (Ybd V₀) := ibd V₀

theorem bAct_eq (g : IntegralGL) : bAct V₀ g = (ibdC V₀).hom ≫ GY principalSix (Ybd V₀) g ≫ (ibdC V₀).inv := rfl

/-- The neat-level boundary chains as the `Γ(6)`-in-`H` coinvariant complex. -/
def ibdH : boundaryLocalChains (Rep.res principalSix.subtype V₀) ≅ CxN (NH H) (YH H V₀) :=
  ibdC V₀ ≪≫ (trCx H V₀ hH).symm

theorem ibdH_hom : (ibdH H hH V₀).hom = (ibdC V₀).hom ≫ (trCx H V₀ hH).inv := rfl

/-- Neat-level boundary homology as the homology of the `Γ(6)`-in-`H` coinvariant complex. -/
def jBdH : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3 ≅
    (CxN (NH H) (YH H V₀)).homology 3 :=
  homologyMapIso (ibdH H hH V₀) 3

/-- The quotient map `H₃(∂X̄_Γ(6); 𝓜) → H₃(∂X̄_H; 𝓜)`. -/
def qBdH : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3 ⟶ QbdH H V₀ :=
  (jBdH H hH V₀).hom ≫ homologyMap (QY (NH H) (YH H V₀)) 3

/-- The averaging projector of the neat-level boundary homology for the geometric action of `H/Γ(6)`. -/
def avgBdH : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3 →ₗ[ℚ]
    (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3 :=
  ((Fintype.card (↥H ⧸ NH H) : ℚ)⁻¹) •
    ∑ x : ↥H ⧸ NH H, (homologyMap (bAct V₀ x.out.1) 3).hom

theorem jBdH_bAct (g : ↥H)
    (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    (jBdH H hH V₀).hom (homologyMap (bAct V₀ g.1) 3 c) =
      homologyMap (GY (NH H) (YH H V₀) g) 3 ((jBdH H hH V₀).hom c) := by
  have h : bAct V₀ g.1 ≫ (ibdH H hH V₀).hom = (ibdH H hH V₀).hom ≫ GY (NH H) (YH H V₀) g := by
    rw [ibdH_hom, bAct_eq]
    have := trCx_GY H V₀ hH g
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, this, Category.assoc]
  have h2 : homologyMap (bAct V₀ g.1) 3 ≫ homologyMap (ibdH H hH V₀).hom 3 =
      homologyMap (ibdH H hH V₀).hom 3 ≫ homologyMap (GY (NH H) (YH H V₀) g) 3 := by
    rw [← homologyMap_comp, ← homologyMap_comp, h]
  exact ConcreteCategory.congr_hom h2 c

theorem jBdH_avg (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    (jBdH H hH V₀).hom (avgBdH H V₀ c) = avgH (NH H) (YH H V₀) 3 ((jBdH H hH V₀).hom c) := by
  unfold avgBdH avgH
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  exact jBdH_bAct H hH V₀ x.out c

theorem card_ne_zero_NH : (Fintype.card (↥H ⧸ NH H) : ℚ) ≠ 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero

theorem qBdH_surjective : Function.Surjective (qBdH H hH V₀).hom := by
  intro y
  obtain ⟨z, hz⟩ := descent_surjective (NH H) (YH H V₀) 3 (card_ne_zero_NH H) y
  refine ⟨(jBdH H hH V₀).inv z, ?_⟩
  change (homologyMap (QY (NH H) (YH H V₀)) 3).hom ((jBdH H hH V₀).hom ((jBdH H hH V₀).inv z)) = y
  rw [Iso.inv_hom_id_apply]
  exact hz

/-- `H₃(∂X̄_Γ(6)) → H₃(∂X̄_H)` kills exactly the kernel of the `H/Γ(6)`-average of the geometric action. -/
theorem qBdH_ker (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    (qBdH H hH V₀).hom c = 0 ↔ avgBdH H V₀ c = 0 := by
  change (homologyMap (QY (NH H) (YH H V₀)) 3).hom ((jBdH H hH V₀).hom c) = 0 ↔ _
  rw [descent_ker (NH H) (YH H V₀) 3 (card_ne_zero_NH H), ← jBdH_avg]
  constructor
  · intro h
    exact (ConcreteCategory.bijective_of_isIso (jBdH H hH V₀).hom).injective (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

theorem qBdH_bAct (g : ↥H) (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    (qBdH H hH V₀).hom (homologyMap (bAct V₀ g.1) 3 c) = (qBdH H hH V₀).hom c := by
  change (homologyMap (QY (NH H) (YH H V₀)) 3).hom ((jBdH H hH V₀).hom (homologyMap (bAct V₀ g.1) 3 c)) = _
  rw [jBdH_bAct]
  exact descent_gam (NH H) (YH H V₀) 3 g _

end Objects

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
