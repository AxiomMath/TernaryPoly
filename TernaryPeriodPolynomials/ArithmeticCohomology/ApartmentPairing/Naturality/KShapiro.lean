module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.HLevelTower
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.HLevelMaps
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.ShapiroCor
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.CapNatural

@[expose] public section

/-!
# O2: the chain-level boundary Shapiro isomorphism `(E ⊗ Sing ∂X̃)_K ≅ (Ind_K^G E ⊗ Sing ∂X̃)_G`

Formalized by Claude Sonnet 5.5.

For `K` the stabilizer of the distinguished covector and `E = E_{n,t} = Res_K V_{n,t}`, `M = M_{n,t} = Ind_K^G E` (the 26-covector system),
`shapiroBd` is the isomorphism of complexes obtained from Mathlib's natural isomorphism `(Ind A ⊗ B)_G ≅ (A ⊗ Res B)_K`
(`coinvariantsTensorIndNatIso`) and `TernaryPoly.inducedIso`.  `shapiroMapB_mk`: it is the identity-coset inclusion `⟦e ⊗ y⟧ ↦ ⟦ι(e) ⊗ y⟧`,
`ι = iotaK` (`ι(a)` is `a` at the distinguished covector and `0` elsewhere).  `shapiroBd_QY`: it intertwines the quotient maps from the
`Γ(6)`-coinvariants, and `shapiroBdH_qBdH` expresses this on neat-level boundary homology: `Sh_∂ ∘ qBdH_K = qBd_G ∘ ι_*`.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryCone
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPoly.SingularBoundaryRestriction TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
open Representation HomologicalComplex
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

abbrev Vnt (n : ℕ) (t : Fin 2) : Rep.{0} ℚ IntegralGL := Rep.of (coeff n t)

open scoped Classical in
/-- natural isomorphism `(E ⊗ Res B)_K ≅ (M ⊗ B)_G`. -/
def shapiroNat (n : ℕ) (t : Fin 2) :
    Rep.resFunctor K.subtype ⋙ (Rep.coinvariantsTensor ℚ ↥K).obj (EK n t) ≅
      (Rep.coinvariantsTensor ℚ IntegralGL).obj (MG n t) :=
  (Rep.coinvariantsTensorIndNatIso K.subtype (EK n t)).symm ≪≫
    (Rep.coinvariantsTensor ℚ IntegralGL).mapIso (inducedIso n (expT t))

open scoped Classical in
/-- **The chain-level boundary Shapiro isomorphism** `(E ⊗ Sing ∂X̃)_K ≅ (M ⊗ Sing ∂X̃)_G`. -/
def shapiroBd (n : ℕ) (t : Fin 2) : CxK (YH K (Vnt n t)) ≅ CxK (Ybd (MG n t)) :=
  (NatIso.mapHomologicalComplex (shapiroNat n t) (ComplexShape.down ℕ)).app
    (equivariantChains IntegralGL (TopCat.of BoundaryCover))

theorem tensor_map_left_mk {G : Type} [Group G] {A A' B : Rep.{0} ℚ G} (f : A ⟶ A') (a : A) (b : B) :
    (((Rep.coinvariantsTensor ℚ G).map f).app B).hom (Rep.coinvariantsTensorMk A B a b) =
      Rep.coinvariantsTensorMk A' B (f.hom a) b := rfl

open scoped Classical in
/-- The component of `shapiroNat`, with its source and target displayed. -/
def shapiroMapB (n : ℕ) (t : Fin 2) (B : Rep.{0} ℚ IntegralGL) :
    ((Rep.coinvariantsTensor ℚ ↥K).obj (subgroupCoefficients n (expT t))).obj (Rep.res K.subtype B) ⟶
      ((Rep.coinvariantsTensor ℚ IntegralGL).obj (Rep.of (coefficientAction n (expT t)))).obj B :=
  Rep.coinvariantsTensorIndInv K.subtype (subgroupCoefficients n (expT t)) B ≫
    ((Rep.coinvariantsTensor ℚ IntegralGL).map (inducedIso n (expT t)).hom).app B

open scoped Classical in
theorem shapiroMapB_mk (n : ℕ) (t : Fin 2) (B : Rep.{0} ℚ IntegralGL) (v : subgroupCoefficients n (expT t)) (c : B) :
    (shapiroMapB n t B).hom (Rep.coinvariantsTensorMk (subgroupCoefficients n (expT t)) (Rep.res K.subtype B) v c) =
      Rep.coinvariantsTensorMk (Rep.of (coefficientAction n (expT t))) B ((iotaK n t).hom v) c := by
  unfold shapiroMapB
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  have h1 := Rep.coinvariantsTensorIndInv_mk_tmul_indMk (φ := K.subtype)
    (A := subgroupCoefficients n (expT t)) (B := B) v c
  have h2 : (Rep.coinvariantsTensorIndInv K.subtype (subgroupCoefficients n (expT t)) B).hom
      (Rep.coinvariantsTensorMk (subgroupCoefficients n (expT t)) (Rep.res K.subtype B) v c) =
      Rep.coinvariantsTensorMk (Rep.ind K.subtype (subgroupCoefficients n (expT t))) B
        (Representation.IndV.mk K.subtype _ 1 v) c := h1
  rw [h2, tensor_map_left_mk]
  rfl

/-- The neat-level coefficient map induced by `ι` on `Γ(6)`-coinvariant boundary chains. -/
def Ci (n : ℕ) (t : Fin 2) :
    coinvariantChains principalSix (TopCat.of BoundaryCover) (Rep.res principalSix.subtype (Vnt n t)) ⟶
      coinvariantChains principalSix (TopCat.of BoundaryCover) (Rep.res principalSix.subtype (MG n t)) :=
  coinvariantCoefficientMap (E := TopCat.of BoundaryCover) (iotaN n t)

/-- `Ci` displayed on the `Γ(6)`-coinvariant complexes of `Ybd`. -/
def CiC (n : ℕ) (t : Fin 2) : CxN principalSix (Ybd (Vnt n t)) ⟶ CxN principalSix (Ybd (MG n t)) := Ci n t

open scoped Classical in
theorem shapiroBd_QY (n : ℕ) (t : Fin 2) :
    QY (NH K) (YH K (Vnt n t)) ≫ (shapiroBd n t).hom =
      (trCx K (Vnt n t) principalSix_le_K).hom ≫ CiC n t ≫ QY principalSix (Ybd (MG n t)) := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply Coinvariants.hom_ext
  apply TensorProduct.ext'
  intro v c
  exact shapiroMapB_mk n t ((equivariantChains IntegralGL (TopCat.of BoundaryCover)).X m) v c

/-- **The boundary Shapiro isomorphism on homology**: `H₃((E ⊗ Sing ∂X̃)_K) ≅ H₃((M ⊗ Sing ∂X̃)_G)`, `M = Ind_K^G E`. -/
def shapiroBdH (n : ℕ) (t : Fin 2) : QbdH K (Vnt n t) ≅ Qbd (MG n t) :=
  homologyMapIso (shapiroBd n t) 3

/-- The neat-level map induced on boundary homology by the identity-coset inclusion `ι`. -/
def neatIota (n : ℕ) (t : Fin 2) : Bd (Vnt n t) →ₗ[ℚ] Bd (MG n t) :=
  (homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering (iotaN n t)) 3).hom

open scoped Classical in
theorem shapiroBdH_qBdH (n : ℕ) (t : Fin 2) (c : Bd (Vnt n t)) :
    (shapiroBdH n t).hom ((qBdH K principalSix_le_K (Vnt n t)).hom c) = (qBd (MG n t)).hom (neatIota n t c) := by
  have hLC : localCoefficientMap boundaryProjection boundaryQuotientCovering (iotaN n t) =
      (ibdC (Vnt n t)).hom ≫ CiC n t ≫
        (ibdC (MG n t)).inv := rfl
  have h : (ibdH K principalSix_le_K (Vnt n t)).hom ≫ QY (NH K) (YH K (Vnt n t)) ≫ (shapiroBd n t).hom =
      localCoefficientMap boundaryProjection boundaryQuotientCovering (iotaN n t) ≫ (ibdC (MG n t)).hom ≫
        QY principalSix (Ybd (MG n t)) := by
    rw [shapiroBd_QY, ibdH_hom, hLC]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h2 : homologyMap (ibdH K principalSix_le_K (Vnt n t)).hom 3 ≫ homologyMap (QY (NH K) (YH K (Vnt n t))) 3 ≫
      homologyMap (shapiroBd n t).hom 3 = homologyMap (localCoefficientMap boundaryProjection
        boundaryQuotientCovering (iotaN n t)) 3 ≫ homologyMap (ibdC (MG n t)).hom 3 ≫
        homologyMap (QY principalSix (Ybd (MG n t))) 3 := by
    rw [← homologyMap_comp, ← homologyMap_comp, h, homologyMap_comp, homologyMap_comp]
  exact ConcreteCategory.congr_hom h2 c

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
