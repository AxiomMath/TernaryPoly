module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Coinvariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Natural
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.CapNatural
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Literal.DualityNatural
public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.Assemble

@[expose] public section


open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.ModThreeGoodAction TernaryPoly.SingularLocalHomology TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.EquivariantSingularResolution
open TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceBordifiedQuotient
open TernaryPeriodPolynomials.Argument.DualityEquivariance
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open CategoryTheory.MonoidalCategory
open TernaryPeriodPolynomials.Argument.CoefficientNaturality (coefHomPost homologyEvaluation_coefHomPost)
open TernaryPoly.OrdinaryBoundaryActualEvaluation TernaryPoly.SymmetricSpaceBoundaryFull
  TernaryPoly.SymmetricSpaceBoundaryFullTransfer TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.RationalCohomologyDescent
  TernaryPoly.OrdinaryBoundaryCone

/-!
# Level G: naturality of the honest diagram in `G`-morphisms of coefficients (G-5)

Formalized by Claude Sonnet 5.5.

Paper: "compatible with induction of coefficients".  For a morphism `f : V₀ ⟶ V₁` of
`GL₃(ℤ)`-representations: `Ymap f` is the induced map of `G`-complexes `M ⊗ Sing(∂X̃)`; the geometric action `bAct` commutes with
the coefficient map `Fb f` (`bAct_natural`, from naturality of the diagonal action `GY`), the quotient `qBd` is natural for
`QbdMap f` (`qBd_natural`), and for morphisms between members of the family `actualCoefficients n e` also `jQ`
(`jQ_natural`), boundary Poincaré duality `PDQ` (`PDQ_natural`, via `resToBoundary_natural`), the right arrow
(`topEvaluationG_natural`, every `M`) and the bottom arrow (`fullBoundaryPairing_natural`).  Bundle: `levelG_natural`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Functoriality of `Ygeo` in the coefficient `G`-representation. -/
def Ymap {V₀ V₁ : Rep.{0} ℚ IntegralGL} (f : V₀ ⟶ V₁) : Ybd V₀ ⟶ Ybd V₁ where
  f n := f ▷ (equivariantChains IntegralGL (TopCat.of BoundaryCover)).X n
  comm' i j _ := by
    exact (whisker_exchange f _).symm

variable {V₀ V₁ : Rep.{0} ℚ IntegralGL} (f : V₀ ⟶ V₁)

theorem Ymap_coef :
    ((cN (k := ℚ) principalSix).mapHomologicalComplex _).map (Ymap f) =
      coinvariantCoefficientMap (E := TopCat.of BoundaryCover) ((Rep.resFunctor principalSix.subtype).map f) := by
  rfl

theorem GY_natural' {Y Y' : ChainComplex (Rep.{0} ℚ IntegralGL) ℕ} (h : Y ⟶ Y') (g : IntegralGL) :
    GY principalSix Y g ≫ ((cN (k := ℚ) principalSix).mapHomologicalComplex _).map h =
      ((cN (k := ℚ) principalSix).mapHomologicalComplex _).map h ≫ GY principalSix Y' g :=
  ((NatTrans.mapHomologicalComplex (gamNat (k := ℚ) principalSix g) _).naturality h).symm

theorem QY_natural' {Y Y' : ChainComplex (Rep.{0} ℚ IntegralGL) ℕ} (h : Y ⟶ Y') :
    QY principalSix Y ≫ ((cK (k := ℚ) (K := IntegralGL)).mapHomologicalComplex _).map h =
      ((cN (k := ℚ) principalSix).mapHomologicalComplex _).map h ≫ QY principalSix Y' :=
  ((NatTrans.mapHomologicalComplex (qNat (k := ℚ) principalSix) _).naturality h).symm

/-- The coefficient map `F f` on the boundary local chains. -/
abbrev Fb : boundaryLocalChains (Rep.res principalSix.subtype V₀) ⟶ boundaryLocalChains (Rep.res principalSix.subtype V₁) :=
  localCoefficientMap boundaryProjection boundaryQuotientCovering ((Rep.resFunctor principalSix.subtype).map f)

theorem Fb_eq : Fb f = (ibd V₀).hom ≫ ((cN (k := ℚ) principalSix).mapHomologicalComplex _).map (Ymap f) ≫ (ibd V₁).inv := rfl

theorem GYb_natural (g : IntegralGL) :
    GYb V₀ g ≫ coinvariantCoefficientMap (E := TopCat.of BoundaryCover) ((Rep.resFunctor principalSix.subtype).map f) =
      coinvariantCoefficientMap (E := TopCat.of BoundaryCover) ((Rep.resFunctor principalSix.subtype).map f) ≫ GYb V₁ g :=
  GY_natural' (Ymap f) g

/-- **G-5: the geometric action commutes with coefficient morphisms** `f : V₀ ⟶ V₁` of `G`-representations. -/
theorem bAct_natural (g : IntegralGL) : bAct V₀ g ≫ Fb f = Fb f ≫ bAct V₁ g := by
  rw [Fb_eq, Ymap_coef]
  unfold bAct
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [reassoc_of% (GYb_natural f g)]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The map on the honest coinvariant homology induced by a coefficient morphism. -/
def QbdMap : Qbd V₀ ⟶ Qbd V₁ := homologyMap (((cK (k := ℚ) (K := IntegralGL)).mapHomologicalComplex _).map (Ymap f)) 3

theorem Fb_ibd : Fb f ≫ (ibd V₁).hom =
    (ibd V₀).hom ≫ ((cN (k := ℚ) principalSix).mapHomologicalComplex _).map (Ymap f) := by
  rw [Fb_eq]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The map on `Γ(6)`-coinvariant homology induced by a coefficient morphism. -/
def NbdMap : (CxN principalSix (Ybd V₀)).homology 3 ⟶ (CxN principalSix (Ybd V₁)).homology 3 :=
  homologyMap (((cN (k := ℚ) principalSix).mapHomologicalComplex _).map (Ymap f)) 3

theorem jBd_natural : homologyMap (Fb f) 3 ≫ (jBd V₁).hom = (jBd V₀).hom ≫ NbdMap f := by
  exact (homologyMap_comp (Fb f) (ibd V₁).hom 3).symm.trans
    ((congrArg (homologyMap · 3) (Fb_ibd f)).trans (homologyMap_comp (ibd V₀).hom _ 3))

theorem QY_homology_natural :
    homologyMap (QY principalSix (Ybd V₀)) 3 ≫ QbdMap f = NbdMap f ≫ homologyMap (QY principalSix (Ybd V₁)) 3 := by
  exact (homologyMap_comp (QY principalSix (Ybd V₀)) _ 3).symm.trans
    ((congrArg (homologyMap · 3) (QY_natural' (Ymap f))).trans (homologyMap_comp _ (QY principalSix (Ybd V₁)) 3))

/-- **G-5: `qBd` is natural in the coefficients.** -/
theorem qBd_natural : homologyMap (Fb f) 3 ≫ qBd V₁ = qBd V₀ ≫ QbdMap f := by
  rw [qBd_eq, qBd_eq, ← Category.assoc, jBd_natural, Category.assoc, Category.assoc, ← QY_homology_natural]

/-- **G-5: the right arrow `z ↦ F_z(ℓ)` is natural in the coefficients** (every `G`-morphism `f : M ⟶ M'`). -/
theorem topEvaluationG_natural (M M' : Rep.{0} ℚ IntegralGL) (f : M ⟶ M') (z : groupHomology M 3) :
    topEvaluationG M' ((groupHomology.map (MonoidHom.id IntegralGL) f 3).hom z) =
      f.hom (topEvaluationG M z) := by
  have h := Lemma45Literal.H3GGen_natural (fun k => capEps k M) (fun k => capEps k M') f z
  rw [topEvaluationG_apply, topEvaluationG_apply]
  exact LinearMap.congr_fun h OrdinaryTopBoundaryComparison.identityApartment

section Family

variable {n n' : ℕ} {e e' : ℤ} (f : actualCoefficients n e ⟶ actualCoefficients n' e')

/-- The coefficient morphism restricted to `H₃(∂X̄_G; 𝓜)`. -/
def H3map : H3boundaryG n e →ₗ[ℚ] H3boundaryG n' e' where
  toFun c := ⟨(homologyMap (Fb f) 3).hom c.1, (mem_H3boundaryG_iff n' e' _).2 (fun g => by
    have h1 := (mem_H3boundaryG_iff n e _).1 c.2 g
    have h2 := ConcreteCategory.congr_hom (congrArg (homologyMap · 3) (bAct_natural f g)) c.1
    rw [homologyMap_comp, homologyMap_comp] at h2
    change (homologyMap (Fb f) 3).hom ((homologyMap (bAct (actualCoefficients n e) g) 3).hom c.1) =
      (homologyMap (bAct (actualCoefficients n' e') g) 3).hom ((homologyMap (Fb f) 3).hom c.1) at h2
    rw [h1] at h2
    exact h2.symm)⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (map_smul _ _ _)

theorem coinvIso_natural (c : H3boundaryG n e) :
    (QbdMap f).hom (coinvIso n e c) = coinvIso n' e' (H3map f c) := by
  rw [coinvIso_apply, coinvIso_apply]
  exact (ConcreteCategory.congr_hom (qBd_natural f) c.1).symm

open TernaryPeriodPolynomials.Argument.Lemma33.Normalized (boundaryToGroup_natural) in
/-- **G-5: `j^G_*` on the honest coinvariant homology is natural in the coefficients.** -/
theorem jQ_natural (y : Qbd (actualCoefficients n e)) :
    jQ n' e' ((QbdMap f).hom y) = (groupHomology.map (MonoidHom.id IntegralGL) f 3).hom (jQ n e y) := by
  obtain ⟨c, rfl⟩ := qBd_surjective (actualCoefficients n e) y
  have h1 : (QbdMap f).hom ((qBd (actualCoefficients n e)).hom c) =
      (qBd (actualCoefficients n' e')).hom ((homologyMap (Fb f) 3).hom c) :=
    (ConcreteCategory.congr_hom (qBd_natural f) c).symm
  rw [h1, jQ_qBd, jQ_qBd]
  have h2 : (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n' e') 3).hom
      ((homologyMap (Fb f) 3).hom c) =
      (groupHomology.map (MonoidHom.id principalSix) ((Rep.resFunctor principalSix.subtype).map f) 3).hom
        ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom c) :=
    ConcreteCategory.congr_hom (boundaryToGroup_natural ((Rep.resFunctor principalSix.subtype).map f)) c
  change (corG n' e').hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n' e') 3).hom
      ((homologyMap (Fb f) 3).hom c)) = _
  rw [h2]
  exact Lemma45Literal.corN_natural f _

theorem restrBd_post :
    restrBd n e ≫ coefHomPost SymmetricSpaceBoundaryIncidenceHomology.boundaryChains
        ((Rep.resFunctor principalSix.subtype).map f) =
      coefHomPost fullBoundaryChains f ≫ restrBd n' e' := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rfl

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary) in
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized (PDboundary_natural) in
theorem resToBoundary_natural (ω : (fullBoundaryCochains n e).homology 1) :
    (homologyMap (Fb f) 3).hom (resToBoundary n e ω) =
      resToBoundary n' e' ((homologyMap (coefHomPost fullBoundaryChains f) 1).hom ω) := by
  apply PDboundary_injective n' e'
  have h1 : (PDboundary (restrictedCoefficients n' e')).hom ((homologyMap (Fb f) 3).hom (resToBoundary n e ω)) =
      (homologyMap (coefHomPost SymmetricSpaceBoundaryIncidenceHomology.boundaryChains
        ((Rep.resFunctor principalSix.subtype).map f)) 1).hom
        ((PDboundary (restrictedCoefficients n e)).hom (resToBoundary n e ω)) :=
    ConcreteCategory.congr_hom (PDboundary_natural ((Rep.resFunctor principalSix.subtype).map f)) _
  rw [h1, PDboundary_resToBoundary, PDboundary_resToBoundary]
  have h2 := ConcreteCategory.congr_hom (congrArg (homologyMap · 1) (restrBd_post f)) ω
  rw [homologyMap_comp, homologyMap_comp] at h2
  exact h2

/-- **G-5: the bottom arrow `ω ↦ ⟨ω, ∂a⟩` is natural in the coefficients.** -/
theorem fullBoundaryPairing_natural (ω : (fullBoundaryCochains n e).homology 1) :
    fullBoundaryPairing n' e' ((homologyMap (coefHomPost fullBoundaryChains f) 1).hom ω) =
      f.hom (fullBoundaryPairing n e ω) := by
  have h := homologyEvaluation_coefHomPost (C := fullBoundaryChains) f 1 ω
  change (OrdinaryTopBoundaryComparison.homologyEvaluation fullBoundaryChains (actualCoefficients n' e') 1
      ((homologyMap (coefHomPost fullBoundaryChains f) 1).hom ω)).hom apartmentClassFull =
    f.hom ((OrdinaryTopBoundaryComparison.homologyEvaluation fullBoundaryChains (actualCoefficients n e) 1 ω).hom apartmentClassFull)
  rw [h]
  rfl

theorem PDG_natural (c : H3boundaryG n e) :
    (homologyMap (coefHomPost fullBoundaryChains f) 1).hom (PDG n e c) = PDG n' e' (H3map f c) := by
  apply resToBoundary_injective n' e'
  have h1 : resToBoundary n e (PDG n e c) = c.1 := by
    have := PDG_symm_apply n e (PDG n e c)
    rw [LinearEquiv.symm_apply_apply] at this
    exact this.symm
  have h2 : resToBoundary n' e' (PDG n' e' (H3map f c)) = (H3map f c).1 := by
    have := PDG_symm_apply n' e' (PDG n' e' (H3map f c))
    rw [LinearEquiv.symm_apply_apply] at this
    exact this.symm
  rw [h2, ← resToBoundary_natural, h1]
  rfl

/-- **G-5: boundary Poincaré duality on `Qbd` is natural in the coefficients.** -/
theorem PDQ_natural (y : Qbd (actualCoefficients n e)) :
    (homologyMap (coefHomPost fullBoundaryChains f) 1).hom (PDQ n e y) = PDQ n' e' ((QbdMap f).hom y) := by
  obtain ⟨c, rfl⟩ := (coinvIso n e).surjective y
  have h := coinvIso_natural f c
  rw [h]
  change (homologyMap (coefHomPost fullBoundaryChains f) 1).hom (PDG n e ((coinvIso n e).symm (coinvIso n e c))) =
    PDG n' e' ((coinvIso n' e').symm (coinvIso n' e' (H3map f c)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact PDG_natural f c

/-- **G-5: the honest level-`G` diagram is natural in `G`-morphisms of coefficients** `f : M_{n,e} ⟶ M_{n',e'}`.  The
geometric action, the quotient map to the honest coinvariant homology, `j^G_*`, boundary Poincaré duality, the right arrow
and the bottom arrow all commute with `f`; hence the diagram `levelG_diagram_Q` for `M'` at `f_* y` is `f` applied to the
diagram for `M` at `y`. -/
theorem levelG_natural :
    (∀ g, bAct (actualCoefficients n e) g ≫ Fb f = Fb f ≫ bAct (actualCoefficients n' e') g) ∧
    (homologyMap (Fb f) 3 ≫ qBd (actualCoefficients n' e') = qBd (actualCoefficients n e) ≫ QbdMap f) ∧
    (∀ y, jQ n' e' ((QbdMap f).hom y) = (groupHomology.map (MonoidHom.id IntegralGL) f 3).hom (jQ n e y)) ∧
    (∀ y, (homologyMap (coefHomPost fullBoundaryChains f) 1).hom (PDQ n e y) = PDQ n' e' ((QbdMap f).hom y)) ∧
    (∀ z, topEvaluationG (actualCoefficients n' e') ((groupHomology.map (MonoidHom.id IntegralGL) f 3).hom z) =
      f.hom (topEvaluationG (actualCoefficients n e) z)) ∧
    (∀ ω, fullBoundaryPairing n' e' ((homologyMap (coefHomPost fullBoundaryChains f) 1).hom ω) =
      f.hom (fullBoundaryPairing n e ω)) :=
  ⟨bAct_natural f, qBd_natural f, jQ_natural f, PDQ_natural f, topEvaluationG_natural _ _ f,
    fullBoundaryPairing_natural f⟩

end Family

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
