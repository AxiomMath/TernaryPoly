module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.ConeHomotopy
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConePsi
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.ConeInstance
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.StratumQuasi
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ProjectiveUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.CofiberMap
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Comparison

@[expose] public section


/-!
# Canonicity of the carried comparison of cones: the strata and the homotopy

The carried quasi-isomorphism `u : coneR ⟶ faceCone` of `exists_PsiF_carried` and the library's
`uCone : coneR ⟶ stabilizerFaceCone` induce, on the three strata (flag, line, plane), maps over the same augmentations
of the projective resolutions of the label modules; the stratum maps are therefore homotopic
(`uniqHomotopy`), and by the cone-level uniqueness `cone_maps_homotopic` the composite
`u ≫ faceConeToStabilizer` is homotopic to `uCone` (`carried_canonical`).

* `StrataData.comp`, `strataOfComparison`, `uConeStrata`, `faceStabStrata`: the stratum data of the comparison maps of
  the library (`CofiberSequence.comparisonMap` of homotopy-commutative squares);
* `sigma_stratum_comp`: the commuting triangle with the augmentation behind `sigma_stratum_quasiIso`;
* `carried_strata`: a carried cone map respects the strata over the augmentations;
* `carried_canonical`: the homotopy `u ≫ faceConeToStabilizer ≃ uCone`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

open CapCompat TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryGeometricCone TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
attribute [local instance] Comparison.vertexAction

section Comp

variable {Γ : Type} [Group Γ]
  {A L P K A' L' P' K' A'' L'' P'' K'' : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  {a' : A' ⟶ L'} {b' : A' ⟶ P'} {a'' : A'' ⟶ L''} {b'' : A'' ⟶ P''}
  {𝒞 : PushCone A L P K a b} {𝒟 : PushCone A' L' P' K' a' b'} {ℰ : PushCone A'' L'' P'' K'' a'' b''}
  {G : K ⟶ K'} {G' : K' ⟶ K''}

/-- Composition of strata data. -/
def StrataData.comp (D : StrataData 𝒞 𝒟 G) (D' : StrataData 𝒟 ℰ G') : StrataData 𝒞 ℰ (G ≫ G') where
  lA := D.lA ≫ D'.lA
  lL := D.lL ≫ D'.lL
  lP := D.lP ≫ D'.lP
  hL n := by
    rw [HomologicalComplex.comp_f, ← Category.assoc, D.hL n, Category.assoc, D'.hL n]
    simp
  hP n := by
    rw [HomologicalComplex.comp_f, ← Category.assoc, D.hP n, Category.assoc, D'.hP n]
    simp
  hA n := by
    have h := D.iA_G n
    have e : 𝒞.iA n ≫ (G ≫ G').f (n + 1) ≫ ℰ.pA n =
        (𝒞.iA n ≫ G.f (n + 1)) ≫ G'.f (n + 1) ≫ ℰ.pA n := by
      simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [e, h]
    simp only [Preadditive.add_comp, Category.assoc]
    rw [D'.hA n, ← Category.assoc (𝒟.iL (n + 1)), D'.hL, Category.assoc, cone_iL_pA (𝒞 := ℰ), ← Category.assoc (𝒟.iP (n + 1)), D'.hP,
      Category.assoc, cone_iP_pA (𝒞 := ℰ)]
    simp

end Comp

section CompMap

variable {Γ : Type} [Group Γ]
  {A L P A' L' P' : ChainComplex (Rep.{0} ℚ Γ) ℕ} (a : A ⟶ L) (b : A ⟶ P) (a' : A' ⟶ L') (b' : A' ⟶ P')
  (u : A ⟶ A') (vL : L ⟶ L') (vP : P ⟶ P')
  (h : Homotopy (pushArrow a b ≫ biprod.map vL vP) (u ≫ pushArrow a' b'))

/-- A cone map induced by a homotopy-commutative square of the arrows respects the strata. -/
def strataOfComparison :
    StrataData (pushConeOfCofiber a b) (pushConeOfCofiber a' b')
      (CofiberSequence.comparisonMap (pushArrow a b) (pushArrow a' b') u (biprod.map vL vP) h) where
  lA := u
  lL := vL
  lP := vP
  hL n := by
    have hm : (HomologicalComplex.homotopyCofiber.inrX (pushArrow a b) n) ≫
        (CofiberSequence.comparisonMap (pushArrow a b) (pushArrow a' b') u (biprod.map vL vP) h).f n =
        (biprod.map vL vP).f n ≫ HomologicalComplex.homotopyCofiber.inrX (pushArrow a' b') n :=
      HomologicalComplex.homotopyCofiber.inrX_desc_f _ _ _ n
    have hl : (biprod.inl : L ⟶ L ⊞ P).f n ≫ (biprod.map vL vP).f n = vL.f n ≫ (biprod.inl : L' ⟶ L' ⊞ P').f n := by
      rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, biprod.inl_map]
    change ((biprod.inl : L ⟶ L ⊞ P).f n ≫ HomologicalComplex.homotopyCofiber.inrX (pushArrow a b) n) ≫ _ =
      vL.f n ≫ ((biprod.inl : L' ⟶ L' ⊞ P').f n ≫ HomologicalComplex.homotopyCofiber.inrX (pushArrow a' b') n)
    rw [Category.assoc, hm, ← Category.assoc, hl, Category.assoc]
  hP n := by
    have hm : (HomologicalComplex.homotopyCofiber.inrX (pushArrow a b) n) ≫
        (CofiberSequence.comparisonMap (pushArrow a b) (pushArrow a' b') u (biprod.map vL vP) h).f n =
        (biprod.map vL vP).f n ≫ HomologicalComplex.homotopyCofiber.inrX (pushArrow a' b') n :=
      HomologicalComplex.homotopyCofiber.inrX_desc_f _ _ _ n
    have hl : (biprod.inr : P ⟶ L ⊞ P).f n ≫ (biprod.map vL vP).f n = vP.f n ≫ (biprod.inr : P' ⟶ L' ⊞ P').f n := by
      rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, biprod.inr_map]
    change ((biprod.inr : P ⟶ L ⊞ P).f n ≫ HomologicalComplex.homotopyCofiber.inrX (pushArrow a b) n) ≫ _ =
      vP.f n ≫ ((biprod.inr : P' ⟶ L' ⊞ P').f n ≫ HomologicalComplex.homotopyCofiber.inrX (pushArrow a' b') n)
    rw [Category.assoc, hm, ← Category.assoc, hl, Category.assoc]
  hA n := by
    rw [pushConeOfCofiber_pA]
    have hlc := CofiberSequence.left_comparisonMap (pushArrow a b) (pushArrow a' b') u (biprod.map vL vP) h n
    change CofiberSequence.left (pushArrow a b) n ≫ _ ≫ _ = _
    rw [← Category.assoc, hlc]
    simp only [Preadditive.add_comp, Category.assoc, CofiberSequence.right_first, CofiberSequence.left_first]
    simp

end CompMap

section UCone

/-- The model-to-stabilizer cone map `uCone` respects the strata, with the resolution comparisons as stratum maps. -/
def uConeStrata : StrataData (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineStabilizerArrow planeStabilizerArrow) uCone :=
  strataOfComparison flagLineHom.hom flagPlaneHom.hom lineStabilizerArrow planeStabilizerArrow
    (comparison resFlag flagStabilizerModel).hom (comparison resLine lineStabilizerModel).hom
    (comparison resPlane planeStabilizerModel).hom
    (signedSquareHomotopy _ _ _ _ _ _ _
      (comparisonHomotopy resFlag flagStabilizerModel resLine lineStabilizerModel lineIncidence
        flagLineHom)
      (comparisonHomotopy resFlag flagStabilizerModel resPlane planeStabilizerModel planeIncidence
        flagPlaneHom))

/-- The face-cone to stabilizer-cone map respects the strata. -/
def faceStabStrata : StrataData CapCompat.FaceCone.cone (pushConeOfCofiber lineStabilizerArrow planeStabilizerArrow)
    faceConeToStabilizer :=
  strataOfComparison lineChainMap planeChainMap lineStabilizerArrow planeStabilizerArrow
    flagStabilizerComparison.hom lineStabilizerComparison.hom planeStabilizerComparison.hom stabilizerFaceSquare

end UCone

section Carried

open CategoryTheory Limits MonoidalCategory
open TernaryPoly.EquivariantSingularResolution
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.SingularComponentAugmentation (Total)
open GeneralEisenstein
open TernaryPoly.OrdinaryIncidence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceBoundaryFaces TernaryPoly.SymmetricSpaceBoundaryMV
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.IntegralGL3Congruence

attribute [local instance] CapCompat.lineLabelTopology CapCompat.planeLabelTopology CapCompat.flagLabelTopology
  CapCompat.lineLabelDiscrete CapCompat.planeLabelDiscrete CapCompat.flagLabelDiscrete

open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)

variable {G : Type} [Group G] {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)]
  [∀ i, ContractibleSpace (X i)] [TopologicalSpace ι] [DiscreteTopology ι] [MulAction G ι]
  [MulAction G (Total X)] [ContinuousConstSMul G (Total X)]
  (hlabel : ∀ (g : G) (x : Total X), (g • x).1 = g • x.1)

/-- The commuting triangle with the augmentation behind `sigma_stratum_quasiIso`. -/
theorem sigma_stratum_comp (V : Type) [MulAction G V] (hfree : ∀ (γ : G) (v : V), γ • v = v → γ = 1) (v₀ : V)
    (w : prodComplex G V ι ⟶ equivariantChains G (TopCat.of (Total X)))
    (hc : ∀ s : (nerveCells G V ι hfree).S 0, (w.f 0).hom ((nerveCells G V ι hfree).cell 0 s) ∈
      (LabelData.ofSigma (G := G) X hlabel).faceK (nerveLab G V ι hfree 0 s) 0)
    (he : ∀ x, (singEps (G := G) (TopCat.of (Total X))).hom ((w.f 0).hom x) = (nerveEps G V ι).hom x) :
    w ≫ SingularComponentAugmentation.augmentationChain X G hlabel = prodEpsToSingle G V ι v₀ := by
  apply toSingle₀_ext
  have e1 : (prodEpsToSingle G V ι v₀).f 0 = prodEps G V ι :=
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
  rw [e1, HomologicalComplex.comp_f, SingularComponentAugmentation.augmentationChain_f_zero]
  apply (nerveCells G V ι hfree).hom_ext 0
  intro s
  have hy := hc s
  have h1 := scalarAug_of_mem_faceK X hlabel _ hy
  have h2 := he ((nerveCells G V ι hfree).cell 0 s)
  have h3 : (nerveEps G V ι).hom ((nerveCells G V ι hfree).cell 0 s) = (1 : ℚ) :=
    nerveEps_single G V ι (show (Fin (0+1) → V) × ι from s)
  have h4 : epsL (G := G) (TopCat.of (Total X)) ((w.f 0).hom ((nerveCells G V ι hfree).cell 0 s)) = 1 :=
    h2.trans h3
  have h5 := prodEps_single G V ι (show (Fin (0+1) → V) × ι from s).1 (show (Fin (0+1) → V) × ι from s).2
  change (SingularComponentAugmentation.augmentation X G hlabel).hom ((w.f 0).hom _) = _
  change (SingularComponentAugmentation.scalarAugmentation X).hom
    ((w.f 0).hom ((nerveCells G V ι hfree).cell 0 s)) = _
  rw [h1, h4, one_smul]
  exact h5.symm

open PushCone in
/-- **A carried cone map respects the strata, over the augmentations of the three strata.**  For a carried map
`u : coneR ⟶ faceCone` (as produced by `exists_PsiF_carried`) there are strata maps `uA, uL, uP` with
`iL ≫ u = uL ≫ iL`, `iP ≫ u = uP ≫ iP`, `iA ≫ u ≫ pA = uA`, and they commute with the augmentations of the resolutions
`resX ⟶ Xresolution` (`uL ≫ lineResolution.π = resLine.π` in degree `0`, etc.). -/
theorem carried_strata (u : coneR ⟶ SymmetricSpaceBoundaryGeometricCone.faceCone)
    (hu : ∀ n, (PushCone.pushCarrierData (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
      (pushConeOfCofiber lineChainMap planeChainMap) modelLabels FaceCone.targets).Carried (u.f n))
    (hueps : u.f 0 ≫ (pushConeOfCofiber lineChainMap planeChainMap).eps FaceCone.SL FaceCone.SP =
      (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom).eps (nerveDiagSystem Γ6 RationalGL3 Line)
        (nerveDiagSystem Γ6 RationalGL3 Plane)) :
    ∃ D : StrataData (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom) FaceCone.cone u,
      D.lL.f 0 ≫ lineResolution.π.f 0 = resLine.π.f 0 ∧ D.lP.f 0 ≫ planeResolution.π.f 0 = resPlane.π.f 0 ∧
      D.lA.f 0 ≫ flagResolution.π.f 0 = resFlag.π.f 0 := by
  have hL := carried_range_L (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineChainMap planeChainMap) modelLabels FaceCone.targets u hu
  have hP := carried_range_P (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineChainMap planeChainMap) modelLabels FaceCone.targets u hu
  obtain ⟨uA, uL, uP, huL, huP, huA, hspecL, hspecP⟩ := exists_strata u hL hP
  have hepsL' := strata_eps_L (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineChainMap planeChainMap) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) FaceCone.SL FaceCone.SP u hueps uL (hspecL 0)
  have hepsP' := strata_eps_P (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineChainMap planeChainMap) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) FaceCone.SL FaceCone.SP u hueps uP (hspecP 0)
  have hepsA' := strata_eps_A (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineChainMap planeChainMap) (nerveDiagSystem Γ6 RationalGL3 Flag)
    (nerveDiagSystem Γ6 RationalGL3 Line) (nerveDiagSystem Γ6 RationalGL3 Plane) FaceCone.SA FaceCone.SL FaceCone.SP
    model_strict FaceCone.strict u uA uL uP huA (hspecL 0) (hspecP 0) hepsL'
  have hcL := strata_carried_L (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineChainMap planeChainMap) modelLabels FaceCone.targets u hu uL huL
  have hcP := strata_carried_P (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineChainMap planeChainMap) modelLabels FaceCone.targets u hu uP huP
  have hcA := strata_carried_A (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineChainMap planeChainMap) modelLabels FaceCone.targets u hu uA huA
  refine ⟨⟨uA, uL, uP, hspecL, hspecP, fun n => (huA n).symm⟩, ?_, ?_, ?_⟩
  · have := sigma_stratum_comp lineFamily lineLabel_equivariant RationalGL3 Comparison.vertexAction_free' 1 uL
      (hcL 0) hepsL'
    exact congrArg (fun m => m.f 0) this
  · have := sigma_stratum_comp planeFamily planeLabel_equivariant RationalGL3 Comparison.vertexAction_free' 1 uP
      (hcP 0) hepsP'
    exact congrArg (fun m => m.f 0) this
  · have := sigma_stratum_comp flagFamily flagLabel_equivariant RationalGL3 Comparison.vertexAction_free' 1 uA
      (hcA 0) hepsA'
    exact congrArg (fun m => m.f 0) this

/-- The properties of the carrier-respecting comparison `u : coneR ⟶ faceCone` of `exists_PsiF_carried` that the
canonicity argument uses: it is carried by the label carriers, and compatible with the augmentations of the diagonal
systems. -/
def CarriedPsi (u : coneR ⟶ SymmetricSpaceBoundaryGeometricCone.faceCone) : Prop :=
  (∀ n, (PushCone.pushCarrierData (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
      (pushConeOfCofiber lineChainMap planeChainMap) modelLabels FaceCone.targets).Carried (u.f n)) ∧
    u.f 0 ≫ (pushConeOfCofiber lineChainMap planeChainMap).eps FaceCone.SL FaceCone.SP =
      (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom).eps (nerveDiagSystem Γ6 RationalGL3 Line)
        (nerveDiagSystem Γ6 RationalGL3 Plane)

section Canon

open PushCone in
/-- **Canonicity of the cone comparison.**  A carried cone map `u : coneR ⟶ faceCone` followed by
`faceConeToStabilizer` is chain homotopic to the library's comparison `uCone : coneR ⟶ stabilizerFaceCone`
(both lie over the same resolution comparisons on the three strata, and the connecting `Ext^{-1}` vanishes). -/
theorem carried_canonical (u : coneR ⟶ SymmetricSpaceBoundaryGeometricCone.faceCone) (hu : CarriedPsi u) :
    Nonempty (Homotopy (u ≫ faceConeToStabilizer) uCone) := by
  obtain ⟨D, hLaug, hPaug, hAaug⟩ := carried_strata u hu.1 hu.2
  let D1 := D.comp faceStabStrata
  have hpF : ∀ n, Projective (resFlag.complex.X n) := fun n => resFlag.projective n
  have hpL : ∀ n, Projective (resLine.complex.X n) := fun n => resLine.projective n
  have hpP : ∀ n, Projective (resPlane.complex.X n) := fun n => resPlane.projective n
  have e1 : ∀ {Z : Rep.{0} ℚ Γ6} (R R' : ProjectiveResolution Z),
      (comparison R R').hom.f 0 ≫ R'.π.f 0 = R.π.f 0 :=
    fun R R' => congrArg (fun m => m.f 0) (comparison_augmentation R R')
  have sA : Homotopy D1.lA uConeStrata.lA := by
    have := hpF
    refine uniqHomotopy (Q := flagStabilizerModel) _ _ ?_
    change (D.lA ≫ flagStabilizerComparison.hom).f 0 ≫ _ = (comparison resFlag flagStabilizerModel).hom.f 0 ≫ _
    refine ((congrArg (fun m => m ≫ _) (HomologicalComplex.comp_f D.lA flagStabilizerComparison.hom 0)).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun m => D.lA.f 0 ≫ m) (e1 flagResolution flagStabilizerModel)).trans
        hAaug))).trans (e1 resFlag flagStabilizerModel).symm
  have sL : Homotopy D1.lL uConeStrata.lL := by
    have := hpL
    refine uniqHomotopy (Q := lineStabilizerModel) _ _ ?_
    change (D.lL ≫ lineStabilizerComparison.hom).f 0 ≫ _ = (comparison resLine lineStabilizerModel).hom.f 0 ≫ _
    refine ((congrArg (fun m => m ≫ _) (HomologicalComplex.comp_f D.lL lineStabilizerComparison.hom 0)).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun m => D.lL.f 0 ≫ m) (e1 lineResolution lineStabilizerModel)).trans
        hLaug))).trans (e1 resLine lineStabilizerModel).symm
  have sP : Homotopy D1.lP uConeStrata.lP := by
    have := hpP
    refine uniqHomotopy (Q := planeStabilizerModel) _ _ ?_
    change (D.lP ≫ planeStabilizerComparison.hom).f 0 ≫ _ = (comparison resPlane planeStabilizerModel).hom.f 0 ≫ _
    refine ((congrArg (fun m => m ≫ _) (HomologicalComplex.comp_f D.lP planeStabilizerComparison.hom 0)).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun m => D.lP.f 0 ≫ m) (e1 planeResolution planeStabilizerModel)).trans
        hPaug))).trans (e1 resPlane planeStabilizerModel).symm
  have := hpF
  exact cone_maps_homotopic D1 uConeStrata sA sL sP (fun n => lineStabilizerModel.exact_succ n)
    (fun n => planeStabilizerModel.exact_succ n)

end Canon

end Carried

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
