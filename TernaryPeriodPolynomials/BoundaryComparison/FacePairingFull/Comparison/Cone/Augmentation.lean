module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeEvaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.CofiberMap
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Unique
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceEvaluation
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.AugmentationRigidity

@[expose] public section


/-!
# The coefficient-sum augmentation of the four cones

The model cone `coneR`, the library's stabilizer cone `stabilizerFaceCone`, its geometric face cone `faceCone`
and the singular chains of the boundary all map to the complex `single₀ ℚ` concentrated in degree zero (the trivial
representation) by the sum of the coefficients: on a resolution of a permutation module by the augmentation
followed by `labelSum`, on a signed cone by `coneDesc` with zero corner homotopy (`augR`, `augS`, `augF`), on the
singular chains of the boundary by `augmentationChain` (`augB`).  The comparison maps of the cones preserve these
augmentations (`uCone_augS`, `faceConeToStabilizer_augS`, `faceConeToBoundary_augB`), and so does the homotopy inverse
of `faceConeStabilizerEquiv` (`inv_comp_eq_of_hom_comp`); consequently the chain map
`coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary` from the model cone to the singular chains of the
boundary is over the augmentation of the model cone (`coneBoundary_augB`), and the restriction `coneToPt` of the
model cone to the point resolution is too (`coneToPt_resAug`).  This is the augmentation input of the comparison of
the geometric restriction with the singular restriction (`Comparison.SingularRestriction`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.TopHomology
open GeneralEisenstein

attribute [local instance] vertexAction

open TernaryPoly.SymmetricSpaceBoundaryMV (Flag LineFaceSum PlaneFaceSum CornerFaceSum)
attribute [local instance] lineLabelTopology planeLabelTopology flagLabelTopology lineLabelDiscrete
  planeLabelDiscrete flagLabelDiscrete
open TernaryPoly.OrdinaryIncidence (Line Plane)

/-- The complex `single₀` of the trivial representation of `Γ(6)` over `ℚ`. -/
abbrev augTarget : ChainComplex (Rep.{0} ℚ Γ6) ℕ :=
  (ChainComplex.single₀ (Rep.{0} ℚ Γ6)).obj (Rep.trivial ℚ Γ6 ℚ)

/-- The augmentation of a resolution of a permutation module, followed by the sum of the coefficients. -/
def resAug {ι : Type} [MulAction Γ6 ι] (R : ProjectiveResolution (Rep.ofMulAction ℚ Γ6 ι)) :
    R.complex ⟶ augTarget :=
  R.π ≫ (ChainComplex.single₀ (Rep.{0} ℚ Γ6)).map labelSum

theorem aug_cond {F L P : ChainComplex (Rep.{0} ℚ Γ6) ℕ} {ιF ιL ιP : Type} [MulAction Γ6 ιF]
    [MulAction Γ6 ιL] [MulAction Γ6 ιP] (a : F ⟶ L) (b : F ⟶ P)
    (Fπ : F ⟶ (ChainComplex.single₀ (Rep.{0} ℚ Γ6)).obj (Rep.ofMulAction ℚ Γ6 ιF))
    (Lπ : L ⟶ (ChainComplex.single₀ (Rep.{0} ℚ Γ6)).obj (Rep.ofMulAction ℚ Γ6 ιL))
    (Pπ : P ⟶ (ChainComplex.single₀ (Rep.{0} ℚ Γ6)).obj (Rep.ofMulAction ℚ Γ6 ιP))
    (iL : Rep.ofMulAction ℚ Γ6 ιF ⟶ Rep.ofMulAction ℚ Γ6 ιL)
    (iP : Rep.ofMulAction ℚ Γ6 ιF ⟶ Rep.ofMulAction ℚ Γ6 ιP)
    (ha : a ≫ Lπ = Fπ ≫ (ChainComplex.single₀ (Rep.{0} ℚ Γ6)).map iL)
    (hb : b ≫ Pπ = Fπ ≫ (ChainComplex.single₀ (Rep.{0} ℚ Γ6)).map iP)
    (hL : iL ≫ labelSum = labelSum) (hP : iP ≫ labelSum = labelSum) :
    a ≫ (Lπ ≫ (ChainComplex.single₀ (Rep.{0} ℚ Γ6)).map labelSum) =
      b ≫ (Pπ ≫ (ChainComplex.single₀ (Rep.{0} ℚ Γ6)).map labelSum) := by
  rw [← Category.assoc, ha, ← Category.assoc, hb, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, hL, hP]

theorem lineIncidence_labelSum : lineIncidence ≫ labelSum = labelSum (ι := Flag) :=
  SymmetricSpaceBoundaryIncidenceHomology.permutationMap_labelSum _ _

theorem planeIncidence_labelSum : planeIncidence ≫ labelSum = labelSum (ι := Flag) :=
  SymmetricSpaceBoundaryIncidenceHomology.permutationMap_labelSum _ _

theorem comparison_resAug {ι : Type} [MulAction Γ6 ι] (R R' : ProjectiveResolution (Rep.ofMulAction ℚ Γ6 ι)) :
    (comparison R R').hom ≫ resAug R' = resAug R := by
  rw [resAug, resAug, ← Category.assoc, comparison_augmentation]

/-- The augmentation of the model cone. -/
def augR : coneR ⟶ augTarget :=
  coneDesc flagLineHom.hom flagPlaneHom.hom (resAug resLine) (resAug resPlane)
    (aug_cond _ _ resFlag.π resLine.π resPlane.π lineIncidence planeIncidence
      flagLineHom.hom_comp_π flagPlaneHom.hom_comp_π lineIncidence_labelSum planeIncidence_labelSum)

/-- The augmentation of the stabilizer cone. -/
def augS : stabilizerFaceCone ⟶ augTarget :=
  coneDesc lineStabilizerArrow planeStabilizerArrow (resAug lineStabilizerModel)
    (resAug planeStabilizerModel)
    (aug_cond _ _ flagStabilizerModel.π lineStabilizerModel.π planeStabilizerModel.π lineIncidence
      planeIncidence (ProjectiveResolution.lift_commutes _ _ _) (ProjectiveResolution.lift_commutes _ _ _)
      lineIncidence_labelSum planeIncidence_labelSum)

/-- The augmentation of the geometric face cone. -/
def augF : faceCone ⟶ augTarget :=
  coneDesc lineChainMap planeChainMap (resAug lineResolution) (resAug planeResolution)
    (aug_cond _ _ flagResolution.π lineResolution.π planeResolution.π lineIncidence planeIncidence
      lineAugmentationChain_natural planeAugmentationChain_natural lineIncidence_labelSum
      planeIncidence_labelSum)

theorem uCone_augS : uCone ≫ augS = augR :=
  cone_map_desc_single₀ _ _ _ _
    (CofiberSequence.inr_comparisonMap (signedArrow flagLineHom.hom flagPlaneHom.hom)
      stabilizerFaceArrow _ _ _) _ _ _ _ _ _
    (comparison_resAug resLine lineStabilizerModel) (comparison_resAug resPlane planeStabilizerModel)

theorem faceConeToStabilizer_augS : faceConeToStabilizer ≫ augS = augF :=
  cone_map_desc_single₀ _ _ _ _ faceConeToStabilizer_inr _ _ _ _ _ _
    (comparison_resAug lineResolution lineStabilizerModel)
    (comparison_resAug planeResolution planeStabilizerModel)

open EquivariantSingularResolution in
/-- The augmentation of the boundary chains. -/
abbrev augB : boundaryChains ⟶ augTarget := augmentationChain principalSix ambient

theorem resAug_lineResolution :
    resAug lineResolution = EquivariantSingularResolution.augmentationChain principalSix
      (TopCat.of LineFaceSum) := by
  apply eq_of_f_zero_single₀
  rw [EquivariantSingularResolution.augmentationChain_f_zero]
  exact SymmetricSpaceBoundaryIncidenceHomology.componentAugmentation_sum lineFamily lineLabel_equivariant

theorem resAug_planeResolution :
    resAug planeResolution = EquivariantSingularResolution.augmentationChain principalSix
      (TopCat.of PlaneFaceSum) := by
  apply eq_of_f_zero_single₀
  rw [EquivariantSingularResolution.augmentationChain_f_zero]
  exact SymmetricSpaceBoundaryIncidenceHomology.componentAugmentation_sum planeFamily planeLabel_equivariant

theorem lineChainToBoundary_augB : lineChainToBoundary ≫ augB = resAug lineResolution :=
  (SingularCoverNaturality.chainMap_augmentationChain lineToBoundary lineToBoundary_equivariant).trans
    resAug_lineResolution.symm

theorem planeChainToBoundary_augB : planeChainToBoundary ≫ augB = resAug planeResolution :=
  (SingularCoverNaturality.chainMap_augmentationChain planeToBoundary planeToBoundary_equivariant).trans
    resAug_planeResolution.symm

theorem faceConeToBoundary_augB : faceConeToBoundary ≫ augB = augF := by
  have h : homotopyCofiber.inr faceArrow ≫ faceConeToBoundary =
      biprod.desc lineChainToBoundary planeChainToBoundary :=
    faceConeToBoundary_inr.trans fullFace_boundary_map
  refine (cone_desc_comp_single₀ lineChainMap planeChainMap h augB ?_).trans ?_
  · rw [lineChainToBoundary_augB, planeChainToBoundary_augB]
    exact aug_cond _ _ flagResolution.π lineResolution.π planeResolution.π lineIncidence planeIncidence
      lineAugmentationChain_natural planeAugmentationChain_natural lineIncidence_labelSum
      planeIncidence_labelSum
  · exact coneDesc_congr _ _ lineChainToBoundary_augB planeChainToBoundary_augB

theorem ofMulActionMap_labelSum {ι κ : Type} [MulAction Γ6 ι] [MulAction Γ6 κ] (u : ι → κ)
    (hu : ∀ (g : Γ6) (i : ι), u (g • i) = g • u i) :
    ofMulActionMap Γ6 ι u hu ≫ labelSum = labelSum := by
  refine hom_ext_single ι _ (fun x => ?_)
  change labelSum ((ofMulActionMap Γ6 ι u hu).hom (MonoidAlgebra.single x 1)) = labelSum (MonoidAlgebra.single x 1)
  rw [ofMulActionMap_single, labelSum_single, labelSum_single]

theorem ptMap_resAug (Z : Type) [MulAction Γ6 Z] :
    ptMap Z ≫ resAug ptRes =
      resAug (prodResolution Γ6 RationalGL3 Z 1 vertexAction_free') := by
  apply eq_of_f_zero_single₀
  have h := prodMapHom_f_zero_comp_eps Γ6 RationalGL3 Z (fun _ => PUnit.unit) (fun _ _ => rfl)
  have key : (ptMap Z).f 0 ≫ prodEps Γ6 RationalGL3 PUnit ≫ labelSum =
      prodEps Γ6 RationalGL3 Z ≫ labelSum := by
    rw [← Category.assoc]
    exact (congrArg (fun m => m ≫ labelSum) h).trans
      ((Category.assoc _ _ _).trans (congrArg (fun m => prodEps Γ6 RationalGL3 Z ≫ m)
        (ofMulActionMap_labelSum _ _)))
  exact key

theorem coneToPt_resAug : coneToPt ≫ resAug ptRes = augR := by
  have h : homotopyCofiber.inr (signedArrow flagLineHom.hom flagPlaneHom.hom) ≫ coneToPt =
      biprod.desc (ptMap Line) (ptMap Plane) := homotopyCofiber.inr_desc _ _ _
  refine (cone_desc_comp_single₀ flagLineHom.hom flagPlaneHom.hom h (resAug ptRes) ?_).trans ?_
  · rw [ptMap_resAug, ptMap_resAug]
    exact aug_cond _ _ resFlag.π resLine.π resPlane.π lineIncidence planeIncidence
      flagLineHom.hom_comp_π flagPlaneHom.hom_comp_π lineIncidence_labelSum planeIncidence_labelSum
  · exact coneDesc_congr _ _ (ptMap_resAug Line) (ptMap_resAug Plane)

theorem coneEquiv_hom_eq : coneEquiv.hom = uCone := Classical.choose_spec exists_coneEquiv

/-- **The chain map from the model cone to the boundary chains preserves the augmentation.** -/
theorem coneBoundary_augB :
    (coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary) ≫ augB = augR := by
  have h1 : faceConeStabilizerEquiv.inv ≫ augF = augS :=
    inv_comp_eq_of_hom_comp faceConeStabilizerEquiv augF augS
      (by rw [faceConeStabilizerEquiv_hom]; exact faceConeToStabilizer_augS)
  rw [Category.assoc, Category.assoc, faceConeToBoundary_augB, h1, coneEquiv_hom_eq]
  exact uCone_augS

theorem labelSum_pt_mono : Mono (labelSum (ι := PUnit)) := by
  rw [Rep.mono_iff_injective]
  intro a b hab
  have h : ∀ c : MonoidAlgebra ℚ PUnit, labelSum c = c.coeff PUnit.unit := by
    intro c
    change (Finsupp.linearCombination ℚ fun _ : PUnit => (1 : ℚ)) c.coeff = _
    rw [Finsupp.linearCombination_unique]
    simp
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  have h1 := h a
  have h2 := h b
  rw [hab] at h1
  rw [Subsingleton.elim i PUnit.unit]
  exact h1.symm.trans h2

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
