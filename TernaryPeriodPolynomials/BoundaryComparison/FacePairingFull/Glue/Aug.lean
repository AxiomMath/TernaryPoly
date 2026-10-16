module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Lift
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.StrataCanon
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.SingularRestriction

@[expose] public section


/-!
# The comparison map `Ψ` of `facePairing_comparison` is over the augmentation

`facePairing_comparison` produces a quasi-isomorphism `Ψ : coneR ⟶ boundaryChains` without recording that it preserves the
coefficient-sum augmentation.  Here the augmentation is recovered from `exists_PsiF` (`u.f 0 ≫ faceDiagSystem.eps =
modelDiagSystem.eps`): the augmentations `augR` of the model cone and `augF` of the face cone are the augmentations of their
diagonal systems (`augR_f_zero`, `augF_f_zero`, on the line and plane summands, through `singEps = augmentation`), so
`Ψ ≫ augB = augR` (`exists_PsiPrime_aug`).  `facePairing_comparison_aug` is `facePairing_comparison` with this extra
conclusion (same proof, the carrier-respecting `Ψ` of `exists_PsiF`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalDuality TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactCap.Algebra TernaryPoly.CompactOrdinaryCap TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceBoundaryManifold TernaryPoly.SymmetricSpaceBoundaryOrientation
  TernaryPoly.HalfSpaceBoundaryOrientation TernaryPoly.RelativeCapConnecting
  TernaryPoly.IntegralGL3Congruence
  TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
  TernaryPoly.FreeActionLinearization TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient labelSum labelSum_single)
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.CoinvScalar
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.SymmetricSpaceBoundaryFull
  TernaryPoly.RationalManifoldCompact
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag LineFaceSum PlaneFaceSum CornerFaceSum)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction
attribute [local instance] lineLabelTopology planeLabelTopology flagLabelTopology lineLabelDiscrete
  planeLabelDiscrete flagLabelDiscrete

theorem augmentation_chainElement (E : TopCat.{0}) [MulAction principalSix E] [ContinuousConstSMul principalSix E]
    (σ : SingularSimplex E 0) :
    (augmentation principalSix E).hom (chainElement principalSix E 0 σ) = (1 : ℚ) :=
  congrArg (fun f => f 1) (congrArg ModuleCat.Hom.hom (generator_augmentation E σ))

theorem singEps_eq_augmentation (E : TopCat.{0}) [MulAction principalSix E] [ContinuousConstSMul principalSix E] :
    singEps (G := principalSix) E = augmentation principalSix E := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply chainRep_linear_ext E
  intro σ
  exact (singEps_chainElement (G := principalSix) E σ).trans (augmentation_chainElement E σ).symm

theorem augF_f_zero : augF.f 0 = faceDiagSystem.eps := by
  refine FaceCone.cone.ext0 ?_ ?_
  · refine (signedLineInclusion_coneDesc _ _ _ _ _ 0).trans ?_
    refine (congrArg (fun m => m.f 0) resAug_lineResolution).trans ?_
    refine (augmentationChain_f_zero ..).trans ?_
    exact (singEps_eq_augmentation (TopCat.of LineFaceSum)).symm.trans
      (FaceCone.cone.iL0_desc0 _ _).symm
  · refine (signedPlaneInclusion_coneDesc _ _ _ _ _ 0).trans ?_
    refine (congrArg (fun m => m.f 0) resAug_planeResolution).trans ?_
    refine (augmentationChain_f_zero ..).trans ?_
    exact (singEps_eq_augmentation (TopCat.of PlaneFaceSum)).symm.trans
      (FaceCone.cone.iP0_desc0 _ _).symm

theorem resAug_f_zero_line : (resAug resLine).f 0 = nerveEps Γ6 RationalGL3 Line := by
  have h1 : (resAug resLine).f 0 = resLine.π.f 0 ≫ labelSum := by
    simp [resAug]
  rw [h1]
  have h2 : resLine.π.f 0 = prodEps Γ6 RationalGL3 Line := by
    simp [resLine, prodResolution, prodEpsToSingle]
  rw [h2]
  refine hom_ext_single ((Fin (0 + 1) → RationalGL3) × Line) _ (fun y => ?_)
  obtain ⟨x, z⟩ := y
  change labelSum ((prodEps Γ6 RationalGL3 Line).hom (MonoidAlgebra.single (x, z) 1)) = _
  rw [prodEps_single, labelSum_single]
  exact (nerveEps_single Γ6 RationalGL3 Line (x, z)).symm

theorem resAug_f_zero_plane : (resAug resPlane).f 0 = nerveEps Γ6 RationalGL3 Plane := by
  have h1 : (resAug resPlane).f 0 = resPlane.π.f 0 ≫ labelSum := by
    simp [resAug]
  rw [h1]
  have h2 : resPlane.π.f 0 = prodEps Γ6 RationalGL3 Plane := by
    simp [resPlane, prodResolution, prodEpsToSingle]
  rw [h2]
  refine hom_ext_single ((Fin (0 + 1) → RationalGL3) × Plane) _ (fun y => ?_)
  obtain ⟨x, z⟩ := y
  change labelSum ((prodEps Γ6 RationalGL3 Plane).hom (MonoidAlgebra.single (x, z) 1)) = _
  rw [prodEps_single, labelSum_single]
  exact (nerveEps_single Γ6 RationalGL3 Plane (x, z)).symm

theorem augR_f_zero : augR.f 0 = modelDiagSystem.eps := by
  refine modelPush.ext0 ?_ ?_
  · refine (signedLineInclusion_coneDesc _ _ _ _ _ 0).trans ?_
    exact resAug_f_zero_line.trans (modelPush.iL0_desc0 _ _).symm
  · refine (signedPlaneInclusion_coneDesc _ _ _ _ _ 0).trans ?_
    exact resAug_f_zero_plane.trans (modelPush.iP0_desc0 _ _).symm

/-- The carrier-respecting comparison `Ψ_F'` of the model cone with the face cone preserves the augmentation (and is
carried, `CarriedPsi`, which is what makes it canonical: `carried_canonical`). -/
theorem exists_PsiF_aug : ∃ u : coneR ⟶ SymmetricSpaceBoundaryGeometricCone.faceCone, CarriedPsi u ∧ QuasiIso u ∧
    u ≫ augF = augR ∧
    ∀ {W : Rep.{0} ℚ Γ6} {n : ℕ} (c : SymmetricSpaceBoundaryGeometricCone.faceCone.X n ⟶ W)
      (hc : SymmetricSpaceBoundaryGeometricCone.faceCone.d (n+1) n ≫ c = 0),
      CapSystem.Homotopic modelDiagSystem.toCapSystem faceDiagSystem.toCapSystem u c hc := by
  obtain ⟨u, hu, heps, hq⟩ := exists_PsiF_carried
  refine ⟨u, ⟨hu, heps⟩, hq, ?_, fun c hc => ?_⟩
  · apply eq_of_f_zero_single₀
    change u.f 0 ≫ augF.f 0 = augR.f 0
    exact (congrArg (fun m => u.f 0 ≫ m) augF_f_zero).trans (heps.trans augR_f_zero.symm)
  · exact PushCone.pushCone_cap_compat (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
      (pushConeOfCofiber SymmetricSpaceBoundaryFaceAugmentation.lineChainMap SymmetricSpaceBoundaryFaceAugmentation.planeChainMap) modelLabels FaceCone.targets
      (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
      (nerveDiagSystem Γ6 RationalGL3 Plane) FaceCone.SA FaceCone.SL FaceCone.SP model_strict FaceCone.strict
      FaceCone.good model_diag FaceCone.respects_flag FaceCone.respects_line FaceCone.respects_plane
      u hu heps c hc

/-- The comparison `Ψ' = u ≫ faceConeToBoundary` with a carried `u`. -/
def IsCarriedPsi (Ψ : coneR ⟶ boundaryChains) : Prop :=
  ∃ u : coneR ⟶ SymmetricSpaceBoundaryGeometricCone.faceCone, CarriedPsi u ∧ Ψ = u ≫ faceConeToBoundary

/-- **The comparison `Ψ' : coneR ⟶ boundaryChains` of `exists_PsiPrime`, over the augmentation.** -/
theorem exists_PsiPrime_aug : ∃ Ψ : coneR ⟶ boundaryChains, IsCarriedPsi Ψ ∧ QuasiIso Ψ ∧ Ψ ≫ augB = augR ∧
    ∀ {W : Rep.{0} ℚ Γ6} {n : ℕ} (c : boundaryChains.X n ⟶ W) (hc : boundaryChains.d (n+1) n ≫ c = 0),
      CapSystem.Homotopic modelDiagSystem.toCapSystem boundaryDiagSystem.toCapSystem Ψ c hc := by
  obtain ⟨u, hcar, hq, haug, H⟩ := exists_PsiF_aug
  refine ⟨u ≫ faceConeToBoundary, ⟨u, hcar, rfl⟩, inferInstance, ?_, fun c hc => ?_⟩
  · rw [Category.assoc, faceConeToBoundary_augB, haug]
  · exact (H (faceConeToBoundary.f _ ≫ c) (chainMap_cocycle faceConeToBoundary c hc)).comp_strict
      faceConeToBoundary faceConeToBoundary_capStrict c hc

theorem exists_PsiPrime_aug_pairing : ∃ Ψ : coneR ⟶ boundaryChains, IsCarriedPsi Ψ ∧ QuasiIso Ψ ∧ Ψ ≫ augB = augR ∧
    ∀ {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
      (b : boundaryChains.X 2 ⟶ W) (_hb : boundaryChains.d (2+1) 2 ≫ b = 0)
      (a : boundaryChains.X 2 ⟶ W') (_ha : boundaryChains.d (2+1) 2 ≫ a = 0)
      (Ω : coneR.X 4) (_hΩ : IsCoinvCycle Ω),
      π.hom (((Ψ.f 2 ≫ b) ⊗ₘ (Ψ.f 2 ≫ a)).hom ((modelDiagSystem.Δ 2 2 4 rfl).hom Ω)) =
        π.hom ((b ⊗ₘ a).hom ((boundaryDiagSystem.Δ 2 2 4 rfl).hom ((Ψ.f 4).hom Ω))) := by
  obtain ⟨Ψ, hcar, hq, haug, H⟩ := exists_PsiPrime_aug
  exact ⟨Ψ, hcar, hq, haug, fun π b hb a ha Ω hΩ =>
    pairing_comparison modelDiagSystem boundaryDiagSystem Ψ π (n := 2) (q := 1) b hb a ha (H b hb) Ω hΩ⟩

theorem facePairing_comparison_aug (Ω : coneR.X 4)
    (hΩ : coinvD coneR 4 3 (Representation.Coinvariants.mk (coneR.X 4).ρ Ω) = 0)
    (hspan : ∀ z : (coneR.X 4).ρ.Coinvariants, coinvD coneR 4 3 z = 0 →
      ∃ c : ℚ, z - c • Representation.Coinvariants.mk (coneR.X 4).ρ Ω ∈ LinearMap.range (coinvD coneR 5 4)) :
    ∃ (Ψ : coneR ⟶ boundaryChains) (κ : ℚ), IsCarriedPsi Ψ ∧ QuasiIso Ψ ∧ Ψ ≫ augB = augR ∧ κ ≠ 0 ∧
      ∀ (V : Rep.{0} ℚ Γ6) (b : boundaryChains.X 2 ⟶ V) (hb : boundaryChains.d (2+1) 2 ≫ b = 0)
        (a : boundaryChains.X 2 ⟶ dualRepresentation V) (ha : boundaryChains.d (2+1) 2 ≫ a = 0),
        (evalRep V).hom (((Ψ.f 2 ≫ b) ⊗ₘ (Ψ.f 2 ≫ a)).hom ((modelDiagSystem.Δ 2 2 4 rfl).hom Ω)) =
          κ * geoPairingBoundary V
            (cochainClass _ 2 (cocycleOf boundaryProjection (dualRepresentation V) 2 a ha))
            (cochainClass _ 2 (cocycleOf boundaryProjection V 2 b hb)) := by
  obtain ⟨Ψ, hcar, hq, haug, Hpair⟩ := exists_PsiPrime_aug_pairing
  have h0 : ∀ n, Projective (resFlag.complex.X n) := fun n => resFlag.projective n
  have h00 : ∀ n, Projective ((resLine.complex ⊞ resPlane.complex).X n) := projective_middle
  have hp1 : ∀ n, Projective (coneR.X n) := fun n =>
    projectiveCone (signedArrow flagLineHom.hom flagPlaneHom.hom) n
  have hp2 : ∀ n, Projective (boundaryChains.X n) := fun n => chainRep_projective principalSix ambient n
  obtain ⟨e, he⟩ : ∃ e : _root_.HomotopyEquiv coneR boundaryChains, e.hom = Ψ :=
    (ChainComplex.quasiIso_iff_of_projective Ψ).mp hq
  set cls := homologyDegreeChange (scalarChains (TopCat.of BoundaryBase)) (2+2) (2+2) rfl
    (ordinaryFundamentalClass 2 boundaryEuclidean boundaryOrientation) with hcls
  obtain ⟨c, hcc⟩ := chainClass_surjective (scalarChains (TopCat.of BoundaryBase)) (2+2) cls
  obtain ⟨ωf, hωf, hΦ⟩ := exists_coinvCycle_lift boundaryProjection boundaryQuotientCovering 3 c.val c.property
  have hωf' : coinvD boundaryChains 4 3 (Representation.Coinvariants.mk (boundaryChains.X 4).ρ ωf) = 0 :=
    (isCoinvCycle_iff_mk_d boundaryChains ωf).1 hωf
  obtain ⟨cc, hcc'⟩ := span_transfer e (Representation.Coinvariants.mk (coneR.X 4).ρ Ω) hspan _ hωf'
  have hcoinv : coinvF e.hom 4 (Representation.Coinvariants.mk (coneR.X 4).ρ Ω) =
      Representation.Coinvariants.mk (boundaryChains.X 4).ρ ((Ψ.f 4).hom Ω) := by
    rw [← he]; rfl
  rw [hcoinv] at hcc'
  have hcc0 : cc ≠ 0 := by
    intro h0
    rw [h0, zero_smul, sub_zero] at hcc'
    obtain ⟨τ, hτ⟩ := pushforward_sub_smul_boundary_four boundaryProjection boundaryQuotientCovering ωf 0 0
      (by rw [zero_smul, sub_zero]; exact hcc')
    rw [zero_smul, sub_zero, hΦ] at hτ
    have hz : chainClass (scalarChains (TopCat.of BoundaryBase)) (2+2) c = 0 :=
      chainClass_eq_zero_of_boundary _ _ c τ hτ
    rw [hcc, hcls] at hz
    have hord : ordinaryFundamentalClass 2 boundaryEuclidean boundaryOrientation = 0 := by
      simpa [homologyDegreeChange] using hz
    have hproj := ordinaryFundamentalClass_projection (B := TopCat.of BoundaryBase) 2 boundaryEuclidean
      boundaryOrientation
    rw [hord, map_zero] at hproj
    exact compactFundamentalClass_ne_zero 2 boundaryEuclidean boundaryOrientation Set.univ isCompact_univ
      Set.univ_nonempty hproj.symm
  refine ⟨Ψ, cc⁻¹, hcar, hq, haug, inv_ne_zero hcc0, fun V b hb a ha => ?_⟩
  have hmodel := Hpair (evalRep V) b hb a ha Ω ((isCoinvCycle_iff_mk_d coneR Ω).2 hΩ)
  have hgeo := geoPairing_eq_pairFun boundaryProjection V boundaryEuclidean boundaryOrientation b hb a ha ωf c
    hΦ.symm hcc
  have hrel := pairFun_eq_of_mem_range boundaryDiagSystem (evalRep V) b hb a ha ωf ((Ψ.f 4).hom Ω) cc hcc'
  have hgeo' : geoPairingBoundary V
      (cochainClass _ 2 (cocycleOf boundaryProjection (dualRepresentation V) 2 a ha))
      (cochainClass _ 2 (cocycleOf boundaryProjection V 2 b hb)) =
      (pairFun boundaryDiagSystem (evalRep V) b a).hom ωf := hgeo
  rw [hgeo', hrel, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcc0, one_mul]
  exact hmodel





end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
