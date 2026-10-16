module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Farey.StokesCan
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Farey.StokesShift
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSNormalFormLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSNormalFormPlane

@[expose] public section


/-!
# From the Hochschild-Serre edge of a mixed class to twisted cusp functions (M3f-1)

Formalized by Claude Sonnet 5.5.

* `edge_class_eq`, `lineEdge_class_eq`, `planeEdge_class_eq`: the cuspidal edge class of a mixed class with relative representative `z` is the class of the crossed homomorphism
  `σ ↦ [splitEdgeCycle σ z] ∈ V = H¹(R, W)` (`splitCocycleEdge`).
* `exists_cusp_function`: a cocycle `C` of `Γ(N)` with values in `V` whose class is cuspidal is `fTw Φ + (v - ρ v)` for a normalised twisted cusp function `Φ` of `transRep V`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open CongruenceSubgroup
open scoped Classical MatrixGroups

variable {N : ℕ}

/-- **The edge class of a relative cocycle is the class of the crossed homomorphism `σ ↦ [splitEdgeCycle σ z]`.** -/
theorem edge_class_eq {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)} (s : ext.Splitting)
    (W : Rep ℂ E) (z : relativeTwoCocycles ext.inl W) :
    splitCohomologyEdge s W (relativeTwoCocycleClass ext.inl W z) =
      groupCohomology.H1π (splitRadicalH1Representation s W) (splitCocycleEdge s W z) :=
  splitCohomologyEdge_apply s W z

/-- The values of the crossed homomorphism `splitCocycleEdge` are the classes of the edge cycles. -/
theorem splitCocycleEdge_val {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (W : Rep ℂ E) (z : relativeTwoCocycles ext.inl W) (σ : Gamma N) :
    (splitCocycleEdge s W z : Gamma N → groupCohomology.H1 (Rep.res ext.inl W)) σ =
      groupCohomology.H1π (Rep.res ext.inl W) (splitEdgeCycle s W σ z) :=
  splitCocycleEdge_apply s W z σ

/-- **Lines:** the edge of a mixed class of the line cusp `h⁻¹Qh` is the class of the crossed homomorphism of any representing relative cocycle. -/
theorem lineEdge_class_eq (N : ℕ) [NeZero N] (h : SL(3, ℤ)) {W : Rep ℂ ↥(gammaNQAt N h)} (x : lineMixedAt N h W)
    (z : relativeTwoCocycles (lineFaceExt N h).inl W)
    (hz : relativeTwoCocycleClass (lineFaceExt N h).inl W z = ⟨x.1, res_radical_of_lineMixedAt x⟩) :
    (mixedEdgeAt N h W x).1 =
      groupCohomology.H1π (splitRadicalH1Representation (lineFaceSplitting N h) W)
        (splitCocycleEdge (lineFaceSplitting N h) W z) := by
  change splitCohomologyEdge (lineFaceSplitting N h) W ⟨x.1, res_radical_of_lineMixedAt x⟩ = _
  rw [← hz]
  exact edge_class_eq _ W z

/-- **Planes.** -/
theorem planeEdge_class_eq (N : ℕ) [NeZero N] (h : SL(3, ℤ)) {W : Rep ℂ ↥(gammaNPAt N h)} (x : planeMixedAt N h W)
    (z : relativeTwoCocycles (faceExt N h).inl W)
    (hz : relativeTwoCocycleClass (faceExt N h).inl W z =
      (⟨x.1, res_radical_of_planeMixedAt x⟩ : (twoCohomologyRestriction (faceExt N h).inl W).ker)) :
    (planeMixedEdgeAt N h W x).1 =
      groupCohomology.H1π (splitRadicalH1Representation (faceSplitting N h) W)
        (splitCocycleEdge (faceSplitting N h) W z) := by
  rw [planeMixedEdgeAt_val N h W x, ← hz]
  exact edge_class_eq _ W z

/-- **A cuspidal crossed homomorphism is a normalised twisted cusp function plus a coboundary.** -/
theorem exists_cusp_function (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) (C : groupCohomology.cocycles₁ V)
    (hC : groupCohomology.H1π V C ∈ cuspidalSubspace (Gamma N) V) :
    ∃ (Φ : Tw (transRep hN V).ρ) (v : V), Φ.1 cusp1 = 0 ∧
      ∀ g : Gamma N, C.1 g = fTw (transRep hN V) Φ.1 (gammaEquiv hN g) + (v - V.ρ g v) := by
  obtain ⟨c', hc', hθ⟩ := thetaIso_hom_π hN V C
  have hmem := (theta_mem_cuspidal_iff hN V _).1 hC
  rw [hθ] at hmem
  obtain ⟨Φ, h0, hΦ⟩ := exists_Tn_of_cuspidal hN (transRep hN V) hmem
  rw [mTw_apply, groupCohomology.H1π_eq_iff] at hΦ
  obtain ⟨v, hv⟩ := hΦ
  refine ⟨Φ, v, h0, fun g => ?_⟩
  have := congrFun hv (gammaEquiv hN g)
  simp only [groupCohomology.d₀₁_hom_apply] at this
  have e1 := hc' (gammaEquiv hN g)
  rw [MulEquiv.symm_apply_apply] at e1
  change (transRep hN V).ρ (gammaEquiv hN g) v - v = fTw (transRep hN V) Φ.1 (gammaEquiv hN g) - c'.1 (gammaEquiv hN g) at this
  rw [transRep_ρ, MulEquiv.symm_apply_apply] at this
  rw [← e1]
  linear_combination (norm := abel) this

/-- If `C = fTw Φ + (v - ρ v)` on `Γ(N)` then the class of `C` corresponds to `mTw Φ` under `thetaIso`. -/
theorem theta_class_of_shape (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) (C : groupCohomology.cocycles₁ V)
    (Φ : Tw (transRep hN V).ρ) (v : V)
    (hC : ∀ g : Gamma N, C.1 g = fTw (transRep hN V) Φ.1 (gammaEquiv hN g) + (v - V.ρ g v)) :
    (thetaIso hN V).hom.hom (groupCohomology.H1π V C) = mTw (transRep hN V) Φ := by
  obtain ⟨c', hc', hθ⟩ := thetaIso_hom_π hN V C
  rw [hθ, mTw_apply, groupCohomology.H1π_eq_iff]
  refine ⟨-v, ?_⟩
  funext g'
  simp only [groupCohomology.d₀₁_hom_apply]
  have e1 := hC ((gammaEquiv hN).symm g')
  rw [MulEquiv.apply_symm_apply] at e1
  have e2 := hc' g'
  change (transRep hN V).ρ g' (-v) - -v = c'.1 g' - fTw (transRep hN V) Φ.1 g'
  rw [e2, e1, transRep_ρ, map_neg]
  abel

/-- **The pairing of two edge classes as a sum over the cusps.** Here `a x = C(γ⁻¹ x)`, `a' x = C'(γ⁻¹ x)` are the crossed homomorphisms of `gammaNGL N`
corresponding to `C`, `C'`, `η` is any primitive of the cup cocycle `⟨a x, x · a' y⟩` (Kosul coupling), and `Φ`, `Φ'` are the normalised twisted cusp functions of
`exists_cusp_function`. -/
theorem edge_pairing_cusp_sum (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (W : Rep ℂ E) [FiniteDimensional ℂ W]
    (C : groupCohomology.cocycles₁ (splitRadicalH1Representation s W))
    (C' : groupCohomology.cocycles₁ (splitRadicalH1Representation s (dualRepG W)))
    (hC : groupCohomology.H1π _ C ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s W))
    (hC' : groupCohomology.H1π _ C' ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG W)))
    (Φ : Tw (transRep hN (splitRadicalH1Representation s W)).ρ)
    (Φ' : Tw (transRep hN (splitRadicalH1Representation s (dualRepG W))).ρ)
    (v : splitRadicalH1Representation s W) (v' : splitRadicalH1Representation s (dualRepG W))
    (h0 : Φ.1 cusp1 = 0)
    (hCΦ : ∀ g : Gamma N, C.1 g = fTw (transRep hN (splitRadicalH1Representation s W)) Φ.1 (gammaEquiv hN g) +
      (v - (splitRadicalH1Representation s W).ρ g v))
    (hCΦ' : ∀ g : Gamma N, C'.1 g = fTw (transRep hN (splitRadicalH1Representation s (dualRepG W))) Φ'.1 (gammaEquiv hN g) +
      (v' - (splitRadicalH1Representation s (dualRepG W)).ρ g v'))
    (η : gammaNGL N → ℂ)
    (hη : ∀ x y, η (x * y) = η x + η y - (leviCoupling hN s hdet W).e (C.1 ((gammaEquiv hN).symm x))
      ((transRep hN (splitRadicalH1Representation s (dualRepG W))).ρ x (C'.1 ((gammaEquiv hN).symm y)))) :
    facePairingCan hN s hdet W ⟨groupCohomology.H1π _ C, hC⟩ ⟨groupCohomology.H1π _ C', hC'⟩ =
      2 * ∑ c ∈ (cuspReps hN).R, ((leviCoupling hN s hdet W).e (Φ.1 c + v) (C'.1 ((gammaEquiv hN).symm (cuspSigma c))) +
        η (cuspSigma c)) := by
  have e1 : (⟨groupCohomology.H1π _ C, hC⟩ : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s W)) =
      (cuspEquiv hN (splitRadicalH1Representation s W)).symm ⟨mTw _ Φ, mTw_mem_cuspidal _ Φ⟩ := by
    rw [LinearEquiv.eq_symm_apply]
    exact Subtype.ext (theta_class_of_shape hN _ C Φ v hCΦ)
  have e2 : (⟨groupCohomology.H1π _ C', hC'⟩ : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG W))) =
      (cuspEquiv hN (splitRadicalH1Representation s (dualRepG W))).symm ⟨mTw _ Φ', mTw_mem_cuspidal _ Φ'⟩ := by
    rw [LinearEquiv.eq_symm_apply]
    exact Subtype.ext (theta_class_of_shape hN _ C' Φ' v' hCΦ')
  rw [e1, e2, facePairingCan_cup hN s hdet W Φ Φ' h0]
  refine cupForm_eq_cusp_sum_gen hN (leviCoupling hN s hdet W) Φ.2 Φ'.2
    (fun x => C.1 ((gammaEquiv hN).symm x)) (fun x => C'.1 ((gammaEquiv hN).symm x)) v v' (fun x => ?_) (fun x => ?_) η hη
  · rw [hCΦ, MulEquiv.apply_symm_apply, transRep_ρ]
  · rw [hCΦ', MulEquiv.apply_symm_apply, transRep_ρ]

/-- **Lines: the canonical pairing of the edges of two mixed classes as a sum over the cusps** (the same for the dual coefficients `dualRepG W`). -/
theorem lineEdge_pairing_cusp_sum [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ)) {W : Rep ℂ ↥(gammaNQAt N h)}
    [FiniteDimensional ℂ W] (x : lineMixedAt N h W) (y : lineMixedAt N h (dualRepG W))
    (z : relativeTwoCocycles (lineFaceExt N h).inl W)
    (hz : relativeTwoCocycleClass (lineFaceExt N h).inl W z =
      (⟨x.1, res_radical_of_lineMixedAt x⟩ : (twoCohomologyRestriction (lineFaceExt N h).inl W).ker))
    (z' : relativeTwoCocycles (lineFaceExt N h).inl (dualRepG W))
    (hz' : relativeTwoCocycleClass (lineFaceExt N h).inl (dualRepG W) z' =
      (⟨y.1, res_radical_of_lineMixedAt y⟩ : (twoCohomologyRestriction (lineFaceExt N h).inl (dualRepG W)).ker))
    (Φ : Tw (transRep hN (splitRadicalH1Representation (lineFaceSplitting N h) W)).ρ)
    (Φ' : Tw (transRep hN (splitRadicalH1Representation (lineFaceSplitting N h) (dualRepG W))).ρ)
    (v : splitRadicalH1Representation (lineFaceSplitting N h) W)
    (v' : splitRadicalH1Representation (lineFaceSplitting N h) (dualRepG W))
    (h0 : Φ.1 cusp1 = 0)
    (hCΦ : ∀ g : Gamma N, (splitCocycleEdge (lineFaceSplitting N h) W z).1 g =
      fTw (transRep hN (splitRadicalH1Representation (lineFaceSplitting N h) W)) Φ.1 (gammaEquiv hN g) +
        (v - (splitRadicalH1Representation (lineFaceSplitting N h) W).ρ g v))
    (hCΦ' : ∀ g : Gamma N, (splitCocycleEdge (lineFaceSplitting N h) (dualRepG W) z').1 g =
      fTw (transRep hN (splitRadicalH1Representation (lineFaceSplitting N h) (dualRepG W))) Φ'.1 (gammaEquiv hN g) +
        (v' - (splitRadicalH1Representation (lineFaceSplitting N h) (dualRepG W)).ρ g v'))
    (η : gammaNGL N → ℂ)
    (hη : ∀ a b, η (a * b) = η a + η b - (leviCoupling hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) W).e
      ((splitCocycleEdge (lineFaceSplitting N h) W z).1 ((gammaEquiv hN).symm a))
      ((transRep hN (splitRadicalH1Representation (lineFaceSplitting N h) (dualRepG W))).ρ a
        ((splitCocycleEdge (lineFaceSplitting N h) (dualRepG W) z').1 ((gammaEquiv hN).symm b)))) :
    facePairingCan hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) W (mixedEdgeAt N h W x)
        (mixedEdgeAt N h (dualRepG W) y) =
      2 * ∑ c ∈ (cuspReps hN).R, ((leviCoupling hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) W).e (Φ.1 c + v)
        ((splitCocycleEdge (lineFaceSplitting N h) (dualRepG W) z').1 ((gammaEquiv hN).symm (cuspSigma c))) +
          η (cuspSigma c)) := by
  have hC : groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting N h) W z) ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation (lineFaceSplitting N h) W) := by
    rw [← lineEdge_class_eq N h x z hz]; exact (mixedEdgeAt N h W x).2
  have hC' : groupCohomology.H1π _ (splitCocycleEdge (lineFaceSplitting N h) (dualRepG W) z') ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation (lineFaceSplitting N h) (dualRepG W)) := by
    rw [← lineEdge_class_eq N h y z' hz']; exact (mixedEdgeAt N h (dualRepG W) y).2
  have e1 : mixedEdgeAt N h W x = ⟨_, hC⟩ := Subtype.ext (lineEdge_class_eq N h x z hz)
  have e2 : mixedEdgeAt N h (dualRepG W) y = ⟨_, hC'⟩ := Subtype.ext (lineEdge_class_eq N h y z' hz')
  rw [e1, e2]
  exact edge_pairing_cusp_sum hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) W _ _ hC hC' Φ Φ' v v' h0 hCΦ hCΦ' η hη


/-- **Planes: the canonical pairing of the edges of two mixed classes as a sum over the cusps** (the same for the dual coefficients `dualRepG W`). -/
theorem planeEdge_pairing_cusp_sum [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ)) {W : Rep ℂ ↥(gammaNPAt N h)}
    [FiniteDimensional ℂ W] (x : planeMixedAt N h W) (y : planeMixedAt N h (dualRepG W))
    (z : relativeTwoCocycles (faceExt N h).inl W)
    (hz : relativeTwoCocycleClass (faceExt N h).inl W z =
      (⟨x.1, res_radical_of_planeMixedAt x⟩ : (twoCohomologyRestriction (faceExt N h).inl W).ker))
    (z' : relativeTwoCocycles (faceExt N h).inl (dualRepG W))
    (hz' : relativeTwoCocycleClass (faceExt N h).inl (dualRepG W) z' =
      (⟨y.1, res_radical_of_planeMixedAt y⟩ : (twoCohomologyRestriction (faceExt N h).inl (dualRepG W)).ker))
    (Φ : Tw (transRep hN (splitRadicalH1Representation (faceSplitting N h) W)).ρ)
    (Φ' : Tw (transRep hN (splitRadicalH1Representation (faceSplitting N h) (dualRepG W))).ρ)
    (v : splitRadicalH1Representation (faceSplitting N h) W)
    (v' : splitRadicalH1Representation (faceSplitting N h) (dualRepG W))
    (h0 : Φ.1 cusp1 = 0)
    (hCΦ : ∀ g : Gamma N, (splitCocycleEdge (faceSplitting N h) W z).1 g =
      fTw (transRep hN (splitRadicalH1Representation (faceSplitting N h) W)) Φ.1 (gammaEquiv hN g) +
        (v - (splitRadicalH1Representation (faceSplitting N h) W).ρ g v))
    (hCΦ' : ∀ g : Gamma N, (splitCocycleEdge (faceSplitting N h) (dualRepG W) z').1 g =
      fTw (transRep hN (splitRadicalH1Representation (faceSplitting N h) (dualRepG W))) Φ'.1 (gammaEquiv hN g) +
        (v' - (splitRadicalH1Representation (faceSplitting N h) (dualRepG W)).ρ g v'))
    (η : gammaNGL N → ℂ)
    (hη : ∀ a b, η (a * b) = η a + η b - (leviCoupling hN (faceSplitting N h) (planeFaceRadicalInput_det N h) W).e
      ((splitCocycleEdge (faceSplitting N h) W z).1 ((gammaEquiv hN).symm a))
      ((transRep hN (splitRadicalH1Representation (faceSplitting N h) (dualRepG W))).ρ a
        ((splitCocycleEdge (faceSplitting N h) (dualRepG W) z').1 ((gammaEquiv hN).symm b)))) :
    facePairingCan hN (faceSplitting N h) (planeFaceRadicalInput_det N h) W (planeMixedEdgeAt N h W x)
        (planeMixedEdgeAt N h (dualRepG W) y) =
      2 * ∑ c ∈ (cuspReps hN).R, ((leviCoupling hN (faceSplitting N h) (planeFaceRadicalInput_det N h) W).e (Φ.1 c + v)
        ((splitCocycleEdge (faceSplitting N h) (dualRepG W) z').1 ((gammaEquiv hN).symm (cuspSigma c))) +
          η (cuspSigma c)) := by
  have hC : groupCohomology.H1π _ (splitCocycleEdge (faceSplitting N h) W z) ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation (faceSplitting N h) W) := by
    rw [← planeEdge_class_eq N h x z hz]; exact (planeMixedEdgeAt N h W x).2
  have hC' : groupCohomology.H1π _ (splitCocycleEdge (faceSplitting N h) (dualRepG W) z') ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation (faceSplitting N h) (dualRepG W)) := by
    rw [← planeEdge_class_eq N h y z' hz']; exact (planeMixedEdgeAt N h (dualRepG W) y).2
  have e1 : planeMixedEdgeAt N h W x = ⟨_, hC⟩ := Subtype.ext (planeEdge_class_eq N h x z hz)
  have e2 : planeMixedEdgeAt N h (dualRepG W) y = ⟨_, hC'⟩ := Subtype.ext (planeEdge_class_eq N h y z' hz')
  rw [e1, e2]
  exact edge_pairing_cusp_sum hN (faceSplitting N h) (planeFaceRadicalInput_det N h) W _ _ hC hC' Φ Φ' v v' h0 hCΦ hCΦ' η hη


end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
