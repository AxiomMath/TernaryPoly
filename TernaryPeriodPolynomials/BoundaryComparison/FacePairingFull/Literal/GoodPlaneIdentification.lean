module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.GoodPlanePresentation

@[expose] public section


/-!
# The good-plane edge dictionary versus the Hochschild-Serre dictionary

At the good plane the literal dictionary of `Literal.Dict` is `ξ ↦ goodPlaneEdge (cuspRes true ξ)`, the library's edge
(`GoodPlaneEdge3`): conjugation by the rational frame `gF` to block coordinates, the Hochschild-Serre edge of
`1 → ℤ² → ΛG → Γ₁'(3) × ℤˣ → 1`, the Kostant coordinate and the transport `Φ = Sym^{n+1}(diag(1,3))` to
`H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`.

`gpLocallyInnerEquiv` is the generic Hochschild-Serre isomorphism of `Face/Iso` for the stabilizer of the cusp flag
`cuspFlag .plane true` with the presentation `gpIota` (`GoodPlanePresentation`), and `gpPsi` the Kostant coordinate
(`gpTheta`) of the mixed class restricted to `Γ₁'(3)` and transported by `Φ`.

* `goodPlaneParabolic_eq_hs`: for every inner plane class `ξ` (`n > 0`),
  `goodPlaneParabolic ξ = gpPsi (gpLocallyInnerEquiv (local class of ξ at the good plane))`, **sign `+1`**: a genuine
  comparison of the library's edge map with the mixed class, not a definitional equality (`Face.goodPlaneLocallyInnerEquivParabolic`
  is *defined* by the edge map).

Scope. The presentation `gpIota` of the stabilizer is the library's own (`goodPlaneSplitting` conjugated by `gF`), which is
the one the dictionary maps use. `Face.goodPlaneLocallyInnerEquiv` (at the flag `dualFlag standardBadLine`, split presentation
transported from the bad line along `φ`) is a different presentation of a level-conjugate stabilizer; its comparison with this
one is not asserted.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3a
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree (parabolicCrossedH1)
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
open TernaryPeriodPolynomials.Argument.FacePairingFull.Literal
open TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.GoodPlaneId

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.GoodPlaneId

variable (n : ℕ)

/-- The radical representation of the good-plane cusp, on the library presentation. -/
abbrev gpRad := (gpRep n).comp SemidirectProduct.inl

/-- The Levi action on the radical cohomology. -/
abbrev gpAction : Representation ℂ Levi (CrossedH1 (gpRad n)) :=
  leviCrossedH1Representation goodPlaneSplitting.conjAct (gpRep n)

theorem gpA_cancel (v : HomogeneousPoly n) :
    gpA n (rationalCoefficientComponent n trivialCharacter gF v) = v := by
  change rationalCoefficientComponent n trivialCharacter gF⁻¹
    (rationalCoefficientComponent n trivialCharacter gF v) = v
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem gpA_cancel' (v : HomogeneousPoly n) :
    rationalCoefficientComponent n trivialCharacter gF (gpA n v) = v := by
  change rationalCoefficientComponent n trivialCharacter gF
    (rationalCoefficientComponent n trivialCharacter gF⁻¹ v) = v
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- `ρ(gF)⁻¹` as a linear equivalence. -/
def gpAeq : HomogeneousPoly n ≃ₗ[ℂ] HomogeneousPoly n :=
  { gpA n with
    invFun := rationalCoefficientComponent n trivialCharacter gF
    left_inv := fun v => gpA_cancel' n v
    right_inv := fun v => gpA_cancel n v }

theorem gp_transport_eq :
    coefficientTransportRepresentation (gpRad n) (gpAeq n) = (upperRadicalLatticeRep n).ρ := by
  apply MonoidHom.ext
  intro r
  apply LinearMap.ext
  intro v
  rw [coefficientTransportRepresentation_apply]
  change gpA n (gpRep n (SemidirectProduct.inl r)
    (rationalCoefficientComponent n trivialCharacter gF v)) = _
  rw [gpA_intertwine, gpA_cancel, sigma_inl]
  rfl

/-- Crossed `H¹` of the radical (face presentation) versus Mathlib `H¹` of the lattice representation, through the
coefficient change `ρ(gF)⁻¹`. -/
def gpTheta0 : CrossedH1 (gpRad n) ≃ₗ[ℂ] groupCohomology.H1 (upperRadicalLatticeRep n) :=
  ((crossedH1CoefficientEquiv (gpRad n) (gpAeq n)).trans
    (crossedH1RepresentationEqEquiv _ _ (gp_transport_eq n))).trans
    (h1EquivCrossed (upperRadicalLatticeRep n))

/-- The one-cocycle of the lattice representation attached to a crossed cocycle of the face presentation. -/
def gpCoc (φ : crossedCocycles (gpRad n)) : groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  cocycleOfCrossed (upperRadicalLatticeRep n)
    (crossedRepresentationEqEquiv _ _ (gp_transport_eq n)
      (crossedCoefficientEquiv (gpRad n) (gpAeq n) φ))

theorem gpTheta0_mk (φ : crossedCocycles (gpRad n)) :
    gpTheta0 n ((crossedBoundaries (gpRad n)).mkQ φ) =
      groupCohomology.H1π (upperRadicalLatticeRep n) (gpCoc n φ) := rfl

theorem gpCoc_apply (φ : crossedCocycles (gpRad n)) (r : RadicalLattice) :
    (gpCoc n φ) r = gpA n (φ.val r) := rfl

theorem gpCoc_levi (l : Levi) (φ : crossedCocycles (gpRad n)) :
    gpCoc n (leviCrossedAction goodPlaneSplitting.conjAct (gpRep n) l φ) =
      splitRadicalCocycleAction goodPlaneSplitting (coefRep n) l (gpCoc n φ) := by
  apply Subtype.ext
  funext r
  change gpA n (gpRep n (SemidirectProduct.inr l) (φ.val (goodPlaneSplitting.conjAct l⁻¹ r))) =
    (coefRep n).ρ (goodPlaneSplitting l) (gpA n (φ.val (goodPlaneSplitting.conjAct l⁻¹ r)))
  rw [gpA_intertwine, sigma_inr]
  rfl

theorem gpTheta0_levi (l : Levi) (c : CrossedH1 (gpRad n)) :
    gpTheta0 n (gpAction n l c) = splitRadicalH1Action goodPlaneSplitting (coefRep n) l (gpTheta0 n c) := by
  obtain ⟨φ, rfl⟩ := (crossedBoundaries (gpRad n)).mkQ_surjective c
  have h2 : gpAction n l ((crossedBoundaries (gpRad n)).mkQ φ) =
      (crossedBoundaries (gpRad n)).mkQ (leviCrossedAction goodPlaneSplitting.conjAct (gpRep n) l φ) :=
    leviCrossedH1Representation_mk _ _ l φ
  rw [h2, gpTheta0_mk, gpTheta0_mk, gpCoc_levi]
  exact (splitRadicalH1Action_apply goodPlaneSplitting (coefRep n) l (gpCoc n φ)).symm

/-- Kostant isomorphism `H¹(N, Sym^n) ≅ Sym^{n+1}` for the good-plane cusp. -/
def gpTheta : CrossedH1 (gpRad n) ≃ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (gpTheta0 n).trans (upperRadicalH1Coordinate n)

theorem gpTheta_levi (m : binaryArithmeticLevel) (d : ℤˣ) (c : CrossedH1 (gpRad n)) :
    gpTheta n (gpAction n (m, d) c) = Mk n m (gpTheta n c) := by
  change upperRadicalH1Coordinate n (gpTheta0 n (gpAction n (m, d) c)) = _
  rw [gpTheta0_levi]
  exact Jh_action n m d _

/-- The function `m ↦ Φ(θ(x(m, 1)))` attached to a crossed cocycle of the Levi, linear in `x`. -/
def gpPsiFun : crossedCocycles (gpAction n) →ₗ[ℂ] (binaryArithmeticLevel → Binary.HomogeneousPoly (n + 1)) :=
  LinearMap.pi (fun m => ((Phi n).comp (gpTheta n).toLinearMap).comp
    ((LinearMap.proj ((m, 1) : Levi)).comp (crossedCocycles (gpAction n)).subtype))

theorem gpPsiFun_apply (x : crossedCocycles (gpAction n)) (m : binaryArithmeticLevel) :
    gpPsiFun n x m = Phi n (gpTheta n (x.val (m, 1))) := rfl

theorem gpPsiFun_mem (x : crossedCocycles (gpAction n)) :
    gpPsiFun n x ∈ crossedCocycles (levelRep (n + 1) (-1)) := by
  intro m m'
  have hx := x.property (m, 1) (m', 1)
  have e : ((m, 1) : Levi) * (m', 1) = (m * m', 1) := Prod.ext rfl (mul_one _)
  rw [e] at hx
  rw [gpPsiFun_apply, gpPsiFun_apply, gpPsiFun_apply, hx, map_add, map_add, gpTheta_levi, levelRep_Phi]

/-- The crossed cocycle of `Γ₁'(3)` obtained from a crossed cocycle of the Levi by restriction to `Γ₁'(3) × 1`, the
Kostant coordinate and `Φ`. -/
def gpPsiCoc : crossedCocycles (gpAction n) →ₗ[ℂ] crossedCocycles (levelRep (n + 1) (-1)) :=
  (gpPsiFun n).codRestrict _ (gpPsiFun_mem n)

theorem gpPsiCoc_apply (x : crossedCocycles (gpAction n)) (m : binaryArithmeticLevel) :
    (gpPsiCoc n x).val m = Phi n (gpTheta n (x.val (m, 1))) := rfl

theorem gpPsiCoc_boundary (v : CrossedH1 (gpRad n)) :
    gpPsiCoc n (crossedBoundary (gpAction n) v) =
      crossedBoundary (levelRep (n + 1) (-1)) (Phi n (gpTheta n v)) := by
  apply Subtype.ext
  funext m
  rw [gpPsiCoc_apply]
  change Phi n (gpTheta n (gpAction n (m, 1) v - v)) =
    levelRep (n + 1) (-1) m (Phi n (gpTheta n v)) - Phi n (gpTheta n v)
  have hsub : ∀ a b : CrossedH1 (gpRad n), gpTheta n (a - b) = gpTheta n a - gpTheta n b :=
    fun a b => (gpTheta n).toLinearMap.map_sub a b
  rw [hsub, map_sub, gpTheta_levi, levelRep_Phi]

/-- Generic: a linear map of crossed cocycles carrying boundaries to boundaries induces a map on crossed `H¹`. -/
def crossedH1Map {G₁ G₂ V₁ V₂ : Type} [Group G₁] [Group G₂] [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] (R₁ : Representation ℂ G₁ V₁) (R₂ : Representation ℂ G₂ V₂)
    (f : crossedCocycles R₁ →ₗ[ℂ] crossedCocycles R₂)
    (hf : ∀ v : V₁, ∃ w : V₂, f (crossedBoundary R₁ v) = crossedBoundary R₂ w) :
    CrossedH1 R₁ →ₗ[ℂ] CrossedH1 R₂ :=
  (crossedBoundaries R₁).mapQ (crossedBoundaries R₂) f (fun _ hx => by
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨w, hw⟩ := hf v
    exact ⟨w, hw.symm⟩)

theorem crossedH1Map_mk {G₁ G₂ V₁ V₂ : Type} [Group G₁] [Group G₂] [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] (R₁ : Representation ℂ G₁ V₁) (R₂ : Representation ℂ G₂ V₂)
    (f : crossedCocycles R₁ →ₗ[ℂ] crossedCocycles R₂)
    (hf : ∀ v : V₁, ∃ w : V₂, f (crossedBoundary R₁ v) = crossedBoundary R₂ w)
    (x : crossedCocycles R₁) :
    crossedH1Map R₁ R₂ f hf ((crossedBoundaries R₁).mkQ x) = (crossedBoundaries R₂).mkQ (f x) := rfl

/-- The Hochschild-Serre composite on classes: Kostant coordinate and `Φ` of the mixed class on `Γ₁'(3)`. -/
def gpPsi : CrossedH1 (gpAction n) →ₗ[ℂ] CrossedH1 (levelRep (n + 1) (-1)) :=
  crossedH1Map (gpAction n) (levelRep (n + 1) (-1)) (gpPsiCoc n)
    (fun v => ⟨_, gpPsiCoc_boundary n v⟩)

theorem gpPsi_mk (x : crossedCocycles (gpAction n)) :
    gpPsi n ((crossedBoundaries (gpAction n)).mkQ x) =
      qcls (levelRep (n + 1) (-1)) (gpPsiCoc n x) :=
  crossedH1Map_mk _ _ _ _ x

variable {n}

theorem sigma_symm_inr (l : Levi) :
    goodPlaneSplitting.semidirectProductMulEquiv.symm (secL l) = SemidirectProduct.inr l := by
  rw [MulEquiv.symm_apply_eq]
  exact (sigma_inr l).symm

theorem gpPush_secL (c₀ : inhomogeneousTwoCycles (gpRep n)) (l : Levi) (x : RadicalLattice) :
    gpPush n c₀ (secL l, radInc x) = gpA n (c₀.val (SemidirectProduct.inr l) (SemidirectProduct.inl x)) := by
  rw [gpPush_apply, sigma_symm_inr, sigma_symm_inl]

theorem gpPush_radInc (c₀ : inhomogeneousTwoCycles (gpRep n)) (l : Levi) (x : RadicalLattice) :
    gpPush n c₀ (radInc x, secL l) = gpA n (c₀.val (SemidirectProduct.inl x) (SemidirectProduct.inr l)) := by
  rw [gpPush_apply, sigma_symm_inr, sigma_symm_inl]

theorem gpCoc_mixed (c₀ : radicalZeroTwoCycles goodPlaneSplitting.conjAct (gpRep n)) (l : Levi) :
    gpCoc n (mixedCrossedMap goodPlaneSplitting.conjAct (gpRep n) l c₀) =
      splitEdgeCycle goodPlaneSplitting (coefRep n) l ⟨gpPush n c₀.val, gpPush_relative n c₀⟩ := by
  refine Subtype.ext (funext fun r => ?_)
  have h1 : gpA n (mixedCrossedCochain goodPlaneSplitting.conjAct (gpRep n) c₀ l r) =
      gpA n (c₀.val.val (SemidirectProduct.inr l)
          (SemidirectProduct.inl (goodPlaneSplitting.conjAct l⁻¹ r))) -
        gpA n (c₀.val.val (SemidirectProduct.inl r) (SemidirectProduct.inr l)) := map_sub _ _ _
  have h2 := gpPush_secL c₀.val l (goodPlaneSplitting.conjAct l⁻¹ r)
  have h3 := gpPush_radInc c₀.val l r
  exact h1.trans (by rw [← h2, ← h3]; rfl)

theorem gpTheta_mixed (c₀ : radicalZeroTwoCycles goodPlaneSplitting.conjAct (gpRep n)) (l : Levi) :
    gpTheta n ((mixedH1CocycleMap goodPlaneSplitting.conjAct (gpRep n) c₀).val l) =
      edgeVal ⟨gpPush n c₀.val, gpPush_relative n c₀⟩ l := by
  change upperRadicalH1Coordinate n (gpTheta0 n ((crossedBoundaries (gpRad n)).mkQ
    (mixedCrossedMap goodPlaneSplitting.conjAct (gpRep n) l c₀))) = _
  rw [gpTheta0_mk, upperRadicalH1Coordinate_apply, gpCoc_mixed]
  rfl

theorem gpPsiCoc_mixed (c₀ : radicalZeroTwoCycles goodPlaneSplitting.conjAct (gpRep n)) :
    gpPsiCoc n (mixedH1CocycleMap goodPlaneSplitting.conjAct (gpRep n) c₀) =
      goodPlaneEdgeCocycle ⟨gpPush n c₀.val, gpPush_relative n c₀⟩ := by
  apply Subtype.ext
  funext m
  rw [gpPsiCoc_apply, gpTheta_mixed]
  rfl

/-- The Hochschild-Serre isomorphism for the good-plane cusp in the library presentation. -/
def gpLocallyInnerEquiv (n : ℕ) :
    locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true) ≃ₗ[ℂ]
      FaceCuspidal goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota :=
  locallyInnerEquivCuspidal goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota
    (leviH2Vanishes_of_binary leviEmbed leviEmbed_injective)
    (fun radical e he => gp_radical_fixes radical e he) leviEmbed leviEmbed_injective

theorem gp_class_eq_mixed (x : H2 (fixedPointLevel rationalLevel (cuspFlag .plane true))
      (rationalCoefficientComponent n trivialCharacter))
    (hxli : x ∈ locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true))
    (c₀ : radicalZeroTwoCycles goodPlaneSplitting.conjAct (gpRep n))
    (hc₀ : (inhomogeneousBoundaries (gpRep n)).mkQ c₀.val =
      faceH2Equiv goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota x) :
    ((gpLocallyInnerEquiv n ⟨x, hxli⟩ :
        FaceCuspidal goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota) :
        CrossedH1 (gpAction n)) =
      (crossedBoundaries (gpAction n)).mkQ
        (mixedH1CocycleMap goodPlaneSplitting.conjAct (gpRep n) c₀) :=
  FaceGeneric.locallyInnerEquivCuspidal_coe_eq_mixed goodPlaneSplitting.conjAct n trivialCharacter
    (cuspFlag .plane true) gpIota (leviH2Vanishes_of_binary leviEmbed leviEmbed_injective)
    (fun radical e he => gp_radical_fixes radical e he) leviEmbed leviEmbed_injective x hxli c₀ hc₀

theorem gp_repExists (x : H2 (fixedPointLevel rationalLevel (cuspFlag .plane true))
      (rationalCoefficientComponent n trivialCharacter))
    (hxli : x ∈ locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true)) :
    ∃ c₀ : radicalZeroTwoCycles goodPlaneSplitting.conjAct (gpRep n),
      (inhomogeneousBoundaries (gpRep n)).mkQ c₀.val =
        faceH2Equiv goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota x :=
  FaceGeneric.exists_radicalZero_representative goodPlaneSplitting.conjAct n trivialCharacter
    (cuspFlag .plane true) gpIota (fun radical e he => gp_radical_fixes radical e he) leviEmbed
    leviEmbed_injective x hxli

/-- The library's good-plane edge of a class represented by a radical-zero face cycle. -/
theorem goodPlaneEdge_eq_of_rep (hn : 0 < n)
    (z : H2 (fixedPointLevel rationalLevel (cuspFlag .plane true))
      (rationalCoefficientComponent n trivialCharacter))
    (c₀ : radicalZeroTwoCycles goodPlaneSplitting.conjAct (gpRep n))
    (hc₀ : (inhomogeneousBoundaries (gpRep n)).mkQ c₀.val =
      faceH2Equiv goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota z) :
    goodPlaneEdge hn z =
      qcls (levelRep (n + 1) (-1)) (goodPlaneEdgeCocycle ⟨gpPush n c₀.val, gpPush_relative n c₀⟩) := by
  induction z using Submodule.Quotient.induction_on with
  | _ C =>
  have h' := hc₀.trans (faceH2Equiv_classOf goodPlaneSplitting.conjAct n trivialCharacter
    (cuspFlag .plane true) gpIota C)
  obtain ⟨u, hu⟩ := (Submodule.Quotient.eq (inhomogeneousBoundaries (gpRep n))).mp h'
  have e2 : c₀.val = faceCycle goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota C +
      (c₀.val - faceCycle goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota C) := by
    abel
  have e3 : gpPush n c₀.val = gpPush n (faceCycle goodPlaneSplitting.conjAct n trivialCharacter
      (cuspFlag .plane true) gpIota C) + gpPush n (c₀.val - faceCycle goodPlaneSplitting.conjAct n
        trivialCharacter (cuspFlag .plane true) gpIota C) := by
    conv_lhs => rw [e2]
    exact gpPush_add n _ _
  have hc : groupCohomology.H2π (coefRep n) (gpPush n c₀.val) =
      groupCohomology.H2π (coefRep n) (ambientCocycleToGroup ΛG (ρn n)
        (GoodPlaneConj.conjCycle (rationalCoefficientComponent n trivialCharacter) gF
          (cuspLevel .plane true) ΛG hH_conj C)) := by
    rw [H2π_conj_eq_push, e3, map_add, ← hu, gpPush_boundary, add_zero]
  exact goodPlaneEdgeH2_apply hn _ ⟨gpPush n c₀.val, gpPush_relative n c₀⟩ hc

/-- **Good plane: the library's explicit edge dictionary is the Hochschild-Serre dictionary.**
For an inner plane class `ξ` (`n > 0`), `goodPlaneParabolic ξ = goodPlaneEdge (cuspRes true ξ)` is (with sign `+1`) the
image of the local class of `ξ` at the good plane under the Hochschild-Serre isomorphism `gpLocallyInnerEquiv` followed by
the Kostant coordinate and `Φ` (`gpPsi`). -/
theorem goodPlaneParabolic_eq_hs (hn : 0 < n) (ξ : innerClasses n .plane) :
    ((goodPlaneParabolic hn ξ : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
        CrossedH1 (levelRep (n + 1) (-1))) =
      gpPsi n ((gpLocallyInnerEquiv n
        ⟨fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
            (cuspFlag .plane true) ξ.val,
          innerBoundary_fixedPointH2_locallyInner ξ.property (cuspFlag .plane true)⟩ :
          FaceCuspidal goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota) :
        CrossedH1 (gpAction n)) := by
  have hxli : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (cuspFlag .plane true) ξ.val ∈
        locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true) :=
    innerBoundary_fixedPointH2_locallyInner ξ.property (cuspFlag .plane true)
  have hrep := gp_repExists _ hxli
  rcases hrep with ⟨c₀, hc₀⟩
  have e1 := gp_class_eq_mixed _ hxli c₀ hc₀
  have e2 := gpPsi_mk n (mixedH1CocycleMap goodPlaneSplitting.conjAct (gpRep n) c₀)
  have e3 := goodPlaneEdge_eq_of_rep hn _ c₀ hc₀
  rw [gpPsiCoc_mixed] at e2
  have e4 := goodPlaneParabolic_coe hn ξ ξ.val rfl
  exact e4.trans (e3.trans (e2.symm.trans (congrArg (gpPsi n) e1.symm)))

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.GoodPlaneId
