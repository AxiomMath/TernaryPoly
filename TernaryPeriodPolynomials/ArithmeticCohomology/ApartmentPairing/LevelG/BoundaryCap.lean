module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.BoundaryReindex
public import TernaryPeriodPolynomials.Topology.DualityEquivariance.EpsNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.BoundaryEdgeEquivariance

@[expose] public section


/-!
# Equivariance of boundary Poincaré duality (G-2) and of the boundary cap

Formalized by Claude Sonnet 5.5.

For `g ∈ GL₃(ℤ)` and a `GL₃(ℤ)`-module `V₀` (`W = Res V₀`), boundary Poincaré duality `PDboundary W` intertwines the geometric action
`bAct g` on `H₃(∂X̄_Γ; W)` (`BoundaryAction.lean`) with the conjugation action `hcohAct` on boundary cohomology
(`PDboundary_equivariant`); the orientation character is trivial (the boundary orientation is the connecting image of the
`GL₃(ℤ)`-invariant relative fundamental class, `fbarBd_fundamentalClass`).  Proof, after
`RelativeCapConnecting.ordinaryCap_eq_absolute` (the boundary cap is the absolute cap against the boundary fundamental class): the
transported action `Ck` on local cochains pulled back along the twisted pair `PhiB k` is the coefficient reindexing `epsCoch`
 (`Ck_phiBStar`); the absolute cap is natural for the reindexing
(`absolute_eps`, `FiberReindex.cap`) and for the twisted pair over `f̄_k` (`absolute_phiB`, `cap_natural`); `epsLoc ≫ LspaceB = bAct`.
-/

open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG.BR

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalHomology
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.EquivariantSingularResolution TernaryPoly.EquivariantSingularSmall
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCoefficient
  TernaryPoly.FreeActionLinearization TernaryPoly.SingularCoverNaturality
  TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPeriodPolynomials.Argument.DualityEquivariance
  TernaryPeriodPolynomials.Argument.GroupHomology
  TernaryPoly.SingularLocalCompactCap.Algebra TernaryPoly.SingularLocalCap
  TernaryPoly.SymmetricSpaceRelativeCapConnecting TernaryPoly.RelativeCapConnecting
  TernaryPeriodPolynomials.Argument.FiberModel

/-- `f̄_k` fixes the boundary fundamental class. -/
theorem fbarBd_fundamentalClass (k : IntegralGL) :
    homologyMap (SingularCoverNaturality.underlyingMap (fbarBd k)) 4
        SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass =
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass := by
  have h := RationalRelativeSingular.connecting_naturality ⟨fbar k, (fbar k).continuous⟩ (boundary principalSix)
    (boundary principalSix) (fun _ hx => fbar_mem_boundary k hx) 4
  have hf := fundamentalClass_fbar k
  have h1 := ConcreteCategory.congr_hom h SymmetricSpaceRelativeFundamental.fundamentalClass
  change homologyMap (RationalSingularAugmentation.chainMap (RationalRelativeSingular.subspaceMap
      ⟨fbar k, (fbar k).continuous⟩ (boundary principalSix) (boundary principalSix)
      (fun _ hx => fbar_mem_boundary k hx))) 4
    (RationalRelativeSingular.connecting (boundary principalSix) 4
      SymmetricSpaceRelativeFundamental.fundamentalClass) = _
  refine h1.trans ?_
  change RationalRelativeSingular.connecting (boundary principalSix) 4
    (homologyMap (fbarRel k) 5 SymmetricSpaceRelativeFundamental.fundamentalClass) = _
  rw [hf]
  rfl


variable (k : IntegralGL) (V₀ : Rep.{0} ℚ IntegralGL)

/-- Pullback of boundary Hom cochains along the twisted boundary pair. -/
def bHomPull (V : Rep.{0} ℚ principalSix) : homCochains boundaryChains V ⟶ homCochains (boundaryChainsTw k) V :=
  homPullback (chainPhiB k) V

/-- The underlying homeomorphism `BoundaryTw k ≅ BoundaryCover` as a morphism of spaces. -/
def hB : TopCat.of (BoundaryTw k) ⟶ TopCat.of BoundaryCover :=
  TopCat.ofHom ⟨fun x => ⟨x.1.val, x.2⟩, (BoundaryTw.homeo k).continuous⟩

theorem PhiB_eq : PhiB k = hB k ≫ scalarMap IntegralGL (TopCat.of BoundaryCover) k := rfl

theorem chainPhiB_f_apply (n : ℕ) (x : (underlyingChains (TopCat.of (BoundaryTw k))).X n) :
    ((chainPhiB k).f n).hom x =
      (bdryAct.act n).ρ k (((underlyingMap (hB k)).f n).hom x) := by
  have h : underlyingMap (PhiB k) =
      underlyingMap (hB k) ≫ scalarChainMap IntegralGL (TopCat.of BoundaryCover) k := by
    rw [PhiB_eq]
    exact Functor.map_comp _ _ _
  exact congrArg (fun m => (m.f n).hom x) h

theorem hcAct_bHomPull_apply (n : ℕ) (φ : boundaryChains.X n ⟶ Rep.res principalSix.subtype V₀)
    (y : (boundaryChainsTw k).X n) :
    ((bHomPull k (Rep.res principalSix.subtype V₀)).f n
      ((hcAct bdryAct (GAct.ofRep principalSix V₀) k).f n φ)).hom y =
    V₀.ρ k (φ.hom (((underlyingMap (hB k)).f n).hom y)) := by
  change V₀.ρ k (φ.hom ((bdryAct.act n).ρ k⁻¹ (((chainPhiB k).f n).hom y))) = _
  have inv : ∀ w, (bdryAct.act n).ρ k⁻¹ ((bdryAct.act n).ρ k w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  exact congrArg (fun z => V₀.ρ k (φ.hom z))
    ((congrArg ((bdryAct.act n).ρ k⁻¹) (chainPhiB_f_apply k n y)).trans (inv _))

/-- The lift of a simplex of the twisted boundary cover to the boundary cover. -/
def liftUntwB {n : ℕ} {σ : SingularSimplex (TopCat.of BoundaryBase) n} (τ : Lifts (pbTw k) σ) :
    Lifts boundaryProjection σ :=
  ⟨CoveringSingularOrbits.projection (hB k) n τ.val, τ.property⟩

theorem cochainIsoB_eps (n : ℕ) (φ : boundaryChains.X n ⟶ Rep.res principalSix.subtype V₀) :
    (cochainIso (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀)).hom.f n
      ((bHomPull k (Rep.res principalSix.subtype V₀)).f n
        ((hcAct bdryAct (GAct.ofRep principalSix V₀) k).f n φ)) =
    (epsReindex k V₀).cochain n
      ((cochainIso boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀)).hom.f n φ) := by
  funext σ
  apply Subtype.ext
  funext e
  obtain ⟨τ, rfl⟩ := (liftVertexEquiv (pbTw k) (twisted_boundary_covering k) σ).surjective e
  have hL := homVertexEquiv_lift (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀) n
    ((bHomPull k (Rep.res principalSix.subtype V₀)).f n
        ((hcAct bdryAct (GAct.ofRep principalSix V₀) k).f n φ)) τ
  have hR := homVertexEquiv_lift boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) n φ
    (liftUntwB k τ)
  have hgen := congrArg (fun m => m.hom (1 : ℚ)) (generator_map (hB k) n τ.val)
  have hK := hcAct_bHomPull_apply k V₀ n φ
    (((TopCat.toSSet.obj (TopCat.of (BoundaryTw k))).ιChainComplex (R := ModuleCat.of ℚ ℚ) τ.val) 1)
  refine hL.trans ?_
  refine Eq.trans ?_ (congrArg (V₀.ρ k) hR).symm
  exact hK.trans (congrArg (fun z => V₀.ρ k (φ.hom z)) hgen)

/-- The action of `k` on the geometric local cochains of the boundary (transport of `hcAct` along `cochainIso`). -/
def Ck : localCochains boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) ⟶
    localCochains boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) :=
  (cochainIso boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀)).inv ≫
    hcAct bdryAct (GAct.ofRep principalSix V₀) k ≫
    (cochainIso boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀)).hom

/-- **The acted cochain, pulled back along the twisted pair, is the coefficient reindexing** (★). -/
theorem Ck_phiBStar :
    Ck k V₀ ≫ phiBStar k (Rep.res principalSix.subtype V₀) = epsCoch k V₀ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro u
  set φ := ((cochainIso boundaryProjection boundaryQuotientCovering
    (Rep.res principalSix.subtype V₀)).inv.f n).hom u with hφ
  have hu : ((cochainIso boundaryProjection boundaryQuotientCovering
      (Rep.res principalSix.subtype V₀)).hom.f n).hom φ = u := by
    rw [hφ]
    exact congrArg (fun m => (m.f n).hom u)
      (Iso.inv_hom_id (cochainIso boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀)))
  have hp := cochainIso_pullback (pbTw k) boundaryProjection (PhiB k) (fbarBd k) (sqB k)
    (twisted_boundary_covering k) boundaryQuotientCovering (PhiB_equivariant k)
    (Rep.res principalSix.subtype V₀)
  have hp' := congrArg (fun m => (m.f n).hom ((hcAct bdryAct (GAct.ofRep principalSix V₀) k).f n φ)) hp
  have he := cochainIsoB_eps k V₀ n φ
  change (phiBStar k (Rep.res principalSix.subtype V₀)).f n
      (((cochainIso boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀)).hom.f n)
        ((hcAct bdryAct (GAct.ofRep principalSix V₀) k).f n φ)) = (epsReindex k V₀).cochain n u
  rw [← hu]
  exact hp'.symm.trans he


variable (W : Rep.{0} ℚ principalSix)

/-- **(BE)** The absolute cap is natural for the coefficient reindexing. -/
theorem absolute_eps (u : (localCochains boundaryProjection boundaryQuotientCovering
      (Rep.res principalSix.subtype V₀)).homology 1)
    (c : (scalarChains (TopCat.of BoundaryBase)).homology (1 + 3)) :
    absolute (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀) 1 3
        (homologyMap (epsCoch k V₀) 1 u) c =
      homologyMap (epsLoc k V₀) 3
        (absolute boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) 1 3 u c) := by
  obtain ⟨x, rfl⟩ := cochainClass_surjective (localCochains boundaryProjection boundaryQuotientCovering
    (Rep.res principalSix.subtype V₀)) 1 u
  obtain ⟨d, rfl⟩ := chainClass_surjective (scalarChains (TopCat.of BoundaryBase)) (1 + 3) c
  let y : Homology.Cycles ((localCochains (pbTw k) (twisted_boundary_covering k)
      (Rep.res principalSix.subtype V₀)).sc' (1 - 1) 1 (1 + 1)) :=
    ⟨(epsCoch k V₀).f 1 x.val, by
      change (localCochains (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀)).d 1 (1 + 1) _ = 0
      erw [complexMap_d]
      have hx : (localCochains boundaryProjection boundaryQuotientCovering
        (Rep.res principalSix.subtype V₀)).d 1 (1 + 1) x.val = 0 := x.property
      rw [hx, map_zero]⟩
  rw [cochainClass_natural (epsCoch k V₀) 1 x y rfl, absolute_representatives, absolute_representatives]
  refine (chainClass_natural (epsLoc k V₀) 3 _ _ ?_).symm
  exact (FiberReindex.cap (epsReindex k V₀) 1 3 _ _).trans (epsLoc_f_eq k V₀ 3 _).symm

/-- **(BN)** The absolute cap is natural for the twisted pair over `f̄_k`. -/
theorem absolute_phiB (u : (localCochains boundaryProjection boundaryQuotientCovering W).homology 1)
    (c : (scalarChains (TopCat.of BoundaryBase)).homology (1 + 3)) :
    homologyMap (LspaceB k W) 3
        (absolute (pbTw k) (twisted_boundary_covering k) W 1 3 (homologyMap (phiBStar k W) 1 u) c) =
      absolute boundaryProjection boundaryQuotientCovering W 1 3 u
        (homologyMap (scalarSpaceMap (fbarBd k)) (1 + 3) c) := by
  obtain ⟨x, rfl⟩ := cochainClass_surjective (localCochains boundaryProjection boundaryQuotientCovering W) 1 u
  obtain ⟨d, rfl⟩ := chainClass_surjective (scalarChains (TopCat.of BoundaryBase)) (1 + 3) c
  let y : Homology.Cycles ((localCochains (pbTw k) (twisted_boundary_covering k) W).sc' (1 - 1) 1 (1 + 1)) :=
    ⟨(phiBStar k W).f 1 x.val, by
      change (localCochains (pbTw k) (twisted_boundary_covering k) W).d 1 (1 + 1) _ = 0
      erw [complexMap_d]
      have hx : (localCochains boundaryProjection boundaryQuotientCovering W).d 1 (1 + 1) x.val = 0 := x.property
      rw [hx, map_zero]⟩
  let d' : Homology.Cycles ((scalarChains (TopCat.of BoundaryBase)).sc' (1 + 3 + 1) (1 + 3) (1 + 3 - 1)) :=
    ⟨(scalarSpaceMap (fbarBd k)).f (1 + 3) d.val, by
      change (scalarChains (TopCat.of BoundaryBase)).d (1 + 3) (1 + 3 - 1) _ = 0
      erw [complexMap_d]
      have hd : (scalarChains (TopCat.of BoundaryBase)).d (1 + 3) (1 + 3 - 1) d.val = 0 := d.property
      rw [hd, map_zero]⟩
  rw [cochainClass_natural (phiBStar k W) 1 x y rfl, chainClass_natural (scalarSpaceMap (fbarBd k)) (1 + 3) d d' rfl,
    absolute_representatives, absolute_representatives]
  refine chainClass_natural (LspaceB k W) 3 _ _ ?_
  exact cap_natural (pbTw k) boundaryProjection (PhiB k) (fbarBd k) (sqB k) (twisted_boundary_covering k)
    boundaryQuotientCovering (PhiB_equivariant k) W 1 3 x.val d.val |>.symm


/-- **Boundary cap equivariance** (trivial orientation character): the boundary cap isomorphism against the boundary fundamental
class intertwines the transported conjugation action `Ck` on local cohomology with the geometric action `bAct` on local
homology. -/
theorem boundaryCap_equivariant (u : (localCochains boundaryProjection boundaryQuotientCovering
      (Rep.res principalSix.subtype V₀)).homology 1) :
    (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (Rep.res principalSix.subtype V₀)
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom (homologyMap (Ck k V₀) 1 u) =
      homologyMap (bAct V₀ k) 3 ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso
        (Rep.res principalSix.subtype V₀) SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom u) := by
  set c := SingularLocalCompactCap.homologyDegreeChange (scalarChains (TopCat.of BoundaryBase)) (2 + 2) (1 + 3)
    (show 1 + 3 = 2 + 2 from rfl).symm
    (HalfSpaceBoundaryOrientation.ordinaryFundamentalClass 2 SymmetricSpaceBoundaryManifold.boundaryEuclidean
      SymmetricSpaceBoundaryOrientation.boundaryOrientation) with hc
  have e1 : ∀ x, (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (Rep.res principalSix.subtype V₀)
      SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom x =
      absolute boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) 1 3 x c :=
    fun x => ordinaryCap_eq_absolute boundaryProjection (Rep.res principalSix.subtype V₀) 2
      SymmetricSpaceBoundaryManifold.boundaryEuclidean SymmetricSpaceBoundaryOrientation.boundaryOrientation 1 3 rfl x
  have hfix : homologyMap (scalarSpaceMap (fbarBd k)) (1 + 3) c = c := by
    have h1 := fbarBd_fundamentalClass k
    rw [SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass_eq_ordinary] at h1
    have h2 := congrArg (fun y => SingularLocalCompactCap.homologyDegreeChange (scalarChains (TopCat.of BoundaryBase))
      (2 + 2) (1 + 3) (show 1 + 3 = 2 + 2 from rfl).symm y) h1
    have hn := congrArg (fun m => m (HalfSpaceBoundaryOrientation.ordinaryFundamentalClass 2
      SymmetricSpaceBoundaryManifold.boundaryEuclidean SymmetricSpaceBoundaryOrientation.boundaryOrientation))
      (SingularLocalCompactCap.homologyDegreeChange_natural (scalarSpaceMap (fbarBd k)) (2 + 2) (1 + 3)
        (show 1 + 3 = 2 + 2 from rfl).symm)
    have hn' : homologyMap (scalarSpaceMap (fbarBd k)) (1 + 3) c =
        SingularLocalCompactCap.homologyDegreeChange (scalarChains (TopCat.of BoundaryBase)) (2 + 2) (1 + 3)
          (show 1 + 3 = 2 + 2 from rfl).symm (homologyMap (scalarSpaceMap (fbarBd k)) (2 + 2)
            (HalfSpaceBoundaryOrientation.ordinaryFundamentalClass 2
              SymmetricSpaceBoundaryManifold.boundaryEuclidean
              SymmetricSpaceBoundaryOrientation.boundaryOrientation)) := hn
    rw [hn']
    exact congrArg _ h1
  rw [e1, e1]
  have hCk : homologyMap (phiBStar k (Rep.res principalSix.subtype V₀)) 1 (homologyMap (Ck k V₀) 1 u) =
      homologyMap (epsCoch k V₀) 1 u := by
    rw [← ConcreteCategory.comp_apply, ← homologyMap_comp, Ck_phiBStar]
  have hBA : homologyMap (LspaceB k (Rep.res principalSix.subtype V₀)) 3
      (homologyMap (epsLoc k V₀) 3 ((absolute boundaryProjection boundaryQuotientCovering
        (Rep.res principalSix.subtype V₀) 1 3) u c)) =
      homologyMap (bAct V₀ k) 3 ((absolute boundaryProjection boundaryQuotientCovering
        (Rep.res principalSix.subtype V₀) 1 3) u c) := by
    rw [← ConcreteCategory.comp_apply, ← homologyMap_comp, epsLoc_LspaceB_eq]
  calc absolute boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) 1 3
        (homologyMap (Ck k V₀) 1 u) c
      = absolute boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) 1 3
        (homologyMap (Ck k V₀) 1 u) (homologyMap (scalarSpaceMap (fbarBd k)) (1 + 3) c) := by rw [hfix]
    _ = homologyMap (LspaceB k (Rep.res principalSix.subtype V₀)) 3
        (absolute (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀) 1 3
          (homologyMap (phiBStar k (Rep.res principalSix.subtype V₀)) 1 (homologyMap (Ck k V₀) 1 u)) c) :=
        (absolute_phiB k _ _ c).symm
    _ = homologyMap (LspaceB k (Rep.res principalSix.subtype V₀)) 3
        (absolute (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀) 1 3
          (homologyMap (epsCoch k V₀) 1 u) c) := by rw [hCk]
    _ = _ := by rw [absolute_eps, hBA]

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary) in
/-- **Equivariance of boundary Poincaré duality** (O-G1, trivial orientation character): for `g ∈ GL₃(ℤ)`,
`PD_∂(g · c) = g · PD_∂(c)`, where `g` acts on boundary homology by the geometric action `bAct` and on boundary cohomology by
the conjugation action `hcohAct` (`φ ↦ ρ(g) ∘ φ ∘ g⁻¹`). -/
theorem PDboundary_equivariant (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    PDboundary (Rep.res principalSix.subtype V₀) (homologyMap (bAct V₀ k) 3 c) =
      hcohAct bdryAct (GAct.ofRep principalSix V₀) k 1
        (PDboundary (Rep.res principalSix.subtype V₀) c) := by
  let A := SymmetricSpaceBoundaryManifold.boundaryH1CapIso (Rep.res principalSix.subtype V₀)
    SymmetricSpaceBoundaryOrientation.boundaryOrientation
  have h1 : A.inv (homologyMap (bAct V₀ k) 3 c) = homologyMap (Ck k V₀) 1 (A.inv c) := by
    apply (ConcreteCategory.bijective_of_isIso A.hom).injective
    rw [Iso.inv_hom_id_apply, boundaryCap_equivariant, Iso.inv_hom_id_apply]
  change (OrdinaryBoundaryActualEvaluation.boundaryCohomologyIso (Rep.res principalSix.subtype V₀)).inv
      (A.inv (homologyMap (bAct V₀ k) 3 c)) = _
  rw [h1]
  change homologyMap (cochainIso boundaryProjection boundaryQuotientCovering
      (Rep.res principalSix.subtype V₀)).inv 1
    (homologyMap (Ck k V₀) 1 (A.inv c)) = homologyMap (hcAct bdryAct (GAct.ofRep principalSix V₀) k) 1
      (homologyMap (cochainIso boundaryProjection boundaryQuotientCovering
        (Rep.res principalSix.subtype V₀)).inv 1 (A.inv c))
  unfold Ck
  simp only [homologyMap_comp, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply (homologyMap (cochainIso boundaryProjection boundaryQuotientCovering
      (Rep.res principalSix.subtype V₀)).hom 1), ← homologyMap_comp, Iso.hom_inv_id, homologyMap_id]
  rfl

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG.BR
