module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.LocalReindexFiber
public import TernaryPeriodPolynomials.Topology.DualityEquivariance.FiberReindex
public import TernaryPeriodPolynomials.Topology.DualityEquivariance.Reindex
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.RelativeEquivariance

@[expose] public section


/-!
# `K`-equivariance of the duality, piece (ii)(b): the cap isomorphism and the coefficient reindexing

`epsFib` (post-composition of fibre coefficients with `ρ_{V₀}(k)`, from the fibres of the
gluing to those of the twisted gluing, which have the same underlying space) commutes with the
covering transport (`fibUntw_fiberTransport`: the monodromy of `pTw k = wholeProjection ∘ GluedTw.homeo k`
corresponds to the monodromy of `wholeProjection`).  Hence it is a `FiberReindex` (`epsReindex`), which
induces the cochain map `epsCoch` of geometric local cochains.  The restriction to the boundary
commutes with it pointwise on fibres (`restrTw_eps`), so it induces `epsRel` on relative cochains.

The pullback `relHomPull` composed with the conjugation action `hcAct` of `k` on relative `Hom`-cochains
is `φ ↦ ρ_{V₀}(k) ∘ φ ∘ (identity on simplices)` (`hcAct_relHomPull_apply_pi`, from the equivariance of the
relative projection and `chainPhiW = ρ(k) ∘ hW`), hence corresponds to `epsCoch` under the library's
isomorphism with geometric cochains (`cochainIso_eps`, `relHomGeom_eps`).  The relative cap is natural
for the reindexing (`relCap_eps`, from `FiberReindex.cap` and `epsLoc_f_eq`), and the fundamental class
is not moved since the base map is the identity (`relativeFundamentalCap_eps`).  The result:

`capEps : homologyMap (hcAct relAct B k ≫ relHomPull k V) 2 ≫ relativeHomCapTw k V =
  (relativeHomCapIso V).hom ≫ homologyMap (epsLoc k V₀) 3`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.DualityEquivariance

open CategoryTheory CategoryTheory.Limits TernaryPoly TernaryPoly.SingularLocalCompactCap.Algebra
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.IntegralGL3Congruence TernaryPoly.EquivariantSingularResolution
  TernaryPoly.FreeActionLinearization TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularCoverNaturality TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalHomology
  TernaryPoly.SymmetricSpaceRelativeCapConnecting TernaryPoly.SingularLocalCoefficient
  HomologicalComplex TernaryPoly.EquivariantSingularCohomology
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPeriodPolynomials.Argument.FiberModel
  TernaryPeriodPolynomials.Argument.GroupHomology

/-- Monodromy along a homeomorphism of the total space. -/
theorem monodromy_comp_homeomorph {X E E' : Type} [TopologicalSpace X] [TopologicalSpace E]
    [TopologicalSpace E'] (p : E → X) (cov : IsCoveringMap p) (h : E' ≃ₜ E) (p' : E' → X)
    (hp : ∀ x, p' x = p (h x)) (cov' : IsCoveringMap p') {x y : X}
    (γ : Path.Homotopic.Quotient x y) (e : p' ⁻¹' {x}) :
    h ((cov'.monodromy γ e).1) =
      (cov.monodromy γ ⟨h e.1, by rw [Set.mem_preimage, ← hp]; exact e.2⟩).1 := by
  obtain ⟨γ⟩ := γ
  have hx : γ 0 = p' e.1 := γ.source.trans e.2.symm
  have hx' : γ 0 = p (h e.1) := hx.trans (hp _)
  change h (cov'.liftPath γ e.1 hx 1) = cov.liftPath γ (h e.1) hx' 1
  have key : (⟨h, h.continuous⟩ : C(E', E)).comp (cov'.liftPath γ e.1 hx) =
      cov.liftPath γ (h e.1) hx' := by
    rw [cov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · funext t
      exact (hp _).symm.trans (congrFun (cov'.liftPath_lifts γ e.1 hx) t)
    · exact congrArg h (cov'.liftPath_zero γ e.1 hx)
  exact congrArg (fun c : C(unitInterval, E) => c 1) key

variable (k : IntegralGL) (V₀ : Rep.{0} ℚ IntegralGL)

/-- Monodromy of the twisted covering corresponds to that of the gluing under `fibUntw`. -/
theorem fibUntw_fiberTransport {x y : BordifiedOrbit}
    (γ : Path.Homotopic.Quotient x y) (e : Fiber (pTw k) x) :
    fibUntw k (fiberTransport (pTw k) (twisted_whole_covering k) γ e) =
      fiberTransport wholeProjection wholeQuotientCovering γ (fibUntw k e) :=
  Subtype.ext (monodromy_comp_homeomorph _ wholeQuotientCovering.isCoveringMap (GluedTw.homeo k) _
    (fun _ => rfl) (twisted_whole_covering k).isCoveringMap γ e)

/-- `epsFib` is linear. -/
def epsFibLin (b : BordifiedOrbit) :
    FiberCoefficient wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀) b →ₗ[ℚ]
      FiberCoefficient (pTw k) (twisted_whole_covering k) (Rep.res principalSix.subtype V₀) b where
  toFun := epsFib k V₀ b
  map_add' _ _ := Subtype.ext (funext fun _ => map_add (V₀.ρ k) _ _)
  map_smul' r _ := Subtype.ext (funext fun _ => map_smul (V₀.ρ k) r _)

/-- `epsFib` as a reindexing of the fibre coefficients of the two coverings. -/
def epsReindex : FiberReindex wholeProjection (pTw k) wholeQuotientCovering
    (twisted_whole_covering k) (Rep.res principalSix.subtype V₀) where
  ε := epsFibLin k V₀
  transport {x y} γ c := by
    apply Subtype.ext
    funext e
    change V₀.ρ k ((coefficientTransport wholeProjection wholeQuotientCovering γ c).val (fibUntw k e)) =
      (epsFib k V₀ x c).val (fiberTransport (pTw k) (twisted_whole_covering k) γ.symm e)
    change V₀.ρ k (c.val (fiberTransport wholeProjection wholeQuotientCovering γ.symm (fibUntw k e))) =
      V₀.ρ k (c.val (fibUntw k (fiberTransport (pTw k) (twisted_whole_covering k) γ.symm e)))
    rw [fibUntw_fiberTransport]

theorem gluedAct_eq : gluedAct = ambientGActC := rfl

/-- Evaluation of the composite on the image of an ambient chain. -/
theorem hcAct_relHomPull_apply_pi (n : ℕ)
    (φ : upstairsRelativeChains.X n ⟶ Rep.res principalSix.subtype V₀)
    (y : (ambientChainsTw k).X n) :
    ((relHomPull k (Rep.res principalSix.subtype V₀)).f n
      ((hcAct relAct (GAct.ofRep principalSix V₀) k).f n φ)).hom
        (((cokernel.π (upstairsBoundaryChainMapTw k)).f n).hom y) =
    V₀.ρ k (φ.hom (((cokernel.π upstairsBoundaryChainMap).f n).hom
      (((underlyingMap (hW k)).f n).hom y))) := by
  have e1 : ((relChainMap k).f n).hom (((cokernel.π (upstairsBoundaryChainMapTw k)).f n).hom y) =
      ((cokernel.π upstairsBoundaryChainMap).f n).hom (((chainPhiW k).f n).hom y) :=
    congrArg (fun m => (m.f n).hom y) (relChainMap_π k)
  change V₀.ρ k (φ.hom ((relAct.act n).ρ k⁻¹ (((relChainMap k).f n).hom
    (((cokernel.π (upstairsBoundaryChainMapTw k)).f n).hom y)))) = _
  rw [e1]
  have e2 := upstairsRelativeProjection_gmor n k⁻¹ (((chainPhiW k).f n).hom y)
  have e3 : (ambientGActC.act n).ρ k⁻¹ (((chainPhiW k).f n).hom y) =
      ((underlyingMap (hW k)).f n).hom y := by
    have inv : ∀ w, (ambientGActC.act n).ρ k⁻¹ ((ambientGActC.act n).ρ k w) = w := fun w => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    exact (congrArg ((ambientGActC.act n).ρ k⁻¹) (chainPhiW_f_apply k n y)).trans (inv _)
  rw [gluedAct_eq, e3] at e2
  exact congrArg (fun z => V₀.ρ k (φ.hom z)) e2.symm

/-- The lift of a simplex of the twisted gluing to the gluing. -/
def liftUntw {n : ℕ} {σ : SingularSimplex (TopCat.of BordifiedOrbit) n} (τ : Lifts (pTw k) σ) :
    Lifts wholeProjection σ :=
  ⟨projection (hW k) n τ.val, τ.property⟩

theorem fibUntw_liftVertexEquiv {n : ℕ} {σ : SingularSimplex (TopCat.of BordifiedOrbit) n}
    (τ : Lifts (pTw k) σ) :
    fibUntw k (liftVertexEquiv (pTw k) (twisted_whole_covering k) σ τ) =
      liftVertexEquiv wholeProjection wholeQuotientCovering σ (liftUntw k τ) := rfl

theorem cochainIso_eps (n : ℕ)
    (φ : upstairsRelativeChains.X n ⟶ Rep.res principalSix.subtype V₀) :
    (cochainIso (pTw k) (twisted_whole_covering k) (Rep.res principalSix.subtype V₀)).hom.f n
      ((homPullback (cokernel.π (upstairsBoundaryChainMapTw k)) (Rep.res principalSix.subtype V₀)).f n
        ((relHomPull k (Rep.res principalSix.subtype V₀)).f n
          ((hcAct relAct (GAct.ofRep principalSix V₀) k).f n φ))) =
    (epsReindex k V₀).cochain n
      ((cochainIso wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀)).hom.f n
        ((homPullback (cokernel.π upstairsBoundaryChainMap) (Rep.res principalSix.subtype V₀)).f n φ)) := by
  funext σ
  apply Subtype.ext
  funext e
  obtain ⟨τ, rfl⟩ := (liftVertexEquiv (pTw k) (twisted_whole_covering k) σ).surjective e
  have hL := homVertexEquiv_lift (pTw k) (twisted_whole_covering k) (Rep.res principalSix.subtype V₀) n
    ((homPullback (cokernel.π (upstairsBoundaryChainMapTw k)) (Rep.res principalSix.subtype V₀)).f n
        ((relHomPull k (Rep.res principalSix.subtype V₀)).f n
          ((hcAct relAct (GAct.ofRep principalSix V₀) k).f n φ))) τ
  have hR := homVertexEquiv_lift wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀) n
    ((homPullback (cokernel.π upstairsBoundaryChainMap) (Rep.res principalSix.subtype V₀)).f n φ) (liftUntw k τ)
  have hgen := congrArg (fun m => m.hom (1 : ℚ))
    (generator_map (hW k) n τ.val)
  have hK := hcAct_relHomPull_apply_pi k V₀ n φ
    (((TopCat.toSSet.obj (TopCat.of (GluedTw k))).ιChainComplex (R := ModuleCat.of ℚ ℚ) τ.val) 1)
  refine hL.trans ?_
  refine Eq.trans ?_ (congrArg (V₀.ρ k) hR).symm
  exact hK.trans (congrArg (fun z => V₀.ρ k (φ.hom (((cokernel.π upstairsBoundaryChainMap).f n).hom z))) hgen)

/-- The fibre of the twisted boundary covering is the fibre of the boundary covering. -/
def fibUntwB {b : BoundaryBase} (e : Fiber (pbTw k) b) : Fiber boundaryProjection b :=
  ⟨⟨e.val.1.val, e.val.2⟩, e.property⟩

theorem restrTw_eps (n : ℕ)
    (c : VertexCochain wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀) n)
    (σb : SingularSimplex (TopCat.of BoundaryBase) n) (e' : Fiber (pbTw k) (atVertex σb)) :
    (((restrTw k (Rep.res principalSix.subtype V₀)).f n) ((epsReindex k V₀).cochain n c) σb).val e' =
      V₀.ρ k (((geometricBoundaryRestriction (Rep.res principalSix.subtype V₀)).f n c σb).val
        (fibUntwB k e')) := rfl

/-- The coefficient reindexing as a cochain map of the geometric local cochains. -/
def epsCoch : localCochains wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀) ⟶
    localCochains (pTw k) (twisted_whole_covering k) (Rep.res principalSix.subtype V₀) :=
  (epsReindex k V₀).cochainMap

theorem epsCoch_f_apply (n : ℕ)
    (c : VertexCochain wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀) n) :
    (epsCoch k V₀).f n c = (epsReindex k V₀).cochain n c := rfl

theorem restrTw_epsCoch_ι (n : ℕ)
    (x : (geometricRelativeCochains (Rep.res principalSix.subtype V₀)).X n) :
    (restrTw k (Rep.res principalSix.subtype V₀)).f n ((epsCoch k V₀).f n
      ((kernel.ι (geometricBoundaryRestriction (Rep.res principalSix.subtype V₀))).f n x)) = 0 := by
  have h0 : (geometricBoundaryRestriction (Rep.res principalSix.subtype V₀)).f n
      ((kernel.ι (geometricBoundaryRestriction (Rep.res principalSix.subtype V₀))).f n x) = 0 :=
    congrArg (fun m : geometricRelativeCochains (Rep.res principalSix.subtype V₀) ⟶
      localCochains boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) =>
      ConcreteCategory.hom (m.f n) x) (kernel.condition
      (geometricBoundaryRestriction (Rep.res principalSix.subtype V₀)))
  funext σb
  apply Subtype.ext
  funext e'
  refine (restrTw_eps k V₀ n _ σb e').trans ?_
  rw [h0]
  exact map_zero _

/-- The coefficient reindexing on relative geometric cochains. -/
def epsRel : geometricRelativeCochains (Rep.res principalSix.subtype V₀) ⟶
    relCochTw k (Rep.res principalSix.subtype V₀) :=
  kernel.lift (restrTw k (Rep.res principalSix.subtype V₀))
    (kernel.ι (geometricBoundaryRestriction (Rep.res principalSix.subtype V₀)) ≫ epsCoch k V₀) (by
      apply HomologicalComplex.hom_ext
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact restrTw_epsCoch_ι k V₀ n x)

theorem epsRel_ι : epsRel k V₀ ≫ kernel.ι (restrTw k (Rep.res principalSix.subtype V₀)) =
    kernel.ι (geometricBoundaryRestriction (Rep.res principalSix.subtype V₀)) ≫ epsCoch k V₀ :=
  kernel.lift_ι _ _ _

/-- **Naturality of the Hom-model/geometric comparison for the coefficient reindexing.** -/
theorem relHomGeom_eps :
    (hcAct relAct (GAct.ofRep principalSix V₀) k ≫ relHomPull k (Rep.res principalSix.subtype V₀)) ≫
        (relativeHomGeometricIsoTw k (Rep.res principalSix.subtype V₀)).hom =
      (relativeHomGeometricIso (Rep.res principalSix.subtype V₀)).hom ≫ epsRel k V₀ := by
  apply (cancel_mono (kernel.ι (restrTw k (Rep.res principalSix.subtype V₀)))).mp
  simp only [Category.assoc]
  rw [relHomGeomTw_ι, epsRel_ι, ← Category.assoc (relativeHomGeometricIso (Rep.res principalSix.subtype V₀)).hom,
    relHomGeom_ι]
  simp only [Category.assoc]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact cochainIso_eps k V₀ n φ

theorem epsLoc_f_eq (b : ℕ)
    (c : VertexChain wholeProjection wholeQuotientCovering (Rep.res principalSix.subtype V₀) b) :
    ((epsLoc k V₀).f b).hom c = (epsReindex k V₀).chain b c :=
  LinearMap.congr_fun (FiberReindex.chain_unique (epsReindex k V₀) b ((epsLoc k V₀).f b).hom
    (fun σ c => epsLoc_single k V₀ b σ c)) c

/-- **Naturality of the relative cap for the coefficient reindexing**, on chain-level
representatives. -/
theorem relCap_eps (a b : ℕ) (x : (geometricRelativeCochains (Rep.res principalSix.subtype V₀)).X a)
    (c : (relativeScalarChains boundaryBaseInclusion).X (a + b)) :
    relCapTw k (Rep.res principalSix.subtype V₀) a b ((epsRel k V₀).f a x) c =
      ((epsLoc k V₀).f b) (relCap (Rep.res principalSix.subtype V₀) a b x c) := by
  obtain ⟨c0, rfl⟩ := RelativeAlgebra.projection_surjective (scalarSpaceMap boundaryBaseInclusion)
    (a + b) c
  rw [relCapTw, relCap, relativeCochainCap_projection]
  have h2 := relativeCochainCap_projection boundaryProjection wholeProjection boundaryInclusion
    boundaryBaseInclusion boundary_square boundaryQuotientCovering wholeQuotientCovering
    boundaryInclusion_equivariant (Rep.res principalSix.subtype V₀) a b x c0
  have h1 : (kernel.ι (restrTw k (Rep.res principalSix.subtype V₀))).f a ((epsRel k V₀).f a x) =
      (epsCoch k V₀).f a ((kernel.ι (geometricBoundaryRestriction
        (Rep.res principalSix.subtype V₀))).f a x) :=
    congrArg (fun m : geometricRelativeCochains (Rep.res principalSix.subtype V₀) ⟶
      localCochains (pTw k) (twisted_whole_covering k) (Rep.res principalSix.subtype V₀) =>
      ConcreteCategory.hom (m.f a) x) (epsRel_ι k V₀)
  rw [h1]
  refine Eq.trans ?_ (congrArg ((epsLoc k V₀).f b).hom h2).symm
  exact (FiberReindex.cap (epsReindex k V₀) a b _ _).trans
    (epsLoc_f_eq k V₀ b _).symm

/-- **The cap product with the relative fundamental class is natural for the coefficient
reindexing.**  The base map is the identity, so the fundamental class is not moved. -/
theorem relativeFundamentalCap_eps :
    homologyMap (epsRel k V₀) 2 ≫ relativeFundamentalCapTw k (Rep.res principalSix.subtype V₀) =
      relativeFundamentalCap (Rep.res principalSix.subtype V₀) ≫ homologyMap (epsLoc k V₀) 3 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro xx
  obtain ⟨x, rfl⟩ := cochainClass_surjective (geometricRelativeCochains
    (Rep.res principalSix.subtype V₀)) 2 xx
  obtain ⟨c, hc⟩ := chainClass_surjective (relativeScalarChains boundaryBaseInclusion) (2 + 3)
    SymmetricSpaceRelativeFundamental.fundamentalClass
  let y : Homology.Cycles ((relCochTw k (Rep.res principalSix.subtype V₀)).sc' (2 - 1) 2 (2 + 1)) :=
    ⟨(epsRel k V₀).f 2 x.val, by
      change (relCochTw k (Rep.res principalSix.subtype V₀)).d 2 (2 + 1) _ = 0
      erw [complexMap_d]
      have hx : (geometricRelativeCochains (Rep.res principalSix.subtype V₀)).d 2 (2 + 1) x.val = 0 :=
        x.property
      rw [hx, map_zero]⟩
  have e1 : homologyMap (epsRel k V₀) 2 (Descent.cochainClass _ 2 x) = Descent.cochainClass _ 2 y :=
    cochainClass_natural (epsRel k V₀) 2 x y rfl
  change relativeCochainCapHomology (pbTw k) (pTw k) (incTw k)
      boundaryBaseInclusion (sqTw k) (twisted_boundary_covering k) (twisted_whole_covering k)
      (incTw_equivariant k) (Rep.res principalSix.subtype V₀) 2 3
      (homologyMap (epsRel k V₀) 2 (Descent.cochainClass _ 2 x))
      SymmetricSpaceRelativeFundamental.fundamentalClass =
    homologyMap (epsLoc k V₀) 3 (relativeCochainCapHomology boundaryProjection wholeProjection
      boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
      wholeQuotientCovering boundaryInclusion_equivariant (Rep.res principalSix.subtype V₀) 2 3
      (Descent.cochainClass _ 2 x) SymmetricSpaceRelativeFundamental.fundamentalClass)
  conv_lhs => rw [← hc]
  conv_rhs => rw [← hc]
  rw [e1, relativeCochainCapHomology_representatives]
  have h2 := relativeCochainCapHomology_representatives boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant (Rep.res principalSix.subtype V₀) 2 3 x c
  refine Eq.trans ?_ (congrArg (homologyMap (epsLoc k V₀) 3).hom h2).symm
  refine (chainClass_natural (epsLoc k V₀) 3 _ _ ?_).symm
  exact relCap_eps k V₀ 2 3 x.val c.val

/-- **The cap isomorphism `S2⁻¹` is equivariant for the coefficient reindexing.**  For a
`GL₃(ℤ)`-representation `V₀` and `V = Res_{Γ(6)} V₀`, composing the conjugation action of `k` on the
relative `Hom`-cohomology (`hcAct`) with the pullback to the twisted pair (`relHomPull`) and then
capping with the relative fundamental class of the twisted covering data is capping with the
fundamental class followed by the coefficient reindexing `epsLoc` (identity on simplices, `ρ_{V₀}(k)`
on coefficients).

This is the actual relative-projection statement, not only the `relTheta` factorization: the evaluation
`hcAct_relHomPull_apply_pi` of `hcAct relAct B k ≫ relHomPull k V` on the image `π y` of an ambient chain
`y` under the relative projection uses the equivariance `upstairsRelativeProjection_gmor` of `π` for the
actual descended action `relAct`, the square `relChainMap_π` (`π_tw ≫ relChainMap = chainPhiW ≫ π`) and
`chainPhiW = ρ(k) ∘ hW`; the `k⁻¹` of `relAct` (`φ ∘ relAct(k⁻¹)`) cancels against `ρ(k)` there, leaving
`ρ_{V₀}(k) ∘ φ ∘ π ∘ hW`. -/
theorem capEps :
    homologyMap (hcAct relAct (GAct.ofRep principalSix V₀) k ≫
        relHomPull k (Rep.res principalSix.subtype V₀)) 2 ≫
      relativeHomCapTw k (Rep.res principalSix.subtype V₀) =
    (OrdinaryTopBoundaryComparison.relativeHomCapIso (Rep.res principalSix.subtype V₀)).hom ≫
      homologyMap (epsLoc k V₀) 3 := by
  have h1 := relHomGeom_eps k V₀
  have h2 := relativeFundamentalCap_eps k V₀
  have h3 : homologyMap (hcAct relAct (GAct.ofRep principalSix V₀) k ≫
        relHomPull k (Rep.res principalSix.subtype V₀)) 2 ≫
      homologyMap (relativeHomGeometricIsoTw k (Rep.res principalSix.subtype V₀)).hom 2 =
      homologyMap (relativeHomGeometricIso (Rep.res principalSix.subtype V₀)).hom 2 ≫
        homologyMap (epsRel k V₀) 2 := by
    rw [← homologyMap_comp, ← homologyMap_comp, h1]
  unfold relativeHomCapTw
  have e0 := OrdinaryTopBoundaryComparison.relativeHomCapIso_hom (Rep.res principalSix.subtype V₀)
  rw [← Category.assoc, h3, Category.assoc, h2]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun m => m ≫ homologyMap (epsLoc k V₀) 3) e0.symm)

end TernaryPeriodPolynomials.Argument.DualityEquivariance
