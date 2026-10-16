module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.BoundaryAction

@[expose] public section


/-!
# Coefficient reindexing between the boundary cover and its conjugation-twisted copy

Formalized by Claude Sonnet 5.5.

The boundary analogue of `LocalReindex`/`LocalReindexFiber` for the twisted boundary covering data
(`BoundaryTw`, `pbTw`, `PhiB`): the identity on simplices together with `ρ_{V₀}(k)` on the coefficients is a chain map
`epsChain` of coinvariant chains, which followed by the comparison `coinvariantSpaceMap (PhiB k)` is the diagonal action of `k`
(`diag_eq_phi_eps`); on geometric local chains `epsLoc ≫ LspaceB = bAct` (`epsLoc_LspaceB_eq`).  `epsReindex` is the fibrewise
reindexing (`FiberReindex`) of the two coverings of the boundary base, so that the cap product is natural for it.
First half of the cap equivariance `PDboundary ∘ hcoh_k = bAct_k ∘ PDboundary`.
-/

open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG.BR

open CategoryTheory AlgebraicTopology TernaryPoly TernaryPoly.FreeActionLinearization TernaryPoly.SingularLocalHomology TernaryPoly.EquivariantSingularResolution
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPeriodPolynomials.Argument.DualityEquivariance
  TernaryPeriodPolynomials.Argument.GroupHomology

variable (k : IntegralGL)

/-- The identification of the singular chains of the gluing with those of the twisted gluing:
the chain map of the homeomorphism `x ↦ ⟨x⟩`. -/
def jInvMap : TopCat.of BoundaryCover ⟶ TopCat.of (BoundaryTw k) :=
  TopCat.ofHom ⟨(BoundaryTw.homeo k).symm, (BoundaryTw.homeo k).symm.continuous⟩

def jInvChains (n : ℕ) : (underlyingChains (TopCat.of BoundaryCover)).X n ⟶
    (underlyingChains (TopCat.of (BoundaryTw k))).X n :=
  (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map (jInvMap k)).f n

theorem jInv_square (γ : principalSix) :
    scalarMap principalSix (TopCat.of BoundaryCover) (cjk k γ) ≫ jInvMap k =
      jInvMap k ≫ scalarMap principalSix (TopCat.of (BoundaryTw k)) γ := rfl

theorem jInvChains_action (γ : principalSix) (n : ℕ)
    (c : (underlyingChains (TopCat.of BoundaryCover)).X n) :
    (jInvChains k n).hom ((chainAction principalSix (TopCat.of BoundaryCover) n (cjk k γ)) c) =
      (chainAction principalSix (TopCat.of (BoundaryTw k)) n γ) ((jInvChains k n).hom c) := by
  have h := congrArg (fun m => ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map m).f n).hom c) (jInv_square k γ)
  simp only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h
  exact h

variable (V₀ : Rep.{0} ℚ IntegralGL)

/-- The reindexing map on tensors: `ρ_{V₀}(k)` on the coefficient and the identification of chains. -/
def epsTensor (n : ℕ) :
    TensorProduct ℚ (Rep.res principalSix.subtype V₀)
        ((chainRep principalSix (TopCat.of BoundaryCover) n)) →ₗ[ℚ]
      Representation.Coinvariants
        ((Rep.res principalSix.subtype V₀).ρ.tprod
          (chainRep principalSix (TopCat.of (BoundaryTw k)) n).ρ) :=
  (Representation.Coinvariants.mk _).comp
    (TensorProduct.map (V₀.ρ k) (jInvChains k n).hom)

theorem cjk_conjElt (γ : principalSix) : cjk k (conjElt principalSix k γ) = γ := by
  apply Subtype.ext
  rw [cjk_val, conjElt_val]
  group

theorem epsTensor_invariant (n : ℕ) (γ : principalSix) :
    (epsTensor k V₀ n).comp
      ((Rep.res principalSix.subtype V₀).ρ.tprod
        (chainRep principalSix (TopCat.of BoundaryCover) n).ρ γ) = epsTensor k V₀ n := by
  apply TensorProduct.ext'
  intro v c
  set γ' := conjElt principalSix k γ with hγ'
  have h1 : V₀.ρ k (V₀.ρ γ.1 v) = V₀.ρ γ'.1 (V₀.ρ k v) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    rw [hγ', conjElt_val]
    group
  have h2 : (jInvChains k n).hom ((chainRep principalSix (TopCat.of BoundaryCover) n).ρ γ c) =
      (chainRep principalSix (TopCat.of (BoundaryTw k)) n).ρ γ' ((jInvChains k n).hom c) := by
    have h := jInvChains_action k γ' n c
    rw [hγ', cjk_conjElt] at h
    exact h
  change Representation.Coinvariants.mk _
      (TensorProduct.map (V₀.ρ k) (jInvChains k n).hom (V₀.ρ γ.1 v ⊗ₜ[ℚ]
        (chainRep principalSix (TopCat.of BoundaryCover) n).ρ γ c)) =
    Representation.Coinvariants.mk _ (TensorProduct.map (V₀.ρ k) (jInvChains k n).hom (v ⊗ₜ[ℚ] c))
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, h1, h2]
  exact Representation.Coinvariants.mk_self_apply
    ((Rep.res principalSix.subtype V₀).ρ.tprod
      (chainRep principalSix (TopCat.of (BoundaryTw k)) n).ρ) γ'
    (V₀.ρ k v ⊗ₜ[ℚ] (jInvChains k n).hom c)

/-- The reindexing map on `(V ⊗ C_n)_Γ`. -/
def epsHomAt (n : ℕ) :
    ((Rep.coinvariantsTensor ℚ principalSix).obj (Rep.res principalSix.subtype V₀)).obj
        (chainRep principalSix (TopCat.of BoundaryCover) n) ⟶
      ((Rep.coinvariantsTensor ℚ principalSix).obj (Rep.res principalSix.subtype V₀)).obj
        (chainRep principalSix (TopCat.of (BoundaryTw k)) n) :=
  ModuleCat.ofHom (Representation.Coinvariants.lift _ (epsTensor k V₀ n)
    (fun γ => epsTensor_invariant k V₀ n γ))

theorem epsHomAt_mk (n : ℕ) (v : Rep.res principalSix.subtype V₀)
    (c : chainRep principalSix (TopCat.of BoundaryCover) n) :
    (epsHomAt k V₀ n).hom (Rep.coinvariantsTensorMk _ _ v c) =
      Rep.coinvariantsTensorMk (Rep.res principalSix.subtype V₀)
        (chainRep principalSix (TopCat.of (BoundaryTw k)) n) (V₀.ρ k v) ((jInvChains k n).hom c) := rfl

theorem jInvChains_comm (i j : ℕ) (c : (underlyingChains (TopCat.of BoundaryCover)).X i) :
    (jInvChains k j).hom ((underlyingChains (TopCat.of BoundaryCover)).d i j c) =
      (underlyingChains (TopCat.of (BoundaryTw k))).d i j ((jInvChains k i).hom c) :=
  (congrArg (fun m => m.hom c) (((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map (jInvMap k)).comm i j).symm))

theorem coinvariantChains_d_mk {G : Type} [Group G] (E : TopCat.{0}) [MulAction G E]
    [ContinuousConstSMul G E] (V : Rep.{0} ℚ G) (i j : ℕ) (v : V)
    (c : (equivariantChains G E).X i) :
    ((coinvariantChains G E V).d i j).hom (Rep.coinvariantsTensorMk V _ v c) =
      Rep.coinvariantsTensorMk V _ v (((equivariantChains G E).d i j).hom c) := rfl

/-- The reindexing chain map `(V ⊗ Sing(Glued))_Γ → (V ⊗ Sing(GluedTw k))_Γ`. -/
def epsChain : coinvariantChains principalSix (TopCat.of BoundaryCover) (Rep.res principalSix.subtype V₀) ⟶
    coinvariantChains principalSix (TopCat.of (BoundaryTw k)) (Rep.res principalSix.subtype V₀) where
  f n := epsHomAt k V₀ n
  comm' i j _ := by
    apply Rep.coinvariantsTensor_hom_ext
    ext v c
    change ((coinvariantChains principalSix (TopCat.of (BoundaryTw k))
        (Rep.res principalSix.subtype V₀)).d i j).hom
        ((epsHomAt k V₀ i).hom (Rep.coinvariantsTensorMk _ _ v c)) =
      (epsHomAt k V₀ j).hom (((coinvariantChains principalSix (TopCat.of BoundaryCover)
        (Rep.res principalSix.subtype V₀)).d i j).hom (Rep.coinvariantsTensorMk _ _ v c))
    let V := Rep.res principalSix.subtype V₀
    let Cs := chainRep principalSix (TopCat.of BoundaryCover)
    let Ct := chainRep principalSix (TopCat.of (BoundaryTw k))
    have h1 : ((coinvariantChains principalSix (TopCat.of (BoundaryTw k)) V).d i j).hom
        ((epsHomAt k V₀ i).hom (Rep.coinvariantsTensorMk V (Cs i) v c)) =
        ((coinvariantChains principalSix (TopCat.of (BoundaryTw k)) V).d i j).hom
          (Rep.coinvariantsTensorMk V (Ct i) (V₀.ρ k v) ((jInvChains k i).hom c)) :=
      congrArg _ (epsHomAt_mk k V₀ i v c)
    have h2 := coinvariantChains_d_mk (TopCat.of (BoundaryTw k)) V i j (V₀.ρ k v)
      ((jInvChains k i).hom c)
    have h3 : Rep.coinvariantsTensorMk V (Ct j) (V₀.ρ k v)
        (((equivariantChains principalSix (TopCat.of (BoundaryTw k))).d i j).hom
          ((jInvChains k i).hom c)) =
        Rep.coinvariantsTensorMk V (Ct j) (V₀.ρ k v) ((jInvChains k j).hom
          (((equivariantChains principalSix (TopCat.of BoundaryCover)).d i j).hom c)) :=
      congrArg _ (jInvChains_comm k i j c).symm
    have h4 := epsHomAt_mk k V₀ j v (((equivariantChains principalSix (TopCat.of BoundaryCover)).d i j).hom c)
    have h5 := coinvariantChains_d_mk (TopCat.of BoundaryCover) V i j v c
    refine h1.trans (h2.trans (h3.trans (h4.symm.trans ?_)))
    exact congrArg (epsHomAt k V₀ j).hom h5.symm

theorem phi_jInv_chains (n : ℕ) (c : (underlyingChains (TopCat.of BoundaryCover)).X n) :
    ((SingularCoverNaturality.chainMap (PhiB k) (PhiB_equivariant k)).f n).hom
        ((jInvChains k n).hom c) =
      (chainAction IntegralGL (TopCat.of BoundaryCover) n k) c := by
  have h := congrArg (fun m => ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map m).f n).hom c)
    (show jInvMap k ≫ PhiB k = scalarMap IntegralGL (TopCat.of BoundaryCover) k from rfl)
  simp only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h
  exact h

theorem diag_eq_phi_eps :
    epsChain k V₀ ≫ coinvariantSpaceMap (PhiB k) (PhiB_equivariant k)
        (Rep.res principalSix.subtype V₀) =
      GYb V₀ k := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.coinvariantsTensor_hom_ext
  ext v c
  let V := Rep.res principalSix.subtype V₀
  have hL : ((epsChain k V₀ ≫ coinvariantSpaceMap (PhiB k) (PhiB_equivariant k) V).f n).hom
      (Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of BoundaryCover) n) v c) =
      Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of BoundaryCover) n) (V₀.ρ k v)
        (((SingularCoverNaturality.chainMap (PhiB k) (PhiB_equivariant k)).f n).hom
          ((jInvChains k n).hom c)) := rfl
  have hR : ((GYb V₀ k).f n).hom
      (Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of BoundaryCover) n) v c) =
      Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of BoundaryCover) n) (V₀.ρ k v)
        ((chainAction IntegralGL (TopCat.of BoundaryCover) n k) c) := rfl
  exact hL.trans ((congrArg (Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of BoundaryCover) n)
    (V₀.ρ k v)) (phi_jInv_chains k n c)).trans hR.symm)



/-- The fibre of the twisted covering over `b` is the fibre of the gluing over `b`. -/
def fibUntw {b : BoundaryBase} (e : Fiber (pbTw k) b) : Fiber boundaryProjection b :=
  ⟨⟨e.val.1.val, e.val.2⟩, e.property⟩

/-- The coefficient reindexing on fibre coefficients: post-composition with `ρ_{V₀}(k)`. -/
def epsFib (b : BoundaryBase)
    (c : FiberCoefficient boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) b) :
    FiberCoefficient (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀) b :=
  ⟨fun e => V₀.ρ k (c.val (fibUntw k e)), fun g e => by
    have h1 : fibUntw k (fiberSmul (pbTw k) (twisted_boundary_covering k) g e) =
        fiberSmul boundaryProjection boundaryQuotientCovering (cjk k g) (fibUntw k e) := rfl
    have h2 := c.property (cjk k g) (fibUntw k e)
    change V₀.ρ k (c.val (fibUntw k (fiberSmul (pbTw k) (twisted_boundary_covering k) g e))) =
      V₀.ρ g.1 (V₀.ρ k (c.val (fibUntw k e)))
    rw [h1, h2]
    change V₀.ρ k (V₀.ρ (cjk k g).1 (c.val (fibUntw k e))) = _
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, cjk_val]
    congr 2
    group⟩

/-- The coefficient reindexing on local chains, transported from coinvariant chains. -/
def epsLoc : localChains boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) ⟶
    localChains (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀) :=
  (chainIso boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀)).inv ≫
    epsChain k V₀ ≫
    (chainIso (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀)).hom

theorem jInv_chainElement (n : ℕ) (τ : SingularSimplex (TopCat.of BoundaryCover) n) :
    (jInvChains k n).hom (chainElement principalSix (TopCat.of BoundaryCover) n τ) =
      chainElement principalSix (TopCat.of (BoundaryTw k)) n (projection (jInvMap k) n τ) := by
  have h := congrArg (fun m => m.hom (1 : ℚ)) (SingularCoverNaturality.generator_map (jInvMap k) n τ)
  exact h

/-- The lift of a simplex of the gluing to a simplex of the twisted gluing. -/
def jInvLift {n : ℕ} {σ : SingularSimplex (TopCat.of BoundaryBase) n} (τ : Lifts boundaryProjection σ) :
    Lifts (pbTw k) σ :=
  ⟨projection (jInvMap k) n τ.val, τ.property⟩

theorem epsChain_generator (n : ℕ) (τ : SingularSimplex (TopCat.of BoundaryCover) n)
    (v : Rep.res principalSix.subtype V₀) :
    ((epsChain k V₀).f n).hom (generator principalSix (TopCat.of BoundaryCover)
        (Rep.res principalSix.subtype V₀) n τ v) =
      generator principalSix (TopCat.of (BoundaryTw k)) (Rep.res principalSix.subtype V₀) n
        (projection (jInvMap k) n τ) (V₀.ρ k v) := by
  change ((epsHomAt k V₀ n).hom (Rep.coinvariantsTensorMk _ _ v
    (chainElement principalSix (TopCat.of BoundaryCover) n τ))) = _
  rw [epsHomAt_mk, jInv_chainElement]
  rfl

theorem epsLoc_single (n : ℕ) (σ : SingularSimplex (TopCat.of BoundaryBase) n)
    (c : FiberCoefficient boundaryProjection boundaryQuotientCovering
      (Rep.res principalSix.subtype V₀) (atVertex σ)) :
    ((epsLoc k V₀).f n).hom
        (DFinsupp.single (β := fun σ' : SingularSimplex (TopCat.of BoundaryBase) n =>
          FiberCoefficient boundaryProjection boundaryQuotientCovering
            (Rep.res principalSix.subtype V₀) (atVertex σ')) σ c) =
      DFinsupp.single (β := fun σ' : SingularSimplex (TopCat.of BoundaryBase) n =>
          FiberCoefficient (pbTw k) (twisted_boundary_covering k)
            (Rep.res principalSix.subtype V₀) (atVertex σ')) σ (epsFib k V₀ (atVertex σ) c) := by
  let V := Rep.res principalSix.subtype V₀
  apply (degreeEquiv (pbTw k) (twisted_boundary_covering k) V n).symm.injective
  let τ := chosenLift boundaryProjection boundaryQuotientCovering n σ
  have e : ∀ x, ((epsLoc k V₀).f n).hom x =
      (degreeEquiv (pbTw k) (twisted_boundary_covering k) V n)
        (((epsChain k V₀).f n).hom (((chainIso boundaryProjection boundaryQuotientCovering V).inv.f n).hom x)) :=
    fun x => rfl
  have hL : (degreeEquiv (pbTw k) (twisted_boundary_covering k) V n).symm
      (((epsLoc k V₀).f n).hom (DFinsupp.single (β := fun σ' : SingularSimplex
        (TopCat.of BoundaryBase) n => FiberCoefficient boundaryProjection boundaryQuotientCovering
          V (atVertex σ')) σ c)) =
      ((epsChain k V₀).f n).hom (((chainIso boundaryProjection boundaryQuotientCovering V).inv.f n).hom
        (DFinsupp.single (β := fun σ' : SingularSimplex (TopCat.of BoundaryBase) n =>
          FiberCoefficient boundaryProjection boundaryQuotientCovering V (atVertex σ')) σ c)) := by
    exact (congrArg (degreeEquiv (pbTw k) (twisted_boundary_covering k) V n).symm (e _)).trans
      (LinearEquiv.symm_apply_apply _ _)
  have h1 := chainIso_inv_single boundaryProjection boundaryQuotientCovering V n τ c
  have h2 := degreeEquiv_symm_single_lift (pbTw k) (twisted_boundary_covering k) V n (jInvLift k τ)
    (epsFib k V₀ (atVertex σ) c)
  rw [hL]
  erw [h1]
  rw [epsChain_generator]
  exact h2.symm




/-- Monodromy of the twisted boundary covering corresponds to that of the boundary covering under `fibUntw`. -/
theorem fibUntw_fiberTransport {x y : BoundaryBase}
    (γ : Path.Homotopic.Quotient x y) (e : Fiber (pbTw k) x) :
    fibUntw k (fiberTransport (pbTw k) (twisted_boundary_covering k) γ e) =
      fiberTransport boundaryProjection boundaryQuotientCovering γ (fibUntw k e) :=
  Subtype.ext (monodromy_comp_homeomorph _ boundaryQuotientCovering.isCoveringMap (BoundaryTw.homeo k) _
    (fun _ => rfl) (twisted_boundary_covering k).isCoveringMap γ e)

/-- `epsFib` is linear. -/
def epsFibLin (b : BoundaryBase) :
    FiberCoefficient boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) b →ₗ[ℚ]
      FiberCoefficient (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀) b where
  toFun := epsFib k V₀ b
  map_add' _ _ := Subtype.ext (funext fun _ => map_add (V₀.ρ k) _ _)
  map_smul' r _ := Subtype.ext (funext fun _ => map_smul (V₀.ρ k) r _)

/-- `epsFib` as a reindexing of the fibre coefficients of the two coverings of the boundary. -/
def epsReindex : FiberReindex boundaryProjection (pbTw k) boundaryQuotientCovering
    (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀) where
  ε := epsFibLin k V₀
  transport {x y} γ c := by
    apply Subtype.ext
    funext e
    change V₀.ρ k ((coefficientTransport boundaryProjection boundaryQuotientCovering γ c).val (fibUntw k e)) =
      (epsFib k V₀ x c).val (fiberTransport (pbTw k) (twisted_boundary_covering k) γ.symm e)
    change V₀.ρ k (c.val (fiberTransport boundaryProjection boundaryQuotientCovering γ.symm (fibUntw k e))) =
      V₀.ρ k (c.val (fibUntw k (fiberTransport (pbTw k) (twisted_boundary_covering k) γ.symm e)))
    rw [fibUntw_fiberTransport]

theorem epsLoc_f_eq (b : ℕ)
    (c : VertexChain boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) b) :
    ((epsLoc k V₀).f b).hom c = (epsReindex k V₀).chain b c :=
  LinearMap.congr_fun (FiberReindex.chain_unique (epsReindex k V₀) b ((epsLoc k V₀).f b).hom
    (fun σ c => epsLoc_single k V₀ b σ c)) c

/-- The coefficient reindexing as a cochain map of the geometric local cochains of the boundary. -/
def epsCoch : localCochains boundaryProjection boundaryQuotientCovering (Rep.res principalSix.subtype V₀) ⟶
    localCochains (pbTw k) (twisted_boundary_covering k) (Rep.res principalSix.subtype V₀) :=
  (epsReindex k V₀).cochainMap

/-- The comparison map of local chains from the twisted to the untwisted boundary cover. -/
abbrev LspaceB (V : Rep.{0} ℚ principalSix) :
    localChains (pbTw k) (twisted_boundary_covering k) V ⟶
      localChains boundaryProjection boundaryQuotientCovering V :=
  localSpaceMap (PhiB k) (PhiB_equivariant k) V (pbTw k) boundaryProjection (twisted_boundary_covering k)
    boundaryQuotientCovering

theorem epsLoc_LspaceB_eq :
    epsLoc k V₀ ≫ LspaceB k (Rep.res principalSix.subtype V₀) = bAct V₀ k := by
  have hd : epsChain k V₀ ≫ coinvariantSpaceMap (PhiB k) (PhiB_equivariant k)
      (Rep.res principalSix.subtype V₀) = GYb V₀ k := diag_eq_phi_eps k V₀
  unfold epsLoc LspaceB localSpaceMap bAct
  rw [← hd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG.BR
