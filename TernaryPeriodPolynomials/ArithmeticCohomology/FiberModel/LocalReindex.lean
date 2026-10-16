module

public import TernaryPeriodPolynomials.Topology.DualityEquivariance.TwistedCovering
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.EquivS1
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalAction

@[expose] public section


/-!
# Coefficient reindexing between the gluing and its conjugation-twisted copy

For `k ∈ GL₃(ℤ)` and a `GL₃(ℤ)`-representation `V₀` the identity on singular chains together with
`ρ_{V₀}(k)` on the coefficients induces a chain map
`epsChain : (V ⊗ Sing(Glued))_Γ → (V ⊗ Sing(GluedTw k))_Γ` (`V = Res_Γ V₀`, `Γ = Γ(6)`).  Composed with
the comparison map of the twisted pair (`coinvariantSpaceMap (PhiW k)`) it is the diagonal action
of `k` on the coinvariant singular chains (`diag_eq_phi_eps`), which by `groupCoinvariantHomologyIso_conj`
is the conjugation action `c_k` of Mathlib's group homology.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open CategoryTheory AlgebraicTopology TernaryPoly TernaryPoly.FreeActionLinearization TernaryPoly.SingularLocalHomology TernaryPoly.EquivariantSingularResolution
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPeriodPolynomials.Argument.DualityEquivariance
  TernaryPeriodPolynomials.Argument.GroupHomology

variable (k : IntegralGL)

/-- The identification of the singular chains of the gluing with those of the twisted gluing:
the chain map of the homeomorphism `x ↦ ⟨x⟩`. -/
def jInvMap : TopCat.of Glued ⟶ TopCat.of (GluedTw k) :=
  TopCat.ofHom ⟨GluedTw.mk, (GluedTw.homeo k).symm.continuous⟩

def jInvChains (n : ℕ) : (underlyingChains (TopCat.of Glued)).X n ⟶
    (underlyingChains (TopCat.of (GluedTw k))).X n :=
  (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map (jInvMap k)).f n

theorem jInv_square (γ : principalSix) :
    scalarMap principalSix (TopCat.of Glued) (cjk k γ) ≫ jInvMap k =
      jInvMap k ≫ scalarMap principalSix (TopCat.of (GluedTw k)) γ := rfl

theorem jInvChains_action (γ : principalSix) (n : ℕ)
    (c : (underlyingChains (TopCat.of Glued)).X n) :
    (jInvChains k n).hom ((chainAction principalSix (TopCat.of Glued) n (cjk k γ)) c) =
      (chainAction principalSix (TopCat.of (GluedTw k)) n γ) ((jInvChains k n).hom c) := by
  have h := congrArg (fun m => ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map m).f n).hom c) (jInv_square k γ)
  simp only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h
  exact h

variable (V₀ : Rep.{0} ℚ IntegralGL)

/-- The reindexing map on tensors: `ρ_{V₀}(k)` on the coefficient and the identification of chains. -/
def epsTensor (n : ℕ) :
    TensorProduct ℚ (Rep.res principalSix.subtype V₀)
        ((chainRep principalSix (TopCat.of Glued) n)) →ₗ[ℚ]
      Representation.Coinvariants
        ((Rep.res principalSix.subtype V₀).ρ.tprod
          (chainRep principalSix (TopCat.of (GluedTw k)) n).ρ) :=
  (Representation.Coinvariants.mk _).comp
    (TensorProduct.map (V₀.ρ k) (jInvChains k n).hom)

theorem cjk_conjElt (γ : principalSix) : cjk k (conjElt principalSix k γ) = γ := by
  apply Subtype.ext
  rw [cjk_val, conjElt_val]
  group

theorem epsTensor_invariant (n : ℕ) (γ : principalSix) :
    (epsTensor k V₀ n).comp
      ((Rep.res principalSix.subtype V₀).ρ.tprod
        (chainRep principalSix (TopCat.of Glued) n).ρ γ) = epsTensor k V₀ n := by
  apply TensorProduct.ext'
  intro v c
  set γ' := conjElt principalSix k γ with hγ'
  have h1 : V₀.ρ k (V₀.ρ γ.1 v) = V₀.ρ γ'.1 (V₀.ρ k v) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    rw [hγ', conjElt_val]
    group
  have h2 : (jInvChains k n).hom ((chainRep principalSix (TopCat.of Glued) n).ρ γ c) =
      (chainRep principalSix (TopCat.of (GluedTw k)) n).ρ γ' ((jInvChains k n).hom c) := by
    have h := jInvChains_action k γ' n c
    rw [hγ', cjk_conjElt] at h
    exact h
  change Representation.Coinvariants.mk _
      (TensorProduct.map (V₀.ρ k) (jInvChains k n).hom (V₀.ρ γ.1 v ⊗ₜ[ℚ]
        (chainRep principalSix (TopCat.of Glued) n).ρ γ c)) =
    Representation.Coinvariants.mk _ (TensorProduct.map (V₀.ρ k) (jInvChains k n).hom (v ⊗ₜ[ℚ] c))
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, h1, h2]
  exact Representation.Coinvariants.mk_self_apply
    ((Rep.res principalSix.subtype V₀).ρ.tprod
      (chainRep principalSix (TopCat.of (GluedTw k)) n).ρ) γ'
    (V₀.ρ k v ⊗ₜ[ℚ] (jInvChains k n).hom c)

/-- The reindexing map on `(V ⊗ C_n)_Γ`. -/
def epsHomAt (n : ℕ) :
    ((Rep.coinvariantsTensor ℚ principalSix).obj (Rep.res principalSix.subtype V₀)).obj
        (chainRep principalSix (TopCat.of Glued) n) ⟶
      ((Rep.coinvariantsTensor ℚ principalSix).obj (Rep.res principalSix.subtype V₀)).obj
        (chainRep principalSix (TopCat.of (GluedTw k)) n) :=
  ModuleCat.ofHom (Representation.Coinvariants.lift _ (epsTensor k V₀ n)
    (fun γ => epsTensor_invariant k V₀ n γ))

theorem epsHomAt_mk (n : ℕ) (v : Rep.res principalSix.subtype V₀)
    (c : chainRep principalSix (TopCat.of Glued) n) :
    (epsHomAt k V₀ n).hom (Rep.coinvariantsTensorMk _ _ v c) =
      Rep.coinvariantsTensorMk (Rep.res principalSix.subtype V₀)
        (chainRep principalSix (TopCat.of (GluedTw k)) n) (V₀.ρ k v) ((jInvChains k n).hom c) := rfl

theorem jInvChains_comm (i j : ℕ) (c : (underlyingChains (TopCat.of Glued)).X i) :
    (jInvChains k j).hom ((underlyingChains (TopCat.of Glued)).d i j c) =
      (underlyingChains (TopCat.of (GluedTw k))).d i j ((jInvChains k i).hom c) :=
  (congrArg (fun m => m.hom c) (((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map (jInvMap k)).comm i j).symm))

theorem coinvariantChains_d_mk {G : Type} [Group G] (E : TopCat.{0}) [MulAction G E]
    [ContinuousConstSMul G E] (V : Rep.{0} ℚ G) (i j : ℕ) (v : V)
    (c : (equivariantChains G E).X i) :
    ((coinvariantChains G E V).d i j).hom (Rep.coinvariantsTensorMk V _ v c) =
      Rep.coinvariantsTensorMk V _ v (((equivariantChains G E).d i j).hom c) := rfl

/-- The reindexing chain map `(V ⊗ Sing(Glued))_Γ → (V ⊗ Sing(GluedTw k))_Γ`. -/
def epsChain : coinvariantChains principalSix (TopCat.of Glued) (Rep.res principalSix.subtype V₀) ⟶
    coinvariantChains principalSix (TopCat.of (GluedTw k)) (Rep.res principalSix.subtype V₀) where
  f n := epsHomAt k V₀ n
  comm' i j _ := by
    apply Rep.coinvariantsTensor_hom_ext
    ext v c
    change ((coinvariantChains principalSix (TopCat.of (GluedTw k))
        (Rep.res principalSix.subtype V₀)).d i j).hom
        ((epsHomAt k V₀ i).hom (Rep.coinvariantsTensorMk _ _ v c)) =
      (epsHomAt k V₀ j).hom (((coinvariantChains principalSix (TopCat.of Glued)
        (Rep.res principalSix.subtype V₀)).d i j).hom (Rep.coinvariantsTensorMk _ _ v c))
    let V := Rep.res principalSix.subtype V₀
    let Cs := chainRep principalSix (TopCat.of Glued)
    let Ct := chainRep principalSix (TopCat.of (GluedTw k))
    have h1 : ((coinvariantChains principalSix (TopCat.of (GluedTw k)) V).d i j).hom
        ((epsHomAt k V₀ i).hom (Rep.coinvariantsTensorMk V (Cs i) v c)) =
        ((coinvariantChains principalSix (TopCat.of (GluedTw k)) V).d i j).hom
          (Rep.coinvariantsTensorMk V (Ct i) (V₀.ρ k v) ((jInvChains k i).hom c)) :=
      congrArg _ (epsHomAt_mk k V₀ i v c)
    have h2 := coinvariantChains_d_mk (TopCat.of (GluedTw k)) V i j (V₀.ρ k v)
      ((jInvChains k i).hom c)
    have h3 : Rep.coinvariantsTensorMk V (Ct j) (V₀.ρ k v)
        (((equivariantChains principalSix (TopCat.of (GluedTw k))).d i j).hom
          ((jInvChains k i).hom c)) =
        Rep.coinvariantsTensorMk V (Ct j) (V₀.ρ k v) ((jInvChains k j).hom
          (((equivariantChains principalSix (TopCat.of Glued)).d i j).hom c)) :=
      congrArg _ (jInvChains_comm k i j c).symm
    have h4 := epsHomAt_mk k V₀ j v (((equivariantChains principalSix (TopCat.of Glued)).d i j).hom c)
    have h5 := coinvariantChains_d_mk (TopCat.of Glued) V i j v c
    refine h1.trans (h2.trans (h3.trans (h4.symm.trans ?_)))
    exact congrArg (epsHomAt k V₀ j).hom h5.symm

theorem phi_jInv_chains (n : ℕ) (c : (underlyingChains (TopCat.of Glued)).X n) :
    ((SingularCoverNaturality.chainMap (PhiW k) (PhiW_equivariant k)).f n).hom
        ((jInvChains k n).hom c) =
      (chainAction IntegralGL (TopCat.of Glued) n k) c := by
  have h := congrArg (fun m => ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map m).f n).hom c)
    (show jInvMap k ≫ PhiW k = scalarMap IntegralGL (TopCat.of Glued) k from rfl)
  simp only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h
  exact h

theorem diag_eq_phi_eps :
    epsChain k V₀ ≫ coinvariantSpaceMap (PhiW k) (PhiW_equivariant k)
        (Rep.res principalSix.subtype V₀) =
      GY principalSix (Ygeo (TopCat.of Glued) V₀) k := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.coinvariantsTensor_hom_ext
  ext v c
  let V := Rep.res principalSix.subtype V₀
  have hL : ((epsChain k V₀ ≫ coinvariantSpaceMap (PhiW k) (PhiW_equivariant k) V).f n).hom
      (Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of Glued) n) v c) =
      Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of Glued) n) (V₀.ρ k v)
        (((SingularCoverNaturality.chainMap (PhiW k) (PhiW_equivariant k)).f n).hom
          ((jInvChains k n).hom c)) := rfl
  have hR : ((GY principalSix (Ygeo (TopCat.of Glued) V₀) k).f n).hom
      (Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of Glued) n) v c) =
      Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of Glued) n) (V₀.ρ k v)
        ((chainAction IntegralGL (TopCat.of Glued) n k) c) := rfl
  exact hL.trans ((congrArg (Rep.coinvariantsTensorMk V (chainRep principalSix (TopCat.of Glued) n)
    (V₀.ρ k v)) (phi_jInv_chains k n c)).trans hR.symm)

end TernaryPeriodPolynomials.Argument.FiberModel
