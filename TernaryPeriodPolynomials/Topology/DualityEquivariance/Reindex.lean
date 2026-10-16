module

public import TernaryPeriodPolynomials.Topology.DualityEquivariance.HomNaturality
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalTwist

@[expose] public section


/-!
# `K`-equivariance of the duality, piece (ii)(b): reindexing the twisted Hom complexes

The twisted covering data of `TwistedCovering` is isomorphic to the untwisted one: `PhiW` and `PhiB`
are `Γ(6)`-equivariant homeomorphisms (`PhiWinv`, `PhiBinv`), so `chainPhiW`, `chainPhiB` and the
induced map of relative chains `relChainMap` are isomorphisms of complexes of `Γ(6)`-representations.
`chainPhiW` is the action of `k` on simplices followed by the homeomorphism `GluedTw k ≅ Glued`
(`chainPhiW_f_apply`); equivalently `ambTheta` identifies the twisted ambient chains with the twist of
the chains of the gluing and is the identity on simplices (`ambTheta_f_apply`).

For a compatible `IntegralGL`-action `A` on the relative chains (a `GActC`) the relative twist
identification `relTheta` gives `relChainMap = relTheta ≫ actC A k`, and
`relHomPull_Xi`: `relHomPull k V ≫ (XiIso B k (relTheta k A)).hom = hcAct A B k⁻¹`: pulling back
relative Hom cochains along the twisted pair is, after the reindexing `XiIso` (`ψ ↦ ρ_W(k)⁻¹ ∘ ψ ∘ Θ⁻¹`),
the conjugation action of `k⁻¹` on `Hom_{Γ(6)}(upstairsRelativeChains, W)` of the shared layer
`GroupHomology/NormalAction`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.DualityEquivariance

open CategoryTheory CategoryTheory.Limits TernaryPoly TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularCoverNaturality
  TernaryPoly.EquivariantSingularResolution TernaryPoly.OrdinaryTopBoundaryComparison
  TernaryPoly.FreeActionLinearization
  TernaryPeriodPolynomials.Argument.GroupHomology

/-- The `IntegralGL`-action on the equivariant chains of the gluing, as a compatible action on the
`Γ(6)`-complex. -/
def ambientGActC : GActC (H := principalSix) (equivariantChains principalSix (TopCat.of Glued)) :=
  GActC.ofChain principalSix (equivariantChains IntegralGL (TopCat.of Glued))

theorem ambientGActC_ρ (n : ℕ) (g : IntegralGL) :
    ((ambientGActC.act n).ρ g) = ((scalarChainMap IntegralGL (TopCat.of Glued) g).f n).hom := rfl


variable (k : IntegralGL) (V : Rep.{0} ℚ principalSix)

/-- Inverse of `PhiW`: the action of `k⁻¹`. -/
def PhiWinv : TopCat.of Glued ⟶ TopCat.of (GluedTw k) :=
  TopCat.ofHom ⟨fun y => ⟨integralAction k⁻¹ y⟩,
    (GluedTw.homeo k).symm.continuous.comp (continuous_leftAction _)⟩

theorem PhiWinv_equivariant (g : principalSix) (y : Glued) :
    PhiWinv k (g • y) = g • PhiWinv k y := by
  change GluedTw.mk (k⁻¹ • ((g : IntegralGL) • y)) = GluedTw.mk ((cjk k g : principalSix) • (k⁻¹ • y))
  congr 1
  change k⁻¹ • ((g : IntegralGL) • y) = ((cjk k g : principalSix) : IntegralGL) • (k⁻¹ • y)
  rw [cjk_val, ← mul_smul, ← mul_smul]
  congr 1
  group

theorem PhiW_PhiWinv : PhiW k ≫ PhiWinv k = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change GluedTw.mk (k⁻¹ • (k • x.val)) = x
  rw [inv_smul_smul]

theorem PhiWinv_PhiW : PhiWinv k ≫ PhiW k = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  change k • (k⁻¹ • y) = y
  rw [smul_inv_smul]


theorem integralAction_mem_boundary (k : IntegralGL) {y : Glued} (hy : y ∈ upstairsBoundary) :
    integralAction k y ∈ upstairsBoundary := by
  rw [boundary_iff] at hy ⊢
  exact fbar_mem_boundary k hy

/-- Inverse of `PhiB`. -/
def PhiBinv : TopCat.of BoundaryCover ⟶ TopCat.of (BoundaryTw k) :=
  TopCat.ofHom ⟨fun y => ⟨⟨integralAction k⁻¹ y.val⟩, integralAction_mem_boundary k⁻¹ y.property⟩,
    (((GluedTw.homeo k).symm.continuous.comp ((continuous_leftAction _).comp
      continuous_subtype_val))).subtype_mk _⟩

theorem PhiBinv_equivariant (g : principalSix) (y : BoundaryCover) :
    PhiBinv k (g • y) = g • PhiBinv k y :=
  Subtype.ext (PhiWinv_equivariant k g y.val)

theorem PhiB_PhiBinv : PhiB k ≫ PhiBinv k = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change GluedTw.mk (k⁻¹ • (k • x.1.val)) = x.1
  rw [inv_smul_smul]

theorem PhiBinv_PhiB : PhiBinv k ≫ PhiB k = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  change k • (k⁻¹ • y.val) = y.val
  rw [smul_inv_smul]

instance chainPhiW_isIso : IsIso (chainPhiW k) :=
  ⟨⟨chainMap (PhiWinv k) (PhiWinv_equivariant k),
    (chainMap_comp (PhiW k) (PhiWinv k) (PhiW_equivariant k) (PhiWinv_equivariant k)).symm.trans
      ((chainMap_congr (PhiW_PhiWinv k) _ _).trans chainMap_id),
    (chainMap_comp (PhiWinv k) (PhiW k) (PhiWinv_equivariant k) (PhiW_equivariant k)).symm.trans
      ((chainMap_congr (PhiWinv_PhiW k) _ _).trans chainMap_id)⟩⟩

instance chainPhiB_isIso : IsIso (chainPhiB k) :=
  ⟨⟨chainMap (PhiBinv k) (PhiBinv_equivariant k),
    (chainMap_comp (PhiB k) (PhiBinv k) (PhiB_equivariant k) (PhiBinv_equivariant k)).symm.trans
      ((chainMap_congr (PhiB_PhiBinv k) _ _).trans chainMap_id),
    (chainMap_comp (PhiBinv k) (PhiB k) (PhiBinv_equivariant k) (PhiB_equivariant k)).symm.trans
      ((chainMap_congr (PhiBinv_PhiB k) _ _).trans chainMap_id)⟩⟩

/-- `relChainMap` is an isomorphism of relative chain complexes. -/
instance relChainMap_isIso : IsIso (relChainMap k) := by
  unfold relChainMap
  infer_instance


/-- The identification of the twisted relative complex with the twist of the relative complex, given
a compatible `G`-action on the relative complex: `relChainMap` followed by the inverse of the action
of `k`. -/
def relTheta (A : GActC (H := principalSix) upstairsRelativeChains) :
    upstairsRelativeChainsTw k ≅ twistC k upstairsRelativeChains :=
  asIso (relChainMap k) ≪≫ (asIso (actC A k)).symm

theorem relChainMap_eq (A : GActC (H := principalSix) upstairsRelativeChains) :
    relChainMap k = (relTheta k A).hom ≫ actC A k := by
  simp [relTheta]

/-- **(a)** Pullback of relative Hom cochains along the twisted pair, followed by the reindexing, is
the conjugation action of `k⁻¹`. -/
theorem relHomPull_Xi (A : GActC (H := principalSix) upstairsRelativeChains)
    (B : GAct principalSix V) :
    relHomPull k V ≫ (XiIso B k (relTheta k A)).hom = hcAct A B k⁻¹ :=
  homPullback_eq_hcAct A B k (relTheta k A) (relChainMap k) (relChainMap_eq k A)


/-- The underlying homeomorphism `GluedTw k ≅ Glued` as a morphism of spaces. -/
def hW : TopCat.of (GluedTw k) ⟶ TopCat.of Glued :=
  TopCat.ofHom ⟨GluedTw.val, (GluedTw.homeo k).continuous⟩

theorem PhiW_eq : PhiW k = hW k ≫ scalarMap IntegralGL (TopCat.of Glued) k := rfl

theorem chainPhiW_f_apply (n : ℕ) (x : (underlyingChains (TopCat.of (GluedTw k))).X n) :
    ((chainPhiW k).f n).hom x =
      (ambientGActC.act n).ρ k (((underlyingMap (hW k)).f n).hom x) := by
  have h : underlyingMap (PhiW k) =
      underlyingMap (hW k) ≫ scalarChainMap IntegralGL (TopCat.of Glued) k := by
    rw [PhiW_eq]
    exact Functor.map_comp _ _ _
  exact congrArg (fun m => (m.f n).hom x) h

/-- The geometric identification of the twisted ambient chains with the twist of the chains of the
gluing: it is induced by the homeomorphism `GluedTw k ≅ Glued`, i.e. it is the identity on simplices. -/
def ambTheta : ambientChainsTw k ≅ twistC k (equivariantChains principalSix (TopCat.of Glued)) :=
  asIso (chainPhiW k) ≪≫ (asIso (actC ambientGActC k)).symm

theorem ambTheta_f_apply (n : ℕ) (x : (underlyingChains (TopCat.of (GluedTw k))).X n) :
    ((ambTheta k).hom.f n).hom x = ((underlyingMap (hW k)).f n).hom x := by
  have h1 : ((asIso (actC ambientGActC k)).inv.f n).hom
      (((actC ambientGActC k).f n).hom (((underlyingMap (hW k)).f n).hom x)) =
      ((underlyingMap (hW k)).f n).hom x := by
    have := congrArg (fun m => (m.f n).hom (((underlyingMap (hW k)).f n).hom x))
      (IsIso.hom_inv_id (actC ambientGActC k))
    exact this
  change ((asIso (actC ambientGActC k)).inv.f n).hom (((chainPhiW k).f n).hom x) = _
  rw [chainPhiW_f_apply]
  exact h1

end TernaryPeriodPolynomials.Argument.DualityEquivariance
