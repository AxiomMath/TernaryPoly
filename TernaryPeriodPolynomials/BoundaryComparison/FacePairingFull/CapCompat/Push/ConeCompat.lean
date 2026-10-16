module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeCap

@[expose] public section


/-!
# Carried chain maps between labelled pushout cones, and their cap compatibility

For a labelled pushout cone `𝒞` (with cell basis and labels) and a pushout cone `𝒟` carrying label carriers, with
strict diagonal systems on the strata, `exists_pushCarried_chainMap` produces a carried chain map `u : K ⟶ K'`
compatible with the augmentations, and `pushCone_cap_compat` is the conclusion of `cap_compat` for every carried
`u` and every cocycle of the target.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

namespace PushCone

variable {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  {A' L' P' K' : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a' : A' ⟶ L'} {b' : A' ⟶ P'}
  {BA : CellBasis A} {BL : CellBasis L} {BP : CellBasis P}
  {ZF ZL ZP : Type} [MulAction Γ ZF] [MulAction Γ ZL] [MulAction Γ ZP] {φL : ZF → ZL} {φP : ZF → ZP}
  (𝒞 : PushCone A L P K a b) (𝒟 : PushCone A' L' P' K' a' b')
  (ld : PushLabels a b BA BL BP ZF ZL ZP φL φP) (T : PushTargets 𝒟 ZF ZL ZP φL φP)
  (SA : DiagSystem A) (SL : DiagSystem L) (SP : DiagSystem P)
  (SA' : DiagSystem A') (SL' : DiagSystem L') (SP' : DiagSystem P')

/-- There is a chain map between the cones carried by the label carriers, compatible with the augmentations. -/
theorem exists_pushCarried_chainMap (hS : Strict (a := a) (b := b) SA SL SP)
    (hS' : Strict (a := a') (b := b') SA' SL' SP') (G : PushTargets.Good 𝒟 SA' SL' SP' T)
    (hepsL : ∀ t : BL.S 0, SL.eps.hom (BL.cell 0 t) = (1 : ℚ))
    (hepsP : ∀ t : BP.S 0, SP.eps.hom (BP.cell 0 t) = (1 : ℚ)) :
    ∃ u : K ⟶ K', (∀ n, (pushCarrierData 𝒞 𝒟 ld T).Carried (u.f n)) ∧
      u.f 0 ≫ 𝒟.eps SL' SP' = 𝒞.eps SL SP := by
  refine (pushCarrierData 𝒞 𝒟 ld T).exists_carried_chainMap (aug := 𝒟.eps SL' SP')
    (pushCarrierData_acyclic 𝒞 𝒟 ld T hS' G) (𝒞.eps SL SP) (𝒞.eps_d hS) ?_
  intro s
  obtain ⟨y, hy, hy1⟩ := (pushK_subAcyc 𝒟 ld T G 0 s).surj
  refine Submodule.mem_map.mpr ⟨y, hy, ?_⟩
  change (𝒟.eps SL' SP').hom y = (𝒞.eps SL SP).hom (coneCell BA BL BP 𝒞 0 s)
  rw [hy1]
  rcases s with t | t
  · rw [show coneCell BA BL BP 𝒞 0 (Sum.inl t) = (𝒞.iL 0).hom (BL.cell 0 t) from rfl, 𝒞.eps_iL, hepsL]
  · rw [show coneCell BA BL BP 𝒞 0 (Sum.inr t) = (𝒞.iP 0).hom (BP.cell 0 t) from rfl, 𝒞.eps_iP, hepsP]

/-- **Cap compatibility of a carried chain map between labelled pushout cones.** -/
theorem pushCone_cap_compat (hS : Strict (a := a) (b := b) SA SL SP)
    (hS' : Strict (a := a') (b := b') SA' SL' SP') (G : PushTargets.Good 𝒟 SA' SL' SP' T)
    (hd : ld.Diag SA SL SP)
    (rA : ∀ f, DiagRespects SA' (T.FA f)) (rL : ∀ z, DiagRespects SL' (T.FL z))
    (rP : ∀ z, DiagRespects SP' (T.FP z))
    (u : K ⟶ K') (hu : ∀ n, (pushCarrierData 𝒞 𝒟 ld T).Carried (u.f n))
    (hueps : u.f 0 ≫ 𝒟.eps SL' SP' = 𝒞.eps SL SP) {W : Rep.{0} ℚ Γ} {n : ℕ} (c : K'.X n ⟶ W)
    (hc : K'.d (n+1) n ≫ c = 0) :
    ∃ h : ∀ q, K.X (n+q) ⟶ W ⊗ K'.X (q+1),
      ((𝒞.diagSystem SA SL SP hS).toCapSystem.cap (u.f n ≫ c) (chainMap_cocycle u c hc) 0 ≫ (W ◁ u.f 0) -
          u.f (n+0) ≫ (𝒟.diagSystem SA' SL' SP' hS').toCapSystem.cap c hc 0 =
        h 0 ≫ (W ◁ K'.d 1 0)) ∧
      ∀ q, (𝒞.diagSystem SA SL SP hS).toCapSystem.cap (u.f n ≫ c) (chainMap_cocycle u c hc) (q+1) ≫
            (W ◁ u.f (q+1)) -
          u.f (n+(q+1)) ≫ (𝒟.diagSystem SA' SL' SP' hS').toCapSystem.cap c hc (q+1) =
        h (q+1) ≫ (W ◁ K'.d (q+1+1) (q+1)) +
          ((-1 : ℤ)^n) • (K.d (n+q+1) (n+q) ≫ h q) :=
  cap_compat (B := coneCells BA BL BP 𝒞) (𝒞.diagSystem SA SL SP hS).toCapSystem
    (𝒟.diagSystem SA' SL' SP' hS').toCapSystem (pushCarrierData 𝒞 𝒟 ld T)
    (pushCarrierData_isSubcomplex 𝒞 𝒟 ld T G) (pushCarrierData_acyclic 𝒞 𝒟 ld T hS' G)
    (pushCellCarried 𝒞 𝒟 ld T SA SL SP hd hS).capCellCarried
    (pushCapPreserved 𝒞 𝒟 ld T hS' rA rL rP) u hu hueps c hc

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
