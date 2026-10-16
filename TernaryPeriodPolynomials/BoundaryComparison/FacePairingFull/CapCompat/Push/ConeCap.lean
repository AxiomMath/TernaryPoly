module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeRespects
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Thm

@[expose] public section


/-!
# Hypotheses of `cap_compat` for labelled pushout cones

* `DiagRespects.cap_mem`: if a diagonal system respects a subspace family, its caps preserve the tensor carriers
  (`CapCarrierPreserved`).
* `DiagCellCarried`: the diagonal of a cell is a combination of tensors of cells whose back factor has a smaller
  carrier; it implies `CapCellCarried`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

theorem DiagRespects.cap_mem {D : ChainComplex (Rep.{0} ℚ Γ) ℕ} {S : DiagSystem D}
    {Kf : ∀ m, Submodule ℚ (D.X m)} (hr : DiagRespects S Kf) {W : Rep.{0} ℚ Γ} {a : ℕ} (b : D.X a ⟶ W)
    (hb : D.d (a+1) a ≫ b = 0) (q : ℕ) {x : D.X (a+q)} (hx : x ∈ Kf (a+q)) :
    (S.toCapSystem.cap b hb q).hom x ∈ tensorK W (Kf q) := by
  change (b ▷ D.X q).hom ((S.Δ a q (a+q) rfl).hom x) ∈ _
  rw [tensorK_eq_span]
  refine PushCone.span_map_mem ((b ▷ D.X q).hom.toLinearMap) ?_ (hr a q (a+q) rfl x hx)
  rintro t ⟨u, v, hu, hv, rfl⟩
  have : (b ▷ D.X q).hom (u ⊗ₜ[ℚ] v) = b.hom u ⊗ₜ[ℚ] v := by
    rw [Rep.hom_whiskerRight]; rfl
  exact Submodule.subset_span ⟨b.hom u, v, hv, this⟩

/-- The diagonal of a cell is a combination of tensors of cells whose back factor has a smaller carrier. -/
def DiagCellCarried {C D : ChainComplex (Rep.{0} ℚ Γ) ℕ} {B : CellBasis C} (S : DiagSystem C)
    (𝒦 : CarrierData B D) : Prop :=
  ∀ (p q n : ℕ) (h : p + q = n) (s : B.S n), (S.Δ p q n h).hom (B.cell n s) ∈ Submodule.span ℚ
    {x | ∃ (t' : B.S p) (t : B.S q), (∀ m, 𝒦.K q t m ≤ 𝒦.K n s m) ∧
      x = (B.cell p t' ⊗ₜ[ℚ] B.cell q t : (C.X p ⊗ C.X q : Rep.{0} ℚ Γ))}

theorem DiagCellCarried.capCellCarried {C D : ChainComplex (Rep.{0} ℚ Γ) ℕ} {B : CellBasis C}
    {S : DiagSystem C} {𝒦 : CarrierData B D} (h : DiagCellCarried S 𝒦) :
    CapCellCarried (B := B) S.toCapSystem 𝒦 := by
  intro W a b hb q s
  change (b ▷ C.X q).hom ((S.Δ a q (a+q) rfl).hom (B.cell (a+q) s)) ∈ _
  refine PushCone.span_map_mem ((b ▷ C.X q).hom.toLinearMap) ?_ (h a q (a+q) rfl s)
  rintro t ⟨t', t'', ht, rfl⟩
  have : (b ▷ C.X q).hom (B.cell a t' ⊗ₜ[ℚ] B.cell q t'') = b.hom (B.cell a t') ⊗ₜ[ℚ] B.cell q t'' := by
    rw [Rep.hom_whiskerRight]; rfl
  exact Submodule.subset_span ⟨b.hom (B.cell a t'), t'', ht, this⟩

/-- The diagonals of the cells of the three strata keep the label of the back factor. -/
structure PushLabels.Diag {A L P : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
    {BA : CellBasis A} {BL : CellBasis L} {BP : CellBasis P} {ZF ZL ZP : Type}
    [MulAction Γ ZF] [MulAction Γ ZL] [MulAction Γ ZP] {φL : ZF → ZL} {φP : ZF → ZP}
    (ld : PushLabels a b BA BL BP ZF ZL ZP φL φP) (SA : DiagSystem A) (SL : DiagSystem L)
    (SP : DiagSystem P) : Prop where
  dgA : ∀ (p q n : ℕ) (h : p + q = n) (s : BA.S n), (SA.Δ p q n h).hom (BA.cell n s) ∈ Submodule.span ℚ
    {x | ∃ (t' : BA.S p) (t : BA.S q), ld.labA q t = ld.labA n s ∧
      x = (BA.cell p t' ⊗ₜ[ℚ] BA.cell q t : (A.X p ⊗ A.X q : Rep.{0} ℚ Γ))}
  dgL : ∀ (p q n : ℕ) (h : p + q = n) (s : BL.S n), (SL.Δ p q n h).hom (BL.cell n s) ∈ Submodule.span ℚ
    {x | ∃ (t' : BL.S p) (t : BL.S q), ld.labL q t = ld.labL n s ∧
      x = (BL.cell p t' ⊗ₜ[ℚ] BL.cell q t : (L.X p ⊗ L.X q : Rep.{0} ℚ Γ))}
  dgP : ∀ (p q n : ℕ) (h : p + q = n) (s : BP.S n), (SP.Δ p q n h).hom (BP.cell n s) ∈ Submodule.span ℚ
    {x | ∃ (t' : BP.S p) (t : BP.S q), ld.labP q t = ld.labP n s ∧
      x = (BP.cell p t' ⊗ₜ[ℚ] BP.cell q t : (P.X p ⊗ P.X q : Rep.{0} ℚ Γ))}

namespace PushCone

variable {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  {A' L' P' K' : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a' : A' ⟶ L'} {b' : A' ⟶ P'}
  {BA : CellBasis A} {BL : CellBasis L} {BP : CellBasis P}
  {ZF ZL ZP : Type} [MulAction Γ ZF] [MulAction Γ ZL] [MulAction Γ ZP] {φL : ZF → ZL} {φP : ZF → ZP}
  (𝒞 : PushCone A L P K a b) (𝒟 : PushCone A' L' P' K' a' b')
  (ld : PushLabels a b BA BL BP ZF ZL ZP φL φP) (T : PushTargets 𝒟 ZF ZL ZP φL φP)
  (SA : DiagSystem A) (SL : DiagSystem L) (SP : DiagSystem P)

theorem pushCell_Lterm (hd : ld.Diag SA SL SP) (p q n : ℕ) (h : p + q = n) (s : BL.S n) :
    (𝒞.Δ SA SL SP p q n h).hom (coneCell BA BL BP 𝒞 n (inLcell n s)) ∈ Submodule.span ℚ
      {x | ∃ (t' : coneS BA BL BP p) (t : coneS BA BL BP q),
        (∀ m, pushK 𝒟 ld T q t m ≤ pushK 𝒟 ld T n (inLcell n s) m) ∧
        x = (coneCell BA BL BP 𝒞 p t' ⊗ₜ[ℚ] coneCell BA BL BP 𝒞 q t :
          (K.X p ⊗ K.X q : Rep.{0} ℚ Γ))} := by
  rw [coneCell_inL]
  have := congrArg (fun φ => φ.hom (BL.cell n s)) (iL_Δ' (𝒞 := 𝒞) (SA := SA) (SL := SL) (SP := SP) p q n h)
  simp only [Rep.hom_comp] at this
  rw [show (𝒞.Δ SA SL SP p q n h).hom ((𝒞.iL n).hom (BL.cell n s)) =
    (𝒞.iL p ⊗ₘ 𝒞.iL q).hom ((SL.Δ p q n h).hom (BL.cell n s)) from this]
  refine span_map_mem ((𝒞.iL p ⊗ₘ 𝒞.iL q).hom.toLinearMap) ?_ (hd.dgL p q n h s)
  rintro x ⟨t', t, ht, rfl⟩
  refine Submodule.subset_span ⟨inLcell p t', inLcell q t, ?_, ?_⟩
  · intro m
    rw [pushK_inL, pushK_inL, ht]
  · rw [coneCell_inL, coneCell_inL]
    exact (tensorHom_hom_tmul _ _ _ _).symm

theorem pushCell_Pterm (hd : ld.Diag SA SL SP) (p q n : ℕ) (h : p + q = n) (s : BP.S n) :
    (𝒞.Δ SA SL SP p q n h).hom (coneCell BA BL BP 𝒞 n (inPcell n s)) ∈ Submodule.span ℚ
      {x | ∃ (t' : coneS BA BL BP p) (t : coneS BA BL BP q),
        (∀ m, pushK 𝒟 ld T q t m ≤ pushK 𝒟 ld T n (inPcell n s) m) ∧
        x = (coneCell BA BL BP 𝒞 p t' ⊗ₜ[ℚ] coneCell BA BL BP 𝒞 q t :
          (K.X p ⊗ K.X q : Rep.{0} ℚ Γ))} := by
  rw [coneCell_inP]
  have := congrArg (fun φ => φ.hom (BP.cell n s)) (iP_Δ' (𝒞 := 𝒞) (SA := SA) (SL := SL) (SP := SP) p q n h)
  simp only [Rep.hom_comp] at this
  rw [show (𝒞.Δ SA SL SP p q n h).hom ((𝒞.iP n).hom (BP.cell n s)) =
    (𝒞.iP p ⊗ₘ 𝒞.iP q).hom ((SP.Δ p q n h).hom (BP.cell n s)) from this]
  refine span_map_mem ((𝒞.iP p ⊗ₘ 𝒞.iP q).hom.toLinearMap) ?_ (hd.dgP p q n h s)
  rintro x ⟨t', t, ht, rfl⟩
  refine Submodule.subset_span ⟨inPcell p t', inPcell q t, ?_, ?_⟩
  · intro m
    rw [pushK_inP, pushK_inP, ht]
  · rw [coneCell_inP, coneCell_inP]
    exact (tensorHom_hom_tmul _ _ _ _).symm

theorem pushCell_corner (hd : ld.Diag SA SL SP) (p q n' : ℕ) (h : p + q = n' + 1) (s0 : BA.S n') :
    (𝒞.Δ SA SL SP p q (n'+1) h).hom (coneCell BA BL BP 𝒞 (n'+1) (Sum.inl s0)) ∈ Submodule.span ℚ
      {x | ∃ (t' : coneS BA BL BP p) (t : coneS BA BL BP q),
        (∀ m, pushK 𝒟 ld T q t m ≤ pushK 𝒟 ld T (n'+1) (Sum.inl s0) m) ∧
        x = (coneCell BA BL BP 𝒞 p t' ⊗ₜ[ℚ] coneCell BA BL BP 𝒞 q t :
          (K.X p ⊗ K.X q : Rep.{0} ℚ Γ))} := by
  have := congrArg (fun φ => φ.hom (BA.cell n' s0)) (𝒞.iA_Δ SA SL SP p q n' h)
  change (𝒞.Δ SA SL SP p q (n'+1) h).hom ((𝒞.iA n').hom (BA.cell n' s0)) =
    (𝒞.aPart SA p q n' h).hom (BA.cell n' s0) at this
  change (𝒞.Δ SA SL SP p q (n'+1) h).hom ((𝒞.iA n').hom (BA.cell n' s0)) ∈ _
  rw [this]
  change (𝒞.tIc SA p q n' h).hom (BA.cell n' s0) + ((-1 : ℤ)^p) • (𝒞.tIIc SA p q n' h).hom (BA.cell n' s0) ∈ _
  refine Submodule.add_mem _ ?_ (Submodule.smul_of_tower_mem _ _ ?_)
  · cases p with
    | zero => simp [tIc]
    | succ p' =>
      change (𝒞.tI SA p' q n' _).hom (BA.cell n' s0) ∈ _
      unfold tI
      rw [Rep.hom_comp]
      change (𝒞.iA p' ⊗ₘ (a.f q ≫ 𝒞.iL q)).hom ((SA.Δ p' q n' _).hom (BA.cell n' s0)) ∈ _
      refine span_map_mem ((𝒞.iA p' ⊗ₘ (a.f q ≫ 𝒞.iL q)).hom.toLinearMap) ?_ (hd.dgA p' q n' _ s0)
      rintro x ⟨t', t, ht, rfl⟩
      refine Submodule.subset_span ⟨Sum.inl t', inLcell q (ld.aCell q t), ?_, ?_⟩
      · intro m
        rw [pushK_inL, ld.labL_aCell, ht]
        change _ ≤ 𝒟.coneK (T.FA (ld.labA n' s0)) (T.FL (φL (ld.labA n' s0))) (T.FP (φP (ld.labA n' s0))) m
        exact 𝒟.coneK_mono (fun _ => bot_le) (fun _ => le_rfl) (fun _ => bot_le) m
      · rw [coneCell_inL]
        change _ = (𝒞.iA p').hom (BA.cell p' t') ⊗ₜ[ℚ] (𝒞.iL q).hom (BL.cell q (ld.aCell q t))
        rw [← ld.a_cell]
        exact tensorHom_hom_tmul _ _ _ _
  · cases q with
    | zero => simp [tIIc]
    | succ q' =>
      change (𝒞.tII SA p q' n' _).hom (BA.cell n' s0) ∈ _
      unfold tII
      rw [Rep.hom_comp]
      change ((b.f p ≫ 𝒞.iP p) ⊗ₘ 𝒞.iA q').hom ((SA.Δ p q' n' _).hom (BA.cell n' s0)) ∈ _
      refine span_map_mem (((b.f p ≫ 𝒞.iP p) ⊗ₘ 𝒞.iA q').hom.toLinearMap) ?_ (hd.dgA p q' n' _ s0)
      rintro x ⟨t', t, ht, rfl⟩
      refine Submodule.subset_span ⟨inPcell p (ld.bCell p t'), Sum.inl t, ?_, ?_⟩
      · intro m
        change 𝒟.coneK (T.FA (ld.labA q' t)) (T.FL (φL (ld.labA q' t))) (T.FP (φP (ld.labA q' t))) m ≤
          𝒟.coneK (T.FA (ld.labA n' s0)) (T.FL (φL (ld.labA n' s0))) (T.FP (φP (ld.labA n' s0))) m
        rw [ht]
      · rw [coneCell_inP]
        change _ = (𝒞.iP p).hom (BP.cell p (ld.bCell p t')) ⊗ₜ[ℚ] (𝒞.iA q').hom (BA.cell q' t)
        rw [← ld.b_cell]
        exact tensorHom_hom_tmul _ _ _ _

theorem pushCellCarried (hd : ld.Diag SA SL SP) (hS : Strict (a := a) (b := b) SA SL SP) :
    DiagCellCarried (B := coneCells BA BL BP 𝒞) (𝒞.diagSystem SA SL SP hS)
      (pushCarrierData 𝒞 𝒟 ld T) := by
  intro p q n h s
  cases n with
  | zero =>
    rcases s with t | t
    · exact pushCell_Lterm 𝒞 𝒟 ld T SA SL SP hd p q 0 h t
    · exact pushCell_Pterm 𝒞 𝒟 ld T SA SL SP hd p q 0 h t
  | succ n' =>
    rcases s with s0 | s | s
    · exact pushCell_corner 𝒞 𝒟 ld T SA SL SP hd p q n' h s0
    · exact pushCell_Lterm 𝒞 𝒟 ld T SA SL SP hd p q (n'+1) h s
    · exact pushCell_Pterm 𝒞 𝒟 ld T SA SL SP hd p q (n'+1) h s

section Respects

variable {SA' : DiagSystem A'} {SL' : DiagSystem L'} {SP' : DiagSystem P'}

theorem bot_map_mem {X Y : ChainComplex (Rep.{0} ℚ Γ) ℕ} (f : X ⟶ Y) (m : ℕ) (Kf : Submodule ℚ (Y.X m)) :
    ∀ x ∈ (⊥ : Submodule ℚ (X.X m)), (f.f m).hom x ∈ Kf := by
  intro x hx
  rw [Submodule.mem_bot] at hx
  rw [hx, map_zero]; exact Kf.zero_mem

/-- Every carrier of the labelled cone is respected by the diagonal of the target cone. -/
theorem pushK_respects (hS : Strict (a := a') (b := b') SA' SL' SP')
    (rA : ∀ f, DiagRespects SA' (T.FA f)) (rL : ∀ z, DiagRespects SL' (T.FL z))
    (rP : ∀ z, DiagRespects SP' (T.FP z)) (n : ℕ) (s : coneS BA BL BP n) :
    DiagRespects (𝒟.diagSystem SA' SL' SP' hS) (pushK 𝒟 ld T n s) := by
  have key : ∀ (KA : ∀ m, Submodule ℚ (A'.X m)) (KL : ∀ m, Submodule ℚ (L'.X m))
      (KP : ∀ m, Submodule ℚ (P'.X m)), DiagRespects SA' KA → DiagRespects SL' KL → DiagRespects SP' KP →
      (∀ m, ∀ x ∈ KA m, (a'.f m).hom x ∈ KL m) → (∀ m, ∀ x ∈ KA m, (b'.f m).hom x ∈ KP m) →
      DiagRespects (𝒟.diagSystem SA' SL' SP' hS) (𝒟.coneK KA KL KP) :=
    fun KA KL KP hA hL hP ha hb p q n h x hx =>
      𝒟.coneK_respects KA KL KP SA' SL' SP' hA hL hP ha hb p q n h hx
  have hbA : ∀ (KL : ∀ m, Submodule ℚ (L'.X m)),
      ∀ m, ∀ x ∈ (fun m => (⊥ : Submodule ℚ (A'.X m))) m, (a'.f m).hom x ∈ KL m :=
    fun KL m => bot_map_mem a' m (KL m)
  have hbB : ∀ (KP : ∀ m, Submodule ℚ (P'.X m)),
      ∀ m, ∀ x ∈ (fun m => (⊥ : Submodule ℚ (A'.X m))) m, (b'.f m).hom x ∈ KP m :=
    fun KP m => bot_map_mem b' m (KP m)
  have kL : ∀ z, DiagRespects (𝒟.diagSystem SA' SL' SP' hS)
      (𝒟.coneK (fun m => (⊥ : Submodule ℚ (A'.X m))) (T.FL z) (fun m => (⊥ : Submodule ℚ (P'.X m)))) :=
    fun z => key _ _ _ (DiagRespects_bot _) (rL z) (DiagRespects_bot _) (hbA _) (hbB _)
  have kP : ∀ z, DiagRespects (𝒟.diagSystem SA' SL' SP' hS)
      (𝒟.coneK (fun m => (⊥ : Submodule ℚ (A'.X m))) (fun m => (⊥ : Submodule ℚ (L'.X m))) (T.FP z)) :=
    fun z => key _ _ _ (DiagRespects_bot _) (DiagRespects_bot _) (rP z) (hbA _) (hbB _)
  cases n with
  | zero =>
    rcases s with s | s
    · exact kL (ld.labL 0 s)
    · exact kP (ld.labP 0 s)
  | succ n =>
    rcases s with s | s | s
    · exact key (T.FA (ld.labA n s)) (T.FL (φL (ld.labA n s))) (T.FP (φP (ld.labA n s)))
        (rA _) (rL _) (rP _) (T.ha _) (T.hb _)
    · exact kL (ld.labL (n+1) s)
    · exact kP (ld.labP (n+1) s)

theorem pushCapPreserved (hS : Strict (a := a') (b := b') SA' SL' SP')
    (rA : ∀ f, DiagRespects SA' (T.FA f)) (rL : ∀ z, DiagRespects SL' (T.FL z))
    (rP : ∀ z, DiagRespects SP' (T.FP z)) :
    CapCarrierPreserved (B := coneCells BA BL BP 𝒞) (𝒟.diagSystem SA' SL' SP' hS).toCapSystem
      (pushCarrierData 𝒞 𝒟 ld T) := by
  intro W a b hb q n s x hx
  exact (pushK_respects 𝒟 ld T hS rA rL rP n s).cap_mem b hb q hx

end Respects

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
