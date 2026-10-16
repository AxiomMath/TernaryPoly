module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeLabels

@[expose] public section


/-!
# Carrier data of a labelled pushout cone

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

/-- The carrier of a cone cell. -/
def pushK : ∀ n, coneS BA BL BP n → ∀ m, Submodule ℚ (K'.X m)
  | 0, Sum.inl s, m => 𝒟.coneK (fun _ => ⊥) (T.FL (ld.labL 0 s)) (fun _ => ⊥) m
  | 0, Sum.inr s, m => 𝒟.coneK (fun _ => ⊥) (fun _ => ⊥) (T.FP (ld.labP 0 s)) m
  | n+1, Sum.inl s, m => 𝒟.coneK (T.FA (ld.labA n s)) (T.FL (φL (ld.labA n s))) (T.FP (φP (ld.labA n s))) m
  | n+1, Sum.inr (Sum.inl s), m => 𝒟.coneK (fun _ => ⊥) (T.FL (ld.labL (n+1) s)) (fun _ => ⊥) m
  | n+1, Sum.inr (Sum.inr s), m => 𝒟.coneK (fun _ => ⊥) (fun _ => ⊥) (T.FP (ld.labP (n+1) s)) m

theorem pushK_smul (n : ℕ) (γ : Γ) (s : coneS BA BL BP n) (m : ℕ) :
    pushK 𝒟 ld T n (γ • s) m = (pushK 𝒟 ld T n s m).map ((K'.X m).ρ γ) := by
  cases n with
  | zero =>
    rcases s with s | s
    · change 𝒟.coneK (fun _ => ⊥) (T.FL (ld.labL 0 (γ • s))) (fun _ => ⊥) m = _
      exact 𝒟.coneK_smul_family γ (fun m => (Submodule.map_bot _).symm)
        (fun m => by rw [ld.labL_smul, T.FL_smul]) (fun m => (Submodule.map_bot _).symm) m
    · change 𝒟.coneK (fun _ => ⊥) (fun _ => ⊥) (T.FP (ld.labP 0 (γ • s))) m = _
      exact 𝒟.coneK_smul_family γ (fun m => (Submodule.map_bot _).symm)
        (fun m => (Submodule.map_bot _).symm) (fun m => by rw [ld.labP_smul, T.FP_smul]) m
  | succ n =>
    rcases s with s | s | s
    · change 𝒟.coneK (T.FA (ld.labA n (γ • s))) (T.FL (φL (ld.labA n (γ • s))))
        (T.FP (φP (ld.labA n (γ • s)))) m = _
      exact 𝒟.coneK_smul_family γ (fun m => by rw [ld.labA_smul, T.FA_smul])
        (fun m => by rw [ld.labA_smul, ld.φL_smul, T.FL_smul])
        (fun m => by rw [ld.labA_smul, ld.φP_smul, T.FP_smul]) m
    · change 𝒟.coneK (fun _ => ⊥) (T.FL (ld.labL (n+1) (γ • s))) (fun _ => ⊥) m = _
      exact 𝒟.coneK_smul_family γ (fun m => (Submodule.map_bot _).symm)
        (fun m => by rw [ld.labL_smul, T.FL_smul]) (fun m => (Submodule.map_bot _).symm) m
    · change 𝒟.coneK (fun _ => ⊥) (fun _ => ⊥) (T.FP (ld.labP (n+1) (γ • s))) m = _
      exact 𝒟.coneK_smul_family γ (fun m => (Submodule.map_bot _).symm)
        (fun m => (Submodule.map_bot _).symm) (fun m => by rw [ld.labP_smul, T.FP_smul]) m

/-- Cone cell of the `L`-stratum in degree `n`. -/
def inLcell : ∀ n, BL.S n → coneS BA BL BP n
  | 0, t => Sum.inl t
  | _+1, t => Sum.inr (Sum.inl t)

/-- Cone cell of the `P`-stratum in degree `n`. -/
def inPcell : ∀ n, BP.S n → coneS BA BL BP n
  | 0, t => Sum.inr t
  | _+1, t => Sum.inr (Sum.inr t)

theorem coneCell_inL (n : ℕ) (t : BL.S n) :
    coneCell BA BL BP 𝒞 n (inLcell n t) = (𝒞.iL n).hom (BL.cell n t) := by
  cases n <;> rfl

theorem coneCell_inP (n : ℕ) (t : BP.S n) :
    coneCell BA BL BP 𝒞 n (inPcell n t) = (𝒞.iP n).hom (BP.cell n t) := by
  cases n <;> rfl

theorem pushK_inL (n : ℕ) (t : BL.S n) (m : ℕ) :
    pushK 𝒟 ld T n (inLcell n t) m = 𝒟.coneK (fun _ => ⊥) (T.FL (ld.labL n t)) (fun _ => ⊥) m := by
  cases n <;> rfl

theorem pushK_inP (n : ℕ) (t : BP.S n) (m : ℕ) :
    pushK 𝒟 ld T n (inPcell n t) m = 𝒟.coneK (fun _ => ⊥) (fun _ => ⊥) (T.FP (ld.labP n t)) m := by
  cases n <;> rfl

theorem span_map_mem {X Y : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    (f : X →ₗ[ℚ] Y) {S : Set X} {T : Set Y} (h : ∀ x ∈ S, f x ∈ Submodule.span ℚ T) {x : X}
    (hx : x ∈ Submodule.span ℚ S) : f x ∈ Submodule.span ℚ T := by
  have : Submodule.span ℚ S ≤ (Submodule.span ℚ T).comap f := Submodule.span_le.mpr h
  exact this hx

theorem pushK_face (n : ℕ) (s : coneS BA BL BP (n+1)) :
    (K.d (n+1) n).hom (coneCell BA BL BP 𝒞 (n+1) s) ∈ Submodule.span ℚ
      {x | ∃ t : coneS BA BL BP n, (∀ m, pushK 𝒟 ld T n t m ≤ pushK 𝒟 ld T (n+1) s m) ∧
        x = coneCell BA BL BP 𝒞 n t} := by
  rcases s with s | s | s
  · -- corner cell
    change (K.d (n+1) n).hom ((𝒞.iA n).hom (BA.cell n s)) ∈ _
    cases n with
    | zero =>
      rw [𝒞.d_iA_zero, ld.a_cell, ld.b_cell]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨inLcell 0 (ld.aCell 0 s), ?_, ?_⟩)
        (Submodule.subset_span ⟨inPcell 0 (ld.bCell 0 s), ?_, ?_⟩)
      · intro m
        rw [pushK_inL, ld.labL_aCell]
        exact 𝒟.coneK_mono (fun _ => bot_le) (fun _ => le_rfl) (fun _ => bot_le) m
      · exact (coneCell_inL 𝒞 0 _).symm
      · intro m
        rw [pushK_inP, ld.labP_bCell]
        exact 𝒟.coneK_mono (fun _ => bot_le) (fun _ => bot_le) (fun _ => le_rfl) m
      · exact (coneCell_inP 𝒞 0 _).symm
    | succ n =>
      rw [𝒞.d_iA_succ, ld.a_cell, ld.b_cell]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ ?_)
        (Submodule.subset_span ⟨inLcell (n+1) (ld.aCell (n+1) s), ?_, ?_⟩))
        (Submodule.subset_span ⟨inPcell (n+1) (ld.bCell (n+1) s), ?_, ?_⟩)
      · refine span_map_mem (𝒞.iA n).hom.toLinearMap ?_ (ld.bdA n s)
        rintro x ⟨t, ht, rfl⟩
        refine Submodule.subset_span ⟨Sum.inl t, ?_, rfl⟩
        intro m
        change 𝒟.coneK (T.FA (ld.labA n t)) (T.FL (φL (ld.labA n t))) (T.FP (φP (ld.labA n t))) m ≤
          𝒟.coneK (T.FA (ld.labA (n+1) s)) (T.FL (φL (ld.labA (n+1) s))) (T.FP (φP (ld.labA (n+1) s))) m
        rw [ht]
      · intro m
        rw [pushK_inL, ld.labL_aCell]
        exact 𝒟.coneK_mono (fun _ => bot_le) (fun _ => le_rfl) (fun _ => bot_le) m
      · exact (coneCell_inL 𝒞 (n+1) _).symm
      · intro m
        rw [pushK_inP, ld.labP_bCell]
        exact 𝒟.coneK_mono (fun _ => bot_le) (fun _ => bot_le) (fun _ => le_rfl) m
      · exact (coneCell_inP 𝒞 (n+1) _).symm
  · -- line cell
    change (K.d (n+1) n).hom ((𝒞.iL (n+1)).hom (BL.cell (n+1) s)) ∈ _
    rw [𝒞.d_iL]
    refine span_map_mem (𝒞.iL n).hom.toLinearMap ?_ (ld.bdL n s)
    rintro x ⟨t, ht, rfl⟩
    refine Submodule.subset_span ⟨inLcell n t, ?_, (coneCell_inL 𝒞 n t).symm⟩
    intro m
    rw [pushK_inL]
    change _ ≤ 𝒟.coneK (fun _ => ⊥) (T.FL (ld.labL (n+1) s)) (fun _ => ⊥) m
    rw [ht]
  · -- plane cell
    change (K.d (n+1) n).hom ((𝒞.iP (n+1)).hom (BP.cell (n+1) s)) ∈ _
    rw [𝒞.d_iP]
    refine span_map_mem (𝒞.iP n).hom.toLinearMap ?_ (ld.bdP n s)
    rintro x ⟨t, ht, rfl⟩
    refine Submodule.subset_span ⟨inPcell n t, ?_, (coneCell_inP 𝒞 n t).symm⟩
    intro m
    rw [pushK_inP]
    change _ ≤ 𝒟.coneK (fun _ => ⊥) (fun _ => ⊥) (T.FP (ld.labP (n+1) s)) m
    rw [ht]

/-- Hypotheses on the target face carriers: acyclicity and compatibility with the augmentations. -/
structure PushTargets.Good (SA' : DiagSystem A') (SL' : DiagSystem L') (SP' : DiagSystem P')
    (_T : PushTargets 𝒟 ZF ZL ZP φL φP) : Prop where
  hA : ∀ f, SubAcyc A' SA'.eps (_T.FA f)
  hL : ∀ z, SubAcyc L' SL'.eps (_T.FL z)
  hP : ∀ z, SubAcyc P' SP'.eps (_T.FP z)
  haeps : ∀ x, SL'.eps.hom ((a'.f 0).hom x) = SA'.eps.hom x
  hbeps : ∀ x, SP'.eps.hom ((b'.f 0).hom x) = SA'.eps.hom x

variable {SA' : DiagSystem A'} {SL' : DiagSystem L'} {SP' : DiagSystem P'}

theorem pushK_subAcyc (G : PushTargets.Good 𝒟 SA' SL' SP' T) (n : ℕ) (s : coneS BA BL BP n) :
    SubAcyc K' (𝒟.eps SL' SP') (pushK 𝒟 ld T n s) := by
  cases n with
  | zero =>
    rcases s with s | s
    · exact 𝒟.coneK_L_subAcyc _ (G.hL _) G.haeps G.hbeps
    · exact 𝒟.coneK_P_subAcyc _ (G.hP _) G.haeps G.hbeps
  | succ n =>
    rcases s with s | s | s
    · exact 𝒟.coneK_corner_subAcyc _ _ _ (G.hA _) (G.hL _) (G.hP _).toAcyc (T.ha _) (T.hb _) G.haeps G.hbeps
    · exact 𝒟.coneK_L_subAcyc _ (G.hL _) G.haeps G.hbeps
    · exact 𝒟.coneK_P_subAcyc _ (G.hP _) G.haeps G.hbeps

/-- The carrier data of the cells of a labelled pushout cone. -/
def pushCarrierData : CarrierData (coneCells BA BL BP 𝒞) K' where
  K := pushK 𝒟 ld T
  K_smul := pushK_smul 𝒟 ld T
  K_face := pushK_face 𝒞 𝒟 ld T

theorem pushCarrierData_isSubcomplex (G : PushTargets.Good 𝒟 SA' SL' SP' T) :
    (pushCarrierData 𝒞 𝒟 ld T).IsSubcomplex := by
  intro n s m x hx
  exact (pushK_subAcyc 𝒟 ld T G n s).sub m x hx

theorem pushCarrierData_acyclic (hS : PushCone.Strict (a := a') (b := b') SA' SL' SP')
    (G : PushTargets.Good 𝒟 SA' SL' SP' T) :
    (pushCarrierData 𝒞 𝒟 ld T).Acyclic (𝒟.eps SL' SP') where
  aug_d := 𝒟.eps_d hS
  acyc0 n s y hy hy0 := (pushK_subAcyc 𝒟 ld T G n s).acyc0 y hy hy0
  acyc n s m y hy hy0 := (pushK_subAcyc 𝒟 ld T G n s).acyc m y hy hy0

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
