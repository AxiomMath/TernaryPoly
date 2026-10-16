module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeCarriers

@[expose] public section


/-!
# Carrier data on the cells of a pushout cone from labelled strata

The cells of the cone are labelled by flags `f` (shifted corner cells), lines (line cells) and planes (plane
cells).  A corner cell is carried by the cone carrier of the triple `(K_A f, K_L (ℓ f), K_P (p f))` of face carriers of
its flag, a line cell by `(0, K_L ℓ, 0)` and a plane cell by `(0, 0, K_P p)`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

namespace PushCone

variable {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  (𝒞 : PushCone A L P K a b)

theorem map_rep_hom {X Y : Rep.{0} ℚ Γ} (f : X ⟶ Y) (γ : Γ) (S : Submodule ℚ X) :
    (S.map f.hom.toLinearMap).map (Y.ρ γ) = (S.map (X.ρ γ)).map f.hom.toLinearMap := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  exact (Rep.hom_comm_apply f γ x).symm

variable (KA : ∀ m, Submodule ℚ (A.X m)) (KL : ∀ m, Submodule ℚ (L.X m)) (KP : ∀ m, Submodule ℚ (P.X m))

theorem coneK_map (γ : Γ) (m : ℕ) :
    (𝒞.coneK KA KL KP m).map ((K.X m).ρ γ) =
      𝒞.coneK (fun m => (KA m).map ((A.X m).ρ γ)) (fun m => (KL m).map ((L.X m).ρ γ))
        (fun m => (KP m).map ((P.X m).ρ γ)) m := by
  cases m with
  | zero =>
    unfold coneK
    rw [Submodule.map_sup, map_rep_hom, map_rep_hom]
  | succ m =>
    unfold coneK
    rw [Submodule.map_sup, Submodule.map_sup, map_rep_hom, map_rep_hom, map_rep_hom]

end PushCone

/-- Labels on the cells of three strata with equivariant label maps `φL`, `φP` from the corner labels. -/
structure PushLabels {A L P : ChainComplex (Rep.{0} ℚ Γ) ℕ} (a : A ⟶ L) (b : A ⟶ P)
    (BA : CellBasis A) (BL : CellBasis L) (BP : CellBasis P) (ZF ZL ZP : Type)
    [MulAction Γ ZF] [MulAction Γ ZL] [MulAction Γ ZP] (φL : ZF → ZL) (φP : ZF → ZP) where
  φL_smul : ∀ (γ : Γ) (f : ZF), φL (γ • f) = γ • φL f
  φP_smul : ∀ (γ : Γ) (f : ZF), φP (γ • f) = γ • φP f
  labA : ∀ n, BA.S n → ZF
  labL : ∀ n, BL.S n → ZL
  labP : ∀ n, BP.S n → ZP
  labA_smul : ∀ n (γ : Γ) (s : BA.S n), labA n (γ • s) = γ • labA n s
  labL_smul : ∀ n (γ : Γ) (s : BL.S n), labL n (γ • s) = γ • labL n s
  labP_smul : ∀ n (γ : Γ) (s : BP.S n), labP n (γ • s) = γ • labP n s
  bdA : ∀ n (s : BA.S (n+1)), (A.d (n+1) n).hom (BA.cell (n+1) s) ∈
    Submodule.span ℚ {x | ∃ t : BA.S n, labA n t = labA (n+1) s ∧ x = BA.cell n t}
  bdL : ∀ n (s : BL.S (n+1)), (L.d (n+1) n).hom (BL.cell (n+1) s) ∈
    Submodule.span ℚ {x | ∃ t : BL.S n, labL n t = labL (n+1) s ∧ x = BL.cell n t}
  bdP : ∀ n (s : BP.S (n+1)), (P.d (n+1) n).hom (BP.cell (n+1) s) ∈
    Submodule.span ℚ {x | ∃ t : BP.S n, labP n t = labP (n+1) s ∧ x = BP.cell n t}
  aCell : ∀ n, BA.S n → BL.S n
  a_cell : ∀ n (s : BA.S n), (a.f n).hom (BA.cell n s) = BL.cell n (aCell n s)
  labL_aCell : ∀ n (s : BA.S n), labL n (aCell n s) = φL (labA n s)
  bCell : ∀ n, BA.S n → BP.S n
  b_cell : ∀ n (s : BA.S n), (b.f n).hom (BA.cell n s) = BP.cell n (bCell n s)
  labP_bCell : ∀ n (s : BA.S n), labP n (bCell n s) = φP (labA n s)

namespace PushCone

variable {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  (𝒞 : PushCone A L P K a b)
  {KA KA' : ∀ m, Submodule ℚ (A.X m)} {KL KL' : ∀ m, Submodule ℚ (L.X m)} {KP KP' : ∀ m, Submodule ℚ (P.X m)}

theorem coneK_mono (hA : ∀ m, KA m ≤ KA' m) (hL : ∀ m, KL m ≤ KL' m) (hP : ∀ m, KP m ≤ KP' m) (m : ℕ) :
    𝒞.coneK KA KL KP m ≤ 𝒞.coneK KA' KL' KP' m := by
  cases m with
  | zero =>
    unfold coneK
    exact sup_le_sup (Submodule.map_mono (hL 0)) (Submodule.map_mono (hP 0))
  | succ m =>
    unfold coneK
    exact sup_le_sup (sup_le_sup (Submodule.map_mono (hA m)) (Submodule.map_mono (hL (m+1))))
      (Submodule.map_mono (hP (m+1)))

theorem coneK_smul_family (γ : Γ) (hA : ∀ m, KA' m = (KA m).map ((A.X m).ρ γ))
    (hL : ∀ m, KL' m = (KL m).map ((L.X m).ρ γ)) (hP : ∀ m, KP' m = (KP m).map ((P.X m).ρ γ)) (m : ℕ) :
    𝒞.coneK KA' KL' KP' m = (𝒞.coneK KA KL KP m).map ((K.X m).ρ γ) := by
  rw [coneK_map]
  have e1 : KA' = fun m => (KA m).map ((A.X m).ρ γ) := funext hA
  have e2 : KL' = fun m => (KL m).map ((L.X m).ρ γ) := funext hL
  have e3 : KP' = fun m => (KP m).map ((P.X m).ρ γ) := funext hP
  rw [e1, e2, e3]

theorem coneK_bot_mono (KA : ∀ m, Submodule ℚ (A.X m)) (KL : ∀ m, Submodule ℚ (L.X m))
    (KP : ∀ m, Submodule ℚ (P.X m)) (m : ℕ) :
    𝒞.coneK (fun _ => ⊥) KL (fun _ => ⊥) m ≤ 𝒞.coneK KA KL KP m :=
  𝒞.coneK_mono (fun _ => bot_le) (fun _ => le_rfl) (fun _ => bot_le) m

theorem coneK_bot_mono' (KA : ∀ m, Submodule ℚ (A.X m)) (KL : ∀ m, Submodule ℚ (L.X m))
    (KP : ∀ m, Submodule ℚ (P.X m)) (m : ℕ) :
    𝒞.coneK (fun _ => ⊥) (fun _ => ⊥) KP m ≤ 𝒞.coneK KA KL KP m :=
  𝒞.coneK_mono (fun _ => bot_le) (fun _ => bot_le) (fun _ => le_rfl) m

end PushCone

/-- Face carriers in the three target strata, indexed by the labels, compatible with the incidence maps. -/
structure PushTargets {A' L' P' K' : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a' : A' ⟶ L'} {b' : A' ⟶ P'}
    (_𝒟 : PushCone A' L' P' K' a' b') (ZF ZL ZP : Type) [MulAction Γ ZF] [MulAction Γ ZL] [MulAction Γ ZP]
    (φL : ZF → ZL) (φP : ZF → ZP) where
  FA : ZF → ∀ m, Submodule ℚ (A'.X m)
  FL : ZL → ∀ m, Submodule ℚ (L'.X m)
  FP : ZP → ∀ m, Submodule ℚ (P'.X m)
  FA_smul : ∀ (γ : Γ) (f : ZF) (m : ℕ), FA (γ • f) m = (FA f m).map ((A'.X m).ρ γ)
  FL_smul : ∀ (γ : Γ) (f : ZL) (m : ℕ), FL (γ • f) m = (FL f m).map ((L'.X m).ρ γ)
  FP_smul : ∀ (γ : Γ) (f : ZP) (m : ℕ), FP (γ • f) m = (FP f m).map ((P'.X m).ρ γ)
  ha : ∀ f m, ∀ x ∈ FA f m, (a'.f m).hom x ∈ FL (φL f) m
  hb : ∀ f m, ∀ x ∈ FA f m, (b'.f m).hom x ∈ FP (φP f) m

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
