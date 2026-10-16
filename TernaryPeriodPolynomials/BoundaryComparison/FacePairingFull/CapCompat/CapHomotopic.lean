module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Thm
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.DiagSystem

@[expose] public section


/-!
# Homotopy compatibility of caps along a chain map

`CapSystem.Homotopic SC SD u c hc` says that the cap with the pullback `u ≫ c` on the source, followed by `u`, agrees
with `u` followed by the cap with `c` on the target, up to a homotopy `h` (one component for each degree).  It is
the conclusion of `cap_compat`; it composes with a strictly cap-compatible chain map (`Homotopic.comp_strict`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

/-- The cap against `c` of a chain map `u` is homotopic to the cap of the source, through a homotopy `h`. -/
def CapSystem.Homotopic {C D : ChainComplex (Rep.{0} ℚ Γ) ℕ} (SC : CapSystem C)
    (SD : CapSystem D) (u : C ⟶ D) {W : Rep.{0} ℚ Γ} {n : ℕ} (c : D.X n ⟶ W) (hc : D.d (n+1) n ≫ c = 0) : Prop :=
  ∃ h : ∀ q, C.X (n+q) ⟶ W ⊗ D.X (q+1),
    (SC.cap (u.f n ≫ c) (chainMap_cocycle u c hc) 0 ≫ (W ◁ u.f 0) - u.f (n+0) ≫ SD.cap c hc 0 =
      h 0 ≫ (W ◁ D.d 1 0)) ∧
    ∀ q, SC.cap (u.f n ≫ c) (chainMap_cocycle u c hc) (q+1) ≫ (W ◁ u.f (q+1)) -
        u.f (n+(q+1)) ≫ SD.cap c hc (q+1) =
      h (q+1) ≫ (W ◁ D.d (q+1+1) (q+1)) + ((-1 : ℤ)^n) • (C.d (n+q+1) (n+q) ≫ h q)

/-- A chain map is cap-strict if its composite with the cap of the target is the cap of the pullback followed by the
chain map. -/
def CapSystem.Strict {D E : ChainComplex (Rep.{0} ℚ Γ) ℕ} (SD : CapSystem D) (SE : CapSystem E) (g : D ⟶ E) : Prop :=
  ∀ {W : Rep.{0} ℚ Γ} {n : ℕ} (c : E.X n ⟶ W) (hc : E.d (n+1) n ≫ c = 0) (q : ℕ),
    g.f (n+q) ≫ SE.cap c hc q = SD.cap (g.f n ≫ c) (chainMap_cocycle g c hc) q ≫ (W ◁ g.f q)

theorem CapSystem.cap_congr {C : ChainComplex (Rep.{0} ℚ Γ) ℕ} (S : CapSystem C) {W : Rep.{0} ℚ Γ} {a : ℕ}
    {b b' : C.X a ⟶ W} (e : b = b') (hb : C.d (a+1) a ≫ b = 0) (hb' : C.d (a+1) a ≫ b' = 0) (q : ℕ) :
    S.cap b hb q = S.cap b' hb' q := by
  subst e; rfl

theorem CapSystem.Homotopic.comp_strict {C D E : ChainComplex (Rep.{0} ℚ Γ) ℕ} {SC : CapSystem C}
    {SD : CapSystem D} {SE : CapSystem E} {u : C ⟶ D} (g : D ⟶ E) (hg : SD.Strict SE g)
    {W : Rep.{0} ℚ Γ} {n : ℕ} (c : E.X n ⟶ W) (hc : E.d (n+1) n ≫ c = 0)
    (H : SC.Homotopic SD u (g.f n ≫ c) (chainMap_cocycle g c hc)) :
    SC.Homotopic SE (u ≫ g) c hc := by
  obtain ⟨h, h0, hq⟩ := H
  have hc1 : ∀ q, SC.cap ((u ≫ g).f n ≫ c) (chainMap_cocycle (u ≫ g) c hc) q =
      SC.cap (u.f n ≫ g.f n ≫ c) (chainMap_cocycle u (g.f n ≫ c) (chainMap_cocycle g c hc)) q :=
    fun q => SC.cap_congr (Category.assoc _ _ _) _ _ q
  refine ⟨fun q => h q ≫ (W ◁ g.f (q+1)), ?_, ?_⟩
  · have e1 := congrArg (fun m => m ≫ (W ◁ g.f 0)) h0
    have e2 := hg c hc 0
    have e3 : D.d 1 0 ≫ g.f 0 = g.f 1 ≫ E.d 1 0 := (g.comm 1 0).symm
    simp only [Preadditive.sub_comp, Category.assoc] at e1
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, e3,
      MonoidalCategory.whiskerLeft_comp] at e1
    rw [hc1 0]
    have e4 : (u ≫ g).f (n+0) ≫ SE.cap c hc 0 = u.f (n+0) ≫ SD.cap (g.f n ≫ c) (chainMap_cocycle g c hc) 0 ≫
        (W ◁ g.f 0) := by
      rw [HomologicalComplex.comp_f, Category.assoc, e2]
    have e5 : (u ≫ g).f 0 = u.f 0 ≫ g.f 0 := rfl
    rw [e4, e5, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    refine e1.trans ?_
    rw [MonoidalCategory.whiskerLeft_comp]
  · intro q
    have e1 := congrArg (fun m => m ≫ (W ◁ g.f (q+1))) (hq q)
    have e2 := hg c hc (q+1)
    have e3 : D.d (q+1+1) (q+1) ≫ g.f (q+1) = g.f (q+1+1) ≫ E.d (q+1+1) (q+1) :=
      (g.comm (q+1+1) (q+1)).symm
    simp only [Preadditive.sub_comp, Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc] at e1
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, e3,
      MonoidalCategory.whiskerLeft_comp] at e1
    rw [hc1 (q+1)]
    have e4 : (u ≫ g).f (n+(q+1)) ≫ SE.cap c hc (q+1) =
        u.f (n+(q+1)) ≫ SD.cap (g.f n ≫ c) (chainMap_cocycle g c hc) (q+1) ≫ (W ◁ g.f (q+1)) := by
      rw [HomologicalComplex.comp_f, Category.assoc, e2]
    have e5 : (u ≫ g).f (q+1) = u.f (q+1) ≫ g.f (q+1) := rfl
    rw [e4, e5, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    refine e1.trans ?_
    simp only [MonoidalCategory.whiskerLeft_comp]

theorem DiagSystem.capStrict {C D : ChainComplex (Rep.{0} ℚ Γ) ℕ} (SC : DiagSystem C) (SD : DiagSystem D)
    (g : C ⟶ D) (hg : ∀ p q n (h : p + q = n), g.f n ≫ SD.Δ p q n h = SC.Δ p q n h ≫ (g.f p ⊗ₘ g.f q)) :
    SC.toCapSystem.Strict SD.toCapSystem g := by
  intro W n c hc q
  change g.f (n+q) ≫ (SD.Δ n q (n+q) rfl ≫ (c ▷ D.X q)) =
    (SC.Δ n q (n+q) rfl ≫ ((g.f n ≫ c) ▷ C.X q)) ≫ (W ◁ g.f q)
  rw [← Category.assoc, hg, Category.assoc, Category.assoc, MonoidalCategory.tensorHom_def,
    Category.assoc, MonoidalCategory.comp_whiskerRight, Category.assoc, ← MonoidalCategory.whisker_exchange]

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
