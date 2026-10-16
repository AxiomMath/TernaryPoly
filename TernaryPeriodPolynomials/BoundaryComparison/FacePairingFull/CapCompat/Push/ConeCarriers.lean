module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeElem
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Carriers

@[expose] public section


/-!
# Carriers of a pushout cone from carriers of its three strata

Given subspaces `KA m ⊆ A.X m`, `KL m ⊆ L.X m`, `KP m ⊆ P.X m` (sub-complexes, augmented acyclic, with
`a(KA) ⊆ KL`, `b(KA) ⊆ KP`), the subspaces `iA(KA) + iL(KL) + iP(KP)` of the pushout cone form a sub-complex which is
augmented acyclic (`coneK_acyclic`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]
  {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}

/-- A family of subspaces of a complex that is a subcomplex and augmented acyclic. -/
structure Acyc (D : ChainComplex (Rep.{0} ℚ Γ) ℕ) (aug : D.X 0 ⟶ 𝟙_ (Rep.{0} ℚ Γ))
    (Kf : ∀ m, Submodule ℚ (D.X m)) : Prop where
  sub : ∀ m, ∀ x ∈ Kf (m+1), (D.d (m+1) m).hom x ∈ Kf m
  acyc0 : ∀ y ∈ Kf 0, aug.hom y = 0 → ∃ x ∈ Kf 1, (D.d 1 0).hom x = y
  acyc : ∀ m, ∀ y ∈ Kf (m+1), (D.d (m+1) m).hom y = 0 → ∃ x ∈ Kf (m+2), (D.d (m+2) (m+1)).hom x = y

/-- An acyclic family with an element of augmentation one. -/
structure SubAcyc (D : ChainComplex (Rep.{0} ℚ Γ) ℕ) (aug : D.X 0 ⟶ 𝟙_ (Rep.{0} ℚ Γ))
    (Kf : ∀ m, Submodule ℚ (D.X m)) : Prop extends Acyc D aug Kf where
  surj : ∃ y ∈ Kf 0, aug.hom y = (1 : ℚ)

theorem Acyc_bot (D : ChainComplex (Rep.{0} ℚ Γ) ℕ) (aug : D.X 0 ⟶ 𝟙_ (Rep.{0} ℚ Γ)) :
    Acyc D aug (fun _ => ⊥) where
  sub m x hx := by
    rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _
  acyc0 y hy _ := ⟨0, Submodule.zero_mem _, by rw [Submodule.mem_bot] at hy; rw [hy, map_zero]⟩
  acyc m y hy _ := ⟨0, Submodule.zero_mem _, by rw [Submodule.mem_bot] at hy; rw [hy, map_zero]⟩

namespace PushCone

variable (𝒞 : PushCone A L P K a b)

theorem d_iL (m : ℕ) (l : L.X (m+1)) :
    (K.d (m+1) m).hom ((𝒞.iL (m+1)).hom l) = (𝒞.iL m).hom ((L.d (m+1) m).hom l) :=
  congrArg (fun φ => φ.hom l) (𝒞.dL m)

theorem d_iP (m : ℕ) (p : P.X (m+1)) :
    (K.d (m+1) m).hom ((𝒞.iP (m+1)).hom p) = (𝒞.iP m).hom ((P.d (m+1) m).hom p) :=
  congrArg (fun φ => φ.hom p) (𝒞.dP m)

theorem d_iA_zero (x : A.X 0) :
    (K.d 1 0).hom ((𝒞.iA 0).hom x) = (𝒞.iL 0).hom (a.f 0 |>.hom x) - (𝒞.iP 0).hom (b.f 0 |>.hom x) := by
  have := congrArg (fun φ => φ.hom x) 𝒞.dA0
  simpa [Rep.sub_hom, Rep.add_hom, Rep.neg_hom] using this

theorem d_iA_succ (m : ℕ) (x : A.X (m+1)) :
    (K.d (m+2) (m+1)).hom ((𝒞.iA (m+1)).hom x) =
      -(𝒞.iA m).hom ((A.d (m+1) m).hom x) + (𝒞.iL (m+1)).hom (a.f (m+1) |>.hom x) -
        (𝒞.iP (m+1)).hom (b.f (m+1) |>.hom x) := by
  have := congrArg (fun φ => φ.hom x) (𝒞.dA m)
  simpa [Rep.sub_hom, Rep.add_hom, Rep.neg_hom] using this

variable (KA : ∀ m, Submodule ℚ (A.X m)) (KL : ∀ m, Submodule ℚ (L.X m)) (KP : ∀ m, Submodule ℚ (P.X m))

/-- The cone carrier attached to a triple of subspace families. -/
def coneK : ∀ m, Submodule ℚ (K.X m)
  | 0 => (KL 0).map (𝒞.iL 0).hom.toLinearMap ⊔ (KP 0).map (𝒞.iP 0).hom.toLinearMap
  | m+1 => ((KA m).map (𝒞.iA m).hom.toLinearMap ⊔ (KL (m+1)).map (𝒞.iL (m+1)).hom.toLinearMap) ⊔
      (KP (m+1)).map (𝒞.iP (m+1)).hom.toLinearMap

theorem mem_coneK_zero (z : K.X 0) :
    z ∈ 𝒞.coneK KA KL KP 0 ↔ ∃ l ∈ KL 0, ∃ p ∈ KP 0, z = (𝒞.iL 0).hom l + (𝒞.iP 0).hom p := by
  unfold coneK
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨u, ⟨l, hl, rfl⟩, v, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨l, hl, p, hp, rfl⟩
  · rintro ⟨l, hl, p, hp, rfl⟩
    exact ⟨_, ⟨l, hl, rfl⟩, _, ⟨p, hp, rfl⟩, rfl⟩

theorem mem_coneK_succ (m : ℕ) (z : K.X (m+1)) :
    z ∈ 𝒞.coneK KA KL KP (m+1) ↔ ∃ x ∈ KA m, ∃ l ∈ KL (m+1), ∃ p ∈ KP (m+1),
      z = (𝒞.iA m).hom x + (𝒞.iL (m+1)).hom l + (𝒞.iP (m+1)).hom p := by
  unfold coneK
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, ⟨p, hp, rfl⟩, rfl⟩
    rw [Submodule.mem_sup] at hu
    obtain ⟨u1, ⟨x, hx, rfl⟩, u2, ⟨l, hl, rfl⟩, rfl⟩ := hu
    exact ⟨x, hx, l, hl, p, hp, rfl⟩
  · rintro ⟨x, hx, l, hl, p, hp, rfl⟩
    exact ⟨_, Submodule.mem_sup.mpr ⟨_, ⟨x, hx, rfl⟩, _, ⟨l, hl, rfl⟩, rfl⟩, _, ⟨p, hp, rfl⟩, rfl⟩

theorem pL0_iL (l : L.X 0) : (𝒞.pL0).hom ((𝒞.iL 0).hom l) = l := by
  have := congrArg (fun φ => φ.hom l) (𝒞.iL0_desc0 (𝟙 (L.X 0)) (0 : P.X 0 ⟶ L.X 0))
  unfold pL0; simpa using this

theorem pL0_iP (p : P.X 0) : (𝒞.pL0).hom ((𝒞.iP 0).hom p) = 0 := by
  have := congrArg (fun φ => φ.hom p) (𝒞.iP0_desc0 (𝟙 (L.X 0)) (0 : P.X 0 ⟶ L.X 0))
  unfold pL0; simpa using this

theorem pP0_iL (l : L.X 0) : (𝒞.pP0).hom ((𝒞.iL 0).hom l) = 0 := by
  have := congrArg (fun φ => φ.hom l) (𝒞.iL0_desc0 (0 : L.X 0 ⟶ P.X 0) (𝟙 (P.X 0)))
  unfold pP0; simpa using this

theorem pP0_iP (p : P.X 0) : (𝒞.pP0).hom ((𝒞.iP 0).hom p) = p := by
  have := congrArg (fun φ => φ.hom p) (𝒞.iP0_desc0 (0 : L.X 0 ⟶ P.X 0) (𝟙 (P.X 0)))
  unfold pP0; simpa using this

theorem eq_zero_zero {l : L.X 0} {p : P.X 0} (h : (𝒞.iL 0).hom l + (𝒞.iP 0).hom p = 0) : l = 0 ∧ p = 0 := by
  constructor
  · have := congrArg (𝒞.pL0).hom h
    simpa [pL0_iL, pL0_iP] using this
  · have := congrArg (𝒞.pP0).hom h
    simpa [pP0_iL, pP0_iP] using this

theorem eq_zero_succ {m : ℕ} {x : A.X m} {l : L.X (m+1)} {p : P.X (m+1)}
    (h : (𝒞.iA m).hom x + (𝒞.iL (m+1)).hom l + (𝒞.iP (m+1)).hom p = 0) : x = 0 ∧ l = 0 ∧ p = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (𝒞.pA m).hom h
    simpa [pA_iA, pA_iL, pA_iP] using this
  · have := congrArg (𝒞.pL m).hom h
    simpa [pL_iA, pL_iL, pL_iP] using this
  · have := congrArg (𝒞.pP m).hom h
    simpa [pP_iA, pP_iL, pP_iP] using this

variable {SA : DiagSystem A} {SL : DiagSystem L} {SP : DiagSystem P}

theorem coneK_sub (hA : ∀ m, ∀ x ∈ KA (m+1), (A.d (m+1) m).hom x ∈ KA m)
    (hL : ∀ m, ∀ x ∈ KL (m+1), (L.d (m+1) m).hom x ∈ KL m)
    (hP : ∀ m, ∀ x ∈ KP (m+1), (P.d (m+1) m).hom x ∈ KP m)
    (ha : ∀ m, ∀ x ∈ KA m, (a.f m).hom x ∈ KL m) (hb : ∀ m, ∀ x ∈ KA m, (b.f m).hom x ∈ KP m) :
    ∀ m, ∀ z ∈ 𝒞.coneK KA KL KP (m+1), (K.d (m+1) m).hom z ∈ 𝒞.coneK KA KL KP m := by
  intro m z hz
  rw [𝒞.mem_coneK_succ KA KL KP m] at hz
  obtain ⟨x, hx, l, hl, p, hp, rfl⟩ := hz
  cases m with
  | zero =>
    rw [𝒞.mem_coneK_zero KA KL KP]
    refine ⟨(a.f 0).hom x + (L.d 1 0).hom l, (KL 0).add_mem (ha 0 x hx) (hL 0 l hl), 
      -(b.f 0).hom x + (P.d 1 0).hom p, (KP 0).add_mem ((KP 0).neg_mem (hb 0 x hx)) (hP 0 p hp), ?_⟩
    rw [map_add, map_add, 𝒞.d_iA_zero, 𝒞.d_iL, 𝒞.d_iP]
    simp only [map_add, map_neg]
    abel
  | succ m =>
    rw [𝒞.mem_coneK_succ KA KL KP m]
    refine ⟨-(A.d (m+1) m).hom x, (KA m).neg_mem (hA m x hx), (a.f (m+1)).hom x + (L.d (m+2) (m+1)).hom l,
      (KL (m+1)).add_mem (ha _ x hx) (hL _ l hl), -(b.f (m+1)).hom x + (P.d (m+2) (m+1)).hom p,
      (KP (m+1)).add_mem ((KP (m+1)).neg_mem (hb _ x hx)) (hP _ p hp), ?_⟩
    rw [map_add, map_add, 𝒞.d_iA_succ, 𝒞.d_iL, 𝒞.d_iP]
    simp only [map_add, map_neg]
    abel

theorem chain_a (m : ℕ) (x : A.X (m+1)) :
    (L.d (m+1) m).hom ((a.f (m+1)).hom x) = (a.f m).hom ((A.d (m+1) m).hom x) :=
  congrArg (fun φ => φ.hom x) (a.comm (m+1) m)

theorem chain_b (m : ℕ) (x : A.X (m+1)) :
    (P.d (m+1) m).hom ((b.f (m+1)).hom x) = (b.f m).hom ((A.d (m+1) m).hom x) :=
  congrArg (fun φ => φ.hom x) (b.comm (m+1) m)

theorem cone_finish (hL : ∀ m, ∀ y ∈ KL (m+1), (L.d (m+1) m).hom y = 0 → ∃ x ∈ KL (m+2), (L.d (m+2) (m+1)).hom x = y)
    (hP : ∀ m, ∀ y ∈ KP (m+1), (P.d (m+1) m).hom y = 0 → ∃ x ∈ KP (m+2), (P.d (m+2) (m+1)).hom x = y)
    (ha : ∀ m, ∀ x ∈ KA m, (a.f m).hom x ∈ KL m) (hb : ∀ m, ∀ x ∈ KA m, (b.f m).hom x ∈ KP m)
    (m : ℕ) {x0 : A.X m} {l : L.X (m+1)} {p : P.X (m+1)} (x' : A.X (m+1)) (hx' : x' ∈ KA (m+1))
    (hl : l ∈ KL (m+1)) (hp : p ∈ KP (m+1)) (hAd : (A.d (m+1) m).hom x' = x0)
    (hl0 : (a.f m).hom x0 + (L.d (m+1) m).hom l = 0) (hp0 : -(b.f m).hom x0 + (P.d (m+1) m).hom p = 0) :
    ∃ z ∈ 𝒞.coneK KA KL KP (m+2), (K.d (m+2) (m+1)).hom z =
      (𝒞.iA m).hom x0 + (𝒞.iL (m+1)).hom l + (𝒞.iP (m+1)).hom p := by
  subst hAd
  obtain ⟨u, hu, hud⟩ := hL m (l + (a.f (m+1)).hom x') ((KL (m+1)).add_mem hl (ha _ x' hx')) (by
    rw [map_add, chain_a, add_comm]; exact hl0)
  obtain ⟨v, hv, hvd⟩ := hP m (p - (b.f (m+1)).hom x') ((KP (m+1)).sub_mem hp (hb _ x' hx')) (by
    rw [map_sub, chain_b, sub_eq_add_neg, add_comm]; exact hp0)
  refine ⟨(𝒞.iA (m+1)).hom (-x') + (𝒞.iL (m+2)).hom u + (𝒞.iP (m+2)).hom v, ?_, ?_⟩
  · rw [𝒞.mem_coneK_succ KA KL KP (m+1)]
    exact ⟨-x', (KA (m+1)).neg_mem hx', u, hu, v, hv, rfl⟩
  · rw [map_add, map_add, 𝒞.d_iA_succ, 𝒞.d_iL, 𝒞.d_iP, hud, hvd]
    simp only [map_neg, map_add, map_sub]
    abel

theorem eps_iL (SL : DiagSystem L) (SP : DiagSystem P) (l : L.X 0) :
    (𝒞.eps SL SP).hom ((𝒞.iL 0).hom l) = SL.eps.hom l :=
  congrArg (fun φ => φ.hom l) (𝒞.iL0_desc0 SL.eps SP.eps)

theorem eps_iP (SL : DiagSystem L) (SP : DiagSystem P) (p : P.X 0) :
    (𝒞.eps SL SP).hom ((𝒞.iP 0).hom p) = SP.eps.hom p :=
  congrArg (fun φ => φ.hom p) (𝒞.iP0_desc0 SL.eps SP.eps)

theorem coneK_acyc (hA : Acyc A SA.eps KA) (hL : Acyc L SL.eps KL) (hP : Acyc P SP.eps KP)
    (ha : ∀ m, ∀ x ∈ KA m, (a.f m).hom x ∈ KL m) (hb : ∀ m, ∀ x ∈ KA m, (b.f m).hom x ∈ KP m)
    (haeps : ∀ x, SL.eps.hom ((a.f 0).hom x) = SA.eps.hom x)
    (hbeps : ∀ x, SP.eps.hom ((b.f 0).hom x) = SA.eps.hom x)
    (hglue : ∀ l ∈ KL 0, ∀ p ∈ KP 0, SL.eps.hom l + SP.eps.hom p = 0 → ∃ x0 ∈ KA 0, SA.eps.hom x0 = SL.eps.hom l) :
    Acyc K (𝒞.eps SL SP) (𝒞.coneK KA KL KP) where
  sub := coneK_sub 𝒞 KA KL KP hA.sub hL.sub hP.sub ha hb
  acyc0 := by
    intro y hy hy0
    obtain ⟨l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_zero KA KL KP y).mp hy
    rw [map_add, 𝒞.eps_iL SL SP, 𝒞.eps_iP SL SP] at hy0
    obtain ⟨x0, hx0, hx0a⟩ := hglue l hl p hp hy0
    obtain ⟨u, hu, hud⟩ := hL.acyc0 (l - (a.f 0).hom x0) ((KL 0).sub_mem hl (ha _ x0 hx0)) (by
      rw [map_sub, haeps, hx0a, sub_self])
    obtain ⟨v, hv, hvd⟩ := hP.acyc0 (p + (b.f 0).hom x0) ((KP 0).add_mem hp (hb _ x0 hx0)) (by
      rw [map_add, hbeps, hx0a, add_comm]; exact hy0)
    refine ⟨(𝒞.iA 0).hom x0 + (𝒞.iL 1).hom u + (𝒞.iP 1).hom v, ?_, ?_⟩
    · rw [𝒞.mem_coneK_succ KA KL KP 0]
      exact ⟨x0, hx0, u, hu, v, hv, rfl⟩
    · rw [map_add, map_add, 𝒞.d_iA_zero, 𝒞.d_iL, 𝒞.d_iP, hud, hvd]
      simp only [map_sub, map_add]
      abel
  acyc := by
    intro m y hy hyd
    obtain ⟨x, hx, l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_succ KA KL KP m y).mp hy
    cases m with
    | zero =>
      rw [map_add, map_add, 𝒞.d_iA_zero, 𝒞.d_iL, 𝒞.d_iP] at hyd
      have h0 : (𝒞.iL 0).hom ((a.f 0).hom x + (L.d 1 0).hom l) +
          (𝒞.iP 0).hom (-(b.f 0).hom x + (P.d 1 0).hom p) = 0 := by
        rw [← hyd]; simp only [map_add, map_neg]; abel
      obtain ⟨h1, h2⟩ := 𝒞.eq_zero_zero h0
      have hxa : SA.eps.hom x = 0 := by
        have h3 := congrArg SL.eps.hom h1
        have hd : SL.eps.hom ((L.d 1 0).hom l) = 0 := by
          have := congrArg (fun φ => φ.hom l) SL.eps_d
          simpa using this
        rw [map_add, haeps, hd, add_zero, map_zero] at h3
        exact h3
      obtain ⟨x', hx', hx'd⟩ := hA.acyc0 x hx hxa
      exact 𝒞.cone_finish KA KL KP hL.acyc hP.acyc ha hb 0 x' hx' hl hp hx'd h1 h2
    | succ m =>
      rw [map_add, map_add, 𝒞.d_iA_succ, 𝒞.d_iL, 𝒞.d_iP] at hyd
      have h0 : (𝒞.iA m).hom (-(A.d (m+1) m).hom x) +
          (𝒞.iL (m+1)).hom ((a.f (m+1)).hom x + (L.d (m+2) (m+1)).hom l) +
          (𝒞.iP (m+1)).hom (-(b.f (m+1)).hom x + (P.d (m+2) (m+1)).hom p) = 0 := by
        rw [← hyd]; simp only [map_add, map_neg]; abel
      obtain ⟨h1, h2, h3⟩ := 𝒞.eq_zero_succ h0
      have hx0 : (A.d (m+1) m).hom x = 0 := neg_eq_zero.mp h1
      obtain ⟨x', hx', hx'd⟩ := hA.acyc m x hx hx0
      exact 𝒞.cone_finish KA KL KP hL.acyc hP.acyc ha hb (m+1) x' hx' hl hp hx'd h2 h3

theorem coneK_surj_L (SL : DiagSystem L) (SP : DiagSystem P) (hL : ∃ y ∈ KL 0, SL.eps.hom y = (1 : ℚ)) :
    ∃ y ∈ 𝒞.coneK KA KL KP 0, (𝒞.eps SL SP).hom y = (1 : ℚ) := by
  obtain ⟨y, hy, hya⟩ := hL
  refine ⟨(𝒞.iL 0).hom y, ?_, ?_⟩
  · rw [𝒞.mem_coneK_zero KA KL KP]
    exact ⟨y, hy, 0, (KP 0).zero_mem, by simp⟩
  · rw [𝒞.eps_iL SL SP]; exact hya

theorem coneK_surj_P (SL : DiagSystem L) (SP : DiagSystem P) (hP : ∃ y ∈ KP 0, SP.eps.hom y = (1 : ℚ)) :
    ∃ y ∈ 𝒞.coneK KA KL KP 0, (𝒞.eps SL SP).hom y = (1 : ℚ) := by
  obtain ⟨y, hy, hya⟩ := hP
  refine ⟨(𝒞.iP 0).hom y, ?_, ?_⟩
  · rw [𝒞.mem_coneK_zero KA KL KP]
    exact ⟨0, (KL 0).zero_mem, y, hy, by simp⟩
  · rw [𝒞.eps_iP SL SP]; exact hya

theorem coneK_corner_subAcyc (hA : SubAcyc A SA.eps KA) (hL : SubAcyc L SL.eps KL)
    (hP : Acyc P SP.eps KP) (ha : ∀ m, ∀ x ∈ KA m, (a.f m).hom x ∈ KL m)
    (hb : ∀ m, ∀ x ∈ KA m, (b.f m).hom x ∈ KP m)
    (haeps : ∀ x, SL.eps.hom ((a.f 0).hom x) = SA.eps.hom x)
    (hbeps : ∀ x, SP.eps.hom ((b.f 0).hom x) = SA.eps.hom x) :
    SubAcyc K (𝒞.eps SL SP) (𝒞.coneK KA KL KP) where
  toAcyc := coneK_acyc 𝒞 KA KL KP hA.toAcyc hL.toAcyc hP ha hb haeps hbeps (by
    intro l _ p _ hlp
    obtain ⟨y1, hy1, hy1a⟩ := hA.surj
    exact ⟨(SL.eps.hom l) • y1, (KA 0).smul_mem _ hy1, by rw [map_smul, hy1a]; simp⟩)
  surj := 𝒞.coneK_surj_L KA KL KP SL SP hL.surj

theorem coneK_L_subAcyc (hL : SubAcyc L SL.eps KL)
    (haeps : ∀ x, SL.eps.hom ((a.f 0).hom x) = SA.eps.hom x)
    (hbeps : ∀ x, SP.eps.hom ((b.f 0).hom x) = SA.eps.hom x) :
    SubAcyc K (𝒞.eps SL SP) (𝒞.coneK (fun _ => ⊥) KL (fun _ => ⊥)) where
  toAcyc := coneK_acyc 𝒞 (fun _ => ⊥) KL (fun _ => ⊥) (Acyc_bot A SA.eps) hL.toAcyc (Acyc_bot P SP.eps)
    (fun m x hx => by
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]; exact Submodule.zero_mem _)
    (fun m x hx => by
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]; exact Submodule.zero_mem _)
    (haeps) (hbeps) (by
      intro l _ p hp hlp
      rw [Submodule.mem_bot] at hp
      subst hp
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp only [map_zero, add_zero] at hlp ⊢
      exact hlp.symm)
  surj := 𝒞.coneK_surj_L (fun _ => ⊥) KL (fun _ => ⊥) SL SP hL.surj

theorem coneK_P_subAcyc (hP : SubAcyc P SP.eps KP)
    (haeps : ∀ x, SL.eps.hom ((a.f 0).hom x) = SA.eps.hom x)
    (hbeps : ∀ x, SP.eps.hom ((b.f 0).hom x) = SA.eps.hom x) :
    SubAcyc K (𝒞.eps SL SP) (𝒞.coneK (fun _ => ⊥) (fun _ => ⊥) KP) where
  toAcyc := coneK_acyc 𝒞 (fun _ => ⊥) (fun _ => ⊥) KP (Acyc_bot A SA.eps) (Acyc_bot L SL.eps) hP.toAcyc
    (fun m x hx => by
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]; exact Submodule.zero_mem _)
    (fun m x hx => by
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]; exact Submodule.zero_mem _)
    haeps hbeps (by
      intro l hl p _ hlp
      rw [Submodule.mem_bot] at hl
      subst hl
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp only [map_zero])
  surj := 𝒞.coneK_surj_P (fun _ => ⊥) (fun _ => ⊥) KP SL SP hP.surj

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
