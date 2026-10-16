module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.RationalCosets
public import Mathlib.Algebra.BigOperators.Finprod

@[expose] public section


/-!
# Counting right cosets by parabolic Levi classes

An abstract parabolic `N ⋊ M` inside a group `G` with an arithmetic subgroup `Γ`, radical
coordinates `U : ℚ² → N` and conjugation action `φ`. For a finite set `R` of right
`Γ`-coset representatives of a right `Γ`-invariant set `D`, the number of representatives whose
Levi class is that of `m` equals the number of classes modulo the lattice `φ(m)⁻¹ ℤ²` of the
radical coordinates `u` with `U u · m ∈ D`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {G : Type*} [Group G] {M : Type*} [Group M]

/-- Parabolic coordinates relative to an arithmetic subgroup `Γ`. -/
structure ParabolicData (Γ : Subgroup G) (M : Type*) [Group M] where
  U : ℚ × ℚ → G
  L : M →* G
  φ : M → (ℚ × ℚ) →+ (ℚ × ℚ)
  ΓM : Subgroup M
  U_add : ∀ a b, U (a + b) = U a * U b
  U_inj : Function.Injective U
  conj : ∀ m u, (L m)⁻¹ * U u * L m = U (φ m u)
  mem : ∀ u m, U u * L m ∈ Γ ↔ u ∈ zLat ∧ m ∈ ΓM

/-- A finite set of right coset representatives. -/
structure RepSet (Γ : Subgroup G) (R : Finset G) (D : Set G) : Prop where
  sub : ∀ r ∈ R, r ∈ D
  disj : ∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ Γ → r = r'
  cover : ∀ x ∈ D, ∃ r ∈ R, r⁻¹ * x ∈ Γ
  right : ∀ x ∈ D, ∀ γ ∈ Γ, x * γ ∈ D

namespace ParabolicData

variable {Γ : Subgroup G} (P : ParabolicData Γ M)

theorem U_zero : P.U 0 = 1 := by
  have h := P.U_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem U_sub (a b : ℚ × ℚ) : (P.U a)⁻¹ * P.U b = P.U (b - a) := by
  rw [inv_mul_eq_iff_eq_mul, ← P.U_add, add_sub_cancel]

theorem quot (a b : ℚ × ℚ) (m m' : M) :
    (P.U a * P.L m)⁻¹ * (P.U b * P.L m') = P.U (P.φ m (b - a)) * P.L (m⁻¹ * m') := by
  rw [← P.conj, ← P.U_sub, map_mul, map_inv]
  group

theorem L_mem {m : M} (hm : m ∈ P.ΓM) : P.L m ∈ Γ := by
  have := (P.mem 0 m).mpr ⟨zero_mem _, hm⟩
  rwa [P.U_zero, one_mul] at this

theorem U_mem {u : ℚ × ℚ} (hu : u ∈ zLat) : P.U u ∈ Γ := by
  have := (P.mem u 1).mpr ⟨hu, one_mem _⟩
  rwa [map_one, mul_one] at this

/-- The lattice of radical coordinates fixed by conjugation by `m`. -/
def latt (m : M) : AddSubgroup (ℚ × ℚ) := zLat.comap (P.φ m)

theorem mem_latt (m : M) (u : ℚ × ℚ) : u ∈ P.latt m ↔ (P.L m)⁻¹ * P.U u * P.L m ∈ Γ := by
  rw [P.conj, latt, AddSubgroup.mem_comap]
  constructor
  · exact fun h => P.U_mem h
  · intro h
    have := (P.mem (P.φ m u) 1).mp (by rwa [map_one, mul_one])
    exact this.1

theorem latt_mul (m : M) {k : M} (hk : k ∈ P.ΓM) : P.latt (m * k) = P.latt m := by
  ext u
  rw [mem_latt, mem_latt, map_mul]
  have hL := P.L_mem hk
  constructor
  · intro h
    have := Γ.mul_mem (Γ.mul_mem hL h) (Γ.inv_mem hL)
    convert this using 1
    group
  · intro h
    have := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hL) h) hL
    convert this using 1
    group

/-- Radical coordinates `u` with `U u · m ∈ D`. -/
def S (D : Set G) (m : M) : Set (ℚ × ℚ) := {u | P.U u * P.L m ∈ D}

/-- **Fibre count.** -/
theorem fiber_card {R : Finset G} {D : Set G} (hR : RepSet Γ R D) (ΓM₀ : Subgroup M)
    [DecidableEq (M ⧸ ΓM₀)]
    (h0 : ΓM₀ ≤ P.ΓM) (pos : M → Prop)
    (hpos : ∀ m m', pos m → pos m' → m⁻¹ * m' ∈ P.ΓM → m⁻¹ * m' ∈ ΓM₀)
    (vR : G → ℚ × ℚ) (mR : G → M)
    (hdec : ∀ r ∈ R, pos (mR r) ∧ r⁻¹ * (P.U (vR r) * P.L (mR r)) ∈ Γ)
    (m : M) (hm : pos m) :
    (R.filter (fun r => (QuotientGroup.mk (mR r) : M ⧸ ΓM₀) = QuotientGroup.mk m)).card =
      ((QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ P.latt m) '' P.S D m).ncard := by
  set F := R.filter (fun r => (QuotientGroup.mk (mR r) : M ⧸ ΓM₀) = QuotientGroup.mk m)
  set f : G → (ℚ × ℚ) ⧸ P.latt m := fun r => QuotientAddGroup.mk (vR r)
  -- members of the fibre
  have hF : ∀ r ∈ F, r ∈ R ∧ m⁻¹ * mR r ∈ ΓM₀ := by
    intro r hr
    rw [Finset.mem_filter] at hr
    refine ⟨hr.1, ?_⟩
    have := QuotientGroup.eq.mp hr.2
    have := ΓM₀.inv_mem this
    simpa using this
  have hlatt : ∀ r ∈ F, P.latt (mR r) = P.latt m := by
    intro r hr
    have hk := h0 (hF r hr).2
    have : mR r = m * (m⁻¹ * mR r) := by group
    rw [this, P.latt_mul m hk]
  have himage : f '' (F : Set G) = QuotientAddGroup.mk '' P.S D m := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' := hF r hr
      refine ⟨vR r, ?_, rfl⟩
      have ha := (hdec r hr'.1).2
      have hk := P.L_mem (h0 hr'.2)
      have : P.U (vR r) * P.L m =
          r * ((r⁻¹ * (P.U (vR r) * P.L (mR r))) * (P.L (m⁻¹ * mR r))⁻¹) := by
        rw [map_mul, map_inv]; group
      change P.U (vR r) * P.L m ∈ D
      rw [this]
      exact hR.right _ (hR.sub r hr'.1) _ (Γ.mul_mem ha (Γ.inv_mem hk))
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨r, hr, hrx⟩ := hR.cover _ hu
      have ha := (hdec r hr).2
      have hq : (P.U (vR r) * P.L (mR r))⁻¹ * (P.U u * P.L m) ∈ Γ := by
        have := Γ.mul_mem (Γ.inv_mem ha) hrx
        convert this using 1
        group
      rw [P.quot] at hq
      obtain ⟨hz, hM⟩ := (P.mem _ _).mp hq
      have h0' := hpos _ _ (hdec r hr).1 hm hM
      have hrF : r ∈ F := by
        rw [Finset.mem_filter]
        exact ⟨hr, QuotientGroup.eq.mpr h0'⟩
      refine ⟨r, hrF, ?_⟩
      change (QuotientAddGroup.mk (vR r) : (ℚ × ℚ) ⧸ P.latt m) = QuotientAddGroup.mk u
      rw [QuotientAddGroup.eq, ← hlatt r hrF, latt, AddSubgroup.mem_comap]
      rwa [neg_add_eq_sub]
  have hinj : Set.InjOn f (F : Set G) := by
    intro r hr r' hr' hrr'
    have hr1 := hF r hr
    have hr1' := hF r' hr'
    have hΔ : vR r' - vR r ∈ P.latt (mR r) := by
      rw [hlatt r hr]
      have := QuotientAddGroup.eq.mp hrr'
      rwa [neg_add_eq_sub] at this
    rw [latt, AddSubgroup.mem_comap] at hΔ
    have hk : (mR r)⁻¹ * mR r' ∈ P.ΓM := by
      have := ΓM₀.mul_mem (ΓM₀.inv_mem hr1.2) hr1'.2
      apply h0
      convert this using 1
      group
    have hmid := (P.mem _ _).mpr ⟨hΔ, hk⟩
    rw [← P.quot] at hmid
    have ha := (hdec r hr1.1).2
    have ha' := (hdec r' hr1'.1).2
    apply hR.disj r hr1.1 r' hr1'.1
    have := Γ.mul_mem (Γ.mul_mem ha hmid) (Γ.inv_mem ha')
    convert this using 1
    group
  rw [← Set.ncard_coe_finset, ← himage, hinj.ncard_image]

/-! ### Invariance of the radical sets -/

theorem S_mul_right {D : Set G} (hDr : ∀ x ∈ D, ∀ γ ∈ Γ, x * γ ∈ D) (m : M) {k : M}
    (hk : k ∈ P.ΓM) : P.S D (m * k) = P.S D m := by
  ext u
  have hL := P.L_mem hk
  change P.U u * P.L (m * k) ∈ D ↔ P.U u * P.L m ∈ D
  rw [map_mul, ← mul_assoc]
  constructor
  · intro h
    have := hDr _ h _ (Γ.inv_mem hL)
    rwa [mul_inv_cancel_right] at this
  · intro h
    exact hDr _ h _ hL

theorem U_mem_iff (x : ℚ × ℚ) : P.U x ∈ Γ ↔ x ∈ zLat := by
  have := P.mem x 1
  rw [map_one, mul_one] at this
  rw [this]
  exact ⟨fun h => h.1, fun h => ⟨h, one_mem _⟩⟩

theorem φ_zLat {k : M} (hk : k ∈ P.ΓM) (u : ℚ × ℚ) : P.φ k u ∈ zLat ↔ u ∈ zLat := by
  have hL := P.L_mem hk
  rw [← P.U_mem_iff, ← P.conj, ← P.U_mem_iff]
  constructor
  · intro h
    have := Γ.mul_mem (Γ.mul_mem hL h) (Γ.inv_mem hL)
    convert this using 1
    group
  · intro h
    exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hL) h) hL

theorem φ_inv_apply (k : M) (u : ℚ × ℚ) : P.φ k⁻¹ (P.φ k u) = u := by
  apply P.U_inj
  rw [← P.conj, ← P.conj, map_inv, inv_inv]
  group

theorem φ_apply_inv (k : M) (u : ℚ × ℚ) : P.φ k (P.φ k⁻¹ u) = u := by
  have := P.φ_inv_apply k⁻¹ u
  rwa [inv_inv] at this

/-- The additive automorphism `φ k`. -/
def φe (k : M) : (ℚ × ℚ) ≃+ (ℚ × ℚ) where
  toFun := P.φ k
  invFun := P.φ k⁻¹
  left_inv := P.φ_inv_apply k
  right_inv := P.φ_apply_inv k
  map_add' := (P.φ k).map_add

theorem S_mul_left {D : Set G} (hDl : ∀ γ ∈ Γ, ∀ x ∈ D, γ * x ∈ D) (m : M) {k : M}
    (hk : k ∈ P.ΓM) (u : ℚ × ℚ) : u ∈ P.S D (k * m) ↔ P.φ k u ∈ P.S D m := by
  have hL := P.L_mem hk
  have heq : P.U u * P.L (k * m) = P.L k * (P.U (P.φ k u) * P.L m) := by
    rw [← P.conj, map_mul]; group
  change P.U u * P.L (k * m) ∈ D ↔ P.U (P.φ k u) * P.L m ∈ D
  rw [heq]
  constructor
  · intro h
    have := hDl _ (Γ.inv_mem hL) _ h
    rwa [inv_mul_cancel_left] at this
  · intro h
    exact hDl _ hL _ h

/-- Classes of radical coordinates modulo `ℤ²`. -/
def NL (D : Set G) (m : M) : ℕ :=
  ((QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ zLat) '' P.S D m).ncard

theorem NL_mul_right {D : Set G} (hDr : ∀ x ∈ D, ∀ γ ∈ Γ, x * γ ∈ D) (m : M) {k : M}
    (hk : k ∈ P.ΓM) : P.NL D (m * k) = P.NL D m := by
  rw [NL, NL, P.S_mul_right hDr m hk]

theorem NL_mul_left {D : Set G} (hDl : ∀ γ ∈ Γ, ∀ x ∈ D, γ * x ∈ D) (m : M) {k : M}
    (hk : k ∈ P.ΓM) : P.NL D (k * m) = P.NL D m := by
  have hmap : zLat.map (P.φe k).toAddMonoidHom = zLat := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (P.φ_zLat hk w).mpr hw
    · intro hu
      refine ⟨P.φ k⁻¹ u, ?_, P.φ_apply_inv k u⟩
      exact (P.φ_zLat hk _).mp (by rwa [P.φ_apply_inv])
  let e := QuotientAddGroup.congr zLat zLat (P.φe k) hmap
  have himg : (QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ zLat) '' P.S D m =
      e '' ((QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ zLat) '' P.S D (k * m)) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨QuotientAddGroup.mk (P.φ k⁻¹ u), ⟨P.φ k⁻¹ u, ?_, rfl⟩, ?_⟩
      · rw [P.S_mul_left hDl m hk, P.φ_apply_inv]; exact hu
      · change QuotientAddGroup.mk (P.φ k (P.φ k⁻¹ u)) = _
        rw [P.φ_apply_inv]
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨P.φ k u, (P.S_mul_left hDl m hk u).mp hu, rfl⟩
  rw [NL, NL, himg, Set.ncard_image_of_injective _ e.injective]

/-- Saturation of the radical sets. -/
theorem S_add_zLat {D : Set G} (hDl : ∀ γ ∈ Γ, ∀ x ∈ D, γ * x ∈ D) (m : M) :
    ∀ u ∈ P.S D m, ∀ l ∈ zLat, u + l ∈ P.S D m := by
  intro u hu l hl
  change P.U (u + l) * P.L m ∈ D
  rw [add_comm, P.U_add, mul_assoc]
  exact hDl _ (P.U_mem hl) _ hu

theorem S_add_latt {D : Set G} (hDr : ∀ x ∈ D, ∀ γ ∈ Γ, x * γ ∈ D) (m : M) :
    ∀ u ∈ P.S D m, ∀ l ∈ P.latt m, u + l ∈ P.S D m := by
  intro u hu l hl
  change P.U (u + l) * P.L m ∈ D
  have : P.U (u + l) * P.L m = (P.U u * P.L m) * ((P.L m)⁻¹ * P.U l * P.L m) := by
    rw [P.U_add]; group
  rw [this]
  exact hDr _ hu _ ((P.mem_latt m l).mp hl)

end ParabolicData

/-- **Sum by classes.** -/
theorem sum_by_class {ι Q : Type*} [DecidableEq Q] (R : Finset ι) (cls : ι → Q) (F : ι → ℂ)
    (Φ : Q → ℂ)
    (hF : ∀ r ∈ R, F r = Φ (cls r)) :
    ∑ r ∈ R, F r = ∑ᶠ c, ((R.filter (fun r => cls r = c)).card : ℂ) * Φ c := by
  rw [finsum_eq_sum_of_support_subset _ (s := R.image cls)]
  · rw [← Finset.sum_fiberwise_of_maps_to (g := cls) (t := R.image cls)
      (fun r hr => Finset.mem_image_of_mem cls hr)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_congr rfl (fun r hr => by rw [hF r (Finset.mem_filter.mp hr).1,
      (Finset.mem_filter.mp hr).2]), Finset.sum_const, nsmul_eq_mul]
  · intro c hc
    rw [Function.mem_support] at hc
    have hne : (R.filter (fun r => cls r = c)).card ≠ 0 := by
      intro h0; apply hc; rw [h0, Nat.cast_zero, zero_mul]
    obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp hne
    rw [Finset.mem_filter] at hr
    rw [Finset.coe_image]
    exact ⟨r, hr.1, hr.2⟩

end TernaryPeriodPolynomials.HeckeEigen.Satake
