module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Gamma2Generation
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section


/-!
# Cusps of `Γ₁(3)`: two orbits of rational lines, of widths one and three

`Γ₁(3) = Γ₂ ∩ SL₂(ℤ)` acts on the rational lines of `ℚ²`. A primitive column `(p,q)ᵗ` with
`3 ∣ q` can be signed and completed to a matrix of `Γ₁(3)` as its first column; if `3 ∤ q` it can be
completed as its second column. So there are exactly two orbits, those of the coordinate lines. The
translation generators of the stabilizers are `(1 1; 0 1)` (width one) and `(1 0; 3 1)` (width three).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

/-- `Γ₁(3) = Γ₂ ∩ SL₂(ℤ)`. -/
def Gamma1_3 : Subgroup GL2Z := Gamma2 ⊓ (Matrix.GeneralLinearGroup.det : GL2Z →* ℤˣ).ker

/-- The image of a subspace of `ℚ²` under an integral matrix. -/
def lineImage (g : GL2Z) (L : Submodule ℚ (Fin 2 → ℚ)) : Submodule ℚ (Fin 2 → ℚ) :=
  L.map (Matrix.toLin' (g.val.map (Int.castRingHom ℚ)))

/-- The coordinate lines `ℚ e₁` and `ℚ e₂`. -/
def lineE (i : Fin 2) : Submodule ℚ (Fin 2 → ℚ) := Submodule.span ℚ {Pi.single i 1}

/-- A rational line: the span of a nonzero vector. -/
def IsRatLine (L : Submodule ℚ (Fin 2 → ℚ)) : Prop := ∃ w : Fin 2 → ℚ, w ≠ 0 ∧ L = Submodule.span ℚ {w}

theorem mem_Gamma1_3 (g : GL2Z) :
    g ∈ Gamma1_3 ↔ g ∈ Gamma2 ∧ g.val.det = 1 := by
  unfold Gamma1_3
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := congrArg (fun u : ℤˣ => (u : ℤ)) h2
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h2

theorem lineImage_span (g : GL2Z) (w : Fin 2 → ℚ) :
    lineImage g (Submodule.span ℚ {w}) =
      Submodule.span ℚ {(g.val.map (Int.castRingHom ℚ)).mulVec w} := by
  unfold lineImage
  rw [Submodule.map_span, Set.image_singleton]
  rfl

/-- Primitive integral representative of a rational vector. -/
theorem primitive_rep (x y : ℚ) (h : x ≠ 0 ∨ y ≠ 0) :
    ∃ (p q : ℤ) (c : ℚ), IsCoprime p q ∧ c ≠ 0 ∧ x = c * p ∧ y = c * q := by
  set P : ℤ := x.num * y.den with hP
  set Q : ℤ := y.num * x.den with hQ
  have hD : ((x.den : ℚ) * y.den) ≠ 0 := by positivity
  have hx : x = P / ((x.den : ℚ) * y.den) := by
    rw [hP]; push_cast
    field_simp
    exact Rat.mul_den_eq_num x
  have hy : y = Q / ((x.den : ℚ) * y.den) := by
    rw [hQ]; push_cast
    field_simp
    exact Rat.mul_den_eq_num y
  have hPQ : 0 < Int.gcd P Q := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    rcases h with h | h
    · apply h; rw [hx, h0.1]; simp
    · apply h; rw [hy, h0.2]; simp
  obtain ⟨g, p, q, hg, hpq, hp, hq⟩ := Int.exists_gcd_one' hPQ
  have hP' : (P : ℚ) = p * g := by rw [hp]; push_cast; ring
  have hQ' : (Q : ℚ) = q * g := by rw [hq]; push_cast; ring
  refine ⟨p, q, (g : ℚ) / ((x.den : ℚ) * y.den), Int.isCoprime_iff_gcd_eq_one.mpr hpq,
    div_ne_zero (by exact_mod_cast hg.ne') hD, ?_, ?_⟩
  · exact hx.trans (by rw [hP']; ring)
  · exact hy.trans (by rw [hQ']; ring)


/-- An element of `GL₂(ℤ)` from a determinant-one matrix. -/
def mkSL (a b c d : ℤ) (h : a * d - b * c = 1) : GL2Z where
  val := !![a, b; c, d]
  inv := !![d, -b; -c, a]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

theorem mkSL_val (a b c d : ℤ) (h : a * d - b * c = 1) (i j : Fin 2) :
    (mkSL a b c d h).val i j = !![a, b; c, d] i j := rfl

theorem mem_Gamma1_3_of (a b c d : ℤ) (h : a * d - b * c = 1) (hc : c % 3 = 0) (hd : d % 3 = 1) :
    mkSL a b c d h ∈ Gamma1_3 := by
  rw [mem_Gamma1_3, mem_Gamma2]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [mkSL] using hc
  · simpa [mkSL] using hd
  · simp [mkSL, Matrix.det_fin_two, h]

/-- A primitive column with `3 ∣ q` is, up to sign, the first column of a matrix of `Γ₁(3)`. -/
theorem complete_first (p q : ℤ) (hc : IsCoprime p q) (h3 : 3 ∣ q) :
    ∃ g ∈ Gamma1_3, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ g.val 0 0 = ε * p ∧ g.val 1 0 = ε * q := by
  obtain ⟨u, v, huv⟩ := hc
  have hu : u % 3 = 1 ∨ u % 3 = 2 := by
    by_contra hcon
    have hu0 : u % 3 = 0 := by omega
    obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero hu0
    obtain ⟨t, ht⟩ := h3
    have : (3 : ℤ) ∣ 1 := ⟨a * p + v * t, by rw [← huv, ha, ht]; ring⟩
    omega
  rcases hu with hu | hu
  · refine ⟨mkSL p (-v) q u (by linarith),
      mem_Gamma1_3_of p (-v) q u (by linarith) (by omega) hu, 1, Or.inl rfl, by simp [mkSL],
      by simp [mkSL]⟩
  · refine ⟨mkSL (-p) v (-q) (-u) (by linarith),
      mem_Gamma1_3_of (-p) v (-q) (-u) (by linarith) (by omega) (by omega), -1, Or.inr rfl,
      by simp [mkSL], by simp [mkSL]⟩

/-- A primitive column with `3 ∤ q` is, up to sign, the second column of a matrix of `Γ₁(3)`. -/
theorem complete_second (p q : ℤ) (hc : IsCoprime p q) (h3 : ¬ 3 ∣ q) :
    ∃ g ∈ Gamma1_3, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ g.val 0 1 = ε * p ∧ g.val 1 1 = ε * q := by
  have hq : q % 3 = 1 ∨ q % 3 = 2 := by omega
  have key : ∀ p' q' : ℤ, IsCoprime p' q' → q' % 3 = 1 →
      ∃ g ∈ Gamma1_3, g.val 0 1 = p' ∧ g.val 1 1 = q' := by
    intro p' q' hc' hq'
    have h3' : IsCoprime q' 3 := ⟨1, -(q' / 3), by omega⟩
    have h4 : IsCoprime q' (3 * p') := h3'.mul_right hc'.symm
    obtain ⟨x, z, hxz⟩ := h4
    refine ⟨mkSL x p' (-3 * z) q' (by linear_combination hxz),
      mem_Gamma1_3_of x p' (-3 * z) q' (by linear_combination hxz) (by omega) hq',
      by simp [mkSL], by simp [mkSL]⟩
  rcases hq with hq | hq
  · obtain ⟨g, hg, h1, h2⟩ := key p q hc hq
    exact ⟨g, hg, 1, Or.inl rfl, by simpa using h1, by simpa using h2⟩
  · obtain ⟨g, hg, h1, h2⟩ := key (-p) (-q) hc.neg_neg (by omega)
    exact ⟨g, hg, -1, Or.inr rfl, by simpa using h1, by simpa using h2⟩


theorem lineImage_lineE (g : GL2Z) (i : Fin 2) :
    lineImage g (lineE i) = Submodule.span ℚ {fun r => (g.val r i : ℚ)} := by
  unfold lineE
  rw [lineImage_span]
  congr 2
  funext r
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem span_col_eq (g : GL2Z) (i : Fin 2) (p q ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h0 : g.val 0 i = ε * p) (h1 : g.val 1 i = ε * q) :
    Submodule.span ℚ {fun r => (g.val r i : ℚ)} = Submodule.span ℚ {![(p : ℚ), q]} := by
  rw [Submodule.span_singleton_eq_span_singleton]
  refine ⟨Units.mk0 (ε : ℚ) (by rcases hε with rfl | rfl <;> norm_num), ?_⟩
  funext r
  fin_cases r
  · simp [h0]
    rcases hε with rfl | rfl <;> simp
  · simp [h1]
    rcases hε with rfl | rfl <;> simp

/-- **Two cusp orbits.** Every rational line is in the `Γ₁(3)`-orbit of `ℚ e₁` or of `ℚ e₂`. -/
theorem cusp_orbits_exhaustive (L : Submodule ℚ (Fin 2 → ℚ)) (hL : IsRatLine L) :
    (∃ g ∈ Gamma1_3, lineImage g (lineE 0) = L) ∨ (∃ g ∈ Gamma1_3, lineImage g (lineE 1) = L) := by
  obtain ⟨w, hw, rfl⟩ := hL
  have hne : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  obtain ⟨p, q, c, hc, hc0, h0, h1⟩ := primitive_rep (w 0) (w 1) hne
  have hwc : w = c • ![(p : ℚ), q] := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have hspan : Submodule.span ℚ {w} = Submodule.span ℚ {![(p : ℚ), q]} := by
    rw [hwc]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0) _
  rw [hspan]
  by_cases h3 : 3 ∣ q
  · left
    obtain ⟨g, hg, ε, hε, h00, h10⟩ := complete_first p q hc h3
    exact ⟨g, hg, by rw [lineImage_lineE]; exact span_col_eq g 0 p q ε hε h00 h10⟩
  · right
    obtain ⟨g, hg, ε, hε, h01, h11⟩ := complete_second p q hc h3
    exact ⟨g, hg, by rw [lineImage_lineE]; exact span_col_eq g 1 p q ε hε h01 h11⟩

theorem mem_lineE_zero (v : Fin 2 → ℚ) (h : v ∈ lineE 0) : v 1 = 0 := by
  unfold lineE at h
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
  simp

theorem mem_lineE_one (v : Fin 2 → ℚ) (h : v ∈ lineE 1) : v 0 = 0 := by
  unfold lineE at h
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
  simp

theorem col_mem (g : GL2Z) (i : Fin 2) : (fun r => (g.val r i : ℚ)) ∈ lineImage g (lineE i) := by
  rw [lineImage_lineE]
  exact Submodule.mem_span_singleton_self _

/-- The two orbits are different: no element of `Γ₂` takes `ℚ e₁` to `ℚ e₂`. -/
theorem cusp_orbits_distinct : ¬ ∃ g ∈ Gamma2, lineImage g (lineE 0) = lineE 1 := by
  rintro ⟨g, hg, h⟩
  have hm := col_mem g 0
  rw [h] at hm
  have h00 : g.val 0 0 = 0 := by exact_mod_cast mem_lineE_one _ hm
  obtain ⟨hc3, -⟩ := (mem_Gamma2 g).mp hg
  have hdet := det_cases g
  rw [h00] at hdet
  have hu : IsUnit (g.val 1 0) := by
    rcases hdet with hd | hd
    · exact isUnit_iff_exists_inv.mpr ⟨-g.val 0 1, by linarith [mul_comm (g.val 0 1) (g.val 1 0)]⟩
    · exact isUnit_iff_exists_inv.mpr ⟨g.val 0 1, by linarith [mul_comm (g.val 0 1) (g.val 1 0)]⟩
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega

/-- Stabilizer of `ℚ e₁` among unipotent determinant-one matrices: the translations. -/
theorem stab_e1 (g : GL2Z) (hdet : g.val.det = 1) (htr : g.val 0 0 + g.val 1 1 = 2)
    (hfix : lineImage g (lineE 0) = lineE 0) : ∃ k : ℤ, g = tk k := by
  have hm := col_mem g 0
  rw [hfix] at hm
  have h10 : g.val 1 0 = 0 := by exact_mod_cast mem_lineE_zero _ hm
  rw [Matrix.det_fin_two, h10] at hdet
  have ha : g.val 0 0 = 1 := by nlinarith
  have hd : g.val 1 1 = 1 := by omega
  refine ⟨g.val 0 1, Units.ext ?_⟩
  rw [Matrix.eta_fin_two g.val, ha, h10, hd]
  simp [tk]

/-- Stabilizer of `ℚ e₂` among unipotent determinant-one matrices: the lower unipotents. -/
theorem stab_e2 (g : GL2Z) (hdet : g.val.det = 1) (htr : g.val 0 0 + g.val 1 1 = 2)
    (hfix : lineImage g (lineE 1) = lineE 1) : ∃ k : ℤ, g.val = !![1, 0; k, 1] := by
  have hm := col_mem g 1
  rw [hfix] at hm
  have h01 : g.val 0 1 = 0 := by exact_mod_cast mem_lineE_one _ hm
  rw [Matrix.det_fin_two, h01] at hdet
  have ha : g.val 0 0 = 1 := by nlinarith
  have hd : g.val 1 1 = 1 := by omega
  refine ⟨g.val 1 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, h01, hd]

theorem tk_fix_e1 (k : ℤ) : lineImage (tk k) (lineE 0) = lineE 0 := by
  rw [lineImage_lineE]
  unfold lineE
  congr 2
  funext r
  fin_cases r <;> simp [tk]

theorem uk_fix_e2 (m : ℤ) : lineImage (uk m) (lineE 1) = lineE 1 := by
  rw [lineImage_lineE]
  unfold lineE
  congr 2
  funext r
  fin_cases r <;> simp [uk]

/-- The lower unipotent `(1 0; k 1)` lies in `Γ₁(3)` exactly when `3 ∣ k`. -/
theorem lower_mem_Gamma1_3_iff (k : ℤ) :
    (mkSL 1 0 k 1 (by ring)) ∈ Gamma1_3 ↔ 3 ∣ k := by
  rw [mem_Gamma1_3, mem_Gamma2]
  simp only [mkSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩
    omega
  · intro h
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simp [Matrix.det_fin_two]


theorem tk_mem_Gamma1_3 (k : ℤ) : tk k ∈ Gamma1_3 := by
  rw [mem_Gamma1_3]
  exact ⟨tk_mem_Gamma2 k, by simp [tk, Matrix.det_fin_two]⟩

theorem uk_mem_Gamma1_3 (m : ℤ) : uk m ∈ Gamma1_3 := by
  rw [mem_Gamma1_3]
  exact ⟨uk_mem_Gamma2 m, by simp [uk, Matrix.det_fin_two]⟩

theorem stab_e2_Gamma1_3 (g : GL2Z) (hg : g ∈ Gamma1_3) (htr : g.val 0 0 + g.val 1 1 = 2)
    (hfix : lineImage g (lineE 1) = lineE 1) : ∃ m : ℤ, g = uk m := by
  rw [mem_Gamma1_3] at hg
  obtain ⟨k, hk⟩ := stab_e2 g hg.2 htr hfix
  obtain ⟨hc3, -⟩ := (mem_Gamma2 g).mp hg.1
  have hk10 : g.val 1 0 = k := by rw [hk]; rfl
  obtain ⟨m, hm⟩ : 3 ∣ k := by omega
  refine ⟨m, Units.ext ?_⟩
  rw [hk, hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uk]

end TernaryPeriodPolynomials.Argument.FiberModel
