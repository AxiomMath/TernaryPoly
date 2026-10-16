module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSpherical
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.CongruenceFactorization

@[expose] public section


/-!
# The finite part of a line-induced section at the identity cell (bad line)

For a vector `v` fixed only by the bad-line Levi level (`k ∈ GL₂(ℤ̂)` with `diag(1, k)` in the
finite level group `K₁`), the spherical construction of `FiniteSpherical` is not available.  Instead
we define the finite vector on the identity cell `P_line(𝔸_f) · K₁`: for `g = p k₁` it is
`χ_f(p) |p|^{a, b} · σ(block p) v`, and `0` off the cell.  It is well defined because
`P_line(𝔸_f) ∩ K₁` is integral (so the factor is `1`) and its `GL₂`-blocks lie in the bad-line Levi
level (so they fix `v`); it is left `P_line(𝔸_f)`-equivariant, right `K₁`-invariant and takes the
value `v` at the identity.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance
  (combineGL_mul atInfinity_mul atFinite_mul)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (lastRow_vecMul)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## The bad-line level subspace -/

section Level

variable (σ : CuspidalRepresentation)

/-- The vectors fixed by every `k ∈ GL₂(ℤ̂)` for which `diag(1, k)` lies in the finite level. -/
def badLevelSubspace : Submodule ℂ σ.H where
  carrier := {v | ∀ k : GeneralLinearGroup (Fin 2) IntegralAdeles,
    GeneralLinearGroup.map integralEmbedding (lineLevi 1 k) ∈ finiteLevel →
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) v = v}
  zero_mem' := by intro k _; simp
  add_mem' {v w} hv hw := by intro k hk; simp [map_add, hv k hk, hw k hk]
  smul_mem' c v hv := by intro k hk; simp [map_smul, hv k hk]

variable {σ}

theorem badLevelSubspace_real {v : σ.H} (hv : v ∈ badLevelSubspace σ) (h : BinaryRealGL) :
    σ.π (atInfinity h) v ∈ badLevelSubspace σ := by
  intro k hk
  rw [← Module.End.mul_apply, ← map_mul, atFinite_mul_atInfinity_comm, map_mul,
    Module.End.mul_apply, hv k hk]

end Level

/-! ## The intersection of the line parabolic with the level -/

theorem lineLevi_one_lineBlockGL_row {R : Type*} [CommRing R] {c : GeneralLinearGroup (Fin 3) R}
    (hc : c ∈ lineParabolic R) (j : Fin 3) :
    (lineLevi 1 (lineBlockGL c hc)).val 2 j = c.val 2 j := by
  have h20 : c.val 2 0 = 0 := hc.2
  rw [lineLevi_val]
  fin_cases j
  · simp [lineBlockGL, h20]
  · simp [lineBlockGL]
  · simp [lineBlockGL]

/-- An element of the line parabolic lying in the finite level is the image of an integral element
of the line parabolic whose `GL₂`-block lies in the bad-line Levi level. -/
theorem lineParabolic_level_decomp {r : FiniteGL} (hr : r ∈ lineParabolic FiniteAdeles)
    (hl : r ∈ finiteLevel) :
    ∃ (c : GeneralLinearGroup (Fin 3) IntegralAdeles) (hc : c ∈ lineParabolic IntegralAdeles),
      r = GeneralLinearGroup.map integralEmbedding c ∧
      GeneralLinearGroup.map integralEmbedding (lineLevi 1 (lineBlockGL c hc)) ∈ finiteLevel := by
  obtain ⟨c, hcl, hcr⟩ := Subgroup.mem_map.mp hl
  have hmap : GeneralLinearGroup.map integralEmbedding c ∈ lineParabolic FiniteAdeles := by
    rw [hcr]
    exact hr
  have hc : c ∈ lineParabolic IntegralAdeles := integral_mem_lineParabolic hmap
  refine ⟨c, hc, hcr.symm, ?_⟩
  have hrow : lastRow ᵥ* (GeneralLinearGroup.map integralReduction c).val = lastRow := hcl
  have key : lastRow ᵥ* (GeneralLinearGroup.map integralReduction
      (lineLevi 1 (lineBlockGL c hc))).val = lastRow := by
    rw [lastRow_vecMul] at hrow ⊢
    funext j
    have h := congrFun hrow j
    simp only [GeneralLinearGroup.map_apply] at h ⊢
    rw [lineLevi_one_lineBlockGL_row hc j]
    exact h
  exact Subgroup.mem_map.mpr ⟨lineLevi 1 (lineBlockGL c hc), key, rfl⟩

theorem finiteLineFactor_level (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1) {r : FiniteGL}
    (hr : r ∈ lineParabolic FiniteAdeles) (hl : r ∈ finiteLevel) :
    finiteLineFactor χ a b r hr = 1 := by
  obtain ⟨c, hc, hrc, _⟩ := lineParabolic_level_decomp hr hl
  subst hrc
  exact finiteLineFactor_integral χ a b hχ hc hr

theorem lineBlockGL_level_fixed {σ : CuspidalRepresentation} {v : σ.H}
    (hv : v ∈ badLevelSubspace σ) {r : FiniteGL} (hr : r ∈ lineParabolic FiniteAdeles)
    (hl : r ∈ finiteLevel) : σ.π (atFinite (lineBlockGL r hr)) v = v := by
  obtain ⟨c, hc, hrc, hmem⟩ := lineParabolic_level_decomp hr hl
  subst hrc
  rw [lineBlockGL_map integralEmbedding c hc hr]
  exact hv (lineBlockGL c hc) hmem

/-! ## The cell vector -/

/-- The identity cell `P_line(𝔸_f) · K₁`. -/
abbrev InBadCell (g : FiniteGL) : Prop :=
  ∃ p : FiniteGL, p ∈ lineParabolic FiniteAdeles ∧ ∃ k : FiniteGL, k ∈ finiteLevel ∧ g = p * k

section Cell

variable (σ : CuspidalRepresentation)

open Classical in
/-- The value `χ_f(p) |p| · σ(block p) v` at a line-parabolic element, and `0` elsewhere. -/
def badCellValue (χ : RankOneCharacter) (a b : ℂ) (v : σ.H) (p : FiniteGL) : σ.H :=
  if hp : p ∈ lineParabolic FiniteAdeles then
    finiteLineFactor χ a b p hp • σ.π (atFinite (lineBlockGL p hp)) v
  else 0

open Classical in
/-- **The finite part of a line-induced vector on the identity cell.** -/
def badLineVector (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v : σ.H) : σ.H :=
  if h : InBadCell g then badCellValue σ χ a b v (Classical.choose h) else 0

variable {σ}

theorem badCellValue_of_mem {χ : RankOneCharacter} {a b : ℂ} {v : σ.H} {p : FiniteGL}
    (hp : p ∈ lineParabolic FiniteAdeles) :
    badCellValue σ χ a b v p = finiteLineFactor χ a b p hp • σ.π (atFinite (lineBlockGL p hp)) v := by
  unfold badCellValue
  exact dite_eq_left hp

theorem badCellValue_of_not_mem {χ : RankOneCharacter} {a b : ℂ} {v : σ.H} {p : FiniteGL}
    (hp : p ∉ lineParabolic FiniteAdeles) : badCellValue σ χ a b v p = 0 := by
  unfold badCellValue
  exact dite_eq_right hp

theorem badLineVector_of_cell {χ : RankOneCharacter} {a b : ℂ} {v : σ.H} {g : FiniteGL}
    (h : InBadCell g) :
    badLineVector σ χ a b g v = badCellValue σ χ a b v (Classical.choose h) := by
  unfold badLineVector
  exact dite_eq_left h

theorem badLineVector_of_not_cell {χ : RankOneCharacter} {a b : ℂ} {v : σ.H} {g : FiniteGL}
    (h : ¬ InBadCell g) : badLineVector σ χ a b g v = 0 := by
  unfold badLineVector
  exact dite_eq_right h

theorem inBadCell_choose_mem {g : FiniteGL} (h : InBadCell g) :
    Classical.choose h ∈ lineParabolic FiniteAdeles :=
  (Classical.choose_spec h).1

theorem inBadCell_mul_left {g p : FiniteGL} (hp : p ∈ lineParabolic FiniteAdeles)
    (h : InBadCell g) : InBadCell (p * g) := by
  obtain ⟨q, hq, k, hk, hg⟩ := h
  exact ⟨p * q, (lineParabolic FiniteAdeles).mul_mem hp hq, k, hk, by rw [hg, mul_assoc]⟩

theorem inBadCell_of_mul_left {g p : FiniteGL} (hp : p ∈ lineParabolic FiniteAdeles)
    (h : InBadCell (p * g)) : InBadCell g := by
  obtain ⟨q, hq, k, hk, hpg⟩ := h
  exact ⟨p⁻¹ * q, (lineParabolic FiniteAdeles).mul_mem ((lineParabolic FiniteAdeles).inv_mem hp) hq,
    k, hk, by rw [mul_assoc, ← hpg, inv_mul_cancel_left]⟩

theorem inBadCell_mul_level {g k : FiniteGL} (hk : k ∈ finiteLevel) (h : InBadCell g) :
    InBadCell (g * k) := by
  obtain ⟨q, hq, k', hk', hg⟩ := h
  exact ⟨q, hq, k' * k, finiteLevel.mul_mem hk' hk, by rw [hg, mul_assoc]⟩

theorem inBadCell_of_mul_level {g k : FiniteGL} (hk : k ∈ finiteLevel)
    (h : InBadCell (g * k)) : InBadCell g := by
  obtain ⟨q, hq, k', hk', hgk⟩ := h
  exact ⟨q, hq, k' * k⁻¹, finiteLevel.mul_mem hk' (finiteLevel.inv_mem hk),
    by rw [← mul_assoc, ← hgk, mul_inv_cancel_right]⟩

/-! ### Independence of the decomposition -/

theorem badCellValue_mul_level (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ badLevelSubspace σ) {p r : FiniteGL}
    (hp : p ∈ lineParabolic FiniteAdeles) (hr : r ∈ lineParabolic FiniteAdeles)
    (hl : r ∈ finiteLevel) :
    badCellValue σ χ a b v (p * r) = badCellValue σ χ a b v p := by
  have hpr : p * r ∈ lineParabolic FiniteAdeles := (lineParabolic FiniteAdeles).mul_mem hp hr
  rw [badCellValue_of_mem hpr, badCellValue_of_mem hp, finiteLineFactor_mul χ a b hp hr,
    finiteLineFactor_level χ a b hχ hr hl, mul_one, lineBlockGL_mul hp hr, ← atFinite_mul,
    map_mul, Module.End.mul_apply, lineBlockGL_level_fixed hv hr hl]

/-- **Independence of the decomposition.** -/
theorem badLineVector_eq (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ badLevelSubspace σ) {g p k : FiniteGL}
    (hp : p ∈ lineParabolic FiniteAdeles) (hk : k ∈ finiteLevel) (hg : g = p * k) :
    badLineVector σ χ a b g v = badCellValue σ χ a b v p := by
  have hcell : InBadCell g := ⟨p, hp, k, hk, hg⟩
  have hq := (Classical.choose_spec hcell).1
  obtain ⟨k', hk', hgk'⟩ := (Classical.choose_spec hcell).2
  have hqeq : Classical.choose hcell = p * (k * k'⁻¹) := by
    have h : p * k = Classical.choose hcell * k' := hg.symm.trans hgk'
    calc Classical.choose hcell = Classical.choose hcell * k' * k'⁻¹ :=
          (mul_inv_cancel_right _ _).symm
      _ = p * k * k'⁻¹ := by rw [← h]
      _ = p * (k * k'⁻¹) := mul_assoc _ _ _
  have hr : k * k'⁻¹ ∈ finiteLevel := finiteLevel.mul_mem hk (finiteLevel.inv_mem hk')
  have hrP : k * k'⁻¹ ∈ lineParabolic FiniteAdeles := by
    have h : k * k'⁻¹ = p⁻¹ * Classical.choose hcell := by
      rw [hqeq, inv_mul_cancel_left]
    rw [h]
    exact (lineParabolic FiniteAdeles).mul_mem ((lineParabolic FiniteAdeles).inv_mem hp) hq
  rw [badLineVector_of_cell hcell, hqeq]
  exact badCellValue_mul_level χ a b hχ hv hp hrP hr

/-! ### Equivariance -/

/-- **Left equivariance.** -/
theorem badLineVector_mul (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ badLevelSubspace σ) {p : FiniteGL} (hp : p ∈ lineParabolic FiniteAdeles)
    (g : FiniteGL) :
    badLineVector σ χ a b (p * g) v =
      finiteLineFactor χ a b p hp • σ.π (atFinite (lineBlockGL p hp))
        (badLineVector σ χ a b g v) := by
  by_cases hcell : InBadCell g
  · obtain ⟨q, hq, k, hk, hg⟩ := hcell
    have hpq : p * q ∈ lineParabolic FiniteAdeles := (lineParabolic FiniteAdeles).mul_mem hp hq
    rw [badLineVector_eq χ a b hχ hv hpq hk (show p * g = p * q * k by rw [hg, mul_assoc]),
      badLineVector_eq χ a b hχ hv hq hk hg, badCellValue_of_mem hpq, badCellValue_of_mem hq,
      finiteLineFactor_mul χ a b hp hq, lineBlockGL_mul hp hq, ← atFinite_mul, map_mul,
      Module.End.mul_apply, map_smul, smul_smul]
  · have hnc : ¬ InBadCell (p * g) := fun h => hcell (inBadCell_of_mul_left hp h)
    rw [badLineVector_of_not_cell hcell, badLineVector_of_not_cell hnc, map_zero, smul_zero]

/-- **Right `K₁`-invariance.** -/
theorem badLineVector_mul_level (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ badLevelSubspace σ) (g : FiniteGL) (k : finiteLevel) :
    badLineVector σ χ a b (g * k.val) v = badLineVector σ χ a b g v := by
  by_cases hcell : InBadCell g
  · obtain ⟨q, hq, k', hk', hg⟩ := hcell
    rw [badLineVector_eq χ a b hχ hv hq (finiteLevel.mul_mem hk' k.property)
        (show g * k.val = q * (k' * k.val) by rw [hg, mul_assoc]),
      badLineVector_eq χ a b hχ hv hq hk' hg]
  · have hnc : ¬ InBadCell (g * k.val) := fun h => hcell (inBadCell_of_mul_level k.property h)
    rw [badLineVector_of_not_cell hcell, badLineVector_of_not_cell hnc]

/-- **The value at the identity.** -/
theorem badLineVector_one (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ badLevelSubspace σ) :
    badLineVector σ χ a b (1 : FiniteGL) v = v := by
  have h1 : (1 : FiniteGL) ∈ lineParabolic FiniteAdeles := (lineParabolic FiniteAdeles).one_mem
  rw [badLineVector_eq χ a b hχ hv h1 (one_mem finiteLevel) (one_mul (1 : FiniteGL)).symm,
    badCellValue_of_mem h1, finiteLineFactor_one, one_smul]
  have hblock : lineBlockGL (1 : FiniteGL) h1 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineBlockGL]
  rw [hblock, TernaryPeriodPolynomials.SphericalDetection.Helpers.atFinite_one, map_one,
    Module.End.one_apply]

/-! ### Linearity, real translations and smoothness -/

theorem badCellValue_real (χ : RankOneCharacter) (a b : ℂ) (p : FiniteGL) (v : σ.H)
    (h : BinaryRealGL) :
    badCellValue σ χ a b (σ.π (atInfinity h) v) p =
      σ.π (atInfinity h) (badCellValue σ χ a b v p) := by
  by_cases hp : p ∈ lineParabolic FiniteAdeles
  · rw [badCellValue_of_mem hp, badCellValue_of_mem hp, map_smul, ← Module.End.mul_apply,
      ← Module.End.mul_apply, ← map_mul, ← map_mul, atFinite_mul_atInfinity_comm]
  · rw [badCellValue_of_not_mem hp, badCellValue_of_not_mem hp, map_zero]

theorem badLineVector_real (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v : σ.H)
    (h : BinaryRealGL) :
    badLineVector σ χ a b g (σ.π (atInfinity h) v) =
      σ.π (atInfinity h) (badLineVector σ χ a b g v) := by
  by_cases hcell : InBadCell g
  · rw [badLineVector_of_cell hcell, badLineVector_of_cell hcell, badCellValue_real]
  · rw [badLineVector_of_not_cell hcell, badLineVector_of_not_cell hcell, map_zero]

theorem badCellValue_smul (χ : RankOneCharacter) (a b : ℂ) (p : FiniteGL) (c : ℂ) (v : σ.H) :
    badCellValue σ χ a b (c • v) p = c • badCellValue σ χ a b v p := by
  by_cases hp : p ∈ lineParabolic FiniteAdeles
  · rw [badCellValue_of_mem hp, badCellValue_of_mem hp, map_smul, smul_comm]
  · rw [badCellValue_of_not_mem hp, badCellValue_of_not_mem hp, smul_zero]

theorem badLineVector_smul (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (c : ℂ) (v : σ.H) :
    badLineVector σ χ a b g (c • v) = c • badLineVector σ χ a b g v := by
  by_cases hcell : InBadCell g
  · rw [badLineVector_of_cell hcell, badLineVector_of_cell hcell, badCellValue_smul]
  · rw [badLineVector_of_not_cell hcell, badLineVector_of_not_cell hcell, smul_zero]

theorem badCellValue_smooth (χ : RankOneCharacter) (a b : ℂ) (p : FiniteGL) {v : σ.H}
    (hv : v ∈ σ.smooth) : badCellValue σ χ a b v p ∈ σ.smooth := by
  by_cases hp : p ∈ lineParabolic FiniteAdeles
  · rw [badCellValue_of_mem hp]
    exact σ.smooth.smul_mem _ (σ.smooth_stable _ _ hv)
  · rw [badCellValue_of_not_mem hp]
    exact σ.smooth.zero_mem

theorem badLineVector_smooth (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) {v : σ.H}
    (hv : v ∈ σ.smooth) : badLineVector σ χ a b g v ∈ σ.smooth := by
  by_cases hcell : InBadCell g
  · rw [badLineVector_of_cell hcell]
    exact badCellValue_smooth χ a b _ hv
  · rw [badLineVector_of_not_cell hcell]
    exact σ.smooth.zero_mem

end Cell

end TernaryPeriodPolynomials.SourceConstruction
