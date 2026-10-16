module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Parabolic.LevelThreeCusps
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne

@[expose] public section


/-!
# Cusps of `GL₂(ℤ)`

The stabilizer of the cusp `∞` in `GL₂(ℤ)` consists of the matrices `f · T^k` with `f` in the Klein
group `{1, -1, ε, -ε}` (`T = [[1,1],[0,1]]`, `ε = diag(-1, 1)`), and every rational cusp is
`GL₂(ℤ)`-equivalent to `∞`. Hence a crossed cocycle of `GL₂(ℤ)` trivial at `T` is trivial on the
stabilizer of every rational cusp (`vanishes_every_cusp_GL`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (epsGL epsGL_mul_self GL2Z)
open TernaryPeriodPolynomials.Spectral.ModularH1 (Modular)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic

/-- The translation `T = [[1, 1], [0, 1]]` in `GL₂(ℤ)`. -/
def Tgl : GL2Z := SpecialLinearGroup.toGL ModularGroup.T

/-- The scalar `-1` of `GL₂(ℤ)`. -/
def mGL : GL2Z := ⟨!![-1, 0; 0, -1], !![-1, 0; 0, -1], by decide, by decide⟩

theorem Tgl_val : Tgl.val = !![1, 1; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem Tgl_zpow_val (k : ℤ) : (Tgl ^ k).val = !![1, k; 0, 1] := by
  induction k using Int.induction_on with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [_root_.zpow_add_one, Units.val_mul, ih, Tgl_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring
  | pred k ih =>
    have h : Tgl ^ (-(k : ℤ) - 1) = Tgl ^ (-(k : ℤ)) * Tgl⁻¹ := _root_.zpow_sub_one _ _
    have hinv : (Tgl⁻¹).val = !![1, -1; 0, 1] := by
      have : Tgl * (⟨!![1, -1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩ : GL2Z) = 1 := by
        apply Units.ext
        rw [Units.val_mul, Tgl_val]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [inv_eq_of_mul_eq_one_right this]
    rw [h, Units.val_mul, ih, hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

theorem mGL_mul_self : mGL * mGL = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem mGL_mul_eps : mGL * epsGL = epsGL * mGL := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mGL, epsGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem mGL_mul_T : mGL * Tgl = Tgl * mGL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Tgl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem eps_mul_T : epsGL * Tgl = Tgl⁻¹ * epsGL := by
  have hinv : Tgl⁻¹ = (⟨!![1, -1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩ : GL2Z) := by
    apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, Tgl_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hinv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Tgl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsGL, Matrix.mul_apply, Fin.sum_univ_two]

/-- The stabilizer in `GL₂(ℤ)` of the cusp of the frame `A`. -/
def cuspStab (A : GeneralLinearGroup (Fin 2) ℚ) : Subgroup GL2Z :=
  borelQ.comap ((MulAut.conj A⁻¹).toMonoidHom.comp (GeneralLinearGroup.map (Int.castRingHom ℚ)))

theorem mem_cuspStab_iff (A : GeneralLinearGroup (Fin 2) ℚ) (l : GL2Z) :
    l ∈ cuspStab A ↔ (A⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) l * A).val 1 0 = 0 := by
  change (MulAut.conj A⁻¹ (GeneralLinearGroup.map (Int.castRingHom ℚ) l)).val 1 0 = 0 ↔ _
  rw [MulAut.conj_apply, inv_inv]

theorem cuspStab_one_iff (l : GL2Z) : l ∈ cuspStab 1 ↔ l.val 1 0 = 0 := by
  rw [mem_cuspStab_iff]
  simp

theorem cuspStab_one_form (l : GL2Z) (h : l ∈ cuspStab 1) :
    ∃ k : ℤ, l = Tgl ^ k ∨ l = mGL * Tgl ^ k ∨ l = epsGL * Tgl ^ k ∨ l = mGL * epsGL * Tgl ^ k := by
  rw [cuspStab_one_iff] at h
  have hdet : l.val 0 0 * l.val 1 1 = 1 ∨ l.val 0 0 * l.val 1 1 = -1 := by
    have := Int.isUnit_iff.mp (Units.isUnit (Matrix.GeneralLinearGroup.det l))
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h] at this
    simpa using this
  have hu : IsUnit (l.val 0 0 * l.val 1 1) := by
    rcases hdet with h' | h'
    · rw [h']; exact isUnit_one
    · rw [h']; exact isUnit_one.neg
  rw [IsUnit.mul_iff] at hu
  have ha := Int.isUnit_iff.mp hu.1
  have hd := Int.isUnit_iff.mp hu.2
  rcases ha with ha | ha <;> rcases hd with hd | hd
  · refine ⟨l.val 0 1, Or.inl ?_⟩
    apply Units.ext
    rw [Tgl_zpow_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h, ha, hd]
  · refine ⟨l.val 0 1, Or.inr (Or.inr (Or.inr ?_))⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Tgl_zpow_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mGL, epsGL, Matrix.mul_apply, Fin.sum_univ_two, h, ha, hd]
  · refine ⟨-(l.val 0 1), Or.inr (Or.inr (Or.inl ?_))⟩
    apply Units.ext
    rw [Units.val_mul, Tgl_zpow_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [epsGL, Matrix.mul_apply, Fin.sum_univ_two, h, ha, hd]
  · refine ⟨-(l.val 0 1), Or.inr (Or.inl ?_)⟩
    apply Units.ext
    rw [Units.val_mul, Tgl_zpow_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mGL, Matrix.mul_apply, Fin.sum_univ_two, h, ha, hd]

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ GL2Z V)

/-- A crossed cocycle of `GL₂(ℤ)` trivial at `T` is trivial on the stabilizer of `∞`. -/
theorem vanishes_cusp_one_GL (x : crossedCocycles ρ)
    (hT : ∃ u, x.val Tgl = ρ Tgl u - u) : ∃ w, ∀ l ∈ cuspStab 1, x.val l = ρ l w - w := by
  obtain ⟨u, hu⟩ := hT
  obtain ⟨w, hw⟩ := klein_cusp_trivial ρ x Tgl mGL epsGL mGL_mul_self epsGL_mul_self mGL_mul_eps
    mGL_mul_T eps_mul_T u hu
  refine ⟨w, fun l hl => ?_⟩
  obtain ⟨k, hk | hk | hk | hk⟩ := cuspStab_one_form l hl
  · rw [hk]; exact (hw k).1
  · rw [hk]; exact (hw k).2.1
  · rw [hk]; exact (hw k).2.2.1
  · rw [hk]; exact (hw k).2.2.2

theorem conj_cuspStab (A f : GeneralLinearGroup (Fin 2) ℚ) (h : GL2Z)
    (hb : f⁻¹ * (GeneralLinearGroup.map (Int.castRingHom ℚ) h)⁻¹ * A ∈ borelQ) :
    ∀ l ∈ cuspStab A, h⁻¹ * l * h ∈ cuspStab f := by
  intro l hl
  rw [mem_cuspStab_iff] at hl ⊢
  set H := GeneralLinearGroup.map (Int.castRingHom ℚ) h with hH
  set b := f⁻¹ * H⁻¹ * A with hbdef
  have hl' : A⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) l * A ∈ borelQ := hl
  have e : A⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) l * A =
      b⁻¹ * (f⁻¹ * (H⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) l * H) * f) * b := by
    simp only [hbdef]; group
  rw [e] at hl'
  have h2 : f⁻¹ * (H⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) l * H) * f ∈ borelQ := by
    have := borelQ.mul_mem (borelQ.mul_mem hb hl') (borelQ.inv_mem hb)
    simpa [mul_assoc] using this
  have e2 : GeneralLinearGroup.map (Int.castRingHom ℚ) (h⁻¹ * l * h) =
      H⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) l * H := by
    simp [hH]
  rw [e2]
  exact h2

/-- The element of `GL₂(ℤ)` with a given determinant-one integral matrix. -/
def glOfEntries (a b c d : ℤ) (hdet : a * d - b * c = 1) : GL2Z :=
  SpecialLinearGroup.toGL
    (⟨!![a, b; c, d], by simpa [Matrix.det_fin_two] using hdet⟩ : SpecialLinearGroup (Fin 2) ℤ)

theorem map_glOfEntries_inv (a b c d : ℤ) (hdet) (i j : Fin 2) :
    ((GeneralLinearGroup.map (Int.castRingHom ℚ) (glOfEntries a b c d hdet))⁻¹).val i j =
      !![(d : ℚ), -(b : ℚ); -(c : ℚ), (a : ℚ)] i j := by
  set g : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two] using hdet⟩ with hg
  rw [← map_inv]
  have this : (glOfEntries a b c d hdet)⁻¹ = SpecialLinearGroup.toGL g⁻¹ := by
    change (SpecialLinearGroup.toGL g)⁻¹ = _
    rw [map_inv]
  rw [this]
  have e : ((SpecialLinearGroup.toGL g⁻¹ : GeneralLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![d, -b; -c, a] := by
    rw [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.SL2_inv_expl]
    rfl
  change (Int.castRingHom ℚ).mapMatrix
    ((SpecialLinearGroup.toGL g⁻¹ : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [e]
  fin_cases i <;> fin_cases j <;> simp

/-- **Every rational cusp is `GL₂(ℤ)`-equivalent to `∞`.** -/
theorem exists_cusp_conj_GL (A : GeneralLinearGroup (Fin 2) ℚ) :
    ∃ h : GL2Z, ∀ l ∈ cuspStab A, h⁻¹ * l * h ∈ cuspStab 1 := by
  by_cases hv1 : A.val 1 0 = 0
  · refine ⟨1, conj_cuspStab A 1 1 ?_⟩
    change (1⁻¹ * (GeneralLinearGroup.map (Int.castRingHom ℚ) (1 : GL2Z))⁻¹ * A).val 1 0 = 0
    simpa using hv1
  · set v0 := A.val 0 0 with hv0
    set v1 := A.val 1 0 with hv1'
    set t : ℚ := v0 / v1 with ht
    set p : ℤ := t.num with hp
    set q : ℤ := (t.den : ℤ) with hq
    have hqpos : (0 : ℚ) < q := by rw [hq]; exact_mod_cast t.den_pos
    have hcop : IsCoprime p q := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [hp, hq, Int.gcd] using t.reduced
    have hcross : v0 * q = v1 * p := by
      have h1 : (p : ℚ) / (q : ℚ) = v0 / v1 := by
        rw [← ht]; simp [hp, hq, Rat.num_div_den]
      field_simp at h1
      linarith
    obtain ⟨x, y, hxy⟩ := hcop
    refine ⟨glOfEntries p (-y) q x (by linarith), conj_cuspStab A 1 _ ?_⟩
    change (1⁻¹ * (GeneralLinearGroup.map (Int.castRingHom ℚ) (glOfEntries p (-y) q x _))⁻¹ *
      A).val 1 0 = 0
    rw [inv_one, one_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      map_glOfEntries_inv, map_glOfEntries_inv]
    simp
    linarith

/-- **A crossed cocycle of `GL₂(ℤ)` trivial at `T` is trivial on every cusp stabilizer.** -/
theorem vanishes_every_cusp_GL (x : crossedCocycles ρ)
    (hT : ∃ u, x.val Tgl = ρ Tgl u - u) (A : GeneralLinearGroup (Fin 2) ℚ) :
    ∃ w, ∀ l ∈ cuspStab A, x.val l = ρ l w - w := by
  obtain ⟨h, hh⟩ := exists_cusp_conj_GL A
  obtain ⟨w₁, hw₁⟩ := vanishes_cusp_one_GL ρ x hT
  exact trivialOn_conj ρ x h⁻¹ (cuspStab 1 : Set GL2Z) (cuspStab A : Set GL2Z) ⟨w₁, hw₁⟩
    (fun t ht => by simpa using hh t ht)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
