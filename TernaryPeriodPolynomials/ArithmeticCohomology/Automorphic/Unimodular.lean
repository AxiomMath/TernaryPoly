module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.Haar
public import Mathlib.MeasureTheory.Group.ModularCharacter

@[expose] public section


/-!
# Unimodularity of `GL₂(𝔸)`

The modular character `Δ` of `GL₂(𝔸)` is a homomorphism to the positive reals. It is trivial on
the centre, hence on the diagonal units `diag(t, 1)` (conjugating by the swap gives
`diag(1, t)`, and the product is the scalar `t`), hence on the unipotents (conjugating `n(b)` by
`diag(2, 1)` gives `n(2b) = n(b)²`). Every element whose upper-left entry is a unit is a product of
such elements, and every element of `GL₂(𝔸)` is moved into that set by an upper unipotent, because
`𝔸 = ℝ × 𝔸_f` has stable range one: for a unimodular column `(a, c)` the element `x` with
`x_v = 1` if `|a|_v < |c|_v` and `x_v = 0` otherwise makes `a + x c` a unit, with
`|a + x c|_v = max(|a|_v, |c|_v)` at every finite place. Consequently the Haar measure
`BinaryHaar.measure` is right invariant.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Measure Matrix IsDedekindDomain
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped NNReal

noncomputable section

namespace TernaryPeriodPolynomials.Automorphic.Unimodular

section Algebra

variable {R : Type*} [CommRing R]

/-- The diagonal element `diag(t, 1)`. -/
def diagonalUnit (t : Rˣ) : GL (Fin 2) R :=
  ⟨!![t.val, 0; 0, 1], !![t⁻¹.val, 0; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The coordinate swap `[[0, 1], [1, 0]]`. -/
def swap : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The lower unipotent `[[1, 0], [c, 1]]`. -/
def lowerUnipotent (c : R) : GL (Fin 2) R :=
  ⟨!![1, 0; c, 1], !![1, 0; -c, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem swap_inv : (swap : GL (Fin 2) R)⁻¹ = swap := rfl

theorem diagonalUnit_mul_conj (t : Rˣ) :
    diagonalUnit t * (swap * diagonalUnit t * swap⁻¹) = GeneralLinearGroup.scalar (Fin 2) t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalUnit, swap, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonalUnit_conj_unipotent (t : Rˣ) (b : R) :
    diagonalUnit t * binaryUnipotent b * (diagonalUnit t)⁻¹ = binaryUnipotent (t.val * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalUnit, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_mul (b c : R) :
    binaryUnipotent b * binaryUnipotent c = binaryUnipotent (b + c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem swap_conj_unipotent (c : R) :
    swap * binaryUnipotent c * swap⁻¹ = lowerUnipotent c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap, binaryUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

/-- A matrix with unit upper-left entry `a` is `n̄(c a⁻¹) diag(a, 1) diag(1, det/a) n(a⁻¹ b)`. -/
theorem decomposition (g : GL (Fin 2) R) (a : Rˣ) (ha : g.val 0 0 = a.val) :
    g = lowerUnipotent (g.val 1 0 * a⁻¹.val) * diagonalUnit a *
      (swap * diagonalUnit (GeneralLinearGroup.det g * a⁻¹) * swap⁻¹) *
        binaryUnipotent (a⁻¹.val * g.val 0 1) := by
  have hinv : a.val * a⁻¹.val = 1 := a.mul_inv
  have hdet : (GeneralLinearGroup.det g).val = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := by
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalUnit, swap, binaryUnipotent, lowerUnipotent, Matrix.mul_apply,
      Fin.sum_univ_two, hdet, ha]
  linear_combination (-(g.val 1 1)) * hinv

/-- A homomorphism to `ℝ≥0` is invariant under conjugation. -/
theorem conj_eq {G : Type*} [Group G] (Δ : G →* ℝ≥0) (h g : G) : Δ (h * g * h⁻¹) = Δ g := by
  have hh : Δ h * Δ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, mul_comm (Δ h) (Δ g), mul_assoc, hh, mul_one]

theorem ne_zero_of_hom {G : Type*} [Group G] (Δ : G →* ℝ≥0) (g : G) : Δ g ≠ 0 := by
  intro hg
  have hh : Δ g * Δ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [hg, zero_mul] at hh
  exact zero_ne_one hh

variable (Δ : GL (Fin 2) R →* ℝ≥0)

theorem diagonal_trivial (central : ∀ t, Δ (GeneralLinearGroup.scalar (Fin 2) t) = 1) (t : Rˣ) :
    Δ (diagonalUnit t) = 1 := by
  have h := congrArg Δ (diagonalUnit_mul_conj t)
  rw [map_mul, conj_eq, central] at h
  have h' : ((Δ (diagonalUnit t) : ℝ) - 1) * ((Δ (diagonalUnit t) : ℝ) + 1) = 0 := by
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    push_cast at this
    linear_combination this
  have hpos : (0 : ℝ) ≤ Δ (diagonalUnit t) := NNReal.coe_nonneg _
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact NNReal.coe_injective (by push_cast; linarith)
  · linarith

theorem unipotent_trivial (two : IsUnit (2 : R)) (b : R) : Δ (binaryUnipotent b) = 1 := by
  have h := congrArg Δ (diagonalUnit_conj_unipotent two.unit b)
  rw [conj_eq, IsUnit.unit_spec, two_mul, ← unipotent_mul, map_mul] at h
  have hne := ne_zero_of_hom Δ (binaryUnipotent b)
  exact (mul_eq_left₀ hne).mp h.symm

theorem lower_trivial (two : IsUnit (2 : R)) (c : R) : Δ (lowerUnipotent c) = 1 := by
  rw [← swap_conj_unipotent, conj_eq, unipotent_trivial Δ two]

theorem trivial_of_unit (central : ∀ t, Δ (GeneralLinearGroup.scalar (Fin 2) t) = 1)
    (two : IsUnit (2 : R)) (g : GL (Fin 2) R) (unit : IsUnit (g.val 0 0)) : Δ g = 1 := by
  rw [decomposition g unit.unit unit.unit_spec.symm, map_mul, map_mul, map_mul,
    lower_trivial Δ two, diagonal_trivial Δ central, conj_eq, diagonal_trivial Δ central,
    unipotent_trivial Δ two]
  simp

/-- If every element is moved by an upper unipotent to one with unit upper-left entry, every
homomorphism to `ℝ≥0` trivial on the centre is trivial. -/
theorem trivial_of_stable (central : ∀ t, Δ (GeneralLinearGroup.scalar (Fin 2) t) = 1)
    (two : IsUnit (2 : R))
    (stable : ∀ g : GL (Fin 2) R, ∃ x : R, IsUnit ((binaryUnipotent x * g).val 0 0))
    (g : GL (Fin 2) R) : Δ g = 1 := by
  obtain ⟨x, hx⟩ := stable g
  have h := trivial_of_unit Δ central two _ hx
  rw [map_mul, unipotent_trivial Δ two, one_mul] at h
  exact h

end Algebra

section StableRange

/-- Stable range one for the real numbers. -/
theorem real_stable (a c p q : ℝ) (h : p * a + q * c = 1) : ∃ x : ℝ, IsUnit (a + x * c) := by
  by_cases ha : a = 0
  · refine ⟨1, isUnit_iff_ne_zero.mpr ?_⟩
    rintro hc
    rw [ha, zero_add, one_mul] at hc
    rw [ha, hc] at h
    simp at h
  · exact ⟨0, by simpa using ha⟩

/-- Stable range one for the finite adeles. -/
theorem finite_stable (a c p q : FiniteAdeles) (h : p * a + q * c = 1) :
    ∃ x : FiniteAdeles, IsUnit (a + x * c) := by
  classical
  let pick : ∀ v : FinitePlace, v.adicCompletion ℚ :=
    fun v => if Valued.v (a v) < Valued.v (c v) then 1 else 0
  have pick_int : ∀ v, pick v ∈ v.adicCompletionIntegers ℚ := by
    intro v
    dsimp only [pick]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  let x : FiniteAdeles := ⟨pick, Filter.Eventually.of_forall pick_int⟩
  have hval : ∀ v, Valued.v ((a + x * c) v) = max (Valued.v (a v)) (Valued.v (c v)) := by
    intro v
    change Valued.v (a v + pick v * c v) = _
    dsimp only [pick]
    split_ifs with hlt
    · rw [one_mul, Valuation.map_add_eq_of_lt_right _ hlt, max_eq_right hlt.le]
    · rw [zero_mul, add_zero, max_eq_left (not_lt.mp hlt)]
  have hne : ∀ v, (a + x * c) v ≠ 0 := by
    intro v hv
    have h0 := hval v
    rw [hv, map_zero] at h0
    have ha : a v = 0 := (Valuation.zero_iff _).mp (le_antisymm (h0 ▸ le_max_left _ _) zero_le)
    have hc : c v = 0 := (Valuation.zero_iff _).mp (le_antisymm (h0 ▸ le_max_right _ _) zero_le)
    have h1 := congrArg (fun y : FiniteAdeles => y v) h
    change p v * a v + q v * c v = 1 at h1
    rw [ha, hc] at h1
    simp at h1
  have hgood : ∀ᶠ v in Filter.cofinite,
      a v ∈ (v : FinitePlace).adicCompletionIntegers ℚ ∧ c v ∈ v.adicCompletionIntegers ℚ ∧
        p v ∈ v.adicCompletionIntegers ℚ ∧ q v ∈ v.adicCompletionIntegers ℚ :=
    a.2.and (c.2.and (p.2.and q.2))
  have hinv_int : ∀ᶠ v in Filter.cofinite,
      ((a + x * c) v)⁻¹ ∈ (v : FinitePlace).adicCompletionIntegers ℚ := by
    filter_upwards [hgood] with v hv
    obtain ⟨ha, hc, hp, hq⟩ := hv
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha hc hp hq ⊢
    have h1 := congrArg (fun y : FiniteAdeles => y v) h
    change p v * a v + q v * c v = 1 at h1
    have hle : (1 : WithZero (Multiplicative ℤ)) ≤ max (Valued.v (a v)) (Valued.v (c v)) := by
      calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (p v * a v + q v * c v) := by
              rw [h1, map_one]
        _ ≤ max (Valued.v (p v * a v)) (Valued.v (q v * c v)) := Valuation.map_add _ _ _
        _ ≤ max (Valued.v (a v)) (Valued.v (c v)) := by
              rw [map_mul, map_mul]
              exact max_le_max (mul_le_of_le_one_left' hp) (mul_le_of_le_one_left' hq)
    have heq : Valued.v ((a + x * c) v) = 1 := by
      rw [hval]
      exact le_antisymm (max_le ha hc) hle
    rw [map_inv₀, heq, inv_one]
  let y : FiniteAdeles := ⟨fun v => ((a + x * c) v)⁻¹, hinv_int⟩
  refine ⟨x, ⟨⟨a + x * c, y, ?_, ?_⟩, rfl⟩⟩
  · exact RestrictedProduct.ext _ _ (fun v => mul_inv_cancel₀ (hne v))
  · exact RestrictedProduct.ext _ _ (fun v => inv_mul_cancel₀ (hne v))

/-- Stable range one for the adeles `ℝ × 𝔸_f`. -/
theorem adele_stable (a c p q : Adeles) (h : p * a + q * c = 1) :
    ∃ x : Adeles, IsUnit (a + x * c) := by
  obtain ⟨x₁, hx₁⟩ := real_stable a.1 c.1 p.1 q.1 (congrArg Prod.fst h)
  obtain ⟨x₂, hx₂⟩ := finite_stable a.2 c.2 p.2 q.2 (congrArg Prod.snd h)
  exact ⟨(x₁, x₂), Prod.isUnit_iff.mpr ⟨hx₁, hx₂⟩⟩

theorem binary_stable (g : BinaryAdelicGL) :
    ∃ x : Adeles, IsUnit ((binaryUnipotent x * g).val 0 0) := by
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) Adeles => m 0 0) g.inv_val
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
  obtain ⟨x, hx⟩ := adele_stable (g.val 0 0) (g.val 1 0) _ _ h
  refine ⟨x, ?_⟩
  simpa [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two] using hx

theorem two_isUnit : IsUnit (2 : Adeles) := by
  rw [← map_ofNat rationalAdele 2]
  exact (isUnit_of_invertible (2 : ℚ)).map rationalAdele

end StableRange

section Measure

instance measure_innerRegular : BinaryHaar.measure.InnerRegular :=
  InnerRegularCompactLTTop.instInnerRegularOfSigmaFinite

theorem scalar_commute (t : Adelesˣ) (x : BinaryAdelicGL) :
    GeneralLinearGroup.scalar (Fin 2) t * x = x * GeneralLinearGroup.scalar (Fin 2) t := by
  apply Units.ext
  simp only [GeneralLinearGroup.scalar, Units.val_mul]
  exact Matrix.ext fun i j => by simp [mul_comm]

/-- The modular character of `GL₂(𝔸)` is trivial on the centre. -/
theorem modularCharacter_scalar (t : Adelesˣ) :
    modularCharacter (GeneralLinearGroup.scalar (Fin 2) t) = 1 := by
  change modularCharacterFun _ = 1
  rw [modularCharacterFun_eq_haarScalarFactor BinaryHaar.measure]
  have h : (fun x : BinaryAdelicGL => x * GeneralLinearGroup.scalar (Fin 2) t) =
      (fun x => GeneralLinearGroup.scalar (Fin 2) t * x) := by
    funext x
    exact (scalar_commute t x).symm
  have hmap : Measure.map (fun x : BinaryAdelicGL => x * GeneralLinearGroup.scalar (Fin 2) t)
      BinaryHaar.measure = BinaryHaar.measure := by
    rw [h]
    exact map_mul_left_eq_self _ _
  simp only [hmap, haarScalarFactor_self]

/-- `GL₂(𝔸)` is unimodular: its modular character is trivial. -/
theorem modularCharacter_eq_one (g : BinaryAdelicGL) : modularCharacter g = 1 :=
  trivial_of_stable modularCharacter modularCharacter_scalar two_isUnit binary_stable g

/-- The Haar measure of `GL₂(𝔸)` is right invariant. -/
instance measure_isMulRightInvariant : BinaryHaar.measure.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  rw [map_right_mul_eq_modularCharacterFun_smul BinaryHaar.measure g]
  change modularCharacter g • BinaryHaar.measure = BinaryHaar.measure
  rw [modularCharacter_eq_one, one_smul]

/-- Right translation invariance of the Haar integral on `GL₂(𝔸)`. -/
theorem integral_right (function : BinaryAdelicGL → ℂ) (matrix : BinaryAdelicGL) :
    ∫ point, function (point * matrix) ∂BinaryHaar.measure =
      ∫ point, function point ∂BinaryHaar.measure :=
  integral_mul_right_eq_self function matrix

/-- Right translation invariance of the Haar lower integral on `GL₂(𝔸)`. -/
theorem lintegral_right (function : BinaryAdelicGL → ENNReal) (matrix : BinaryAdelicGL) :
    ∫⁻ point, function (point * matrix) ∂BinaryHaar.measure =
      ∫⁻ point, function point ∂BinaryHaar.measure :=
  lintegral_mul_right_eq_self function matrix

end Measure

end TernaryPeriodPolynomials.Automorphic.Unimodular
