module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreStab
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Cosets

@[expose] public section


/-!
# The stabilizer of the base Hecke coset of `Γ₁'(3)` and an explicit transversal

Let `Γ = Γ₁'(3) = binaryArithmeticLevel`, `p ≠ 3` prime, and `S = levelCosets p hp3` the `p + 1`
right cosets `Γ α_j` with `α_j = [[1, j], [0, p]]`, `α_∞ = ε_p [[p, 0], [0, 1]]`.  The *base coset*
is `j₀ = baseIdx p = 0`, with representative `α₀ = diag(1, p)`.

* `matGL`, `matLevel` build elements of `GL₂(ℤ)` and of `Γ` from an integral matrix of determinant
  `±1`; `levelNext_eq_of_mul` and `levelDelta_eq_of_mul` read the coset action and the transitions
  off an integral relation `δ α_k = α_j g`.
* **The stabilizer of the base coset is `Γ ∩ Γ⁰(p)`** (`mem_stab_iff`): `h = [[a, b], [c, d]]`
  stabilizes the coset `0` iff `p ∣ b`.  (The level-three condition on `α₀ h α₀⁻¹ =
  [[a, b/p], [p c, d]]` is automatic because `p` is a unit modulo `3`.)
* **An explicit transversal** `transv p hp3 : Option (Fin p) → Γ`: `transv (some i) = T^i` and
  `transv none = γ_∞ = [[p u, v], [3, 1]]` with `p u - 3 v = 1` (Bezout), carrying the coset `0` to
  the coset `j` (`levelNext_transv`).  The transition is `α₀ T^i = α_i` for `j = i`, and
  `α₀ γ_∞ = δ_∞ α_∞` with `δ_∞ = ε_p [[u, v], [3, p]] ∈ Γ` (`levelDelta_transv_none`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed integralEmbed_val)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets

section Construct

/-- Equality of `2 × 2` matrices from the equality of the four entries. -/
theorem mat2_eq {R : Type*} {x11 x12 x21 x22 y11 y12 y21 y22 : R} (h11 : x11 = y11)
    (h12 : x12 = y12) (h21 : x21 = y21) (h22 : x22 = y22) :
    (!![x11, x12; x21, x22] : Matrix (Fin 2) (Fin 2) R) = !![y11, y12; y21, y22] := by
  rw [h11, h12, h21, h22]

/-- The element of `GL₂(ℤ)` with matrix `[[a, b], [c, d]]` of determinant `s = ±1`. -/
def matGL (a b c d s : ℤ) (hs : s * s = 1) (hdet : a * d - b * c = s) : GL (Fin 2) ℤ :=
  ⟨!![a, b; c, d], !![s * d, -(s * b); -(s * c), s * a], by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact mat2_eq (by linear_combination s * hdet + hs) (by ring) (by ring)
      (by linear_combination s * hdet + hs), by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact mat2_eq (by linear_combination s * hdet + hs) (by ring) (by ring)
      (by linear_combination s * hdet + hs)⟩

theorem matGL_val (a b c d s : ℤ) (hs : s * s = 1) (hdet : a * d - b * c = s) :
    ((matGL a b c d s hs hdet : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := rfl

/-- The element of `Γ₁'(3)` with matrix `[[a, b], [c, d]]` of determinant `s = ±1`, `c ≡ 0` and
`d ≡ 1` modulo `3`. -/
def matLevel (a b c d s : ℤ) (hs : s * s = 1) (hdet : a * d - b * c = s)
    (hc : (c : ZMod 3) = 0) (hd : (d : ZMod 3) = 1) : binaryArithmeticLevel :=
  ⟨matGL a b c d s hs hdet, by
    apply (mem_binaryArithmeticLevel_iff _).mpr
    intro column
    fin_cases column
    · exact hc
    · exact hd⟩

theorem matLevel_val (a b c d s : ℤ) (hs : s * s = 1) (hdet : a * d - b * c = s)
    (hc : (c : ZMod 3) = 0) (hd : (d : ZMod 3) = 1) :
    (((matLevel a b c d s hs hdet hc hd : binaryArithmeticLevel).val : GL (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := rfl

/-- The determinant of an element of `GL₂(ℤ)` is a sign. -/
theorem det_mul_self (g : GL (Fin 2) ℤ) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ)).det * ((g : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 := by
  have h := congrArg Units.val (Int.units_mul_self (GeneralLinearGroup.det g))
  rw [Units.val_mul, GeneralLinearGroup.val_det_apply, Units.val_one] at h
  exact h

end Construct

section Cosets

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- **The base coset** `0`, with representative `α₀ = diag(1, p)`. -/
def baseIdx : Option (Fin p.val) := some ⟨0, p.property.pos⟩

theorem N_baseIdx : N p (baseIdx p) = !![1, 0; 0, (p.val : ℤ)] := by
  rw [baseIdx, N_some]
  simp

include hp3 in
/-- The coset index of `α_j g` is `k` as soon as `δ α_k = α_j g` for some `δ ∈ Γ₁'(3)`. -/
theorem levelNext_eq_of_mul (g δ : binaryArithmeticLevel) (j k : Option (Fin p.val))
    (h : (δ.val : Matrix (Fin 2) (Fin 2) ℤ) * N p k = N p j * (g.val : Matrix (Fin 2) (Fin 2) ℤ)) :
    levelNext p hp3 g j = k :=
  ((levelCosets p hp3).next_unique ((embed_eq_iff p δ.val g.val j k).mpr h)).symm

include hp3 in
/-- The transition is `δ` as soon as `δ α_k = α_j g` for some `δ ∈ Γ₁'(3)`. -/
theorem levelDelta_eq_of_mul (g δ : binaryArithmeticLevel) (j k : Option (Fin p.val))
    (h : (δ.val : Matrix (Fin 2) (Fin 2) ℤ) * N p k = N p j * (g.val : Matrix (Fin 2) (Fin 2) ℤ)) :
    levelDelta p hp3 g j = δ := by
  have hk := levelNext_eq_of_mul p hp3 g δ j k h
  symm
  apply (levelCosets p hp3).delta_unique levelEmbed_injective
  have := (embed_eq_iff p δ.val g.val j k).mpr h
  rw [← hk] at this
  exact this

theorem base_mul (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (!![1, 0; 0, (p.val : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * M =
      !![M 0 0, M 0 1; (p.val : ℤ) * M 1 0, (p.val : ℤ) * M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_base (M : Matrix (Fin 2) (Fin 2) ℤ) :
    M * (!![1, 0; 0, (p.val : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![M 0 0, (p.val : ℤ) * M 0 1; M 1 0, (p.val : ℤ) * M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

include hp3 in
/-- **The stabilizer of the base coset is `Γ₁'(3) ∩ Γ⁰(p)`**: `h` stabilizes the coset `0` iff `p`
divides the upper right entry of `h`. -/
theorem mem_stab_iff (h : binaryArithmeticLevel) :
    h ∈ AdjCore.stab (levelCosets p hp3) (baseIdx p) ↔ (p.val : ℤ) ∣ h.val.val 0 1 := by
  change levelNext p hp3 h (baseIdx p) = baseIdx p ↔ _
  constructor
  · intro hn
    have spec := levelDelta_spec p hp3 h (baseIdx p)
    rw [hn, N_baseIdx, mul_base, base_mul] at spec
    have e : (p.val : ℤ) * (levelDelta p hp3 h (baseIdx p)).val.val 0 1 = h.val.val 0 1 := by
      simpa using congrFun (congrFun spec 0) 1
    exact ⟨_, e.symm⟩
  · rintro ⟨b', hb'⟩
    obtain ⟨hc3, hd3⟩ := level_row h
    refine levelNext_eq_of_mul p hp3 h
      (matLevel (h.val.val 0 0) b' ((p.val : ℤ) * h.val.val 1 0) (h.val.val 1 1)
        (h.val.val.det) (det_mul_self h.val) ?_ ?_ ?_) (baseIdx p) (baseIdx p) ?_
    · rw [Matrix.det_fin_two]
      linear_combination (h.val.val 1 0) * hb'
    · push_cast
      rw [hc3, mul_zero]
    · exact hd3
    · rw [matLevel_val, N_baseIdx, base_mul, Matrix.mul_fin_two]
      exact mat2_eq (by ring) (by linear_combination (-1 : ℤ) * hb') (by ring) (by ring)

end Cosets

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
