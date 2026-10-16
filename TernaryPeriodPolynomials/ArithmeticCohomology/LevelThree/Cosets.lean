module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ExactLevel

@[expose] public section


/-!
# The `p + 1` Hecke cosets of `Γ₁'(3)` and `Γ₁(3)`

Let `p ≠ 3` be prime and `ε_p = ±1` with `ε_p ≡ p mod 3`. The Levi group of both level-three cusps
is
`Γ₁'(3) = binaryArithmeticLevel = {A ∈ GL₂(ℤ) : second row ≡ (0, 1) mod 3}`, and the Levi double
coset occurring in the bad-line local correspondence of `T_p = Γ diag(p,1,1) Γ` is
`Δ_p = {α ∈ M₂(ℤ) : det α = ± p, second row of α ≡ (0, p) mod 3}`
(the inverses `p B⁻¹` of the Levi blocks `B` of the local cosets: `det B = ± p`, second row of `B`
`≡ (0, 1)`). The matrices
`α_j = [[1, j], [0, p]]` (`0 ≤ j < p`) and `α_∞ = ε_p · [[p, 0], [0, 1]]`
(all of determinant `p`) represent the `p + 1` right cosets `Γ₁'(3) α` in `Δ_p`, and right
multiplication by `Γ₁'(3)` permutes them: `α_j g = δ α_{next g j}` with `δ ∈ Γ₁'(3)`
(`levelCosets`). For `g ∈ Γ₁(3) = core` the transition `δ` has determinant one, hence lies in
`Γ₁(3)`, which gives the same data for `Γ₁(3) diag(1,p) Γ₁(3)` with the same transitions
(`coreCosets`, `coreEmbed_coreDelta`).

The transitions are obtained from the level-one transitions of `LevelOneCosets.exists_transition`
(`GL₂(ℤ) diag(p,1) GL₂(ℤ)`), after twisting the `∞` representative by the scalar `ε_p`, and the
level condition on `δ` is a computation modulo `3`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeCosets

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators GammaOneThree
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.SphericalDetection.Helpers

section Residues

variable (p : Nat.Primes)

theorem cast_ne_zero (hp3 : p.val ≠ 3) : (p.val : ZMod 3) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  rcases (Nat.prime_dvd_prime_iff_eq Nat.prime_three p.property).mp h with h'
  exact hp3 h'.symm

theorem cast_mul_self (hp3 : p.val ≠ 3) : (p.val : ZMod 3) * (p.val : ZMod 3) = 1 := by
  have key : ∀ a : ZMod 3, a ≠ 0 → a * a = 1 := by decide
  exact key _ (cast_ne_zero p hp3)

/-- The sign `ε_p ∈ {±1}` with `ε_p ≡ p mod 3`. -/
def signP : ℤˣ := if (p.val : ZMod 3) = 1 then 1 else -1

theorem signP_cast (hp3 : p.val ≠ 3) : (((signP p : ℤˣ) : ℤ) : ZMod 3) = p.val := by
  unfold signP
  split_ifs with h
  · simp [h]
  · have key : ∀ a : ZMod 3, a ≠ 0 → a ≠ 1 → a = -1 := by decide
    rw [key _ (cast_ne_zero p hp3) h]
    simp

theorem signP_mul_self : ((signP p : ℤˣ) : ℤ) * ((signP p : ℤˣ) : ℤ) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

end Residues

section Matrices

variable (p : Nat.Primes)

/-- The scalar matrix `ε_p · 1` in `GL₂(ℤ)`. -/
def signMatrix : GL (Fin 2) ℤ :=
  ⟨!![(signP p : ℤ), 0; 0, (signP p : ℤ)], !![(signP p : ℤ), 0; 0, (signP p : ℤ)], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, signP_mul_self p], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, signP_mul_self p]⟩

/-- The twist of the level-one representative: `ε_p · 1` at `∞`, `1` otherwise. -/
def twist : Option (Fin p.val) → GL (Fin 2) ℤ
  | none => signMatrix p
  | some _ => 1

theorem twist_comm (j : Option (Fin p.val)) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    (twist p j : Matrix (Fin 2) (Fin 2) ℤ) * A = A * (twist p j : Matrix (Fin 2) (Fin 2) ℤ) := by
  cases j with
  | none =>
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [twist, signMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  | some _ => simp [twist]

/-- The integral representatives `α_j = [[1, j], [0, p]]`, `α_∞ = ε_p [[p, 0], [0, 1]]`. -/
def N (j : Option (Fin p.val)) : Matrix (Fin 2) (Fin 2) ℤ :=
  (twist p j : Matrix (Fin 2) (Fin 2) ℤ) * M p j

theorem N_none : N p none = !![(signP p : ℤ) * p.val, 0; 0, (signP p : ℤ)] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [N, twist, signMatrix, M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_some (i : Fin p.val) : N p (some i) = !![1, (i.val : ℤ); 0, (p.val : ℤ)] := by
  simp [N, twist, M, modularHeckeMatrix]

theorem N_det (j : Option (Fin p.val)) : (N p j).det = p.val := by
  cases j with
  | none =>
    rw [N_none, Matrix.det_fin_two_of]
    linear_combination (p.val : ℤ) * signP_mul_self p
  | some i =>
    rw [N_some, Matrix.det_fin_two_of]
    ring

/-- **The Hecke representatives** in `GL₂(ℚ)`. -/
def heckeRep (j : Option (Fin p.val)) : GL (Fin 2) ℚ :=
  integralEmbed (twist p j) * binaryHeckeRepresentative p j

theorem heckeRep_val (j : Option (Fin p.val)) :
    (heckeRep p j : Matrix (Fin 2) (Fin 2) ℚ) = (N p j).map (Int.castRingHom ℚ) := by
  rw [heckeRep, Units.val_mul, integralEmbed_val, rep_val, N, Matrix.map_mul]

theorem heckeRep_none :
    (heckeRep p none : Matrix (Fin 2) (Fin 2) ℚ) =
      !![((signP p : ℤ) : ℚ) * p.val, 0; 0, ((signP p : ℤ) : ℚ)] := by
  rw [heckeRep_val, N_none]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem heckeRep_some (i : Fin p.val) :
    (heckeRep p (some i) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (i.val : ℚ); 0, (p.val : ℚ)] := by
  rw [heckeRep_val, N_some]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-- The rational relation `ι(δ) = α_j ι(g) α_k⁻¹` is the integral relation `δ α_k = α_j g`. -/
theorem embed_eq_iff (δ g : GL (Fin 2) ℤ) (j k : Option (Fin p.val)) :
    integralEmbed δ = heckeRep p j * integralEmbed g * (heckeRep p k)⁻¹ ↔
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * N p k = N p j * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [eq_mul_inv_iff_mul_eq]
  constructor
  · intro h
    apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
    have hv := congrArg (fun x : GL (Fin 2) ℚ => (x : Matrix (Fin 2) (Fin 2) ℚ)) h
    simp only [Units.val_mul, integralEmbed_val, heckeRep_val] at hv
    simpa only [Matrix.map_mul] using hv
  · intro h
    apply Units.ext
    simp only [Units.val_mul, integralEmbed_val, heckeRep_val]
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]

/-- Distinct indices give distinct cosets. -/
theorem disjoint_N (g : Matrix (Fin 2) (Fin 2) ℤ) (i j : Option (Fin p.val))
    (h : g * N p j = N p i) : i = j := by
  apply disjoint_int p (((twist p i)⁻¹ : GL (Fin 2) ℤ) * g * (twist p j : Matrix (Fin 2) (Fin 2) ℤ))
  have hinv : (((twist p i)⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      (twist p i : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h' := congrArg (fun x => (((twist p i)⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * x) h
  simp only [N] at h'
  calc _ = (((twist p i)⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
        (g * ((twist p j : Matrix (Fin 2) (Fin 2) ℤ) * M p j)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := h'
    _ = M p i := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

end Matrices

section Level

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- `Γ₁'(3) → GL₂(ℚ)`. -/
def levelEmbed : binaryArithmeticLevel →* GL (Fin 2) ℚ :=
  integralEmbed.comp binaryArithmeticLevel.subtype

theorem levelEmbed_apply (g : binaryArithmeticLevel) : levelEmbed g = integralEmbed g.val := rfl

theorem levelEmbed_injective : Function.Injective levelEmbed :=
  integralEmbed_injective.comp Subtype.val_injective

/-- Second row of a level element modulo `3`. -/
theorem level_row (g : binaryArithmeticLevel) :
    ((g.val.val 1 0 : ℤ) : ZMod 3) = 0 ∧ ((g.val.val 1 1 : ℤ) : ZMod 3) = 1 := by
  have h := (mem_binaryArithmeticLevel_iff g.val).mp g.property
  exact ⟨by simpa using h 0, by simpa using h 1⟩

include hp3 in
/-- **The level condition on the transition**: if `δ α_k = α_j g` with `g ∈ Γ₁'(3)`, then
`δ ∈ Γ₁'(3)`. -/
theorem transition_mem (δ : GL (Fin 2) ℤ) (g : binaryArithmeticLevel) (j k : Option (Fin p.val))
    (h : (δ : Matrix (Fin 2) (Fin 2) ℤ) * N p k = N p j * (g.val : Matrix (Fin 2) (Fin 2) ℤ)) :
    δ ∈ binaryArithmeticLevel := by
  apply (mem_binaryArithmeticLevel_iff δ).mpr
  have hpp := cast_mul_self p hp3
  have hs := signP_cast p hp3
  obtain ⟨g0, g1⟩ := level_row g
  have e0 := congrArg (Int.cast : ℤ → ZMod 3) (congrFun (congrFun h 1) 0)
  have e1 := congrArg (Int.cast : ℤ → ZMod 3) (congrFun (congrFun h 1) 1)
  -- the right-hand side: second row of `α_j g` is `≡ (0, p)`
  have r0 : ((N p j * (g.val : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 3) = 0 := by
    cases j with
    | none =>
      simp only [N_none, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      simp [g0]
    | some i =>
      simp only [N_some, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      simp [g0]
  have r1 : ((N p j * (g.val : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 : ZMod 3) = p.val := by
    cases j with
    | none =>
      simp only [N_none, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      simp [g1, hs]
    | some i =>
      simp only [N_some, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      simp [g1]
  rw [r0] at e0
  rw [r1] at e1
  intro column
  cases k with
  | none =>
    simp only [N_none, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at e0 e1
    push_cast at e0 e1
    rw [hs] at e0 e1
    have z0 : ((δ.val 1 0 : ℤ) : ZMod 3) = 0 := by
      linear_combination e0 - ((δ.val 1 0 : ℤ) : ZMod 3) * hpp
    fin_cases column
    · show ((δ.val 1 0 : ℤ) : ZMod 3) = 0
      exact z0
    · show ((δ.val 1 1 : ℤ) : ZMod 3) = 1
      linear_combination (p.val : ZMod 3) * e1 - ((δ.val 1 1 : ℤ) : ZMod 3) * hpp + hpp
  | some i =>
    simp only [N_some, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at e0 e1
    push_cast at e0 e1
    have z0 : ((δ.val 1 0 : ℤ) : ZMod 3) = 0 := by linear_combination e0
    rw [z0] at e1
    fin_cases column
    · show ((δ.val 1 0 : ℤ) : ZMod 3) = 0
      exact z0
    · show ((δ.val 1 1 : ℤ) : ZMod 3) = 1
      linear_combination (p.val : ZMod 3) * e1 - ((δ.val 1 1 : ℤ) : ZMod 3) * hpp + hpp

include hp3 in
/-- **Existence of transitions in `Γ₁'(3)`.** -/
theorem exists_level_transition (g : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    ∃ k : Option (Fin p.val), ∃ δ : binaryArithmeticLevel,
      (δ.val : Matrix (Fin 2) (Fin 2) ℤ) * N p k = N p j * (g.val : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨k, δ, hδ⟩ := exists_transition p (twist p j * g.val) j
  have hinv : (((twist p k)⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      (twist p k : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ((δ * (twist p k)⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * N p k =
      N p j * (g.val : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Units.val_mul, N, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ (twist p k : Matrix (Fin 2) (Fin 2) ℤ), hinv, Matrix.one_mul, hδ, N,
      Units.val_mul, ← Matrix.mul_assoc, ← twist_comm, Matrix.mul_assoc]
  exact ⟨k, ⟨_, transition_mem p hp3 _ g j k key⟩, key⟩

/-- The next coset index. -/
def levelNext (g : binaryArithmeticLevel) (j : Option (Fin p.val)) : Option (Fin p.val) :=
  (exists_level_transition p hp3 g j).choose

/-- The transition element `δ = α_j g α_{next g j}⁻¹ ∈ Γ₁'(3)`. -/
def levelDelta (g : binaryArithmeticLevel) (j : Option (Fin p.val)) : binaryArithmeticLevel :=
  (exists_level_transition p hp3 g j).choose_spec.choose

theorem levelDelta_spec (g : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    ((levelDelta p hp3 g j).val : Matrix (Fin 2) (Fin 2) ℤ) * N p (levelNext p hp3 g j) =
      N p j * (g.val : Matrix (Fin 2) (Fin 2) ℤ) :=
  (exists_level_transition p hp3 g j).choose_spec.choose_spec

/-- **The Hecke cosets of `Γ₁'(3)` in `Δ_p`**: representatives `heckeRep p j`
(`α_j = [[1, j], [0, p]]`, `α_∞ = ε_p [[p, 0], [0, 1]]`), transitions
`levelEmbed (levelDelta g j) = α_j · levelEmbed g · α_{levelNext g j}⁻¹`. -/
def levelCosets : RightCosets levelEmbed where
  index := Option (Fin p.val)
  rep := heckeRep p
  next := levelNext p hp3
  delta := levelDelta p hp3
  delta_spec g j := (embed_eq_iff p _ g.val j _).mpr (levelDelta_spec p hp3 g j)
  disjoint i j g h := by
    have h' : integralEmbed g.val = heckeRep p i * integralEmbed 1 * (heckeRep p j)⁻¹ := by
      rw [map_one, mul_one]; exact h
    have := (embed_eq_iff p g.val 1 i j).mp h'
    rw [Units.val_one, Matrix.mul_one] at this
    exact disjoint_N p _ i j this

theorem levelCosets_rep : (levelCosets p hp3).rep = heckeRep p := rfl

theorem levelCosets_next : (levelCosets p hp3).next = levelNext p hp3 := rfl

theorem levelCosets_delta : (levelCosets p hp3).delta = levelDelta p hp3 := rfl

end Level

section Core

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

theorem reflection_det : GeneralLinearGroup.det (reflection : binaryArithmeticLevel).val = -1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, reflection, Matrix.det_fin_two_of]

/-- **`Γ₁(3)` is the determinant-one part of `Γ₁'(3)`.** -/
theorem mem_core_iff (g : binaryArithmeticLevel) :
    g ∈ core ↔ GeneralLinearGroup.det g.val = 1 := by
  constructor
  · intro hg
    exact ExactLevel.core_det ⟨g, hg⟩
  · intro hdet
    rcases mem_core_or g with hg | hg
    · exact hg
    · exfalso
      have h := ExactLevel.core_det ⟨g * reflection, hg⟩
      change GeneralLinearGroup.det (g.val * reflection.val) = 1 at h
      rw [map_mul, hdet, reflection_det, one_mul] at h
      exact absurd h (by decide)

theorem det_levelDelta (g : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    GeneralLinearGroup.det (levelDelta p hp3 g j).val = GeneralLinearGroup.det g.val := by
  apply Units.ext
  have h := congrArg Matrix.det (levelDelta_spec p hp3 g j)
  rw [Matrix.det_mul, Matrix.det_mul, N_det, N_det, mul_comm (p.val : ℤ)] at h
  have hp : (p.val : ℤ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  simpa [GeneralLinearGroup.val_det_apply] using mul_right_cancel₀ hp h

/-- `Γ₁(3) → GL₂(ℚ)`. -/
def coreEmbed : core →* GL (Fin 2) ℚ := levelEmbed.comp core.subtype

theorem coreEmbed_injective : Function.Injective coreEmbed :=
  levelEmbed_injective.comp Subtype.val_injective

/-- The transition of a `Γ₁(3)` element, in `Γ₁(3)`. -/
def coreDelta (k : core) (j : Option (Fin p.val)) : core :=
  ⟨levelDelta p hp3 k j, (mem_core_iff _).mpr
    ((det_levelDelta p hp3 _ j).trans ((mem_core_iff _).mp k.property))⟩

theorem coreDelta_val (k : core) (j : Option (Fin p.val)) :
    (coreDelta p hp3 k j : binaryArithmeticLevel) = levelDelta p hp3 k j := rfl

/-- **The Hecke cosets of `Γ₁(3) diag(1,p) Γ₁(3)`**, with the same representatives and the same
transitions as for `Γ₁'(3)` (all representatives have determinant `p > 0`). -/
def coreCosets : RightCosets coreEmbed where
  index := Option (Fin p.val)
  rep := heckeRep p
  next k := levelNext p hp3 k
  delta := coreDelta p hp3
  delta_spec k j := (levelCosets p hp3).delta_spec k j
  disjoint i j k h := (levelCosets p hp3).disjoint i j k h

theorem coreCosets_rep : (coreCosets p hp3).rep = heckeRep p := rfl

theorem coreCosets_next (k : core) : (coreCosets p hp3).next k = levelNext p hp3 k := rfl

theorem coreCosets_delta (k : core) (j : Option (Fin p.val)) :
    ((coreCosets p hp3).delta k j : binaryArithmeticLevel) = levelDelta p hp3 k j := rfl

end Core

end TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
