module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.HeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.HeckeCorrespondence

@[expose] public section


/-!
# The `p + 1` Hecke cosets of `GL₂(ℤ)` and `SL₂(ℤ)`

For a prime `p` the matrices `α_∞ = [[p,0],[0,1]]` and `α_j = [[1,j],[0,p]]` (`0 ≤ j < p`) represent
distinct right cosets `Γ α` of `Γ = GL₂(ℤ)` (and of `Γ = SL₂(ℤ)`), and right multiplication by `Γ`
permutes these cosets. This packages the classical decomposition of `Γ diag(p,1) Γ` as
`HeckeH1.RightCosets` data (`arithmeticCosets`, `modularCosets`). The `SL₂(ℤ)` transitions come from
the coset permutation of the Sol port (`modularHeckeTransition`); the determinant `-1` elements of
`GL₂(ℤ)` are handled through `diag(-1,1)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped MatrixGroups
open Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.HeckeH1

namespace TernaryPeriodPolynomials.Spectral.LevelOneCosets

/-- `GL₂(ℤ) → GL₂(ℚ)`. -/
def integralEmbed : GL (Fin 2) ℤ →* GL (Fin 2) ℚ := GeneralLinearGroup.map (Int.castRingHom ℚ)

theorem integralEmbed_val (g : GL (Fin 2) ℤ) :
    (integralEmbed g : Matrix (Fin 2) (Fin 2) ℚ) = (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) :=
  rfl

theorem integralEmbed_injective : Function.Injective integralEmbed := by
  intro g h hgh
  apply Units.ext
  have hv : (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) =
      (h : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
    rw [← integralEmbed_val, ← integralEmbed_val, hgh]
  exact Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective hv

/-- `SL₂(ℤ) → GL₂(ℚ)`. -/
def modularEmbed : SL(2, ℤ) →* GL (Fin 2) ℚ := integralEmbed.comp SpecialLinearGroup.toGL

theorem modularEmbed_injective : Function.Injective modularEmbed := by
  intro g h hgh
  apply Subtype.ext
  have := integralEmbed_injective hgh
  exact congrArg (fun g : GL (Fin 2) ℤ => (g : Matrix (Fin 2) (Fin 2) ℤ)) this

variable (p : Nat.Primes)

/-- The integral Hecke matrices. -/
abbrev M : Option (Fin p.val) → Matrix (Fin 2) (Fin 2) ℤ := modularHeckeMatrix p

theorem rep_val (j : Option (Fin p.val)) :
    (binaryHeckeRepresentative p j : Matrix (Fin 2) (Fin 2) ℚ) = (M p j).map (Int.castRingHom ℚ) :=
  (modularHeckeMatrix_rational p j).symm

/-- The rational relation `ι(δ) = α_j ι(g) α_k⁻¹` is the integral relation `δ α_k = α_j g`. -/
theorem embed_eq_iff (δ g : GL (Fin 2) ℤ) (j k : Option (Fin p.val)) :
    integralEmbed δ = binaryHeckeRepresentative p j * integralEmbed g *
        (binaryHeckeRepresentative p k)⁻¹ ↔
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * M p k = M p j * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [eq_mul_inv_iff_mul_eq]
  constructor
  · intro h
    apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
    have hv := congrArg (fun x : GL (Fin 2) ℚ => (x : Matrix (Fin 2) (Fin 2) ℚ)) h
    simp only [Units.val_mul, integralEmbed_val, rep_val] at hv
    simpa only [Matrix.map_mul] using hv
  · intro h
    apply Units.ext
    simp only [Units.val_mul, integralEmbed_val, rep_val]
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]

theorem prime_two_le : 2 ≤ (p.val : ℤ) := by exact_mod_cast p.property.two_le

/-- Distinct indices give distinct cosets. -/
theorem disjoint_int (g : Matrix (Fin 2) (Fin 2) ℤ) (i j : Option (Fin p.val))
    (h : g * M p j = M p i) : i = j := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  have hp := prime_two_le p
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two] at e10 e11
      rw [e10] at e11
      simp only [zero_mul, zero_add] at e11
      have : (p.val : ℤ) ∣ 1 := ⟨g 1 1, by rw [← e11]; ring⟩
      have := Int.le_of_dvd one_pos this
      omega
  | some i =>
    cases j with
    | none =>
      simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two] at e00
      have : (p.val : ℤ) ∣ 1 := ⟨g 0 0, by rw [← e00]; ring⟩
      have := Int.le_of_dvd one_pos this
      omega
    | some j =>
      simp [M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
      rw [e00] at e01
      have hdvd : (p.val : ℤ) ∣ (i.val : ℤ) - j.val := ⟨g 0 1, by rw [← e01]; ring⟩
      have hi := i.isLt
      have hj := j.isLt
      have hzero := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
      congr 1
      apply Fin.ext
      omega

/-- The reflection `diag(-1,1)`. -/
def epsilon : GL (Fin 2) ℤ :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The involution `[[-1,1],[0,1]]`. -/
def epsilonShift : GL (Fin 2) ℤ :=
  ⟨!![-1, 1; 0, 1], !![-1, 1; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem epsilon_val : (epsilon : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 0; 0, 1] := rfl

theorem epsilonShift_val : (epsilonShift : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 1; 0, 1] := rfl

theorem epsilon_mul_self :
    (epsilon : Matrix (Fin 2) (Fin 2) ℤ) * (epsilon : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsilon_val, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α_i diag(-1,1) ∈ GL₂(ℤ) α_m`. -/
theorem epsilon_transition (i : Option (Fin p.val)) :
    ∃ m : Option (Fin p.val), ∃ D : GL (Fin 2) ℤ,
      M p i * (epsilon : Matrix (Fin 2) (Fin 2) ℤ) = (D : Matrix (Fin 2) (Fin 2) ℤ) * M p m := by
  cases i with
  | none =>
    refine ⟨none, epsilon, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [M, modularHeckeMatrix, epsilon_val, Matrix.mul_apply, Fin.sum_univ_two]
  | some i =>
    by_cases hi : i.val = 0
    · refine ⟨some i, epsilon, ?_⟩
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [M, modularHeckeMatrix, epsilon_val, Matrix.mul_apply, Fin.sum_univ_two, hi]
    · have hlt : p.val - i.val < p.val := by omega
      refine ⟨some ⟨p.val - i.val, hlt⟩, epsilonShift, ?_⟩
      have hle : i.val ≤ p.val := i.isLt.le
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [M, modularHeckeMatrix, epsilonShift_val, epsilon_val, Matrix.mul_apply, Fin.sum_univ_two,
          Nat.cast_sub hle]

theorem det_units (g : GL (Fin 2) ℤ) :
    (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℤ).det = -1 := by
  have h := Int.units_eq_one_or (GeneralLinearGroup.det g)
  rcases h with h | h
  · left
    have := congrArg Units.val h
    simpa [GeneralLinearGroup.val_det_apply] using this
  · right
    have := congrArg Units.val h
    simpa [GeneralLinearGroup.val_det_apply] using this

/-- **Existence of transitions in `GL₂(ℤ)`.** -/
theorem exists_transition (g : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    ∃ k : Option (Fin p.val), ∃ δ : GL (Fin 2) ℤ,
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * M p k = M p j * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
  rcases det_units g with hdet | hdet
  · let σ : SL(2, ℤ) := ⟨g, hdet⟩
    let i := (modularHeckePermutation p σ).symm j
    have h := modularHeckeTransition_matrix p σ i
    simp only [i, Equiv.apply_symm_apply] at h
    exact ⟨i, SpecialLinearGroup.toGL (modularHeckeTransition p σ i), h.symm⟩
  · have hdet' : ((g : Matrix (Fin 2) (Fin 2) ℤ) * epsilon).det = 1 := by
      rw [Matrix.det_mul, hdet]
      simp [epsilon_val, Matrix.det_fin_two]
    let σ : SL(2, ℤ) := ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) * epsilon, hdet'⟩
    obtain ⟨i, hi⟩ : ∃ i, modularHeckePermutation p σ i = j :=
      ⟨(modularHeckePermutation p σ).symm j, Equiv.apply_symm_apply _ _⟩
    have h := modularHeckeTransition_matrix p σ i
    rw [hi] at h
    obtain ⟨m, D, hD⟩ := epsilon_transition p i
    refine ⟨m, SpecialLinearGroup.toGL (modularHeckeTransition p σ i) * D, ?_⟩
    rw [Units.val_mul, Matrix.mul_assoc, ← hD, ← Matrix.mul_assoc]
    change (modularHeckeTransition p σ i : Matrix (Fin 2) (Fin 2) ℤ) * M p i * _ = _
    rw [← h]
    change M p j * ((g : Matrix (Fin 2) (Fin 2) ℤ) * epsilon) * epsilon = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, epsilon_mul_self, Matrix.mul_one]

/-- The next coset index. -/
def arithmeticNext (g : GL (Fin 2) ℤ) (j : Option (Fin p.val)) : Option (Fin p.val) :=
  (exists_transition p g j).choose

/-- The transition element. -/
def arithmeticDelta (g : GL (Fin 2) ℤ) (j : Option (Fin p.val)) : GL (Fin 2) ℤ :=
  (exists_transition p g j).choose_spec.choose

theorem arithmeticDelta_spec (g : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    (arithmeticDelta p g j : Matrix (Fin 2) (Fin 2) ℤ) * M p (arithmeticNext p g j) =
      M p j * (g : Matrix (Fin 2) (Fin 2) ℤ) :=
  (exists_transition p g j).choose_spec.choose_spec

/-- **The Hecke cosets of `GL₂(ℤ) diag(p,1) GL₂(ℤ)`.** -/
def arithmeticCosets : RightCosets integralEmbed where
  index := Option (Fin p.val)
  rep := binaryHeckeRepresentative p
  next := arithmeticNext p
  delta := arithmeticDelta p
  delta_spec g j := (embed_eq_iff p _ g j _).mpr (arithmeticDelta_spec p g j)
  disjoint i j g h := by
    have h' : integralEmbed g = binaryHeckeRepresentative p i * integralEmbed 1 *
        (binaryHeckeRepresentative p j)⁻¹ := by rw [map_one, mul_one]; exact h
    have := (embed_eq_iff p g 1 i j).mp h'
    rw [Units.val_one, Matrix.mul_one] at this
    exact disjoint_int p _ i j this

theorem arithmeticCosets_rep : (arithmeticCosets p).rep = binaryHeckeRepresentative p := rfl

/-- Transitions of determinant-one elements have determinant one. -/
theorem det_delta_of_det (g : GL (Fin 2) ℤ) (hg : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1)
    (j : Option (Fin p.val)) : (arithmeticDelta p g j : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  have h := congrArg Matrix.det (arithmeticDelta_spec p g j)
  rw [Matrix.det_mul, Matrix.det_mul, hg, mul_one, modularHeckeMatrix_det,
    modularHeckeMatrix_det] at h
  have hp : (p.val : ℤ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  exact mul_right_cancel₀ hp (h.trans (one_mul _).symm)

/-- The transition of an `SL₂(ℤ)` element, in `SL₂(ℤ)`. -/
def modularDelta (σ : SL(2, ℤ)) (j : Option (Fin p.val)) : SL(2, ℤ) :=
  ⟨arithmeticDelta p (SpecialLinearGroup.toGL σ) j, det_delta_of_det p _ σ.property j⟩

theorem toGL_modularDelta (σ : SL(2, ℤ)) (j : Option (Fin p.val)) :
    SpecialLinearGroup.toGL (modularDelta p σ j) = arithmeticDelta p (SpecialLinearGroup.toGL σ) j := by
  apply Units.ext
  rfl

/-- **The Hecke cosets of `SL₂(ℤ) diag(p,1) SL₂(ℤ)`**, with the same transitions as for `GL₂(ℤ)`. -/
def modularCosets : RightCosets modularEmbed where
  index := Option (Fin p.val)
  rep := binaryHeckeRepresentative p
  next σ := arithmeticNext p (SpecialLinearGroup.toGL σ)
  delta := modularDelta p
  delta_spec σ j := by
    change integralEmbed (SpecialLinearGroup.toGL (modularDelta p σ j)) = _
    rw [toGL_modularDelta]
    exact (arithmeticCosets p).delta_spec _ j
  disjoint i j σ h := (arithmeticCosets p).disjoint i j (SpecialLinearGroup.toGL σ) h

theorem arithmeticNext_one (j : Option (Fin p.val)) : arithmeticNext p 1 j = j := by
  symm
  apply (arithmeticCosets p).next_unique (h := 1)
  change integralEmbed 1 = binaryHeckeRepresentative p j * integralEmbed 1 *
    (binaryHeckeRepresentative p j)⁻¹
  simp

theorem arithmeticDelta_one (j : Option (Fin p.val)) : arithmeticDelta p 1 j = 1 := by
  symm
  apply (arithmeticCosets p).delta_unique integralEmbed_injective
  change integralEmbed 1 = binaryHeckeRepresentative p j * integralEmbed 1 *
    (binaryHeckeRepresentative p (arithmeticNext p 1 j))⁻¹
  rw [arithmeticNext_one]
  simp

end TernaryPeriodPolynomials.Spectral.LevelOneCosets
