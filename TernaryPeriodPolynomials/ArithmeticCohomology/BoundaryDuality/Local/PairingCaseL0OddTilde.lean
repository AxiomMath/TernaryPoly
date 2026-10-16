module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneCosetsBasic

@[expose] public section


/-!
# The involution `h ↦ δ h^{-T} δ⁻¹` of `GL₂(ℚ)` on the Hecke representatives of level three

Let `δ = diag(1, 3)` and `tilde h = δ (h⁻¹)ᵀ δ⁻¹`, an involutive automorphism of `GL₂(ℚ)` which
restricts to the cusp-exchanging involution `α` of `Γ₁'(3)`.  On the Hecke representatives
`α_j` of `Γ₁'(3) diag(1, p) Γ₁'(3)` it is `tilde α_j = p⁻¹ B_jᵀ`, where `B_j = p (δ⁻¹ α_j δ)⁻¹`
are the matrices of the good plane (`GoodPlaneCosetData.Bmat`).

* `invTQ`, `tilde`: the inverse transpose and the involution `tilde` as a group endomorphism;
* `tilde_heckeRep`: the matrix of `tilde α_j`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTilde

open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (del del_val del_inv_val)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneCosetData (Bmat BG BG_val)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
  (heckeRep heckeRep_none heckeRep_some signP signP_mul_self signP_cast levelEmbed levelEmbed_apply)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed_val)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel mem_binaryArithmeticLevel_iff)

/-- The inverse transpose of `GL₂(R)`. -/
def invTG {R : Type*} [CommRing R] (h : GL (Fin 2) R) : GL (Fin 2) R :=
  ⟨(h⁻¹ : GL (Fin 2) R).val.transpose, h.val.transpose, by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one], by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem invTG_val {R : Type*} [CommRing R] (h : GL (Fin 2) R) :
    (invTG h).val = ((h⁻¹ : GL (Fin 2) R).val).transpose := rfl

theorem invTG_mul {R : Type*} [CommRing R] (g h : GL (Fin 2) R) :
    invTG (g * h) = invTG g * invTG h := by
  apply Units.ext
  rw [Units.val_mul, invTG_val, invTG_val, invTG_val, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem invTG_one {R : Type*} [CommRing R] : invTG (1 : GL (Fin 2) R) = 1 := by
  apply Units.ext
  rw [invTG_val, inv_one, Units.val_one, Matrix.transpose_one]

/-- The inverse transpose commutes with change of coefficients. -/
theorem map_invTG {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (h : GL (Fin 2) R) :
    GeneralLinearGroup.map f (invTG h) = invTG (GeneralLinearGroup.map f h) := by
  have e : GeneralLinearGroup.map f (h⁻¹) = (GeneralLinearGroup.map f h)⁻¹ := map_inv _ h
  apply Units.ext
  ext i j
  have := congrArg (fun x : GL (Fin 2) S => x.val j i) e
  exact this

/-- The inverse transpose of `GL₂(ℚ)`. -/
abbrev invTQ (h : GL (Fin 2) ℚ) : GL (Fin 2) ℚ := invTG h

theorem invTQ_val (h : GL (Fin 2) ℚ) :
    (invTQ h).val = ((h⁻¹ : GL (Fin 2) ℚ).val).transpose := rfl

theorem invTQ_mul (g h : GL (Fin 2) ℚ) : invTQ (g * h) = invTQ g * invTQ h := invTG_mul g h

theorem invTQ_one : invTQ (1 : GL (Fin 2) ℚ) = 1 := invTG_one

/-- **The involution** `tilde h = δ (h⁻¹)ᵀ δ⁻¹` of `GL₂(ℚ)`. -/
def tilde : GL (Fin 2) ℚ →* GL (Fin 2) ℚ where
  toFun h := del * invTQ h * del⁻¹
  map_one' := by rw [invTQ_one]; group
  map_mul' g h := by
    rw [invTQ_mul]
    group

theorem tilde_apply (h : GL (Fin 2) ℚ) : tilde h = del * invTQ h * del⁻¹ := rfl

/-- The matrix of `tilde h` from a right inverse `Kt` of the matrix of `h` and its transpose. -/
theorem tilde_val_of_inv (h : GL (Fin 2) ℚ) (Kt K : Matrix (Fin 2) (Fin 2) ℚ)
    (hKt : Kt.transpose = K) (hH : h.val * Kt = 1) :
    (tilde h).val = del.val * K * (del⁻¹ : GL (Fin 2) ℚ).val := by
  have hinv : (h⁻¹ : GL (Fin 2) ℚ).val = Kt := by
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.inv_eq_right_inv hH
  rw [tilde_apply, Units.val_mul, Units.val_mul, invTQ_val, hinv, hKt]

section HeckeReps

variable (p : Nat.Primes)

theorem sign_sq : ((signP p : ℤ) : ℚ) * ((signP p : ℤ) : ℚ) = 1 := by
  exact_mod_cast signP_mul_self p

theorem p_ne : (p.val : ℚ) ≠ 0 := by exact_mod_cast p.property.ne_zero

/-- The matrix of `tilde α_∞`. -/
theorem tilde_heckeRep_none :
    (tilde (heckeRep p none)).val =
      !![((signP p : ℤ) : ℚ) / (p.val : ℚ), 0; 0, ((signP p : ℤ) : ℚ)] := by
  have hs := sign_sq p
  have hp := p_ne p
  rw [tilde_val_of_inv (heckeRep p none) !![((signP p : ℤ) : ℚ) / (p.val : ℚ), 0;
    0, ((signP p : ℤ) : ℚ)] !![((signP p : ℤ) : ℚ) / (p.val : ℚ), 0; 0, ((signP p : ℤ) : ℚ)]
    (by ext a b; fin_cases a <;> fin_cases b <;> rfl) (by
      rw [heckeRep_none]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> linear_combination hs),
    del_val, del_inv_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try field_simp)

/-- The matrix of `tilde α_i`. -/
theorem tilde_heckeRep_some (i : Fin p.val) :
    (tilde (heckeRep p (some i))).val =
      !![1, 0; -(3 * (i.val : ℚ)) / (p.val : ℚ), 1 / (p.val : ℚ)] := by
  have hp := p_ne p
  rw [tilde_val_of_inv (heckeRep p (some i)) !![1, -(i.val : ℚ) / (p.val : ℚ);
    0, 1 / (p.val : ℚ)] !![1, 0; -(i.val : ℚ) / (p.val : ℚ), 1 / (p.val : ℚ)]
    (by ext a b; fin_cases a <;> fin_cases b <;> rfl) (by
      rw [heckeRep_some]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      all_goals (first | (field_simp; done) | (field_simp; ring))),
    del_val, del_inv_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try field_simp)

end HeckeReps

section Perm

variable (p : Nat.Primes)

instance : NeZero p.val := ⟨p.property.ne_zero⟩

instance : Fact p.val.Prime := ⟨p.property⟩

/-- The residue `k ≡ -(3 i)⁻¹ (mod p)`. -/
def kOf (i : Fin p.val) : Fin p.val :=
  ⟨(-(3 * (i.val : ZMod p.val))⁻¹ : ZMod p.val).val, ZMod.val_lt _⟩

theorem kOf_cast (i : Fin p.val) :
    ((kOf p i).val : ZMod p.val) = -(3 * (i.val : ZMod p.val))⁻¹ := by
  unfold kOf
  exact ZMod.natCast_zmod_val _

theorem three_ne (hp3 : p.val ≠ 3) : (3 : ZMod p.val) ≠ 0 := by
  intro h
  have h3 : ((3 : ℕ) : ZMod p.val) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_three).mp h3)

theorem cast_ne_zero_of_ne (hp3 : p.val ≠ 3) (i : Fin p.val) (hi : i.val ≠ 0) :
    (3 * (i.val : ZMod p.val)) ≠ 0 := by
  refine mul_ne_zero (three_ne p hp3) ?_
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact hi (Nat.eq_zero_of_dvd_of_lt h i.2)

/-- `3 i k + 1 ≡ 0 (mod p)`. -/
theorem three_mul_kOf (hp3 : p.val ≠ 3) (i : Fin p.val) (hi : i.val ≠ 0) :
    ((3 * (i.val : ℤ) * (kOf p i).val + 1 : ℤ) : ZMod p.val) = 0 := by
  have h := cast_ne_zero_of_ne p hp3 i hi
  push_cast
  erw [show (3 : ZMod p.val) * (i.val : ZMod p.val) * ((kOf p i).val : ZMod p.val) =
    (3 * (i.val : ZMod p.val)) * ((kOf p i).val : ZMod p.val) by ring, kOf_cast, mul_neg,
    mul_inv_cancel₀ h]
  ring

theorem kOf_ne_zero (hp3 : p.val ≠ 3) (i : Fin p.val) (hi : i.val ≠ 0) : (kOf p i).val ≠ 0 := by
  intro h0
  have h1 := three_mul_kOf p hp3 i hi
  rw [h0] at h1
  simp at h1

theorem kOf_kOf (hp3 : p.val ≠ 3) (i : Fin p.val) (hi : i.val ≠ 0) : kOf p (kOf p i) = i := by
  have hk := kOf_ne_zero p hp3 i hi
  apply Fin.ext
  have h3 := cast_ne_zero_of_ne p hp3 i hi
  have h3' := three_ne p hp3
  have hi0 : (i.val : ZMod p.val) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hi (Nat.eq_zero_of_dvd_of_lt h i.2)
  have e : ((kOf p (kOf p i)).val : ZMod p.val) = (i.val : ZMod p.val) := by
    rw [kOf_cast, kOf_cast]
    field_simp
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp e |> fun h => by
    rw [Nat.mod_eq_of_lt (kOf p (kOf p i)).2, Nat.mod_eq_of_lt i.2] at h
    exact h

/-- The index permutation `π`: `∞ ↔ 0` and `i ↦ -(3 i)⁻¹ (mod p)`. -/
def piFun : Option (Fin p.val) → Option (Fin p.val)
  | none => some ⟨0, p.property.pos⟩
  | some i => if i.val = 0 then none else some (kOf p i)

theorem piFun_involutive (hp3 : p.val ≠ 3) : Function.Involutive (piFun p) := by
  intro j
  cases j with
  | none => simp [piFun]
  | some i =>
    by_cases hi : i.val = 0
    · simp [piFun, hi]
      exact Fin.ext hi.symm
    · have hk := kOf_ne_zero p hp3 i hi
      simp [piFun, hi, hk, kOf_kOf p hp3 i hi]

/-- The permutation `π` of the Hecke cosets. -/
def piEquiv (hp3 : p.val ≠ 3) : Equiv.Perm (Option (Fin p.val)) :=
  (piFun_involutive p hp3).toPerm _

end Perm

section CosetData

variable (p : Nat.Primes)

/-- The central element `z = ε_p p⁻¹ · 1` of `GL₂(ℚ)`. -/
def zUnit : GL (Fin 2) ℚ :=
  ⟨(((signP p : ℤ) : ℚ) / (p.val : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ),
    (((signP p : ℤ) : ℚ) * (p.val : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ), by
    have h : (((signP p : ℤ) : ℚ) / (p.val : ℚ)) * (((signP p : ℤ) : ℚ) * (p.val : ℚ)) = 1 := by
      have hs := sign_sq p
      have hp := p_ne p
      field_simp
      linear_combination hs
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_one, smul_smul, h, one_smul], by
    have h : (((signP p : ℤ) : ℚ) * (p.val : ℚ)) * (((signP p : ℤ) : ℚ) / (p.val : ℚ)) = 1 := by
      have hs := sign_sq p
      have hp := p_ne p
      field_simp
      linear_combination hs
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_one, smul_smul, h, one_smul]⟩

theorem zUnit_val : (zUnit p).val =
    (((signP p : ℤ) : ℚ) / (p.val : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := rfl

theorem zUnit_comm (x : GL (Fin 2) ℚ) : zUnit p * x = x * zUnit p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, zUnit_val, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

/-- The element of `Γ₁'(3)` with matrix `[[a, b], [c, d]]` of determinant one. -/
def mkLevel (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : ((c : ℤ) : ZMod 3) = 0)
    (hd : ((d : ℤ) : ZMod 3) = 1) : binaryArithmeticLevel :=
  ⟨⟨!![a, b; c, d], !![d, -b; -c, a], by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination hdet, by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination hdet⟩, by
    apply (mem_binaryArithmeticLevel_iff _).mpr
    intro column
    fin_cases column
    · simpa using hc
    · simpa using hd⟩

theorem levelEmbed_mkLevel_val (a b c d : ℤ) (hdet : a * d - b * c = 1)
    (hc : ((c : ℤ) : ZMod 3) = 0) (hd : ((d : ℤ) : ZMod 3) = 1) :
    (levelEmbed (mkLevel a b c d hdet hc hd)).val =
      !![(a : ℚ), (b : ℚ); (c : ℚ), (d : ℚ)] := by
  rw [levelEmbed_apply, integralEmbed_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkLevel]

end CosetData

section Compat

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

theorem piEquiv_none : piEquiv p hp3 none = some ⟨0, p.property.pos⟩ := rfl

theorem piEquiv_some_zero (i : Fin p.val) (hi : i.val = 0) : piEquiv p hp3 (some i) = none := by
  change piFun p (some i) = none
  simp [piFun, hi]

theorem piEquiv_some (i : Fin p.val) (hi : i.val ≠ 0) :
    piEquiv p hp3 (some i) = some (kOf p i) := by
  change piFun p (some i) = some (kOf p i)
  simp [piFun, hi]

theorem tilde_heckeRep_eq_none :
    ∃ γ : binaryArithmeticLevel,
      tilde (heckeRep p none) = zUnit p * levelEmbed γ * heckeRep p (piEquiv p hp3 none) := by
  refine ⟨1, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, zUnit_val, map_one, Units.val_one, tilde_heckeRep_none,
    piEquiv_none, heckeRep_some]
  have hp := p_ne p
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem tilde_heckeRep_eq_zero (i : Fin p.val) (hi : i.val = 0) :
    ∃ γ : binaryArithmeticLevel,
      tilde (heckeRep p (some i)) = zUnit p * levelEmbed γ * heckeRep p (piEquiv p hp3 (some i)) := by
  refine ⟨1, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, zUnit_val, map_one, Units.val_one, tilde_heckeRep_some,
    piEquiv_some_zero p hp3 i hi, heckeRep_none]
  have hp := p_ne p
  have hs := sign_sq p
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hi]
  all_goals (try field_simp)
  all_goals (try linear_combination (-1 : ℚ) * hs)

theorem tilde_heckeRep_eq_ne (i : Fin p.val) (hi : i.val ≠ 0) :
    ∃ γ : binaryArithmeticLevel,
      tilde (heckeRep p (some i)) = zUnit p * levelEmbed γ * heckeRep p (piEquiv p hp3 (some i)) := by
  have hdvd : (p.val : ℤ) ∣ 3 * (i.val : ℤ) * ((kOf p i).val : ℤ) + 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.val).mp (three_mul_kOf p hp3 i hi)
  obtain ⟨m, hm⟩ := hdvd
  have hεε : (signP p : ℤ) * (signP p : ℤ) = 1 := signP_mul_self p
  have hdet : ((signP p : ℤ) * p.val) * ((signP p : ℤ) * m) -
      (-((signP p : ℤ) * ((kOf p i).val : ℤ))) * (-(3 * (signP p : ℤ) * (i.val : ℤ))) = 1 := by
    linear_combination (-((signP p : ℤ) * (signP p : ℤ))) * hm + hεε
  have h3 : (3 : ZMod 3) = 0 := by decide
  have hc : ((-(3 * (signP p : ℤ) * (i.val : ℤ)) : ℤ) : ZMod 3) = 0 := by
    push_cast
    rw [h3]
    ring
  have hd : (((signP p : ℤ) * m : ℤ) : ZMod 3) = 1 := by
    have hεc := signP_cast p hp3
    have hmz := congrArg (Int.cast : ℤ → ZMod 3) hm
    push_cast at hmz
    push_cast
    rw [hεc]
    erw [h3, zero_mul, zero_mul, zero_add] at hmz
    exact hmz.symm
  refine ⟨mkLevel ((signP p : ℤ) * p.val) (-((signP p : ℤ) * ((kOf p i).val : ℤ)))
    (-(3 * (signP p : ℤ) * (i.val : ℤ))) ((signP p : ℤ) * m) hdet hc hd, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, zUnit_val, levelEmbed_mkLevel_val, tilde_heckeRep_some,
    piEquiv_some p hp3 i hi, heckeRep_some]
  have hp := p_ne p
  have hs := sign_sq p
  have hmq : (3 : ℚ) * (i.val : ℚ) * ((kOf p i).val : ℚ) + 1 = (p.val : ℚ) * (m : ℚ) := by
    exact_mod_cast hm
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination (-1 : ℚ) * hs | linear_combination hs |
    linear_combination (-1 : ℚ) * hs + (((signP p : ℤ) : ℚ) ^ 2) * hmq)

/-- **The involution permutes the Hecke cosets**: there are `γ_j ∈ Γ₁'(3)` with
`tilde α_j = z · γ_j · α_{π j}`. -/
theorem exists_coset_data :
    ∃ γ : Option (Fin p.val) → binaryArithmeticLevel, ∀ j,
      tilde (heckeRep p j) = zUnit p * levelEmbed (γ j) * heckeRep p (piEquiv p hp3 j) := by
  have h : ∀ j : Option (Fin p.val), ∃ g : binaryArithmeticLevel,
      tilde (heckeRep p j) = zUnit p * levelEmbed g * heckeRep p (piEquiv p hp3 j) := by
    intro j
    cases j with
    | none => exact tilde_heckeRep_eq_none p hp3
    | some i =>
      by_cases hi : i.val = 0
      · exact tilde_heckeRep_eq_zero p hp3 i hi
      · exact tilde_heckeRep_eq_ne p hp3 i hi
  choose γ hγ using h
  exact ⟨γ, hγ⟩

end Compat

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTilde

end
