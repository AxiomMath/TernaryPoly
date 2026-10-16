module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsTransversal

@[expose] public section


/-!
# Conjugation by the Fricke element `g' = α₀⁻¹ s` on `Γ₁'(3) ∩ Γ⁰(p)`

With `s = sF`, `α₀ = diag(1, p)` the element `g' = gP = α₀⁻¹ s ∈ GL₂(ℚ)` has the integral inverse
`g'⁻¹ = gPinv = s⁻¹ α₀ = [[-p, p ε], [1 - ε p, p]]`, `(g'⁻¹)² = p ε · 1`.  Conjugation by `g'`
preserves the stabilizer `H = Γ₁'(3) ∩ Γ⁰(p)` of the base coset, and is an involution of `H`:

* `rep_mul_gP : α₀ g' = s` (the hypothesis `hs` of the generic Fricke lemma, with `s = sF`);
* `gP_sq_central : g' g' k = k g' g'` for all `k ∈ GL₂(ℚ)`;
* `fricke : H →* H` with `levelEmbed (fricke h) = g' (levelEmbed h) g'⁻¹` (`levelEmbed_fricke`) and
  `fricke (fricke h) = h` (`fricke_fricke`);
* `fricke_of_conj`: if `α₀ X = Y α₀` then `fricke X = s⁻¹ Y s`; in particular
  `fricke (T^p) = s⁻¹ T s` and `fricke L = s⁻¹ L^p s` (`fricke_upper`, `fricke_lower`).

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

section Elements

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The integral matrix `g'⁻¹ = [[-p, p ε], [1 - ε p, p]]`. -/
def gInvInt : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-(p.val : ℤ), p.val * eps p; 1 - eps p * p.val, p.val]

include hp3 in
/-- **`g'⁻¹ = s⁻¹ α₀`**, an integral matrix of `GL₂(ℚ)`. -/
def gPinv : GL (Fin 2) ℚ := levelEmbed (sInv p hp3) * heckeRep p (baseIdx p)

/-- **The Fricke element `g' = α₀⁻¹ s ∈ GL₂(ℚ)`.** -/
def gP : GL (Fin 2) ℚ := (gPinv p hp3)⁻¹

theorem gP_inv : (gP p hp3)⁻¹ = gPinv p hp3 := inv_inv _

theorem gPinv_val : ((gPinv p hp3 : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
    (gInvInt p).map (Int.castRingHom ℚ) := by
  rw [gPinv, Units.val_mul, levelEmbed_apply, integralEmbed_val, heckeRep_val, N_baseIdx,
    sInv_val, ← Matrix.map_mul, Matrix.mul_fin_two]
  refine congrArg (fun M => Matrix.map M (Int.castRingHom ℚ)) ?_
  rw [gInvInt]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

/-- `α₀ g' = s`. -/
theorem rep_mul_gP : heckeRep p (baseIdx p) * gP p hp3 = levelEmbed (sF p hp3) := by
  rw [gP, gPinv, _root_.mul_inv_rev, mul_inv_cancel_left, ← map_inv, ← sF_eq_inv]

theorem gInvInt_sq : gInvInt p * gInvInt p =
    !![(p.val : ℤ) * eps p, 0; 0, (p.val : ℤ) * eps p] := by
  have he := eps_mul_self p
  rw [gInvInt, Matrix.mul_fin_two]
  exact mat2_eq (by linear_combination (-(p.val : ℤ) ^ 2) * he) (by ring) (by ring)
    (by linear_combination (-(p.val : ℤ) ^ 2) * he)

theorem gPinv_sq_val : ((gPinv p hp3 * gPinv p hp3 : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
    (((p.val : ℤ) * eps p : ℤ) : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  rw [Units.val_mul, gPinv_val, ← Matrix.map_mul, gInvInt_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **`(g'⁻¹)²` is central.** -/
theorem gPinv_sq_central (k : GL (Fin 2) ℚ) :
    gPinv p hp3 * gPinv p hp3 * k = k * (gPinv p hp3 * gPinv p hp3) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, ← Units.val_mul,
    gPinv_sq_val, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- **`g'²` is central** (hypothesis `hcent` of the generic Fricke lemma). -/
theorem gP_sq_central (k : GL (Fin 2) ℚ) : gP p hp3 * gP p hp3 * k = k * (gP p hp3 * gP p hp3) := by
  have h : Commute (gPinv p hp3 * gPinv p hp3) k := gPinv_sq_central p hp3 k
  have h' := h.inv_left
  rw [_root_.mul_inv_rev] at h'
  exact h'

/-- Conjugation by `g'` equals conjugation by `g'⁻¹`. -/
theorem conj_gP_eq (X : GL (Fin 2) ℚ) : gP p hp3 * X * (gP p hp3)⁻¹ = (gP p hp3)⁻¹ * X * gP p hp3 := by
  calc gP p hp3 * X * (gP p hp3)⁻¹
      = (gP p hp3)⁻¹ * (gP p hp3 * gP p hp3 * X) * (gP p hp3)⁻¹ := by group
    _ = (gP p hp3)⁻¹ * (X * (gP p hp3 * gP p hp3)) * (gP p hp3)⁻¹ := by
        rw [gP_sq_central p hp3 X]
    _ = (gP p hp3)⁻¹ * X * gP p hp3 := by group

end Elements

section Conj

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The quotient `b' = b / p` of the upper right entry. -/
def bQuot (h : binaryArithmeticLevel) : ℤ := h.val.val 0 1 / p.val

theorem bQuot_spec (h : binaryArithmeticLevel) (hh : (p.val : ℤ) ∣ h.val.val 0 1) :
    (p.val : ℤ) * bQuot p h = h.val.val 0 1 := Int.mul_ediv_cancel' hh

include hp3 in
theorem fC_cast (a bp c d : ℤ) (hc : (c : ZMod 3) = 0) (hd : (d : ZMod 3) = 1) :
    ((fC (p.val : ℤ) (eps p) a bp c d : ℤ) : ZMod 3) = 0 := by
  unfold fC
  push_cast
  rw [eps_cast p hp3, hc, hd]
  linear_combination ((p.val : ZMod 3) * bp) * cast_mul_self p hp3

include hp3 in
theorem fD_cast (a bp c d : ℤ) (hc : (c : ZMod 3) = 0) (hd : (d : ZMod 3) = 1) :
    ((fD (p.val : ℤ) (eps p) a bp c d : ℤ) : ZMod 3) = 1 := by
  unfold fD
  push_cast
  rw [eps_cast p hp3, hc, hd]
  linear_combination (1 - (a : ZMod 3)) * cast_mul_self p hp3

theorem frickeEntries_det (h : binaryArithmeticLevel) (hh : (p.val : ℤ) ∣ h.val.val 0 1) :
    fA (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0) (h.val.val 1 1) *
        fD (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0) (h.val.val 1 1) -
      ((p.val : ℤ) * fB (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0)
        (h.val.val 1 1)) *
        fC (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0) (h.val.val 1 1) =
      (h.val.val : Matrix (Fin 2) (Fin 2) ℤ).det := by
  have key := fricke_det (p := (p.val : ℤ)) (e := eps p) (a := h.val.val 0 0)
    (bp := bQuot p h) (c := h.val.val 1 0) (d := h.val.val 1 1) (eps_mul_self p)
  have hb := bQuot_spec p h hh
  rw [Matrix.det_fin_two]
  linear_combination key - (h.val.val 1 0) * hb

include hp3 in
/-- **The Fricke conjugate** of an element of `Γ₁'(3)` with `p ∣ b`:
`[[a, p b'], [c, d]] ↦ [[A, p B], [C, D]]`. -/
def frickeVal (h : binaryArithmeticLevel) (hh : (p.val : ℤ) ∣ h.val.val 0 1) :
    binaryArithmeticLevel :=
  matLevel (fA (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0) (h.val.val 1 1))
    ((p.val : ℤ) * fB (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0)
      (h.val.val 1 1))
    (fC (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0) (h.val.val 1 1))
    (fD (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0) (h.val.val 1 1))
    (h.val.val.det) (det_mul_self h.val) (frickeEntries_det p h hh)
    (fC_cast p hp3 _ _ _ _ (level_row h).1 (level_row h).2)
    (fD_cast p hp3 _ _ _ _ (level_row h).1 (level_row h).2)

theorem frickeVal_val (h : binaryArithmeticLevel) (hh : (p.val : ℤ) ∣ h.val.val 0 1) :
    (((frickeVal p hp3 h hh).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![fA (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0) (h.val.val 1 1),
        (p.val : ℤ) * fB (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0)
          (h.val.val 1 1);
        fC (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0) (h.val.val 1 1),
        fD (p.val : ℤ) (eps p) (h.val.val 0 0) (bQuot p h) (h.val.val 1 0) (h.val.val 1 1)] := rfl

/-- **Conjugation formula**: `g'⁻¹ · fricke h = h · g'⁻¹` (an identity of integral matrices). -/
theorem gPinv_mul_frickeVal (h : binaryArithmeticLevel) (hh : (p.val : ℤ) ∣ h.val.val 0 1) :
    gPinv p hp3 * levelEmbed (frickeVal p hp3 h hh) = levelEmbed h * gPinv p hp3 := by
  have hE : (h.val.val : Matrix (Fin 2) (Fin 2) ℤ) =
      !![h.val.val 0 0, (p.val : ℤ) * bQuot p h; h.val.val 1 0, h.val.val 1 1] := by
    have := Matrix.eta_fin_two (h.val.val : Matrix (Fin 2) (Fin 2) ℤ)
    rwa [← bQuot_spec p h hh] at this
  have key : gInvInt p * (((frickeVal p hp3 h hh).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      (h.val.val : Matrix (Fin 2) (Fin 2) ℤ) * gInvInt p := by
    have hc := fricke_conj (p := (p.val : ℤ)) (e := eps p) (a := h.val.val 0 0)
      (bp := bQuot p h) (c := h.val.val 1 0) (d := h.val.val 1 1) (eps_mul_self p)
    rw [frickeVal_val, gInvInt, hc, ← hE]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, gPinv_val, levelEmbed_apply, levelEmbed_apply,
    integralEmbed_val, integralEmbed_val, ← Matrix.map_mul, ← Matrix.map_mul, key]

/-- The stabilizer of the base coset. -/
abbrev stabH : Subgroup binaryArithmeticLevel := AdjCore.stab (levelCosets p hp3) (baseIdx p)

theorem mem_stabH_iff (h : binaryArithmeticLevel) :
    h ∈ stabH p hp3 ↔ (p.val : ℤ) ∣ h.val.val 0 1 := mem_stab_iff p hp3 h

theorem dvd_of_mem_stabH {h : binaryArithmeticLevel} (hh : h ∈ stabH p hp3) :
    (p.val : ℤ) ∣ h.val.val 0 1 := (mem_stabH_iff p hp3 h).mp hh

/-- The Fricke conjugate of an element of the stabilizer. -/
def frickeElt (h : stabH p hp3) : binaryArithmeticLevel :=
  frickeVal p hp3 h.1 (dvd_of_mem_stabH p hp3 h.2)

theorem frickeElt_mem (h : stabH p hp3) : frickeElt p hp3 h ∈ stabH p hp3 :=
  (mem_stabH_iff p hp3 _).mpr
    ⟨fB (p.val : ℤ) (eps p) (h.1.val.val 0 0) (bQuot p h.1) (h.1.val.val 1 0) (h.1.val.val 1 1),
      rfl⟩

/-- **The Fricke conjugation is conjugation by `g'`**: `embed (fricke h) = g' · embed h · g'⁻¹`. -/
theorem levelEmbed_frickeElt (h : stabH p hp3) :
    levelEmbed (frickeElt p hp3 h) = gP p hp3 * levelEmbed h.1 * (gP p hp3)⁻¹ := by
  have key := gPinv_mul_frickeVal p hp3 h.1 (dvd_of_mem_stabH p hp3 h.2)
  rw [gP_inv]
  have e : gP p hp3 * levelEmbed h.1 * gPinv p hp3 =
      gP p hp3 * (levelEmbed h.1 * gPinv p hp3) := mul_assoc _ _ _
  rw [e, ← key, gP]
  exact (inv_mul_cancel_left _ _).symm

/-- **The Fricke involution** `h ↦ g' h g'⁻¹` of the stabilizer `Γ₁'(3) ∩ Γ⁰(p)` of the base coset. -/
def fricke : stabH p hp3 →* stabH p hp3 :=
  MonoidHom.mk' (fun h => ⟨frickeElt p hp3 h, frickeElt_mem p hp3 h⟩) (by
    intro x y
    apply Subtype.ext
    apply levelEmbed_injective
    show levelEmbed (frickeElt p hp3 (x * y)) =
      levelEmbed (frickeElt p hp3 x * frickeElt p hp3 y)
    rw [map_mul, levelEmbed_frickeElt, levelEmbed_frickeElt, levelEmbed_frickeElt,
      Subgroup.coe_mul, map_mul]
    group)

theorem fricke_val (h : stabH p hp3) : (fricke p hp3 h).1 = frickeElt p hp3 h := rfl

/-- **The conjugation property** `hc`. -/
theorem levelEmbed_fricke (h : stabH p hp3) :
    levelEmbed (fricke p hp3 h).1 = gP p hp3 * levelEmbed h.1 * (gP p hp3)⁻¹ :=
  levelEmbed_frickeElt p hp3 h

/-- **The Fricke map is an involution** (`hcc`). -/
theorem fricke_fricke (h : stabH p hp3) : fricke p hp3 (fricke p hp3 h) = h := by
  apply Subtype.ext
  apply levelEmbed_injective
  rw [levelEmbed_fricke, levelEmbed_fricke]
  have hc := gP_sq_central p hp3 (levelEmbed h.1)
  calc gP p hp3 * (gP p hp3 * levelEmbed h.1 * (gP p hp3)⁻¹) * (gP p hp3)⁻¹
      = (gP p hp3 * gP p hp3 * levelEmbed h.1) * ((gP p hp3)⁻¹ * (gP p hp3)⁻¹) := by group
    _ = (levelEmbed h.1 * (gP p hp3 * gP p hp3)) * ((gP p hp3)⁻¹ * (gP p hp3)⁻¹) := by rw [hc]
    _ = levelEmbed h.1 := by group

end Conj

section Cusps

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- If `α₀ X = Y α₀` then `fricke X = s⁻¹ Y s`. -/
theorem fricke_of_conj (X : stabH p hp3) (Y : binaryArithmeticLevel)
    (hrel : N p (baseIdx p) * (((X.1).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((Y.val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)) * N p (baseIdx p)) :
    (fricke p hp3 X).1 = sInv p hp3 * Y * sF p hp3 := by
  apply levelEmbed_injective
  have hrep : heckeRep p (baseIdx p) * levelEmbed X.1 = levelEmbed Y * heckeRep p (baseIdx p) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, heckeRep_val, levelEmbed_apply, levelEmbed_apply,
      integralEmbed_val, integralEmbed_val, ← Matrix.map_mul, ← Matrix.map_mul, hrel]
  have hsF : (levelEmbed (sInv p hp3))⁻¹ = levelEmbed (sF p hp3) := by
    rw [← map_inv, ← sF_eq_inv]
  rw [levelEmbed_fricke, conj_gP_eq, gP_inv, gP, gPinv, _root_.mul_inv_rev, hsF, map_mul, map_mul]
  calc levelEmbed (sInv p hp3) * heckeRep p (baseIdx p) * levelEmbed X.1 *
        ((heckeRep p (baseIdx p))⁻¹ * levelEmbed (sF p hp3))
      = levelEmbed (sInv p hp3) * (heckeRep p (baseIdx p) * levelEmbed X.1) *
        ((heckeRep p (baseIdx p))⁻¹ * levelEmbed (sF p hp3)) := by group
    _ = levelEmbed (sInv p hp3) * (levelEmbed Y * heckeRep p (baseIdx p)) *
        ((heckeRep p (baseIdx p))⁻¹ * levelEmbed (sF p hp3)) := by rw [hrep]
    _ = levelEmbed (sInv p hp3) * levelEmbed Y * levelEmbed (sF p hp3) := by group

theorem upper_mem_stabH : upper (p.val : ℤ) ∈ stabH p hp3 :=
  (mem_stabH_iff p hp3 _).mpr (by
    show (p.val : ℤ) ∣ (p.val : ℤ)
    exact dvd_refl _)

theorem lower_mem_stabH (n : ℤ) : lower n ∈ stabH p hp3 :=
  (mem_stabH_iff p hp3 _).mpr (by
    show (p.val : ℤ) ∣ 0
    exact dvd_zero _)

/-- **The Fricke involution sends the cusp generator `T^p` to the transit `s⁻¹ T s`.** -/
theorem fricke_upper :
    (fricke p hp3 ⟨upper (p.val : ℤ), upper_mem_stabH p hp3⟩).1 =
      sInv p hp3 * upper 1 * sF p hp3 := by
  apply fricke_of_conj
  show N p (baseIdx p) * (((upper (p.val : ℤ)).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
    (((upper 1).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * N p (baseIdx p)
  rw [N_baseIdx, upper_val, upper_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

/-- **The Fricke involution sends the cusp generator `L` to the transit `s⁻¹ L^p s`.** -/
theorem fricke_lower :
    (fricke p hp3 ⟨lower 1, lower_mem_stabH p hp3 1⟩).1 =
      sInv p hp3 * lower (p.val : ℤ) * sF p hp3 := by
  apply fricke_of_conj
  show N p (baseIdx p) * (((lower 1).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
    (((lower (p.val : ℤ)).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * N p (baseIdx p)
  rw [N_baseIdx, lower_val, lower_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

end Cusps

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
