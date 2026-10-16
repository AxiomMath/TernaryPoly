module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineCosets

@[expose] public section


/-!
# Group law and transitions of the bad-line cosets

The group `ΛB` in the coordinates `Mel x e A = R(x, e, A)` (`x ∈ ℤ²`, `e = ±1`, `A ∈ Γ₁'(3)`):
`Mel x e A * Mel x' e' A' = Mel (x + e x' A⁻¹) (e e') (A A')` (`Mel_mul`), with the radical elements
`Ux x = Mel x 1 1` and the Levi elements `Lm A = Mel 0 1 A`, so that `Lm A * Ux y = Ux (y A⁻¹) * Lm A`
(`Lm_Ux`).

For the local correspondence `badLineCosets p`, the transitions of the elements `Ux u`, `Lm A` and
general `Mel x e A` are computed from `levi_mul` and `rad_mul` of `BadLineCosets`:

* Levi index `j`: `next (Mel x e A) j = levelNext A j`, `δ = Mel (x B_j) e (levelDelta A j)`;
* radical index `c`: `next = radNext x e A c`, `δ = Mel (radDelta x e A c) e A`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineTransitions

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets AmbientHecke LocalHecke
open GoodLineCosets (cvec crep cq)
open TernaryPeriodPolynomials.Spectral.HeckeH1

/-! ### The group law -/

theorem Mel_congr {x x' : ℤ × ℤ} {e e' : ℤˣ} {A A' : binaryArithmeticLevel} (hx : x = x')
    (he : e = e') (hA : A = A') : Mel x e A = Mel x' e' A' := by
  subst hx he hA
  rfl

theorem ivmul_zero (A : Matrix (Fin 2) (Fin 2) ℤ) : ivmul 0 A = 0 := by
  simp [ivmul]

theorem Mel_mul (x x' : ℤ × ℤ) (e e' : ℤˣ) (A A' : binaryArithmeticLevel) :
    Mel x e A * Mel x' e' A' =
      Mel (x + (e : ℤ) • ivmul x' (A.val⁻¹ : GL (Fin 2) ℤ).val) (e * e') (A * A') := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Mel_val, Mel_val, Mel_val, R_mul]
  refine R_congr ?_ ?_ ?_
  · rw [levelEmbed_apply, ← map_inv, vmul_integralEmbed, ucast_val, icast_add, icast_smul_int]
  · exact (map_mul ucast e e').symm
  · exact (map_mul levelEmbed A A').symm

/-- The radical element `Ux x = R(x, 1, 1)`. -/
def Ux (x : ℤ × ℤ) : ΛB := Mel x 1 1

/-- The Levi element `Lm A = R(0, 1, A)`. -/
def Lm (A : binaryArithmeticLevel) : ΛB := Mel 0 1 A

theorem Ux_mul (x y : ℤ × ℤ) : Ux x * Ux y = Ux (x + y) := by
  rw [Ux, Ux, Ux, Mel_mul]
  refine Mel_congr ?_ ?_ ?_
  · simp [ivmul_one]
  · simp
  · simp

theorem Lm_mul (A B : binaryArithmeticLevel) : Lm A * Lm B = Lm (A * B) := by
  rw [Lm, Lm, Lm, Mel_mul]
  refine Mel_congr ?_ ?_ ?_
  · simp [ivmul_zero]
  · simp
  · rfl

theorem Lm_Ux (A : binaryArithmeticLevel) (y : ℤ × ℤ) :
    Lm A * Ux y = Ux (ivmul y (A.val⁻¹ : GL (Fin 2) ℤ).val) * Lm A := by
  rw [Lm, Ux, Ux, Mel_mul, Mel_mul]
  refine Mel_congr ?_ ?_ ?_
  · simp [ivmul_zero]
  · simp
  · simp

theorem Mel_eq (x : ℤ × ℤ) (A : binaryArithmeticLevel) : Mel x 1 A = Ux x * Lm A := by
  rw [Ux, Lm, Mel_mul]
  refine Mel_congr ?_ ?_ ?_
  · simp [ivmul_zero]
  · simp
  · simp

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-! ### The cosets of `Γ₁'(3)` at the identity -/

theorem levelNext_one (j : Option (Fin p.val)) :
    levelNext p hp3 1 j = j := by
  symm
  apply (levelCosets p hp3).next_unique (h := 1)
  change levelEmbed 1 = heckeRep p j * levelEmbed 1 * (heckeRep p j)⁻¹
  simp

theorem levelDelta_one (j : Option (Fin p.val)) :
    levelDelta p hp3 1 j = 1 := by
  symm
  apply (levelCosets p hp3).delta_unique levelEmbed_injective
  change levelEmbed 1 = heckeRep p j * levelEmbed 1 * (heckeRep p (levelNext p hp3 1 j))⁻¹
  rw [levelNext_one]
  simp

/-! ### The transitions of the explicit correspondence -/

/-- The representative with index `i`. -/
def toRep (i : BIdx p) : (badLineCosets p hp3).representatives :=
  ⟨rExpl p i, rExpl_mem p hp3 i⟩

theorem toRep_bijective : Function.Bijective (toRep p hp3) := by
  constructor
  · intro i i' h
    exact rExpl_injective p (congrArg Subtype.val h)
  · rintro ⟨s, hs⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨i, rfl⟩

theorem repsB_not_mem : ∀ s ∈ (badLineCosets p hp3).representatives, s ∉ ΛB := by
  intro s hs
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
  exact rExpl_not_mem p i

theorem conj_eq_of_mul {G : Type*} [Group G] (s g t d : G) (h : s * d = g * t) :
    s⁻¹ * g * t = d := by
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem next_inl (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    nextRep (badLineCosets p hp3) (Mel x e A) (toRep p hp3 (.inl j)) =
      toRep p hp3 (.inl (levelNext p hp3 A j)) := by
  apply nextRep_unique
  change (rExpl p (.inl j))⁻¹ * (Mel x e A : RationalGL3) * rExpl p (.inl (levelNext p hp3 A j))
    ∈ ΛB
  have h := conj_eq_of_mul (rExpl p (.inl j)) (Mel x e A : RationalGL3)
    (rExpl p (.inl (levelNext p hp3 A j))) _ (levi_mul p hp3 x e A j)
  rw [h]
  exact (Mel _ _ _).property

theorem delta_inl (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    deltaRep (badLineCosets p hp3) (Mel x e A) (toRep p hp3 (.inl j)) =
      Mel (ivmul x (Bl p j)) e (levelDelta p hp3 A j) := by
  apply Subtype.ext
  rw [deltaRep_val, next_inl]
  exact conj_eq_of_mul _ _ _ _ (levi_mul p hp3 x e A j)

theorem next_inr (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    nextRep (badLineCosets p hp3) (Mel x e A) (toRep p hp3 (.inr c)) =
      toRep p hp3 (.inr (radNext p x e A c)) := by
  apply nextRep_unique
  change (rExpl p (.inr c))⁻¹ * (Mel x e A : RationalGL3) * rExpl p (.inr (radNext p x e A c))
    ∈ ΛB
  have h := conj_eq_of_mul (rExpl p (.inr c)) (Mel x e A : RationalGL3)
    (rExpl p (.inr (radNext p x e A c))) _ (rad_mul p x e A c)
  rw [h]
  exact (Mel _ _ _).property

theorem delta_inr (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    deltaRep (badLineCosets p hp3) (Mel x e A) (toRep p hp3 (.inr c)) =
      Mel (radDelta p x e A c) e A := by
  apply Subtype.ext
  rw [deltaRep_val, next_inr]
  exact conj_eq_of_mul _ _ _ _ (rad_mul p x e A c)

/-! ### Special cases -/

theorem yv_Ux (u : ℤ × ℤ) (c : Fin p.val × Fin p.val) :
    yv p u 1 1 c = cvec p c - u := by
  simp [yv, ivmul_one]

theorem yv_Lm (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    yv p 0 1 A c = ivmul (cvec p c) A.val.val := by
  simp [yv]

theorem radNext_Ux (u : ℤ × ℤ) (c : Fin p.val × Fin p.val) :
    radNext p u 1 1 c = crep p (cvec p c - u) := by
  rw [radNext, yv_Ux]

theorem radNext_Lm (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    radNext p 0 1 A c = crep p (ivmul (cvec p c) A.val.val) := by
  rw [radNext, yv_Lm]

theorem radDelta_Ux (u : ℤ × ℤ) (c : Fin p.val × Fin p.val) :
    radDelta p u 1 1 c = -cq p (cvec p c - u) := by
  simp [radDelta, yv_Ux, ivmul_one]

theorem radDelta_Lm (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    radDelta p 0 1 A c =
      -ivmul (cq p (ivmul (cvec p c) A.val.val)) (A.val⁻¹ : GL (Fin 2) ℤ).val := by
  simp only [radDelta, yv_Lm, Units.val_one, one_smul]

theorem next_Ux_inl (u : ℤ × ℤ) (j : Option (Fin p.val)) :
    nextRep (badLineCosets p hp3) (Ux u) (toRep p hp3 (.inl j)) = toRep p hp3 (.inl j) := by
  rw [Ux, next_inl, levelNext_one]

theorem delta_Ux_inl (u : ℤ × ℤ) (j : Option (Fin p.val)) :
    deltaRep (badLineCosets p hp3) (Ux u) (toRep p hp3 (.inl j)) = Ux (ivmul u (Bl p j)) := by
  rw [Ux, delta_inl, levelDelta_one]
  rfl

theorem next_Lm_inl (A : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    nextRep (badLineCosets p hp3) (Lm A) (toRep p hp3 (.inl j)) =
      toRep p hp3 (.inl (levelNext p hp3 A j)) := by
  rw [Lm, next_inl]

theorem delta_Lm_inl (A : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    deltaRep (badLineCosets p hp3) (Lm A) (toRep p hp3 (.inl j)) = Lm (levelDelta p hp3 A j) := by
  rw [Lm, delta_inl, ivmul_zero]
  rfl

theorem next_Ux_inr (u : ℤ × ℤ) (c : Fin p.val × Fin p.val) :
    nextRep (badLineCosets p hp3) (Ux u) (toRep p hp3 (.inr c)) =
      toRep p hp3 (.inr (crep p (cvec p c - u))) := by
  rw [Ux, next_inr, radNext_Ux]

theorem delta_Ux_inr (u : ℤ × ℤ) (c : Fin p.val × Fin p.val) :
    deltaRep (badLineCosets p hp3) (Ux u) (toRep p hp3 (.inr c)) =
      Ux (-cq p (cvec p c - u)) := by
  rw [Ux, delta_inr, radDelta_Ux]
  rfl

theorem next_Lm_inr (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    nextRep (badLineCosets p hp3) (Lm A) (toRep p hp3 (.inr c)) =
      toRep p hp3 (.inr (crep p (ivmul (cvec p c) A.val.val))) := by
  rw [Lm, next_inr, radNext_Lm]

theorem delta_Lm_inr (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    deltaRep (badLineCosets p hp3) (Lm A) (toRep p hp3 (.inr c)) =
      Mel (-ivmul (cq p (ivmul (cvec p c) A.val.val)) (A.val⁻¹ : GL (Fin 2) ℤ).val) 1 A := by
  rw [Lm, delta_inr, radDelta_Lm]

end TernaryPeriodPolynomials.LevelThree.BadLineTransitions
