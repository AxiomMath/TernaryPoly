module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineCosets

@[expose] public section


/-!
# The local `T_p` cosets at the bad line

For a prime `p ≠ 3`, the stabilizer `ΛB = {R(x, e, A)}` of the bad-line cusp
(`x ∈ ℤ²`, `e = ±1`, `A ∈ Γ₁'(3)`, `R(w, a, B) = [[a, wB], [0, B]]`) has the local cosets of
`Γ diag(p,1,1) Γ` represented by the `p + 1` Levi elements
`ℓ_j = R(0, 1, B_j)`, `B_j = p α_j⁻¹` (`α_j` the level-three Hecke matrices of `LevelThreeCosets`),
and the `p²` radical elements `τ_c = R(c, εp, 1)` (`c ∈ (ℤ/p)²`, `εp = ±p ≡ 1 mod 3`).
This file builds the local correspondence `badLineCosets p` and computes the transitions
`s⁻¹ g s' ∈ ΛB` for `g = R(x, e, A)`:

* `levi_mul`: `ℓ_j⁻¹ R(x,e,A) ℓ_k = R(x B_j, e, δ_j(A))` with `k = levelNext A j`;
* `rad_mul`: `τ_c⁻¹ R(x,e,A) τ_{c'} = R(-e q(y) A⁻¹, e, A)` with `y = e (c - x) A`, `c' = crep y`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineCosets

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open GoodLineCosets (cvec crep cq cvec_crep crep_unique ivmul_smul ivmul_sub)
open AmbientHecke LocalHecke

theorem R_congr {w w' : ℚ × ℚ} {a a' : ℚˣ} {B B' : GL (Fin 2) ℚ} (hw : w = w') (ha : a = a')
    (hB : B = B') : R w a B = R w' a' B' := by
  subst hw ha hB
  rfl

variable (p : Nat.Primes)

/-! ### The integral Levi blocks `B_j = p α_j⁻¹` -/

/-- `B_i = [[p, -i], [0, 1]]`, `B_∞ = ε_p diag(1, p)`; these satisfy `B_j α_j = α_j B_j = p`. -/
def Bl : Option (Fin p.val) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(signP p : ℤ), 0; 0, (signP p : ℤ) * p.val]
  | some i => !![(p.val : ℤ), -(i.val : ℤ); 0, 1]

theorem Bl_mul_N (j : Option (Fin p.val)) :
    Bl p j * N p j = (p.val : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  cases j with
  | none =>
    rw [N_none]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Bl, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination (p.val : ℤ) * signP_mul_self p
  | some i =>
    rw [N_some]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Bl, Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem N_mul_Bl (j : Option (Fin p.val)) :
    N p j * Bl p j = (p.val : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  cases j with
  | none =>
    rw [N_none]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Bl, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination (p.val : ℤ) * signP_mul_self p
  | some i =>
    rw [N_some]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Bl, Matrix.mul_apply, Fin.sum_univ_two]

theorem Bl_det (j : Option (Fin p.val)) : (Bl p j).det = p.val := by
  cases j with
  | none =>
    simp only [Bl, Matrix.det_fin_two_of]
    linear_combination (p.val : ℤ) * signP_mul_self p
  | some i =>
    simp only [Bl, Matrix.det_fin_two_of]
    ring

/-- `B_j` in `GL₂(ℚ)`. -/
def BQ (j : Option (Fin p.val)) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero ((Bl p j).map (Int.castRingHom ℚ)) (by
    rw [show ((Bl p j).map (Int.castRingHom ℚ)).det = (((Bl p j).det : ℤ) : ℚ) from
      (RingHom.map_det (Int.castRingHom ℚ) (Bl p j)).symm, Bl_det]
    exact_mod_cast p.property.ne_zero)

theorem BQ_val (j : Option (Fin p.val)) :
    (BQ p j).val = (Bl p j).map (Int.castRingHom ℚ) := rfl

/-- **The Levi transition in integral matrices**: `B_j δ_j(A) = A B_{next A j}`. -/
theorem Bl_delta (hp3 : p.val ≠ 3) (A : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    Bl p j * (levelDelta p hp3 A j).val.val = A.val.val * Bl p (levelNext p hp3 A j) := by
  have hp : (p.val : ℤ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have key : (p.val : ℤ) • (Bl p j * (levelDelta p hp3 A j).val.val) =
      (p.val : ℤ) • (A.val.val * Bl p (levelNext p hp3 A j)) := by
    calc (p.val : ℤ) • (Bl p j * (levelDelta p hp3 A j).val.val)
        = Bl p j * (levelDelta p hp3 A j).val.val * (N p (levelNext p hp3 A j) *
            Bl p (levelNext p hp3 A j)) := by
          rw [N_mul_Bl, Matrix.mul_smul, Matrix.mul_one]
      _ = Bl p j * ((levelDelta p hp3 A j).val.val * N p (levelNext p hp3 A j)) *
            Bl p (levelNext p hp3 A j) := by simp only [Matrix.mul_assoc]
      _ = Bl p j * (N p j * A.val.val) * Bl p (levelNext p hp3 A j) := by
          rw [levelDelta_spec]
      _ = (Bl p j * N p j) * (A.val.val * Bl p (levelNext p hp3 A j)) := by
          simp only [Matrix.mul_assoc]
      _ = (p.val : ℤ) • (A.val.val * Bl p (levelNext p hp3 A j)) := by
          rw [Bl_mul_N, Matrix.smul_mul, Matrix.one_mul]
  ext a b
  have h := congrFun (congrFun key a) b
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  exact mul_left_cancel₀ hp h

/-- `B_j⁻¹ B_k = A ∈ Γ₁'(3)` forces `j = k`. -/
theorem Bl_disjoint (j k : Option (Fin p.val)) (A : GL (Fin 2) ℤ)
    (h : Bl p k = Bl p j * A.val) : j = k := by
  have hp : (p.val : ℤ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have key : (p.val : ℤ) • N p j = (p.val : ℤ) • (A.val * N p k) := by
    calc (p.val : ℤ) • N p j = N p j * (Bl p k * N p k) := by
          rw [Bl_mul_N, Matrix.mul_smul, Matrix.mul_one]
      _ = N p j * (Bl p j * A.val) * N p k := by rw [h]; simp only [Matrix.mul_assoc]
      _ = (N p j * Bl p j) * (A.val * N p k) := by simp only [Matrix.mul_assoc]
      _ = (p.val : ℤ) • (A.val * N p k) := by rw [N_mul_Bl, Matrix.smul_mul, Matrix.one_mul]
  have hN : A.val * N p k = N p j := by
    ext a b
    have h' := congrFun (congrFun key a) b
    simp only [Matrix.smul_apply, smul_eq_mul] at h'
    exact (mul_left_cancel₀ hp h').symm
  exact disjoint_N p A.val j k hN

/-! ### Elements of `ΛB` and the explicit representatives -/

/-- The element `R(x, e, A)` of `ΛB`. -/
def Mel (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) : ΛB :=
  ψ (⟨Multiplicative.ofAdd x, (e, A)⟩ : BadLineSemidirect)

theorem Mel_val (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) :
    (Mel x e A : RationalGL3) = R (icast x) (ucast e) (levelEmbed A) := by
  rw [Mel, psi_val]
  rfl

theorem exists_Mel (g : ΛB) : ∃ (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel), g = Mel x e A := by
  obtain ⟨s, rfl⟩ := ψ.surjective g
  exact ⟨s.left.toAdd, s.right.1, s.right.2, congrArg ψ (SemidirectProduct.ext rfl rfl)⟩

/-- The index type: Levi-type `inl j` and radical-type `inr c`. -/
abbrev BIdx := Option (Fin p.val) ⊕ (Fin p.val × Fin p.val)

/-- `ℓ_j = R(0, 1, B_j)`. -/
def sLev (j : Option (Fin p.val)) : RationalGL3 := R 0 1 (BQ p j)

/-- `τ_c = R(c, εp, 1)`. -/
def sRad (c : Fin p.val × Fin p.val) : RationalGL3 := R (icast (cvec p c)) (epsU p) 1

/-- The explicit local representatives. -/
def rExpl : BIdx p → RationalGL3
  | .inl j => sLev p j
  | .inr c => sRad p c

theorem vmul_BQ (y : ℤ × ℤ) (j : Option (Fin p.val)) :
    vmul (icast y) (BQ p j).val = icast (ivmul y (Bl p j)) := by
  rw [BQ_val]
  exact vmul_icast y (Bl p j)

/-! ### Transitions of Levi type -/

theorem levi_mul (hp3 : p.val ≠ 3) (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel)
    (j : Option (Fin p.val)) :
    sLev p j * (Mel (ivmul x (Bl p j)) e (levelDelta p hp3 A j) : RationalGL3) =
      (Mel x e A : RationalGL3) * sLev p (levelNext p hp3 A j) := by
  rw [Mel_val, Mel_val, sLev, sLev, R_mul, R_mul]
  refine R_congr ?_ ?_ ?_
  · rw [vmul_zero, smul_zero, add_zero, zero_add, Units.val_one, one_smul, ← vmul_BQ,
      vmul_inv_cancel]
  · rw [one_mul, mul_one]
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, BQ_val, BQ_val, levelEmbed_apply, levelEmbed_apply,
      integralEmbed_val, integralEmbed_val, ← Matrix.map_mul, ← Matrix.map_mul,
      Bl_delta p hp3]

/-! ### Transitions of radical type -/

/-- `y = e (c - x) A`. -/
def yv (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) : ℤ × ℤ :=
  (e : ℤ) • ivmul (cvec p c - x) A.val.val

/-- The next radical index `c' = crep (e (c - x) A)`. -/
def radNext (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    Fin p.val × Fin p.val :=
  crep p (yv p x e A c)

/-- The radical part `-e q(y) A⁻¹` of the transition. -/
def radDelta (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    ℤ × ℤ :=
  -((e : ℤ) • ivmul (cq p (yv p x e A c)) (A.val⁻¹ : GL (Fin 2) ℤ).val)

theorem rad_int (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    cvec p c + epsP p • radDelta p x e A c =
      x + (e : ℤ) • ivmul (cvec p (radNext p x e A c)) (A.val⁻¹ : GL (Fin 2) ℤ).val := by
  have h1 : ivmul (yv p x e A c) (A.val⁻¹ : GL (Fin 2) ℤ).val = (e : ℤ) • (cvec p c - x) := by
    rw [yv, ivmul_smul, ivmul_inv_cancel]
  have h2 : ivmul (cvec p (radNext p x e A c)) (A.val⁻¹ : GL (Fin 2) ℤ).val =
      (e : ℤ) • (cvec p c - x) -
        epsP p • ivmul (cq p (yv p x e A c)) (A.val⁻¹ : GL (Fin 2) ℤ).val := by
    rw [radNext, cvec_crep, ivmul_sub, ivmul_smul, h1]
  rw [h2, radDelta]
  rcases Int.units_eq_one_or e with rfl | rfl <;> simp only [Units.val_one, Units.val_neg] <;>
    module

theorem rad_mul (x : ℤ × ℤ) (e : ℤˣ) (A : binaryArithmeticLevel) (c : Fin p.val × Fin p.val) :
    sRad p c * (Mel (radDelta p x e A c) e A : RationalGL3) =
      (Mel x e A : RationalGL3) * sRad p (radNext p x e A c) := by
  rw [Mel_val, Mel_val, sRad, sRad, R_mul, R_mul]
  refine R_congr ?_ ?_ ?_
  · rw [inv_one, Units.val_one, vmul_one, epsU_val, levelEmbed_apply, ← map_inv,
      vmul_integralEmbed, ucast_val, icast_smul_int, icast_smul_int, ← icast_add, ← icast_add,
      rad_int]
  · exact mul_comm _ _
  · rw [one_mul, mul_one]

/-! ### Disjointness -/

theorem epsU_ne_ucast (e : ℤˣ) : epsU p ≠ ucast e := by
  intro h
  have h1 := congrArg Units.val h
  rw [epsU_val, ucast_val] at h1
  have h2 : epsP p = (e : ℤ) := by exact_mod_cast h1
  have h3 := epsP_natAbs p
  rw [h2, Int.natAbs_of_isUnit e.isUnit] at h3
  exact p.property.one_lt.ne' h3.symm

theorem sLev_inv_mul (j k : Option (Fin p.val)) :
    (sLev p j)⁻¹ * sLev p k = R 0 1 ((BQ p j)⁻¹ * BQ p k) := by
  rw [sLev, sLev, R_inv, R_mul]
  simp only [vmul_zero, smul_zero, add_zero, inv_one, one_mul]

theorem sRad_inv_mul (c c' : Fin p.val × Fin p.val) :
    (sRad p c)⁻¹ * sRad p c' =
      R ((((epsU p)⁻¹ : ℚˣ) : ℚ) • (icast (cvec p c') - icast (cvec p c))) 1 1 := by
  rw [sRad, sRad, R_inv, R_mul]
  refine R_congr ?_ ?_ ?_
  · simp only [inv_one, Units.val_one, vmul_one]
    module
  · exact inv_mul_cancel _
  · simp

theorem disjoint_idx (i j : BIdx p) (h : (rExpl p i)⁻¹ * rExpl p j ∈ ΛB) : i = j := by
  rcases i with j₁ | c₁ <;> rcases j with j₂ | c₂
  · simp only [rExpl] at h
    rw [sLev_inv_mul, R_mem_iff] at h
    obtain ⟨x, e, A, -, -, hB⟩ := h
    have hB' : BQ p j₂ = BQ p j₁ * levelEmbed A := by rw [← hB, mul_inv_cancel_left]
    have hv := congrArg Units.val hB'
    rw [Units.val_mul, BQ_val, BQ_val, levelEmbed_apply, integralEmbed_val,
      ← Matrix.map_mul] at hv
    have hm := Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective hv
    exact congrArg Sum.inl (Bl_disjoint p j₁ j₂ A.val hm)
  · simp only [rExpl, sLev, sRad] at h
    rw [R_inv, R_mul, R_mem_iff] at h
    obtain ⟨x, e, A, -, ha, -⟩ := h
    exfalso
    apply epsU_ne_ucast p e
    rw [← ha]
    simp
  · simp only [rExpl, sLev, sRad] at h
    rw [R_inv, R_mul, R_mem_iff] at h
    obtain ⟨x, e, A, -, ha, -⟩ := h
    exfalso
    apply epsU_ne_ucast p e⁻¹
    rw [map_inv, ← ha]
    simp
  · simp only [rExpl] at h
    rw [sRad_inv_mul, R_mem_iff] at h
    obtain ⟨x, e, A, hw, -, -⟩ := h
    have he : (epsP p : ℚ) ≠ 0 := epsP_ne_zero p
    have h1 : icast (cvec p c₂ - cvec p c₁) = icast (epsP p • x) := by
      rw [icast_sub, ← icast_smul_int, ← hw, Units.val_inv_eq_inv_val, epsU_val, smul_smul,
        mul_inv_cancel₀ he, one_smul]
    have h2 := crep_unique p c₂ c₁ x (icast_injective h1)
    exact congrArg Sum.inr h2.symm

theorem rExpl_injective : Function.Injective (rExpl p) := by
  intro i j h
  apply disjoint_idx p i j
  rw [h, inv_mul_cancel]
  exact ΛB.one_mem

theorem next_exists (hp3 : p.val ≠ 3) (g : ΛB) (i : BIdx p) :
    ∃ k, (rExpl p i)⁻¹ * (g : RationalGL3) * rExpl p k ∈ ΛB := by
  obtain ⟨x, e, A, rfl⟩ := exists_Mel g
  rcases i with j | c
  · refine ⟨.inl (levelNext p hp3 A j), ?_⟩
    have h := levi_mul p hp3 x e A j
    simp only [rExpl]
    rw [mul_assoc, ← h, inv_mul_cancel_left]
    exact (Mel _ _ _).property
  · refine ⟨.inr (radNext p x e A c), ?_⟩
    have h := rad_mul p x e A c
    simp only [rExpl]
    rw [mul_assoc, ← h, inv_mul_cancel_left]
    exact (Mel _ _ _).property

/-- **The explicit local correspondence at the bad line.** -/
def badLineCosets (hp3 : p.val ≠ 3) : LocalCorrespondence ΛB where
  representatives := Finset.univ.image (rExpl p)
  stable := by
    intro g hg s hs
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hs
    classical
    let f : BIdx p → BIdx p := fun i => (next_exists p hp3 ⟨g, hg⟩ i).choose
    have hf : ∀ i, (rExpl p i)⁻¹ * g * rExpl p (f i) ∈ ΛB :=
      fun i => (next_exists p hp3 ⟨g, hg⟩ i).choose_spec
    have hinj : Function.Injective f := by
      intro i i' h
      apply disjoint_idx p
      have h1 := hf i
      have h2 := hf i'
      rw [← h] at h2
      have h3 := ΛB.mul_mem h1 (ΛB.inv_mem h2)
      convert h3 using 1
      group
    obtain ⟨i, hi⟩ := Finite.surjective_of_injective hinj k
    refine ⟨rExpl p i, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h4 := hf i
    rw [hi, mul_assoc] at h4
    exact h4
  disjoint := by
    intro s hs s' hs' h
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hs'
    rw [disjoint_idx p i i' h]

theorem rExpl_mem (hp3 : p.val ≠ 3) (i : BIdx p) :
    rExpl p i ∈ (badLineCosets p hp3).representatives :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem rExpl_not_mem (i : BIdx p) : rExpl p i ∉ ΛB := by
  intro h
  rcases i with j | c
  · simp only [rExpl, sLev] at h
    rw [R_mem_iff] at h
    obtain ⟨x, e, A, -, -, hB⟩ := h
    have hv := congrArg Units.val hB
    rw [BQ_val, levelEmbed_apply, integralEmbed_val] at hv
    have hm := Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective hv
    have hd := congrArg Matrix.det hm
    rw [Bl_det] at hd
    have hp := p.property.two_le
    rcases det_units A.val with h1 | h1 <;> rw [h1] at hd <;> omega
  · simp only [rExpl, sRad] at h
    rw [R_mem_iff] at h
    obtain ⟨x, e, A, -, ha, -⟩ := h
    exact epsU_ne_ucast p e ha

end TernaryPeriodPolynomials.LevelThree.BadLineCosets
