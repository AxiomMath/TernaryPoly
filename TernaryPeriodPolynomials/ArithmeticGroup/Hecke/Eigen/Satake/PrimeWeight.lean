module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.PrimeCoset
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.SingleCharacter

@[expose] public section


/-!
# Plane weights of the prime Hecke correspondence `diag(p, 1, 1)`

For the double coset of `diag(p,1,1)`, every plane Iwasawa datum `(B, s)` with `s > 0` falls into
exactly one of two classes:

* `s = p` and `B ∈ GL₂(ℤ)`, with weight that of `(1, p)`;
* `s = 1` and `B` integral of determinant `±p`, with weight that of `(diag(p,1), 1)`.

Consequently the plane eigenvalue of any such correspondence is `N • W_p + M • W_1`, where
`N + M` is the number of representatives.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n p : ℕ}

theorem transposeGL_Γ2 {k : GeneralLinearGroup (Fin 2) ℚ} (hk : k ∈ Γ2) : transposeGL k ∈ Γ2 := by
  obtain ⟨k₀, rfl⟩ := hk
  exact ⟨transposeGL k₀, (transposeGL_map _ k₀).symm⟩

theorem ratPlaneWeight_mul_left (D : InducingData n) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ)
    {k : GeneralLinearGroup (Fin 2) ℚ} (hk : k ∈ Γ2) :
    ratPlaneWeight D (k * B) s = ratPlaneWeight D B s := by
  rw [← ratPlaneWeight_transpose D (k * B), transposeGL_mul,
    ratPlaneWeight_mul D _ s (transposeGL_Γ2 hk), ratPlaneWeight_transpose]

theorem ratPlaneWeight_Γ2 (D : InducingData n) {k : GeneralLinearGroup (Fin 2) ℚ} (hk : k ∈ Γ2)
    (s : ℚˣ) : ratPlaneWeight D k s = ratPlaneWeight D 1 s := by
  simpa using ratPlaneWeight_mul D 1 s hk

theorem intCast_map_mul2 (M N : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * N).map (Int.cast : ℤ → ℚ) = M.map (Int.cast : ℤ → ℚ) * N.map (Int.cast : ℤ → ℚ) := by
  have := Matrix.map_mul (L := M) (M := N) (f := Int.castRingHom ℚ)
  simpa only [Int.coe_castRingHom] using this

theorem intCast_det2 (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (M.map (Int.cast : ℤ → ℚ)).det = (M.det : ℚ) := by
  have := (Int.castRingHom ℚ).map_det M
  simpa only [Int.coe_castRingHom, RingHom.mapMatrix_apply] using this.symm

/-- An integral matrix of determinant `±1` lies in `GL₂(ℤ)`. -/
theorem mem_Γ2_of_int {x : GeneralLinearGroup (Fin 2) ℚ} (X : Matrix (Fin 2) (Fin 2) ℤ)
    (hX : X.map (Int.cast : ℤ → ℚ) = x.val) (hdet : X.det * X.det = 1) : x ∈ Γ2 := by
  have h1 : X * (X.det • X.adjugate) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hdet, one_smul]
  refine ⟨⟨X, X.det • X.adjugate, h1, mul_eq_one_comm.mp h1⟩, ?_⟩
  apply Units.ext
  rw [← hX]
  rfl

/-- `diag(p, 1)` in `GL₂(ℚ)`. -/
def dP (hp : p.Prime) : GeneralLinearGroup (Fin 2) ℚ :=
  ⟨diagonal ![(p : ℚ), 1], diagonal ![(p : ℚ)⁻¹, 1], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    fin_cases i <;> simp [this], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    fin_cases i <;> simp [this]⟩

theorem dP_inv_val (hp : p.Prime) : ((dP hp)⁻¹).val = diagonal ![(p : ℚ)⁻¹, 1] := rfl

theorem weight_diag (D : InducingData n) (hp : p.Prime) (x : GeneralLinearGroup (Fin 2) ℚ)
    (c : Fin 2 → ℤ) (hx : x.val = (diagonal c).map (Int.cast : ℤ → ℚ)) {e : ℤ}
    (h0 : c 0 = p * e) (he : e * e = 1) (h1 : c 1 * c 1 = 1) (s : ℚˣ) :
    ratPlaneWeight D x s = ratPlaneWeight D (dP hp) s := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hE : (dP hp)⁻¹ * x ∈ Γ2 := by
    apply mem_Γ2_of_int (diagonal ![e, c 1])
    · rw [Units.val_mul, hx, dP_inv_val, diagonal_map Int.cast_zero, diagonal_map Int.cast_zero,
        diagonal_mul_diagonal]
      congr 1; funext i
      fin_cases i <;> simp [h0, hp0]
    · rw [det_diagonal, Fin.prod_univ_two]
      have : (![e, c 1] 0 * ![e, c 1] 1) * (![e, c 1] 0 * ![e, c 1] 1) = (e * e) * (c 1 * c 1) := by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
      rw [this, he, h1, one_mul]
  rw [show x = dP hp * ((dP hp)⁻¹ * x) by group, ratPlaneWeight_mul D _ s hE]

/-- The swap matrix in `GL₂(ℚ)`. -/
def wS : GeneralLinearGroup (Fin 2) ℚ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem wS_val : wS.val = !![0, 1; 1, 0] := rfl

theorem wS_Γ2 : wS ∈ Γ2 := by
  apply mem_Γ2_of_int !![0, 1; 1, 0]
  · rw [wS_val]; ext i j; fin_cases i <;> fin_cases j <;> simp
  · simp [det_fin_two]

theorem weight_diag_swap (D : InducingData n) (hp : p.Prime) (x : GeneralLinearGroup (Fin 2) ℚ)
    (c : Fin 2 → ℤ) (hx : x.val = (diagonal c).map (Int.cast : ℤ → ℚ)) {e : ℤ}
    (h0 : c 0 * c 0 = 1) (h1 : c 1 = p * e) (he : e * e = 1) (s : ℚˣ) :
    ratPlaneWeight D x s = ratPlaneWeight D (dP hp) s := by
  have hval : (wS * x * wS).val = (diagonal ![c 1, c 0]).map (Int.cast : ℤ → ℚ) := by
    rw [Units.val_mul, Units.val_mul, hx, wS_val, diagonal_map Int.cast_zero,
      diagonal_map Int.cast_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal]
  have key := weight_diag D hp (wS * x * wS) ![c 1, c 0] hval (e := e) (by simpa using h1) he
    (by simpa using h0) s
  rw [ratPlaneWeight_mul D _ s wS_Γ2, ratPlaneWeight_mul_left D _ s wS_Γ2] at key
  exact key

/-- An integral `B` of determinant `±p` has the weight of `diag(p, 1)`. -/
theorem weight_int_det (D : InducingData n) (hp : p.Prime) (B : GeneralLinearGroup (Fin 2) ℚ)
    (hB : ∀ i j, ∃ z : ℤ, (z : ℚ) = B.val i j) (hdet : B.val.det = p ∨ B.val.det = -p)
    (s : ℚˣ) : ratPlaneWeight D B s = ratPlaneWeight D (dP hp) s := by
  choose X hX using hB
  have hXB : (Matrix.of X).map (Int.cast : ℤ → ℚ) = B.val := by ext i j; exact hX i j
  have hdetX : (Matrix.of X).det = p ∨ (Matrix.of X).det = -p := by
    have h := intCast_det2 (Matrix.of X)
    rw [hXB] at h
    rcases hdet with hd | hd
    · left; exact_mod_cast h.symm.trans hd
    · right; exact_mod_cast h.symm.trans hd
  have hX0 : (Matrix.of X).det ≠ 0 := by
    have : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rcases hdetX with hd | hd <;> rw [hd] <;> simpa using this
  obtain ⟨A, Q, A', Q', a, hAA, hA'A, hQQ, hQ'Q, hfac⟩ :=
    TernaryPeriodPolynomials.HeckeCommutativity.exists_eq_mul_diagonal_mul (Matrix.of X) hX0
  obtain ⟨UA, hUAinv, hUA⟩ : ∃ U : GeneralLinearGroup (Fin 2) ℚ,
      (U⁻¹).val = A'.map (Int.cast : ℤ → ℚ) ∧ U ∈ Γ2 :=
    ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) ⟨A, A', hAA, hA'A⟩, by rw [← map_inv]; rfl,
      ⟨_, rfl⟩⟩
  obtain ⟨UQ, hUQinv, hUQ⟩ : ∃ U : GeneralLinearGroup (Fin 2) ℚ,
      (U⁻¹).val = Q'.map (Int.cast : ℤ → ℚ) ∧ U ∈ Γ2 :=
    ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) ⟨Q, Q', hQQ, hQ'Q⟩, by rw [← map_inv]; rfl,
      ⟨_, rfl⟩⟩
  have hxval : (UA⁻¹ * B * UQ⁻¹).val = (diagonal a).map (Int.cast : ℤ → ℚ) := by
    rw [Units.val_mul, Units.val_mul, hUAinv, hUQinv, ← hXB, ← intCast_map_mul2,
      ← intCast_map_mul2, hfac]
    congr 1
    calc A' * (A * diagonal a * Q) * Q' = (A' * A) * diagonal a * (Q * Q') := by
          simp only [Matrix.mul_assoc]
      _ = diagonal a := by rw [hA'A, hQQ, Matrix.one_mul, Matrix.mul_one]
  have hBx : ratPlaneWeight D B s = ratPlaneWeight D (UA⁻¹ * B * UQ⁻¹) s := by
    rw [ratPlaneWeight_mul D _ s (Γ2.inv_mem hUQ), ratPlaneWeight_mul_left D _ s (Γ2.inv_mem hUA)]
  rw [hBx]
  -- the diagonal entries multiply to `±p`
  have hprod : (a 0 * a 1).natAbs = p := by
    have hd : (Matrix.of X).det = A.det * (a 0 * a 1) * Q.det := by
      rw [hfac, det_mul, det_mul, det_diagonal, Fin.prod_univ_two]
    have hA1 : A.det.natAbs = 1 := by
      have h : A.det * A'.det = 1 := by rw [← det_mul, hAA, det_one]
      rcases Int.eq_one_or_neg_one_of_mul_eq_one h with e | e <;> rw [e] <;> rfl
    have hQ1 : Q.det.natAbs = 1 := by
      have h : Q.det * Q'.det = 1 := by rw [← det_mul, hQQ, det_one]
      rcases Int.eq_one_or_neg_one_of_mul_eq_one h with e | e <;> rw [e] <;> rfl
    have : (Matrix.of X).det.natAbs = p := by
      rcases hdetX with h | h <;> rw [h] <;> simp
    rw [hd, Int.natAbs_mul, Int.natAbs_mul, hA1, hQ1] at this
    simpa using this
  rw [Int.natAbs_mul] at hprod
  have hdvd : (a 0).natAbs ∣ p := ⟨_, hprod.symm⟩
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h0 | h0
  · -- `|a 0| = 1`, `|a 1| = p`
    rw [h0, one_mul] at hprod
    rcases Int.natAbs_eq (a 1) with e1 | e1
    · exact weight_diag_swap D hp _ a hxval (e := 1) (sq_one_of_natAbs h0) (by rw [e1, hprod]; ring)
        (by norm_num) s
    · exact weight_diag_swap D hp _ a hxval (e := -1) (sq_one_of_natAbs h0) (by rw [e1, hprod]; ring)
        (by norm_num) s
  · rw [h0] at hprod
    have h1 : (a 1).natAbs = 1 := by
      have hp1 : 0 < p := hp.pos
      have : p * (a 1).natAbs = p * 1 := by rw [mul_one]; exact hprod
      exact Nat.eq_of_mul_eq_mul_left hp1 this
    rcases Int.natAbs_eq (a 0) with e0 | e0
    · exact weight_diag D hp _ a hxval (e := 1) (by rw [e0, h0]; ring) (by norm_num)
        (sq_one_of_natAbs h1) s
    · exact weight_diag D hp _ a hxval (e := -1) (by rw [e0, h0]; ring) (by norm_num)
        (sq_one_of_natAbs h1) s

/-- **Plane Levi data of the prime double coset.** -/
theorem prime_plane_levi (hp : p.Prime) (v : ℚ × ℚ)
    (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) (hs : 0 < (s : ℚ))
    (h : pU v * planeLevi B s ∈ DZ (gP hp)) :
    ((s : ℚ) = p ∧ B ∈ Γ2) ∨
      ((s : ℚ) = 1 ∧ (∀ i j, ∃ z : ℤ, (z : ℚ) = B.val i j) ∧
        (B.val.det = p ∨ B.val.det = -p)) := by
  obtain ⟨⟨hB, ⟨z, hz⟩, -, -⟩, hdet⟩ := (plane_mem_DZ_gP_iff hp v B s).mp h
  have hB' := hB
  choose X hX using hB'
  have hXB : (Matrix.of X).map (Int.cast : ℤ → ℚ) = B.val := by ext i j; exact hX i j
  have hdetB : B.val.det = ((Matrix.of X).det : ℚ) := by rw [← hXB, intCast_det2]
  have hz0 : 0 < z := by exact_mod_cast hz ▸ hs
  have hint : (Matrix.of X).det * z = p ∨ (Matrix.of X).det * z = -p := by
    rw [hdetB, ← hz] at hdet
    rcases hdet with hd | hd
    · left; exact_mod_cast hd
    · right; exact_mod_cast hd
  have hzabs : z.natAbs ∣ p := by
    refine ⟨(Matrix.of X).det.natAbs, ?_⟩
    rcases hint with hd | hd
    · have := congrArg Int.natAbs hd
      rw [Int.natAbs_mul] at this
      simpa [mul_comm] using this.symm
    · have := congrArg Int.natAbs hd
      rw [Int.natAbs_mul] at this
      simpa [mul_comm] using this.symm
  have hzn : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz0.le
  rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hzabs with h1 | h1
  · -- `s = 1`
    have hz1 : z = 1 := by rw [← hzn, h1]; rfl
    right
    have hs1 : (s : ℚ) = 1 := by rw [← hz, hz1]; simp
    refine ⟨hs1, hB, ?_⟩
    rw [hs1, mul_one] at hdet
    exact hdet
  · -- `s = p`
    have hzp : z = p := by rw [← hzn, h1]
    left
    refine ⟨by rw [← hz, hzp]; simp, mem_Γ2_of_int (Matrix.of X) hXB ?_⟩
    rw [hzp] at hint
    rcases hint with hd | hd
    · have : (Matrix.of X).det = 1 := by
        have := hd; nlinarith [this]
      rw [this]; rfl
    · have : (Matrix.of X).det = -1 := by
        have := hd; nlinarith [this]
      rw [this]; rfl

/-- **Plane weights of the prime double coset.** -/
theorem prime_plane_weight (D : InducingData n) (hp : p.Prime) (v : ℚ × ℚ)
    (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) (hs : 0 < (s : ℚ))
    (h : pU v * planeLevi B s ∈ DZ (gP hp)) :
    ((s : ℚ) = p ∧ ratPlaneWeight D B s = ratPlaneWeight D 1 s) ∨
      ((s : ℚ) = 1 ∧ ratPlaneWeight D B s = ratPlaneWeight D (dP hp) s) := by
  rcases prime_plane_levi hp v B s hs h with ⟨hs', hB⟩ | ⟨hs', hB, hdet⟩
  · exact Or.inl ⟨hs', ratPlaneWeight_Γ2 D hB s⟩
  · exact Or.inr ⟨hs', weight_int_det D hp B hB hdet s⟩

/-- `p` as a unit of `ℚ`. -/
def pUnit (hp : p.Prime) : ℚˣ := Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero)

theorem pUnit_val (hp : p.Prime) : ((pUnit hp : ℚˣ) : ℚ) = p := Units.val_mk0 _

theorem rep_plane_mem (hp : p.Prime) {t : HeckeCorrespondence} (ht : AwayThree t)
    (hg : t.g = gP hp) {r : RationalGL3} (hr : r ∈ t.representatives) {v : ℚ × ℚ}
    {B : GeneralLinearGroup (Fin 2) ℚ} {s : ℚˣ} {γ : IntegralGL}
    (hdec : r = pU v * planeLevi B s * integralRational γ) :
    pU v * planeLevi B s ∈ DZ (gP hp) := by
  have h1 := (repSet ht).sub r hr
  rw [hg] at h1
  have heq : pU v * planeLevi B s = r * (integralRational γ)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]; exact hdec.symm
  rw [heq]
  exact DZ_right h1 (Γ.inv_mem ⟨γ, rfl⟩)

/-- **Exactly one representative has plane scalar `p`.** -/
theorem prime_plane_count (hp : p.Prime) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = gP hp) (vP : RationalGL3 → ℚ × ℚ) (BP : RationalGL3 → GeneralLinearGroup (Fin 2) ℚ)
    (sP : RationalGL3 → ℚˣ) (γP : RationalGL3 → IntegralGL)
    (hP : ∀ r ∈ t.representatives,
      r = pU (vP r) * planeLevi (BP r) (sP r) * integralRational (γP r))
    (hsP : ∀ r ∈ t.representatives, 0 < (sP r : ℚ)) :
    (t.representatives.filter (fun r => (sP r : ℚ) = p)).card = 1 := by
  classical
  have hRS := repSet ht
  have hdecP : ∀ r ∈ t.representatives, 0 < (((BP r, sP r) : MP).2 : ℚ) ∧
      r⁻¹ * (planeData.U (vP r) * planeData.L (BP r, sP r)) ∈ Γ := by
    intro r hr
    refine ⟨hsP r hr, ?_⟩
    change r⁻¹ * (pU (vP r) * planeLevi (BP r) (sP r)) ∈ Γ
    have : pU (vP r) * planeLevi (BP r) (sP r) = r * (integralRational (γP r))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact (hP r hr).symm
    rw [this, inv_mul_cancel_left]
    exact Γ.inv_mem ⟨_, rfl⟩
  have hpos : (0 : ℚ) < ((pUnit hp : ℚˣ) : ℚ) := by
    rw [pUnit_val]; exact_mod_cast hp.pos
  have hfilter : t.representatives.filter (fun r => (sP r : ℚ) = p) =
      t.representatives.filter (fun r => (QuotientGroup.mk (BP r, sP r) : MP ⧸ ΓM0) =
        QuotientGroup.mk ((1 : GeneralLinearGroup (Fin 2) ℚ), pUnit hp)) := by
    refine Finset.filter_congr fun r hr => ?_
    rw [QuotientGroup.eq]
    constructor
    · intro hs
      rcases prime_plane_levi hp _ _ _ (hsP r hr) (rep_plane_mem hp ht hg hr (hP r hr)) with
        ⟨_, hB⟩ | ⟨hs1, -⟩
      · refine Subgroup.mem_prod.mpr ⟨?_, ?_⟩
        · simpa using hB
        · rw [Subgroup.mem_bot]
          apply Units.ext
          rw [Prod.snd_mul, Prod.snd_inv, Units.val_mul, Units.val_inv_eq_inv_val, pUnit_val, hs,
            Units.val_one]
          have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
          field_simp
      · exfalso
        rw [hs1] at hs
        have : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
        rw [← hs] at this
        exact lt_irrefl _ this
    · intro hm
      obtain ⟨-, h2⟩ := Subgroup.mem_prod.mp hm
      rw [Subgroup.mem_bot, Prod.snd_mul, Prod.snd_inv, inv_mul_eq_one] at h2
      change sP r = pUnit hp at h2
      rw [h2, pUnit_val]
  rw [hfilter, planeData.fiber_card hRS ΓM0 ΓM0_le (fun m : MP => 0 < (m.2 : ℚ)) pos_class
    vP (fun r => (BP r, sP r)) hdecP ((1 : GeneralLinearGroup (Fin 2) ℚ), pUnit hp) hpos]
  -- the radical coordinates form exactly the lattice
  have hS : ∀ u, u ∈ planeData.S (DZ t.g) ((1 : GeneralLinearGroup (Fin 2) ℚ), pUnit hp) ↔
      (∃ z : ℤ, (z : ℚ) = u.1 * p) ∧ ∃ z : ℤ, (z : ℚ) = u.2 * p := by
    intro u
    change pU u * planeLevi 1 (pUnit hp) ∈ DZ t.g ↔ _
    rw [hg, plane_mem_DZ_gP_iff, pUnit_val]
    constructor
    · rintro ⟨⟨-, -, h1, h2⟩, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun i j => ?_, ⟨p, rfl⟩, h1, h2⟩, Or.inl (by simp)⟩
      fin_cases i <;> fin_cases j
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hL : ∀ u, u ∈ planeData.latt ((1 : GeneralLinearGroup (Fin 2) ℚ), pUnit hp) ↔
      (∃ z : ℤ, (z : ℚ) = u.1 * p) ∧ ∃ z : ℤ, (z : ℚ) = u.2 * p := by
    intro u
    rw [ParabolicData.latt, AddSubgroup.mem_comap, mem_zLat]
    simp [planeData, matHom_apply, pUnit_val, mul_comm]
  rw [Set.ncard_eq_one]
  refine ⟨0, Set.ext fun y => ?_⟩
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Set.mem_singleton_iff, QuotientAddGroup.eq_zero_iff, hL]
    exact (hS u).mp hu
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    refine ⟨0, (hS 0).mpr ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩, ?_⟩
    rw [hy]; rfl

/-- **The plane eigenvalue of the prime correspondence.** For every correspondence of the double
coset of `diag(p,1,1)`, the plane eigenvalue is `W(1, p) + M • W(diag(p,1), 1)` where `1 + M` is
the number of representatives. -/
theorem prime_plane_eigenvalue (D : InducingData n) (hp : p.Prime) (t : HeckeCorrespondence)
    (ht : AwayThree t) (hg : t.g = gP hp) :
    ∃ M : ℕ, 1 + M = t.representatives.card ∧
      ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
        ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
          (ratPlaneWeight D 1 (pUnit hp) + (M : ℂ) * ratPlaneWeight D (dP hp) 1) * f g := by
  classical
  choose vP BP sP γP hsP hP using plane_iwasawa_pos
  have hform := plane_rational_formula D t ht vP BP sP γP (fun r _ => hP r)
  have hcount := prime_plane_count hp t ht hg vP BP sP γP (fun r _ => hP r) (fun r _ => hsP r)
  have hterm : ∀ r ∈ t.representatives, ratPlaneWeight D (BP r) (sP r) =
      if (sP r : ℚ) = p then ratPlaneWeight D 1 (pUnit hp) else ratPlaneWeight D (dP hp) 1 := by
    intro r hr
    have hmem := rep_plane_mem hp ht hg hr (hP r)
    rcases prime_plane_weight D hp _ _ _ (hsP r) hmem with ⟨hs, hw⟩ | ⟨hs, hw⟩
    · rw [ite_eq_left hs, hw, show sP r = pUnit hp from Units.ext (by rw [hs, pUnit_val])]
    · have hne : (sP r : ℚ) ≠ p := by rw [hs]; exact_mod_cast hp.one_lt.ne
      rw [ite_eq_right hne, hw, show sP r = 1 from Units.ext (by rw [hs, Units.val_one])]
  refine ⟨(t.representatives.filter (fun r => ¬ (sP r : ℚ) = p)).card, ?_, fun f hf g => ?_⟩
  · rw [← hcount]; exact Finset.card_filter_add_card_filter_not _
  rw [hform f hf g, Finset.sum_congr rfl hterm, Finset.sum_ite]
  simp [Finset.sum_const, nsmul_eq_mul, hcount]

end TernaryPeriodPolynomials.HeckeEigen.Satake
