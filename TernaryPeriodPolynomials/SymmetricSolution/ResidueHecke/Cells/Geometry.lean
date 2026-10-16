module

public import Mathlib

@[expose] public section


/-!
# Lemma B.1: the explicit map `i(w, C) = G(w, C)` and the ternary well-rounded cell

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3
(`app:Hecke-coordinate`), proof of `lem:literal-residue-comparison`.

For a binary form `C` and `w ∈ ℝ²` put `δ_C(w)² = min_{z ∈ ℤ²} (w - z)ᵗ C (w - z)` (`deltaSq`) and
`G(w, C) = [[1 + wᵗCw - δ², wᵗC],[Cw, C]]` (`Gmat`).  Proved here, in the paper's order:

* the squared length of `(k, z)` for `G(w,C)` is `k²(1 - δ²) + (z + kw)ᵗ C (z + kw)` (`Gmat_quad`),
  so the Schur complement of `C` is `1 - δ²` (`Gmat_schur`);
* the covering radius of `C(t) = [[1,t],[t,1]]`, `|t| ≤ 1/2`, is `δ² ≤ 1/(2(1+|t|)) ≤ 1/2`
  (`deltaSq_Ct_le`, via the Voronoi inequalities `voronoi_inequalities` and the hexagon bound
  `hex_bound`); hence the Schur complement is positive and `G(w, C(t))` is positive definite
  (`Gmat_posDef`);
* minimum one: `G(w,C)` takes values `≥ 1` on every nonzero integral vector when `C` has minimum
  one and `δ² ≤ 1/2` (`Gmat_min_one`), and `(1, z*)` (`z*` a nearest lattice point), `(0,1,0)`,
  `(0,0,1)` are three minimal vectors of determinant one (`Gmat_min_vectors`): `G(w,C(t))` is a
  well-rounded ternary form;
* equivariance `pᵗ G(w,C) p = G(w', DᵗCD)` for `p = [[η,0],[u,D]]`, `w' = D⁻¹(u + ηw)`
  (`Gmat_equivariant`), together with `δ_{DᵗCD}(w') = δ_C(w)` (`deltaSq_conj`);
* injectivity of `(w, C) ↦ G(w, C)` (`Gmat_injective`, `Gmat_Ct_injective`);
* the image of the standard binary edge is the unit-diagonal ternary cell: `Tcell` consists of the
  positive definite forms with unit diagonal and minimum at least one, and
  `{G(w, C(t)) : |t| ≤ 1/2, w ∈ Vor(C(t))} = Tcell` (`Gmat_mem_Tcell`, `Tcell_eq_Gmat`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry

open Matrix

abbrev Vec2 := Fin 2 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- The real vector underlying an integral vector. -/
def intVec (z : Fin 2 → ℤ) : Vec2 := fun i => (z i : ℝ)

/-- The quadratic form `v ↦ vᵗ C v`. -/
def quad (C : Mat2) (v : Vec2) : ℝ := v ⬝ᵥ (C *ᵥ v)

/-- The binary Gram matrices `C(t) = [[1,t],[t,1]]` of the standard well-rounded edge. -/
def Ct (t : ℝ) : Mat2 := !![1,t;t,1]

theorem quad_Ct (t : ℝ) (v : Vec2) :
    quad (Ct t) v = v 0 ^ 2 + 2 * t * v 0 * v 1 + v 1 ^ 2 := by
  simp [quad, Ct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem quad_Ct_nonneg {t : ℝ} (ht : |t| ≤ 1) (v : Vec2) : 0 ≤ quad (Ct t) v := by
  rw [quad_Ct]
  have h1 := abs_le.mp ht
  nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1), sq_nonneg (v 0), sq_nonneg (v 1),
    mul_nonneg (by linarith : 0 ≤ 1 + t) (sq_nonneg (v 0 + v 1)),
    mul_nonneg (by linarith : 0 ≤ 1 - t) (sq_nonneg (v 0 - v 1))]

/-- `δ_C(w)² = min_{z ∈ ℤ²} (w - z)ᵗ C (w - z)`, the squared distance of `w` to the lattice. -/
def deltaSq (C : Mat2) (w : Vec2) : ℝ := ⨅ z : Fin 2 → ℤ, quad C (w - intVec z)

theorem deltaSq_le {C : Mat2} (hC : ∀ v, 0 ≤ quad C v) (w : Vec2) (z : Fin 2 → ℤ) :
    deltaSq C w ≤ quad C (w - intVec z) :=
  ciInf_le ⟨0, by rintro _ ⟨_, rfl⟩; exact hC _⟩ z

theorem le_deltaSq {C : Mat2} {w : Vec2} {a : ℝ} (h : ∀ z, a ≤ quad C (w - intVec z)) :
    a ≤ deltaSq C w := le_ciInf h

theorem deltaSq_nonneg {C : Mat2} (hC : ∀ v, 0 ≤ quad C v) (w : Vec2) : 0 ≤ deltaSq C w :=
  le_deltaSq (fun _ => hC _)

/-- A nearest lattice point exists for the standard binary forms. -/
theorem exists_nearest {t : ℝ} (ht : |t| ≤ 1/2) (w : Vec2) :
    ∃ z : Fin 2 → ℤ, ∀ z' : Fin 2 → ℤ, quad (Ct t) (w - intVec z) ≤ quad (Ct t) (w - intVec z') := by
  have h1 := abs_le.mp ht
  set R := quad (Ct t) w with hR
  have hRz : quad (Ct t) (w - intVec 0) = R := by
    have : intVec (0 : Fin 2 → ℤ) = 0 := by funext i; simp [intVec]
    rw [this, sub_zero]
  -- coercivity: q(v) ≥ (v0^2+v1^2)/2
  have hco : ∀ v : Vec2, (v 0 ^ 2 + v 1 ^ 2) / 2 ≤ quad (Ct t) v := by
    intro v
    rw [quad_Ct]
    nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]
  let S : Set (Fin 2 → ℤ) := {z | quad (Ct t) (w - intVec z) ≤ R}
  have hS : S.Finite := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, |w 0| + |w 1| + 2 * |R| + 2 ≤ N := exists_nat_ge _
    apply Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin 2 => Set.Icc (-(N : ℤ)) N)
      (fun _ => Set.finite_Icc _ _))
    intro z hz
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    have hq := hco (w - intVec z)
    have hzR : quad (Ct t) (w - intVec z) ≤ R := hz
    have hsq : (w 0 - z 0) ^ 2 + (w 1 - z 1) ^ 2 ≤ 2 * R := by
      simp only [Pi.sub_apply, intVec] at hq
      linarith
    have hb : ∀ i : Fin 2, |(w i - z i)| ≤ 1 + 2 * |R| := by
      intro i
      have hi : (w i - z i) ^ 2 ≤ 2 * R := by
        fin_cases i <;> simp <;> nlinarith [sq_nonneg (w 0 - z 0), sq_nonneg (w 1 - z 1)]
      have hR0 : 2 * R ≤ 2 * |R| := by linarith [le_abs_self R]
      by_contra hcon
      push Not at hcon
      nlinarith [abs_nonneg (w i - z i), sq_abs (w i - z i), abs_nonneg R]
    intro i
    have := hb i
    have hwi : |w i| ≤ |w 0| + |w 1| := by
      fin_cases i <;> simp [abs_nonneg]
    have h3 : |(z i : ℝ)| ≤ |w i| + (1 + 2 * |R|) := by
      calc |(z i : ℝ)| = |w i - (w i - z i)| := by ring_nf
        _ ≤ |w i| + |w i - z i| := abs_sub _ _
        _ ≤ _ := by linarith
    have h4 : |(z i : ℝ)| ≤ N := by linarith [abs_nonneg R, abs_nonneg (w 0), abs_nonneg (w 1)]
    have h5 := abs_le.mp h4
    constructor
    · exact_mod_cast h5.1
    · exact_mod_cast h5.2
  have hne : S.Nonempty := ⟨0, by
    show quad (Ct t) (w - intVec 0) ≤ R
    rw [hRz]⟩
  obtain ⟨a, haS, ha⟩ := Set.exists_min_image S (fun z => quad (Ct t) (w - intVec z)) hS hne
  refine ⟨a, fun z' => ?_⟩
  by_cases hz' : z' ∈ S
  · exact ha z' hz'
  · have : R < quad (Ct t) (w - intVec z') := not_le.mp hz'
    exact le_trans haS this.le

/-! ### The covering radius of the standard binary forms -/

theorem hex_bound {t p r : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) (hp : |p| ≤ 1/2) (hr : |r| ≤ 1/2)
    (hpr : |p - r| ≤ 1 - t) : p ^ 2 + r ^ 2 - 2 * t * p * r ≤ (1 - t) / 2 := by
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  obtain ⟨hr1, hr2⟩ := abs_le.mp hr
  obtain ⟨hs1, hs2⟩ := abs_le.mp hpr
  rcases le_total 0 p with hp0 | hp0 <;> rcases le_total 0 r with hr0 | hr0
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 1/2 - t) (by linarith : 0 ≤ (1 - 2 * p) + (1 - 2 * r)),
      mul_nonneg ht0 (mul_nonneg (by linarith : 0 ≤ 1 - 2 * p) (by linarith : 0 ≤ 1 - 2 * r)),
      mul_nonneg hp0 (by linarith : 0 ≤ 1/2 - p), mul_nonneg hr0 (by linarith : 0 ≤ 1/2 - r)]
  · -- p ≥ 0 ≥ r
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - t) (mul_nonneg (by linarith : 0 ≤ 1/2 - p)
        (by linarith : 0 ≤ 1/2 + r)),
      mul_nonneg (by linarith : 0 ≤ p - r) (by linarith : 0 ≤ (1 - t) - (p - r))]
  · -- p ≤ 0 ≤ r
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - t) (mul_nonneg (by linarith : 0 ≤ 1/2 + p)
        (by linarith : 0 ≤ 1/2 - r)),
      mul_nonneg (by linarith : 0 ≤ r - p) (by linarith : 0 ≤ (1 - t) - (r - p))]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 1/2 - t) (by linarith : 0 ≤ (1 + 2 * p) + (1 + 2 * r)),
      mul_nonneg ht0 (mul_nonneg (by linarith : 0 ≤ 1 + 2 * p) (by linarith : 0 ≤ 1 + 2 * r)),
      mul_nonneg (by linarith : 0 ≤ -p) (by linarith : 0 ≤ 1/2 + p),
      mul_nonneg (by linarith : 0 ≤ -r) (by linarith : 0 ≤ 1/2 + r)]

theorem intVec_add (z z' : Fin 2 → ℤ) : intVec (z + z') = intVec z + intVec z' := by
  funext i; simp [intVec]

/-- Local minimality of a nearest lattice point gives the Voronoi inequalities. -/
theorem voronoi_inequalities {t : ℝ} (x : Vec2)
    (hx : ∀ z : Fin 2 → ℤ, quad (Ct t) x ≤ quad (Ct t) (x - intVec z)) :
    |x 0 + t * x 1| ≤ 1/2 ∧ |t * x 0 + x 1| ≤ 1/2 ∧
      (t < 1 → |x 0 - x 1| ≤ 1) ∧ (-1 < t → |x 0 + x 1| ≤ 1) := by
  have h1 := hx ![1, 0]
  have h2 := hx ![-1, 0]
  have h3 := hx ![0, 1]
  have h4 := hx ![0, -1]
  have h5 := hx ![1, -1]
  have h6 := hx ![-1, 1]
  have h7 := hx ![1, 1]
  have h8 := hx ![-1, -1]
  simp only [quad_Ct, intVec, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_one, Int.cast_zero, Int.cast_neg] at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨abs_le.mpr ⟨by nlinarith, by nlinarith⟩, abs_le.mpr ⟨by nlinarith, by nlinarith⟩, ?_, ?_⟩
  · intro ht
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · intro ht
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- **Covering radius.** For `|t| ≤ 1/2`, every point of `ℝ²` lies within `1/(2(1+|t|))` of the
lattice in the norm of `C(t)`. -/
theorem deltaSq_Ct_le {t : ℝ} (ht : |t| ≤ 1/2) (w : Vec2) :
    deltaSq (Ct t) w ≤ 1 / (2 * (1 + |t|)) := by
  have htt := abs_le.mp ht
  have hpsd : ∀ v, 0 ≤ quad (Ct t) v := quad_Ct_nonneg (by linarith)
  obtain ⟨z0, hz0⟩ := exists_nearest ht w
  set x : Vec2 := w - intVec z0 with hxdef
  have hx : ∀ z : Fin 2 → ℤ, quad (Ct t) x ≤ quad (Ct t) (x - intVec z) := by
    intro z
    have := hz0 (z0 + z)
    have e : w - intVec (z0 + z) = x - intVec z := by
      rw [intVec_add, hxdef]; abel
    rwa [e] at this
  refine le_trans (deltaSq_le hpsd w z0) ?_
  show quad (Ct t) x ≤ _
  obtain ⟨hp, hr, hd1, hd2⟩ := voronoi_inequalities x hx
  rw [quad_Ct]
  rcases le_or_gt 0 t with ht0 | ht0
  · rw [abs_of_nonneg ht0]
    have hd := hd1 (by linarith)
    have hpr : |(x 0 + t * x 1) - (t * x 0 + x 1)| ≤ 1 - t := by
      have e : (x 0 + t * x 1) - (t * x 0 + x 1) = (1 - t) * (x 0 - x 1) := by ring
      rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
      nlinarith [abs_nonneg (x 0 - x 1)]
    have key := hex_bound ht0 (by linarith) hp hr hpr
    rw [le_div_iff₀ (by linarith)]
    have h1t : 0 < 1 - t := by linarith
    have hq : (x 0 ^ 2 + 2 * t * x 0 * x 1 + x 1 ^ 2) * (1 - t ^ 2) ≤ (1 - t) / 2 := by
      nlinarith [key]
    nlinarith [hq, h1t]
  · rw [abs_of_neg ht0]
    have hd := hd2 (by linarith)
    have hpr : |(x 0 + t * x 1) - (-(t * x 0 + x 1))| ≤ 1 - (-t) := by
      have e : (x 0 + t * x 1) - (-(t * x 0 + x 1)) = (1 + t) * (x 0 + x 1) := by ring
      rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + t)]
      nlinarith [abs_nonneg (x 0 + x 1)]
    have hr' : |-(t * x 0 + x 1)| ≤ 1/2 := by rw [abs_neg]; exact hr
    have key := hex_bound (t := -t) (by linarith) (by linarith) hp hr' hpr
    rw [le_div_iff₀ (by linarith)]
    have h1t : 0 < 1 + t := by linarith
    have hq : (x 0 ^ 2 + 2 * t * x 0 * x 1 + x 1 ^ 2) * (1 - t ^ 2) ≤ (1 + t) / 2 := by
      nlinarith [key]
    nlinarith [hq, h1t]

/-! ### The ternary form `G(w,C)` -/

/-- The vector `(k, z) ∈ ℝ × ℝ²` in the ordered coordinates `(a, b, c)`. -/
def vec3 (k : ℝ) (z : Vec2) : Fin 3 → ℝ := ![k, z 0, z 1]

/-- `G(w,C) = [[1 + wᵗCw - δ_C(w)², wᵗC],[Cw, C]]`, the map `i(w,C)` of the proof of
Lemma B.1 (`app:Hecke-coordinate`). -/
def Gmat (w : Vec2) (C : Mat2) : Mat3 :=
  !![1 + quad C w - deltaSq C w, (C *ᵥ w) 0, (C *ᵥ w) 1;
     (C *ᵥ w) 0, C 0 0, C 0 1;
     (C *ᵥ w) 1, C 1 0, C 1 1]

/-- The Schur complement of `C` in `G(w,C)` is `1 - δ_C(w)²`. -/
theorem Gmat_schur (w : Vec2) (C : Mat2) :
    Gmat w C 0 0 - quad C w = 1 - deltaSq C w := by
  simp [Gmat]
  ring

/-- The squared length of `(k, z)` for `G(w,C)`: `k²(1 - δ²) + (z + k w)ᵗ C (z + k w)`. -/
theorem Gmat_quad {C : Mat2} (hC : C 1 0 = C 0 1) (w : Vec2) (k : ℝ) (z : Vec2) :
    vec3 k z ⬝ᵥ (Gmat w C *ᵥ vec3 k z) = k ^ 2 * (1 - deltaSq C w) + quad C (z + k • w) := by
  simp [vec3, Gmat, quad, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
  rw [hC]
  ring

/-- Positive definiteness of a real quadratic form given by a matrix. -/
def PosDefQ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.transpose = A ∧ ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (A *ᵥ v)

theorem Ct_pos {t : ℝ} (ht : |t| ≤ 1/2) (v : Vec2) (hv : v ≠ 0) : 0 < quad (Ct t) v := by
  have h1 := abs_le.mp ht
  rw [quad_Ct]
  have hv' : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    by_contra h
    apply hv
    funext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]

theorem Ct_symm (t : ℝ) : (Ct t).transpose = Ct t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ct]

theorem Gmat_symm {C : Mat2} (hC : C.transpose = C) (w : Vec2) :
    (Gmat w C).transpose = Gmat w C := by
  have h : C 1 0 = C 0 1 := by
    have := congrFun (congrFun hC 0) 1
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gmat, h]

/-- The Schur complement is positive for the standard forms. -/
theorem one_sub_deltaSq {t : ℝ} (ht : |t| ≤ 1/2) (w : Vec2) : 1/2 ≤ 1 - deltaSq (Ct t) w := by
  have h := deltaSq_Ct_le ht w
  have h1 : 1 / (2 * (1 + |t|)) ≤ 1/2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg t]
  linarith

/-- **Schur-complement positivity**: `G(w,C(t))` is positive definite for every `w` and every
`|t| ≤ 1/2`. -/
theorem Gmat_posDef {t : ℝ} (ht : |t| ≤ 1/2) (w : Vec2) : PosDefQ (Gmat w (Ct t)) := by
  refine ⟨Gmat_symm (Ct_symm t) w, ?_⟩
  intro v hv
  have hs := one_sub_deltaSq ht w
  have hC : (Ct t) 1 0 = (Ct t) 0 1 := by simp [Ct]
  have hv3 : v = vec3 (v 0) ![v 1, v 2] := by
    funext i; fin_cases i <;> simp [vec3]
  rw [hv3, Gmat_quad hC]
  have hpsd : ∀ u, 0 ≤ quad (Ct t) u := quad_Ct_nonneg (by linarith [abs_nonneg t])
  by_cases hk : v 0 = 0
  · have hz : (![v 1, v 2] : Vec2) ≠ 0 := by
      intro h
      apply hv
      funext i
      fin_cases i
      · exact hk
      · exact congrFun h 0
      · exact congrFun h 1
    rw [hk]
    simpa using Ct_pos ht _ hz
  · have : 0 < v 0 ^ 2 * (1 - deltaSq (Ct t) w) := by
      have := sq_pos_of_ne_zero hk
      nlinarith
    linarith [hpsd (![v 1, v 2] + v 0 • w)]

/-! ### Minimum one and well-roundedness -/

theorem quad_neg (C : Mat2) (v : Vec2) : quad C (-v) = quad C v := by
  simp [quad, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem quad_smul (C : Mat2) (a : ℝ) (v : Vec2) : quad C (a • v) = a ^ 2 * quad C v := by
  simp [quad, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The binary form `C(t)`, `|t| ≤ 1/2`, has minimum one on nonzero integral vectors. -/
theorem Ct_min_one {t : ℝ} (ht : |t| ≤ 1/2) (z : Fin 2 → ℤ) (hz : z ≠ 0) :
    1 ≤ quad (Ct t) (intVec z) := by
  have h1 := abs_le.mp ht
  rw [quad_Ct]
  simp only [intVec]
  have hz' : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  have key : ∀ a b : ℤ, a ≠ 0 → (1 : ℝ) ≤ (a : ℝ) ^ 2 + 2 * t * a * b + (b : ℝ) ^ 2 := by
    intro a b ha
    have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
    rcases eq_or_ne b 0 with hb | hb
    · subst hb
      simp only [Int.cast_zero, mul_zero, add_zero]
      nlinarith [sq_abs (a : ℝ)]
    · have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb
      have hab : |2 * t * a * b| ≤ |(a : ℝ)| * |(b : ℝ)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_two]
        have : 2 * |t| ≤ 1 := by linarith
        have h0 : 0 ≤ |(a : ℝ)| * |(b : ℝ)| := by positivity
        nlinarith [abs_nonneg t]
      have h2 := abs_le.mp hab
      nlinarith [sq_abs (a : ℝ), sq_abs (b : ℝ), sq_nonneg (|(a : ℝ)| - |(b : ℝ)|),
        mul_le_mul ha1 hb1 zero_le_one (abs_nonneg _)]
  rcases hz' with h | h
  · exact key _ _ h
  · have := key (z 1) (z 0) h
    nlinarith [this]

/-- **Minimum one.** If `C` has minimum one and `δ_C(w)² ≤ 1/2`, then `G(w,C)` takes a value
`≥ 1` on every nonzero integral vector `(k, z)`. -/
theorem Gmat_min_one {C : Mat2} (hC : C 1 0 = C 0 1) (hpsd : ∀ v, 0 ≤ quad C v)
    (hmin : ∀ z : Fin 2 → ℤ, z ≠ 0 → 1 ≤ quad C (intVec z)) (w : Vec2)
    (hδ : deltaSq C w ≤ 1/2) (k : ℤ) (z : Fin 2 → ℤ) (hkz : k ≠ 0 ∨ z ≠ 0) :
    1 ≤ vec3 (k : ℝ) (intVec z) ⬝ᵥ (Gmat w C *ᵥ vec3 (k : ℝ) (intVec z)) := by
  rw [Gmat_quad hC]
  have hd0 := deltaSq_nonneg hpsd w
  have hq := hpsd (intVec z + (k : ℝ) • w)
  rcases (show k = 0 ∨ k = 1 ∨ k = -1 ∨ 2 ≤ k ∨ k ≤ -2 by omega) with h | h | h | h | h
  · subst h
    have hz : z ≠ 0 := hkz.resolve_left (by simp)
    simpa using hmin z hz
  · subst h
    have := deltaSq_le hpsd w (-z)
    have e : intVec z + ((1 : ℤ) : ℝ) • w = w - intVec (-z) := by
      funext i; simp [intVec]; ring
    rw [e]
    push_cast
    nlinarith
  · subst h
    have := deltaSq_le hpsd w z
    have e : intVec z + ((-1 : ℤ) : ℝ) • w = -(w - intVec z) := by
      funext i; simp [intVec]; ring
    rw [e, quad_neg]
    push_cast
    nlinarith
  · have : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast h
      nlinarith
    nlinarith
  · have : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (k : ℝ) ≤ -2 := by exact_mod_cast h
      nlinarith
    nlinarith

/-- **Three minimal vectors.** For `|t| ≤ 1/2` and every `w` there is an integral vector
`(1, z)` of squared length exactly one for `G(w, C(t))` (a nearest lattice point), and the vectors
`(0,1,0)`, `(0,0,1)` also have squared length one; together they have determinant one. -/
theorem Gmat_min_vectors {t : ℝ} (ht : |t| ≤ 1/2) (w : Vec2) :
    ∃ z : Fin 2 → ℤ,
      vec3 1 (intVec z) ⬝ᵥ (Gmat w (Ct t) *ᵥ vec3 1 (intVec z)) = 1 ∧
      vec3 0 ![1, 0] ⬝ᵥ (Gmat w (Ct t) *ᵥ vec3 0 ![1, 0]) = 1 ∧
      vec3 0 ![0, 1] ⬝ᵥ (Gmat w (Ct t) *ᵥ vec3 0 ![0, 1]) = 1 ∧
      (!![1, (z 0 : ℤ), z 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := by
  have hC : (Ct t) 1 0 = (Ct t) 0 1 := by simp [Ct]
  have hpsd : ∀ v, 0 ≤ quad (Ct t) v := quad_Ct_nonneg (by linarith [abs_nonneg t])
  obtain ⟨z0, hz0⟩ := exists_nearest ht w
  have hdelta : deltaSq (Ct t) w = quad (Ct t) (w - intVec z0) := by
    apply le_antisymm (deltaSq_le hpsd w z0)
    exact le_deltaSq hz0
  refine ⟨-z0, ?_, ?_, ?_, ?_⟩
  · rw [Gmat_quad hC]
    have e : intVec (-z0) + (1 : ℝ) • w = w - intVec z0 := by
      funext i; simp [intVec]; ring
    rw [e, hdelta]; ring
  · rw [Gmat_quad hC]
    simp [quad_Ct]
  · rw [Gmat_quad hC]
    simp [quad_Ct]
  · simp [Matrix.det_fin_three]

/-! ### Equivariance under the integral parabolic -/

abbrev IMat2 := Matrix (Fin 2) (Fin 2) ℤ

/-- The real matrix underlying an integral binary matrix. -/
def castMat (D : IMat2) : Mat2 := D.map (Int.cast : ℤ → ℝ)

theorem quad_conj (C D : Mat2) (v : Vec2) : quad (Dᵀ * C * D) v = quad C (D *ᵥ v) := by
  simp [quad, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem castMat_mulVec_intVec (D : IMat2) (z : Fin 2 → ℤ) :
    castMat D *ᵥ intVec z = intVec (D *ᵥ z) := by
  funext i
  simp [castMat, Matrix.mulVec, dotProduct, intVec, Fin.sum_univ_two]

/-- `δ` is invariant under the change of variables `D w' = u + η w` by a unimodular `D`. -/
theorem deltaSq_conj (C : Mat2) (D E : IMat2) (hDE : D * E = 1) (hED : E * D = 1)
    (u : Fin 2 → ℤ) (η : ℤ) (hη : η = 1 ∨ η = -1) (w w' : Vec2)
    (hw : castMat D *ᵥ w' = intVec u + (η : ℝ) • w) :
    deltaSq ((castMat D)ᵀ * C * castMat D) w' = deltaSq C w := by
  have hηη : η * η = 1 := by rcases hη with rfl | rfl <;> norm_num
  let e : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
    { toFun := fun z => η • (D *ᵥ z - u)
      invFun := fun z' => E *ᵥ (η • z' + u)
      left_inv := by
        intro z
        simp only [smul_smul, hηη, one_smul, sub_add_cancel, Matrix.mulVec_mulVec, hED,
          Matrix.one_mulVec]
      right_inv := by
        intro z'
        simp only [add_sub_cancel_right, Matrix.mulVec_mulVec, hDE, Matrix.one_mulVec, smul_smul,
          hηη, one_smul] }
  unfold deltaSq
  refine Equiv.iInf_congr e ?_
  intro z
  symm
  show quad ((castMat D)ᵀ * C * castMat D) (w' - intVec z) =
    quad C (w - intVec (η • (D *ᵥ z - u)))
  rw [quad_conj, Matrix.mulVec_sub, hw, castMat_mulVec_intVec]
  have hη' : (η : ℝ) * (η : ℝ) = 1 := by exact_mod_cast hηη
  have key : intVec u + (η : ℝ) • w - intVec (D *ᵥ z) =
      (η : ℝ) • (w - intVec (η • (D *ᵥ z - u))) := by
    funext i
    simp only [intVec, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.smul_apply]
    push_cast
    linear_combination (((D *ᵥ z) i : ℝ) - (u i : ℝ)) * hη'
  have hη2 : (η : ℝ) ^ 2 = 1 := by rw [sq]; exact hη'
  rw [key, quad_smul, hη2, one_mul]

/-- Polarization for symmetric `3×3` matrices. -/
theorem symm_eq_of_quad_eq {A B : Mat3} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : ∀ v : Fin 3 → ℝ, v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (B *ᵥ v)) : A = B := by
  have a01 : A 0 1 = A 1 0 := by simpa using (congrFun (congrFun hA 0) 1).symm
  have a02 : A 0 2 = A 2 0 := by simpa using (congrFun (congrFun hA 0) 2).symm
  have a12 : A 1 2 = A 2 1 := by simpa using (congrFun (congrFun hA 1) 2).symm
  have b01 : B 0 1 = B 1 0 := by simpa using (congrFun (congrFun hB 0) 1).symm
  have b02 : B 0 2 = B 2 0 := by simpa using (congrFun (congrFun hB 0) 2).symm
  have b12 : B 1 2 = B 2 1 := by simpa using (congrFun (congrFun hB 1) 2).symm
  have h0 := h ![1, 0, 0]
  have h1 := h ![0, 1, 0]
  have h2 := h ![0, 0, 1]
  have h3 := h ![1, 1, 0]
  have h4 := h ![1, 0, 1]
  have h5 := h ![0, 1, 1]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at h0 h1 h2 h3 h4 h5
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- The matrix of the integral parabolic `p = [[η, 0],[u, D]]`. -/
def parab (η : ℤ) (u : Fin 2 → ℤ) (D : IMat2) : Mat3 :=
  !![(η : ℝ), 0, 0; (u 0 : ℝ), (D 0 0 : ℝ), (D 0 1 : ℝ); (u 1 : ℝ), (D 1 0 : ℝ), (D 1 1 : ℝ)]

theorem parab_vec (η : ℤ) (u : Fin 2 → ℤ) (D : IMat2) (k : ℝ) (z : Vec2) :
    parab η u D *ᵥ vec3 k z = vec3 (η * k) (k • intVec u + castMat D *ᵥ z) := by
  funext i
  fin_cases i <;> simp [parab, vec3, castMat, intVec, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three] <;> ring

theorem quad_conj3 (A P : Mat3) (v : Fin 3 → ℝ) :
    v ⬝ᵥ ((Pᵀ * A * P) *ᵥ v) = (P *ᵥ v) ⬝ᵥ (A *ᵥ (P *ᵥ v)) := by
  simp [dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem castMat_symm {C : Mat2} (hC : Cᵀ = C) (D : IMat2) :
    ((castMat D)ᵀ * C * castMat D)ᵀ = (castMat D)ᵀ * C * castMat D := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hC, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **Equivariance.** For `p = [[η,0],[u,D]]` with `η = ±1`, `u ∈ ℤ²` and `D ∈ GL₂(ℤ)`, and
`D w' = u + η w`: `pᵗ G(w,C) p = G(w', DᵗCD)` (so `w' = D⁻¹(u + ηw)`, `C' = DᵗCD`). -/
theorem Gmat_equivariant {C : Mat2} (hC : Cᵀ = C) (D E : IMat2) (hDE : D * E = 1)
    (hED : E * D = 1) (u : Fin 2 → ℤ) (η : ℤ) (hη : η = 1 ∨ η = -1) (w w' : Vec2)
    (hw : castMat D *ᵥ w' = intVec u + (η : ℝ) • w) :
    (parab η u D)ᵀ * Gmat w C * parab η u D =
      Gmat w' ((castMat D)ᵀ * C * castMat D) := by
  have hC10 : C 1 0 = C 0 1 := by simpa using congrFun (congrFun hC 0) 1
  have hC' := castMat_symm hC D
  have hC'10 : ((castMat D)ᵀ * C * castMat D) 1 0 = ((castMat D)ᵀ * C * castMat D) 0 1 := by
    simpa using congrFun (congrFun hC' 0) 1
  have hd := deltaSq_conj C D E hDE hED u η hη w w' hw
  have hη' : (η : ℝ) * (η : ℝ) = 1 := by
    rcases hη with rfl | rfl <;> norm_num
  apply symm_eq_of_quad_eq
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Gmat_symm hC,
      Matrix.mul_assoc]
  · exact Gmat_symm hC' w'
  · intro v
    have hv : v = vec3 (v 0) ![v 1, v 2] := by
      funext i; fin_cases i <;> simp [vec3]
    rw [quad_conj3, hv, parab_vec, Gmat_quad hC10, Gmat_quad hC'10, hd, quad_conj]
    have e : castMat D *ᵥ (![v 1, v 2] + v 0 • w') = (v 0) • intVec u + castMat D *ᵥ ![v 1, v 2]
        + ((η : ℝ) * v 0) • w := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hw]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    have : ((η : ℝ) * v 0) ^ 2 = v 0 ^ 2 := by
      have := hη'
      nlinarith [this]
    rw [this]

/-- `G(·,C)` is injective (for positive definite `C`) and determines `C`. -/
theorem Gmat_injective {C C' : Mat2} (hC : ∀ v, v ≠ 0 → 0 < quad C v) {w w' : Vec2}
    (h : Gmat w C = Gmat w' C') : C = C' ∧ w = w' := by
  have hCC : C = C' := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Gmat] using congrFun (congrFun h 1) 1
    · simpa [Gmat] using congrFun (congrFun h 1) 2
    · simpa [Gmat] using congrFun (congrFun h 2) 1
    · simpa [Gmat] using congrFun (congrFun h 2) 2
  subst hCC
  refine ⟨rfl, ?_⟩
  have h1 : (C *ᵥ w) 0 = (C *ᵥ w') 0 := by simpa [Gmat] using congrFun (congrFun h 0) 1
  have h2 : (C *ᵥ w) 1 = (C *ᵥ w') 1 := by simpa [Gmat] using congrFun (congrFun h 0) 2
  by_contra hne
  have hv : w - w' ≠ 0 := sub_ne_zero.mpr hne
  have hq := hC _ hv
  have hz : C *ᵥ (w - w') = 0 := by
    funext i
    rw [Matrix.mulVec_sub]
    fin_cases i
    · show (C *ᵥ w) 0 - (C *ᵥ w') 0 = 0
      linarith
    · show (C *ᵥ w) 1 - (C *ᵥ w') 1 = 0
      linarith
  have : quad C (w - w') = 0 := by simp [quad, hz]
  linarith

/-! ### The unit-diagonal ternary cell -/

/-- The Voronoi cell of `0` for the form `C`: the points at least as close to `0` as to any other
lattice point. -/
def Voronoi (C : Mat2) : Set Vec2 := {w | quad C w = deltaSq C w}

theorem mem_Voronoi_iff {t : ℝ} (ht : |t| ≤ 1/2) (w : Vec2) :
    w ∈ Voronoi (Ct t) ↔ ∀ z : Fin 2 → ℤ, quad (Ct t) w ≤ quad (Ct t) (w - intVec z) := by
  have hpsd : ∀ v, 0 ≤ quad (Ct t) v := quad_Ct_nonneg (by linarith [abs_nonneg t])
  constructor
  · intro h z
    have h0 := deltaSq_le hpsd w z
    have h' : quad (Ct t) w = deltaSq (Ct t) w := h
    linarith
  · intro h
    show quad (Ct t) w = deltaSq (Ct t) w
    apply le_antisymm
    · exact le_deltaSq h
    · have := deltaSq_le hpsd w 0
      have e : intVec (0 : Fin 2 → ℤ) = 0 := by funext i; simp [intVec]
      rw [e, sub_zero] at this
      exact this

/-- Integral vectors as real vectors. -/
def castVec3 (v : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (v i : ℝ)

theorem vec3_eq_castVec3 (k : ℤ) (z : Fin 2 → ℤ) :
    vec3 (k : ℝ) (intVec z) = castVec3 ![k, z 0, z 1] := by
  funext i; fin_cases i <;> simp [vec3, castVec3, intVec]

/-- **The standard ternary top cell**: positive definite forms with unit diagonal and minimum
at least one on nonzero integral vectors. -/
def Tcell : Set Mat3 :=
  {A | PosDefQ A ∧ A 0 0 = 1 ∧ A 1 1 = 1 ∧ A 2 2 = 1 ∧
    ∀ v : Fin 3 → ℤ, v ≠ 0 → 1 ≤ castVec3 v ⬝ᵥ (A *ᵥ castVec3 v)}

theorem Gmat_mem_Tcell {t : ℝ} (ht : |t| ≤ 1/2) {w : Vec2} (hw : w ∈ Voronoi (Ct t)) :
    Gmat w (Ct t) ∈ Tcell := by
  have hC : (Ct t) 1 0 = (Ct t) 0 1 := by simp [Ct]
  have hpsd : ∀ v, 0 ≤ quad (Ct t) v := quad_Ct_nonneg (by linarith [abs_nonneg t])
  have hδ : deltaSq (Ct t) w ≤ 1/2 := by
    refine le_trans (deltaSq_Ct_le ht w) ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg t]
  have hw' : quad (Ct t) w = deltaSq (Ct t) w := hw
  refine ⟨Gmat_posDef ht w, ?_, by simp [Gmat, Ct], by simp [Gmat, Ct], ?_⟩
  · simp [Gmat, hw']
  · intro v hv
    have hv3 : castVec3 v = vec3 ((v 0 : ℤ) : ℝ) (intVec ![v 1, v 2]) := by
      funext i; fin_cases i <;> simp [vec3, castVec3, intVec]
    rw [hv3]
    refine Gmat_min_one hC hpsd (fun z hz => Ct_min_one ht z hz) w hδ (v 0) ![v 1, v 2] ?_
    by_contra h
    push Not at h
    apply hv
    funext i
    fin_cases i
    · exact h.1
    · exact congrFun h.2 0
    · exact congrFun h.2 1

theorem Ct_injective {t t' : ℝ} (h : Ct t = Ct t') : t = t' := by
  simpa [Ct] using congrFun (congrFun h 0) 1

/-- `i` is injective on `{(w, t) : |t| ≤ 1/2}`: `G(w, C(t))` determines `t` and `w`. -/
theorem Gmat_Ct_injective {t t' : ℝ} (ht : |t| ≤ 1/2) {w w' : Vec2}
    (h : Gmat w (Ct t) = Gmat w' (Ct t')) : t = t' ∧ w = w' := by
  obtain ⟨hC, hw⟩ := Gmat_injective (fun v hv => Ct_pos ht v hv) h
  exact ⟨Ct_injective hC, hw⟩

/-- **The cell is parametrized by `(w, t)`.** Every form of the unit-diagonal ternary cell is
`G(w, C(t))` for a unique `|t| ≤ 1/2` and `w` in the Voronoi cell of `0`. -/
theorem Tcell_eq_Gmat {A : Mat3} (hA : A ∈ Tcell) :
    ∃ t : ℝ, |t| ≤ 1/2 ∧ ∃ w ∈ Voronoi (Ct t), A = Gmat w (Ct t) := by
  obtain ⟨⟨hsym, _⟩, h00, h11, h22, hmin⟩ := hA
  have s01 : A 1 0 = A 0 1 := by simpa using congrFun (congrFun hsym 0) 1
  have s02 : A 2 0 = A 0 2 := by simpa using congrFun (congrFun hsym 0) 2
  have s12 : A 2 1 = A 1 2 := by simpa using congrFun (congrFun hsym 1) 2
  have hm1 := hmin ![0, 1, -1] (by intro h; have := congrFun h 1; simp at this)
  have hm2 := hmin ![0, 1, 1] (by intro h; have := congrFun h 1; simp at this)
  simp [castVec3, dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hm1 hm2
  obtain ⟨t, ht12⟩ : ∃ t : ℝ, A 1 2 = t := ⟨_, rfl⟩
  have s12' : A 2 1 = t := by rw [s12, ht12]
  have ht : |t| ≤ 1/2 := by
    rw [abs_le]
    constructor <;> nlinarith [h11, h22, s12']
  have hd : 1 - t ^ 2 ≠ 0 := by
    have := abs_le.mp ht
    nlinarith
  obtain ⟨w, hw0, hw1⟩ : ∃ w : Vec2, w 0 + t * w 1 = A 0 1 ∧ t * w 0 + w 1 = A 0 2 :=
    ⟨![(A 0 1 - t * A 0 2) / (1 - t ^ 2), (A 0 2 - t * A 0 1) / (1 - t ^ 2)], by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; field_simp; ring, by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; field_simp; ring⟩
  have hvor : w ∈ Voronoi (Ct t) := by
    rw [mem_Voronoi_iff ht]
    intro z
    have hz := hmin ![1, -z 0, -z 1] (by intro h; have := congrFun h 0; simp at this)
    simp [castVec3, dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hz
    simp only [s01, s02, s12', ht12, h00, h11, h22] at hz
    have hz' : (0 : ℝ) ≤ (z 0 : ℝ) ^ 2 + 2 * t * z 0 * z 1 + (z 1 : ℝ) ^ 2 -
        2 * (A 0 1 * z 0 + A 0 2 * z 1) := by
      nlinarith [hz]
    rw [quad_Ct, quad_Ct]
    simp only [intVec, Pi.sub_apply]
    have e : ((w 0 - z 0) ^ 2 + 2 * t * (w 0 - z 0) * (w 1 - z 1) + (w 1 - z 1) ^ 2) -
        (w 0 ^ 2 + 2 * t * w 0 * w 1 + w 1 ^ 2) =
        ((z 0 : ℝ) ^ 2 + 2 * t * z 0 * z 1 + (z 1 : ℝ) ^ 2 - 2 * (A 0 1 * z 0 + A 0 2 * z 1)) := by
      linear_combination (-2 * (z 0 : ℝ)) * hw0 + (-2 * (z 1 : ℝ)) * hw1
    linarith [e, hz']
  have hdelta : deltaSq (Ct t) w = quad (Ct t) w := (hvor : quad (Ct t) w = deltaSq (Ct t) w).symm
  have c0 : (Ct t *ᵥ w) 0 = w 0 + t * w 1 := by
    simp [Ct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have c1 : (Ct t *ᵥ w) 1 = t * w 0 + w 1 := by
    simp [Ct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨t, ht, w, hvor, ?_⟩
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · show A 0 0 = 1 + quad (Ct t) w - deltaSq (Ct t) w
    rw [hdelta, h00]; ring
  · show A 0 1 = (Ct t *ᵥ w) 0
    rw [c0, hw0]
  · show A 0 2 = (Ct t *ᵥ w) 1
    rw [c1, hw1]
  · show A 1 0 = (Ct t *ᵥ w) 0
    rw [c0, hw0, s01]
  · show A 1 1 = Ct t 0 0
    simp [Ct, h11]
  · show A 1 2 = Ct t 0 1
    simp [Ct, ht12]
  · show A 2 0 = (Ct t *ᵥ w) 1
    rw [c1, hw1, s02]
  · show A 2 1 = Ct t 1 0
    simp [Ct, s12']
  · show A 2 2 = Ct t 1 1
    simp [Ct, h22]

end TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry
