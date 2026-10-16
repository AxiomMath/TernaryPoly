module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBig
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Levi
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KNeg

@[expose] public section


/-!
# Bruhat evaluation of the orbit integrals of the line row

And `eq:intertwiner`, `(Tφ)(g) = ∫ φ(w₀⁻¹ u(s,t) g) ds dt`.

The orbit integral of the line row is `∫_{ℝ²} orbitIntegrand h G u du`, with `G = k γ_o ∈ SL₃(ℤ)` and
`orbitIntegrand h G u` the coefficient of the `jFace`-pullback of the summand `S_h(G qMat u)`.

* `integral_orbit_shift`: Lebesgue measure is translation invariant, so the integral depends on `G` only
  modulo right multiplication by `qMat w`.
* `bruhatP G = G qMat(bw G) w₀ ∈ P(ℝ)`: for `G₂₀ ≠ 0`, `G qMat(bw G) = bruhatP G · w₀⁻¹` with `bruhatP G`
  of bottom row `(0, 0, G₂₀)` (the big Bruhat cell `P w₀⁻¹ Q`).
* The Levi step: for `P` of bottom row `(0,0,c)`, `c > 0`, `S_h(P G) = S_{h|A}(G)` (`A` the top block of
  `P`, `det A = 1/c`); for `c < 0`, `S_h(P G)` is the conjugate (`cxP true`) summand of
  `hStar (h|A⁺)`, `A⁺ = A diag(1,-1)`: the sign of the line row.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial ComplexConjugate
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi

section Weyl

/-- The Weyl element `w₀ = [[0,0,1],[1,0,0],[0,1,0]]` of the paper. -/
def W0 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- Its inverse `w₀⁻¹ = w₀ᵀ`. -/
def W0inv : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem W0_mul_W0inv : W0 * W0inv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W0, W0inv, Matrix.mul_apply, Fin.sum_univ_three]

theorem W0inv_mul_W0 : W0inv * W0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W0, W0inv, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_W0 : W0.det = 1 := by
  simp [W0, Matrix.det_fin_three]

theorem det_W0inv : W0inv.det = 1 := by
  simp [W0inv, Matrix.det_fin_three]

end Weyl

section Integrand

variable (n : ℕ)

/-- **The orbit integrand**: the `m`-th coefficient of the `jFace`-pullback of the summand `S_h(G · qMat u)`
at the face point `x`, evaluated on `(e_p, e_q)`. -/
def orbitIntegrand (h : ℂ → ℂ) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 2 → ℝ) : ℂ :=
  (fPull jFace (fun y a b => summandPoly n h (G * qMat u) y a b) x p q).coeff m

theorem orbitIntegrand_shift (h : ℂ → ℂ) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (u w : Fin 2 → ℝ) :
    orbitIntegrand n h x p q m G (w + u) = orbitIntegrand n h x p q m (G * qMat w) u := by
  unfold orbitIntegrand
  rw [Matrix.mul_assoc, qMat_mul]

/-- **Translation invariance**: the orbit integral depends on `G` only modulo `qMat`-translations. -/
theorem integral_orbit_shift (h : ℂ → ℂ) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 2 → ℝ) :
    ∫ u : Fin 2 → ℝ, orbitIntegrand n h x p q m (G * qMat w) u =
      ∫ u : Fin 2 → ℝ, orbitIntegrand n h x p q m G u := by
  simp_rw [← orbitIntegrand_shift]
  exact integral_add_left_eq_self (μ := volume) (fun u => orbitIntegrand n h x p q m G u) w

theorem PhiQ0_eq_orbitIntegrand (N : ℕ) (k : SL(3, ℤ)) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : Ck N k) (u : Fin 2 → ℝ) :
    PhiQ0 N k n f x p q m c u =
      orbitIntegrand n (hfun f) x p q m (realMat k * realMat (Quotient.out c).1) u := rfl

end Integrand

section Bruhat

/-- The translation of the big cell: `w_G = (G₂₂/G₂₀, G₂₁/G₂₀)`. -/
def bw (G : Matrix (Fin 3) (Fin 3) ℝ) : Fin 2 → ℝ := ![G 2 2 / G 2 0, G 2 1 / G 2 0]

/-- **The parabolic Bruhat representative**: `G qMat(bw G) = bruhatP G · w₀⁻¹`. -/
def bruhatP (G : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := G * qMat (bw G) * W0

theorem bruhat_decomp (G : Matrix (Fin 3) (Fin 3) ℝ) : G * qMat (bw G) = bruhatP G * W0inv := by
  unfold bruhatP
  rw [Matrix.mul_assoc, W0_mul_W0inv, Matrix.mul_one]

theorem bruhatP_row (G : Matrix (Fin 3) (Fin 3) ℝ) (h0 : G 2 0 ≠ 0) :
    bruhatP G 2 0 = 0 ∧ bruhatP G 2 1 = 0 ∧ bruhatP G 2 2 = G 2 0 := by
  unfold bruhatP bw W0 qMat
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

theorem det_bruhatP (G : Matrix (Fin 3) (Fin 3) ℝ) : (bruhatP G).det = G.det := by
  unfold bruhatP
  rw [Matrix.det_mul, Matrix.det_mul, det_qMat, det_W0]; ring

end Bruhat

section Levi

theorem planeAct_transDiag (v0 v1 : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (hA : 0 < A.det)
    (ht : 0 < t) (hAt : A.det * t = 1) {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    planeAct (transMat v0 v1 * diagMat A t) x = leviMap A t x + ![v0, v1, 0, 0, 0] := by
  have hd : (diagMat A t).det = 1 := by rw [det_diagMat]; exact hAt
  have hm : leviMap A t x ∈ Omega := by
    rw [← planeAct_diag A t hA ht hAt hx]; exact planeAct_mem hd hx
  rw [planeAct_mul hd hx, planeAct_diag A t hA ht hAt hx, planeAct_transMat v0 v1 hm]

theorem formPullback_transDiag_seed (n : ℕ) (h : ℂ → ℂ) (v0 v1 : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) (hA : 0 < A.det) (ht : 0 < t) (hAt : A.det * t = 1) {y : Fin 5 → ℝ} (hy : y ∈ Omega)
    (a b : Fin 5) :
    formPullback (planeAct (transMat v0 v1 * diagMat A t)) (seedForm n h) y a b =
      rho (transMat v0 v1 * diagMat A t) (seedForm n (slashTwisted (n + 3) A h) y a b) := by
  have hev : planeAct (transMat v0 v1 * diagMat A t) =ᶠ[nhds y]
      fun x => leviMap A t x + ![v0, v1, 0, 0, 0] :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hy) fun x hx =>
      planeAct_transDiag v0 v1 A t hA ht hAt hx
  rw [formPullback_congr _ hev, SeedC3.formPullback_translate,
    (TernaryPeriodPolynomials.seed_closed_equivariant n h).2.2.1 A t hA ht y hy.1 a b,
    rho_diagMat A t hA.ne' ht.ne', rho_transMat, rho_mul]

/-- **Left multiplication by `trans · diag(A, t)` (determinant one) changes `h` into `h|A`.** -/
theorem summandPoly_transDiag_mul (n : ℕ) (h : ℂ → ℂ) (v0 v1 : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) (hA : 0 < A.det) (ht : 0 < t) (hAt : A.det * t = 1) {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hG : G.det = 1) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n h (transMat v0 v1 * diagMat A t * G) q i j =
      summandPoly n (slashTwisted (n + 3) A h) G q i j := by
  set L := transMat v0 v1 * diagMat A t with hLdef
  have hL : L.det = 1 := by rw [hLdef, Matrix.det_mul, det_transMat, det_diagMat, hAt]; norm_num
  have hq' := planeAct_mem hG hq
  have hev : planeAct (L * G) =ᶠ[nhds q] planeAct L ∘ planeAct G :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq) fun x hx => planeAct_mul hG hx
  unfold summandPoly
  rw [formPullback_congr _ hev, formPullback_comp _ _ _ q (differentiableAt_planeAct hG hq)
    (differentiableAt_planeAct hL hq') i j]
  rw [formPullback_congr_form (Φ := planeAct G)
      (ν' := fun x a b => rho L (seedForm n (slashTwisted (n + 3) A h) x a b)) q
      (fun a b => formPullback_transDiag_seed n h v0 v1 A t hA ht hAt hq' a b) i j,
    EisensteinClass.formPullback_rho, rho_mul]
  have hLu : IsUnit L.det := by rw [hL]; exact isUnit_one
  have hinv : (L * G)⁻¹ * L = G⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.mul_one]
  rw [hinv]

/-- **Positive Levi step**: for `P` of bottom row `(0, 0, c)`, `c > 0`, `det P = 1`, the summand of `P G` is
the summand of `G` for the slashed form `h|A`, `A` the top block of `P` (of determinant `1/c`). -/
theorem summandPoly_bottom_mul (n : ℕ) (h : ℂ → ℂ) {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : P.det = 1)
    (h0 : P 2 0 = 0) (h1 : P 2 1 = 0) (hc : 0 < P 2 2) {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hG : G.det = 1) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n h (P * G) q i j =
      summandPoly n (slashTwisted (n + 3) (topBlock P) h) G q i j := by
  have hdetA : (topBlock P).det * P 2 2 = 1 := by
    have : P.det = (topBlock P).det * P 2 2 := by
      simp [topBlock, Matrix.det_fin_three, Matrix.det_fin_two, h0, h1]; ring
    rw [← this]; exact hP
  have hApos : 0 < (topBlock P).det := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have e : P = transMat (P 0 2 / P 2 2) (P 1 2 / P 2 2) * diagMat (topBlock P) (P 2 2) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [transMat, diagMat, topBlock, Matrix.mul_apply, Fin.sum_univ_three, h0, h1] <;>
      field_simp
  have := summandPoly_transDiag_mul n h (P 0 2 / P 2 2) (P 1 2 / P 2 2) (topBlock P) (P 2 2)
    hApos hc hdetA hG hq i j
  rw [← e] at this
  exact this

end Levi

section Reflection

open ComplexConjugate

theorem summandPoly_rPrime (n : ℕ) (h : ℂ → ℂ) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    summandPoly n h (realMat rPrime) y i j =
      cxP true (seedForm n (hStar h) y i j) := by
  have hrefl : planeAct (realMat rPrime) =ᶠ[nhds y] reflMap5 :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hy) fun z hz => planeAct_rPrime hz
  unfold summandPoly
  rw [formPullback_congr _ hrefl, refl_pullback n h (hStar h) y rfl i j]
  have hhom : (MvPolynomial.map (starRingEnd ℂ) (seedForm n (hStar h) y i j)).IsHomogeneous n :=
    (seedForm_isHomogeneous n (hStar h) y i j).map _
  have := rho_rPrime_refl _ hhom
  rw [this]
  rfl

end Reflection

section Negative

open ComplexConjugate

theorem realMat_rPrime_mul_self : realMat rPrime * realMat rPrime = 1 := by
  rw [← realMat_mul, rPrime_mul_self, realMat_one]

/-- **Negative Levi step (the sign of the line row)**: for `P` of bottom row `(0, 0, c)`, `c < 0`, the summand
of `P G` is the conjugate summand (`cxP true`) of `hStar (h|A⁺)`, `A⁺` the top block of `P diag(1,-1,-1)`. -/
theorem summandPoly_bottom_neg_mul (n : ℕ) (h : ℂ → ℂ) {P : Matrix (Fin 3) (Fin 3) ℝ}
    (hP : P.det = 1) (h0 : P 2 0 = 0) (h1 : P 2 1 = 0) (hc : P 2 2 < 0)
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n h (P * G) q i j =
      cxP true (summandPoly n (hStar (slashTwisted (n + 3) (topBlock (P * realMat rPrime)) h)) G q i j) := by
  set R := realMat rPrime with hR
  have hRd : R.det = 1 := det_realMat rPrime
  have hRR : R * R = 1 := realMat_rPrime_mul_self
  have hP'd : (P * R).det = 1 := by rw [Matrix.det_mul, hP, hRd]; norm_num
  have hP'0 : (P * R) 2 0 = 0 := by
    simp [hR, realMat_rPrime, Matrix.mul_apply, Fin.sum_univ_three, h0]
  have hP'1 : (P * R) 2 1 = 0 := by
    simp [hR, realMat_rPrime, Matrix.mul_apply, Fin.sum_univ_three, h1]
  have hP'2 : 0 < (P * R) 2 2 := by
    have : (P * R) 2 2 = -P 2 2 := by
      simp [hR, realMat_rPrime, Matrix.mul_apply, Fin.sum_univ_three, h0, h1]
    rw [this]; linarith
  have hRG : (R * G).det = 1 := by rw [Matrix.det_mul, hRd, hG]; norm_num
  have e : P * G = (P * R) * (R * G) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc R R G, hRR, Matrix.one_mul]
  have hq' : planeAct G q ∈ Omega := planeAct_mem hG hq
  rw [e, summandPoly_bottom_mul n h hP'd hP'0 hP'1 hP'2 hRG hq i j,
    summandPoly_mul_eq n _ hRd hG hq i j]
  set hp := slashTwisted (n + 3) (topBlock (P * R)) h with hhp
  rw [formPullback_congr_form (Φ := planeAct G)
    (ν' := fun y a b => cxP true (seedForm n (hStar hp) y a b)) q
    (fun a b => summandPoly_rPrime n hp hq' a b) i j, formPullback_cxP, rho_cxP]
  unfold summandPoly
  rfl

end Negative

section Evaluation

variable (n : ℕ)

/-- **The real intertwining integral of a seed** `h`: `T_∞[h](x; e_p, e_q)_m =
∫_{ℝ²} coeff_m (jFace^* S_h(w₀⁻¹ qMat u))(x; e_p, e_q) du`, i.e. the printed integrand
`φ(w₀⁻¹ u(s,t) g)` of `eq:intertwiner` at the frame point `jFace x` (with `u(s,t) = qMat (−t,−s)`). -/
def Tinf (h : ℂ → ℂ) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) : ℂ :=
  ∫ u : Fin 2 → ℝ, orbitIntegrand n h x p q m W0inv u

theorem orbitIntegrand_bottom_mul (h : ℂ → ℂ) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : P.det = 1) (h0 : P 2 0 = 0)
    (h1 : P 2 1 = 0) (hc : 0 < P 2 2) (u : Fin 2 → ℝ) :
    orbitIntegrand n h x p q m (P * W0inv) u =
      orbitIntegrand n (slashTwisted (n + 3) (topBlock P) h) x p q m W0inv u := by
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  have hG : (W0inv * qMat u).det = 1 := by rw [Matrix.det_mul, det_W0inv, det_qMat]; norm_num
  unfold orbitIntegrand
  rw [fPull_congr_at jFace _ (fun y a b => summandPoly n (slashTwisted (n + 3) (topBlock P) h)
    (W0inv * qMat u) y a b) x (fun a b => by
      rw [Matrix.mul_assoc]
      exact summandPoly_bottom_mul n h hP h0 h1 hc hG hy a b) p q]

theorem orbitIntegrand_bottom_neg_mul (h : ℂ → ℂ) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : P.det = 1) (h0 : P 2 0 = 0)
    (h1 : P 2 1 = 0) (hc : P 2 2 < 0) (u : Fin 2 → ℝ) :
    orbitIntegrand n h x p q m (P * W0inv) u =
      conj (orbitIntegrand n (hStar (slashTwisted (n + 3) (topBlock (P * realMat rPrime)) h))
        x p q m W0inv u) := by
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  have hG : (W0inv * qMat u).det = 1 := by rw [Matrix.det_mul, det_W0inv, det_qMat]; norm_num
  unfold orbitIntegrand
  rw [fPull_congr_at jFace _ (fun y a b => cxP true (summandPoly n
    (hStar (slashTwisted (n + 3) (topBlock (P * realMat rPrime)) h)) (W0inv * qMat u) y a b)) x
    (fun a b => by
      rw [Matrix.mul_assoc]
      exact summandPoly_bottom_neg_mul n h hP h0 h1 hc hG hy a b) p q,
    fPull_cxP, coeff_cxP]
  rfl

end Evaluation

section Orbits

variable (n : ℕ)

theorem topBlock_bruhatP (G : Matrix (Fin 3) (Fin 3) ℝ) :
    topBlock (bruhatP G) =
      !![G 0 1 - G 0 0 * (G 2 1 / G 2 0), G 0 2 - G 0 0 * (G 2 2 / G 2 0);
        G 1 1 - G 1 0 * (G 2 1 / G 2 0), G 1 2 - G 1 0 * (G 2 2 / G 2 0)] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [topBlock, bruhatP, bw, qMat, W0, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_topBlock_bruhatP (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.det = 1) (h0 : G 2 0 ≠ 0) :
    (topBlock (bruhatP G)).det = (G 2 0)⁻¹ := by
  obtain ⟨r0, r1, r2⟩ := bruhatP_row G h0
  have hd : (bruhatP G).det = (topBlock (bruhatP G)).det * bruhatP G 2 2 := by
    simp [topBlock, Matrix.det_fin_three, Matrix.det_fin_two, r0, r1]; ring
  rw [det_bruhatP, hG, r2] at hd
  field_simp
  linarith

/-- **Positive orbit (`r₀ > 0`)**: the orbit integral is the real intertwining integral of `h|A`,
`A = ` top block of the Bruhat representative (`det A = 1/r₀`). -/
theorem integral_orbit_pos (h : ℂ → ℂ) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) (h0 : 0 < G 2 0) :
    ∫ u : Fin 2 → ℝ, orbitIntegrand n h x p q m G u =
      Tinf n (slashTwisted (n + 3) (topBlock (bruhatP G)) h) x p q m := by
  obtain ⟨r0, r1, r2⟩ := bruhatP_row G h0.ne'
  have hPd : (bruhatP G).det = 1 := by rw [det_bruhatP, hG]
  rw [← integral_orbit_shift n h x p q m G (bw G), bruhat_decomp]
  unfold Tinf
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact orbitIntegrand_bottom_mul n h hx p q m hPd r0 r1 (by rw [r2]; exact h0) u

/-- **Negative orbit (`r₀ < 0`)**: the orbit integral is the complex conjugate of the real intertwining
integral of the reflected seed `hStar (h|A⁺)`, `A⁺ = ` top block of `bruhatP G · diag(1,-1,-1)`. -/
theorem integral_orbit_neg (h : ℂ → ℂ) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) (h0 : G 2 0 < 0) :
    ∫ u : Fin 2 → ℝ, orbitIntegrand n h x p q m G u =
      conj (Tinf n (hStar (slashTwisted (n + 3) (topBlock (bruhatP G * realMat rPrime)) h))
        x p q m) := by
  obtain ⟨r0, r1, r2⟩ := bruhatP_row G h0.ne
  have hPd : (bruhatP G).det = 1 := by rw [det_bruhatP, hG]
  rw [← integral_orbit_shift n h x p q m G (bw G), bruhat_decomp]
  unfold Tinf
  rw [← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact orbitIntegrand_bottom_neg_mul n h hx p q m hPd r0 r1 (by rw [r2]; exact h0) u

end Orbits

section Assembly

open ComplexConjugate

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The real matrix `k γ_c` of a coset. -/
def orbitMat (c : Ck N k) : Matrix (Fin 3) (Fin 3) ℝ := realMat (k * (Quotient.out c).1)

omit [NeZero N] in
theorem orbitMat_det (c : Ck N k) : (orbitMat N k c).det = 1 := det_realMat _

omit [NeZero N] in
theorem orbitMat_row0 (c : Ck N k) :
    orbitMat N k c 2 0 = ((cuspRow (gammaN N) (CuspData.ofSL k).r c 0 : ℤ) : ℝ) := by
  rw [cuspRow_out]
  simp [orbitMat, realMat_apply]

/-- The sign of the line row: `true` iff the first entry of the bottom row of `k γ_c` is negative. -/
def orbitSign (c : Ck N k) : Bool := decide (orbitMat N k c 2 0 < 0)

/-- **The seed attached to an orbit**: `h|A` (positive orbit) or `hStar (h|A⁺)` (negative orbit). -/
def orbitSeed (c : Ck N k) : ℂ → ℂ :=
  if 0 < orbitMat N k c 2 0 then
    slashTwisted (n + 3) (topBlock (bruhatP (orbitMat N k c))) (hfun f)
  else
    hStar (slashTwisted (n + 3) (topBlock (bruhatP (orbitMat N k c) * realMat rPrime)) (hfun f))

omit [NeZero N] in
theorem PhiQ0_eq_orbitMat (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : Ck N k) (u : Fin 2 → ℝ) :
    PhiQ0 N k n f x p q m c u = orbitIntegrand n (hfun f) x p q m (orbitMat N k c) u := by
  unfold PhiQ0 orbitIntegrand orbitMat
  rw [realMat_mul]

omit [NeZero N] in
/-- **The ℝ² integral of an orbit representative is a real intertwining integral.** -/
theorem PhiQ0_integral_eval {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : Ck N k)
    (hr : cuspRow (gammaN N) (CuspData.ofSL k).r c 0 ≠ 0) :
    ∫ u : Fin 2 → ℝ, PhiQ0 N k n f x p q m c u =
      cx (orbitSign N k c) (Tinf n (orbitSeed N k n f c) x p q m) := by
  have hne : orbitMat N k c 2 0 ≠ 0 := by
    rw [orbitMat_row0]; exact_mod_cast hr
  simp_rw [PhiQ0_eq_orbitMat]
  by_cases hpos : 0 < orbitMat N k c 2 0
  · have := integral_orbit_pos n (hfun f) hx p q m (orbitMat_det N k c) hpos
    have hnl : ¬ orbitMat N k c 2 0 < 0 := not_lt.2 hpos.le
    simp [orbitSign, orbitSeed, hpos, hnl, this, cx]
  · have hneg : orbitMat N k c 2 0 < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne
    have := integral_orbit_neg n (hfun f) hx p q m (orbitMat_det N k c) hneg
    simp [orbitSign, orbitSeed, hpos, hneg, this, cx]

omit [NeZero N] in
theorem integral_comp_smul_N (F : (Fin 2 → ℝ) → ℂ) :
    ∫ v : Fin 2 → ℝ, F ((N : ℝ) • v) = ((N : ℂ) ^ 2)⁻¹ * ∫ u : Fin 2 → ℝ, F u := by
  rw [MeasureTheory.Measure.integral_comp_smul]
  have h2 : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  have h3 : |((N : ℝ) ^ 2)⁻¹| = ((N : ℝ) ^ 2)⁻¹ := abs_of_nonneg (by positivity)
  rw [h2, h3, Complex.real_smul]
  push_cast
  rfl

/-- **Evaluation of the explicit line coefficient** (holomorphic and antiholomorphic type `b`):
`lineA1K = N⁻² Σ_{free orbits o} cx b (cx (sign o) (T_∞[seed_o]))`, with the explicit real intertwining
integral `Tinf`, `seed_o = h|A_o` for `r₀ > 0` and `hStar (h|A_o⁺)` (conjugated) for `r₀ < 0`. -/
theorem lineA1K_eval (b : Bool) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    lineA1K N k n f b x p q m = ((N : ℂ) ^ 2)⁻¹ *
      ∑' o : {o : Quotient (qActK N k).orbSetoid // (qActK N k).r0Q o ≠ 0},
        cx b (cx (orbitSign N k (Quotient.out o.1))
          (Tinf n (orbitSeed N k n f (Quotient.out o.1)) x p q m)) := by
  unfold lineA1K
  rw [← tsum_mul_left]
  refine tsum_congr fun o => ?_
  have hr : cuspRow (gammaN N) (CuspData.ofSL k).r (Quotient.out o.1) 0 ≠ 0 := by
    have := o.2
    rw [QAct.r0Q_out] at this
    exact this
  have hint : ∫ v : Fin 2 → ℝ, cxL b (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) =
      cx b (∫ v : Fin 2 → ℝ, PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) := by
    simp_rw [cxL_apply]
    cases b
    · simp [cx]
    · simp only [cx, ite_true]
      exact integral_conj
  rw [hint, integral_comp_smul_N, PhiQ0_integral_eval N k n f hx p q m _ hr]
  cases b <;> simp [cx]

end Assembly

end TernaryPeriodPolynomials.Argument.EisensteinClass
