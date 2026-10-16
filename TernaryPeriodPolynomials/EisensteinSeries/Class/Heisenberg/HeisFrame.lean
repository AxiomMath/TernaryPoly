module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisGauge
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.PullbackAlgebra

@[expose] public section



/-!
# Differential forms on the Heisenberg chart in the left-invariant frame and the gauge of a unipotent representation

Formalized by Claude Sonnet 5.5.

For a smooth `E`-valued form `ω` on `Pt = ℝ³` (Mathlib's `ContinuousAlternatingMap`-valued functions with `extDeriv`):

* `A1 ω k = ω(X_k)`, `A2 ω b c = ω(X_b, X_c)`; the gauge-trivialized frame coefficients are `gauge1 ρt ω k = ρ(q)⁻¹ ω(X_k)`, `gauge2 ρt ω m = ρ(q)⁻¹ ω(X_{m+1}, X_{m+2})`.
* `extDeriv_frame_one`, `extDeriv_frame_two`: the exterior derivative on frame vectors (`dω(X_b, X_c) = X_b ω(X_c) - X_c ω(X_b) - ω([X_b, X_c])`, `[X₀, X₁] = X₂`;
  `dω(X₀, X₁, X₂) = Σ ± X_i ω(...)`, no structure term because the Heisenberg group is unimodular).
* `frame_curl`, `frame_div` (for a unipotent representation `ρt`, `HeisRep`): in the gauge, `ρ⁻¹ dω` is the Chevalley-Eilenberg differential `curlC`, `divC`
  (degree `1 → 2`, `2 → 3` parts of `D = Σ ε_k X_k + 𝔇`, where `𝔇` involves `ρ_k` and the structure constant).
* `Dop_i2`, `Dop_pack2`: the matching component formulas for `D` on the cochain space `CE E`, so that `d` and `D` correspond (`curlC`, `divC`).
-/

open scoped ContDiff
open TernaryPoly.SmoothCoveringDeRham
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

section Alt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem alt1_add (φ : Pt [⋀^Fin 1]→L[ℝ] E) (x y : Pt) :
    φ (fun _ => x + y) = φ (fun _ => x) + φ (fun _ => y) := by
  have h := φ.toContinuousMultilinearMap.map_update_add (fun _ => (0 : Pt)) 0 x y
  have e : ∀ z : Pt, Function.update (fun _ : Fin 1 => (0 : Pt)) 0 z = fun _ => z := by
    intro z; funext i; fin_cases i; simp
  simpa [e] using h

theorem alt1_smul (φ : Pt [⋀^Fin 1]→L[ℝ] E) (c : ℝ) (x : Pt) :
    φ (fun _ => c • x) = c • φ (fun _ => x) := by
  have h := φ.toContinuousMultilinearMap.map_update_smul (fun _ => (0 : Pt)) 0 c x
  have e : ∀ z : Pt, Function.update (fun _ : Fin 1 => (0 : Pt)) 0 z = fun _ => z := by
    intro z; funext i; fin_cases i; simp
  simpa [e] using h

theorem alt2_add_left (φ : Pt [⋀^Fin 2]→L[ℝ] E) (x y z : Pt) :
    φ ![x + y, z] = φ ![x, z] + φ ![y, z] := by
  have h := φ.toContinuousMultilinearMap.map_update_add ![0, z] 0 x y
  have e : ∀ t : Pt, Function.update ![0, z] 0 t = ![t, z] := by
    intro t; funext i; fin_cases i <;> simp
  simpa [e] using h

theorem alt2_smul_left (φ : Pt [⋀^Fin 2]→L[ℝ] E) (c : ℝ) (x z : Pt) :
    φ ![c • x, z] = c • φ ![x, z] := by
  have h := φ.toContinuousMultilinearMap.map_update_smul ![0, z] 0 c x
  have e : ∀ t : Pt, Function.update ![0, z] 0 t = ![t, z] := by
    intro t; funext i; fin_cases i <;> simp
  simpa [e] using h

theorem alt2_add_right (φ : Pt [⋀^Fin 2]→L[ℝ] E) (x y z : Pt) :
    φ ![x, y + z] = φ ![x, y] + φ ![x, z] := by
  have h := φ.toContinuousMultilinearMap.map_update_add ![x, 0] 1 y z
  have e : ∀ t : Pt, Function.update ![x, 0] 1 t = ![x, t] := by
    intro t; funext i; fin_cases i <;> simp
  simpa [e] using h

theorem alt2_smul_right (φ : Pt [⋀^Fin 2]→L[ℝ] E) (c : ℝ) (x z : Pt) :
    φ ![x, c • z] = c • φ ![x, z] := by
  have h := φ.toContinuousMultilinearMap.map_update_smul ![x, 0] 1 c z
  have e : ∀ t : Pt, Function.update ![x, 0] 1 t = ![x, t] := by
    intro t; funext i; fin_cases i <;> simp
  simpa [e] using h

theorem alt2_same (φ : Pt [⋀^Fin 2]→L[ℝ] E) (x : Pt) : φ ![x, x] = 0 :=
  φ.map_eq_zero_of_eq ![x, x] (by simp) (by decide : (0 : Fin 2) ≠ 1)

end Alt

section Smooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation of a smooth family of alternating maps on smooth vector fields is smooth. -/
theorem contDiff_ev {n : ℕ} {om : Pt → Pt [⋀^Fin n]→L[ℝ] E} (hom : ContDiff ℝ ∞ om)
    {v : Fin n → Pt → Pt} (hv : ∀ i, ContDiff ℝ ∞ (v i)) :
    ContDiff ℝ ∞ (fun q => om q (fun i => v i q)) := by
  let B : Pt → (Fin n → ℝ) →L[ℝ] Pt := fun q =>
    ∑ i, (ContinuousLinearMap.proj i).smulRight (v i q)
  have hB : ContDiff ℝ ∞ B := by
    refine ContDiff.sum fun i _ => ?_
    exact ((ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) Pt
      (ContinuousLinearMap.proj i)).contDiff).comp (hv i)
  have h := smooth_compContinuousLinearMap (D := Fin n → ℝ) n (s := Set.univ) hom.contDiffOn hB.contDiffOn
  have h2 := (ContinuousAlternatingMap.apply ℝ (Fin n → ℝ) E (fun i => Pi.single i 1)).contDiff.comp_contDiffOn h
  refine contDiffOn_univ.mp (h2.congr fun q _ => ?_)
  simp [B]
  congr 1
  funext j
  simp [Pi.single_apply]

end Smooth

section Frame1

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_Xf (k : Fin 3) : ContDiff ℝ ∞ (Xf k) := by
  fin_cases k
  · exact contDiff_const
  · exact contDiff_const.add (contDiff_fst.smul contDiff_const)
  · exact contDiff_const

/-- The frame component `ω(X_k)` of a `1`-form. -/
def A1 (om : Pt → Pt [⋀^Fin 1]→L[ℝ] E) (k : Fin 3) (q : Pt) : E := om q (fun _ => Xf k q)

/-- The frame component `ω(X_b, X_c)` of a `2`-form. -/
def A2 (om : Pt → Pt [⋀^Fin 2]→L[ℝ] E) (b c : Fin 3) (q : Pt) : E := om q ![Xf b q, Xf c q]

theorem A1_contDiff {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (k : Fin 3) :
    ContDiff ℝ ∞ (A1 om k) :=
  contDiff_ev hom (fun _ => contDiff_Xf k)

theorem A2_contDiff {om : Pt → Pt [⋀^Fin 2]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (b c : Fin 3) :
    ContDiff ℝ ∞ (A2 om b c) :=
  contDiff_ev hom (fun i => by fin_cases i <;> simp [contDiff_Xf])

theorem Xf_shift (b : Fin 3) (p q : Pt) :
    Xf b p = Xf b q + (if b = 1 then (p.1 - q.1) • e3 else 0) := by
  fin_cases b
  · simp [Xf]
  · simp only [Xf]
    ext <;> simp [e2, e3]
  · simp [Xf]

/-- Expansion of the value of a `1`-form on a frame vector based at another point. -/
theorem om1_shift (om : Pt → Pt [⋀^Fin 1]→L[ℝ] E) (b : Fin 3) (p q : Pt) :
    om q (fun _ => Xf b p) = A1 om b q + (if b = 1 then (p.1 - q.1) • A1 om 2 q else 0) := by
  rw [Xf_shift b p q, alt1_add]
  unfold A1
  split_ifs
  · rw [alt1_smul]; rfl
  · have h0 : om q (fun _ => (0 : Pt)) = 0 := by simpa using alt1_smul (om q) 0 0
    simp [h0]

end Frame1


section D1

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem extDeriv_one {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (p v w : Pt) :
    extDeriv om p ![v, w] = fderiv ℝ (fun q => om q (fun _ => w)) p v -
      fderiv ℝ (fun q => om q (fun _ => v)) p w := by
  have hd : DifferentiableAt ℝ om p := (hom.differentiable (by simp)) p
  rw [extDeriv_apply hd, Fin.sum_univ_two]
  have e0 : Fin.removeNth 0 ![v, w] = fun _ => w := by funext i; fin_cases i; rfl
  have e1 : Fin.removeNth 1 ![v, w] = fun _ => v := by funext i; fin_cases i; rfl
  rw [e0, e1]
  simp [sub_eq_add_neg]

theorem fderiv_om1_const {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (b : Fin 3) (p w : Pt) :
    fderiv ℝ (fun q => om q (fun _ => Xf b p)) p w =
      fderiv ℝ (A1 om b) p w - (if b = 1 then w.1 • A1 om 2 p else 0) := by
  have hfun : (fun q => om q (fun _ => Xf b p)) =
      fun q => A1 om b q + (if b = 1 then (p.1 - q.1) • A1 om 2 q else 0) := funext (om1_shift om b p)
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (A1 om b) p := ((A1_contDiff hom b).differentiable (by simp)) p
  have hd2 : DifferentiableAt ℝ (A1 om 2) p := ((A1_contDiff hom 2).differentiable (by simp)) p
  by_cases hb : b = 1
  · subst hb
    simp only [ite_true]
    have hc : DifferentiableAt ℝ (fun q : Pt => p.1 - q.1) p := by fun_prop
    have h := fderiv_add hd1 (hc.smul hd2)
    have hs := fderiv_smul hc hd2
    have hfst : fderiv ℝ (fun q : Pt => q.1) p = ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) :=
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).fderiv
    have hf1 : fderiv ℝ (fun q : Pt => p.1 - q.1) p = -ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) := by
      rw [fderiv_const_sub]
      exact congrArg Neg.neg hfst
    show fderiv ℝ (A1 om 1 + (fun q : Pt => p.1 - q.1) • A1 om 2) p w = _
    rw [h, hs, hf1]
    simp [sub_eq_add_neg]
  · simp [hb]


/-- **The exterior derivative of a `1`-form on a pair of frame vectors**
(`dω(X_b, X_c) = X_b ω(X_c) - X_c ω(X_b) - ω([X_b, X_c])`, with `[X₀, X₁] = X₂`). -/
theorem extDeriv_frame_one {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (b c : Fin 3) (p : Pt) :
    extDeriv om p ![Xf b p, Xf c p] =
      Xop b (A1 om c) p - Xop c (A1 om b) p - (if c = 1 then (Xf b p).1 • A1 om 2 p else 0) +
        (if b = 1 then (Xf c p).1 • A1 om 2 p else 0) := by
  rw [extDeriv_one hom, fderiv_om1_const hom c p, fderiv_om1_const hom b p, ← Xop_eq, ← Xop_eq]
  abel


end D1

section D2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The shift coefficient `s_b(q) = (p₁ - q₁)` for `b = 1` and `0` otherwise. -/
def sh (b : Fin 3) (p q : Pt) : ℝ := if b = 1 then p.1 - q.1 else 0

theorem sh_diff (b : Fin 3) (p : Pt) : DifferentiableAt ℝ (sh b p) p := by
  unfold sh
  split_ifs
  · fun_prop
  · exact differentiableAt_const _

theorem sh_self (b : Fin 3) (p : Pt) : sh b p p = 0 := by
  unfold sh; split_ifs <;> simp

theorem fderiv_sh (b : Fin 3) (p w : Pt) : fderiv ℝ (sh b p) p w = if b = 1 then -w.1 else 0 := by
  unfold sh
  split_ifs
  · have hfst : fderiv ℝ (fun q : Pt => q.1) p = ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) :=
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).fderiv
    rw [fderiv_const_sub, hfst]
    simp
  · simp

theorem Xf_shift' (b : Fin 3) (p q : Pt) : Xf b p = Xf b q + sh b p q • e3 := by
  rw [Xf_shift b p q]
  unfold sh
  split_ifs <;> simp

theorem fderiv_vanish {A B : Pt → E} (s : Pt → ℝ) {p : Pt} (hA : DifferentiableAt ℝ A p)
    (hB : DifferentiableAt ℝ B p) (hs : DifferentiableAt ℝ s p) (hsp : s p = 0) (w : Pt) :
    fderiv ℝ (fun q => A q + s q • B q) p w = fderiv ℝ A p w + (fderiv ℝ s p w) • B p := by
  have h := fderiv_add hA (hs.smul hB)
  have hm := fderiv_smul hs hB
  show fderiv ℝ (A + s • B) p w = _
  rw [h, hm, hsp]
  simp

/-- Expansion of the value of a `2`-form on frame vectors based at another point. -/
theorem om2_shift (om : Pt → Pt [⋀^Fin 2]→L[ℝ] E) (b c : Fin 3) (p q : Pt) :
    om q ![Xf b p, Xf c p] = A2 om b c q + sh c p q • A2 om b 2 q + sh b p q • A2 om 2 c q := by
  rw [Xf_shift' b p q, Xf_shift' c p q]
  have h1 : (Xf 2 q) = e3 := rfl
  rw [alt2_add_left, alt2_add_right, alt2_add_right, alt2_smul_left, alt2_smul_right, alt2_smul_left,
    alt2_smul_right, alt2_same, smul_zero, smul_zero, add_zero]
  unfold A2
  rw [h1]

theorem fderiv_om2_const {om : Pt → Pt [⋀^Fin 2]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (b c : Fin 3) (p w : Pt) :
    fderiv ℝ (fun q => om q ![Xf b p, Xf c p]) p w =
      fderiv ℝ (A2 om b c) p w + (fderiv ℝ (sh c p) p w) • A2 om b 2 p +
        (fderiv ℝ (sh b p) p w) • A2 om 2 c p := by
  have hd : ∀ b c : Fin 3, DifferentiableAt ℝ (A2 om b c) p := fun b c =>
    ((A2_contDiff hom b c).differentiable (by simp)) p
  have hfun : (fun q => om q ![Xf b p, Xf c p]) =
      fun q => (A2 om b c q + sh c p q • A2 om b 2 q) + sh b p q • A2 om 2 c q :=
    funext (om2_shift om b c p)
  have hA : DifferentiableAt ℝ (fun q => A2 om b c q + sh c p q • A2 om b 2 q) p :=
    (hd b c).add ((sh_diff c p).smul (hd b 2))
  rw [hfun, fderiv_vanish (sh b p) hA (hd 2 c) (sh_diff b p) (sh_self b p),
    fderiv_vanish (sh c p) (hd b c) (hd b 2) (sh_diff c p) (sh_self c p)]


theorem A2_same {om : Pt → Pt [⋀^Fin 2]→L[ℝ] E} (b : Fin 3) (q : Pt) : A2 om b b q = 0 :=
  alt2_same _ _

/-- **The exterior derivative of a `2`-form on the full frame**:
`dω(X₀, X₁, X₂) = X₀ ω(X₁, X₂) - X₁ ω(X₀, X₂) + X₂ ω(X₀, X₁)` (the Heisenberg group is unimodular). -/
theorem extDeriv_frame_two {om : Pt → Pt [⋀^Fin 2]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (p : Pt) :
    extDeriv om p ![Xf 0 p, Xf 1 p, Xf 2 p] =
      Xop 0 (A2 om 1 2) p - Xop 1 (A2 om 0 2) p + Xop 2 (A2 om 0 1) p := by
  have hd : DifferentiableAt ℝ om p := (hom.differentiable (by simp)) p
  rw [extDeriv_apply hd, Fin.sum_univ_three]
  have e0 : Fin.removeNth 0 ![Xf 0 p, Xf 1 p, Xf 2 p] = ![Xf 1 p, Xf 2 p] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.removeNth 1 ![Xf 0 p, Xf 1 p, Xf 2 p] = ![Xf 0 p, Xf 2 p] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.removeNth 2 ![Xf 0 p, Xf 1 p, Xf 2 p] = ![Xf 0 p, Xf 1 p] := by
    funext i; fin_cases i <;> rfl
  rw [e0, e1, e2]
  simp only [fderiv_om2_const hom, fderiv_sh, Xop_eq, A2_same]
  simp [Xf, e3, sub_eq_add_neg]
  abel


theorem alt2_swap (φ : Pt [⋀^Fin 2]→L[ℝ] E) (x y : Pt) : φ ![y, x] = -φ ![x, y] := by
  have h := alt2_same φ (x + y)
  rw [alt2_add_left, alt2_add_right, alt2_add_right, alt2_same, alt2_same] at h
  rw [eq_neg_iff_add_eq_zero]
  simpa [add_comm] using h

theorem A2_swap {om : Pt → Pt [⋀^Fin 2]→L[ℝ] E} (b c : Fin 3) (q : Pt) :
    A2 om c b q = -A2 om b c q := alt2_swap _ _ _


end D2

section Gauge

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ρt : Pt → E →L[ℝ] E}

theorem contDiff_invH : ContDiff ℝ ∞ invH := by
  unfold invH
  fun_prop

theorem HeisRep.cancel (R : HeisRep ρt) (q : Pt) (x : E) : ρt q (ρt (invH q) x) = x := by
  have h := R.mul q (invH q)
  rw [mulH_invH, R.one] at h
  have := congrArg (fun A : E →L[ℝ] E => A x) h
  simpa using this.symm

theorem HeisRep.cancel' (R : HeisRep ρt) (q : Pt) (x : E) : ρt (invH q) (ρt q x) = x := by
  have h := R.mul (invH q) q
  rw [invH_mulH, R.one] at h
  have := congrArg (fun A : E →L[ℝ] E => A x) h
  simpa using this.symm

/-- **The gauge-trivialized frame components of a `1`-form**: `ρ(q)⁻¹ ω(X_k)`. -/
def gauge1 (ρt : Pt → E →L[ℝ] E) (om : Pt → Pt [⋀^Fin 1]→L[ℝ] E) (k : Fin 3) (q : Pt) : E :=
  ρt (invH q) (A1 om k q)

/-- **The gauge-trivialized frame components of a `2`-form**: `ρ(q)⁻¹ ω(X_{m+1}, X_{m+2})`. -/
def gauge2 (ρt : Pt → E →L[ℝ] E) (om : Pt → Pt [⋀^Fin 2]→L[ℝ] E) (m : Fin 3) (q : Pt) : E :=
  ρt (invH q) (A2 om (m + 1) (m + 2) q)

theorem gauge1_contDiff (R : HeisRep ρt) {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (k : Fin 3) :
    ContDiff ℝ ∞ (gauge1 ρt om k) :=
  (R.smooth.comp contDiff_invH).clm_apply (A1_contDiff hom k)

theorem gauge2_contDiff (R : HeisRep ρt) {om : Pt → Pt [⋀^Fin 2]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (m : Fin 3) :
    ContDiff ℝ ∞ (gauge2 ρt om m) :=
  (R.smooth.comp contDiff_invH).clm_apply (A2_contDiff hom _ _)

theorem A1_eq (R : HeisRep ρt) (om : Pt → Pt [⋀^Fin 1]→L[ℝ] E) (k : Fin 3) :
    A1 om k = fun q => ρt q (gauge1 ρt om k q) := by
  funext q; exact (R.cancel q _).symm

/-- **The product rule for the gauge**: `X_k (ρ f) = ρ (ρ_k f + X_k f)`. -/
theorem Xop_gauge (R : HeisRep ρt) {f : Pt → E} (hf : ContDiff ℝ ∞ f) (k : Fin 3) (p : Pt) :
    Xop k (fun q => ρt q (f q)) p = ρt p (heisGen ρt k (f p) + Xop k f p) := by
  have hc : DifferentiableAt ℝ ρt p := (R.smooth.differentiable (by simp)) p
  have hf' : DifferentiableAt ℝ f p := (hf.differentiable (by simp)) p
  rw [Xop_eq, fderiv_clm_apply hc hf']
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    R.fderiv_eq, Xop_eq, map_add, mul_apply_eq_comp]
  rw [add_comm]

/-- **The `d` of a `1`-form in the gauge-trivialized frame** (Chevalley-Eilenberg curl):
`ρ⁻¹ dω(X_{m+1}, X_{m+2}) = (X_{m+1} + ρ_{m+1}) u_{m+2} - (X_{m+2} + ρ_{m+2}) u_{m+1} - c^m u₂`. -/
def curlC (ρ : Fin 3 → E →L[ℝ] E) (a : Fin 3 → Pt → E) (m : Fin 3) (p : Pt) : E :=
  Xop (m + 1) (a (m + 2)) p - Xop (m + 2) (a (m + 1)) p + ρ (m + 1) (a (m + 2) p) -
    ρ (m + 2) (a (m + 1) p) - (if m = 2 then a 2 p else 0)

theorem gauge_xop1 (R : HeisRep ρt) {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (b c : Fin 3)
    (p : Pt) :
    Xop b (A1 om c) p = ρt p (heisGen ρt b (gauge1 ρt om c p) + Xop b (gauge1 ρt om c) p) := by
  rw [A1_eq R om c]
  exact Xop_gauge R (gauge1_contDiff R hom c) b p

theorem frame_curl0 (R : HeisRep ρt) {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (p : Pt) :
    ρt (invH p) (extDeriv om p ![Xf 1 p, Xf 2 p]) =
      Xop 1 (gauge1 ρt om 2) p - Xop 2 (gauge1 ρt om 1) p + heisGen ρt 1 (gauge1 ρt om 2 p) -
        heisGen ρt 2 (gauge1 ρt om 1 p) := by
  rw [extDeriv_frame_one hom 1 2 p, gauge_xop1 R hom, gauge_xop1 R hom]
  simp [Xf, e3, map_sub, map_add, R.cancel']
  abel

theorem frame_curl1 (R : HeisRep ρt) {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (p : Pt) :
    ρt (invH p) (extDeriv om p ![Xf 2 p, Xf 0 p]) =
      Xop 2 (gauge1 ρt om 0) p - Xop 0 (gauge1 ρt om 2) p + heisGen ρt 2 (gauge1 ρt om 0 p) -
        heisGen ρt 0 (gauge1 ρt om 2 p) := by
  rw [extDeriv_frame_one hom 2 0 p, gauge_xop1 R hom, gauge_xop1 R hom]
  simp [map_sub, map_add, R.cancel']
  abel

theorem frame_curl2 (R : HeisRep ρt) {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (p : Pt) :
    ρt (invH p) (extDeriv om p ![Xf 0 p, Xf 1 p]) =
      Xop 0 (gauge1 ρt om 1) p - Xop 1 (gauge1 ρt om 0) p + heisGen ρt 0 (gauge1 ρt om 1 p) -
        heisGen ρt 1 (gauge1 ρt om 0 p) - gauge1 ρt om 2 p := by
  rw [extDeriv_frame_one hom 0 1 p, gauge_xop1 R hom, gauge_xop1 R hom]
  simp [Xf, e1, map_sub, map_add, R.cancel']
  simp only [gauge1]
  abel

/-- **`d` of a `1`-form in the gauge-trivialized frame is the Chevalley-Eilenberg differential** (the degree `1 → 2` part of `D`). -/
theorem frame_curl (R : HeisRep ρt) {om : Pt → Pt [⋀^Fin 1]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (m : Fin 3)
    (p : Pt) :
    ρt (invH p) (extDeriv om p ![Xf (m + 1) p, Xf (m + 2) p]) =
      curlC (heisGen ρt) (gauge1 ρt om) m p := by
  match m with
  | 0 => simpa [curlC] using frame_curl0 R hom p
  | 1 => simpa [curlC] using frame_curl1 R hom p
  | 2 => simpa [curlC] using frame_curl2 R hom p

theorem Xop_neg {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {u : Pt → W} (hu : ContDiff ℝ ∞ u) (k : Fin 3) (p : Pt) :
    Xop k (fun q => -u q) p = -Xop k u p := by
  have h := congrFun (Xop_lin (-ContinuousLinearMap.id ℝ W) hu k) p
  have e : lin (-ContinuousLinearMap.id ℝ W) u = fun q => -u q := by funext q; simp [lin]
  rw [e] at h
  simpa [lin] using h

theorem A2_eq (R : HeisRep ρt) (om : Pt → Pt [⋀^Fin 2]→L[ℝ] E) (m : Fin 3) :
    A2 om (m + 1) (m + 2) = fun q => ρt q (gauge2 ρt om m q) := by
  funext q; exact (R.cancel q _).symm

theorem gauge_xop2 (R : HeisRep ρt) {om : Pt → Pt [⋀^Fin 2]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (b m : Fin 3)
    (p : Pt) :
    Xop b (A2 om (m + 1) (m + 2)) p =
      ρt p (heisGen ρt b (gauge2 ρt om m p) + Xop b (gauge2 ρt om m) p) := by
  rw [A2_eq R om m]
  exact Xop_gauge R (gauge2_contDiff R hom m) b p

/-- **The divergence**: `d` of a `2`-form in the gauge-trivialized frame (the degree `2 → 3` part of `D`). -/
def divC (ρ : Fin 3 → E →L[ℝ] E) (a : Fin 3 → Pt → E) (p : Pt) : E :=
  ∑ m, (Xop m (a m) p + ρ m (a m p))

theorem frame_div (R : HeisRep ρt) {om : Pt → Pt [⋀^Fin 2]→L[ℝ] E} (hom : ContDiff ℝ ∞ om) (p : Pt) :
    ρt (invH p) (extDeriv om p ![Xf 0 p, Xf 1 p, Xf 2 p]) = divC (heisGen ρt) (gauge2 ρt om) p := by
  rw [extDeriv_frame_two hom p]
  have h0 : Xop 0 (A2 om 1 2) p =
      ρt p (heisGen ρt 0 (gauge2 ρt om 0 p) + Xop 0 (gauge2 ρt om 0) p) := gauge_xop2 R hom 0 0 p
  have h2 : Xop 2 (A2 om 0 1) p =
      ρt p (heisGen ρt 2 (gauge2 ρt om 2 p) + Xop 2 (gauge2 ρt om 2) p) := gauge_xop2 R hom 2 2 p
  have h1 : Xop 1 (A2 om 0 2) p =
      -(ρt p (heisGen ρt 1 (gauge2 ρt om 1 p) + Xop 1 (gauge2 ρt om 1) p)) := by
    have e : A2 om 0 2 = fun q => -(ρt q (gauge2 ρt om 1 q)) := by
      funext q
      rw [A2_swap (om := om) 2 0 q]
      exact congrArg Neg.neg (congrFun (A2_eq R om 1) q)
    rw [e, Xop_neg ((R.smooth).clm_apply (gauge2_contDiff R hom 1)) 1 p]
    exact congrArg Neg.neg (Xop_gauge R (gauge2_contDiff R hom 1) 1 p)
  rw [h0, h1, h2]
  simp [divC, Fin.sum_univ_three, map_sub, map_add, map_neg, R.cancel']
  abel

end Gauge

section CEside

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Xop_clm {W V : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : W →L[ℝ] V) {u : Pt → W} (hu : ContDiff ℝ ∞ u) (k : Fin 3) (p : Pt) :
    Xop k (fun q => L (u q)) p = L (Xop k u p) := by
  have hd : DifferentiableAt ℝ u p := (hu.differentiable (by simp)) p
  have h := L.hasFDerivAt.comp p hd.hasFDerivAt
  have h' : fderiv ℝ (fun q => L (u q)) p = L.comp (fderiv ℝ u p) := h.fderiv
  rw [Xop_eq, Xop_eq, h']
  rfl

theorem Xop_proj {u : Pt → CE E} (hu : ContDiff ℝ ∞ u) (k : Fin 3) (p : Pt) (j : Fin 8) :
    Xop k u p j = Xop k (fun q => u q j) p :=
  (Xop_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 8 => E) j) hu k p).symm

/-- The index of the `θ^k` component. -/
def i1 (k : Fin 3) : Fin 8 := ⟨1 + k.val, by omega⟩

/-- The index of the `θ^{k+1} ∧ θ^{k+2}` component. -/
def i2 (k : Fin 3) : Fin 8 := ⟨4 + k.val, by omega⟩

theorem Dop_i2 (ρ : Fin 3 → E →L[ℝ] E) (hρ : HeisMod ρ) {η : Pt → CE E} (hη : ContDiff ℝ ∞ η) (m : Fin 3)
    (p : Pt) :
    Dop (ceData ρ hρ) η p (i2 m) = curlC ρ (fun k q => η q (i1 k)) m p := by
  rw [Dop_apply]
  simp only [Pi.add_apply, Finset.sum_apply]
  fin_cases m <;>
  · simp [curlC, i1, i2, epsC, ceD0_eq, structC, matOp_apply, Fin.sum_univ_eight, Fin.sum_univ_three, epsM, iotM,
      hat_apply, Matrix.mul_apply]
    simp only [Xop_proj hη]
    abel

end CEside

section Pack

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A degree-`2` cochain from its three coefficients. -/
def pack2 (b : Fin 3 → E) : CE E := ![0, 0, 0, 0, b 0, b 1, b 2, 0]

/-- A degree-`1` cochain from its three coefficients. -/
def pack1 (a : Fin 3 → E) : CE E := ![0, a 0, a 1, a 2, 0, 0, 0, 0]

theorem Xop_zero_fun {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (k : Fin 3) (p : Pt) :
    Xop k (fun _ : Pt => (0 : W)) p = 0 := by
  rw [Xop_eq]; simp

theorem pack2_contDiff {b : Pt → Fin 3 → E} (hb : ∀ m, ContDiff ℝ ∞ (fun q => b q m)) :
    ContDiff ℝ ∞ (fun q => pack2 (b q)) := by
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i <;> simp [pack2, hb, contDiff_const]

theorem Dop_pack2 (ρ : Fin 3 → E →L[ℝ] E) (hρ : HeisMod ρ) {b : Pt → Fin 3 → E}
    (hb : ∀ m, ContDiff ℝ ∞ (fun q => b q m)) (p : Pt) (i : Fin 8) :
    Dop (ceData ρ hρ) (fun q => pack2 (b q)) p i = if i = 7 then divC ρ (fun m q => b q m) p else 0 := by
  have hu := pack2_contDiff hb
  rw [Dop_apply]
  simp only [Pi.add_apply, Finset.sum_apply]
  fin_cases i
  all_goals
    simp [divC, epsC, ceD0_eq, structC, matOp_apply, Fin.sum_univ_eight, Fin.sum_univ_three, epsM, iotM,
      hat_apply, Matrix.mul_apply]
  all_goals
    try simp only [Xop_proj hu]
    try simp [pack2, Xop_zero_fun]
  abel

end Pack

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
