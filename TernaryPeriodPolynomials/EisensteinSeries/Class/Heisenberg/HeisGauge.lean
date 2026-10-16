module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisD2

@[expose] public section


/-!
# The Heisenberg group, its left-invariant frame, and the gauge of a unipotent representation

Formalized by Claude Sonnet 5.5.

* `mulH`, `invH`: the Heisenberg group `[[1,x,z],[0,1,y],[0,0,1]]` on the Malcev chart `Pt = ℝ³`; left translation `q ↦ p q` has derivative `Mx p.1` (`hasFDerivAt_mulH`).
* `Xf`, `theta`: the left-invariant frame `X₀ = ∂ₓ`, `X₁ = ∂_y + x ∂_z`, `X₂ = ∂_z` and coframe `θ⁰ = dx`, `θ¹ = dy`, `θ² = dz - x dy`; `Xop_eq`: `Xop k u p = du_p (X_k(p))`;
  `Mx_Xf`, `theta_Mx`: left invariance of the frame and coframe.
* `HeisRep ρt`: a smooth multiplicative unipotent family `ρt : H → End E` (the polynomial coefficient representation restricted to the radical).  `heisGen ρt k = dρt_0 (X_k)`
  and `HeisRep.Xop_eq`: `X_k ρt = ρt ρ_k`.  `HeisRep.heisMod`: `(ρ_k)` is a unipotent Heisenberg module (`HeisMod`: `[ρ₀, ρ₁] = ρ₂` central, nilpotent;
  derived from the symmetry of mixed partials and the unipotence of `ρt`), so `HeisD2.heis_nomizu_ce` applies.
-/

open scoped ContDiff
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

/-! ### The Heisenberg group in Malcev coordinates -/

/-- **Multiplication of the Heisenberg group** `[[1,x,z],[0,1,y],[0,0,1]]` in the coordinates `(x, y, z)`. -/
def mulH (p q : Pt) : Pt := (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.1 * q.2.1)

/-- The inverse. -/
def invH (p : Pt) : Pt := (-p.1, -p.2.1, -p.2.2 + p.1 * p.2.1)

theorem mulH_assoc (p q r : Pt) : mulH (mulH p q) r = mulH p (mulH q r) := by
  simp only [mulH]; ext <;> simp <;> ring

theorem mulH_zero_left (p : Pt) : mulH 0 p = p := by simp [mulH]
theorem mulH_zero_right (p : Pt) : mulH p 0 = p := by simp [mulH]

theorem mulH_invH (p : Pt) : mulH p (invH p) = 0 := by
  simp only [mulH, invH]; ext <;> simp

theorem invH_mulH (p : Pt) : mulH (invH p) p = 0 := by
  simp only [mulH, invH]; ext <;> simp

theorem latX_eq_mulH (a : ℝ) (p : Pt) : latX a p = mulH (a, 0, 0) p := by
  simp only [latX_apply, mulH]
  ext <;> simp
  ring

/-- The left-invariant frame at `p`. -/
def Xf : Fin 3 → Pt → Pt
  | 0 => fun _ => e1
  | 1 => fun p => e2 + p.1 • e3
  | 2 => fun _ => e3

section Frame

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem Xop_eq (u : Pt → W) (k : Fin 3) (p : Pt) : Xop k u p = fderiv ℝ u p (Xf k p) := by
  fin_cases k
  · rfl
  · show ddir e2 u p + p.1 • ddir e3 u p = _
    simp [Xf, ddir]
  · rfl

end Frame

/-- The derivative of left translation `q ↦ p * q` is the linear map `Mx p.1`. -/
theorem mulH_eq (p q : Pt) : mulH p q = Mx p.1 q + p := by
  simp only [mulH, Mx]; ext <;> simp <;> ring

theorem hasFDerivAt_mulH (p q : Pt) : HasFDerivAt (mulH p) (Mx p.1) q := by
  have : mulH p = fun q => Mx p.1 q + p := funext (mulH_eq p)
  rw [this]
  exact (Mx p.1).hasFDerivAt.add_const p

theorem Mx_Xf (a : ℝ) (k : Fin 3) (q : Pt) : Mx a (Xf k q) = Xf k (mulH (a, 0, 0) q) := by
  fin_cases k
  · simp [Xf, Mx_e1]
  · simp only [Xf, map_add, map_smul, Mx_e2, Mx_e3, mulH]
    ext <;> simp [e2, e3]
  · simp [Xf, Mx_e3]

/-- The left-invariant coframe: `θ⁰ = dx`, `θ¹ = dy`, `θ² = dz - x dy`. -/
def theta : Fin 3 → Pt → Pt → ℝ
  | 0 => fun _ v => v.1
  | 1 => fun _ v => v.2.1
  | 2 => fun q v => v.2.2 - q.1 * v.2.1

theorem theta_Xf (j k : Fin 3) (q : Pt) : theta j q (Xf k q) = if j = k then 1 else 0 := by
  fin_cases j <;> fin_cases k <;> simp [theta, Xf, e1, e2, e3]

theorem frame_decomp (q v : Pt) : v = ∑ k, theta k q v • Xf k q := by
  simp only [Fin.sum_univ_three, theta, Xf]
  ext <;> simp [e1, e2, e3]
  ring

/-- The coframe is left invariant: `θ(dL_p v) = θ(v)`. -/
theorem theta_Mx (p : Pt) (k : Fin 3) (q v : Pt) : theta k (mulH p q) (Mx p.1 v) = theta k q v := by
  fin_cases k
  · simp [theta, Mx]
  · simp [theta, Mx]
  · simp [theta, Mx, mulH]; ring


section Rep

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A smooth unipotent representation of the Heisenberg group** (the polynomial coefficient representation, restricted to the radical):
`ρt : H → End E` smooth, multiplicative, with every `ρt p - 1` nilpotent of bounded order. -/
structure HeisRep (ρt : Pt → E →L[ℝ] E) : Prop where
  smooth : ContDiff ℝ ∞ ρt
  one : ρt 0 = 1
  mul : ∀ p q, ρt (mulH p q) = ρt p * ρt q
  unip : ∃ K : ℕ, ∀ p, (ρt p - 1) ^ K = 0

variable {ρt : Pt → E →L[ℝ] E}

/-- The action `ρ_k` of the frame vector `X_k` on `E`: the differential of `ρt` at the identity. -/
def heisGen (ρt : Pt → E →L[ℝ] E) (k : Fin 3) : E →L[ℝ] E := fderiv ℝ ρt 0 (Xf k 0)

theorem Xf_congr (k : Fin 3) (p : Pt) : Xf k p = Xf k (p.1, 0, 0) := by
  fin_cases k <;> rfl

/-- **The differential of `ρt` along the left-invariant fields**: `X_k ρt = ρt ρ_k`. -/
theorem HeisRep.fderiv_eq (R : HeisRep ρt) (k : Fin 3) (p : Pt) :
    fderiv ℝ ρt p (Xf k p) = ρt p * heisGen ρt k := by
  have hd : ∀ q, DifferentiableAt ℝ ρt q := fun q => (R.smooth.differentiable (by simp)) q
  have h1 : HasFDerivAt (fun q => ρt (mulH p q)) ((fderiv ℝ ρt p).comp (Mx p.1)) 0 := by
    have hg : HasFDerivAt ρt (fderiv ℝ ρt (mulH p 0)) (mulH p 0) := (hd _).hasFDerivAt
    have := hg.comp 0 (hasFDerivAt_mulH p 0)
    rw [mulH_zero_right] at this
    exact this
  have h2 : HasFDerivAt (fun q => ρt p * ρt q)
      ((ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (ρt p)).comp (fderiv ℝ ρt 0)) 0 :=
    (ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (ρt p)).hasFDerivAt.comp 0 (hd 0).hasFDerivAt
  have h3 : (fun q => ρt (mulH p q)) = fun q => ρt p * ρt q := funext (R.mul p)
  rw [h3] at h1
  have h4 := h1.unique h2
  have h5 := congrArg (fun A : Pt →L[ℝ] (E →L[ℝ] E) => A (Xf k 0)) h4
  simp only [ContinuousLinearMap.comp_apply] at h5
  have h6 : Mx p.1 (Xf k 0) = Xf k p := by
    rw [Xf_congr k p, Mx_Xf, mulH]
    simp
  rw [h6] at h5
  rw [h5]
  rfl

theorem HeisRep.Xop_eq (R : HeisRep ρt) (k : Fin 3) (p : Pt) : Xop k ρt p = ρt p * heisGen ρt k := by
  rw [Heisenberg.Xop_eq]; exact R.fderiv_eq k p

end Rep


section RepMod

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ρt : Pt → E →L[ℝ] E}

theorem HeisRep.Xop_Xop_eq (R : HeisRep ρt) (k l : Fin 3) (p : Pt) :
    Xop k (Xop l ρt) p = ρt p * heisGen ρt k * heisGen ρt l := by
  have h : Xop l ρt = lin ((ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).flip (heisGen ρt l)) ρt := by
    funext q
    rw [R.Xop_eq]
    rfl
  rw [h, Xop_lin _ R.smooth, ]
  show (Xop k ρt p) * heisGen ρt l = _
  rw [R.Xop_eq]

theorem HeisRep.hasDerivAt_line (R : HeisRep ρt) (k : Fin 3) :
    HasDerivAt (fun t : ℝ => ρt (t • Xf k 0)) (heisGen ρt k) 0 := by
  have hd : DifferentiableAt ℝ ρt ((0 : ℝ) • Xf k 0) := (R.smooth.differentiable (by simp)) _
  have hl : HasDerivAt (fun t : ℝ => t • Xf k 0) (Xf k 0) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Xf k 0)
  have := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  simp only [zero_smul] at this
  exact this

/-- The generators of a unipotent representation are nilpotent. -/
theorem HeisRep.gen_nilpotent (R : HeisRep ρt) (k : Fin 3) : IsNilpotent (heisGen ρt k) := by
  obtain ⟨K, hK⟩ := R.unip
  have hs := (hasDerivAt_iff_tendsto_slope.mp (R.hasDerivAt_line k)).pow K
  have hz : ∀ t : ℝ, slope (fun t : ℝ => ρt (t • Xf k 0)) 0 t ^ K = 0 := by
    intro t
    rw [slope_def_module, smul_pow, zero_smul, R.one]
    simp only [sub_zero]
    rw [hK, smul_zero]
  simp only [hz] at hs
  exact ⟨K, tendsto_nhds_unique hs tendsto_const_nhds⟩

/-- **The Lie algebra action of a smooth unipotent representation of the Heisenberg group is a unipotent module**
(`[ρ₀, ρ₁] = ρ₂` central, nilpotent): derived from the symmetry of mixed partial derivatives. -/
theorem HeisRep.heisMod (R : HeisRep ρt) : HeisMod (heisGen ρt) where
  br := by
    have h := Xop_comm01 R.smooth 0
    rw [R.Xop_Xop_eq, R.Xop_Xop_eq, R.Xop_eq, R.one] at h
    simpa using h
  c02 := by
    have h := congrFun (Xop_comm02 R.smooth) 0
    rw [R.Xop_Xop_eq, R.Xop_Xop_eq, R.one] at h
    simpa using h
  c12 := by
    have h := Xop_comm12 R.smooth 0
    rw [R.Xop_Xop_eq, R.Xop_Xop_eq, R.one] at h
    simpa using h
  nil := R.gen_nilpotent

end RepMod

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
