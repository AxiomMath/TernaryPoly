module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisLattice

@[expose] public section


/-!
# The Chevalley-Eilenberg cochain space of the Heisenberg algebra with unipotent coefficients

Formalized by Claude Sonnet 5.5.

The cochain space `Λ•(ℝ³)* ⊗ E` of the Heisenberg algebra `𝔥 = ⟨X₀, X₁, X₂ | [X₀, X₁] = X₂⟩` with coefficients in a module `E` is the space `CE E = Fin 8 → E`
(components: degree `0`; `θ^k`; `θ^{k+1} ∧ θ^{k+2}`; `θ⁰ ∧ θ¹ ∧ θ²`).  The wedge operators `ε_k` and contractions `ι_k = ε_kᵀ` are integer matrices (`epsM`, `iotM`), so
that all identities between them are decided by the kernel (`epsM_anti`, `cartanM`, `epsMm`, ...).  For operators `ρ_k` on `E` forming a unipotent module (`HeisMod`: `[ρ₀, ρ₁] = ρ₂`
central, all nilpotent) the constant part of the differential is `𝔇 = Σ ε_k ρ_k - ε₀ ε₁ ι₂` (`ceD0`; the last term is `dθ² = -θ⁰ ∧ θ¹`), and

* `ceLam`: the Lie derivative `Λ_j = ι_j 𝔇 + 𝔇 ι_j = ρ_j - N_j` with `N_j² = 0` commuting with `ρ_j`, hence nilpotent (`ceLam_nilpotent`);
* `ceData ρ h : CartanData (CE E)`: the data consumed by `heis_nomizu`;
* `eps_D0`, `D0_sq`: `ε_l 𝔇 + 𝔇 ε_l = -δ_{l2} ε₀ ε₁` and `𝔇² = 0`, the constant-coefficient halves of `D² = 0` (`HeisD2` assembles `D² = 0`).
-/

open scoped ContDiff
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

/-- The matrix of `ε_k` (wedge with `θ^k`) on the eight components. -/
def epsM (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i j =>
  if i.val = 1 + k.val ∧ j.val = 0 then 1
  else if i.val = 4 + (k.val + 2) % 3 ∧ j.val = 1 + (k.val + 1) % 3 then 1
  else if i.val = 4 + (k.val + 1) % 3 ∧ j.val = 1 + (k.val + 2) % 3 then -1
  else if i.val = 7 ∧ j.val = 4 + k.val then 1 else 0

/-- The matrix of `ι_k`: the transpose of `ε_k`. -/
def iotM (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ := (epsM k).transpose

theorem epsM_anti (k l : Fin 3) : epsM k * epsM l + epsM l * epsM k = 0 := by
  fin_cases k <;> fin_cases l <;> decide +kernel

theorem iotM_anti (k l : Fin 3) : iotM k * iotM l + iotM l * iotM k = 0 := by
  fin_cases k <;> fin_cases l <;> decide +kernel

theorem cartanM (k j : Fin 3) : epsM k * iotM j + iotM j * epsM k = if j = k then 1 else 0 := by
  fin_cases k <;> fin_cases j <;> decide +kernel

/-- The structure part `N_j` of the Lie derivative `Λ_j`. -/
def nilM (j : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  (if j = 0 then epsM 1 * iotM 2 else 0) - (if j = 1 then epsM 0 * iotM 2 else 0)

theorem lamM (j : Fin 3) :
    iotM j * (epsM 0 * (epsM 1 * iotM 2)) + (epsM 0 * (epsM 1 * iotM 2)) * iotM j = nilM j := by
  fin_cases j <;> decide +kernel

theorem nilM_sq (j : Fin 3) : nilM j * nilM j = 0 := by
  fin_cases j <;> decide +kernel


theorem epsMm (l : Fin 3) :
    epsM l * (epsM 0 * (epsM 1 * iotM 2)) + (epsM 0 * (epsM 1 * iotM 2)) * epsM l =
      if l = 2 then epsM 0 * epsM 1 else 0 := by
  fin_cases l <;> decide +kernel

theorem MmM_sq : (epsM 0 * (epsM 1 * iotM 2)) * (epsM 0 * (epsM 1 * iotM 2)) = 0 := by
  decide +kernel

theorem epsM_sq (k : Fin 3) : epsM k * epsM k = 0 := by
  fin_cases k <;> decide +kernel


theorem sub_mul_sub_self {R : Type*} [Ring R] (S M : R) :
    (S - M) * (S - M) = S * S - (S * M + M * S) + M * M := by noncomm_ring

/-- The square of `Σ ε_k r_k` in a ring (the algebraic heart of `D² = 0`). -/
theorem sq_sum {R : Type*} [Ring R] (e r : Fin 3 → R) (hanti : ∀ k l, e k * e l + e l * e k = 0)
    (hsq : ∀ k, e k * e k = 0) (hcomm : ∀ k l, r k * e l = e l * r k)
    (h01 : r 0 * r 1 - r 1 * r 0 = r 2) (h02 : r 0 * r 2 = r 2 * r 0) (h12 : r 1 * r 2 = r 2 * r 1) :
    (∑ k, e k * r k) * (∑ k, e k * r k) = e 0 * e 1 * r 2 := by
  have h10 : e 1 * e 0 = -(e 0 * e 1) := eq_neg_of_add_eq_zero_left (hanti 1 0)
  have h20 : e 2 * e 0 = -(e 0 * e 2) := eq_neg_of_add_eq_zero_left (hanti 2 0)
  have h21 : e 2 * e 1 = -(e 1 * e 2) := eq_neg_of_add_eq_zero_left (hanti 2 1)
  have key : ∀ k l, e k * r k * (e l * r l) = e k * e l * (r k * r l) := by
    intro k l
    rw [mul_assoc, ← mul_assoc (r k), hcomm k l, mul_assoc (e l), ← mul_assoc]
  simp only [Fin.sum_univ_three, add_mul, mul_add, key, hsq, h10, h20, h21, zero_mul, neg_mul]
  rw [h02, h12]
  conv_rhs => rw [← h01]
  noncomm_ring


section CE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Chevalley-Eilenberg cochain space** `Λ•(ℝ³)* ⊗ E`: component `0` is the degree `0` part, `1 + k` the coefficient of `θ^k`,
`4 + k` that of `θ^{k+1} ∧ θ^{k+2}`, and `7` that of `θ⁰ ∧ θ¹ ∧ θ²`. -/
abbrev CE (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Type := Fin 8 → E

/-- The operator of an integer matrix on the eight components. -/
def matOp (M : Matrix (Fin 8) (Fin 8) ℤ) : CE E →L[ℝ] CE E :=
  ContinuousLinearMap.pi fun i => ∑ j, ((M i j : ℤ) : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 8 => E) j

theorem matOp_apply (M : Matrix (Fin 8) (Fin 8) ℤ) (w : CE E) (i : Fin 8) :
    matOp M w i = ∑ j, ((M i j : ℤ) : ℝ) • w j := by
  simp [matOp]

theorem matOp_add (M N : Matrix (Fin 8) (Fin 8) ℤ) : matOp (E := E) (M + N) = matOp M + matOp N := by
  ext w i
  simp only [matOp_apply, Matrix.add_apply, add_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [add_smul]

theorem matOp_mul (M N : Matrix (Fin 8) (Fin 8) ℤ) : matOp (E := E) (M * N) = (matOp M).comp (matOp N) := by
  ext w i
  simp only [matOp_apply, Matrix.mul_apply, ContinuousLinearMap.comp_apply, Int.cast_sum, Int.cast_mul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem matOp_one : matOp (E := E) (1 : Matrix (Fin 8) (Fin 8) ℤ) = 1 := by
  ext w i
  simp [matOp_apply, Matrix.one_apply]

theorem matOp_zero : matOp (E := E) (0 : Matrix (Fin 8) (Fin 8) ℤ) = 0 := by
  ext w i
  simp [matOp_apply]

theorem matOp_sub (M N : Matrix (Fin 8) (Fin 8) ℤ) : matOp (E := E) (M - N) = matOp M - matOp N := by
  have h := matOp_add (E := E) (M - N) N
  rw [sub_add_cancel] at h
  rw [eq_sub_iff_add_eq, ← h]
  
/-- The Lie algebra operator `ρ̂`: apply an endomorphism of `E` componentwise. -/
def hat (L : E →L[ℝ] E) : CE E →L[ℝ] CE E :=
  ContinuousLinearMap.pi fun i => L.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 8 => E) i)

theorem hat_apply (L : E →L[ℝ] E) (w : CE E) (i : Fin 8) : hat L w i = L (w i) := rfl

theorem hat_comp_matOp (L : E →L[ℝ] E) (M : Matrix (Fin 8) (Fin 8) ℤ) :
    (hat L).comp (matOp (E := E) M) = (matOp M).comp (hat L) := by
  ext w i
  simp [hat_apply, matOp_apply, map_sum, map_smul]

theorem hat_mul (L L' : E →L[ℝ] E) : hat (L * L') = (hat L).comp (hat L') := rfl

theorem hat_mul' (L L' : E →L[ℝ] E) : hat (L * L') = hat L * hat L' := rfl

theorem hat_sub (L L' : E →L[ℝ] E) : hat (L - L') = hat L - hat L' := rfl

theorem hat_pow (L : E →L[ℝ] E) (n : ℕ) : hat (L ^ n) = (hat L) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, hat_mul, ih]; rfl

theorem hat_zero : hat (0 : E →L[ℝ] E) = 0 := rfl

end CE


section Data

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `ε_k`: wedge with `θ^k`. -/
def epsC (k : Fin 3) : CE E →L[ℝ] CE E := matOp (epsM k)

/-- `ι_k`: contraction with the dual frame vector. -/
def iotC (k : Fin 3) : CE E →L[ℝ] CE E := matOp (iotM k)

/-- **The constant part of the Chevalley-Eilenberg differential with coefficients** (`ρ_k` = the action of the frame
vector `X_k` on `E`): `𝔇 = Σ_k ε_k ρ_k - ε₀ ε₁ ι₂`, the last term being `dθ² = -θ⁰ ∧ θ¹` (`[X₀, X₁] = X₂`). -/
def ceD0 (ρ : Fin 3 → E →L[ℝ] E) : CE E →L[ℝ] CE E :=
  ∑ k, (epsC k).comp (hat (ρ k)) - (epsC 0).comp ((epsC 1).comp (iotC 2))

theorem cartanC (k j : Fin 3) :
    (epsC (E := E) k).comp (iotC j) + (iotC j).comp (epsC k) = if j = k then 1 else 0 := by
  unfold epsC iotC
  rw [← matOp_mul, ← matOp_mul, ← matOp_add, cartanM]
  split_ifs
  · exact matOp_one
  · exact matOp_zero

theorem cartanC_apply (k j : Fin 3) (x : CE E) :
    epsC k (iotC j x) + iotC j (epsC k x) = if j = k then x else 0 := by
  have h := congrArg (fun A : CE E →L[ℝ] CE E => A x) (cartanC (E := E) k j)
  simp only [add_apply, ContinuousLinearMap.comp_apply] at h
  rw [h]
  split_ifs <;> simp

theorem ceLam_S (ρ : Fin 3 → E →L[ℝ] E) (j : Fin 3) :
    (iotC j).comp (∑ k, (epsC k).comp (hat (ρ k))) + (∑ k, (epsC k).comp (hat (ρ k))).comp (iotC j) =
      hat (ρ j) := by
  ext w : 1
  have hc : ∀ k (x : CE E), hat (ρ k) (iotC j x) = iotC j (hat (ρ k) x) := fun k x =>
    congrArg (fun A : CE E →L[ℝ] CE E => A x) (hat_comp_matOp (ρ k) (iotM j))
  simp only [add_apply, ContinuousLinearMap.comp_apply, sum_apply, map_sum, hc]
  rw [← Finset.sum_add_distrib]
  have : ∀ k, iotC j (epsC k (hat (ρ k) w)) + epsC k (iotC j (hat (ρ k) w)) =
      if j = k then hat (ρ k) w else 0 := fun k => by
    rw [add_comm]; exact cartanC_apply k j _
  simp only [this]
  simp

theorem ceLam_M (j : Fin 3) :
    (iotC (E := E) j).comp ((epsC 0).comp ((epsC 1).comp (iotC 2))) +
      ((epsC 0).comp ((epsC 1).comp (iotC 2))).comp (iotC j) = matOp (nilM j) := by
  simp only [epsC, iotC, ← matOp_mul, ← matOp_add, lamM]

theorem ceLam (ρ : Fin 3 → E →L[ℝ] E) (j : Fin 3) :
    (iotC j).comp (ceD0 ρ) + (ceD0 ρ).comp (iotC j) = hat (ρ j) - matOp (nilM j) := by
  unfold ceD0
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, ← ceLam_S ρ j, ← ceLam_M j]
  abel

/-- The module hypotheses on the action `ρ_k` of the frame vectors on the coefficient space: `[ρ₀, ρ₁] = ρ₂` central,
all nilpotent (a unipotent module for the Heisenberg algebra). -/
structure HeisMod (ρ : Fin 3 → E →L[ℝ] E) : Prop where
  br : ρ 0 * ρ 1 - ρ 1 * ρ 0 = ρ 2
  c02 : ρ 0 * ρ 2 = ρ 2 * ρ 0
  c12 : ρ 1 * ρ 2 = ρ 2 * ρ 1
  nil : ∀ j, IsNilpotent (ρ j)

theorem hat_commute_eps (L : E →L[ℝ] E) (k : Fin 3) :
    hat L * epsC k = epsC k * hat L := hat_comp_matOp L (epsM k)

theorem hat_commute_iot (L : E →L[ℝ] E) (k : Fin 3) :
    hat L * iotC k = iotC k * hat L := hat_comp_matOp L (iotM k)

theorem epsC_anti (k l : Fin 3) : epsC (E := E) k * epsC l + epsC l * epsC k = 0 := by
  unfold epsC
  change (matOp (epsM k)).comp (matOp (epsM l)) + (matOp (epsM l)).comp (matOp (epsM k)) = 0
  rw [← matOp_mul, ← matOp_mul, ← matOp_add, epsM_anti, matOp_zero]

theorem epsC_sq (k : Fin 3) : epsC (E := E) k * epsC k = 0 := by
  unfold epsC
  change (matOp (epsM k)).comp (matOp (epsM k)) = 0
  rw [← matOp_mul, epsM_sq, matOp_zero]

/-- The wedge `ε₀ ε₁`. -/
def epsC01 : CE E →L[ℝ] CE E := matOp (epsM 0 * epsM 1)

/-- The structure term `ε₀ ε₁ ι₂`. -/
def structC : CE E →L[ℝ] CE E := matOp (epsM 0 * (epsM 1 * iotM 2))

theorem structC_eq : structC (E := E) = epsC 0 * (epsC 1 * iotC 2) := by
  unfold structC epsC iotC
  change _ = (matOp (epsM 0)).comp ((matOp (epsM 1)).comp (matOp (iotM 2)))
  rw [← matOp_mul, ← matOp_mul]

theorem epsC01_eq : epsC01 (E := E) = epsC 0 * epsC 1 := by
  unfold epsC01 epsC
  change _ = (matOp (epsM 0)).comp (matOp (epsM 1))
  rw [← matOp_mul]

theorem ceD0_eq (ρ : Fin 3 → E →L[ℝ] E) :
    ceD0 ρ = ∑ k, epsC k * hat (ρ k) - structC := by
  rw [structC_eq]; rfl

theorem eps_struct (l : Fin 3) :
    epsC (E := E) l * structC + structC * epsC l = if l = 2 then epsC01 else 0 := by
  unfold structC epsC epsC01
  change (matOp (epsM l)).comp (matOp (epsM 0 * (epsM 1 * iotM 2))) +
    (matOp (epsM 0 * (epsM 1 * iotM 2))).comp (matOp (epsM l)) = _
  rw [← matOp_mul, ← matOp_mul, ← matOp_add, epsMm]
  split_ifs <;> simp [matOp_zero]

theorem struct_sq : structC (E := E) * structC = 0 := by
  unfold structC
  change (matOp (epsM 0 * (epsM 1 * iotM 2))).comp (matOp (epsM 0 * (epsM 1 * iotM 2))) = 0
  rw [← matOp_mul, MmM_sq, matOp_zero]

theorem hat_commute_struct (L : E →L[ℝ] E) : hat L * structC = structC * hat L := hat_comp_matOp L _

theorem eps_S (ρ : Fin 3 → E →L[ℝ] E) (l : Fin 3) :
    epsC l * (∑ k, epsC k * hat (ρ k)) + (∑ k, epsC k * hat (ρ k)) * epsC l = 0 := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h1 : hat (ρ k) * epsC l = epsC l * hat (ρ k) := hat_commute_eps _ _
  calc epsC l * (epsC k * hat (ρ k)) + epsC k * hat (ρ k) * epsC l
      = (epsC l * epsC k + epsC k * epsC l) * hat (ρ k) := by
        rw [mul_assoc (epsC k), h1, ← mul_assoc, ← mul_assoc, add_mul]
    _ = 0 := by rw [epsC_anti l k, zero_mul]

theorem eps_D0 (ρ : Fin 3 → E →L[ℝ] E) (l : Fin 3) :
    epsC l * ceD0 ρ + ceD0 ρ * epsC l = -(if l = 2 then epsC01 else 0) := by
  rw [ceD0_eq, mul_sub, sub_mul]
  have h := eps_S ρ l
  have h2 := eps_struct (E := E) l
  rw [← h2]
  rw [← sub_eq_zero] at h ⊢
  rw [← h]
  abel_nf

theorem S_sq {ρ : Fin 3 → E →L[ℝ] E} (h : HeisMod ρ) :
    (∑ k, epsC (E := E) k * hat (ρ k)) * (∑ k, epsC k * hat (ρ k)) = epsC01 * hat (ρ 2) := by
  have := sq_sum (fun k => epsC (E := E) k) (fun k => hat (ρ k)) (fun k l => epsC_anti k l)
    (fun k => epsC_sq k) (fun k l => hat_commute_eps _ _)
    (by rw [← hat_mul', ← hat_mul', ← hat_sub, h.br]) (by rw [← hat_mul', ← hat_mul', h.c02])
    (by rw [← hat_mul', ← hat_mul', h.c12])
  rw [epsC01_eq]
  exact this

theorem S_struct (ρ : Fin 3 → E →L[ℝ] E) :
    (∑ k, epsC (E := E) k * hat (ρ k)) * structC + structC * (∑ k, epsC k * hat (ρ k)) =
      epsC01 * hat (ρ 2) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have key : ∀ k, epsC (E := E) k * hat (ρ k) * structC + structC * (epsC k * hat (ρ k)) =
      (if k = 2 then epsC01 else 0) * hat (ρ k) := fun k => by
    have h1 : hat (ρ k) * structC = structC * hat (ρ k) := hat_commute_struct _
    calc epsC k * hat (ρ k) * structC + structC * (epsC k * hat (ρ k))
        = (epsC k * structC + structC * epsC k) * hat (ρ k) := by
          rw [mul_assoc, h1, ← mul_assoc, ← mul_assoc, add_mul]
      _ = _ := by rw [eps_struct]
  simp only [key, Fin.sum_univ_three]
  simp

theorem D0_sq {ρ : Fin 3 → E →L[ℝ] E} (h : HeisMod ρ) : ceD0 (E := E) ρ * ceD0 ρ = 0 := by
  rw [ceD0_eq]
  have e := sub_mul_sub_self (∑ k, epsC (E := E) k * hat (ρ k)) structC
  rw [e, S_sq h, S_struct, struct_sq]
  simp

theorem nil_pow_two (j : Fin 3) : (matOp (E := E) (nilM j)) ^ 2 = 0 := by
  rw [pow_two]
  change (matOp (E := E) (nilM j)).comp (matOp (nilM j)) = 0
  rw [← matOp_mul, nilM_sq, matOp_zero]

theorem ceLam_nilpotent {ρ : Fin 3 → E →L[ℝ] E} (hρ : ∀ j, IsNilpotent (ρ j)) (j : Fin 3) :
    IsNilpotent ((iotC j).comp (ceD0 ρ) + (ceD0 ρ).comp (iotC j)) := by
  rw [ceLam]
  obtain ⟨n, hn⟩ := hρ j
  have h1 : IsNilpotent (hat (ρ j)) := ⟨n, by rw [← hat_pow, hn]; rfl⟩
  have h2 : IsNilpotent (matOp (E := E) (nilM j)) := ⟨2, nil_pow_two j⟩
  have hcomm : Commute (hat (ρ j)) (matOp (E := E) (nilM j)) := hat_comp_matOp _ _
  exact hcomm.isNilpotent_sub h1 h2

/-- **The Chevalley-Eilenberg Cartan data of the Heisenberg algebra with coefficients in `E`**, for nilpotent
operators `ρ_k` (the action of the frame vectors on the unipotent module `E`). -/
def ceData (ρ : Fin 3 → E →L[ℝ] E) (h : HeisMod ρ) : CartanData (CE E) where
  eps := epsC
  iot := iotC
  D0 := ceD0 ρ
  cartan := fun j k => cartanC k j
  nilpotent := by
    choose K hK using fun j => ceLam_nilpotent h.nil j
    refine ⟨K 0 + K 1 + K 2, fun j => ?_⟩
    refine pow_eq_zero_of_le ?_ (hK j)
    fin_cases j <;> simp <;> omega

end Data

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
