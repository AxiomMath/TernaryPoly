module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PeterssonCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHecke

@[expose] public section


/-!
# The Petersson inner product and self-adjointness of `T_p` at level one

`pet k f g = ∫_𝒟 conj(f) g y^k dμ` over the standard fundamental domain. With
`α₀ = [[1,0],[0,p]]`, the Hecke matrices are `α₀ βᵢ` up to `SL₂(ℤ)` on the left, so
`pet (T_p f) g = ∫_{𝒟₀} petersson(f|α₀, g)` and `pet f (T_p g) = ∫_{𝒟₀} petersson(f, g|α₀)`, where
`𝒟₀ = ⋃ βᵢ 𝒟` is a fundamental domain of `Γ⁰(p)`. The Fricke-type element `W = S α₀` normalizes
`Γ⁰(p)` and carries one integrand to the other, so the two integrals agree
(`pet_hecke`: `T_p` is self-adjoint for the Petersson product).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory
open scoped MatrixGroups Pointwise ModularForm Manifold

namespace TernaryPeriodPolynomials.Spectral.PeterssonHecke

open PeterssonDomain PeterssonCosets LevelOneHecke
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (k : ℤ) (p : Nat.Primes)

/-! ### Elementary slash and Petersson identities -/

theorem sigma_of_det_pos (g : GL (Fin 2) ℝ) (h : 0 < ((GeneralLinearGroup.det g : ℝˣ) : ℝ))
    (z : ℂ) : σ g z = z := by
  simp only [σ]
  rw [ite_eq_left h]
  rfl

theorem norm_sigma (g : GL (Fin 2) ℝ) (z : ℂ) : ‖σ g z‖ = ‖z‖ := by
  unfold σ
  split_ifs <;> simp

theorem det_mapGL (γ : SL(2, ℤ)) :
    ((GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ γ) : ℝˣ) : ℝ) = 1 := by
  simp

theorem petersson_mapGL (F G : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    petersson k (F ∣[k] SpecialLinearGroup.mapGL ℝ γ) (G ∣[k] SpecialLinearGroup.mapGL ℝ γ) τ =
      petersson k F G (γ • τ) := by
  rw [petersson_slash, det_mapGL, sigma_of_det_pos _ (by rw [det_mapGL]; norm_num)]
  simp
  rfl

theorem petersson_add_left (F₁ F₂ G : ℍ → ℂ) (τ : ℍ) :
    petersson k (F₁ + F₂) G τ = petersson k F₁ G τ + petersson k F₂ G τ := by
  simp only [petersson, Pi.add_apply, map_add]
  ring

theorem petersson_add_right (F G₁ G₂ : ℍ → ℂ) (τ : ℍ) :
    petersson k F (G₁ + G₂) τ = petersson k F G₁ τ + petersson k F G₂ τ := by
  simp only [petersson, Pi.add_apply]
  ring

theorem petersson_sum_left {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (G : ℍ → ℂ) (τ : ℍ) :
    petersson k (∑ i ∈ s, F i) G τ = ∑ i ∈ s, petersson k (F i) G τ := by
  simp only [petersson, Finset.sum_apply, map_sum, Finset.sum_mul]

theorem petersson_sum_right {ι : Type*} (s : Finset ι) (F : ℍ → ℂ) (G : ι → ℍ → ℂ) (τ : ℍ) :
    petersson k F (∑ i ∈ s, G i) τ = ∑ i ∈ s, petersson k F (G i) τ := by
  simp only [petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]

theorem petersson_smul_right (F G : ℍ → ℂ) (c : ℂ) (τ : ℍ) :
    petersson k F (c • G) τ = c * petersson k F G τ := by
  simp only [petersson, Pi.smul_apply, smul_eq_mul]
  ring

/-- Slashing by a positive scalar matrix multiplies by `u^(k-2)`. -/
theorem slash_scalar (F : ℍ → ℂ) (u : ℝˣ) :
    F ∣[k] GeneralLinearGroup.scalar (Fin 2) u = ((u : ℝ) : ℂ) ^ (k - 2) • F := by
  funext τ
  rw [ModularForm.slash_def]
  have hdet : ((GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) u) : ℝˣ) : ℝ) =
      (u : ℝ) ^ 2 := by
    simp [GeneralLinearGroup.scalar]
  have hpos : 0 < ((GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) u) : ℝˣ) : ℝ) := by
    rw [hdet]
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 u.ne_zero))
  beta_reduce
  rw [sigma_of_det_pos _ hpos, glScalar_smul, hdet]
  have hdenom : denom (GeneralLinearGroup.scalar (Fin 2) u) τ = ((u : ℝ) : ℂ) := by
    simp [denom, GeneralLinearGroup.scalar]
  rw [hdenom, abs_of_nonneg (sq_nonneg _)]
  have hu : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast u.ne_zero
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_assoc, ← zpow_add₀ hu, mul_comm]
  congr 2
  push_cast
  ring

/-! ### Matrices -/

/-- `α₀ = [[1,0],[0,p]]`. -/
abbrev alpha0 : GL (Fin 2) ℝ := heckeMatrix p (some ⟨0, p.property.pos⟩)

theorem heckeMatrix_some_val (j : Fin p.val) :
    (heckeMatrix p (some j) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, (j.val : ℝ); 0, (p.val : ℝ)] :=
  binaryHeckeTranslate_real p.val p.property.pos j

theorem heckeMatrix_none_val :
    (heckeMatrix p none : Matrix (Fin 2) (Fin 2) ℝ) = !![(p.val : ℝ), 0; 0, 1] :=
  binaryHeckeDilate_real p.val p.property.pos

theorem alpha0_val : (alpha0 p : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (p.val : ℝ)] := by
  rw [heckeMatrix_some_val]
  simp

theorem mapGL_val (γ : SL(2, ℤ)) :
    ((SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(γ 0 0 : ℝ), γ 0 1; γ 1 0, γ 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.mapGL]

theorem heckeMatrix_some_eq (j : Fin p.val) :
    heckeMatrix p (some j) = alpha0 p * SpecialLinearGroup.mapGL ℝ (beta p (some j)) := by
  apply Units.ext
  rw [Units.val_mul, heckeMatrix_some_val, alpha0_val, mapGL_val]
  simp only [beta, ModularGroup.coe_T_zpow]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem heckeMatrix_none_eq :
    SpecialLinearGroup.mapGL ℝ (beta p none) * heckeMatrix p none =
      alpha0 p * SpecialLinearGroup.mapGL ℝ (beta p none) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, heckeMatrix_none_val, alpha0_val, mapGL_val]
  simp only [beta, ModularGroup.coe_S]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Slash decompositions -/

theorem slash_levelOne (f : CuspForm levelOne k) (γ : SL(2, ℤ)) :
    (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ γ = f :=
  SlashInvariantForm.slash_action_eqn f _ ⟨γ, rfl⟩

theorem slash_heckeMatrix (f : CuspForm levelOne k) (i : Option (Fin p.val)) :
    (f : ℍ → ℂ) ∣[k] heckeMatrix p i =
      ((f : ℍ → ℂ) ∣[k] alpha0 p) ∣[k] SpecialLinearGroup.mapGL ℝ (beta p i) := by
  cases i with
  | none =>
    have h : heckeMatrix p none = (SpecialLinearGroup.mapGL ℝ (beta p none))⁻¹ *
        (alpha0 p * SpecialLinearGroup.mapGL ℝ (beta p none)) := by
      rw [← heckeMatrix_none_eq, inv_mul_cancel_left]
    rw [h, SlashAction.slash_mul, SlashAction.slash_mul, ← map_inv, slash_levelOne]
  | some j => rw [heckeMatrix_some_eq, SlashAction.slash_mul]

theorem petersson_hecke_left (f g : CuspForm levelOne k) (τ : ℍ) :
    petersson k (heckeFun k p f) g τ =
      ∑ i, petersson k ((f : ℍ → ℂ) ∣[k] alpha0 p) g (beta p i • τ) := by
  rw [heckeFun, petersson_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  have h := petersson_mapGL k ((f : ℍ → ℂ) ∣[k] alpha0 p) g (beta p i) τ
  rw [slash_levelOne] at h
  rw [slash_heckeMatrix, h]

theorem petersson_hecke_right (f g : CuspForm levelOne k) (τ : ℍ) :
    petersson k f (heckeFun k p g) τ =
      ∑ i, petersson k f ((g : ℍ → ℂ) ∣[k] alpha0 p) (beta p i • τ) := by
  rw [heckeFun, petersson_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  have h := petersson_mapGL k f ((g : ℍ → ℂ) ∣[k] alpha0 p) (beta p i) τ
  rw [slash_levelOne] at h
  rw [slash_heckeMatrix, h]

/-! ### The Fricke-type element `W = S α₀` -/

/-- `W = S α₀ = [[0,-p],[1,0]]`. -/
abbrev W : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ ModularGroup.S * alpha0 p

/-- `p` as a unit of `ℝ`. -/
def pUnit : ℝˣ := Units.mk0 (p.val : ℝ) (by exact_mod_cast p.property.ne_zero)

theorem pUnit_val : ((pUnit p : ℝˣ) : ℝ) = p.val := rfl

theorem scalar_val (u : ℝˣ) :
    (GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) ℝ) = !![(u : ℝ), 0; 0, u] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [GeneralLinearGroup.scalar]

theorem alpha0_mul_W : alpha0 p * W p =
    GeneralLinearGroup.scalar (Fin 2) (pUnit p) * SpecialLinearGroup.mapGL ℝ ModularGroup.S := by
  apply Units.ext
  simp only [Units.val_mul, alpha0_val, mapGL_val, ModularGroup.coe_S, scalar_val, pUnit_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_W : ((GeneralLinearGroup.det (W p) : ℝˣ) : ℝ) = p.val := by
  simp only [map_mul, Units.val_mul, det_mapGL, one_mul]
  change (alpha0 p : Matrix (Fin 2) (Fin 2) ℝ).det = p.val
  rw [alpha0_val, Matrix.det_fin_two_of]
  ring

/-- The conjugate `W γ W⁻¹` of an element of `Γ⁰(p)` (with `γ₀₁ = p b`). -/
def upperConj (γ : SL(2, ℤ)) (b : ℤ) (hb : γ 0 1 = p.val * b) : SL(2, ℤ) :=
  ⟨!![γ 1 1, -((p.val : ℤ) * γ 1 0); -b, γ 0 0], by
    rw [Matrix.det_fin_two_of]
    have := PeterssonCosets.det_eq γ
    rw [hb] at this
    linear_combination this⟩

theorem upperConj_mem (γ : SL(2, ℤ)) (b : ℤ) (hb : γ 0 1 = p.val * b) :
    upperConj p γ b hb ∈ upperLevel p := by
  rw [mem_upperLevel]
  change (p.val : ℤ) ∣ -((p.val : ℤ) * γ 1 0)
  exact (dvd_neg).mpr (dvd_mul_right _ _)

theorem W_mul_mapGL (γ : SL(2, ℤ)) (b : ℤ) (hb : γ 0 1 = p.val * b) :
    W p * SpecialLinearGroup.mapGL ℝ γ = SpecialLinearGroup.mapGL ℝ (upperConj p γ b hb) * W p := by
  have hb' : (γ 0 1 : ℝ) = p.val * b := by exact_mod_cast hb
  apply Units.ext
  simp only [Units.val_mul, alpha0_val, mapGL_val, ModularGroup.coe_S]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, upperConj, hb'] <;> ring

/-- The conjugate `α₀ γ α₀⁻¹` of an element of `Γ⁰(p)`. -/
def lowerShift (γ : SL(2, ℤ)) (b : ℤ) (hb : γ 0 1 = p.val * b) : SL(2, ℤ) :=
  ⟨!![γ 0 0, b; (p.val : ℤ) * γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    have := PeterssonCosets.det_eq γ
    rw [hb] at this
    linear_combination this⟩

theorem alpha0_mul_mapGL (γ : SL(2, ℤ)) (b : ℤ) (hb : γ 0 1 = p.val * b) :
    alpha0 p * SpecialLinearGroup.mapGL ℝ γ =
      SpecialLinearGroup.mapGL ℝ (lowerShift p γ b hb) * alpha0 p := by
  have hb' : (γ 0 1 : ℝ) = p.val * b := by exact_mod_cast hb
  apply Units.ext
  simp only [Units.val_mul, alpha0_val, mapGL_val]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lowerShift, hb'] <;> ring

/-! ### The two integrands -/

/-- `petersson(f, g|α₀)` is invariant under `Γ⁰(p)`. -/
theorem right_integrand_invariant (f g : CuspForm levelOne k) (γ : SL(2, ℤ))
    (hγ : γ ∈ upperLevel p) (τ : ℍ) :
    petersson k f ((g : ℍ → ℂ) ∣[k] alpha0 p) (γ • τ) =
      petersson k f ((g : ℍ → ℂ) ∣[k] alpha0 p) τ := by
  obtain ⟨b, hb⟩ := (mem_upperLevel p).mp hγ
  rw [← petersson_mapGL, slash_levelOne, ← SlashAction.slash_mul, alpha0_mul_mapGL p γ b hb,
    SlashAction.slash_mul, slash_levelOne]

/-- `W` carries the right integrand to the left one. -/
theorem right_integrand_W (f g : CuspForm levelOne k) (τ : ℍ) :
    petersson k f ((g : ℍ → ℂ) ∣[k] alpha0 p) (W p • τ) =
      petersson k ((f : ℍ → ℂ) ∣[k] alpha0 p) g τ := by
  have h := petersson_slash k f ((g : ℍ → ℂ) ∣[k] alpha0 p) (W p) τ
  have hdet := det_W p
  have hpos : 0 < ((GeneralLinearGroup.det (W p) : ℝˣ) : ℝ) := by
    rw [hdet]; exact_mod_cast p.property.pos
  rw [sigma_of_det_pos _ hpos, hdet] at h
  have hf : (f : ℍ → ℂ) ∣[k] W p = (f : ℍ → ℂ) ∣[k] alpha0 p := by
    rw [SlashAction.slash_mul, slash_levelOne]
  have hg : ((g : ℍ → ℂ) ∣[k] alpha0 p) ∣[k] W p = ((p.val : ℝ) : ℂ) ^ (k - 2) • (g : ℍ → ℂ) := by
    rw [← SlashAction.slash_mul, alpha0_mul_W, SlashAction.slash_mul, slash_scalar,
      ModularForm.smul_slash, slash_levelOne, sigma_of_det_pos _ (by rw [det_mapGL]; norm_num),
      pUnit_val]
  rw [hf, hg, petersson_smul_right] at h
  have hp : ((p.val : ℝ) : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
  have habs : ((|(p.val : ℝ)| : ℝ) : ℂ) = ((p.val : ℝ) : ℂ) := by
    rw [abs_of_nonneg (by positivity)]
  rw [habs] at h
  exact (mul_left_cancel₀ hp h).symm

/-- The image of `W` in `PGL(2,ℝ)`. -/
abbrev Wbar : PGL(2, ℝ) := ProjGenLinGroup.mk (W p)

theorem Wbar_conj_psl (γ : SL(2, ℤ)) (b : ℤ) (hb : γ 0 1 = p.val * b) :
    MulAut.conj (Wbar p) (psl γ) = psl (upperConj p γ b hb) := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  change ProjGenLinGroup.mk (W p) * ProjGenLinGroup.mk (SpecialLinearGroup.mapGL ℝ γ) =
    ProjGenLinGroup.mk (SpecialLinearGroup.mapGL ℝ (upperConj p γ b hb)) * ProjGenLinGroup.mk (W p)
  rw [← map_mul, ← map_mul, W_mul_mapGL p γ b hb]

theorem upperConj_upperConj (γ : SL(2, ℤ)) (b : ℤ) (hb : γ 0 1 = p.val * b) :
    upperConj p (upperConj p γ b hb) (-γ 1 0) (by simp [upperConj]) = γ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperConj, hb]

/-- **`W` normalizes `Γ⁰(p)`.** -/
theorem upperImage_map_Wbar :
    (upperImage p).map (MulAut.conj (Wbar p)).toMonoidHom = upperImage p := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := (mem_upperLevel p).mp hγ
    exact ⟨_, upperConj_mem p γ b hb, (Wbar_conj_psl p γ b hb).symm⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨b, hb⟩ := (mem_upperLevel p).mp hγ
    refine ⟨psl (upperConj p γ b hb), ⟨_, upperConj_mem p γ b hb, rfl⟩, ?_⟩
    change MulAut.conj (Wbar p) (psl (upperConj p γ b hb)) = psl γ
    rw [Wbar_conj_psl p _ (-γ 1 0) (by simp [upperConj]), upperConj_upperConj]

/-! ### Bounds and integrability -/

/-- `petersson k F F` is bounded. -/
def PBounded (F : ℍ → ℂ) : Prop := ∃ C, ∀ τ, ‖petersson k F F τ‖ ≤ C

theorem pbounded_cuspForm (f : CuspForm levelOne k) : PBounded k f :=
  CuspFormClass.petersson_bounded_left k levelOne f f

theorem pbounded_slash {F : ℍ → ℂ} (hF : PBounded k F) (g : GL (Fin 2) ℝ) :
    PBounded k (F ∣[k] g) := by
  obtain ⟨C, hC⟩ := hF
  refine ⟨‖((|((GeneralLinearGroup.det g : ℝˣ) : ℝ)| : ℝ) : ℂ) ^ (k - 2)‖ * C, fun τ => ?_⟩
  rw [petersson_slash, norm_mul, norm_sigma]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

theorem norm_petersson_le (F G : ℍ → ℂ) (τ : ℍ) :
    ‖petersson k F G τ‖ ≤ (‖petersson k F F τ‖ + ‖petersson k G G τ‖) / 2 := by
  simp only [petersson, norm_mul, Complex.norm_conj]
  have h3 := norm_nonneg ((τ.im : ℂ) ^ k)
  nlinarith [mul_nonneg (sq_nonneg (‖F τ‖ - ‖G τ‖)) h3]

theorem bounded_petersson {F G : ℍ → ℂ} (hF : PBounded k F) (hG : PBounded k G) :
    ∃ C, ∀ τ, ‖petersson k F G τ‖ ≤ C := by
  obtain ⟨C₁, h₁⟩ := hF
  obtain ⟨C₂, h₂⟩ := hG
  exact ⟨(C₁ + C₂) / 2, fun τ => (norm_petersson_le k F G τ).trans (by linarith [h₁ τ, h₂ τ])⟩

theorem continuous_cuspForm (f : CuspForm levelOne k) : Continuous (f : ℍ → ℂ) :=
  f.holo'.continuous

theorem continuous_slash_cuspForm (f : CuspForm levelOne k) (g : GL (Fin 2) ℝ) :
    Continuous ((f : ℍ → ℂ) ∣[k] g) :=
  (CuspForm.translate f g).holo'.continuous

theorem integrableOn_fd {Φ : ℍ → ℂ} (hc : Continuous Φ) (hb : ∃ C, ∀ τ, ‖Φ τ‖ ≤ C) :
    IntegrableOn Φ ModularGroup.fd volume := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)

theorem volume_upperDomain_lt_top : volume (upperDomain p) < ⊤ := by
  calc volume (upperDomain p) ≤ ∑ i, volume (psl (beta p i) • ModularGroup.fd) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _i : Option (Fin p.val), volume ModularGroup.fd := by simp only [measure_smul]
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ => volume_fd_lt_top

instance : IsFiniteMeasure (volume.restrict (upperDomain p)) :=
  isFiniteMeasure_restrict.mpr (volume_upperDomain_lt_top p).ne

theorem psl_beta_injective : Function.Injective fun i => psl (beta p i) := by
  intro i j h
  simp only at h
  rcases (psl_eq_iff _ _).mp h with h | h
  · apply beta_unique p (beta p j)⁻¹ i j
    · rw [h, mul_inv_cancel]; exact (upperLevel p).one_mem
    · rw [mul_inv_cancel]; exact (upperLevel p).one_mem
  · apply beta_unique p (beta p j)⁻¹ i j
    · rw [h, neg_mul, mul_inv_cancel]; exact neg_mem_upperLevel p (upperLevel p).one_mem
    · rw [mul_inv_cancel]; exact (upperLevel p).one_mem

theorem subgroup_smul_set (H : Subgroup PGL(2, ℝ)) (g : H) (S : Set ℍ) :
    g • S = (g : PGL(2, ℝ)) • S := rfl

theorem pairwise_aedisjoint :
    Pairwise (Function.onFun (AEDisjoint volume) fun i => psl (beta p i) • ModularGroup.fd) := by
  intro i j hij
  have hne : (⟨psl (beta p i), beta p i, rfl⟩ : modularImage) ≠ ⟨psl (beta p j), beta p j, rfl⟩ := by
    intro h
    exact hij (psl_beta_injective p (congrArg Subtype.val h))
  have h := fd_isFundamentalDomain.aedisjoint hne
  simp only [Function.onFun] at h ⊢
  rwa [subgroup_smul_set, subgroup_smul_set] at h

/-- **Unfolding.** -/
theorem integral_beta_sum {Φ : ℍ → ℂ} (hc : Continuous Φ) (hb : ∃ C, ∀ τ, ‖Φ τ‖ ≤ C) :
    ∫ τ in ModularGroup.fd, ∑ i, Φ (beta p i • τ) = ∫ τ in upperDomain p, Φ τ := by
  obtain ⟨C, hC⟩ := hb
  have hint : ∀ i, IntegrableOn (fun τ => Φ (beta p i • τ)) ModularGroup.fd volume := by
    intro i
    apply integrableOn_fd (hc.comp (continuous_const_smul (SpecialLinearGroup.mapGL ℝ (beta p i))))
    exact ⟨C, fun τ => hC _⟩
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have h1 : ∀ i, ∫ τ in ModularGroup.fd, Φ (beta p i • τ) =
      ∫ τ in psl (beta p i) • ModularGroup.fd, Φ τ := by
    intro i
    rw [setIntegral_smul_set]
    simp only [psl_smul]
  simp_rw [h1]
  have hU : IntegrableOn Φ (upperDomain p) volume :=
    Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)
  rw [upperDomain, integral_iUnion_ae (fun i => fd_isFundamentalDomain.nullMeasurableSet.smul _)
    (pairwise_aedisjoint p) hU, tsum_fintype]

/-! ### Self-adjointness -/

/-- **The Petersson product** `∫_𝒟 conj(f) g y^k dμ`. -/
def pet (f g : CuspForm levelOne k) : ℂ := ∫ τ in ModularGroup.fd, petersson k f g τ

theorem pet_hecke_left (f g : CuspForm levelOne k) :
    pet k (levelOneHecke k p f) g =
      ∫ τ in upperDomain p, petersson k ((f : ℍ → ℂ) ∣[k] alpha0 p) g τ := by
  unfold pet
  rw [levelOneHecke_apply]
  simp_rw [petersson_hecke_left]
  exact integral_beta_sum p
    (petersson_continuous k (continuous_slash_cuspForm k f _) (continuous_cuspForm k g))
    (bounded_petersson k (pbounded_slash k (pbounded_cuspForm k f) _) (pbounded_cuspForm k g))

theorem pet_hecke_right (f g : CuspForm levelOne k) :
    pet k f (levelOneHecke k p g) =
      ∫ τ in upperDomain p, petersson k f ((g : ℍ → ℂ) ∣[k] alpha0 p) τ := by
  unfold pet
  rw [levelOneHecke_apply]
  simp_rw [petersson_hecke_right]
  exact integral_beta_sum p
    (petersson_continuous k (continuous_cuspForm k f) (continuous_slash_cuspForm k g _))
    (bounded_petersson k (pbounded_cuspForm k f) (pbounded_slash k (pbounded_cuspForm k g) _))

/-- **`T_p` is self-adjoint for the Petersson product.** -/
theorem pet_hecke (f g : CuspForm levelOne k) :
    pet k (levelOneHecke k p f) g = pet k f (levelOneHecke k p g) := by
  rw [pet_hecke_left, pet_hecke_right]
  have hU := upperDomain_isFundamentalDomain p
  have hWU : IsFundamentalDomain (upperImage p) (Wbar p • upperDomain p) volume := by
    have := isFundamentalDomain_conj (upperImage p) hU (Wbar p)
    rwa [upperImage_map_Wbar] at this
  have hinv : ∀ (h : upperImage p) (x : ℍ),
      petersson k f ((g : ℍ → ℂ) ∣[k] alpha0 p) (h • x) =
        petersson k f ((g : ℍ → ℂ) ∣[k] alpha0 p) x := by
    rintro ⟨_, γ, hγ, rfl⟩ x
    change petersson k f ((g : ℍ → ℂ) ∣[k] alpha0 p) (psl γ • x) = _
    rw [psl_smul]
    exact right_integrand_invariant k p f g γ hγ x
  symm
  rw [hU.setIntegral_eq hWU hinv, setIntegral_smul_set]
  congr 1
  funext τ
  rw [pglMk_smul, right_integrand_W]

end TernaryPeriodPolynomials.Spectral.PeterssonHecke
