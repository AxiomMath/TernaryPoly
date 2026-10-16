module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.LiftFields
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.LiftSpan
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ArithmeticModularity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ModularFiniteIndexDimension
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Mathlib.NumberTheory.ModularForms.Cusps

@[expose] public section


/-!
# Finite dimensionality of the level subspaces of the span of lifts

Let `U ⊆ GL₂(𝔸_f)` be an open subgroup and `φ` a function in the span of the right
`GL₂(𝔸_f)`-translates of adelic lifts of weight-`k` cusp forms on `Γ₁(3)` which is right
`U`-invariant. Finitely many `c` with `K' ⊆ ⋃ c U` exist (`K'` is compact). For each such `c` the
function `τ ↦ (Im τ)^(-k/2) φ(c · gUp τ)` is a modular form of weight `k` for the image `Γ_c` of
`{σ ∈ SL₂(ℤ) | c⁻¹ σ c ∈ U}`, a subgroup of finite index (`GL₂(Ẑ)` is compact): invariance comes
from left `GL₂(ℚ)`-invariance and right `U`-invariance, holomorphy and the weight law from
`IsHolomorphicWeight`, and the growth condition from boundedness of `φ`. Strong approximation
`GL₂(𝔸) = GL₂(ℚ) GL₂(ℝ)⁺ K'` shows that these finitely many modular forms determine `φ`, so the
level subspace embeds in a finite product of finite-dimensional spaces (`liftLevelFinite`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold
open TernaryPeriodPolynomials.CuspIntegral
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (binaryRealGammaOneThree modular_finite_dimensional_of_finite_index)

namespace TernaryPeriodPolynomials.Regularity

namespace LevelFinite

/-! ### Group-theoretic preliminaries -/

theorem atInf_mul (A B : BinaryRealGL) : atInfinity (A * B) = atInfinity A * atInfinity B :=
  map_mul infGL A B

theorem atFin_mul (u v : BinaryFiniteGL) : atFinite (u * v) = atFinite u * atFinite v :=
  map_mul finGL u v

theorem atFin_inv (u : BinaryFiniteGL) : atFinite u⁻¹ = (atFinite u)⁻¹ :=
  map_inv finGL u

theorem atFin_atInf_comm (u : BinaryFiniteGL) (r : BinaryRealGL) :
    atFinite u * atInfinity r = atInfinity r * atFinite u :=
  (infGL_finGL_comm r u).symm

/-- A compact set is covered by finitely many translates `x W`, `W = {g | c⁻¹ g c ∈ U}`. -/
theorem exists_finset_cover {U : Subgroup BinaryFiniteGL} (hU : IsOpen (U : Set BinaryFiniteGL))
    {C : Set BinaryFiniteGL} (hC : IsCompact C) (c : BinaryFiniteGL) :
    ∃ t : Finset BinaryFiniteGL, ∀ y ∈ C, ∃ x ∈ t, c⁻¹ * (x⁻¹ * y) * c ∈ U := by
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover
    (fun x => (fun y => c⁻¹ * (x⁻¹ * y) * c) ⁻¹' (U : Set BinaryFiniteGL)) (fun x _ => by
      have hcont : Continuous fun y : BinaryFiniteGL => c⁻¹ * (x⁻¹ * y) * c :=
        (continuous_const.mul (continuous_const.mul continuous_id)).mul continuous_const
      refine (hU.preimage hcont).mem_nhds ?_
      show c⁻¹ * (x⁻¹ * x) * c ∈ U
      rw [inv_mul_cancel, mul_one, inv_mul_cancel]
      exact U.one_mem)
  refine ⟨t, fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
  exact ⟨x, hx, hyx⟩

theorem levelGroup_le_integralLevel : levelGroup ≤ integralLevel := by
  intro κ hκ
  obtain ⟨m, -, rfl⟩ := hκ
  exact ⟨m, rfl⟩

/-- Finitely many `c` with `K' ⊆ ⋃ c U`. -/
theorem exists_levelReps {U : Subgroup BinaryFiniteGL} (hU : IsOpen (U : Set BinaryFiniteGL)) :
    ∃ t : Finset BinaryFiniteGL, ∀ κ ∈ levelGroup, ∃ c ∈ t, c⁻¹ * κ ∈ U := by
  obtain ⟨t, ht⟩ := exists_finset_cover hU integralLevel_isOpenCompact.2 1
  refine ⟨t, fun κ hκ => ?_⟩
  obtain ⟨x, hx, hxκ⟩ := ht κ (levelGroup_le_integralLevel hκ)
  refine ⟨x, hx, ?_⟩
  simpa using hxκ

/-- The finite component `SL₂(ℤ) → GL₂(Ẑ) → GL₂(𝔸_f)` of a rational matrix of `SL₂(ℤ)`. -/
def finSL : SpecialLinearGroup (Fin 2) ℤ →* BinaryFiniteGL :=
  (GeneralLinearGroup.map (n := Fin 2) integralEmbedding).comp
    (SpecialLinearGroup.mapGL IntegralAdeles)

theorem finSL_apply (σ : SpecialLinearGroup (Fin 2) ℤ) :
    finSL σ = GeneralLinearGroup.map integralEmbedding
      (SpecialLinearGroup.mapGL IntegralAdeles σ) :=
  rfl

theorem finSL_mem (σ : SpecialLinearGroup (Fin 2) ℤ) : finSL σ ∈ integralLevel :=
  ⟨SpecialLinearGroup.mapGL IntegralAdeles σ, rfl⟩

/-- `{σ ∈ SL₂(ℤ) | c⁻¹ σ_f c ∈ U}`. -/
def gammaC (U : Subgroup BinaryFiniteGL) (c : BinaryFiniteGL) :
    Subgroup (SpecialLinearGroup (Fin 2) ℤ) :=
  U.comap ((MulAut.conj c⁻¹).toMonoidHom.comp finSL)

theorem mem_gammaC {U : Subgroup BinaryFiniteGL} {c : BinaryFiniteGL}
    {σ : SpecialLinearGroup (Fin 2) ℤ} : σ ∈ gammaC U c ↔ c⁻¹ * finSL σ * c ∈ U := by
  show (MulAut.conj c⁻¹) (finSL σ) ∈ U ↔ _
  rw [MulAut.conj_apply, inv_inv]

/-- `Γ_c` has finite index in `SL₂(ℤ)`: `GL₂(Ẑ)` is compact and `U` is open. -/
theorem gammaC_finiteIndex {U : Subgroup BinaryFiniteGL} (hU : IsOpen (U : Set BinaryFiniteGL))
    (c : BinaryFiniteGL) : (gammaC U c).FiniteIndex := by
  obtain ⟨t, ht⟩ := exists_finset_cover hU integralLevel_isOpenCompact.2 c
  have hcov : ∀ σ : SpecialLinearGroup (Fin 2) ℤ, ∃ x ∈ t, c⁻¹ * (x⁻¹ * finSL σ) * c ∈ U :=
    fun σ => ht _ (finSL_mem σ)
  choose pick hpick hpickU using hcov
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  refine Finite.of_injective
    (fun q : SpecialLinearGroup (Fin 2) ℤ ⧸ gammaC U c => (⟨pick q.out, hpick _⟩ : t)) ?_
  intro q₁ q₂ h
  have h' : pick q₁.out = pick q₂.out := congrArg Subtype.val h
  have e₁ := QuotientGroup.out_eq' q₁
  have e₂ := QuotientGroup.out_eq' q₂
  rw [← e₁, ← e₂, QuotientGroup.eq, mem_gammaC]
  have a₁ := hpickU q₁.out
  have a₂ := hpickU q₂.out
  rw [h'] at a₁
  have h₃ := U.mul_mem (U.inv_mem a₁) a₂
  convert h₃ using 1
  rw [map_mul, map_inv]
  group

/-- The real image `Γ_c ⊆ SL₂(ℝ)` of `gammaC U c`. -/
def realGamma (U : Subgroup BinaryFiniteGL) (c : BinaryFiniteGL) : Subgroup (GL (Fin 2) ℝ) :=
  (gammaC U c).map (SpecialLinearGroup.mapGL ℝ)

instance realGamma_hasDetOne (U : Subgroup BinaryFiniteGL) (c : BinaryFiniteGL) :
    (realGamma U c).HasDetOne := by
  unfold realGamma
  infer_instance

theorem realGamma_finiteRelIndex {U : Subgroup BinaryFiniteGL}
    (hU : IsOpen (U : Set BinaryFiniteGL)) (c : BinaryFiniteGL) :
    (realGamma U c).IsFiniteRelIndex (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range := by
  have := gammaC_finiteIndex hU c
  constructor
  rw [realGamma, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]
  exact Subgroup.finiteIndex_iff.mp inferInstance

theorem realGamma_le_SL (U : Subgroup BinaryFiniteGL) (c : BinaryFiniteGL) :
    realGamma U c ≤ 𝒮ℒ := by
  intro γ hγ
  obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hγ
  exact ⟨σ, rfl⟩

/-! ### Möbius algebra -/

/-- `g · gUp z = gUp (g z) · stab a b` with `a - b i = c z + d`. -/
theorem mul_gUp (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    g * gUp z = gUp (moeb g z) * stab (denom g z).re (-(denom g z).im) := by
  have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
  have h := mul_gBar g hz'
  simp only [gBar, Complex.conj_conj, moeb_conj, denom_conj, Complex.conj_re,
    Complex.conj_im] at h
  exact h

theorem normSq_rpow_half (j : ℂ) (k : ℕ) : Complex.normSq j ^ ((k : ℝ) / 2) = ‖j‖ ^ k := by
  rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast ‖j‖ 2, ← Real.rpow_mul (norm_nonneg _),
    show ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = ((k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

theorem conj_div_norm_pow {j : ℂ} (hj : j ≠ 0) (k : ℕ) :
    ((starRingEnd ℂ) j / ((‖j‖ : ℝ) : ℂ)) ^ k = ((‖j‖ : ℝ) : ℂ) ^ k * (j ^ k)⁻¹ := by
  have hJ : ((‖j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hj
  have hsq : ((‖j‖ : ℝ) : ℂ) ^ 2 = j * (starRingEnd ℂ) j := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [div_pow, div_eq_iff (pow_ne_zero k hJ)]
  calc (starRingEnd ℂ) j ^ k = (j * (starRingEnd ℂ) j) ^ k * (j ^ k)⁻¹ := by
        rw [mul_pow, mul_comm (j ^ k), mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hj), mul_one]
    _ = (((‖j‖ : ℝ) : ℂ) ^ 2) ^ k * (j ^ k)⁻¹ := by rw [hsq]
    _ = ((‖j‖ : ℝ) : ℂ) ^ k * (j ^ k)⁻¹ * ((‖j‖ : ℝ) : ℂ) ^ k := by ring

/-! ### The functions on `GL₂(𝔸)` -/

variable {k : ℕ} {χ : Adelesˣ →* ℂ} {φ : BinaryAdelicGL → ℂ} {U : Subgroup BinaryFiniteGL}

/-- The weight law along `r · gUp z`. -/
theorem phi_mul_gUp (hw : IsHolomorphicWeight k φ) (x : BinaryAdelicGL) (r : BinaryRealGL)
    {z : ℂ} (hz : z.im ≠ 0) :
    φ (x * atInfinity (r * gUp z)) =
      ((starRingEnd ℂ) (denom r z) / ((‖denom r z‖ : ℝ) : ℂ)) ^ k *
        φ (x * atInfinity (gUp (moeb r z))) := by
  have hab : (denom r z).re ^ 2 + (-(denom r z).im) ^ 2 ≠ 0 := by
    rw [neg_sq]
    exact stab_sq_ne r hz
  rw [mul_gUp r hz, atInf_mul, ← mul_assoc, hw.weight _ _ _ hab]
  have h1 : (⟨(denom r z).re, -(denom r z).im⟩ : ℂ) = (starRingEnd ℂ) (denom r z) :=
    Complex.ext (by simp) (by simp)
  rw [h1, Complex.norm_conj]

/-- Invariance of `r ↦ φ (c · r)` under `Γ_c`, from left rationality and right `U`-invariance. -/
theorem shift_invariant (hφ : CuspIntegral.IsCuspidalLike χ φ)
    (hφU : ∀ u ∈ U, (fun x => φ (x * atFinite u)) = φ) {c : BinaryFiniteGL}
    {σ : SpecialLinearGroup (Fin 2) ℤ} (hσ : σ ∈ gammaC U c) (s : BinaryRealGL) :
    φ (atFinite c * atInfinity (SpecialLinearGroup.mapGL ℝ σ * s)) =
      φ (atFinite c * atInfinity s) := by
  rw [mem_gammaC] at hσ
  have hdec : GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ σ) =
      atInfinity (SpecialLinearGroup.mapGL ℝ σ) * atFinite (finSL σ) :=
    PlaneEisensteinContinuation.ArithmeticModularity.rational_decomposition σ
  have hA : atInfinity (SpecialLinearGroup.mapGL ℝ σ) =
      GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ σ) *
        (atFinite (finSL σ))⁻¹ :=
    eq_mul_inv_of_mul_eq hdec.symm
  have hu : c⁻¹ * (finSL σ)⁻¹ * c ∈ U := by
    convert U.inv_mem hσ using 1
    group
  calc φ (atFinite c * atInfinity (SpecialLinearGroup.mapGL ℝ σ * s))
      = φ (GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ σ) *
          ((atFinite (finSL σ))⁻¹ * atFinite c * atInfinity s)) := by
        rw [atInf_mul, ← mul_assoc (atFinite c) (atInfinity (SpecialLinearGroup.mapGL ℝ σ)),
          atFin_atInf_comm c (SpecialLinearGroup.mapGL ℝ σ), hA]
        simp only [mul_assoc]
    _ = φ ((atFinite (finSL σ))⁻¹ * atFinite c * atInfinity s) := hφ.leftRational _ _
    _ = φ (atFinite c * atInfinity s * atFinite (c⁻¹ * (finSL σ)⁻¹ * c)) := by
        rw [mul_assoc (atFinite c) (atInfinity s), ← atFin_atInf_comm, ← mul_assoc, ← atFin_mul,
          show c * (c⁻¹ * (finSL σ)⁻¹ * c) = (finSL σ)⁻¹ * c by group, atFin_mul, atFin_inv]
    _ = φ (atFinite c * atInfinity s) := congrFun (hφU _ hu) _

/-! ### The classical functions -/

/-- `τ ↦ (Im τ)^(-k/2) φ (c · gUp τ)`. -/
def classicalFun (k : ℕ) (φ : BinaryAdelicGL → ℂ) (c : BinaryFiniteGL) (τ : ℍ) : ℂ :=
  (((τ.im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) * φ (atFinite c * atInfinity (gUp (τ : ℂ)))

theorem norm_classicalFun_mul (c : BinaryFiniteGL) (τ : ℍ) :
    ‖classicalFun k φ c τ‖ * τ.im ^ ((k : ℝ) / 2) =
      ‖φ (atFinite c * atInfinity (gUp (τ : ℂ)))‖ := by
  have hB : 0 < τ.im ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos τ.im_pos _
  have hB' : τ.im ^ ((k : ℝ) / 2) ≠ 0 := hB.ne'
  rw [classicalFun, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hB.le),
    mul_right_comm, inv_mul_cancel₀ hB', one_mul]

theorem classicalFun_moeb (hφ : CuspIntegral.IsCuspidalLike χ φ)
    (hw : IsHolomorphicWeight k φ) (hφU : ∀ u ∈ U, (fun x => φ (x * atFinite u)) = φ)
    {c : BinaryFiniteGL} {σ : SpecialLinearGroup (Fin 2) ℤ} (hσ : σ ∈ gammaC U c) (τ : ℍ)
    (hmw : 0 < (moeb (SpecialLinearGroup.mapGL ℝ σ) τ).im) :
    classicalFun k φ c ⟨moeb (SpecialLinearGroup.mapGL ℝ σ) τ, hmw⟩ *
        (denom (SpecialLinearGroup.mapGL ℝ σ) τ ^ k)⁻¹ = classicalFun k φ c τ := by
  have hz : 0 < (τ : ℂ).im := τ.im_pos
  have hj : denom (SpecialLinearGroup.mapGL ℝ σ) τ ≠ 0 := denom_ne_zero _ hz.ne'
  have hdet1 : (SpecialLinearGroup.mapGL ℝ σ).val.det = 1 := by
    have h := congrArg Units.val (det_mapGL_real σ)
    rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h
  have him : (moeb (SpecialLinearGroup.mapGL ℝ σ) τ).im =
      (τ : ℂ).im / Complex.normSq (denom (SpecialLinearGroup.mapGL ℝ σ) τ) := by
    rw [im_moeb, hdet1, one_mul]
  have hQ : φ (atFinite c * atInfinity (gUp (τ : ℂ))) =
      ((starRingEnd ℂ) (denom (SpecialLinearGroup.mapGL ℝ σ) τ) /
          ((‖denom (SpecialLinearGroup.mapGL ℝ σ) τ‖ : ℝ) : ℂ)) ^ k *
        φ (atFinite c * atInfinity (gUp (moeb (SpecialLinearGroup.mapGL ℝ σ) τ))) := by
    rw [← shift_invariant hφ hφU hσ (gUp (τ : ℂ))]
    exact phi_mul_gUp hw _ _ hz.ne'
  have hBw : (moeb (SpecialLinearGroup.mapGL ℝ σ) τ).im ^ ((k : ℝ) / 2) =
      (τ : ℂ).im ^ ((k : ℝ) / 2) / ‖denom (SpecialLinearGroup.mapGL ℝ σ) τ‖ ^ k := by
    rw [him, Real.div_rpow hz.le (Complex.normSq_nonneg _), normSq_rpow_half]
  change ((((moeb (SpecialLinearGroup.mapGL ℝ σ) τ).im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) *
      φ (atFinite c * atInfinity (gUp (moeb (SpecialLinearGroup.mapGL ℝ σ) τ))) *
        (denom (SpecialLinearGroup.mapGL ℝ σ) τ ^ k)⁻¹ =
      ((((τ : ℂ).im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) * φ (atFinite c * atInfinity (gUp (τ : ℂ)))
  rw [hQ, hBw, conj_div_norm_pow hj]
  generalize φ (atFinite c * atInfinity (gUp (moeb (SpecialLinearGroup.mapGL ℝ σ) τ))) = P
  generalize (τ : ℂ).im ^ ((k : ℝ) / 2) = B
  push_cast
  rw [inv_div]
  ring

/-- Invariance of the classical function under `Γ_c`. -/
theorem classicalFun_slash (hφ : CuspIntegral.IsCuspidalLike χ φ)
    (hw : IsHolomorphicWeight k φ) (hφU : ∀ u ∈ U, (fun x => φ (x * atFinite u)) = φ)
    {c : BinaryFiniteGL} {σ : SpecialLinearGroup (Fin 2) ℤ} (hσ : σ ∈ gammaC U c) :
    classicalFun k φ c ∣[(k : ℤ)] (SpecialLinearGroup.mapGL ℝ σ) = classicalFun k φ c := by
  funext τ
  have hdet : 0 < (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ σ) : ℝˣ).val := by
    rw [det_mapGL_real, Units.val_one]
    exact one_pos
  have hmw : 0 < (moeb (SpecialLinearGroup.mapGL ℝ σ) τ).im := by
    have h := (SpecialLinearGroup.mapGL ℝ σ • τ).im_pos
    rwa [← UpperHalfPlane.coe_im, LiftFields.coe_smul_eq_moeb hdet] at h
  have hsm : SpecialLinearGroup.mapGL ℝ σ • τ = ⟨moeb (SpecialLinearGroup.mapGL ℝ σ) τ, hmw⟩ :=
    UpperHalfPlane.ext (LiftFields.coe_smul_eq_moeb hdet τ)
  have key := classicalFun_moeb hφ hw hφU hσ τ hmw
  rw [← hsm] at key
  show (classicalFun k φ c ∣[(k : ℤ)] σ) τ = classicalFun k φ c τ
  rw [ModularForm.SL_slash_apply, _root_.zpow_neg, zpow_natCast]
  exact key

theorem mdifferentiable_classicalFun (hw : IsHolomorphicWeight k φ) (c : BinaryFiniteGL) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (classicalFun k φ c) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (hw.holomorphic (atFinite c)).congr fun z hz => ?_
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos (mem_upper_iff.1 hz)]
  rfl

/-- A function with `‖F τ‖ (Im τ)^(k/2)` bounded is bounded at `∞` after any slash by
`SL₂(ℤ)`. -/
theorem isBoundedAtImInfty_slash_of_bound {F : ℍ → ℂ} {C : ℝ}
    (hC : ∀ τ : ℍ, ‖F τ‖ * τ.im ^ ((k : ℝ) / 2) ≤ C) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (F ∣[(k : ℤ)] γ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨C, 1, fun τ hτ => ?_⟩
  rw [ModularForm.SL_slash_apply, norm_mul, norm_zpow, _root_.zpow_neg, zpow_natCast]
  have him := ModularGroup.im_smul_eq_div_normSq γ τ
  have hj : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := by
    intro h0
    have hpos := (γ • τ).im_pos
    rw [him, h0, map_zero, div_zero] at hpos
    exact lt_irrefl _ hpos
  have hB := hC (γ • τ)
  rw [him, Real.div_rpow τ.im_pos.le (Complex.normSq_nonneg _), normSq_rpow_half] at hB
  have h1 : 1 ≤ τ.im ^ ((k : ℝ) / 2) := Real.one_le_rpow hτ (by positivity)
  have hjk : 0 < ‖UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ ^ k :=
    pow_pos (norm_pos_iff.mpr hj) k
  calc ‖F (γ • τ)‖ * (‖UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ ^ k)⁻¹
      ≤ ‖F (γ • τ)‖ * (‖UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ ^ k)⁻¹ *
          τ.im ^ ((k : ℝ) / 2) :=
        le_mul_of_one_le_right (by positivity) h1
    _ = ‖F (γ • τ)‖ *
          (τ.im ^ ((k : ℝ) / 2) / ‖UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ ^ k) := by
        ring
    _ ≤ C := hB

/-! ### The modular forms attached to a vector of the level subspace -/

variable {S : Set (CuspForm binaryRealGammaOneThree (k : ℤ))}

theorem data (φ : levelSubmodule S U) :
    CuspIntegral.IsCuspidalLike (centralChar (k : ℤ)) φ.1 ∧
      IsHolomorphicWeight k φ.1 ∧ ∀ u ∈ U, (fun x => φ.1 (x * atFinite u)) = φ.1 := by
  have hm : φ.1 ∈ liftSpan S ∧ ∀ u ∈ U, (fun x => φ.1 (x * atFinite u)) = φ.1 := φ.2
  have h := span_translates_le_cuspidalLike_inf S hm.1
  exact ⟨(Submodule.mem_inf.mp h).1, (Submodule.mem_inf.mp h).2, hm.2⟩

/-- The modular form of weight `k` for `Γ_c` attached to `φ`. -/
def classicalForm (φ : levelSubmodule S U) (c : BinaryFiniteGL) :
    ModularForm (realGamma U c) (k : ℤ) where
  toFun := classicalFun k φ.1 c
  slash_action_eq' := by
    intro γ hγ
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
    exact classicalFun_slash (data φ).1 (data φ).2.1 (data φ).2.2 hσ
  holo' := mdifferentiable_classicalFun (data φ).2.1 c
  bdd_at_cusps' := by
    intro c' hc'
    obtain ⟨C, hC⟩ := (data φ).1.bounded
    have hc'' : IsCusp c' 𝒮ℒ := IsCusp.mono (realGamma_le_SL U c) hc'
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc'']
    intro γ _
    exact isBoundedAtImInfty_slash_of_bound
      (fun τ => (norm_classicalFun_mul c τ).trans_le (hC _)) γ

theorem classicalForm_apply (φ : levelSubmodule S U) (c : BinaryFiniteGL) (τ : ℍ) :
    classicalForm φ c τ = classicalFun k φ.1 c τ :=
  rfl

/-- `φ ↦ classicalForm φ c` is linear. -/
def classicalMap (S : Set (CuspForm binaryRealGammaOneThree (k : ℤ))) (U : Subgroup BinaryFiniteGL)
    (c : BinaryFiniteGL) : levelSubmodule S U →ₗ[ℂ] ModularForm (realGamma U c) (k : ℤ) where
  toFun φ := classicalForm φ c
  map_add' φ ψ := by
    ext τ
    change classicalFun k (φ.1 + ψ.1) c τ = classicalFun k φ.1 c τ + classicalFun k ψ.1 c τ
    simp only [classicalFun, Pi.add_apply, mul_add]
  map_smul' a φ := by
    ext τ
    change classicalFun k (a • φ.1) c τ = a • classicalFun k φ.1 c τ
    simp only [classicalFun, Pi.smul_apply, smul_eq_mul]
    ring

/-- The classical functions at finitely many `c` with `K' ⊆ ⋃ c U` determine `φ`. -/
theorem eq_zero_of_classicalFun (hφ : CuspIntegral.IsCuspidalLike χ φ)
    (hw : IsHolomorphicWeight k φ) (hφU : ∀ u ∈ U, (fun x => φ (x * atFinite u)) = φ)
    {t : Finset BinaryFiniteGL} (ht : ∀ κ ∈ levelGroup, ∃ c ∈ t, c⁻¹ * κ ∈ U)
    (h0 : ∀ c ∈ t, ∀ τ, classicalFun k φ c τ = 0) : φ = 0 := by
  funext x
  show φ x = 0
  obtain ⟨γ, r, κ, hr, hκ, hx⟩ := exists_isDecomp x
  obtain ⟨c, hc, hu⟩ := ht κ hκ
  have h1 : φ x = φ (atFinite c * atInfinity r) := by
    rw [hx]
    calc φ (ratGL γ * (infGL r * finGL κ)) = φ (atInfinity r * atFinite κ) :=
          hφ.leftRational γ _
      _ = φ (atInfinity r * atFinite c * atFinite (c⁻¹ * κ)) := by
          rw [mul_assoc, ← atFin_mul, mul_inv_cancel_left]
      _ = φ (atInfinity r * atFinite c) := congrFun (hφU _ hu) _
      _ = φ (atFinite c * atInfinity r) := by rw [atFin_atInf_comm]
  have hdet : 0 < r.val.det := by rwa [GeneralLinearGroup.val_det_apply] at hr
  have hI : Complex.I.im ≠ 0 := by simp
  have hw0 : 0 < (moeb r Complex.I).im :=
    mem_upper_iff.1 (moeb_mem_upper r hdet (mem_upper_iff.2 (by simp)))
  have h2 := phi_mul_gUp hw (atFinite c) r hI
  rw [gUp_I, mul_one] at h2
  have h3 : φ (atFinite c * atInfinity (gUp (moeb r Complex.I))) = 0 := by
    have h := h0 c hc ⟨moeb r Complex.I, hw0⟩
    change ((((moeb r Complex.I).im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) *
      φ (atFinite c * atInfinity (gUp (moeb r Complex.I))) = 0 at h
    refine (mul_eq_zero.mp h).resolve_left ?_
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.rpow_pos_of_pos hw0 _).ne')
  rw [h1, h2, h3, mul_zero]

/-- **Finite dimensionality of the level subspaces** for open `U`. -/
theorem levelSubmodule_finiteDimensional (S : Set (CuspForm binaryRealGammaOneThree (k : ℤ)))
    {U : Subgroup BinaryFiniteGL} (hU : IsOpen (U : Set BinaryFiniteGL)) :
    FiniteDimensional ℂ (levelSubmodule S U) := by
  obtain ⟨t, ht⟩ := exists_levelReps hU
  have : ∀ c : t, FiniteDimensional ℂ (ModularForm (realGamma U c.1) (k : ℤ)) := fun c => by
    have := realGamma_finiteRelIndex hU c.1
    exact modular_finite_dimensional_of_finite_index (realGamma U c.1) (k : ℤ)
  let Φ : levelSubmodule S U →ₗ[ℂ] ((c : t) → ModularForm (realGamma U c.1) (k : ℤ)) :=
    LinearMap.pi fun c => classicalMap S U c.1
  refine FiniteDimensional.of_injective Φ ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ0
  apply Subtype.ext
  refine eq_zero_of_classicalFun (data φ).1 (data φ).2.1 (data φ).2.2 ht fun c hc τ => ?_
  have h := congrArg (fun F : ModularForm (realGamma U c) (k : ℤ) => F τ) (congrFun hφ0 ⟨c, hc⟩)
  exact h

end LevelFinite

open LevelFinite in
/-- **`LiftLevelFinite`**: the level subspaces of the span of finite translates of lifts are
finite dimensional. -/
theorem liftLevelFinite {k : ℕ} (S : Set (CuspForm binaryRealGammaOneThree (k : ℤ))) :
    LiftLevelFinite S :=
  fun _ hU _ => levelSubmodule_finiteDimensional S hU

end TernaryPeriodPolynomials.Regularity

end
