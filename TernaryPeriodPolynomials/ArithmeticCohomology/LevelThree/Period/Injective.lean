module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Eval
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Bol
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Decay
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ModularForms

@[expose] public section


/-!
# Injectivity of the level-three period map (Bol's argument)

Let `f ∈ S_{m+2}(Γ₁(3))`, `m > 0`, and suppose the class of its period cocycle in
`H¹(Γ₁(3), Sym^m ⊗ det^e)` vanishes: `P(γ i) = γ v - v` for some `v ∈ Sym^m`. Then
`Q = P + v` is `Γ₁(3)`-equivariant, `Q' = f (X₀ - zX₁)^m`, and
`Φ(z) = Q(z)(z, 1)` is a holomorphic function on the upper half-plane with
`Φ ∣[-m] γ = Φ` for `γ ∈ Γ₁(3)` (`Phi_slash`). The Taylor coordinates of `Q` satisfy the Bol
recursion (`LevelThreePeriodBol`) and are periodic at both cusps, hence `Φ` is bounded at both cusps
(`LevelThreePeriodDecay`): the cusp `∞` for `(f, Q)` and the cusp `0` for the `S`-transform
`(f ∣ S, ρ(S)⁻¹ Q(S ·))`. So `Φ` is a modular form of negative weight `-m` for `Γ₁(3)`
(`LevelThreeModularForms.mkForm`), hence zero, hence `f = 0` (Bol).

* `levelThreePeriodMap_injective`: for `m > 0` the period map
  `S_{m+2}(Γ₁(3)) → H¹(Γ₁(3), Sym^m ⊗ det^e)` is injective; in particular
  `S_{m+2}(Γ₁(3))` embeds in a finite-dimensional space.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix MvPolynomial UpperHalfPlane Filter Asymptotics
open scoped Manifold ModularForm MatrixGroups Topology
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParabolic
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodEval
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodTaylor
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodBol
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodDecay
open TernaryPeriodPolynomials.LevelThree.SymFixed (upperC lowerC)
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodInjective

variable (m : ℕ) (e : ℤ) (f : S m) (v : V m)

/-! ### Primitives with a constant -/

theorem isPrimitive_add_const {g : ℍ → ℂ} {P : ℂ → V m} (hP : IsPrimitive m g P) (w : V m) :
    IsPrimitive m g (fun z => P z + w) := by
  intro ℓ z hz
  have := (hP ℓ z hz).add_const (ℓ w)
  simpa [map_add] using this

/-- The `Γ₁(3)`-equivariant candidate `Q = P + v`. -/
def Qf : ℂ → V m := fun z => periodPrimitive m f z + v

theorem Qf_isPrimitive : IsPrimitive m ⇑f (Qf m f v) :=
  isPrimitive_add_const m (primitive_isPrimitive m (form_holo f)) v

/-- If the period cocycle is the coboundary of `v`, then `Q = P + v` is equivariant. -/
theorem Qf_equivariant (hv : ∀ k : core, (periodCocycle m e f).val k = coreRep m e k v - v)
    (k : core) (z : ℍ) :
    Qf m f v ((coreReal k • z : ℍ) : ℂ) = coreRep m e k (Qf m f v (z : ℂ)) := by
  have h1 := periodCocycle_primitive m e f k z
  rw [hv k] at h1
  have h2 : periodPrimitive m f ((coreReal k • z : ℍ) : ℂ) =
      (coreRep m e k v - v) + coreRep m e k (periodPrimitive m f z) := by
    rw [h1]
    abel
  simp only [Qf, map_add]
  rw [h2]
  abel

/-! ### The weight `-m` function `Φ` -/

/-- `Φ(z) = Q(z)(z, 1)`. -/
def Phi : ℍ → ℂ := fun z => aN m (Qf m f v) 0 (z : ℂ)

theorem Phi_eq (z : ℍ) : Phi m f v z = eval ![(z : ℂ), 1] (Qf m f v (z : ℂ)).val := aN_zero m _ _

theorem Phi_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Phi m f v) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 : DifferentiableOn ℂ (aN m (Qf m f v) 0) {z : ℂ | 0 < z.im} := fun z hz =>
    (hasDerivAt_aN m (Qf_isPrimitive m f v) 0 z hz).differentiableAt.differentiableWithinAt
  refine h1.congr (fun w hw => ?_)
  show aN m (Qf m f v) 0 ((ofComplex w : ℍ) : ℂ) = aN m (Qf m f v) 0 w
  rw [ofComplex_apply_of_im_pos hw]

theorem Phi_slash (hv : ∀ k : core, (periodCocycle m e f).val k = coreRep m e k v - v)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) :
    Phi m f v ∣[(-(m : ℤ))] γ = Phi m f v := by
  funext z
  obtain ⟨k, rfl⟩ := exists_core_of_mem γ hγ
  rw [ModularForm.SL_slash_apply]
  have hM : (coreSL k : GL (Fin 2) ℝ) = coreReal k := mapGL_coreSL k
  have hsmul : (coreSL k • z : ℍ) = coreReal k • z := by
    rw [← hM]
    try rfl
  have hΦ : Phi m f v (coreReal k • z) = (denom (coreReal k) z)⁻¹ ^ m * Phi m f v z := by
    rw [Phi_eq, Phi_eq, Qf_equivariant m e f v hv k z, coreRep_eq]
    exact eval_equivariant m e (coreReal k) (coreReal_det k) z _
  rw [hsmul, hM, hΦ, neg_neg, zpow_natCast]
  have hne : denom (coreReal k) z ≠ 0 := denom_ne_zero _ z
  have hne' : denom (coreReal k) z ^ m ≠ 0 := pow_ne_zero m hne
  rw [inv_pow]
  field_simp

/-! ### Boundedness at `∞` -/

theorem decay_atInfty {g : ℍ → ℂ} {κ : ℝ}
    (h : g =O[UpperHalfPlane.atImInfty] fun z : ℍ => Real.exp (-κ * z.im)) :
    ∃ C A : ℝ, 0 < A ∧ ∀ z : ℂ, A ≤ z.im →
      ‖g (ofComplex z)‖ ≤ C * Real.exp (-κ * z.im) := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hC
  refine ⟨C, max A 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
  have hpos : 0 < z.im := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) hz
  have hz' : A ≤ (⟨z, hpos⟩ : ℍ).im := le_trans (le_max_left _ _) hz
  have h1 := hA ⟨z, hpos⟩ hz'
  rw [ofComplex_apply_of_im_pos hpos]
  simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using h1

theorem f_decay : (⇑f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
    fun z : ℍ => Real.exp (-(2 * Real.pi) * z.im) :=
  (gammaOneThree_exp_decay f).congr_right (fun z => by congr 1; ring)

theorem slashS_decay : slashS m f =O[UpperHalfPlane.atImInfty]
    fun z : ℍ => Real.exp (-(2 * Real.pi / 3) * z.im) := by
  have h := gammaOneThree_ST_exp_decay f 0
  have h' : slashS m f =O[UpperHalfPlane.atImInfty]
      fun point : ℍ => Real.exp (-2 * Real.pi * point.im / 3) := by
    simpa using h
  exact h'.congr_right (fun z => by congr 1; ring)

theorem Phi_bounded_infty (hv : ∀ k : core, (periodCocycle m e f).val k = coreRep m e k v - v) :
    IsBoundedAtImInfty (Phi m f v) := by
  obtain ⟨C, A, hA, hF⟩ := decay_atInfty (f_decay m f)
  have hshift : ∀ z : ℂ, 0 < z.im → ∀ s : ℂ,
      eval ![s, 1] (Qf m f v (z + ((1 : ℝ) : ℂ))).val =
        eval ![s - ((1 : ℝ) : ℂ), 1] (Qf m f v z).val := by
    intro z hz s
    let ζ : ℍ := ⟨z, hz⟩
    have hcoe : ((coreReal coreT • ζ : ℍ) : ℂ) = z + ((1 : ℝ) : ℂ) := by
      rw [coreT_coe]
      simp [ζ]
    have heq := Qf_equivariant m e f v hv coreT ζ
    rw [hcoe] at heq
    rw [heq, coreRep_T, eval_upperC]
    simp [ζ]
  obtain ⟨M, hM⟩ := bounded_zero (m := m) (a := aN m (Qf m f v))
    (F := fun z => (⇑f) (ofComplex z)) (c := 1) (κ := 2 * Real.pi) (C := C) (A := A)
    one_pos (by positivity) hA
    (fun i z hz => hasDerivAt_aN m (Qf_isPrimitive m f v) i z hz) (aN_top m _)
    (fun i z hz => aN_periodic m (Qf m f v) ((1 : ℝ) : ℂ) z (hshift z hz) i) hF
  exact UpperHalfPlane.isBoundedAtImInfty_iff.mpr
    ⟨M, A, fun z hz => hM (z : ℂ) (by simpa using hz)⟩

/-! ### Boundedness at the cusp `0` -/

/-- The `S`-transform of `Q`. -/
def Qs : ℂ → V m := fun z =>
  Binary.homogeneousAction m e (complexify sG)⁻¹ (Qf m f v ((sG • ofComplex z : ℍ) : ℂ))

theorem Qs_apply (z : ℂ) : Qs m e f v z =
    Binary.homogeneousAction m e sC⁻¹ (Qf m f v ((sG • ofComplex z : ℍ) : ℂ)) := by
  unfold Qs
  rw [complexify_sG]

theorem Qs_isPrimitive : IsPrimitive m (slashS m f) (Qs m e f v) := by
  have hM : 0 < sG.val.det := by rw [sG_det]; exact one_pos
  have hprim := transform_isPrimitive m e (form_holo f) sG hM
  rw [sG_det, Complex.ofReal_one, _root_.one_zpow, one_smul] at hprim
  have hslash : (⇑f ∣[(m : ℤ) + 2] sG) = slashS m f := rfl
  rw [hslash] at hprim
  have h2 := isPrimitive_add_const m hprim (Binary.homogeneousAction m e (complexify sG)⁻¹ v)
  have hfun : Qs m e f v = fun z =>
      Binary.homogeneousAction m e (complexify sG)⁻¹
        (primitive m ⇑f ((sG • ofComplex z : ℍ) : ℂ)) +
      Binary.homogeneousAction m e (complexify sG)⁻¹ v := by
    funext z
    simp only [Qs, Qf, periodPrimitive, map_add]
  rw [hfun]
  exact h2

theorem Qs_shift (hv : ∀ k : core, (periodCocycle m e f).val k = coreRep m e k v - v)
    (z : ℂ) (hz : 0 < z.im) (s : ℂ) :
    eval ![s, 1] (Qs m e f v (z + ((3 : ℝ) : ℂ))).val =
      eval ![s - ((3 : ℝ) : ℂ), 1] (Qs m e f v z).val := by
  let ζ : ℍ := ⟨z, hz⟩
  have hζ : ofComplex z = ζ := ofComplex_apply_of_im_pos hz
  have hζ3 : ofComplex (z + ((3 : ℝ) : ℂ)) = (3 : ℝ) +ᵥ ζ := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos (by simpa using hz), UpperHalfPlane.coe_vadd]
    change z + ((3 : ℝ) : ℂ) = ((3 : ℝ) : ℂ) + (ζ : ℂ)
    exact add_comm _ _
  have e1 := Qf_equivariant m e f v hv coreL (sG • ((3 : ℝ) +ᵥ ζ))
  rw [coreL_smul_sG_smul, coreRep_L] at e1
  have e2 : Qf m f v ((sG • ((3 : ℝ) +ᵥ ζ) : ℍ) : ℂ) =
      Binary.homogeneousAction m e (lowerC 3)⁻¹ (Qf m f v ((sG • ζ : ℍ) : ℂ)) := by
    rw [e1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hQz : Qs m e f v z =
      Binary.homogeneousAction m e sC⁻¹ (Qf m f v ((sG • ζ : ℍ) : ℂ)) := by
    rw [Qs_apply, hζ]
  have hQz3 : Qs m e f v (z + ((3 : ℝ) : ℂ)) =
      Binary.homogeneousAction m e sC⁻¹ (Binary.homogeneousAction m e (lowerC 3)⁻¹
        (Qf m f v ((sG • ζ : ℍ) : ℂ))) := by
    rw [Qs_apply, hζ3, e2]
  have hw : Qf m f v ((sG • ζ : ℍ) : ℂ) =
      Binary.homogeneousAction m e sC (Qs m e f v z) := by
    rw [hQz, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have key : Qs m e f v (z + ((3 : ℝ) : ℂ)) =
      Binary.homogeneousAction m e (upperC 3) (Qs m e f v z) := by
    rw [hQz3, hw, ← sC_conj, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [key, eval_upperC]
  simp

theorem aN_Qs_eq (ζ : ℍ) :
    aN m (Qs m e f v) 0 (ζ : ℂ) = (Phi m f v ∣[(-(m : ℤ))] ModularGroup.S) ζ := by
  rw [aN_zero, ModularForm.SL_slash_apply]
  change eval ![(ζ : ℂ), 1] (Qs m e f v (ζ : ℂ)).val =
    Phi m f v (sG • ζ) * denom sG ζ ^ (-(-(m : ℤ)))
  have hζne : (ζ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero ζ
  have hu : Qs m e f v (ζ : ℂ) = Binary.homogeneousAction m e (complexify sG)⁻¹
      (Qf m f v ((sG • ζ : ℍ) : ℂ)) := by
    unfold Qs
    rw [ofComplex_apply]
  have hE := eval_equivariant m e sG sG_det ζ (Qs m e f v (ζ : ℂ))
  rw [hu, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
    sG_denom] at hE
  rw [neg_neg, zpow_natCast, sG_denom, Phi_eq, hu, hE, inv_pow]
  field_simp

theorem Phi_slashS_bounded (hv : ∀ k : core, (periodCocycle m e f).val k = coreRep m e k v - v) :
    IsBoundedAtImInfty (Phi m f v ∣[(-(m : ℤ))] ModularGroup.S) := by
  obtain ⟨C, A, hA, hF⟩ := decay_atInfty (slashS_decay m f)
  have hper : ∀ (i : ℕ) (z : ℂ), 0 < z.im → aN m (Qs m e f v) i (z + ((3 : ℝ) : ℂ)) =
      aN m (Qs m e f v) i z := fun i z hz =>
    aN_periodic m (Qs m e f v) ((3 : ℝ) : ℂ) z (Qs_shift m e f v hv z hz) i
  obtain ⟨M, hM⟩ := bounded_zero (m := m) (a := aN m (Qs m e f v))
    (F := fun z => (slashS m f) (ofComplex z)) (c := 3) (κ := 2 * Real.pi / 3) (C := C) (A := A)
    (by norm_num) (by positivity) hA
    (fun i z hz => hasDerivAt_aN m (Qs_isPrimitive m e f v) i z hz) (aN_top m _) hper hF
  refine UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨M, A, fun ζ hζ => ?_⟩
  rw [← aN_Qs_eq m e f v ζ]
  exact hM (ζ : ℂ) (by simpa using hζ)

/-! ### Conclusion -/

theorem Phi_zero (hv : ∀ k : core, (periodCocycle m e f).val k = coreRep m e k v - v)
    (hm : 0 < m) (z : ℍ) : Phi m f v z = 0 := by
  have hT : Phi m f v ∣[(-(m : ℤ))] ModularGroup.T = Phi m f v :=
    Phi_slash m e f v hv _ GammaOneThreeCosets.T_mem
  have hlower : Phi m f v ∣[(-(m : ℤ))] GammaOneThreeCosets.lowerL = Phi m f v :=
    Phi_slash m e f v hv _ GammaOneThreeCosets.lowerL_mem
  have h1 : (Phi m f v ∣[(-(m : ℤ))] ModularGroup.S) ∣[(-(m : ℤ))]
      (ModularGroup.T ^ (-3 : ℤ) : SL(2, ℤ)) = Phi m f v ∣[(-(m : ℤ))] ModularGroup.S := by
    rw [← SlashAction.slash_mul, ← GammaOneThreeCosets.lowerL_mul_S, SlashAction.slash_mul,
      hlower]
  have hS : (Phi m f v ∣[(-(m : ℤ))] ModularGroup.S) ∣[(-(m : ℤ))]
      (ModularGroup.T ^ 3 : SL(2, ℤ)) = Phi m f v ∣[(-(m : ℤ))] ModularGroup.S := by
    conv_lhs => rw [← h1]
    rw [← SlashAction.slash_mul, show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, _root_.zpow_neg,
      zpow_natCast, inv_mul_cancel, SlashAction.slash_one]
  let F := LevelThreeModularForms.mkForm (-(m : ℤ)) (Phi m f v) (Phi_mdifferentiable m f v) hT hS
    (Phi_bounded_infty m e f v hv) (Phi_slashS_bounded m e f v hv)
  have hzero : F = 0 := ModularForm.isZero_of_neg_weight (by omega) F
  have h2 := DFunLike.congr_fun hzero z
  simpa [F] using h2

/-- **Injectivity of the level-three period map (Bol).** -/
theorem levelThreePeriodMap_injective (hm : 0 < m) :
    Function.Injective (levelThreePeriodMap m e) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  rw [levelThreePeriodMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hf
  obtain ⟨v, hv'⟩ := hf
  have hv : ∀ k : core, (periodCocycle m e f).val k = coreRep m e k v - v := by
    intro k
    rw [← hv']
    rfl
  have hzero : ∀ z : ℂ, 0 < z.im → aN m (Qf m f v) 0 z = 0 := fun z hz =>
    Phi_zero m e f v hv hm ⟨z, hz⟩
  have hf0 := f_eq_zero_of_aN_zero m (Qf_isPrimitive m f v) hzero
  ext z
  have h3 := hf0 (z : ℂ) z.im_pos
  rw [ofComplex_apply] at h3
  simpa using h3

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodInjective
