module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.RealizeFields

@[expose] public section


/-!
# Equivariance of the realization

The realization intertwines the action `bergmanRep M` with right translation of functions on
`GL₂(𝔸)`. For the archimedean part this is the change of variables `w ↦ g⁻¹ w` (the hyperbolic
measure is Möbius invariant) together with the identity
`g · gBar v = gBar (g v) · stab a b` (`a + b i = denom g v`) and the weight-`k` law of the
finite-adelic model under the stabiliser of `i`; the automorphy factor of the action is exactly
the resulting phase (`autFactor_mul_rpow`). For the finite part it is the equivariance of `ε`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.Automorphic.SmoothVectors

namespace TernaryPeriodPolynomials.Regularity

/-- The automorphy factor is the phase `(j/|j|)^k`, `j = denom g (g⁻¹ w)`, relating the weights
`|Im w|^(k/2)` and `|Im (g⁻¹ w)|^(k/2)`. -/
theorem autFactor_mul_rpow (k : ℕ) (r : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    autFactor k r w * ((|w.im| ^ ((k : ℝ) / 2) : ℝ) : ℂ) =
      (denom r (moeb r⁻¹ w) / ((‖denom r (moeb r⁻¹ w)‖ : ℝ) : ℂ)) ^ k *
        ((|(moeb r⁻¹ w).im| ^ ((k : ℝ) / 2) : ℝ) : ℂ) := by
  have hD0 : denom r⁻¹ w ≠ 0 := denom_ne_zero r⁻¹ hw
  have hinv : denom r (moeb r⁻¹ w) = (denom r⁻¹ w)⁻¹ := by
    have h := denom_inv_moeb r⁻¹ hw
    rw [inv_inv] at h
    exact eq_inv_of_mul_eq_one_left h
  rw [← norm_autFactor_rpow k r hw, hinv]
  have hA : autFactor k r w =
      (((|r.val.det| ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) * (denom r⁻¹ w ^ k)⁻¹ := rfl
  have hc0 : 0 ≤ (|r.val.det| ^ ((k : ℝ) / 2))⁻¹ := by positivity
  have hDn : ((‖denom r⁻¹ w‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hD0
  have hX : ((|r.val.det| ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < |r.val.det| ^ ((k : ℝ) / 2) :=
      Real.rpow_pos_of_pos (abs_pos.mpr (gl_det_ne_zero r)) _
    exact_mod_cast this.ne'
  rw [hA]
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0, norm_inv, norm_pow]
  push_cast
  field_simp
  rw [div_pow]
  have hDk : denom r⁻¹ w ^ k ≠ 0 := pow_ne_zero _ hD0
  field_simp

variable {k : ℕ} (M : FiniteModel k)

/-- Vectors fixed by `U` are moved by `σ f` to vectors fixed by `f U f⁻¹`. -/
theorem mem_fixed_conj {U : Subgroup BinaryFiniteGL} {e : M.E}
    (he : e ∈ fixedSubmodule M.σ U) (f : BinaryFiniteGL) :
    M.σ f e ∈ fixedSubmodule M.σ (U.map (MulAut.conj f).toMonoidHom) := by
  rintro ⟨_, hmem⟩
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hmem
  change M.σ (f * u * f⁻¹) (M.σ f e) = M.σ f e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    ← Module.End.mul_apply (M.σ f⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    he ⟨u, hu⟩]

/-- Archimedean equivariance at a fixed level. -/
theorem realizeU_realRep {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    {F : BergmanSpace k M.E} (hF : ∀ w, F w ∈ fixedSubmodule M.σ U) (r : GL (Fin 2) ℝ)
    (x : BinaryAdelicGL) :
    realizeU M hU (realRep k M.E r F) x = realizeU M hU F (x * atInfinity r) := by
  have hmp := measurePreserving_moeb r⁻¹
  have hRHS : realizeU M hU F (x * atInfinity r) =
      ∫ w, evalU M hU (x * atInfinity r * atInfinity (gBar (moeb r⁻¹ w))) (F (moeb r⁻¹ w)) *
        ((|(moeb r⁻¹ w).im| ^ ((k : ℝ) / 2) : ℝ) : ℂ) ∂hypMeasure := by
    rw [realizeU]
    conv_lhs => rw [← hmp.map_eq]
    refine integral_map hmp.measurable.aemeasurable ?_
    rw [hmp.map_eq]
    exact BergmanAux.aesm (continuousOn_realizeIntegrand M hU F _)
  rw [hRHS, realizeU]
  refine integral_congr_ae ?_
  filter_upwards [ae_im_ne_zero] with w hw
  have hv : (moeb r⁻¹ w).im ≠ 0 := moeb_im_ne_zero r⁻¹ hw
  have hmat : x * atInfinity r * atInfinity (gBar (moeb r⁻¹ w)) =
      x * atInfinity (gBar w) *
        atInfinity (stab (denom r (moeb r⁻¹ w)).re (denom r (moeb r⁻¹ w)).im) := by
    rw [mul_assoc, ← atInfinity_mul_binary, mul_gBar r hv, moeb_moeb_inv r hw,
      atInfinity_mul_binary, mul_assoc]
  rw [realRep_apply r F hw, map_smul, smul_eq_mul, hmat, evalU_of_mem M hU _ (hF _),
    evalU_of_mem M hU _ (hF _), M.weight _ _ _ _ (stab_sq_ne r hv), Complex.eta,
    mul_right_comm, autFactor_mul_rpow k r hw]
  ring

/-- Finite-adelic equivariance at a fixed level. -/
theorem realizeU_finRep {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    {F : BergmanSpace k M.E} (hF : ∀ w, F w ∈ fixedSubmodule M.σ U) (f : BinaryFiniteGL)
    (x : BinaryAdelicGL) :
    realizeU M (hU.map_conj f) (finRep k M.σ M.unitary f F) x =
      realizeU M hU F (x * atFinite f) := by
  unfold realizeU
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [finRep_apply]
  rw [evalU_of_mem M (hU.map_conj f) _ (mem_fixed_conj M (hF w) f), evalU_of_mem M hU _ (hF w),
    mul_assoc x (atFinite f), ← atInfinity_mul_atFinite_comm, ← mul_assoc]
  have h := M.equivariant f ⟨F w, fixed_le_finiteSmooth M hU (hF w)⟩ (x * atInfinity (gBar w))
  exact congrArg (· * ((|w.im| ^ ((k : ℝ) / 2) : ℝ) : ℂ)) h

theorem eq_atInfinity_mul_atFinite (g : BinaryAdelicGL) :
    g = atInfinity (Automorphic.SmoothVectors.realPart g) *
      atFinite (Automorphic.SmoothVectors.finitePart g) := by
  rw [atInfinity, atFinite, combineGL_mul, mul_one, one_mul, combineGL_parts]

/-- The values of `bergmanRep M g F` are fixed by the conjugate level. -/
theorem bergmanRep_apply_mem {U : Subgroup BinaryFiniteGL} {F : BergmanSpace k M.E}
    (hF : ∀ w, F w ∈ fixedSubmodule M.σ U) (g : BinaryAdelicGL) (w : ℂ) :
    bergmanRep M g F w ∈ fixedSubmodule M.σ (U.map (MulAut.conj (finitePart g)).toMonoidHom) := by
  rw [bergmanRep_apply]
  by_cases hw : w.im = 0
  · rw [realRep_apply_of_im_eq_zero _ _ hw]
    exact Submodule.zero_mem _
  · rw [realRep_apply _ _ hw, finRep_apply]
    exact Submodule.smul_mem _ _ (mem_fixed_conj M (hF _) _)

/-- Equivariance of the realization of smooth vectors. -/
theorem realizeFun_equivariant (g : BinaryAdelicGL) (F : smoothSubmodule (bergmanRep M))
    (x : BinaryAdelicGL) :
    realizeFun ⟨bergmanRep M g F.val, smooth_stable (bergmanRep_unitary M) g F.property⟩ x =
      realizeFun F (x * g) := by
  have hU := level_isOpenCompact F
  have hFU : ∀ w, (F.val : BergmanSpace k M.E) w ∈ fixedSubmodule M.σ (level F) :=
    apply_mem_fixed (level_fixed F)
  have hfin : ∀ w, finRep k M.σ M.unitary (finitePart g) F.val w ∈
      fixedSubmodule M.σ ((level F).map (MulAut.conj (finitePart g)).toMonoidHom) := fun w => by
    rw [finRep_apply]
    exact mem_fixed_conj M (hFU w) _
  rw [realizeFun_eq _ (hU.map_conj (finitePart g)) (bergmanRep_apply_mem M hFU g),
    realizeFun_eq F hU hFU]
  show realizeU M _ (bergmanRep M g F.val) x = _
  rw [bergmanRep_apply, realizeU_realRep M (hU.map_conj (finitePart g)) hfin,
    realizeU_finRep M hU hFU, mul_assoc, ← eq_atInfinity_mul_atFinite]

end TernaryPeriodPolynomials.Regularity

end
