module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Width
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeDecay

@[expose] public section


/-!
# The period map of `Γ₁(3)` cusp forms lands in the parabolic cohomology

The period cocycle `z ↦ P(γ i)` of a cusp form `f ∈ S_{m+2}(Γ₁(3))` takes values in `(T - 1)V` at
`T = [[1,1],[0,1]]` and in `(L - 1)V` at `L = [[1,0],[3,1]]`, the generators of the two cusp
stabilizers `∞` and `0` (these hyperplanes are `{p(1,0) = 0}` and `{p(0,1) = 0}`).

* At `∞`: `c(T)(1, 0) = F(i + 1) - F(i)` where `F` is the `X₀^m`-coordinate of the Eichler integral,
  and `F` is `1`-periodic because `f` is `1`-periodic and decays at `i∞`
  (`LevelThreePeriodWidth.coord_primitive_periodic`).
* At `0`: write `L = S T^{-3} S⁻¹`. The Eichler integral of `f` transforms along `S` into that of
  `g = f ∣ S`, which is `3`-periodic and decays at `i∞`, and `p(0, 1) ∘ ρ(S) = p(1, 0)`
  (`ell1_primitive_S`); this gives `c(L)(0, 1) = 0`.

Hence `levelThreePeriodMap_mem_parabolic`: the class of every period cocycle lies in
`parabolicH1 (coreRep m e) coreT coreL`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodWidth
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParabolic

/-! ### The matrix `S` and the functional identity `p(0,1) ∘ ρ(S) = p(1,0)` -/

/-- `S = [[0, -1], [1, 0]]` as a real matrix. -/
abbrev sG : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ ModularGroup.S

/-- `S = [[0, -1], [1, 0]]` as a complex matrix. -/
def sC : Binary.GL2 :=
  ⟨!![0, -1; 1, 0], !![0, 1; -1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem sG_det : sG.val.det = 1 := by
  rw [Matrix.det_fin_two]
  simp [binaryIntegral_mapGL_entry, ModularGroup.coe_S]

theorem complexify_sG : complexify sG = sC := by
  rw [show complexify sG = GeneralLinearGroup.map (algebraMap ℝ ℂ) (SpecialLinearGroup.mapGL ℝ
    ModularGroup.S) from rfl, binaryIntegral_mapGL_map]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryIntegral_mapGL_entry, sC, ModularGroup.coe_S]

theorem sC_inv_det : (GeneralLinearGroup.det sC⁻¹ : ℂ) = 1 := by
  rw [GeneralLinearGroup.val_det_apply]
  change Matrix.det !![(0 : ℂ), 1; -1, 0] = 1
  simp [Matrix.det_fin_two_of]

variable (m : ℕ) (e : ℤ)

/-- `p(1, 0) ∘ ρ(S)⁻¹ = p(0, 1)`. -/
theorem ell0_action_inv (v : V m) :
    ell0 m (Binary.homogeneousAction m e sC⁻¹ v) = ell1 m v := by
  rw [ell0_apply, Binary.homogeneousAction_coe, ell1_apply,
    SymFixed.eval_action_of_det e _ sC_inv_det]
  congr 2
  funext i
  fin_cases i <;> simp [sC, Fin.sum_univ_two]

/-- `p(0, 1)` is invariant under `L = [[1,0],[3,1]]`. -/
theorem ell1_coreRep_L (v : V m) : ell1 m (coreRep m e coreL v) = ell1 m v := by
  rw [ell1_apply, ell1_apply, coreRep_L, Binary.homogeneousAction_coe, SymFixed.eval_lower]
  simp

/-- `p(1, 0)` is invariant under `T = [[1,1],[0,1]]`. -/
theorem ell0_coreRep_T (v : V m) : ell0 m (coreRep m e coreT v) = ell0 m v := by
  rw [ell0_apply, ell0_apply, coreRep_T, Binary.homogeneousAction_coe, SymFixed.eval_upper]
  simp

/-! ### The Eichler integral at the cusp `0` -/

/-- The slash `f ∣ S` of a level-three cusp form. -/
abbrev slashS (f : S m) : ℍ → ℂ := (⇑f) ∣[weight m] ModularGroup.S

theorem slashS_holo (f : S m) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (slashS m f) :=
  gammaOneThree_slash_mdifferentiable f ModularGroup.S

theorem slashS_periodic (f : S m) : Function.Periodic (slashS m f ∘ ofComplex) (3 : ℂ) := by
  have h := gammaOneThree_ST_periodic f 0
  rw [pow_zero, mul_one] at h
  exact h

theorem slashS_zero (f : S m) : IsZeroAtImInfty (slashS m f) := by
  have h := CuspFormClass.zero_at_infty_slash f (ModularGroup.S * ModularGroup.T ^ 0)
  rw [pow_zero, mul_one] at h
  exact h

theorem S_smul_I : (sG • I : ℍ) = I := by
  change (ModularGroup.S • I : ℍ) = I
  rw [UpperHalfPlane.modular_S_smul]
  ext
  simp

/-- **The Eichler integral along `S`.** `p(0,1)` of `P_f(S ζ)` is `p(1,0)` of `P_{f∣S}(ζ)`. -/
theorem ell1_primitive_S (f : S m) (ζ : ℍ) :
    ell1 m (primitive m ⇑f ((sG • ζ : ℍ) : ℂ)) = ell0 m (primitive m (slashS m f) (ζ : ℂ)) := by
  have hf := form_holo f
  have hg := slashS_holo m f
  have hM : 0 < sG.val.det := by rw [sG_det]; exact one_pos
  have hprim := transform_isPrimitive m 0 hf sG hM
  rw [sG_det, Complex.ofReal_one, _root_.one_zpow, one_smul] at hprim
  have hslash : (⇑f ∣[(m : ℤ) + 2] sG) = slashS m f := rfl
  rw [hslash] at hprim
  have key := eq_primitive_add m hg _ hprim ζ ζ.im_pos
  have hI : ofComplex Complex.I = I := ofComplex_apply I
  simp only [ofComplex_apply, hI, S_smul_I, UpperHalfPlane.coe_I] at key
  have h0 : primitive m (⇑f) Complex.I = 0 := primitive_basepoint m ⇑f
  rw [h0, map_zero, add_zero] at key
  rw [complexify_sG] at key
  rw [← ell0_action_inv m 0, key]

/-! ### Vanishing of the boundary coordinates -/

theorem coreReal_coreT_val : (coreReal coreT).val = !![1, 1; 0, 1] := by
  rw [coreReal_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coreT, upper]

theorem coreReal_coreL_val : (coreReal coreL).val = !![1, 0; 3, 1] := by
  rw [coreReal_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coreL, lower]

theorem coreT_coe (w : ℍ) : ((coreReal coreT • w : ℍ) : ℂ) = (w : ℂ) + 1 := by
  have hpos : 0 < ((GeneralLinearGroup.det (coreReal coreT) : ℝˣ) : ℝ) := by
    rw [GeneralLinearGroup.val_det_apply, coreReal_det]
    exact one_pos
  rw [coe_smul_of_det_pos hpos, num_eq, denom_eq, coreReal_coreT_val]
  simp

theorem coreL_coe (w : ℍ) : ((coreReal coreL • w : ℍ) : ℂ) = (w : ℂ) / (3 * (w : ℂ) + 1) := by
  have hpos : 0 < ((GeneralLinearGroup.det (coreReal coreL) : ℝˣ) : ℝ) := by
    rw [GeneralLinearGroup.val_det_apply, coreReal_det]
    exact one_pos
  rw [coe_smul_of_det_pos hpos, num_eq, denom_eq, coreReal_coreL_val]
  simp

theorem sG_coe (z : ℍ) : ((sG • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
  change ((ModularGroup.S • z : ℍ) : ℂ) = _
  rw [UpperHalfPlane.modular_S_smul]
  simp [div_eq_mul_inv]

/-- The point `3 + i`. -/
def zeta3 : ℍ := (3 : ℝ) +ᵥ I

theorem zeta3_coe : (zeta3 : ℂ) = Complex.I + ((3 : ℝ) : ℂ) := by
  simp [zeta3, add_comm]

/-- `L · S · (3 + i) = i`. -/
theorem coreL_smul_sG_smul_zeta3 : coreReal coreL • (sG • zeta3) = I := by
  apply UpperHalfPlane.ext
  have hden : (3 : ℂ) + Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hz : (zeta3 : ℂ) = 3 + Complex.I := by
    rw [zeta3_coe]
    simp [add_comm]
  rw [coreL_coe, sG_coe, hz]
  have hy : (3 : ℂ) * (-1 / (3 + Complex.I)) + 1 = Complex.I / (3 + Complex.I) := by
    first | (field_simp; done) | (field_simp; ring)
  rw [hy, div_eq_iff (div_ne_zero Complex.I_ne_zero hden), UpperHalfPlane.coe_I,
    ← mul_div_assoc, Complex.I_mul_I]

theorem zero_at_infty (f : S m) : IsZeroAtImInfty (⇑f) := by
  simpa using CuspFormClass.zero_at_infty_slash f (1 : SL(2, ℤ))

/-- `c(T)(1, 0) = 0`. -/
theorem ell0_cocycle_T (f : S m) : ell0 m ((periodCocycle m e f).val coreT) = 0 := by
  rw [periodCocycle_apply, coreT_coe, UpperHalfPlane.coe_I]
  have h := coord_primitive_periodic m (form_holo f) 1 one_pos
    (by rw [Complex.ofReal_one]; exact gammaOneThree_periodic f) (zero_at_infty m f)
    Complex.I (by simp)
  rw [Complex.ofReal_one] at h
  change ell0 m (primitive m ⇑f (Complex.I + 1)) = 0
  rw [h, primitive_basepoint, map_zero]

/-- `c(L)(0, 1) = 0`. -/
theorem ell1_cocycle_L (f : S m) : ell1 m ((periodCocycle m e f).val coreL) = 0 := by
  rw [periodCocycle_primitive m e f coreL (sG • zeta3), coreL_smul_sG_smul_zeta3, map_sub,
    ell1_coreRep_L]
  have hI : periodPrimitive m f ((I : ℍ) : ℂ) = 0 := by
    rw [UpperHalfPlane.coe_I]
    exact primitive_basepoint m ⇑f
  rw [hI, map_zero, zero_sub, neg_eq_zero]
  change ell1 m (primitive m ⇑f ((sG • zeta3 : ℍ) : ℂ)) = 0
  rw [ell1_primitive_S m f zeta3, zeta3_coe]
  have h := coord_primitive_periodic m (slashS_holo m f) 3 (by norm_num)
    (by rw [show ((3 : ℝ) : ℂ) = 3 by norm_num]; exact slashS_periodic m f)
    (slashS_zero m f) Complex.I (by simp)
  rw [h, primitive_basepoint, map_zero]

/-- **Parabolicity of the period cocycle.** -/
theorem periodCocycle_mem_parabolic (f : S m) :
    periodCocycle m e f ∈ parabolicCocycles (coreRep m e) coreT coreL := by
  constructor
  · have h : moved (coreRep m e) coreT = LinearMap.ker (SymFixed.evalAt ![1, 0]) :=
      FullBound.moved_T_eq (m := m) (e := e)
    rw [h]
    exact LinearMap.mem_ker.mpr (ell0_cocycle_T m e f)
  · have h : moved (coreRep m e) coreL = LinearMap.ker (SymFixed.evalAt ![0, 1]) :=
      FullBound.moved_L_eq (m := m) (e := e)
    rw [h]
    exact LinearMap.mem_ker.mpr (ell1_cocycle_L m e f)

/-- **The level-three period classes are parabolic.** -/
theorem levelThreePeriodMap_mem_parabolic (f : S m) :
    levelThreePeriodMap m e f ∈ parabolicH1 (coreRep m e) coreT coreL :=
  ⟨periodCocycle m e f, periodCocycle_mem_parabolic m e f, rfl⟩

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParabolic
