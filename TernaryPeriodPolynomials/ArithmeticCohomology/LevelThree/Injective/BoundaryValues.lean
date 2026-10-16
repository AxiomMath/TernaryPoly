module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.BoundaryValuesAux
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.PrimitiveLimits
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Moment

@[expose] public section


/-!
# Boundary values of the period cocycle of a level-three cusp form

Let `f ∈ S_{m+2}(Γ₁(3))`, `P` its Eichler integral with `P(i) = 0`, and `c = periodCocycle m e f`.
The limit `a = P(i∞)` along the imaginary axis exists and satisfies `c(T) = a - ρ(T) a`; the
Eichler integral `Q` of `f ∣ S` has a limit `a_S` at `i∞`, and `b = ρ(S) a_S = P(0)` satisfies
`c(L) = b - ρ(L) b`. The coordinates of `a - b` are `C(m, j) (-i)^(m-j) i · M_{m-j}(f)`, where
`M_p(f) = ∫_0^∞ t^p f(i t) dt` is the `p`-th moment (`exists_boundary_values`). The moments are
integrable for cusp forms of any weight (`moment_integrable`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane Filter MeasureTheory
open scoped Manifold ModularForm MatrixGroups Topology
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodWidth
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParabolic
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers (binaryStandardBasis)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodEval (coreL_smul_sG_smul)
open TernaryPeriodPolynomials.LevelThreeInjective.BoundaryValuesAux
open TernaryPeriodPolynomials.LevelThreeInjective.PrimitiveLimits
  (ExpDecay exists_tendsto_shift coord_eq_integral_Ioi coord_eq_integral_Ioc
    integrableOn_Ioi_one integrableOn_Ioc_zero_one)

namespace TernaryPeriodPolynomials.LevelThreeInjective.BoundaryValues

/-! ### Coordinatewise convergence in `V m` -/

/-- Coordinatewise convergence in `V m`. -/
def CoordTendsto (m : ℕ) {α : Type*} (l : Filter α) (v : α → V m) (a : V m) : Prop :=
  ∀ j : Fin (m + 1), Tendsto (fun t => (binaryStandardBasis m).coord j (v t)) l
    (𝓝 ((binaryStandardBasis m).coord j a))

namespace CoordTendsto

variable {m : ℕ} {α : Type*} {l : Filter α} {v w : α → V m} {a b : V m}

theorem sub (hv : CoordTendsto m l v a) (hw : CoordTendsto m l w b) :
    CoordTendsto m l (fun t => v t - w t) (a - b) := fun j => by
  simpa only [map_sub] using (hv j).sub (hw j)

theorem linear (φ : V m →ₗ[ℂ] V m) (hv : CoordTendsto m l v a) :
    CoordTendsto m l (fun t => φ (v t)) (φ a) := by
  intro j
  have key : ∀ x : V m, (binaryStandardBasis m).coord j (φ x) =
      ∑ i, (binaryStandardBasis m).coord i x * (binaryStandardBasis m).coord j
        (φ (binaryStandardBasis m i)) := by
    intro x
    conv_lhs => rw [← (binaryStandardBasis m).sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
  have h : Tendsto (fun t => ∑ i, (binaryStandardBasis m).coord i (v t) *
      (binaryStandardBasis m).coord j (φ (binaryStandardBasis m i))) l
      (𝓝 (∑ i, (binaryStandardBasis m).coord i a *
        (binaryStandardBasis m).coord j (φ (binaryStandardBasis m i)))) :=
    tendsto_finsetSum _ (fun i _ => (hv i).mul_const _)
  have e1 : (fun t => (binaryStandardBasis m).coord j (φ (v t))) = fun t =>
      ∑ i, (binaryStandardBasis m).coord i (v t) *
        (binaryStandardBasis m).coord j (φ (binaryStandardBasis m i)) :=
    funext fun t => key (v t)
  show Tendsto (fun t => (binaryStandardBasis m).coord j (φ (v t))) l
    (𝓝 ((binaryStandardBasis m).coord j (φ a)))
  rw [e1, key a]
  exact h

theorem unique [l.NeBot] {a' : V m} (h : CoordTendsto m l v a) (h' : CoordTendsto m l v a') :
    a = a' := by
  apply (binaryStandardBasis m).ext_elem
  intro i
  exact tendsto_nhds_unique (h i) (h' i)

theorem congr' (hvw : ∀ᶠ t in l, w t = v t) (hw : CoordTendsto m l w a) :
    CoordTendsto m l v a := fun j =>
  (hw j).congr' (hvw.mono fun t ht => by rw [ht])

theorem comp {β : Type*} {k : Filter β} {φ : β → α} (hv : CoordTendsto m l v a)
    (hφ : Tendsto φ k l) : CoordTendsto m k (fun t => v (φ t)) a :=
  fun j => (hv j).comp hφ

end CoordTendsto

variable (m : ℕ) (e : ℤ)

/-- If `c = Q t - ρ (P t)` eventually, and `P`, `Q` both converge to `a`, then `c = a - ρ a`. -/
theorem eq_sub_of_coordTendsto {c a : V m} {ρ : V m →ₗ[ℂ] V m} {P Q : ℝ → V m}
    (hP : CoordTendsto m atTop P a) (hQ : CoordTendsto m atTop Q a)
    (h : ∀ᶠ t in atTop, c = Q t - ρ (P t)) : c = a - ρ a := by
  have h1 : CoordTendsto m atTop (fun t => Q t - ρ (P t)) (a - ρ a) := hQ.sub (hP.linear ρ)
  have h2 : CoordTendsto m atTop (fun _ => c) (a - ρ a) :=
    CoordTendsto.congr' (h.mono fun t ht => ht.symm) h1
  have h3 : CoordTendsto m atTop (fun _ : ℝ => c) c := fun j => tendsto_const_nhds
  exact CoordTendsto.unique h3 h2

/-! ### The Eichler integral along `S` -/

/-- `P(S ζ) = ρ(S) Q(ζ)` for `Q` the Eichler integral of `f ∣ S`. -/
theorem primitive_sG_smul (f : S m) (ζ : ℍ) :
    primitive m ⇑f ((sG • ζ : ℍ) : ℂ) =
      Binary.homogeneousAction m e sC (primitive m (slashS m f) (ζ : ℂ)) := by
  have hf := form_holo f
  have hg := slashS_holo m f
  have hM : 0 < sG.val.det := by rw [sG_det]; exact one_pos
  have hprim := transform_isPrimitive m e hf sG hM
  rw [sG_det, Complex.ofReal_one, _root_.one_zpow, one_smul] at hprim
  have hslash : (⇑f ∣[(m : ℤ) + 2] sG) = slashS m f := rfl
  rw [hslash] at hprim
  have key := eq_primitive_add m hg _ hprim ζ ζ.im_pos
  have hI : ofComplex Complex.I = I := ofComplex_apply I
  simp only [ofComplex_apply, hI, S_smul_I, UpperHalfPlane.coe_I] at key
  have h0 : primitive m (⇑f) Complex.I = 0 := primitive_basepoint m ⇑f
  rw [h0, map_zero, add_zero] at key
  rw [complexify_sG] at key
  rw [← key, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- `P(i u) = ρ(S) Q(i / u)` for `u > 0`. -/
theorem primitive_imag_inv (f : S m) (u : ℝ) (hu : 0 < u) :
    primitive m ⇑f (Complex.I * (u : ℂ)) =
      Binary.homogeneousAction m e sC
        (primitive m (slashS m f) (Complex.I * ((u⁻¹ : ℝ) : ℂ))) := by
  have h := primitive_sG_smul m e f (iPt u⁻¹ (inv_pos.mpr hu))
  rw [sG_smul_iPt_inv u hu, iPt_coe, iPt_coe] at h
  exact h

/-! ### The cocycle at `T` and `L` along the imaginary axis -/

theorem cocycle_T_eq (f : S m) (t : ℝ) (ht : 0 < t) :
    (periodCocycle m e f).val coreT =
      periodPrimitive m f (Complex.I * (t : ℂ) + ((1 : ℝ) : ℂ)) -
        coreRep m e coreT (periodPrimitive m f (Complex.I * (t : ℂ))) := by
  rw [periodCocycle_primitive m e f coreT (iPt t ht), coreT_coe, iPt_coe, Complex.ofReal_one]

theorem cocycle_L_eq (f : S m) (t : ℝ) (ht : 0 < t) :
    (periodCocycle m e f).val coreL =
      Binary.homogeneousAction m e sC (primitive m (slashS m f) (Complex.I * (t : ℂ))) -
        coreRep m e coreL (Binary.homogeneousAction m e sC
          (primitive m (slashS m f) (Complex.I * (t : ℂ) + ((3 : ℝ) : ℂ)))) := by
  have hζ : (((3 : ℝ) +ᵥ iPt t ht : ℍ) : ℂ) = Complex.I * (t : ℂ) + ((3 : ℝ) : ℂ) := by
    rw [UpperHalfPlane.coe_vadd, iPt_coe, add_comm]
  rw [periodCocycle_primitive m e f coreL (sG • ((3 : ℝ) +ᵥ iPt t ht)),
    coreL_smul_sG_smul]
  simp only [periodPrimitive]
  rw [primitive_sG_smul m e f, primitive_sG_smul m e f, hζ, iPt_coe]

/-! ### Integrals -/

theorem integral_Ioi_zero_split {F : ℝ → ℂ} (h1 : IntegrableOn F (Set.Ioc 0 1))
    (h2 : IntegrableOn F (Set.Ioi 1)) :
    ∫ t : ℝ in Set.Ioi 0, F t =
      (∫ t : ℝ in Set.Ioc 0 1, F t) + ∫ t : ℝ in Set.Ioi 1, F t := by
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr (Set.mem_Ioi.mp hx'))
  rw [← hunion]
  exact setIntegral_union (s := Set.Ioc 0 1) (t := Set.Ioi 1) hdisj measurableSet_Ioi h1 h2

/-- The moments of a cusp form for `Γ₁(3)` of any weight are integrable. -/
theorem moment_integrable {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (p : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ p * f (ofComplex (Complex.I * (t : ℂ))))
      (Set.Ioi 0) := by
  have hf := CuspFormClass.holo f
  have h1 := integrableOn_Ioc_zero_one hf (exists_bound_near_zero f) p
  have h2 := integrableOn_Ioi_one hf (decay_form f) p
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact h1.union h2

/-! ### The boundary values -/

/-- **Boundary values of the period cocycle.** -/
theorem exists_boundary_values (m : ℕ) (e : ℤ) (f : S m) :
    ∃ a b : V m,
      (periodCocycle m e f).val coreT = a - coreRep m e coreT a ∧
      (periodCocycle m e f).val coreL = b - coreRep m e coreL b ∧
      ∀ j : Fin (m + 1), (binaryStandardBasis m).coord j (a - b) =
        ((m.choose j.val : ℕ) : ℂ) * (-Complex.I) ^ (m - j.val) * Complex.I *
          Moment.moment (⇑f) (m - j.val) := by
  have hf := form_holo f
  have hg := slashS_holo m f
  have hdf : ExpDecay ⇑f := decay_form f
  have hdg : ExpDecay (slashS m f) := decay_slashS f
  have hbd := exists_bound_near_zero f
  obtain ⟨a, ha⟩ := exists_tendsto_shift m hf hdf (primitive_isPrimitive m hf)
  obtain ⟨aS, haS⟩ := exists_tendsto_shift m hg hdg (primitive_isPrimitive m hg)
  have ha0 : CoordTendsto m atTop (fun t : ℝ => periodPrimitive m f (Complex.I * (t : ℂ))) a :=
    fun j => by
      have h := ha 0 j
      simp only [Complex.ofReal_zero, add_zero] at h
      exact h
  have ha1 : CoordTendsto m atTop
      (fun t : ℝ => periodPrimitive m f (Complex.I * (t : ℂ) + ((1 : ℝ) : ℂ))) a :=
    fun j => ha 1 j
  have haS0 : CoordTendsto m atTop
      (fun t : ℝ => primitive m (slashS m f) (Complex.I * (t : ℂ))) aS := fun j => by
    have h := haS 0 j
    simp only [Complex.ofReal_zero, add_zero] at h
    exact h
  have haS3 : CoordTendsto m atTop
      (fun t : ℝ => primitive m (slashS m f) (Complex.I * (t : ℂ) + ((3 : ℝ) : ℂ))) aS :=
    fun j => haS 3 j
  have hT : (periodCocycle m e f).val coreT = a - coreRep m e coreT a :=
    eq_sub_of_coordTendsto m (ρ := coreRep m e coreT) ha0 ha1
      ((eventually_gt_atTop (0 : ℝ)).mono fun t ht => cocycle_T_eq m e f t ht)
  have hL : (periodCocycle m e f).val coreL = Binary.homogeneousAction m e sC aS -
      coreRep m e coreL (Binary.homogeneousAction m e sC aS) :=
    eq_sub_of_coordTendsto m (ρ := coreRep m e coreL)
      (haS3.linear (Binary.homogeneousAction m e sC)) (haS0.linear (Binary.homogeneousAction m e sC))
      ((eventually_gt_atTop (0 : ℝ)).mono fun t ht => cocycle_L_eq m e f t ht)
  have hb0 : CoordTendsto m (𝓝[>] (0 : ℝ))
      (fun u : ℝ => periodPrimitive m f (Complex.I * (u : ℂ)))
      (Binary.homogeneousAction m e sC aS) := by
    have h1 : CoordTendsto m (𝓝[>] (0 : ℝ))
        (fun u : ℝ => Binary.homogeneousAction m e sC
          (primitive m (slashS m f) (Complex.I * ((u⁻¹ : ℝ) : ℂ))))
        (Binary.homogeneousAction m e sC aS) :=
      (haS0.comp tendsto_inv_nhdsGT_zero).linear (Binary.homogeneousAction m e sC)
    refine CoordTendsto.congr' ?_ h1
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (primitive_imag_inv m e f u (Set.mem_Ioi.mp hu)).symm
  refine ⟨a, Binary.homogeneousAction m e sC aS, hT, hL, fun j => ?_⟩
  have hA := coord_eq_integral_Ioi m hf hdf (primitive_isPrimitive m hf)
    (primitive_basepoint m ⇑f) j (ha0 j)
  have hB := coord_eq_integral_Ioc m hf hbd (primitive_isPrimitive m hf)
    (primitive_basepoint m ⇑f) j (hb0 j)
  rw [map_sub, hA, hB]
  unfold Moment.moment
  rw [integral_Ioi_zero_split (integrableOn_Ioc_zero_one hf hbd (m - j.val))
    (integrableOn_Ioi_one hf hdf (m - j.val))]
  ring

end TernaryPeriodPolynomials.LevelThreeInjective.BoundaryValues
