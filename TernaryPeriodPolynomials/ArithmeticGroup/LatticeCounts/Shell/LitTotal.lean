module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Literal
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitZp2

@[expose] public section


/-!
# The whole literal local integral over `ℚ_p²` (`0 < det g∞`), conditional on absolute summability

Formalized by Claude Haiku 5.5.

`ℚ_p² = ℤ_p² ⊔ ⋃_{r ≥ 1} pairShell p r` (`zp2_or_shell`, `shell_pairwise_disjoint`,
`zp2_disjoint_shell`). On each shell the literal integrand is integrable (fibre decomposition).
`local_integral_literal` assembles the integral over `ℚ_p²` as the `ℤ_p²` term plus the shell
values, and identifies the sum with `vhValue · c_p`.

The integrability over `ℚ_p²` is CONDITIONAL on the hypothesis `habs`: summability of the shell
integrals of the norm. That summability is not in the library (it needs a bound on the cusp form
values at the cyclic Hermite points). The conclusion is therefore not an unconditional integral
identity; it is the exact reduction to `habs`.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (cuspScalarWeightedLinear finitePadicMeasure finitePadicMeasure_normalized)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotal

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- A `ℚ_p` element of norm above one has norm `p^(r+1)` for some `r`. -/
theorem norm_eq_pow_succ {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : 1 < ‖x‖) :
    ∃ r : ℕ, ‖x‖ = (p : ℝ) ^ (r + 1) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  rw [Padic.norm_eq_zpow_neg_valuation hx0] at hx ⊢
  generalize -x.valuation = e at hx ⊢
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have he1 : 1 ≤ e := by
    by_contra hc
    have := zpow_le_one_of_nonpos₀ hp1.le (by omega : e ≤ 0)
    linarith
  refine ⟨(e - 1).toNat, ?_⟩
  have hexp : (((e - 1).toNat + 1 : ℕ) : ℤ) = e := by omega
  rw [← zpow_natCast, hexp]

/-- Every point of `ℚ_p²` lies in `ℤ_p²` or in a shell `pairShell p (r+1)`. -/
theorem zp2_or_shell {p : ℕ} [Fact p.Prime] (z : ℚ_[p] × ℚ_[p]) :
    z ∈ Padic.Zp2 p ∨ ∃ r : ℕ, z ∈ Padic.pairShell p (r + 1) := by
  by_cases hz : z ∈ Padic.Zp2 p
  · exact Or.inl hz
  right
  have hmax : 1 < max ‖z.1‖ ‖z.2‖ := by
    by_contra hc
    have hc' : max ‖z.1‖ ‖z.2‖ ≤ 1 := not_lt.1 hc
    exact hz ⟨le_trans (le_max_left _ _) hc', le_trans (le_max_right _ _) hc'⟩
  rcases max_choice ‖z.1‖ ‖z.2‖ with hm | hm
  · obtain ⟨r, hr⟩ := norm_eq_pow_succ (x := z.1) (by rw [← hm]; exact hmax)
    exact ⟨r, by show max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ (r + 1); rw [hm, hr]⟩
  · obtain ⟨r, hr⟩ := norm_eq_pow_succ (x := z.2) (by rw [← hm]; exact hmax)
    exact ⟨r, by show max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ (r + 1); rw [hm, hr]⟩

/-- The shells `pairShell p (r+1)` are pairwise disjoint. -/
theorem shell_pairwise_disjoint {p : ℕ} [Fact p.Prime] :
    Pairwise (Function.onFun Disjoint fun r : ℕ => Padic.pairShell p (r + 1)) := by
  intro r r' hrr'
  refine Set.disjoint_left.2 fun z hz hz' => hrr' ?_
  have hz2 : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ (r + 1) := hz
  have hz2' : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ (r' + 1) := hz'
  have e : (p : ℝ) ^ (r + 1) = (p : ℝ) ^ (r' + 1) := hz2.symm.trans hz2'
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : p.Prime).one_lt.ne'
  have := pow_right_injective₀ hp hp1 e
  omega

/-- `ℤ_p²` is disjoint from every shell `pairShell p (r+1)`, `r ≥ 0`. -/
theorem zp2_disjoint_shell {p : ℕ} [Fact p.Prime] (r : ℕ) :
    Disjoint (Padic.Zp2 p) (Padic.pairShell p (r + 1)) := by
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  have hz2 : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ (r + 1) := hz'
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h1 : (1 : ℝ) < (p : ℝ) ^ (r + 1) := one_lt_pow₀ hp1 (Nat.succ_ne_zero r)
  have hle : max ‖z.1‖ ‖z.2‖ ≤ 1 := max_le hz.1 hz.2
  linarith

/-- On each shell the literal integrand is integrable (finite union of cyclic fibres on which
it is constant). -/
theorem shell_integrableOn (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    {s : ℕ} (hs : 1 ≤ s) :
    IntegrableOn (ShellLitFibre.shellIntegrand v I gInf)
      (Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s)
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
  have key := ShellFibreSum.fibre_sum_integral
    ((finitePadicMeasure v).prod (finitePadicMeasure v))
    (T := cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s)
    (F := fun t => ShellLitSet.shellFibre (Rat.HeightOneSpectrum.primesEquiv v).val s t)
    (c := fun t => ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        vhValue (-2 * I.halfWeight) h gInf (ιGL v (ShellLitFibre.shellB v t)))
    (f := ShellLitFibre.shellIntegrand v I gInf)
    (ShellLitSet.isOpen_pairShell hs).measurableSet
    (fun t _ => (ShellLitSet.isOpen_shellFibre hs t).measurableSet)
    (fun t _ => ShellLitSet.shellFibre_sub t)
    (fun i hi j hj hij => Set.disjoint_left.2 fun z hzi hzj =>
      hij (ShellLitSet.shellFibre_unique hi hj hzi hzj))
    (fun z hz => by
      obtain ⟨t, ht, hzt⟩ := ShellLitSet.exists_shellFibre hz
      exact Set.mem_iUnion₂.2 ⟨t, ht, hzt⟩)
    (fun t ht => by
      have hm : (finitePadicMeasure v).prod (finitePadicMeasure v)
          (ShellLitSet.shellFibre (Rat.HeightOneSpectrum.primesEquiv v).val s t) =
          ((((Rat.HeightOneSpectrum.primesEquiv v).val ^ s -
            (Rat.HeightOneSpectrum.primesEquiv v).val ^ (s - 1) : ℕ)) : ENNReal) :=
        Padic.hermLat_fibre_measure_finitePlace v hs ht
      rw [hm]
      exact ENNReal.natCast_ne_top _)
    (fun t ht z hz => by
      have hzt : Padic.pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z =
          Padic.hermLat (Rat.HeightOneSpectrum.primesEquiv v).val t :=
        (Submodule.toAddSubgroup_inj _ _).1 hz.2
      exact ShellLitFibre.shellIntegrand_fibre v I h hform gInf hg ht hz.1 hzt
        (ShellLitFibre.shellB v t)
        (fun i j => ShellLitFibre.shellB_entry v (ShellLitSet.mem_hnfData_of_cyclic ht) i j))
  exact key.1

/-- **The whole literal local integral over `ℚ_p²` (`0 < det g∞`), conditional on `habs`.**
If the shell integrals of the norm are summable (`habs`, not proved here), the integrand is
integrable on `ℚ_p²` and its integral is `vhValue · c_p`, the `ℤ_p²` term plus the shell sum.
The hypothesis `6 < k` is explicit, with `k = -2·halfWeight`. -/
theorem local_integral_literal (I : EichlerInput σ n) (k : ℤ) (hk_eq : k = -2 * I.halfWeight)
    (hk : 6 < k) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (habs : Summable (fun r : ℕ => ∫ z in Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1),
      ‖ShellLitFibre.shellIntegrand v I gInf z‖ ∂((finitePadicMeasure v).prod (finitePadicMeasure v)))) :
    IntegrableOn (ShellLitFibre.shellIntegrand v I gInf) Set.univ
        ((finitePadicMeasure v).prod (finitePadicMeasure v)) ∧
      ∫ z, ShellLitFibre.shellIntegrand v I gInf z ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) =
        vhValue k h gInf 1 * ((1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) +
          ((p : ℕ) : ℂ) ^ (1 - k)) /
          (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k))) := by
  subst hk_eq
  obtain ⟨-, heq⟩ := ShellLiteral.shell_total_literal I (-2 * I.halfWeight) rfl hk h hh hform p v hv
    gInf hgInf
  have hZ := ShellLitZp2.integral_zp2_literal v I h hform gInf hgInf
  have hmeasZ : MeasurableSet (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) :=
    (ShellLitSet.isOpen_zp2 (p := (Rat.HeightOneSpectrum.primesEquiv v).val)).measurableSet
  have hmeasS : ∀ r : ℕ, MeasurableSet
      (Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1)) :=
    fun r => (ShellLitSet.isOpen_pairShell (by omega : 1 ≤ r + 1)).measurableSet
  have hi : ∀ r : ℕ, IntegrableOn (ShellLitFibre.shellIntegrand v I gInf)
      (Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1))
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
    fun r => shell_integrableOn v I h hform gInf hgInf (by omega : 1 ≤ r + 1)
  have hU : IntegrableOn (ShellLitFibre.shellIntegrand v I gInf)
      (⋃ r : ℕ, Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1))
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
    integrableOn_iUnion_of_summable_integral_norm hi habs
  have hfin : ((finitePadicMeasure v).prod (finitePadicMeasure v))
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val) ≠ ⊤ := by
    have hnorm := finitePadicMeasure_normalized v
    rw [show Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val =
        {value | ‖value‖ ≤ 1} ×ˢ {value | ‖value‖ ≤ 1} from rfl,
      Measure.prod_prod, hnorm, one_mul]
    exact ENNReal.one_ne_top
  have hZi : IntegrableOn (ShellLitFibre.shellIntegrand v I gInf)
      (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val)
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) :=
    (integrableOn_const (C := vhValue (-2 * I.halfWeight) h gInf 1) hfin).congr_fun
      (fun z hz => (ShellLitZp2.shellIntegrand_zp2 v I h hform gInf hgInf hz).symm) hmeasZ
  have hcov : (Set.univ : Set (ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) =
      Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val ∪
        ⋃ r : ℕ, Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1) := by
    ext z
    simp only [Set.mem_univ, Set.mem_union, Set.mem_iUnion, true_iff]
    exact zp2_or_shell z
  have hint : IntegrableOn (ShellLitFibre.shellIntegrand v I gInf) Set.univ
      ((finitePadicMeasure v).prod (finitePadicMeasure v)) := by
    rw [hcov]
    exact hZi.union hU
  refine ⟨hint, ?_⟩
  have hdisj : Disjoint (Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val)
      (⋃ r : ℕ, Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val (r + 1)) :=
    Set.disjoint_iUnion_right.2 fun r => zp2_disjoint_shell r
  rw [← setIntegral_univ, hcov, setIntegral_union hdisj (MeasurableSet.iUnion hmeasS) hZi hU,
    integral_iUnion hmeasS shell_pairwise_disjoint hU, hZ]
  exact heq

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotal

end
