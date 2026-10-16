module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitZp2G
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBoundG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.SeedCp
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.CyclicAdelic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibre
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitSet
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.FibreSum

@[expose] public section


/-!
# The literal shell value and the total at a general base point `g_f`

Formalized by Claude Haiku 5.5.

Generalises `ShellLiteral` (base point `g_f = 1`) to an arbitrary finite base point `g_f`, with
`gf.val.map (finiteEvaluation v) = gp.val` and `IntGL v gp.val` as explicit hypotheses.

Route. Put `Y = g_f · ι_v(gp)⁻¹`, which is the identity at `v` (`trivial_at_v`). Then:
* the literal shell value is `normPower(det g_f) · p^{-s k/2} · ∑_t w_t · vhValueFull(ι_v B_t · Y)`
  (`shellValLitG_seed`, from the fibre decomposition and fibre constancy);
* `ι_v B_t · Y = Y · ι_v B_t` (`ιGL_comm_of_trivial`), so the sum is a lattice sum at base `Y`;
* the cyclic Hecke identity holds at every `gf` (`eq_cyclic_hecke`), giving
  `∑_t vhValue(Y · ι_v B_t) = c_r · vhValue(Y)` (`H1_cyc_at`);
* equal share per cyclic lattice (`fibreWeight_eq_share`) and the algebra of `ShellBundle` then give
  the per-shell identity (`shellValLitG_perShell`), and the summed identity (`shell_total_literalG`).

The integral over `ℤ_p²` is `normPower(det g_f) · vhValueFull(g_f · ι_v gp⁻¹)` by
`ShellLitZp2G.integral_zp2_literal_G`.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (cuspScalarWeightedLinear finitePadicMeasure HasPrimeHeckeRelations)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (IntGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg (vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue (intMat)
open TernaryPeriodPolynomials.Argument.LatticeCounts (cyclicHNF hnfData card_cyclicHNF)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG
  (shellIntegrandG shellIntegrandG_fibre trivial_at_v ιGL_comm_of_trivial)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitZp2G (integral_zp2_literal_G)
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLiteralG

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- `vhValueFull` equals `vhValue` when `det g∞ > 0`. -/
theorem vhValueFull_eq_of_pos (k : ℤ) (h : CuspForm levelOne k) (gInf : BinaryRealGL)
    (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val) (X : BinaryFiniteGL) :
    vhValueFull k h gInf X = vhValue k h gInf X := by
  unfold vhValueFull
  rw [ite_eq_left hg]

/-- The literal shell value at a general base point `g_f`: the integral of the literal integrand over
`pairShell p s` with respect to the finite-place product Haar measure. -/
def shellValLitG (v : FinitePlace) (I : EichlerInput σ n) (gf : BinaryFiniteGL)
    (gInf : BinaryRealGL) (s : ℕ) : ℂ :=
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  ∫ z in Padic.pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s,
    shellIntegrandG v I gf gInf z
    ∂((finitePadicMeasure v).prod (finitePadicMeasure v))

/-- **Seed identity at a general base point (`s ≥ 1`).** The shell value is the fibre sum of the
literal integrand: the constant on each cyclic fibre `t` is `p^{-s k/2} · normPower(det g_f) ·
vhValueFull k h g∞ (ι_v B_t · Y)`, with `Y = g_f · ι_v gp⁻¹`, weighted by the fibre measure. -/
theorem shellValLitG_seed (v : FinitePlace) (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val)
    {s : ℕ} (hs : 1 ≤ s) :
    shellValLitG v I gf gInf s =
      ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        ∑ t ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s,
          ((ShellBundle.fibreWeight v s t : ℝ) : ℂ) *
            vhValueFull (-2 * I.halfWeight) h gInf
              (ιGL v (ShellLitFibre.shellB v t) * (gf * ιGL v gp⁻¹)) := by
  have : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  have key := ShellFibreSum.fibre_sum_integral
    ((finitePadicMeasure v).prod (finitePadicMeasure v))
    (T := cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s)
    (F := fun t => ShellLitSet.shellFibre (Rat.HeightOneSpectrum.primesEquiv v).val s t)
    (c := fun t => ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf
          (ιGL v (ShellLitFibre.shellB v t) * (gf * ιGL v gp⁻¹)))
    (f := shellIntegrandG v I gf gInf)
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
      exact shellIntegrandG_fibre v I h hform gInf hg gf gp hgp hgI ht hz.1 hzt
        (ShellLitFibre.shellB v t)
        (fun i j => ShellLitFibre.shellB_entry v (ShellLitSet.mem_hnfData_of_cyclic ht) i j))
  dsimp only [shellValLitG]
  rw [key.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hw : ShellBundle.fibreWeight v s t =
      ((finitePadicMeasure v).prod (finitePadicMeasure v)).real
        (ShellLitSet.shellFibre (Rat.HeightOneSpectrum.primesEquiv v).val s t) := rfl
  rw [hw, Complex.real_smul]
  ring

/-- **`eq:cyclic-hecke` at a general base point, in `vhValue` form over the cyclic triples.** The
sum over the cyclic Hermite lifts of `v_h(g_∞, g_f · ι_v B_t)` equals
`p^{r(1-k/2)} {a_h(p^r) - p^{k-2} a_h(p^{r-2})} · v_h(g_∞, g_f)`. It is the base-one statement
`ShellLitBound`-side `H1_cyc` with `1` replaced by `g_f`, from `eq_cyclic_hecke`. -/
theorem H1_cyc_at (k : ℤ) (h : CuspForm levelOne k) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k h eigenvalues)
    (normalized : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1) (p : Nat.Primes) (r : ℕ)
    (v : FinitePlace) (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData (p.val ^ r), (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ))
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) :
    ∑ t ∈ cyclicHNF p.val r, vhValue k h gInf (gf * ιGL v (B t)) =
      ((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
        ((UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r) -
          (p.val : ℂ) ^ (k - 2) *
            (if 2 ≤ r then (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ (r - 2)) else 0)) *
        vhValue k h gInf gf := by
  have key := LatticeCyclicAdelic.eq_cyclic_hecke k h eigenvalues relations
    normalized p r v hv B hB gInf hgInf gf
  refine (Finset.sum_coe_sort (cyclicHNF p.val r)
    (fun t => vhValue k h gInf (gf * ιGL v (B t)))).symm.trans ?_
  exact key

/-- The fibre sum with the fibre weights is the shell share times the plain sum (`fibreWeight_eq_share`). -/
theorem fibre_share_sum (v : FinitePlace) (p : Nat.Primes)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val) {s : ℕ} (hs : 1 ≤ s)
    (F : ℕ × ℕ × ℕ → ℂ) :
    ∑ t ∈ cyclicHNF p.val s, ((ShellBundle.fibreWeight v s t : ℝ) : ℂ) * F t =
      ((ShellBundle.shellHaarMeasure v s / ((cyclicHNF p.val s).card : ℝ) : ℝ) : ℂ) *
        ∑ t ∈ cyclicHNF p.val s, F t := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t ht => by
    rw [ShellBundle.fibreWeight_eq_share v p hv hs ht]

/-- The real identity with complex constants: the shell factor times the cyclic Hecke sum equals the
per-shell term `v · (1 - p⁻¹) p^{-s(k-2)} · Z`, for `s ≥ 1` (`ShellBundle.shell_real_identity`). -/
theorem shell_alg_core (p : Nat.Primes) (k : ℤ) {s : ℕ} (hs : 1 ≤ s) (Z V : ℂ) :
    ((((p.val : ℝ) ^ (-(s : ℝ) * ((k : ℝ) / 2)) : ℝ) : ℂ)) *
      ((((p.val ^ (2 * s) - p.val ^ (2 * s - 2) : ℕ) : ℝ) /
        ((p.val ^ s + p.val ^ (s - 1) : ℕ) : ℝ) : ℝ) : ℂ) *
      ((((p.val ^ s : ℕ) : ℂ)) ^ (1 - (k : ℂ) / 2) * Z) * V =
    V * ((1 - ((p.val : ℕ) : ℂ)⁻¹) * ((p.val : ℕ) : ℂ) ^ (-((s : ℤ) * (k - 2))) * Z) := by
  have : Fact p.val.Prime := ⟨p.property⟩
  have hx : (1 : ℝ) < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  have hx0 : (0 : ℝ) < (p.val : ℝ) := by linarith
  have hM : ((p.val ^ (2 * s) - p.val ^ (2 * s - 2) : ℕ) : ℝ) =
      (p.val : ℝ) ^ (2 * s) - (p.val : ℝ) ^ (2 * s - 2) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right p.property.pos (by omega))]
    push_cast
    ring
  have hC : ((p.val ^ s + p.val ^ (s - 1) : ℕ) : ℝ) =
      (p.val : ℝ) ^ s + (p.val : ℝ) ^ (s - 1) := by
    push_cast
    ring
  have main : (((p.val ^ (2 * s) - p.val ^ (2 * s - 2) : ℕ) : ℝ) /
      ((p.val ^ s + p.val ^ (s - 1) : ℕ) : ℝ)) *
      (p.val : ℝ) ^ (-(s : ℝ) * ((k : ℝ) / 2)) * ((p.val : ℝ) ^ s) ^ (1 - (k : ℝ) / 2) =
      (1 - (p.val : ℝ)⁻¹) * (p.val : ℝ) ^ (-(s : ℝ) * ((k : ℝ) - 2)) := by
    rw [hM, hC]
    exact ShellBundle.shell_real_identity (p.val : ℝ) hx k s hs
  have hR : ((p.val ^ s : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) =
      ((((p.val : ℝ) ^ s) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((p.val ^ s : ℕ) : ℂ) = (((p.val : ℝ) ^ s : ℝ) : ℂ) by push_cast; ring]
    exact ShellBundle.cpow_shell_eq_real (p.val : ℝ) hx0.le s k
  have hz : ((p.val : ℕ) : ℂ) ^ (-((s : ℤ) * (k - 2))) =
      (((p.val : ℝ) ^ (-(s : ℝ) * ((k : ℝ) - 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ShellBundle.zpow_shell_eq_real]
  have hone : (1 - ((p.val : ℕ) : ℂ)⁻¹) = (((1 - (p.val : ℝ)⁻¹) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hR, hz, hone]
  have hk := congrArg (fun r : ℝ => (r : ℂ)) main
  simp only [Complex.ofReal_mul] at hk
  linear_combination (Z * V) * hk

/-- **The literal shell value at a general base point, per shell (`s ≥ 1`).** The shell value is
`normPower(det g_f) · v_h(g∞, Y) · (1-p⁻¹) p^{-s(k-2)} (a_h(p^s) - p^{k-2} a_h(p^{s-2}))`, with
`Y = g_f · ι_v gp⁻¹`. The sum over the cyclic triples is `H1_cyc_at` at base `Y`. -/
theorem shellValLitG_perShell (v : FinitePlace) (p : Nat.Primes)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val)
    {s : ℕ} (hs : 1 ≤ s) :
    shellValLitG v I gf gInf s =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf (gf * ιGL v gp⁻¹) *
      ((1 - ((p.val : ℕ) : ℂ)⁻¹) * ((p.val : ℕ) : ℂ) ^ (-((s : ℤ) * (-2 * I.halfWeight - 2))) *
        (fourierCoeff h (p.val ^ s) -
          ((p.val : ℕ) : ℂ) ^ (-2 * I.halfWeight - 2) *
            (if 2 ≤ s then fourierCoeff h (p.val ^ (s - 2)) else 0))) := by
  obtain ⟨hnorm, eig, rel⟩ := hh
  have hfc : ∀ m : ℕ, fourierCoeff h m = (UpperHalfPlane.qExpansion 1 h).coeff m := by
    intro m
    unfold fourierCoeff
    simp only [Subgroup.strictWidthInfty_SL2Z]
  have hB : ∀ t ∈ hnfData (p.val ^ s),
      (ShellLitFibre.shellB v t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ) := by
    intro t ht
    rw [← hv] at ht
    exact ShellLitFibre.shellB_val v ht
  have hY := trivial_at_v v gf gp hgp
  have hval : ∀ t, vhValueFull (-2 * I.halfWeight) h gInf
      (ιGL v (ShellLitFibre.shellB v t) * (gf * ιGL v gp⁻¹)) =
      vhValue (-2 * I.halfWeight) h gInf
        ((gf * ιGL v gp⁻¹) * ιGL v (ShellLitFibre.shellB v t)) := by
    intro t
    rw [ιGL_comm_of_trivial v _ _ hY]
    exact vhValueFull_eq_of_pos _ h gInf hg _
  have hH := H1_cyc_at (-2 * I.halfWeight) h eig rel (by rw [← hfc]; exact hnorm) p s v hv
    (ShellLitFibre.shellB v) hB gInf hg (gf * ιGL v gp⁻¹)
  simp only [← hfc] at hH
  rw [shellValLitG_seed v I h hform gInf hg gf gp hgp hgI hs, hv]
  simp only [hval]
  rw [fibre_share_sum v p hv hs, hH, ShellBundle.shellHaarMeasure_eq v hs, hv,
    card_cyclicHNF hs, vhValueFull_eq_of_pos _ h gInf hg]
  have core := shell_alg_core p (-2 * I.halfWeight) hs
    (fourierCoeff h (p.val ^ s) -
      ((p.val : ℕ) : ℂ) ^ (-2 * I.halfWeight - 2) *
        (if 2 ≤ s then fourierCoeff h (p.val ^ (s - 2)) else 0))
    (vhValue (-2 * I.halfWeight) h gInf (gf * ιGL v gp⁻¹))
  linear_combination (normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
    (((-2 * I.halfWeight : ℤ) : ℂ) / 2)) * core

/-- **The literal shell total at a general base point (`6 < k`).** The integral over `ℤ_p²` plus
the literal shells `s = r + 1` is `normPower(det g_f) · v_h(g∞, g_f · ι_v gp⁻¹) · c_p`, where `c_p`
is the right-hand side of the `unramified_local_factor`. The shells are summable. -/
theorem shell_total_literalG (I : EichlerInput σ n) (k : ℤ) (hk_eq : k = -2 * I.halfWeight)
    (hk : 6 < k) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : Nat.Primes) (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val) :
    Summable (fun r : ℕ => shellValLitG v I gf gInf (r + 1)) ∧
    (∫ z in Padic.Zp2 (Rat.HeightOneSpectrum.primesEquiv v).val,
        shellIntegrandG v I gf gInf z
        ∂((finitePadicMeasure v).prod (finitePadicMeasure v))) +
      ∑' r : ℕ, shellValLitG v I gf gInf (r + 1) =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf)) (((k : ℤ) : ℂ) / 2) *
        vhValueFull k h gInf (gf * ιGL v gp⁻¹) *
      (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) + ((p : ℕ) : ℂ) ^ (1 - k)) /
        (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k)) := by
  subst hk_eq
  obtain ⟨hsum, hcp⟩ := TernaryPeriodPolynomials.unramified_local_factor hk h hh p
  have hterm : ∀ r : ℕ, shellValLitG v I gf gInf (r + 1) =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf (gf * ιGL v gp⁻¹) *
      ((1 - ((p.val : ℕ) : ℂ)⁻¹) *
        (((p.val : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (-2 * I.halfWeight - 2))) *
          (fourierCoeff h (p.val ^ (r + 1)) -
            ((p.val : ℕ) : ℂ) ^ (-2 * I.halfWeight - 2) *
              (if r = 0 then 0 else fourierCoeff h (p.val ^ (r - 1)))))) := by
    intro r
    rw [shellValLitG_perShell v p hv I h hh hform gInf hg gf gp hgp hgI (s := r + 1) (by omega)]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [ite_eq_right (show ¬ (2 ≤ 0 + 1) by norm_num), ite_eq_left rfl]
      simp only [Nat.cast_zero, Nat.cast_one, zero_add, mul_zero, sub_zero, mul_assoc]
    · rw [ite_eq_left (show 2 ≤ r + 1 by omega), ite_eq_right (show r ≠ 0 by omega),
        show r + 1 - 2 = r - 1 by omega]
      push_cast
      ring
  have hsum' : Summable (fun r : ℕ => shellValLitG v I gf gInf (r + 1)) := by
    refine (hsum.mul_left (normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
      (((-2 * I.halfWeight : ℤ) : ℂ) / 2) * vhValueFull (-2 * I.halfWeight) h gInf
        (gf * ιGL v gp⁻¹) * (1 - ((p.val : ℕ) : ℂ)⁻¹))).congr fun r => ?_
    rw [hterm r]
    ring
  have hsumT : ∑' r : ℕ, shellValLitG v I gf gInf (r + 1) =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf (gf * ιGL v gp⁻¹) *
      ((1 - ((p.val : ℕ) : ℂ)⁻¹) * ∑' r : ℕ,
        ((p.val : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (-2 * I.halfWeight - 2))) *
          (fourierCoeff h (p.val ^ (r + 1)) -
            ((p.val : ℕ) : ℂ) ^ (-2 * I.halfWeight - 2) *
              (if r = 0 then 0 else fourierCoeff h (p.val ^ (r - 1))))) := by
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_mul_left]
  refine ⟨hsum', ?_⟩
  rw [integral_zp2_literal_G v I h hform gInf gf gp hgp hgI, hsumT]
  linear_combination (normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
    (((-2 * I.halfWeight : ℤ) : ℂ) / 2) * vhValueFull (-2 * I.halfWeight) h gInf
      (gf * ιGL v gp⁻¹)) * hcp

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLiteralG

end
