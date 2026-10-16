module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCoordinate

@[expose] public section


/-!
# The binary coordinate of the good-line edge under the local Hecke operator

Lower-radical cocycles are exponentials of their infinitesimal pairs:
`ξ(y) = avg(N(y)) (y₁ a₀ + y₂ a₁)` (`cocycle_exp`). Rational Levi elements conjugate `N(y)` to
`N(y M⁻¹)` (`avg_levi`), and `σ = diag(1, 1, εp)` scales it by `εp` (`avg_sigma`). Consequently the
Levi translate of an exponential is the exponential of the Levi pair (`levi_exp`), and the
corestriction over the radical representatives multiplies the class by `p²` after rescaling by `σ`
(`cor_exp`). On the binary coordinate this gives the cocycle-level Hecke formula
`E(Tc)(m) = E(c)(m) + ∑_j ρ(B_j) E(c)(μ_j)` (`binaryEdgeL_hecke`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.GoodLineCoordinate

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets LineCoordinates GoodLineCosets GoodLineEdge
open IdentityPlaneCoordinate

attribute [local instance] complexEndRationalAlgebra

variable (n : ℕ)

/-! ### The lower-radical generators -/

/-- `N(w) = w₀ N₀ + w₁ N₁`. -/
def NC (w : Fin 2 → ℂ) : Module.End ℂ (HomogeneousPoly n) :=
  w 0 • lowerRadicalGenerator n 0 + w 1 • lowerRadicalGenerator n 1

/-- The Levi action `A_M = ρ(diag(M, 1))`. -/
abbrev AL (M : Binary.GL2) : Module.End ℂ (HomogeneousPoly n) :=
  homogeneousAction n (-1) (planeLevi M 1)

/-- Row vector times complex matrix. -/
def rowMul (w : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → ℂ :=
  fun k => w 0 * M 0 k + w 1 * M 1 k

theorem NC_comp_levi (M : Binary.GL2) (w : Fin 2 → ℂ) :
    (NC n w).comp (AL n M) = (AL n M).comp (NC n (rowMul w M.val)) := by
  have h0 := lowerRadicalGenerator_levi n M 0
  have h1 := lowerRadicalGenerator_levi n M 1
  apply LinearMap.ext
  intro v
  have e0 := LinearMap.congr_fun h0 v
  have e1 := LinearMap.congr_fun h1 v
  simp only [LinearMap.comp_apply] at e0 e1
  simp only [NC, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, e0, e1, rowMul,
    map_add, map_smul, add_smul, mul_smul, smul_add]
  abel

theorem NC_nilpotent (w : Fin 2 → ℂ) : NC n w ^ (2 * n + 1) = 0 := by
  rw [NC]
  have hc : Commute (w 0 • lowerRadicalGenerator n 0) (w 1 • lowerRadicalGenerator n 1) :=
    ((lowerRadicalGenerators_commute n).smul_left _).smul_right _
  rw [hc.add_pow, Finset.sum_eq_zero]
  intro i hi
  rw [Finset.mem_range] at hi
  by_cases h : n + 1 ≤ i
  · simp only [smul_pow, pow_eq_zero_of_le h (lowerRadicalGenerator_power_zero n 0), smul_zero,
      zero_mul]
  · have h' : n + 1 ≤ 2 * n + 1 - i := by omega
    simp only [smul_pow, pow_eq_zero_of_le h' (lowerRadicalGenerator_power_zero n 1), smul_zero,
      mul_zero, zero_mul]

/-- The exponential average `avg(N(w))` with the uniform cutoff. -/
abbrev avgC (w : Fin 2 → ℂ) : Module.End ℂ (HomogeneousPoly n) :=
  nilpotentExponentialAverage (NC n w) (2 * n + 1)

theorem avg_levi (M : Binary.GL2) (w : Fin 2 → ℂ) (v : HomogeneousPoly n) :
    avgC n w (AL n M v) = AL n M (avgC n (rowMul w M.val) v) :=
  nilpotentAverage_intertwines (NC n (rowMul w M.val)) (NC n w) (AL n M) (NC_comp_levi n M w) _ v

theorem average_cutoff (N : Module.End ℂ (HomogeneousPoly n)) (k k' : ℕ) (hN : N ^ k = 0)
    (hk : k ≤ k') : nilpotentExponentialAverage N k = nilpotentExponentialAverage N k' := by
  unfold nilpotentExponentialAverage
  rw [← Finset.sum_range_add_sum_Ico _ hk]
  rw [Finset.sum_eq_zero (s := Finset.Ico k k'), add_zero]
  intro i hi
  rw [Finset.mem_Ico] at hi
  rw [show i = (i - k) + k by omega, pow_add, hN, mul_zero]
  refine (Algebra.smul_def (R := ℚ) (A := Module.End ℂ (HomogeneousPoly n)) _ _).trans ?_
  exact mul_zero _

/-! ### The scaling `σ = diag(1, 1, d)` -/

/-- `ρ(diag(1,1,d))`. -/
abbrev AS (d : ℂˣ) : Module.End ℂ (HomogeneousPoly n) :=
  homogeneousAction n (-1) (planeLevi (1 : Binary.GL2) d)

theorem linearForm_sigma (d : ℂ) (i : Fin 2) :
    linearForm (planeBlock (1 : Matrix (Fin 2) (Fin 2) ℂ) d) i.castSucc = X i.castSucc := by
  fin_cases i <;> simp [linearForm, planeBlock, Fin.sum_univ_three]

theorem lower_sigma (d : ℂˣ) (i : Fin 2) (v : HomogeneousPoly n) :
    lowerRadicalGenerator n i (AS n d v) = ((d⁻¹ : ℂˣ) : ℂ) • AS n d (lowerRadicalGenerator n i v) := by
  apply Subtype.ext
  change (-3 : ℂ) • (X i.castSucc * pderiv 2 (action (-1) (planeLevi 1 d) v.val)) =
    ((d⁻¹ : ℂˣ) : ℂ) • action (-1) (planeLevi 1 d) ((-3 : ℂ) • (X i.castSucc * pderiv 2 v.val))
  rw [action_apply, action_apply, planeLevi_inverse, planeLevi_value, inv_one, Derivation.map_smul,
    map_smul, map_mul, substitute_X, Units.val_one, pderiv_substitute_planeBlock_third,
    linearForm_sigma]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring

theorem NC_comp_sigma (d : ℂˣ) (w : Fin 2 → ℂ) :
    (NC n w).comp (AS n d) = (AS n d).comp (NC n (((d⁻¹ : ℂˣ) : ℂ) • w)) := by
  apply LinearMap.ext
  intro v
  simp only [NC, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, lower_sigma,
    map_add, map_smul, smul_smul, Pi.smul_apply, smul_eq_mul]
  congr 1 <;> ring_nf

theorem avg_sigma (d : ℂˣ) (w : Fin 2 → ℂ) (v : HomogeneousPoly n) :
    avgC n w (AS n d v) = AS n d (avgC n (((d⁻¹ : ℂˣ) : ℂ) • w) v) :=
  nilpotentAverage_intertwines (NC n (((d⁻¹ : ℂˣ) : ℂ) • w)) (NC n w) (AS n d)
    (NC_comp_sigma n d w) _ v

/-! ### Exponential cocycles -/

/-- The complex coordinates of an integral vector. -/
def cw (y : ℤ × ℤ) : Fin 2 → ℂ := ![(y.1 : ℂ), (y.2 : ℂ)]

/-- `b(w) = w₀ b₀ + w₁ b₁`. -/
def pdir (b : Fin 2 → HomogeneousPoly n) (w : Fin 2 → ℂ) : HomogeneousPoly n := w 0 • b 0 + w 1 • b 1

/-- The exponential `Exp(b)(y) = avg(N(y)) b(y)`. -/
def Exp (b : Fin 2 → HomogeneousPoly n) (y : ℤ × ℤ) : HomogeneousPoly n := avgC n (cw y) (pdir n b (cw y))

theorem NC_cw (y : ℤ × ℤ) :
    NC n (cw y) = latticeInfinitesimal (lowerRadicalGenerator n 0) (lowerRadicalGenerator n 1)
      (Multiplicative.ofAdd y) := by
  simp [NC, cw, latticeInfinitesimal]

/-- **Every lower-radical cocycle is the exponential of its pair.** -/
theorem cocycle_exp (ξ : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n)) (y : ℤ × ℤ) :
    ξ (Multiplicative.ofAdd y) = Exp n (lowerRadicalCocyclePair n ξ) y := by
  have h := latticeCocycle_direction (lowerRadicalLatticeRep n) ξ
    (lowerRadicalGenerator n 0) (lowerRadicalGenerator n 1)
    (lowerRadicalCocyclePair n ξ 0) (lowerRadicalCocyclePair n ξ 1)
    (lowerRadicalGenerators_commute n) (lowerRadicalCocyclePair_generator_closed ξ)
    n n (lowerRadicalGenerator_power_zero n 0) (lowerRadicalGenerator_power_zero n 1)
    ((lowerRadicalLatticeRep_first n).trans (exp_inst_irrel _ _ _))
    ((lowerRadicalLatticeRep_second n).trans (exp_inst_irrel _ _ _))
    (lowerRadicalCocyclePair_average ξ 0).symm (lowerRadicalCocyclePair_average ξ 1).symm
    (Multiplicative.ofAdd y) (2 * n)
    (by have := NC_nilpotent n (cw y); rw [NC_cw] at this; exact this)
  rw [h, Exp, avgC, NC_cw]
  rfl

theorem cw_e0 : cw ((1, 0) : ℤ × ℤ) = ![1, 0] := by simp [cw]

theorem cw_e1 : cw ((0, 1) : ℤ × ℤ) = ![0, 1] := by simp [cw]

/-- The basis vectors of `ℤ²`. -/
def eL (i : Fin 2) : ℤ × ℤ := if i = 0 then (1, 0) else (0, 1)

theorem avg_eL (i : Fin 2) (v : HomogeneousPoly n) :
    avgC n (cw (eL i)) v = lowerRadicalAverageEquiv n i v := by
  have hcut := average_cutoff n (lowerRadicalGenerator n i) (n + 1) (2 * n + 1)
    (lowerRadicalGenerator_power_zero n i) (by omega)
  have hN : NC n (cw (eL i)) = lowerRadicalGenerator n i := by
    fin_cases i <;> simp [NC, cw, eL]
  rw [avgC, hN, ← hcut]
  rfl

theorem pdir_eL (b : Fin 2 → HomogeneousPoly n) (i : Fin 2) : pdir n b (cw (eL i)) = b i := by
  fin_cases i <;> simp [pdir, cw, eL]

/-- **The pair of an exponential.** -/
theorem pair_exp (b : Fin 2 → HomogeneousPoly n) (i : Fin 2) :
    (lowerRadicalAverageEquiv n i).symm (Exp n b (eL i)) = b i := by
  rw [Exp, avg_eL, pdir_eL, LinearEquiv.symm_apply_apply]

/-! ### Levi translates of exponentials -/

/-- The Levi pair `(M · b)_i = ∑_k M_{ik} A_M b_k`. -/
def leviP (M : Binary.GL2) (b : Fin 2 → HomogeneousPoly n) : Fin 2 → HomogeneousPoly n :=
  fun i => M.val i 0 • AL n M (b 0) + M.val i 1 • AL n M (b 1)

theorem AL_pdir (M : Binary.GL2) (b : Fin 2 → HomogeneousPoly n) (w : Fin 2 → ℂ) :
    AL n M (pdir n b (rowMul w M.val)) = pdir n (leviP n M b) w := by
  simp only [pdir, rowMul, leviP, map_add, map_smul, smul_add, smul_smul, add_smul]
  module

theorem cw_ivmul (y : ℤ × ℤ) (Mint : Matrix (Fin 2) (Fin 2) ℤ) :
    cw (ivmul y Mint) = rowMul (cw y) (Mint.map (Int.cast : ℤ → ℂ)) := by
  funext k
  fin_cases k <;> simp [cw, ivmul, rowMul]

/-- **Levi translate of an exponential.** -/
theorem levi_exp (M : Binary.GL2) (Mint : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.val = Mint.map (Int.cast : ℤ → ℂ)) (b : Fin 2 → HomogeneousPoly n) (y : ℤ × ℤ) :
    AL n M (Exp n b (ivmul y Mint)) = Exp n (leviP n M b) y := by
  rw [Exp, Exp, cw_ivmul, ← hM, ← AL_pdir, avg_levi]

/-- The restriction of the `σ`-action. -/
theorem restrict_sigma (d : ℂˣ) (f : Poly) :
    binaryPolynomialRestrict (action (-1) (planeLevi (1 : Binary.GL2) d) f) =
      ((d⁻¹ : ℂˣ) : ℂ) • binaryPolynomialRestrict f := by
  rw [action_apply, planeLevi_determinantCharacter, planeLevi_inverse, planeLevi_value, map_smul,
    restrict_substitute_planeBlock, inv_one, Units.val_one]
  simp [Binary.substitute_one, Binary.determinantCharacter]

/-- **Equivariance of the lower coordinate under rational Levi elements.** -/
theorem coord_leviP (M : Binary.GL2) (b : Fin 2 → HomogeneousPoly n) :
    lowerRadicalCoordinate n (leviP n M b) =
      Binary.homogeneousAction (n + 1) 0 M (lowerRadicalCoordinate n b) := by
  apply Subtype.ext
  change binaryPolynomialRestrict (lowerRadicalContraction (leviP n M b 0).val (leviP n M b 1).val) =
    Binary.action 0 M (binaryPolynomialRestrict (lowerRadicalContraction (b 0).val (b 1).val))
  have h : ∀ i, (leviP n M b i).val = lowerRadicalLeviPair M (fun k => (b k).val) i := by
    intro i
    simp [leviP, lowerRadicalLeviPair, Fin.sum_univ_two, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [h, h, lowerRadicalLeviPair_contraction, restrict_substitute_planeBlock, Binary.action_apply]
  simp [Binary.determinantCharacter]

/-- The `σ`-rescaled pair `b'_i = d⁻¹ ρ(σ) b_i`. -/
def sigmaP (d : ℂˣ) (b : Fin 2 → HomogeneousPoly n) : Fin 2 → HomogeneousPoly n :=
  fun i => ((d⁻¹ : ℂˣ) : ℂ) • AS n d (b i)

theorem coord_sigmaP (d : ℂˣ) (b : Fin 2 → HomogeneousPoly n) :
    lowerRadicalCoordinate n (sigmaP n d b) =
      (((d⁻¹ : ℂˣ) : ℂ) * ((d⁻¹ : ℂˣ) : ℂ)) • lowerRadicalCoordinate n b := by
  apply Subtype.ext
  change binaryPolynomialRestrict (lowerRadicalContraction (sigmaP n d b 0).val (sigmaP n d b 1).val) =
    (((d⁻¹ : ℂˣ) : ℂ) * ((d⁻¹ : ℂˣ) : ℂ)) •
      binaryPolynomialRestrict (lowerRadicalContraction (b 0).val (b 1).val)
  simp only [sigmaP, lowerRadicalContraction, Submodule.coe_smul, homogeneousAction_coe, map_sub,
    map_mul, map_smul, restrict_sigma]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul]
  ring

/-! ### The coordinate of a function -/

/-- The inverse-averaged generator values of a function `ℤ² → V`. -/
def valsL : (ℤ × ℤ → HomogeneousPoly n) →ₗ[ℂ] (Fin 2 → HomogeneousPoly n) :=
  LinearMap.pi fun i => (lowerRadicalAverageEquiv n i).symm.toLinearMap ∘ₗ LinearMap.proj (eL i)

theorem valsL_apply (f : ℤ × ℤ → HomogeneousPoly n) (i : Fin 2) :
    valsL n f i = (lowerRadicalAverageEquiv n i).symm (f (eL i)) := rfl

/-- The lower-radical coordinate of a function `ℤ² → V`, computed from its values at `e₁, e₂`. -/
def coordF : (ℤ × ℤ → HomogeneousPoly n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (lowerRadicalCoordinate n).comp (valsL n)

theorem coordF_exp (b : Fin 2 → HomogeneousPoly n) : coordF n (Exp n b) = lowerRadicalCoordinate n b := by
  change lowerRadicalCoordinate n (valsL n (Exp n b)) = _
  congr 1
  funext i
  exact pair_exp n b i

theorem rho_eL (i : Fin 2) :
    ρn n (lowerRadicalLattice (Multiplicative.ofAdd (eL i))) = IsNilpotent.exp (lowerRadicalGenerator n i) := by
  fin_cases i
  · exact lowerRadicalLatticeRep_first n
  · exact lowerRadicalLatticeRep_second n

theorem lowerGen_val (i : Fin 2) (S : HomogeneousPoly n) :
    (lowerRadicalGenerator n i S).val = (-3 : ℂ) • (X i.castSucc * pderiv 2 S.val) := rfl

/-- **Coboundaries have zero coordinate.** -/
theorem coordF_cob (S : HomogeneousPoly n) :
    coordF n (fun y => ρn n (lowerRadicalLattice (Multiplicative.ofAdd y)) S - S) = 0 := by
  have h : ∀ i, valsL n (fun y => ρn n (lowerRadicalLattice (Multiplicative.ofAdd y)) S - S) i =
      lowerRadicalGenerator n i S := by
    intro i
    rw [valsL_apply]
    apply (lowerRadicalAverageEquiv n i).injective
    rw [LinearEquiv.apply_symm_apply]
    have e := nilpotent_difference_apply (lowerRadicalGenerator n i) n
      (lowerRadicalGenerator_power_zero n i) S
    rw [LinearMap.sub_apply, Module.End.one_apply] at e
    rw [rho_eL, exp_inst_irrel _ Algebra.toModule]
    exact e
  change lowerRadicalCoordinate n (valsL n _) = 0
  rw [show valsL n (fun y => ρn n (lowerRadicalLattice (Multiplicative.ofAdd y)) S - S) =
    fun i => lowerRadicalGenerator n i S from funext h]
  apply Subtype.ext
  change binaryPolynomialRestrict (lowerRadicalContraction (lowerRadicalGenerator n 0 S).val
    (lowerRadicalGenerator n 1 S).val) = 0
  rw [lowerGen_val, lowerGen_val]
  rw [show lowerRadicalContraction ((-3 : ℂ) • (X (Fin.castSucc 0) * pderiv 2 S.val))
      ((-3 : ℂ) • (X (Fin.castSucc 1) * pderiv 2 S.val)) = 0 by
    simp only [lowerRadicalContraction, Algebra.smul_def, MvPolynomial.algebraMap_eq, Fin.castSucc_zero,
      Fin.castSucc_one]; ring, map_zero]

/-! ### The corestriction over the radical representatives -/

/-- Closedness of a pair in generator form. -/
def ClosedL (b : Fin 2 → HomogeneousPoly n) : Prop :=
  lowerRadicalGenerator n 0 (b 1) = lowerRadicalGenerator n 1 (b 0)

theorem closedL_iff (b : Fin 2 → HomogeneousPoly n) :
    ClosedL n b ↔ b ∈ lowerRadicalCycles n := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    rw [lowerGen_val, lowerGen_val] at hv
    change X 0 * pderiv 2 (b 1).val = X 1 * pderiv 2 (b 0).val
    have h3 : (-3 : ℂ) ≠ 0 := by norm_num
    exact smul_right_injective _ h3 hv
  · intro h
    apply Subtype.ext
    rw [lowerGen_val, lowerGen_val]
    change X 0 * pderiv 2 (b 1).val = X 1 * pderiv 2 (b 0).val at h
    exact congrArg _ h

theorem closedL_sigmaP (d : ℂˣ) (b : Fin 2 → HomogeneousPoly n) (hb : ClosedL n b) :
    ClosedL n (sigmaP n d b) := by
  unfold ClosedL sigmaP at *
  rw [map_smul, map_smul, lower_sigma, lower_sigma, hb]

theorem closedL_leviP (M : Binary.GL2) (b : Fin 2 → HomogeneousPoly n) (hb : ClosedL n b) :
    ClosedL n (leviP n M b) := by
  unfold ClosedL leviP at *
  have e : ∀ i (v : HomogeneousPoly n), lowerRadicalGenerator n i (AL n M v) =
      AL n M (M.val i 0 • lowerRadicalGenerator n 0 v + M.val i 1 • lowerRadicalGenerator n 1 v) :=
    fun i v => LinearMap.congr_fun (lowerRadicalGenerator_levi n M i) v
  simp only [map_add, map_smul, e, smul_add, smul_smul]
  rw [hb]
  module

/-- A cocycle with a given closed pair. -/
theorem exists_cocycle (b : Fin 2 → HomogeneousPoly n) (hb : ClosedL n b) :
    ∃ ξ : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n), ∀ y, ξ (Multiplicative.ofAdd y) = Exp n b y := by
  obtain ⟨ξ, hξ⟩ := lowerRadicalCocycleToInfinitesimal_surjective n ⟨b, (closedL_iff n b).mp hb⟩
  refine ⟨ξ, fun y => ?_⟩
  rw [cocycle_exp]
  congr 1
  exact congrArg Subtype.val hξ

variable (p : Nat.Primes)

/-- `εp` as a complex unit. -/
def epsC : ℂˣ := Units.map (algebraMap ℚ ℂ) (epsU p)

theorem epsC_val : ((epsC p : ℂˣ) : ℂ) = (epsP p : ℂ) := by
  simp [epsC, epsU_val]

theorem rho_tau (c : Fin p.val × Fin p.val) (v : HomogeneousPoly n) :
    ρn n (rExpl p (.inr c)) v = ρn n (lowerRadicalLattice (Multiplicative.ofAdd (cvec p c)))
      (AS n (epsC p) v) := by
  have hQ : rExpl p (.inr c) = lowerRadicalLattice (Multiplicative.ofAdd (cvec p c)) *
      planeLevi (1 : GL (Fin 2) ℚ) (epsU p) := by
    simp only [rExpl, Q]
    congr 1
  rw [hQ, map_mul, Module.End.mul_apply]
  congr 1
  apply Subtype.ext
  rw [rho_coe]
  change action (-1) _ v.val = action (-1) (planeLevi (1 : Binary.GL2) (epsC p)) v.val
  congr 2
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeLevi, planeBlock, GeneralLinearGroup.map_apply, epsC]

theorem cw_smul (z : ℤ) (y : ℤ × ℤ) : cw (z • y) = (z : ℂ) • cw y := by
  funext k
  fin_cases k <;> simp [cw]

theorem sigma_exp (b : Fin 2 → HomogeneousPoly n) (w : ℤ × ℤ) :
    AS n (epsC p) (Exp n b w) = Exp n (sigmaP n (epsC p) b) (epsP p • w) := by
  have he : ((epsC p : ℂˣ) : ℂ) ≠ 0 := (epsC p).ne_zero
  have hcw : cw w = (((epsC p)⁻¹ : ℂˣ) : ℂ) • cw (epsP p • w) := by
    rw [cw_smul, smul_smul, Units.val_inv_eq_inv_val, epsC_val, inv_mul_cancel₀ (by
      rw [← epsC_val]; exact he), one_smul]
  rw [Exp, Exp]
  conv_lhs => rw [hcw]
  rw [← avg_sigma]
  congr 1
  simp only [pdir, sigmaP, map_add, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul,
    Units.val_inv_eq_inv_val]
  congr 1 <;> congr 1 <;> field_simp

theorem sum_shift {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℂ W] (f : ι → ι)
    (hf : Function.Bijective f) (T : W →ₗ[ℂ] W) (g : ι → W) (v : W) :
    ∑ c, (T (g (f c)) + v - g c) = (Fintype.card ι : ℂ) • v + (T (∑ c, g c) - ∑ c, g c) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← map_sum, hf.sum_comp g, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  abel

/-- **The corestriction of an exponential.** For a closed pair `b`,
`Cor(Exp b)(x) = p² Exp(b')(x) + (ρ(u(x)) - 1) S` with `b' = εp⁻¹ ρ(σ) b`. -/
theorem cor_exp (b : Fin 2 → HomogeneousPoly n) (hb : ClosedL n b) :
    ∃ S : HomogeneousPoly n, ∀ x : ℤ × ℤ,
      (CorL p (ρn n) (Exp n b) x : HomogeneousPoly n) =
        ((p.val : ℂ) ^ 2) • Exp n (sigmaP n (epsC p) b) x +
          (ρn n (lowerRadicalLattice (Multiplicative.ofAdd x)) S - S) := by
  obtain ⟨ξ, hξ⟩ := exists_cocycle n (sigmaP n (epsC p) b) (closedL_sigmaP n _ b hb)
  let ξv : ℤ × ℤ → HomogeneousPoly n := fun y => @id (HomogeneousPoly n) (ξ (Multiplicative.ofAdd y))
  have hξv : ∀ y, ξv y = Exp n (sigmaP n (epsC p) b) y := hξ
  have hcoc : ∀ a z : ℤ × ℤ, ξv (a + z) =
      ρn n (lowerRadicalLattice (Multiplicative.ofAdd a)) (ξv z) + ξv a := by
    intro a z
    exact (groupCohomology.mem_cocycles₁_iff ξ).mp ξ.2 (Multiplicative.ofAdd a) (Multiplicative.ofAdd z)
  refine ⟨∑ c : Fin p.val × Fin p.val, ξv (cvec p c), fun x => ?_⟩
  have hterm : ∀ c : Fin p.val × Fin p.val,
      (R1 (ρn n) (rExpl p (.inr c)) (Exp n b (-cq p (cvec p c - x))) : HomogeneousPoly n) =
        ρn n (lowerRadicalLattice (Multiplicative.ofAdd x)) (ξv (cvec p (crep p (cvec p c - x)))) +
          ξv x - ξv (cvec p c) := by
    intro c
    change ρn n (rExpl p (.inr c)) (Exp n b (-cq p (cvec p c - x))) = _
    rw [rho_tau, sigma_exp, ← hξv]
    have h1 := hcoc (cvec p c) (epsP p • -cq p (cvec p c - x))
    have h2 := hcoc x (cvec p (crep p (cvec p c - x)))
    have hsum : cvec p c + epsP p • -cq p (cvec p c - x) = x + cvec p (crep p (cvec p c - x)) := by
      rw [smul_neg, eps_smul_cq]
      abel
    rw [hsum, h2] at h1
    rw [eq_sub_of_add_eq h1.symm]
  change ∑ c : Fin p.val × Fin p.val,
      (R1 (ρn n) (rExpl p (.inr c)) (Exp n b (-cq p (cvec p c - x))) : HomogeneousPoly n) = _
  refine (Finset.sum_congr rfl (fun c _ => hterm c)).trans ?_
  refine (sum_shift (fun c => crep p (cvec p c - x)) (crep_shift_bijective p x)
    (ρn n (lowerRadicalLattice (Multiplicative.ofAdd x))) (fun c => ξv (cvec p c)) (ξv x)).trans ?_
  have hc : (Fintype.card (Fin p.val × Fin p.val) : ℂ) = (p.val : ℂ) ^ 2 := by simp [sq]
  rw [hc, hξv]

/-! ### The binary edge of the good line -/

/-- The relative two-cocycles of the good-line stabilizer. -/
abbrev RelL := relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n)

theorem edgeL_eq (c : RelL n) (μ : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    edgeL (ρn n) c.val μ y = goodLineRadicalEdgeCycle n c μ (Multiplicative.ofAdd y) := by
  rw [goodLineSplitEdgeCycle_apply, inl1_eq, inl1_eq, splitting1_eq]
  rfl

/-- The pair of the edge cocycle at `μ`. -/
abbrev pairE (c : RelL n) (μ : GL (Fin 2) ℤ) : Fin 2 → HomogeneousPoly n :=
  lowerRadicalCocyclePair n (goodLineRadicalEdgeCycle n c μ)

theorem edgeL_exp (c : RelL n) (μ : GL (Fin 2) ℤ) :
    (fun y => (edgeL (ρn n) c.val μ y : HomogeneousPoly n)) = Exp n (pairE n c μ) := by
  funext y
  rw [edgeL_eq, cocycle_exp]

theorem closed_pairE (c : RelL n) (μ : GL (Fin 2) ℤ) : ClosedL n (pairE n c μ) :=
  lowerRadicalCocyclePair_generator_closed _

theorem binaryEdgeL_eq (hn : 0 < n) (c : RelL n) (μ : GL (Fin 2) ℤ) :
    (goodLineBinaryEdgeCycle n hn c μ : Binary.HomogeneousPoly (n + 1)) =
      lowerRadicalCoordinate n (pairE n c μ) := by
  rw [goodLineBinaryEdgeCycle_apply]
  rfl

theorem binaryEdgeL_coordF (hn : 0 < n) (c : RelL n) (μ : GL (Fin 2) ℤ) :
    (goodLineBinaryEdgeCycle n hn c μ : Binary.HomogeneousPoly (n + 1)) =
      coordF n (fun y => (edgeL (ρn n) c.val μ y : HomogeneousPoly n)) := by
  rw [binaryEdgeL_eq, edgeL_exp, coordF_exp]

theorem rel1_U1 (c : RelL n) (a b : ℤ × ℤ) : c.val (U1 a, U1 b) = 0 := by
  have h := c.2 (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
  rwa [inl1_eq, inl1_eq] at h

/-- The Hecke image as a relative cocycle. -/
def heckeRelL (c : RelL n) : RelL n :=
  ⟨heckeTwoL p (ρn n) c.val, by
    intro u v
    rw [inl1_eq, inl1_eq]
    exact heckeTwoL_relative p (ρn n) c.val (rel1_U1 n c) _ _⟩

theorem rho_leviQ (B : GL (Fin 2) ℚ) (v : HomogeneousPoly n) :
    ρn n (Q 0 B 1) v = AL n (cx2 B) v := by
  apply Subtype.ext
  rw [rho_coe, ← levi_eq_Q, map_planeLevi_one]
  rfl

theorem rho_U (u : ℤ × ℤ) (v : HomogeneousPoly n) :
    ρn n (Qint u 1) v = ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) v := by
  have : Qint u 1 = lowerRadicalLattice (Multiplicative.ofAdd u) := by
    have h := congrArg Subtype.val (inl1_eq (Multiplicative.ofAdd u))
    exact h.symm
  rw [this]

theorem cx2_integral (m : GL (Fin 2) ℤ) : (cx2 (integralEmbed m)).val = m.val.map (Int.cast : ℤ → ℂ) := by
  ext i j
  simp [cx2, integralEmbed, GeneralLinearGroup.map_apply]

theorem cx2_BGL (j : Option (Fin p.val)) : (cx2 (BGL p j)).val = (Bint p j).map (Int.cast : ℤ → ℂ) := by
  ext a b
  have h := congrFun (congrFun (Bmat_eq p j) a) b
  change algebraMap ℚ ℂ (Bmat p j a b) = _
  rw [h]
  simp

/-- The binary edge cocycle value, as a binary polynomial. -/
def bE (hn : 0 < n) (c : RelL n) (μ : GL (Fin 2) ℤ) : Binary.HomogeneousPoly (n + 1) :=
  @id (Binary.HomogeneousPoly (n + 1)) (goodLineBinaryEdgeCycle n hn c μ)

theorem bE_eq (hn : 0 < n) (c : RelL n) (μ : GL (Fin 2) ℤ) :
    bE n hn c μ = lowerRadicalCoordinate n (pairE n c μ) := binaryEdgeL_eq n hn c μ

theorem levi_term (c : RelL n) (μ : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    (fun u => (R1 (ρn n) (rExpl p (.inl j)) (edgeL (ρn n) c.val μ (ivmul u (Bint p j))) :
      HomogeneousPoly n)) = Exp n (leviP n (cx2 (BGL p j)) (pairE n c μ)) := by
  funext u
  have e : (edgeL (ρn n) c.val μ (ivmul u (Bint p j)) : HomogeneousPoly n) =
      Exp n (pairE n c μ) (ivmul u (Bint p j)) := congrFun (edgeL_exp n c μ) _
  have h1 : @id (HomogeneousPoly n) (R1 (ρn n) (rExpl p (.inl j)) (edgeL (ρn n) c.val μ (ivmul u (Bint p j)))) =
      ρn n (Q 0 (BGL p j) 1) (Exp n (pairE n c μ) (ivmul u (Bint p j))) := by
    rw [← e]; rfl
  refine h1.trans ?_
  rw [rho_leviQ, levi_exp n (cx2 (BGL p j)) (Bint p j) (cx2_BGL p j)]

theorem conj_term (c : RelL n) (ν μ : GL (Fin 2) ℤ) :
    (fun y => (conjL (ρn n) ν (edgeL (ρn n) c.val μ) y : HomogeneousPoly n)) =
      Exp n (leviP n (cx2 (integralEmbed ν)) (pairE n c μ)) := by
  funext y
  have e : (edgeL (ρn n) c.val μ (ivmul y ν.val) : HomogeneousPoly n) =
      Exp n (pairE n c μ) (ivmul y ν.val) := congrFun (edgeL_exp n c μ) _
  have hq : Qint 0 ν = Q 0 (integralEmbed ν) 1 := by simp [Qint, icast]; rfl
  unfold conjL
  rw [hq]
  refine (congrArg (ρn n (Q 0 (integralEmbed ν) 1)) e).trans ?_
  rw [rho_leviQ, levi_exp n (cx2 (integralEmbed ν)) ν.val (cx2_integral ν)]

theorem epsP_sq : ((epsP p : ℂ)) ^ 2 = (p.val : ℂ) ^ 2 := by
  unfold epsP
  split_ifs <;> push_cast <;> ring

theorem AL_mul (M M' : Binary.GL2) (v : Binary.HomogeneousPoly (n + 1)) :
    Binary.homogeneousAction (n + 1) 0 M (Binary.homogeneousAction (n + 1) 0 M' v) =
      Binary.homogeneousAction (n + 1) 0 (M * M') v := by
  rw [map_mul, Module.End.mul_apply]

theorem Qint_zero (ν : GL (Fin 2) ℤ) : Qint 0 ν = Q 0 (integralEmbed ν) 1 := by
  simp [Qint, icast]; rfl

theorem hcomm (m : GL (Fin 2) ℤ) (u : ℤ × ℤ) (v : HomogeneousPoly n) :
    ρn n (Qint 0 m) (ρn n (lowerRadicalLattice (Multiplicative.ofAdd (ivmul u m.val))) v) =
      ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) (ρn n (Qint 0 m) v) := by
  rw [← rho_U, ← rho_U, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  have h := congrArg Subtype.val (L1_U1 m (ivmul u m.val))
  change Qint 0 m * Qint (ivmul u m.val) 1 = Qint (ivmul (ivmul u m.val) (m⁻¹ : GL (Fin 2) ℤ).val) 1 *
    Qint 0 m at h
  rw [ivmul_inv_cancel] at h
  rw [h]

/-- The radical term of the edge formula, as an exponential plus a coboundary. -/
theorem rad_term (c : RelL n) (m : GL (Fin 2) ℤ) : ∃ T : HomogeneousPoly n, ∀ u : ℤ × ℤ,
    @id (HomogeneousPoly n) (R1 (ρn n) (Qint 0 m)
      (CorL p (ρn n) (conjL (ρn n) m⁻¹ (edgeL (ρn n) c.val m)) (ivmul u m.val))) =
      ((p.val : ℂ) ^ 2) • Exp n (leviP n (cx2 (integralEmbed m))
        (sigmaP n (epsC p) (leviP n (cx2 (integralEmbed m⁻¹)) (pairE n c m)))) u +
        (ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) T - T) := by
  set b := leviP n (cx2 (integralEmbed m⁻¹)) (pairE n c m)
  have hb : ClosedL n b := closedL_leviP n _ _ (closed_pairE n c m)
  obtain ⟨S, hS⟩ := cor_exp n p b hb
  refine ⟨ρn n (Qint 0 m) S, fun u => ?_⟩
  have hc : CorL p (ρn n) (conjL (ρn n) m⁻¹ (edgeL (ρn n) c.val m)) (ivmul u m.val) =
      CorL p (ρn n) (Exp n b) (ivmul u m.val) := by
    have := conj_term n c m⁻¹ m
    unfold CorL
    exact Finset.sum_congr rfl (fun d _ => congrArg _ (congrFun this _))
  rw [hc]
  refine (congrArg (ρn n (Qint 0 m)) (hS (ivmul u m.val))).trans ?_
  rw [map_add, map_smul, map_sub, hcomm, Qint_zero, rho_leviQ,
    levi_exp n (cx2 (integralEmbed m)) m.val (cx2_integral m)]

theorem levi_pt (c : RelL n) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (u : ℤ × ℤ) :
    @id (HomogeneousPoly n) (R1 (ρn n) (rExpl p (.inl j))
      (edgeL (ρn n) c.val (arithmeticDelta p m j) (ivmul u (Bint p j)))) =
      Exp n (leviP n (cx2 (BGL p j)) (pairE n c (arithmeticDelta p m j))) u :=
  congrFun (levi_term n p c (arithmeticDelta p m j) j) u

theorem cob_pt (Φ : Aρ1 (ρn n)) (u : ℤ × ℤ) :
    @id (HomogeneousPoly n) (R1 (ρn n) (Qint u 1) Φ - Φ) =
      ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) (@id (HomogeneousPoly n) Φ) -
        @id (HomogeneousPoly n) Φ := by
  change ρn n (Qint u 1) (@id (HomogeneousPoly n) Φ) - @id (HomogeneousPoly n) Φ = _
  rw [rho_U]

theorem p_sq_eps : ((p.val : ℂ) ^ 2) * ((((epsC p)⁻¹ : ℂˣ) : ℂ) * (((epsC p)⁻¹ : ℂˣ) : ℂ)) = 1 := by
  have he : (epsP p : ℂ) ≠ 0 := by exact_mod_cast epsP_ne_zero' p
  rw [Units.val_inv_eq_inv_val, epsC_val, ← epsP_sq]
  field_simp

/-- **Cocycle-level Hecke formula for the good-line binary edge.**
`E(Tc)(m) = E(c)(m) + ∑_j ρ(B_j) E(c)(μ_j)`. -/
theorem binaryEdgeL_hecke (hn : 0 < n) (c : RelL n) (m : GL (Fin 2) ℤ) :
    bE n hn (heckeRelL n p c) m = bE n hn c m + ∑ j : Option (Fin p.val),
      Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j)) (bE n hn c (arithmeticDelta p m j)) := by
  obtain ⟨T, hT⟩ := rad_term n p c m
  set Φ : Aρ1 (ρn n) := ∑ d : Fin p.val × Fin p.val, phiL p (ρn n) c.val m d
  have hfun : (fun u => @id (HomogeneousPoly n) (edgeL (ρn n) (heckeTwoL p (ρn n) c.val) m u)) =
      (∑ j : Option (Fin p.val), Exp n (leviP n (cx2 (BGL p j)) (pairE n c (arithmeticDelta p m j)))) +
        (((p.val : ℂ) ^ 2) • Exp n (leviP n (cx2 (integralEmbed m))
          (sigmaP n (epsC p) (leviP n (cx2 (integralEmbed m⁻¹)) (pairE n c m)))) +
          fun u => ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) T - T) +
        fun u => ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) (@id (HomogeneousPoly n) Φ) -
          @id (HomogeneousPoly n) Φ := by
    funext u
    refine (congrArg (@id (HomogeneousPoly n))
      (edgeL_heckeTwoL p (ρn n) c.val (rel1_U1 n c) m u)).trans ?_
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    have hsplit : @id (HomogeneousPoly n)
        ((∑ j : Option (Fin p.val), R1 (ρn n) (rExpl p (.inl j))
            (edgeL (ρn n) c.val (arithmeticDelta p m j) (ivmul u (Bint p j)))) +
          R1 (ρn n) (Qint 0 m) (CorL p (ρn n) (conjL (ρn n) m⁻¹ (edgeL (ρn n) c.val m)) (ivmul u m.val)) +
          (R1 (ρn n) (Qint u 1) Φ - Φ)) =
        (∑ j : Option (Fin p.val), @id (HomogeneousPoly n) (R1 (ρn n) (rExpl p (.inl j))
            (edgeL (ρn n) c.val (arithmeticDelta p m j) (ivmul u (Bint p j))))) +
          @id (HomogeneousPoly n) (R1 (ρn n) (Qint 0 m)
            (CorL p (ρn n) (conjL (ρn n) m⁻¹ (edgeL (ρn n) c.val m)) (ivmul u m.val))) +
          @id (HomogeneousPoly n) (R1 (ρn n) (Qint u 1) Φ - Φ) := rfl
    refine hsplit.trans ?_
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·)
      (Finset.sum_congr rfl (fun j _ => levi_pt n p c m j u)) (hT u)) (cob_pt n Φ u)
  have hL : ∀ j : Option (Fin p.val),
      coordF n (Exp n (leviP n (cx2 (BGL p j)) (pairE n c (arithmeticDelta p m j)))) =
        Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j)) (bE n hn c (arithmeticDelta p m j)) := by
    intro j
    rw [coordF_exp, coord_leviP, bE_eq]
  have hR : ((p.val : ℂ) ^ 2) • coordF n (Exp n (leviP n (cx2 (integralEmbed m))
      (sigmaP n (epsC p) (leviP n (cx2 (integralEmbed m⁻¹)) (pairE n c m))))) = bE n hn c m := by
    rw [coordF_exp, coord_leviP, coord_sigmaP, coord_leviP, map_smul, smul_smul, p_sq_eps p,
      one_smul, AL_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one,
      Module.End.one_apply, bE_eq]
  have key : coordF n
      ((∑ j : Option (Fin p.val), Exp n (leviP n (cx2 (BGL p j)) (pairE n c (arithmeticDelta p m j)))) +
        (((p.val : ℂ) ^ 2) • Exp n (leviP n (cx2 (integralEmbed m))
          (sigmaP n (epsC p) (leviP n (cx2 (integralEmbed m⁻¹)) (pairE n c m)))) +
          fun u => ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) T - T) +
        fun u => ρn n (lowerRadicalLattice (Multiplicative.ofAdd u)) (@id (HomogeneousPoly n) Φ) -
          @id (HomogeneousPoly n) Φ) =
      (∑ j : Option (Fin p.val), Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j))
        (bE n hn c (arithmeticDelta p m j))) + bE n hn c m := by
    generalize ((p.val : ℂ) ^ 2) = k at hR ⊢
    have hs := map_smul (coordF n) k (Exp n (leviP n (cx2 (integralEmbed m))
      (sigmaP n (epsC p) (leviP n (cx2 (integralEmbed m⁻¹)) (pairE n c m)))))
    simp only [map_add, map_sum, hs, hR, coordF_cob, add_zero]
    exact congrArg (· + bE n hn c m) (Finset.sum_congr rfl (fun j _ => hL j))
  calc bE n hn (heckeRelL n p c) m
      = coordF n (fun u => @id (HomogeneousPoly n) (edgeL (ρn n) (heckeTwoL p (ρn n) c.val) m u)) :=
        binaryEdgeL_coordF n hn (heckeRelL n p c) m
    _ = _ := (congrArg (coordF n) hfun).trans key
    _ = _ := add_comm _ _

end TernaryPeriodPolynomials.Spectral.GoodLineCoordinate
