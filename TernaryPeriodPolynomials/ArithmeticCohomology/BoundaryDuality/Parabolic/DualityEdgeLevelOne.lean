module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne
public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.Separation
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.FullBound

@[expose] public section


/-!
# The edge classes at the level-one cusps are parabolic

The local joint generalized eigenclasses at the good line and at the identity plane (untwisted and
for the odd quadratic character of conductor three) map under the Hochschild–Serre edge maps into
the joint generalized eigenspace of the Hecke operators `T_p` (`p ≠ 3`) on
`H¹(GL₂(ℤ), Sym^{n+1} ⊗ det^σ)`.  When the eigenvalue of `T_2` has norm below `2^{n+2-σ}`, the
boundary functional `[z] ↦ ℓ(z(T))` (a Hecke eigenfunctional with the Eisenstein eigenvalue
`2^{n+2-σ} + 2^{-σ}`) kills the class; since `(T - 1) Sym^{m}` is exactly the kernel of the
evaluation at `(1, 0)`, the vanishing of the functional says that the value of a representative
cocycle at `T` is a coboundary: the class is parabolic.

* `mem_parabolicH1_of_betaGL_eq_zero`: classes killed by the boundary functional are parabolic.
* `mem_parabolicH1_of_jointH1`: so are the classes of a joint eigenspace whose `T_{p₀}` eigenvalue is
  smaller than the Eisenstein one.
* `phiL_mem_parabolicH1` (good line, trivial character), `edgeH2_mem_parabolicH1` (identity plane),
  `edgeH2LT_mem_parabolicH1` (good line, odd character), `edgeH2T_mem_parabolicH1` (identity plane,
  odd character).
* The coefficient pairings: `twistedPairing_goodLine_trivial`, `twistedPairing_goodLine_odd`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.LevelOneEisenstein (betaGL betaGL_arithmeticHecke)
open TernaryPeriodPolynomials.LevelThree

section Core

/-- The matrix of `T` in `GL₂(ℂ)`. -/
theorem map_toGL_T :
    Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (toGL ModularGroup.T) = SymFixed.upperC 1 := by
  apply Units.ext
  ext i j
  change ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) i j = _
  rw [ModularGroup.coe_T]
  fin_cases i <;> fin_cases j <;> simp [SymFixed.upperC]

/-- `T` acts on `Sym^d ⊗ det^σ` through the shear `[[1, 1], [0, 1]]`. -/
theorem rho_T_eq (d : ℕ) (σ : ℤ) :
    (arithmeticBinaryRep d σ).ρ (toGL ModularGroup.T) =
      Binary.homogeneousAction d σ (SymFixed.upperC 1) := by
  change Binary.homogeneousAction d σ
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (toGL ModularGroup.T)) = _
  rw [map_toGL_T]

/-- A binary form with vanishing value at `(1, 0)` is a coboundary of `T`. -/
theorem exists_sub_of_ell_eq_zero (d : ℕ) (σ : ℤ) (v : arithmeticBinaryRep d σ)
    (h : ell d v = 0) :
    ∃ u : arithmeticBinaryRep d σ, (arithmeticBinaryRep d σ).ρ (toGL ModularGroup.T) u - u = v := by
  have hv : (v : Binary.HomogeneousPoly d) ∈ LinearMap.ker (SymFixed.evalAt (m := d) ![1, 0]) := by
    exact (LinearMap.mem_ker (f := SymFixed.evalAt (m := d) ![1, 0])).mpr h
  rw [← FullBound.movedSpace_upper_eq σ one_ne_zero] at hv
  obtain ⟨u, hu⟩ := hv
  refine ⟨u, ?_⟩
  rw [rho_T_eq]
  exact hu

/-- **Classes killed by the boundary functional are parabolic.** -/
theorem mem_parabolicH1_of_betaGL_eq_zero {d : ℕ} {σ : ℤ}
    {x : groupCohomology.H1 (arithmeticBinaryRep d σ)} (h : betaGL d σ x = 0) :
    x ∈ parabolicH1 (arithmeticBinaryRep d σ) := by
  obtain ⟨z, rfl⟩ := oneCocycle_H1_surjective (arithmeticBinaryRep d σ) x
  have h1 : betaGL d σ (groupCohomology.H1π (arithmeticBinaryRep d σ) z) =
      ell d (z (toGL ModularGroup.T)) := by
    show beta d σ (restriction d σ σ (groupCohomology.H1π (arithmeticBinaryRep d σ) z)) = _
    rw [restriction_apply, beta_H1π]
    rfl
  have hz : ell d (z (toGL ModularGroup.T)) = 0 := h1.symm.trans h
  obtain ⟨u, hu⟩ := exists_sub_of_ell_eq_zero d σ _ hz
  have hpar : z ∈ parabolicCocycles (arithmeticBinaryRep d σ) :=
    (mem_parabolicCocycles_iff _ z).mpr ⟨u, hu.symm⟩
  exact Submodule.mem_map_of_mem hpar

/-- The boundary functional kills the joint eigenclasses whose `T_{p₀}` eigenvalue is smaller than
`p₀^(d+1-σ)`, a lower bound for the Eisenstein eigenvalue. -/
theorem betaGL_eq_zero_of_jointH1 {d : ℕ} {σ : ℤ} {e : Nat.Primes → ℂ}
    {x : groupCohomology.H1 (arithmeticBinaryRep d σ)} (hx : x ∈ jointH1 d σ e)
    (p₀ : Nat.Primes) (hp₀ : p₀.val ≠ 3)
    (h : ‖e p₀‖ < ((p₀.val : ℕ) : ℝ) ^ ((d : ℤ) + 1 - σ)) : betaGL d σ x = 0 := by
  have hne : e p₀ ≠ q d σ p₀ := by
    intro heq
    have hq := LevelOneEisenstein.le_norm_q d σ p₀
    rw [← heq] at hq
    exact absurd h (not_lt.mpr hq)
  exact functional_eq_zero_of_mem_maxGenEigenspace _ (betaGL d σ) (q d σ p₀) (e p₀)
    (betaGL_arithmeticHecke d σ p₀) hne ((Submodule.mem_iInf _).mp hx ⟨p₀, hp₀⟩)

/-- **Joint eigenclasses with small `T_{p₀}` eigenvalue are parabolic.** -/
theorem mem_parabolicH1_of_jointH1 {d : ℕ} {σ : ℤ} {e : Nat.Primes → ℂ}
    {x : groupCohomology.H1 (arithmeticBinaryRep d σ)} (hx : x ∈ jointH1 d σ e)
    (p₀ : Nat.Primes) (hp₀ : p₀.val ≠ 3)
    (h : ‖e p₀‖ < ((p₀.val : ℕ) : ℝ) ^ ((d : ℤ) + 1 - σ)) :
    x ∈ parabolicH1 (arithmeticBinaryRep d σ) :=
  mem_parabolicH1_of_betaGL_eq_zero (betaGL_eq_zero_of_jointH1 hx p₀ hp₀ h)

/-- The norm of `a * 2^k` for `‖a‖ ≤ 3/4`. -/
theorem norm_mul_two_pow_lt {a : ℂ} (ha : ‖a‖ ≤ 3 / 4) (k : ℕ) :
    ‖a * (2 : ℂ) ^ k‖ < (2 : ℝ) ^ (k + 1) := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_mul, norm_pow, h2]
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  calc ‖a‖ * 2 ^ k ≤ 3 / 4 * 2 ^ k := mul_le_mul_of_nonneg_right ha hpos.le
    _ < 2 ^ (k + 1) := by
      rw [pow_succ]
      linarith

/-- The norm of `a / (2^k)⁻¹` for `‖a‖ ≤ 3/4`, with `2 = LocalUniqueness.two`. -/
theorem norm_div_inv_lt {a : ℂ} (ha : ‖a‖ ≤ 3 / 4) (k : ℕ) :
    ‖a / (((LocalUniqueness.two.val : ℕ) : ℂ) ^ k)⁻¹‖ < (2 : ℝ) ^ (k + 1) := by
  have h2 : (((LocalUniqueness.two.val : ℕ)) : ℂ) = 2 := by simp [LocalUniqueness.two]
  rw [h2, div_inv_eq_mul]
  exact norm_mul_two_pow_lt ha k

theorem two_val_real : (((LocalUniqueness.two.val : ℕ)) : ℝ) = 2 := by
  simp [LocalUniqueness.two]

end Core

section Edges

variable (n : ℕ)

/-- **Good line, trivial character.**  The edge `phiL` of a local joint generalized eigenclass
(which lies in `ML` by `localJoint_le_ML`) is a parabolic class of
`H¹(GL₂(ℤ), Sym^{n+1})` (the coefficients `(m, e) = (n + 1, 0)`). -/
theorem phiL_mem_parabolicH1 (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    {y : CuspH2 n trivialCharacter .line true}
    (hy : y ∈ localJoint n trivialCharacter c .line true) :
    LocalUniqueness.phiL n hn ⟨y, LocalUniqueness.localJoint_le_ML c hc hy⟩ ∈
      parabolicH1 (arithmeticBinaryRep (n + 1) 0) := by
  refine mem_parabolicH1_of_jointH1
    (LocalUniqueness.phiL_mem_jointH1 c hn ⟨y, LocalUniqueness.localJoint_le_ML c hc hy⟩ hy)
    LocalUniqueness.two LocalUniqueness.two_ne_three ?_
  rw [two_val_real]
  have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - 0) = 2 ^ (n + 2) := by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 - 0 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hexp]
  exact norm_div_inv_lt hc (n + 1)

/-- **Identity plane, trivial character.**  The edge `edgeH2` of a local joint generalized eigenclass
is a parabolic class of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` (`(m, e) = (n + 1, -1)`). -/
theorem edgeH2_mem_parabolicH1 (hn : 0 < n) (hodd : Odd n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    {x : CuspH2 n trivialCharacter .plane false}
    (hx : x ∈ localJoint n trivialCharacter c .plane false) :
    IdentityPlaneHecke.edgeH2 n hn hodd x ∈ parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) := by
  refine mem_parabolicH1_of_jointH1 (LocalUniqueness.edgeH2_mem_jointH1 c hn hodd hx)
    LocalUniqueness.two LocalUniqueness.two_ne_three ?_
  rw [two_val_real]
  have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - (-1)) = 2 ^ (n + 3) := by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 - (-1) = ((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hexp]
  exact norm_div_inv_lt hc (n + 2)

/-- **Good line, odd character of conductor three.**  The twisted edge `edgeH2LT` of a local joint
generalized eigenclass is a parabolic class of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`
(`(m, e) = (n + 1, -1)`), when `‖c(T_2) + 1‖ ≤ 3/4`. -/
theorem edgeH2LT_mem_parabolicH1 (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    {y : CuspH2 n χ .line true} (hy : y ∈ localJoint n χ c .line true) :
    Twisted.edgeH2LT n χ hχ hn (Twisted.psiLT n χ y) ∈
      parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) := by
  refine mem_parabolicH1_of_jointH1 (Twisted.edgeH2LT_mem_jointH1 n χ hχ hn c hy)
    LocalUniqueness.two LocalUniqueness.two_ne_three ?_
  rw [two_val_real]
  have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - (-1)) = 2 ^ (n + 3) := by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 - (-1) = ((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hexp]
  have ha : ‖c (TpExistence.tp LocalUniqueness.two) -
      ((IdentityPlaneLocalOp.sgnP LocalUniqueness.two : ℤ) : ℂ)‖ ≤ 3 / 4 := by
    rw [Twisted.sgnP_two, Int.cast_neg, Int.cast_one, sub_neg_eq_add]
    exact hc
  exact norm_div_inv_lt ha (n + 2)

/-- **Identity plane, odd character of conductor three.**  The twisted edge `edgeH2T` of a local joint
generalized eigenclass is a parabolic class of `H¹(GL₂(ℤ), Sym^{n+1})` (`(m, e) = (n + 1, 0)`), when
`‖c(T_2) + 1‖ ≤ 3/4`. -/
theorem edgeH2T_mem_parabolicH1 (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    {x : CuspH2 n χ .plane false} (hx : x ∈ localJoint n χ c .plane false) :
    Twisted.edgeH2T n χ hχ hn hodd x ∈ parabolicH1 (arithmeticBinaryRep (n + 1) 0) := by
  refine mem_parabolicH1_of_jointH1 (Twisted.edgeH2T_mem_jointH1 n χ hχ c hn hodd hx)
    LocalUniqueness.two LocalUniqueness.two_ne_three ?_
  rw [two_val_real]
  have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - 0) = 2 ^ (n + 2) := by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 - 0 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hexp]
  have ha : ‖c (TpExistence.tp LocalUniqueness.two) -
      ((IdentityPlaneLocalOp.sgnP LocalUniqueness.two : ℤ) : ℂ)‖ ≤ 3 / 4 := by
    rw [Twisted.sgnP_two, Int.cast_neg, Int.cast_one, sub_neg_eq_add]
    exact hc
  exact norm_div_inv_lt ha (n + 1)

end Edges

section Pairings

/-- **Coefficient pairing at the good line / identity plane, trivial character**: the line edges
live in `Sym^{n+1}` and the plane edges in `Sym^{n+1} ⊗ det⁻¹`; for odd `n` the classical pairing
`binaryPairing (n + 1)` satisfies the hypotheses of the parabolic duality
(`(m, e, e') = (n + 1, 0, -1)`: `m` even, `e + e' - m = -(n + 2)` odd). -/
theorem twistedPairing_goodLine_trivial {n : ℕ} (hodd : Odd n) :
    TwistedPairing (arithmeticBinaryRep (n + 1) 0) (arithmeticBinaryRep (n + 1) (-1))
      (BinaryPairing.binaryPairing (n + 1)) :=
  twistedPairing_arithmeticBinaryRep (n + 1) 0 (-1) hodd.add_one (by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨-(k : ℤ) - 2, by omega⟩)

/-- **Coefficient pairing at the good line / identity plane, odd character of conductor three**:
the line edges live in `Sym^{n+1} ⊗ det⁻¹` and the plane edges in `Sym^{n+1}`
(`(m, e, e') = (n + 1, -1, 0)`). -/
theorem twistedPairing_goodLine_odd {n : ℕ} (hodd : Odd n) :
    TwistedPairing (arithmeticBinaryRep (n + 1) (-1)) (arithmeticBinaryRep (n + 1) 0)
      (BinaryPairing.binaryPairing (n + 1)) :=
  twistedPairing_arithmeticBinaryRep (n + 1) (-1) 0 hodd.add_one (by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨-(k : ℤ) - 2, by omega⟩)

/-- **Left nondegeneracy in the line variable, trivial character.** -/
theorem goodLine_left_nondegenerate_trivial {n : ℕ} (hodd : Odd n)
    (cl : parabolicH1 (arithmeticBinaryRep (n + 1) 0))
    (h : ∀ cl' : parabolicH1 (arithmeticBinaryRep (n + 1) (-1)),
      parabolicPairing (twistedPairing_goodLine_trivial hodd) cl cl' = 0) : cl = 0 :=
  parabolicPairing_left_nondegenerate (twistedPairing_goodLine_trivial hodd) cl h

/-- **Left nondegeneracy in the line variable, odd character of conductor three.** -/
theorem goodLine_left_nondegenerate_odd {n : ℕ} (hodd : Odd n)
    (cl : parabolicH1 (arithmeticBinaryRep (n + 1) (-1)))
    (h : ∀ cl' : parabolicH1 (arithmeticBinaryRep (n + 1) 0),
      parabolicPairing (twistedPairing_goodLine_odd hodd) cl cl' = 0) : cl = 0 :=
  parabolicPairing_left_nondegenerate (twistedPairing_goodLine_odd hodd) cl h

end Pairings

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
