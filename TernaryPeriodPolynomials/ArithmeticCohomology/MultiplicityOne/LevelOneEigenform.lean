module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PeterssonSemisimple
public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.Separation

@[expose] public section


/-!
# Level-one cusp eigenforms from nonzero local joint eigenspaces

A nonzero local joint generalized eigenspace at the identity-plane or good-line cusp maps
injectively into the joint generalized eigenspace of level-one `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det^σ)`
(`σ = -1`, resp. `0`). When the `T_2` eigenvalue is separated from the Eisenstein eigenvalue, every
class in that joint eigenspace is a period class of a joint generalized eigenform, which is an
honest eigenform by Petersson semisimplicity. The eigenvalue of `T_p` (`p ≠ 3`) on the resulting
cusp form of weight `n + 3` is `p^(n+1) (c(T_p) - 1)` at both cusps.
-/

noncomputable section

open scoped ModularForm MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.LevelOneHecke
open TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.LocalUniqueness (two two_ne_three)

namespace TernaryPeriodPolynomials.MultiplicityOne

/-! ### From a nonzero joint `H¹` class to a cusp eigenform -/

/-- The Eisenstein eigenvalue differs from `e 2` as soon as `‖e 2‖ < 2^(d+1-σ)`. -/
theorem ne_q_of_norm_lt (d : ℕ) (σ : ℤ) (e : Nat.Primes → ℂ)
    (h : ‖e LevelOneEisenstein.two‖ < (2 : ℝ) ^ ((d : ℤ) + 1 - σ)) :
    e LevelOneEisenstein.two ≠ q d σ LevelOneEisenstein.two := by
  intro heq
  have hq := LevelOneEisenstein.le_norm_q d σ LevelOneEisenstein.two
  rw [← heq] at hq
  have h2 : ((LevelOneEisenstein.two.val : ℕ) : ℝ) = 2 := by
    simp [LevelOneEisenstein.two]
  rw [h2] at hq
  exact absurd h (not_lt.mpr hq)

/-- **A nonzero class in the joint generalized eigenspace of level-one `H¹` is the period class
of a nonzero joint eigenform** with eigenvalues `p^σ e_p`, provided `e_2` differs from the
Eisenstein eigenvalue. -/
theorem exists_eigenform_of_mem_jointH1 {d r : ℕ} {k : ℤ} (hd : d = 2 * r) (hk : k = -2 * hw r)
    (positive : 0 < r) (σ : ℤ) (e : Nat.Primes → ℂ)
    (hne : e LevelOneEisenstein.two ≠ q d σ LevelOneEisenstein.two)
    {y : groupCohomology.H1 (arithmeticBinaryRep d σ)} (hy : y ∈ jointH1 d σ e) (hy0 : y ≠ 0) :
    ∃ f : CuspForm levelOne k, f ≠ 0 ∧
      f ∈ LevelOneMultiplicityOne.eigenspaceAwayThree k (fun p => (p.val : ℂ) ^ σ * e p) := by
  subst hd
  subst hk
  have hx' : ∀ p : {p : Nat.Primes // p.val ≠ 3},
      y ∈ (arithmeticHecke (2 * r) σ p.1).maxGenEigenspace (e p.1) := by
    intro p
    exact (Submodule.mem_iInf _).mp hy p
  have hrange := LevelOneEisenstein.mem_range_per_of_mem_maxGenEigenspace r positive σ
    LevelOneEisenstein.two (e LevelOneEisenstein.two) hne
    (hx' ⟨LevelOneEisenstein.two, LevelOneEisenstein.two_ne_three⟩)
  obtain ⟨f, rfl⟩ := hrange
  have hfJ : f ∈ PeterssonSemisimple.jointGenEigenspaceAwayThree (-2 * hw r)
      (fun p => (p.val : ℂ) ^ σ * e p) := by
    change f ∈ ⨅ p : {p : Nat.Primes // p.val ≠ 3},
      Module.End.maxGenEigenspace (levelOneHecke (-2 * hw r) p.1) ((p.1.val : ℂ) ^ σ * e p.1)
    rw [Submodule.mem_iInf]
    intro p
    exact mem_maxGenEigenspace_of_intertwine (per r σ) (per_injective r σ) _ _ _ _
      (levelOnePeriodMap_hecke (2 * r) σ p.1 (hw r) (weight_eq_r r) (even_two_mul r)
        (parityOf σ) (parityOf_sign σ)) (hx' p)
  refine ⟨f, ?_, PeterssonSemisimple.jointGenEigenspaceAwayThree_le _ _ hfJ⟩
  rintro rfl
  exact hy0 (map_zero _)

/-! ### Separation from the Eisenstein eigenvalue at `p = 2` -/

/-- Identity plane: `e_2 = 2^{n+2} (c(T_2) - 1)` is not the Eisenstein eigenvalue. -/
theorem eIdentity_ne_q {n : ℕ} (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4) :
    LocalUniqueness.eIdentity n c LevelOneEisenstein.two ≠
      q (n + 1) (-1) LevelOneEisenstein.two := by
  refine ne_q_of_norm_lt (n + 1) (-1) (LocalUniqueness.eIdentity n c) ?_
  have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - (-1)) = 2 ^ (n + 3) := by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 - (-1) = ((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h2 : ‖((LevelOneEisenstein.two.val : ℕ) : ℂ)‖ = 2 := by
    simp [LevelOneEisenstein.two]
  change ‖(c (TpExistence.tp two) - 1) /
    (((LevelOneEisenstein.two.val : ℕ) : ℂ) ^ (n + 2))⁻¹‖ < _
  rw [hexp, norm_div, norm_inv, norm_pow, h2, div_inv_eq_mul]
  have hpos : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  calc ‖c (TpExistence.tp two) - 1‖ * 2 ^ (n + 2) ≤ 3 / 4 * 2 ^ (n + 2) :=
        mul_le_mul_of_nonneg_right hc hpos.le
    _ < 2 ^ (n + 3) := by
      have hx : (2 : ℝ) ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
      rw [hx]
      linarith

/-- Good line: `e_2 = 2^{n+1} (c(T_2) - 1)` is not the Eisenstein eigenvalue. -/
theorem eGoodLine_ne_q {n : ℕ} (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4) :
    LocalUniqueness.eGoodLine n c LevelOneEisenstein.two ≠
      q (n + 1) 0 LevelOneEisenstein.two := by
  refine ne_q_of_norm_lt (n + 1) 0 (LocalUniqueness.eGoodLine n c) ?_
  have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - 0) = 2 ^ (n + 2) := by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 - 0 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h2 : ‖((LevelOneEisenstein.two.val : ℕ) : ℂ)‖ = 2 := by
    simp [LevelOneEisenstein.two]
  change ‖(c (TpExistence.tp two) - 1) /
    (((LevelOneEisenstein.two.val : ℕ) : ℂ) ^ (n + 1))⁻¹‖ < _
  rw [hexp, norm_div, norm_inv, norm_pow, h2, div_inv_eq_mul]
  have hpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  calc ‖c (TpExistence.tp two) - 1‖ * 2 ^ (n + 1) ≤ 3 / 4 * 2 ^ (n + 1) :=
        mul_le_mul_of_nonneg_right hc hpos.le
    _ < 2 ^ (n + 2) := by
      have hx : (2 : ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
      rw [hx]
      linarith

/-! ### The eigenvalue formulas -/

/-- Identity plane: `p^{-1} · p^{n+2} (c(T_p) - 1) = p^{n+1} (c(T_p) - 1)`. -/
theorem identity_eigenvalue (n : ℕ) (c : HeckeCorrespondence → ℂ) (p : Nat.Primes) :
    (p.val : ℂ) ^ (-1 : ℤ) * LocalUniqueness.eIdentity n c p =
      (p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1) := by
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have h2 : (p.val : ℂ) ^ (n + 2) = (p.val : ℂ) ^ (n + 1) * (p.val : ℂ) := by ring
  rw [LocalUniqueness.eIdentity, div_inv_eq_mul, zpow_neg_one, h2]
  calc (p.val : ℂ)⁻¹ * ((c (TpExistence.tp p) - 1) * ((p.val : ℂ) ^ (n + 1) * (p.val : ℂ)))
      = ((p.val : ℂ)⁻¹ * (p.val : ℂ)) * ((p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1)) := by
        ring
    _ = (p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1) := by
        rw [inv_mul_cancel₀ hp, one_mul]

/-- Good line: `p^0 · p^{n+1} (c(T_p) - 1) = p^{n+1} (c(T_p) - 1)`. -/
theorem goodLine_eigenvalue (n : ℕ) (c : HeckeCorrespondence → ℂ) (p : Nat.Primes) :
    (p.val : ℂ) ^ (0 : ℤ) * LocalUniqueness.eGoodLine n c p =
      (p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1) := by
  rw [LocalUniqueness.eGoodLine, div_inv_eq_mul, zpow_zero, one_mul]
  ring

/-! ### The two cusps -/

/-- **A level-one cusp eigenform from the identity-plane cusp.** For `n` odd and `c` with
`‖c(T_2) - 1‖ ≤ 3/4`, a nonzero local joint generalized eigenspace at the identity plane yields a
nonzero cusp form of weight `n + 3` and level one with `T_p f = p^{n+1} (c(T_p) - 1) f` for all
primes `p ≠ 3`. (The `H¹` eigenvalues are `eIdentity n c p = p^{n+2} (c(T_p) - 1)` and the twist
is `σ = -1`.) -/
theorem exists_levelOne_eigenform_identityPlane {n : ℕ} {k : ℤ} (hk : k = (n : ℤ) + 3)
    (hn : 0 < n) (hodd : Odd n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hne : CuspReduction.localJoint n trivialCharacter c .plane false ≠ ⊥) :
    ∃ f : CuspForm levelOne k, f ≠ 0 ∧
      f ∈ LevelOneMultiplicityOne.eigenspaceAwayThree k
        (fun p => (p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1)) := by
  subst hk
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨m, hm⟩ := id hodd
  have hy := LocalUniqueness.edgeH2_mem_jointH1 c hn hodd hx
  have hy0 : IdentityPlaneHecke.edgeH2 n hn hodd x ≠ 0 := by
    intro h
    apply hx0
    apply IdentityPlaneHecke.edgeH2_injective n hn hodd
    rw [h]
    exact (map_zero _).symm
  have hm' : (n : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
  obtain ⟨f, hf0, hf⟩ := exists_eigenform_of_mem_jointH1 (d := n + 1) (r := m + 1)
    (k := (n : ℤ) + 3) (by omega) (by simp only [hw]; omega) (by omega) (-1)
    (LocalUniqueness.eIdentity n c) (eIdentity_ne_q c hc) hy hy0
  refine ⟨f, hf0, ?_⟩
  have hfun : (fun p : Nat.Primes => (p.val : ℂ) ^ (-1 : ℤ) * LocalUniqueness.eIdentity n c p) =
      fun p => (p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1) :=
    funext (identity_eigenvalue n c)
  rwa [hfun] at hf

/-- **A level-one cusp eigenform from the good-line cusp.** Same as the identity-plane statement,
with the edge `phiL` on `ML n` (the local joint eigenspace lies in `ML n` since
`‖c(T_2) - 1‖ ≤ 3/4`), twist `σ = 0` and `H¹` eigenvalues
`eGoodLine n c p = p^{n+1} (c(T_p) - 1)`. -/
theorem exists_levelOne_eigenform_goodLine {n : ℕ} {k : ℤ} (hk : k = (n : ℤ) + 3)
    (hn : 0 < n) (hodd : Odd n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hne : CuspReduction.localJoint n trivialCharacter c .line true ≠ ⊥) :
    ∃ f : CuspForm levelOne k, f ≠ 0 ∧
      f ∈ LevelOneMultiplicityOne.eigenspaceAwayThree k
        (fun p => (p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1)) := by
  subst hk
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨m, hm⟩ := id hodd
  have hxM : x ∈ LocalUniqueness.ML n := LocalUniqueness.localJoint_le_ML c hc hx
  have hy := LocalUniqueness.phiL_mem_jointH1 c hn ⟨x, hxM⟩ hx
  have hy0 : LocalUniqueness.phiL n hn ⟨x, hxM⟩ ≠ 0 := by
    intro h
    apply hx0
    have h' := LocalUniqueness.phiL_injective hn
      (h.trans (map_zero (LocalUniqueness.phiL n hn)).symm)
    exact congrArg Subtype.val h'
  have hm' : (n : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
  obtain ⟨f, hf0, hf⟩ := exists_eigenform_of_mem_jointH1 (d := n + 1) (r := m + 1)
    (k := (n : ℤ) + 3) (by omega) (by simp only [hw]; omega) (by omega) 0
    (LocalUniqueness.eGoodLine n c) (eGoodLine_ne_q c hc) hy hy0
  refine ⟨f, hf0, ?_⟩
  have hfun : (fun p : Nat.Primes => (p.val : ℂ) ^ (0 : ℤ) * LocalUniqueness.eGoodLine n c p) =
      fun p => (p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1) :=
    funext (goodLine_eigenvalue n c)
  rwa [hfun] at hf

end TernaryPeriodPolynomials.MultiplicityOne
