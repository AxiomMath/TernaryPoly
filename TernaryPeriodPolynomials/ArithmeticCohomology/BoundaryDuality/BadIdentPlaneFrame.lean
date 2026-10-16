module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBad
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspDualL2

@[expose] public section


/-!
# The frame carrying the dual plane of the bad line to the good-plane block coordinates

The dual plane of the bad line `L₀` is `F = φ(L₀) = longWeyl ⟨e₀, e₁⟩ = ⟨e₁, e₂⟩`, a good plane.  The
Hochschild–Serre edge of the good-plane cusp is defined in the block coordinates of
`GoodPlaneFrame`, in which the stabilizer is `Λ_G = g_F⁻¹ Γ_cusp g_F` with Levi elements
`P(0, κ(m), 1) = diag(κ(m), 1)`, `κ(m) = δ⁻¹ m δ`, `δ = diag(1, 3)`.

With `q = diag(σ, 1)` the exchange of the first two coordinates, `σ = [[0,1],[1,0]]`, and
`τ = q · g_F`, the matrices of the bad-line dual frame `badFrame` satisfy

* `badFrame = τ · q` (`badFrame_eq`), and `q` carries the cusp flag `g_F P` to `F`
  (`swapQ_smul_cuspFlag`), so `τ` carries the reference plane to `F`;
* `τ u(p) τ⁻¹ = φ(u_L(σ p))` for the radical lattice elements (`tau_upper`), where `u_L` is the
  lattice of the bad line, and `σ p` exchanges the two coordinates;
* `τ P(0, κ(m), 1) τ⁻¹ = φ(diag(1, γ))` when `m = α(γ)` (`tau_levi`), where
  `α(γ) = δ γ^{-T} δ⁻¹` is the involution of `Γ₁'(3)` which exchanges the two cusps
  (`α(T) = L⁻¹`, `α(L) = T⁻¹`, `alpha_upper`, `alpha_lower`) and satisfies `κ(α(γ)) = γ^{-T}`
  (`kap_alpha`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)
open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates LevelOneCosets CuspOrbits IdentityPlaneCosets
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne (GL2Z)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (leviHom invT invT_inv_val swapZ swapInt swapInt_mul_self badDualLevi badFrame
    badFrame_conj badFrame_conj_levi swapNegHom)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad

/-! ### The exchange matrix -/

/-- The exchange matrix `σ = [[0,1],[1,0]]` of `GL₂(ℤ)` is an involution. -/
theorem swapZ_mul_self : swapZ * swapZ = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  exact swapInt_mul_self

/-- The exchange matrix `q = diag(σ, 1)` of `GL₃(ℚ)`. -/
def swapQ : RationalGL3 := leviHom swapZ

/-- The matrix of `q`. -/
theorem swapQ_val :
    ((swapQ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapQ, leviHom, planeLeviOneHom, planeLevi, planeBlock, swapZ, swapInt]

/-- `q` is an involution. -/
theorem swapQ_mul_self : swapQ * swapQ = 1 := by
  unfold swapQ
  rw [← map_mul, swapZ_mul_self, map_one]

/-- `q⁻¹ = q`. -/
theorem swapQ_inv : swapQ⁻¹ = swapQ := inv_eq_of_mul_eq_one_right swapQ_mul_self

/-- The matrix of `badFrame`. -/
theorem badFrame_val :
    ((badFrame : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) = !![0, 0, 1; 0, 1, 0; 3, 0, 0] := rfl

/-- The frame `τ = q · g_F`. -/
def tauF : RationalGL3 := swapQ * gF

/-- **The frame identity** `badFrame = τ · q`. -/
theorem badFrame_eq : badFrame = tauF * swapQ := by
  apply Units.ext
  unfold tauF
  rw [Units.val_mul, Units.val_mul, swapQ_val, gF_val, badFrame_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- The inverse of `τ`: `τ⁻¹ = q · badFrame⁻¹`. -/
theorem tauF_inv_eq : tauF⁻¹ = swapQ * badFrame⁻¹ := by
  rw [badFrame_eq, _root_.mul_inv_rev, swapQ_inv, ← mul_assoc, swapQ_mul_self, one_mul]

/-- The Levi element of the exchange matrix is `q`. -/
theorem arithmeticLevi_swapZ : arithmeticLevi swapZ = swapQ := rfl

/-! ### The exchange of the radical lattice coordinates -/

/-- The upper Levi lattice input of the exchange matrix exchanges the two coordinates. -/
theorem sw_apply (p : RadicalLattice) :
    upperLeviLatticeInput swapZ p = Multiplicative.ofAdd (p.toAdd.2, p.toAdd.1) := by
  have hs : swapZ⁻¹ = swapZ := inv_eq_of_mul_eq_one_right swapZ_mul_self
  apply Multiplicative.toAdd.injective
  change ((((swapZ⁻¹ : GL2Z)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * p.toAdd.1 +
        (((swapZ⁻¹ : GL2Z)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * p.toAdd.2,
      (((swapZ⁻¹ : GL2Z)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * p.toAdd.1 +
        (((swapZ⁻¹ : GL2Z)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * p.toAdd.2) = _
  rw [hs]
  simp [swapZ, swapInt]

/-- The exchange of the coordinates is an involution. -/
theorem sw_sw (p : RadicalLattice) :
    upperLeviLatticeInput swapZ (upperLeviLatticeInput swapZ p) = p := by
  rw [sw_apply, sw_apply]
  apply Multiplicative.toAdd.injective
  simp

/-! ### Conjugation of the radical lattice by `τ` -/

/-- The lattice element of the bad line attached to the radical coordinate `p` through the
exchange: `u_L(σ p)`. -/
def radL (p : RadicalLattice) : RationalGL3 :=
  latL0.hom (swapNegHom (upperLeviLatticeInput swapZ p))

/-- The lattice elements `radL p` lie in the lattice `U` of the bad line. -/
theorem radL_mem (p : RadicalLattice) : radL p ∈ latL0.sub := ⟨_, rfl⟩

/-- **Conjugation of the radical lattice by `τ`**: `τ u(p) τ⁻¹ = φ(u_L(σ p))`. -/
theorem tau_upper (p : RadicalLattice) :
    tauF * upperRadicalLattice p * tauF⁻¹ = dualInvolution (radL p) := by
  have hb : badFrame⁻¹ * dualInvolution (radL p) * badFrame =
      upperRadicalLattice (upperLeviLatticeInput swapZ p) :=
    badFrame_conj (upperLeviLatticeInput swapZ p)
  have hc : upperRadicalLattice (upperLeviLatticeInput swapZ p) * swapQ =
      swapQ * upperRadicalLattice p := by
    have h := upperLeviLatticeInput_conjugation swapZ (upperLeviLatticeInput swapZ p)
    rw [sw_sw] at h
    exact h
  have h1 : dualInvolution (radL p) =
      badFrame * upperRadicalLattice (upperLeviLatticeInput swapZ p) * badFrame⁻¹ := by
    rw [← hb]
    group
  have hc2 : swapQ * upperRadicalLattice (upperLeviLatticeInput swapZ p) * swapQ⁻¹ =
      upperRadicalLattice p := by
    rw [swapQ_inv]
    calc swapQ * upperRadicalLattice (upperLeviLatticeInput swapZ p) * swapQ
        = swapQ * (upperRadicalLattice (upperLeviLatticeInput swapZ p) * swapQ) := by
          rw [mul_assoc]
      _ = swapQ * (swapQ * upperRadicalLattice p) := by rw [hc]
      _ = (swapQ * swapQ) * upperRadicalLattice p := by rw [mul_assoc]
      _ = upperRadicalLattice p := by rw [swapQ_mul_self, one_mul]
  rw [h1, badFrame_eq]
  calc tauF * upperRadicalLattice p * tauF⁻¹
      = tauF * (swapQ * upperRadicalLattice (upperLeviLatticeInput swapZ p) * swapQ⁻¹) * tauF⁻¹ := by
        rw [hc2]
    _ = tauF * swapQ * upperRadicalLattice (upperLeviLatticeInput swapZ p) * (tauF * swapQ)⁻¹ := by
        group

/-! ### The Levi elements -/

/-- The block Levi element `P(0, κ(m), 1)` is `diag(κ(m), 1)`. -/
theorem Pg_zero_eq (m : binaryArithmeticLevel) : Pg 0 m 1 = arithmeticLevi (kap m) := by
  apply Units.ext
  rw [Pg, P_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [arithmeticLevi, GeneralLinearGroup.map_apply, planeLevi, planeBlock, integralEmbed_val,
      icast]

/-- The integral matrix `[[κ₀₀, κ₀₁/3], [3 κ₁₀, κ₁₁]]`. -/
def unkapMat (κ : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![κ 0 0, κ 0 1 / 3; 3 * κ 1 0, κ 1 1]

/-- The determinant of `unkapMat κ` is the determinant of `κ`. -/
theorem unkapMat_det (κ : Matrix (Fin 2) (Fin 2) ℤ) (h3 : (3 : ℤ) ∣ κ 0 1) :
    (unkapMat κ).det = κ.det := by
  obtain ⟨c, hc⟩ := h3
  have e : κ 0 1 / 3 = c := by omega
  rw [unkapMat, Matrix.det_fin_two_of, Matrix.det_fin_two, e, hc]
  ring

/-- **The preimage under `κ`** of a matrix `κ` with `3 ∣ κ₀₁` and `κ₁₁ ≡ 1 mod 3`: the element
`[[κ₀₀, κ₀₁/3], [3 κ₁₀, κ₁₁]]` of `Γ₁'(3)`. -/
def unkap (κ : GL2Z) (h3 : (3 : ℤ) ∣ κ.val 0 1) (h1 : ((κ.val 1 1 : ℤ) : ZMod 3) = 1) :
    binaryArithmeticLevel :=
  have hM : IsUnit (unkapMat κ.val).det := by
    rw [unkapMat_det _ h3]
    exact (Matrix.isUnit_iff_isUnit_det _).mp κ.isUnit
  ⟨⟨unkapMat κ.val, (unkapMat κ.val)⁻¹, Matrix.mul_nonsing_inv _ hM, Matrix.nonsing_inv_mul _ hM⟩,
    by
      apply (mem_binaryArithmeticLevel_iff _).mpr
      intro column
      have h3z : (3 : ZMod 3) = 0 := by decide
      fin_cases column
      · simp [unkapMat, h3z]
      · simpa [unkapMat] using h1⟩

/-- `κ` of the preimage is the matrix. -/
theorem kap_unkap (κ : GL2Z) (h3 : (3 : ℤ) ∣ κ.val 0 1) (h1 : ((κ.val 1 1 : ℤ) : ZMod 3) = 1) :
    kap (unkap κ h3 h1) = κ := by
  apply Units.ext
  rw [kap_val]
  have e1 : 3 * (κ.val 0 1 / 3) = κ.val 0 1 := by omega
  have e2 : 3 * κ.val 1 0 / 3 = κ.val 1 0 := by omega
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unkap, kapMat, unkapMat, e1, e2]

/-- The upper-right entry of `γ^{-T}` is divisible by `3`. -/
theorem alpha_dvd (γ : binaryArithmeticLevel) : (3 : ℤ) ∣ (invT γ.1).val 0 1 :=
  three_dvd_of_cast_zero (level_row γ⁻¹).1

/-- The lower-right entry of `γ^{-T}` is `1` modulo `3`. -/
theorem alpha_one (γ : binaryArithmeticLevel) : (((invT γ.1).val 1 1 : ℤ) : ZMod 3) = 1 :=
  (level_row γ⁻¹).2

/-- **The involution `α(γ) = δ γ^{-T} δ⁻¹` of `Γ₁'(3)`** which exchanges the two cusps. -/
def alpha (γ : binaryArithmeticLevel) : binaryArithmeticLevel :=
  unkap (invT γ.1) (alpha_dvd γ) (alpha_one γ)

/-- `κ(α(γ)) = γ^{-T}`. -/
theorem kap_alpha (γ : binaryArithmeticLevel) : kap (alpha γ) = invT γ.1 :=
  kap_unkap _ _ _

/-- `κ(L) = (T^{-T})⁻¹`. -/
theorem kap_lower_one : kap (lower 1) = (invT (upper 1).val)⁻¹ := by
  apply Units.ext
  rw [invT_inv_val, kap_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kapMat, upper, lower]

/-- `κ(T) = (L^{-T})⁻¹`. -/
theorem kap_upper_one : kap (upper 1) = (invT (lower 1).val)⁻¹ := by
  apply Units.ext
  rw [invT_inv_val, kap_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kapMat, upper, lower]

/-- `α(T) = L⁻¹`. -/
theorem alpha_upper : alpha (upper 1) = (lower 1)⁻¹ := by
  refine kap_injective ?_
  rw [map_inv, kap_lower_one, inv_inv]
  exact kap_alpha (upper 1)

/-- `α(L) = T⁻¹`. -/
theorem alpha_lower : alpha (lower 1) = (upper 1)⁻¹ := by
  refine kap_injective ?_
  rw [map_inv, kap_upper_one, inv_inv]
  exact kap_alpha (lower 1)

/-- The Levi lemma in terms of the Levi elements of the line: `Pg 0 (α γ) 1 = diag(γ^{-T}, 1)`. -/
theorem Pg_alpha (γ : binaryArithmeticLevel) : Pg 0 (alpha γ) 1 = leviHom (invT γ.1) := by
  rw [Pg_zero_eq, kap_alpha]
  rfl

/-- The arithmetic Levi element of a product. -/
theorem arithmeticLevi_mul (a b : GL2Z) :
    arithmeticLevi (a * b) = arithmeticLevi a * arithmeticLevi b :=
  map_mul leviHom a b

/-- **Conjugation of the Levi element by `τ`**: `τ P(0, κ(α γ), 1) τ⁻¹ = φ(diag(1, γ))`. -/
theorem tau_levi (γ : binaryArithmeticLevel) :
    tauF * Pg 0 (alpha γ) 1 * tauF⁻¹ = dualInvolution (Kostant.badLevi γ) := by
  have h1 := badFrame_conj_levi γ
  have h2 : dualInvolution (Kostant.badLevi γ) =
      badFrame * arithmeticLevi (badDualLevi γ) * badFrame⁻¹ := by
    rw [← h1]
    group
  have h3 : arithmeticLevi (badDualLevi γ) = swapQ * leviHom (invT γ.1) * swapQ := by
    unfold badDualLevi
    rw [arithmeticLevi_mul, arithmeticLevi_mul]
    rfl
  have hqq := swapQ_mul_self
  rw [h2, h3, Pg_alpha, badFrame_eq]
  have e : tauF * swapQ * (swapQ * leviHom (invT γ.1) * swapQ) * (tauF * swapQ)⁻¹ =
      tauF * (swapQ * swapQ) * leviHom (invT γ.1) * (swapQ * swapQ⁻¹) * tauF⁻¹ := by
    group
  rw [e, hqq, mul_inv_cancel]
  group

/-! ### The cusp flag -/

/-- `q` lies in the arithmetic level. -/
theorem swapQ_mem_level : swapQ ∈ rationalLevel :=
  (Subgroup.mem_inf.mp (arithmeticLevi_identityPlane swapZ)).1

/-- **`q` carries the reference good-plane cusp flag to the dual plane of the bad line.** -/
theorem swapQ_smul_cuspFlag :
    swapQ • cuspFlag .plane true = (QuotientGroup.mk longWeyl : Flags .plane) := by
  rw [cuspFlag_eq]
  change (QuotientGroup.mk (swapQ * gF) : Flags .plane) = QuotientGroup.mk longWeyl
  rw [QuotientGroup.eq]
  refine ⟨?_, ?_⟩ <;>
    rw [_root_.mul_inv_rev, swapQ_inv, Units.val_mul, Units.val_mul, gF_inv_val, swapQ_val] <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, longWeyl, longWeylMatrix]

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad

end
