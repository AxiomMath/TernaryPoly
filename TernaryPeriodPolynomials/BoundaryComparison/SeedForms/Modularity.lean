module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarModularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PrimeReduction
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.Level
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceIdentity
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Instance
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.GammaNPlane
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.EichlerClass

@[expose] public section


/-!
# Levi modularity of the scalar functions `H = F(1 · b_F(1))`, `H' = F(J · b_F(1))` of the model's identity-plane cochain

Formalized by Claude Sonnet 5.5.

For the scalar weighted realization `F = cuspScalarWeightedRealization σ hw v` of a vector fixed by the level-3 congruence subgroup of `GL₂(Ẑ)`
(in particular a spherical one) with the rotation law of weight `2 hw = -(n+3)`:

* `cuspScalarWeightedRealization_modular_base`: modularity `F(x)(γz) = (cz+d)^{-2hw} F(x)(z)` at an ARBITRARY adelic base `x`, whenever
  `x ι_∞(γ) = ι_ℚ(γ') x ι_f(k)` with `π(ι_f k) v = v` (the generalization of `cuspScalarWeightedRealization_modular`, which is the case `x = 1`).
* `bFin_one_integral`: `b_F(1)` is the image of an element of `GL₂(Ẑ)` (it is the block of the chosen finite Iwasawa factor of `1`).
* `base_relation`, `fixed_conj`: the commutation relation and the fixedness of `ι_f(B⁻¹ γ_f⁻¹ B)`.
* `hmod_H`, `hmod_H'`: the hypotheses `hmod` of the seed class of `Γ_P = Γ(N) ∩ P(ℤ)` (`3 ∣ N`) for `H` and `H'` (the latter via
  `J γ J⁻¹ = γ'`, `conjJ`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

theorem atFinite_one_bin : atFinite (1 : BinaryFiniteGL) = 1 := by
  apply Units.ext
  funext row column
  apply Prod.ext
  · by_cases h : row = column <;> simp [atFinite, combineGL, pairMatrix, h]
  · by_cases h : row = column <;> simp [atFinite, combineGL, pairMatrix, h]

theorem atFinite_inv_bin (f : BinaryFiniteGL) : atFinite f⁻¹ = (atFinite f)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← atFinite_mul, inv_mul_cancel, atFinite_one_bin]

/-- **The base relation for the scalar realization**: for `x = ι_∞(c) ι_f(B)` and a real `γ` with `c γ = γ' c`, `γ' = ι(A')`,
`A' ∈ SL₂(ℤ)`, one has `x ι_∞(γ) = ι_ℚ(A') x ι_f(k)`, `k = B⁻¹ ι_f(A')⁻¹ B`. -/
theorem base_relation (c γ : BinaryRealGL) (A' : SL(2, ℤ)) (B : BinaryFiniteGL)
    (hcomm : c * γ = SpecialLinearGroup.mapGL ℝ A' * c) :
    atInfinity c * atFinite B * atInfinity γ =
      GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ A') * (atInfinity c * atFinite B) *
        atFinite (B⁻¹ * (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (SpecialLinearGroup.mapGL ℚ A'))⁻¹ * B) := by
  have hsplit := binaryRationalMatrix_split (SpecialLinearGroup.mapGL ℚ A')
  rw [binaryIntegral_specialLinear_real] at hsplit
  rw [hsplit]
  have e1 : atInfinity c * atInfinity γ = atInfinity (SpecialLinearGroup.mapGL ℝ A') * atInfinity c := by
    rw [← atInfinity_mul, ← atInfinity_mul, hcomm]
  have cm : ∀ (r : BinaryRealGL) (f : BinaryFiniteGL), atFinite f * atInfinity r = atInfinity r * atFinite f :=
    fun r f => (atInfinity_commute_atFinite r f).eq.symm
  simp only [atFinite_mul, atFinite_inv_bin]
  generalize GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (SpecialLinearGroup.mapGL ℚ A') = Fq
  have key : atInfinity (SpecialLinearGroup.mapGL ℝ A') * atFinite Fq * (atInfinity c * atFinite B) *
      ((atFinite B)⁻¹ * (atFinite Fq)⁻¹ * atFinite B) =
      atInfinity (SpecialLinearGroup.mapGL ℝ A') * (atFinite Fq * atInfinity c) * (atFinite Fq)⁻¹ * atFinite B := by
    group
  rw [key, cm c Fq]
  calc atInfinity c * atFinite B * atInfinity γ
      = atInfinity c * atInfinity γ * atFinite B := by rw [mul_assoc, cm, ← mul_assoc]
    _ = atInfinity (SpecialLinearGroup.mapGL ℝ A') * atInfinity c * atFinite B := by rw [e1]
    _ = _ := by group

open TernaryPeriodPolynomials.PlaneEisensteinContinuation in
/-- **The conjugate of a level-3 congruence element by `ι_f(B)`, `B ∈ GL₂(Ẑ)`, fixes a level-3-fixed vector.** -/
theorem fixed_conj (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (hfix : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (B : GeneralLinearGroup (Fin 2) IntegralAdeles) (A' : SL(2, ℤ))
    (hA' : ∀ i j, (((A' : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod 3) = (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j) :
    cusp.π (atFinite ((GeneralLinearGroup.map integralEmbedding B)⁻¹ *
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (SpecialLinearGroup.mapGL ℚ A'))⁻¹ *
      GeneralLinearGroup.map integralEmbedding B)) vector.val = vector.val := by
  have equality : GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (SpecialLinearGroup.mapGL ℚ A') =
      GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles A') := by
    apply Units.ext
    funext row column
    simp only [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe]
    change algebraMap ℚ FiniteAdeles (algebraMap ℤ ℚ (A'.val row column)) =
      integralEmbedding (algebraMap ℤ IntegralAdeles (A'.val row column))
    simp
  have hg' : GeneralLinearGroup.map integralReduction (SpecialLinearGroup.mapGL IntegralAdeles A') = 1 := by
    apply Units.ext
    ext i j
    simp only [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe,
      Units.val_one]
    change integralReduction (algebraMap ℤ IntegralAdeles (A'.val i j)) = (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j
    simpa using hA' i j
  have hk : B⁻¹ * (SpecialLinearGroup.mapGL IntegralAdeles A')⁻¹ * B ∈ BinaryLevel.integralCongruence := by
    rw [BinaryLevel.integralCongruence, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hg', inv_one, mul_one, inv_mul_cancel]
  rw [equality]
  have := hfix ⟨GeneralLinearGroup.map integralEmbedding (B⁻¹ * (SpecialLinearGroup.mapGL IntegralAdeles A')⁻¹ * B),
    ⟨_, hk, rfl⟩⟩
  simpa only [map_mul, map_inv] using this



/-- **Modularity of the scalar weighted realization at an arbitrary adelic base.**  If `x · ι_∞(γ) = ι_ℚ(γ') · x · ι_f(k)` with
`γ'` rational and `π(ι_f k) v = v`, then `F(x)(γ z) = (cz+d)^{-2 hw} F(x)(z)`. -/
theorem cuspScalarWeightedRealization_modular_base (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (base : BinaryAdelicGL) (γ : BinaryRealGL) (determinant : (GeneralLinearGroup.det γ).val = 1)
    (γ' : BinaryRationalGL) (k : BinaryFiniteGL)
    (hbase : base * atInfinity γ = GeneralLinearGroup.map rationalAdele γ' * base * atFinite k)
    (fixed : cusp.π (atFinite k) vector.val = vector.val) (point : UpperHalfPlane) :
    cuspScalarWeightedRealization cusp halfWeight vector base ((γ • point : UpperHalfPlane) : ℂ) =
      UpperHalfPlane.denom γ point ^ (-2 * halfWeight) *
        cuspScalarWeightedRealization cusp halfWeight vector base point := by
  have identity := cuspScalarAffineRealization_rotation cusp vector (2 * halfWeight) rotation base γ determinant point
  have key : cusp.realize vector (base * atInfinity (γ * binarySymmetricSection point)) =
      cuspScalarAffineRealization cusp vector base point := by
    calc cusp.realize vector (base * atInfinity (γ * binarySymmetricSection point))
        = cusp.realize vector ((base * atInfinity γ) * atInfinity (binarySymmetricSection point)) := by
          rw [atInfinity_mul, mul_assoc]
      _ = cusp.realize vector ((GeneralLinearGroup.map rationalAdele γ' * base * atFinite k) *
            atInfinity (binarySymmetricSection point)) := by rw [hbase]
      _ = cusp.realize vector (GeneralLinearGroup.map rationalAdele γ' *
            (base * atFinite k * atInfinity (binarySymmetricSection point))) := by simp only [mul_assoc]
      _ = cusp.realize vector (base * atFinite k * atInfinity (binarySymmetricSection point)) :=
          cusp.leftRational γ' vector _
      _ = cusp.realize vector ((base * atInfinity (binarySymmetricSection point)) * atFinite k) := by
          rw [mul_assoc, (atInfinity_commute_atFinite _ k).eq.symm, ← mul_assoc]
      _ = 1 * cusp.realize vector (base * atInfinity (binarySymmetricSection point)) :=
          cuspRealization_right_eigenvector cusp vector _ 1 (by simpa only [one_smul] using fixed) _
      _ = cuspScalarAffineRealization cusp vector base point := by
          rw [one_mul, cuspScalarAffineRealization, binaryUpperSectionMatrix_coe, invertibleMatrix_coe]
  rw [key] at identity
  have identity' : binaryPhaseValue γ point ^ (2 * halfWeight) *
      cuspScalarAffineRealization cusp vector base ((γ • point : UpperHalfPlane) : ℂ) =
      cuspScalarAffineRealization cusp vector base point := identity.symm
  simp only [cuspScalarWeightedRealization, Complex.real_smul]
  change (((γ • point : UpperHalfPlane).im ^ halfWeight : ℝ) : ℂ) * _ = _
  rw [binary_weighted_phase_identity _ determinant point halfWeight, mul_assoc, mul_assoc, identity']
  rfl



/-- Conjugation by the reflection `J = diag(-1, 1)` on `SL₂(ℤ)`. -/
def conjJ (A : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0, -(A : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      -(A : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

theorem mapGL_apply_int (A : SL(2, ℤ)) (i j : Fin 2) :
    ((SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      (((A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) := rfl

theorem J_mul_mapGL (A : SL(2, ℤ)) :
    UpperHalfPlane.J * SpecialLinearGroup.mapGL ℝ A = SpecialLinearGroup.mapGL ℝ (conjJ A) * UpperHalfPlane.J := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, UpperHalfPlane.val_J]
  ext i j
  have hc : ∀ i j, (((conjJ A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) = 
      (![![1, -1], ![-1, 1]] : Matrix (Fin 2) (Fin 2) ℝ) i j * (((A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjJ]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply_int, hc]
  fin_cases i <;> fin_cases j <;> simp



/-- **`b_F(1)` is integral**: the `GL₂` translation attached to the identity finite adele is the image of an element of `GL₂(Ẑ)`. -/
theorem bFin_one_integral :
    ∃ B : GeneralLinearGroup (Fin 2) IntegralAdeles,
      bFin (1 : FiniteGL) = atFinite (GeneralLinearGroup.map integralEmbedding B) := by
  obtain ⟨k, hk⟩ := finitePlaneParabolic_spec (1 : FiniteGL)
  set p := finitePlaneParabolic (1 : FiniteGL) with hp
  have hpmem := finitePlaneParabolic_mem (1 : FiniteGL)
  have hpk : p = GeneralLinearGroup.map integralEmbedding k⁻¹ := by
    have h1 : p = p * GeneralLinearGroup.map integralEmbedding k * GeneralLinearGroup.map integralEmbedding k⁻¹ := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [h1, ← hk, one_mul]
  have hmem : GeneralLinearGroup.map integralEmbedding k⁻¹ ∈ planeParabolic FiniteAdeles := hpk ▸ hpmem
  have hkk : k⁻¹ ∈ planeParabolic IntegralAdeles := integral_mem_planeParabolic hmem
  refine ⟨planeBlockGL k⁻¹ hkk, ?_⟩
  unfold bFin
  rw [planeBlockGL_congr hpk (finitePlaneParabolic_mem 1) hmem, planeBlockGL_map integralEmbedding k⁻¹ hkk hmem]


open TernaryPeriodPolynomials.PlaneEisensteinContinuation in
/-- **Modularity of the scalar weighted realization at the bases `ι_∞(c) ι_f(B)`, `B ∈ GL₂(Ẑ)`** under `A ∈ SL₂(ℤ)` with `c A c⁻¹ = A'`,
`A' ≡ 1 mod 3`, for a vector fixed by the level-3 congruence group. -/
theorem scalar_modular_levelBase (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (hfix : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (B : GeneralLinearGroup (Fin 2) IntegralAdeles) (c : BinaryRealGL) (A A' : SL(2, ℤ))
    (hcomm : c * SpecialLinearGroup.mapGL ℝ A = SpecialLinearGroup.mapGL ℝ A' * c)
    (hA' : ∀ i j, (((A' : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod 3) = (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j)
    (point : UpperHalfPlane) :
    cuspScalarWeightedRealization cusp halfWeight vector
        (atInfinity c * atFinite (GeneralLinearGroup.map integralEmbedding B))
        ((SpecialLinearGroup.mapGL ℝ A • point : UpperHalfPlane) : ℂ) =
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ A) point ^ (-2 * halfWeight) *
        cuspScalarWeightedRealization cusp halfWeight vector
          (atInfinity c * atFinite (GeneralLinearGroup.map integralEmbedding B)) point := by
  have determinant : (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ A)).val = 1 :=
    (SpecialLinearGroup.map (algebraMap ℤ ℝ) A).property
  exact cuspScalarWeightedRealization_modular_base cusp halfWeight vector rotation _ _ determinant
    (SpecialLinearGroup.mapGL ℚ A') _ (base_relation c _ A' (GeneralLinearGroup.map integralEmbedding B) hcomm)
    (fixed_conj cusp vector hfix B A' hA') point

theorem mapGL_mod3 {N : ℕ} (h3 : 3 ∣ N) {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma N) :
    ∀ i j, (((A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod 3) = (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j := by
  rw [CongruenceSubgroup.Gamma_mem] at hA
  obtain ⟨h00, h01, h10, h11⟩ := hA
  have hc : ∀ x : ℤ, (ZMod.castHom h3 (ZMod 3)) ((x : ℤ) : ZMod N) = ((x : ℤ) : ZMod 3) := fun x => by simp
  intro i j
  fin_cases i <;> fin_cases j
  · have := congrArg (ZMod.castHom h3 (ZMod 3)) h00; rw [hc, map_one] at this; simpa using this
  · have := congrArg (ZMod.castHom h3 (ZMod 3)) h01; rw [hc, map_zero] at this; simpa using this
  · have := congrArg (ZMod.castHom h3 (ZMod 3)) h10; rw [hc, map_zero] at this; simpa using this
  · have := congrArg (ZMod.castHom h3 (ZMod 3)) h11; rw [hc, map_one] at this; simpa using this

theorem conjJ_mod3 {A : SL(2, ℤ)}
    (hA : ∀ i j, (((A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod 3) = (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j) :
    ∀ i j, (((conjJ A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod 3) = (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j := by
  intro i j
  have h00 := hA 0 0; have h01 := hA 0 1; have h10 := hA 1 0; have h11 := hA 1 1
  fin_cases i <;> fin_cases j <;> simp_all [conjJ]

/-- The Levi block of an element of `Γ_P = Γ(N) ∩ P(ℤ)`, as an element of `Γ₂(N) ⊂ SL₂(ℤ)`. -/
theorem lam_eq_mapGL (N : ℕ) (g : ↥(gammaNP N)) :
    ∃ A ∈ CongruenceSubgroup.Gamma N, SpecialLinearGroup.mapGL ℝ A = (gammaNPlaneData N).lam g := by
  have := gammaNPlaneData_lam_mem N g
  obtain ⟨A, hA, he⟩ := Subgroup.mem_map.mp this
  exact ⟨A, hA, he⟩

theorem mob_mapGL (A : SL(2, ℤ)) (point : UpperHalfPlane) :
    mob (SpecialLinearGroup.mapGL ℝ A) (point : ℂ) = ((SpecialLinearGroup.mapGL ℝ A • point : UpperHalfPlane) : ℂ) := by
  have h : ((SpecialLinearGroup.mapGL ℝ A • point : UpperHalfPlane) : ℂ) =
      (((algebraMap ℤ ℝ (A 0 0) : ℝ) : ℂ) * point + (algebraMap ℤ ℝ (A 0 1) : ℝ)) /
        (((algebraMap ℤ ℝ (A 1 0) : ℝ) : ℂ) * point + (algebraMap ℤ ℝ (A 1 1) : ℝ)) :=
    UpperHalfPlane.coe_specialLinearGroup_apply A point
  rw [h]
  simp [mob, mapGL_apply_int]

theorem dnm_mapGL (A : SL(2, ℤ)) (point : UpperHalfPlane) :
    dnm (SpecialLinearGroup.mapGL ℝ A) (point : ℂ) = UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ A) point := rfl

theorem atInfinity_one_bin : atInfinity (1 : BinaryRealGL) = 1 := by
  apply Units.ext
  funext row column
  apply Prod.ext
  · by_cases h : row = column <;> simp [atInfinity, combineGL, pairMatrix, h]
  · by_cases h : row = column <;> simp [atInfinity, combineGL, pairMatrix, h]

open TernaryPeriodPolynomials.PlaneEisensteinContinuation in
/-- **Levi modularity of `H = F(1 · b_F(1))` for `Γ_P = Γ(N) ∩ P(ℤ)`** (`3 ∣ N`): for the scalar weighted realization of a level-3-fixed
vector with weight `2 hw = -(n+3)`. -/
theorem hmod_H (cusp : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (hweight : 2 * halfWeight = -((n : ℤ) + 3))
    (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (hfix : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (N : ℕ) (h3 : 3 ∣ N) (g : ↥(gammaNP N)) (z : ℂ) (hz : 0 < z.im) :
    cuspScalarWeightedRealization cusp halfWeight vector (1 * bF (1 : AdelicGL))
        (mob ((gammaNPlaneData N).lam g) z) =
      dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) *
        cuspScalarWeightedRealization cusp halfWeight vector (1 * bF (1 : AdelicGL)) z := by
  obtain ⟨B, hB⟩ := bFin_one_integral
  have hb : (1 * bF (1 : AdelicGL) : BinaryAdelicGL) = atInfinity 1 * atFinite (GeneralLinearGroup.map integralEmbedding B) := by
    rw [bF_one, hB, atInfinity_one_bin]
  obtain ⟨A, hAN, hAeq⟩ := lam_eq_mapGL N g
  rw [hb, ← hAeq]
  have key := scalar_modular_levelBase cusp halfWeight vector rotation hfix B 1 A A (by simp)
    (mapGL_mod3 h3 hAN) ⟨z, hz⟩
  rw [← mob_mapGL] at key
  rw [show dnm (SpecialLinearGroup.mapGL ℝ A) z = UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ A) (⟨z, hz⟩ : UpperHalfPlane) from rfl]
  have hw' : -2 * halfWeight = ((n + 3 : ℕ) : ℤ) := by push_cast; omega
  rw [hw', zpow_natCast] at key
  exact key

open TernaryPeriodPolynomials.PlaneEisensteinContinuation in
/-- **Levi modularity of the reflected scalar `H' = F(J · b_F(1))`.** -/
theorem hmod_H' (cusp : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (hweight : 2 * halfWeight = -((n : ℤ) + 3))
    (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (hfix : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (N : ℕ) (h3 : 3 ∣ N) (g : ↥(gammaNP N)) (z : ℂ) (hz : 0 < z.im) :
    cuspScalarWeightedRealization cusp halfWeight vector (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))
        (mob ((gammaNPlaneData N).lam g) z) =
      dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) *
        cuspScalarWeightedRealization cusp halfWeight vector (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)) z := by
  obtain ⟨B, hB⟩ := bFin_one_integral
  have hb : (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL) : BinaryAdelicGL) =
      atInfinity UpperHalfPlane.J * atFinite (GeneralLinearGroup.map integralEmbedding B) := by
    rw [bF_one, hB]
  obtain ⟨A, hAN, hAeq⟩ := lam_eq_mapGL N g
  rw [hb, ← hAeq]
  have key := scalar_modular_levelBase cusp halfWeight vector rotation hfix B UpperHalfPlane.J A (conjJ A)
    (J_mul_mapGL A) (conjJ_mod3 (mapGL_mod3 h3 hAN)) ⟨z, hz⟩
  rw [← mob_mapGL] at key
  rw [show dnm (SpecialLinearGroup.mapGL ℝ A) z = UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ A) (⟨z, hz⟩ : UpperHalfPlane) from rfl]
  have hw' : -2 * halfWeight = ((n + 3 : ℕ) : ℤ) := by push_cast; omega
  rw [hw', zpow_natCast] at key
  exact key

end TernaryPeriodPolynomials.Argument.FormSeedBridge
