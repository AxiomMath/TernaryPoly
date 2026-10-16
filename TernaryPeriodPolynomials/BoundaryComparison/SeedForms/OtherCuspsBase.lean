module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.AntiHolomorphic

@[expose] public section


/-!
# `g5_levelOne` at the other plane cusps: integrality of `b_F` and Levi modularity of `H_g`, `H'_g`

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 (`ar:lem:seed`) at the plane cusps `h⁻¹ P h` ("rationally conjugate the other plane cusps to `P`").

* `bFin_integral`: `b_F f` is the image of an element of `GL₂(Ẑ)` whenever `f ∈ GL₃(Ẑ)` (generalizes `bFin_one_integral`); `integralFinite_integral`, `bF_rational_integral`: the finite image of an integral matrix is integral.
* `hmod_H_of_bF`, `hmod_H'_of_bF`: Levi modularity of `F(1·b_F G)` and `F(J·b_F G)` for the group `Γ_P = Γ(N) ∩ P(ℤ)`, `3 ∣ N`, for every adele `G` with integral `b_F G` (the proofs of `hmod_H`, `hmod_H'` with the base `B` arbitrary).
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

/-- **`b_F` of an integral finite adele is integral** (generalizes `bFin_one_integral`, the case `f = 1`). -/
theorem bFin_integral {f : FiniteGL}
    (hf : ∃ k₀ : GeneralLinearGroup (Fin 3) IntegralAdeles, f = GeneralLinearGroup.map integralEmbedding k₀) :
    ∃ B : GeneralLinearGroup (Fin 2) IntegralAdeles,
      bFin f = atFinite (GeneralLinearGroup.map integralEmbedding B) := by
  obtain ⟨k₀, hk₀⟩ := hf
  obtain ⟨k, hk⟩ := finitePlaneParabolic_spec f
  set p := finitePlaneParabolic f with hp
  have hpmem := finitePlaneParabolic_mem f
  have hpk : p = GeneralLinearGroup.map integralEmbedding (k₀ * k⁻¹) := by
    have h1 : p = p * GeneralLinearGroup.map integralEmbedding k * GeneralLinearGroup.map integralEmbedding k⁻¹ := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [h1, ← hk, hk₀, ← map_mul]
  have hmem : GeneralLinearGroup.map integralEmbedding (k₀ * k⁻¹) ∈ planeParabolic FiniteAdeles := hpk ▸ hpmem
  have hkk : k₀ * k⁻¹ ∈ planeParabolic IntegralAdeles := integral_mem_planeParabolic hmem
  refine ⟨planeBlockGL (k₀ * k⁻¹) hkk, ?_⟩
  unfold bFin
  rw [planeBlockGL_congr hpk (finitePlaneParabolic_mem f) hmem, planeBlockGL_map integralEmbedding (k₀ * k⁻¹) hkk hmem]

/-- The finite image of an integral matrix is integral. -/
theorem integralFinite_integral (γ : IntegralGL) :
    ∃ k₀ : GeneralLinearGroup (Fin 3) IntegralAdeles,
      integralFinite γ = GeneralLinearGroup.map integralEmbedding k₀ := by
  refine ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ, ?_⟩
  apply Units.ext
  ext i j
  simp [integralFinite, rationalFinite, integralRational, GeneralLinearGroup.map_apply]

/-- `b_F g` is integral for `g` the diagonal image of an integral matrix. -/
theorem bF_rational_integral (γ : IntegralGL) :
    ∃ B : GeneralLinearGroup (Fin 2) IntegralAdeles,
      bF (rationalGroup (integralRational γ)) = atFinite (GeneralLinearGroup.map integralEmbedding B) := by
  obtain ⟨k₀, hk₀⟩ := integralFinite_integral γ
  exact bFin_integral ⟨k₀, hk₀⟩

open TernaryPeriodPolynomials.PlaneEisensteinContinuation in
/-- **Levi modularity of `H_g = F(1 · b_F g)`** for every `g` with `b_F g` integral. -/
theorem hmod_H_of_bF (cusp : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (hweight : 2 * halfWeight = -((n : ℤ) + 3))
    (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (hfix : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (N : ℕ) (h3 : 3 ∣ N) (G : AdelicGL)
    (hB : ∃ B : GeneralLinearGroup (Fin 2) IntegralAdeles, bF G = atFinite (GeneralLinearGroup.map integralEmbedding B))
    (g : ↥(gammaNP N)) (z : ℂ) (hz : 0 < z.im) :
    cuspScalarWeightedRealization cusp halfWeight vector (1 * bF G) (mob ((gammaNPlaneData N).lam g) z) =
      dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) *
        cuspScalarWeightedRealization cusp halfWeight vector (1 * bF G) z := by
  obtain ⟨B, hB⟩ := hB
  have hb : (1 * bF G : BinaryAdelicGL) = atInfinity 1 * atFinite (GeneralLinearGroup.map integralEmbedding B) := by
    rw [hB, atInfinity_one_bin]
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
/-- **Levi modularity of `H'_g = F(J · b_F g)`** for every `g` with `b_F g` integral. -/
theorem hmod_H'_of_bF (cusp : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (hweight : 2 * halfWeight = -((n : ℤ) + 3))
    (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (hfix : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (N : ℕ) (h3 : 3 ∣ N) (G : AdelicGL)
    (hB : ∃ B : GeneralLinearGroup (Fin 2) IntegralAdeles, bF G = atFinite (GeneralLinearGroup.map integralEmbedding B))
    (g : ↥(gammaNP N)) (z : ℂ) (hz : 0 < z.im) :
    cuspScalarWeightedRealization cusp halfWeight vector (atInfinity UpperHalfPlane.J * bF G)
        (mob ((gammaNPlaneData N).lam g) z) =
      dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) *
        cuspScalarWeightedRealization cusp halfWeight vector (atInfinity UpperHalfPlane.J * bF G) z := by
  obtain ⟨B, hB⟩ := hB
  have hb : (atInfinity UpperHalfPlane.J * bF G : BinaryAdelicGL) =
      atInfinity UpperHalfPlane.J * atFinite (GeneralLinearGroup.map integralEmbedding B) := by
    rw [hB]
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
