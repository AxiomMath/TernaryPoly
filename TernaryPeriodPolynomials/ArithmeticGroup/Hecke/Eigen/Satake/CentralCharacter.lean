module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Values

@[expose] public section


/-!
# Scalars act through the central character

If a cuspidal representation has a nonzero smooth vector, every scalar matrix `t · 1` acts on the
whole Hilbert space by the central character value `ω(t)`. This uses Schur's lemma
(`cuspidal_schur`) and injectivity of the realization.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

theorem scalar_central (t : Adelesˣ) (g : BinaryAdelicGL) :
    GeneralLinearGroup.scalar (Fin 2) t * g = g * GeneralLinearGroup.scalar (Fin 2) t :=
  Matrix.GeneralLinearGroup.scalar_commute t g

/-- **Scalars act by the central character.** -/
theorem pi_scalar (σ : CuspidalRepresentation) (t : Adelesˣ)
    (h : ∃ v ∈ σ.smooth, v ≠ 0) (v : σ.H) :
    σ.π (GeneralLinearGroup.scalar (Fin 2) t) v = σ.centralCharacter t • v := by
  set z := GeneralLinearGroup.scalar (Fin 2) t
  obtain ⟨c, hc⟩ := cuspidal_schur σ (cuspOperator σ z) (fun g w => by
    rw [cuspOperator_apply, cuspOperator_apply, ← Module.End.mul_apply, ← map_mul,
      scalar_central, map_mul, Module.End.mul_apply])
  obtain ⟨v₀, hv₀, hne⟩ := h
  have hc' : ∀ w, σ.π z w = c • w := fun w => by rw [← cuspOperator_apply]; exact hc w
  -- compare realizations
  have hsub : (⟨σ.π z v₀, σ.smooth_stable z v₀ hv₀⟩ : σ.smooth) = c • ⟨v₀, hv₀⟩ :=
    Subtype.ext (by simp only [SetLike.val_smul]; exact hc' v₀)
  have hreal : ∀ x, c * σ.realize ⟨v₀, hv₀⟩ x = σ.centralCharacter t * σ.realize ⟨v₀, hv₀⟩ x := by
    intro x
    have e := σ.equivariant z ⟨v₀, hv₀⟩ x
    rw [hsub, map_smul, Pi.smul_apply, smul_eq_mul] at e
    rw [e, ← scalar_central, σ.central]
  have hnz : σ.realize ⟨v₀, hv₀⟩ ≠ 0 := by
    intro h0
    apply hne
    have := σ.injective (h0.trans (map_zero σ.realize).symm)
    exact congrArg Subtype.val this
  obtain ⟨x, hx⟩ : ∃ x, σ.realize ⟨v₀, hv₀⟩ x ≠ 0 := by
    by_contra hall
    exact hnz (funext fun x => not_not.mp (fun hx => hall ⟨x, hx⟩))
  have hcz : c = σ.centralCharacter t := mul_right_cancel₀ hx (hreal x)
  rw [hc' v, hcz]

variable {p : ℕ}

theorem Bo_pScalar2_entry (hp : p.Prime) (i j : Fin 2) :
    (Bo (pScalar2 hp)).val i j = if i = j then (unitAway (unitF (pUnit hp))).val else 0 := by
  apply finiteAdele_ext
  intro v
  by_cases hv : v = placeThree
  · subst hv
    have h3 : finiteEvaluation placeThree ((Bo (pScalar2 hp)).val i j) =
        (1 : Matrix (Fin 2) (Fin 2) _) i j :=
      congrArg (fun M : GeneralLinearGroup (Fin 2) _ => M.val i j) (glAway2_three (glF (pScalar2 hp)))
    rw [h3]
    split_ifs with hij
    · subst hij
      rw [Matrix.one_apply_eq]
      exact (adeleAway_three _ _).symm
    · rw [Matrix.one_apply_ne hij, map_zero]
  · have h3 : finiteEvaluation v ((Bo (pScalar2 hp)).val i j) =
        finiteEvaluation v ((glF (pScalar2 hp)).val i j) :=
      congrArg (fun M : GeneralLinearGroup (Fin 2) _ => M.val i j)
        (glAway2_away (glF (pScalar2 hp)) hv)
    rw [h3]
    change finiteEvaluation v (algebraMap ℚ FiniteAdeles ((pScalar2 hp).val i j)) = _
    rw [pScalar2_val]
    split_ifs with hij
    · subst hij
      change _ = finiteEvaluation v (adeleAway _ 1)
      rw [adeleAway_away _ _ hv]
      simp [pUnit_val]
    · simp [Matrix.one_apply_ne hij]

/-- The finite away-from-three part of `p · 1` is the scalar of `sAd p`. -/
theorem atFinite_Bo_pScalar2 (hp : p.Prime) :
    atFinite (Bo (pScalar2 hp)) = GeneralLinearGroup.scalar (Fin 2) (sAd (pUnit hp)) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · change ((1 : GeneralLinearGroup (Fin 2) ℝ).val i j) =
      ((GeneralLinearGroup.scalar (Fin 2) (sAd (pUnit hp))).val i j).1
    by_cases hij : i = j
    · subst hij
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, sAd,
        finiteAdeleUnit]
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, hij]
  · change (Bo (pScalar2 hp)).val i j =
      ((GeneralLinearGroup.scalar (Fin 2) (sAd (pUnit hp))).val i j).2
    rw [Bo_pScalar2_entry]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, sAd,
        finiteAdeleUnit]
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, hij]

/-- **The Hecke scalar of `p · 1` is the central character.** -/
theorem omega_pScalar2 (σ : CuspidalRepresentation) (hp : p.Prime)
    (h : ∃ v ∈ σ.smooth, v ≠ 0) [hn : Nontrivial (fixedVectors σ K3)] :
    omega σ (Bo (pScalar2 hp)) = σ.centralCharacter (sAd (pUnit hp)) := by
  have hT : ∀ w, compression σ K3 (atFinite (Bo (pScalar2 hp))) w =
      σ.centralCharacter (sAd (pUnit hp)) • w := by
    intro w
    apply ext_inner_right ℂ
    intro u
    rw [inner_compression, atFinite_Bo_pScalar2, pi_scalar σ _ h, Submodule.coe_inner,
      Submodule.coe_smul]
  obtain ⟨w, hw⟩ := exists_ne (0 : fixedVectors σ K3)
  have hs := omega_spec σ (B := Bo (pScalar2 hp)) (glAway2_mem (glF (pScalar2 hp))) w
  rw [hT w] at hs
  exact (smul_left_injective ℂ hw hs).symm

theorem det_pScalar2 (hp : p.Prime) : GeneralLinearGroup.det (pScalar2 hp) = pUnit hp ^ 2 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, pScalar2_val, det_smul, det_one,
    Fintype.card_fin, mul_one, Units.val_pow_eq_pow_val, pUnit_val]

theorem normPower_sAd_prime_sq (hp : p.Prime) (h3 : p ≠ 3) (z : ℂ) :
    normPower (sAd (pUnit hp ^ 2)) z = Complex.exp (-(2 * z * (Real.log p : ℂ))) := by
  have h1 : Int3 ((pUnit hp ^ 2 : ℚˣ) : ℚ) := by
    rw [Units.val_pow_eq_pow_val, pow_two]
    exact Int3_mul (Int3_prime hp) (Int3_prime hp)
  have h2 : Int3 ((pUnit hp ^ 2 : ℚˣ) : ℚ)⁻¹ := by
    rw [Units.val_pow_eq_pow_val, pow_two, mul_inv]
    exact Int3_mul (Int3_prime_inv hp h3) (Int3_prime_inv hp h3)
  rw [normPower, adeleNorm_sAd h1 h2, Units.val_pow_eq_pow_val, pUnit_val]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [show |(((p : ℚ) ^ 2 : ℚ) : ℝ)|⁻¹ = ((p : ℝ) ^ 2)⁻¹ by push_cast; rw [abs_of_pos (by positivity)],
    Real.log_inv, Real.log_pow]
  push_cast
  ring_nf

/-- **The explicit central plane eigenvalue.** -/
theorem central_plane_eigenvalue_explicit {n : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = pScalar hp)
    (hsm : ∃ v ∈ D.cusp.smooth, v ≠ 0) [Nontrivial (fixedVectors D.cusp K3)] :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (D.chi.toMonoidHom (sAd (pUnit hp)) *
          Complex.exp (2 * inductionExponent .plane cohomologicalPoint * (Real.log p : ℂ)) *
          (Complex.exp (-(2 * planeExp n * (Real.log p : ℂ))) *
            D.cusp.centralCharacter (sAd (pUnit hp)))) * f g := by
  intro f hf g
  rw [central_plane_eigenvalue D hp t ht hg f hf g, ratPlaneWeight_prime_scalar D hp h3,
    omega_pScalar2 D.cusp hp hsm, det_atFinite_Bo, det_pScalar2, normPower_sAd_prime_sq hp h3]

theorem Bo_one : Bo 1 = 1 := by
  have h := Bo_mul 1 1
  rw [mul_one] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem sAd_one : sAd 1 = 1 := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · change adeleAway ((unitF 1 : FiniteAdelesˣ) : FiniteAdeles) 1 = 1
    rw [show (unitF 1 : FiniteAdelesˣ) = 1 from map_one (Units.map _), Units.val_one]
    apply finiteAdele_ext
    intro v
    by_cases hv : v = placeThree
    · subst hv; rw [adeleAway_three, map_one]
    · rw [adeleAway_away _ _ hv]

theorem normPower_one (z : ℂ) : normPower 1 z = 1 := by
  simp [normPower]

theorem omega_one (σ : CuspidalRepresentation) [Nontrivial (fixedVectors σ K3)] :
    omega σ 1 = 1 := by
  have hT : ∀ w, compression σ K3 (atFinite 1) w = (1 : ℂ) • w := by
    intro w
    apply ext_inner_right ℂ
    intro u
    rw [inner_compression, atFinite_one, map_one, Module.End.one_apply, one_smul, Submodule.coe_inner]
  obtain ⟨w, hw⟩ := exists_ne (0 : fixedVectors σ K3)
  have hs := omega_spec σ (B := 1) (one_mem _) w
  rw [hT w] at hs
  exact (smul_left_injective ℂ hw hs).symm

/-- **The explicit Satake form of the prime plane eigenvalue.** For `p ≠ 3`, if the
away-from-three fixed space is nontrivial, the plane eigenvalue of `diag(p,1,1)` is
`χ(sAd p) p^{2e} + (p² + p) p^{-planeExp} ω(diag(p,1))`. -/
theorem prime_plane_eigenvalue_satake {n : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors D.cusp K3)] :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (D.chi.toMonoidHom (sAd (pUnit hp)) *
            Complex.exp (2 * inductionExponent .plane cohomologicalPoint * (Real.log p : ℂ)) +
          ((p : ℂ) ^ 2 + p) * (Complex.exp (-(planeExp n * (Real.log p : ℂ))) *
            omega D.cusp (Bo (dP hp)))) * f g := by
  intro f hf g
  rw [(prime_plane_eigenvalue_explicit D hp t ht hg).2 f hf g, ratPlaneWeight_prime_scalar D hp h3,
    ratPlaneWeight_dP D hp h3, Bo_one, omega_one, atFinite_one, map_one, sAd_one, map_one,
    normPower_one, normPower_one]
  ring

/-- **The explicit Satake form of the `diag(p,p,1)` plane eigenvalue.** -/
theorem prime2_plane_eigenvalue_satake {n : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP2 hp)
    (hsm : ∃ v ∈ D.cusp.smooth, v ≠ 0) [Nontrivial (fixedVectors D.cusp K3)] :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        ((p : ℂ) ^ 2 * (Complex.exp (-(2 * planeExp n * (Real.log p : ℂ))) *
              D.cusp.centralCharacter (sAd (pUnit hp))) +
          ((p : ℂ) + 1) * (D.chi.toMonoidHom (sAd (pUnit hp)) *
            Complex.exp (2 * inductionExponent .plane cohomologicalPoint * (Real.log p : ℂ)) *
            (Complex.exp (-(planeExp n * (Real.log p : ℂ))) * omega D.cusp (Bo (dP hp))))) * f g := by
  intro f hf g
  rw [(prime2_plane_eigenvalue D hp t ht hg).2 f hf g, ratPlaneWeight_prime_scalar D hp h3]
  simp only [ratPlaneWeight, planeWeight]
  rw [sAd_one, map_one, normPower_one, det_atFinite_Bo, det_pScalar2, normPower_sAd_prime_sq hp h3,
    omega_pScalar2 D.cusp hp hsm, det_atFinite_Bo, det_dP, normPower_sAd_prime hp h3]
  ring

end TernaryPeriodPolynomials.HeckeEigen.Satake
