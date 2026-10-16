module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.KTypeSection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSpherical
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationEigenvectors

@[expose] public section


/-!
# Analytic rotation weight vectors of a nonzero smooth vector

For a nonzero smooth vector `v` of the cuspidal representation of an inducing datum `D`, some
rotation weight projection `P_ℓ v` is nonzero (Fourier completeness on the circle); it is again a
smooth vector (analytic orbit), fixed by every finite element fixing `v`, and its weight satisfies
`|ℓ| ≥ n + 3 > 0` by the cohomological weight gap.  Depending on the sign of `ℓ` the vector `P_ℓ v`
or its reflection `σ(ε) P_ℓ v` is a vector of rotation weight `-m` with `m = |ℓ| > 0`, the
convention of `KTypeSection.RotationWeight`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers (binaryRotations)
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (cuspSmoothRotationProjection cuspSmoothRotationProjection_exists_nonzero
    cohomological_smooth_projection_gap cuspRotationProjection_real_rotation
    cuspRotationProjection_finite_fixed cuspSmoothRotationProjection_apply_val
    binaryCircleRotation binaryCircleRotation_val binaryRotationPath)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## Comparison of the two rotation parametrizations -/

/-- The rotation `binaryCircleRotation` is the inverse of `binaryRotations`. -/
theorem binaryRotations_eq_circleRotation_inv (a : Circle) :
    binaryRotations a = binaryCircleRotation a⁻¹ := by
  have h : binaryCircleRotation a = (binaryRotations a)⁻¹ :=
    Units.ext (by
      rw [binaryCircleRotation_val, binaryRotations_inv_val]
      try rfl)
  rw [map_inv binaryCircleRotation a, h, inv_inv]

theorem binaryRotations_exp (θ : ℝ) :
    binaryRotations (Circle.exp θ) = binaryRotationPath (-θ) := by
  unfold binaryRotationPath
  rw [binaryRotations_eq_circleRotation_inv, Circle.exp_neg]

/-- The projection onto the weight `ℓ` rotation character, in the convention
`σ(rot a) P = a^(-ℓ) P`. -/
theorem projection_rotation (cusp : CuspidalRepresentation) (ℓ : ℤ) (v : cusp.smooth) (a : Circle) :
    cusp.π (atInfinity (binaryRotations a)) (cuspSmoothRotationProjection cusp ℓ v).val =
      ((a : ℂ) ^ (-ℓ)) • (cuspSmoothRotationProjection cusp ℓ v).val := by
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective a
  rw [binaryRotations_exp, cuspSmoothRotationProjection_apply_val,
    cuspRotationProjection_real_rotation cusp ℓ v.val (-θ)]
  congr 1
  rw [Circle.coe_exp, ← Complex.exp_int_mul]
  congr 1
  push_cast
  try ring

/-! ## From a character vector to a weight `-m` vector -/

theorem wPlus_wPlus (σ : CuspidalRepresentation) (w : σ.H) : wPlus σ (wPlus σ w) = w := by
  unfold wPlus
  rw [← rep_atInfinity_mul, binaryReflection_mul_self, rep_atInfinity_one]

theorem wPlus_zero (σ : CuspidalRepresentation) : wPlus σ (0 : σ.H) = 0 := by
  unfold wPlus
  exact map_zero _

/-- The reflection of a vector on which the rotations act by `a ↦ a^m` has rotation weight `-m`. -/
theorem rotationWeight_wPlus (σ : CuspidalRepresentation) (m : ℕ) (P : σ.H)
    (hrot : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) P = (a : ℂ) ^ (m : ℤ) • P) :
    RotationWeight σ m (wPlus σ P) := by
  intro a
  unfold wPlus
  rw [← rep_atInfinity_mul, rotation_mul_reflection, rep_atInfinity_mul,
    ← map_inv binaryRotations a, hrot a⁻¹, map_smul, Circle.coe_inv, _root_.inv_zpow, _root_.zpow_neg]

theorem exists_weight_vector_of_projection (σ : CuspidalRepresentation) (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (P : σ.H) (hP : P ∈ σ.smooth) (hP0 : P ≠ 0)
    (hrot : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) P = (a : ℂ) ^ (-ℓ) • P) :
    ∃ (m : ℕ) (w : σ.H), 0 < m ∧ w ∈ σ.smooth ∧ w ≠ 0 ∧ RotationWeight σ m w ∧
      ∀ k : BinaryFiniteGL, σ.π (atFinite k) P = P → σ.π (atFinite k) w = w := by
  rcases lt_or_gt_of_ne hℓ with hneg | hpos
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -ℓ = (m : ℤ) :=
      ⟨(-ℓ).toNat, (Int.toNat_of_nonneg (neg_nonneg.mpr hneg.le)).symm⟩
    have hℓm : ℓ = -(m : ℤ) := by omega
    subst hℓm
    refine ⟨m, wPlus σ P, ?_, wPlus_mem σ P hP, ?_, ?_, ?_⟩
    · omega
    · intro h
      apply hP0
      have h2 := wPlus_wPlus σ P
      rw [h, wPlus_zero] at h2
      exact h2.symm
    · refine rotationWeight_wPlus σ m P (fun a => ?_)
      have h := hrot a
      rwa [neg_neg] at h
    · intro k hk
      unfold wPlus
      rw [← Module.End.mul_apply, ← map_mul, atFinite_mul_atInfinity_comm, map_mul,
        Module.End.mul_apply, hk]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, ℓ = (m : ℤ) := ⟨ℓ.toNat, (Int.toNat_of_nonneg hpos.le).symm⟩
    subst hm
    refine ⟨m, P, ?_, hP, hP0, fun a => hrot a, fun k hk => hk⟩
    omega

/-- **Weight vectors.**  A nonzero smooth vector of the cuspidal representation of an inducing
datum produces a nonzero smooth vector `w` of rotation weight `-m` with `m > 0`, fixed by every
finite element that fixes the original vector. -/
theorem exists_weight_vector {n : ℕ} (D : InducingData n) (v : D.cusp.smooth) (hv : v ≠ 0) :
    ∃ (m : ℕ) (w : D.cusp.H), 0 < m ∧ w ∈ D.cusp.smooth ∧ w ≠ 0 ∧ RotationWeight D.cusp m w ∧
      ∀ k : BinaryFiniteGL, D.cusp.π (atFinite k) v.val = v.val →
        D.cusp.π (atFinite k) w = w := by
  obtain ⟨ℓ, hℓ⟩ := cuspSmoothRotationProjection_exists_nonzero D.cusp v hv
  have gap := cohomological_smooth_projection_gap D.cohomological ℓ v hℓ
  have hℓ0 : ℓ ≠ 0 := by
    intro h0
    have habs : |(ℓ : ℝ)| = 0 := by simp [h0]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨m, w, hm, hws, hw0, hwrot, hwfix⟩ := exists_weight_vector_of_projection D.cusp ℓ hℓ0
    (cuspSmoothRotationProjection D.cusp ℓ v).val
    (cuspSmoothRotationProjection D.cusp ℓ v).property
    (fun h => hℓ (Subtype.ext h)) (projection_rotation D.cusp ℓ v)
  exact ⟨m, w, hm, hws, hw0, hwrot, fun k hk => hwfix k
    (cuspRotationProjection_finite_fixed D.cusp ℓ v.val k hk)⟩

end TernaryPeriodPolynomials.SourceConstruction
