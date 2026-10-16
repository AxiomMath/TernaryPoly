module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationBasis

@[expose] public section


/-!
# A rotation-invariant cuspidal polynomial cochain vanishes under the weight gap

Let `v` be a cuspidal polynomial-valued function (`BinaryValues σ n v`) fixed by the twisted action
of every rotation `binaryRotations a`.  In the rotation eigenbasis `binaryRotationBasis (n + 1)`
of `Sym^{n+1}(ℂ²)* ⊗ det⁻¹`, the coordinate `ε` of `v` is realized by a vector `u_ε` of `σ`, and
the invariance of `v` says that `σ(atInfinity (binaryRotations a))` acts on `u_ε` through the
character `a ↦ a ^ (ε₀ - ε₁)` with `|ε₀ - ε₁| ≤ n + 1`.  The weight gap then forces
`u_ε = 0`, hence `v = 0`.  Consequently a cochain `α` vanishing on the orthogonal group and
not identically zero is not the coboundary of a cuspidal polynomial-valued function.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers (binaryRotations
  binaryRotationBasis binaryRotationBasis_coefficient BinaryHomogeneousExponent
  binaryHomogeneousExponent_sum binaryCuspidalValues binarySmoothCoordinate
  binarySmoothCoordinate_realize binary_normalizingFactor_eq binaryRotationMatrix_det)

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-- The eigenvalue of the rotation `binaryRotations a` on the basis vector `ε` of
`binaryRotationBasis`. -/
def rotationEigenvalue (a : Circle) {d : ℕ} (ε : BinaryHomogeneousExponent d) : ℂ :=
  ((a : ℂ)⁻¹) ^ ε.val 0 * (a : ℂ) ^ ε.val 1

/-- A point of the unit circle is nonzero as a complex number. -/
theorem circle_coe_ne_zero (a : Circle) : (a : ℂ) ≠ 0 := by
  intro h
  have h1 := Circle.normSq_coe a
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- The inverse of the rotation eigenvalue is the character `a ^ (ε₀ - ε₁)`. -/
theorem rotationEigenvalue_inv (a : Circle) {d : ℕ} (ε : BinaryHomogeneousExponent d) :
    (rotationEigenvalue a ε)⁻¹ = (a : ℂ) ^ ((ε.val 0 : ℤ) - (ε.val 1 : ℤ)) := by
  have ha := circle_coe_ne_zero a
  apply inv_eq_of_mul_eq_one_right
  rw [rotationEigenvalue, zpow_sub₀ ha, zpow_natCast, zpow_natCast, inv_pow]
  field_simp

/-- A rotation by an element of the circle is orthogonal. -/
theorem binaryRotations_orth (a : Circle) :
    (binaryRotations a).val.transpose * (binaryRotations a).val = 1 := by
  have h := Circle.normSq_coe a
  rw [Complex.normSq_apply] at h
  have hval : (binaryRotations a).val =
      !![(a : ℂ).re, -(a : ℂ).im; (a : ℂ).im, (a : ℂ).re] := rfl
  rw [hval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]

/-- The determinant normalization of the cohomological action is trivial on rotations. -/
theorem normPower_rotation (a : Circle) (z : ℂ) :
    normPower (Matrix.GeneralLinearGroup.det (atInfinity (binaryRotations a))) z = 1 := by
  have hdet : (binaryRotations a).val.det = 1 := binaryRotationMatrix_det a
  rw [binary_normalizingFactor_eq, hdet, Real.log_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero]

/-- The coordinate of the rotation basis is an eigenfunctional of the rotation. -/
theorem coord_rotation {n : ℕ} (a : Circle) (ε : BinaryHomogeneousExponent (n + 1))
    (w : Binary.HomogeneousPoly (n + 1)) :
    (binaryRotationBasis (n + 1)).coord ε (binaryCoefficient n (binaryRotations a) w) =
      rotationEigenvalue a ε * (binaryRotationBasis (n + 1)).coord ε w := by
  classical
  have h : ((binaryRotationBasis (n + 1)).coord ε).comp (binaryCoefficient n (binaryRotations a)) =
      rotationEigenvalue a ε • (binaryRotationBasis (n + 1)).coord ε := by
    apply (binaryRotationBasis (n + 1)).ext
    intro s
    simp only [LinearMap.comp_apply, binaryRotationBasis_coefficient, map_smul,
      Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.smul_apply, smul_eq_mul]
    by_cases hs : s = ε
    · subst hs
      simp [rotationEigenvalue]
    · simp [hs]
  have h2 := LinearMap.congr_fun h w
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] using h2

/-- The vector realizing the coordinate `ε` of a rotation-invariant cuspidal cochain is an
eigenvector of the rotations, of weight `ε₀ - ε₁`. -/
theorem rotation_eigenvector {σ : CuspidalRepresentation} {n : ℕ}
    (v : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (hv : BinaryValues σ n v)
    (hfix : ∀ (a : Circle) x, binaryCohomologicalAction n (binaryRotations a) v x = v x)
    (ε : BinaryHomogeneousExponent (n + 1)) (a : Circle) :
    σ.π (atInfinity (binaryRotations a))
        (binarySmoothCoordinate σ ((binaryRotationBasis (n + 1)).coord ε) ⟨v, hv⟩).val =
      (a : ℂ) ^ ((ε.val 0 : ℤ) - (ε.val 1 : ℤ)) •
        (binarySmoothCoordinate σ ((binaryRotationBasis (n + 1)).coord ε) ⟨v, hv⟩).val := by
  set u := binarySmoothCoordinate σ ((binaryRotationBasis (n + 1)).coord ε) ⟨v, hv⟩
  have ha := circle_coe_ne_zero a
  have hreal : ∀ x, σ.realize u x = (binaryRotationBasis (n + 1)).coord ε (v x) :=
    fun x =>
    binarySmoothCoordinate_realize σ ((binaryRotationBasis (n + 1)).coord ε) ⟨v, hv⟩ x
  have hstep : ∀ x, v x =
      binaryCoefficient n (binaryRotations a) (v (x * atInfinity (binaryRotations a))) := by
    intro x
    have h := hfix a x
    rw [binaryCohomologicalAction, normPower_rotation, one_smul] at h
    exact h.symm
  have heq : u = rotationEigenvalue a ε •
      (⟨σ.π (atInfinity (binaryRotations a)) u.val, σ.smooth_stable _ _ u.property⟩ :
        σ.smooth) := by
    apply σ.injective
    funext x
    rw [map_smul, Pi.smul_apply, σ.equivariant, hreal, hreal, hstep x, coord_rotation,
      smul_eq_mul]
  have hval : u.val = rotationEigenvalue a ε • σ.π (atInfinity (binaryRotations a)) u.val :=
    congrArg Subtype.val heq
  have hne0 : rotationEigenvalue a ε ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha)) (pow_ne_zero _ ha)
  rw [← rotationEigenvalue_inv a ε]
  calc σ.π (atInfinity (binaryRotations a)) u.val
      = (rotationEigenvalue a ε)⁻¹ •
          (rotationEigenvalue a ε • σ.π (atInfinity (binaryRotations a)) u.val) := by
        rw [smul_smul, inv_mul_cancel₀ hne0, one_smul]
    _ = (rotationEigenvalue a ε)⁻¹ • u.val := by rw [← hval]

/-- **A nonzero cochain vanishing on the orthogonal group is not the coboundary of a cuspidal
polynomial-valued function when the representation has the weight gap.** -/
theorem not_coboundary_of_weightGap_alpha {σ : CuspidalRepresentation} {n : ℕ}
    (α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (orth : ∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0)
    (gap : WeightGap σ n) (hne : ∃ g x, α g x ≠ 0) :
    ¬ ∃ v : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      BinaryValues σ n v ∧
        ∀ g x, α g x = binaryCohomologicalAction n g v x - v x := by
  rintro ⟨v, hv, hcob⟩
  have hfix : ∀ (a : Circle) x, binaryCohomologicalAction n (binaryRotations a) v x = v x := by
    intro a x
    have h0 := hcob (binaryRotations a) x
    rw [orth (binaryRotations a) (binaryRotations_orth a) x] at h0
    exact sub_eq_zero.mp h0.symm
  have hzero : ∀ (ε : BinaryHomogeneousExponent (n + 1)) x,
      (binaryRotationBasis (n + 1)).coord ε (v x) = 0 := by
    intro ε x
    have hsum := binaryHomogeneousExponent_sum ε
    have hlt : |((ε.val 0 : ℤ) - (ε.val 1 : ℤ))| < (n : ℤ) + 3 := by
      rw [abs_lt]
      constructor <;> omega
    have hu := gap _ _ (fun a => rotation_eigenvector v hv hfix ε a) hlt
    have hu0 : binarySmoothCoordinate σ ((binaryRotationBasis (n + 1)).coord ε) ⟨v, hv⟩ = 0 :=
      Subtype.ext hu
    have h := binarySmoothCoordinate_realize σ ((binaryRotationBasis (n + 1)).coord ε) ⟨v, hv⟩ x
    rw [hu0, map_zero] at h
    simpa using h.symm
  have hv0 : ∀ x, v x = 0 := by
    intro x
    apply (binaryRotationBasis (n + 1)).ext_elem
    intro ε
    simpa [Module.Basis.coord_apply] using hzero ε x
  obtain ⟨g, x, hgx⟩ := hne
  apply hgx
  rw [hcob g x]
  simp [binaryCohomologicalAction, hv0]

end TernaryPeriodPolynomials.Automorphic.Constituent
