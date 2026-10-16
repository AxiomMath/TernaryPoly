module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Coefficients
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.DualJ.Jmath

@[expose] public section


open MvPolynomial Matrix

/-!
# The target model of `E*` (`E ∘ dualInvolution`, apolar `dualPairing`) and its comparison with the `ȷ`-model

Formalized by Claude Sonnet 5.5.

The targets encode `E*` as `E ∘ dualInvolution`
(`dualInvolution g = levelScale · g^{-T} · levelScale⁻¹`) with the apolar pairing `dualPairing`.  Here:

* `dualPairing_nondegenerate_right`: `dualPairing` is nondegenerate in the second slot too (symmetry of the apolar pairing);
* `thetaModelEquiv : E ≃ₗ E*`, `w ↦ (v ↦ dualPairing v w)`; `thetaModel_equivariant`: `Θ(ρ_χ(φ g) w) = ρ_χ(g)^∨ Θ(w)` (with the character scalar
  of `dualPairing_invariant`); `thetaModelEquiv_eval`: it carries `dualPairing` to the evaluation pairing `E ⊗ E* → ℂ`;
* comparison with the `ȷ`-model of `DualCoefficients`: `factorial_mul_dualIso : n! · (dualIso f)(h) = ⟨f(J X), h⟩_apolar`,
  `dualPairing_eq_dualIso`, `thetaModel_eq_dualIso` (the two identifications of `E*` differ by the fixed coordinate change `J · levelScale` and the scalar
  `n!`), and `jGL_complexify_eq_conj : ȷ = Ad(J a⁻¹) ∘ dualInvolution` over `ℂ` (from `FacePairingFull.DualJ.jmath_eq_conj`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open GeneralEisenstein TernaryPeriodPolynomials.Duality

/-! ### The apolar pairing is symmetric; `dualPairing` is nondegenerate in the second slot -/

theorem apolarPoly_comm (f k : Poly) : apolarPoly f k = apolarPoly k f := by
  rw [apolarPoly_apply, apolarPoly_apply, ← apolarSum, ← apolarSum,
    apolarSum_eq_of_subset f k (Finset.subset_union_left (s₂ := k.support)),
    apolarSum_eq_of_subset k f (Finset.subset_union_right (s₁ := f.support))]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem apolar_comm (n : ℕ) (f k : HomogeneousPoly n) : apolar n f k = apolar n k f := by
  rw [apolar_apply, apolar_apply]
  exact apolarPoly_comm _ _

theorem dualPairing_nondegenerate_right {n : ℕ} (w : HomogeneousPoly n)
    (h : ∀ v, dualPairing n v w = 0) : w = 0 := by
  have h1 : homogeneousSubstitute n complexLevelScale w = 0 := by
    refine apolar_nondegenerate _ fun v => ?_
    rw [apolar_comm, ← dualPairing_apply]
    exact h v
  have hw : homogeneousSubstitute n ((complexify levelScale)⁻¹ : GL3)
      (homogeneousSubstitute n complexLevelScale w) = w := by
    apply Subtype.ext
    rw [homogeneousSubstitute_coe, homogeneousSubstitute_coe, ← AlgHom.comp_apply, substitute_comp,
      complexLevelScale, Units.mul_inv, substitute_one, AlgHom.id_apply]
  rw [← hw, h1, map_zero]

/-! ### The model `E ∘ φ ≅ E*` through `dualPairing` -/

/-- **The model isomorphism** `Θ : E ∘ φ → E*`, `w ↦ (v ↦ dualPairing v w)`. -/
def thetaModel (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] Module.Dual ℂ (HomogeneousPoly n) := (dualPairing n).flip

theorem thetaModel_apply (n : ℕ) (w v : HomogeneousPoly n) : thetaModel n w v = dualPairing n v w := rfl

theorem thetaModel_injective (n : ℕ) : Function.Injective (thetaModel n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  exact dualPairing_nondegenerate_right w fun v => by
    have := LinearMap.congr_fun hw v
    simpa [thetaModel_apply] using this

/-- `Θ` is a linear isomorphism `E ≃ E*` (nondegeneracy and equal dimensions). -/
def thetaModelEquiv (n : ℕ) : HomogeneousPoly n ≃ₗ[ℂ] Module.Dual ℂ (HomogeneousPoly n) :=
  LinearEquiv.ofBijective (thetaModel n) ⟨thetaModel_injective n,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℂ) (V := HomogeneousPoly n)).symm).1 (thetaModel_injective n)⟩

/-- **The evaluation pairing `E ⊗ E* → ℂ` carries `dualPairing` to the evaluation**: `ev(v, Θ w) = dualPairing v w`. -/
theorem thetaModelEquiv_eval (n : ℕ) (v w : HomogeneousPoly n) :
    (thetaModelEquiv n w) v = dualPairing n v w := rfl

/-- **Equivariance of the model isomorphism** (`E ∘ φ`, twisted by the character scalar as in `dualPairing_invariant`, is the
contragredient of `E`): `Θ(ρ(φ g) w) = ρ(g)^∨ Θ(w)`. -/
theorem thetaModel_equivariant (n : ℕ) (χ : RankOneCharacter) (g : RationalGL3) (w : HomogeneousPoly n) :
    thetaModel n (rationalCoefficientComponent n χ (dualInvolution g) w) =
      (rationalCoefficientComponent n χ).dual g (thetaModel n w) := by
  apply LinearMap.ext
  intro v
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, thetaModel_apply, thetaModel_apply]
  have h := dualPairing_invariant n χ g (rationalCoefficientComponent n χ g⁻¹ v) w
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact h

/-! ### Comparison of the two models of `E*` -/

theorem permJ_permJ (n : ℕ) (f : HomogeneousPoly n) : permJ n (permJ n f) = f := by
  apply Subtype.ext
  change substitute Jm (substitute Jm f.1) = f.1
  have := congrArg (fun q : Poly →ₐ[ℂ] Poly => q f.1) (substitute_comp Jm Jm)
  simp only [AlgHom.comp_apply, Jm_mul_self, substitute_one, AlgHom.id_apply] at this
  exact this

theorem support_subset_Sn {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) : p.support ⊆ Sn n := by
  intro m hm
  rw [mem_support_iff] at hm
  rw [mem_Sn_degree, Finsupp.degree_eq_weight_one]
  exact hp hm

/-- **The apolar form of the identification** `E ∘ ȷ ≅ E*`: `n! · (dualIso f)(h) = ⟨f(J X), h⟩_apolar`. -/
theorem factorial_mul_dualIso (n : ℕ) (f h : HomogeneousPoly n) :
    ((n.factorial : ℕ) : ℂ) * dualIso n f h = apolar n (permJ n f) h := by
  have hh : dualIso n f h = extFun n (dualIso n f) h.1 := (extFun_of_homogeneous _ h.2).symm
  have L : ((n.factorial : ℕ) : ℂ) * dualIso n f h =
      ∑ t ∈ Sn n, h.1.coeff t * (((n.factorial : ℕ) : ℂ) * extFun n (dualIso n f) (monomial t (1 : ℂ))) := by
    rw [hh]
    conv_lhs => rw [homogeneous_eq_sum (n := n) h.2]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
    ring
  have R : apolar n (permJ n f) h =
      ∑ t ∈ Sn n, apolarWeight t * (permJ n f : Poly).coeff t * h.1.coeff t := by
    rw [apolar_apply, apolarPoly_apply, ← apolarSum, apolarSum_eq_of_subset _ _ (support_subset_Sn (permJ n f).2)]
  rw [L, R]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [dualIso_monomial_factorial n f ht, coeff_permJ]
  unfold apolarWeight
  push_cast
  ring

/-- **The two models of `E*` agree up to the fixed coordinate change**: `dualPairing h u = n! · (dualIso (J·a·u)) h` with
`a = diag(1,1,3)` (the level scale) and `J` the antidiagonal permutation. -/
theorem dualPairing_eq_dualIso (n : ℕ) (u h : HomogeneousPoly n) :
    dualPairing n h u = ((n.factorial : ℕ) : ℂ) *
      dualIso n (permJ n (homogeneousSubstitute n complexLevelScale u)) h := by
  rw [factorial_mul_dualIso, permJ_permJ, dualPairing_apply, apolar_comm]

theorem thetaModel_eq_dualIso (n : ℕ) (u : HomogeneousPoly n) :
    thetaModel n u = ((n.factorial : ℕ) : ℂ) •
      dualIso n (permJ n (homogeneousSubstitute n complexLevelScale u)) := by
  apply LinearMap.ext
  intro h
  rw [thetaModel_apply, dualPairing_eq_dualIso]
  rfl

/-! ### `ȷ` versus `dualInvolution`: the two models are conjugate by `J · levelScale⁻¹` -/

theorem complexify_longWeyl :
    ((complexify longWeyl : GL3) : Matrix (Fin 3) (Fin 3) ℂ) = Jm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexify, longWeyl, longWeylMatrix, Jm, Fin.rev]

/-- The complexification of the paper's `ȷ` on `GL₃(ℚ)` (`DualJ.jmath`, `ȷ(g) = J (g⁻¹)ᵗ J`) is `jGL`. -/
theorem complexify_jmath (g : RationalGL3) :
    complexify (TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ.jmath g) = jGL (complexify g) := by
  apply Units.ext
  rw [TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ.jmath_apply, map_mul, map_mul]
  change ((complexify longWeyl : GL3) : Matrix (Fin 3) (Fin 3) ℂ) *
      ((complexify (inverseTranspose g) : GL3) : Matrix (Fin 3) (Fin 3) ℂ) *
      ((complexify longWeyl : GL3) : Matrix (Fin 3) (Fin 3) ℂ) =
    Jm * ((((complexify g)⁻¹ : GL3)) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * Jm
  have h := complexify_inverseTranspose_inv g⁻¹
  rw [inv_inv, map_inv] at h
  rw [complexify_longWeyl, h]

/-- **`ȷ` is `dualInvolution` conjugated by the fixed matrix `w = J a⁻¹`** (`a = levelScale = diag(1,1,3)`), over `ℂ`. -/
theorem jGL_complexify_eq_conj (g : RationalGL3) :
    jGL (complexify g) =
      complexify TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ.jmathConj *
        complexify (dualInvolution g) *
        (complexify TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ.jmathConj)⁻¹ := by
  rw [← complexify_jmath, TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ.jmath_eq_conj,
    map_mul, map_mul, map_inv]

end TernaryPeriodPolynomials.Argument.EisensteinDual
