module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.CentralCharacter

@[expose] public section


/-!
# The trivial (unitarity) bound for the Hecke scalars

Compressions of unitary operators to the fixed vectors are contractions, so every Hecke scalar
`ω(B)` has absolute value at most one. Consequently the cuspidal part of the plane `T_p`
eigenvalue is bounded by `(p² + p) |p^{-planeExp}|`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-- Compressions are contractions. -/
theorem compression_norm_le (σ : CuspidalRepresentation) (K : Subgroup BinaryAdelicGL)
    (g : BinaryAdelicGL) (w : fixedVectors σ K) : ‖compression σ K g w‖ ≤ ‖w‖ := by
  set c := compression σ K g w
  have h1 : ‖c‖ ^ 2 ≤ ‖w‖ * ‖c‖ := by
    rw [@norm_sq_eq_re_inner ℂ]
    have e : inner ℂ c c = inner ℂ (σ.π g (w : σ.H)) (c : σ.H) := inner_compression g w c
    rw [e]
    calc RCLike.re (inner ℂ (σ.π g (w : σ.H)) (c : σ.H))
        ≤ ‖σ.π g (w : σ.H)‖ * ‖(c : σ.H)‖ := re_inner_le_norm _ _
      _ = ‖w‖ * ‖c‖ := by rw [σ.unitary]; rfl
  have hc : 0 ≤ ‖c‖ := norm_nonneg _
  have hw : 0 ≤ ‖w‖ := norm_nonneg _
  nlinarith

/-- **The trivial bound** `|ω(B)| ≤ 1`. -/
theorem omega_norm_le (σ : CuspidalRepresentation) {B : BinaryFiniteGL}
    (hB : B ∈ awayGroup placeThree) : ‖omega σ B‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (fixedVectors σ K3) with hs | hn
  · have h0 : omega σ B = 0 := by
      unfold omega scalarOf
      rw [dite_eq_right]
      rintro ⟨h1, -⟩
      exact (not_nontrivial_iff_subsingleton.mpr hs) h1
    rw [h0, norm_zero]
    exact zero_le_one
  · obtain ⟨w, hw⟩ := exists_ne (0 : fixedVectors σ K3)
    have hle := compression_norm_le σ K3 (atFinite B) w
    rw [omega_spec σ hB w, norm_smul] at hle
    have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
    exact (mul_le_iff_le_one_left hw').mp hle

/-- **Bound on the cuspidal part of the plane `T_p` eigenvalue.** -/
theorem prime_plane_cusp_part_bound {n p : ℕ} (D : InducingData n) (hp : p.Prime) :
    ‖((p : ℂ) ^ 2 + p) * (Complex.exp (-(planeExp n * (Real.log p : ℂ))) *
        omega D.cusp (Bo (dP hp)))‖ ≤
      ‖((p : ℂ) ^ 2 + p) * Complex.exp (-(planeExp n * (Real.log p : ℂ)))‖ := by
  rw [← mul_assoc, norm_mul]
  have := omega_norm_le D.cusp (glAway2_mem (glF (dP hp)))
  calc ‖((p : ℂ) ^ 2 + p) * Complex.exp (-(planeExp n * (Real.log p : ℂ)))‖ *
        ‖omega D.cusp (Bo (dP hp))‖
      ≤ ‖((p : ℂ) ^ 2 + p) * Complex.exp (-(planeExp n * (Real.log p : ℂ)))‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

theorem inductionExponent_plane_cohomological :
    inductionExponent .plane cohomologicalPoint = 0 := by
  simp only [inductionExponent, cohomologicalPoint]
  ring

theorem planeExp_eq (n : ℕ) : planeExp n = ((n : ℂ) + 3) / 2 := by
  rw [planeExp, inductionExponent_plane_cohomological, add_zero]

/-- **The plane `T_p` eigenvalue at the cohomological point.** For `p ≠ 3` it equals
`χ(sAd p) + (p² + p) p^{-(n+3)/2} ω(diag(p,1))`. -/
theorem prime_plane_eigenvalue_cohomological {n p : ℕ} (D : InducingData n) (hp : p.Prime)
    (h3 : p ≠ 3) (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors D.cusp K3)] :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (D.chi.toMonoidHom (sAd (pUnit hp)) +
          ((p : ℂ) ^ 2 + p) * (Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ))) *
            omega D.cusp (Bo (dP hp)))) * f g := by
  intro f hf g
  rw [prime_plane_eigenvalue_satake D hp h3 t ht hg f hf g, inductionExponent_plane_cohomological,
    planeExp_eq]
  simp

/-- **Explicit bound for the cuspidal part at the cohomological point.** -/
theorem prime_plane_cusp_part_bound_real {n p : ℕ} (D : InducingData n) (hp : p.Prime) :
    ‖((p : ℂ) ^ 2 + p) * (Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ))) *
        omega D.cusp (Bo (dP hp)))‖ ≤
      ((p : ℝ) ^ 2 + p) * Real.exp (-(((n : ℝ) + 3) / 2 * Real.log p)) := by
  have h := prime_plane_cusp_part_bound D hp
  rw [planeExp_eq] at h
  refine h.trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_exp]
  congr 1
  · have : ((p : ℂ) ^ 2 + p) = (((p : ℝ) ^ 2 + p : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  · congr 1
    have : -(((n : ℂ) + 3) / 2 * (Real.log p : ℂ)) = ((-(((n : ℝ) + 3) / 2 * Real.log p) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]

/-- **The `diag(p,p,1)` plane eigenvalue at the cohomological point.** -/
theorem prime2_plane_eigenvalue_cohomological {n p : ℕ} (D : InducingData n) (hp : p.Prime)
    (h3 : p ≠ 3) (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP2 hp)
    (hsm : ∃ v ∈ D.cusp.smooth, v ≠ 0) [Nontrivial (fixedVectors D.cusp K3)] :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        ((p : ℂ) ^ 2 * (Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ))) *
              D.cusp.centralCharacter (sAd (pUnit hp))) +
          ((p : ℂ) + 1) * (D.chi.toMonoidHom (sAd (pUnit hp)) *
            (Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ))) *
              omega D.cusp (Bo (dP hp))))) * f g := by
  intro f hf g
  rw [prime2_plane_eigenvalue_satake D hp h3 t ht hg hsm f hf g,
    inductionExponent_plane_cohomological, planeExp_eq]
  have e : -(2 * (((n : ℂ) + 3) / 2) * (Real.log p : ℂ)) = -(((n : ℂ) + 3) * (Real.log p : ℂ)) := by
    ring
  rw [e]
  simp

/-- **The central plane eigenvalue at the cohomological point.** -/
theorem central_plane_eigenvalue_cohomological {n p : ℕ} (D : InducingData n) (hp : p.Prime)
    (h3 : p ≠ 3) (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = pScalar hp)
    (hsm : ∃ v ∈ D.cusp.smooth, v ≠ 0) [Nontrivial (fixedVectors D.cusp K3)] :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (D.chi.toMonoidHom (sAd (pUnit hp)) *
          (Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ))) *
            D.cusp.centralCharacter (sAd (pUnit hp)))) * f g := by
  intro f hf g
  rw [central_plane_eigenvalue_explicit D hp h3 t ht hg hsm f hf g,
    inductionExponent_plane_cohomological, planeExp_eq]
  have e : -(2 * (((n : ℂ) + 3) / 2) * (Real.log p : ℂ)) = -(((n : ℂ) + 3) * (Real.log p : ℂ)) := by
    ring
  rw [e]
  simp

end TernaryPeriodPolynomials.HeckeEigen.Satake
