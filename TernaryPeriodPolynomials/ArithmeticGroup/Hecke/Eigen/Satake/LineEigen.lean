module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.OmegaBound

@[expose] public section


/-!
# The explicit `T_p` eigenvalue on line sections

Through the Satake comparison `satake_sum`, the line eigenvalue of the prime correspondence equals
the plane one; hence it is `χ(sAd p) + (p² + p) p^{-(n+3)/2} ω(diag(p,1))` at the cohomological
point.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n p : ℕ}

/-- The plane weight sum of the prime correspondence. -/
theorem prime_plane_weight_sum (D : InducingData n) (hp : p.Prime) (t : HeckeCorrespondence)
    (ht : AwayThree t) (hg : t.g = gP hp) (vP : RationalGL3 → ℚ × ℚ)
    (BP : RationalGL3 → GeneralLinearGroup (Fin 2) ℚ) (sP : RationalGL3 → ℚˣ)
    (γP : RationalGL3 → IntegralGL)
    (hP : ∀ r, r = pU (vP r) * planeLevi (BP r) (sP r) * integralRational (γP r))
    (hsP : ∀ r, 0 < (sP r : ℚ)) :
    ∑ r ∈ t.representatives, ratPlaneWeight D (BP r) (sP r) =
      ratPlaneWeight D 1 (pUnit hp) + ((p : ℂ) ^ 2 + p) * ratPlaneWeight D (dP hp) 1 := by
  classical
  have hcount := prime_plane_count hp t ht hg vP BP sP γP (fun r _ => hP r) (fun r _ => hsP r)
  have hcount1 := prime_plane_count_one hp t ht hg vP BP sP γP (fun r _ => hP r)
    (fun r _ => hsP r)
  have hterm : ∀ r ∈ t.representatives, ratPlaneWeight D (BP r) (sP r) =
      if (sP r : ℚ) = p then ratPlaneWeight D 1 (pUnit hp) else ratPlaneWeight D (dP hp) 1 := by
    intro r hr
    have hmem := rep_plane_mem hp ht hg hr (hP r)
    rcases prime_plane_weight D hp _ _ _ (hsP r) hmem with ⟨hs, hw⟩ | ⟨hs, hw⟩
    · rw [ite_eq_left hs, hw, show sP r = pUnit hp from Units.ext (by rw [hs, pUnit_val])]
    · have hne : (sP r : ℚ) ≠ p := by rw [hs]; exact_mod_cast hp.one_lt.ne
      rw [ite_eq_right hne, hw, show sP r = 1 from Units.ext (by rw [hs, Units.val_one])]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, hcount, hcount1]
  push_cast
  ring

/-- **The line eigenvalue of the prime correspondence.** -/
theorem prime_line_eigenvalue (D : InducingData n) (hp : p.Prime) (t : HeckeCorrespondence)
    (ht : AwayThree t) (hg : t.g = gP hp) :
    ∀ f : AdelicGL → ℂ, IsInduced D .line cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (ratPlaneWeight D 1 (pUnit hp) + ((p : ℂ) ^ 2 + p) * ratPlaneWeight D (dP hp) 1) * f g := by
  intro f hf g
  choose vP BP sP γP hsP hP using plane_iwasawa_pos
  choose wL dL AL γL hdL hL using line_iwasawa_pos
  rw [line_rational_formula D t ht wL dL AL γL (fun r _ => hL r) f hf g,
    ← satake_sum D ht vP BP sP γP (fun r _ => hP r) (fun r _ => hsP r) wL dL AL γL
      (fun r _ => hL r) (fun r _ => hdL r),
    prime_plane_weight_sum D hp t ht hg vP BP sP γP hP hsP]

/-- **The line `T_p` eigenvalue at the cohomological point.** -/
theorem prime_line_eigenvalue_cohomological (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors D.cusp K3)] :
    ∀ f : AdelicGL → ℂ, IsInduced D .line cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (D.chi.toMonoidHom (sAd (pUnit hp)) +
          ((p : ℂ) ^ 2 + p) * (Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ))) *
            omega D.cusp (Bo (dP hp)))) * f g := by
  intro f hf g
  rw [prime_line_eigenvalue D hp t ht hg f hf g, ratPlaneWeight_prime_scalar D hp h3,
    ratPlaneWeight_dP D hp h3, Bo_one, omega_one, atFinite_one, map_one, sAd_one, map_one,
    normPower_one, normPower_one, inductionExponent_plane_cohomological, planeExp_eq]
  simp

end TernaryPeriodPolynomials.HeckeEigen.Satake
