module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.Plane
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitTotal
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitLocal

@[expose] public section


/-!
# Global limit: local plane data with the determinant norm

For `s, t ∈ K_w` there is a factorisation `L(s,t) = P κ` with `P` of mirror-parabolic shape, `κ ∈ GL₃(O_w)`, and
`‖pe w (det blk₂ P)‖ = (max 1 (max ‖pe w s‖ ‖pe w t‖))⁻¹`, so that the local exponential factor of
`GlobalIntegrand.globalIntegrand_absorb` has norm `phiR` (the level weight of `GlobalLimitLocal`).

Formalized by Claude Sonnet 5.5.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG (psiV_mem_OS)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotal (zp2_or_shell)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitPlane

theorem psiV_pe (v : FinitePlace) (x : v.adicCompletion ℚ) : psiV v (pe v x) = x :=
  (finiteCompletionPadicEquiv v).symm_apply_apply x

theorem pe_psiV (v : FinitePlace) (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    pe v (psiV v x) = x := finiteCompletionPadicEquiv_psiV v x

/-- The determinant of the `2×2` block of a shell datum is `ψ(p^r)`. -/
theorem det_blk2_norm (v : FinitePlace) (P : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    (A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) (r : ℕ)
    (hA : A.det = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ^ r)
    (hP : blk2 P = A.map (fun x => psiV v (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]))) :
    ‖pe v (blk2 P).det‖ = (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r)⁻¹ := by
  have h1 : (blk2 P).det = psiV v (((A.det : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) := by
    rw [hP]
    have := RingHom.map_det ((psiV v).comp (PadicInt.Coe.ringHom (p := (Rat.HeightOneSpectrum.primesEquiv v).val))) A
    exact this.symm
  rw [h1, pe_psiV, hA]
  push_cast
  rw [norm_pow, Padic.norm_p]
  simp

/-- **Local plane datum with the level weight.** -/
theorem local_plane_level (v : FinitePlace) (s t : v.adicCompletion ℚ) :
    ∃ P κ : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ),
      P.val 2 0 = 0 ∧ P.val 2 1 = 0 ∧ LstR s t = P.val * κ.val ∧ IntGL3 v κ.val ∧
      ‖pe v (blk2 P.val).det‖ = (max 1 (max ‖pe v s‖ ‖pe v t‖))⁻¹ := by
  have hs : psiV v (pe v s) = s := psiV_pe v s
  have ht : psiV v (pe v t) = t := psiV_pe v t
  rcases zp2_or_shell (p := (Rat.HeightOneSpectrum.primesEquiv v).val) (pe v s, pe v t) with hz | ⟨r, hr⟩
  · have hz' : ‖pe v s‖ ≤ 1 ∧ ‖pe v t‖ ≤ 1 := hz
    obtain ⟨P, κ, hP20, hP21, hfac, hκ, hb⟩ :=
      local_plane_zero v ((mem_iff_norm v s).2 hz'.1) ((mem_iff_norm v t).2 hz'.2)
    refine ⟨P, κ, hP20, hP21, hfac, hκ, ?_⟩
    rw [hb, Matrix.det_one, map_one, norm_one, max_eq_left (max_le hz'.1 hz'.2)]
    simp
  · have hmax : max ‖(pe v s, pe v t).1‖ ‖(pe v s, pe v t).2‖ =
        ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (r + 1) := hr
    obtain ⟨P, κ, hP20, hP21, hfac, hκ, A, hA, hb⟩ := local_plane_shell v (r + 1) hmax
    rw [hs, ht] at hfac
    refine ⟨P, κ, hP20, hP21, hfac, hκ, ?_⟩
    rw [det_blk2_norm v P.val A (r + 1) hA hb]
    have hp : (1 : ℝ) ≤ ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (r + 1) :=
      one_le_pow₀ (Nat.one_le_cast.2 (Rat.HeightOneSpectrum.primesEquiv v).2.one_lt.le)
    have : max ‖pe v s‖ ‖pe v t‖ = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ (r + 1) := hmax
    rw [this, max_eq_right hp]

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitPlane
