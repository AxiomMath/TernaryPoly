module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FibreConst
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.PlaneClass

@[expose] public section


/-!
# Tuple value of the global integrand on a product fibre (route (b), step (B2))

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For a point `z ∈ U_S` whose local coordinates on `S` lie in the Hermite classes `tc w` (cyclic of
level `p_w^{r_w}`), the global integrand equals a weight depending only on the tuple `tc`, times
`normPower(det Z)` times `vhValueFull` at a block `X_tc · Z`, where the local values of `X_tc` are
`(Mz (tc w)).map ψ_w` on `S` and `1` off `S`. The data are determined by the tuple alone.
The proof uses `local_plane_class` on each `w ∈ S`, `intGL3_LfinGLof_of_mem` off `S`, and
`globalIntegrand_absorb`.
-/

open Classical Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.PointwiseMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinScalar
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.FibreConst
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.TupleValue

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The local `ℚ_p`-coordinate of a finite-adelic value at `w`. -/
abbrev coordP (w : FinitePlace) (a : FiniteAdeles) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv w).val] :=
  finiteCompletionPadicEquiv w (finiteEvaluation w a)

theorem psiV_coordP (w : FinitePlace) (a : FiniteAdeles) :
    psiV w (coordP w a) = finiteEvaluation w a :=
  (finiteCompletionPadicEquiv w).symm_apply_apply (finiteEvaluation w a)

/-- **Tuple value.** On `U_S`, with the local coordinates of `z` on `S` in the Hermite classes
`tc w`, the global integrand is `(tuple weight) · normPower(det Z) · vhValueFull(g∞, X · Z)`, with
`X` determined by the tuple: local values `(Mz (tc w)).map ψ_w` on `S`, and `1` off `S`. -/
theorem globalIntegrand_tuple_value (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (S : Finset FinitePlace) (r : FinitePlace → ℕ) (tc : FinitePlace → ℕ × ℕ × ℕ)
    (htc : ∀ w ∈ S, tc w ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv w).val (r w))
    (z : FiniteAwayThree × FiniteAwayThree)
    (hz : z ∈ UregionS S)
    (hmax : ∀ w ∈ S, max ‖coordP w (awayVal z.1)‖ ‖coordP w (awayVal z.2)‖ =
      ((Rat.HeightOneSpectrum.primesEquiv w).val : ℝ) ^ r w)
    (hfib : ∀ w ∈ S, pairLat (Rat.HeightOneSpectrum.primesEquiv w).val
      (coordP w (awayVal z.1), coordP w (awayVal z.2)) = hermLat (Rat.HeightOneSpectrum.primesEquiv w).val (tc w))
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) :
    ∃ X : GeneralLinearGroup (Fin 2) FiniteAdeles,
      (∀ w, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
        if w ∈ S then (Mz (q := (Rat.HeightOneSpectrum.primesEquiv w).val) (tc w)).map
          (fun x => psiV w (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv w).val])) else 1) ∧
      globalIntegrand I Z gInf z =
        ((∏ w ∈ S, Complex.exp (expo I * (Real.log ‖pe w
            (((Mz (q := (Rat.HeightOneSpectrum.primesEquiv w).val) (tc w)).map
              (fun x => psiV w (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv w).val]))).det)‖ : ℂ))) *
          normPower (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit
            (GeneralLinearGroup.det Z)) (expo I)) *
          vhValueFull (-2 * I.halfWeight) h gInf (X * Z) := by
  have key : ∀ w : FinitePlace, ∃ P κ : GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ),
      w ∈ S → ((P.val 2 0 = 0 ∧ P.val 2 1 = 0) ∧
        LstR (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2)) = P.val * κ.val ∧
        IntGL3 w κ.val ∧
        blk2 P.val = (Mz (q := (Rat.HeightOneSpectrum.primesEquiv w).val) (tc w)).map
          (fun x => psiV w (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv w).val]))) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨P, κ, p20, p21, hL, hκ, hblk⟩ :=
        LocalPlaneClass.local_plane_class w (r w) (coordP w (awayVal z.1), coordP w (awayVal z.2))
          (hmax w hw) (tc w) (htc w hw) (hfib w hw)
      refine ⟨P, κ, fun _ => ⟨⟨p20, p21⟩, ?_, hκ, hblk⟩⟩
      rw [← psiV_coordP w (awayVal z.1), ← psiV_coordP w (awayVal z.2)]
      exact hL
    · exact ⟨1, 1, fun hw' => absurd hw' hw⟩
  choose P κ hPκ using key
  have hP : ∀ w ∈ S, (P w).val 2 0 = 0 ∧ (P w).val 2 1 = 0 := fun w hw => (hPκ w hw).1
  have hS : ∀ w ∈ S, evM3 w (LfinGLof (awayVal z.1) (awayVal z.2)).val = (P w).val * (κ w).val := by
    intro w hw
    rw [evM3_LfinGLof]
    exact (hPκ w hw).2.1
  have hκ : ∀ w ∈ S, IntGL3 w (κ w).val := fun w hw => (hPκ w hw).2.2.1
  have hL : ∀ w, w ∉ S → IntGL3 w (evM3 w (LfinGLof (awayVal z.1) (awayVal z.2)).val) :=
    fun w hw => intGL3_LfinGLof_of_mem hz w hw
  obtain ⟨X, hX, heq⟩ := globalIntegrand_absorb I h hform S P κ hP z hS hκ hL Z hZ gInf
  refine ⟨X, ?_, ?_⟩
  · intro w
    rw [hX w]
    split_ifs with hw
    · exact (hPκ w hw).2.2.2
    · rfl
  · have hprod : (∏ w ∈ S, Complex.exp (expo I * (Real.log ‖pe w (blk2 (P w).val).det‖ : ℂ))) =
        ∏ w ∈ S, Complex.exp (expo I * (Real.log ‖pe w
            (((Mz (q := (Rat.HeightOneSpectrum.primesEquiv w).val) (tc w)).map
              (fun x => psiV w (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv w).val]))).det)‖ : ℂ)) :=
      Finset.prod_congr rfl (fun w hw => by rw [(hPκ w hw).2.2.2])
    rw [heq, hprod]

end TernaryPeriodPolynomials.Argument.LatticeCounts.TupleValue

end
