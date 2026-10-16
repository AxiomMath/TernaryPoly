module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NCanonical
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.ZeroFlagsPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.EdgeSurjective

@[expose] public section


/-!
# Naming `Tξ ∈ 𝒞_Q(E)`: the line restrictions of the classical series through the Hochschild-Serre edge

Formalized by Claude Sonnet 5.5.

* `series_zeroFlags`, `series_line_mixed`: a SINGLE classical series (any cusp `h'`, either seed) has zero flag restrictions and mixed cuspidal line restrictions at EVERY line cusp.
* `seriesLineCusp`: the unique element of `𝒞_{Q'}(E) = lineFaceCuspidal N h n` whose image under the injection `lineFaceCuspidalEmbedding` (inverse edge) is `r_{h⁻¹Qh} ℰ^b_{h'}`; `seriesLineCusp_spec`, `seriesLineCusp_unique`.
* `TclLine : TwTuple N n →ₗ[ℂ] LineCuspSum N n`: the summed classical series, line coordinates in `⨁ 𝒞_{Q'}(E)`, linear in the tuple, with `lineCuspSumEmbedding_TclLine`.  It is the line-row map before the
  factorisation through the seed vector (that factorisation is `ClassicalLineConstantTerm`).
-/

open scoped MatrixGroups DirectSum
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **A single classical series has zero flag restrictions** (any cusp `h'`, either seed). -/
theorem series_zeroFlags (hN : 3 ≤ N) (hn : 4 ≤ n) (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h' : SL(3, ℤ)) (b : Bool) :
    ZeroFlags N n (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g h' b hn)) := by
  refine zeroFlags_of_plane_mixed N n hN _ fun h => ?_
  have e : rPlane N n h = resAtC N h n := by
    unfold rPlane resAtC twoCohomologyRestriction
    rfl
  rw [e]
  exact faceSeedSpan_le_cuspidalInH2 N h n ((cuspValues N n hN hn).mem g h h' b)

/-- **A single classical series has mixed cuspidal line restrictions at every line cusp.** -/
theorem series_line_mixed (hN : 3 ≤ N) (hn : 4 ≤ n) (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h h' : SL(3, ℤ)) (b : Bool) :
    rLine N n h (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g h' b hn)) ∈ lineFaceCuspidalInH2 N h n :=
  zeroFlags_line_mixed N n hN _ (series_zeroFlags N n hN hn g h' b) h

theorem exists_seriesLineCusp (hN : 3 ≤ N) (hn : 4 ≤ n) (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h h' : SL(3, ℤ)) (b : Bool) :
    ∃ ξ : lineFaceCuspidal N h n, lineFaceCuspidalEmbedding N h n ξ = rLine N n h (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g h' b hn)) := by
  have := series_line_mixed N n hN hn g h h' b
  rw [lineFaceCuspidalInH2_eq_range] at this
  exact this

/-- **The class `r_{h⁻¹Qh} ℰ^b_{h'}(g)` as an element of `𝒞_{Q'}(E) ⊂ H¹(Γ₂(N), H¹(N_{Q'}, E))`** (through the inverse Hochschild-Serre edge). -/
def seriesLineCusp (hN : 3 ≤ N) (hn : 4 ≤ n) (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h h' : SL(3, ℤ)) (b : Bool) :
    lineFaceCuspidal N h n :=
  (exists_seriesLineCusp N n hN hn g h h' b).choose

theorem seriesLineCusp_spec (hN : 3 ≤ N) (hn : 4 ≤ n) (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h h' : SL(3, ℤ)) (b : Bool) :
    lineFaceCuspidalEmbedding N h n (seriesLineCusp N n hN hn g h h' b) = rLine N n h (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g h' b hn)) :=
  (exists_seriesLineCusp N n hN hn g h h' b).choose_spec

theorem seriesLineCusp_unique (hN : 3 ≤ N) (hn : 4 ≤ n) (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h h' : SL(3, ℤ)) (b : Bool)
    (ξ : lineFaceCuspidal N h n)
    (hξ : lineFaceCuspidalEmbedding N h n ξ = rLine N n h (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g h' b hn))) :
    ξ = seriesLineCusp N n hN hn g h h' b :=
  lineFaceCuspidalEmbedding_injective N h n (hξ.trans (seriesLineCusp_spec N n hN hn g h h' b).symm)

theorem exists_tupleLine (hN : 3 ≤ N) (hn : 4 ≤ n) (f : TwTuple N n) :
    lineBoundary N n (classCG N n hn f) ∈ LinearMap.range (lineCuspSumEmbedding N n) := by
  have hm : MixedCuspidalRestrictions N n (classCG N n hn f) :=
    (zeroFlags_iff_mixed N n hN _).1 (classicalPlaneConstantTerms N n hN hn f).1
  exact (exists_coordinates N n _ hm).2

/-- **The line coordinates of the summed classical series in `⨁ 𝒞_{Q'}(E)`**, linear in the tuple. -/
def TclLine (hN : 3 ≤ N) (hn : 4 ≤ n) : TwTuple N n →ₗ[ℂ] LineCuspSum N n :=
  (LinearEquiv.ofInjective (lineCuspSumEmbedding N n) (lineCuspSumEmbedding_injective N n)).symm.toLinearMap ∘ₗ
    (lineBoundary N n ∘ₗ classLin hn (classicalLinearity N n hn)).codRestrict
      (LinearMap.range (lineCuspSumEmbedding N n)) (exists_tupleLine N n hN hn)

theorem lineCuspSumEmbedding_TclLine (hN : 3 ≤ N) (hn : 4 ≤ n) (f : TwTuple N n) :
    lineCuspSumEmbedding N n (TclLine N n hN hn f) = lineBoundary N n (classCG N n hn f) := by
  have := (LinearEquiv.ofInjective (lineCuspSumEmbedding N n) (lineCuspSumEmbedding_injective N n)).apply_symm_apply
    ⟨lineBoundary N n (classCG N n hn f), exists_tupleLine N n hN hn f⟩
  exact congrArg Subtype.val this

end TernaryPeriodPolynomials.Argument.FormClassK
