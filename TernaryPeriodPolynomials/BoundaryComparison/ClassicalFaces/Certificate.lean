module

public import TernaryPeriodPolynomials.BoundaryComparison.ClassicalFaces.Faces
public import TernaryPeriodPolynomials.BoundaryComparison.ClassicalFaces.NormalizationRecord
public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntry.FiniteEntry

@[expose] public section


/-!
# The R3 certificate and the certified detection

* `paper_entry_at_classical_faces`: the exact R3 contract (`ARGUMENT_FLOW_TARGETS.lean.txt`),
  `paper_entry_at_classical_faces_of_entry` applied to the `paper_finite_entry`.
* `cuspRes_line_true_image_ne_zero_certified`: the good-line coordinate of the image of the bad-plane section is
  nonzero.  Its proof takes the equation `phiLine (goodComponent (T ζ)) = S.printedScalar • seed` from the
  certificate `paper_entry_at_classical_faces` (N = 6), the seed nonvanishing from `lineSeedBoundary_paper_ne_zero`.
  No finite-entry hypothesis remains: it is `paper_finite_entry`, inside the certificate.

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.  Inputs: `paper_finite_entry`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1)
open TernaryPeriodPolynomials.Argument.KDaggerComparison (phiLine)
open TernaryPeriodPolynomials.Argument.LineSeed (lineSeedBoundary lineEntryTupleC lineSeedIdentity)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

/-- R3: the joint certificate for the same graph operator, entry data and classical seed (the exact contract type).
The finite entry identity is the `paper_finite_entry`, consumed by `classLevel_paper_of_entry` inside
`paper_entry_at_classical_faces_of_entry`. -/
theorem paper_entry_at_classical_faces (N : ℕ) [NeZero N] (n : ℕ)
    (hn : Odd n) (h3 : 3 ∣ N) (hN : 3 ≤ N)
    (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hf : (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I)
    (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand M.inducingData .plane →ₗ[ℂ] boundarySummand M.inducingData .line)
    (hT : RealizesStandardConv M.inducingData T) :
    phiLine N h3 hN n
        (goodComponent n M.inducingData.chi .line
          (T (SphericalEntryData.badPlaneClass S I)).val) =
      S.printedScalar • lineSeedBoundary N n
        (lineEntryTupleC (-(((n : ℂ) + 1) / 2)) f) :=
  paper_entry_at_classical_faces_of_entry N n hn h3 hN M S I f hf hw hv T hT
    (paper_finite_entry M.inducingData S I hw hv)


/-- **The good-line coordinate of the image of the bad-plane section is nonzero, via the R3 certificate.**  The
equation comes from `paper_entry_at_classical_faces` at `N = 6`; the nonvanishing of the classical seed vector from
`lineSeedBoundary_paper_ne_zero` (see its limitation note); the printed scalar is nonzero. -/
theorem cuspRes_line_true_image_ne_zero_certified (n : ℕ) (M : CohomologicalCuspData n) (hodd : Odd n)
    (S : SphericalEntryData M.inducingData) (I : EichlerInput M.cusp n)
    (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand M.inducingData .plane →ₗ[ℂ] boundarySummand M.inducingData .line)
    (hT : RealizesStandardConv M.inducingData T) :
    cuspRes n M.inducingData.chi .line true (T (SphericalEntryData.badPlaneClass S I)).val ≠ 0 := by
  obtain ⟨f, hf, -⟩ := lineSeedIdentity hodd M S I
  have hb := paper_entry_at_classical_faces 6 n hodd (by norm_num) (by norm_num) M S I f hf hw hv T hT
  have hseed := lineSeedBoundary_paper_ne_zero 6 n hodd (by norm_num) (by norm_num) M S I f hf
  have hgc : goodComponent n M.inducingData.chi .line (T (SphericalEntryData.badPlaneClass S I)).val ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hb
    exact (smul_eq_zero.mp hb.symm).elim S.printedScalar_ne_zero hseed
  intro hz
  exact hgc ((goodComponent_line_eq_zero_iff _).mpr hz)

end TernaryPeriodPolynomials.Argument.BoundaryComparison
