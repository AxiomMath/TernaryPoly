module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REValue
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBadMain
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REOrbit
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad6
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RESupply

@[expose] public section


/-!
# R-e: the finite adelic input `FiniteEntryIdentity` of the class-level entry comparison (ML4b, Appendix C.5)

Formalized by Claude Sonnet 5.5.

**Setting.**  `Entry.SphericalEntryData D` packages the hypotheses on the inducing datum `D` and on the section:
`D.chi` is trivial on the integral units, `3 < n`, `F = cuspScalarWeightedRealization D.cusp halfWeight vector`
for a nonzero `GL₂(Ẑ)`-spherical vector which is a prime Hecke eigenvector with eigenvalues
`p^{halfWeight+1}·a_p` of a normalized level-one eigenform of weight `n + 3 = -2 halfWeight`.  The identity is
false for arbitrary `F` (the finite plane factor is defined through a choice of Iwasawa decomposition and the
Euler factors need the eigenvector property), and it is *not* asserted for an arbitrary inducing datum.

**Results.**

* `finite_entry_identity_spherical`: `FiniteEntryIdentity D (fun _ => 1) ιL F r_full` for every guard `ιL` (the
  identity holds at *every* `g`, `x`, `z`): measurability of `(v, z) ↦ c_F(g_v) F(x b_F(g_v))(z)` on
  `𝔸_f² × ℍ`, a locally (in `z`) uniform integrable majorant, and
  `∫_{𝔸_f²} c_F(g_v) F(x b_F(g_v))(z) dv = r_full · c_F^{line}(g) F(x b_F^{line}(g))(z)`.
  `r_full = ∏_p c_p` over *all* finite places, i.e. `L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` times the local factor at `3`
  (`rFull_eq_lseries_ratio`: `r_full = L(h,k-2)/L(h,k-1)`).
* `bad_plane_entry_identity`: the guarded two-weight form `FiniteEntryIdentity D ιP ιL F r_bad` with the bad-plane
  weight `ιP = badPlaneWeight` (indicator of `P(ℚ₃)K₁`) and the good-line weight `ιL = goodLineWeight` (indicator of
  `L(ℚ₃)g₀K₁`), `r_bad = (1/9)·∏_{p≠3} c_p = (1/9)·L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`.  Nothing is asserted off the
  good-line orbit: at the representative `g = 1` of the other orbit the `3`-adic support of the weight along the
  radical is not the box `(3ℤ₃)²` (`otherOrbit_support`), so the `1/9` computation does not apply and no value is
  asserted.  `entry_orbit_decomposition`: spherical section = bad-plane orbit (`r_bad`) + other orbit
  (`r_full − r_bad`) at the good-line cusp.
* Additions: `bad_plane_entry_identity_of_support` (the bad-plane identity holds for every line guard supported
  in the good-line orbit; the paper evaluates the bad-plane integral only at the good-line cusp `g₀`, ms.,
 and uses only the image at the good-line cusp, ms., so the other line orbit is not needed);
  `exists_spherical_entry_package` (for `D.chi = trivialCharacter`, `SphericalCusp D.cusp`, `Odd n`: a
  `SphericalEntryData D` together with an `EichlerInput` of the same vector), `…_of_spherical`, `…_of_bad_plane`
  (parity and sphericity supplied by the library's closed pieces), `entry_package_holomorphic`, `entry_package_decay`.
* Scalars: `r_full_formula` (`r_full = L(h,k-2)/L(h,k-1)`), `r_full_ne_zero`, `r_bad_eq_r_print`
  (`r_bad = (1/9)·globalEntryRatio`), `r_print_ne_zero`, `printedScalar_ne_zero` (from the `global_entry_ne_zero`), `r_full_eq_nine_mul` (`r_full = 9·c₃·r_print`).
* **Sign.**  `entryScalar_r_print`: `entryScalar n r_print = −(printed scalar)`.  The finite scalar `r_print` carries
  no sign; the minus comes from the archimedean ledger of K's cochain computation (`h_plane = (-1)ⁿ(n+1)F`,
  `h_line = (-1)^{n+1}(n+1)F`).  It is a normalization item (dictionary of the paper's induced-section
  and differential-form conventions) and is not resolved here.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FiniteEntry

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open MeasureTheory

/-- **R-e, spherical case.** -/
theorem finite_entry_identity_spherical {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)
    (ιL : AdelicGL → ℂ) : FiniteEntryIdentity D (fun _ => 1) ιL S.F S.rFull :=
  finiteEntryIdentity_spherical S ιL

/-- **R-e, bad plane at the good-line orbit.** -/
theorem bad_plane_entry_identity {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) :
    FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad :=
  badPlaneEntryIdentity S

/-- The bad-plane weight is a plane weight and the good-line weight a line weight. -/
theorem weights : PlaneWeight badPlaneWeight ∧ LineWeight goodLineWeight :=
  ⟨badPlaneWeight_planeWeight, goodLineWeight_lineWeight⟩

/-- **The formula for `r`**: the product of the local Euler factors at all places is `L(h,k-2)/L(h,k-1)`. -/
theorem r_full_formula {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) :
    S.rFull = S.lseries ((n : ℂ) + 1) / S.lseries ((n : ℂ) + 2) :=
  S.rFull_eq_lseries_ratio

/-- `r_full ≠ 0`. -/
theorem r_full_ne_zero {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) : S.rFull ≠ 0 :=
  S.rFull_ne_zero

/-- The bad-plane scalar is the paper's finite scalar `(1/9)·L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`. -/
theorem r_bad_eq_r_print {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) : S.rBad = S.rPrint :=
  S.rBad_eq_rPrint

theorem r_print_ne_zero {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) : S.rPrint ≠ 0 :=
  S.rPrint_ne_zero

/-- `r_full = 9 · c₃ · r_print`. -/
theorem r_full_eq_nine_mul {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) :
    S.rFull = 9 * S.euler3 * S.rPrint :=
  S.rFull_eq_nine_mul

/-- The paper's printed scalar is nonzero (deduced from the `global_entry_ne_zero`). -/
theorem printed_scalar_ne_zero {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) :
    S.printedScalar ≠ 0 :=
  S.printedScalar_ne_zero_of_frozen

/-- **The sign** (open normalization item): `entryScalar n r_print = −(printed scalar)`. -/
theorem entryScalar_r_print {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) :
    entryScalar n S.rPrint = -S.printedScalar :=
  S.entryScalar_rPrint

/-- **Orbit decomposition at the good-line cusp**: the complementary `P(ℚ₃)\GL₃(ℚ₃)/K₁` orbit contributes
`r_full − r_bad`. -/
theorem orbit_decomposition {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) (g : AdelicGL)
    (hg : goodLineWeight g ≠ 0) (x : BinaryAdelicGL) (z : ℂ) (hz : 0 < z.im) :
    (∫ v : FiniteAdeles × FiniteAdeles, (1 - badPlaneWeight (finiteEntryElement v g)) *
        (cF D (finiteEntryElement v g) * S.F (x * bF (finiteEntryElement v g)) z)
        ∂(finiteMeasure.prod finiteMeasure)) =
      (S.rFull - S.rBad) * (cFLine D g * S.F (x * bFLine g) z) :=
  entry_orbit_decomposition S g hg x z hz

/-- At the representative `g = 1` of the other line orbit the support of the bad-plane weight along the radical
contains a point outside `(3ℤ₃)²`. -/
theorem other_orbit_support :
    badPlaneSet (weyl⁻¹ * lineUnipotent (0 : ℚ_[3]) (1 / 3) * 1) ∧
      ¬ (‖(0 : ℚ_[3])‖ < 1 ∧ ‖(1 / 3 : ℚ_[3])‖ < 1) :=
  otherOrbit_support

/-- The bad-plane identity for every line guard supported in the good-line orbit. -/
theorem bad_plane_entry_identity_of_support {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)
    (ιL : AdelicGL → ℂ) (hsupp : ∀ g, ιL g ≠ 0 → goodLineWeight g ≠ 0) :
    FiniteEntryIdentity D badPlaneWeight ιL S.F S.rBad :=
  badPlaneEntryIdentity_of_support S ιL hsupp

/-- **Existence of the entry data** for an inducing datum with trivial character and a spherical cuspidal constituent
in odd degree. -/
theorem exists_spherical_entry_package {n : ℕ} (D : InducingData n) (hodd : Odd n)
    (hχ : D.chi = trivialCharacter) (hsph : SphericalCusp D.cusp) : Nonempty (SphericalEntryPackage D) :=
  exists_sphericalEntryPackage D hodd hχ hsph

/-- The same, with `n` odd supplied by `level_one_cohomological_parity`. -/
theorem exists_spherical_entry_package_of_spherical {n : ℕ} (hn : 0 < n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hsph : SphericalCusp D.cusp) : Nonempty (SphericalEntryPackage D) :=
  exists_sphericalEntryPackage_of_spherical hn D hχ hsph

/-- The same for a nonzero plane class with a bad-plane representative. -/
theorem exists_spherical_entry_package_of_bad_plane {n : ℕ} (hn : 0 < n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (ξ : boundarySummand D .plane) (hξ : ξ ≠ 0)
    (hrep : BadPlaneRepresentative D ξ) : Nonempty (SphericalEntryPackage D) :=
  exists_sphericalEntryPackage_of_badPlane hn D hχ ξ hξ hrep

/-- Holomorphy of the datum `S.F x` on the upper half plane for every adelic base point. -/
theorem entry_package_holomorphic {n : ℕ} {D : InducingData n} (P : SphericalEntryPackage D) (x : BinaryAdelicGL) :
    DifferentiableOn ℂ (P.S.F x) {z : ℂ | 0 < z.im} :=
  P.holomorphic x

/-- Decay of the datum. -/
theorem entry_package_decay {n : ℕ} {D : InducingData n} (P : SphericalEntryPackage D) (x : BinaryAdelicGL) :
    ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖P.S.F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M :=
  P.decay x

end TernaryPeriodPolynomials.Argument.Statements.FiniteEntry
