module

public import TernaryPeriodPolynomials.BoundaryComparison.LemmaC2Geometric
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDKoszul
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDLefschetz
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDRadical
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDRestr
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDPlane

@[expose] public section


/-!
# The literal content of `ar:eq:facepair`: Koszul pairing of the radical, cuspidal pairing of the binary Levi, per face

Formalized by Claude Sonnet 5.5.

**(a) Fibre.**  `Koszul.KData` (two commuting automorphisms of `E`, `E'`, an invariant perfect pairing): the Koszul complex
`E → E² → E` computes `H¹(ℤ², E)`, the cup product of one-cocycles on the fundamental class of the torus is
`Phi ((p₁, p₂), (q₁, q₂)) = e p₁ (t₁ q₂) - e p₂ (t₂ q₁)`, and `Koszul.KData.pairing` on `H¹ × H¹` is **perfect in both
arguments** (`koszul_pairing_perfect`).  For the radical lattices of the library (`latL0` bad line, `latL1` good line) acting on `E`
and `E^φ` this is the library's fibre-integration pairing `κ(f, g) = ⟨f ⌣ g, σ⟩` of equivariant homogeneous cocycles
(`kostant_eq_koszul`), perfect (`lattice_koszul_perfect`), and its Kostant coordinates are the invariant pairing of `Sym^{n+1}` up to
the explicit nonzero constants `(n+1)!/3`, `-(n+1)!/3`, `-(n+1)!` (`badLine_koszul_eq_binaryPairing`,
`badLine_koszul_eq_binaryPairing_odd`, `goodLine_koszul_eq_binaryPairing`).

**(b) Base.**  `Lefschetz.imagePairing`: the pairing `⟨j a, j' b⟩ = PD a (j' b) = PD' (j a) b` between the images of
compactly supported cohomology under `j : H_c(E) → H(E)`, `j' : H_c(E*) → H(E*)` is well defined and nondegenerate on both sides
(the annihilator of either image is the kernel of the transpose map), from the nondegeneracy of the Poincare-Lefschetz pairings.
The cuspidal pairing used for the actual faces is the parabolic cup pairing of the binary Levi (`Statements.FacePairing`:
`levelOne_pairing_perfect`, `levelThree_pairing_perfect_odd/even`; cuspidal classes = classes whose restriction to every cusp
stabilizer is a coboundary, `parabolicCocycles`), perfect by the library's parabolic Poincare duality.  The identification of the
parabolic classes with the image of the TRUE compactly supported cohomology (relative cocycles `(Z, primitives)`, `j` forgets the
primitives) and the instance of `Lefschetz.imagePairing` for `Γ₁'(3)` and `GL₂(ℤ)` (Poincare-Lefschetz pairings `H_c × H` of the
punctured-surface groups relative to their cusp subgroups, with `j'` the transpose of `j` by the skew-symmetry of the cup product) is
proved in `Statements.FacePairingBinaryPL` (`Glue.FacePDBinaryPL*`): for odd `n` (good line, identity plane, bad line, good plane) the pairing of
the images is the library's parabolic cup pairing and is nondegenerate on both sides, for even `n` the bad-line / good-plane pairing is
that pairing composed with the library's transport.  The names `cuspidal_image_pairing_*` below are only the ABSTRACT linear algebra.
The dual coefficient system used there is a perfect invariant pairing (contragredient twisted by the determinant,
`levelOne_dual_is_contragredient`); the connection of the model dual `E^φ` of the ternary level with the literal contragredient is
NOT made here.

**(c) Combination.**  `facePairing_literal`: for the single nonzero constant `c` of the comparison with the boundary, the
Poincare-duality pairing of `∂M` on the lifts (`geoLinePairing`, `geoPlanePairing`) is `r (c⁻¹ · κ_n · ⟨ , ⟩_cusp)`, with
`⟨ , ⟩_cusp` the parabolic cup pairing of the binary Levi at each reference cusp applied to the Hochschild-Serre/Kostant
dictionary classes, and `κ_n = (n+1)!/3`, `-(n+1)!/3`, `(n+1)!` the Koszul-to-invariant-pairing constants of (a); the plane face
has the opposite orientation `-c` and the sign `a = ±1` of the swap relation.

**(d) Face components** (`Glue.FacePDRestr`): the model's face coordinates of a class of `H^n(∂M; W)` equal the library's
restrictions to the open faces followed by the comparison of the face-chain resolutions with the model resolutions
(`faceLine_eq_original`, `facePlane_eq_original`), for all `W`, `n` and classes.

Not proved: the absolute value of `c` (orientation of the comparison with the boundary fundamental class); the comparison of the
face coefficient systems of the ternary level (the model dual `E^φ`) with the literal contragredient `E*` (see (b)).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.Statements.LemmaC2Geometric
open TernaryPeriodPolynomials.BoundaryDuality

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FacePairingPD

/-! ### (a) The Koszul pairing of the radical -/

/-- **The two-generator Koszul pairing is perfect** (Poincare duality of the torus fibre with dual local systems). -/
theorem koszul_pairing_perfect {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] (K : Glue.FacePD.Koszul.KData E E') :
    (∀ a : K.H1, (∀ b : K.H1', K.pairing a b = 0) → a = 0) ∧ ∀ b : K.H1', (∀ a : K.H1, K.pairing a b = 0) → b = 0 :=
  ⟨fun a h => K.pairing_left_nondegenerate a h, fun b h => K.pairing_right_nondegenerate b h⟩

alias kostant_eq_koszul := Glue.FacePD.kostant_eq_koszul
alias lattice_koszul_perfect := Glue.FacePD.latticeKoszul_perfect
/-- **The Koszul pairings of the plane radicals** (identity plane `P₀`, good plane `P₁`) are perfect (`FacePDPlane`). -/
alias latP0_koszul_perfect := Glue.FacePD.latP0_koszul_perfect
alias latP1_koszul_perfect := Glue.FacePD.latP1_koszul_perfect
alias latP0_koszul_eq_kostant := Glue.FacePD.latP0_koszul_eq_kostant
alias latP1_koszul_eq_kostant := Glue.FacePD.latP1_koszul_eq_kostant

alias badLine_koszul_eq_binaryPairing := Glue.FacePD.badLine_koszul_eq_binaryPairing
alias badLine_koszul_eq_binaryPairing_odd := Glue.FacePD.badLine_koszul_eq_binaryPairing_odd
alias goodLine_koszul_eq_binaryPairing := Glue.FacePD.goodLine_koszul_eq_binaryPairing

/-! ### (b) The pairing between images of compactly supported cohomology -/

/-- **Abstract Lefschetz lemma, left nondegeneracy** (pure linear algebra, no cohomology): for ARBITRARY linear maps `j : H_c → H`,
`j' : H_c' → H'` and bilinear maps `PD : H_c × H' → ℂ`, `PD' : H × H_c' → ℂ` with `PD a (j' b) = PD' (j a) b` and `PD'` nondegenerate
on the `H` side, the pairing `⟨j a, j' b⟩ = PD a (j' b)` of the images is nondegenerate on the `Im j` side.  Nothing here says what
`j`, `PD` are: it is NOT a statement about a concrete modular curve and in particular not about any edge map.  The concrete instance
with the true compact-support map (relative cocycles `(Z, primitives)`, `j` forgets the primitives) is `Glue.FacePD.BinaryPL`
(`Setup.j`, `Setup.PD`, `Setup.PDt`, `Setup.hT`). -/
alias cuspidal_image_pairing_left_nondegenerate := Glue.FacePD.Lefschetz.imagePairing_left_nondegenerate
/-- **Abstract Lefschetz lemma, right nondegeneracy** (see `cuspidal_image_pairing_left_nondegenerate`; abstract, no concrete `j`). -/
alias cuspidal_image_pairing_right_nondegenerate := Glue.FacePD.Lefschetz.imagePairing_right_nondegenerate

/-! ### (c) The combined pairing -/

open TernaryPeriodPolynomials.Argument.Statements.FacePairing in
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality in
/-- **`ar:eq:facepair`, literal form.** One nonzero constant `c` such that, for every `ℚ`-linear `r : ℂ → ℚ`:
the geometric Poincare-duality pairings of the lifts of inner classes are the model face pairings divided by `c` (line) and `-c`
(plane), and these are the parabolic cup pairings of the binary Levi at the reference cusps times the Koszul constants. -/
theorem facePairing_literal : ∃ c : ℂ, c ≠ 0 ∧
    (∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane),
      r (c⁻¹ * facePairing n b ξ) = geoLinePairing n r b ξ) ∧
    (∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line),
      r ((-c)⁻¹ * Plane.facePairingP n ξ b) = geoPlanePairing n r ξ b) ∧
    (∀ (n : ℕ) (hn : 0 < n) (heven : Even n) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane),
      geoLinePairing n r b ξ = r (c⁻¹ * ((((n + 1).factorial : ℂ) / 3) *
        LocalPairingCaseL0Even.badGoodPairingEven heven (Literal.badLineParabolic hn b)
          (Literal.goodPlaneParabolic hn ξ)))) ∧
    (∀ (n : ℕ) (hn : 0 < n) (hodd : Odd n) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane),
      geoLinePairing n r b ξ = r (c⁻¹ * (
        (-((n + 1).factorial : ℂ) / 3) * LocalPairingCaseL0Odd.badGoodPairingOdd hodd (Literal.badLineParabolic hn b)
            (Literal.goodPlaneParabolic hn ξ) +
        ((n + 1).factorial : ℂ) * ParabolicDuality.LevelOne.parabolicPairing
          (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd) (Literal.goodLineParabolic hn b)
          (Literal.badPlaneParabolic hn hodd ξ)))) := by
  exact facePairing_geometric.elim (fun c hc => ⟨c, hc.1, hc.2.1, hc.2.2, fun n hn heven r b ξ =>
    (hc.2.1 n r b ξ).symm.trans (congrArg (fun z => r (c⁻¹ * z)) (facePairing_even_literal n hn heven b ξ)),
    fun n hn hodd r b ξ =>
    (hc.2.1 n r b ξ).symm.trans (congrArg (fun z => r (c⁻¹ * z)) (facePairing_odd_literal n hn hodd b ξ))⟩)

open TernaryPeriodPolynomials.Argument.Statements.FacePairing in
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality in
/-- The plane face, even `n`: the geometric plane pairing is `a = ±1` times the same cuspidal expression, with the opposite
face orientation `-c`. -/
theorem geoPlanePairing_literal_even (c : ℂ)
    (hP : ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line),
      r ((-c)⁻¹ * Plane.facePairingP n ξ b) = geoPlanePairing n r ξ b)
    (n : ℕ) (hn : 0 < n) (heven : Even n) :
    ∃ a : ℂ, (a = 1 ∨ a = -1) ∧ ∀ (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line),
      geoPlanePairing n r ξ b = r ((-c)⁻¹ * (a * ((((n + 1).factorial : ℂ) / 3) *
        LocalPairingCaseL0Even.badGoodPairingEven heven (Literal.badLineParabolic hn b)
          (Literal.goodPlaneParabolic hn ξ)))) :=
  (facePairingP_even_literal n hn heven).elim (fun a ha => ⟨a, ha.1, fun r ξ b =>
    (hP n r ξ b).symm.trans (congrArg (fun z => r ((-c)⁻¹ * z)) (ha.2 ξ b))⟩)

open TernaryPeriodPolynomials.Argument.Statements.FacePairing in
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality in
theorem geoPlanePairing_literal_odd (c : ℂ)
    (hP : ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line),
      r ((-c)⁻¹ * Plane.facePairingP n ξ b) = geoPlanePairing n r ξ b)
    (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    ∃ a : ℂ, (a = 1 ∨ a = -1) ∧ ∀ (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line),
      geoPlanePairing n r ξ b = r ((-c)⁻¹ * (a * (
        (-((n + 1).factorial : ℂ) / 3) * LocalPairingCaseL0Odd.badGoodPairingOdd hodd (Literal.badLineParabolic hn b)
            (Literal.goodPlaneParabolic hn ξ) +
        ((n + 1).factorial : ℂ) * ParabolicDuality.LevelOne.parabolicPairing
          (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd) (Literal.goodLineParabolic hn b)
          (Literal.badPlaneParabolic hn hodd ξ)))) :=
  (facePairingP_odd_literal n hn hodd).elim (fun a ha => ⟨a, ha.1, fun r ξ b =>
    (hP n r ξ b).symm.trans (congrArg (fun z => r ((-c)⁻¹ * z)) (ha.2 ξ b))⟩)

/-! ### (d) Face components -/

alias faceLine_eq_original := Glue.faceLine_eq_original
alias facePlane_eq_original := Glue.facePlane_eq_original

end TernaryPeriodPolynomials.Argument.Statements.FacePairingPD
