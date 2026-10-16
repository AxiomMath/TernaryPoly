module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneLevelDescentFull
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Transfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven

@[expose] public section


/-!
# The bad-plane paragraph of the proof of Proposition `thm:J-vanishes`, at the level `K†`

Formalized by Claude Sonnet 5.5.  Paper: "Let `P_0` be the stabilizer of the bad plane `⟨e₁,e₂⟩` in `K†`.  Its radical is `N_P = ⟨U₁₃,U₂₃⟩`,
its Levi quotient is `L_P ≅ GL₂(ℤ)`.  `H¹(N_P,E_n) = det⁻¹ Sym^{n+1}((ℚ²)*)`, `H²(N_P,E_n) = det⁻² Sym^n((ℚ²)*)`.  The two opposite binary unipotents have no common invariant in positive
degree, so the second module has no `L_P`-invariants.  The Levi has rational cohomological dimension one, leaving only the mixed restriction.  At a binary cusp the mixed edge map is injective for the
same dimension reason.  Flag vanishing therefore makes the plane class cuspidal."

All objects here are the paper's own, at the level `K†` (`rationalLevel`), over `ℂ`:
`P_0 = flagArithmeticStabilizer .plane (mk 1)` (the stabilizer of the identity plane `⟨e₁,e₂⟩`), `N_P = RadicalLattice` (`identityPlaneRadicalInclusion`), the Levi `GL₂(ℤ)` with its splitting
`identityPlaneSplitting`, and `E_n = identityPlaneCoefficientRep n` (`rationalCoefficientComponent n trivialCharacter` restricted to `P_0`: `Sym^n((ℂ³)*) ⊗ det⁻¹`).  The clauses are proved by assembling the
following library results:

* (a) `radicalH1_iso`: `H¹(N_P,E_n) ≅ det⁻¹ Sym^{n+1}` as `GL₂(ℤ)`-modules (`identityPlaneRadicalCoordinateIso`, the gradient calculation of the support proof), and
  `radicalH0_iso`: `H⁰(N_P,E_n) = E_n^{N_P} ≅ det⁻¹`.  `H²(N_P,E_n)` and the twisted tables over `ℚ` for the lattice model are in `BadPlaneTables.lean`.
* (b), (c) `radical_restriction_zero`: for `n > 0`, EVERY class of `H²(P_0,E_n)` restricts to zero on `N_P` (the projected alternation of a 2-cocycle on `N_P` is an `SL₂(ℤ)`-invariant of `Sym^n`,
  hence zero: this is the absence of `L_P`-invariants in positive degree, `IdentityPlaneEven.alternation_eq_zero`); `mixedEdge`, `mixedEdge_injective`: the Hochschild-Serre edge
  `H²(P_0,E_n) → H¹(GL₂(ℤ), det⁻¹ Sym^{n+1})` is defined on all of `H²(P_0,E_n)` and injective (`H²(GL₂(ℤ), det⁻¹) = 0`): only the mixed restriction survives.
* (d) `binary_cusp_edge_injective`: for the stabilizer `E_B = N_P ⋊ B` in `P_0` of the complete flag over `⟨e₁,e₂⟩` determined by a rational cusp, `B = cuspGL F ⊂ GL₂(ℤ)` (virtually cyclic, `H²(B,·)=0`
  for every complex representation, `hB_GL`), the mixed edge map of `E_B` is injective.
* (e) `cuspidal_iff_flags`: a class of `H²(P_0,E_n)` has zero radical restriction and mixed edge in the cuspidal group `badPlaneCuspidal n` (restriction to every binary cusp stabilizer of `H¹(GL₂(ℤ),
  det⁻¹Sym^{n+1})` zero) iff it restricts to zero on every flag stabilizer `E_{cuspGL F}`; `plane_class_cuspidal_of_flag_vanishing`: for a global `K†`-cocycle `c` whose class restricts to zero on the
  stabilizer of every complete flag, the Shapiro coordinate of its plane stratum at the bad plane is the image of a class `z ∈ H²(P_0,E_n)` with zero radical restriction and cuspidal mixed edge.
-/

open CategoryTheory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Spectral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.BadPlane

/-! ### (a) The cohomology of the radical `N_P` -/

/-- **(a), `H¹`:** `H¹(N_P, E_n) = det⁻¹ Sym^{n+1}((ℚ²)*)` as `L_P = GL₂(ℤ)`-modules. -/
def radicalH1_iso (n : ℕ) :
    splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRep n) ≅
      arithmeticBinaryRep (n + 1) (-1) :=
  identityPlaneRadicalCoordinateIso n

/-- **(a), `H⁰`:** `E_n^{N_P} = ℂ z^n`, on which `GL₂(ℤ)` acts by `det⁻¹`. -/
def radicalH0_iso (n : ℕ) :
    arithmeticDeterminantRep ≅
      splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRep n) :=
  identityPlaneInvariantIso n

/-! ### (b), (c) Only the mixed restriction survives -/

/-- **(b), (c): for `n > 0` every class of `H²(P_0, E_n)` restricts to zero on `N_P`.**  A 2-cocycle's projected alternation on `N_P` is an `SL₂(ℤ)`-invariant of `Sym^n ⊗ det⁻¹`
(`IdentityPlaneEven.alternation_modular_fixed`); the two opposite binary unipotents have no common invariant in positive degree (`ModularSymDimension.inf_fixed_eq_bot`). -/
theorem radical_restriction_zero (n : ℕ) (hn : 0 < n)
    (x : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) x = 0 :=
  IdentityPlaneEven.H2_restriction_zero n hn x

/-- **(c): the mixed edge** `H²(P_0, E_n) → H¹(GL₂(ℤ), det⁻¹ Sym^{n+1})`, defined on every class (`n > 0`). -/
def mixedEdge (n : ℕ) (hn : 0 < n) :
    groupCohomology.H2 (identityPlaneCoefficientRep n) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (identityPlaneBinaryEdge n).comp (LinearMap.id.codRestrict _ (radical_restriction_zero n hn))

/-- **(c): the mixed edge is injective** (`H²(GL₂(ℤ), det⁻¹) = 0`, "the Levi has cohomological dimension one"). -/
theorem mixedEdge_injective (n : ℕ) (hn : 0 < n) : Function.Injective (mixedEdge n hn) := by
  intro x y h
  exact congrArg Subtype.val (identityPlaneBinaryEdge_injective n h)

/-! ### (d) The binary cusps -/

/-- **(d): the mixed edge map at a binary cusp is injective.**  For a rational cusp `F ∈ GL₂(ℚ)` let `B = cuspGL F ⊂ GL₂(ℤ)` be its stabilizer; the stabilizer in `P_0` of the corresponding
complete flag over `⟨e₁,e₂⟩` is the preimage `E_B = N_P ⋊ B`.  The Hochschild-Serre edge of this split extension
(from the kernel of the radical restriction into `H¹(B, H¹(N_P,E_n))`) is injective, because `H²(B, ·) = 0` for all complex representations of the virtually cyclic group `B`. -/
theorem binary_cusp_edge_injective (n : ℕ) (F : GL (Fin 2) ℚ) :
    Function.Injective
      (splitCohomologyEdge (LocallyInner.splitRestrict identityPlaneSplitting (cuspGL F))
        (LocallyInner.resRep identityPlaneExtension (identityPlaneCoefficientRep n) (cuspGL F))) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero _ _ (fun x => hB_GL F _ x)

/-! ### (e) Flag vanishing makes the plane class cuspidal -/

/-- **(e), local form:** a class `z ∈ H²(P_0, E_n)` has zero radical restriction and mixed edge in the cuspidal group `badPlaneCuspidal n` (restriction to every binary cusp stabilizer
of `H¹(GL₂(ℤ), det⁻¹ Sym^{n+1})` zero) if and only if it restricts to zero on the stabilizer `E_{cuspGL F}` of every complete flag over the bad plane. -/
theorem cuspidal_iff_flags (n : ℕ) (z : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    (∃ hz : twoCohomologyRestriction identityPlaneExtension.inl (identityPlaneCoefficientRep n) z = 0,
        splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep n) ⟨z, hz⟩ ∈
          badPlaneCuspidal n) ↔
      ∀ F : GL (Fin 2) ℚ,
        twoCohomologyRestriction (LocallyInner.incl identityPlaneExtension (cuspGL F))
          (identityPlaneCoefficientRep n) z = 0 :=
  LocallyInner.cuspH2_iff_flags (identityPlaneCoefficientRep n) identityPlaneSplitting cuspGL
    (fun F V x => hB_GL F V x) z

/-- **(e), global form:** let `c` be a cocycle of `K†` with coefficients `E_n` whose class restricts to zero on the stabilizer of every complete flag (`Edges`).  Then the
Shapiro coordinate at the bad plane `⟨e₁,e₂⟩` of its plane stratum is the image, under the identification `badPlaneH2Equiv` of Mathlib's `H²(P_0,E_n)` with the homogeneous model, of a class `z`
with zero radical restriction and mixed edge in the cuspidal group `badPlaneCuspidal n`: the plane class is cuspidal. -/
theorem plane_class_cuspidal_of_flag_vanishing (n : ℕ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (h : ∀ e : Edges, resH2 (rationalCoefficientComponent n trivialCharacter)
      (FormClassK.fixedPointLevel_le_level e) (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0) :
    ∃ z : groupCohomology.H2 (identityPlaneCoefficientRep n),
      badPlaneH2Equiv n z =
          CuspReduction.cuspRes n trivialCharacter .plane false
            (globalCoordinates n trivialCharacter c).1 ∧
        ∃ hz : twoCohomologyRestriction identityPlaneExtension.inl (identityPlaneCoefficientRep n) z = 0,
          splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep n) ⟨z, hz⟩ ∈
            badPlaneCuspidal n := by
  have hinner := FormClassK.innerBoundary_of_edgeVanishing n trivialCharacter .plane c h
  have hloc := (innerBoundary_iff_locallyInner (globalCoordinates n trivialCharacter c).1).mp hinner
    (CuspOrbits.cuspFlag .plane false)
  let x : H2 (fixedPointLevel rationalLevel FacePairingFull.Face.badPlaneFlag)
      (rationalCoefficientComponent n trivialCharacter) :=
    CuspReduction.cuspRes n trivialCharacter .plane false (globalCoordinates n trivialCharacter c).1
  have hmem : badPlaneH2Equiv n ((badPlaneH2Equiv n).symm x) ∈
      locallyInnerClasses n trivialCharacter .plane FacePairingFull.Face.badPlaneFlag := by
    rw [LinearEquiv.apply_symm_apply]
    exact hloc
  exact ⟨(badPlaneH2Equiv n).symm x, LinearEquiv.apply_symm_apply _ _,
    (badPlaneH2Equiv_mem_locallyInner_iff_general n _).mp hmem⟩

end TernaryPeriodPolynomials.Argument.Identities.BadPlane
