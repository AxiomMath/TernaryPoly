module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.Core
public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.Cohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.Action
public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.Faces
public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.KDagger
public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.KDaggerHomog

@[expose] public section


/-!
# The Hochschild-Serre right edge

Formalized by Claude Sonnet 5.5.

Paper: Appendix C,: for a maximal-face stabilizer `R = N_R ⋊ L_R`, "only the `(1,1)` and `(0,2)` terms survive in total degree two
because `L_R` has rational cohomological dimension one", i.e.

    0 → H¹(L_R, H¹(N_R, E)) → H²(R, E) --res_{N_R}--> H²(N_R, E)^{L_R} → 0.

The left half (injectivity and surjectivity of the edge) was in the library (`Statements.GammaNFacesFull`, `SeedC3S4c.faceEdge_injective`); this file exports the right end.

## What is proved

* **Generic theorem** `right_edge_iff`, `right_edge_range`: for a split group extension `ext` of `L` by `N` with splitting `s` and `ρ : Rep ℂ E`, if the complex degree-two cohomology of `L`
  vanishes in all coefficients (`H2Vanishes L`, from the library's `LeviH2Vanishes`), then
  `y ∈ range (twoCohomologyRestriction ext.inl ρ) ↔ ∀ l, splitRadicalH2Action s ρ l y = y`, i.e. `range res = splitRadicalH2Invariants s ρ`.
* **The Levi action on `H²(N, E)`** `splitRadicalH2Action` (degree-two analogue of `splitRadicalH1Action`: transport along `conjAct(l⁻¹)` with the coefficient map `ρ(s l)`;
  `(l·z)(a,b) = ρ(s l) z(l⁻¹ a l, l⁻¹ b l)`): `splitRadicalH2Action_one`, `_mul` (an action; bundled as `splitRadicalH2Representation`) and
  `splitRadicalH2Action_splitting_indep` (independent of the lift `s l`: two lifts differ by an element of `N`, which acts trivially on `H²(N, E|_N)`).
* **Both inclusions**: `restriction_invariant` (the image is invariant: inner automorphisms of `E` act trivially on `H²(E, ρ)`, the `GammaNStokes.h2Map_conj_self`) and `exists_lift` (every
  invariant class lifts: the content).
* **Proof route** (no spectral sequence, no `H³`): `RightEdge.Core`: `lift_crossed` is the degree-ONE right edge (an `L`-invariant crossed homomorphism `N → W` extends to `R` when `H²(L, ·) = 0`;
  the obstruction lies in `H²(L, W^N)`), and dimension shifting through the right-translation module `U = Map(R, V) ⊇ V` (`mapShiftData`, `N`-acyclic in degrees one and two by the explicit
  contracting homotopies `ξ(a)(l n) = ρ(l) z(n, a)`, `u(l n) = ξ(n)(l)`) reduces degree two for `V` to degree one for `U/V` (`right_edge_cochain`, `right_edge_cochain_map`).
* **The actual face groups**: `face_right_edge`, `lineFace_right_edge`, `gammaN_right_edge`, `line_right_edge` (the plane and line cusps `h⁻¹Ph`, `h⁻¹Qh` of `Γ(N)` and the standard faces,
  `L = Γ₂(N) ≤ SL₂(ℤ)` by `GammaNFacesFull.leviH2Vanishes_subgroup`), the full short exact sequences `face_hochschild_serre`, `lineFace_hochschild_serre` (edge bijective and `range res = invariants`),
  and `semidirect_right_edge` for the semidirect faces of the model `FacePairingFull.Face` (Levi embedded in `GL₂(ℤ) × ℤˣ`), instantiated in `KDagger` for the four reference faces
  (`badLine_right_edge`, `goodLine_right_edge`, `badPlane_right_edge` (identity plane), `goodPlane_right_edge`) and every degree and character, and in the HOMOGENEOUS model of the actual K†
  stabilizers `KDaggerHomog`: `face_homogeneous_right_edge` and `badLine_homogeneous_right_edge`, `goodLine_…`, `badPlane_…`, `goodPlane_…` (a class of the library's `H²(N_F, E)` is the radical restriction
  `radicalRestrictionH2 ∘ faceH2Equiv` of a homogeneous class of `H²(Γ_F, E)` iff it is invariant under the Levi action `leviH2ActionInh`).

## What is NOT proved

* Nothing beyond the statement file is claimed; the compactly-supported / cuspidal refinements of the faces are in `Statements.GammaNFacesFull` and `Statements.FacePairingPD`.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.RightEdge

open TernaryPeriodPolynomials.Argument.RightEdge

alias right_edge_generic := right_edge_iff
alias right_edge_range_eq_invariants := right_edge_range
alias levi_h2_action := splitRadicalH2Action
alias levi_h2_action_one := splitRadicalH2Action_one
alias levi_h2_action_mul := splitRadicalH2Action_mul
alias levi_h2_action_independent_of_splitting := splitRadicalH2Action_splitting_indep
alias image_of_restriction_invariant := restriction_invariant
alias invariant_class_lifts := exists_lift
alias degree_one_right_edge := lift_crossed
alias right_edge_cochains := right_edge_cochain_map
alias plane_face_right_edge := face_right_edge
alias line_face_right_edge := lineFace_right_edge
alias plane_face_hochschild_serre := face_hochschild_serre
alias line_face_hochschild_serre := lineFace_hochschild_serre
alias semidirect_face_right_edge := semidirect_right_edge
alias bad_line_right_edge := badLine_right_edge
alias good_line_right_edge := goodLine_right_edge
alias identity_plane_right_edge := badPlane_right_edge
alias good_plane_right_edge := goodPlane_right_edge
alias kdagger_face_right_edge := face_homogeneous_right_edge
alias bad_line_right_edge_homogeneous := badLine_homogeneous_right_edge
alias good_line_right_edge_homogeneous := goodLine_homogeneous_right_edge
alias identity_plane_right_edge_homogeneous := badPlane_homogeneous_right_edge
alias good_plane_right_edge_homogeneous := goodPlane_homogeneous_right_edge

end TernaryPeriodPolynomials.Argument.Statements.RightEdge
