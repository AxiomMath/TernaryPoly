module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.InnerVanishing
public import TernaryPeriodPolynomials.Polynomial.PositiveInnerVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.OrdinaryBoundaryConeConsumer
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConeMVZero
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConePairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.Inflation
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.CommonRootSupport
public import TernaryPeriodPolynomials.SymmetricSpace.Orientation.Determinant
public import TernaryPeriodPolynomials.BoundaryComparison.FiberModel

@[expose] public section


/-!
# Proposition 3.4 (`thm:boundary-evaluation`): the internal claims of its proof

Formalized by Claude Sonnet 5.5.

If `n > 0`, every
`K`-equivariant map `St → E_{n,t}` takes the identity apartment into `U_n`.  The proof has four steps, each
stated below with the library theorem proving it (the assembled statement is the target `support_principle`, and
`ordinary_functional_boundary_pairwise` below is its last step in the library's formulation):

1. *Passage to the boundary*: `H_c²(X_Γ',E) → H²(X_Γ',E)` is zero (`compact_support_to_ordinary_zero`;
   the library proves it for the principal level-six cover and the rational coefficient systems of the
   paper, `Statements.GeneralCoercivity` for all admissible `Γ`), the symmetric space `𝒳` has trivial
   orientation character (`orientation_determinant`: the congruence action on symmetric matrices has determinant
   `(det g)^4`), whence boundary homology surjects onto the top ordinary homology
   (`boundary_homology_surjects`), and `H₃(K,E)` is the coinvariants of `H₃(Γ',E)` under `K/Γ'`
   (`Statements.FiberModel.H3_K_descent_surjective`, `H3_K_descent_ker`).
2. *Face cocycles and radical invariance*: the mapping-cone model of the boundary and its
   Mayer-Vietoris sequence `eq:MV-boundary` (`cone_mv_connecting`, `cone_mv_faces`, `cone_mv_h0`), the adjointness
   of the cone differential and the dual chain differential (`cone_adjunction0`, `cone_adjunction1`,
   `cocycle_pair_boundary`, `gauge_pair_cycle`), `eq:inflated` (`plane_inflation`, `line_inflation`: face cocycles
   may be chosen to vanish on the radical with values fixed by the radical; this rests on
   `plane_radical_H1_invariants_zero`, `line_radical_H1_invariants_zero`, the vanishing of the Levi
   invariants of `H¹(N_R,M)`), and the invariants of the common root of two adjacent radicals have pairwise
   support (`common_root_invariant_pairwise`).
3. *Evaluation on the coordinate apartment*: every class has a cone representative `(A_P,A_Q,u)`
   with pairwise face and corner values (`class_pairwise_representative`), every functional annihilating
   `U_n` vanishes on them (`class_annihilator_representative`, the `λ ∈ U_n^⊥` of the paper), and the
   finite apartment cycle (six edges with the stated incidence signs, three face terms and the corner
   term) evaluates a normalized cone cocycle with pairwise support
   (`finite_apartment_pairwise`, `canonical_cocycle_finite_pairwise`).
4. *Conclusion*: `ordinary_functional_boundary_pairwise`.

**Model.**  The library works with the actual singular homology of the arithmetic quotient for the principal
level-six cover and the induced coefficient system `M = Ind_K^G E_{n,t}` (`restrictedCoefficients n e`, the
26-covector module), and with the group-cohomology cone model of the boundary for the Mayer-Vietoris and
corner arguments; the exports quote its theorems unchanged.
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.BoundaryEvaluation

open SymmetricSpaceAllTopBoundary OrdinaryBoundaryCone SymmetricSpaceBoundaryDuality
open SymmetricSpaceBoundaryFull

/-- **`H_c² → H²` vanishes** for the polynomial coefficient systems `E_{n,e}`, `n > 0`, on the
principal level-six cover: `PositivePolynomialInnerVanishing` is, by definition,
`∀ n > 0, ∀ e, compactForget interiorCover (polynomialCoefficients n e) 2 = 0`, the actual singular
compact-support-to-ordinary map in degree two. -/
theorem compact_support_to_ordinary_zero : PositivePolynomialInnerVanishing :=
  positivePolynomialInnerVanishing

/-- **Trivial orientation character:** `Q ↦ gᵀQg` on symmetric matrices has determinant
`(det g)^4`. -/
alias orientation_determinant :=
  SymmetricSpaceOrientation.congruence_det

/-- **Boundary homology surjects onto ordinary top homology:** for `n > 0` and every
determinant exponent, the map from the homology of the whole boundary to the top ordinary homology of the
quotient, for the 26-covector coefficient system, is surjective. -/
theorem boundary_homology_surjects (n : ℕ) (hn : 0 < n) (e : ℤ) :
    Function.Surjective (boundaryToGroup (restrictedCoefficients n e) 3).hom :=
  OrdinaryBoundaryActualEvaluation.coefficient_boundary_surjective_of_inner_vanishing
    positivePolynomialInnerVanishing n hn e


/-- Pro memoria for the finite-cover descent `H₃(K,E) ≅ H₃(Γ',E)_Δ` of the paper: the corestriction
`H₃(Γ(6),E) → H₃(K,E)` is surjective and its kernel is the kernel of the averaging operator
(`Statements.FiberModel.H3_K_descent_surjective`, `H3_K_descent_ker`), compatibly with the boundary map. -/
alias finite_cover_descent_surjective := FiberModel.H3_K_descent_surjective

/-- **Mayer-Vietoris, `H¹(∂) → H¹(P) ⊕ H¹(Q)` (`eq:MV-boundary`), mapping-cone model:** the image
of the corner invariants `H⁰(B₀,M)` is the kernel of the map to the face classes. -/
alias cone_mv_connecting := OrdinaryBoundaryCone.range_connecting_eq_ker_toFaces

/-- **Mayer-Vietoris, exactness at `H¹(P) ⊕ H¹(Q)`:** a pair of face classes comes from the cone iff its restrictions
to the corner agree. -/
alias cone_mv_faces := OrdinaryBoundaryCone.range_toFaces_eq_ker_restrictionDifference

/-- **Mayer-Vietoris, exactness at `H⁰(B₀,M)`:** a pure corner class vanishes iff it is a difference of face
invariants. -/
alias cone_mv_h0 := OrdinaryBoundaryCone.connecting_eq_zero_iff

/-- **Adjointness of the cone differential and the dual chain differential, degree zero.** -/
alias cone_adjunction0 := OrdinaryBoundaryCone.cone_adjunction0

/-- The same in degree one. -/
alias cone_adjunction1 := OrdinaryBoundaryCone.cone_adjunction1

/-- A cone cocycle annihilates every finite cone boundary. -/
alias cocycle_pair_boundary := OrdinaryBoundaryCone.cocycle_pair_boundary

/-- The cone pairing is gauge invariant on finite cone cycles. -/
alias gauge_pair_cycle := OrdinaryBoundaryCone.gauge_pair_cycle

/-- **The Levi-invariants of `H¹(N_P,M)` vanish**, for every `n` and every determinant exponent:
two opposite root unipotents of the Levi have no common invariant. -/
alias plane_radical_H1_invariants_zero := OrdinaryFaceRadical.actualPlane_radical_H1_invariants_zero

/-- The same for the line radical. -/
alias line_radical_H1_invariants_zero := OrdinaryFaceRadical.actualLine_radical_H1_invariants_zero

open OrdinaryParabolicGroups OrdinaryBoundaryCommonRoot LowDegreeHochschildSerre
open BoundaryCochainNormalization RadicalFirstCohomologyLattice

/-- **`eq:inflated` for the plane face:** every `1`-cocycle of the plane parabolic with
coefficients in the 26-covector module is cohomologous to one that vanishes on the radical and takes values
fixed by the radical, i.e. factors through the Levi with values in `M^{N_R}`. -/
theorem plane_inflation (n : ℕ) (e : ℤ)
    (c : groupCohomology.cocycles₁ (Rep.of (planeParabolicCoefficients n e))) :
    ∃ u : Coefficients n,
      (∀ r : planeRadical, normalize (Rep.of (planeParabolicCoefficients n e)) c u
        (planeEquiv (SemidirectProduct.inl r)) = 0) ∧
      ∀ g, normalize (Rep.of (planeParabolicCoefficients n e)) c u g ∈
        Representation.invariants ((coefficientAction n e).comp planeRadical.subtype) :=
  OrdinaryFaceInflation.plane_normalized n e
    (fun v hv => OrdinaryFaceRadical.actualPlane_radical_H1_invariants_zero n e v hv) c

/-- **`eq:inflated` for the line face.** -/
theorem line_inflation (n : ℕ) (e : ℤ)
    (c : groupCohomology.cocycles₁ (Rep.of (lineParabolicCoefficients n e))) :
    ∃ u : Coefficients n,
      (∀ r : lineRadical, normalize (Rep.of (lineParabolicCoefficients n e)) c u
        (lineEquiv (SemidirectProduct.inl r)) = 0) ∧
      ∀ g, normalize (Rep.of (lineParabolicCoefficients n e)) c u g ∈
        Representation.invariants ((coefficientAction n e).comp lineRadical.subtype) :=
  OrdinaryFaceInflation.line_normalized n e
    (fun v hv => OrdinaryFaceRadical.actualLine_radical_H1_invariants_zero n e v hv) c

/-- **Invariants of the common root have pairwise support:** if `F` is fixed by the common root
subgroup `{I + aE₁₃}` of two adjacent maximal radicals, then `F(ℓ)` lies in `U_n`. -/
alias common_root_invariant_pairwise := OrdinaryBoundaryCommonRoot.invariant_evaluation_pairwise

/-- **Mapping-cone representative with pairwise values:** every class of the cone has a
representative `(A_P, A_Q, u)` with `A_P`, `A_Q`, `u` taking pairwise (two-variable) values. -/
alias class_pairwise_representative := OrdinaryBoundaryCone.actual_class_pairwise_representative

/-- **Every functional annihilating `U_n` vanishes on a representative.** -/
alias class_annihilator_representative := OrdinaryBoundaryCone.actual_class_annihilator_representative

/-- **The finite apartment cycle:** the six edges `(1,2,3), (2,1,3), (2,3,1), (3,2,1), (3,1,2),
(1,3,2)` with signs `+,-,+,-,+,-`, three face terms and the corner term: a normalized cone cocycle
with pairwise face and corner values evaluates the cycle with pairwise support. -/
alias finite_apartment_pairwise := OrdinaryBoundaryActualEvaluation.finiteApartmentChain_pairwise

/-- The finite apartment evaluation of an arbitrary cocycle of the canonical cone. -/
alias canonical_cocycle_finite_pairwise := OrdinaryBoundaryActualEvaluation.canonicalCocycle_finite_pairwise

/-- The finite apartment evaluation of an arbitrary cocycle of the full boundary cone. -/
alias full_boundary_cocycle_finite_pairwise :=
  OrdinaryBoundaryActualEvaluation.fullBoundaryCocycle_finite_pairwise

/-- **Conclusion of the evaluation step:** a full-equivariant ordinary functional whose
top homology class comes from the boundary has pairwise reference coefficient. -/
alias ordinary_functional_boundary_pairwise :=
  OrdinaryBoundaryActualEvaluation.ordinary_functional_boundary_pairwise

end TernaryPeriodPolynomials.Argument.Statements.BoundaryEvaluation
