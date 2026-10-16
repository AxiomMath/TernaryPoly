module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatApartment
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Flat.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatEpsilon

@[expose] public section


/-!
# Lemma 3.3 (`lem:apartment-boundary-pairing`): geometric Poincaré--Lefschetz comparison

Exports of the steps of the geometric comparison; the library-model diagram
`Exports/AppendixLemmas.apartment_boundary_diagram` is

* (b) `apartment_evaluation_eq_pairing`: the group evaluator `groupApartmentEvaluation W (j_* c)` equals
  `⟨PD(j_* c), a⟩` for every relative class `a`
  with `∂a` the coordinate apartment, so the pairing depends only on `∂a`;
* (G1) `flat_boundary_class`: the compactified diagonal flat `{diag(a,b,(ab)⁻¹)}` is an honest
  singular relative 2-chain of the pair `(M̄, ∂M̄)` (six Weyl chambers, each in its Borel corner
  chart, glued along their walls), whose relative class has boundary the coordinate apartment;
* `evaluation_connecting`: `⟨δ^* ω, a⟩ = ⟨ω, ∂a⟩` for every `a`.

* (G3, global half) `flat_intersection_bridge` and `apartment_evaluation_eq_coefficient`:
  unconditionally, there is a nonzero rational constant such that the top evaluator of the class of every
  cellular top cycle `z` (any coefficient system) equals that constant times the coefficient of `z` at the
  standard top cell `T₀`, i.e. times the intersection number of `z` with the flat; a cycle with vanishing
  coefficient at `T₀` has zero evaluator.  The numerical value of the constant (orientation, "local
  intersection number +1") is not part of these statements.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma33Geometric

open TernaryPeriodPolynomials.Argument.Lemma33

/-- **Lemma 3.3, step (b).** The top evaluation of a boundary class equals its Poincaré--Lefschetz
pairing with any relative class bounding the coordinate apartment. -/
theorem apartment_evaluation_eq_pairing (W : Rep.{0} ℚ principalSix)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
    (a : OrdinaryTopBoundaryComparison.upstairsRelativeChains.homology 2)
    (ha : OrdinaryTopBoundaryComparison.upstairsRelativeSequence_shortExact.δ 2 1 rfl a =
      OrdinaryTopBoundaryComparison.identityApartmentBoundaryClass) :
    OrdinaryTopBoundaryComparison.groupApartmentEvaluation W
        (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c) =
      (OrdinaryTopBoundaryComparison.homologyEvaluation
        OrdinaryTopBoundaryComparison.upstairsRelativeChains W 2
        ((OrdinaryTopBoundaryComparison.relativeHomCapIso W).inv
          (HomologicalComplex.homologyMap (SingularLocalHomology.boundaryInclusionMap W) 3 c))).hom a :=
  TernaryPeriodPolynomials.Argument.Lemma33.apartment_evaluation_eq_pairing W c a ha

/-- **Lemma 3.3, step G1.** The compactified diagonal flat defines a relative homology class of the
pair `(bordification, boundary)` whose connecting homomorphism is the coordinate apartment class of
the boundary. -/
theorem flat_boundary_class :
    ∃ a : OrdinaryTopBoundaryComparison.upstairsRelativeChains.homology 2,
      OrdinaryTopBoundaryComparison.upstairsRelativeSequence_shortExact.δ 2 1 rfl a =
        OrdinaryTopBoundaryComparison.identityApartmentBoundaryClass :=
  ⟨TernaryPeriodPolynomials.Argument.Lemma33.flatClass,
    TernaryPeriodPolynomials.Argument.Lemma33.delta_flatClass⟩

/-- The singular boundary of the compactified flat chain is the hexagon of twelve arcs (the
interior walls and diagonals cancel). -/
theorem flat_chain_boundary :
    ((TernaryPoly.EquivariantSingularResolution.underlyingChains
        (TopCat.of TernaryPoly.SymmetricSpaceRationalGluing.Glued)).d 2 1).hom
        TernaryPeriodPolynomials.Argument.Lemma33.flatChain =
      TernaryPeriodPolynomials.Argument.Lemma33.hexBoundary :=
  TernaryPeriodPolynomials.Argument.Lemma33.d_flatChain

/-- **Lemma 3.3, the first arrow with the geometric flat.** The top evaluator of a boundary class
`j_* c` is the Kronecker pairing of its Poincaré--Lefschetz dual with the relative class of the
compactified diagonal flat (intersection with the flat). -/
theorem apartment_evaluation_eq_flat_pairing (W : Rep.{0} ℚ principalSix)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3) :
    OrdinaryTopBoundaryComparison.groupApartmentEvaluation W
        (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c) =
      (OrdinaryTopBoundaryComparison.homologyEvaluation
        OrdinaryTopBoundaryComparison.upstairsRelativeChains W 2
        ((OrdinaryTopBoundaryComparison.relativeHomCapIso W).inv
          (HomologicalComplex.homologyMap (SingularLocalHomology.boundaryInclusionMap W) 3 c))).hom
        TernaryPeriodPolynomials.Argument.Lemma33.flatClass :=
  TernaryPeriodPolynomials.Argument.Lemma33.apartment_evaluation_eq_pairing W c _
    TernaryPeriodPolynomials.Argument.Lemma33.delta_flatClass

/-- The geometric class of the compactified flat is the algebraic relative apartment class (the
bordification is contractible, so the connecting map is an isomorphism). -/
theorem flatClass_eq_apartmentRelativeClass :
    TernaryPeriodPolynomials.Argument.Lemma33.flatClass =
      OrdinaryTopBoundaryComparison.identityApartmentRelativeClass :=
  TernaryPeriodPolynomials.Argument.Lemma33.flatClass_eq_identityApartmentRelativeClass

/-- **Intersection with the flat reads the top evaluator**: for every capped relative class, the
top evaluator is the evaluation on the class of the compactified flat. -/
theorem flat_intersection_reads_evaluation (W : Rep.{0} ℚ principalSix)
    (x : (EquivariantSingularSmall.homCochains OrdinaryTopBoundaryComparison.upstairsRelativeChains W).homology 2) :
    OrdinaryTopBoundaryComparison.groupApartmentEvaluation W
        ((SingularLocalHomology.bordifiedGroupLocalHomologyIso W 3).inv
          ((OrdinaryTopBoundaryComparison.relativeHomCapIso W).hom x)) =
      (OrdinaryTopBoundaryComparison.homologyEvaluation
        OrdinaryTopBoundaryComparison.upstairsRelativeChains W 2 x).hom
        TernaryPeriodPolynomials.Argument.Lemma33.flatClass := by
  rw [flatClass_eq_apartmentRelativeClass]
  exact OrdinaryTopBoundaryComparison.cappedClass_apartmentEvaluation W x

/-- **Lemma 3.3, the collar comparison, with every convention explicit.**

* the boundary fundamental class is the literal connecting image `∂[X̄, ∂X̄]` of the relative
  fundamental class, and the local generators are the literal connecting-to-point images (the
  collar/outward-normal-first orientation convention of the boundary, `boundaryOrientation`);
* the cap square `ordinary_cap_connecting` commutes with the sign `±1` that it records (no sign is introduced here):
  `j_* ∘ (∩ [∂X̄]) = (∩ [X̄, ∂X̄]) ∘ ∂^*` on boundary `H¹` into `H₃`, for every local coefficient system;
* hence for `z = j_* c` the top evaluator is the Kronecker pairing of `PD_∂ c` with the boundary of
  the geometric flat. -/
theorem collar_comparison (W : Rep.{0} ℚ principalSix)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3) :
    SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass =
        RationalRelativeSingular.connecting (SymmetricSpaceBordifiedQuotient.boundary principalSix) 4
          SymmetricSpaceRelativeFundamental.fundamentalClass ∧
      (∀ x, SymmetricSpaceBoundaryOrientation.boundaryGenerator x =
        (RationalRelativeSingular.connecting (SymmetricSpaceBordifiedQuotient.boundary principalSix) 4 ≫
          HomologicalComplex.homologyMap (HalfSpaceBoundaryOrientation.absolutePointProjection x) 4)
            SymmetricSpaceRelativeFundamental.fundamentalClass) ∧
      ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso W
          SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom ≫
        HomologicalComplex.homologyMap (SingularLocalHomology.boundaryInclusionMap W) 3 =
          SymmetricSpaceRelativeCapConnecting.geometricBoundaryConnecting W 1 ≫
            SymmetricSpaceRelativeCapConnecting.relativeFundamentalCap W) ∧
      OrdinaryTopBoundaryComparison.groupApartmentEvaluation W
          (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c) =
        (OrdinaryTopBoundaryComparison.homologyEvaluation
          SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W 1
          ((OrdinaryBoundaryActualEvaluation.boundaryCohomologyIso W).inv
            ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso W
              SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv c))).hom
          (OrdinaryTopBoundaryComparison.upstairsRelativeSequence_shortExact.δ 2 1 rfl
            TernaryPeriodPolynomials.Argument.Lemma33.flatClass) :=
  ⟨rfl, fun _ => rfl, SymmetricSpaceRelativeCapConnecting.ordinary_cap_connecting W, by
    rw [TernaryPeriodPolynomials.Argument.Lemma33.delta_flatClass]
    exact OrdinaryBoundaryActualEvaluation.boundary_image_apartment W c⟩

open TernaryPeriodPolynomials.Argument.Lemma33.Retract in
/-- **Lemma 3.3, the global bridge (unconditional).**  There is a nonzero rational `κ` such that for every
coefficient representation `W` of `Γ(6)` and every cellular top cycle `z`, the top evaluator of the class of
`z` is `κ` times the intersection sum of `z` with the flat. -/
theorem flat_intersection_bridge :
    ∃ κ : ℚ, κ ≠ 0 ∧ ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
      (hz : ((cellCoinv W).d 3 2).hom z = 0),
      OrdinaryTopBoundaryComparison.groupApartmentEvaluation W
          ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) = κ • (intersectionSum W).hom z :=
  TernaryPeriodPolynomials.Argument.Lemma33.Locality.flatIntersectionBridge_exists

open TernaryPeriodPolynomials.Argument.Lemma33.Retract in
/-- **Lemma 3.3, the coefficient dictionary (unconditional).**  There is a nonzero rational `c` such that for
every coefficient representation `W` and every cellular top cycle `z`, the top evaluator of the class of `z`
is `c` times the coefficient of `z` at the standard top cell `T₀` (the intersection of `z` with the flat). -/
theorem apartment_evaluation_eq_coefficient :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
      (hz : ((cellCoinv W).d 3 2).hom z = 0),
      OrdinaryTopBoundaryComparison.groupApartmentEvaluation W
          ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) = c • (coeffAtT0 W).hom z := by
  obtain ⟨κ, hκ, hB⟩ :=
    TernaryPeriodPolynomials.Argument.Lemma33.Locality.flatIntersectionBridge_exists
  refine ⟨κ * LocalDegree.dT0, mul_ne_zero hκ
    TernaryPeriodPolynomials.Argument.Lemma33.Orient.dT0_ne_zero, ?_⟩
  intro W z hz
  exact evaluation_eq_coeffAtT0 hB W z hz

open TernaryPeriodPolynomials.Argument.Lemma33.Retract in
/-- **Lemma 3.3, orientation transport (P2).**  The dictionary constant `κ · dT0` of
`apartment_evaluation_eq_coefficient` is `d₅ · ε`: `d₅` is the library degree of the positive product cell
(the staircase triangulation of tetrahedron × triangle, `OrientTransport.d5`), `ε = - τ / lam2` where `τ` is the
value of the pulled-back planar Thom cochain on the chart chain of the flat, i.e. minus the degree of the flat over the
positive reference triangle (`lam2`, the library degree of that triangle).  All constants are nonzero.  In the orientation
of `M` for which the positive product cell has degree one (`d₅ = 1`) the constant is `ε`; the value of `τ / lam2`
(the orientation of the formal flat chain relative to the plane coordinates) is computed in `apartment_orientation_sign`. -/
theorem apartment_orientation_transport :
    ∃ (κ τ : ℚ), κ ≠ 0 ∧ FlatIntersectionBridge κ ∧
      TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.d5 ≠ 0 ∧ τ ≠ 0 ∧
      κ * LocalDegree.dT0 =
        TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.d5 *
          (-(TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.flatDegree τ)) :=
  TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.apartment_orientation_transport

open TernaryPeriodPolynomials.Argument.Lemma33.Retract in
/-- **Lemma 3.3, the orientation transport in product form**: `lam2 · (κ · dT0) = - d₅ · τ`. -/
theorem lam2_mul_kappa_dT0 :
    ∃ (κ τ : ℚ), κ ≠ 0 ∧ FlatIntersectionBridge κ ∧
      TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.lam2 * (κ * LocalDegree.dT0) =
        -(TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.d5 * τ) :=
  TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.lam2_mul_kappa_dT0

open TernaryPeriodPolynomials.Argument.Lemma33.Retract in
/-- **Lemma 3.3, the sign of the orientation transport (P2).**  The chart chain of the formal flat
(six Weyl chambers with alternating signs, in the log-pivot plane coordinates `rho = (log a, log b)`) has planar degree
exactly that of the positive reference triangle (`flatDegree τ = τ / lam2 = 1`), so the dictionary constant is
`κ · dT0 = - d₅`, i.e. `ε = -1`: since the standard top cell has `dT0 = - lamPos`
(`dT0_eq_neg_lamPos`), the paper's `+1` is matched only up to this sign convention for the
orientation of the standard cell against the positive product cell. -/
theorem apartment_orientation_sign :
    ∃ (κ τ : ℚ), κ ≠ 0 ∧ FlatIntersectionBridge κ ∧
      TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.flatDegree τ = 1 ∧
      κ * LocalDegree.dT0 = -TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.d5 :=
  TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.apartment_orientation_sign

open TernaryPeriodPolynomials.Argument.Lemma33.Retract in
/-- **Lemma 3.3, the values of the constants (P2).**  The intersection constant of the global bridge is
`κ = d₅ / lamPos` and the dictionary constant is `κ · dT0 = - d₅`, where `d₅`, `lamPos` are the (non-zero) library degrees
of the staircase product cell and of the positive reference tetrahedron.  Their absolute values depend on the normalization of
the library's local top homology `localTopIso` (built from the choice `zeroReducedHomologyIso`), so `|κ| = 1` and `|c| = 1` are not
statements the library can decide; the relation to the paper's `+1` is the sign convention `c = - d₅`. -/
theorem apartment_constant_values :
    ∃ κ : ℚ, κ ≠ 0 ∧ FlatIntersectionBridge κ ∧
      κ * TernaryPeriodPolynomials.Argument.Lemma33.Orient.lamPos =
        TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.d5 ∧
      κ * LocalDegree.dT0 = -TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.d5 ∧
      TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.d5 ≠ 0 ∧
      TernaryPeriodPolynomials.Argument.Lemma33.Orient.lamPos ≠ 0 ∧
      TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.lam2 ≠ 0 :=
  TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.apartment_constant_values

open TernaryPeriodPolynomials.Argument.Lemma33.Retract in
/-- **Lemma 3.3, the coefficient dictionary with its explicit constant**: the top evaluator of a cellular top cycle is
`- d₅` times its coefficient at the standard top cell `T₀`. -/
theorem apartment_evaluation_eq_neg_d5_coefficient :
    ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
      OrdinaryTopBoundaryComparison.groupApartmentEvaluation W
          ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
        (-TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.d5) • (coeffAtT0 W).hom z :=
  TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.apartment_evaluation_eq_neg_d5_coefficient

/-- **The local degree of the positive reference triangle is non-zero.** -/
theorem lam2_ne_zero :
    TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.lam2 ≠ 0 :=
  TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport.lam2_ne_zero

end TernaryPeriodPolynomials.Argument.Statements.Lemma33Geometric
