module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Apartment
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Cap
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Transfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SymbolEquiv
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BinaryHeckeComparison
public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Flat.Geometry
public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Flat.Orientation

@[expose] public section


/-!
# Literal exports for Lemma 3.3, Lemma A.1 and Lemma B.1

Paper:.

## Lemma 3.3 (`lem:apartment-boundary-pairing`)

The library's model of the paper's objects, for a rational coefficient system
`W : Rep ℚ principalSix` (the level-six cover on which every later argument is carried out):

* `H₃(∂X̄_G; M)`  is `(boundaryLocalChains W).homology 3` (genuine geometric chains on the entire
  actual arithmetic boundary, all corner strata included);
* `H₃(X̄_G; M)` is the group homology `groupHomology W 3`, identified with the bordified local
  chains by `bordifiedGroupLocalHomologyIso`; `j_*` is `boundaryToGroup`;
* `PD_∂ : H₃(∂) → H¹(∂)` is the inverse of the actual boundary cap isomorphism `boundaryH1CapIso`
  (cap product with the literal boundary fundamental class `boundaryOrientation`), followed by the
  identification `boundaryCohomologyIso` of geometric and equivariant boundary cohomology;
* the right arrow `z ↦ φ(F_z)` is `groupApartmentEvaluation`: the actual cap isomorphism
  `groupOrdinaryIso : H₃(G, W) ≅ ordinaryFunctionals W` (equivariant maps from the Steinberg
  module), followed by evaluation at the identity apartment;
* the bottom arrow `ω ↦ ⟨ω, ∂a⟩` is the canonical pairing `homologyEvaluation` of a boundary
  cohomology class with the boundary homology class `identityApartmentBoundaryClass` of the
  coordinate apartment (the hexagon `L₁, P₁₂, L₂, P₂₃, L₃, P₃₁`), and the compactified flat `a` is
  the relative class `identityApartmentRelativeClass` whose connecting image is that apartment
  (`identityApartmentRelativeClass_connecting`): "the boundary of the flat represents the coordinate
  apartment" holds by construction in this model.

Model difference, stated explicitly: the library does not contain the geometric flat
`{diag(a, b, (ab)⁻¹)} ⊂ 𝒳` or its local intersection numbers with the top cell. The statement
"intersection with the flat reads the top-cell coefficient" is replaced by the library's
definition of the top evaluator through the actual relative cap and the identity apartment class,
and it is proved in that form (`cappedClass_apartmentEvaluation`). Poincaré--Lefschetz duality is
the genuine compact cap duality of `CompactOrdinaryCapDuality`.

The geometric facts used in the paper's local calculation of the flat are proved separately
(`flat_meets_cells_iff`, `flat_cell_eq_identity`, `identity_minimal_vectors`,
`flat_cell_transverse`): the determinant-one diagonal flat `diag(a, b, (ab)⁻¹)` meets the union of
the top cells of the well-rounded retract exactly at the identity form (a diagonal form is well
rounded only when its three entries agree), whose shortest vectors are exactly `±e_i`, and its
tangent space at the identity is complementary to that of the standard cell (transversality).
The orientation characters of the stabilizer of the identity apartment (signed permutations) on the
cell and on the flat are proved (`apartment_cell_orientation_character`,
`apartment_flat_orientation_character`, `apartment_cell_flat_frame_det`): the local intersection
numbers assemble with the permutation-sign character, and `+1` for coordinate sign changes. The
global orientation normalizations (local intersection number `+1` at the standard cell) are
conventions, and the intersection numbers of chains in the symmetric space remain outside the
library's combinatorial model.

## Lemma B.1 (`lem:literal-residue-comparison`), in the library's Hom model

After cap duality `H₃(G, W) ≅ Hom_G(St₃, W)` (`groupOrdinaryIso`) and `H₁(GL₂(ℤ), M) ≅
Hom_{GL₂(ℤ)}(St₂, M)`, the objects of the diagram (`eq:residue-comparison-diagram`) are:

* `H₃(G, 𝓡_n ⊗ det)` is `OrdinaryFullCoefficient.ResidueHom n (-1)` (equivariant maps from the
  ordinary cycle module into the direct-sum residue module `Residues n`, determinant exponent `-1`);
* `H₁(GL₂(ℤ), D_{n+1})` is `BinaryModularSymbol.PeriodHom (n+1)`;
* `res_H` (reading the literal `1/a` residue, in the coordinates `b, c`) is the literal coordinate
  `OrdinaryFullCoefficient.coordinatePeriod n 0` (= `OrdinaryResiduePeriod.periodEquiv n`),
  valued in `ℬ_{n+1} = OrdinaryResiduePeriod.periodSpace (n+1)`;
* `edge_2` (the coefficient of the standard binary well-rounded edge) is the reference evaluation
  `BinaryModularSymbol.periodEvaluation (n+1)`;
* `κ ∘ Sh` is `OrdinaryResidueSymbol.toBinaryHom n`, the restriction of a residue functional to the
  plane cone of binary cycles (`binaryCone`) followed by the zero-coordinate fibre.

Model difference, stated explicitly: the library does not contain Shapiro's lemma for group
HOMOLOGY at the stabilizer `P_H`, nor the Hochschild--Serre edge `κ` for `P_H = ℤ² ⋉ GL₂(ℤ)` as
separate maps; their composite is replaced by the explicit restriction `toBinaryHom`, which is a
linear equivalence (`toBinaryHom_surjective`, `toBinaryHom_injective`) commuting with the Hecke
operators (`toBinaryHom_prime`). The diagram then commutes with the literal normalizations of the
library, i.e. with scalar exactly `1` (`residue_comparison_diagram`), and the composite is the
period polynomial of `ℬ_{n+1}`, which satisfies the four literal symmetric, separately odd and
period relations (`mem_periodSpace`). The cell calculation of the ternary retract (Voronoi
inequalities) is not needed in this model, where the reference evaluation is by definition the
coefficient of the standard apartment.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex
open TernaryPoly.IntegralGL3Congruence
open TernaryPoly.EquivariantSingularSmall TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalHomology
open TernaryPoly.SymmetricSpaceBoundaryManifold TernaryPoly.SymmetricSpaceBoundaryOrientation
  TernaryPoly.SymmetricSpaceBoundaryDuality
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.OrdinaryTopBoundaryComparison
open TernaryPoly.OrdinaryBoundaryActualEvaluation
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.OrdinaryBoundaryCone TernaryPoly.RationalCohomologyDescent

noncomputable section

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace TernaryPeriodPolynomials.Argument.Statements.AppendixLemmas

/-- **Lemma 3.3**, diagram (`eq:apartment-boundary-diagram`) in the library's model: for a
boundary top class `c`, the top-cell coefficient evaluated at the identity apartment of its image
`j_* c` equals the pairing of `PD_∂ c` with the boundary of the apartment. -/
theorem apartment_boundary_diagram (W : Rep.{0} ℚ principalSix)
    (c : (boundaryLocalChains W).homology 3) :
    groupApartmentEvaluation W (boundaryToGroup W 3 c) =
      (homologyEvaluation boundaryChains W 1
        ((boundaryCohomologyIso W).inv ((boundaryH1CapIso W boundaryOrientation).inv c))).hom
          identityApartmentBoundaryClass :=
  boundary_image_apartment W c

/-- **Lemma 3.3**, evaluation formula (`eq:apartment-boundary-evaluation`): for every functional
`λ` on the coefficient module (`φ_λ(F) = λ(F(ℓ))`), `λ(F_{j_*c}(ℓ)) = ⟨PD_∂ c, ∂a_{φ_λ}⟩`. -/
theorem apartment_boundary_evaluation (W : Rep.{0} ℚ principalSix) (lam : W →ₗ[ℚ] ℚ)
    (c : (boundaryLocalChains W).homology 3) :
    lam (groupApartmentEvaluation W (boundaryToGroup W 3 c)) =
      lam ((homologyEvaluation boundaryChains W 1
        ((boundaryCohomologyIso W).inv ((boundaryH1CapIso W boundaryOrientation).inv c))).hom
          identityApartmentBoundaryClass) := by
  rw [apartment_boundary_diagram]

/-- **Lemma 3.3**, the flat: the apartment is the boundary of the relative apartment class, and the
arithmetic top evaluator of a capped relative class is the evaluation on this relative class
("intersection with the flat reads the top-cell coefficient"). -/
theorem apartment_relative_flat (W : Rep.{0} ℚ principalSix) :
    upstairsRelativeSequence_shortExact.δ 2 1 rfl identityApartmentRelativeClass =
        identityApartmentBoundaryClass ∧
      ∀ x : (homCochains upstairsRelativeChains W).homology 2,
        groupApartmentEvaluation W ((bordifiedGroupLocalHomologyIso W 3).inv
          ((relativeHomCapIso W).hom x)) =
        (homologyEvaluation upstairsRelativeChains W 2 x).hom identityApartmentRelativeClass :=
  ⟨identityApartmentRelativeClass_connecting, cappedClass_apartmentEvaluation W⟩

/-- **Lemma 3.3**, compatibility with passage to a finite-index subgroup: for the normalized
transfer of a cover-boundary cocycle `x`, the top evaluator equals the index-normalized average of
the translated boundary-apartment evaluations. -/
theorem apartment_boundary_transfer (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) :
    groupApartmentEvaluation (restrictedCoefficients n e)
      (normalizedBoundaryClassToGroup n e
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x)) =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ •
        ∑ q : RightCosets principalSix, (actualCoefficients n e).ρ q.out⁻¹
          ((cocycleValue boundaryChains (restrictedCoefficients n e) 1 x).hom
            ((fullBoundaryChains.X 1).ρ q.out
              ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain))) :=
  normalizedBoundaryClassToGroup_evaluation n e x

/-- **Lemma 3.3, the flat meets the top cells only at the identity.** A point `diag(a, b, (ab)⁻¹)`
of the diagonal flat lies in the top cell (minimum one, attained on a basis) of some integral basis
iff it is the identity form. -/
theorem apartment_flat_meets_cells_iff {a b c : ℝ}
    (hf : TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.OnFlat a b c) :
    (∃ u : Fin 3 → Fin 3 → ℤ, ((Matrix.of u).det = 1 ∨ (Matrix.of u).det = -1) ∧
        TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.diagForm a b c ∈
          TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.TopCellOf u) ↔
      a = 1 ∧ b = 1 ∧ c = 1 :=
  TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.flat_meets_cells_iff hf

/-- **Lemma 3.3, shortest vectors at the identity**: exactly `±e_k`. -/
theorem apartment_identity_minimal_vectors (v : Fin 3 → ℤ) (hv : v ≠ 0) :
    TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.qf
        (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.diagForm 1 1 1)
        (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.castVec v) = 1 ↔
      ∃ k : Fin 3, v = Pi.single k 1 ∨ v = -Pi.single k 1 :=
  TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.identity_minimal_vectors v hv

/-- **Lemma 3.3, transversality at the identity**: the tangent spaces of the flat and of the
standard top cell are complementary in the tangent space of the symmetric space. -/
theorem apartment_flat_cell_transverse (X : Matrix (Fin 3) (Fin 3) ℝ)
    (hX : TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.TangentSpace X) :
    ∃! p : Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 3) ℝ,
      TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.TangentFlat p.1 ∧
        TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.TangentCell p.2 ∧ X = p.1 + p.2 :=
  TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.flat_cell_transverse X hX

/-- **Lemma 3.3, orientation of the cell.** The signed permutation matrix `g = (σ, s)` (`g e_j =
s_j e_{σ j}`, `s_j = ±1`) acts on the tangent space of the standard top cell at the identity (the
off-diagonal symmetric matrices, oriented by `(r₁₂, r₁₃, r₂₃)`) with determinant `sgn σ`: the
permutation sign, and `+1` for coordinate sign changes. -/
theorem apartment_cell_orientation_character (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ)
    (hs : ∀ k, s k * s k = 1) :
    (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.cellMatrix
      (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.signedPerm σ s)).det =
      (σ.sign : ℝ) :=
  TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.det_cellMatrix_eq_sign σ s hs

/-- **Lemma 3.3, orientation of the flat**: the same signed permutation acts on the flat tangent
space (trace-zero diagonal matrices, oriented by `(x₁, x₂)`) with determinant `sgn σ`. -/
theorem apartment_flat_orientation_character (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ)
    (hs : ∀ k, s k * s k = 1) :
    (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.flatMatrix
      (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.signedPerm σ s)).det =
      (σ.sign : ℝ) :=
  TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.det_flatMatrix σ s hs

/-- **Lemma 3.3, the total orientation is preserved**: the product of the two determinants is
`1`, so the local intersection of the flat with the oriented translate of the cell is carried by
the cell's permutation sign. -/
theorem apartment_cell_flat_frame_det (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ)
    (hs : ∀ k, s k * s k = 1) :
    (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.cellMatrix
        (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.signedPerm σ s)).det *
      (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.flatMatrix
        (TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.signedPerm σ s)).det = 1 :=
  TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat.cell_flat_frame_det σ s hs

/-- **Lemma B.1**, the diagram (`eq:residue-comparison-diagram`) in the Hom model, with scalar `1`:
`edge₂ ∘ (κ ∘ Sh) = res_H`, i.e. reading the standard binary edge of the restriction of a residue
functional to the plane cone is its literal residue coordinate. -/
theorem residue_comparison_diagram (n : ℕ)
    (F : TernaryPoly.OrdinaryFullCoefficient.ResidueHom n (-1)) :
    TernaryPoly.BinaryModularSymbol.periodEvaluation (n + 1)
        (TernaryPoly.OrdinaryResidueSymbol.toBinaryHom n F) =
      TernaryPoly.OrdinaryResiduePeriod.periodEquiv n F :=
  TernaryPoly.BinaryModularSymbol.periodEvaluation_restriction n F

/-- **Lemma B.1**, the coordinates are not mixed: the value of the binary coordinate of the
restriction at the reference edge is literally the `(b, c)` numerator of the residue at
`H = {a = 0}` (the whole direct sum is read through its fibre at `H`). -/
theorem residue_comparison_coordinate (n : ℕ)
    (F : TernaryPoly.OrdinaryFullCoefficient.ResidueHom n (-1)) :
    (TernaryPoly.BinaryModularSymbol.periodEvaluation (n + 1)
        (TernaryPoly.OrdinaryResidueSymbol.toBinaryHom n F)).val =
      TernaryPoly.OrdinaryFullCoefficient.coordinatePeriod n 0 F :=
  TernaryPoly.OrdinaryResidueSymbol.evaluation_toBinaryHom n F

/-- **Lemma B.1**, `Sh` and `κ` are isomorphisms (their composite, in the Hom model): the
restriction from residue functionals to binary modular symbols is bijective. -/
theorem residue_comparison_bijective (n : ℕ) :
    Function.Bijective (TernaryPoly.OrdinaryResidueSymbol.toBinaryHom n) :=
  (TernaryPoly.OrdinaryResidueSymbol.residueSymbolEquiv n).bijective

/-- **Lemma B.1**, the composite identifies the residue with the usual period polynomial: the two
period coordinates of `H₃(G, 𝓡_n ⊗ det)` and `H₁(GL₂(ℤ), D_{n+1})` agree as linear equivalences onto
`ℬ_{n+1}`. -/
theorem residue_comparison_equiv (n : ℕ)
    (F : TernaryPoly.OrdinaryFullCoefficient.ResidueHom n (-1)) :
    TernaryPoly.BinaryModularSymbol.periodEquiv (n + 1)
        (TernaryPoly.OrdinaryResidueSymbol.residueSymbolEquiv n F) =
      TernaryPoly.OrdinaryResiduePeriod.periodEquiv n F :=
  TernaryPoly.OrdinaryResidueSymbol.residueSymbolEquiv_period n F

/-- **Lemma B.1**, the target `ℬ_{n+1}` is the space of binary polynomials satisfying the literal
symmetric, separately odd and period relations. -/
theorem residue_comparison_period_relations (n : ℕ)
    (q : TernaryPoly.SinglePoleCoordinate.BinaryV (n + 1)) :
    q ∈ TernaryPoly.OrdinaryResiduePeriod.periodSpace (n + 1) ↔
      TernaryPoly.SymmetricBinaryPeriodRelations q.val :=
  TernaryPoly.OrdinaryResiduePeriod.mem_periodSpace (n + 1) q

/-- **Lemma B.1**, Hecke equivariance of `κ ∘ Sh` (the Hom-model of "Shapiro is Hecke-equivariant"):
the ternary prime operator restricts to `p` times the binary Hecke operator plus the identity. -/
theorem residue_comparison_hecke (n p : ℕ) [Fact p.Prime]
    (F : TernaryPoly.OrdinaryFullCoefficient.ResidueHom n (-1)) :
    TernaryPoly.OrdinaryResidueSymbol.toBinaryHom n
        (TernaryPoly.OrdinaryHomHecke.rationalHecke
          (TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p)
          (TernaryPoly.SinglePole.residueAction n (-1)) F) =
      (p : ℚ) • TernaryPoly.BinaryRationalHecke.rationalHecke
          (TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p)
          (TernaryPoly.BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1))
          (TernaryPoly.OrdinaryResidueSymbol.toBinaryHom n F) +
        TernaryPoly.OrdinaryResidueSymbol.toBinaryHom n F :=
  TernaryPoly.OrdinaryBinaryHecke.toBinaryHom_prime n p F

end TernaryPeriodPolynomials.Argument.Statements.AppendixLemmas
