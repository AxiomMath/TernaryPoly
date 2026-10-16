module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33Geometric
public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Flat.AppendixLemmas

@[expose] public section


/-!
# Lemma 3.3 (`lem:apartment-boundary-pairing`): the commuting Poincar\'e--Lefschetz diagram, with cells

Formalized by Claude Sonnet 5.5.

Paper: Lemma 3.3:

> Let `j` be the inclusion of the boundary, and let `PD_∂ : H_3(∂X̄_G; 𝓜) → H^1(∂X̄_G; 𝓜)` be boundary Poincar\'e duality.
> The diagram `H_3(∂X̄_G;𝓜) --j_*--> H_3(X̄_G;𝓜)`, `PD_∂` down on the left, `z ↦ φ(F_z)` down on the right,
> `H^1(∂X̄_G;𝓜) --(ω ↦ ⟨ω, ∂a_φ⟩)--> ℚ` along the bottom, commutes.  In particular `λ(F_{j_*c}(ℓ)) = ⟨PD_∂ c, ∂a_{φ_λ}⟩`.

with the proof: "Intersection with the flat reads the top-cell coefficient. Moving the intersection into a
boundary collar gives the bottom arrow", the first by the local computation at the identity of the standard top cell
 together with the normalization "we orient the flat and the averaged standard top-cell generator so that
their local intersection number is `+1`", the second by "smooth the neat cover's corners and move `c`
slightly inward along a collar ... the cap-product definition gives `⟨PD_∂ c, ∂a_φ⟩`".

## The objects

For `W : Rep ℚ Γ(6)` (the level-six cover; `φ` is a functional on `W`, i.e. `W`-valued maps compose with `λ ∈ W*`):

* `H_3(∂X̄_G; 𝓜)` is `(boundaryLocalChains W).homology 3`, `H_3(X̄_G; 𝓜)` is `groupHomology W 3`, and `j_*` is
  `boundaryToGroup W 3` (singular chains of the actual arithmetic boundary, through the contractible bordification);
* `PD_∂` is `PDboundary W`: the inverse of the library's boundary cap isomorphism `boundaryH1CapIso` (cap product with
  the boundary fundamental class `boundaryOrientation`, a case of `boundaryOrdinaryCapIso`, compact Poincar\'e duality
  of the 4-manifold with corners `∂X̄`) followed by the identification of geometric and equivariant boundary cohomology;
* the right arrow is `groupApartmentEvaluation W` (the cap isomorphism `groupOrdinaryIso` followed by evaluation at the
  identity apartment, `z ↦ F_z(ℓ)`);
* the bottom arrow is `flatBoundaryPairing W`: `ω ↦ ⟨ω, ∂a⟩` where `a = flatClass` is the relative class of the
  compactified diagonal flat `{diag(a,b,(ab)⁻¹)}` (six Weyl-chamber charts glued along walls; `Lemma33.flatChain`,
  `Lemma33.delta_flatClass`: its boundary is the coordinate apartment hexagon).  Taking `λ ∈ W*` gives the paper's
  scalar `⟨ω, ∂a_{φ_λ}⟩` (`evaluation_apply`).

## What is proved

* `diagram_commutes`, `diagram_apply`, `evaluation_apply`: the diagram commutes (with sign `+1`, no scalar), for every
  coefficient system `W`; this is the "collar" step.  `lefschetz` collects the Poincar\'e--Lefschetz inputs it rests on:
  Lefschetz duality for the pair `(X̄, ∂X̄)` in all complementary degrees (`relativeCapMap_isIso`), the cap/connecting
  square `j_* ∘ (∩[∂X̄]) = (∩[X̄,∂X̄]) ∘ δ^*`, `⟨δ^*ω, a⟩ = ⟨ω, ∂a⟩`, and "intersection with the flat reads the
  evaluation" for every capped relative class.
* The cellular half: `cellular_iso` (A2's cellular complex of the well-rounded retract computes `H_*(Γ(6); W)`),
  `cellular_diagram_of_bridge(_forall)`: for every `c`, `j_* c` is the class of a cellular top cycle `z`
  (`cellGroupHomologyMap`, `cellClass`) and then `⟨PD_∂ c, ∂a⟩ = (κ·dT0) • coeffAtT0 z`: the pairing reads the top-cell
  coefficient at `T₀` times the dictionary constant.
* `lemma_3_3_diagram`: unconditional (no hypotheses beyond the coefficient system): there is a nonzero `κ` with
  `FlatIntersectionBridge κ`, `d₅ ≠ 0` (the degree of the positive product cell) and the **proved dictionary constant**
  `κ * dT0 = - d₅` (the formal flat chain has the orientation of the positive
  reference triangle, so `ε = -1`), such that the diagram commutes and intersection with the flat reads `(-d₅) • coeffAtT0`.
  `lemma_3_3_diagram_oriented`: in the orientation with `d₅ = 1`, intersection with the flat reads **minus** the coefficient at `T₀`.
* `paper_sign_discrepancy`: a statement about the LIBRARY-normalized constant only: it is `-d₅`, and `κ * dT0 = 1 ↔ d₅ = -1`.
  This is not a paper discrepancy: CHOOSES the orientations of the flat and of the averaged top-cell
  generator so that their local intersection is `+1`; that choice is constructed geometrically in `Statements.Lemma33GeoNormalized`
  (generator `-T₀` in the library orientation), which supersedes the sign language of this file (Claude Opus 5.5).
* `normalized_diagram`: under the paper's normalization, **stated as the visible hypothesis** `κ * dT0 = 1`, the pairing is
  exactly the top-cell coefficient at `T₀` (consistent only with `d₅ = -1`, see `paper_sign_discrepancy`).

## What has no Lean counterpart

* The Ash retract as a subspace of the symmetric space: `Retract` models the well-rounded retract by its cell complex `cellCoinv W` and an
  equivariant chain map `cellToBordified` realizing every cell as a singular chain of the bordification
  (`cellAt`, `cellAt_eq_embedding_map`, `reach_well_rounded`: the realized cells lie in the well-rounded locus), and proves
  that it induces isomorphisms on group homology (`cellGroupHomologyMap_isIso`) by comparison of projective resolutions.
  Ash's theorem that the locus is a deformation retract of the symmetric space, and the dimension count "no degree-four cells"
  as a topological fact, are not statements of the development (the chain-level isomorphism is what is used).
* The relative local-coefficient class `a_φ ∈ H₂(X̄_G, ∂X̄_G; 𝓜*)` (constant dual coefficient `φ` on the universal flat, then the
  equivariant quotient): NOT constructed here.  This file uses the trivial-coefficient flat with `W`-valued evaluation followed by `φ`;
  the identity `⟨ω, ∂a_φ⟩ = φ(⟨ω, ∂a⟩)` is a comparison not proved in this file.
* The local intersection numbers of cycles with the flat in the symmetric space itself are replaced by the coefficient at
  `T₀` (`intersectionSum = dT0 • coeffAtT0`) through A2's bridge `flat_intersection_bridge`.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram

open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPoly.OrdinaryTopBoundaryComparison

variable (W : Rep.{0} ℚ principalSix)

/-- Boundary Poincar\'e duality `PD_∂ : H_3(∂X̄_G; 𝓜) → H^1(∂X̄_G; 𝓜)`: the inverse of the boundary cap isomorphism
(cap with the boundary fundamental class) followed by the identification of geometric and equivariant boundary cohomology. -/
noncomputable def PDboundary :
    (SingularLocalHomology.boundaryLocalChains W).homology 3 ⟶
      (EquivariantSingularSmall.homCochains SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W).homology 1 :=
  (SymmetricSpaceBoundaryManifold.boundaryH1CapIso W
      SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv ≫
    (OrdinaryBoundaryActualEvaluation.boundaryCohomologyIso W).inv

/-- The bottom arrow `ω ↦ ⟨ω, ∂a⟩` of the diagram, `W`-valued: Kronecker evaluation of a boundary `H¹` class on the boundary
of the relative class `flatClass` of the compactified diagonal flat. -/
noncomputable def flatBoundaryPairing :
    (EquivariantSingularSmall.homCochains SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W).homology 1 ⟶
      ModuleCat.of ℚ W :=
  homologyEvaluation SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W 1 ≫
    ModuleCat.ofHom
      { toFun := fun f => f.hom (upstairsRelativeSequence_shortExact.δ 2 1 rfl flatClass)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }

/-- Unfolding of `flatBoundaryPairing`. -/
theorem flatBoundaryPairing_apply
    (ω : (EquivariantSingularSmall.homCochains SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W).homology 1) :
    flatBoundaryPairing W ω =
      (homologyEvaluation SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W 1 ω).hom
        (upstairsRelativeSequence_shortExact.δ 2 1 rfl flatClass) := rfl

/-- **The diagram of Lemma 3.3, elementwise**: `φ(F_{j_*c}(ℓ)) = ⟨PD_∂ c, ∂a⟩` (the evaluator of `j_* c` is the pairing
of `PD_∂ c` with the boundary of the flat); sign `+1`. -/
theorem diagram_apply (c : (SingularLocalHomology.boundaryLocalChains W).homology 3) :
    groupApartmentEvaluation W (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c) =
      flatBoundaryPairing W (PDboundary W c) :=
  (Statements.Lemma33Geometric.collar_comparison W c).2.2.2

/-- **The diagram of Lemma 3.3 commutes** (equality of morphisms of `ℚ`-modules). -/
theorem diagram_commutes :
    SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 ≫ groupApartmentEvaluation W =
      PDboundary W ≫ flatBoundaryPairing W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact diagram_apply W c


/-- **`eq:apartment-boundary-evaluation`**: `λ(F_{j_*c}(ℓ)) = ⟨PD_∂ c, ∂a_{φ_λ}⟩` for every functional `λ` of the coefficients. -/
theorem evaluation_apply (lam : W →ₗ[ℚ] ℚ) (c : (SingularLocalHomology.boundaryLocalChains W).homology 3) :
    lam (groupApartmentEvaluation W (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c)) =
      lam (flatBoundaryPairing W (PDboundary W c)) := by
  rw [diagram_apply]

/-- **The Poincar\'e--Lefschetz inputs of the collar step**: Lefschetz duality for `(X̄, ∂X̄)` (all complementary degrees, and
the cap used here), the cap/connecting square, `⟨δ^*ω, a⟩ = ⟨ω, ∂a⟩`, and intersection with the flat reads the evaluator. -/
theorem lefschetz :
    (∀ a b : ℕ, ∀ hab : a + b = 5, IsIso (SymmetricSpaceRelativeCap.relativeCapMap W a b hab)) ∧
    IsIso (SymmetricSpaceRelativeCapConnecting.relativeFundamentalCap W) ∧
    ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso W
          SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom ≫
        HomologicalComplex.homologyMap (SingularLocalHomology.boundaryInclusionMap W) 3 =
      SymmetricSpaceRelativeCapConnecting.geometricBoundaryConnecting W 1 ≫
        SymmetricSpaceRelativeCapConnecting.relativeFundamentalCap W) ∧
    (∀ (ω : (EquivariantSingularSmall.homCochains SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W).homology 1)
        (a : upstairsRelativeChains.homology 2),
      (homologyEvaluation upstairsRelativeChains W 2
          (HomologicalComplex.homologyMap (relativeHomKernelIso W).inv 2 (boundaryConnecting W 1 ω))).hom a =
        (homologyEvaluation SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W 1 ω).hom
          (upstairsRelativeSequence_shortExact.δ 2 1 rfl a)) ∧
    (∀ x : (EquivariantSingularSmall.homCochains upstairsRelativeChains W).homology 2,
      groupApartmentEvaluation W ((SingularLocalHomology.bordifiedGroupLocalHomologyIso W 3).inv
          ((relativeHomCapIso W).hom x)) =
        (homologyEvaluation upstairsRelativeChains W 2 x).hom flatClass) :=
  ⟨fun a b hab => SymmetricSpaceRelativeCap.relativeCapMap_isIso W a b hab,
    SymmetricSpaceAllTopBoundary.relativeFundamentalCap_isIso W,
    SymmetricSpaceRelativeCapConnecting.ordinary_cap_connecting W,
    fun ω a => evaluation_connecting W ω a,
    fun x => Statements.Lemma33Geometric.flat_intersection_reads_evaluation W x⟩


open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport (d5 flatDegree)
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree (dT0)

/-- A2's cellular complex of the well-rounded retract computes the group homology of `Γ(6)` in every coefficient system. -/
theorem cellular_iso : IsIso (cellGroupHomologyMap W 3) := inferInstance

/-- For a bridge constant `κ`: every `j_* c` is the class of a cellular top cycle `z`, and the pairing `⟨PD_∂ c, ∂a⟩` is
`(κ * dT0)` times the top-cell coefficient of `z` at `T₀` (intersection with the flat reads the coefficient). -/
theorem cellular_diagram_of_bridge {κ : ℚ} (hB : FlatIntersectionBridge κ)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3) :
    ∃ (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
      SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
          cellGroupHomologyMap W 3 (cellClass W z hz) ∧
        flatBoundaryPairing W (PDboundary W c) = (κ * dT0) • (coeffAtT0 W).hom z := by
  obtain ⟨y, hy⟩ := cellGroupHomologyMap_surjective W
    (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c)
  obtain ⟨z, hz, rfl⟩ := exists_cellClass W y
  refine ⟨z, hz, hy.symm, ?_⟩
  rw [← diagram_apply, ← hy]
  exact evaluation_eq_coeffAtT0 hB W z hz

/-- The same for every cellular top cycle `z` representing `j_* c`. -/
theorem cellular_diagram_of_bridge_forall {κ : ℚ} (hB : FlatIntersectionBridge κ)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
    (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0)
    (h : SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
      cellGroupHomologyMap W 3 (cellClass W z hz)) :
    flatBoundaryPairing W (PDboundary W c) = (κ * dT0) • (coeffAtT0 W).hom z := by
  rw [← diagram_apply, h]
  exact evaluation_eq_coeffAtT0 hB W z hz

/-- Under the paper's normalization, taken as the visible hypothesis `κ * dT0 = 1` (local intersection number `+1`), the
pairing is exactly the coefficient at `T₀`. -/
theorem normalized_diagram {κ : ℚ} (hB : FlatIntersectionBridge κ) (hnorm : κ * dT0 = 1)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
    (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0)
    (h : SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
      cellGroupHomologyMap W 3 (cellClass W z hz)) :
    flatBoundaryPairing W (PDboundary W c) = (coeffAtT0 W).hom z := by
  rw [cellular_diagram_of_bridge_forall W hB c z hz h, hnorm, one_smul]

/-- **Lemma 3.3, the commuting Poincar\'e--Lefschetz diagram with its cellular reading, unconditional.**  The diagram
commutes for every coefficient system; there is a nonzero `κ` with `FlatIntersectionBridge κ`, `d₅ ≠ 0` (the degree of the positive
product cell) and the proved dictionary constant `κ * dT0 = - d₅`; the top evaluator on
cellular cycles, hence the bottom arrow on all of `j_* H_3(∂)`, is `(-d₅)` times the coefficient at `T₀`.  In the orientation of
`M` in which the positive product cell has degree one (`d₅ = 1`) this is `-1` times the coefficient (`lemma_3_3_diagram_oriented`). -/
theorem lemma_3_3_diagram :
    ∃ κ : ℚ, κ ≠ 0 ∧ FlatIntersectionBridge κ ∧ d5 ≠ 0 ∧ κ * dT0 = -d5 ∧
      ∀ W : Rep.{0} ℚ principalSix,
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 ≫ groupApartmentEvaluation W =
          PDboundary W ≫ flatBoundaryPairing W ∧
        (∀ (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
          groupApartmentEvaluation W (cellGroupHomologyMap W 3 (cellClass W z hz)) =
            (-d5) • (coeffAtT0 W).hom z) ∧
        ∀ c : (SingularLocalHomology.boundaryLocalChains W).homology 3,
          ∃ (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
            SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
                cellGroupHomologyMap W 3 (cellClass W z hz) ∧
              flatBoundaryPairing W (PDboundary W c) = (-d5) • (coeffAtT0 W).hom z := by
  obtain ⟨κ, hκ, hB, -, hneg, hd, -, -⟩ := Statements.Lemma33Geometric.apartment_constant_values
  refine ⟨κ, hκ, hB, hd, hneg, fun W => ⟨diagram_commutes W, fun z hz => ?_, fun c => ?_⟩⟩
  · rw [← hneg]; exact evaluation_eq_coeffAtT0 hB W z hz
  · obtain ⟨z, hz, h1, h2⟩ := cellular_diagram_of_bridge W hB c
    exact ⟨z, hz, h1, by rw [← hneg]; exact h2⟩

/-- **The oriented form**: in the orientation of `M` for which the positive product cell has degree one (`d₅ = 1`), intersection
with the flat reads **minus** the coefficient at `T₀`: the pairing `⟨PD_∂ c, ∂a⟩` is `-(coeffAtT0 z)` for a cellular top cycle `z`
representing `j_* c`, and the top evaluator of every cellular top cycle is `-(coeffAtT0 z)`. -/
theorem lemma_3_3_diagram_oriented (hd5 : d5 = 1) :
    ∃ κ : ℚ, κ ≠ 0 ∧ FlatIntersectionBridge κ ∧ κ * dT0 = -1 ∧
      ∀ W : Rep.{0} ℚ principalSix,
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 ≫ groupApartmentEvaluation W =
          PDboundary W ≫ flatBoundaryPairing W ∧
        (∀ (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
          groupApartmentEvaluation W (cellGroupHomologyMap W 3 (cellClass W z hz)) =
            -(coeffAtT0 W).hom z) ∧
        ∀ c : (SingularLocalHomology.boundaryLocalChains W).homology 3,
          ∃ (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
            SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
                cellGroupHomologyMap W 3 (cellClass W z hz) ∧
              flatBoundaryPairing W (PDboundary W c) = -(coeffAtT0 W).hom z := by
  obtain ⟨κ, hκ, hB, -, hneg, h⟩ := lemma_3_3_diagram
  rw [hd5] at hneg h
  refine ⟨κ, hκ, hB, hneg, fun W => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h W
  refine ⟨h1, fun z hz => ?_, fun c => ?_⟩
  · simpa using h2 z hz
  · obtain ⟨z, hz, e, e'⟩ := h3 c
    exact ⟨z, hz, e, by simpa using e'⟩

/-- **The printed normalization versus the proved constant.**  The dictionary constant of Lemma 3.3 is `κ * dT0 = - d₅`, where `d₅`
is the degree of the positive product cell.  In the orientation `d₅ = 1` it is `-1`, not the `+1` printed in the paper
("so that their local intersection number is `+1`"); the printed value is attained exactly when `d₅ = -1`, i.e. for
the opposite orientation of `M` (equivalently the opposite orientation of the standard top cell).  Consequently
`normalized_diagram` (hypothesis `κ * dT0 = 1`) is consistent only with that opposite orientation; the paper's statement of
the lemma is true after replacing `+1` by the convention-dependent constant `-d₅`, which is a sign convention of the normalization,
not of the diagram (the diagram commutes with no scalar). -/
theorem paper_sign_discrepancy :
    ∃ κ : ℚ, FlatIntersectionBridge κ ∧ d5 ≠ 0 ∧ κ * dT0 = -d5 ∧
      (d5 = 1 → κ * dT0 = -1 ∧ κ * dT0 ≠ 1) ∧ (κ * dT0 = 1 ↔ d5 = -1) := by
  obtain ⟨κ, -, hB, hd, hneg, -⟩ := lemma_3_3_diagram
  refine ⟨κ, hB, hd, hneg, fun h => ?_, ?_⟩
  · rw [hneg, h]; norm_num
  · rw [hneg]; constructor <;> intro h <;> linarith

end TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram
