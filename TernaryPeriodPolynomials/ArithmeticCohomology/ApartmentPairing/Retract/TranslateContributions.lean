module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.LocalDegree
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellRep
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubChainSubspaceBridge

@[expose] public section


/-!
# Translate contributions to the local degree

Boundary-avoidance and finite-translate-sum facts for the cell chains, used when the PL pairing with
the flat is evaluated on a cellular top cycle:

* `cellAt_translate`: the `Γ(6)`-translate of a cell chain of `Glued` is the image of the cell chain
  `cellAtSpace n (g • C)` of the symmetric space (equivariance `cellAt_smul_six`);
* `translate_off_flat`: if `g • C ≠ T₀` the chain of the translated cell has zero image
  `locRel` (it is invisible to the unipotent projection; `flat_reach`), hence
  `degπ_of_locRel_zero`: its local degree is `0` (and all its boundary hypotheses hold);
* `translate_unique`: at most one `g ∈ Γ(6)` carries a given cell to `T₀` (the action on cells is
  free), so the finite sum over translates of a top cell contributes `dT0` for the unique `g` with
  `g • C = T₀` (if any) and `0` otherwise;
* `embedding_map_injective`: chains of the symmetric space are determined by their image in `Glued`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly.ContractibleSingularHomology
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalRelativeSingular
open GeneralEisenstein TernaryPoly TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.SingularCoverNaturality TernaryPoly.EquivariantSingularResolution
  TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

theorem embedding_map_injective (n : ℕ) :
    Function.Injective ((underlyingMap embeddingHom).f n).hom := by
  apply SphereOddDegree.singularChainMap_injective_of_pushSimplex_injective (R := ℚ) embeddingHom n
  intro σ τ h
  apply (SpaceTop.toSSetObjEquiv _).injective
  refine ContinuousMap.ext fun t => ?_
  have := congrArg (fun s => (TopCat.of Glued).toSSetObjEquiv _ s t) h
  exact TernaryPoly.SymmetricSpaceRationalGluing.embedding_injective this

theorem cellAt_translate (g : TernaryPoly.IntegralGL3Congruence.principalSix) (n : ℕ) (C : Cell) :
    (chainRep IntegralGL3 (TopCat.of Glued) n).ρ g.1 (cellAt n C) =
      ((underlyingMap embeddingHom).f n).hom (cellAtSpace n (g • C)) := by
  rw [six_smul_cell, ← cellAt_smul_six, cellAt_eq_embedding_map]

/-- A translate of a cell other than `T₀` is invisible to the unipotent projection: the
chain of the translated cell has zero image in the local chains of `ℝ³` at the origin. -/
theorem translate_off_flat (g : TernaryPoly.IntegralGL3Congruence.principalSix) (C : Cell)
    (hne : g • C ≠ T0) (n : ℕ) :
    (locRel.f n).hom (cellAtSpace n (g • C)) = 0 :=
  locRel_cellAtSpace_zero _ hne n

/-- Over `Γ(6)` at most one translate of a cell is `T₀` (the action on cells is free). -/
theorem translate_unique (g g' : TernaryPoly.IntegralGL3Congruence.principalSix) (C : Cell)
    (h : g • C = T0) (h' : g' • C = T0) : g = g' := by
  have hs : (g'⁻¹ * g) • C = C := by
    rw [mul_smul, h, ← h', inv_smul_smul]
  have h1 : levelOfSix (g'⁻¹ * g) = 1 := Cell.free _ C hs
  have h2 : (g'⁻¹ * g) = 1 := by
    apply Subtype.ext
    have := congrArg levelLift h1
    rw [levelLift_levelOfSix] at this
    exact this.trans (map_one _)
  exact (inv_mul_eq_one.mp h2).symm

theorem degπ_of_locRel_zero (c : (chains TernaryPoly.SymmetricSpacePositive.Space).X 3) (hc : (locRel.f 3).hom c = 0)
    (h : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c) = 0) : degπ c h = 0 := by
  have hnext : (ComplexShape.down ℕ).next 3 = 2 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map ((localChains 3).iCycles 3)) :=
    (Preadditive.mono_iff_injective ((localChains 3).iCycles 3)).1 inferInstance
  have h0 : (localChains 3).cyclesMk ((locRel.f 3).hom c) 2 hnext h = 0 := by
    apply inj
    have e := (localChains 3).i_cyclesMk ((locRel.f 3).hom c) 2 hnext h
    rw [map_zero]
    exact e.trans hc
  unfold degπ
  rw [h0, map_zero, map_zero]

end TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
