module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Geo

@[expose] public section


/-!
# Lemma `ar:lem:stokes` at level `Γ(6)` for the orbit pairings, with a complex coefficient module and its complex dual

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPoly.BoundaryFaceResolutionComparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

/-- The coinvariant cycle of the model cone of `cone_stokes_geo` (`cone_stokes_complex` with the geometric comparison data of the cycle retained). -/
def stokesCycle : coneR.X 4 := Classical.choose cone_stokes_geo

theorem stokesCycle_isCoinvCycle : IsCoinvCycle stokesCycle := (Classical.choose_spec cone_stokes_geo).1

/-- **The Stokes cycle carries the geometric comparison data of `exists_pairGeo`**: a carried quasi-isomorphism `Ψ` to the boundary chains, `κ ≠ 0` with `PairGeo Ψ stokesCycle κ`,
and `c₀ ≠ 0` for the level trace (so that `glue_of_pairGeo` gives `LineGlue Ψ (κ c₀)` and `PlaneGlue Ψ (-(κ c₀))`). -/
theorem stokesCycle_geoData : GeoData stokesCycle := (Classical.choose_spec cone_stokes_geo).2.1

section Global

variable {W : Rep.{0} ℚ Γ6}
  (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ W) (hf : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
  (w : A.X 1 ⟶ W) (hw : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f)

/-- The line datum of a global cocycle with a flag primitive. -/
def LineDatum.ofGlobal : LineDatum W where
  z := (ptMap Line).f 2 ≫ f
  hz := by rw [← Category.assoc, ← (ptMap Line).comm 3 2, Category.assoc, hf, comp_zero]
  w := w
  hw := hw

include hw in
/-- The plane datum of a global cocycle with a flag primitive. -/
def PlaneDatum.ofGlobal : PlaneDatum W where
  z := (ptMap Plane).f 2 ≫ f
  hz := by rw [← Category.assoc, ← (ptMap Plane).comm 3 2, Category.assoc, hf, comp_zero]
  w := w
  hw := plane_edge_of_line_edge f w hw

end Global


section Stokes

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  {G : Type} [Group G] (ι : Γ6 →* G) (ρ : Representation ℂ G V)
  [Fintype (labelOrbits Γ6 Line)] [Fintype (labelOrbits Γ6 Plane)]

/-- **Lemma `ar:lem:stokes` at level `Γ(6)`, orbit by orbit, for a complex coefficient module `E` and its complex dual `E^*`.**  For global cocycles
`f` (coefficients `E`), `f'` (coefficients `E^*`) of `Γ(6)` whose restrictions to the complete flags are the coboundaries of `w`, `w'`, the sum over the
`Γ(6)`-orbits of lines of the pairings of the parts of the line data supported on the orbit, plus the same sum over the orbits of planes, vanishes. -/
theorem cone_stokes_orbits
    (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ qRep ι ρ)
    (hf : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
    (f' : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ qRep ι ρ.dual)
    (hf' : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f' = 0)
    (w : A.X 1 ⟶ qRep ι ρ) (hw : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f)
    (w' : A.X 1 ⟶ qRep ι ρ.dual) (hw' : A.d 2 1 ≫ w' = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f') :
    ∑ o : labelOrbits Γ6 Line,
        conePairC (evalC ι ρ) stokesCycle
          ((LineDatum.ofGlobal f hf w hw).cut (labelOrbit Γ6 Line o) (labelOrbit_invariant o)).cone
          ((LineDatum.ofGlobal f' hf' w' hw').cut (labelOrbit Γ6 Line o) (labelOrbit_invariant o)).cone +
      ∑ p : labelOrbits Γ6 Plane,
        conePairC (evalC ι ρ) stokesCycle
          ((PlaneDatum.ofGlobal f hf w hw).cut (labelOrbit Γ6 Plane p) (labelOrbit_invariant p)).cone
          ((PlaneDatum.ofGlobal f' hf' w' hw').cut (labelOrbit Γ6 Plane p) (labelOrbit_invariant p)).cone = 0 := by
  have h := (Classical.choose_spec cone_stokes_geo).2.2 ι ρ f hf f' hf' w hw w' hw'
  have e1 := LineDatum.pairC_eq_sum (evalC ι ρ) stokesCycle
    (fun o : labelOrbits Γ6 Line => labelOrbit Γ6 Line o) (fun o => labelOrbit_invariant o)
    labelOrbit_partition (LineDatum.ofGlobal f hf w hw) (LineDatum.ofGlobal f' hf' w' hw')
  have e2 := PlaneDatum.pairC_eq_sum (evalC ι ρ) stokesCycle
    (fun o : labelOrbits Γ6 Plane => labelOrbit Γ6 Plane o) (fun o => labelOrbit_invariant o)
    labelOrbit_partition (PlaneDatum.ofGlobal f hf w hw) (PlaneDatum.ofGlobal f' hf' w' hw')
  rw [← e1, ← e2]
  exact h

end Stokes

end TernaryPeriodPolynomials.Argument.GammaNStokes
