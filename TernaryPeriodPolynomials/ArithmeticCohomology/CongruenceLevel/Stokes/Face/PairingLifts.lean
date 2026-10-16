module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MixedTransfer

@[expose] public section


/-!
# Lifts exist for every mixed class of a line or plane face: the face pairings of mixed classes are cone pairings of data

Formalized by Claude Sonnet 5.5.

For a representation `ρ` of `Γ(6) ⊂ SL₃(ℤ)` and a line face `i`, let `lineMixedSub ρ i ⊂ H²(Γ(6) ∩ h⁻¹Qh, E)` be the classes vanishing on the stabilizer of every complete flag over
the line (the locally inner classes of the paper, `lineLocallyInner`).  For classes `x ∈ lineMixedSub ρ i`, `y ∈ lineMixedSub ρ.dual i`:

* `lineFace_exists_lifts`: there are line data `d`, `e` supported on the orbit with the Shapiro coordinates `τ x`, `τ y`;
* `lineFacePairM_eq_cone`: the face pairing `lineFacePairM ρ i x y` is the cone pairing of ANY such lifts (so the fallback `0` of the `if` in `lineOrbitPair` is never used).

The same for planes.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section Mixed

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- **The mixed classes of the line face `i`**: classes of `H²(Γ(6) ∩ h⁻¹Qh, E)` vanishing on the stabilizer of every complete flag over the line. -/
def lineMixedSub (i : LineFaces 6) :
    Submodule ℂ (groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ))) :=
  ⨅ F : GL (Fin 2) ℚ, LinearMap.ker (twoCohomologyRestriction (lineFlagStab 6 i.rep F).subtype
    (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))

/-- **The mixed classes of the plane face `i`.** -/
def planeMixedSub (i : PlaneFaces 6) :
    Submodule ℂ (groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ))) :=
  ⨅ F : GL (Fin 2) ℚ, LinearMap.ker (twoCohomologyRestriction (faceFlagStab 6 (planeFaceRepr i) F).subtype
    (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineMixedSub_apply (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (hx : x ∈ lineMixedSub ρ i) (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (lineFlagStab 6 i.rep F).subtype
      (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) x = 0 :=
  LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hx F)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeMixedSub_apply (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (hx : x ∈ planeMixedSub ρ i) (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (faceFlagStab 6 (planeFaceRepr i) F).subtype
      (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) x = 0 :=
  LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hx F)

/-- The class `τ x` at the orbit representative of the line face `i` is mixed. -/
theorem lineFace_mixedModel (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (hx : x ∈ lineMixedSub ρ i) :
    MixedModel (W := qRep (MonoidHom.id Γ6) (rep6 ρ)) flagLineOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant (lineFacesEquivOrbits i)
      (faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) (rep6 ρ) i
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x)) :=
  faceTauQ_mixed (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
    (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
    (fun i => lineEmb_range i.rep) flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant
    (rep6 ρ) i _ (fun F' hF' => lineMixed_hx ρ i x (lineMixedSub_apply ρ i x hx) F' hF')

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineFace_mixedModel_dual (i : LineFaces 6)
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hy : y ∈ lineMixedSub ρ.dual i) :
    MixedModel (W := qRep (MonoidHom.id Γ6) (rep6 ρ).dual) flagLineOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant (lineFacesEquivOrbits i)
      (faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y)) :=
  faceTauQ_mixed (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
    (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
    (fun i => lineEmb_range i.rep) flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant
    (rep6 ρ).dual i _ (fun F' hF' => lineMixedDual_hx ρ i y (lineMixedSub_apply ρ.dual i y hy) F' hF')

/-- The class `τ x` at the orbit representative of the plane face `i` is mixed. -/
theorem planeFace_mixedModel (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (hx : x ∈ planeMixedSub ρ i) :
    MixedModel (W := qRep (MonoidHom.id Γ6) (rep6 ρ)) flagPlaneOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant (planeFacesEquivOrbits i)
      (faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x)) :=
  faceTauQ_mixed (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
    (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
    (fun i => planeEmb_range (planeFaceRepr i)) flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant
    (rep6 ρ) i _ (fun F' hF' => planeMixed_hx ρ i x (planeMixedSub_apply ρ i x hx) F' hF')

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeFace_mixedModel_dual (i : PlaneFaces 6)
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hy : y ∈ planeMixedSub ρ.dual i) :
    MixedModel (W := qRep (MonoidHom.id Γ6) (rep6 ρ).dual) flagPlaneOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant (planeFacesEquivOrbits i)
      (faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y)) :=
  faceTauQ_mixed (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
    (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
    (fun i => planeEmb_range (planeFaceRepr i)) flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant
    (rep6 ρ).dual i _ (fun F' hF' => planeMixedDual_hx ρ i y (planeMixedSub_apply ρ.dual i y hy) F' hF')


omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineFace_pair_eq_cone [Module ℚ V] [IsScalarTower ℚ ℂ V] (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (d : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hd : d.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)))
    (he : e.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)))
    (hdc : d.coord (lineFacesEquivOrbits i) =
      faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) (rep6 ρ) i
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x))
    (hec : e.coord (lineFacesEquivOrbits i) =
      faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y)) :
    lineFacePairM ρ i x y = conePairC (evalC (MonoidHom.id Γ6) (rep6 ρ)) stokesCycle d.cone e.cone := by
  unfold lineFacePairM lineFacePair
  rw [← hdc, ← hec]
  exact lineOrbitPair_eq _ stokesCycle stokesCycle_isCoinvCycle _ d e hd he

/-- **Lifts exist for every pair of mixed classes of a line face, and the face pairing is the cone pairing of the lifts.** -/
theorem lineFace_exists_lifts (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx : x ∈ lineMixedSub ρ i) (hy : y ∈ lineMixedSub ρ.dual i) :
    ∃ (d : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual)),
      d.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)) ∧ e.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)) ∧
      d.coord (lineFacesEquivOrbits i) =
        faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
          (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
          (fun i => lineEmb_range i.rep) (rep6 ρ) i
          (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x) ∧
      e.coord (lineFacesEquivOrbits i) =
        faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
          (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
          (fun i => lineEmb_range i.rep) (rep6 ρ).dual i
          (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y) := by
  obtain ⟨d, hd, hdc⟩ := LineMixedModel_liftable (W := qRep (MonoidHom.id Γ6) (rep6 ρ)) (lineFacesEquivOrbits i) _
    (lineFace_mixedModel ρ i x hx)
  obtain ⟨e, he, hec⟩ := LineMixedModel_liftable (W := qRep (MonoidHom.id Γ6) (rep6 ρ).dual) (lineFacesEquivOrbits i) _
    (lineFace_mixedModel_dual ρ i y hy)
  exact ⟨d, e, hd, he, hdc, hec⟩

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeFace_pair_eq_cone [Module ℚ V] [IsScalarTower ℚ ℂ V] (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hd : d.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)))
    (he : e.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)))
    (hdc : d.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x))
    (hec : e.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y)) :
    planeFacePairM ρ i x y = conePairC (evalC (MonoidHom.id Γ6) (rep6 ρ)) stokesCycle d.cone e.cone := by
  unfold planeFacePairM planeFacePair
  rw [← hdc, ← hec]
  exact planeOrbitPair_eq _ stokesCycle stokesCycle_isCoinvCycle _ d e hd he

/-- **Lifts exist for every pair of mixed classes of a plane face, and the face pairing is the cone pairing of the lifts.** -/
theorem planeFace_exists_lifts (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hx : x ∈ planeMixedSub ρ i) (hy : y ∈ planeMixedSub ρ.dual i) :
    ∃ (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual)),
      d.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)) ∧ e.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)) ∧
      d.coord (planeFacesEquivOrbits i) =
        faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
          (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
          (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
          (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x) ∧
      e.coord (planeFacesEquivOrbits i) =
        faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
          (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
          (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
          (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y) := by
  obtain ⟨d, hd, hdc⟩ := PlaneMixedModel_liftable (W := qRep (MonoidHom.id Γ6) (rep6 ρ)) (planeFacesEquivOrbits i) _
    (planeFace_mixedModel ρ i x hx)
  obtain ⟨e, he, hec⟩ := PlaneMixedModel_liftable (W := qRep (MonoidHom.id Γ6) (rep6 ρ).dual) (planeFacesEquivOrbits i) _
    (planeFace_mixedModel_dual ρ i y hy)
  exact ⟨d, e, hd, he, hdc, hec⟩

end Mixed

end TernaryPeriodPolynomials.Argument.GammaNStokes

