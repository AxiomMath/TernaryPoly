module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Pairs
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Dictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Orbits

@[expose] public section


/-!
# The line and plane faces of `Γ(6)` as face data

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section LineData

/-- The embedding of the line group `gammaNQAt 6 h` in the model group `Γ(6)`. -/
def lineEmb (h : SL(3, ℤ)) : ↥(gammaNQAt 6 h) →* Γ6 :=
  (gammaSixEquiv : gammaN 6 →* Γ6).comp (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 h hp))

theorem lineEmb_injective (h : SL(3, ℤ)) : Function.Injective (lineEmb h) :=
  gammaSixEquiv.injective.comp (Subgroup.inclusion_injective _)

theorem lineEmb_range (h : SL(3, ℤ)) : (lineEmb h).range = MulAction.stabilizer Γ6 (lineOf h) := by
  ext γ
  constructor
  · rintro ⟨p, rfl⟩
    exact (mem_stabilizer_lineOf_iff (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 h hp) p) h).2 p.2
  · intro hγ
    obtain ⟨p', rfl⟩ := gammaSixEquiv.surjective γ
    have hp' := (mem_stabilizer_lineOf_iff p' h).1 hγ
    exact ⟨⟨p'.1, hp'⟩, rfl⟩

theorem lineOf_rep_mem (i : LineFaces 6) : lineOf i.rep ∈ labelOrbit Γ6 Line (lineFacesEquivOrbits i) := by
  rw [mem_labelOrbit_iff]
  change Quotient.mk'' (lineOf (Quotient.out i)) = lineFaceToOrbit i
  conv_rhs => rw [← Quotient.out_eq i]
  rfl

end LineData

section PlaneData

/-- The embedding of the plane group `gammaNPAt 6 h` in the model group `Γ(6)`. -/
def planeEmb (h : SL(3, ℤ)) : ↥(gammaNPAt 6 h) →* Γ6 :=
  (gammaSixEquiv : gammaN 6 →* Γ6).comp (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 h hp))

theorem planeEmb_injective (h : SL(3, ℤ)) : Function.Injective (planeEmb h) :=
  gammaSixEquiv.injective.comp (Subgroup.inclusion_injective _)

theorem planeEmb_range (h : SL(3, ℤ)) : (planeEmb h).range = MulAction.stabilizer Γ6 (planeOf h) := by
  ext γ
  constructor
  · rintro ⟨p, rfl⟩
    exact (mem_stabilizer_planeOf_iff (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 h hp) p) h).2 p.2
  · intro hγ
    obtain ⟨p', rfl⟩ := gammaSixEquiv.surjective γ
    have hp' := (mem_stabilizer_planeOf_iff p' h).1 hγ
    exact ⟨⟨p'.1, hp'⟩, rfl⟩

theorem planeOf_rep_mem (i : PlaneFaces 6) :
    planeOf (planeFaceRepr i) ∈ labelOrbit Γ6 Plane (planeFacesEquivOrbits i) := by
  rw [mem_labelOrbit_iff]
  change Quotient.mk'' (planeOf (Quotient.out i)) = planeFaceToOrbit i
  conv_rhs => rw [← Quotient.out_eq i]
  rfl

end PlaneData


section Pairings

noncomputable instance lineOrbitsFintype : Fintype (labelOrbits Γ6 Line) :=
  Fintype.ofEquiv (LineFaces 6) lineFacesEquivOrbits

noncomputable instance planeOrbitsFintype : Fintype (labelOrbits Γ6 Plane) :=
  Fintype.ofEquiv (PlaneFaces 6) planeFacesEquivOrbits

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ Γ6 V)

/-- **The face pairing of the line face `i` of `Γ(6)`**: the orbit pairing at the corresponding orbit of the transports of two classes of `H²` of the line group
`gammaNQAt 6 i.rep`. -/
def lineFacePair (i : LineFaces 6) (x : groupCohomology.H2 (Rep.res (lineEmb i.rep) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (lineEmb i.rep) (Rep.of ρ.dual))) : ℂ :=
  lineOrbitPair (evalC (MonoidHom.id Γ6) ρ) stokesCycle (lineFacesEquivOrbits i)
    (faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
      (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
      (fun i => lineEmb_range i.rep) ρ i x)
    (faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
      (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
      (fun i => lineEmb_range i.rep) ρ.dual i y)

/-- … of the plane face `i`. -/
def planeFacePair (i : PlaneFaces 6) (x : groupCohomology.H2 (Rep.res (planeEmb (planeFaceRepr i)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (planeEmb (planeFaceRepr i)) (Rep.of ρ.dual))) : ℂ :=
  planeOrbitPair (evalC (MonoidHom.id Γ6) ρ) stokesCycle (planeFacesEquivOrbits i)
    (faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
      (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i))
      (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) ρ i x)
    (faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
      (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i))
      (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) ρ.dual i y)


theorem lineCoord_eq (X : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (qRep (MonoidHom.id Γ6) ρ)).homology 2)
    (c : groupCohomology.H2 (Rep.of ρ))
    (hX : (fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) ρ) 2).hom X = qH2 ρ c)
    (i : LineFaces 6) :
    lineCoord (qRep (MonoidHom.id Γ6) ρ) X (lineFacesEquivOrbits i) =
      faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
        (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
        (fun i => lineEmb_range i.rep) ρ i (twoCohomologyRestriction (lineEmb i.rep) (Rep.of ρ) c) := by
  rw [faceTauQ_restriction]
  have h := congrArg (fun m => m.hom X) (faceCoord_restriction (stabilizer Γ6 (lineFacesEquivOrbits i).out)
    (qRep (MonoidHom.id Γ6) ρ) (1 : RationalGL3) (lineFacesEquivOrbits i).out (fun g => g.2) 2)
  have h' : (faceCoord (stabilizer Γ6 (lineFacesEquivOrbits i).out) (qRep (MonoidHom.id Γ6) ρ) (1 : RationalGL3)
      (lineFacesEquivOrbits i).out (fun g => g.2) 2).hom
      ((HomologicalComplex.homologyMap (homPullback (ptMap Line) (qRep (MonoidHom.id Γ6) ρ)) 2).hom X) =
      (groupCohomology.map (stabilizer Γ6 (lineFacesEquivOrbits i).out).subtype
        (𝟙 (Rep.res (stabilizer Γ6 (lineFacesEquivOrbits i).out).subtype (qRep (MonoidHom.id Γ6) ρ))) 2).hom
        ((fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) ρ) 2).hom X) := h
  unfold lineCoord
  rw [h', hX]
  rfl


theorem planeCoord_eq (X : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (qRep (MonoidHom.id Γ6) ρ)).homology 2)
    (c : groupCohomology.H2 (Rep.of ρ))
    (hX : (fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) ρ) 2).hom X = qH2 ρ c)
    (i : PlaneFaces 6) :
    planeCoord (qRep (MonoidHom.id Γ6) ρ) X (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i))
        (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) ρ i
        (twoCohomologyRestriction (planeEmb (planeFaceRepr i)) (Rep.of ρ) c) := by
  rw [faceTauQ_restriction]
  have h := congrArg (fun m => m.hom X) (faceCoord_restriction (stabilizer Γ6 (planeFacesEquivOrbits i).out)
    (qRep (MonoidHom.id Γ6) ρ) (1 : RationalGL3) (planeFacesEquivOrbits i).out (fun g => g.2) 2)
  have h' : (faceCoord (stabilizer Γ6 (planeFacesEquivOrbits i).out) (qRep (MonoidHom.id Γ6) ρ) (1 : RationalGL3)
      (planeFacesEquivOrbits i).out (fun g => g.2) 2).hom
      ((HomologicalComplex.homologyMap (homPullback (ptMap Plane) (qRep (MonoidHom.id Γ6) ρ)) 2).hom X) =
      (groupCohomology.map (stabilizer Γ6 (planeFacesEquivOrbits i).out).subtype
        (𝟙 (Rep.res (stabilizer Γ6 (planeFacesEquivOrbits i).out).subtype (qRep (MonoidHom.id Γ6) ρ))) 2).hom
        ((fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) ρ) 2).hom X) := h
  unfold planeCoord
  rw [h', hX]
  rfl

/-- **Lemma `ar:lem:stokes` at level `Γ(6)`, face by face, in terms of the cohomology of the face groups.**  Let `c`, `c'` be classes of `H²(Γ(6), E)`, `H²(Γ(6), E^*)` whose geometric
representatives in the point resolution have vanishing restrictions to the complete flags.  Then the sum over the line faces `gammaNQAt 6 h` of the face pairings of the restrictions
of `c`, `c'`, plus the sum over the plane faces `gammaNPAt 6 h`, vanishes. -/
theorem gamma6_stokes_classes
    (c : groupCohomology.H2 (Rep.of ρ)) (c' : groupCohomology.H2 (Rep.of ρ.dual))
    (hflag : ∃ (X : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (qRep (MonoidHom.id Γ6) ρ)).homology 2)
        (X' : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (qRep (MonoidHom.id Γ6) ρ.dual)).homology 2),
      (fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) ρ) 2).hom X = qH2 ρ c ∧
      (fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) ρ.dual) 2).hom X' = qH2 ρ.dual c' ∧
      (HomologicalComplex.homologyMap (homPullback (ptMap Flag) (qRep (MonoidHom.id Γ6) ρ)) 2).hom X = 0 ∧
      (HomologicalComplex.homologyMap (homPullback (ptMap Flag) (qRep (MonoidHom.id Γ6) ρ.dual)) 2).hom X' = 0) :
    ∑ i : LineFaces 6, lineFacePair ρ i (twoCohomologyRestriction (lineEmb i.rep) (Rep.of ρ) c)
        (twoCohomologyRestriction (lineEmb i.rep) (Rep.of ρ.dual) c') +
      ∑ i : PlaneFaces 6, planeFacePair ρ i (twoCohomologyRestriction (planeEmb (planeFaceRepr i)) (Rep.of ρ) c)
        (twoCohomologyRestriction (planeEmb (planeFaceRepr i)) (Rep.of ρ.dual) c') = 0 := by
  obtain ⟨X, X', h1, h2, hf, hf'⟩ := hflag
  have key := stokes_orbit_coordinates ρ X X' hf hf'
  rw [← Equiv.sum_comp lineFacesEquivOrbits, ← Equiv.sum_comp planeFacesEquivOrbits] at key
  rw [← key]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold lineFacePair
    rw [lineCoord_eq ρ X c h1 i, lineCoord_eq ρ.dual X' c' h2 i]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold planeFacePair
    rw [planeCoord_eq ρ X c h1 i, planeCoord_eq ρ.dual X' c' h2 i]

end Pairings

end TernaryPeriodPolynomials.Argument.GammaNStokes
