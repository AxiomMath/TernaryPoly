module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlusEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneESDimension

@[expose] public section


/-!
# The edge of `Λ₀⁺` with Levi quotient `SL(2, ℤ)` and its comparison with the edge of `Λ₀`

The extension `ℤ² → Λ₀⁺ → SL(2, ℤ)` (`plusExtensionS`, Levi quotient the type
`SpecialLinearGroup (Fin 2) ℤ` used by the library's `SL₂(ℤ)` cohomology), its edge
`plusEdgeS` (injective, since `H²` of every representation of `SL₂(ℤ)` vanishes), the coordinate
isomorphism of its radical cohomology with `modularBinaryRep (n+1) (-1)` (`plusRadicalCoordinateIso`),
and the comparison theorem `plusEdge_restrict`: the `Λ₀⁺`-edge of the restriction of a `Λ₀`-class is the
`SL₂(ℤ)`-restriction (`LevelOneESDimension.restriction`) of the library's `Λ₀`-edge
`identityPlaneBinaryEdge`. Used to identify the de Rham class of the seed (Lemma C.3) with the
library's plane classes (S4c).

Written by Claude Opus 5.5.
-/

open GeneralEisenstein Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH2
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension

/-- `SL(2, ℤ)` inside `GL₂(ℤ)` as the subgroup `SL2Z`. -/
def specialToSL2Z : SpecialLinearGroup (Fin 2) ℤ →* SL2Z :=
  (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) ℤ →* GeneralLinearGroup (Fin 2) ℤ).codRestrict _
    (fun m => by
      show GeneralLinearGroup.det (SpecialLinearGroup.toGL m) = 1
      ext
      simp)

theorem sl2zToSpecial_specialToSL2Z (m : SpecialLinearGroup (Fin 2) ℤ) :
    sl2zToSpecial (specialToSL2Z m) = m := Subtype.ext rfl

theorem specialToSL2Z_sl2zToSpecial (m : SL2Z) : specialToSL2Z (sl2zToSpecial m) = m :=
  Subtype.ext (Units.ext rfl)

/-- The Levi projection `Λ₀⁺ → SL(2, ℤ)`. -/
def plusProjS : Lam0Plus →* SpecialLinearGroup (Fin 2) ℤ := sl2zToSpecial.comp plusProj

/-- The Levi section `SL(2, ℤ) → Λ₀⁺`. -/
def plusSectionS : SpecialLinearGroup (Fin 2) ℤ →* Lam0Plus := plusSection.comp specialToSL2Z

theorem plusProjS_section (m : SpecialLinearGroup (Fin 2) ℤ) : plusProjS (plusSectionS m) = m := by
  change sl2zToSpecial (plusProj (plusSection (specialToSL2Z m))) = m
  rw [plusProj_section, sl2zToSpecial_specialToSL2Z]

/-- The split extension `ℤ² → Λ₀⁺ → SL(2, ℤ)`. -/
def plusExtensionS : GroupExtension RadicalLattice Lam0Plus (SpecialLinearGroup (Fin 2) ℤ) where
  inl := plusInl
  rightHom := plusProjS
  inl_injective := plusExtension.inl_injective
  range_inl_eq_ker_rightHom := by
    have h := plusExtension.range_inl_eq_ker_rightHom
    ext g
    change g ∈ plusInl.range ↔ sl2zToSpecial (plusProj g) = 1
    change plusInl.range = plusProj.ker at h
    rw [h, MonoidHom.mem_ker]
    constructor
    · intro hg
      rw [hg, map_one]
    · intro hg
      apply sl2zToSpecial_injective
      rw [hg, map_one]
  rightHom_surjective m := ⟨plusSectionS m, plusProjS_section m⟩

/-- The Levi splitting of `Λ₀⁺ → SL(2, ℤ)`. -/
def plusSplittingS : plusExtensionS.Splitting :=
  ⟨plusSectionS, plusProjS_section⟩

/-- The `(1,1)` edge of `Λ₀⁺`, Levi quotient `SL(2, ℤ)`. -/
def plusEdgeS (n : ℕ) :
    (twoCohomologyRestriction plusExtensionS.inl (plusRep n)).ker →ₗ[ℂ]
      groupCohomology.H1 (splitRadicalH1Representation plusSplittingS (plusRep n)) :=
  splitCohomologyEdge plusSplittingS (plusRep n)

/-- **The edge of `Λ₀⁺` is injective.** -/
theorem plusEdgeS_injective (n : ℕ) : Function.Injective (plusEdgeS n) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero plusSplittingS (plusRep n)
    (fun x => modularH2_zero _ x)

theorem plusS_radicalInput (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    splitRadicalInput plusSplittingS m r =
      splitRadicalInput identityPlaneSplitting (SpecialLinearGroup.toGL m) r := by
  apply identityPlaneRadicalInclusion_injective
  have h1 := congrArg (fun x : Lam0Plus => (x : Lam0)) (splitRadicalInput_commute plusSplittingS m r)
  have h2 := splitRadicalInput_commute identityPlaneSplitting (SpecialLinearGroup.toGL m) r
  change identityPlaneRadicalInclusion r * identityPlaneLeviSection (SpecialLinearGroup.toGL m) =
    identityPlaneLeviSection (SpecialLinearGroup.toGL m) *
      identityPlaneRadicalInclusion (splitRadicalInput plusSplittingS m r) at h1
  change identityPlaneRadicalInclusion r * identityPlaneLeviSection (SpecialLinearGroup.toGL m) =
    identityPlaneLeviSection (SpecialLinearGroup.toGL m) *
      identityPlaneRadicalInclusion (splitRadicalInput identityPlaneSplitting
        (SpecialLinearGroup.toGL m) r) at h2
  exact mul_left_cancel (h1.symm.trans h2)

/-- The Levi action on radical cocycles of `Λ₀⁺` is the library's upper-radical Levi action. -/
theorem plusS_cocycle_action (n : ℕ) (m : SpecialLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    splitRadicalCocycleAction plusSplittingS (plusRep n) m cycle =
      upperRadicalCocycleLevi n (SpecialLinearGroup.toGL m) cycle := by
  apply groupCohomology.cocycles₁_ext
  intro r
  change (plusRep n).ρ (plusSplittingS m) (cycle (splitRadicalInput plusSplittingS m r)) = _
  rw [plusS_radicalInput]
  exact (identityPlaneSplitting_cocycle_action n (SpecialLinearGroup.toGL m) cycle r).symm

theorem plusS_H1_action (n : ℕ) (m : SpecialLinearGroup (Fin 2) ℤ) :
    splitRadicalH1Action plusSplittingS (plusRep n) m =
      upperRadicalH1Levi n (SpecialLinearGroup.toGL m) := by
  apply LinearMap.ext
  intro cohomology
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (upperRadicalLatticeRep n) cohomology
  exact (splitRadicalH1Action_apply plusSplittingS (plusRep n) m cycle).trans
    ((congrArg (fun c : groupCohomology.cocycles₁ (upperRadicalLatticeRep n) =>
      groupCohomology.H1π (upperRadicalLatticeRep n) c) (plusS_cocycle_action n m cycle)).trans
      (upperRadicalH1Levi_apply _ cycle).symm)

/-- The radical cohomology of `Λ₀⁺`, as an `SL(2, ℤ)`-representation, is `Sym^{n+1} ⊗ det⁻¹`. -/
def plusRadicalCoordinateIso (n : ℕ) :
    splitRadicalH1Representation plusSplittingS (plusRep n) ≅ modularBinaryRep (n + 1) (-1) :=
  Rep.mkIso (Representation.Equiv.mk (upperRadicalH1Coordinate n) (by
    intro m
    apply LinearMap.ext
    intro cohomology
    change groupCohomology.H1 (upperRadicalLatticeRep n) at cohomology
    change upperRadicalH1Coordinate n
        (splitRadicalH1Action plusSplittingS (plusRep n) m cohomology) =
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL m))
        (upperRadicalH1Coordinate n cohomology)
    rw [plusS_H1_action]
    exact upperRadicalH1Coordinate_equivariant _ cohomology))

/-- `H¹` of the radical cohomology of `Λ₀⁺` is `H¹(SL(2, ℤ), Sym^{n+1} ⊗ det⁻¹)`. -/
def plusLeviCohomologyIso (n : ℕ) :
    groupCohomology.H1 (splitRadicalH1Representation plusSplittingS (plusRep n)) ≅
      groupCohomology.H1 (modularBinaryRep (n + 1) (-1)) :=
  (groupCohomology.functor ℂ (SpecialLinearGroup (Fin 2) ℤ) 1).mapIso (plusRadicalCoordinateIso n)

/-- Restriction of a relative two-cocycle of `Λ₀` to `Λ₀⁺` (Levi quotient `SL(2, ℤ)`). -/
def plusRestrictS (n : ℕ) :
    relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) →ₗ[ℂ]
      relativeTwoCocycles plusExtensionS.inl (plusRep n) :=
  plusRestrict n

theorem plusS_splitEdgeCycle (n : ℕ) (m : SpecialLinearGroup (Fin 2) ℤ)
    (c : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n)) :
    splitEdgeCycle plusSplittingS (plusRep n) m (plusRestrictS n c) =
      splitEdgeCycle identityPlaneSplitting (identityPlaneCoefficientRep n)
        (SpecialLinearGroup.toGL m) c := by
  apply groupCohomology.cocycles₁_ext
  intro r
  change c.val.val (identityPlaneLeviSection (SpecialLinearGroup.toGL m),
      identityPlaneRadicalInclusion (splitRadicalInput plusSplittingS m r)) -
      c.val.val (identityPlaneRadicalInclusion r, identityPlaneLeviSection (SpecialLinearGroup.toGL m)) =
    c.val.val (identityPlaneLeviSection (SpecialLinearGroup.toGL m),
      identityPlaneRadicalInclusion (splitRadicalInput identityPlaneSplitting
        (SpecialLinearGroup.toGL m) r)) -
      c.val.val (identityPlaneRadicalInclusion r, identityPlaneLeviSection (SpecialLinearGroup.toGL m))
  rw [plusS_radicalInput]

private theorem plusEdge_coord_eq (n : ℕ) (m : SpecialLinearGroup (Fin 2) ℤ)
    (c : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n)) :
    upperRadicalH1Coordinate n (groupCohomology.H1π _
        (splitEdgeCycle plusSplittingS (plusRep n) m (plusRestrictS n c))) =
      upperRadicalH1Coordinate n (groupCohomology.H1π _
        (splitEdgeCycle identityPlaneSplitting (identityPlaneCoefficientRep n)
          (SpecialLinearGroup.toGL m) c)) := by
  rw [plusS_splitEdgeCycle]

/-- The edge cocycles of `Λ₀⁺` and `Λ₀` agree after the binary coordinate isomorphisms. -/
theorem plusEdge_restrict_cocycle (n : ℕ)
    (c : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n)) :
    (groupCohomology.map (MonoidHom.id _) (plusRadicalCoordinateIso n).hom 1)
        (groupCohomology.H1π _ (splitCocycleEdge plusSplittingS (plusRep n) (plusRestrictS n c))) =
      restriction (n + 1) (-1) (-1)
        ((groupCohomology.map (MonoidHom.id _) (identityPlaneRadicalCoordinateIso n).hom 1)
          (groupCohomology.H1π _ (splitCocycleEdge identityPlaneSplitting
            (identityPlaneCoefficientRep n) c))) := by
  rw [groupCohomology.H1π_comp_map_apply, groupCohomology.H1π_comp_map_apply, restriction_apply]
  refine congrArg (fun z => groupCohomology.H1π (modularBinaryRep (n + 1) (-1)) z) ?_
  apply groupCohomology.cocycles₁_ext
  intro m
  exact plusEdge_coord_eq n m c

/-- **Compatibility of the edges.** The `Λ₀⁺`-edge of the restriction of a relative `Λ₀`-cocycle,
in binary coordinates, is the `SL(2, ℤ)`-restriction of the library's `Λ₀`-edge of its class. -/
theorem plusEdge_restrict (n : ℕ)
    (c : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n)) :
    (plusLeviCohomologyIso n).hom (plusEdgeS n
        (relativeTwoCocycleClass plusExtensionS.inl (plusRep n) (plusRestrictS n c))) =
      restriction (n + 1) (-1) (-1) (identityPlaneBinaryEdge n
        (relativeTwoCocycleClass identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) c)) :=
  (congrArg (fun x => (plusLeviCohomologyIso n).hom x)
      (splitCohomologyEdge_apply plusSplittingS (plusRep n) (plusRestrictS n c))).trans
    ((plusEdge_restrict_cocycle n c).trans
      (congrArg (fun x => restriction (n + 1) (-1) (-1) x) (identityPlaneBinaryEdge_apply n c).symm))

end TernaryPeriodPolynomials.Argument.SeedC3S4c
