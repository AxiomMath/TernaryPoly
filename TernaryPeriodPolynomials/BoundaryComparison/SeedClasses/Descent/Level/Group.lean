module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.Relative
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ESSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2

@[expose] public section


/-!
# The group `ℤ² ⋊ Λ` for a subgroup `Λ ⊆ SL₂(ℤ)` and its Hochschild--Serre edge

Paper: Lemma C.3
(`ar:lem:seed`), the plane parabolic group with radical `ℤ²` and Levi block `Λ`.

`levelGroup Λ = plusProjS⁻¹(Λ) ⊆ Λ₀⁺` is the split extension `ℤ² → ℤ² ⋊ Λ → Λ`
(`levelExt`, `levelSplitting`) with the coefficient representation `levelRep n` restricted from
`Λ₀⁺`. The radical cohomology is `Sym^{n+1} ⊗ det⁻¹` as a `Λ`-module (`levelCoordinateIso`),
`H²(Λ, W) = 0` for every subgroup `Λ ⊆ SL₂(ℤ)` and every representation `W`
(`H2_vanish_level`, Shapiro's lemma and `ModularH2.modularSubgroupH2_zero`), hence the
`(1,1)` Hochschild--Serre edge is injective on classes with zero radical restriction
(`levelEdge_injective`), whatever the index of `Λ`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

variable (Λ : Subgroup SL(2, ℤ))

/-- The plane group `ℤ² ⋊ Λ ⊂ Λ₀⁺`. -/
def levelGroup : Subgroup Lam0Plus := Λ.comap plusProjS

/-- The radical lattice inside `ℤ² ⋊ Λ`. -/
def levelInl : RadicalLattice →* levelGroup Λ :=
  plusInl.codRestrict _ (fun r => by
    show plusProjS (plusInl r) ∈ Λ
    have : plusProjS (plusInl r) = 1 := plusExtensionS.rightHom_inl r
    rw [this]
    exact one_mem _)

/-- The Levi projection `ℤ² ⋊ Λ → Λ`. -/
def levelRight : levelGroup Λ →* Λ :=
  (plusProjS.comp (levelGroup Λ).subtype).codRestrict Λ (fun g => g.2)

/-- The Levi section `Λ → ℤ² ⋊ Λ`. -/
def levelSection : Λ →* levelGroup Λ :=
  (plusSectionS.comp Λ.subtype).codRestrict (levelGroup Λ) (fun m => by
    show plusProjS (plusSectionS m.1) ∈ Λ
    rw [plusProjS_section]
    exact m.2)

theorem levelRight_section (m : Λ) : levelRight Λ (levelSection Λ m) = m := by
  apply Subtype.ext
  exact plusProjS_section m.1

/-- The split extension `ℤ² → ℤ² ⋊ Λ → Λ`. -/
def levelExt : GroupExtension RadicalLattice (levelGroup Λ) Λ where
  inl := levelInl Λ
  rightHom := levelRight Λ
  inl_injective := fun a b h => plusExtensionS.inl_injective (congrArg Subtype.val h)
  range_inl_eq_ker_rightHom := by
    ext g
    have h := plusExtensionS.range_inl_eq_ker_rightHom
    constructor
    · rintro ⟨r, rfl⟩
      apply Subtype.ext
      exact plusExtensionS.rightHom_inl r
    · intro hg
      have hg' : g.1 ∈ plusExtensionS.rightHom.ker :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      rw [← h] at hg'
      obtain ⟨r, hr⟩ := hg'
      exact ⟨r, Subtype.ext hr⟩
  rightHom_surjective m := ⟨levelSection Λ m, levelRight_section Λ m⟩

/-- The Levi splitting of `ℤ² ⋊ Λ`. -/
def levelSplitting : (levelExt Λ).Splitting := ⟨levelSection Λ, levelRight_section Λ⟩

/-- The coefficient representation of `ℤ² ⋊ Λ`. -/
abbrev levelRep (n : ℕ) : Rep ℂ (levelGroup Λ) := Rep.res (levelGroup Λ).subtype (plusRep n)

/-- `H²(Λ, W) = 0` for every subgroup `Λ ⊂ SL₂(ℤ)` and every representation. -/
theorem H2_vanish_level (A : Rep ℂ Λ) (x : groupCohomology.H2 A) : x = 0 :=
  TernaryPeriodPolynomials.Spectral.ModularH2.modularSubgroupH2_zero Λ A x


theorem level_radicalInput (m : Λ) (r : RadicalLattice) :
    splitRadicalInput (levelSplitting Λ) m r = splitRadicalInput plusSplittingS m.1 r := by
  apply plusExtensionS.inl_injective
  have h1 := congrArg (fun x : levelGroup Λ => (x : Lam0Plus))
    (splitRadicalInput_commute (levelSplitting Λ) m r)
  have h2 := splitRadicalInput_commute plusSplittingS m.1 r
  change plusInl r * plusSectionS m.1 = plusSectionS m.1 *
    plusInl (splitRadicalInput (levelSplitting Λ) m r) at h1
  exact mul_left_cancel (h1.symm.trans h2)

theorem levelRep_res_inl (n : ℕ) :
    Rep.res (levelExt Λ).inl (levelRep Λ n) = upperRadicalLatticeRep n := rfl

theorem level_cocycleAction_eq (n : ℕ) (m : Λ)
    (cycle : groupCohomology.cocycles₁ (Rep.res (levelExt Λ).inl (levelRep Λ n))) :
    splitRadicalCocycleAction (levelSplitting Λ) (levelRep Λ n) m cycle =
      upperRadicalCocycleLevi n (SpecialLinearGroup.toGL m.1) cycle := by
  apply groupCohomology.cocycles₁_ext
  intro r
  change (levelRep Λ n).ρ (levelSplitting Λ m)
    (cycle (splitRadicalInput (levelSplitting Λ) m r)) = _
  rw [level_radicalInput, plusS_radicalInput]
  exact (identityPlaneSplitting_cocycle_action n (SpecialLinearGroup.toGL m.1) cycle r).symm

def levelCoordinateIso (n : ℕ) :
    splitRadicalH1Representation (levelSplitting Λ) (levelRep Λ n) ≅
      Rep.res Λ.subtype (modularBinaryRep (n + 1) (-1)) :=
  Rep.mkIso (Representation.Equiv.mk (upperRadicalH1Coordinate n) (by
    intro m
    apply LinearMap.ext
    intro cohomology
    refine Eq.trans ?_ (upperRadicalH1Coordinate_equivariant (SpecialLinearGroup.toGL m.1)
      cohomology)
    show upperRadicalH1Coordinate n
        (splitRadicalH1Action (levelSplitting Λ) (levelRep Λ n) m cohomology) = _
    have hobtain1 := oneCocycle_H1_surjective _ cohomology
    obtain ⟨cycle, rfl⟩ := hobtain1
    rw [splitRadicalH1Action_apply]
    have hcyc := level_cocycleAction_eq Λ n m cycle
    rw [hcyc]
    exact congrArg (upperRadicalH1Coordinate n)
      (upperRadicalH1Levi_apply (SpecialLinearGroup.toGL m.1) cycle).symm))

theorem levelEdge_injective (n : ℕ) :
    Function.Injective (splitCohomologyEdge (levelSplitting Λ) (levelRep Λ n)) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero (levelSplitting Λ) (levelRep Λ n)
    (fun x => H2_vanish_level Λ _ x)

/-- `H¹` of the radical cohomology of `ℤ² ⋊ Λ` is `H¹(Λ, Sym^{n+1} ⊗ det⁻¹)`. -/
def levelLeviIso (n : ℕ) :
    groupCohomology.H1 (splitRadicalH1Representation (levelSplitting Λ) (levelRep Λ n)) ≅
      groupCohomology.H1 (binRep Λ n) :=
  (groupCohomology.functor ℂ Λ 1).mapIso (levelCoordinateIso Λ n)

/-- **The edge of `ℤ² ⋊ Λ` in binary coordinates**: classes with zero radical restriction map to
`H¹(Λ, Sym^{n+1} ⊗ det⁻¹)`. -/
def levelEdge (n : ℕ) :
    (twoCohomologyRestriction (levelExt Λ).inl (levelRep Λ n)).ker →ₗ[ℂ]
      groupCohomology.H1 (binRep Λ n) :=
  (ModuleCat.Hom.hom (levelLeviIso Λ n).hom).comp
    (splitCohomologyEdge (levelSplitting Λ) (levelRep Λ n))

theorem levelEdge_injective_binary (n : ℕ) : Function.Injective (levelEdge Λ n) := by
  intro x y h
  apply levelEdge_injective Λ n
  have h' := congrArg (ModuleCat.Hom.hom (levelLeviIso Λ n).inv) h
  have e : ∀ z, (ModuleCat.Hom.hom (levelLeviIso Λ n).inv)
      ((ModuleCat.Hom.hom (levelLeviIso Λ n).hom) z) = z := fun z =>
    congrArg (fun φ => ModuleCat.Hom.hom φ z) (levelLeviIso Λ n).hom_inv_id
  simpa [levelEdge, e] using h'


end TernaryPeriodPolynomials.Argument.SeedC3S4c
