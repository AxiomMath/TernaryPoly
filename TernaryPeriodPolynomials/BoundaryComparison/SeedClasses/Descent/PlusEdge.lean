module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlusGroup
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2

@[expose] public section


/-!
# The Hochschild–Serre edge of `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)`

The library's binary edge `identityPlaneBinaryEdge` (the `(1,1)` Hochschild–Serre edge of the
identity-plane stabilizer `Λ₀ = ℤ² ⋊ GL₂(ℤ)`) is built from the generic split-extension edge
`splitCohomologyEdge`. This module applies the same construction to the determinant-one part
`Λ₀⁺` (`plusEdge`) and proves that it is injective on classes with zero radical restriction
(`plusEdge_injective`), because `H²` of every representation of `SL₂(ℤ)` vanishes
(`ModularH2.modularSubgroupH2_zero`). It is used to identify the de Rham class of the seed
(Lemma C.3) with the library's plane classes (S4c).

Written by Claude Opus 5.5.
-/

open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH2

/-- The coefficient representation of `Λ₀⁺` (restriction of the library's `Λ₀`-representation). -/
abbrev plusRep (n : ℕ) : Rep ℂ Lam0Plus :=
  Rep.res Lam0Plus.subtype (identityPlaneCoefficientRep n)

/-- `SL₂(ℤ) ⊂ GL₂(ℤ)` embeds in `SpecialLinearGroup (Fin 2) ℤ`. -/
def sl2zToSpecial : SL2Z →* SpecialLinearGroup (Fin 2) ℤ where
  toFun m := ⟨((m : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ), by
    have h : GeneralLinearGroup.det (m : GeneralLinearGroup (Fin 2) ℤ) = 1 := m.property
    have := congrArg Units.val h
    simpa [GeneralLinearGroup.val_det_apply] using this⟩
  map_one' := Subtype.ext rfl
  map_mul' a b := Subtype.ext rfl

theorem sl2zToSpecial_injective : Function.Injective sl2zToSpecial := by
  intro a b h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

/-- `H²` of every complex representation of `SL₂(ℤ)` vanishes. -/
theorem sl2z_H2_zero (A : Rep ℂ SL2Z) (x : groupCohomology.H2 A) : x = 0 :=
  H2_zero_of_injective sl2zToSpecial sl2zToSpecial_injective
    (fun S B y => modularSubgroupH2_zero S B y) A x

/-- The `(1,1)` edge of `Λ₀⁺` on classes with zero radical restriction. -/
def plusEdge (n : ℕ) :
    (twoCohomologyRestriction plusExtension.inl (plusRep n)).ker →ₗ[ℂ]
      groupCohomology.H1 (splitRadicalH1Representation plusSplitting (plusRep n)) :=
  splitCohomologyEdge plusSplitting (plusRep n)

/-- **The edge of `Λ₀⁺` is injective.** -/
theorem plusEdge_injective (n : ℕ) : Function.Injective (plusEdge n) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero plusSplitting (plusRep n)
    (fun x => sl2z_H2_zero _ x)

/-! ### Compatibility with the edge of `Λ₀` -/

/-- The radical conjugation of `Λ₀⁺` is that of `Λ₀`. -/
theorem plus_radicalInput (m : SL2Z) (r : RadicalLattice) :
    splitRadicalInput plusSplitting m r =
      splitRadicalInput identityPlaneSplitting (m : GeneralLinearGroup (Fin 2) ℤ) r := by
  apply identityPlaneRadicalInclusion_injective
  have h1 := congrArg (fun x : Lam0Plus => (x : Lam0)) (splitRadicalInput_commute plusSplitting m r)
  have h2 := splitRadicalInput_commute identityPlaneSplitting (m : GeneralLinearGroup (Fin 2) ℤ) r
  change identityPlaneRadicalInclusion r * identityPlaneLeviSection m =
    identityPlaneLeviSection m * identityPlaneRadicalInclusion (splitRadicalInput plusSplitting m r) at h1
  change identityPlaneRadicalInclusion r * identityPlaneLeviSection m =
    identityPlaneLeviSection m *
      identityPlaneRadicalInclusion (splitRadicalInput identityPlaneSplitting m r) at h2
  exact mul_left_cancel (h1.symm.trans h2)

/-- Restriction of a relative two-cocycle of `Λ₀` to `Λ₀⁺`. -/
def plusRestrict (n : ℕ) :
    relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) →ₗ[ℂ]
      relativeTwoCocycles plusExtension.inl (plusRep n) where
  toFun c := ⟨twoCocycleRestriction Lam0Plus.subtype (identityPlaneCoefficientRep n) c.val,
    fun a b => c.property a b⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The edge cocycle of the restriction is the restriction of the edge cocycle. -/
theorem plus_splitEdgeCycle (n : ℕ) (m : SL2Z)
    (c : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n))
    (r : RadicalLattice) :
    ((splitEdgeCycle plusSplitting (plusRep n) m (plusRestrict n c) r :
        Rep.res plusExtension.inl (plusRep n)) : HomogeneousPoly n) =
      ((splitEdgeCycle identityPlaneSplitting (identityPlaneCoefficientRep n)
        (m : GeneralLinearGroup (Fin 2) ℤ) c r : Rep.res identityPlaneRadicalInclusion
          (identityPlaneCoefficientRep n)) : HomogeneousPoly n) := by
  change c.val.val (identityPlaneLeviSection m,
      identityPlaneRadicalInclusion (splitRadicalInput plusSplitting m r)) -
      c.val.val (identityPlaneRadicalInclusion r, identityPlaneLeviSection m) =
    c.val.val (identityPlaneLeviSection m,
      identityPlaneRadicalInclusion (splitRadicalInput identityPlaneSplitting m r)) -
      c.val.val (identityPlaneRadicalInclusion r, identityPlaneLeviSection m)
  rw [plus_radicalInput]

end TernaryPeriodPolynomials.Argument.SeedC3S4c
