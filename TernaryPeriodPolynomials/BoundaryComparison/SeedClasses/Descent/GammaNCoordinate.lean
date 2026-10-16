module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNExt

@[expose] public section


/-!
# The radical cohomology of the paper's plane group `Γ(N) ∩ P(ℤ)`

Paper: Lemma C.3
(`ar:lem:seed`): `H¹(N_P, E) ≅ Sym^{n+1} ⊗ det⁻¹` as a `Λ_P`-module, for the plane group
`Γ_P = Γ(N) ∩ P(ℤ)` with radical `N_P = Nℤ²` and Levi block `Λ_P = Γ₂(N)`.

The conjugation operator `T = ρ(diag(1, 1, N))` intertwines the action of the radical `Nℤ²` on `E_n`
with that of `ℤ²` (`tOp_rad`) and commutes with the Levi action, so it induces an isomorphism
`thetaEquiv : H¹(Nℤ², E_n) ≅ H¹(ℤ², E_n)` (`thetaH1`, `thetaH1Inv`); composed with the library's
binary coordinate of the radical cohomology it gives `gammaNCoordinateIso`, an isomorphism of
`Γ₂(N)`-representations from the radical cohomology of `Γ_P` (with the Levi action of the
splitting) onto `Sym^{n+1} ⊗ det⁻¹`. Since `H²(Γ₂(N), W) = 0` for every representation `W`, the
Hochschild--Serre edge of `Γ_P` is injective on classes with zero radical restriction
(`gammaNEdge_injective`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open Matrix GeneralEisenstein CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The radical lattice representation of `Γ(N) ∩ P(ℤ)`: `Nℤ²` acting on `E_n`. -/
abbrev gammaNRadRep : Rep ℂ RadicalLattice := Rep.res (gammaNInl N) (gammaNRep N n)

theorem tOp_rad' (r : RadicalLattice) (v : HomogeneousPoly n) :
    tOp N n ((gammaNRadRep N n).ρ r v) = (upperRadicalLatticeRep n).ρ r (tOp N n v) :=
  tOp_rad N n r v

theorem tOp_rad_intertwines (r : RadicalLattice) :
    ((upperRadicalLatticeRep n).ρ r).comp (tOp N n) = (tOp N n).comp ((gammaNRadRep N n).ρ r) := by
  apply LinearMap.ext
  intro v
  exact (tOp_rad' N n r v).symm


/-- The inverse conjugation operator. -/
def tInv : Module.End ℂ (HomogeneousPoly n) := GeneralEisenstein.realCoefficient n (dmat N)⁻¹

theorem tInv_tOp (v : HomogeneousPoly n) : tInv N n (tOp N n v) = v :=
  (tEquiv N n).left_inv v

theorem tOp_tInv (v : HomogeneousPoly n) : tOp N n (tInv N n v) = v :=
  (tEquiv N n).right_inv v

theorem tInv_rad_intertwines (r : RadicalLattice) :
    ((gammaNRadRep N n).ρ r).comp (tInv N n) =
      (tInv N n).comp ((upperRadicalLatticeRep n).ρ r) := by
  apply LinearMap.ext
  intro v
  apply (tEquiv N n).injective
  change tOp N n ((gammaNRadRep N n).ρ r (tInv N n v)) =
    tOp N n (tInv N n ((upperRadicalLatticeRep n).ρ r v))
  rw [tOp_rad', tOp_tInv]
  exact (tOp_tInv N n _).symm

/-- The comparison `H¹(Nℤ², E_n) → H¹(ℤ², E_n)` induced by `T = ρ(diag(1,1,N))`. -/
def thetaH1 : groupCohomology.H1 (gammaNRadRep N n) →ₗ[ℂ]
    groupCohomology.H1 (upperRadicalLatticeRep n) :=
  oneCocyclePullbackH1 (gammaNRadRep N n) (upperRadicalLatticeRep n) (MonoidHom.id _)
    (tOp N n) (tOp_rad_intertwines N n)

/-- Its inverse. -/
def thetaH1Inv : groupCohomology.H1 (upperRadicalLatticeRep n) →ₗ[ℂ]
    groupCohomology.H1 (gammaNRadRep N n) :=
  oneCocyclePullbackH1 (upperRadicalLatticeRep n) (gammaNRadRep N n) (MonoidHom.id _)
    (tInv N n) (tInv_rad_intertwines N n)

theorem thetaH1_π (c : groupCohomology.cocycles₁ (gammaNRadRep N n)) :
    thetaH1 N n (groupCohomology.H1π (gammaNRadRep N n) c) =
      groupCohomology.H1π (upperRadicalLatticeRep n)
        (oneCocyclePullback (gammaNRadRep N n) (upperRadicalLatticeRep n) (MonoidHom.id _)
          (tOp N n) (tOp_rad_intertwines N n) c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

theorem thetaH1Inv_π (c : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    thetaH1Inv N n (groupCohomology.H1π (upperRadicalLatticeRep n) c) =
      groupCohomology.H1π (gammaNRadRep N n)
        (oneCocyclePullback (upperRadicalLatticeRep n) (gammaNRadRep N n) (MonoidHom.id _)
          (tInv N n) (tInv_rad_intertwines N n) c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

/-- **`H¹(Nℤ², E_n) ≅ H¹(ℤ², E_n)`**. -/
def thetaEquiv : groupCohomology.H1 (gammaNRadRep N n) ≃ₗ[ℂ]
    groupCohomology.H1 (upperRadicalLatticeRep n) :=
  LinearEquiv.ofLinearMap (thetaH1 N n) (thetaH1Inv N n)
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (upperRadicalLatticeRep n) x
      change thetaH1 N n (thetaH1Inv N n (groupCohomology.H1π _ c)) = _
      rw [thetaH1Inv_π, thetaH1_π]
      refine congrArg (fun z => groupCohomology.H1π _ z) ?_
      apply groupCohomology.cocycles₁_ext
      intro r
      exact tOp_tInv N n _)
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (gammaNRadRep N n) x
      change thetaH1Inv N n (thetaH1 N n (groupCohomology.H1π _ c)) = _
      rw [thetaH1_π, thetaH1Inv_π]
      refine congrArg (fun z => groupCohomology.H1π _ z) ?_
      apply groupCohomology.cocycles₁_ext
      intro r
      exact tInv_tOp N n _)



/-- The binary coordinate of the radical cohomology of `Γ(N) ∩ P(ℤ)`. -/
def gammaNRadicalCoordinate : groupCohomology.H1 (gammaNRadRep N n) ≃ₗ[ℂ]
    Binary.HomogeneousPoly (n + 1) :=
  (thetaEquiv N n).trans (upperRadicalH1Coordinate n)

theorem gammaNRadicalCoordinate_π (c : groupCohomology.cocycles₁ (gammaNRadRep N n)) :
    gammaNRadicalCoordinate N n (groupCohomology.H1π (gammaNRadRep N n) c) =
      upperRadicalCocycleCoordinate n
        (oneCocyclePullback (gammaNRadRep N n) (upperRadicalLatticeRep n) (MonoidHom.id _)
          (tOp N n) (tOp_rad_intertwines N n) c) := by
  change upperRadicalH1Coordinate n (thetaH1 N n (groupCohomology.H1π _ c)) = _
  rw [thetaH1_π, upperRadicalH1Coordinate_apply]

/-- **The radical cohomology `H¹(Nℤ², E_n)` of the paper's plane group is
`Sym^{n+1} ⊗ det⁻¹` as a `Γ₂(N)`-representation.** -/
def gammaNCoordinateIso :
    splitRadicalH1Representation (gammaNSplitting N) (gammaNRep N n) ≅
      Rep.res (CongruenceSubgroup.Gamma N).subtype (modularBinaryRep (n + 1) (-1)) :=
  Rep.mkIso (Representation.Equiv.mk (gammaNRadicalCoordinate N n) (by
    intro A
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (Rep.res (gammaNExt N).inl (gammaNRep N n)) x
    have h1 := splitRadicalH1Action_apply (gammaNSplitting N) (gammaNRep N n) A c
    have hcyc : oneCocyclePullback (gammaNRadRep N n) (upperRadicalLatticeRep n) (MonoidHom.id _)
        (tOp N n) (tOp_rad_intertwines N n)
        (splitRadicalCocycleAction (gammaNSplitting N) (gammaNRep N n) A c) =
        upperRadicalCocycleLevi n (SpecialLinearGroup.toGL A.1)
          (oneCocyclePullback (gammaNRadRep N n) (upperRadicalLatticeRep n) (MonoidHom.id _)
            (tOp N n) (tOp_rad_intertwines N n) c) := by
      apply groupCohomology.cocycles₁_ext
      intro r
      change tOp N n ((gammaNRep N n).ρ (gammaNSplitting N A)
          (c (splitRadicalInput (gammaNSplitting N) A r))) = _
      rw [gammaN_radicalInput, upperRadicalCocycleLevi_apply]
      exact tOp_sect N n A _
    have h2 := gammaNRadicalCoordinate_π N n
      (splitRadicalCocycleAction (gammaNSplitting N) (gammaNRep N n) A c)
    have h3 := gammaNRadicalCoordinate_π N n c
    have h4 := upperRadicalH1Coordinate_equivariant (SpecialLinearGroup.toGL A.1)
      (groupCohomology.H1π (upperRadicalLatticeRep n)
        (oneCocyclePullback (gammaNRadRep N n) (upperRadicalLatticeRep n) (MonoidHom.id _)
          (tOp N n) (tOp_rad_intertwines N n) c))
    rw [upperRadicalH1Levi_apply, upperRadicalH1Coordinate_apply,
      upperRadicalH1Coordinate_apply] at h4
    change gammaNRadicalCoordinate N n
        (splitRadicalH1Action (gammaNSplitting N) (gammaNRep N n) A
          (groupCohomology.H1π (Rep.res (gammaNExt N).inl (gammaNRep N n)) c)) =
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL A.1))
        (gammaNRadicalCoordinate N n (groupCohomology.H1π (gammaNRadRep N n) c))
    refine (congrArg (gammaNRadicalCoordinate N n) h1).trans (h2.trans ?_)
    rw [hcyc, h3]
    exact h4))


/-- **The Hochschild--Serre edge of the paper's plane group is injective** on the classes with
zero radical restriction (`H²(Γ₂(N), W) = 0` for every `W`). -/
theorem gammaNEdge_injective :
    Function.Injective (splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n)) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero (gammaNSplitting N) (gammaNRep N n)
    (fun x => H2_vanish_level (CongruenceSubgroup.Gamma N) _ x)

/-- `H¹` of the radical cohomology of `Γ_P` is `H¹(Γ₂(N), Sym^{n+1} ⊗ det⁻¹)`. -/
def gammaNLeviIso :
    groupCohomology.H1 (splitRadicalH1Representation (gammaNSplitting N) (gammaNRep N n)) ≅
      groupCohomology.H1 (binRep (CongruenceSubgroup.Gamma N) n) :=
  (groupCohomology.functor ℂ (CongruenceSubgroup.Gamma N) 1).mapIso (gammaNCoordinateIso N n)

/-- **The edge of the paper's plane group in binary coordinates.** -/
def gammaNEdge :
    (twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n)).ker →ₗ[ℂ]
      groupCohomology.H1 (binRep (CongruenceSubgroup.Gamma N) n) :=
  (ModuleCat.Hom.hom (gammaNLeviIso N n).hom).comp
    (splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n))

theorem gammaNEdge_injective_binary : Function.Injective (gammaNEdge N n) := by
  intro x y h
  apply gammaNEdge_injective N n
  have h' := congrArg (ModuleCat.Hom.hom (gammaNLeviIso N n).inv) h
  have e : ∀ z, (ModuleCat.Hom.hom (gammaNLeviIso N n).inv)
      ((ModuleCat.Hom.hom (gammaNLeviIso N n).hom) z) = z := fun z =>
    congrArg (fun φ => ModuleCat.Hom.hom φ z) (gammaNLeviIso N n).hom_inv_id
  simpa [gammaNEdge, e] using h'

end TernaryPeriodPolynomials.Argument.SeedC3S4c
