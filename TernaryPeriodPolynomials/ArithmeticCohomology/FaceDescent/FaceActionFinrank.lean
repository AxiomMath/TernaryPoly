module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceActionDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.CuspidalFinite
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.LineFaceDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.PlaneFaceDescent

@[expose] public section


/-!
# The invariants of the cuspidal groups have the same dimension

Formalized by Claude Sonnet 5.5.

`FaceAction.cusp_descends_finrank`: with the hypotheses of `cusp_descends_left/right`, the `G`-invariants of `𝒞(H¹(N, ρ))` and of `𝒞(H¹(N, ρ^*))` have the same (finite) dimension (the canonical pairing between them is perfect on both sides and the
cuspidal groups are finite-dimensional, `finiteDimensional_cuspidal`).  `lineFace_descends_finrank`, `planeFace_descends_finrank`: the same for the faces of `Γ(N)` and the stabilizers in `SL₃(ℤ)`.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FrameInvariance
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c

section Generic

variable {N : ℕ} {hN : 3 ≤ N} {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)} {ρ : Rep ℂ E}
  {G : Type} [Group G] (F : FaceAction hN ext ρ G) [FiniteDimensional ℂ ρ] (s : ext.Splitting)
  (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (K : Subgroup G) [K.Normal]
  (hK : ∀ k ∈ K, ∃ e : E, (∀ e', F.θ k e' = e * e' * e⁻¹) ∧ ∀ v, F.T k v = ρ.ρ e v) [Finite (G ⧸ K)]
  (hrad : ∀ g, radDet (F.twist g).φ.toMonoidHom = (((F.A g)⁻¹).val.det : ℤ))

include hdet hK hrad in
/-- **The two spaces of invariants have the same dimension.** -/
theorem FaceAction.cusp_descends_finrank :
    Module.finrank ℂ (F.invariants s) = Module.finrank ℂ (F.invariantsDual s) := by
  classical
  have : Fintype (G ⧸ K) := Fintype.ofFinite (G ⧸ K)
  have hfd : FiniteDimensional ℂ (splitRadicalH1Representation s ρ) := finiteDimensional_H1 (Rep.res ext.inl ρ)
  have hfd' : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG ρ)) :=
    finiteDimensional_H1 (Rep.res ext.inl (dualRepG ρ))
  have h1 := finiteDimensional_cuspidal hN (splitRadicalH1Representation s ρ)
  have h2 := finiteDimensional_cuspidal hN (splitRadicalH1Representation s (dualRepG ρ))
  have hK1 : ∀ k ∈ K, ∀ v, F.cuspRep s k v = v := fun k hk v => F.cuspRep_trivial s K hK k hk v
  have hK2 : ∀ k ∈ K, ∀ v, F.dual.cuspRep s k v = v := fun k hk v => F.dual_cuspRep_trivial s K hK k hk v
  have hinv : ∀ (q : G ⧸ K) v w, facePairingCan hN s hdet ρ (quotRep (F.cuspRep s) K hK1 q v)
      (quotRep (F.dual.cuspRep s) K hK2 q w) = facePairingCan hN s hdet ρ v w := by
    intro q v w
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [quotRep_mk, quotRep_mk]
    exact F.pairing_invariant s hdet hrad g v w
  have e1 : F.invariants s = isoSub (quotRep (F.cuspRep s) K hK1) 1 := by
    ext x; exact (mem_isoSub_quotRep_one _ K hK1).symm
  have e2 : F.invariantsDual s = isoSub (quotRep (F.dual.cuspRep s) K hK2) 1 := by
    ext x; exact (mem_isoSub_quotRep_one _ K hK2).symm
  rw [e1, e2]
  exact isoPairing_finrank_eq (facePairingCan hN s hdet ρ) 1 1 1 (fun g => by simp)
    (fun q v w => by simpa using hinv q v w) (facePairingCan_perfect hN s hdet ρ).1 (facePairingCan_perfect hN s hdet ρ).2

end Generic

section Concrete

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ)) {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ SL(3, ℤ) V)

/-- **The descended pairing of the line face: the two spaces of invariants have the same dimension.** -/
theorem lineFace_descends_finrank [FiniteDimensional ℂ (lineGRep ρ N h)] :
    Module.finrank ℂ ((lineFaceAction N hN h ρ).invariants (lineFaceSplitting N h)) =
      Module.finrank ℂ ((lineFaceAction N hN h ρ).invariantsDual (lineFaceSplitting N h)) := by
  have := gammaNQAt_big_normal N h
  have hfi := gammaNQAt_big_finiteIndex N h hN
  have : Finite (↥(bigLineStabAt h) ⧸ (gammaNQAt N h).subgroupOf (bigLineStabAt h)) :=
    @Subgroup.finite_quotient_of_finiteIndex _ _ _ hfi
  exact (lineFaceAction N hN h ρ).cusp_descends_finrank (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) ((gammaNQAt N h).subgroupOf (bigLineStabAt h))
    (lineFace_inner N hN h ρ) (lineFaceAction_radDet N hN h ρ)

/-- **The descended pairing of the plane face: the two spaces of invariants have the same dimension.** -/
theorem planeFace_descends_finrank [FiniteDimensional ℂ (planeGRep ρ N h)] :
    Module.finrank ℂ ((planeFaceAction N hN h ρ).invariants (faceSplitting N h)) =
      Module.finrank ℂ ((planeFaceAction N hN h ρ).invariantsDual (faceSplitting N h)) := by
  have := gammaNPAt_big_normal N h
  have hfi := gammaNPAt_big_finiteIndex N h hN
  have : Finite (↥(bigPlaneStabAt h) ⧸ (gammaNPAt N h).subgroupOf (bigPlaneStabAt h)) :=
    @Subgroup.finite_quotient_of_finiteIndex _ _ _ hfi
  exact (planeFaceAction N hN h ρ).cusp_descends_finrank (faceSplitting N h) (planeFaceRadicalInput_det N h) ((gammaNPAt N h).subgroupOf (bigPlaneStabAt h))
    (planeFace_inner N hN h ρ) (planeFaceAction_radDet N hN h ρ)

end Concrete

end TernaryPeriodPolynomials.Argument.FaceDescent
