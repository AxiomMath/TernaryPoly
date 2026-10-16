module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceActionFinrank

@[expose] public section


/-!
# The descended canonical face pairing is a perfect pairing on the finite-group invariants

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`: "The two internal orientation characters multiply to the face orientation.  All determinant and reflection actions are retained
before taking finite-group invariants, so the descended pairing is still perfect."

the `FaceAction.cusp_descends_left/right/finrank` (and the concrete `lineFace_descends_*`, `planeFace_descends_*`) state the two kernel conditions and the equality of dimensions separately, for the canonical pairing `facePairingCan` of the cuspidal groups
`𝒞(H¹(N, ρ))`, `𝒞(H¹(N, ρ^*))` restricted to the `G`-invariants (`G` the face stabilizer in `SL₃(ℤ)`, determinant and reflection elements included, acting through the finite quotient by the face group of `Γ(N)`).  Here they are assembled into
Mathlib's `LinearMap.IsPerfPair` for the restricted pairing:

* `FaceAction.descended_isPerfPair`: generic `FaceAction`;
* `lineFace_descended_isPerfPair`, `planeFace_descended_isPerfPair`: the faces of `Γ(N)`, any finite-dimensional coefficient module of `SL₃(ℤ)`;
* `lineFace_descended_isPerfPair_En`, `planeFace_descended_isPerfPair_En`: for `E_n`.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FrameInvariance
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
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
/-- **The descended pairing is perfect.**  The canonical pairing of `𝒞(H¹(N, ρ))` and `𝒞(H¹(N, ρ^*))` restricted to the `G`-invariants is a perfect pairing (`LinearMap.IsPerfPair`). -/
theorem FaceAction.descended_isPerfPair :
    ((facePairingCan hN s hdet ρ).compl₁₂ (F.invariants s).subtype (F.invariantsDual s).subtype).IsPerfPair := by
  have hfd : FiniteDimensional ℂ (splitRadicalH1Representation s ρ) := finiteDimensional_H1 (Rep.res ext.inl ρ)
  have h1 := finiteDimensional_cuspidal hN (splitRadicalH1Representation s ρ)
  refine LinearMap.IsPerfPair.of_injective ?_ ?_
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact F.cusp_descends_left s hdet K hK hrad x (fun y => by simpa using LinearMap.congr_fun hx y)
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact F.cusp_descends_right s hdet K hK hrad y (fun x => by simpa using LinearMap.congr_fun hy x)

end Generic

section Concrete

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ)) {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ SL(3, ℤ) V)

/-- **The descended canonical pairing of the line face is perfect**: on the invariants of the face stabilizer in `SL₃(ℤ)` (determinant and reflection elements included) the canonical pairing of
`𝒞(H¹(N_R, ρ))` and `𝒞(H¹(N_R, ρ^*))` is a perfect pairing. -/
theorem lineFace_descended_isPerfPair [FiniteDimensional ℂ (lineGRep ρ N h)] :
    ((facePairingCan hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) (lineGRep ρ N h)).compl₁₂
      ((lineFaceAction N hN h ρ).invariants (lineFaceSplitting N h)).subtype
      ((lineFaceAction N hN h ρ).invariantsDual (lineFaceSplitting N h)).subtype).IsPerfPair := by
  have := gammaNQAt_big_normal N h
  have hfi := gammaNQAt_big_finiteIndex N h hN
  have : Finite (↥(bigLineStabAt h) ⧸ (gammaNQAt N h).subgroupOf (bigLineStabAt h)) :=
    @Subgroup.finite_quotient_of_finiteIndex _ _ _ hfi
  exact (lineFaceAction N hN h ρ).descended_isPerfPair (lineFaceSplitting N h) (lineFaceRadicalInput_det N h)
    ((gammaNQAt N h).subgroupOf (bigLineStabAt h)) (lineFace_inner N hN h ρ) (lineFaceAction_radDet N hN h ρ)

/-- **The descended canonical pairing of the plane face is perfect**. -/
theorem planeFace_descended_isPerfPair [FiniteDimensional ℂ (planeGRep ρ N h)] :
    ((facePairingCan hN (faceSplitting N h) (planeFaceRadicalInput_det N h) (planeGRep ρ N h)).compl₁₂
      ((planeFaceAction N hN h ρ).invariants (faceSplitting N h)).subtype
      ((planeFaceAction N hN h ρ).invariantsDual (faceSplitting N h)).subtype).IsPerfPair := by
  have := gammaNPAt_big_normal N h
  have hfi := gammaNPAt_big_finiteIndex N h hN
  have : Finite (↥(bigPlaneStabAt h) ⧸ (gammaNPAt N h).subgroupOf (bigPlaneStabAt h)) :=
    @Subgroup.finite_quotient_of_finiteIndex _ _ _ hfi
  exact (planeFaceAction N hN h ρ).descended_isPerfPair (faceSplitting N h) (planeFaceRadicalInput_det N h)
    ((gammaNPAt N h).subgroupOf (bigPlaneStabAt h)) (planeFace_inner N hN h ρ) (planeFaceAction_radDet N hN h ρ)

end Concrete

section En

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ)) (n : ℕ)

instance lineGRepAmbFD : FiniteDimensional ℂ (lineGRep (ambRep n) N h) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ n)

instance planeGRepAmbFD : FiniteDimensional ℂ (planeGRep (ambRep n) N h) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ n)

/-- The same for `E_n = Sym^n((ℂ³)*)` and its literal contragredient. -/
theorem lineFace_descended_isPerfPair_En :
    ((facePairingCan hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) (lineGRep (ambRep n) N h)).compl₁₂
      ((lineFaceAction N hN h (ambRep n)).invariants (lineFaceSplitting N h)).subtype
      ((lineFaceAction N hN h (ambRep n)).invariantsDual (lineFaceSplitting N h)).subtype).IsPerfPair :=
  lineFace_descended_isPerfPair N hN h (ambRep n)

/-- The same for the plane face and `E_n`. -/
theorem planeFace_descended_isPerfPair_En :
    ((facePairingCan hN (faceSplitting N h) (planeFaceRadicalInput_det N h) (planeGRep (ambRep n) N h)).compl₁₂
      ((planeFaceAction N hN h (ambRep n)).invariants (faceSplitting N h)).subtype
      ((planeFaceAction N hN h (ambRep n)).invariantsDual (faceSplitting N h)).subtype).IsPerfPair :=
  planeFace_descended_isPerfPair N hN h (ambRep n)

end En

end TernaryPeriodPolynomials.Argument.FaceDescent
