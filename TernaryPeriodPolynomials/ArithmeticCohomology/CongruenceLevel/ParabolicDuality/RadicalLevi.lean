module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalCocycles
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.RadicalAction

@[expose] public section


/-!
# The Koszul pairing of the radical `H¹(N_R, E) × H¹(N_R, E^*)` and its Levi invariance

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

For a split extension `ℤ² → E → L` with Levi section `s`, coefficient modules `ρ, ρ'` of `E` with a perfect `E`-invariant pairing
`e` (a finite-dimensional module and its contragredient), the Koszul pairing of `RadicalCocycles` is a perfect pairing
`radPairingOf : H¹(ℤ², ρ) × H¹(ℤ², ρ') → ℂ`, and it is invariant under the Levi action
`splitRadicalH1Representation` of every `m ∈ L` whose action `splitRadicalInput` on the radical lattice has determinant one
(`radPairingOf_levi`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped Classical

/-- The determinant of an endomorphism of the radical lattice `ℤ²`. -/
def radDet (ψ : RadicalLattice →* RadicalLattice) : ℤ :=
  (ψ rl1).toAdd.1 * (ψ rl2).toAdd.2 - (ψ rl1).toAdd.2 * (ψ rl2).toAdd.1

section Pullback

variable {A A' : Rep ℂ RadicalLattice} {e : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ}

/-- **The Koszul pairing transforms by the determinant under a change of the radical lattice.** -/
theorem PhiC_pullback (he : ∀ g a b, e (A.ρ g a) (A'.ρ g b) = e a b) (ψ : RadicalLattice →* RadicalLattice)
    (S : A →ₗ[ℂ] A) (S' : A' →ₗ[ℂ] A')
    (hS' : ∀ r b, A'.ρ r (S' b) = S' (A'.ρ (ψ r) b)) (hSe : ∀ a b, e (S a) (S' b) = e a b)
    (c d : groupCohomology.cocycles₁ A) (c' d' : groupCohomology.cocycles₁ A')
    (hd : ∀ r, d.1 r = S (c.1 (ψ r))) (hd' : ∀ r, d'.1 r = S' (c'.1 (ψ r))) :
    PhiC A A' e d d' = (radDet ψ : ℂ) * PhiC A A' e c c' := by
  have hcc := (groupCohomology.mem_cocycles₁_iff c.1).1 c.2
  have hcc' := (groupCohomology.mem_cocycles₁_iff c'.1).1 c'.2
  have step : ∀ u v : RadicalLattice,
      e (d.1 u) (A'.ρ u (d'.1 v)) = e (c.1 (ψ u)) (A'.ρ (ψ u) (c'.1 (ψ v))) := by
    intro u v
    rw [hd, hd', hS', hSe]
  have h1 : PhiC A A' e d d' = altForm A'.ρ e c.1 c'.1 (ψ rl1) (ψ rl2) := by
    rw [PhiC_apply, step, step]
    rfl
  have hp : ψ rl1 = rl1 ^ (ψ rl1).toAdd.1 * rl2 ^ (ψ rl1).toAdd.2 := rl_decomp _
  have hq : ψ rl2 = rl1 ^ (ψ rl2).toAdd.1 * rl2 ^ (ψ rl2).toAdd.2 := rl_decomp _
  have key := altForm_gen he hcc hcc' rl1 rl2 (ψ rl1).toAdd.1 (ψ rl1).toAdd.2 (ψ rl2).toAdd.1 (ψ rl2).toAdd.2
  rw [← hp, ← hq] at key
  rw [h1, key]
  simp only [radDet]
  push_cast
  rfl

end Pullback

section Levi

/-- A perfect `G`-invariant pairing between two modules. -/
structure PerfectInv {G : Type} [Group G] {V W : Rep ℂ G} (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) : Prop where
  inv : ∀ g a b, e (V.ρ g a) (W.ρ g b) = e a b
  left : ∀ a, (∀ b, e a b = 0) → a = 0
  right : ∀ b, (∀ a, e a b = 0) → b = 0

variable {E L : Type} [Group E] [Group L] {ext : GroupExtension RadicalLattice E L}
  {rep rep' : Rep ℂ E} {e : rep →ₗ[ℂ] rep' →ₗ[ℂ] ℂ}

instance resFD (f : RadicalLattice →* E) (V : Rep ℂ E) [FiniteDimensional ℂ V] :
    FiniteDimensional ℂ (Rep.res f V) := inferInstanceAs (FiniteDimensional ℂ V)

/-- **The Koszul pairing `H¹(N_R, E) × H¹(N_R, E') → ℂ`** of the radical lattice of a split extension. -/
def radPairingOf (hp : PerfectInv e) [FiniteDimensional ℂ rep] [FiniteDimensional ℂ rep'] :
    groupCohomology.H1 (Rep.res ext.inl rep) →ₗ[ℂ] groupCohomology.H1 (Rep.res ext.inl rep') →ₗ[ℂ] ℂ :=
  Classical.choose (exists_radPairing (A := Rep.res ext.inl rep) (A' := Rep.res ext.inl rep') (e := e)
    (fun r a b => hp.inv (ext.inl r) a b) hp.left hp.right)

theorem radPairingOf_spec (hp : PerfectInv e) [FiniteDimensional ℂ rep] [FiniteDimensional ℂ rep']
    (c : groupCohomology.cocycles₁ (Rep.res ext.inl rep)) (c' : groupCohomology.cocycles₁ (Rep.res ext.inl rep')) :
    radPairingOf (ext := ext) hp (groupCohomology.H1π _ c) (groupCohomology.H1π _ c') =
      PhiC (Rep.res ext.inl rep) (Rep.res ext.inl rep') e c c' :=
  (Classical.choose_spec (exists_radPairing (A := Rep.res ext.inl rep) (A' := Rep.res ext.inl rep') (e := e)
    (fun r a b => hp.inv (ext.inl r) a b) hp.left hp.right)).1 c c'

theorem radPairingOf_left (hp : PerfectInv e) [FiniteDimensional ℂ rep] [FiniteDimensional ℂ rep']
    (x : groupCohomology.H1 (Rep.res ext.inl rep)) (h : ∀ y, radPairingOf (ext := ext) hp x y = 0) : x = 0 :=
  (Classical.choose_spec (exists_radPairing (A := Rep.res ext.inl rep) (A' := Rep.res ext.inl rep') (e := e)
    (fun r a b => hp.inv (ext.inl r) a b) hp.left hp.right)).2.1 x h

theorem radPairingOf_right (hp : PerfectInv e) [FiniteDimensional ℂ rep] [FiniteDimensional ℂ rep']
    (y : groupCohomology.H1 (Rep.res ext.inl rep')) (h : ∀ x, radPairingOf (ext := ext) hp x y = 0) : y = 0 :=
  (Classical.choose_spec (exists_radPairing (A := Rep.res ext.inl rep) (A' := Rep.res ext.inl rep') (e := e)
    (fun r a b => hp.inv (ext.inl r) a b) hp.left hp.right)).2.2 y h

/-- **Levi invariance of the radical Koszul pairing**: if `m ∈ L` acts on the radical lattice with determinant one, the
pairing is invariant under `splitRadicalH1Action m` on both factors. -/
theorem radPairingOf_levi (hp : PerfectInv e) [FiniteDimensional ℂ rep] [FiniteDimensional ℂ rep']
    (s : ext.Splitting) (m : L) (hdet : radDet (splitRadicalInput s m) = 1)
    (x : groupCohomology.H1 (Rep.res ext.inl rep)) (y : groupCohomology.H1 (Rep.res ext.inl rep')) :
    radPairingOf (ext := ext) hp (splitRadicalH1Action s rep m x) (splitRadicalH1Action s rep' m y) =
      radPairingOf (ext := ext) hp x y := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    induction y using groupCohomology.H1_induction_on with
    | h c' =>
      rw [splitRadicalH1Action_apply, splitRadicalH1Action_apply, radPairingOf_spec, radPairingOf_spec]
      have := PhiC_pullback (A := Rep.res ext.inl rep) (A' := Rep.res ext.inl rep') (e := e)
        (fun r a b => hp.inv (ext.inl r) a b) (splitRadicalInput s m) (rep.ρ (s m)) (rep'.ρ (s m))
        (fun r b => by
          have := splitRadicalCoefficient_intertwines s rep' m r
          exact congrArg (fun f => f b) this)
        (fun a b => hp.inv (s m) a b) c (splitRadicalCocycleAction s rep m c) c' (splitRadicalCocycleAction s rep' m c')
        (fun r => splitRadicalCocycleAction_apply s rep m c r) (fun r => splitRadicalCocycleAction_apply s rep' m c' r)
      rw [this, hdet]
      simp

end Levi

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
