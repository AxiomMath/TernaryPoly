module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.FaceCan

@[expose] public section


/-!
# The canonical face pairing under an isometric comparison of coefficient modules over the same Levi group

Formalized by Claude Sonnet 5.5.

**`facePairingCan_iso`**: let `ext : ℤ² → S → Γ(N)` and `ext' : ℤ² → E₂ → Γ(N)` be split extensions with a homomorphism `α : E₂ → S` over the identity of `Γ(N)` and of `ℤ²`
(`α ∘ inl' = inl`, `α ∘ s' = s`), `W₁` an `S`-module, `W₂` an `E₂`-module and `T : W₁ → W₂`, `T' : W₁^* → W₂^*` equivariant maps with `⟨T a, T' b⟩ = ⟨a, b⟩`.  Then the canonical face pairing
of the cuspidal groups of the radical `H¹` is preserved, with the constant `1` (the case `M = N` of `cuspidal_pairing_phi`).  Instances: a group isomorphism `E₂ ≃ S` (transport of structure) and the
inclusion of an orbit component of an induced module (`T` the inclusion, `T'` the transpose of the projection).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open scoped Classical

variable {S E₂ : Type} [Group S] [Group E₂] {N : ℕ} {ext : GroupExtension RadicalLattice S (Gamma N)} {s : ext.Splitting}
  {ext' : GroupExtension RadicalLattice E₂ (Gamma N)} {s' : ext'.Splitting}
  (α : E₂ →* S) (hinl : ∀ r, α (ext'.inl r) = ext.inl r) (hsplit : ∀ m, α (s' m) = s m)
  {W₁ : Rep ℂ S} {W₂ : Rep ℂ E₂} (T : W₁ →ₗ[ℂ] W₂) (T' : dualRepG W₁ →ₗ[ℂ] dualRepG W₂)
  (hT : ∀ (g : E₂) (v : W₁), T (W₁.ρ (α g) v) = W₂.ρ g (T v))
  (hT' : ∀ (g : E₂) (f : dualRepG W₁), T' ((dualRepG W₁).ρ (α g) f) = (dualRepG W₂).ρ g (T' f))

/-- The comparison of the radical `H¹` modules. -/
def isoMor : Rep.res (Subgroup.inclusion (le_refl (Gamma N))) (splitRadicalH1Representation s W₁) ⟶
    splitRadicalH1Representation s' W₂ :=
  EdgeNat.modMor s s' α (Subgroup.inclusion (le_refl (Gamma N))) (MonoidHom.id RadicalLattice) hinl hsplit W₁ W₂ T hT

/-- The comparison of the radical `H¹` modules of the contragredients. -/
def isoMorD : Rep.res (Subgroup.inclusion (le_refl (Gamma N))) (splitRadicalH1Representation s (dualRepG W₁)) ⟶
    splitRadicalH1Representation s' (dualRepG W₂) :=
  EdgeNat.modMor s s' α (Subgroup.inclusion (le_refl (Gamma N))) (MonoidHom.id RadicalLattice) hinl hsplit (dualRepG W₁) (dualRepG W₂) T' hT'

section Rad

include hinl hT in
/-- The cocycle map of the radical `H¹` comparison. -/
def isoCoc : groupCohomology.cocycles₁ (Rep.res ext.inl W₁) →ₗ[ℂ] groupCohomology.cocycles₁ (Rep.res ext'.inl W₂) :=
  oneCocyclePullback (Rep.res ext.inl W₁) (Rep.res ext'.inl W₂) (MonoidHom.id RadicalLattice) T (by
    intro r
    apply LinearMap.ext
    intro v
    have h := hT (ext'.inl r) v
    rw [hinl] at h
    exact h.symm)

include hinl hT' in
/-- The cocycle map of the radical `H¹` comparison for the contragredients. -/
def isoCocD : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG W₁)) →ₗ[ℂ] groupCohomology.cocycles₁ (Rep.res ext'.inl (dualRepG W₂)) :=
  oneCocyclePullback (Rep.res ext.inl (dualRepG W₁)) (Rep.res ext'.inl (dualRepG W₂)) (MonoidHom.id RadicalLattice) T' (by
    intro r
    apply LinearMap.ext
    intro v
    have h := hT' (ext'.inl r) v
    rw [hinl] at h
    exact h.symm)

include hinl hsplit hT in
theorem isoMor_apply (c : groupCohomology.cocycles₁ (Rep.res ext.inl W₁)) :
    (isoMor α hinl hsplit T hT (s := s) (s' := s')).hom (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (isoCoc α hinl T hT c) := by
  unfold isoMor isoCoc EdgeNat.modMor EdgeNat.radH1Map oneCocyclePullbackMorphism
  exact oneCocyclePullbackH1_apply _ _ _ _ _ c

include hinl hsplit hT' in
theorem isoMorD_apply (c : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG W₁))) :
    (isoMorD α hinl hsplit T' hT' (s := s) (s' := s')).hom (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (isoCocD α hinl T' hT' c) := by
  unfold isoMorD isoCocD EdgeNat.modMor EdgeNat.radH1Map oneCocyclePullbackMorphism
  exact oneCocyclePullbackH1_apply _ _ _ _ _ c

variable (hiso : ∀ (a : W₁) (b : dualRepG W₁), T' b (T a) = b a)

include hinl hT hT' hiso in
theorem phiC_iso (c : groupCohomology.cocycles₁ (Rep.res ext.inl W₁))
    (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG W₁))) :
    PhiC (Rep.res ext'.inl W₂) (Rep.res ext'.inl (dualRepG W₂)) (Module.Dual.eval ℂ W₂)
        (isoCoc α hinl T hT c) (isoCocD α hinl T' hT' c') =
      PhiC (Rep.res ext.inl W₁) (Rep.res ext.inl (dualRepG W₁)) (Module.Dual.eval ℂ W₁) c c' := by
  have key : ∀ (r : RadicalLattice) (a : W₁) (f : dualRepG W₁),
      (Module.Dual.eval ℂ W₂) (T a) ((dualRepG W₂).ρ (ext'.inl r) (T' f)) =
        (Module.Dual.eval ℂ W₁) a ((dualRepG W₁).ρ (ext.inl r) f) := by
    intro r a f
    have h := hT' (ext'.inl r) f
    rw [hinl] at h
    change ((dualRepG W₂).ρ (ext'.inl r) (T' f)) (T a) = ((dualRepG W₁).ρ (ext.inl r) f) a
    rw [← h]
    exact hiso a _
  rw [PhiC_apply, PhiC_apply]
  exact congrArg₂ (· - ·) (key rl1 (c.1 rl1) (c'.1 rl2)) (key rl2 (c.1 rl2) (c'.1 rl1))

variable [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]

include hinl hsplit hT hT' hiso in
theorem radPairing_iso (a : groupCohomology.H1 (Rep.res ext.inl W₁)) (b : groupCohomology.H1 (Rep.res ext.inl (dualRepG W₁))) :
    radPairingOf (ext := ext') (perfectInv_dual W₂) ((isoMor α hinl hsplit T hT (s := s) (s' := s')).hom a)
        ((isoMorD α hinl hsplit T' hT' (s := s) (s' := s')).hom b) =
      radPairingOf (ext := ext) (perfectInv_dual W₁) a b := by
  induction a using groupCohomology.H1_induction_on with
  | h c =>
    induction b using groupCohomology.H1_induction_on with
    | h c' =>
      rw [isoMor_apply α hinl hsplit T hT, isoMorD_apply α hinl hsplit T' hT', radPairingOf_spec, radPairingOf_spec]
      exact phiC_iso α hinl T T' hT hT' hiso c c'

end Rad

end TernaryPeriodPolynomials.Argument.RadicalInduction
