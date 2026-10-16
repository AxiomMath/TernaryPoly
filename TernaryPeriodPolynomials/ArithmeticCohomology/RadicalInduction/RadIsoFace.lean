module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadIso
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.FaceCan

@[expose] public section


/-!
# The canonical face pairing under an isometric comparison: the pairing and the edges

Formalized by Claude Sonnet 5.5.

`facePairingCan_iso` and `facePairingCan_iso_edge`: see `RadIso`.  The constant is exactly `1` (the case `M = N` of `cuspidal_pairing_phi`).
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

instance (N : ℕ) : Subsingleton (Gamma N ⧸ subM N N) :=
  ⟨fun x y => by
    induction x using QuotientGroup.induction_on with
    | H g =>
      induction y using QuotientGroup.induction_on with
      | H h => exact QuotientGroup.eq.mpr (by simp [subM])⟩

section Face

variable [hN : Fact (3 ≤ N)] [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
  (hiso : ∀ (a : W₁) (b : dualRepG W₁), T' b (T a) = b a)
  (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (hdet' : ∀ A, radDet (splitRadicalInput s' A) = 1)

include hinl hsplit hT hT' hiso hdet hdet' in
/-- **The canonical face pairing under an isometric comparison of coefficient modules over the same Levi group, constant `1`.** -/
theorem facePairingCan_iso
    (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s W₁))
    (y : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG W₁))) :
    facePairingCan hN.out s hdet W₁ x y =
      facePairingCan hN.out s' hdet' W₂ (mapCusp hN.out (le_refl (Gamma N)) (isoMor α hinl hsplit T hT (s := s) (s' := s')) x)
        (mapCusp hN.out (le_refl (Gamma N)) (isoMorD α hinl hsplit T' hT' (s := s) (s' := s')) y) := by
  have : Fintype (Gamma N ⧸ subM N N) := Fintype.ofFinite _
  have : FiniteDimensional ℂ (splitRadicalH1Representation s W₁) := finiteDimensional_H1 (Rep.res ext.inl W₁)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG W₁)) := finiteDimensional_H1 (Rep.res ext.inl (dualRepG W₁))
  have : FiniteDimensional ℂ (splitRadicalH1Representation s' W₂) := finiteDimensional_H1 (Rep.res ext'.inl W₂)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s' (dualRepG W₂)) := finiteDimensional_H1 (Rep.res ext'.inl (dualRepG W₂))
  have h := cuspidal_pairing_phi (N := N) (M := N) hN.out (le_refl (Gamma N))
    (isoMor α hinl hsplit T hT (s := s) (s' := s')) (isoMorD α hinl hsplit T' hT' (s := s) (s' := s'))
    (radPairingOf (ext := ext) (perfectInv_dual W₁)) (radPairingOf (ext := ext') (perfectInv_dual W₂)) 1
    (fun γ a b => radPairingOf_levi (perfectInv_dual W₁) s γ (hdet γ) a b)
    (fun a ha => radPairingOf_left (perfectInv_dual W₁) a ha)
    (fun b hb => radPairingOf_right (perfectInv_dual W₁) b hb)
    (fun γ a b => radPairingOf_levi (perfectInv_dual W₂) s' γ (hdet' γ) a b)
    (fun a ha => radPairingOf_left (perfectInv_dual W₂) a ha)
    (fun b hb => radPairingOf_right (perfectInv_dual W₂) b hb)
    (fun a b => by
      rw [Fintype.sum_subsingleton _ ((1 : Gamma N) : Gamma N ⧸ subM N N), one_mul]
      have e1 := Rep.hom_comm_apply (isoMor α hinl hsplit T hT (s := s) (s' := s'))
        (Quotient.out ((1 : Gamma N) : Gamma N ⧸ subM N N))⁻¹ a
      have e2 := Rep.hom_comm_apply (isoMorD α hinl hsplit T' hT' (s := s) (s' := s'))
        (Quotient.out ((1 : Gamma N) : Gamma N ⧸ subM N N))⁻¹ b
      have step1 : radPairingOf (ext := ext') (perfectInv_dual W₂)
          ((isoMor α hinl hsplit T hT (s := s) (s' := s')).hom
            ((splitRadicalH1Representation s W₁).ρ (Quotient.out ((1 : Gamma N) : Gamma N ⧸ subM N N))⁻¹ a))
          ((isoMorD α hinl hsplit T' hT' (s := s) (s' := s')).hom
            ((splitRadicalH1Representation s (dualRepG W₁)).ρ (Quotient.out ((1 : Gamma N) : Gamma N ⧸ subM N N))⁻¹ b)) =
          radPairingOf (ext := ext') (perfectInv_dual W₂)
            ((splitRadicalH1Representation s' W₂).ρ (Quotient.out ((1 : Gamma N) : Gamma N ⧸ subM N N))⁻¹
              ((isoMor α hinl hsplit T hT (s := s) (s' := s')).hom a))
            ((splitRadicalH1Representation s' (dualRepG W₂)).ρ (Quotient.out ((1 : Gamma N) : Gamma N ⧸ subM N N))⁻¹
              ((isoMorD α hinl hsplit T' hT' (s := s) (s' := s')).hom b)) :=
        congrArg₂ (fun u v => radPairingOf (ext := ext') (perfectInv_dual W₂) u v) e1 e2
      exact (step1.trans ((radPairingOf_levi (perfectInv_dual W₂) s' _ (hdet' _) _ _).trans
        (radPairing_iso α hinl hsplit T T' hT hT' hiso a b))).symm)
    (facePairingCan hN.out s hdet W₁) (facePairingCan hN.out s' hdet' W₂)
    (isCupPairing_facePairingCan hN.out s hdet W₁) (isCupPairing_facePairingCan hN.out s' hdet' W₂) x y
  rw [one_mul] at h
  exact h

/-- The pull-back along `α` composed with `T`, on the classes with vanishing radical restriction. -/
def isoKer : (twoCohomologyRestriction ext.inl W₁).ker →ₗ[ℂ] (twoCohomologyRestriction ext'.inl W₂).ker :=
  EdgeNat.kerMap α (MonoidHom.id RadicalLattice) hinl W₁ W₂ T hT

/-- The same for the contragredients. -/
def isoKerD : (twoCohomologyRestriction ext.inl (dualRepG W₁)).ker →ₗ[ℂ] (twoCohomologyRestriction ext'.inl (dualRepG W₂)).ker :=
  EdgeNat.kerMap α (MonoidHom.id RadicalLattice) hinl (dualRepG W₁) (dualRepG W₂) T' hT'

omit hN [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂] in
include hsplit in
theorem isoMor_edge (z : (twoCohomologyRestriction ext.inl W₁).ker) :
    mapH1 (le_refl (Gamma N)) (isoMor α hinl hsplit T hT (s := s) (s' := s')) (splitCohomologyEdge s W₁ z) =
      splitCohomologyEdge s' W₂ (isoKer α hinl T hT z) :=
  (EdgeNat.edge_kerMap s s' α (Subgroup.inclusion (le_refl (Gamma N))) (MonoidHom.id RadicalLattice) hinl hsplit W₁ W₂ T hT z).symm

omit hN [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂] in
include hsplit in
theorem isoMorD_edge (z : (twoCohomologyRestriction ext.inl (dualRepG W₁)).ker) :
    mapH1 (le_refl (Gamma N)) (isoMorD α hinl hsplit T' hT' (s := s) (s' := s')) (splitCohomologyEdge s (dualRepG W₁) z) =
      splitCohomologyEdge s' (dualRepG W₂) (isoKerD α hinl T' hT' z) :=
  (EdgeNat.edge_kerMap s s' α (Subgroup.inclusion (le_refl (Gamma N))) (MonoidHom.id RadicalLattice) hinl hsplit (dualRepG W₁)
    (dualRepG W₂) T' hT' z).symm

omit [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂] in
include hsplit in
theorem isoKer_edge_mem (z : (twoCohomologyRestriction ext.inl W₁).ker)
    (hz : splitCohomologyEdge s W₁ z ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s W₁)) :
    splitCohomologyEdge s' W₂ (isoKer α hinl T hT z) ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s' W₂) := by
  rw [← isoMor_edge α hinl hsplit T hT (s := s) (s' := s')]
  exact mapH1_mem hN.out (le_refl (Gamma N)) _ ⟨_, hz⟩

omit [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂] in
include hsplit in
theorem isoKerD_edge_mem (z : (twoCohomologyRestriction ext.inl (dualRepG W₁)).ker)
    (hz : splitCohomologyEdge s (dualRepG W₁) z ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG W₁))) :
    splitCohomologyEdge s' (dualRepG W₂) (isoKerD α hinl T' hT' z) ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s' (dualRepG W₂)) := by
  rw [← isoMorD_edge α hinl hsplit T' hT' (s := s) (s' := s')]
  exact mapH1_mem hN.out (le_refl (Gamma N)) _ ⟨_, hz⟩

include hinl hsplit hT hT' hiso hdet hdet' in
/-- **The canonical face pairing of the edges under an isometric comparison, constant `1`.** -/
theorem facePairingCan_iso_edge
    (z : (twoCohomologyRestriction ext.inl W₁).ker) (z' : (twoCohomologyRestriction ext.inl (dualRepG W₁)).ker)
    (hz : splitCohomologyEdge s W₁ z ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s W₁))
    (hz' : splitCohomologyEdge s (dualRepG W₁) z' ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG W₁)))
    (h1 : splitCohomologyEdge s' W₂ (isoKer α hinl T hT z) ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s' W₂))
    (h2 : splitCohomologyEdge s' (dualRepG W₂) (isoKerD α hinl T' hT' z') ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s' (dualRepG W₂))) :
    facePairingCan hN.out s hdet W₁ ⟨splitCohomologyEdge s W₁ z, hz⟩ ⟨splitCohomologyEdge s (dualRepG W₁) z', hz'⟩ =
      facePairingCan hN.out s' hdet' W₂ ⟨splitCohomologyEdge s' W₂ (isoKer α hinl T hT z), h1⟩
        ⟨splitCohomologyEdge s' (dualRepG W₂) (isoKerD α hinl T' hT' z'), h2⟩ := by
  rw [facePairingCan_iso α hinl hsplit T T' hT hT' hiso hdet hdet' ⟨_, hz⟩ ⟨_, hz'⟩]
  have e1 : mapCusp hN.out (le_refl (Gamma N)) (isoMor α hinl hsplit T hT (s := s) (s' := s')) ⟨splitCohomologyEdge s W₁ z, hz⟩ =
      ⟨splitCohomologyEdge s' W₂ (isoKer α hinl T hT z), h1⟩ :=
    Subtype.ext (isoMor_edge α hinl hsplit T hT z)
  have e2 : mapCusp hN.out (le_refl (Gamma N)) (isoMorD α hinl hsplit T' hT' (s := s) (s' := s')) ⟨splitCohomologyEdge s (dualRepG W₁) z', hz'⟩ =
      ⟨splitCohomologyEdge s' (dualRepG W₂) (isoKerD α hinl T' hT' z'), h2⟩ :=
    Subtype.ext (isoMorD_edge α hinl hsplit T' hT' z')
  rw [e1, e2]

end Face

end TernaryPeriodPolynomials.Argument.RadicalInduction
