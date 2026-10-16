module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.RestrictRad
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FiniteH1

@[expose] public section


/-!
# Restriction of a face to a finite-index subface: edges and the canonical pairing

Formalized by Claude Sonnet 5.5.

`levTr`: the comparison of Levi modules `Res_{Γ(M)} H¹(N₁, W₁) → H¹(N₂, W₂)`; `edge_tr_class`: the Hochschild-Serre edge of the transported relative cocycle is the transport of the edge;
`facePairingCan_restrict`: `B_M(Ξ_* x, Ξ'_* y) = det(ψ) · [Γ(N):Γ(M)] · B_N(x, y)` for the canonical pairings (the Koszul scaling `radPairing_tr` and the `cuspidal_pairing_phi`).
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.RadicalInduction
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open scoped Classical

section Cusp

variable {N M : ℕ} (hle : Gamma M ≤ Gamma N) {E₁ E₂ : Type} [Group E₁] [Group E₂]
  {ext₁ : GroupExtension RadicalLattice E₁ (Gamma N)} {ext₂ : GroupExtension RadicalLattice E₂ (Gamma M)}
  (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (ι : E₂ →* E₁) (ψ : RadicalLattice →* RadicalLattice)
  (hinl : ∀ r, ι (ext₂.inl r) = ext₁.inl (ψ r)) (hsplit : ∀ l, ι (s₂ l) = s₁ (Subgroup.inclusion hle l))
  (W₁ : Rep ℂ E₁) (W₂ : Rep ℂ E₂) (T : W₁ →ₗ[ℂ] W₂) (hT : ∀ e v, T (W₁.ρ (ι e) v) = W₂.ρ e (T v))

/-- **The comparison of Levi modules**. -/
def levTr : Rep.res (Subgroup.inclusion hle) (splitRadicalH1Representation s₁ W₁) ⟶ splitRadicalH1Representation s₂ W₂ :=
  oneCocyclePullbackMorphism (splitRadicalH1Representation s₁ W₁) (splitRadicalH1Representation s₂ W₂)
    (Subgroup.inclusion hle) (radTr ι ψ W₁ W₂ T hT hinl)
    (fun m => LinearMap.ext fun x => (radTr_levi hle s₁ s₂ ι ψ hinl hsplit W₁ W₂ T hT m x).symm)

theorem levTr_apply (x : splitRadicalH1Representation s₁ W₁) :
    (levTr hle s₁ s₂ ι ψ hinl hsplit W₁ W₂ T hT).hom x = radTr ι ψ W₁ W₂ T hT hinl x := rfl

/-- The transported relative two-cocycle. -/
def trRel (z : relativeTwoCocycles ext₁.inl W₁) : relativeTwoCocycles ext₂.inl W₂ :=
  ⟨groupCohomology.mapCocycles₂ ι
    (oneCocyclePullbackMorphism W₁ W₂ ι T (fun e => LinearMap.ext fun v => (hT e v).symm)) z.val, by
    intro a b
    change T (z.val.1 (ι (ext₂.inl a), ι (ext₂.inl b))) = 0
    rw [hinl, hinl]
    exact (congrArg T (z.property (ψ a) (ψ b))).trans (map_zero T)⟩

theorem trRel_val (z : relativeTwoCocycles ext₁.inl W₁) (a b : E₂) :
    (trRel ι ψ hinl W₁ W₂ T hT z).val (a, b) = T (z.val (ι a, ι b)) := rfl

include hsplit in
/-- The edge cycle of the transported cocycle is the transport of the edge cycle. -/
theorem edgeCycle_tr (z : relativeTwoCocycles ext₁.inl W₁) (m : Gamma M) :
    splitEdgeCycle s₂ W₂ m (trRel ι ψ hinl W₁ W₂ T hT z) =
      oneCocyclePullback (Rep.res ext₁.inl W₁) (Rep.res ext₂.inl W₂) ψ T (radTr_inter ι ψ hinl W₁ W₂ T hT)
        (splitEdgeCycle s₁ W₁ (Subgroup.inclusion hle m) z) := by
  apply groupCohomology.cocycles₁_ext
  intro r
  rw [splitEdgeCycle_apply, oneCocyclePullback_apply, splitEdgeCycle_apply, trRel_val, trRel_val, hsplit, hinl, hinl,
    radInput_compat hle s₁ s₂ ι ψ hinl hsplit m r, map_sub]

include hsplit in
/-- **The Hochschild-Serre edge is natural for the restriction to the subface.** -/
theorem edge_tr_class (z : relativeTwoCocycles ext₁.inl W₁) :
    splitCohomologyEdge s₂ W₂ (relativeTwoCocycleClass ext₂.inl W₂ (trRel ι ψ hinl W₁ W₂ T hT z)) =
      mapH1 hle (levTr hle s₁ s₂ ι ψ hinl hsplit W₁ W₂ T hT)
        (splitCohomologyEdge s₁ W₁ (relativeTwoCocycleClass ext₁.inl W₁ z)) := by
  rw [splitCohomologyEdge_apply, splitCohomologyEdge_apply]
  change _ = oneCocyclePullbackH1 (splitRadicalH1Representation s₁ W₁) (splitRadicalH1Representation s₂ W₂)
    (Subgroup.inclusion hle) (radTr ι ψ W₁ W₂ T hT hinl) _ _
  refine Eq.trans ?_ (oneCocyclePullbackH1_apply _ _ _ _ _ _).symm
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro m
  change groupCohomology.H1π _ (splitEdgeCycle s₂ W₂ m (trRel ι ψ hinl W₁ W₂ T hT z)) =
    radTr ι ψ W₁ W₂ T hT hinl (groupCohomology.H1π _ (splitEdgeCycle s₁ W₁ (Subgroup.inclusion hle m) z))
  rw [radTr_π, edgeCycle_tr hle s₁ s₂ ι ψ hinl hsplit W₁ W₂ T hT z m]

section Pairing

variable [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) [Fintype (Gamma N ⧸ subM N M)] [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
  (T' : dualRepG W₁ →ₗ[ℂ] dualRepG W₂)
  (hT' : ∀ e v, T' ((dualRepG W₁).ρ (ι e) v) = (dualRepG W₂).ρ e (T' v)) (hSe : ∀ a b, T' b (T a) = b a)
  (hdet₁ : ∀ A, radDet (splitRadicalInput s₁ A) = 1) (hdet₂ : ∀ A, radDet (splitRadicalInput s₂ A) = 1)
  (hD : radDet ψ ≠ 0)

include hM hD hSe in
/-- **Restriction of the canonical face pairing to a finite-index subface**: `B_M(Ξ_* x, Ξ'_* y) = det(ψ) · [Γ(N):Γ(M)] · B_N(x, y)`. -/
theorem facePairingCan_restrict (xC : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s₁ W₁))
    (yC : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s₁ (dualRepG W₁))) :
    facePairingCan hM s₂ hdet₂ W₂ (mapCusp hM hle (levTr hle s₁ s₂ ι ψ hinl hsplit W₁ W₂ T hT) xC)
        (mapCusp hM hle (levTr hle s₁ s₂ ι ψ hinl hsplit (dualRepG W₁) (dualRepG W₂) T' hT') yC) =
      (radDet ψ : ℂ) * (Fintype.card (Gamma N ⧸ subM N M) : ℂ) * facePairingCan hN.out s₁ hdet₁ W₁ xC yC := by
  have fd1 : FiniteDimensional ℂ (splitRadicalH1Representation s₁ W₁) := finiteDimensional_H1 (Rep.res ext₁.inl W₁)
  have fd1' : FiniteDimensional ℂ (splitRadicalH1Representation s₁ (dualRepG W₁)) :=
    finiteDimensional_H1 (Rep.res ext₁.inl (dualRepG W₁))
  have fd2 : FiniteDimensional ℂ (splitRadicalH1Representation s₂ W₂) := finiteDimensional_H1 (Rep.res ext₂.inl W₂)
  have fd2' : FiniteDimensional ℂ (splitRadicalH1Representation s₂ (dualRepG W₂)) :=
    finiteDimensional_H1 (Rep.res ext₂.inl (dualRepG W₂))
  have hcard : (Fintype.card (Gamma N ⧸ subM N M) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hD' : (radDet ψ : ℂ) ≠ 0 := by exact_mod_cast hD
  have hBN := isCupPairing_facePairingCan hN.out s₁ hdet₁ W₁
  have hBM := isCupPairing_facePairingCan hM s₂ hdet₂ W₂
  have key := cuspidal_pairing_phi hM hle (levTr hle s₁ s₂ ι ψ hinl hsplit W₁ W₂ T hT)
    (levTr hle s₁ s₂ ι ψ hinl hsplit (dualRepG W₁) (dualRepG W₂) T' hT')
    (radPairingOf (ext := ext₁) (perfectInv_dual W₁)) (radPairingOf (ext := ext₂) (perfectInv_dual W₂))
    (((radDet ψ : ℂ) * (Fintype.card (Gamma N ⧸ subM N M) : ℂ))⁻¹)
    (fun γ x y => radPairingOf_levi (perfectInv_dual W₁) s₁ γ (hdet₁ γ) x y)
    (fun x hx => radPairingOf_left (perfectInv_dual W₁) x hx) (fun y hy => radPairingOf_right (perfectInv_dual W₁) y hy)
    (fun γ x y => radPairingOf_levi (perfectInv_dual W₂) s₂ γ (hdet₂ γ) x y)
    (fun x hx => radPairingOf_left (perfectInv_dual W₂) x hx) (fun y hy => radPairingOf_right (perfectInv_dual W₂) y hy)
    (fun a b => by
      have hx : ∀ u : Gamma N, radPairingOf (ext := ext₂) (perfectInv_dual W₂)
          ((levTr hle s₁ s₂ ι ψ hinl hsplit W₁ W₂ T hT).hom ((splitRadicalH1Representation s₁ W₁).ρ u⁻¹ a))
          ((levTr hle s₁ s₂ ι ψ hinl hsplit (dualRepG W₁) (dualRepG W₂) T' hT').hom
            ((splitRadicalH1Representation s₁ (dualRepG W₁)).ρ u⁻¹ b)) =
          (radDet ψ : ℂ) * radPairingOf (ext := ext₁) (perfectInv_dual W₁) a b := fun u => by
        rw [levTr_apply, levTr_apply]
        refine (radPairing_tr ι ψ hinl W₁ W₂ T hT T' hT' hSe ((splitRadicalH1Representation s₁ W₁).ρ u⁻¹ a)
          ((splitRadicalH1Representation s₁ (dualRepG W₁)).ρ u⁻¹ b)).trans ?_
        exact congrArg (fun t => (radDet ψ : ℂ) * t) (radPairingOf_levi (perfectInv_dual W₁) s₁ u⁻¹ (hdet₁ u⁻¹) a b)
      refine Eq.trans ?_ (congrArg (fun t => (((radDet ψ : ℂ) * (Fintype.card (Gamma N ⧸ subM N M) : ℂ))⁻¹) * t)
        (Finset.sum_congr rfl (fun (x : Gamma N ⧸ subM N M) _ => hx (Quotient.out x)))).symm
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      try rfl)
    (facePairingCan hN.out s₁ hdet₁ W₁) (facePairingCan hM s₂ hdet₂ W₂) hBN hBM xC yC
  rw [key]
  field_simp

end Pairing

end Cusp

end TernaryPeriodPolynomials.Argument.LevelDescent
