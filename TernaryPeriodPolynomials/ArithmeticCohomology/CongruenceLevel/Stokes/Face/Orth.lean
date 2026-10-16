module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrthCoef

@[expose] public section


/-!
# Orthogonality and decomposition of the face pairings along equivariant idempotents

Formalized by Claude Sonnet 5.5.

For `ρ` a representation of `Γ(6) ⊂ SL₃(ℤ)` and `S` the group of a line (plane) face, `S`-equivariant endomorphisms `e₁`, `e₂` of the coefficient module with `e₂ e₁ = 0` act on mixed classes
(`h2E`) and the face pairings of `h2E e₁ x` and `h2E e₂ᵀ y` vanish (`lineFacePairM_orth`, `planeFacePairM_orth`); if moreover `e₁ + e₂ = id`, `e₁ e₂ = 0`, the face pairing is the sum of the two
diagonal terms (`lineFacePairM_decomp`, `planeFacePairM_decomp`).  Proof: pointwise application of the label-dependent conjugates `ρ(γ) e ρ(γ)⁻¹` to the lifts (`LineDatum.act`) and adjointness of the
cone pairing (`conePairC_lineCone_act`).
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section LineOrth

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem cmpH2_h2E (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNQAt 6 i.rep) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e v))
    (he' : ∀ (t : gammaNQAt 6 i.rep) (v : V), e (rep6 ρ (lineEmb i.rep t) v) = rep6 ρ (lineEmb i.rep t) (e v))
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ))) :
    cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp))
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e (fun k v => he k v) x) =
      h2E (Rep.res (lineEmb i.rep) (Rep.of (rep6 ρ))) e (fun k v => he' k v)
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective _ x
  unfold cmpH2 h2E
  erw [EdgeNat.h2Map_π, EdgeNat.h2Map_π, EdgeNat.h2Map_π, EdgeNat.h2Map_π]
  congr 1

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem cmpH2Dual_h2E (e : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V)
    (he : ∀ (t : gammaNQAt 6 i.rep) (v : Module.Dual ℂ V), e (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e v))
    (he' : ∀ (t : gammaNQAt 6 i.rep) (v : Module.Dual ℂ V), e ((rep6 ρ).dual (lineEmb i.rep t) v) = (rep6 ρ).dual (lineEmb i.rep t) (e v))
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual))) :
    cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp))
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) e (fun k v => he k v) x) =
      h2E (Rep.res (lineEmb i.rep) (Rep.of (rep6 ρ).dual)) e (fun k v => he' k v)
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective _ x
  unfold cmpH2Dual h2E
  erw [EdgeNat.h2Map_π, EdgeNat.h2Map_π, EdgeNat.h2Map_π, EdgeNat.h2Map_π]
  congr 1

end LineOrth

section LineOrthFinal

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6)

/-- The conjugated endomorphism for the line face `i`. -/
abbrev lineEConj {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ Γ6 W) (e : W →ₗ[ℂ] W) : W →ₗ[ℂ] W :=
  eConj (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem σ i e

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineHe' (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNQAt 6 i.rep) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e v)) (t : gammaNQAt 6 i.rep) (v : V) :
    e (rep6 ρ (lineEmb i.rep t) v) = rep6 ρ (lineEmb i.rep t) (e v) := by
  change e (ρ (gammaSixEquiv.symm (gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t))) v) =
    ρ (gammaSixEquiv.symm (gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t))) (e v)
  rw [MulEquiv.symm_apply_apply]
  exact he t v

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineHeD' (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNQAt 6 i.rep) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e v)) (t : gammaNQAt 6 i.rep)
    (f : Module.Dual ℂ V) :
    e.dualMap ((rep6 ρ).dual (lineEmb i.rep t) f) = (rep6 ρ).dual (lineEmb i.rep t) (e.dualMap f) := by
  apply LinearMap.ext
  intro v
  change f (rep6 ρ (lineEmb i.rep t)⁻¹ (e v)) = f (e (rep6 ρ (lineEmb i.rep t)⁻¹ v))
  have := lineHe' ρ i e he t⁻¹ v
  rw [← map_inv (lineEmb i.rep) t, ← this]

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineHeD (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNQAt 6 i.rep) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e v)) (t : gammaNQAt 6 i.rep)
    (f : Module.Dual ℂ V) :
    e.dualMap (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) f) =
      ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e.dualMap f) := by
  apply LinearMap.ext
  intro v
  change f (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t)⁻¹ (e v)) =
    f (e (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t)⁻¹ v))
  have := he t⁻¹ v
  rw [map_inv (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) t] at this
  rw [this]

end LineOrthFinal

section OrthMain

theorem stabEnd_congr {W : Rep.{0} ℚ Γ6} (S : Subgroup Γ6) {e e' : W →ₗ[ℚ] W} (h : e = e')
    (he : ∀ (g : S) (v : W), e (W.ρ g v) = W.ρ g (e v)) (he' : ∀ (g : S) (v : W), e' (W.ρ g v) = W.ρ g (e' v)) :
    stabEnd S e he = stabEnd S e' he' := by
  subst h
  rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (σ : Representation ℂ Γ6 V) {Z : Type} [MulAction Γ6 Z] (z₀ : Z)

theorem famC_base (e : V →ₗ[ℂ] V) (he : ∀ (s : Γ6), s • z₀ = z₀ → ∀ v, e (σ s v) = σ s (e v)) :
    (famC σ z₀ e he).P z₀ = e.restrictScalars ℚ := by
  have := famOfStab_apply (W := qRep (MonoidHom.id Γ6) σ) z₀ (e.restrictScalars ℚ) (fun s hs v => he s hs v) 1
  rw [one_smul] at this
  change (famOfStab (W := qRep (MonoidHom.id Γ6) σ) z₀ (e.restrictScalars ℚ) _).P z₀ = _
  rw [this]
  apply LinearMap.ext
  intro v
  change (σ 1) (e ((σ 1⁻¹) v)) = e v
  rw [inv_one, map_one]
  rfl

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem famCD_base (e : V →ₗ[ℂ] V) (he : ∀ (s : Γ6), s • z₀ = z₀ → ∀ v, e (σ s v) = σ s (e v)) :
    (famCD σ z₀ e he).P z₀ = e.dualMap.restrictScalars ℚ := by
  have := famOfStab_apply (W := qRep (MonoidHom.id Γ6) σ.dual) z₀ (e.dualMap.restrictScalars ℚ)
    (fun s hs f => dual_equiv σ z₀ e he s hs f) 1
  rw [one_smul] at this
  change (famOfStab (W := qRep (MonoidHom.id Γ6) σ.dual) z₀ (e.dualMap.restrictScalars ℚ) _).P z₀ = _
  rw [this]
  apply LinearMap.ext
  intro v
  change (σ.dual 1) (e.dualMap ((σ.dual 1⁻¹) v)) = e.dualMap v
  rw [inv_one, map_one]
  rfl

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem famCD_famC_comp_zero (e₁ : V →ₗ[ℂ] V) (he₁ : ∀ (s : Γ6), s • z₀ = z₀ → ∀ v, e₁ (σ s v) = σ s (e₁ v))
    (e₂c : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V)
    (he₂c : ∀ (s : Γ6), s • z₀ = z₀ → ∀ f, e₂c (σ.dual s f) = σ.dual s (e₂c f))
    (h : ∀ g, e₁.dualMap (e₂c g) = 0) (z : Z) (f : qRep (MonoidHom.id Γ6) σ.dual) :
    (famCD σ z₀ e₁ he₁).P z ((famC σ.dual z₀ e₂c he₂c).P z f) = 0 := by
  by_cases hz : ∃ γ : Γ6, γ • z₀ = z
  · obtain ⟨γ, rfl⟩ := hz
    have h1 : (famCD σ z₀ e₁ he₁).P (γ • z₀) =
        (qRep (MonoidHom.id Γ6) σ.dual).ρ γ ∘ₗ e₁.dualMap.restrictScalars ℚ ∘ₗ (qRep (MonoidHom.id Γ6) σ.dual).ρ γ⁻¹ :=
      famOfStab_apply (W := qRep (MonoidHom.id Γ6) σ.dual) z₀ (e₁.dualMap.restrictScalars ℚ)
        (fun s hs f => dual_equiv σ z₀ e₁ he₁ s hs f) γ
    have h2 : (famC σ.dual z₀ e₂c he₂c).P (γ • z₀) =
        (qRep (MonoidHom.id Γ6) σ.dual).ρ γ ∘ₗ e₂c.restrictScalars ℚ ∘ₗ (qRep (MonoidHom.id Γ6) σ.dual).ρ γ⁻¹ :=
      famOfStab_apply (W := qRep (MonoidHom.id Γ6) σ.dual) z₀ (e₂c.restrictScalars ℚ) (fun s hs f => he₂c s hs f) γ
    rw [h2, h1]
    change (σ.dual γ) (e₁.dualMap ((σ.dual γ⁻¹) ((σ.dual γ) (e₂c ((σ.dual γ⁻¹) f))))) = 0
    rw [← Module.End.mul_apply (σ.dual γ⁻¹) (σ.dual γ), ← map_mul, inv_mul_cancel, map_one]
    change (σ.dual γ) (e₁.dualMap (e₂c ((σ.dual γ⁻¹) f))) = 0
    rw [h, map_zero]
  · have h2 : (famC σ.dual z₀ e₂c he₂c).P z = 0 :=
      famOfStab_not_mem (W := qRep (MonoidHom.id Γ6) σ.dual) z₀ (e₂c.restrictScalars ℚ) (fun s hs f => he₂c s hs f) z hz
    rw [h2]
    exact map_zero _

end OrthMain

section LineOrthThm

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineEConj_dual_comp (e₁ e₂ : V →ₗ[ℂ] V) (h₂₁ : ∀ v, e₂ (e₁ v) = 0) (g : Module.Dual ℂ V) :
    (lineEConj i (rep6 ρ) e₁).dualMap (lineEConj i (rep6 ρ).dual e₂.dualMap g) = 0 := by
  apply LinearMap.ext
  intro v
  set G := faceG (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem i with hG
  change g ((rep6 ρ) G⁻¹ (e₂ ((rep6 ρ) G⁻¹⁻¹ ((rep6 ρ) G⁻¹ (e₁ ((rep6 ρ) G v)))))) = 0
  rw [inv_inv, ← Module.End.mul_apply ((rep6 ρ) G) ((rep6 ρ) G⁻¹), ← map_mul, mul_inv_cancel, map_one]
  change g ((rep6 ρ) G⁻¹ (e₂ (e₁ ((rep6 ρ) G v)))) = 0
  rw [h₂₁, map_zero, map_zero]

theorem lineFacePairM_orth (e₁ e₂ : V →ₗ[ℂ] V)
    (h₁ : ∀ (t : gammaNQAt 6 i.rep) (v : V), e₁ (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e₁ v))
    (h₂ : ∀ (t : gammaNQAt 6 i.rep) (v : V), e₂ (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e₂ v))
    (h₂₁ : ∀ v, e₂ (e₁ v) = 0)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx : x ∈ lineMixedSub ρ i) (hy : y ∈ lineMixedSub ρ.dual i) :
    lineFacePairM ρ i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e₁ (fun k v => h₁ k v) x)
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) e₂.dualMap
        (fun k v => lineHeD ρ i e₂ h₂ k v) y) = 0 := by
  have he₁' := lineHe' ρ i e₁ h₁
  have he₂' := lineHeD' ρ i e₂ h₂
  have hc₁ : ∀ s : Γ6, s • (lineFacesEquivOrbits i).out = (lineFacesEquivOrbits i).out →
      ∀ v, lineEConj i (rep6 ρ) e₁ (rep6 ρ s v) = rep6 ρ s (lineEConj i (rep6 ρ) e₁ v) := fun s hs v =>
    eConj_commute (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
      (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
      (fun i => lineEmb_range i.rep) (rep6 ρ) i e₁ he₁' ⟨s, MulAction.mem_stabilizer_iff.2 hs⟩ v
  have hc₂ : ∀ s : Γ6, s • (lineFacesEquivOrbits i).out = (lineFacesEquivOrbits i).out →
      ∀ f, lineEConj i (rep6 ρ).dual e₂.dualMap ((rep6 ρ).dual s f) =
        (rep6 ρ).dual s (lineEConj i (rep6 ρ).dual e₂.dualMap f) := fun s hs f =>
    eConj_commute (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
      (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
      (fun i => lineEmb_range i.rep) (rep6 ρ).dual i e₂.dualMap he₂' ⟨s, MulAction.mem_stabilizer_iff.2 hs⟩ f
  set P₁ := famC (rep6 ρ) (lineFacesEquivOrbits i).out (lineEConj i (rep6 ρ) e₁) hc₁ with hP₁
  set P₁D := famCD (rep6 ρ) (lineFacesEquivOrbits i).out (lineEConj i (rep6 ρ) e₁) hc₁ with hP₁D
  set P₂D := famC (rep6 ρ).dual (lineFacesEquivOrbits i).out (lineEConj i (rep6 ρ).dual e₂.dualMap) hc₂ with hP₂D
  obtain ⟨d, e, hd, he, hdc, hec⟩ := lineFace_exists_lifts ρ i x y hx hy
  have hd' := LineDatum.act_isOn P₁ _ d hd
  have he' := LineDatum.act_isOn P₂D _ e he
  have hdc' : (d.act P₁).coord (lineFacesEquivOrbits i) = lineTau ρ i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e₁ (fun k v => h₁ k v) x) := by
    rw [LineDatum.act_coord, hdc]
    have hτ := faceTauQ_h2E (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
      (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
      (fun i => lineEmb_range i.rep) (rep6 ρ) i e₁ he₁'
      (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x)
    have hcmp := cmpH2_h2E ρ i e₁ h₁ he₁' x
    have hse := stabEnd_congr (stabilizer Γ6 (lineFacesEquivOrbits i).out) (famC_base (rep6 ρ) _ _ hc₁)
      (Fam.equiv_stab P₁ _ _ (fun g => g.2)) (fun g v => eConj_commute (fun i : LineFaces 6 => lineFacesEquivOrbits i)
        (fun i => lineOf i.rep) lineOf_rep_mem (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
        (fun i => lineEmb_injective i.rep) (fun i => lineEmb_range i.rep) (rep6 ρ) i e₁ he₁' g v)
    rw [hse]
    refine Eq.trans hτ.symm ?_
    unfold lineTau
    rw [hcmp]
  have hec' : (e.act P₂D).coord (lineFacesEquivOrbits i) = lineTauD ρ i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) e₂.dualMap
        (fun k v => lineHeD ρ i e₂ h₂ k v) y) := by
    rw [LineDatum.act_coord, hec]
    have hτ := faceTauQ_h2E (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
      (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
      (fun i => lineEmb_range i.rep) (rep6 ρ).dual i e₂.dualMap he₂'
      (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y)
    have hcmp := cmpH2Dual_h2E ρ i e₂.dualMap (fun k v => lineHeD ρ i e₂ h₂ k v) he₂' y
    have hse := stabEnd_congr (stabilizer Γ6 (lineFacesEquivOrbits i).out) (famC_base (rep6 ρ).dual _ _ hc₂)
      (Fam.equiv_stab P₂D _ _ (fun g => g.2)) (fun g v => eConj_commute (fun i : LineFaces 6 => lineFacesEquivOrbits i)
        (fun i => lineOf i.rep) lineOf_rep_mem (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep)
        (fun i => lineEmb_injective i.rep) (fun i => lineEmb_range i.rep) (rep6 ρ).dual i e₂.dualMap he₂' g v)
    rw [hse]
    refine Eq.trans hτ.symm ?_
    unfold lineTauD
    rw [hcmp]
  rw [lineFace_pair_eq_cone ρ i _ _ (d.act P₁) (e.act P₂D) hd' he' hdc' hec']
  exact conePairC_lineCone_orth (evalC (MonoidHom.id Γ6) (rep6 ρ)) stokesCycle P₁ P₁D P₂D
    (famC_adj (rep6 ρ) _ _ hc₁)
    (famCD_famC_comp_zero (rep6 ρ) _ _ hc₁ _ hc₂ (lineEConj_dual_comp ρ i e₁ e₂ h₂₁)) d e

end LineOrthThm

section LineDecomp

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- **A mixed class stays mixed under an `S`-equivariant coefficient endomorphism.** -/
theorem lineMixedSub_h2E (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNQAt 6 i.rep) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e v))
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (hx : x ∈ lineMixedSub ρ i) :
    h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e (fun k v => he k v) x ∈
      lineMixedSub ρ i := by
  refine (Submodule.mem_iInf _).2 (fun F => LinearMap.mem_ker.2 ?_)
  have h := restriction_h2E (lineFlagStab 6 i.rep F).subtype
    (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e (fun k v => he k v)
    (fun k v => he _ v) x
  refine h.trans ?_
  rw [lineMixedSub_apply ρ i x hx F, map_zero]

end LineDecomp

section LineDecomp2

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem lineMixedSub_h2E_dual (e : V →ₗ[ℂ] V)
    (h : ∀ (t : gammaNQAt 6 i.rep) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e v))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hy : y ∈ lineMixedSub ρ.dual i) :
    h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) e.dualMap
      (fun k v => lineHeD ρ i e h k v) y ∈ lineMixedSub ρ.dual i :=
  lineMixedSub_h2E ρ.dual i e.dualMap (fun k v => lineHeD ρ i e h k v) y hy

/-- **Decomposition of the face pairing along complementary orthogonal `S`-equivariant idempotents.** -/
theorem lineFacePairM_decomp (e₁ e₂ : V →ₗ[ℂ] V)
    (h₁ : ∀ (t : gammaNQAt 6 i.rep) (v : V), e₁ (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e₁ v))
    (h₂ : ∀ (t : gammaNQAt 6 i.rep) (v : V), e₂ (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e₂ v))
    (hsum : ∀ v, e₁ v + e₂ v = v) (h₁₂ : ∀ v, e₁ (e₂ v) = 0) (h₂₁ : ∀ v, e₂ (e₁ v) = 0)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx : x ∈ lineMixedSub ρ i) (hy : y ∈ lineMixedSub ρ.dual i) :
    lineFacePairM ρ i x y =
      lineFacePairM ρ i
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e₁ (fun k v => h₁ k v) x)
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) e₁.dualMap
          (fun k v => lineHeD ρ i e₁ h₁ k v) y) +
      lineFacePairM ρ i
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e₂ (fun k v => h₂ k v) x)
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) e₂.dualMap
          (fun k v => lineHeD ρ i e₂ h₂ k v) y) := by
  have hxs : x = h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e₁ (fun k v => h₁ k v) x +
      h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e₂ (fun k v => h₂ k v) x := by
    have h₁₂' : ∀ (t : gammaNQAt 6 i.rep) (v : V), (e₁ + e₂) (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
        ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) ((e₁ + e₂) v) := fun t v => by
      rw [LinearMap.add_apply, LinearMap.add_apply, h₁ t v, h₂ t v, map_add]
    rw [← h2E_add _ e₁ e₂ _ _ (fun k v => h₁₂' k v) x]
    rw [h2E_congr _ (e' := LinearMap.id) (LinearMap.ext (fun v => hsum v)) _ (fun k v => rfl)]
    exact (h2E_id _ _ x).symm
  have hys : y = h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) e₁.dualMap
        (fun k v => lineHeD ρ i e₁ h₁ k v) y +
      h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) e₂.dualMap
        (fun k v => lineHeD ρ i e₂ h₂ k v) y := by
    have h₁₂' : ∀ (t : gammaNQAt 6 i.rep) (f : Module.Dual ℂ V), (e₁.dualMap + e₂.dualMap) (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) f) =
        ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) ((e₁.dualMap + e₂.dualMap) f) := fun t f => by
      rw [LinearMap.add_apply, LinearMap.add_apply, lineHeD ρ i e₁ h₁ t f, lineHeD ρ i e₂ h₂ t f, map_add]
    rw [← h2E_add _ e₁.dualMap e₂.dualMap _ _ (fun k v => h₁₂' k v) y]
    rw [h2E_congr _ (e' := LinearMap.id) (LinearMap.ext (fun f => LinearMap.ext (fun v => by
      change f (e₁ v) + f (e₂ v) = f v
      rw [← map_add, hsum]))) _ (fun k v => rfl)]
    exact (h2E_id _ _ y).symm
  have hx1 := lineMixedSub_h2E ρ i e₁ h₁ x hx
  have hx2 := lineMixedSub_h2E ρ i e₂ h₂ x hx
  have hy1 := lineMixedSub_h2E_dual ρ i e₁ h₁ y hy
  have hy2 := lineMixedSub_h2E_dual ρ i e₂ h₂ y hy
  conv_lhs => rw [hxs, hys]
  rw [lineFacePairM_add_right ρ i _ _ _ (Submodule.add_mem _ hx1 hx2) hy1 hy2,
    lineFacePairM_add_left ρ i _ _ _ hx1 hx2 hy1, lineFacePairM_add_left ρ i _ _ _ hx1 hx2 hy2,
    lineFacePairM_orth ρ i e₁ e₂ h₁ h₂ h₂₁ x y hx hy, lineFacePairM_orth ρ i e₂ e₁ h₂ h₁ h₁₂ x y hx hy]
  abel

end LineDecomp2

section PlaneOrth

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem cmpH2_h2E_plane (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e v))
    (he' : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e (rep6 ρ (planeEmb (planeFaceRepr i) t) v) = rep6 ρ (planeEmb (planeFaceRepr i) t) (e v))
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ))) :
    cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp))
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) e (fun k v => he k v) x) =
      h2E (Rep.res (planeEmb (planeFaceRepr i)) (Rep.of (rep6 ρ))) e (fun k v => he' k v)
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective _ x
  unfold cmpH2 h2E
  erw [EdgeNat.h2Map_π, EdgeNat.h2Map_π, EdgeNat.h2Map_π, EdgeNat.h2Map_π]
  congr 1

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem cmpH2Dual_h2E_plane (e : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V)
    (he : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : Module.Dual ℂ V), e (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e v))
    (he' : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : Module.Dual ℂ V), e ((rep6 ρ).dual (planeEmb (planeFaceRepr i) t) v) = (rep6 ρ).dual (planeEmb (planeFaceRepr i) t) (e v))
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual))) :
    cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp))
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) e (fun k v => he k v) x) =
      h2E (Rep.res (planeEmb (planeFaceRepr i)) (Rep.of (rep6 ρ).dual)) e (fun k v => he' k v)
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective _ x
  unfold cmpH2Dual h2E
  erw [EdgeNat.h2Map_π, EdgeNat.h2Map_π, EdgeNat.h2Map_π, EdgeNat.h2Map_π]
  congr 1

end PlaneOrth

section PlaneOrthFinal

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6)

/-- The conjugated endomorphism for the line face `i`. -/
abbrev planeEConj {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ Γ6 W) (e : W →ₗ[ℂ] W) : W →ₗ[ℂ] W :=
  eConj (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem σ i e

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeHe' (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e v)) (t : gammaNPAt 6 (planeFaceRepr i)) (v : V) :
    e (rep6 ρ (planeEmb (planeFaceRepr i) t) v) = rep6 ρ (planeEmb (planeFaceRepr i) t) (e v) := by
  change e (ρ (gammaSixEquiv.symm (gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t))) v) =
    ρ (gammaSixEquiv.symm (gammaSixEquiv (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t))) (e v)
  rw [MulEquiv.symm_apply_apply]
  exact he t v

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeHeD' (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e v)) (t : gammaNPAt 6 (planeFaceRepr i))
    (f : Module.Dual ℂ V) :
    e.dualMap ((rep6 ρ).dual (planeEmb (planeFaceRepr i) t) f) = (rep6 ρ).dual (planeEmb (planeFaceRepr i) t) (e.dualMap f) := by
  apply LinearMap.ext
  intro v
  change f (rep6 ρ (planeEmb (planeFaceRepr i) t)⁻¹ (e v)) = f (e (rep6 ρ (planeEmb (planeFaceRepr i) t)⁻¹ v))
  have := planeHe' ρ i e he t⁻¹ v
  rw [← map_inv (planeEmb (planeFaceRepr i)) t, ← this]

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeHeD (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e v)) (t : gammaNPAt 6 (planeFaceRepr i))
    (f : Module.Dual ℂ V) :
    e.dualMap (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) f) =
      ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e.dualMap f) := by
  apply LinearMap.ext
  intro v
  change f (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t)⁻¹ (e v)) =
    f (e (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t)⁻¹ v))
  have := he t⁻¹ v
  rw [map_inv (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) t] at this
  rw [this]

end PlaneOrthFinal

section PlaneOrthThm

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeEConj_dual_comp (e₁ e₂ : V →ₗ[ℂ] V) (h₂₁ : ∀ v, e₂ (e₁ v) = 0) (g : Module.Dual ℂ V) :
    (planeEConj i (rep6 ρ) e₁).dualMap (planeEConj i (rep6 ρ).dual e₂.dualMap g) = 0 := by
  apply LinearMap.ext
  intro v
  set G := faceG (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem i with hG
  change g ((rep6 ρ) G⁻¹ (e₂ ((rep6 ρ) G⁻¹⁻¹ ((rep6 ρ) G⁻¹ (e₁ ((rep6 ρ) G v)))))) = 0
  rw [inv_inv, ← Module.End.mul_apply ((rep6 ρ) G) ((rep6 ρ) G⁻¹), ← map_mul, mul_inv_cancel, map_one]
  change g ((rep6 ρ) G⁻¹ (e₂ (e₁ ((rep6 ρ) G v)))) = 0
  rw [h₂₁, map_zero, map_zero]

theorem planeFacePairM_orth (e₁ e₂ : V →ₗ[ℂ] V)
    (h₁ : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e₁ (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e₁ v))
    (h₂ : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e₂ (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e₂ v))
    (h₂₁ : ∀ v, e₂ (e₁ v) = 0)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hx : x ∈ planeMixedSub ρ i) (hy : y ∈ planeMixedSub ρ.dual i) :
    planeFacePairM ρ i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) e₁ (fun k v => h₁ k v) x)
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) e₂.dualMap
        (fun k v => planeHeD ρ i e₂ h₂ k v) y) = 0 := by
  have he₁' := planeHe' ρ i e₁ h₁
  have he₂' := planeHeD' ρ i e₂ h₂
  have hc₁ : ∀ s : Γ6, s • (planeFacesEquivOrbits i).out = (planeFacesEquivOrbits i).out →
      ∀ v, planeEConj i (rep6 ρ) e₁ (rep6 ρ s v) = rep6 ρ s (planeEConj i (rep6 ρ) e₁ v) := fun s hs v =>
    eConj_commute (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
      (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
      (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i e₁ he₁' ⟨s, MulAction.mem_stabilizer_iff.2 hs⟩ v
  have hc₂ : ∀ s : Γ6, s • (planeFacesEquivOrbits i).out = (planeFacesEquivOrbits i).out →
      ∀ f, planeEConj i (rep6 ρ).dual e₂.dualMap ((rep6 ρ).dual s f) =
        (rep6 ρ).dual s (planeEConj i (rep6 ρ).dual e₂.dualMap f) := fun s hs f =>
    eConj_commute (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
      (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
      (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i e₂.dualMap he₂' ⟨s, MulAction.mem_stabilizer_iff.2 hs⟩ f
  set P₁ := famC (rep6 ρ) (planeFacesEquivOrbits i).out (planeEConj i (rep6 ρ) e₁) hc₁ with hP₁
  set P₁D := famCD (rep6 ρ) (planeFacesEquivOrbits i).out (planeEConj i (rep6 ρ) e₁) hc₁ with hP₁D
  set P₂D := famC (rep6 ρ).dual (planeFacesEquivOrbits i).out (planeEConj i (rep6 ρ).dual e₂.dualMap) hc₂ with hP₂D
  obtain ⟨d, e, hd, he, hdc, hec⟩ := planeFace_exists_lifts ρ i x y hx hy
  have hd' := PlaneDatum.act_isOn P₁ _ d hd
  have he' := PlaneDatum.act_isOn P₂D _ e he
  have hdc' : (d.act P₁).coord (planeFacesEquivOrbits i) = planeTau ρ i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) e₁ (fun k v => h₁ k v) x) := by
    rw [PlaneDatum.act_coord, hdc]
    have hτ := faceTauQ_h2E (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
      (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
      (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i e₁ he₁'
      (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x)
    have hcmp := cmpH2_h2E_plane ρ i e₁ h₁ he₁' x
    have hse := stabEnd_congr (stabilizer Γ6 (planeFacesEquivOrbits i).out) (famC_base (rep6 ρ) _ _ hc₁)
      (Fam.equiv_stab P₁ _ _ (fun g => g.2)) (fun g v => eConj_commute (fun i : PlaneFaces 6 => planeFacesEquivOrbits i)
        (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i))
        (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i e₁ he₁' g v)
    rw [hse]
    refine Eq.trans hτ.symm ?_
    unfold planeTau
    rw [hcmp]
  have hec' : (e.act P₂D).coord (planeFacesEquivOrbits i) = planeTauD ρ i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) e₂.dualMap
        (fun k v => planeHeD ρ i e₂ h₂ k v) y) := by
    rw [PlaneDatum.act_coord, hec]
    have hτ := faceTauQ_h2E (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
      (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
      (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i e₂.dualMap he₂'
      (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y)
    have hcmp := cmpH2Dual_h2E_plane ρ i e₂.dualMap (fun k v => planeHeD ρ i e₂ h₂ k v) he₂' y
    have hse := stabEnd_congr (stabilizer Γ6 (planeFacesEquivOrbits i).out) (famC_base (rep6 ρ).dual _ _ hc₂)
      (Fam.equiv_stab P₂D _ _ (fun g => g.2)) (fun g v => eConj_commute (fun i : PlaneFaces 6 => planeFacesEquivOrbits i)
        (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i))
        (fun i => planeEmb_injective (planeFaceRepr i)) (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i e₂.dualMap he₂' g v)
    rw [hse]
    refine Eq.trans hτ.symm ?_
    unfold planeTauD
    rw [hcmp]
  rw [planeFace_pair_eq_cone ρ i _ _ (d.act P₁) (e.act P₂D) hd' he' hdc' hec']
  exact conePairC_planeCone_orth (evalC (MonoidHom.id Γ6) (rep6 ρ)) stokesCycle P₁ P₁D P₂D
    (famC_adj (rep6 ρ) _ _ hc₁)
    (famCD_famC_comp_zero (rep6 ρ) _ _ hc₁ _ hc₂ (planeEConj_dual_comp ρ i e₁ e₂ h₂₁)) d e

end PlaneOrthThm

section PlaneDecomp

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- **A mixed class stays mixed under an `S`-equivariant coefficient endomorphism.** -/
theorem planeMixedSub_h2E (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e v))
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (hx : x ∈ planeMixedSub ρ i) :
    h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) e (fun k v => he k v) x ∈
      planeMixedSub ρ i := by
  refine (Submodule.mem_iInf _).2 (fun F => LinearMap.mem_ker.2 ?_)
  have h := restriction_h2E (faceFlagStab 6 (planeFaceRepr i) F).subtype
    (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) e (fun k v => he k v)
    (fun k v => he _ v) x
  refine h.trans ?_
  rw [planeMixedSub_apply ρ i x hx F, map_zero]

end PlaneDecomp

section PlaneDecomp2

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem planeMixedSub_h2E_dual (e : V →ₗ[ℂ] V)
    (h : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e v))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hy : y ∈ planeMixedSub ρ.dual i) :
    h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) e.dualMap
      (fun k v => planeHeD ρ i e h k v) y ∈ planeMixedSub ρ.dual i :=
  planeMixedSub_h2E ρ.dual i e.dualMap (fun k v => planeHeD ρ i e h k v) y hy

/-- **Decomposition of the face pairing along complementary orthogonal `S`-equivariant idempotents.** -/
theorem planeFacePairM_decomp (e₁ e₂ : V →ₗ[ℂ] V)
    (h₁ : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e₁ (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e₁ v))
    (h₂ : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e₂ (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e₂ v))
    (hsum : ∀ v, e₁ v + e₂ v = v) (h₁₂ : ∀ v, e₁ (e₂ v) = 0) (h₂₁ : ∀ v, e₂ (e₁ v) = 0)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hx : x ∈ planeMixedSub ρ i) (hy : y ∈ planeMixedSub ρ.dual i) :
    planeFacePairM ρ i x y =
      planeFacePairM ρ i
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) e₁ (fun k v => h₁ k v) x)
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) e₁.dualMap
          (fun k v => planeHeD ρ i e₁ h₁ k v) y) +
      planeFacePairM ρ i
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) e₂ (fun k v => h₂ k v) x)
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) e₂.dualMap
          (fun k v => planeHeD ρ i e₂ h₂ k v) y) := by
  have hxs : x = h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) e₁ (fun k v => h₁ k v) x +
      h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) e₂ (fun k v => h₂ k v) x := by
    have h₁₂' : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), (e₁ + e₂) (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
        ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) ((e₁ + e₂) v) := fun t v => by
      rw [LinearMap.add_apply, LinearMap.add_apply, h₁ t v, h₂ t v, map_add]
    rw [← h2E_add _ e₁ e₂ _ _ (fun k v => h₁₂' k v) x]
    rw [h2E_congr _ (e' := LinearMap.id) (LinearMap.ext (fun v => hsum v)) _ (fun k v => rfl)]
    exact (h2E_id _ _ x).symm
  have hys : y = h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) e₁.dualMap
        (fun k v => planeHeD ρ i e₁ h₁ k v) y +
      h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) e₂.dualMap
        (fun k v => planeHeD ρ i e₂ h₂ k v) y := by
    have h₁₂' : ∀ (t : gammaNPAt 6 (planeFaceRepr i)) (f : Module.Dual ℂ V), (e₁.dualMap + e₂.dualMap) (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) f) =
        ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) ((e₁.dualMap + e₂.dualMap) f) := fun t f => by
      rw [LinearMap.add_apply, LinearMap.add_apply, planeHeD ρ i e₁ h₁ t f, planeHeD ρ i e₂ h₂ t f, map_add]
    rw [← h2E_add _ e₁.dualMap e₂.dualMap _ _ (fun k v => h₁₂' k v) y]
    rw [h2E_congr _ (e' := LinearMap.id) (LinearMap.ext (fun f => LinearMap.ext (fun v => by
      change f (e₁ v) + f (e₂ v) = f v
      rw [← map_add, hsum]))) _ (fun k v => rfl)]
    exact (h2E_id _ _ y).symm
  have hx1 := planeMixedSub_h2E ρ i e₁ h₁ x hx
  have hx2 := planeMixedSub_h2E ρ i e₂ h₂ x hx
  have hy1 := planeMixedSub_h2E_dual ρ i e₁ h₁ y hy
  have hy2 := planeMixedSub_h2E_dual ρ i e₂ h₂ y hy
  conv_lhs => rw [hxs, hys]
  rw [planeFacePairM_add_right ρ i _ _ _ (Submodule.add_mem _ hx1 hx2) hy1 hy2,
    planeFacePairM_add_left ρ i _ _ _ hx1 hx2 hy1, planeFacePairM_add_left ρ i _ _ _ hx1 hx2 hy2,
    planeFacePairM_orth ρ i e₁ e₂ h₁ h₂ h₂₁ x y hx hy, planeFacePairM_orth ρ i e₂ e₁ h₂ h₁ h₁₂ x y hx hy]
  abel

end PlaneDecomp2

end TernaryPeriodPolynomials.Argument.GammaNStokes
