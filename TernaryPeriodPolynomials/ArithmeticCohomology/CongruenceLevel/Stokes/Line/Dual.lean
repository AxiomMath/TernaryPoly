module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.ThetaConv
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MixedEdgeBij

@[expose] public section


/-!
# The components of the induced module in the `S`-world: idempotent, injectivity and the dual component

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section SWorld

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ S : Subgroup G)

theorem eO_dual_equivariant (o : orbitRel.Quotient ↥S (G ⧸ Δ)) (k : ↥S) (f : Module.Dual ℂ ((G ⧸ Δ) → E)) :
    (eO Δ S o).dualMap ((permRep ρ Δ).dual k.1 f) = (permRep ρ Δ).dual k.1 ((eO Δ S o).dualMap f) := by
  apply LinearMap.ext
  intro v
  change f (permRep ρ Δ k.1⁻¹ (eO Δ S o v)) = f (eO Δ S o (permRep ρ Δ k.1⁻¹ v))
  have := eO_equivariant ρ Δ S o k⁻¹ v
  exact (congrArg f this).symm

/-- `e_O` acting on `H²(S, Res_S V)` is the composite of the orbit projection and the extension by zero. -/
theorem h2E_eO_eq (o : orbitRel.Quotient ↥S (G ⧸ Δ)) (x : G ⧸ Δ) (hx : x = Quotient.out o)
    (z : groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ Δ)))) :
    h2E (Rep.res S.subtype (Rep.of (permRep ρ Δ))) (eO Δ S o) (fun k v => eO_equivariant ρ Δ S o k v) z =
      h2Hom (jRep ρ S x) (h2Hom (qRep ρ S x) z) := by
  rw [← h2Hom_comp, h2Hom_eq_h2Map]
  unfold h2E
  refine h2Map_congr rfl _ _ _ _ ?_ _
  exact (eO_eq_qj Δ S o x hx).symm

end SWorld

section ThetaProps

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

omit [NeZero M] in
theorem LineOver.mu_bijective (h6 : 6 ∣ M) : Function.Bijective D.mu :=
  ⟨D.mu_injective, fun p => ⟨D.back h6 p, D.mu_back h6 p⟩⟩

omit [NeZero M] in
theorem LineOver.thetaGen_injective (h6 : 6 ∣ M) : Function.Injective (D.thetaGen ρ ρM hρ) := by
  intro a b hab
  have h1 : shapiroEquiv ρ (Δ6 M) (lineSub D.i) D.u (EdgeNat.h2Map D.mu (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
      (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ) a) =
      shapiroEquiv ρ (Δ6 M) (lineSub D.i) D.u (EdgeNat.h2Map D.mu (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
      (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ) b) := by
    have := congrArg (h2Hom (qRep ρ (lineSub D.i) (D.u : ↥(gammaN 6) ⧸ Δ6 M))) hab
    unfold LineOver.thetaGen Theta at this
    simp only [LinearMap.comp_apply] at this
    rwa [← h2Hom_comp, jRep_qRep, h2Hom_id, ← h2Hom_comp, jRep_qRep, h2Hom_id] at this
  have h2 := (shapiroEquiv ρ (Δ6 M) (lineSub D.i) D.u).injective h1
  have hid : Function.Bijective (ρ (D.u : ↥(gammaN 6))) := rho_bijective ρ _
  exact EdgeNat.h2Map_injective D.mu (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
    (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ) (D.mu_bijective h6) hid h2

omit [NeZero M] in
theorem LineOver.h2Map_mu_surjective (h6 : 6 ∣ M) :
    Function.Surjective (EdgeNat.h2Map D.mu (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
      (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)) :=
  EdgeNat.h2Map_surjective D.mu (lineW i' ρM) (Rep.of (rhoStab ρ (Δ6 M) (lineSub D.i) D.u))
    (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ) (D.mu_bijective h6) (rho_bijective ρ _)

end ThetaProps

section Components

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

omit [NeZero M] in
/-- **`Θ(ε)` lies in the `e_O`-component**, transported to the line group. -/
theorem LineOver.component_fixed (ε : groupCohomology.H2 (lineW i' ρM)) :
    h2E (Rep.res (lineIncl D.i) (Rep.of (permRep ρ (Δ6 M)))) (eO (Δ6 M) (lineSub D.i) D.o)
      (fun k v => eO_line_equivariant ρ (Δ6 M) D.i D.o k v)
      (toK D.i (Rep.of (permRep ρ (Δ6 M))) (D.thetaGen ρ ρM hρ ε)) =
    toK D.i (Rep.of (permRep ρ (Δ6 M))) (D.thetaGen ρ ρM hρ ε) := by
  rw [toK_h2E D.i (Rep.of (permRep ρ (Δ6 M))) (eO (Δ6 M) (lineSub D.i) D.o)
    (fun k v => eO_equivariant ρ (Δ6 M) (lineSub D.i) D.o k v) (fun k v => eO_line_equivariant ρ (Δ6 M) D.i D.o k v)]
  congr 1
  rw [h2E_eO_eq ρ (Δ6 M) (lineSub D.i) D.o (D.u : ↥(gammaN 6) ⧸ Δ6 M) D.hu]
  unfold LineOver.thetaGen Theta
  simp only [LinearMap.comp_apply]
  have key : ∀ c, h2Hom (qRep ρ (lineSub D.i) (D.u : ↥(gammaN 6) ⧸ Δ6 M)) (h2Hom (jRep ρ (lineSub D.i) (D.u : ↥(gammaN 6) ⧸ Δ6 M)) c) = c :=
    fun c => by rw [← h2Hom_comp, jRep_qRep, h2Hom_id]
  rw [key]

/-- The identification `Fun(G/Δ, E*) ≅ (Fun(G/Δ, E))*` on `H²(S, ·)`. -/
def dualPushS (i : LineFaces 6) : groupCohomology.H2 (Rep.res (lineSub i).subtype (Rep.of (permRep ρ.dual (Δ6 M)))) →ₗ[ℂ]
    groupCohomology.H2 (Rep.res (lineSub i).subtype (Rep.of (permRep ρ (Δ6 M)).dual)) :=
  h2Hom ((Rep.resFunctor (lineSub i).subtype).map (dualRepHom ρ (Δ6 M)))

end Components

section DualSurj

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E)

theorem shapiroEquiv_PhiH {G E' : Type} [Group G] [AddCommGroup E'] [Module ℂ E'] (ρ' : Representation ℂ G E') (Δ S : Subgroup G) (u : G)
    (w : groupCohomology.H2 (Rep.of (permRep (ρ'.comp S.subtype) (StabS Δ S u)))) :
    shapiroEquiv ρ' Δ S u (PhiH (ρ'.comp S.subtype) (StabS Δ S u) w) = w :=
  (LinearEquiv.ofBijective (PhiH (ρ'.comp S.subtype) (StabS Δ S u)) (PhiH_bijective (ρ'.comp S.subtype) (StabS Δ S u))).symm_apply_apply w

theorem dualPushS_pull (z : groupCohomology.H2 (Rep.res (lineSub D.i).subtype (Rep.of (permRep ρ (Δ6 M)).dual))) :
    dualPushS ρ (M := M) D.i (h2Hom ((Rep.resFunctor (lineSub D.i).subtype).map (dualRepInv ρ (Δ6 M))) z) = z := by
  unfold dualPushS
  rw [← h2Hom_comp, ← CategoryTheory.Functor.map_comp, dualRepInv_dualRepHom, CategoryTheory.Functor.map_id, h2Hom_id]

end DualSurj

section DualSurj2

/-- The identification `Fun(G/Δ, E*) ≅ (Fun(G/Δ, E))*` on `H²(S, Res_S ·)`, for a subgroup `S`. -/
def dualPushG {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ S : Subgroup G) [Fintype (G ⧸ Δ)] :
    groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ.dual Δ))) →ₗ[ℂ]
      groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)) :=
  h2Hom ((Rep.resFunctor S.subtype).map (dualRepHom ρ Δ))

section SDual

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ S : Subgroup G) [Fintype (G ⧸ Δ)]

theorem dualPushG_pull (z : groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual))) :
    dualPushG ρ Δ S (h2Hom ((Rep.resFunctor S.subtype).map (dualRepInv ρ Δ)) z) = z := by
  unfold dualPushG
  rw [← h2Hom_comp, ← CategoryTheory.Functor.map_comp, dualRepInv_dualRepHom, CategoryTheory.Functor.map_id, h2Hom_id]

/-- **The dual component in the `S`-world**. -/
theorem dual_component_S (o : orbitRel.Quotient ↥S (G ⧸ Δ)) (x : G ⧸ Δ) (hx : x = Quotient.out o)
    (yS : groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)))
    (hS : ∀ (k : ↥S) (v : Module.Dual ℂ ((G ⧸ Δ) → E)),
      (eO Δ S o).dualMap ((Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)).ρ k v) =
        (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)).ρ k ((eO Δ S o).dualMap v))
    (hyS : h2E (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)) (eO Δ S o).dualMap hS yS = yS) :
    ∃ z₀ : groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ.dual Δ))),
      yS = dualPushG ρ Δ S (h2Hom (jRep ρ.dual S x) (h2Hom (qRep ρ.dual S x) z₀)) := by
  set z₀ := h2Hom ((Rep.resFunctor S.subtype).map (dualRepInv ρ Δ)) yS with hz₀
  have hpush : dualPushG ρ Δ S z₀ = yS := dualPushG_pull ρ Δ S yS
  refine ⟨z₀, ?_⟩
  have hcomm : ∀ φ : (G ⧸ Δ) → Module.Dual ℂ E,
      (dualRepHom ρ Δ).hom.toLinearMap (eO Δ S o φ) = (eO Δ S o).dualMap ((dualRepHom ρ Δ).hom.toLinearMap φ) := fun φ => by
    subst hx
    exact dualPair_idem Δ S (Quotient.out o) φ
  have e1 := h2Map_h2E (MonoidHom.id ↥S) (Rep.res S.subtype (Rep.of (permRep ρ.dual Δ)))
    (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)) (dualRepHom ρ Δ).hom.toLinearMap
    (fun g v => Rep.hom_comm_apply (dualRepHom ρ Δ) g.1 v)
    (eO Δ S o) (fun k v => eO_equivariant ρ.dual Δ S o k v)
    (eO Δ S o).dualMap hS hcomm z₀
  rw [← h2E_eO_eq ρ.dual Δ S o x hx]
  calc yS = h2E (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)) (eO Δ S o).dualMap hS yS := hyS.symm
    _ = h2E (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)) (eO Δ S o).dualMap hS (dualPushG ρ Δ S z₀) := by rw [hpush]
    _ = dualPushG ρ Δ S (h2E (Rep.res S.subtype (Rep.of (permRep ρ.dual Δ))) (eO Δ S o) (fun k v => eO_equivariant ρ.dual Δ S o k v) z₀) :=
      e1.symm

end SDual

end DualSurj2

section DualSurj3

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρMd : Representation ℂ ↥(gammaN M) (Module.Dual ℂ E))
  (hρd : ∀ x : ↥(Δ6 M), ρMd (eΔ M x) = ρ.dual x.1)

omit [NeZero M] in
theorem eO_dual_equivariantK {i' : LineFaces M} (D : LineOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ ↥(gammaN 6) E) (k : ↥(gammaNQAt 6 D.i.rep)) (f : Module.Dual ℂ ((↥(gammaN 6) ⧸ Δ6 M) → E)) :
    (eO (Δ6 M) (lineSub D.i) D.o).dualMap ((Rep.res (lineIncl D.i) (Rep.of (permRep ρ (Δ6 M)).dual)).ρ k f) =
      (Rep.res (lineIncl D.i) (Rep.of (permRep ρ (Δ6 M)).dual)).ρ k ((eO (Δ6 M) (lineSub D.i) D.o).dualMap f) :=
  eO_dual_equivariant ρ (Δ6 M) (lineSub D.i) D.o ((lineSubEquiv D.i).symm k) f

omit [NeZero M] in
theorem LineOver.exists_theta_of_component (h6 : 6 ∣ M)
    (z₀ : groupCohomology.H2 (Rep.res (lineSub D.i).subtype (Rep.of (permRep ρ.dual (Δ6 M))))) :
    ∃ ε' : groupCohomology.H2 (lineW i' ρMd), D.thetaGen ρ.dual ρMd hρd ε' =
      h2Hom (jRep ρ.dual (lineSub D.i) (D.u : ↥(gammaN 6) ⧸ Δ6 M))
        (h2Hom (qRep ρ.dual (lineSub D.i) (D.u : ↥(gammaN 6) ⧸ Δ6 M)) z₀) := by
  obtain ⟨ε', hε'⟩ := LineOver.h2Map_mu_surjective D ρ.dual ρMd hρd h6
    (PhiH (ρ.dual.comp (lineSub D.i).subtype) (StabS (Δ6 M) (lineSub D.i) D.u)
      (h2Hom (qRep ρ.dual (lineSub D.i) (D.u : ↥(gammaN 6) ⧸ Δ6 M)) z₀))
  refine ⟨ε', ?_⟩
  unfold LineOver.thetaGen Theta
  simp only [LinearMap.comp_apply]
  rw [hε']
  exact congrArg (h2Hom (jRep ρ.dual (lineSub D.i) (D.u : ↥(gammaN 6) ⧸ Δ6 M))) (shapiroEquiv_PhiH ρ.dual (Δ6 M) (lineSub D.i) D.u _)

/-- **The dual component** (line group version). -/
theorem LineOver.dual_component_surj (h6 : 6 ∣ M)
    (y' : groupCohomology.H2 (Rep.res (lineIncl D.i) (Rep.of (permRep ρ (Δ6 M)).dual)))
    (hy' : h2E (Rep.res (lineIncl D.i) (Rep.of (permRep ρ (Δ6 M)).dual)) (eO (Δ6 M) (lineSub D.i) D.o).dualMap
      (fun k v => eO_dual_equivariantK D ρ k v) y' = y') :
    ∃ ε' : groupCohomology.H2 (lineW i' ρMd),
      y' = toK D.i (Rep.of (permRep ρ (Δ6 M)).dual) (dualPushG ρ (Δ6 M) (lineSub D.i) (D.thetaGen ρ.dual ρMd hρd ε')) := by
  obtain ⟨yS, rfl⟩ := (toK_bijective D.i (Rep.of (permRep ρ (Δ6 M)).dual)).2 y'
  have hS : ∀ (k : ↥(lineSub D.i)) (v : Module.Dual ℂ ((↥(gammaN 6) ⧸ Δ6 M) → E)),
      (eO (Δ6 M) (lineSub D.i) D.o).dualMap ((Rep.res (lineSub D.i).subtype (Rep.of (permRep ρ (Δ6 M)).dual)).ρ k v) =
        (Rep.res (lineSub D.i).subtype (Rep.of (permRep ρ (Δ6 M)).dual)).ρ k ((eO (Δ6 M) (lineSub D.i) D.o).dualMap v) :=
    fun k v => eO_dual_equivariant ρ (Δ6 M) (lineSub D.i) D.o k v
  have hyS : h2E (Rep.res (lineSub D.i).subtype (Rep.of (permRep ρ (Δ6 M)).dual)) (eO (Δ6 M) (lineSub D.i) D.o).dualMap hS yS = yS := by
    rw [toK_h2E D.i (Rep.of (permRep ρ (Δ6 M)).dual) (eO (Δ6 M) (lineSub D.i) D.o).dualMap hS
      (fun k v => eO_dual_equivariantK D ρ k v)] at hy'
    exact (toK_bijective D.i (Rep.of (permRep ρ (Δ6 M)).dual)).1 hy'
  obtain ⟨z₀, hz⟩ := dual_component_S ρ (Δ6 M) (lineSub D.i) D.o (D.u : ↥(gammaN 6) ⧸ Δ6 M) D.hu yS hS hyS
  obtain ⟨ε', hε'⟩ := D.exists_theta_of_component ρ ρMd hρd h6 z₀
  refine ⟨ε', ?_⟩
  rw [hε', ← hz]

end DualSurj3

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
