module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Dual
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Component
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.DualMixed

@[expose] public section


/-!
# The line pairing family from the Mackey transports

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section Part1

theorem eO_idem {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (Δ S : Subgroup G) (o : orbitRel.Quotient ↥S (G ⧸ Δ))
    (f : (G ⧸ Δ) → E) : eO Δ S o (eO Δ S o f) = eO Δ S o f := by
  change jL S (Quotient.out o : G ⧸ Δ) (qL S (Quotient.out o : G ⧸ Δ) (jL S (Quotient.out o : G ⧸ Δ) (qL S (Quotient.out o : G ⧸ Δ) f))) =
    jL S (Quotient.out o : G ⧸ Δ) (qL S (Quotient.out o : G ⧸ Δ) f)
  rw [qL_jL]

theorem res_h2Hom_eq {G H : Type} [Group G] [Group H] (ι : H →* G) {A B : Rep ℂ G} (f : A ⟶ B) (x : groupCohomology.H2 A) :
    twoCohomologyRestriction ι B (h2Hom f x) = h2Hom ((Rep.resFunctor ι).map f) (twoCohomologyRestriction ι A x) := by
  rw [twoCohomologyRestriction_eq_h2Map, h2Hom_eq_h2Map, twoCohomologyRestriction_eq_h2Map, h2Hom_eq_h2Map]
  have e1 := h2Map_comp (MonoidHom.id G) ι A B (Rep.res ι B) f.hom.toLinearMap (fun g v => Rep.hom_comm_apply f g v)
    LinearMap.id (fun _ _ => rfl) x
  have e2 := h2Map_comp ι (MonoidHom.id H) A (Rep.res ι A) (Rep.res ι B) LinearMap.id (fun _ _ => rfl)
    f.hom.toLinearMap (fun g v => Rep.hom_comm_apply f (ι g) v) x
  rw [e1]
  exact (h2Map_congr (by ext; rfl) _ _ _ _ (LinearMap.ext fun _ => rfl) x).trans e2.symm

end Part1

section Part2

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ S : Subgroup G) [Fintype (G ⧸ Δ)]

theorem h2E_dualPushG (o : orbitRel.Quotient ↥S (G ⧸ Δ))
    (hS : ∀ (k : ↥S) (v : Module.Dual ℂ ((G ⧸ Δ) → E)),
      (eO Δ S o).dualMap ((Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)).ρ k v) =
        (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)).ρ k ((eO Δ S o).dualMap v))
    (z : groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ.dual Δ)))) :
    h2E (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)) (eO Δ S o).dualMap hS (dualPushG ρ Δ S z) =
      dualPushG ρ Δ S (h2E (Rep.res S.subtype (Rep.of (permRep ρ.dual Δ))) (eO Δ S o)
        (fun k v => eO_equivariant ρ.dual Δ S o k v) z) := by
  have hcomm : ∀ φ : (G ⧸ Δ) → Module.Dual ℂ E,
      (dualRepHom ρ Δ).hom.toLinearMap (eO Δ S o φ) = (eO Δ S o).dualMap ((dualRepHom ρ Δ).hom.toLinearMap φ) := fun φ =>
    dualPair_idem Δ S (Quotient.out o) φ
  exact (h2Map_h2E (MonoidHom.id ↥S) (Rep.res S.subtype (Rep.of (permRep ρ.dual Δ)))
    (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)) (dualRepHom ρ Δ).hom.toLinearMap
    (fun g v => Rep.hom_comm_apply (dualRepHom ρ Δ) g.1 v)
    (eO Δ S o) (fun k v => eO_equivariant ρ.dual Δ S o k v)
    (eO Δ S o).dualMap hS hcomm z).symm

end Part2

section Part3

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') (n : ℕ)

theorem LineOver.termX_eq (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀) :
    (lineTermX c₀ hz cV hcV D.i D.o).1 =
      toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)))
        (D.thetaGen (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) (rLine M n i'.rep c₀)) := by
  have hS : ∀ (k : ↥(lineSub D.i)) (v : (↥(gammaN 6) ⧸ Δ6 M) → GeneralEisenstein.HomogeneousPoly n),
      eO (Δ6 M) (lineSub D.i) D.o ((Rep.res (lineSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M)))).ρ k v) =
        (Rep.res (lineSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M)))).ρ k (eO (Δ6 M) (lineSub D.i) D.o v) :=
    fun k v => eO_equivariant (rhoEn n) (Δ6 M) (lineSub D.i) D.o k v
  have h1 : (lineTermX c₀ hz cV hcV D.i D.o).1 =
      h2E (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)))) (eO (Δ6 M) (lineSub D.i) D.o)
        (fun k v => eO_line_equivariant (rhoEn n) (Δ6 M) D.i D.o k v)
        (toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)))
          (twoCohomologyRestriction (lineSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M))) cV)) := by
    rw [← toK_res]; rfl
  rw [h1, toK_h2E D.i (Rep.of (permRep (rhoEn n) (Δ6 M))) (eO (Δ6 M) (lineSub D.i) D.o) hS
    (fun k v => eO_line_equivariant (rhoEn n) (Δ6 M) D.i D.o k v)]
  congr 1
  exact D.comp_eq (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀ cV hcV

theorem LineOver.termY_eq (c₀' : groupCohomology.H2 (gammaNRepAllDual M n)) (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀')
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀') :
    (lineTermY c₀' hz' cVd hcVd D.i D.o).1 =
      toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)
        (dualPushG (rhoEn n) (Δ6 M) (lineSub D.i)
          (D.thetaGen (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
            (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M i'.rep hp)) (gammaNRepAllDual M n) c₀'))) := by
  have hS : ∀ (k : ↥(lineSub D.i)) (v : Module.Dual ℂ ((↥(gammaN 6) ⧸ Δ6 M) → GeneralEisenstein.HomogeneousPoly n)),
      (eO (Δ6 M) (lineSub D.i) D.o).dualMap ((Rep.res (lineSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)).ρ k v) =
        (Rep.res (lineSub D.i).subtype (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)).ρ k ((eO (Δ6 M) (lineSub D.i) D.o).dualMap v) :=
    fun k v => eO_dual_equivariant (rhoEn n) (Δ6 M) (lineSub D.i) D.o k v
  have h1 : (lineTermY c₀' hz' cVd hcVd D.i D.o).1 =
      h2E (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)) (eO (Δ6 M) (lineSub D.i) D.o).dualMap
        (fun k v => eO_dual_equivariantK D (rhoEn n) k v)
        (toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual)
          (dualPushG (rhoEn n) (Δ6 M) (lineSub D.i) (twoCohomologyRestriction (lineSub D.i).subtype (Rep.of (permRep (rhoEn n).dual (Δ6 M))) cVd))) := by
    have e := toK_res D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (h2Hom (dualRepHom (rhoEn n) (Δ6 M)) cVd)
    have e2 := res_h2Hom_eq (lineSub D.i).subtype (dualRepHom (rhoEn n) (Δ6 M)) cVd
    unfold lineTermY
    change h2E _ _ _ (twoCohomologyRestriction (lineIncl D.i) _ _) = _
    rw [e, e2]; rfl
  rw [h1, toK_h2E D.i (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (eO (Δ6 M) (lineSub D.i) D.o).dualMap hS
    (fun k v => eO_dual_equivariantK D (rhoEn n) k v), h2E_dualPushG (rhoEn n) (Δ6 M) (lineSub D.i) D.o hS]
  congr 2
  exact D.comp_eq (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀' cVd hcVd

end Part3

section Part4

variable {M : ℕ} [NeZero M] (n : ℕ)

theorem emb_flag_zero (h : SL(3, ℤ)) (ξ : lineFaceCuspidal M h n) (F'' : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (lineFlagStab M h F'').subtype (lineFaceRep M h n) (lineFaceCuspidalEmbedding M h n ξ) = 0 := by
  have hmem : lineFaceCuspidalEmbedding M h n ξ ∈ lineFaceCuspidalInH2 M h n := by
    rw [lineFaceCuspidalInH2_eq_range]; exact LinearMap.mem_range_self _ ξ
  rw [lineFaceCuspidalInH2_eq_locallyInner, lineLocallyInner_eq_iInf] at hmem
  exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hmem F'')

variable {i' : LineFaces M} (D : LineOver M i')

/-- The raw `E`-side transport `𝒞_{Q'}(E) → H²(K_i, Res V)`. -/
def LineOver.JEraw : lineFaceCuspidal M i'.rep n →ₗ[ℂ] groupCohomology.H2 (Rep.res (lineIncl D.i) (Rep.of (permRep (rhoEn n) (Δ6 M)))) :=
  (toK D.i (Rep.of (permRep (rhoEn n) (Δ6 M)))).comp
    ((D.thetaGen (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)).comp (lineFaceCuspidalEmbedding M i'.rep n))

theorem LineOver.JEraw_mem (ξ : lineFaceCuspidal M i'.rep n) :
    D.JEraw n ξ ∈ lineMixedSub (permRep (rhoEn n) (Δ6 M)) D.i :=
  (Submodule.mem_iInf _).2 fun F₀ => LinearMap.mem_ker.2
    (D.thetaGen_flag_zero (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) _ (emb_flag_zero n i'.rep ξ) F₀)

/-- **The `E`-side transport** `𝒞_{Q'}(E) → lineMixedSub V i`. -/
def LineOver.JE : lineFaceCuspidal M i'.rep n →ₗ[ℂ] lineMixedSub (permRep (rhoEn n) (Δ6 M)) D.i :=
  (D.JEraw n).codRestrict _ (D.JEraw_mem n)

theorem LineOver.JE_injective (h6 : 6 ∣ M) : Function.Injective (D.JE n) := by
  intro a b hab
  have h1 : D.JEraw n a = D.JEraw n b := congrArg Subtype.val hab
  have h2 := (toK_bijective D.i (Rep.of (permRep (rhoEn n) (Δ6 M)))).1 h1
  have h3 := D.thetaGen_injective (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) h6 h2
  exact lineFaceCuspidalEmbedding_injective M i'.rep n h3

end Part4

section Part5

theorem h2E_comp {K : Type} [Group K] (A : Rep ℂ K) (e₁ e₂ : A →ₗ[ℂ] A) (he₁ : ∀ k v, e₁ (A.ρ k v) = A.ρ k (e₁ v))
    (he₂ : ∀ k v, e₂ (A.ρ k v) = A.ρ k (e₂ v)) (he : ∀ k v, (e₁ ∘ₗ e₂) (A.ρ k v) = A.ρ k ((e₁ ∘ₗ e₂) v))
    (x : groupCohomology.H2 A) :
    h2E A e₁ he₁ (h2E A e₂ he₂ x) = h2E A (e₁ ∘ₗ e₂) he x := by
  unfold h2E
  rw [h2Map_comp]
  exact h2Map_congr (by ext; rfl) _ _ _ _ rfl x

theorem h2E_idem {K : Type} [Group K] (A : Rep ℂ K) (e : A →ₗ[ℂ] A) (he : ∀ k v, e (A.ρ k v) = A.ρ k (e v))
    (hidem : ∀ v, e (e v) = e v) (x : groupCohomology.H2 A) :
    h2E A e he (h2E A e he x) = h2E A e he x := by
  rw [h2E_comp A e e he he (fun k v => by rw [LinearMap.comp_apply, LinearMap.comp_apply, he k v, he k (e v)]) x]
  exact LinearMap.congr_fun (h2E_congr A (e := e ∘ₗ e) (e' := e) (LinearMap.ext fun v => hidem v) _ he) x

theorem dualPushG_inv {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ S : Subgroup G) [Fintype (G ⧸ Δ)]
    (z : groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ.dual Δ)))) :
    h2Hom ((Rep.resFunctor S.subtype).map (dualRepInv ρ Δ)) (dualPushG ρ Δ S z) = z := by
  unfold dualPushG
  rw [← h2Hom_comp, ← CategoryTheory.Functor.map_comp, dualRepHom_dualRepInv, CategoryTheory.Functor.map_id, h2Hom_id]

end Part5

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
