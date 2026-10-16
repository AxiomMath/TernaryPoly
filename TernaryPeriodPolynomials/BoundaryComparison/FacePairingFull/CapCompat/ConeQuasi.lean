module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.Cone
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SuspensionQuasi
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.CofiberMap
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Biproduct

@[expose] public section


/-!
# A chain map of pushout cones that respects the three strata is a quasi-isomorphism

If `u : pushCone a b ⟶ pushCone a' b'` maps the `L`- and `P`-coordinates into the `L'`- and `P'`-coordinates through chain
maps `uL`, `uP` and induces `uA` on the shifted `A`-coordinate, with `uA`, `uL`, `uP` quasi-isomorphisms, then `u` is a
quasi-isomorphism (five lemma on the cone sequences `L ⊞ P ⟶ cone ⟶ ΣA`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open TernaryPoly.BoundaryFaceResolutionComparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]
  {A L P A' L' P' : ChainComplex (Rep.{0} ℚ Γ) ℕ} (a : A ⟶ L) (b : A ⟶ P) (a' : A' ⟶ L') (b' : A' ⟶ P')

open HomologicalComplex in
theorem pushCone_map_quasiIso (u : pushCone a b ⟶ pushCone a' b') (uA : A ⟶ A') (uL : L ⟶ L') (uP : P ⟶ P')
    [QuasiIso uA] [QuasiIso uL] [QuasiIso uP]
    (hL : ∀ n, coneIL a b n ≫ u.f n = uL.f n ≫ coneIL a' b' n)
    (hP : ∀ n, coneIP a b n ≫ u.f n = uP.f n ≫ coneIP a' b' n)
    (hA : ∀ n, coneIA a b n ≫ u.f (n+1) ≫ CofiberSequence.first (pushArrow a' b') n = uA.f n) :
    QuasiIso u := by
  let φ : CofiberSequence.shortComplex (pushArrow a b) ⟶ CofiberSequence.shortComplex (pushArrow a' b') :=
    { τ₁ := biprod.map uL uP
      τ₂ := u
      τ₃ := Suspension.map uA
      comm₁₂ := by
        apply HomologicalComplex.hom_ext
        intro n
        change (biprod.map uL uP).f n ≫ homotopyCofiber.inrX (pushArrow a' b') n =
          homotopyCofiber.inrX (pushArrow a b) n ≫ u.f n
        symm
        apply biprodX_ext_from
        · have h1 := congrArg (fun m => m.f n) (biprod.inl_map uL uP)
          have h2 : (biprod.inl : L ⟶ L ⊞ P).f n ≫ (biprod.map uL uP).f n = uL.f n ≫ (biprod.inl : L' ⟶ L' ⊞ P').f n := h1
          have := hL n
          unfold coneIL at this
          simp only [← Category.assoc] at this ⊢
          rw [this, h2]
        · have h1 := congrArg (fun m => m.f n) (biprod.inr_map uL uP)
          have h2 : (biprod.inr : P ⟶ L ⊞ P).f n ≫ (biprod.map uL uP).f n = uP.f n ≫ (biprod.inr : P' ⟶ L' ⊞ P').f n := h1
          have := hP n
          unfold coneIP at this
          simp only [← Category.assoc] at this ⊢
          rw [this, h2]
      comm₂₃ := by
        apply HomologicalComplex.hom_ext
        intro n
        cases n with
        | zero => exact (isZero_zero _).eq_of_tgt _ _
        | succ n =>
          apply homotopyCofiber.ext_from_X (pushArrow a b) n (n+1) (down_rel_succ n)
          · change CofiberSequence.left (pushArrow a b) n ≫ (u.f (n+1) ≫ CofiberSequence.first (pushArrow a' b') n) =
              CofiberSequence.left (pushArrow a b) n ≫ (CofiberSequence.first (pushArrow a b) n ≫ uA.f n)
            refine (hA n).trans ?_
            rw [← Category.assoc, CofiberSequence.left_first, Category.id_comp]
          · change CofiberSequence.right (pushArrow a b) (n+1) ≫ (u.f (n+1) ≫ CofiberSequence.first (pushArrow a' b') n) =
              CofiberSequence.right (pushArrow a b) (n+1) ≫ (CofiberSequence.first (pushArrow a b) n ≫ uA.f n)
            have hr : homotopyCofiber.inrX (pushArrow a' b') (n+1) ≫ CofiberSequence.first (pushArrow a' b') n = 0 :=
              CofiberSequence.right_first (pushArrow a' b') n
            have hz : CofiberSequence.right (pushArrow a b) (n+1) ≫ u.f (n+1) ≫
                CofiberSequence.first (pushArrow a' b') n = 0 := by
              apply biprodX_ext_from
              · have h := hL (n+1)
                unfold coneIL at h
                change (biprod.inl : L ⟶ L ⊞ P).f (n+1) ≫ homotopyCofiber.inrX (pushArrow a b) (n+1) ≫
                  u.f (n+1) ≫ CofiberSequence.first (pushArrow a' b') n = _
                rw [reassoc_of% h, hr]
                simp
              · have h := hP (n+1)
                unfold coneIP at h
                change (biprod.inr : P ⟶ L ⊞ P).f (n+1) ≫ homotopyCofiber.inrX (pushArrow a b) (n+1) ≫
                  u.f (n+1) ≫ CofiberSequence.first (pushArrow a' b') n = _
                rw [reassoc_of% h, hr]
                simp
            rw [hz, ← Category.assoc, CofiberSequence.right_first, zero_comp] }
  have h1 : QuasiIso φ.τ₁ := biprodMap_quasiIso uL uP
  have h3 : QuasiIso φ.τ₃ := suspension_map_quasiIso uA
  exact middle_quasiIso φ (CofiberSequence.shortExact _) (CofiberSequence.shortExact _)

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
