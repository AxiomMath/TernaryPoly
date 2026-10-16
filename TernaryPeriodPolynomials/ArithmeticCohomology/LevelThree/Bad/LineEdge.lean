module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineVectors

@[expose] public section


/-!
# The local `T_p` operator in edge coordinates at the bad line

For a two-cocycle `c` of the bad-line stabilizer `ΛB = {R(x, e, A)}` which vanishes on the radical
(`c (Ux a, Ux b) = 0`, "relative"), the Hecke image `T c` for the explicit cosets of `BadLineCosets` is
again relative (`heckeTwo_relative`), and its mixed (edge) cochain at the Levi element `Lm A` is

`edge (T c) A r = ∑_j ρ(ℓ_j) edge c (δ_j A) (r B_j) + ∑_d ρ(τ_d) ρ(Ux w_d) edge c A (z'_d A⁻¹)
  + (ρ(Ux r) Φ - Φ)`

(`edge_heckeTwo'`), where `edge c A r = c(Lm A, Ux (r A)) - c(Ux r, Lm A)` is the mixed cochain of
Sol's Hochschild–Serre map at the Levi element `(1, A)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineEdge

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets BadLineTransitions BadLineVectors AmbientHecke LocalHecke
open GoodLineCosets (cvec crep cq crep_shift_bijective ivmul_sub)

/-! ### Relative two-cocycles of `ΛB` -/

section Relative

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

/-- The coefficient representation of `ΛB`. -/
abbrev Aρ : Rep ℂ ΛB := subgroupCoefficientRep ΛB ρ

/-- `ρ(g)` on the coefficients of `ΛB`. -/
abbrev R1 (g : RationalGL3) : Module.End ℂ (Aρ ρ) := ρ g

theorem R1_mul (g h : RationalGL3) (v : Aρ ρ) : R1 ρ g (R1 ρ h v) = R1 ρ (g * h) v := by
  change ρ g (ρ h v) = ρ (g * h) v
  rw [map_mul]
  rfl

variable (c : groupCohomology.cocycles₂ (Aρ ρ))

/-- `F(A, x) = c(Ux x, Lm A)`. -/
def Fb (A : binaryArithmeticLevel) (x : ℤ × ℤ) : Aρ ρ := c (Ux x, Lm A)

/-- The mixed (edge) cochain `edge c A v = c(Lm A, Ux (v A)) - c(Ux v, Lm A)`. -/
def edgeB (A : binaryArithmeticLevel) (v : ℤ × ℤ) : Aρ ρ :=
  c (Lm A, Ux (ivmul v A.val.val)) - c (Ux v, Lm A)

variable (hrel : ∀ a b, c (Ux a, Ux b) = 0)

include hrel in
theorem relative_right (x z : ℤ × ℤ) (A : binaryArithmeticLevel) :
    c (Ux x, Mel z 1 A) = Fb ρ c A (x + z) - (Aρ ρ).ρ (Ux x) (Fb ρ c A z) := by
  have key := twoCocycle_relation (Aρ ρ) c (Ux x) (Ux z) (Lm A)
  rw [Ux_mul, hrel, add_zero, ← Mel_eq] at key
  unfold Fb
  rw [key]
  abel

include hrel in
theorem relative_left (x y : ℤ × ℤ) (A : binaryArithmeticLevel) :
    c (Mel x 1 A, Ux y) =
      (Aρ ρ).ρ (Ux x) (edgeB ρ c A (ivmul y (A.val⁻¹ : GL (Fin 2) ℤ).val)) +
        Fb ρ c A (x + ivmul y (A.val⁻¹ : GL (Fin 2) ℤ).val) - Fb ρ c A x := by
  have key := twoCocycle_relation (Aρ ρ) c (Ux x) (Lm A) (Ux y)
  rw [Lm_Ux, ← Mel_eq, ← Mel_eq, relative_right ρ c hrel] at key
  unfold edgeB
  rw [ivmul_cancel_inv, map_sub]
  unfold Fb at key ⊢
  have h : c (Mel x 1 A, Ux y) = (Aρ ρ).ρ (Ux x) (c (Lm A, Ux y)) +
      (c (Ux (x + ivmul y (A.val⁻¹ : GL (Fin 2) ℤ).val), Lm A) -
        (Aρ ρ).ρ (Ux x) (c (Ux (ivmul y (A.val⁻¹ : GL (Fin 2) ℤ).val), Lm A))) -
      c (Ux x, Lm A) := by
    rw [← key]
    abel
  rw [h]
  abel

end Relative

/-! ### The Hecke image of a cocycle -/

section Hecke

variable (p : Nat.Primes) (hp3 : p.val ≠ 3) {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- The local Hecke image of an inhomogeneous cocycle at the bad line. -/
def heckeTwo (c : groupCohomology.cocycles₂ (Aρ ρ)) : groupCohomology.cocycles₂ (Aρ ρ) :=
  ambientCocycleToGroup ΛB ρ (cocycleAction ρ (badLineCosets p hp3)
    (liftCocycle (badLineCosets p hp3) ρ c))

theorem heckeTwo_apply (c : groupCohomology.cocycles₂ (Aρ ρ)) (g h : ΛB) :
    heckeTwo p hp3 ρ c (g, h) = ∑ i : BIdx p, R1 ρ (rExpl p i)
      (c (deltaRep (badLineCosets p hp3) g (toRep p hp3 i),
        deltaRep (badLineCosets p hp3) h (nextRep (badLineCosets p hp3) g (toRep p hp3 i)))) := by
  rw [heckeTwo, ambientHecke_lift (badLineCosets p hp3) (repsB_not_mem p hp3) ρ c g h]
  exact (Fintype.sum_bijective (toRep p hp3) (toRep_bijective p hp3) _ _ (fun i => rfl)).symm

variable (c : groupCohomology.cocycles₂ (Aρ ρ)) (hrel : ∀ a b, c (Ux a, Ux b) = 0)

include hrel in
/-- **The Hecke image of a relative cocycle is relative.** -/
theorem heckeTwo_relative (a b : ℤ × ℤ) : heckeTwo p hp3 ρ c (Ux a, Ux b) = 0 := by
  rw [heckeTwo_apply]
  apply Finset.sum_eq_zero
  intro i _
  rcases i with j | d
  · rw [delta_Ux_inl, next_Ux_inl, delta_Ux_inl, hrel, map_zero]
  · rw [delta_Ux_inr, next_Ux_inr, delta_Ux_inr, hrel, map_zero]

/-- The radical terms `φ_e = ρ(τ_e) F(A, w_e)`. -/
def phiB (A : binaryArithmeticLevel) (e : Fin p.val × Fin p.val) : Aρ ρ :=
  R1 ρ (sRad p e) (Fb ρ c A (wB p A e))

theorem sRad_Ux (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) :
    sRad p d * ((Ux (zS p r d) : ΛB) : RationalGL3) =
      ((Ux r : ΛB) : RationalGL3) * sRad p (dS p r d) := by
  have h := rad_mul p r 1 1 d
  rw [radDelta_Ux, radNext_Ux] at h
  exact h

include hrel in
/-- **One radical term of the edge of the Hecke image.** -/
theorem rad_term (A : binaryArithmeticLevel) (r : ℤ × ℤ) (d : Fin p.val × Fin p.val) :
    R1 ρ (sRad p d) (c (Mel (wB p A d) 1 A, Ux (zP p A r d))) -
        R1 ρ (sRad p d) (c (Ux (zS p r d), Mel (wB p A (dS p r d)) 1 A)) =
      R1 ρ (sRad p d) ((Aρ ρ).ρ (Ux (wB p A d))
          (edgeB ρ c A (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val))) -
        phiB p ρ c A d + R1 ρ (Ux r) (phiB p ρ c A (dS p r d)) := by
  have h1 := relative_left ρ c hrel (wB p A d) (zP p A r d) A
  have h2 := relative_right ρ c hrel (zS p r d) (wB p A (dS p r d)) A
  rw [h1, h2, wB_zP p A r d]
  simp only [map_add, map_sub]
  have e2 : R1 ρ (sRad p d) ((Aρ ρ).ρ (Ux (zS p r d)) (Fb ρ c A (wB p A (dS p r d)))) =
      R1 ρ (Ux r) (phiB p ρ c A (dS p r d)) := by
    change R1 ρ (sRad p d) (R1 ρ (Ux (zS p r d)) _) = _
    rw [R1_mul, sRad_Ux, ← R1_mul]
    rfl
  rw [e2]
  unfold phiB
  abel

include hrel in
/-- **The edge cocycle of the local Hecke image at the bad line.** -/
theorem edge_heckeTwo (A : binaryArithmeticLevel) (r : ℤ × ℤ) :
    edgeB ρ (heckeTwo p hp3 ρ c) A r =
      ∑ j : Option (Fin p.val), R1 ρ (sLev p j)
          (edgeB ρ c (levelDelta p hp3 A j) (ivmul r (Bl p j))) +
        ∑ d : Fin p.val × Fin p.val,
          (R1 ρ (sRad p d) ((Aρ ρ).ρ (Ux (wB p A d))
              (edgeB ρ c A (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val))) -
            phiB p ρ c A d + R1 ρ (Ux r) (phiB p ρ c A (dS p r d))) := by
  have key : edgeB ρ (heckeTwo p hp3 ρ c) A r =
      (∑ j : Option (Fin p.val), R1 ρ (sLev p j)
          (c (Lm (levelDelta p hp3 A j),
            Ux (ivmul (ivmul r A.val.val) (Bl p (levelNext p hp3 A j))))) +
        ∑ d : Fin p.val × Fin p.val, R1 ρ (sRad p d)
          (c (Mel (wB p A d) 1 A, Ux (zP p A r d)))) -
      (∑ j : Option (Fin p.val), R1 ρ (sLev p j)
          (c (Ux (ivmul r (Bl p j)), Lm (levelDelta p hp3 A j))) +
        ∑ d : Fin p.val × Fin p.val, R1 ρ (sRad p d)
          (c (Ux (zS p r d), Mel (wB p A (dS p r d)) 1 A))) := by
    change heckeTwo p hp3 ρ c (Lm A, Ux (ivmul r A.val.val)) - heckeTwo p hp3 ρ c (Ux r, Lm A) = _
    rw [heckeTwo_apply, heckeTwo_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [next_Lm_inl, delta_Lm_inl, next_Ux_inl, delta_Ux_inl, next_Lm_inr, delta_Lm_inr,
      next_Ux_inr, delta_Ux_inr, rExpl]
  have hlevi : ∀ j : Option (Fin p.val),
      R1 ρ (sLev p j) (c (Lm (levelDelta p hp3 A j),
          Ux (ivmul (ivmul r A.val.val) (Bl p (levelNext p hp3 A j))))) -
        R1 ρ (sLev p j) (c (Ux (ivmul r (Bl p j)), Lm (levelDelta p hp3 A j))) =
      R1 ρ (sLev p j) (edgeB ρ c (levelDelta p hp3 A j) (ivmul r (Bl p j))) := by
    intro j
    have e : ivmul (ivmul r A.val.val) (Bl p (levelNext p hp3 A j)) =
        ivmul (ivmul r (Bl p j)) (levelDelta p hp3 A j).val.val := by
      rw [← ivmul_mul, ← ivmul_mul, Bl_delta p hp3]
    rw [← map_sub, edgeB, e]
  have hrad : (∑ d : Fin p.val × Fin p.val, R1 ρ (sRad p d)
          (c (Mel (wB p A d) 1 A, Ux (zP p A r d)))) -
      (∑ d : Fin p.val × Fin p.val, R1 ρ (sRad p d)
          (c (Ux (zS p r d), Mel (wB p A (dS p r d)) 1 A))) =
      ∑ d : Fin p.val × Fin p.val,
          (R1 ρ (sRad p d) ((Aρ ρ).ρ (Ux (wB p A d))
              (edgeB ρ c A (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val))) -
            phiB p ρ c A d + R1 ρ (Ux r) (phiB p ρ c A (dS p r d))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => rad_term p ρ c hrel A r d)
  have hL : (∑ j : Option (Fin p.val), R1 ρ (sLev p j)
          (c (Lm (levelDelta p hp3 A j),
            Ux (ivmul (ivmul r A.val.val) (Bl p (levelNext p hp3 A j)))))) -
      (∑ j : Option (Fin p.val), R1 ρ (sLev p j)
          (c (Ux (ivmul r (Bl p j)), Lm (levelDelta p hp3 A j)))) =
      ∑ j : Option (Fin p.val), R1 ρ (sLev p j)
          (edgeB ρ c (levelDelta p hp3 A j) (ivmul r (Bl p j))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => hlevi j)
  have hshuffle : ∀ (a b c' d : Aρ ρ), (a + c') - (b + d) = (a - b) + (c' - d) :=
    fun a b c' d => by abel
  rw [key, hshuffle, hL, hrad]

include hrel in
/-- The edge cocycle of the Hecke image, with the radical correction `Φ` isolated. -/
theorem edge_heckeTwo' (A : binaryArithmeticLevel) (r : ℤ × ℤ) :
    edgeB ρ (heckeTwo p hp3 ρ c) A r =
      ∑ j : Option (Fin p.val), R1 ρ (sLev p j)
          (edgeB ρ c (levelDelta p hp3 A j) (ivmul r (Bl p j))) +
        (∑ d : Fin p.val × Fin p.val, R1 ρ (sRad p d) ((Aρ ρ).ρ (Ux (wB p A d))
              (edgeB ρ c A (ivmul (zP p A r d) (A.val⁻¹ : GL (Fin 2) ℤ).val))) +
          (R1 ρ (Ux r) (∑ d : Fin p.val × Fin p.val, phiB p ρ c A d) -
            ∑ d : Fin p.val × Fin p.val, phiB p ρ c A d)) := by
  have hsc : ∑ d : Fin p.val × Fin p.val, R1 ρ (Ux r) (phiB p ρ c A (dS p r d)) =
      ∑ e : Fin p.val × Fin p.val, R1 ρ (Ux r) (phiB p ρ c A e) :=
    (crep_shift_bijective p r).sum_comp (fun e => R1 ρ (Ux r) (phiB p ρ c A e))
  rw [edge_heckeTwo p hp3 ρ c hrel, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsc, map_sum]
  abel

end Hecke

end TernaryPeriodPolynomials.LevelThree.BadLineEdge
