module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Sums
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Kappa

@[expose] public section


/-!
# Hecke adjointness of the cup pairing of `Γ₁(3)`

The Fricke involution `Ω` of the stabilizer `H` of the base coset transports a cup primitive `θ'` of
`(x', y|_H)` into a cup primitive `θ''` of `(x|_H, y')` (`AdjL3Transport`), with
`loc θ'' h = κΩ · loc θ' (Ω h)` (`swap_pair`).  Combined with the evaluation of the cup formulas of
`(T x, y)` and `(x, T y)` as sums of four local terms (`lhs_value`, `rhs_value`), this gives

  `cup(T x, y) = κ_gen · cup(x, T y)`,    `κ_gen = (κΩ · (-ε_p))⁻¹`            (`coreAdjoint`),

the statement `CoreAdjoint m e e' p hp3 (kappaGen m e e' p)`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
open TernaryPeriodPolynomials.BoundaryDuality.AdjCore
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho
  level_compat core_compat crossedHeckeFun_mem)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep coreRep)
open GeneralEisenstein
open TripleModel LinearDuality CocycleBridge EpsilonSplit

section Swap

variable {m : ℕ} {e e' : ℤ} (D : Data m e e') (p : Nat.Primes) (hp3 : p.val ≠ 3)

theorem hinvH (h : HK p hp3) (v w : Binary.HomogeneousPoly m) :
    Bm m (ρH m e p hp3 h v) (ρH m e' p hp3 h w) = Bm m v w := hinvK m e e' h.1 v w

/-- The cup primitive of `(x|_H, y')` obtained from `θ'` by the Fricke transport. -/
def thetaR (θ' : HK p hp3 → ℂ) : HK p hp3 → ℂ :=
  transportPrim (Bm m) (ρH m e' p hp3) (Ω p hp3) (frickeKappa p m e e') θ'
    (fun h : HK p hp3 => D.x h.1.1) (yBase D p hp3) (fricke_u p hp3 (rationalRho m e) D.x)
    (rationalRho m e' (heckeRep p (J0 p))⁻¹ (D.y (sF p hp3)))

theorem thetaR_isCupPrimitive {θ' : HK p hp3 → ℂ}
    (hθ' : IsCupPrimitive (Bm m) (ρH m e' p hp3) (xBase D p hp3)
      (fun h : HK p hp3 => D.y h.1.1) θ') :
    IsCupPrimitive (Bm m) (ρH m e' p hp3) (fun h : HK p hp3 => D.x h.1.1) (yBase D p hp3)
      (thetaR D p hp3 θ') :=
  transport_isCupPrimitive (hinvH (m := m) (e := e) (e' := e') p hp3) (Ω p hp3) (rationalRho m e (gP p hp3)⁻¹)
    (rationalRho m e' (gP p hp3)) (frickeKappa p m e e') (fricke_hF' m e' p hp3)
    (fricke_hcomp m e e' p hp3) (yH_isCocycle D p hp3) (xH_isCocycle D p hp3) hθ'
    (fricke_u p hp3 (rationalRho m e) D.x)
    (rationalRho m e' (heckeRep p (J0 p))⁻¹ (D.y (sF p hp3)))
    (relation_left m e p hp3 D.hx) (relation_right m e' p hp3 D.hy)

/-- **The local term at `h₁` of the transported primitive is `κΩ · (-ε)` times the local term of `θ'`
at the partner `h₂`** (`Ω h₁ = h₂^{±1}`). -/
theorem swap_pair {θ' : HK p hp3 → ℂ}
    (hθ' : IsCupPrimitive (Bm m) (ρH m e' p hp3) (xBase D p hp3)
      (fun h : HK p hp3 => D.y h.1.1) θ')
    {h₁ h₂ : HK p hp3}
    (hΩ : (eps p = -1 ∧ Ω p hp3 h₁ = h₂) ∨ (eps p = 1 ∧ Ω p hp3 h₁ = h₂⁻¹))
    {u w : Binary.HomogeneousPoly m} (hu : xBase D p hp3 h₂ = (ρH m e p hp3 h₂ - 1) u)
    (hw : D.x h₁.1.1 = (ρH m e p hp3 h₁ - 1) w)
    (hy : CobAt (ρH m e' p hp3) (yBase D p hp3) h₁) :
    localTerm (Bm m) (thetaR D p hp3 θ') (yBase D p hp3) h₁ w =
      (frickeKappa p m e e' * (-((eps p : ℤ) : ℂ))) *
        localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) h₂ u := by
  -- the primitive of `x'` at `Ω h₁` and the sign
  have key : ∃ s : ℂ, s = -((eps p : ℤ) : ℂ) ∧ xBase D p hp3 (Ω p hp3 h₁) =
      (ρH m e p hp3 (Ω p hp3 h₁) - 1) u ∧
      localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) (Ω p hp3 h₁) u =
        s * localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) h₂ u := by
    rcases hΩ with ⟨he, hΩ⟩ | ⟨he, hΩ⟩
    · refine ⟨1, ?_, ?_, ?_⟩
      · rw [he]; simp
      · rw [hΩ]; exact hu
      · rw [hΩ, one_mul]
    · refine ⟨-1, ?_, ?_, ?_⟩
      · rw [he]; simp
      · rw [hΩ]
        exact primitive_inv (xBase_isCocycle D p hp3) hu
      · rw [hΩ, neg_one_mul]
        exact localTerm_inv (hinvH (m := m) (e := e) (e' := e') p hp3) (xBase_isCocycle D p hp3) (yH_isCocycle D p hp3) hθ' hu
  obtain ⟨s, hs, hv, hloc⟩ := key
  obtain ⟨uy, huy⟩ := hy
  have hX : ∀ h : HK p hp3, rationalRho m e (gP p hp3)⁻¹ (xBase D p hp3 (Ω p hp3 h)) +
      (ρH m e p hp3 h (fricke_u p hp3 (rationalRho m e) D.x) -
        fricke_u p hp3 (rationalRho m e) D.x) = D.x h.1.1 :=
    fun h => relation_left m e p hp3 D.hx h
  have hY : ∀ h : HK p hp3, rationalRho m e' (gP p hp3) (D.y (Ω p hp3 h).1.1) =
      yBase D p hp3 h +
        (ρH m e' p hp3 h (rationalRho m e' (heckeRep p (J0 p))⁻¹ (D.y (sF p hp3))) -
          rationalRho m e' (heckeRep p (J0 p))⁻¹ (D.y (sF p hp3))) :=
    fun h => relation_right m e' p hp3 D.hy h
  have hF := fricke_hF m e p hp3
  have hw0 : D.x h₁.1.1 = (ρH m e p hp3 h₁ - 1)
      (rationalRho m e (gP p hp3)⁻¹ u + fricke_u p hp3 (rationalRho m e) D.x) := by
    rw [← hX h₁, hv]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hF, map_add]
  have h1 : localTerm (Bm m) (thetaR D p hp3 θ') (yBase D p hp3) h₁
      (rationalRho m e (gP p hp3)⁻¹ u + fricke_u p hp3 (rationalRho m e) D.x) =
      frickeKappa p m e e' * localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1)
        (Ω p hp3 h₁) u :=
    transport_localTerm (B := Bm m) (X₁ := xBase D p hp3) (X₂ := fun h : HK p hp3 => D.x h.1.1)
      (Y₁ := fun h : HK p hp3 => D.y h.1.1) (Y₂ := yBase D p hp3) (θ₁ := θ') (hinvH (m := m) (e := e) (e' := e') p hp3)
      (Ω p hp3) (rationalRho m e (gP p hp3)⁻¹) (rationalRho m e' (gP p hp3))
      (frickeKappa p m e e') hF (fricke_hcomp m e e' p hp3)
      (fricke_u p hp3 (rationalRho m e) D.x)
      (rationalRho m e' (heckeRep p (J0 p))⁻¹ (D.y (sF p hp3))) hX hY h₁ hv
  have h2 : localTerm (Bm m) (thetaR D p hp3 θ') (yBase D p hp3) h₁ w =
      localTerm (Bm m) (thetaR D p hp3 θ') (yBase D p hp3) h₁
        (rationalRho m e (gP p hp3)⁻¹ u + fricke_u p hp3 (rationalRho m e) D.x) :=
    localTerm_eq_of_primitive (X := fun h : HK p hp3 => D.x h.1.1)
      (hinvH (m := m) (e := e) (e' := e') p hp3) hw hw0 huy
  rw [h2, h1, hloc, hs]
  ring

end Swap

section Main

variable {m : ℕ} {e e' : ℤ} (D : Data m e e') (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The primitives of `x` at the four cusp elements, from a primitive at `T`. -/
theorem x_prim_four (wT : Binary.HomogeneousPoly m)
    (hwT : D.x (upper 1) = (levelRep m e (upper 1) - 1) wT) :
    D.x (TpK p hp3).1.1 = (ρH m e p hp3 (TpK p hp3) - 1) wT ∧
    D.x (tK2 p hp3).1.1 = (ρH m e p hp3 (tK2 p hp3) - 1)
      (coreRep m e (rK p hp3 none) wT - restr D.x (rK p hp3 none)) ∧
    D.x (LK p hp3).1.1 = (ρH m e p hp3 (LK p hp3) - 1) (-restr D.x (rK p hp3 (J0 p))) ∧
    D.x (tL2 p hp3).1.1 = (ρH m e p hp3 (tL2 p hp3) - 1) (-restr D.x (rK p hp3 none)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change D.x (TpK p hp3).1.1 = (levelRep m e (TpK p hp3).1.1 - 1) wT
    rw [TpK_val]
    have := cocycle_pow_primitive D.hx hwT p.val
    rwa [upper_pow] at this
  · change D.x (tK2 p hp3).1.1 = (levelRep m e (tK2 p hp3).1.1 - 1)
      (levelRep m e (rInfG p hp3) wT - D.x (rInfG p hp3))
    rw [tr_T_none_val]
    exact primitive_conj D.hx hwT (rInfG p hp3)
  · change D.x (LK p hp3).1.1 = (levelRep m e (LK p hp3).1.1 - 1) (-D.x (rK p hp3 (J0 p)).1)
    rw [rK_base, LK_val, D.hxL]
    simp [D.hx.map_one]
  · change D.x (tL2 p hp3).1.1 = (levelRep m e (tL2 p hp3).1.1 - 1) (-D.x (rInfG p hp3))
    rw [tr_Lpow_none_val]
    have h0 : D.x (lower (p.val : ℤ)) = (levelRep m e (lower (p.val : ℤ)) - 1) 0 := by
      have := cocycle_pow_eq_zero D.hx D.hxL p.val
      rw [lower_pow] at this
      rw [this]
      simp
    have := primitive_conj D.hx h0 (rInfG p hp3)
    simpa using this

/-- **Hecke adjointness of the cup formula of `Γ₁(3)`.** -/
theorem coreAdjoint (m : ℕ) (e e' : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3) :
    CoreAdjoint m e e' p hp3 (kappaGen m e e' p) := by
  intro D v hv w hw hYL
  obtain ⟨θ', hθ'⟩ := exists_isCupPrimitive_of_H2 (H2_zero_HK p hp3) (hinvH (m := m) (e := e) (e' := e') p hp3)
    (xBase_isCocycle D p hp3) (yH_isCocycle D p hp3)
  have hxL : CobAt (levelRep m e) D.x (lower 1) := ⟨0, by rw [D.hxL]; simp⟩
  have hyL : CobAt (levelRep m e') D.y (lower 1) := ⟨0, by rw [D.hyL]; simp⟩
  obtain ⟨_, xA2, _, xA4, xD1, xD2, xD3, xD4⟩ := Para.four p hp3 D.hx D.hxT hxL
  obtain ⟨_, _, _, _, yD1, yD2, yD3, yD4⟩ := Para.four p hp3 D.hy D.hyT hyL
  obtain ⟨u₁', hu₁'⟩ := xD1
  obtain ⟨u₂', hu₂'⟩ := xD2
  obtain ⟨u₃', hu₃'⟩ := xD3
  obtain ⟨u₄', hu₄'⟩ := xD4
  have hu₁ := baseCocycle_cobAt e p hp3 (TpK p hp3) hu₁'
  have hu₂ := baseCocycle_cobAt e p hp3 (tK2 p hp3) hu₂'
  have hu₃ := baseCocycle_cobAt e p hp3 (LK p hp3) hu₃'
  have hu₄ := baseCocycle_cobAt e p hp3 (tL2 p hp3) hu₄'
  obtain ⟨v₁', hv₁'⟩ := yD1
  obtain ⟨v₂', hv₂'⟩ := yD2
  obtain ⟨v₃', hv₃'⟩ := yD3
  obtain ⟨v₄', hv₄'⟩ := yD4
  have hy₁ : CobAt (ρH m e' p hp3) (yBase D p hp3) (TpK p hp3) :=
    ⟨_, baseCocycle_cobAt e' p hp3 (TpK p hp3) hv₁'⟩
  have hy₂ : CobAt (ρH m e' p hp3) (yBase D p hp3) (tK2 p hp3) :=
    ⟨_, baseCocycle_cobAt e' p hp3 (tK2 p hp3) hv₂'⟩
  have hy₃ : CobAt (ρH m e' p hp3) (yBase D p hp3) (LK p hp3) :=
    ⟨_, baseCocycle_cobAt e' p hp3 (LK p hp3) hv₃'⟩
  have hy₄ : CobAt (ρH m e' p hp3) (yBase D p hp3) (tL2 p hp3) :=
    ⟨_, baseCocycle_cobAt e' p hp3 (tL2 p hp3) hv₄'⟩
  have hθ'' := thetaR_isCupPrimitive D p hp3 hθ'
  obtain ⟨hw₁, hw₂, hw₃, hw₄⟩ := x_prim_four D p hp3 w.1 hw.1
  rw [lhs_value D p hp3 hθ' hv hu₁ hu₂ hu₃ hu₄, rhs_value D p hp3 hθ'' hw hYL,
    swap_pair D p hp3 hθ' (Ω_TpK p hp3) hu₂ hw₁ hy₁,
    swap_pair D p hp3 hθ' (Ω_tK2 p hp3) hu₁ hw₂ hy₂,
    swap_pair D p hp3 hθ' (Ω_LK p hp3) hu₄ hw₃ hy₃,
    swap_pair D p hp3 hθ' (Ω_tL2 p hp3) hu₃ hw₄ hy₄]
  have hK : AdjL3Cosets.frickeKappa p m e e' * (-((AdjL3Cosets.eps p : ℤ) : ℂ)) ≠ 0 :=
    mul_ne_zero (AdjL3Cosets.frickeKappa_ne_zero p m e e')
      (neg_ne_zero.mpr (AdjL3Cosets.eps_ne_zero_C p))
  have hκ := AdjL3Cosets.frickeKappa_ne_zero p m e e'
  have hE := AdjL3Cosets.eps_ne_zero_C p
  unfold kappaGen
  field_simp
  ring

end Main

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
