module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Farey.StokesCup

@[expose] public section


/-!
# Twisted Farey Stokes, part 4: invariance under coboundaries; the cusp formula for arbitrary representing crossed homomorphisms

Formalized by Claude Sonnet 5.5.

`cupForm_eq_cusp_sum_gen`: for twisted cusp functions `Φ`, `Φ'` and ARBITRARY crossed homomorphisms `a`, `a'` cohomologous to their crossed homomorphisms (`a = fTw Φ + (v − ρ·v)`, `a' = fTw Φ' + (v' − ρ'·v')`) and any
primitive `η` of the cup cocycle `⟨a x, x · a' y⟩`: `cupForm Φ Φ' = 2 ∑_c (⟨Φ(c) + v, a'(σ_c)⟩ + η(σ_c))`.  This is the form needed to match the Hochschild-Serre crossed homomorphisms of mixed cocycles.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

variable {N : ℕ}

section Shift

variable {A : Rep ℂ (gammaNGL N)}

/-- A twisted cusp function stays twisted after adding a constant. -/
theorem shift_const_mem_Tw {Φ : RationalLine2 → A} (hΦ : Φ ∈ Tw A.ρ) (v : A) : (fun x => Φ x + v) ∈ Tw A.ρ := by
  obtain ⟨f, hf, hf'⟩ := hΦ
  refine ⟨fun γ => f γ + (v - A.ρ γ v), fun g h => ?_, fun γ x => ?_⟩
  · simp only [hf g h, map_add, map_sub, ← Module.End.mul_apply, ← map_mul]
    abel
  · simp only [hf' γ x, map_add]
    abel

theorem fTw_shift_const (Φ : RationalLine2 → A) (v : A) (γ : gammaNGL N) :
    fTw A (fun x => Φ x + v) γ = fTw A Φ γ + (v - A.ρ γ v) := by
  unfold fTw
  simp only [map_add]
  abel

theorem bdryTw_shift_const (hN : 3 ≤ N) {Φ : RationalLine2 → A} (hΦ : Φ ∈ Tw A.ρ) (v : A) :
    bdryTw A.ρ hN ⟨fun x => Φ x + v, shift_const_mem_Tw hΦ v⟩ = bdryTw A.ρ hN ⟨Φ, hΦ⟩ := by
  apply Subtype.ext
  funext q
  change (Φ (head q) + v) - (Φ (tail q) + v) = Φ (head q) - Φ (tail q)
  abel

/-- The cochain carrying the cocycle of `Φ'` has the cocycle `fTw Φ'` up to a coboundary. -/
theorem coc_cuspG (hN : 3 ≤ N) {Φ' : RationalLine2 → A} (hΦ' : Φ' ∈ Tw A.ρ) :
    ∃ u : A, ∀ x : gammaNGL N, coc A.ρ (cuspG hN hΦ') x = fTw A Φ' x + (A.ρ x u - u) := by
  set D := gammaNFareyData hN
  have hg := fTw_cocycle A hΦ'
  set Hh := HhatFn A D (fTw A Φ') with hHh
  have htw : ∀ (γ : gammaNGL N) (x : Tri), Hh ((γ : IntegralGL) • x) = A.ρ γ (Hh x) + fTw A Φ' γ :=
    HhatFn_twisted A D (fTw A Φ') hg
  refine ⟨Hh triPlus, fun x => ?_⟩
  have hP : ∀ t, Hh t - Hh triPlus = pot A.ρ (cuspG hN hΦ') t := fun t =>
    pot_unique A.ρ (cuspG hN hΦ') (P := fun t => Hh t - Hh triPlus) (fun q => by
      change Hh q.1.2 - Hh triPlus - (Hh q.1.1 - Hh triPlus) = Hh q.1.2 - Hh q.1.1
      abel) (by simp) t
  unfold coc
  rw [← hP, htw x triPlus]
  abel

theorem shift_crossed {Φ : RationalLine2 → A} (hΦ : Φ ∈ Tw A.ρ) (v : A) (a : gammaNGL N → A)
    (ha : ∀ x, a x = fTw A Φ x + (v - A.ρ x v)) (g h : gammaNGL N) : a (g * h) = A.ρ g (a h) + a g := by
  have hf := fTw_cocycle A hΦ g h
  rw [ha, ha, ha, hf]
  simp only [map_add, map_sub, ← Module.End.mul_apply, ← map_mul]
  abel

end Shift

section Gen

variable {A A' : Rep ℂ (gammaNGL N)}

/-- **The twisted cusp formula for `cupForm`, for arbitrary representing crossed homomorphisms.** -/
theorem cupForm_eq_cusp_sum_gen (hN : 3 ≤ N) (C : Coupling A.ρ A'.ρ) {Φ : RationalLine2 → A} (hΦ : Φ ∈ Tw A.ρ)
    {Φ' : RationalLine2 → A'} (hΦ' : Φ' ∈ Tw A'.ρ) (a : gammaNGL N → A) (a' : gammaNGL N → A') (v : A) (v' : A')
    (ha : ∀ x, a x = fTw A Φ x + (v - A.ρ x v)) (ha' : ∀ x, a' x = fTw A' Φ' x + (v' - A'.ρ x v'))
    (η : gammaNGL N → ℂ) (hη : ∀ x y, η (x * y) = η x + η y - C.e (a x) (A'.ρ x (a' y))) :
    cupForm hN C Φ Φ' =
      2 * ∑ c ∈ (cuspReps hN).R, (C.e (Φ c + v) (a' (cuspSigma c)) + η (cuspSigma c)) := by
  set G := cuspG hN hΦ' with hG
  have hΦh := shift_const_mem_Tw hΦ v
  have hfa : fTw A (fun x => Φ x + v) = a := by
    funext x; rw [fTw_shift_const, ha]
  obtain ⟨u', hu'⟩ := coc_cuspG hN hΦ'
  have hacross := shift_crossed hΦ v a ha
  have h1 : cupForm hN C Φ Φ' = pV C (gammaNFareyData hN) (bdryTw A.ρ hN ⟨fun x => Φ x + v, hΦh⟩) G := by
    rw [bdryTw_shift_const hN hΦ v, ← pV_bdry_deltaTw hN C hΦ hΦ']
    rfl
  rw [h1, pV_bdryTw_eq hN C hΦh G, hfa]
  congr 1
  have hgrel : ∀ x, coc A'.ρ G x = a' x + (A'.ρ x (u' + v') - (u' + v')) := by
    intro x
    rw [hu', ha']
    simp only [map_add]
    abel
  set w := u' + v' with hw
  have hrel1 : ∀ x y, (fun x => - etaPre hN C a G x) (x * y) =
      (fun x => - etaPre hN C a G x) x + (fun x => - etaPre hN C a G x) y - C.e (a x) (A'.ρ x (coc A'.ρ G y)) := by
    intro x y
    simp only
    rw [etaPre_mul hN C a hacross]
    ring
  set ψ : gammaNGL N → ℂ := fun x => C.e (a x) (A'.ρ x w) with hψ
  have hrel2 : ∀ x y, (fun x => η x - ψ x) (x * y) =
      (fun x => η x - ψ x) x + (fun x => η x - ψ x) y - C.e (a x) (A'.ρ x (coc A'.ρ G y)) := by
    intro x y
    simp only
    have e1 : ψ (x * y) = ψ y + C.e (a x) (A'.ρ (x * y) w) := by
      simp only [hψ]
      rw [hacross x y]
      simp only [map_add, LinearMap.add_apply]
      have := C.inv x (a y) (A'.ρ y w)
      rw [map_mul, Module.End.mul_apply]
      rw [this]
    have e2 : C.e (a x) (A'.ρ x (coc A'.ρ G y)) =
        C.e (a x) (A'.ρ x (a' y)) + C.e (a x) (A'.ρ (x * y) w) - ψ x := by
      rw [hgrel y]
      simp only [hψ, map_add, map_sub, map_mul, Module.End.mul_apply]
      ring
    rw [e1, e2, hη x y]
    ring
  have hsum := cusp_sum_eq_of_relation hN (fun x y => C.e (a x) (A'.ρ x (coc A'.ρ G y))) (fun x => - etaPre hN C a G x) (fun x => η x - ψ x) hrel1 hrel2
  have hterm : ∀ c ∈ (cuspReps hN).R, C.e (Φ c + v) (coc A'.ρ G (cuspSigma c)) - etaPre hN C a G (cuspSigma c) -
      (C.e (Φ c + v) (a' (cuspSigma c)) + η (cuspSigma c)) =
        (- etaPre hN C a G (cuspSigma c) - (η (cuspSigma c) - ψ (cuspSigma c))) := by
    intro c _
    have hcc := cusp_cancel (Φ := fun x => Φ x + v) C hΦh c w
    rw [hfa] at hcc
    rw [hgrel (cuspSigma c)]
    simp only [map_add, LinearMap.add_apply, hψ] at hcc ⊢
    linear_combination hcc
  have := Finset.sum_congr rfl hterm
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib] at this hsum ⊢
  linear_combination this + hsum

end Gen

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
