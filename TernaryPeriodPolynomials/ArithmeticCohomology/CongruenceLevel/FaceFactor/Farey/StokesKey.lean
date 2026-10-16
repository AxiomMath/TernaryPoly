module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Farey.StokesTau

@[expose] public section


/-!
# Twisted Farey Stokes, part 2: the Key Lemma `pV(dΦ, G) = 2 ∑_c (⟨Φ(c), coc G σ_c⟩ − η_G(σ_c))` for a twisted cusp function `Φ` and any cochain `G`

Formalized by Claude Sonnet 5.5.  Sub-lemma M3e: the extension of `pV_bdry_eq` from strictly equivariant to twisted `Φ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

section Key

variable {N : ℕ} (hN : 3 ≤ N) {A A' : Rep ℂ (gammaNGL N)} (C : Coupling A.ρ A'.ρ)

theorem head_mem_cuspReps {r : OTE} (hr : r ∈ (edgeReps hN).R) : head r ∈ (cuspReps hN).R := by
  simp only [edgeReps, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hr
  obtain ⟨⟨c, k⟩, ⟨hc, hk⟩, rfl⟩ := hr
  rw [edgeRep_head]
  exact hc

theorem decE_rep {r : OTE} (hr : r ∈ (edgeReps hN).R) : dec (edgeReps hN) r = (⟨r, hr⟩, 1) :=
  dec_eq (edgeReps hN) (gammaNFareyData hN).freeO (by simp)

/-- The paired representative of an edge representative: `r.swap = ν r • r̄`. -/
def rbarE (r : OTE) : OTE := ((dec (edgeReps hN) r.swap).1 : OTE)

def nuE (r : OTE) : gammaNGL N := (dec (edgeReps hN) r.swap).2

theorem rbarE_mem (r : OTE) : rbarE hN r ∈ (edgeReps hN).R := (dec (edgeReps hN) r.swap).1.2

theorem swap_eq_nuE (r : OTE) : r.swap = ((nuE hN r : gammaNGL N) : IntegralGL) • rbarE hN r :=
  (dec_spec (edgeReps hN) r.swap).symm

theorem rbarE_rbarE {r : OTE} (hr : r ∈ (edgeReps hN).R) : rbarE hN (rbarE hN r) = r := by
  have h1 := swap_eq_nuE hN r
  have h2 : (rbarE hN r).swap = (((nuE hN r)⁻¹ : gammaNGL N) : IntegralGL) • r := by
    have : r = ((nuE hN r : gammaNGL N) : IntegralGL) • (rbarE hN r).swap := by
      calc r = r.swap.swap := (OTE.swap_swap r).symm
        _ = (((nuE hN r : gammaNGL N) : IntegralGL) • rbarE hN r).swap := by rw [← h1]
        _ = _ := OTE.swap_smul _ _
    have key : ∀ (ν : gammaNGL N) (x : OTE), r = (ν : IntegralGL) • x → x = ((ν⁻¹ : gammaNGL N) : IntegralGL) • r := by
      intro ν x h
      rw [h, ← mul_smul]
      simp
    exact key _ _ this
  have h3 : dec (edgeReps hN) (rbarE hN r).swap = (⟨r, hr⟩, (nuE hN r)⁻¹) :=
    dec_eq (edgeReps hN) (gammaNFareyData hN).freeO h2.symm
  have h4 : rbarE hN (rbarE hN r) = ((dec (edgeReps hN) (rbarE hN r).swap).1 : OTE) := rfl
  rw [h4, h3]

theorem pV_eq_edgeReps (F : C1 A.ρ) (G : C1 A'.ρ) :
    pV C (gammaNFareyData hN) F G = ∑ r ∈ (edgeReps hN).R, C.e (F.1 r) (G.1 r) := by
  rw [pV_apply]
  unfold pairR
  exact sum_rep_indep (gammaNFareyData hN).freeO (gammaNFareyData hN).RE (edgeReps hN)
    (fun q => C.e (F.1 q) (G.1 q)) (fun γ q => by
      have h1 : F.1 ((γ : IntegralGL) • q) = A.ρ γ (F.1 q) := F.2.1 γ q
      have h2 : G.1 ((γ : IntegralGL) • q) = A'.ρ γ (G.1 q) := G.2.1 γ q
      change C.e (F.1 ((γ : IntegralGL) • q)) (G.1 ((γ : IntegralGL) • q)) = C.e (F.1 q) (G.1 q)
      rw [h1, h2, C.inv])

theorem sum_rbarE (ψ : OTE → ℂ) : ∑ r ∈ (edgeReps hN).R, ψ (rbarE hN r) = ∑ r ∈ (edgeReps hN).R, ψ r :=
  Finset.sum_bij' (fun r _ => rbarE hN r) (fun r _ => rbarE hN r) (fun r _ => rbarE_mem hN r) (fun r _ => rbarE_mem hN r)
    (fun _ hr => rbarE_rbarE hN hr) (fun _ hr => rbarE_rbarE hN hr) (fun _ _ => rfl)

variable {Φ : RationalLine2 → A}

theorem tail_term (hΦ : Φ ∈ Tw A.ρ) (G : C1 A'.ρ) (r : OTE) :
    C.e (Φ (tail r)) (G.1 r) = - C.e (Φ (head (rbarE hN r))) (G.1 (rbarE hN r)) + C.e (fTw A Φ (nuE hN r)) (G.1 r) := by
  have hsw := swap_eq_nuE hN r
  have hsl : IsSL ((nuE hN r : gammaNGL N) : IntegralGL) := gammaN_isSL hN (nuE hN r).2
  have h1 : tail r = ((nuE hN r : gammaNGL N) : IntegralGL) • head (rbarE hN r) := by
    rw [← head_swap, hsw, head_smul hsl]
  have h2 : G.1 r = - A'.ρ (nuE hN r) (G.1 (rbarE hN r)) := by
    have e1 : G.1 r.swap = - G.1 r := G.2.2 r
    have e2 : G.1 r.swap = A'.ρ (nuE hN r) (G.1 (rbarE hN r)) := by
      rw [hsw]; exact G.2.1 (nuE hN r) (rbarE hN r)
    rw [e2] at e1
    exact (neg_eq_iff_eq_neg.mp e1.symm)
  have h3 := fTw_twisted A hΦ (nuE hN r) (head (rbarE hN r))
  rw [h1, h3]
  have h4 := C.inv (nuE hN r) (Φ (head (rbarE hN r))) (G.1 (rbarE hN r))
  conv_lhs => rw [h2]
  simp only [map_add, LinearMap.add_apply, map_neg]
  rw [h4]
  conv_rhs => rw [h2]
  simp only [map_neg]
  ring

theorem tauHat_edgeRep (f : gammaNGL N → A) (hf : ∀ g h, f (g * h) = A.ρ g (f h) + f g) (G : C1 A'.ρ) {r : OTE}
    (hr : r ∈ (edgeReps hN).R) : tauHat hN C f G r = C.e (f (nuE hN r)) (G.1 r) / 2 := by
  have h1 : f 1 = 0 := by
    have := hf 1 1
    simp only [mul_one, map_one, Module.End.one_apply] at this
    exact (add_eq_left.mp this.symm)
  unfold tauHat edgeT
  rw [decE_rep hN hr]
  have h2 : G.1 r.swap = - G.1 r := G.2.2 r
  have h3 : (dec (edgeReps hN) r.swap).2 = nuE hN r := rfl
  rw [h3, h2]
  simp only [h1, map_zero, LinearMap.zero_apply, map_neg]
  ring

theorem cusp_cancel (hΦ : Φ ∈ Tw A.ρ) (c : RationalLine2) (P : A') :
    C.e (Φ c) (A'.ρ (cuspSigma (N := N) c) P - P) - C.e (fTw A Φ (cuspSigma c)) (A'.ρ (cuspSigma c) P) = 0 := by
  have h := fTw_twisted A hΦ (cuspSigma (N := N) c) c
  rw [show ((cuspSigma (N := N) c : gammaNGL N) : IntegralGL) • c = c from cuspSigma_cusp c] at h
  have h2 := C.inv (cuspSigma (N := N) c) (Φ c) P
  have h3 : fTw A Φ (cuspSigma c) = Φ c - A.ρ (cuspSigma c) (Φ c) := eq_sub_of_add_eq' h.symm
  rw [h3, map_sub, map_sub, LinearMap.sub_apply, h2]
  ring

/-- **Key Lemma (twisted Farey Stokes for the pairing with a cochain).**  For a twisted cusp function `Φ` with crossed homomorphism `f = fTw Φ` and ANY cochain `G ∈ C¹(A')`,
`pV(dΦ, G) = 2 ∑_c ( ⟨Φ(c), coc G (σ_c)⟩ − η_G(σ_c) )` where `η_G = etaPre` is the explicit function with `η_G(xy) = η_G x + η_G y + ⟨f x, x · coc G y⟩`. -/
theorem pV_bdryTw_eq (hΦ : Φ ∈ Tw A.ρ) (G : C1 A'.ρ) :
    pV C (gammaNFareyData hN) (bdryTw A.ρ hN ⟨Φ, hΦ⟩) G =
      2 * ∑ c ∈ (cuspReps hN).R, (C.e (Φ c) (coc A'.ρ G (cuspSigma c)) - etaPre hN C (fTw A Φ) G (cuspSigma c)) := by
  have hf := fTw_cocycle A hΦ
  rw [pV_eq_edgeReps]
  have e1 : ∀ r ∈ (edgeReps hN).R, C.e ((bdryTw A.ρ hN ⟨Φ, hΦ⟩).1 r) (G.1 r) =
      C.e (Φ (head r)) (G.1 r) - C.e (Φ (tail r)) (G.1 r) := by
    intro r _
    change C.e (Φ (head r) - Φ (tail r)) (G.1 r) = _
    rw [map_sub, LinearMap.sub_apply]
  rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib]
  have e2 : ∑ r ∈ (edgeReps hN).R, C.e (Φ (tail r)) (G.1 r) =
      - ∑ r ∈ (edgeReps hN).R, C.e (Φ (head r)) (G.1 r) + ∑ r ∈ (edgeReps hN).R, C.e (fTw A Φ (nuE hN r)) (G.1 r) := by
    rw [Finset.sum_congr rfl (fun r _ => tail_term hN C hΦ G r), Finset.sum_add_distrib, Finset.sum_neg_distrib]
    congr 2
    exact sum_rbarE hN (fun q => C.e (Φ (head q)) (G.1 q))
  have e3 : ∑ r ∈ (edgeReps hN).R, C.e (fTw A Φ (nuE hN r)) (G.1 r) =
      2 * ∑ r ∈ (edgeReps hN).R, tauHat hN C (fTw A Φ) G r := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [tauHat_edgeRep hN C (fTw A Φ) hf G hr]
    ring
  have e4 : ∑ r ∈ (edgeReps hN).R, C.e (Φ (head r)) (G.1 r) =
      ∑ c ∈ (cuspReps hN).R, C.e (Φ c) (A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) +
        coc A'.ρ G (cuspSigma c) - pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) := by
    rw [sum_edgeReps hN (fun q => C.e (Φ (head q)) (G.1 q))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← fan_G_sum G c, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [edgeRep_head]
  have e5 : ∑ r ∈ (edgeReps hN).R, tauHat hN C (fTw A Φ) G r =
      ∑ c ∈ (cuspReps hN).R, (etaPre hN C (fTw A Φ) G (cuspSigma c) +
        C.e (fTw A Φ (cuspSigma c)) (A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)))) := by
    rw [sum_edgeReps hN (fun q => tauHat hN C (fTw A Φ) G q)]
    exact Finset.sum_congr rfl fun c _ => fan_tau_sum hN C (fTw A Φ) hf G c
  have e6 : ∀ c ∈ (cuspReps hN).R, C.e (Φ c) (A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) +
        coc A'.ρ G (cuspSigma c) - pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) -
      (etaPre hN C (fTw A Φ) G (cuspSigma c) +
        C.e (fTw A Φ (cuspSigma c)) (A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)))) =
      C.e (Φ c) (coc A'.ρ G (cuspSigma c)) - etaPre hN C (fTw A Φ) G (cuspSigma c) := by
    intro c _
    have := cusp_cancel (Φ := Φ) C hΦ c (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus))
    have e : A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) +
        coc A'.ρ G (cuspSigma c) - pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus) =
        (A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) -
          pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) + coc A'.ρ G (cuspSigma c) := by abel
    rw [e, map_add]
    linear_combination this
  rw [e2, e3, e4, e5]
  have : ∑ c ∈ (cuspReps hN).R, (C.e (Φ c) (coc A'.ρ G (cuspSigma c)) - etaPre hN C (fTw A Φ) G (cuspSigma c)) =
      ∑ c ∈ (cuspReps hN).R, (C.e (Φ c) (A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) +
        coc A'.ρ G (cuspSigma c) - pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) -
      (etaPre hN C (fTw A Φ) G (cuspSigma c) +
        C.e (fTw A Φ (cuspSigma c)) (A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus))))) :=
    (Finset.sum_congr rfl fun c hc => (e6 c hc).symm)
  rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

end Key

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
