module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalCup

@[expose] public section


/-!
# Twisted Farey Stokes, part 1: the edge weights `τ̂`, the function `η_G`, and the fan sums

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

section Tau

variable {N : ℕ} (hN : 3 ≤ N) {A A' : Rep ℂ (gammaNGL N)} (C : Coupling A.ρ A'.ρ) (f : gammaNGL N → A)

/-- The weight of an oriented edge: `e(f(h_q), G q)` with `q = h_q • r_q` the decomposition along the representatives `edgeReps`. -/
def edgeT (G : C1 A'.ρ) (q : OTE) : ℂ := C.e (f (dec (edgeReps hN) q).2) (G.1 q)

/-- The antisymmetrized weight. -/
def tauHat (G : C1 A'.ρ) (q : OTE) : ℂ := (edgeT hN C f G q - edgeT hN C f G q.swap) / 2

theorem tauHat_swap (G : C1 A'.ρ) (q : OTE) : tauHat hN C f G q.swap = - tauHat hN C f G q := by
  unfold tauHat
  rw [OTE.swap_swap]
  ring

theorem decE_smul (g : gammaNGL N) (q : OTE) :
    dec (edgeReps hN) ((g : IntegralGL) • q) = ((dec (edgeReps hN) q).1, g * (dec (edgeReps hN) q).2) :=
  dec_eq (edgeReps hN) (gammaNFareyData hN).freeO (by
    have := dec_spec (edgeReps hN) q
    change (g * (dec (edgeReps hN) q).2) • ((dec (edgeReps hN) q).1 : OTE) = (g : IntegralGL) • q
    rw [mul_smul]
    exact congrArg (fun x => (g : IntegralGL) • x) this)

theorem edgeT_smul (hf : ∀ g h, f (g * h) = A.ρ g (f h) + f g) (G : C1 A'.ρ) (g : gammaNGL N) (q : OTE) :
    edgeT hN C f G ((g : IntegralGL) • q) = edgeT hN C f G q + C.e (f g) (G.1 ((g : IntegralGL) • q)) := by
  unfold edgeT
  rw [decE_smul, hf]
  simp only [map_add, LinearMap.add_apply]
  have h1 : G.1 ((g : IntegralGL) • q) = A'.ρ g (G.1 q) := G.2.1 g q
  have h2 := C.inv g (f (dec (edgeReps hN) q).2) (G.1 q)
  rw [h1, h2]

theorem tauHat_smul (hf : ∀ g h, f (g * h) = A.ρ g (f h) + f g) (G : C1 A'.ρ) (g : gammaNGL N) (q : OTE) :
    tauHat hN C f G ((g : IntegralGL) • q) = tauHat hN C f G q + C.e (f g) (G.1 ((g : IntegralGL) • q)) := by
  unfold tauHat
  have h1 := edgeT_smul hN C f hf G g q
  have h2 := edgeT_smul hN C f hf G g q.swap
  rw [OTE.swap_smul, h1, h2]
  have h3 : G.1 ((g : IntegralGL) • q.swap) = - G.1 ((g : IntegralGL) • q) := by
    rw [← OTE.swap_smul]; exact G.2.2 _
  rw [h3, map_neg]
  ring

/-- The (negative of the) primitive of the cup cocycle: the potential of `τ̂` at the translate of the base triangle. -/
def etaPre (G : C1 A'.ρ) (x : gammaNGL N) : ℂ := potFn (tauHat hN C f G) ((x : IntegralGL) • triPlus)

theorem potFn_tau_smul (hf : ∀ g h, f (g * h) = A.ρ g (f h) + f g) (G : C1 A'.ρ) (g : gammaNGL N) (t : Tri) :
    potFn (tauHat hN C f G) ((g : IntegralGL) • t) = potFn (tauHat hN C f G) ((g : IntegralGL) • triPlus) +
      potFn (tauHat hN C f G) t + C.e (f g) (A'.ρ g (pot A'.ρ G t)) := by
  have hanti : ∀ q : OTE, tauHat hN C f G q.swap = - tauHat hN C f G q := tauHat_swap hN C f G
  have h := tri_const (P := fun t => potFn (tauHat hN C f G) ((g : IntegralGL) • t) - C.e (f g) (A'.ρ g (pot A'.ρ G t))
      - potFn (tauHat hN C f G) t) (fun q => by
    have h1 := potFn_delta (tauHat hN C f G) hanti ((g : IntegralGL) • q)
    have h2 := potFn_delta (tauHat hN C f G) hanti q
    have h3 := pot_delta A'.ρ G q
    have h4 := tauHat_smul hN C f hf G g q
    have h5 : G.1 ((g : IntegralGL) • q) = A'.ρ g (G.1 q) := G.2.1 g q
    change potFn (tauHat hN C f G) ((g : IntegralGL) • q.1.2) - potFn (tauHat hN C f G) ((g : IntegralGL) • q.1.1) =
      tauHat hN C f G ((g : IntegralGL) • q) at h1
    have h6 : C.e (f g) (A'.ρ g (pot A'.ρ G q.1.2)) - C.e (f g) (A'.ρ g (pot A'.ρ G q.1.1)) =
        C.e (f g) (G.1 ((g : IntegralGL) • q)) := by
      rw [h5, ← h3, map_sub, map_sub]
    show potFn (tauHat hN C f G) ((g : IntegralGL) • q.1.2) - C.e (f g) (A'.ρ g (pot A'.ρ G q.1.2)) -
        potFn (tauHat hN C f G) q.1.2 = potFn (tauHat hN C f G) ((g : IntegralGL) • q.1.1) -
        C.e (f g) (A'.ρ g (pot A'.ρ G q.1.1)) - potFn (tauHat hN C f G) q.1.1
    linear_combination h1 - h6 - h2 + h4) t
  have h0 : C.e (f g) (A'.ρ g (pot A'.ρ G triPlus)) = 0 := by simp [pot_base]
  rw [h0, potFn_base] at h
  linear_combination h

theorem etaPre_mul (hf : ∀ g h, f (g * h) = A.ρ g (f h) + f g) (G : C1 A'.ρ) (g h : gammaNGL N) :
    etaPre hN C f G (g * h) = etaPre hN C f G g + etaPre hN C f G h + C.e (f g) (A'.ρ g (coc A'.ρ G h)) := by
  unfold etaPre coc
  have := potFn_tau_smul hN C f hf G g ((h : IntegralGL) • triPlus)
  have e : (((g * h : gammaNGL N)) : IntegralGL) • triPlus = (g : IntegralGL) • ((h : IntegralGL) • triPlus) := by
    rw [← mul_smul]; rfl
  rw [e, this]

end Tau

section Fan

variable {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Telescoping of an antisymmetric edge function along one period of the fan at the cusp `c`. -/
theorem fan_telescope (F : OTE → V) (hF : ∀ q : OTE, F q.swap = -F q) (c : RationalLine2) :
    ∑ k ∈ Finset.range N, F ((cuspElt c * Tk (k : ℤ)) • p0.swap) =
      potFn F ((cuspElt c * Tk ((N : ℤ) + (-1))) • triPlus) - potFn F ((cuspElt c * Tk (-1)) • triPlus) := by
  let t : ℤ → Tri := fun m => (cuspElt c * Tk m) • triPlus
  have hq : ∀ k : ℕ, F ((cuspElt c * Tk (k : ℤ)) • p0.swap) = potFn F (t k) - potFn F (t ((k : ℤ) - 1)) := by
    intro k
    rw [← potFn_delta F hF ((cuspElt c * Tk (k : ℤ)) • p0.swap)]
    have h2 : ((cuspElt c * Tk (k : ℤ)) • p0.swap).1.2 = t k := rfl
    have h1 : ((cuspElt c * Tk (k : ℤ)) • p0.swap).1.1 = t ((k : ℤ) - 1) := by
      change (cuspElt c * Tk (k : ℤ)) • triMinus = _
      rw [← Tk_neg_one_triPlus, ← mul_smul]
      show _ = (cuspElt c * Tk ((k : ℤ) - 1)) • triPlus
      congr 1
      rw [mul_assoc, ← Tk_add]
      congr 2
    rw [h1, h2]
  simp_rw [hq]
  have := Finset.sum_range_sub (fun k : ℕ => potFn F (t ((k : ℤ) - 1))) N
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at this
  rw [this]
  simp [t, sub_eq_add_neg]

end Fan

section Cusp

variable {N : ℕ} (hN : 3 ≤ N) {A A' : Rep ℂ (gammaNGL N)} (C : Coupling A.ρ A'.ρ) (f : gammaNGL N → A)

theorem cusp_triangle_shift (c : RationalLine2) :
    (cuspElt c * Tk ((N : ℤ) + (-1))) • triPlus =
      ((cuspSigma (N := N) c : gammaNGL N) : IntegralGL) • ((cuspElt c * Tk (-1)) • triPlus) :=
  (cuspSigma_triangle c (-1)).symm

/-- The sum of the weights along one period of the fan at `c`. -/
theorem fan_tau_sum (hf : ∀ g h, f (g * h) = A.ρ g (f h) + f g) (G : C1 A'.ρ) (c : RationalLine2) :
    ∑ k ∈ Finset.range N, tauHat hN C f G ((cuspElt c * Tk (k : ℤ)) • p0.swap) =
      etaPre hN C f G (cuspSigma (N := N) c) +
        C.e (f (cuspSigma c)) (A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus))) := by
  rw [fan_telescope (tauHat hN C f G) (tauHat_swap hN C f G) c, cusp_triangle_shift,
    potFn_tau_smul hN C f hf G]
  unfold etaPre
  ring

/-- The sum of `G` along one period of the fan at `c`. -/
theorem fan_G_sum (G : C1 A'.ρ) (c : RationalLine2) :
    ∑ k ∈ Finset.range N, G.1 ((cuspElt c * Tk (k : ℤ)) • p0.swap) =
      A'.ρ (cuspSigma c) (pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus)) + coc A'.ρ G (cuspSigma c) -
        pot A'.ρ G ((cuspElt c * Tk (-1)) • triPlus) := by
  rw [fan_telescope G.1 G.2.2 c, cusp_triangle_shift]
  change pot A'.ρ G _ - pot A'.ρ G _ = _
  rw [pot_smul]
  unfold coc
  abel

end Cusp

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
