module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BMat

@[expose] public section


/-!
# The value of the cup class of a line datum on the Heisenberg cycle

Formalized by Claude Sonnet 5.5.

Let `K` carry Heisenberg coordinates `H` coming from a homomorphism `M_g : K → SL₃(ℤ)` into the standard unipotent group, and let `M_h` be another homomorphism of line type with `q M_h = M_g q` for a `q` in
the Borel of the line.  If `u = c · b` (`b` the cusp coordinate), then the class `[u ∪ β_{M_h}]` takes the value `q₀₀ · c · (-2 p² q'²)` on the Heisenberg cycle (`local_value`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open Matrix TernaryPeriodPolynomials.Argument.FlagH3 TernaryPeriodPolynomials.Argument.GammaNFacesFull

variable {K : Type} [Group K]

/-- **The value of a line cup class on a bar `3`-cycle, relative to a standard datum**: if the frame homomorphism `M_g` has the line datum `D'`, `M_h` is related to `M_g` by `q ∈ lineBorel`, `z` is a cycle on which
`b' ∪ β_{D'}` takes the value `κ` and `u = c b'`, then `u ∪ β_{M_h}` takes the value `q₀₀ c κ`. -/
theorem local_value_gen (D' : LineData K) (b' : K → ℤ) (hb' : ∀ g h, b' (g * h) = b' g + b' h)
    (Mg Mh : K →* SL(3, ℤ)) (hg : LineType Mg) (hh : LineType Mh)
    (hD : ∀ s, (matLineData Mg hg).A s = D'.A s ∧ (matLineData Mg hg).v s = D'.v s)
    (q : SL(3, ℤ)) (hq : q ∈ lineBorel)
    (hrel : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * (Mh s : Matrix (Fin 3) (Fin 3) ℤ) =
      (Mg s : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ))
    (z : (Fin 3 → K) →₀ ℚ) (hz : IsCycle z) (κ : ℚ)
    (hval : chainEval z (fun g : Fin 3 → K => (b' (g 0) : ℚ) * D'.beta (g 1) (g 2)) = κ)
    (c : ℚ) (u : K → ℚ) (hu : ∀ s, u s = c * b' s) :
    chainEval z (fun g : Fin 3 → K => u (g 0) * (matLineData Mh hh).beta (g 1) (g 2)) =
      ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ) * (c * κ) := by
  obtain ⟨hQQ, hε, hdet, hA, hv⟩ := frame_relation Mg Mh hg hh q hq hrel
  have hu' : ∀ g h, u (g * h) = u g + u h := fun g h => by
    rw [hu, hu, hu, hb']; push_cast; ring
  have hA' : ∀ s, (matLineData Mh hh).A s = blockQinv q * D'.A s * blockQ q := by
    intro s; rw [hA s, (hD s).1]
  have hv' : ∀ s, (matLineData Mh hh).v s = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 •
      ((D'.v s + frameW q ᵥ* (1 - D'.A s)) ᵥ* blockQ q) := by
    intro s; rw [hv s, (hD s).1, (hD s).2]
  have key := LineData.cup_eval_change z hz u hu' (matLineData Mh hh) D' (blockQ q) (blockQinv q) hQQ _ hε (frameW q) hA' hv'
  rw [key, hdet]
  have hpt : (fun g : Fin 3 → K => u (g 0) * D'.beta (g 1) (g 2)) =
      c • (fun g : Fin 3 → K => (b' (g 0) : ℚ) * D'.beta (g 1) (g 2)) := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, hu]
    ring
  rw [hpt, ← chainEvalL_apply, map_smul, chainEvalL_apply, hval, smul_eq_mul]

theorem local_value (H : HeisCoords K) (Mg Mh : K →* SL(3, ℤ)) (hg : LineType Mg) (hh : LineType Mh)
    (hH : ∀ s, (matLineData Mg hg).A s = (heisLineData H).A s ∧ (matLineData Mg hg).v s = (heisLineData H).v s)
    (q : SL(3, ℤ)) (hq : q ∈ lineBorel)
    (hrel : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * (Mh s : Matrix (Fin 3) (Fin 3) ℤ) =
      (Mg s : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ))
    (X Y : K) (p r : ℤ) (hXa : H.a X = p) (hXb : H.b X = 0) (hXc : H.c X = 0)
    (hYa : H.a Y = 0) (hYb : H.b Y = r) (hYc : H.c Y = 0) (c : ℚ) (u : K → ℚ) (hu : ∀ s, u s = c * H.b s) :
    chainEval (heisCycle X Y) (fun g : Fin 3 → K => u (g 0) * (matLineData Mh hh).beta (g 1) (g 2)) =
      ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ) * (c * (-2 * (p : ℚ) ^ 2 * (r : ℚ) ^ 2)) :=
  local_value_gen (heisLineData H) H.b H.b_mul Mg Mh hg hh hH q hq hrel (heisCycle X Y)
    (H.cycle_isCycle X Y p r hXa hXb hXc hYa hYb hYc) _ (heis_cycle_cup H X Y p r hXa hXb hXc hYa hYb hYc) c u hu

end TernaryPeriodPolynomials.Argument.GammaNStokes
