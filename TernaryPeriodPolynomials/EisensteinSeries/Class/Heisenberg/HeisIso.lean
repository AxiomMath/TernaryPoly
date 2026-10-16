module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisD2

@[expose] public section



/-!
# The Nomizu-Kasuya isomorphism for the Heisenberg nilmanifold: the averaging is a cochain map

Formalized by Claude Sonnet 5.5.

* `heisAv_const`: `Av ∘ ι = I` (the average of a constant cochain is the constant).
* `heisAv_Dop`: `Av (D u) = 𝔇 (Av u)`: the averaging is a cochain map from periodic cochains to the Lie algebra complex.
* `heis_inclusion_injective`: a constant coboundary of a periodic cochain is a coboundary in the Lie algebra complex.
Together with `heis_nomizu` (surjectivity: every closed periodic cochain is cohomologous to its average) the inclusion is an isomorphism on cohomology with inverse induced by `Av`.
-/

open scoped ContDiff
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

section Iso

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] (ax ay az : ℝ)

theorem heisAv_const (c : W) : heisAv ax ay az (fun _ => c) = c := by
  rw [heisAv_eq]
  simp

/-- **The averaging is a cochain map**: `Av (D u) = 𝔇 (Av u)` for periodic smooth cochains. -/
theorem heisAv_Dop (T : CartanData W) (hax : ax ≠ 0) (hay : ay ≠ 0) (haz : az ≠ 0)
    (hD2 : ∀ u : Pt → W, ContDiff ℝ ∞ u → Dop T (Dop T u) = 0) {u : Pt → W} (hu : u ∈ C1 ax ay az) :
    heisAv ax ay az (Dop T u) = T.D0 (heisAv ax ay az u) := by
  let SZ := stepZ ax ay az T haz hD2
  let SY := stepY ax ay az T hay hD2
  let SX := stepX ax ay az T hax hD2
  have u2m : avD e3 az u ∈ C2 ax ay az := SZ.avOut u hu
  have u3m : avD e2 ay (avD e3 az u) ∈ C3 ax ay az := SY.avOut _ u2m
  have u4m : avD e1 ax (avD e2 ay (avD e3 az u)) ∈ C4 ax ay az := SX.avOut _ u3m
  have hconst : avD e1 ax (avD e2 ay (avD e3 az u)) = fun _ => heisAv ax ay az u := by
    funext p
    exact C4_const ax ay az u4m p
  have h1 : Dop T (avD e3 az u) = avD e3 az (Dop T u) := SZ.avD_Dop hu
  have h2 : Dop T (avD e2 ay (avD e3 az u)) = avD e2 ay (Dop T (avD e3 az u)) := SY.avD_Dop u2m
  have h3 : Dop T (avD e1 ax (avD e2 ay (avD e3 az u))) =
      avD e1 ax (Dop T (avD e2 ay (avD e3 az u))) := SX.avD_Dop u3m
  have h4 : Dop T (avD e1 ax (avD e2 ay (avD e3 az u))) =
      avD e1 ax (avD e2 ay (avD e3 az (Dop T u))) := by
    rw [h3, h2, h1]
  rw [hconst, Dop_const] at h4
  have := congrFun h4 0
  simpa [heisAv] using this.symm

/-- **Injectivity of the inclusion `ι` on cohomology**: a constant cochain which is a coboundary of a periodic cochain
is a coboundary of the Lie algebra complex (`Av ∘ ι = I` and `Av` is a cochain map). -/
theorem heis_inclusion_injective (T : CartanData W) (hax : ax ≠ 0) (hay : ay ≠ 0) (haz : az ≠ 0)
    (hD2 : ∀ u : Pt → W, ContDiff ℝ ∞ u → Dop T (Dop T u) = 0) {η : Pt → W} (hη : η ∈ C1 ax ay az) {c : W}
    (h : Dop T η = fun _ => c) : c = T.D0 (heisAv ax ay az η) := by
  have := heisAv_Dop ax ay az T hax hay haz hD2 hη
  rw [h, heisAv_const] at this
  exact this

end Iso

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
