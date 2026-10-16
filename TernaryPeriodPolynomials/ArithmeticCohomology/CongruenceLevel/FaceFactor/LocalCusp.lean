module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.EdgeToCusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.SlantExt

@[expose] public section


/-!
# The local term at a cusp: a flag primitive determines the Koszul term (M3c(iii), lines and planes)

Formalized by Claude Sonnet 5.5.

For a normal-form cocycle `z` and a 1-cochain `w : E → W` which is a primitive of `z` on the flag group `inl N · ⟨s σ⟩` (relations `hR1`-`hR3`), `φ = w ∘ inl` is a radical
cocycle and `c̃σ = σ·φ - φ - d(w(s σ))` (`edge_eq_of_primitive`).  At a cusp `c` fixed by `σ` (`gammaEquiv σ = cuspSigma c`) the edge cocycle is `(1 - σ)(Φ c + v)` (`edge_val_cusp`).
`local_cusp_line`: `altForm (w|_N) (c̃'σ) e₁ e₂ = -⟨Φ c + v, C'σ⟩`; `local_cusp_plane`: `altForm (c̃σ) (σ·φ') e₁ e₂ = +⟨Φ c + v, C'σ⟩`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open CongruenceSubgroup
open scoped Classical MatrixGroups

variable {N : ℕ}

/-- **The edge cocycle at a cusp fixed by `σ`**: `C σ = (1 - σ)(Φ c + v)`. -/
theorem edge_val_cusp (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) (C : groupCohomology.cocycles₁ V)
    (Φ : Tw (transRep hN V).ρ) (v : V)
    (hC : ∀ g : Gamma N, C.1 g = fTw (transRep hN V) Φ.1 (gammaEquiv hN g) + (v - V.ρ g v))
    (c : RationalLine2) (σ : Gamma N) (hσ : gammaEquiv hN σ = cuspSigma c) :
    C.1 σ = (Φ.1 c + v) - V.ρ σ (Φ.1 c + v) := by
  have h1 := fTw_twisted (transRep hN V) Φ.2 (gammaEquiv hN σ) c
  have hfix : ((gammaEquiv hN σ : gammaNGL N) : IntegralGL) • c = c := by rw [hσ]; exact cuspSigma_cusp c
  rw [hfix, transRep_ρ, MulEquiv.symm_apply_apply] at h1
  rw [hC σ, map_add]
  have h2 : fTw (transRep hN V) Φ.1 (gammaEquiv hN σ) = Φ.1 c - V.ρ σ (Φ.1 c) := by
    exact eq_sub_of_add_eq' h1.symm
  rw [h2]
  abel

section Flag

variable {N E L : Type} [Group N] [Group E] [Group L] {ext : GroupExtension N E L} (s : ext.Splitting) (W : Rep ℂ E)

/-- The radical cocycle `φ = w ∘ inl` of a 1-cochain `w` satisfying the cocycle relation on the radical. -/
def flagRadCocycle (w : E → W)
    (hR1 : ∀ r r' : N, W.ρ (ext.inl r) (w (ext.inl r')) - w (ext.inl r * ext.inl r') + w (ext.inl r) = 0) :
    groupCohomology.cocycles₁ (Rep.res ext.inl W) :=
  ⟨fun r => w (ext.inl r), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro r r'
    have h := hR1 r r'
    change w (ext.inl (r * r')) = W.ρ (ext.inl r) (w (ext.inl r')) + w (ext.inl r)
    rw [map_mul]
    linear_combination (norm := abel) -h⟩

theorem flagRadCocycle_apply (w : E → W)
    (hR1 : ∀ r r' : N, W.ρ (ext.inl r) (w (ext.inl r')) - w (ext.inl r * ext.inl r') + w (ext.inl r) = 0) (r : N) :
    flagRadCocycle W w hR1 r = w (ext.inl r) := rfl

/-- **`c̃σ = σ·φ - φ - d(w(sσ))`** for a primitive `w` of a normal-form cocycle on the flag group. -/
theorem edge_eq_of_primitive (z : relativeTwoCocycles ext.inl W)
    (hmix : ∀ (r : N) (l : L), z.val (ext.inl r, s l) = 0) (σ : L) (w : E → W)
    (hR1 : ∀ r r' : N, W.ρ (ext.inl r) (w (ext.inl r')) - w (ext.inl r * ext.inl r') + w (ext.inl r) = 0)
    (hR2 : ∀ r : N, W.ρ (ext.inl r) (w (s σ)) - w (ext.inl r * s σ) + w (ext.inl r) = 0)
    (hR3 : ∀ r : N, W.ρ (s σ) (w (ext.inl r)) - w (s σ * ext.inl r) + w (s σ) = z.val (s σ, ext.inl r)) :
    splitEdgeCycle s W σ z = splitRadicalCocycleAction s W σ (flagRadCocycle W w hR1) - flagRadCocycle W w hR1 -
      oneBoundaryCycle (Rep.res ext.inl W) (w (s σ)) := by
  apply groupCohomology.cocycles₁_ext
  intro r'
  have h3 := hR3 (splitRadicalInput s σ r')
  have h2 := hR2 r'
  rw [splitRadicalInput_commute s σ r'] at h2
  have h4 := hmix r' σ
  change z.val (s σ, ext.inl (splitRadicalInput s σ r')) - z.val (ext.inl r', s σ) =
    W.ρ (s σ) (w (ext.inl (splitRadicalInput s σ r'))) - w (ext.inl r') -
    (W.ρ (ext.inl r') (w (s σ)) - w (s σ))
  linear_combination (norm := abel) -h3 + h2 - h4

/-- **Class of the edge of a flag primitive**: `σ[φ] - [φ] = [c̃σ]`. -/
theorem flag_class_relation (z : relativeTwoCocycles ext.inl W)
    (hmix : ∀ (r : N) (l : L), z.val (ext.inl r, s l) = 0) (σ : L) (w : E → W)
    (hR1 : ∀ r r' : N, W.ρ (ext.inl r) (w (ext.inl r')) - w (ext.inl r * ext.inl r') + w (ext.inl r) = 0)
    (hR2 : ∀ r : N, W.ρ (ext.inl r) (w (s σ)) - w (ext.inl r * s σ) + w (ext.inl r) = 0)
    (hR3 : ∀ r : N, W.ρ (s σ) (w (ext.inl r)) - w (s σ * ext.inl r) + w (s σ) = z.val (s σ, ext.inl r)) :
    splitRadicalH1Action s W σ (groupCohomology.H1π _ (flagRadCocycle W w hR1)) -
        groupCohomology.H1π _ (flagRadCocycle W w hR1) =
      groupCohomology.H1π _ (splitEdgeCycle s W σ z) := by
  rw [edge_eq_of_primitive s W z hmix σ w hR1 hR2 hR3, map_sub, map_sub, oneBoundaryCycle_H1_zero,
    splitRadicalH1Action_apply, sub_zero]

end Flag

section Pairing

variable {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)} (s : ext.Splitting) (W : Rep ℂ E)
  [FiniteDimensional ℂ W]

/-- **Fixed class**: if `σ[φ] - [φ] = X - σX` then `[φ] + X` is `σ`-fixed, and the invariant coupling kills `(1 - σ)Y'`
against it. -/
theorem coupling_alt_of_primitive (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (σ : Gamma N)
    (P X : groupCohomology.H1 (Rep.res ext.inl W)) (Y' : groupCohomology.H1 (Rep.res ext.inl (dualRepG W)))
    (hP : splitRadicalH1Action s W σ P - P = X - splitRadicalH1Action s W σ X) :
    radPairingOf (ext := ext) (perfectInv_dual W) P (Y' - splitRadicalH1Action s (dualRepG W) σ Y') =
      -radPairingOf (ext := ext) (perfectInv_dual W) X (Y' - splitRadicalH1Action s (dualRepG W) σ Y') := by
  have hfix : splitRadicalH1Action s W σ (P + X) = P + X := by
    rw [map_add]
    linear_combination (norm := abel) hP
  have h1 : radPairingOf (ext := ext) (perfectInv_dual W) (P + X) (splitRadicalH1Action s (dualRepG W) σ Y') =
      radPairingOf (ext := ext) (perfectInv_dual W) (P + X) Y' := by
    have := radPairingOf_levi (ext := ext) (perfectInv_dual W) s σ (hdet σ) (P + X) Y'
    rwa [hfix] at this
  simp only [map_add, map_sub, LinearMap.add_apply] at h1 ⊢
  linear_combination (-1 : ℂ) * h1

/-- **Local cusp, lines (iii)**: for a flag primitive `w` of the normal-form cocycle `z`, and classes `X`, `Y'` with
`C σ = (1-σ)X`, `C' σ = (1-σ)Y'`, the alternating form of `(w∘inl, c̃'σ)` on `(e₁, e₂)` is `-⟨X, C'σ⟩`. -/
theorem local_cusp_line_gen (hN : 3 ≤ N) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1)
    (z : relativeTwoCocycles ext.inl W) (z' : relativeTwoCocycles ext.inl (dualRepG W))
    (hmix : ∀ (r : RadicalLattice) (l : Gamma N), z.val (ext.inl r, s l) = 0) (σ : Gamma N) (w : E → W)
    (hR1 : ∀ r r' : RadicalLattice,
      W.ρ (ext.inl r) (w (ext.inl r')) - w (ext.inl r * ext.inl r') + w (ext.inl r) = 0)
    (hR2 : ∀ r : RadicalLattice, W.ρ (ext.inl r) (w (s σ)) - w (ext.inl r * s σ) + w (ext.inl r) = 0)
    (hR3 : ∀ r : RadicalLattice,
      W.ρ (s σ) (w (ext.inl r)) - w (s σ * ext.inl r) + w (s σ) = z.val (s σ, ext.inl r))
    (X : splitRadicalH1Representation s W)
    (hX : (splitCocycleEdge s W z).1 σ = X - (splitRadicalH1Representation s W).ρ σ X)
    (Y' : splitRadicalH1Representation s (dualRepG W))
    (hY' : (splitCocycleEdge s (dualRepG W) z').1 σ = Y' - (splitRadicalH1Representation s (dualRepG W)).ρ σ Y') :
    altForm (Rep.res ext.inl (dualRepG W)).ρ (Module.Dual.eval ℂ W) (fun u => w (ext.inl u))
        (fun r => splitEdgeCycle s (dualRepG W) σ z' r) latE1 latE2 =
      -(leviCoupling hN s hdet W).e X ((splitCocycleEdge s (dualRepG W) z').1 σ) := by
  have hP := flag_class_relation s W z hmix σ w hR1 hR2 hR3
  have hP' : splitRadicalH1Action s W σ (groupCohomology.H1π _ (flagRadCocycle W w hR1)) -
      groupCohomology.H1π _ (flagRadCocycle W w hR1) =
        (id X : groupCohomology.H1 (Rep.res ext.inl W)) - splitRadicalH1Action s W σ X := by
    rw [hP, ← splitCocycleEdge_val]
    exact hX
  have key := coupling_alt_of_primitive s W hdet σ _ X Y' hP'
  have e1 : altForm (Rep.res ext.inl (dualRepG W)).ρ (Module.Dual.eval ℂ W) (fun u => w (ext.inl u))
        (fun r => splitEdgeCycle s (dualRepG W) σ z' r) latE1 latE2 =
      radPairingOf (ext := ext) (perfectInv_dual W) (groupCohomology.H1π _ (flagRadCocycle W w hR1))
        (groupCohomology.H1π _ (splitEdgeCycle s (dualRepG W) σ z')) := by
    rw [radPairingOf_spec]
    rfl
  have e2 : groupCohomology.H1π _ (splitEdgeCycle s (dualRepG W) σ z') =
      (id Y' : groupCohomology.H1 (Rep.res ext.inl (dualRepG W))) - splitRadicalH1Action s (dualRepG W) σ Y' := by
    rw [← splitCocycleEdge_val]
    exact hY'
  rw [e1, e2, hY']
  exact key

/-- **Local cusp, lines**: the statements (i)-(iii) with the cusp data `C = fTw Φ + (v - ρ v)` of `edge_pairing_cusp_sum` for `z` and
`C' = fTw Φ' + (v' - ρ' v')` for `z'`, at an element `σ` of `Γ(N)` fixing the cusp `c`. -/
theorem local_cusp_line (hN : 3 ≤ N) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1)
    (z : relativeTwoCocycles ext.inl W) (z' : relativeTwoCocycles ext.inl (dualRepG W))
    (hmix : ∀ (r : RadicalLattice) (l : Gamma N), z.val (ext.inl r, s l) = 0) (σ : Gamma N) (w : E → W)
    (hR1 : ∀ r r' : RadicalLattice,
      W.ρ (ext.inl r) (w (ext.inl r')) - w (ext.inl r * ext.inl r') + w (ext.inl r) = 0)
    (hR2 : ∀ r : RadicalLattice, W.ρ (ext.inl r) (w (s σ)) - w (ext.inl r * s σ) + w (ext.inl r) = 0)
    (hR3 : ∀ r : RadicalLattice,
      W.ρ (s σ) (w (ext.inl r)) - w (s σ * ext.inl r) + w (s σ) = z.val (s σ, ext.inl r))
    (Φ : Tw (transRep hN (splitRadicalH1Representation s W)).ρ) (v : splitRadicalH1Representation s W)
    (hCΦ : ∀ g : Gamma N, (splitCocycleEdge s W z).1 g =
      fTw (transRep hN (splitRadicalH1Representation s W)) Φ.1 (gammaEquiv hN g) +
        (v - (splitRadicalH1Representation s W).ρ g v))
    (Φ' : Tw (transRep hN (splitRadicalH1Representation s (dualRepG W))).ρ)
    (v' : splitRadicalH1Representation s (dualRepG W))
    (hCΦ' : ∀ g : Gamma N, (splitCocycleEdge s (dualRepG W) z').1 g =
      fTw (transRep hN (splitRadicalH1Representation s (dualRepG W))) Φ'.1 (gammaEquiv hN g) +
        (v' - (splitRadicalH1Representation s (dualRepG W)).ρ g v'))
    (c : RationalLine2) (hσ : gammaEquiv hN σ = cuspSigma c) :
    altForm (Rep.res ext.inl (dualRepG W)).ρ (Module.Dual.eval ℂ W) (fun u => w (ext.inl u))
        (fun r => splitEdgeCycle s (dualRepG W) σ z' r) latE1 latE2 =
      -(leviCoupling hN s hdet W).e (Φ.1 c + v) ((splitCocycleEdge s (dualRepG W) z').1 σ) :=
  local_cusp_line_gen s W hN hdet z z' hmix σ w hR1 hR2 hR3 (Φ.1 c + v)
    (edge_val_cusp hN _ _ Φ v hCΦ c σ hσ) (Φ'.1 c + v')
    (edge_val_cusp hN _ _ Φ' v' hCΦ' c σ hσ)

end Pairing

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
