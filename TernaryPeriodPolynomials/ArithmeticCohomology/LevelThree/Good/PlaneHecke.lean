module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneHeckeCoord
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1

@[expose] public section


/-!
# The local `T_p` at the good plane is `1 + p^{-(n+2)} T_p^{Γ₁'(3)}` on the edge

For the explicit local correspondence `goodPlaneCosets p hp3` of the good-plane stabilizer
`ΛG = {P(b, κ(m), d) : b ∈ ℤ², m ∈ Γ₁'(3), d = ±1}` (`1 + p + p²` cosets: `σ₀ = diag(1, 1, ±p)`
and `u(w_{j,r}) diag(B_j, 1)`), the good-plane edge into `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`
(`GoodPlaneEdge3.goodPlaneEdgeH2`) intertwines the local Hecke operator with
`1 + p^{-(n+2)} T_p`, where `T_p = LevelThreeHeckeH1.levelHecke` is the cohomological Hecke operator
of `Γ₁'(3) diag(p, 1) Γ₁'(3)`:

* `rho_rep_inv`: `σ(α_j)⁻¹ ∘ Φ = p^{n+3} Φ ∘ A_{B_j}` on `Sym^{n+1} ⊗ det⁻¹`, where
  `B_j = p (δ⁻¹ α_j δ)⁻¹` and `Φ = Sym^{n+1}(δ)` is the coordinate transport of the edge;
* `goodPlaneEdgeCocycle_hecke`: the cocycle-level identity
  `E(T c) = E(c) + p^{-(n+2)} T_p E(c)` for relative cocycles `c`;
* `goodPlaneEdgeH2_hecke`: the class-level identity on `H²(ΛG, Sym^n)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneHecke

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets (p_ne_zero)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.AmbientHecke
  (liftCocycle ambientCocycleToGroup_lift ambientHecke_congr)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (del ΛG)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
  (goodPlaneExtension coefRep)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot (qcls qcls_add qcls_smul)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneCosetData (BG)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneCosets
  (goodPlaneCosets sc sc_inv_comm alphaK BG_inv_eq_sc)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
  (Phi edgeVal goodPlaneEdgeCocycle goodPlaneEdgeCocycle_apply)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
  (goodPlaneEdgeH2 goodPlaneEdgeH2_apply ambientEdgeKer)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneHeckeCoord
  (heckeRel edgeVal_hecke)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
  (rationalRho level_compat crossedHeckeCocycles levelHecke levelHecke_mk
    levelHeckeCocycles_apply)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
  (heckeRep levelCosets levelEmbed_injective levelDelta)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

/-! ### The coordinate transport of the Hecke representatives -/

section Rho

variable (n : ℕ) (p : Nat.Primes)

theorem rho_mul_apply (g h : GL (Fin 2) ℚ) (w : Binary.HomogeneousPoly (n + 1)) :
    rationalRho (n + 1) (-1) (g * h) w =
      rationalRho (n + 1) (-1) g (rationalRho (n + 1) (-1) h w) := by
  rw [map_mul, Module.End.mul_apply]

theorem rho_inv_apply (g : GL (Fin 2) ℚ) (w : Binary.HomogeneousPoly (n + 1)) :
    rationalRho (n + 1) (-1) g⁻¹ (rationalRho (n + 1) (-1) g w) = w := by
  rw [← rho_mul_apply, inv_mul_cancel, map_one, Module.End.one_apply]

/-- `σ((p·1)⁻¹) = p^{n+3}` on `Sym^{n+1} ⊗ det⁻¹`. -/
theorem rho_sc_inv (v : Binary.HomogeneousPoly (n + 1)) :
    rationalRho (n + 1) (-1) (sc p)⁻¹ v = ((p.val : ℂ) ^ (n + 3)) • v := by
  have hs : (sc p)⁻¹ =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p.val : ℚ) (p_ne_zero p))⁻¹ :=
    (map_inv (GeneralLinearGroup.scalar (Fin 2)) (Units.mk0 (p.val : ℚ) (p_ne_zero p))).symm
  rw [hs]
  change Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ)
    (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p.val : ℚ) (p_ne_zero p))⁻¹)) v = _
  rw [GeneralLinearGroup.map_scalar]
  refine (binary_homogeneousAction_scalar v _).trans ?_
  congr 1
  simp

theorem Phi_eq (w : Binary.HomogeneousPoly (n + 1)) :
    Phi n w = rationalRho (n + 1) (-1) del w := rfl

/-- `α_j⁻¹ = p⁻¹ δ B_j δ⁻¹` in `GL₂(ℚ)`. -/
theorem heckeRep_inv (j : Option (Fin p.val)) :
    (heckeRep p j)⁻¹ = (sc p)⁻¹ * (del * BG p j * del⁻¹) := by
  have e1 : heckeRep p j = del * alphaK p j * del⁻¹ := by
    unfold alphaK
    group
  have hA : alphaK p j = sc p * (BG p j)⁻¹ := by
    rw [BG_inv_eq_sc, mul_inv_cancel_left]
  rw [e1, hA]
  calc (del * (sc p * (BG p j)⁻¹) * del⁻¹)⁻¹ = (del * BG p j) * (sc p)⁻¹ * del⁻¹ := by group
    _ = (sc p)⁻¹ * (del * BG p j) * del⁻¹ := by rw [← sc_inv_comm p (del * BG p j)]
    _ = (sc p)⁻¹ * (del * BG p j * del⁻¹) := by group

/-- **`ρ(α_j)⁻¹ = p^{n+3} ρ(B_j)` on `Sym^{n+1} ⊗ det⁻¹`**, in the transported coordinates:
`σ(α_j)⁻¹ Φ w = p^{n+3} Φ (A_{B_j} w)`. -/
theorem rho_rep_inv (j : Option (Fin p.val)) (w : Binary.HomogeneousPoly (n + 1)) :
    rationalRho (n + 1) (-1) (heckeRep p j)⁻¹ (Phi n w) =
      ((p.val : ℂ) ^ (n + 3)) • Phi n (Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) (BG p j)) w) := by
  change rationalRho (n + 1) (-1) (heckeRep p j)⁻¹ (rationalRho (n + 1) (-1) del w) =
    ((p.val : ℂ) ^ (n + 3)) • rationalRho (n + 1) (-1) del
      (rationalRho (n + 1) (-1) (BG p j) w)
  rw [heckeRep_inv p j, rho_mul_apply, rho_mul_apply, rho_mul_apply, rho_inv_apply,
    rho_sc_inv]

theorem cast_p : (((p.val : ℚ) : ℂ)) = ((p.val : ℂ) ^ (n + 2))⁻¹ * (p.val : ℂ) ^ (n + 3) := by
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  field_simp
  push_cast
  ring

/-- The termwise identity behind `goodPlaneEdgeCocycle_hecke`. -/
theorem term_eq (j : Option (Fin p.val)) (w : Binary.HomogeneousPoly (n + 1)) :
    ((p.val : ℚ) : ℂ) • Phi n (Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) (BG p j)) w) =
      ((p.val : ℂ) ^ (n + 2))⁻¹ • rationalRho (n + 1) (-1) (heckeRep p j)⁻¹ (Phi n w) := by
  rw [rho_rep_inv, smul_smul, ← cast_p n p]

end Rho

/-! ### The cocycle-level identity -/

section Cocycle

variable (n : ℕ) (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The Hecke operator of `Γ₁'(3) diag(p, 1) Γ₁'(3)` on crossed cocycles. -/
abbrev levelT :
    crossedCocycles (levelRep (n + 1) (-1)) →ₗ[ℂ] crossedCocycles (levelRep (n + 1) (-1)) :=
  crossedHeckeCocycles (levelCosets p hp3) (rationalRho (n + 1) (-1)) (levelRep (n + 1) (-1))
    (level_compat (n + 1) (-1)) levelEmbed_injective

theorem levelT_apply (c' : crossedCocycles (levelRep (n + 1) (-1))) (m : binaryArithmeticLevel) :
    (levelT n p hp3 c').val m = ∑ j : Option (Fin p.val),
      rationalRho (n + 1) (-1) (heckeRep p j)⁻¹ (c'.val (levelDelta p hp3 m j)) :=
  levelHeckeCocycles_apply (n + 1) (-1) p hp3 c' m

/-- **Cocycle-level identity**: `E(T c) = E(c) + p^{-(n+2)} T_p E(c)`. -/
theorem goodPlaneEdgeCocycle_hecke (c : GoodPlaneHeckeCoord.Rel n) :
    goodPlaneEdgeCocycle (heckeRel p hp3 c) = goodPlaneEdgeCocycle c +
      ((p.val : ℂ) ^ (n + 2))⁻¹ • levelT n p hp3 (goodPlaneEdgeCocycle c) := by
  apply Subtype.ext
  funext m
  change Phi n (edgeVal (heckeRel p hp3 c) (m, 1)) = Phi n (edgeVal c (m, 1)) +
    ((p.val : ℂ) ^ (n + 2))⁻¹ • (levelT n p hp3 (goodPlaneEdgeCocycle c)).val m
  rw [levelT_apply, edgeVal_hecke, map_add, map_smul, map_sum]
  simp only [goodPlaneEdgeCocycle_apply]
  refine congrArg (fun x => Phi n (edgeVal c (m, 1)) + x) ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j _ => term_eq n p j _)

end Cocycle

/-! ### The class-level identity -/

section Class

variable (p : Nat.Primes) (hp3 : p.val ≠ 3) {n : ℕ}

/-- **The local Hecke operator of the good plane, identified.** On `H²(ΛG, Sym^n)` (`n > 0`), the
good-plane edge intertwines the local Hecke operator of the explicit correspondence
`goodPlaneCosets p hp3` with `1 + p^{-(n+2)} T_p`, `T_p` the Hecke operator of
`Γ₁'(3) diag(p, 1) Γ₁'(3)` on `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`. -/
theorem goodPlaneEdgeH2_hecke (hn : 0 < n) (x : H2 ΛG (ρn n)) :
    goodPlaneEdgeH2 hn (LocalHecke.cohomologyAction (ρn n) (goodPlaneCosets p hp3) x) =
      goodPlaneEdgeH2 hn x + ((p.val : ℂ) ^ (n + 2))⁻¹ •
        levelHecke (n + 1) (-1) p hp3 (goodPlaneEdgeH2 hn x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  obtain ⟨c, hc⟩ := relativeTwoCocycleClass_surjective goodPlaneExtension.inl
    goodPlaneExtension.inl_injective (coefRep n) (ambientEdgeKer hn C)
  have hc' : groupCohomology.H2π (coefRep n) c.val =
      groupCohomology.H2π (coefRep n) (ambientCocycleToGroup ΛG (ρn n) C) :=
    congrArg Subtype.val hc
  have hcongr := ambientHecke_congr (goodPlaneCosets p hp3) (ρn n) C
    (liftCocycle (goodPlaneCosets p hp3) (ρn n) c.val)
    (by rw [ambientCocycleToGroup_lift]; exact hc'.symm)
  have h1 : goodPlaneEdgeH2 hn (classOf ΛG (ρn n) C) =
      qcls (levelRep (n + 1) (-1)) (goodPlaneEdgeCocycle c) :=
    goodPlaneEdgeH2_apply hn C c hc'
  have h2 : goodPlaneEdgeH2 hn
      (classOf ΛG (ρn n) (LocalHecke.cocycleAction (ρn n) (goodPlaneCosets p hp3) C)) =
      qcls (levelRep (n + 1) (-1))
        (goodPlaneEdgeCocycle (heckeRel p hp3 c)) :=
    goodPlaneEdgeH2_apply hn _ (heckeRel p hp3 c) hcongr.symm
  have key : levelHecke (n + 1) (-1) p hp3
      (qcls (levelRep (n + 1) (-1)) (goodPlaneEdgeCocycle c)) =
      qcls (levelRep (n + 1) (-1)) (levelT n p hp3 (goodPlaneEdgeCocycle c)) :=
    levelHecke_mk (n + 1) (-1) p hp3 (goodPlaneEdgeCocycle c)
  change goodPlaneEdgeH2 hn (LocalHecke.cohomologyAction (ρn n) (goodPlaneCosets p hp3)
      (classOf ΛG (ρn n) C)) = goodPlaneEdgeH2 hn (classOf ΛG (ρn n) C) +
    ((p.val : ℂ) ^ (n + 2))⁻¹ • levelHecke (n + 1) (-1) p hp3
      (goodPlaneEdgeH2 hn (classOf ΛG (ρn n) C))
  rw [LocalHecke.cohomologyAction_classOf, h2, h1, goodPlaneEdgeCocycle_hecke, qcls_add,
    qcls_smul, key]

end Class

end TernaryPeriodPolynomials.LevelThree.GoodPlaneHecke
