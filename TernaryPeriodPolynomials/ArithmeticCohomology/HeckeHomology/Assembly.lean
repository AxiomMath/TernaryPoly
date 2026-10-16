module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.SigmaPH
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.ShapiroLof

@[expose] public section


/-!
# Lemma 4.5: `T₃(p,1) = p · T₂(p) + p² · I` on literal group homology

Formalized by Claude Sonnet 5.5.
Paper: `eq:Hecke-formula`, proof.

`hecke_formula_literal`: in the literal residue coordinate (Shapiro `shLit n` followed by the Hochschild-Serre isomorphism `kappaLit n`
of the split extension `1 → ℤ² → P_H → GL₂(ℤ) ⋉ {±1}`), the homology Hecke operator `heckeOp (primeDatum p) (residueAction n (-1)) 3`
of `g = diag(p,1,1)⁻¹` on `H₃(GL₃(ℤ), 𝓡_n)` is `p · T₂(p) + p² · I`, where `T₂(p) = hecke2 p (n+1) = heckeOp (binDatum p) (binMod (n+1)) 1`
is the homology Hecke operator of `diag(1/p, 1)` on `H₁(GL₂(ℤ), Sym^{n+1})`.  It holds for every prime `p`.  The two summands come from
the two double cosets `S_p · 1 · P_H` (identity term `p²`, `kappaLit_T3raw`) and `S_p · σ · P_H` (`sigma_term_kappa`) of
`prime_hecke_pair`.

**Which operator is `T₃(p,1)`.**  `primeDatum p` is the Hecke datum of `g = diag(p,1,1)⁻¹` for `Γ = GL₃(ℤ)`: `S_p = Γ ∩ g⁻¹Γg =
{k | p ∣ k₀₁, p ∣ k₀₂}`, `f(s) = g s g⁻¹`, coefficient transport `ρ(g)`; on `H₀` it is `[m] ↦ ∑_{S_p x ∈ S_p\Γ} [ρ(g x) m]`, a sum over the
`p²+p+1` cosets `Γ g x` of `Γ g Γ`.  The paper's modules are right modules (`D_d` "with the right substitution action", residue
fibre `q ↦ det(C) q(C(b,c))`); the left module used here is `ρ(h) m = m · h⁻¹`, so `R_n ⊗ det` (right) is `integralResidueAction n (-1)`.
For a right module the Hecke operator of the double coset of `diag(1,1,p)` on coinvariants sums `[m · h]` over the left cosets `hΓ`
(column lattices of index `p`), i.e. `[ρ(h⁻¹) m]` over right cosets of the inverse double coset: this is `heckeOp (primeDatum p)`.
The same dictionary identifies the paper's `T₂(p)` (matrices `C_c = (1 0; c p)`, `C_∞ = diag(p,1)`) with `heckeOp (binDatum p)` with no
extra scalar.  The details (and the relation `hecke2 = p^d · T_*(diag(1,p))` for the left-module reading) are in `AssemblyConventions.lean`.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly TernaryPeriodPolynomials.Argument.AppendixBResidue

variable (p : ℕ) [Fact p.Prime]

/-- **`T₂(p)`**: the homology Hecke operator of `diag(1/p, 1)` on `H₁(GL₂(ℤ), Sym^d)` (double coset of the binary datum). -/
def hecke2 (d : ℕ) : groupHomology (FareyTree.Dplain d) 1 →ₗ[ℚ] groupHomology (FareyTree.Dplain d) 1 :=
  (heckeOp (binDatum p) (binMod d) 1).hom

/-- **`eq:Hecke-formula`**: `κ ∘ Sh ∘ T₃(p,1) = (p · T₂(p) + p²) ∘ κ ∘ Sh` on `H₃(GL₃(ℤ), 𝓡_n)`. -/
theorem hecke_formula_literal (n : ℕ) (y : groupHomology (ResRep n) 3) :
    kappaLit n (shLit n ((heckeOp (primeDatum p) (Rep.of (SinglePole.residueAction n (-1))) 3).hom y)) =
      (p : ℚ) • hecke2 p (n + 1) (kappaLit n (shLit n y)) +
        ((p : ℚ) ^ 2) • kappaLit n (shLit n y) := by
  set x : groupHomology (FibRep n) 3 := shLit n y with hx
  have e1 : ∀ w, (shapiroHomologyIso n 3).hom.hom ((groupHomology.map PH.subtype (lofHom n) 3).hom w) = w := by
    intro w
    rw [← shapiroHomologyIso_inv]
    exact congrArg (fun m => m.hom w) (shapiroHomologyIso n 3).inv_hom_id
  have e2 : (groupHomology.map PH.subtype (lofHom n) 3).hom x = y := by
    rw [← shapiroHomologyIso_inv]
    exact congrArg (fun m => m.hom y) (shapiroHomologyIso n 3).hom_inv_id
  have h := congrArg (fun m => m.hom x) (prime_hecke_pair p n 3)
  have h' : (heckeOp (primeDatum p) (Rep.of (SinglePole.residueAction n (-1))) 3).hom y =
      (groupHomology.map PH.subtype (lofHom n) 3).hom
        ((groupHomology.map (f0 p) (c0 p n) 3).hom ((trR (Sx PH (primeDatum p).S 1) (FibRep n) 3).hom x)) +
      (groupHomology.map PH.subtype (lofHom n) 3).hom
        ((groupHomology.map (f1 (p := p)) (c1 p n) 3).hom ((trR (Sx PH (primeDatum p).S sigma) (FibRep n) 3).hom x)) := by
    rw [← e2]
    exact h
  have h2 : shLit n ((heckeOp (primeDatum p) (Rep.of (SinglePole.residueAction n (-1))) 3).hom y) =
      (groupHomology.map (f0 p) (c0 p n) 3).hom ((trR (Sx PH (primeDatum p).S 1) (FibRep n) 3).hom x) +
        (groupHomology.map (f1 (p := p)) (c1 p n) 3).hom ((trR (Sx PH (primeDatum p).S sigma) (FibRep n) 3).hom x) := by
    change (shapiroHomologyIso n 3).hom.hom ((heckeOp (primeDatum p) (Rep.of (SinglePole.residueAction n (-1))) 3).hom y) = _
    rw [h', map_add, e1, e1]
  rw [h2, map_add, kappaLit_T3raw p n x, sigma_term_kappa n x]
  exact add_comm _ _

end TernaryPeriodPolynomials.Argument.HeckeHomology
