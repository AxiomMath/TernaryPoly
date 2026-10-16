module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.SigmaHS
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.SigmaLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.PrimeKappa

@[expose] public section


/-!
# The `σ` double coset contributes `p · T₂(p)` under the Hochschild-Serre isomorphism

Formalized by Claude Sonnet 5.5.
Paper: "The Hecke transfer": the second family
of representatives of `diag(1,1,p)` and `diag(p,1,1)` has binary blocks `C_c`, `C_∞`; transfer contributes `e_t = p` and
the residue coefficient `det C`, so that this part of the correspondence is `p · T₂(p)`.

`sigma_term_kappa`: for the `P_H`-level correspondence `(P_H ∩ σ⁻¹ S_p σ, f₁, c₁)` of `Prime{Hecke,Cosets}.lean`,

`κ ∘ (tr ≫ H₃(f₁, c₁)) = p · T₂(p) ∘ κ`, with `T₂(p) = heckeOp (binDatum p) (binMod (n+1)) 1`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.HochschildSerre

variable {p : ℕ} [Fact p.Prime]

theorem f1_hfU (s : ↥(Psig p)) (hs : (s : PH) ∈ AppendixBResidue.U) : f1 (p := p) s ∈ AppendixBResidue.U :=
  f1_mem_U s hs

/-- **The `σ`-coset contributes `p · T₂(p)` under `κ`.** -/
theorem sigma_term_kappa (n : ℕ) (x : groupHomology (FibRep n) 3) :
    kappaLit n ((groupHomology.map (f1 (p := p)) (c1 p n) 3).hom
        ((trR (Sx PH (primeDatum p).S sigma) (FibRep n) 3).hom x)) =
      (p : ℚ) • (heckeOp (binDatum p) (binMod (n + 1)) 1).hom (kappaLit n x) := by
  have hker : (pibar.ker : Set (PH ⧸ AppendixBResidue.U)).Finite := by
    have := finite_ker_pibar; exact Set.toFinite _
  have h := hsFarey_corr (U := AppendixBResidue.U) (S := Psig p) (f := f1 (p := p)) (hfU := f1_hfU)
    (hf := f1_injective) (A := FibRep n) (c := c1 p n) (eU := AppendixBResidue.eU) (hA := fun u => FibRep_U n u) (p := p)
    (π := pibar) (hπ := pibar_surjective) (hker := hker)
    (hU3 := isZero_res_three AppendixBResidue.eU (fun u => FibRep_U n u))
    (M := binMod (n + 1)) (lin := fiberLin n) (hcompat := fun g a => fiber_compat n g a)
    (μ := muRad p) (hμ := muRad_nuU f1_hfU) (hω := by rw [omega_muRad, card_RC_U1])
    (hne := by rw [card_RC_U1]; exact_mod_cast (Fact.out : p.Prime).ne_zero)
    (hGamma := G0_mem_iff) (hchi := pibar_chi f1_hfU G0_mem_iff) (r := (p : ℚ))
    (hc := fiberLin_c1 (p := p) n) x
  exact h

end TernaryPeriodPolynomials.Argument.HeckeHomology
