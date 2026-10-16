module

public import TernaryPeriodPolynomials.GroupCohomology.Homology.ShapiroInv
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Induced

@[expose] public section


/-!
# The Shapiro isomorphism for the residue module is inverse to the map induced by `lof`

`shapiroHomologyIso_inv`: the inverse of `shapiroHomologyIso n k : H_k(G, 𝓡_n) ≅ H_k(P_H, 𝓡_{n,H₀})` is
`groupHomology.map PH.subtype (lofHom n) k`, the corestriction along `P_H ↪ G` of the map induced by the inclusion
`lof_{H₀} : 𝓡_{n,H₀} → Res_{P_H} 𝓡_n` of the `H₀`-summand (from `GroupHomology.indIso_inv_eq_map`).  This is the form in which
the geometry of the Borel-Serre boundary sees `Sh`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory TernaryPoly TernaryPoly.ModThreeGoodAction
open TernaryPeriodPolynomials.Argument.GroupHomology

attribute [local instance] Classical.propDecidable

theorem indToRes_unit (n : ℕ) :
    indUnit PH (FibRep n) ≫ (Rep.resFunctor PH.subtype).map (indToRes n) = lofHom n := by
  have h := (Rep.indResAdjunction.{0, 0, 0} ℚ PH.subtype).homEquiv_unit (f := indToRes n)
  refine h.symm.trans ?_
  exact (Rep.indResHomEquiv PH.subtype (FibRep n) (ResRep n)).apply_symm_apply (lofHom n)

theorem shapiroHomologyIso_inv (n k : ℕ) :
    (shapiroHomologyIso n k).inv = groupHomology.map PH.subtype (lofHom n) k := by
  have h1 : (shapiroHomologyIso n k).inv = (groupHomology.indIso PH (FibRep n) k).inv ≫
      groupHomology.map (MonoidHom.id IntegralGL) (indToRes n) k := rfl
  rw [h1, indIso_inv_eq_map]
  have h2 := groupHomology.map_comp (k := ℚ) (C := ResRep n) PH.subtype (MonoidHom.id IntegralGL)
    (indUnit PH (FibRep n))
    (show Rep.ind PH.subtype (FibRep n) ⟶ Rep.res (MonoidHom.id IntegralGL) (ResRep n) from indToRes n) k
  rw [← h2]
  exact groupHomology.map_congr (MonoidHom.id_comp _) (by rw [indToRes_unit]) k

end TernaryPeriodPolynomials.Argument.AppendixBResidue
