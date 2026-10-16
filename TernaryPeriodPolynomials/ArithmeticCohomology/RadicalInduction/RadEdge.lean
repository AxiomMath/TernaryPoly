module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadFace

@[expose] public section


/-!
# The Hochschild-Serre edge of induced classes and the canonical face pairing

Formalized by Claude Sonnet 5.5.

For a class `z ∈ H²(S, Fun(S/Stab, E))` restricting to zero on the radical, `kerMapW z` is its pull-back along `α` followed by evaluation at the base point (`EdgeNat.kerMap`: the class of `H²(E₂, E)` of the induced
class in the sense of Shapiro's lemma), and `phiRad_edge` says `H¹(ι, phiRad)(edge z) = edge(kerMapW z)`.  **`facePairingCan_ind_edge`**: for classes `z`, `z'` (coefficients `Fun(S/Stab, E)` and its contragredient) with
cuspidal edges, `facePairingCan(edge z, edge z') = facePairingCan(edge(kerMapW z), edge(kerMapWD z'))`, with the constant exactly `1`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open scoped Classical

variable {S E₂ : Type} [Group S] [Group E₂] {N M : ℕ} {ext : GroupExtension RadicalLattice S (Gamma N)} {s : ext.Splitting}
  {Stab : Subgroup S} {α : E₂ →* S} {ext' : GroupExtension RadicalLattice E₂ (Gamma M)} {s' : ext'.Splitting}
  {hle : Gamma M ≤ Gamma N} {m0 : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

variable (hc : Compat ext s Stab α ext' s' (Subgroup.inclusion hle) m0) (ρ : Representation ℂ S E)

/-- The pull-back to `E₂` and evaluation at the base point, on the classes with vanishing radical restriction. -/
def kerMapW : (twoCohomologyRestriction ext.inl (WI ext Stab ρ)).ker →ₗ[ℂ]
    (twoCohomologyRestriction ext'.inl (AS α ρ)).ker :=
  EdgeNat.kerMap α (powMonoidHom m0) hc.inl_eq (WI ext Stab ρ) (AS α ρ) (evT ext Stab α ρ) (evT_hT α hc.mem_stab ρ)

/-- The same for the contragredient coefficients. -/
def kerMapWD : (twoCohomologyRestriction ext.inl (dualRepG (WI ext Stab ρ))).ker →ₗ[ℂ]
    (twoCohomologyRestriction ext'.inl (dualRepG (AS α ρ))).ker :=
  EdgeNat.kerMap α (powMonoidHom m0) hc.inl_eq (dualRepG (WI ext Stab ρ)) (dualRepG (AS α ρ)) (evTD ext Stab α ρ)
    (evTD_hT hc.mem_stab ρ)

theorem phiRad_edge (z : (twoCohomologyRestriction ext.inl (WI ext Stab ρ)).ker) :
    mapH1 hle (phiRad hc ρ) (splitCohomologyEdge s (WI ext Stab ρ) z) =
      splitCohomologyEdge s' (AS α ρ) (kerMapW hc ρ z) :=
  (EdgeNat.edge_kerMap s s' α (Subgroup.inclusion hle) (powMonoidHom m0) hc.inl_eq hc.split_eq (WI ext Stab ρ) (AS α ρ)
    (evT ext Stab α ρ) (evT_hT α hc.mem_stab ρ) z).symm

theorem phiRadD_edge (z : (twoCohomologyRestriction ext.inl (dualRepG (WI ext Stab ρ))).ker) :
    mapH1 hle (phiRadD hc ρ) (splitCohomologyEdge s (dualRepG (WI ext Stab ρ)) z) =
      splitCohomologyEdge s' (dualRepG (AS α ρ)) (kerMapWD hc ρ z) :=
  (EdgeNat.edge_kerMap s s' α (Subgroup.inclusion hle) (powMonoidHom m0) hc.inl_eq hc.split_eq (dualRepG (WI ext Stab ρ))
    (dualRepG (AS α ρ)) (evTD ext Stab α ρ) (evTD_hT hc.mem_stab ρ) z).symm

variable [hN : Fact (3 ≤ N)] (hM : 3 ≤ M)

include hc hM in
theorem edge_kerMapW_mem (z : (twoCohomologyRestriction ext.inl (WI ext Stab ρ)).ker)
    (hz : splitCohomologyEdge s (WI ext Stab ρ) z ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (WI ext Stab ρ))) :
    splitCohomologyEdge s' (AS α ρ) (kerMapW hc ρ z) ∈ cuspidalSubspace (Gamma M) (splitRadicalH1Representation s' (AS α ρ)) := by
  rw [← phiRad_edge]
  exact mapH1_mem hM hle (phiRad hc ρ) ⟨_, hz⟩

include hc hM in
theorem edge_kerMapWD_mem (z : (twoCohomologyRestriction ext.inl (dualRepG (WI ext Stab ρ))).ker)
    (hz : splitCohomologyEdge s (dualRepG (WI ext Stab ρ)) z ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG (WI ext Stab ρ)))) :
    splitCohomologyEdge s' (dualRepG (AS α ρ)) (kerMapWD hc ρ z) ∈
      cuspidalSubspace (Gamma M) (splitRadicalH1Representation s' (dualRepG (AS α ρ))) := by
  rw [← phiRadD_edge]
  exact mapH1_mem hM hle (phiRadD hc ρ) ⟨_, hz⟩

variable (hdet' : ∀ A, radDet (splitRadicalInput s' A) = 1)

include hc hM hdet' in
/-- **The canonical face pairing of the edges of induced mixed classes, with the constant `1`.** -/
theorem facePairingCan_ind_edge [NeZero m0] [Fintype (YN ext Stab)] [Fintype (Gamma N ⧸ subM N M)] [FiniteDimensional ℂ E]
    (z : (twoCohomologyRestriction ext.inl (WI ext Stab ρ)).ker)
    (z' : (twoCohomologyRestriction ext.inl (dualRepG (WI ext Stab ρ))).ker)
    (hz : splitCohomologyEdge s (WI ext Stab ρ) z ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (WI ext Stab ρ)))
    (hz' : splitCohomologyEdge s (dualRepG (WI ext Stab ρ)) z' ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG (WI ext Stab ρ)))) :
    facePairingCan hN.out s hc.det (WI ext Stab ρ) ⟨splitCohomologyEdge s (WI ext Stab ρ) z, hz⟩
        ⟨splitCohomologyEdge s (dualRepG (WI ext Stab ρ)) z', hz'⟩ =
      facePairingCan hM s' hdet' (AS α ρ) ⟨splitCohomologyEdge s' (AS α ρ) (kerMapW hc ρ z), edge_kerMapW_mem hc ρ hM z hz⟩
        ⟨splitCohomologyEdge s' (dualRepG (AS α ρ)) (kerMapWD hc ρ z'), edge_kerMapWD_mem hc ρ hM z' hz'⟩ := by
  rw [facePairingCan_ind hc ρ hM hdet' ⟨_, hz⟩ ⟨_, hz'⟩]
  have e1 : mapCusp hM hle (phiRad hc ρ) ⟨splitCohomologyEdge s (WI ext Stab ρ) z, hz⟩ =
      ⟨splitCohomologyEdge s' (AS α ρ) (kerMapW hc ρ z), edge_kerMapW_mem hc ρ hM z hz⟩ :=
    Subtype.ext (phiRad_edge hc ρ z)
  have e2 : mapCusp hM hle (phiRadD hc ρ) ⟨splitCohomologyEdge s (dualRepG (WI ext Stab ρ)) z', hz'⟩ =
      ⟨splitCohomologyEdge s' (dualRepG (AS α ρ)) (kerMapWD hc ρ z'), edge_kerMapWD_mem hc ρ hM z' hz'⟩ :=
    Subtype.ext (phiRadD_edge hc ρ z')
  rw [e1, e2]

end TernaryPeriodPolynomials.Argument.RadicalInduction
