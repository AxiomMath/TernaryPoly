module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

@[expose] public section


/-!
# Lemma B.1, Stage 2 preparation: `𝓡_n ≅ Ind_{P_H}^G 𝓡_{n,H₀}` as `G`-representations

Formalized by Claude Sonnet 5.5.
Paper: Lemma B.1
(`lem:literal-residue-comparison`): the Shapiro isomorphism
`H₃(P_H, 𝓡_{n,H} ⊗ det) ≅ H₃(G, 𝓡_n ⊗ det)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction CategoryTheory
open TernaryPoly.OrdinaryResidueSupport (rowAction axis rowAction_mul rowAction_one)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate

theorem fiberAction_eq (n : ℕ) (g : IntegralGL) (a : ResidueFiber n (axis 0)) :
    fiberAction n g a = component n (axis 0) (rho n g (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) a)) :=
  rfl

theorem fiberAction_mul (n : ℕ) {s t : IntegralGL} (ht : t ∈ PH) (a : ResidueFiber n (axis 0)) :
    fiberAction n (s * t) a = fiberAction n s (fiberAction n t a) := by
  rw [fiberAction_eq, rho_mul, rho_PH_lof n ht, ← fiberAction_eq]

theorem fiberAction_one (n : ℕ) (a : ResidueFiber n (axis 0)) : fiberAction n 1 a = a := by
  rw [fiberAction_eq, rho_one]
  simp

/-- The representation of `P_H` on the `H₀`-summand `𝓡_{n,H₀}`. -/
def fiberRep (n : ℕ) : Representation ℚ PH (ResidueFiber n (axis 0)) where
  toFun s := fiberAction n s.val
  map_one' := by
    apply LinearMap.ext
    intro a
    exact fiberAction_one n a
  map_mul' s t := by
    apply LinearMap.ext
    intro a
    exact fiberAction_mul n t.2 a

/-- The `G`-representation `𝓡_n` (exponent `-1`) as an object of `Rep ℚ G`. -/
abbrev ResRep (n : ℕ) : Rep ℚ IntegralGL := Rep.of (integralResidueAction n (-1))

/-- The `P_H`-representation `𝓡_{n,H₀}` as an object of `Rep ℚ P_H`. -/
abbrev FibRep (n : ℕ) : Rep ℚ PH := Rep.of (fiberRep n)

/-- The inclusion `lof_{H₀} : 𝓡_{n,H₀} → Res_{P_H} 𝓡_n` of the `H₀`-summand, a `P_H`-map. -/
def lofHom (n : ℕ) : FibRep n ⟶ Rep.res PH.subtype (ResRep n) :=
  Rep.ofHom ⟨DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0), fun s => by
    apply LinearMap.ext
    intro a
    exact (rho_PH_lof n s.2 a).symm⟩

/-- The `G`-map `Ind_{P_H}^G 𝓡_{n,H₀} → 𝓡_n` of the induction adjunction. -/
def indToRes (n : ℕ) : Rep.ind PH.subtype (FibRep n) ⟶ ResRep n :=
  ((Rep.indResHomEquiv PH.subtype (FibRep n) (ResRep n)).symm (lofHom n))

theorem indToRes_mk (n : ℕ) (h : IntegralGL) (a : ResidueFiber n (axis 0)) :
    (indToRes n).hom (Representation.IndV.mk PH.subtype (fiberRep n) h a) =
      rho n h⁻¹ (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) a) := by
  simp [indToRes, Rep.indResHomEquiv, lofHom]

theorem IndV_mk_PH (n : ℕ) (s : PH) (g : IntegralGL) (a : ResidueFiber n (axis 0)) :
    Representation.IndV.mk PH.subtype (fiberRep n) (s.val * g) (fiberRep n s a) =
      Representation.IndV.mk PH.subtype (fiberRep n) g a := by
  have := Representation.Coinvariants.mk_self_apply
    (ρ := Representation.tprod ((Representation.leftRegular ℚ IntegralGL).comp PH.subtype)
      (fiberRep n)) s (MonoidAlgebra.single g (1 : ℚ) ⊗ₜ[ℚ] a)
  simpa [Representation.IndV.mk] using this

theorem eq_lof_of_support (n : ℕ) (r : Residues n) (H : Normal) (h : ∀ J, J ≠ H → r J = 0) :
    r = DirectSum.lof ℚ Normal (ResidueFiber n) H (r H) := by
  apply DFinsupp.ext
  intro J
  by_cases hJ : J = H
  · subst hJ; simp
  · rw [h J hJ]; exact (DirectSum.of_eq_of_ne _ _ _ hJ).symm

/-- `ρ(g)` moves a summand at `H` to the summand at `H g⁻¹`. -/
theorem rho_lof_support (n : ℕ) (g : IntegralGL) (H : Normal) (z : ResidueFiber n H) :
    rho n g (DirectSum.lof ℚ Normal (ResidueFiber n) H z) =
      DirectSum.lof ℚ Normal (ResidueFiber n) (rowAction g⁻¹ H)
        (rho n g (DirectSum.lof ℚ Normal (ResidueFiber n) H z) (rowAction g⁻¹ H)) :=
  eq_lof_of_support n _ _ (fun J hJ => action_lof_component_zero n (-1) g H J z hJ)

/-- The chosen representative `x_H` with `ν x_H = H`. -/
def xrep (H : Normal) : IntegralGL := Classical.choose (nu_surj H)

theorem nu_xrep (H : Normal) : nu (xrep H) = H := Classical.choose_spec (nu_surj H)

/-- The inverse map on the summand `H`: `z ↦ ⟦x_H ⊗ comp_{H₀}(ρ(x_H) z)⟧`. -/
def phiSummand (n : ℕ) (H : Normal) :
    ResidueFiber n H →ₗ[ℚ] Representation.IndV PH.subtype (fiberRep n) :=
  (Representation.IndV.mk PH.subtype (fiberRep n) (xrep H)) ∘ₗ (component n (axis 0)) ∘ₗ
    (rho n (xrep H)) ∘ₗ (DirectSum.lof ℚ Normal (ResidueFiber n) H)

/-- The inverse `Residues n → Ind_{P_H}^G 𝓡_{n,H₀}`. -/
def residuesToInd (n : ℕ) : Residues n →ₗ[ℚ] Representation.IndV PH.subtype (fiberRep n) :=
  DirectSum.toModule ℚ Normal _ (phiSummand n)

theorem residuesToInd_lof (n : ℕ) (H : Normal) (z : ResidueFiber n H) :
    residuesToInd n (DirectSum.lof ℚ Normal (ResidueFiber n) H z) = phiSummand n H z := by
  simp [residuesToInd]

theorem indToRes_residuesToInd (n : ℕ) (r : Residues n) :
    (indToRes n).hom (residuesToInd n r) = r := by
  induction r using DirectSum.induction_on with
  | zero => simp
  | of H z =>
    change (indToRes n).hom (residuesToInd n (DirectSum.lof ℚ Normal (ResidueFiber n) H z)) =
      DirectSum.lof ℚ Normal (ResidueFiber n) H z
    rw [residuesToInd_lof]
    change (indToRes n).hom (Representation.IndV.mk PH.subtype (fiberRep n) (xrep H)
      (component n (axis 0) (rho n (xrep H) (DirectSum.lof ℚ Normal (ResidueFiber n) H z)))) = _
    rw [indToRes_mk]
    have hx : nu (xrep H) = H := nu_xrep H
    have hsupp : rho n (xrep H) (DirectSum.lof ℚ Normal (ResidueFiber n) H z) =
        DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0)
          (component n (axis 0) (rho n (xrep H) (DirectSum.lof ℚ Normal (ResidueFiber n) H z))) := by
      have h1 := rho_lof_support n (xrep H) H z
      have h2 : rowAction (xrep H)⁻¹ H = axis 0 := by
        have h3 : rowAction (xrep H)⁻¹ (nu (xrep H)) = axis 0 := by
          unfold nu
          rw [← rowAction_mul, mul_inv_cancel, rowAction_one]
        rw [hx] at h3
        exact h3
      rw [h2] at h1
      exact h1
    rw [← hsupp, rho_inv_rho]
  | add r r' hr hr' => simp [map_add, hr, hr']

theorem residuesToInd_indToRes (n : ℕ)
    (x : Representation.IndV PH.subtype (fiberRep n)) :
    residuesToInd n ((indToRes n).hom x) = x := by
  have key : (residuesToInd n) ∘ₗ (indToRes n).hom.toLinearMap = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro h
    apply LinearMap.ext
    intro a
    change residuesToInd n ((indToRes n).hom (Representation.IndV.mk PH.subtype (fiberRep n) h a)) = _
    rw [indToRes_mk]
    have hsupp := rho_lof_support n h⁻¹ (axis 0) a
    rw [inv_inv] at hsupp
    have hnu : rowAction h (axis 0) = nu h := rfl
    rw [hnu] at hsupp
    rw [hsupp, residuesToInd_lof]
    change Representation.IndV.mk PH.subtype (fiberRep n) (xrep (nu h))
      (component n (axis 0) (rho n (xrep (nu h)) (DirectSum.lof ℚ Normal (ResidueFiber n) (nu h)
        (rho n h⁻¹ (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) a) (nu h))))) = _
    rw [← hsupp]
    obtain ⟨s, hs, hsh⟩ := nu_eq (nu_xrep (nu h))
    have hxh : xrep (nu h) * h⁻¹ = s⁻¹ := by
      calc xrep (nu h) * h⁻¹ = xrep (nu h) * (s * xrep (nu h))⁻¹ := by rw [← hsh]
        _ = s⁻¹ := by group
    rw [← rho_mul, hxh, rho_PH_lof n (PH.inv_mem hs)]
    simp only [component_apply, DirectSum.lof_apply]
    have h1 := IndV_mk_PH n ⟨s⁻¹, PH.inv_mem hs⟩ (s * xrep (nu h)) a
    have e1 : Representation.IndV.mk PH.subtype (fiberRep n) h a =
        Representation.IndV.mk PH.subtype (fiberRep n) (s * xrep (nu h)) a := by rw [← hsh]
    show _ = Representation.IndV.mk PH.subtype (fiberRep n) h a
    rw [e1]
    simp only [inv_mul_cancel_left, Representation.IndV.mk, LinearMap.comp_apply] at h1 ⊢
    exact h1
  exact LinearMap.congr_fun key x

theorem indToRes_bijective (n : ℕ) : Function.Bijective (indToRes n).hom :=
  ⟨Function.LeftInverse.injective (g := residuesToInd n) (residuesToInd_indToRes n),
    Function.RightInverse.surjective (g := residuesToInd n) (indToRes_residuesToInd n)⟩

instance isIso_indToRes (n : ℕ) : IsIso (indToRes n) := by
  have : IsIso ((forget (Rep ℚ IntegralGL)).map (indToRes n)) := by
    rw [isIso_iff_bijective]
    exact indToRes_bijective n
  exact isIso_of_reflects_iso (indToRes n) (forget (Rep ℚ IntegralGL))

/-- **`𝓡_n ≅ Ind_{P_H}^G 𝓡_{n,H₀}` as `G`-representations** (exponent `-1`): the residue module is
the induced module of its `H₀`-summand, for Mathlib's `Rep.ind` along `P_H ↪ G`. -/
def indResiduesIso (n : ℕ) : Rep.ind PH.subtype (FibRep n) ≅ ResRep n := asIso (indToRes n)

/-- **Shapiro in group homology for the residue module**:
`H_k(G, 𝓡_n ⊗ det⁻¹) ≅ H_k(P_H, 𝓡_{n,H₀})`, obtained from Mathlib's `groupHomology.indIso`
and the identification `𝓡_n ≅ Ind_{P_H}^G 𝓡_{n,H₀}`. -/
def shapiroHomologyIso (n k : ℕ) : groupHomology (ResRep n) k ≅ groupHomology (FibRep n) k := by
  classical
  exact ((groupHomology.functor ℚ IntegralGL k).mapIso (indResiduesIso n).symm) ≪≫
    groupHomology.indIso PH (FibRep n) k

end TernaryPeriodPolynomials.Argument.AppendixBResidue
