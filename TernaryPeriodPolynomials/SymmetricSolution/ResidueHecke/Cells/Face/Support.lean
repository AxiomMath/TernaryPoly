module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Face.Reduction

@[expose] public section


/-!
# Lemma B.1, boundary route: the support clause of `FaceEval` from coefficient naturality of the neat duality

Formalized by Claude Sonnet 5.5.

`M0 n` is the `Γ(6)`-submodule of `𝓡_n` spanned by the summands `𝓡_{n,H}` with `H` in the `Γ(6)`-orbit of `H₀`
(`rho_mem_M0`), `M0Rep n` the corresponding representation of `Γ(6)`, `incl0` its inclusion in `Res 𝓡_n`, and `lof0` the
inclusion of the `H₀`-summand, so `ι_* = (incl0)_* ∘ (lof0)_*` (`iotaStar_factor`).  The `a = 0` component of `ρ(g) M0`
vanishes for `g ∉ P_H · Γ(6)` (`component_rho_M0`, from `action_lof_component_zero` and `nu_eq`).  Granted the naturality of
the neat duality `groupOrdinaryIso` in the coefficient representation (hypothesis `hnat`), the functional
`Θ_N(ι_* y)` takes values in `M0` (`psiN_mem_M0`) and the support clause of `FaceEval` holds
(`termF_eq_zero_of_natural`).  `FaceEvalMain` is `FaceEval` without that clause and
`phCompat_of_faceEvalMain` the resulting reduction.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
open TernaryPoly.OrdinaryResidueSupport (rowAction rowAction_mul rowAction_one axis)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel

/-- The hyperplanes of the `Γ(6)`-orbit of `H₀`. -/
def orbN : Set Normal := {H | ∃ m ∈ principalSix, H = nu m}

/-- The `Γ(6)`-submodule of `𝓡_n` spanned by the `H`-summands, `H` in the `Γ(6)`-orbit of `H₀`. -/
def M0 (n : ℕ) : Submodule ℚ (Residues n) :=
  ⨆ H ∈ orbN, LinearMap.range (DirectSum.lof ℚ Normal (ResidueFiber n) H)

theorem lof_mem_M0 (n : ℕ) {H : Normal} (hH : H ∈ orbN) (z : ResidueFiber n H) :
    DirectSum.lof ℚ Normal (ResidueFiber n) H z ∈ M0 n :=
  (le_iSup₂ (f := fun H (_ : H ∈ orbN) => LinearMap.range (DirectSum.lof ℚ Normal (ResidueFiber n) H))
    H hH) ⟨z, rfl⟩

theorem rowAction_inv_mem_orbN {m : IntegralGL} (hm : m ∈ principalSix) {H : Normal} (hH : H ∈ orbN) :
    rowAction m⁻¹ H ∈ orbN := by
  obtain ⟨m', hm', rfl⟩ := hH
  refine ⟨m' * m⁻¹, principalSix.mul_mem hm' (principalSix.inv_mem hm), ?_⟩
  unfold nu
  rw [rowAction_mul]

theorem rho_mem_M0 (n : ℕ) {m : IntegralGL} (hm : m ∈ principalSix) {r : Residues n} (hr : r ∈ M0 n) :
    rho n m r ∈ M0 n := by
  have key : M0 n ≤ (M0 n).comap (rho n m) := by
    refine iSup₂_le fun H hH => ?_
    rintro _ ⟨z, rfl⟩
    rw [Submodule.mem_comap, rho_lof_support]
    exact lof_mem_M0 n (rowAction_inv_mem_orbN hm hH) _
  exact key hr

theorem component_rho_M0 (n : ℕ) {g : IntegralGL} (hg : ¬ InPHN g) {r : Residues n} (hr : r ∈ M0 n) :
    component n (axis 0) (rho n g r) = 0 := by
  have key : M0 n ≤ LinearMap.ker ((component n (axis 0)).comp (rho n g)) := by
    refine iSup₂_le fun H hH => ?_
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    obtain ⟨m, hm, rfl⟩ := hH
    have hne : axis 0 ≠ rowAction g⁻¹ (nu m) := by
      intro h
      apply hg
      have hs : m * g⁻¹ ∈ PH := by
        change rowAction (m * g⁻¹) (axis 0) = axis 0
        rw [rowAction_mul]
        exact h.symm
      refine ⟨(m * g⁻¹)⁻¹, PH.inv_mem hs, m, hm, by group⟩
    have := action_lof_component_zero n (-1) g (nu m) (axis 0) z hne
    simpa using this
  exact LinearMap.mem_ker.mp (key hr)

/-- `M0` as a representation of `Γ(6)`. -/
def M0Rep (n : ℕ) : Rep.{0} ℚ principalSix :=
  Rep.of
    { toFun := fun m => (rho n m.1).restrict (fun r hr => rho_mem_M0 n m.2 hr)
      map_one' := by
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        exact rho_one n r.1
      map_mul' := fun a b => by
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        exact rho_mul n a.1 b.1 r.1 }

/-- The inclusion `M₀ ⟶ Res_{Γ(6)} 𝓡_n`. -/
def incl0 (n : ℕ) : M0Rep n ⟶ Rep.res principalSix.subtype (ResRep n) :=
  Rep.ofHom ⟨(M0 n).subtype, fun m => by
    apply LinearMap.ext
    intro r
    rfl⟩

/-- `lof_{H₀}` with values in `M₀`, restricted to `P_N`. -/
def lof0 (n : ℕ) : Rep.res PN.subtype (FibRep n) ⟶ Rep.res jPN (M0Rep n) :=
  Rep.ofHom ⟨(DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0)).codRestrict (M0 n)
      (fun a => lof_mem_M0 n ⟨1, principalSix.one_mem, nu_one.symm⟩ a), fun p => by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact (rho_PH_lof n p.1.2 a).symm⟩

theorem lofN_eq (n : ℕ) :
    lofN n = lof0 n ≫ (Rep.resFunctor jPN).map (incl0 n) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rfl

theorem iotaStar_factor (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    iotaStar n y = (groupHomology.map (MonoidHom.id principalSix) (incl0 n) 3).hom
      ((groupHomology.map jPN (lof0 n) 3).hom y) := by
  have h1 := groupHomology.map_comp (k := ℚ) (C := Rep.res principalSix.subtype (ResRep n)) jPN (MonoidHom.id principalSix)
    (lof0 n) (incl0 n) 3
  have h3 := groupHomology.map_congr (k := ℚ) (B := Rep.res principalSix.subtype (ResRep n))
    (f := (MonoidHom.id principalSix).comp jPN) (g := jPN) (MonoidHom.id_comp jPN)
    (φ := lof0 n ≫ (Rep.resFunctor jPN).map (incl0 n)) (ψ := lofN n)
    (by rw [lofN_eq]) 3
  exact congrArg (fun m => m.hom y) (h3.symm.trans h1)

theorem psiN_mem_M0
    (hnat : ∀ {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W') (x : groupHomology W 3),
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso W').hom.hom
          ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
        (OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom.hom x ≫ f)
    (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3)
    (τ : OrdinaryIncidenceChains.Cycles) : psiN n y τ ∈ M0 n := by
  have h1 : psiN n y τ = ((OrdinaryTopBoundaryComparison.groupOrdinaryIso
      (Rep.res principalSix.subtype (ResRep n))).hom.hom (iotaStar n y)).hom τ := by
    unfold psiN psiGen
    rw [LinearMap.comp_apply, thetaGen_refl_apply]
    rfl
  rw [h1, iotaStar_factor, hnat]
  exact ((OrdinaryTopBoundaryComparison.groupOrdinaryIso (M0Rep n)).hom.hom
    ((groupHomology.map jPN (lof0 n) 3).hom y)).hom τ |>.2

theorem termF_eq_zero_of_natural
    (hnat : ∀ {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W') (x : groupHomology W 3),
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso W').hom.hom
          ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
        (OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom.hom x ≫ f)
    (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) {g : IntegralGL} (hg : ¬ InPHN g) :
    termF n y g = 0 := by
  unfold termF
  have h := component_rho_M0 n hg (psiN_mem_M0 hnat n y (stG g⁻¹ (OrdinaryApartmentPresentation.frameCycle 1)))
  have h' : SinglePoleSupport.component n (axis 0)
      (TernaryPeriodPolynomials.Argument.GroupHomology.term stG (ResRep n).ρ (psiN n y) g
        (OrdinaryApartmentPresentation.frameCycle 1)) = 0 := h
  rw [h', map_zero]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **`FaceEval` without the support clause** (the main evaluation clause only). -/
def FaceEvalMain (n : ℕ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ ∀ y : groupHomology (Rep.res PN.subtype (FibRep n)) 3,
    ∑ s : PH ⧸ PN, termF n y ((s.out : PH) : IntegralGL) =
      c • (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (corN PN (FibRep n) 3 y)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1))

theorem phCompat_of_faceEvalMain
    (hnat : ∀ {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W') (x : groupHomology W 3),
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso W').hom.hom
          ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
        (OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom.hom x ≫ f)
    (n : ℕ) (h : FaceEvalMain n) : PHCompat n := by
  obtain ⟨c, hc, hF⟩ := h
  exact phCompat_of_faceEval n ⟨c, hc, fun y => ⟨fun _ hg => termF_eq_zero_of_natural hnat n y hg, hF y⟩⟩

end TernaryPeriodPolynomials.Argument.AppendixBResidue
