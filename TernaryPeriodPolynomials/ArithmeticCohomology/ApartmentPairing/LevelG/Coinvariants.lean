module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Fixed

@[expose] public section


open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.RationalCohomologyDescent
  TernaryPoly.SingularLocalHomology TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryCone
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel

/-!
# Level G: the honest coinvariant homology of the boundary and its identification with `H3boundaryG` (G-3, G-4)

Formalized by Claude Sonnet 5.5.

The group `G = GL₃(ℤ)` acts on the singular chains of the boundary cover
(`BoundaryAction.lean`); `Qbd V₀ = H₃((V₀ ⊗ Sing ∂X̃)_G)` is the homology of the `G`-coinvariants, the honest `H₃(∂X̄_G; 𝓜)`,
and `qBd : H₃(∂X̄_Γ(6); 𝓜) → Qbd` is induced by the quotient map `QY` of coinvariant complexes.  Results: `qBd` is surjective,
its kernel is the kernel of the `G/Γ(6)`-average `avgBd` of the geometric action (`qBd_ker`), `G` acts trivially on `Qbd`
(`qBd_bAct`), and `qBd` restricts to a linear isomorphism `coinvIso : H3boundaryG ≃ Qbd` from the invariant classes.
`jQ` and `PDQ` are `j^G_*` and boundary Poincaré duality on `Qbd`; `jQ ∘ qBd = Cor ∘ j_*` (`jQ_qBd`, from equivariance of
`boundaryToGroup`, `boundaryToGroup_equivariant`, and `Cor ∘ c_g = Cor`), and the level-`G` diagram holds on `Qbd`
(`levelG_diagram_Q`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (V₀ : Rep.{0} ℚ IntegralGL)

/-- **The honest `H₃(∂X̄_G; 𝓜)`**: the homology of the `G`-coinvariants of `M ⊗ Sing(∂X̃)` (diagonal action of
`G = GL₃(ℤ)` on the simplices of the boundary cover and on `M`). -/
abbrev Qbd : ModuleCat ℚ := (CxK (Ybd V₀)).homology 3

/-- The quotient map from the neat-level boundary homology `H₃(∂X̄_Γ(6); 𝓜)` to `Qbd V₀`. -/
def qBd : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3 ⟶ Qbd V₀ :=
  homologyMap (ibd V₀).hom 3 ≫ homologyMap (QY principalSix (Ybd V₀)) 3

/-- Transport of the neat-level boundary homology to the `Γ(6)`-coinvariant complex. -/
def jBd : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3 ≅
    (CxN principalSix (Ybd V₀)).homology 3 :=
  homologyMapIso (ibd V₀) 3

theorem qBd_eq : qBd V₀ = (jBd V₀).hom ≫ homologyMap (QY principalSix (Ybd V₀)) 3 := rfl

theorem qBd_surjective : Function.Surjective (qBd V₀).hom := by
  intro y
  obtain ⟨z, hz⟩ := descent_surjective principalSix (Ybd V₀) 3 (card_ne_zero_quot principalSix) y
  refine ⟨(jBd V₀).inv z, ?_⟩
  rw [qBd_eq]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  exact hz

theorem jBd_bAct (g : IntegralGL) (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    (jBd V₀).hom (homologyMap (bAct V₀ g) 3 c) = homologyMap (GY principalSix (Ybd V₀) g) 3 ((jBd V₀).hom c) := by
  have h : homologyMap (bAct V₀ g) 3 ≫ homologyMap (ibd V₀).hom 3 =
      homologyMap (ibd V₀).hom 3 ≫ homologyMap (GYb V₀ g) 3 := by
    unfold bAct
    rw [homologyMap_comp, homologyMap_comp]
    simp only [Category.assoc]
    rw [← homologyMap_comp (ibd V₀).inv (ibd V₀).hom, Iso.inv_hom_id, homologyMap_id, Category.comp_id]
  exact ConcreteCategory.congr_hom h c

/-- The averaging projector of `H₃(∂X̄_Γ(6); 𝓜)` for the geometric action `bAct` of `G/Γ(6)`. -/
def avgBd : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3 →ₗ[ℚ]
    (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3 :=
  ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹) •
    ∑ x : IntegralGL ⧸ principalSix, (homologyMap (bAct V₀ x.out) 3).hom

theorem jBd_avgBd (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    (jBd V₀).hom (avgBd V₀ c) = avgH principalSix (Ybd V₀) 3 ((jBd V₀).hom c) := by
  unfold avgBd avgH
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  exact jBd_bAct V₀ x.out c

/-- `Γ(6)`-coinvariants to `G`-coinvariants: the class `qBd c` vanishes iff the `G`-average of `c` does. -/
theorem qBd_ker (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    (qBd V₀).hom c = 0 ↔ avgBd V₀ c = 0 := by
  rw [qBd_eq]
  change (homologyMap (QY principalSix (Ybd V₀)) 3).hom ((jBd V₀).hom c) = 0 ↔ _
  rw [descent_ker principalSix (Ybd V₀) 3 (card_ne_zero_quot principalSix), ← jBd_avgBd]
  constructor
  · intro h
    exact (ConcreteCategory.bijective_of_isIso (jBd V₀).hom).injective (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

theorem qBd_bAct (g : IntegralGL) (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    (qBd V₀).hom (homologyMap (bAct V₀ g) 3 c) = (qBd V₀).hom c := by
  rw [qBd_eq]
  change (homologyMap (QY principalSix (Ybd V₀)) 3).hom ((jBd V₀).hom (homologyMap (bAct V₀ g) 3 c)) = _
  rw [jBd_bAct]
  exact descent_gam principalSix (Ybd V₀) 3 g _

theorem avgBd_bAct (g : IntegralGL) (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    homologyMap (bAct V₀ g) 3 (avgBd V₀ c) = avgBd V₀ c := by
  apply (ConcreteCategory.bijective_of_isIso (jBd V₀).hom).injective
  rw [jBd_bAct, jBd_avgBd]
  set z := (jBd V₀).hom c
  have h : (homologyMap (avgY principalSix (Ybd V₀) ≫ GY principalSix (Ybd V₀) g) 3).hom z =
      (homologyMap (avgY principalSix (Ybd V₀)) 3).hom z := by
    rw [avgY_GY]
  rw [homologyMap_comp] at h
  change (homologyMap (GY principalSix (Ybd V₀) g) 3).hom ((homologyMap (avgY principalSix (Ybd V₀)) 3).hom z) =
    (homologyMap (avgY principalSix (Ybd V₀)) 3).hom z at h
  rw [avgY_homology] at h
  exact h

theorem avgBd_of_fixed (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3)
    (hc : ∀ g : IntegralGL, homologyMap (bAct V₀ g) 3 c = c) : avgBd V₀ c = c := by
  unfold avgBd
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  have : ∀ x : IntegralGL ⧸ principalSix, (homologyMap (bAct V₀ x.out) 3).hom c = c := fun x => hc _
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (card_ne_zero_quot principalSix), one_smul]

/-- `avgBd` is idempotent, with image the `G`-invariant classes. -/
theorem avgBd_idem (c : (boundaryLocalChains (Rep.res principalSix.subtype V₀)).homology 3) :
    avgBd V₀ (avgBd V₀ c) = avgBd V₀ c :=
  avgBd_of_fixed V₀ _ (fun g => avgBd_bAct V₀ g c)

variable (n : ℕ) (e : ℤ)

/-- The quotient map restricted to `H₃(∂X̄_G; 𝓜)` (the invariant subspace of `H₃(∂X̄_Γ(6); 𝓜)`). -/
def qBdG : H3boundaryG n e →ₗ[ℚ] Qbd (actualCoefficients n e) :=
  (qBd (actualCoefficients n e)).hom ∘ₗ (H3boundaryG n e).subtype

theorem avgBd_mem (c : (boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    avgBd (actualCoefficients n e) c ∈ H3boundaryG n e :=
  (mem_H3boundaryG_iff n e _).2 (fun g => avgBd_bAct (actualCoefficients n e) g c)

/-- **G-3 (honest coinvariant identification)**: the quotient map from the neat-level boundary homology to the homology of
the `G`-coinvariants `Qbd = H₃((M ⊗ Sing ∂X̃)_G)` restricts to a linear isomorphism from `H₃(∂X̄_G; 𝓜)` (the invariant classes,
`mem_H3boundaryG_iff`) onto `Qbd`. -/
def coinvIso : H3boundaryG n e ≃ₗ[ℚ] Qbd (actualCoefficients n e) :=
  LinearEquiv.ofBijective (qBdG n e) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      have hker : (qBd (actualCoefficients n e)).hom (a.1 - b.1) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.2 hab
      rw [qBd_ker] at hker
      have ha := avgBd_of_fixed (actualCoefficients n e) (a.1 - b.1)
        (fun g => by
          rw [map_sub, ((mem_H3boundaryG_iff n e _).1 a.2 g), ((mem_H3boundaryG_iff n e _).1 b.2 g)])
      rw [hker] at ha
      exact (sub_eq_zero.1 ha.symm)
    · intro y
      obtain ⟨c, hc⟩ := qBd_surjective (actualCoefficients n e) y
      refine ⟨⟨avgBd (actualCoefficients n e) c, avgBd_mem n e c⟩, ?_⟩
      change (qBd (actualCoefficients n e)).hom (avgBd (actualCoefficients n e) c) = y
      rw [← hc]
      have : (qBd (actualCoefficients n e)).hom (avgBd (actualCoefficients n e) c - c) = 0 := by
        rw [qBd_ker, map_sub, avgBd_idem, sub_self]
      rw [map_sub] at this
      exact sub_eq_zero.1 this)

theorem coinvIso_apply (c : H3boundaryG n e) :
    coinvIso n e c = (qBd (actualCoefficients n e)).hom c.1 := rfl

theorem corG_boundaryToGroup_bAct (g : IntegralGL)
    (c : (boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3
      (homologyMap (bAct (actualCoefficients n e) g) 3 c)) =
    corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 c) := by
  have h := ConcreteCategory.congr_hom (boundaryToGroup_equivariant (actualCoefficients n e) g) c
  change corN principalSix (actualCoefficients n e) 3 _ = corN principalSix (actualCoefficients n e) 3 _
  have h' : (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom
      ((homologyMap (bAct (actualCoefficients n e) g) 3).hom c) =
      cAct principalSix (actualCoefficients n e) 3 g
        ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom c) := h
  rw [h']
  exact corN_cAct g _

theorem corG_boundaryToGroup_avgBd (c : (boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3
      (avgBd (actualCoefficients n e) c)) =
    corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 c) := by
  change (corG n e).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom
      (avgBd (actualCoefficients n e) c)) = _
  unfold avgBd
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hx : ∀ x : IntegralGL ⧸ principalSix,
      (corG n e).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom
        ((homologyMap (bAct (actualCoefficients n e) x.out) 3).hom c)) =
      (corG n e).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom c) :=
    fun x => corG_boundaryToGroup_bAct n e x.out c
  simp only [hx, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (card_ne_zero_quot principalSix), one_smul]

/-- `j^G_* : H₃(∂X̄_G; 𝓜) → H₃(G, M)` on the honest coinvariant homology `Qbd`, characterized by `jQ ∘ qBd = Cor ∘ j_*`. -/
def jQ : Qbd (actualCoefficients n e) →ₗ[ℚ] groupHomology (actualCoefficients n e) 3 :=
  (corG n e).hom ∘ₗ (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom ∘ₗ
    (H3boundaryG n e).subtype ∘ₗ (coinvIso n e).symm.toLinearMap

/-- `PD_∂ : H₃(∂X̄_G; 𝓜) → H¹(∂X̄_G; M)` on the honest coinvariant homology `Qbd`. -/
def PDQ : Qbd (actualCoefficients n e) ≃ₗ[ℚ] (fullBoundaryCochains n e).homology 1 :=
  (coinvIso n e).symm.trans (PDG n e)

theorem coinvIso_symm_qBd (c : (boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    (coinvIso n e).symm ((qBd (actualCoefficients n e)).hom c) = ⟨avgBd (actualCoefficients n e) c, avgBd_mem n e c⟩ := by
  rw [LinearEquiv.symm_apply_eq]
  change (qBd (actualCoefficients n e)).hom c = (qBd (actualCoefficients n e)).hom (avgBd (actualCoefficients n e) c)
  have : (qBd (actualCoefficients n e)).hom (avgBd (actualCoefficients n e) c - c) = 0 := by
    rw [qBd_ker, map_sub, avgBd_idem, sub_self]
  rw [map_sub] at this
  exact (sub_eq_zero.1 this).symm

/-- **Compatibility of `j^G_*` with `Cor ∘ j_*`**: `jQ (qBd c) = Cor (j_* c)`. -/
theorem jQ_qBd (c : (boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    jQ n e ((qBd (actualCoefficients n e)).hom c) =
      (corG n e).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom c) := by
  change (corG n e).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom
    ((coinvIso n e).symm ((qBd (actualCoefficients n e)).hom c)).1) = _
  rw [coinvIso_symm_qBd]
  exact corG_boundaryToGroup_avgBd n e c

/-- **Lemma 3.3 at level `G` on the honest coinvariant homology**: for every `y ∈ H₃((M ⊗ Sing ∂X̃)_G)`,
`F_{j^G_* y}(ℓ) = ⟨PD_∂ y, ∂a⟩ ∈ M`. -/
theorem levelG_diagram_Q (y : Qbd (actualCoefficients n e)) :
    topEvaluationG (actualCoefficients n e) (jQ n e y) = fullBoundaryPairing n e (PDQ n e y) := by
  have h := levelG_diagram_PD n e ((coinvIso n e).symm y)
  exact h

/-- The same for classes coming from the neat level: `F_{Cor j_* c}(ℓ) = ⟨PD_∂ (qBd c), ∂a⟩`. -/
theorem levelG_diagram_Q_qBd (c : (boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    topEvaluationG (actualCoefficients n e)
        ((corG n e).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3).hom c)) =
      fullBoundaryPairing n e (PDQ n e ((qBd (actualCoefficients n e)).hom c)) := by
  rw [← jQ_qBd]
  exact levelG_diagram_Q n e _

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
