module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonApartment
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalDescent
public import TernaryPeriodPolynomials.GroupCohomology.Homology.HomAveraging
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Defs

@[expose] public section


/-!
# The K-level duality, conditional on the K-equivariance of the neat-level duality

`H₃(K, E_{n,t})` (Mathlib's `groupHomology`) is the quotient of `H₃(Γ(6), E_{n,t})` by the kernel of
the averaging operator `avgN` over `K/Γ(6)` (`GroupHomology.NormalDescent`), and `Hom_K(St, E_{n,t})`
is the image of the averaging operator on `Hom_{Γ(6)}(St, E_{n,t})` (`GroupHomology.HomAveraging`).
The neat-level duality `Θ` of the library identifies `H₃(Γ(6), E)` with `Hom_{Γ(6)}(St, E)`.
**If** `Θ` intertwines the conjugation action `c_g` of `K` on `H₃(Γ(6), E)` with the action
`Φ ↦ ρ(g) ∘ Φ ∘ g⁻¹` on functionals (`NeatDualityEquivariant`), then `H₃(K, E) ≃ Hom_K(St, E)`.

This is a CONDITIONAL reduction, not a proof of the K-level duality: `NeatDualityEquivariant` is not
established.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
  TernaryPeriodPolynomials.Argument.GroupHomology

/-- The group `K` of Lemma 3.2 as a type. -/
abbrev KT : Type := ↥K

/-- The coefficient module `E_{n,t}` as a `K`-representation. -/
abbrev EK (n : ℕ) (t : Fin 2) : Rep.{0} ℚ KT := Rep.res K.subtype (Rep.of (coeff n t))

/-- The coefficient module `E_{n,t}` restricted to `Γ(6)` (the library's neat-level coefficients). -/
abbrev EGamma (n : ℕ) (t : Fin 2) : Rep.{0} ℚ principalSix :=
  Rep.res principalSix.subtype (Rep.of (coeff n t))

/-- The isomorphism `Γ(6)-in-K ≃* Γ(6)`. -/
def sixEquiv : ↥principalSixInK ≃* ↥principalSix where
  toFun n := ⟨n.1.1, (mem_principalSixInK n.1).mp n.2⟩
  invFun γ := ⟨⟨γ.1, principalSix_le_K γ.2⟩, (mem_principalSixInK _).mpr γ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl


/-- The neat-level duality transported to the copy of `Γ(6)` inside `K`. -/
def thetaN (n : ℕ) (t : Fin 2) :
    groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3 ≅
      OrdinaryTopBoundaryComparison.ordinaryFunctionals (EGamma n t) :=
  groupHomology.mapIso sixEquiv (LinearEquiv.refl ℚ (V n)) (fun _ => rfl) 3 ≪≫
    OrdinaryTopBoundaryComparison.groupOrdinaryIso (EGamma n t)

/-- The Steinberg module as a representation of `K`. -/
abbrev stK : Representation ℚ KT OrdinaryIncidenceChains.Cycles :=
  OrdinaryIncidenceChains.complex.cyclesAction

/-- The coefficient representation of `K` on `V_n`. -/
abbrev coeffK (n : ℕ) (t : Fin 2) : Representation ℚ KT (V n) := (coeff n t).comp K.subtype

/-- The underlying linear map of an equivariant functional. -/
def toLin {n : ℕ} {t : Fin 2}
    (φ : SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶ EGamma n t) :
    OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n := φ.hom.toLinearMap

theorem toLin_injective {n : ℕ} {t : Fin 2} :
    Function.Injective (toLin : (SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶
      EGamma n t) → _) := by
  intro φ ψ h
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact h

theorem toLin_isEquivOn {n : ℕ} {t : Fin 2}
    (φ : SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶ EGamma n t) :
    GroupHomology.IsEquivOn stK (coeffK n t) principalSixInK (toLin φ) := by
  intro g hg z
  have h := Rep.hom_comm_apply φ (sixEquiv ⟨g, hg⟩) z
  exact h


theorem exists_toLin_eq {n : ℕ} {t : Fin 2} (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n)
    (hΦ : GroupHomology.IsEquivOn stK (coeffK n t) principalSixInK Φ) :
    ∃ φ : SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶ EGamma n t, toLin φ = Φ := by
  refine ⟨Rep.ofHom ⟨Φ, fun γ => LinearMap.ext fun z => ?_⟩, rfl⟩
  exact hΦ (SymmetricSpaceBoundaryIncidenceHomology.principalToK γ)
    ((mem_principalSixInK _).mpr γ.2) z

open scoped Classical

/-- `toLin` as a linear map. -/
def toLinL {n : ℕ} {t : Fin 2} :
    (SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶ EGamma n t) →ₗ[ℚ]
      (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n) where
  toFun := toLin
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Conditional

variable (n : ℕ) (t : Fin 2)

/-- The neat-level duality followed by forgetting equivariance. -/
def psi : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3 →ₗ[ℚ]
    (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n) :=
  toLinL ∘ₗ (thetaN n t).hom.hom

theorem psi_injective : Function.Injective (psi n t) := by
  intro x y h
  have h1 := toLin_injective h
  have h2 : (thetaN n t).hom.hom x = (thetaN n t).hom.hom y := h1
  have := congrArg (fun z => (thetaN n t).inv.hom z) h2
  simpa using this

theorem mem_range_psi_iff (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n) :
    Φ ∈ LinearMap.range (psi n t) ↔ GroupHomology.IsEquivOn stK (coeffK n t) principalSixInK Φ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact toLin_isEquivOn _
  · intro hΦ
    obtain ⟨φ, hφ⟩ := exists_toLin_eq Φ hΦ
    refine ⟨(thetaN n t).inv.hom φ, ?_⟩
    change toLin ((thetaN n t).hom.hom ((thetaN n t).inv.hom φ)) = Φ
    have : (thetaN n t).hom.hom ((thetaN n t).inv.hom φ) = φ := by simp
    rw [this, hφ]

theorem natCard_ne_zero : (Nat.card (KT ⧸ principalSixInK) : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero

theorem mem_homK_iff (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n) :
    Φ ∈ homK (coeff n t) ↔ GroupHomology.IsEquivOn stK (coeffK n t) ⊤ Φ :=
  ⟨fun h k _ z => h k z, fun h k z => h k trivial z⟩

variable {n t}

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem card_ne_zero : (Fintype.card (KT ⧸ principalSixInK) : ℚ) ≠ 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_ne_zero

/-- **The K-equivariance of the neat-level duality** (the hypothesis of the CONDITIONAL reduction
below): the duality `Θ` of the library, transported to the copy of `Γ(6)` inside `K`, intertwines the
conjugation action `c_g` of `g ∈ K` on `H₃(Γ(6), E)` (Mathlib's functoriality for the pair
`(conj g, ρ(g))`) with the action `Φ ↦ ρ(g) ∘ Φ ∘ g⁻¹` on `Γ(6)`-equivariant functionals
`St → E`.  It is not proved. -/
def NeatDualityEquivariant (n : ℕ) (t : Fin 2) : Prop :=
  ∀ (g : KT) (x : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3),
    psi n t (cAct principalSixInK (EK n t) 3 g x) =
      GroupHomology.actL stK (coeffK n t) g (psi n t x)

theorem psi_avgN (h : NeatDualityEquivariant n t)
    (x : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    psi n t (avgN principalSixInK (EK n t) 3 x) =
      GroupHomology.avg stK (coeffK n t) principalSixInK (psi n t x) := by
  have h' : ∀ (g : KT) (x : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3),
      psi n t (cAct principalSixInK (EK n t) 3 g x) =
        GroupHomology.actL stK (coeffK n t) g (psi n t x) := h
  rw [GroupHomology.avg_eq_sum]
  unfold avgN
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, h']

theorem psi_avgN_mem (h : NeatDualityEquivariant n t)
    (x : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    psi n t (avgN principalSixInK (EK n t) 3 x) ∈ homK (coeff n t) := by
  rw [psi_avgN h, mem_homK_iff]
  exact GroupHomology.avg_isEquiv ((mem_range_psi_iff n t _).mp ⟨x, rfl⟩)

theorem corN_avgN (x : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    corN principalSixInK (EK n t) 3 (avgN principalSixInK (EK n t) 3 x) =
      corN principalSixInK (EK n t) 3 x := by
  unfold avgN
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, corN_cAct,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ card_ne_zero, one_smul]

/-- **CONDITIONAL.**  If the neat-level duality of the library is `K`-equivariant
(`NeatDualityEquivariant`), then `H₃(K, E_{n,t}) ≃ Hom_K(St, E_{n,t})`. -/
def kEquivOfEquivariance (h : NeatDualityEquivariant n t) :
    groupHomology (EK n t) 3 ≃ₗ[ℚ] homK (coeff n t) :=
  let E := LinearMap.range (avgN principalSixInK (EK n t) 3)
  have hfix : ∀ z ∈ E, avgN principalSixInK (EK n t) 3 z = z := by
    rintro _ ⟨w, rfl⟩
    exact avgN_idem card_ne_zero w
  let corE : E →ₗ[ℚ] groupHomology (EK n t) 3 :=
    (corN principalSixInK (EK n t) 3).domRestrict E
  let psiE : E →ₗ[ℚ] homK (coeff n t) :=
    LinearMap.codRestrict (homK (coeff n t)) ((psi n t).domRestrict E) (by
      rintro ⟨_, w, rfl⟩
      exact psi_avgN_mem h w)
  have hcorInj : Function.Injective corE := by
    intro z z' hzz
    have h1 : corN principalSixInK (EK n t) 3 (z.1 - z'.1) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hzz
    have h2 := (corN_eq_zero_iff card_ne_zero _).mp h1
    have h3 : avgN principalSixInK (EK n t) 3 (z.1 - z'.1) = z.1 - z'.1 := by
      rw [map_sub, hfix _ z.2, hfix _ z'.2]
    exact Subtype.ext (sub_eq_zero.mp (h3 ▸ h2))
  have hcorSurj : Function.Surjective corE := by
    intro w
    obtain ⟨z, rfl⟩ := corN_surjective (A := EK n t) (n := 3) card_ne_zero w
    exact ⟨⟨avgN principalSixInK (EK n t) 3 z, z, rfl⟩, corN_avgN z⟩
  have hpsiInj : Function.Injective psiE := fun z z' hzz =>
    Subtype.ext (psi_injective n t (congrArg Subtype.val hzz))
  have hpsiSurj : Function.Surjective psiE := by
    rintro ⟨Ψ, hΨ⟩
    have hΨ' := (mem_homK_iff n t Ψ).mp hΨ
    obtain ⟨y, hy⟩ := (mem_range_psi_iff n t Ψ).mpr (fun g hg z => hΨ' g trivial z)
    refine ⟨⟨avgN principalSixInK (EK n t) 3 y, y, rfl⟩, Subtype.ext ?_⟩
    change psi n t (avgN principalSixInK (EK n t) 3 y) = Ψ
    rw [psi_avgN h, hy]
    exact GroupHomology.avg_of_isEquiv_natCard hΨ' natCard_ne_zero
  (LinearEquiv.ofBijective corE ⟨hcorInj, hcorSurj⟩).symm.trans
    (LinearEquiv.ofBijective psiE ⟨hpsiInj, hpsiSurj⟩)

end Conditional

end TernaryPeriodPolynomials.Argument.FiberModel
