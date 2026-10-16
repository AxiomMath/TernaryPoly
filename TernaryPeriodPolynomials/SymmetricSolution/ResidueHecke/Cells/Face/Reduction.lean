module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.NeatAverage
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.ShapiroLof

@[expose] public section


/-!
# Lemma B.1, boundary route: the reduction of `PHCompat` to the neat-level statement `FaceEval`

Formalized by Claude Sonnet 5.5.

With `N = Γ(6)`, `P_N = P_H ∩ N` (normal of finite index in `P_H`), `ι_* : H₃(P_N, 𝓡_{n,H₀}) → H₃(N, 𝓡_n)` and
`cor` the corestrictions:

* (a) (`ShapiroLof`) `Sh⁻¹ = cor^G_{P_H} ∘ lof_*`;
* `cor_compat`: `lof_* (cor^{P_H}_{P_N} y) = cor^G_N (ι_* y)`, and every class of `H₃(G, 𝓡_n)` is of the form `lof_* (cor^{P_H}_{P_N} y)`;
* `resHLit_cor_lof` (from `resHLit_corN`): `res_H` of such a class is `[G:N]⁻¹ ∑_{q ∈ G/N} termF y q`, where
  `termF y g` is the literal `a = 0` residue `lit₀(comp₀(ρ(g) Θ_N(ι_* y)(g⁻¹ σ₀)))`;
* (b) `sum_termF_collapse`: if `termF y g = 0` for `g ∉ P_H · N`, the sum collapses to `P_H/P_N`;
* `FaceEval n` states the vanishing together with the identification of the collapsed sum with `c · edge₂ κ (cor y)`;
* `phCompat_of_faceEval : FaceEval n → PHCompat n`.

The module is unconditional: `FaceEval` is a hypothesis of `phCompat_of_faceEval`, not an axiom.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology

/-- `P_N = P_H ∩ Γ(6)` as a subgroup of `P_H`. -/
def PN : Subgroup PH := principalSix.comap PH.subtype

instance : PN.Normal := Subgroup.Normal.comap inferInstance _

instance : PN.FiniteIndex :=
  ⟨by
    unfold PN
    rw [Subgroup.index_comap]
    exact ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero
      (Subgroup.relIndex_dvd_index_of_normal _ _)⟩

/-- The inclusion `P_N → Γ(6)`. -/
def jPN : PN →* principalSix :=
  (PH.subtype.comp PN.subtype).codRestrict principalSix (fun p => p.2)

/-- The coefficient map `Res_{P_N} 𝓡_{n,H₀} → Res_{P_N} Res_{Γ(6)} 𝓡_n` (`lof` restricted to `P_N`). -/
def lofN (n : ℕ) :
    Rep.res PN.subtype (FibRep n) ⟶ Rep.res jPN (Rep.res principalSix.subtype (ResRep n)) :=
  (Rep.resFunctor PN.subtype).map (lofHom n)

/-- `ι_* : H₃(P_N, 𝓡_{n,H₀}) → H₃(Γ(6), 𝓡_n)`. -/
def iotaStar (n : ℕ) :
    groupHomology (Rep.res PN.subtype (FibRep n)) 3 →ₗ[ℚ]
      groupHomology (Rep.res principalSix.subtype (ResRep n)) 3 :=
  (groupHomology.map jPN (lofN n) 3).hom

theorem cor_compat (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    (groupHomology.map PH.subtype (lofHom n) 3).hom (corN PN (FibRep n) 3 y) =
      corN principalSix (ResRep n) 3 (iotaStar n y) := by
  have h1 := groupHomology.map_comp (k := ℚ) PN.subtype PH.subtype (𝟙 (Rep.res PN.subtype (FibRep n)))
    (lofHom n) 3
  have h2 := groupHomology.map_comp (k := ℚ) jPN principalSix.subtype (lofN n)
    (𝟙 (Rep.res principalSix.subtype (ResRep n))) 3
  have hf : PH.subtype.comp PN.subtype = principalSix.subtype.comp jPN := MonoidHom.ext fun _ => rfl
  have h3 := groupHomology.map_congr (k := ℚ) (B := ResRep n) (f := PH.subtype.comp PN.subtype) (g := principalSix.subtype.comp jPN) hf
    (φ := 𝟙 (Rep.res PN.subtype (FibRep n)) ≫ (Rep.resFunctor PN.subtype).map (lofHom n))
    (ψ := lofN n ≫ (Rep.resFunctor jPN).map (𝟙 (Rep.res principalSix.subtype (ResRep n))))
    (by ext; rfl) 3
  exact congrArg (fun m => m.hom y) (h1.symm.trans (h3.trans h2))

open TernaryPoly.SinglePoleCoordinate
open TernaryPoly.OrdinaryResidueSupport (axis)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The neat-level duality functional of `ι_* y`. -/
abbrev psiN (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResRep n :=
  psiGen principalSix (MulEquiv.refl ↥principalSix) (ResRep n) (iotaStar n y)

/-- The literal `a = 0` residue (`lit₀ ∘ comp₀`) of the translate `ρ(g) Ψ(g⁻¹ σ₀)` of the neat functional
`Ψ = Θ_N(ι_* y)` on the identity apartment `σ₀`. -/
def termF (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) (g : IntegralGL) :
    BinaryV (n + 1) :=
  literalFiberMap n 0 (SinglePoleSupport.component n (axis 0)
    (TernaryPeriodPolynomials.Argument.GroupHomology.term stG (ResRep n).ρ (psiN n y) g (OrdinaryApartmentPresentation.frameCycle 1)))

theorem resHLit_cor_lof (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    ((resHLit n ((groupHomology.map PH.subtype (lofHom n) 3).hom (corN PN (FibRep n) 3 y)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) =
      ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹) • ∑ q : IntegralGL ⧸ principalSix, termF n y q.out := by
  rw [cor_compat, resHLit_corN]
  simp only [map_smul, map_sum]
  rfl

/-- `g ∈ P_H · Γ(6)`. -/
def InPHN (g : IntegralGL) : Prop := ∃ s ∈ PH, ∃ m ∈ principalSix, g = s * m

theorem termF_mk_eq (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) {g g' : IntegralGL}
    (h : (g : IntegralGL ⧸ principalSix) = g') : termF n y g = termF n y g' := by
  have hΦ := (mem_range_psiGen_iff principalSix (MulEquiv.refl ↥principalSix) stG (ResRep n)
    (fun n => stG_principal n) (psiN n y)).mp ⟨_, rfl⟩
  exact congrArg (fun v => literalFiberMap n 0 (SinglePoleSupport.component n (axis 0) v))
    (term_eq_of_mk_eq hΦ h _)

/-- The class map `P_H/P_N → G/Γ(6)`. -/
def jQuot : PH ⧸ PN →* IntegralGL ⧸ principalSix :=
  QuotientGroup.map PN principalSix PH.subtype le_rfl

theorem jQuot_mk (s : PH) : jQuot (s : PH ⧸ PN) = ((s : IntegralGL) : IntegralGL ⧸ principalSix) := rfl

theorem jQuot_injective : Function.Injective jQuot := by
  intro a b hab
  induction a using QuotientGroup.induction_on with
  | H a' =>
    induction b using QuotientGroup.induction_on with
    | H b' =>
      rw [jQuot_mk, jQuot_mk, QuotientGroup.eq] at hab
      refine QuotientGroup.eq.mpr ?_
      show ((a'⁻¹ * b' : PH) : IntegralGL) ∈ principalSix
      simpa using hab

/-- **(b) The collapse of the translate average**: if the translates of the neat functional of `ι_* y`
by elements outside `P_H · Γ(6)` have zero `a = 0` residue, the average over `G/Γ(6)` reduces to the one over
`P_H/P_N`. -/
theorem sum_termF_collapse (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3)
    (hvan : ∀ g : IntegralGL, ¬ InPHN g → termF n y g = 0) :
    ∑ q : IntegralGL ⧸ principalSix, termF n y q.out = ∑ s : PH ⧸ PN, termF n y ((s.out : PH) : IntegralGL) := by
  classical
  have h1 : ∑ q : IntegralGL ⧸ principalSix, termF n y q.out =
      ∑ q ∈ Finset.univ.image jQuot, termF n y q.out := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun q _ hq => ?_).symm
    apply hvan
    rintro ⟨s, hs, m, hm, hqm⟩
    apply hq
    rw [Finset.mem_image]
    refine ⟨(⟨s, hs⟩ : PH), Finset.mem_univ _, ?_⟩
    rw [jQuot_mk]
    have : ((q.out : IntegralGL) : IntegralGL ⧸ principalSix) = q := QuotientGroup.out_eq' q
    rw [← this, hqm]
    exact QuotientGroup.eq.mpr (by simpa using hm)
  rw [h1, Finset.sum_image (fun a _ b _ hab => jQuot_injective hab)]
  refine Finset.sum_congr rfl fun s _ => termF_mk_eq n y ?_
  rw [QuotientGroup.out_eq']
  conv_lhs => rw [← QuotientGroup.out_eq' s]
  rfl

/-- **`FaceEval`**: the single remaining statement of Lemma B.1 (neat level).  For every class
`y ∈ H₃(P_N, 𝓡_{n,H₀})` (`P_N = P_H ∩ Γ(6)`), with `Ψ = Θ_N(ι_* y)` the neat-level Borel-Serre functional of `ι_* y ∈ H₃(Γ(6), 𝓡_n)`
and `σ₀` the identity apartment:

* (support) the `a = 0` residue of `ρ(g) Ψ(g⁻¹ σ₀)` vanishes for `g ∉ P_H · Γ(6)`;
* (face evaluation) the sum over `P_H/P_N` of these residues is `c · edge₂(κ(cor_{P_N}^{P_H} y))`, for one `c ≠ 0`. -/
def FaceEval (n : ℕ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ ∀ y : groupHomology (Rep.res PN.subtype (FibRep n)) 3,
    (∀ g : IntegralGL, ¬ InPHN g → termF n y g = 0) ∧
    ∑ s : PH ⧸ PN, termF n y ((s.out : PH) : IntegralGL) =
      c • (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (corN PN (FibRep n) 3 y)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1))

/-- **`PHCompat` follows from `FaceEval`.** -/
theorem phCompat_of_faceEval (n : ℕ) (h : FaceEval n) : PHCompat n := by
  obtain ⟨c, hc, hF⟩ := h
  refine ⟨(Fintype.card (IntegralGL ⧸ principalSix) : ℚ) / c,
    div_ne_zero (card_ne_zero_gen principalSix) hc, fun x => ?_⟩
  obtain ⟨y, hy⟩ := corN_surjective (A := FibRep n) (n := 3) (N := PN) (card_ne_zero_gen PN)
    (shLit n x)
  have hx : x = (groupHomology.map PH.subtype (lofHom n) 3).hom (corN PN (FibRep n) 3 y) := by
    rw [hy]
    have h1 := congrArg (fun m => m x) (shapiroHomologyIso n 3).hom_inv_id
    refine h1.symm.trans ?_
    rw [shapiroHomologyIso_inv]
    rfl
  obtain ⟨hvan, hsum⟩ := hF y
  apply Subtype.ext
  have e1 : ((residuePeriodAlg n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) =
      (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (corN PN (FibRep n) 3 y)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) := by
    unfold residuePeriodAlg
    change (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (shLit n x)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) = _
    rw [← hy]
  have e2 := resHLit_cor_lof n y
  rw [← hx, sum_termF_collapse n y hvan, hsum] at e2
  rw [e1]
  change _ = ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ) / c) •
    ((resHLit n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1))
  rw [e2, smul_smul, smul_smul]
  have hcard := card_ne_zero_gen principalSix
  rw [show ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ) / c) * ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹) * c = 1 by
    field_simp]
  rw [one_smul]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
