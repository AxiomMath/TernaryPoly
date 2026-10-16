module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.NeatSingular

@[expose] public section


/-!
# Finite-group descent of the singular `H²_c → H²` vanishing to groups with torsion

The paper proves the vanishing `H²_c → H²` (Proposition `ar:prop:coercivity`) for a neat normal
subgroup `Γ' ⊂ K ∩ SL₃(ℤ)` and then descends: "Put `Δ = K/Γ'`. Rational Hochschild-Serre and averaging
give `H₃(K, E_{n,t}) ≅ H₃(Γ', E_{n,t})_Δ`", "Determinant twists are trivial on `SL₃`,
and finite-group averaging descends a primitive from a neat normal cover", "The
conclusion holds for either determinant twist after descent from a neat normal subgroup".  Here `K = {g ∈ GL₃(ℤ) : ℓ g = ℓ (mod 3)}` has torsion and elements of
determinant `-1`, and `E_{n,t} = Sym^n((ℚ³)*) ⊗ det^{-t}`.

For a group `G` with torsion there is no quotient manifold, so `compactForget` is not defined.  The
equivariant cohomology (`H^*(G; V)` for contractible `Space`) is, however, the cohomology of
`G`-equivariant singular cochains on `Space`; this is exactly the function model of
`Singular/Intrinsic`.  `EquivSingularVanish G V` says: every closed `G`-equivariant degree-two simplex
function with values in the rational representation `V`, vanishing off `G · C` for a compact `C ⊂ Space`,
is the coboundary of a `G`-equivariant one-cochain.  For an admissible (free) group it is equivalent to
`SingularVanish` (`equivSingularVanish_iff`), so it is the correct extension of the statement.

* `equivSingularVanish_of_finiteIndex`: **rational transfer/averaging over `Γ/Γ'`**: vanishing for a
  finite-index subgroup `Γ'` with the restricted coefficients gives vanishing for `Γ` (characteristic
  zero; `Singular/Transfer.funVanish_of_res`).  Neither freeness nor normality is used.
* `equivSingularVanish_iff`: for admissible groups it is `SingularVanish`.
* `equivSingularVanish_real/dual/complex/complex_dual_of_descent`: the coefficient systems of
  `Variants/GeneralSingular` (the twist `det^e`, `e = -t`, is built into `realSystem κ n e`) for any
  `H ≤ GL₃(ℤ)` containing a neat determinant-one finite-index subgroup `H'`; the restriction of the
  system of `H` to `H'` is the system of `H'` (`intStructure_comp_inclusion`, `res_realSystem_int`).
* `equivSingularVanish_paper_*`, `equivSingularVanish_K`, `equivSingularVanish_kSL`,
  `equivSingularVanish_GL`: the groups of the paper, `K`, `K ∩ SL₃(ℤ)` and `GL₃(ℤ)`, with the neat normal
  cover `Γ' = Γ(6) ∩ SL₃(ℤ)` (`neatCover`, neat by `ConvergenceC4.gammaN_isNeat`); `paperCoefficient_apply`
  shows that `realSystem (intStructure H) n (-t)` is the paper's `g · f = det(g)^{-t} f(g⁻¹ x)`.

The smooth counterpart (primitive averaged over `Γ/Γ'`, real twist `det^{-e}`) is
`TierB/Descent.exists_twisted_primitive_of_normal`; the present file is the singular/rational one.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open CategoryTheory TopologicalSpace TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.IntegralGL3Congruence
open TernaryPoly.PolynomialGLAction (GL3 homogeneousAction)

section Equivariant

/-- The `G`-saturation `G · C` of a subset of `Space`. -/
def saturation (G : Subgroup RealGL) (C : Set Space) : Set Space :=
  {x | ∃ g : G, ∃ c ∈ C, g • c = x}

/-- **Equivariant compact-to-ordinary vanishing in degree two** for a (possibly non-free) subgroup `G`
of `GL₃(ℝ)` acting on `Space`: closed `G`-equivariant degree-two simplex functions vanishing off
`G · C` (`C` compact) are coboundaries of `G`-equivariant one-cochains. -/
def EquivSingularVanish (G : Subgroup RealGL) (V : Rep.{0} ℚ G) : Prop :=
  ∀ C : Set Space, IsCompact C →
    FunVanish (G := G) (E := TopCat.of Space) V (saturation G C)ᶜ

theorem funVanish_mono {G : Type} [Group G] {E : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
    (V : Rep.{0} ℚ G) {S S' : Set E} (h : S ⊆ S') (H : FunVanish (G := G) (E := E) V S) :
    FunVanish (G := G) (E := E) V S' := by
  intro f hf hv
  exact H f hf (fun σ hσ => hv σ (hσ.mono h))

/-- For an admissible group the equivariant statement is the actual singular one. -/
theorem equivSingularVanish_iff {Γ : Subgroup RealGL} (hΓ : Admissible Γ) (A : Rep.{0} ℚ Γ) :
    EquivSingularVanish Γ A ↔ SingularVanish Γ hΓ A := by
  let _ : Fact (IsQuotientCoveringMap (coverHom Γ) Γ) := ⟨hΓ.quotientCovering⟩
  unfold SingularVanish
  rw [compactForget_two_eq_zero_iff_funVanish]
  have := hΓ.t2
  constructor
  · intro H K
    obtain ⟨C, hC, hKC⟩ := exists_compact_lift (proj Γ) hΓ.isOpenMap_proj proj_surjective K.isCompact
    refine funVanish_mono A ?_ (H C hC)
    intro x hx hxK
    apply hx
    obtain ⟨c, hc, hcx⟩ := hKC hxK
    obtain ⟨γ, hγ⟩ := proj_eq_iff.mp hcx
    exact ⟨γ, c, hc, hγ⟩
  · intro H C hC
    have hK : IsCompact (proj Γ '' C) := hC.image continuous_proj
    have := H ⟨proj Γ '' C, hK⟩
    have e : (coverHom Γ) ⁻¹' ((proj Γ '' C : Set (OrbitSpace Γ)))ᶜ = (saturation Γ C)ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      apply not_congr
      constructor
      · rintro ⟨c, hc, hcx⟩
        obtain ⟨γ, hγ⟩ := proj_eq_iff.mp hcx
        exact ⟨γ, c, hc, hγ⟩
      · rintro ⟨γ, c, hc, rfl⟩
        exact ⟨c, hc, (proj_smul γ c).symm⟩
    change FunVanish (G := Γ) (E := TopCat.of Space) A ((coverHom Γ) ⁻¹' ((proj Γ '' C : Set (OrbitSpace Γ)))ᶜ) at this
    rw [e] at this
    exact this

/-- **Rational transfer/averaging over `Γ/Γ'`.**  Equivariant vanishing for a finite-index subgroup `Γ'`
with the restricted coefficients gives equivariant vanishing for `Γ` (characteristic zero).  Neither
freeness nor normality is used. -/
theorem equivSingularVanish_of_finiteIndex {Γ' Γ : Subgroup RealGL} (hle : Γ' ≤ Γ)
    [Finite (Γ ⧸ Γ'.subgroupOf Γ)] (V : Rep.{0} ℚ Γ)
    (h : EquivSingularVanish Γ' (Rep.res (Subgroup.inclusion hle) V)) : EquivSingularVanish Γ V := by
  classical
  intro C hC
  obtain ⟨R, hR⟩ := exists_right_transversal (Γ'.subgroupOf Γ)
  let D : Set Space := ⋃ r ∈ R, (fun S => r • S) '' C
  have hD : IsCompact D := R.isCompact_biUnion fun r _ => hC.image (continuous_const_smul r)
  have e : saturation Γ C = saturation Γ' D := by
    ext x
    constructor
    · rintro ⟨g, c, hc, rfl⟩
      obtain ⟨r, hrR, k, hk, hgk⟩ := hR g
      refine ⟨⟨k.1, hk⟩, r • c, Set.mem_iUnion₂.mpr ⟨r, hrR, c, hc, rfl⟩, ?_⟩
      rw [hgk, mul_smul]
      rfl
    · rintro ⟨γ, d, hd, rfl⟩
      obtain ⟨r, hrR, c, hc, rfl⟩ := Set.mem_iUnion₂.mp hd
      exact ⟨Subgroup.inclusion hle γ * r, c, hc, by rw [mul_smul]; rfl⟩
  have := h D hD
  rw [← e] at this
  have hfin : Finite (Γ ⧸ (Subgroup.inclusion hle).range) := by
    have e2 : (Subgroup.inclusion hle).range = Γ'.subgroupOf Γ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x.1, hx⟩, rfl⟩
    rw [e2]; exact inferInstance
  exact funVanish_of_res (Subgroup.inclusion hle) (fun _ _ => rfl) _ this

end Equivariant


section Integral

variable {H' H : Subgroup IntegralGL} (hHH : H' ≤ H)

theorem intStructure_comp_inclusion :
    (intStructure H).comp (Subgroup.inclusion (Subgroup.map_mono (f := realIntegral) hHH)) =
      intStructure H' := by
  apply MonoidHom.ext
  intro y
  have h1 := (Subgroup.equivMapOfInjective H realIntegral realIntegral_injective).apply_symm_apply
    (Subgroup.inclusion (Subgroup.map_mono (f := realIntegral) hHH) y)
  have h2 := (Subgroup.equivMapOfInjective H' realIntegral realIntegral_injective).apply_symm_apply y
  have h3 : ((Subgroup.equivMapOfInjective H realIntegral realIntegral_injective).symm
      (Subgroup.inclusion (Subgroup.map_mono (f := realIntegral) hHH) y) : IntegralGL) =
      ((Subgroup.equivMapOfInjective H' realIntegral realIntegral_injective).symm y : IntegralGL) := by
    apply realIntegral_injective
    have a := congrArg Subtype.val h1
    have b := congrArg Subtype.val h2
    rw [Subgroup.coe_equivMapOfInjective_apply] at a b
    exact a.trans b.symm
  change embZ ((Subgroup.equivMapOfInjective H realIntegral realIntegral_injective).symm
      (Subgroup.inclusion (Subgroup.map_mono (f := realIntegral) hHH) y) : IntegralGL) =
    embZ ((Subgroup.equivMapOfInjective H' realIntegral realIntegral_injective).symm y : IntegralGL)
  rw [h3]

theorem res_realSystem_int (n : ℕ) (e : ℤ) :
    Rep.res (Subgroup.inclusion (Subgroup.map_mono (f := realIntegral) hHH))
        (realSystem (intStructure H) n e) = realSystem (intStructure H') n e := by
  change Rep.of ((homogeneousAction n e).comp ((intStructure H).comp _)) = _
  rw [intStructure_comp_inclusion hHH]
  rfl

theorem res_dualSystem_int (n : ℕ) :
    Rep.res (Subgroup.inclusion (Subgroup.map_mono (f := realIntegral) hHH))
        (dualSystem (intStructure H) n) = dualSystem (intStructure H') n := by
  change Rep.of ((dualAction n).comp ((intStructure H).comp _)) = _
  rw [intStructure_comp_inclusion hHH]
  rfl

include hHH in
theorem finite_quotient_map_realIntegral [H'.FiniteIndex] :
    Finite (H.map realIntegral ⧸ (H'.map realIntegral).subgroupOf (H.map realIntegral)) := by
  apply finite_quotient_of_relIndex
  rw [Subgroup.relIndex_map_map_of_injective H' H realIntegral_injective]
  exact ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero
    (Subgroup.relIndex_dvd_index_of_le hHH)

theorem res_doubleRep {G H : Type} [Group G] [Group H] (φ : H →* G) (B : Rep.{0} ℚ G) :
    Rep.res φ (doubleRep B) = doubleRep (Rep.res φ B) := rfl

theorem intStructure_apply (g : H) :
    intStructure H ⟨realIntegral g, ⟨g, g.2, rfl⟩⟩ = embZ g := by
  change embZ ((Subgroup.equivMapOfInjective H realIntegral realIntegral_injective).symm
    ⟨realIntegral g, ⟨g, g.2, rfl⟩⟩ : IntegralGL) = _
  congr 2
  rw [MulEquiv.symm_apply_eq]
  rfl

section Systems

variable [H'.FiniteIndex] (hdet : ∀ h ∈ H', h.val.det = 1) (htf : ∀ h ∈ H', IsOfFinOrder h → h = 1)
  {n : ℕ} (hn : 0 < n)

include hHH hdet htf hn in
/-- **Descent, real coefficients with the determinant twist** `E_{n,t}`, `e = -t`: equivariant
vanishing for `H ≥ H'` from the neat determinant-one finite-index subgroup `H'`. -/
theorem equivSingularVanish_real_of_descent (e : ℤ) :
    EquivSingularVanish (H.map realIntegral) (realSystem (intStructure H) n e) := by
  have := finite_quotient_map_realIntegral hHH
  apply equivSingularVanish_of_finiteIndex (Subgroup.map_mono (f := realIntegral) hHH)
  rw [res_realSystem_int hHH]
  exact (equivSingularVanish_iff (admissible_map_realIntegral_of_torsionFree H' hdet htf) _).mpr
    (singularVanish_tf_real H' hdet htf hn e)

include hHH hdet htf hn in
/-- **Descent, dual coefficients.** -/
theorem equivSingularVanish_dual_of_descent :
    EquivSingularVanish (H.map realIntegral) (dualSystem (intStructure H) n) := by
  have := finite_quotient_map_realIntegral hHH
  apply equivSingularVanish_of_finiteIndex (Subgroup.map_mono (f := realIntegral) hHH)
  rw [res_dualSystem_int hHH]
  exact (equivSingularVanish_iff (admissible_map_realIntegral_of_torsionFree H' hdet htf) _).mpr
    (singularVanish_tf_dual H' hdet htf hn)

include hHH hdet htf hn in
/-- **Descent, complex coefficients (doubled rational model).** -/
theorem equivSingularVanish_complex_of_descent (e : ℤ) :
    EquivSingularVanish (H.map realIntegral) (complexSystem (intStructure H) n e) := by
  have := finite_quotient_map_realIntegral hHH
  apply equivSingularVanish_of_finiteIndex (Subgroup.map_mono (f := realIntegral) hHH)
  rw [res_doubleRep, res_realSystem_int hHH]
  exact (equivSingularVanish_iff (admissible_map_realIntegral_of_torsionFree H' hdet htf) _).mpr
    (singularVanish_tf_complex H' hdet htf hn e)

include hHH hdet htf hn in
/-- **Descent, complexified dual coefficients (doubled rational model); also the literal dual.** -/
theorem equivSingularVanish_complex_dual_of_descent :
    EquivSingularVanish (H.map realIntegral) (complexDualSystem (intStructure H) n) := by
  have := finite_quotient_map_realIntegral hHH
  apply equivSingularVanish_of_finiteIndex (Subgroup.map_mono (f := realIntegral) hHH)
  rw [res_doubleRep, res_dualSystem_int hHH]
  exact (equivSingularVanish_iff (admissible_map_realIntegral_of_torsionFree H' hdet htf) _).mpr
    (singularVanish_tf_complex_dual H' hdet htf hn)

end Systems

end Integral


/-! ### The groups of the paper: `K`, `K ∩ SL₃(ℤ)`, `GL₃(ℤ)` -/

section Paper

open scoped MatrixGroups

/-- The determinant-one subgroup of `GL₃(ℤ)`. -/
def slSubgroup : Subgroup IntegralGL := (Matrix.GeneralLinearGroup.det : IntegralGL →* ℤˣ).ker

/-- `K ∩ SL₃(ℤ)`, where `K = {g : ℓ g = ℓ (mod 3)}`. -/
def kSL : Subgroup IntegralGL := TernaryPoly.ModThreeGoodAction.K ⊓ slSubgroup

/-- The neat normal congruence subgroup `Γ' = Γ(6) ∩ SL₃(ℤ)` used for the descent. -/
abbrev neatCover : Subgroup IntegralGL := toGLSubgroup (ConvergenceC4.gammaN 6)

instance neatCover_finiteIndex : neatCover.FiniteIndex := by
  have : NeZero (6 : ℕ) := ⟨by norm_num⟩
  have := finiteIndex_gammaN 6
  exact finiteIndex_toGLSubgroup _

theorem neatCover_isNeat : IsNeat neatCover :=
  isNeat_toGLSubgroup (ConvergenceC4.gammaN_isNeat (by norm_num))

theorem neatCover_le_K : neatCover ≤ TernaryPoly.ModThreeGoodAction.K := by
  rintro _ ⟨γ, hγ, rfl⟩
  have : (Matrix.SpecialLinearGroup.toGL γ) ∈ principal 6 := hγ
  exact principalSix_le_K this

theorem neatCover_le_kSL : neatCover ≤ kSL := by
  intro x hx
  refine ⟨neatCover_le_K hx, ?_⟩
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  exact toGLSubgroup_det _ x hx

section Systems

variable {H : Subgroup IntegralGL} (hH : neatCover ≤ H) {n : ℕ} (hn : 0 < n)

include hH hn in
/-- **Descent from the neat normal cover `Γ(6) ∩ SL₃(ℤ)` to any `H ⊇ Γ(6) ∩ SL₃(ℤ)` of `GL₃(ℤ)`
(in particular `K`, `K ∩ SL₃(ℤ)`, `GL₃(ℤ)`), real coefficients `E_{n,t}`, `e = -t`.** -/
theorem equivSingularVanish_paper_real (e : ℤ) :
    EquivSingularVanish (H.map realIntegral) (realSystem (intStructure H) n e) :=
  equivSingularVanish_real_of_descent hH (toGLSubgroup_det _) neatCover_isNeat.torsionFree hn e

include hH hn in
/-- Dual coefficients. -/
theorem equivSingularVanish_paper_dual :
    EquivSingularVanish (H.map realIntegral) (dualSystem (intStructure H) n) :=
  equivSingularVanish_dual_of_descent hH (toGLSubgroup_det _) neatCover_isNeat.torsionFree hn

include hH hn in
/-- Complex coefficients (doubled rational model). -/
theorem equivSingularVanish_paper_complex (e : ℤ) :
    EquivSingularVanish (H.map realIntegral) (complexSystem (intStructure H) n e) :=
  equivSingularVanish_complex_of_descent hH (toGLSubgroup_det _) neatCover_isNeat.torsionFree hn e

include hH hn in
/-- Complexified dual coefficients (doubled rational model). -/
theorem equivSingularVanish_paper_complex_dual :
    EquivSingularVanish (H.map realIntegral) (complexDualSystem (intStructure H) n) :=
  equivSingularVanish_complex_dual_of_descent hH (toGLSubgroup_det _) neatCover_isNeat.torsionFree hn

end Systems

/-- **`K`, with the determinant twist `E_{n,t}`** (`e = -t`; `K` contains elements of determinant `-1`
and torsion). -/
theorem equivSingularVanish_K (n : ℕ) (hn : 0 < n) (e : ℤ) :
    EquivSingularVanish (TernaryPoly.ModThreeGoodAction.K.map realIntegral)
      (realSystem (intStructure TernaryPoly.ModThreeGoodAction.K) n e) :=
  equivSingularVanish_paper_real neatCover_le_K hn e

/-- **`K ∩ SL₃(ℤ)`.** -/
theorem equivSingularVanish_kSL (n : ℕ) (hn : 0 < n) (e : ℤ) :
    EquivSingularVanish (kSL.map realIntegral) (realSystem (intStructure kSL) n e) :=
  equivSingularVanish_paper_real neatCover_le_kSL hn e

/-- **`G = GL₃(ℤ)`.** -/
theorem equivSingularVanish_GL (n : ℕ) (hn : 0 < n) (e : ℤ) :
    EquivSingularVanish ((⊤ : Subgroup IntegralGL).map realIntegral)
      (realSystem (intStructure ⊤) n e) :=
  equivSingularVanish_paper_real (le_top) hn e

/-- The coefficient module of the paper: for `g ∈ H` the rational representation
`realSystem (intStructure H) n (-t)` acts by `g · f = det(g)^{-t} f(g⁻¹ x)`. -/
theorem paperCoefficient_apply (H : Subgroup IntegralGL) (n : ℕ) (t : ℤ) (g : H)
    (f : MvPolynomial (Fin 3) ℚ) (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℚ n) :
    Subtype.val (((realSystem (intStructure H) n (-t)).ρ ⟨realIntegral g, ⟨g, g.2, rfl⟩⟩)
        (⟨f, hf⟩ : TernaryPoly.PolynomialGLAction.HomogeneousPoly n)) =
      TernaryPoly.PolynomialGLAction.determinantCharacter (-t) (embZ g) •
        TernaryPoly.PolynomialGLAction.substitute (((embZ g)⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℚ) f := by
  change TernaryPoly.PolynomialGLAction.action (-t) (intStructure H ⟨realIntegral g, ⟨g, g.2, rfl⟩⟩) f = _
  rw [intStructure_apply, TernaryPoly.PolynomialGLAction.action_apply]

end Paper

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
