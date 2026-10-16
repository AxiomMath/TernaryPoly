module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.TranslateContributions
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellRep
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonApartment

@[expose] public section


/-!
# Lemma 3.3, G3 S4: the coefficient at the standard cell and the translate sum

`coeffAtT0 W : (W ⊗ cells₃)_{Γ(6)} → W` sends the coinvariant class `[w ⊗ C]` to `ρ(g) w` for the unique
`g ∈ Γ(6)` with `g • C = T₀` (the action on cells is free, `translate_unique`), and to `0` if no translate of `C`
is `T₀`.  Conventions: the coinvariant relation is `[ρ(h) w ⊗ h • C] = [w ⊗ C]`, so the cell `g⁻¹ • T₀`
carries the coefficient `ρ(g) w` (`coeffAtT0_translate`): the cell moves by `g⁻¹`, the coefficient by `g`.
No other choice is well defined on coinvariants.

`localDeg`, `degπ'_translate`, `translate_sum`: the local degree of a translate `g • C` of a cell along the
unipotent projection is `dT0` if `g • C = T₀` and `0` otherwise (`translate_off_flat`), so the finite sum over
the translates is `dT0 · coeffVal`; this is the finite translate sum, with trivial stabilizers.  `intersectionSum`
is `dT0 • coeffAtT0` and `intersectionSum_mk` says it is the translate sum of local degrees.

`FlatIntersectionBridge κ` is the global bridge in the form it must be proved: evaluator of the cellular class
equals `κ` times the intersection sum.  It is a hypothesis here.  `evaluation_eq_coeffAtT0` is the dictionary conditional on it.  `kappa_mul_dT0_ne_zero` and
`dT0_ne_zero_of_bridge` give the acyclic derivation of `κ ≠ 0 ∧ dT0 ≠ 0` from the bridge with some constant,
the surjectivity of `cellGroupHomologyMap W 3` and the non-vanishing of `groupApartmentEvaluation W`.  The
orientation convention (sign of `κ`, product orientation of the unipotent projection) and the paper's signed
`+1` (`κ * dT0 = ±1`) are NOT addressed here.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open CategoryTheory Limits HomologicalComplex TernaryPoly.ContractibleSingularHomology
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalRelativeSingular
open Finsupp GeneralEisenstein TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.OrdinaryTopBoundaryComparison
  TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

/-- `T₀` as a cell of grade three. -/
def T0g : Graded 3 := ⟨T0, T0_grade⟩

variable (W : Rep.{0} ℚ principalSix)

/-- The coefficient of a coinvariant generator `w ⊗ C` at `T₀`: `ρ(g) w` when `g • C = T₀`, else `0`. -/
def coeffVal (w : W) (C : Graded 3) : W :=
  if h : ∃ g : principalSix, g • C = T0g then W.ρ h.choose w else 0

theorem coeffVal_eq (w : W) (C : Graded 3) (g : principalSix) (hg : g • C = T0g) :
    coeffVal W w C = W.ρ g w := by
  have h : ∃ g : principalSix, g • C = T0g := ⟨g, hg⟩
  rw [coeffVal, dite_eq_left h]
  have := translate_unique h.choose g C.1 (congrArg Subtype.val h.choose_spec) (congrArg Subtype.val hg)
  rw [this]

theorem coeffVal_eq_zero (w : W) (C : Graded 3) (h : ¬ ∃ g : principalSix, g • C = T0g) :
    coeffVal W w C = 0 := by
  rw [coeffVal, dite_eq_right h]

theorem coeffVal_smul (g : principalSix) (w : W) (C : Graded 3) :
    coeffVal W (W.ρ g w) (g • C) = coeffVal W w C := by
  by_cases h : ∃ g' : principalSix, g' • C = T0g
  · obtain ⟨g', hg'⟩ := h
    have h2 : (g' * g⁻¹) • (g • C) = T0g := by rw [mul_smul, inv_smul_smul, hg']
    rw [coeffVal_eq W _ _ _ h2, coeffVal_eq W _ _ _ hg']
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  · have h2 : ¬ ∃ g'' : principalSix, g'' • (g • C) = T0g := by
      rintro ⟨g'', hg''⟩
      exact h ⟨g'' * g, by rw [mul_smul]; exact hg''⟩
    rw [coeffVal_eq_zero W _ _ h, coeffVal_eq_zero W _ _ h2]

theorem coeffVal_add (w w' : W) (C : Graded 3) :
    coeffVal W (w + w') C = coeffVal W w C + coeffVal W w' C := by
  by_cases h : ∃ g' : principalSix, g' • C = T0g
  · obtain ⟨g', hg'⟩ := h
    simp only [coeffVal_eq W _ _ _ hg', map_add]
  · simp [coeffVal_eq_zero W _ _ h]

theorem coeffVal_smul' (a : ℚ) (w : W) (C : Graded 3) :
    coeffVal W (a • w) C = a • coeffVal W w C := by
  by_cases h : ∃ g' : principalSix, g' • C = T0g
  · obtain ⟨g', hg'⟩ := h
    simp only [coeffVal_eq W _ _ _ hg', map_smul]
  · simp [coeffVal_eq_zero W _ _ h]


/-- `coeffVal` as a linear map in `w`. -/
def coeffLin (C : Graded 3) : W →ₗ[ℚ] W where
  toFun w := coeffVal W w C
  map_add' w w' := coeffVal_add W w w' C
  map_smul' a w := coeffVal_smul' W a w C

/-- The bilinear form `(w, x) ↦ ∑ x_C · coeff(w ⊗ C)` on `W × ℚ[Graded 3]`. -/
def coeffBil : W →ₗ[ℚ] (Graded 3 →₀ ℚ) →ₗ[ℚ] W :=
  (Finsupp.lsum (S := ℚ) (R := ℚ) (M := ℚ) (N := W) (α := Graded 3)).toLinearMap ∘ₗ
    LinearMap.pi (fun C : Graded 3 => (LinearMap.ringLmapEquivSelf ℚ ℚ W).symm.toLinearMap ∘ₗ coeffLin W C)

theorem coeffBil_single (w : W) (C : Graded 3) (a : ℚ) :
    coeffBil W w (single C a) = a • coeffVal W w C := by
  simp [coeffBil, coeffLin]

/-- The linear form on `W ⊗ ℚ[cells of grade 3]`. -/
def coeffTensor : TensorProduct ℚ W (cellRep 3) →ₗ[ℚ] W :=
  TensorProduct.lift ((coeffBil W).compl₂ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)

theorem coeffTensor_tmul (w : W) (x : cellRep 3) :
    coeffTensor W (w ⊗ₜ[ℚ] x) = coeffBil W w (MonoidAlgebra.coeffLinearEquiv ℚ x) := by
  simp [coeffTensor]

theorem coeffTensor_invariant (g : principalSix) :
    coeffTensor W ∘ₗ (W.ρ.tprod (cellRep 3).ρ g) = coeffTensor W := by
  apply TensorProduct.ext'
  intro w x
  rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul, coeffTensor_tmul, coeffTensor_tmul]
  have key : ∀ y : Graded 3 →₀ ℚ, coeffBil W (W.ρ g w)
      ((MonoidAlgebra.coeffLinearEquiv ℚ) ((cellRep 3).ρ g ((MonoidAlgebra.coeffLinearEquiv ℚ).symm y))) =
      coeffBil W w y := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single C a =>
      have e : (MonoidAlgebra.coeffLinearEquiv ℚ) ((cellRep 3).ρ g ((MonoidAlgebra.coeffLinearEquiv ℚ).symm
          (single C a))) = single (g • C) a := by
        have h2 := congrArg (MonoidAlgebra.coeffLinearEquiv ℚ)
          (Representation.ofMulAction_single (k := ℚ) g C a)
        exact h2
      rw [e, coeffBil_single, coeffBil_single, coeffVal_smul]
  simpa using key (MonoidAlgebra.coeffLinearEquiv ℚ x)

/-- **The coefficient at `T₀`**: the functional `(W ⊗ cells₃)_{Γ(6)} → W` sending the coinvariant class
`[w ⊗ C]` to `ρ(g) w` when `g • C = T₀` (the unique such `g`, by freeness) and to `0` otherwise.  Well defined
because `[ρ(h) w ⊗ h • C] = [w ⊗ C]` and `ρ(g h⁻¹) ρ(h) = ρ(g)`. -/
def coeffAtT0 : (cellCoinv W).X 3 ⟶ ModuleCat.of ℚ W :=
  ModuleCat.ofHom (Representation.Coinvariants.lift _ (coeffTensor W) (coeffTensor_invariant W))

theorem coeffAtT0_mk (w : W) (C : Graded 3) :
    (coeffAtT0 W).hom (Rep.coinvariantsTensorMk W (cellRep 3) w (MonoidAlgebra.single C 1)) =
      coeffVal W w C := by
  change coeffTensor W (w ⊗ₜ[ℚ] (MonoidAlgebra.single C (1 : ℚ))) = _
  rw [coeffTensor_tmul]
  have h : (MonoidAlgebra.coeffLinearEquiv ℚ) (MonoidAlgebra.single C (1 : ℚ)) =
      (single C 1 : Graded 3 →₀ ℚ) := rfl
  rw [h, coeffBil_single, one_smul]

/-- The coefficient of the generator `[w ⊗ g⁻¹ • T₀]` is `ρ(g) w` (sign of the action: the cell moves by `g⁻¹`,
the coefficient by `g`). -/
theorem coeffAtT0_translate (w : W) (g : principalSix) :
    (coeffAtT0 W).hom (Rep.coinvariantsTensorMk W (cellRep 3) w
      (MonoidAlgebra.single (g⁻¹ • T0g) 1)) = W.ρ g w := by
  rw [coeffAtT0_mk, coeffVal_eq W w _ g (smul_inv_smul g T0g)]

theorem coeffAtT0_of_ne (w : W) (C : Graded 3) (h : ∀ g : principalSix, g • C ≠ T0g) :
    (coeffAtT0 W).hom (Rep.coinvariantsTensorMk W (cellRep 3) w (MonoidAlgebra.single C 1)) = 0 := by
  rw [coeffAtT0_mk, coeffVal_eq_zero W w C (by rintro ⟨g, hg⟩; exact h g hg)]

/-! ### Local degrees of translates and the finite translate sum -/

/-- The local degree of the cell `D` (as a lift to the symmetric space) along the unipotent projection:
`dT0` for the standard cell `T₀` and `0` for every other cell. -/
def localDeg (D : Cell) : ℚ := if D = T0 then dT0 else 0

/-- The total version of `degπ`: the local degree of a lifted 3-chain, `0` when the chain does not have a
boundary missing the flat. -/
def degπ' (c : (chains TernaryPoly.SymmetricSpacePositive.Space).X 3) : ℚ :=
  if h : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c) = 0 then degπ c h else 0

theorem degπ'_translate (g : principalSix) (C : Cell) :
    degπ' (cellAtSpace 3 (g • C)) = localDeg (g • C) := by
  by_cases e : g • C = T0
  · rw [localDeg, ite_eq_left e, degπ', dite_eq_left (by rw [e]; exact cycle_T0)]
    have : ∀ (D : Cell) (hD : D = T0) (h : ((localChains 3).d 3 2).hom ((locRel.f 3).hom (cellAtSpace 3 D)) = 0),
        degπ (cellAtSpace 3 D) h = dT0 := by
      intro D hD h
      subst hD
      rfl
    exact this _ e _
  · have hz : (locRel.f 3).hom (cellAtSpace 3 (g • C)) = 0 := translate_off_flat g C e 3
    rw [localDeg, ite_eq_right e, degπ', dite_eq_left (by rw [hz]; exact map_zero _)]
    exact degπ_of_locRel_zero _ hz _

/-- **The finite translate sum.**  For a generator `w ⊗ C` the contributions of the translates
`g • C`, `g ∈ Γ(6)`, are `localDeg (g • C) · ρ(g) w`; at most one is non-zero (freeness of the action,
`translate_unique`; the stabilizers are trivial), and the sum equals `dT0 · coeffVal`. -/
theorem translate_sum (w : W) (C : Graded 3) :
    ∑ᶠ g : principalSix, degπ' (cellAtSpace 3 (g • C.1)) • W.ρ g w = dT0 • coeffVal W w C := by
  simp only [degπ'_translate]
  by_cases h : ∃ g : principalSix, g • C = T0g
  · obtain ⟨g0, hg0⟩ := h
    have hg0' : g0 • C.1 = T0 := congrArg Subtype.val hg0
    rw [finsum_eq_single _ g0, coeffVal_eq W w C g0 hg0, localDeg, ite_eq_left hg0']
    intro g hg
    have hne : g • C.1 ≠ T0 := fun h' => hg (translate_unique g g0 C.1 h' hg0')
    rw [localDeg, ite_eq_right hne, zero_smul]
  · rw [coeffVal_eq_zero W w C h, smul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun g => ?_
    have hne : g • C.1 ≠ T0 := fun h' => h ⟨g, Subtype.ext h'⟩
    rw [localDeg, ite_eq_right hne, zero_smul]

/-- The intersection sum at the flat: the coefficient at `T₀` weighted by the local degree. -/
def intersectionSum : (cellCoinv W).X 3 ⟶ ModuleCat.of ℚ W := dT0 • coeffAtT0 W

theorem intersectionSum_mk (w : W) (C : Graded 3) :
    (intersectionSum W).hom (Rep.coinvariantsTensorMk W (cellRep 3) w (MonoidAlgebra.single C 1)) =
      ∑ᶠ g : principalSix, degπ' (cellAtSpace 3 (g • C.1)) • W.ρ g w := by
  rw [translate_sum]
  change dT0 • (coeffAtT0 W).hom _ = _
  rw [coeffAtT0_mk]

/-! ### The conditional milestone and the non-circular scalar argument -/

theorem next_three : (ComplexShape.down ℕ).next 3 = 2 :=
  (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)

/-- The homology class of a degree-three cycle of the cellular complex with coefficients. -/
def cellClass (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0) :
    (cellCoinv W).homology 3 :=
  (cellCoinv W).homologyπ 3 ((cellCoinv W).cyclesMk z 2 next_three hz)

/-- Every top-degree homology class of a chain complex of `ℚ`-modules is the class of a cycle. -/
theorem exists_cellClass (y : (cellCoinv W).homology 3) :
    ∃ (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0), cellClass W z hz = y := by
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective ((cellCoinv W).homologyπ 3)).mp inferInstance) y
  have hz : ((cellCoinv W).d 3 2).hom (((cellCoinv W).iCycles 3).hom c) = 0 := by
    have h := (cellCoinv W).iCycles_d 3 2
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, h]
    simp
  refine ⟨((cellCoinv W).iCycles 3).hom c, hz, ?_⟩
  unfold cellClass
  congr 1
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map ((cellCoinv W).iCycles 3)) :=
    (Preadditive.mono_iff_injective ((cellCoinv W).iCycles 3)).1 inferInstance
  apply inj
  exact HomologicalComplex.i_cyclesMk (cellCoinv W) (((cellCoinv W).iCycles 3).hom c) 2 next_three hz

/-- **The global bridge, in the form it must be proved**:
for a universal constant `κ`, the arithmetic evaluator of the group homology class of a cellular top cycle
`z` equals `κ` times the intersection sum of `z` with the flat, i.e. `κ ∑_{g} deg(g • C ∩ flat) ρ(g) w`
over the generators `w ⊗ C` of `z` (`intersectionSum_mk`). -/
def FlatIntersectionBridge (κ : ℚ) : Prop :=
  ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
    (groupApartmentEvaluation W).hom ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
      κ • (intersectionSum W).hom z

/-- **The coefficient dictionary** (conditional on the bridge): the arithmetic evaluator of the class of a
cellular top cycle is `κ · dT0` times the coefficient at the standard cell `T₀`, transported by `ρ(g)` for
the unique `g` with `g • C = T₀`. -/
theorem evaluation_eq_coeffAtT0 {κ : ℚ} (hB : FlatIntersectionBridge κ) (W : Rep.{0} ℚ principalSix)
    (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0) :
    (groupApartmentEvaluation W).hom ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
      (κ * dT0) • (coeffAtT0 W).hom z := by
  rw [hB W z hz]
  change κ • dT0 • (coeffAtT0 W).hom z = _
  rw [smul_smul]

/-- **`κ · dT0 ≠ 0` from the bridge and the non-vanishing of the evaluator (acyclic).**  Hypotheses: the
bridge with *some* constant `κ`; surjectivity of `cellGroupHomologyMap W 3` (the cellular complex and the
singular chains of the bordification are both free resolutions); and that the arithmetic evaluator on
`H₃(Γ(6), W)` is non-zero.  Nothing about the value of `dT0` is used to prove any of them. -/
theorem kappa_mul_dT0_ne_zero {κ : ℚ} (hB : FlatIntersectionBridge κ) (W : Rep.{0} ℚ principalSix)
    (hsurj : Function.Surjective (cellGroupHomologyMap W 3).hom)
    (hne : groupApartmentEvaluation W ≠ 0) : κ * dT0 ≠ 0 := by
  intro h0
  apply hne
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨z, hz, rfl⟩ := exists_cellClass W y
  have := evaluation_eq_coeffAtT0 hB W z hz
  rw [h0, zero_smul] at this
  exact this

theorem dT0_ne_zero_of_bridge {κ : ℚ} (hB : FlatIntersectionBridge κ) (W : Rep.{0} ℚ principalSix)
    (hsurj : Function.Surjective (cellGroupHomologyMap W 3).hom)
    (hne : groupApartmentEvaluation W ≠ 0) : κ ≠ 0 ∧ dT0 ≠ 0 :=
  ⟨left_ne_zero_of_mul (kappa_mul_dT0_ne_zero hB W hsurj hne),
    right_ne_zero_of_mul (kappa_mul_dT0_ne_zero hB W hsurj hne)⟩

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
