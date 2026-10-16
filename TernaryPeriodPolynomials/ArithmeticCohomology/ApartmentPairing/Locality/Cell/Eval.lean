module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Support
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.DegreeHomotopy
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Frame
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ECap
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CoeffAtT0
public import TernaryPeriodPolynomials.Topology.SingularHomology.IteratedSubdivisionSmallChains

@[expose] public section


/-!
# Lemma 3.3, G3: the translate sum of the Thom cochain on the cell chains

`thomMap ρ'` is the scaled unipotent projection `π / ρ'` to `ℝ³`.  For a scalar 3-cochain `y` of the
symmetric space with the properties of the Thom pullback along it (vanishing on simplices subordinate to the
complement of the tube, equal to the local degree on relative cycles) and a tube radius `ρ'` below `‖π‖` on
the carriers of the lower cells and of every translate of the top cell other than `T₀`:

* `y_vanishes_of_sub`: a chain carried outside the tube is invisible to `y`;
* `y_cell_T0`: `y (cellAtSpace 3 T₀) = dT0` (homotopy `π/ρ' ≃ π`, `degR3_homotopy`);
* `Ybil_sum`: the translate-sum pairing `Ybil` is a finite sum over translates;
* `Yco_cell`: the translate-sum pairing of the elementary coinvariant chain `w ⊗ cellAtSpace 3 C` is
  `dT0 • coeffVal V w C` (so on cell cycles it is the intersection sum of `CoeffAtT0`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits Finsupp TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SingularCoverNaturality TernaryPoly.EquivariantSingularResolution
  TernaryPoly.EuclideanLocalHomology SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
  TernaryPoly.ContractibleSingularHomology TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SingularLocalCap
  TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

/-- The scaled unipotent projection `π / ρ'` as a map of the symmetric space to `ℝ³`. -/
def thomMap (ρ' : Space → ℝ) (hρc : Continuous ρ') (hρpos : ∀ S, 0 < ρ' S) :
    SpaceTop ⟶ TopCat.of R3 :=
  TopCat.ofHom ⟨fun S => (ρ' S)⁻¹ • piR3 S,
    (hρc.inv₀ fun S => (hρpos S).ne').smul piR3.continuous⟩

theorem thomMap_apply (ρ' : Space → ℝ) (hρc : Continuous ρ') (hρpos : ∀ S, 0 < ρ' S) (S : Space) :
    (thomMap ρ' hρc hρpos).hom S = (ρ' S)⁻¹ • piR3 S := rfl

theorem one_lt_thomMap_iff (ρ' : Space → ℝ) (hρc : Continuous ρ') (hρpos : ∀ S, 0 < ρ' S)
    (S : Space) : 1 < ‖(thomMap ρ' hρc hρpos).hom S‖ ↔ ρ' S < ‖piR3 S‖ := by
  rw [thomMap_apply, norm_smul, norm_inv, Real.norm_of_nonneg (hρpos S).le]
  have := hρpos S
  rw [← div_eq_inv_mul, one_lt_div this]

/-- The projection `π` as a map of topological spaces. -/
def piHom : SpaceTop ⟶ TopCat.of R3 := TopCat.ofHom piR3

theorem degπ_eq_degR3 (c : (chains Space).X 3)
    (h : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c) = 0) :
    degπ c h = degR3 ((singularChainMap ℚ piHom 3).hom c) h := rfl

section CellValues

variable (ρ' : Space → ℝ) (hρc : Continuous ρ') (hρpos : ∀ S, 0 < ρ' S)
  (y : singularChainGroup ℚ SpaceTop 3 →ₗ[ℚ] ℚ)
  (hy2 : ∀ τ : SingularSimplex SpaceTop 3,
    IsSubordinate {s : SpaceTop | 1 < ‖(thomMap ρ' hρc hρpos).hom s‖} τ →
      y (chainGenerator ℚ SpaceTop 3 τ) = 0)

include hy2 in
/-- A cell chain whose carrier misses the tube is invisible to the Thom cochain. -/
theorem y_vanishes_of_sub (A : Set SpaceTop)
    (hA : A ⊆ {S : SpaceTop | ρ' S < ‖piR3 S‖}) (c : singularChainGroup ℚ SpaceTop 3)
    (hc : c ∈ subChainSubmodule ℚ SpaceTop A 3) : y c = 0 := by
  have hsub : A ⊆ {s : SpaceTop | 1 < ‖(thomMap ρ' hρc hρpos).hom s‖} := fun S hS =>
    (one_lt_thomMap_iff ρ' hρc hρpos S).mpr (hA hS)
  refine subChainSubmodule_induction (S := A) (p := fun x => y x = 0) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    exact hy2 σ (hσ.mono hsub)
  · exact map_zero _
  · intro a b ha hb; rw [map_add, ha, hb, add_zero]
  · intro a x hx; rw [map_smul, hx, smul_zero]

/-- The boundary of the standard top cell chain, as the sum of its faces. -/
theorem boundary_cellAtSpace_T0 :
    (singularBoundary ℚ SpaceTop 2).hom (cellAtSpace 3 T0) =
      (incQ T0).sum fun D a => a • cellAtSpace 2 D := by
  have hd : ((chains Space).d 3 2).hom (cellAtSpace 3 T0) =
      (incQ T0).sum fun D a => a • cellAtSpace 2 D := by
    unfold cellAtSpace
    rw [realizeS_eq_via, d_realizeVia, coneData.phi_boundary 2 T0 T0_grade, realizeVia_Phi]
    rfl
  exact hd

/-- Faces of the top cell lie in a given set when their carriers do. -/
theorem boundary_T0_mem_sub (A : Set SpaceTop) (hA : ∀ D ∈ (incQ T0).support, cellSet 2 D ⊆ A) :
    (singularBoundary ℚ SpaceTop 2).hom (cellAtSpace 3 T0) ∈ subChainSubmodule ℚ SpaceTop A 2 := by
  rw [boundary_cellAtSpace_T0, Finsupp.sum]
  refine Submodule.sum_mem _ fun D hD => Submodule.smul_mem _ _ ?_
  exact subChainSubmodule_mono (hA D hD) 2 (cellAtSpace_mem_sub 2 D)

omit hy2 in
/-- The Thom cochain evaluated on the standard top cell chain is the local degree `dT0`. -/
theorem y_cell_T0
    (hy3 : ∀ c : singularChainGroup ℚ SpaceTop 3,
      (singularBoundary ℚ SpaceTop 2).hom c ∈
        subChainSubmodule ℚ SpaceTop {s : SpaceTop | 1 < ‖(thomMap ρ' hρc hρpos).hom s‖} 2 →
      ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom
          ((singularChainMap ℚ (thomMap ρ' hρc hρpos) 3).hom c)) = 0,
        y c = degR3 ((singularChainMap ℚ (thomMap ρ' hρc hρpos) 3).hom c) h)
    (hD2 : ∀ D ∈ (incQ T0).support, cellSet 2 D ⊆ {S : SpaceTop | ρ' S < ‖piR3 S‖}) :
    y (cellAtSpace 3 T0) = dT0 := by
  have hsub : {S : SpaceTop | ρ' S < ‖piR3 S‖} ⊆
      {s : SpaceTop | 1 < ‖(thomMap ρ' hρc hρpos).hom s‖} := fun S hS =>
    (one_lt_thomMap_iff ρ' hρc hρpos S).mpr hS
  obtain ⟨h, hy⟩ := hy3 (cellAtSpace 3 T0)
    (boundary_T0_mem_sub _ fun D hD => (hD2 D hD).trans hsub)
  -- the homotopy from `π / ρ'` to `π`
  let H : ContinuousMap.Homotopy (thomMap ρ' hρc hρpos).hom piHom.hom :=
    { toFun := fun p => ((1 - (p.1 : ℝ)) * (ρ' p.2)⁻¹ + (p.1 : ℝ)) • piR3 p.2
      continuous_toFun := by
        have h1 : Continuous fun p : unitInterval × Space => (ρ' p.2)⁻¹ :=
          (hρc.comp continuous_snd).inv₀ fun p => (hρpos p.2).ne'
        have h2 : Continuous fun p : unitInterval × Space => (p.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        exact (((continuous_const.sub h2).mul h1).add h2).smul (piR3.continuous.comp continuous_snd)
      map_zero_left := fun S => by
        simp only [Set.Icc.coe_zero, sub_zero, one_mul, add_zero]
        exact (thomMap_apply ρ' hρc hρpos S).symm
      map_one_left := fun S => by
        simp [piHom] }
  have hflat : ∀ D ∈ (incQ T0).support, cellSet 2 D ⊆ {S : SpaceTop | piR3 S ≠ 0} := by
    intro D hD S hS hSπ
    have hne : D ≠ T0 := by
      intro hDT
      have := incQ_grade T0 D (Finsupp.mem_support_iff.mp hD)
      rw [hDT] at this
      omega
    exact cellSet_not_flat 2 D hne S hS hSπ
  obtain ⟨hf, hg, hfg⟩ := degR3_homotopy (thomMap ρ' hρc hρpos) piHom H {S : SpaceTop | piR3 S ≠ 0}
    (fun t S hS => by
      intro hz
      have hz' : ((1 - (t : ℝ)) * (ρ' S)⁻¹ + (t : ℝ)) • piR3 S = 0 := hz
      have hpos : 0 < (1 - (t : ℝ)) * (ρ' S)⁻¹ + (t : ℝ) := by
        have h0 : (0 : ℝ) ≤ t := t.2.1
        have h1 : (t : ℝ) ≤ 1 := t.2.2
        have := inv_pos.mpr (hρpos S)
        rcases h0.eq_or_lt with h0' | h0'
        · rw [← h0']; simpa using this
        · have : 0 ≤ (1 - (t : ℝ)) * (ρ' S)⁻¹ := mul_nonneg (by linarith) (inv_pos.mpr (hρpos S)).le
          linarith
      exact hS ((smul_eq_zero.mp hz').resolve_left hpos.ne'))
    (cellAtSpace 3 T0)
    (boundary_T0_mem_sub _ hflat)
  rw [hy]
  unfold dT0
  rw [degπ_eq_degR3]
  exact hfg

end CellValues

section Sum

variable {G : Type} [Group G] {E : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (V : Rep.{0} ℚ G) {b : ℕ} (y : singularChainGroup ℚ E b →ₗ[ℚ] ℚ)
  (hfin : ∀ τ : SingularSimplex E b, {g : G | y (chainGenerator ℚ E b (g • τ)) ≠ 0}.Finite)

theorem Ybil_sum (c : singularChainGroup ℚ E b) :
    ∃ S : Finset G, (∀ g, g ∉ S → y ((chainRep G E b).ρ g c) = 0) ∧
      ∀ w, Ybil V y hfin w c = ∑ g ∈ S, y ((chainRep G E b).ρ g c) • V.ρ g w := by
  have hc : c ∈ Submodule.span ℚ (Set.range (chainGenerator ℚ E b)) := by
    rw [chainGenerator_span_top]; trivial
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨τ, rfl⟩ := hx
    refine ⟨(hfin τ).toFinset, ?_, ?_⟩
    · intro g hg
      have hc : (chainRep G E b).ρ g (chainGenerator ℚ E b τ) = chainGenerator ℚ E b (g • τ) :=
        chainElement_smul G E b g τ
      rw [hc]
      by_contra h
      exact hg ((Set.Finite.mem_toFinset _).mpr h)
    · intro w
      rw [Ybil_generator, Ysimp_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [show (chainRep G E b).ρ g (chainGenerator ℚ E b τ) = chainGenerator ℚ E b (g • τ) from
        chainElement_smul G E b g τ]
  | zero => exact ⟨∅, fun g _ => by simp, fun w => by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨S₁, h₁, e₁⟩ := hx
    obtain ⟨S₂, h₂, e₂⟩ := hz
    refine ⟨S₁ ∪ S₂, ?_, ?_⟩
    · intro g hg
      rw [map_add, map_add, h₁ g (fun h => hg (Finset.mem_union_left _ h)),
        h₂ g (fun h => hg (Finset.mem_union_right _ h)), add_zero]
    · intro w
      rw [map_add, e₁, e₂]
      have hx : ∑ g ∈ S₁, y ((chainRep G E b).ρ g x) • V.ρ g w =
          ∑ g ∈ S₁ ∪ S₂, y ((chainRep G E b).ρ g x) • V.ρ g w := by
        apply Finset.sum_subset Finset.subset_union_left
        intro g _ hg
        rw [h₁ g hg, zero_smul]
      have hz : ∑ g ∈ S₂, y ((chainRep G E b).ρ g z) • V.ρ g w =
          ∑ g ∈ S₁ ∪ S₂, y ((chainRep G E b).ρ g z) • V.ρ g w := by
        apply Finset.sum_subset Finset.subset_union_right
        intro g _ hg
        rw [h₂ g hg, zero_smul]
      rw [hx, hz, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_add, map_add, add_smul]
  | smul a x _ hx =>
    obtain ⟨S, h, e⟩ := hx
    refine ⟨S, ?_, ?_⟩
    · intro g hg
      rw [map_smul, map_smul, h g hg, smul_zero]
    · intro w
      rw [map_smul, e, Finset.smul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_smul, map_smul, smul_assoc]

end Sum

section YcoCell

open TernaryPoly.IntegralGL3Congruence

variable (ρ' : Space → ℝ) (hρc : Continuous ρ') (hρpos : ∀ S, 0 < ρ' S)
  (y : singularChainGroup ℚ SpaceTop 3 →ₗ[ℚ] ℚ)
  (hfin : ∀ τ : SingularSimplex SpaceTop 3,
    {g : principalSix | y (chainGenerator ℚ SpaceTop 3 (g • τ)) ≠ 0}.Finite)

theorem Yco_mk (V : Rep.{0} ℚ principalSix) (w : V) (c : singularChainGroup ℚ SpaceTop 3) :
    Yco V y hfin (Rep.coinvariantsTensorMk V (chainRep principalSix SpaceTop 3) w c) =
      Ybil V y hfin w c := rfl

theorem chainRep_cellAtSpace (g : principalSix) (n : ℕ) (D : Cell) :
    (chainRep principalSix SpaceTop n).ρ g (cellAtSpace n D) = cellAtSpace n (g • D) :=
  smul_cellAtSpace g n D

/-- **The translate sum of a cell is `dT0` times the coefficient at `T₀`.** -/
theorem Yco_cell
    (hy2 : ∀ τ : SingularSimplex SpaceTop 3,
      IsSubordinate {s : SpaceTop | 1 < ‖(thomMap ρ' hρc hρpos).hom s‖} τ →
        y (chainGenerator ℚ SpaceTop 3 τ) = 0)
    (hy3 : ∀ c : singularChainGroup ℚ SpaceTop 3,
      (singularBoundary ℚ SpaceTop 2).hom c ∈
        subChainSubmodule ℚ SpaceTop {s : SpaceTop | 1 < ‖(thomMap ρ' hρc hρpos).hom s‖} 2 →
      ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom
          ((singularChainMap ℚ (thomMap ρ' hρc hρpos) 3).hom c)) = 0,
        y c = degR3 ((singularChainMap ℚ (thomMap ρ' hρc hρpos) 3).hom c) h)
    (hD2 : ∀ D ∈ (incQ T0).support, cellSet 2 D ⊆ {S : SpaceTop | ρ' S < ‖piR3 S‖})
    (V : Rep.{0} ℚ principalSix) (w : V) (C : Graded 3)
    (hcells : ∀ g : principalSix, g • C.1 ≠ T0 →
      cellSet 3 (g • C.1) ⊆ {S : SpaceTop | ρ' S < ‖piR3 S‖}) :
    Yco V y hfin (Rep.coinvariantsTensorMk V (chainRep principalSix SpaceTop 3) w
      (cellAtSpace 3 C.1)) = dT0 • coeffVal V w C := by
  rw [Yco_mk]
  obtain ⟨S, hS0, hSsum⟩ := Ybil_sum V y hfin (cellAtSpace 3 C.1)
  rw [hSsum w]
  have hval : ∀ g : principalSix,
      y ((chainRep principalSix SpaceTop 3).ρ g (cellAtSpace 3 C.1)) =
        degπ' (cellAtSpace 3 (g • C.1)) := by
    intro g
    rw [chainRep_cellAtSpace, degπ'_translate]
    by_cases hg : g • C.1 = T0
    · rw [localDeg, ite_eq_left hg, hg]
      exact y_cell_T0 ρ' hρc hρpos y hy3 hD2
    · rw [localDeg, ite_eq_right hg]
      exact y_vanishes_of_sub ρ' hρc hρpos y hy2 _ (hcells g hg) _ (cellAtSpace_mem_sub 3 _)
  simp_rw [hval]
  rw [← translate_sum V w C]
  rw [finsum_eq_sum_of_support_subset]
  intro g hg
  by_contra hgS
  apply hg
  have := hS0 g hgS
  rw [hval] at this
  simp [this]

end YcoCell

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
