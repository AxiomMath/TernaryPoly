module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.ClassicalBridge
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.SphericalSupply
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Covers
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.ClassicalTrace
public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.ClassicalPair
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ParabolicES

@[expose] public section


/-!
# Step (ii): the global sum identity

For level-one `f` of weight `-2 * hw (k+1)` (`n = 2k+1`), `Constituent.modelCoversForms` writes
`f`'s restriction to `Γ₁(3)` as a sum of classical forms of Levi-fixed weight vectors `v_j` of
constituents `D_j`. Applying the Reynolds average (`ReynoldsAverage.lean`) to each `v_j`, and using
that "classical form of a vector" intertwines the average with the classical slash action
(`EvenLevelThree.WtModular.levelThree_slash_eqWt`, bridged to the adelic `cuspAt` picture
by `ClassicalBridge.lean`'s `cuspAt_eq_rationalSlash`) and that `f` itself is already `levelOne`-
invariant (`SlashInvariantFormClass.slash_action_eq`), gives `f` as the *same* sum but with each
`v_j` replaced by its own Reynolds average. If `f ≠ 0`, some piece's average cannot vanish; by
`SphericalSupply.lean`'s `forall_cuspAt_eq_of_mem_levelThreeValues` that average is already
`GL₂(ℤ̂)`-fixed, so nonvanishing packages it directly as `SphericalCusp` for that constituent.

`modelCoversForms` needs `3 ≤ n`; the hypothesis `h`
of `CuspidalSupply.lean` only assumes `0 < n`. The excluded case is `n = 1` (`k = 0`), i.e.
`f : CuspForm levelOne 4` — classically `S_4(SL₂(ℤ)) = 0` by the dimension formula, which would
close it by forcing `f = 0`. `sumIdentity` below is stated for `k ≥ 1` (equivalently `n ≥ 3`) only; the `k = 0` case is

left to a successor.
-/

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open UpperHalfPlane
open scoped ModularForm MatrixGroups Manifold
open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Automorphic.Constituent (modelCoversForms)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.MultiplicityOne.Classical
  (restrictThree coe_restrictThree)
open TernaryPeriodPolynomials.Oldform (exists_cuspForm_cast)
open TernaryPeriodPolynomials.EvenLevelThree
open TernaryPeriodPolynomials.Spectral.ParabolicES (hw)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)

/-- Push a fixed slash through a `List.sum` of a mapped list (list analogue of the already-proved
`Spectral.LevelOneHecke.sum_slash`, which is stated for `Finset.sum`). -/
private theorem list_sum_slash {α : Type*} (wt : ℤ) (g : GL (Fin 2) ℝ) (l : List α)
    (F : α → ℍ → ℂ) :
    (l.map F).sum ∣[wt] g = (l.map fun a => F a ∣[wt] g).sum := by
  induction l with
  | nil => simp [SlashAction.zero_slash]
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [SlashAction.add_slash, ih]

/-- Swap an outer `Finset.sum` over `Fin 8` with an inner `List.sum`. -/
private theorem finset_sum_list_sum_comm {α : Type*} (l : List α) (F : Fin 8 → α → ℍ → ℂ) :
    ∑ i : Fin 8, (l.map (F i)).sum = (l.map fun a => ∑ i : Fin 8, F i a).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

/-- A constant scalar pulls out of a `List.sum` of a mapped list. -/
private theorem list_sum_smul {α : Type*} (c : ℂ) (l : List α) (G : α → ℍ → ℂ) :
    (l.map fun a => c • G a).sum = c • (l.map G).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

/-- The average of eight copies of a constant, scaled by `8⁻¹`, is the constant itself. -/
private theorem reynolds_const_avg (c : ℍ → ℂ) :
    (8⁻¹ : ℂ) • (∑ _i : Fin 8, c) = c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  exact inv_smul_smul₀ (by norm_num) c

/-- **Step (ii), the global sum identity.** For `n = 2k+1` with `k ≥ 1`, every level-one cusp
form `f` of weight `-2 * hw (k+1)` is, as a function, the sum of classical forms of the Reynolds
averages of the Levi-fixed vectors `modelCoversForms` supplies for its `Γ₁(3)`-restriction; if
`f ≠ 0`, some piece's average is itself nonzero, making its constituent spherical. `k = 0` (`n = 1`)
is excluded; see the module doc. -/
theorem sumIdentity (n k : ℕ) (hnk : n = 2 * k + 1) (hk1 : 1 ≤ k)
    (f : CuspForm levelOne (-2 * hw (k + 1))) :
    ∃ l : List (Σ D : CohomologicalCuspData n, levelThreeClassicalVectorsWt D.cusp (-((n : ℤ) + 3))),
      (⇑f : ℍ → ℂ) = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
              (reynoldsAverage p.1.cusp p.2.1)).sum ∧
      (f ≠ 0 → ∃ p ∈ l, SphericalCusp p.1.cusp ∧ reynoldsAverage p.1.cusp p.2.1 ≠ 0) := by
  have hn3 : 3 ≤ n := by omega
  have hwteq : -2 * hw (k + 1) = (n : ℤ) + 3 := by unfold hw; omega
  obtain ⟨f', hf'⟩ : ∃ f' : CuspForm levelOne ((n : ℤ) + 3), (⇑f' : ℍ → ℂ) = ⇑f :=
    exists_cuspForm_cast hwteq f
  have hweq2 : (n : ℤ) + 3 = ((n + 1 : ℕ) : ℤ) + 2 := by omega
  obtain ⟨g, hg⟩ : ∃ g : S (n + 1), (⇑g : ℍ → ℂ) = ⇑(restrictThree ((n : ℤ) + 3) f') :=
    exists_cuspForm_cast hweq2 (restrictThree ((n : ℤ) + 3) f')
  obtain ⟨l, hl⟩ := modelCoversForms n hn3 g
  have hfl : (⇑f : ℍ → ℂ) =
      (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1 p.2.1).sum :=
    hf'.symm.trans ((coe_restrictThree f').symm.trans (hg.symm.trans hl))
  refine ⟨l, ?_, ?_⟩
  · -- The main identity: replace each piece by its own Reynolds average.
    have hstep : ∀ i : Fin 8, (⇑f : ℍ → ℂ) =
        (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
          (cuspAt p.1.cusp (γ i) p.2.1)).sum := by
      intro i
      have hpiece : ∀ p ∈ l,
          cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1 p.2.1
              ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i)) =
            cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
              (cuspAt p.1.cusp (γ i) p.2.1) := by
        intro p _
        have hrot := p.2.2.2.1
        have hkey := levelThree_slash_eqWt p.1.cusp (-((n : ℤ) + 3)) p.2.1 hrot (M i)
        rw [neg_neg] at hkey
        rw [← hkey, cuspAt_eq_rationalSlash]
      calc (⇑f : ℍ → ℂ)
          = (⇑f' : ℍ → ℂ) := hf'.symm
        _ = (⇑f' : ℍ → ℂ) ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i)) :=
            (SlashInvariantFormClass.slash_action_eq f' (SpecialLinearGroup.mapGL ℝ (M i))
              (⟨M i, rfl⟩ : SpecialLinearGroup.mapGL ℝ (M i) ∈ levelOne)).symm
        _ = (⇑f : ℍ → ℂ) ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i)) := by rw [hf']
        _ = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1 p.2.1).sum
              ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i)) := by rw [hfl]
        _ = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1 p.2.1
              ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i))).sum :=
            list_sum_slash _ _ _ _
        _ = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
              (cuspAt p.1.cusp (γ i) p.2.1)).sum := by
            congr 1
            exact List.map_congr_left hpiece
    have hpiece2 : ∀ p : Σ D : CohomologicalCuspData n,
        levelThreeClassicalVectorsWt D.cusp (-((n : ℤ) + 3)),
        cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
            (reynoldsAverage p.1.cusp p.2.1) =
          (8⁻¹ : ℂ) • ∑ i : Fin 8, cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
            (cuspAt p.1.cusp (γ i) p.2.1) := by
      intro p
      unfold reynoldsAverage
      rw [map_smul, map_sum]
    calc (⇑f : ℍ → ℂ)
        = (8⁻¹ : ℂ) • ∑ _i : Fin 8, (⇑f : ℍ → ℂ) := (reynolds_const_avg _).symm
      _ = (8⁻¹ : ℂ) • ∑ i : Fin 8, (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp
              (-((n : ℤ) + 3)) 1 (cuspAt p.1.cusp (γ i) p.2.1)).sum := by
          rw [Finset.sum_congr rfl (fun i _ => hstep i)]
      _ = (8⁻¹ : ℂ) • (l.map fun p => ∑ i : Fin 8, cuspScalarWeightedLinearWt p.1.cusp
              (-((n : ℤ) + 3)) 1 (cuspAt p.1.cusp (γ i) p.2.1)).sum := by
          rw [finset_sum_list_sum_comm]
      _ = (l.map fun p => (8⁻¹ : ℂ) • ∑ i : Fin 8, cuspScalarWeightedLinearWt p.1.cusp
              (-((n : ℤ) + 3)) 1 (cuspAt p.1.cusp (γ i) p.2.1)).sum :=
          (list_sum_smul _ _ _).symm
      _ = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
              (reynoldsAverage p.1.cusp p.2.1)).sum := by
          congr 1
          exact List.map_congr_left (fun p _ => (hpiece2 p).symm)
  · -- Nonvanishing-and-sphericity packaging.
    intro hf0
    by_contra hcon
    push Not at hcon
    have hall0 : ∀ p ∈ l, reynoldsAverage p.1.cusp p.2.1 = 0 := by
      intro p hp
      by_contra hne
      exact hne (hcon p hp ⟨reynoldsAverage p.1.cusp p.2.1, hne,
        forall_cuspAt_eq_of_mem_levelThreeValues p.1.cusp p.2.1 p.2.2.1⟩)
    apply hf0
    apply DFunLike.coe_injective
    have hzero : (⇑f : ℍ → ℂ) = 0 := by
      have hmain : (⇑f : ℍ → ℂ) = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp
          (-((n : ℤ) + 3)) 1 (reynoldsAverage p.1.cusp p.2.1)).sum := by
        have hstep : ∀ i : Fin 8, (⇑f : ℍ → ℂ) =
            (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
              (cuspAt p.1.cusp (γ i) p.2.1)).sum := by
          intro i
          have hpiece : ∀ p ∈ l,
              cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1 p.2.1
                  ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i)) =
                cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
                  (cuspAt p.1.cusp (γ i) p.2.1) := by
            intro p _
            have hrot := p.2.2.2.1
            have hkey := levelThree_slash_eqWt p.1.cusp (-((n : ℤ) + 3)) p.2.1 hrot (M i)
            rw [neg_neg] at hkey
            rw [← hkey, cuspAt_eq_rationalSlash]
          calc (⇑f : ℍ → ℂ)
              = (⇑f' : ℍ → ℂ) := hf'.symm
            _ = (⇑f' : ℍ → ℂ) ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i)) :=
                (SlashInvariantFormClass.slash_action_eq f' (SpecialLinearGroup.mapGL ℝ (M i))
                  (⟨M i, rfl⟩ : SpecialLinearGroup.mapGL ℝ (M i) ∈ levelOne)).symm
            _ = (⇑f : ℍ → ℂ) ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i)) := by rw [hf']
            _ = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
                  p.2.1).sum ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i)) := by rw [hfl]
            _ = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1 p.2.1
                  ∣[(n : ℤ) + 3] (SpecialLinearGroup.mapGL ℝ (M i))).sum :=
                list_sum_slash _ _ _ _
            _ = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
                  (cuspAt p.1.cusp (γ i) p.2.1)).sum := by
                congr 1
                exact List.map_congr_left hpiece
        have hpiece2 : ∀ p : Σ D : CohomologicalCuspData n,
            levelThreeClassicalVectorsWt D.cusp (-((n : ℤ) + 3)),
            cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
                (reynoldsAverage p.1.cusp p.2.1) =
              (8⁻¹ : ℂ) • ∑ i : Fin 8, cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
                (cuspAt p.1.cusp (γ i) p.2.1) := by
          intro p
          unfold reynoldsAverage
          rw [map_smul, map_sum]
        calc (⇑f : ℍ → ℂ)
            = (8⁻¹ : ℂ) • ∑ _i : Fin 8, (⇑f : ℍ → ℂ) := (reynolds_const_avg _).symm
          _ = (8⁻¹ : ℂ) • ∑ i : Fin 8, (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp
                  (-((n : ℤ) + 3)) 1 (cuspAt p.1.cusp (γ i) p.2.1)).sum := by
              rw [Finset.sum_congr rfl (fun i _ => hstep i)]
          _ = (8⁻¹ : ℂ) • (l.map fun p => ∑ i : Fin 8, cuspScalarWeightedLinearWt p.1.cusp
                  (-((n : ℤ) + 3)) 1 (cuspAt p.1.cusp (γ i) p.2.1)).sum := by
              rw [finset_sum_list_sum_comm]
          _ = (l.map fun p => (8⁻¹ : ℂ) • ∑ i : Fin 8, cuspScalarWeightedLinearWt p.1.cusp
                  (-((n : ℤ) + 3)) 1 (cuspAt p.1.cusp (γ i) p.2.1)).sum :=
              (list_sum_smul _ _ _).symm
          _ = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
                  (reynoldsAverage p.1.cusp p.2.1)).sum := by
              congr 1
              exact List.map_congr_left (fun p _ => (hpiece2 p).symm)
      rw [hmain]
      rw [show (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp (-((n : ℤ) + 3)) 1
          (reynoldsAverage p.1.cusp p.2.1)) = l.map (fun _ => (0 : ℍ → ℂ)) from
        List.map_congr_left (fun p hp => by rw [hall0 p hp, map_zero])]
      induction l with
      | nil => simp
      | cons a l ih => simp
    exact hzero

end TernaryPeriodPolynomials.Argument.CuspidalSpan
