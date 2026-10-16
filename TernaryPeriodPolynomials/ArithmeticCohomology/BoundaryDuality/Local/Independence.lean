module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspSeparation

@[expose] public section


/-!
# The local value is a pairing of local classes

The local value `lineValue Θ T v z w y` at a representative line `v̄` vanishes when the line cocycle
is exact at `v̄`, `z(·)(v̄) = du` with `u` equivariant under the stabilizer of `v̄`, provided the
edge pullback of `y` is exact (`lineValue_eq_zero_of_line_exact`): on each complete flag `e`
above `v̄` the edge primitive is `u + η` with `η` a cocycle of the stabilizer of `e`, the
`η`-term is the coboundary `−d(η ⌣ s^φ)` there, and the remaining `u`-terms cancel against the
filling term `⟨d(u ⌣ y^φ), D_v⟩`. Together with the dependence on the plane coordinate only
(`CuspSeparation.lineValue_eq_of_fixedPointH2_eq`), the local value only depends on the Shapiro
coordinates of the line class at `v̄` and of the plane class at its dual plane
(`lineValue_eq_of_coordinates`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalIndependence

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.CuspSeparation
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  (Θ : TraceData ι L P) {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- **Vanishing of the local value at a locally exact line cocycle.** -/
theorem lineValue_eq_zero_of_line_exact (v : L) {z : MaximalCycles n χ .line}
    {w : EdgeCochains n χ 1} {y : MaximalCycles n χ .plane} (hw : EdgePrimitive z w)
    (flat : PlaneEdgeExact y) (u : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hu_eq : ∀ γ ∈ levelStabilizer (Θ.lineRep v), ∀ a b : RationalGL3,
      u ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (u ![a, b]))
    (hu : ∀ x : Fin 3 → RationalGL3, z.val.val x (Θ.lineRep v) = differentialOneRaw u x) :
    lineValue Θ T v z w y = 0 := by
  obtain ⟨s, hs⟩ := flat
  set Lv := Θ.lineRep v with hLv
  set F := T.dualFlag Lv with hF
  -- the scalar three-cochain `u ⌣ y^φ` at the line
  let k : (Fin 4 → RationalGL3) → ℂ := fun x =>
    T.B (u ![x 0, x 1]) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F)
  have k_inv : ∀ (γ : levelStabilizer Lv) x, k (fun i => γ.val * x i) = k x := by
    intro γ x
    have level : γ.val ∈ rationalLevel := (Subgroup.mem_inf.mp γ.property).1
    have fixed : γ.val • Lv = Lv := MulAction.mem_stabilizer_iff.mp
      (Subgroup.mem_inf.mp γ.property).2
    have dual : T.φ γ.val ∈ rationalLevel := T.level γ.val level
    have fixedF : (T.φ γ.val)⁻¹ • F = F := by
      rw [inv_smul_eq_iff, hF, ← T.dualFlag_smul, fixed]
    have hy := congrFun (cochain_triple y.val ⟨T.φ γ.val, dual⟩ (T.φ (x 1)) (T.φ (x 2))
      (T.φ (x 3))) F
    change y.val.val ![T.φ γ.val * T.φ (x 1), T.φ γ.val * T.φ (x 2), T.φ γ.val * T.φ (x 3)] F =
      rationalCoefficientComponent n χ (T.φ γ.val)
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] ((T.φ γ.val)⁻¹ • F)) at hy
    rw [fixedF] at hy
    change T.B (u ![γ.val * x 0, γ.val * x 1])
        (y.val.val ![T.φ (γ.val * x 1), T.φ (γ.val * x 2), T.φ (γ.val * x 3)] F) =
      T.B (u ![x 0, x 1]) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F)
    rw [map_mul, map_mul, map_mul, hy, hu_eq γ.val γ.property, T.invariant γ.val level]
  -- the filling term is `⟨dk, D_v⟩`
  have fill : (fun x => T.B (z.val.val ![x 0, x 1, x 2] Lv)
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] F)) = differentialThreeRaw k := by
    funext x
    have cocycle : IsCocycleTwo (fun x' => y.val.val x' F) := fun x' =>
      congrFun (isCocycleTwo_of_mem y x') F
    rw [show k = cupOneTwo T.B T.φ u (fun x' => y.val.val x' F) from rfl,
      differentialThreeRaw_cupOneTwo T.B T.φ u cocycle x, hu]
    rfl
  -- each edge term is `⟨k, C_e⟩` up to a coboundary
  have edge : ∀ i ∈ Finset.univ.filter (fun i => Θ.lineOf i = v),
      Finsupp.linearCombination ℂ (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F)) (Θ.chain i) =
      Finsupp.linearCombination ℂ k (Θ.chain i) := by
    intro i hi
    have hv : Θ.lineOf i = v := (Finset.mem_filter.mp hi).2
    have hend : endpoint .line (Θ.edge i) = Lv := by rw [hLv, ← hv, Θ.line_endpoint i]
    set e' := T.dualEdge (Θ.edge i) with he'
    have hFe : endpoint .plane e' = F := by rw [he', T.endpoint_dualEdge, hend, hF]
    -- `η = w(·)(e) − u` is a cocycle
    have hη : ∀ x : Fin 3 → RationalGL3,
        (w.val ![x 1, x 2] (Θ.edge i) - u ![x 1, x 2]) -
          (w.val ![x 0, x 2] (Θ.edge i) - u ![x 0, x 2]) +
          (w.val ![x 0, x 1] (Θ.edge i) - u ![x 0, x 1]) = 0 := by
      intro x
      have h₁ : z.val.val x Lv = w.val ![x 1, x 2] (Θ.edge i) - w.val ![x 0, x 2] (Θ.edge i) +
          w.val ![x 0, x 1] (Θ.edge i) := by
        rw [← hend]
        exact hw x (Θ.edge i)
      have h₂ : z.val.val x Lv = u ![x 1, x 2] - u ![x 0, x 2] + u ![x 0, x 1] := hu x
      have h₃ := h₁.symm.trans h₂
      calc _ = (w.val ![x 1, x 2] (Θ.edge i) - w.val ![x 0, x 2] (Θ.edge i) +
            w.val ![x 0, x 1] (Θ.edge i)) - (u ![x 1, x 2] - u ![x 0, x 2] + u ![x 0, x 1]) := by
            abel
        _ = 0 := by rw [h₃, sub_self]
    let g : (Fin 3 → RationalGL3) → ℂ := fun x =>
      T.B (w.val ![x 0, x 1] (Θ.edge i) - u ![x 0, x 1]) (s.val ![T.φ (x 1), T.φ (x 2)] e')
    have g_inv : ∀ (γ : levelStabilizer (Θ.edge i)) x, g (fun j => γ.val * x j) = g x := by
      intro γ x
      have level : γ.val ∈ rationalLevel := (Subgroup.mem_inf.mp γ.property).1
      have fixedE : γ.val⁻¹ • Θ.edge i = Θ.edge i := MulAction.mem_stabilizer_iff.mp
        ((MulAction.stabilizer RationalGL3 (Θ.edge i)).inv_mem
          (Subgroup.mem_inf.mp γ.property).2)
      have hline : γ.val ∈ levelStabilizer Lv := by
        rw [hLv, ← hv]
        exact mem_line_of_mem_edge Θ γ.property
      have dual : T.φ γ.val ∈ rationalLevel := T.level γ.val level
      have fixedE' : (T.φ γ.val)⁻¹ • e' = e' := by
        rw [he', ← map_inv, ← T.dualEdge_smul, fixedE]
      have hwγ := congrFun (cochain_pair w ⟨γ.val, level⟩ (x 0) (x 1)) (Θ.edge i)
      change w.val ![γ.val * x 0, γ.val * x 1] (Θ.edge i) =
        rationalCoefficientComponent n χ γ.val (w.val ![x 0, x 1] (γ.val⁻¹ • Θ.edge i)) at hwγ
      rw [fixedE] at hwγ
      have hsγ := congrFun (cochain_pair s ⟨T.φ γ.val, dual⟩ (T.φ (x 1)) (T.φ (x 2))) e'
      change s.val ![T.φ γ.val * T.φ (x 1), T.φ γ.val * T.φ (x 2)] e' =
        rationalCoefficientComponent n χ (T.φ γ.val)
          (s.val ![T.φ (x 1), T.φ (x 2)] ((T.φ γ.val)⁻¹ • e')) at hsγ
      rw [fixedE'] at hsγ
      change T.B (w.val ![γ.val * x 0, γ.val * x 1] (Θ.edge i) - u ![γ.val * x 0, γ.val * x 1])
          (s.val ![T.φ (γ.val * x 1), T.φ (γ.val * x 2)] e') =
        T.B (w.val ![x 0, x 1] (Θ.edge i) - u ![x 0, x 1]) (s.val ![T.φ (x 1), T.φ (x 2)] e')
      rw [hwγ, hu_eq γ.val hline, ← map_sub, map_mul, map_mul, hsγ, T.invariant γ.val level]
    have pointwise : (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F)) = k - differentialTwoRaw g := by
      funext x
      have hy : y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F =
          s.val ![T.φ (x 2), T.φ (x 3)] e' - s.val ![T.φ (x 1), T.φ (x 3)] e' +
            s.val ![T.φ (x 1), T.φ (x 2)] e' := by
        rw [← hFe]
        exact hs ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] e'
      have hη₀ := hη ![x 0, x 1, x 2]
      change (w.val ![x 1, x 2] (Θ.edge i) - u ![x 1, x 2]) -
          (w.val ![x 0, x 2] (Θ.edge i) - u ![x 0, x 2]) +
          (w.val ![x 0, x 1] (Θ.edge i) - u ![x 0, x 1]) = 0 at hη₀
      -- η(x₀, x₁) ⌣ ds = −dg, using dη = 0 on the faces
      have key : T.B (w.val ![x 0, x 1] (Θ.edge i))
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F) =
          T.B (u ![x 0, x 1]) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F) +
            T.B (w.val ![x 0, x 1] (Θ.edge i) - u ![x 0, x 1])
              (s.val ![T.φ (x 2), T.φ (x 3)] e' - s.val ![T.φ (x 1), T.φ (x 3)] e' +
                s.val ![T.φ (x 1), T.φ (x 2)] e') := by
        rw [← hy]
        simp only [map_sub, LinearMap.sub_apply]
        abel
      have e₁ : w.val ![x 1, x 2] (Θ.edge i) - u ![x 1, x 2] =
          (w.val ![x 0, x 2] (Θ.edge i) - u ![x 0, x 2]) -
            (w.val ![x 0, x 1] (Θ.edge i) - u ![x 0, x 1]) := by
        rw [← sub_eq_zero, ← hη₀]; abel
      change T.B (w.val ![x 0, x 1] (Θ.edge i))
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F) =
        T.B (u ![x 0, x 1]) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F) -
          (T.B (w.val ![x 1, x 2] (Θ.edge i) - u ![x 1, x 2]) (s.val ![T.φ (x 2), T.φ (x 3)] e') -
            T.B (w.val ![x 0, x 2] (Θ.edge i) - u ![x 0, x 2])
              (s.val ![T.φ (x 2), T.φ (x 3)] e') +
            T.B (w.val ![x 0, x 1] (Θ.edge i) - u ![x 0, x 1])
              (s.val ![T.φ (x 1), T.φ (x 3)] e') -
            T.B (w.val ![x 0, x 1] (Θ.edge i) - u ![x 0, x 1])
              (s.val ![T.φ (x 1), T.φ (x 2)] e'))
      rw [key, e₁]
      simp only [map_add, map_sub, LinearMap.sub_apply]
      abel
    rw [pointwise, lc_sub, eval_boundary_null g g_inv (Θ.chain i) (Θ.edge_closed i), sub_zero]
  unfold lineValue
  rw [← hLv, ← hF, Finset.sum_congr rfl edge, fill,
    ← map_sum (Finsupp.linearCombination ℂ k)]
  have hnull := eval_null k k_inv (Θ.line_filled v)
  rw [map_sub, sub_eq_zero, ← eval_differentialThree] at hnull
  rw [hnull, sub_self]

/-- Edge primitives subtract. -/
theorem edgePrimitive_sub {z₁ z₂ : MaximalCycles n χ .line} {w₁ w₂ : EdgeCochains n χ 1}
    (h₁ : EdgePrimitive z₁ w₁) (h₂ : EdgePrimitive z₂ w₂) :
    EdgePrimitive (z₁ - z₂) (w₁ - w₂) := by
  intro x e
  change z₁.val.val x (endpoint .line e) - z₂.val.val x (endpoint .line e) =
    differentialOneRaw (w₁.val - w₂.val) x e
  rw [h₁ x e, h₂ x e]
  simp only [differentialOneRaw, Pi.sub_apply, Pi.add_apply]
  abel

/-- The local value is linear in the line data. -/
theorem lineValue_sub_left (v : L) (z₁ z₂ : MaximalCycles n χ .line)
    (w₁ w₂ : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) :
    lineValue Θ T v (z₁ - z₂) (w₁ - w₂) y =
      lineValue Θ T v z₁ w₁ y - lineValue Θ T v z₂ w₂ y := by
  have e₁ : ∀ i, (fun x : Fin 4 → RationalGL3 => T.B ((w₁ - w₂).val ![x 0, x 1] (Θ.edge i))
      (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (Θ.lineRep v)))) =
      (fun x : Fin 4 → RationalGL3 => T.B (w₁.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (Θ.lineRep v)))) -
      (fun x : Fin 4 → RationalGL3 => T.B (w₂.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (Θ.lineRep v)))) := by
    intro i
    funext x
    exact LinearMap.congr_fun (map_sub T.B _ _) _
  have e₂ : (fun x : Fin 5 → RationalGL3 => T.B ((z₁ - z₂).val.val ![x 0, x 1, x 2] (Θ.lineRep v))
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) =
      (fun x : Fin 5 → RationalGL3 => T.B (z₁.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
        (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) -
      (fun x : Fin 5 → RationalGL3 => T.B (z₂.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
        (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) := by
    funext x
    exact LinearMap.congr_fun (map_sub T.B _ _) _
  unfold lineValue
  simp only [e₁, e₂, lc_sub, Finset.sum_sub_distrib]
  abel

/-- A vanishing Shapiro coordinate at a line gives a locally exact representative there. -/
theorem exists_line_exact (v : L) (z : MaximalCycles n χ .line)
    (hz : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (Θ.lineRep v)
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z) =
        0) :
    ∃ u : (Fin 2 → RationalGL3) → HomogeneousPoly n,
      (∀ γ ∈ levelStabilizer (Θ.lineRep v), ∀ a b : RationalGL3,
        u ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (u ![a, b])) ∧
      ∀ x : Fin 3 → RationalGL3, z.val.val x (Θ.lineRep v) = differentialOneRaw u x := by
  have hz' := (fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n χ)
    (Θ.lineRep v) z).symm.trans hz
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hz')
  refine ⟨p.val, fun γ hγ a b => ?_, fun x => ?_⟩
  · have e : (fun i => γ * (![a, b] : Fin 2 → RationalGL3) i) = ![γ * a, γ * b] := by
      funext i
      fin_cases i <;> rfl
    exact (congrArg p.val e).symm.trans (p.property ⟨γ, hγ⟩ ![a, b])
  · exact (congrFun (congrArg (fun c => c.val.val) hp) x).symm

/-- **The local value only depends on the Shapiro coordinate of the line class at the line**, for
a plane cocycle with exact edge pullback. -/
theorem lineValue_eq_of_line_fixedPointH2_eq (v : L) {z₁ z₂ : MaximalCycles n χ .line}
    {w₁ w₂ : EdgeCochains n χ 1} (hw₁ : EdgePrimitive z₁ w₁) (hw₂ : EdgePrimitive z₂ w₂)
    {y : MaximalCycles n χ .plane} (flat : PlaneEdgeExact y)
    (heq : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (Θ.lineRep v)
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z₁) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (Θ.lineRep v)
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line)
          z₂)) :
    lineValue Θ T v z₁ w₁ y = lineValue Θ T v z₂ w₂ y := by
  have hzero : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (Θ.lineRep v)
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line)
        (z₁ - z₂)) = 0 := by
    rw [map_sub]
    exact (map_sub _ _ _).trans (sub_eq_zero.mpr heq)
  obtain ⟨u, hu_eq, hu⟩ := exists_line_exact Θ v (z₁ - z₂) hzero
  have := lineValue_eq_zero_of_line_exact Θ T v (edgePrimitive_sub hw₁ hw₂) flat u hu_eq hu
  rw [lineValue_sub_left] at this
  exact sub_eq_zero.mp this

/-- **The local value is a function of the two local coordinates.** -/
theorem lineValue_eq_of_coordinates (v : L) {z₁ z₂ : MaximalCycles n χ .line}
    {w₁ w₂ : EdgeCochains n χ 1} (hw₁ : EdgePrimitive z₁ w₁) (hw₂ : EdgePrimitive z₂ w₂)
    {y₁ y₂ : MaximalCycles n χ .plane} (flat₁ : PlaneEdgeExact y₁)
    (hz : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (Θ.lineRep v)
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z₁) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (Θ.lineRep v)
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z₂))
    (hy : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
        (T.dualFlag (Θ.lineRep v))
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y₁) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (T.dualFlag (Θ.lineRep v))
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane)
          y₂)) :
    lineValue Θ T v z₁ w₁ y₁ = lineValue Θ T v z₂ w₂ y₂ := by
  rw [lineValue_eq_of_line_fixedPointH2_eq Θ T v hw₁ hw₂ flat₁ hz,
    lineValue_eq_of_fixedPointH2_eq Θ T v hw₂ hy]

end TernaryPeriodPolynomials.BoundaryDuality.LocalIndependence
