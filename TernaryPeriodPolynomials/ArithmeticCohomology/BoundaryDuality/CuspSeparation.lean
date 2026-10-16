module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainLocal
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.CutoffPlane

@[expose] public section


/-!
# Separating the line cusps in the chain value

The local value of the chain value at a representative line `v̄` (`ChainLocal.lineValue`) only
sees the plane cocycle `y` at the dual plane `F = dualFlag v̄`. If `y` is exact there, i.e.
`y(·)(F) = ds` for a cochain `s` equivariant under `φ` of the stabilizer of `v̄`, the local value
vanishes (`lineValue_eq_zero_of_exact`): the edge terms become `⟨z ⌣ s^φ, C_e⟩` after removing the
coboundary `d(w ⌣ s^φ)`, and the filling term is `⟨d(z ⌣ s^φ), D_v⟩ = ⟨z ⌣ s^φ, Σ_e C_e⟩`.
Hence the local value only depends on the Shapiro coordinate of the class of `y` at `F`
(`lineValue_eq_of_fixedPointH2_eq`).

With two representative lines whose dual planes lie in the two different plane cusp orbits, the
cutoff of plane summand classes (`Separation.exists_cutoff_plane`) kills the other local
value. So boundary duality only needs, for every nonzero line summand class, ONE line cusp and one
plane summand class with nonzero local value there (`chainWitness_of_localWitness`). If the
representative lines meet every line orbit, that line cusp can be any one where the class has
nonzero Shapiro coordinate, so the input becomes duality at each line cusp separately
(`CuspDuality`, `associateDuality_of_cuspDuality`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.CuspSeparation

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainPairing
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary)

/-- Evaluation of chains is linear in the function. -/
theorem lc_sub {X : Type} (f g : X → ℂ) (c : X →₀ ℂ) :
    Finsupp.linearCombination ℂ (f - g) c =
      Finsupp.linearCombination ℂ f c - Finsupp.linearCombination ℂ g c := by
  simp only [Finsupp.linearCombination_apply, Pi.sub_apply, smul_sub, Finsupp.sum_sub]

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  (Θ : TraceData ι L P) {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- An element of the stabilizer of a complete flag stabilizes its line endpoint. -/
theorem mem_line_of_mem_edge {i : ι} {γ : RationalGL3} (hγ : γ ∈ levelStabilizer (Θ.edge i)) :
    γ ∈ levelStabilizer (Θ.lineRep (Θ.lineOf i)) := by
  obtain ⟨level, fixed⟩ := Subgroup.mem_inf.mp hγ
  refine Subgroup.mem_inf.mpr ⟨level, ?_⟩
  have fixed' : γ • Θ.edge i = Θ.edge i := MulAction.mem_stabilizer_iff.mp fixed
  rw [MulAction.mem_stabilizer_iff, ← Θ.line_endpoint i, ← endpoint_smul, fixed']

/-- **Vanishing of the local value at an exact plane cocycle.** -/
theorem lineValue_eq_zero_of_exact (v : L) {z : MaximalCycles n χ .line}
    {w : EdgeCochains n χ 1} {y : MaximalCycles n χ .plane} (hw : EdgePrimitive z w)
    (s : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hs_eq : ∀ γ ∈ levelStabilizer (Θ.lineRep v), ∀ a b : RationalGL3,
      s ![T.φ γ * a, T.φ γ * b] = rationalCoefficientComponent n χ (T.φ γ) (s ![a, b]))
    (hs : ∀ x : Fin 3 → RationalGL3,
      y.val.val x (T.dualFlag (Θ.lineRep v)) = differentialOneRaw s x) :
    lineValue Θ T v z w y = 0 := by
  set Lv := Θ.lineRep v with hLv
  set F := T.dualFlag Lv with hF
  -- the scalar three-cochain `z ⌣ s^φ` at the line
  let h : (Fin 4 → RationalGL3) → ℂ := fun x =>
    T.B (z.val.val ![x 0, x 1, x 2] Lv) (s ![T.φ (x 2), T.φ (x 3)])
  have h_inv : ∀ (γ : levelStabilizer Lv) x, h (fun i => γ.val * x i) = h x := by
    intro γ x
    have level : γ.val ∈ rationalLevel := (Subgroup.mem_inf.mp γ.property).1
    have fixed : γ.val⁻¹ • Lv = Lv := MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer RationalGL3 Lv).inv_mem (Subgroup.mem_inf.mp γ.property).2)
    have hz := congrFun (cochain_triple z.val ⟨γ.val, level⟩ (x 0) (x 1) (x 2)) Lv
    change z.val.val ![γ.val * x 0, γ.val * x 1, γ.val * x 2] Lv =
      rationalCoefficientComponent n χ γ.val (z.val.val ![x 0, x 1, x 2] (γ.val⁻¹ • Lv)) at hz
    rw [fixed] at hz
    change T.B (z.val.val ![γ.val * x 0, γ.val * x 1, γ.val * x 2] Lv)
        (s ![T.φ (γ.val * x 2), T.φ (γ.val * x 3)]) =
      T.B (z.val.val ![x 0, x 1, x 2] Lv) (s ![T.φ (x 2), T.φ (x 3)])
    rw [hz, map_mul, map_mul, hs_eq γ.val γ.property, T.invariant γ.val level]
  -- the filling term is the evaluation of `dh` on the filling chain
  have fill : (fun x => T.B (z.val.val ![x 0, x 1, x 2] Lv)
      (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] F)) = differentialThreeRaw h := by
    funext x
    have cocycle : IsCocycleTwo (fun x' => z.val.val x' Lv) := fun x' =>
      congrFun (isCocycleTwo_of_mem z x') Lv
    rw [show h = cupTwoOne T.B T.φ (fun x' => z.val.val x' Lv) s from rfl,
      differentialThreeRaw_cupTwoOne T.B T.φ cocycle s x, hs]
  -- each edge term is `⟨h, C_e⟩` up to a coboundary
  have edge : ∀ i ∈ Finset.univ.filter (fun i => Θ.lineOf i = v),
      Finsupp.linearCombination ℂ (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F)) (Θ.chain i) =
      Finsupp.linearCombination ℂ h (Θ.chain i) := by
    intro i hi
    have hv : Θ.lineOf i = v := (Finset.mem_filter.mp hi).2
    let g : (Fin 3 → RationalGL3) → ℂ := fun x =>
      T.B (w.val ![x 0, x 1] (Θ.edge i)) (s ![T.φ (x 1), T.φ (x 2)])
    have g_inv : ∀ (γ : levelStabilizer (Θ.edge i)) x, g (fun j => γ.val * x j) = g x := by
      intro γ x
      have level : γ.val ∈ rationalLevel := (Subgroup.mem_inf.mp γ.property).1
      have fixed : γ.val⁻¹ • Θ.edge i = Θ.edge i := MulAction.mem_stabilizer_iff.mp
        ((MulAction.stabilizer RationalGL3 (Θ.edge i)).inv_mem
          (Subgroup.mem_inf.mp γ.property).2)
      have hline : γ.val ∈ levelStabilizer Lv := by
        rw [hLv, ← hv]
        exact mem_line_of_mem_edge Θ γ.property
      have hwγ := congrFun (cochain_pair w ⟨γ.val, level⟩ (x 0) (x 1)) (Θ.edge i)
      change w.val ![γ.val * x 0, γ.val * x 1] (Θ.edge i) =
        rationalCoefficientComponent n χ γ.val (w.val ![x 0, x 1] (γ.val⁻¹ • Θ.edge i)) at hwγ
      rw [fixed] at hwγ
      change T.B (w.val ![γ.val * x 0, γ.val * x 1] (Θ.edge i))
          (s ![T.φ (γ.val * x 1), T.φ (γ.val * x 2)]) =
        T.B (w.val ![x 0, x 1] (Θ.edge i)) (s ![T.φ (x 1), T.φ (x 2)])
      rw [hwγ, map_mul, map_mul, hs_eq γ.val hline, T.invariant γ.val level]
    have pointwise : (fun x => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F)) = h - differentialTwoRaw g := by
      funext x
      have hz : z.val.val ![x 0, x 1, x 2] Lv =
          w.val ![x 1, x 2] (Θ.edge i) - w.val ![x 0, x 2] (Θ.edge i) +
            w.val ![x 0, x 1] (Θ.edge i) := by
        rw [hLv, ← hv, ← Θ.line_endpoint i]
        exact hw ![x 0, x 1, x 2] (Θ.edge i)
      have hy : y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F =
          s ![T.φ (x 2), T.φ (x 3)] - s ![T.φ (x 1), T.φ (x 3)] + s ![T.φ (x 1), T.φ (x 2)] :=
        hs _
      change T.B (w.val ![x 0, x 1] (Θ.edge i))
          (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] F) =
        T.B (z.val.val ![x 0, x 1, x 2] Lv) (s ![T.φ (x 2), T.φ (x 3)]) -
          (T.B (w.val ![x 1, x 2] (Θ.edge i)) (s ![T.φ (x 2), T.φ (x 3)]) -
            T.B (w.val ![x 0, x 2] (Θ.edge i)) (s ![T.φ (x 2), T.φ (x 3)]) +
            T.B (w.val ![x 0, x 1] (Θ.edge i)) (s ![T.φ (x 1), T.φ (x 3)]) -
            T.B (w.val ![x 0, x 1] (Θ.edge i)) (s ![T.φ (x 1), T.φ (x 2)]))
      rw [hy, hz]
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
      abel
    rw [pointwise, lc_sub, eval_boundary_null g g_inv (Θ.chain i) (Θ.edge_closed i), sub_zero]
  unfold lineValue
  rw [← hLv, ← hF, Finset.sum_congr rfl edge, fill,
    ← map_sum (Finsupp.linearCombination ℂ h)]
  have hnull := eval_null h h_inv (Θ.line_filled v)
  rw [map_sub, sub_eq_zero, ← eval_differentialThree] at hnull
  rw [hnull, sub_self]

/-- The local value is additive-linear in the plane cocycle. -/
theorem lineValue_sub (v : L) (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (y₁ y₂ : MaximalCycles n χ .plane) :
    lineValue Θ T v z w (y₁ - y₂) = lineValue Θ T v z w y₁ - lineValue Θ T v z w y₂ := by
  have e₁ : ∀ i, (fun x : Fin 4 → RationalGL3 => T.B (w.val ![x 0, x 1] (Θ.edge i))
      ((y₁ - y₂).val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (Θ.lineRep v)))) =
      (fun x : Fin 4 → RationalGL3 => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y₁.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (Θ.lineRep v)))) -
      (fun x : Fin 4 → RationalGL3 => T.B (w.val ![x 0, x 1] (Θ.edge i))
        (y₂.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (Θ.lineRep v)))) := by
    intro i
    funext x
    exact map_sub _ _ _
  have e₂ : (fun x : Fin 5 → RationalGL3 => T.B (z.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
      ((y₁ - y₂).val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) =
      (fun x : Fin 5 → RationalGL3 => T.B (z.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
        (y₁.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) -
      (fun x : Fin 5 → RationalGL3 => T.B (z.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
        (y₂.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag (Θ.lineRep v)))) := by
    funext x
    exact map_sub _ _ _
  unfold lineValue
  simp only [e₁, e₂, lc_sub, Finset.sum_sub_distrib]
  abel

/-- A vanishing Shapiro coordinate at the dual plane gives an exact representative there. -/
theorem exists_exact_of_fixedPointH2 (v : L) (y : MaximalCycles n χ .plane)
    (hy : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (T.dualFlag (Θ.lineRep v))
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) =
        0) :
    ∃ s : (Fin 2 → RationalGL3) → HomogeneousPoly n,
      (∀ γ ∈ levelStabilizer (Θ.lineRep v), ∀ a b : RationalGL3,
        s ![T.φ γ * a, T.φ γ * b] = rationalCoefficientComponent n χ (T.φ γ) (s ![a, b])) ∧
      ∀ x : Fin 3 → RationalGL3,
        y.val.val x (T.dualFlag (Θ.lineRep v)) = differentialOneRaw s x := by
  have hy' := (fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n χ)
    (T.dualFlag (Θ.lineRep v)) y).symm.trans hy
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hy')
  refine ⟨p.val, fun γ hγ a b => ?_, fun x => ?_⟩
  · obtain ⟨level, fixed⟩ := Subgroup.mem_inf.mp hγ
    have hφ : T.φ γ ∈ fixedPointLevel rationalLevel (T.dualFlag (Θ.lineRep v)) := by
      refine Subgroup.mem_inf.mpr ⟨T.level γ level, ?_⟩
      rw [MulAction.mem_stabilizer_iff, ← T.dualFlag_smul,
        MulAction.mem_stabilizer_iff.mp fixed]
    have e : (fun i => T.φ γ * (![a, b] : Fin 2 → RationalGL3) i) = ![T.φ γ * a, T.φ γ * b] := by
      funext i
      fin_cases i <;> rfl
    exact (congrArg p.val e).symm.trans (p.property ⟨T.φ γ, hφ⟩ ![a, b])
  · exact (congrFun (congrArg (fun c => c.val.val) hp) x).symm

/-- **The local value only depends on the Shapiro coordinate of the plane class at the dual
plane.** -/
theorem lineValue_eq_of_fixedPointH2_eq (v : L) {z : MaximalCycles n χ .line}
    {w : EdgeCochains n χ 1} (hw : EdgePrimitive z w) {y₁ y₂ : MaximalCycles n χ .plane}
    (heq : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
        (T.dualFlag (Θ.lineRep v))
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y₁) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (T.dualFlag (Θ.lineRep v))
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane)
          y₂)) :
    lineValue Θ T v z w y₁ = lineValue Θ T v z w y₂ := by
  have hzero : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
      (T.dualFlag (Θ.lineRep v))
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane)
        (y₁ - y₂)) = 0 := by
    rw [map_sub]
    exact (map_sub _ _ _).trans (sub_eq_zero.mpr heq)
  obtain ⟨s, hs_eq, hs⟩ := exists_exact_of_fixedPointH2 Θ T v (y₁ - y₂) hzero
  have := lineValue_eq_zero_of_exact Θ T v hw s hs_eq hs
  rw [lineValue_sub] at this
  exact sub_eq_zero.mp this

/-- A plane class vanishing at a plane cusp vanishes at every plane flag of that cusp orbit. -/
theorem fixedPointH2_eq_zero_of_cuspRes {good : Bool} {F : Flags .plane}
    (hF : ∃ γ : rationalLevel, γ.val • cuspFlag .plane good = F) {a : StratumH2 n χ .plane}
    (ha : cuspRes n χ .plane good a = 0) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) F a = 0 := by
  obtain ⟨γ, hγ⟩ := hF
  rw [← stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) γ
    (cuspFlag .plane good) F hγ a]
  change stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n χ) γ
    (cuspFlag .plane good) F hγ (cuspRes n χ .plane good a) = 0
  rw [ha, map_zero]

section Witness

variable {D : InducingData n}

/-- **The local witness**: for every nonzero line summand class, one representative line and one
plane summand class, with representatives, whose local value there is nonzero. -/
def LocalWitness (Θ : TraceData ι L P) (D : InducingData n) (T : DualityData n D.chi) : Prop :=
  ∀ b ∈ boundarySummand D .line, b ≠ 0 → ∃ v : L, ∃ ξ ∈ boundarySummand D .plane,
    ∃ (z : MaximalCycles n D.chi .line) (w : EdgeCochains n D.chi 1)
      (y : MaximalCycles n D.chi .plane),
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z =
        b ∧
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y =
        ξ ∧
      EdgePrimitive z w ∧ lineValue Θ T v z w y ≠ 0

/-- **Separation of the line cusps.** If the dual planes of the representative lines lie in plane
cusp orbits `good v`, and two different lines have different plane cusps, a local witness is a
chain witness. -/
theorem chainWitness_of_localWitness (T : DualityData n D.chi) (good : L → Bool)
    (hdual : ∀ v, ∃ γ : rationalLevel, γ.val • cuspFlag .plane (good v) = T.dualFlag (Θ.lineRep v))
    (hgood : ∀ u v, u ≠ v → good u = !good v) (local_ : LocalWitness Θ D T) :
    ChainWitness Θ D T := by
  intro b hb hne
  obtain ⟨v, ξ, hξ, z, w, y, hz, hy, hw, hval⟩ := local_ b hb hne
  obtain ⟨ξ', hξ', hsame, hzero⟩ := Separation.exists_cutoff_plane D (good v) hξ
  obtain ⟨y', hy'⟩ := Submodule.mkQ_surjective _ ξ'
  have hy'' : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y' = ξ' := hy'
  refine ⟨ξ', hξ', z, w, y', hz, hy'', hw, ?_⟩
  rw [chainValue_eq_sum]
  have others : ∀ u ∈ Finset.univ, u ≠ v → lineValue Θ T u z w y' = 0 := by
    intro u _ huv
    have hcusp : cuspRes n D.chi .plane (good u)
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
          y') = 0 := by
      rw [hy'', hgood u v huv]
      exact hzero
    obtain ⟨s, hs_eq, hs⟩ := exists_exact_of_fixedPointH2 Θ T u y'
      (fixedPointH2_eq_zero_of_cuspRes (hdual u) hcusp)
    exact lineValue_eq_zero_of_exact Θ T u hw s hs_eq hs
  rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ v) others]
  have hcoord : fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi)
      (T.dualFlag (Θ.lineRep v))
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
        y' - classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y) = 0 := by
    refine fixedPointH2_eq_zero_of_cuspRes (hdual v) ?_
    rw [map_sub, hy'', hy, hsame, sub_self]
  replace hcoord := sub_eq_zero.mp ((map_sub _ _ _).symm.trans hcoord)
  rw [lineValue_eq_of_fixedPointH2_eq Θ T v hw hcoord]
  exact hval

/-- **Duality at one line cusp**: every line summand class with nonzero Shapiro coordinate at the
representative line `v̄` has nonzero local value at `v̄` against some plane summand class. -/
def CuspDuality (Θ : TraceData ι L P) (D : InducingData n) (T : DualityData n D.chi) (v : L) :
    Prop :=
  ∀ b ∈ boundarySummand D .line,
    fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) (Θ.lineRep v) b ≠ 0 →
    ∃ ξ ∈ boundarySummand D .plane,
    ∃ (z : MaximalCycles n D.chi .line) (w : EdgeCochains n D.chi 1)
      (y : MaximalCycles n D.chi .plane),
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z =
        b ∧
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y =
        ξ ∧
      EdgePrimitive z w ∧ lineValue Θ T v z w y ≠ 0

/-- A nonzero line class has a nonzero Shapiro coordinate at one of the representative lines, if
these meet every orbit of line flags. -/
theorem exists_lineRep_ne_zero
    (hlines : ∀ F : Flags .line, ∃ v : L, ∃ γ : rationalLevel, γ.val • Θ.lineRep v = F)
    {b : StratumH2 n χ .line} (hb : b ≠ 0) :
    ∃ v : L, fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (Θ.lineRep v) b ≠ 0 := by
  by_contra hcon
  have h : ∀ v : L,
      fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (Θ.lineRep v) b = 0 :=
    fun v => Classical.byContradiction fun hne => hcon ⟨v, hne⟩
  apply hb
  refine (eq_zero_iff_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) b).mpr ?_
  intro F
  obtain ⟨v, γ, hγ⟩ := hlines F
  rw [← stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) γ
    (Θ.lineRep v) F hγ b, h v, map_zero]

/-- **Duality at each line cusp gives the local witness.** -/
theorem localWitness_of_cuspDuality (T : DualityData n D.chi)
    (hlines : ∀ F : Flags .line, ∃ v : L, ∃ γ : rationalLevel, γ.val • Θ.lineRep v = F)
    (duality : ∀ v, CuspDuality Θ D T v) : LocalWitness Θ D T := by
  intro b hb hne
  obtain ⟨v, hv⟩ := exists_lineRep_ne_zero Θ hlines hne
  exact ⟨v, duality v b hb hv⟩

/-- **Boundary duality on the associate pair from duality at each line cusp**, for chain data
whose representative lines meet every line orbit and whose dual planes lie in the two different
plane cusp orbits. -/
theorem associateDuality_of_cuspDuality (T : DualityData n D.chi) (good : L → Bool)
    (hdual : ∀ v, ∃ γ : rationalLevel, γ.val • cuspFlag .plane (good v) = T.dualFlag (Θ.lineRep v))
    (hgood : ∀ u v, u ≠ v → good u = !good v)
    (hlines : ∀ F : Flags .line, ∃ v : L, ∃ γ : rationalLevel, γ.val • Θ.lineRep v = F)
    (duality : ∀ v, CuspDuality Θ D T v) : AssociateDuality D T.φ T.dualFlag T.B :=
  associateDuality_of_chainWitness Θ T
    (chainWitness_of_localWitness Θ T good hdual hgood
      (localWitness_of_cuspDuality Θ T hlines duality))

end Witness

end TernaryPeriodPolynomials.BoundaryDuality.CuspSeparation
