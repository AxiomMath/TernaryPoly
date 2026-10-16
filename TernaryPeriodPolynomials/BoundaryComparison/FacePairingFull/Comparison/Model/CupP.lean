module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Cup
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceEvaluation
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Plane.Pairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.Comparison

@[expose] public section


/-!
# The plane-supported twin of the model cone cup product

Mirror of `ModelCup` under the exchange of the line and plane sides (`DualityDataP`, `boundaryValueP`,
`EdgePrimitiveP`, `VertexPrimitiveP`, `dualityDataP` of `Plane/Core`).  The cone is taken with the plane complex in
the first slot: `planeCone z w = (z, 0, w)` for a plane cocycle `z` with edge primitive `w` (`z ∘ endpoint = dw`), and
`twistPlane T y s = (y^φ, 0, s^φ)` for a line cocycle `y` moved to the plane side by `φ` and `dualFlag`.  Then
`boundaryValueP_eq_cone` identifies the model's `w ⌣ y^φ - γ` on the plane side with the corner component of
`modelCupP (planeCone z w) (twistPlane T y s)` minus the pullback of the plane primitive `γ`, and
`modelCupP_eq` the cone cup product with `(dγ, 0, rₚ γ + boundaryValueP)`.  `traceValueP_eq_evalOmega` is the analogue of
`PairingCone.traceValue_eq_evalOmega` for `⟨ , ⟩_P`, from the same trace comparison.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable {n : ℕ} {χ : RankOneCharacter}

section Model

variable (T : DualityDataP n χ)

/-- The coefficient pairing as a biadditive map. -/
def BhomP : HomogeneousPoly n →+ HomogeneousPoly n →+ ℂ :=
  AddMonoidHom.mk' (fun u => (T.B u).toAddMonoidHom) (fun a b => by ext v; simp)

/-- The plane-supported cone cochain `(z, 0, w)`. -/
def planeCone (z : Ch RationalGL3 (Flags .plane → HomogeneousPoly n) 2)
    (w : Ch RationalGL3 (Edges → HomogeneousPoly n) 1) :
    Cone RationalGL3 (Flags .plane → HomogeneousPoly n) (Flags .line → HomogeneousPoly n)
      (Edges → HomogeneousPoly n) 1 :=
  ⟨z, 0, w⟩

/-- The `φ`-transport of a line cone class to a plane-supported cone cochain: `(y^φ, 0, s^φ)`. -/
def twistPlane (y : Ch RationalGL3 (Flags .line → HomogeneousPoly n) 2)
    (s : Ch RationalGL3 (Edges → HomogeneousPoly n) 1) :
    Cone RationalGL3 (Flags .plane → HomogeneousPoly n) (Flags .line → HomogeneousPoly n)
      (Edges → HomogeneousPoly n) 1 :=
  ⟨Ch.pre T.φ T.dualFlag y, 0, Ch.pre T.φ T.dualEdge s⟩

/-- The cone cup product of the model, for the coefficient pairing `B`. -/
def modelCupP {a b m : ℕ} (h : a + b + 1 = m)
    (U : Cone RationalGL3 (Flags .plane → HomogeneousPoly n) (Flags .line → HomogeneousPoly n)
      (Edges → HomogeneousPoly n) a)
    (U' : Cone RationalGL3 (Flags .plane → HomogeneousPoly n) (Flags .line → HomogeneousPoly n)
      (Edges → HomogeneousPoly n) b) :
    Cone RationalGL3 (Flags .plane → ℂ) (Flags .line → ℂ) (Edges → ℂ) m :=
  coneCup (pwPair _ (BhomP T)) (pwPair _ (BhomP T)) (pwPair _ (BhomP T)) (endRestr .plane)
    (endRestr .line) h U U'

/-- **The boundary cup product of the model is the corner component of the cone cup product** `(z, 0, w) ⌣
(y^φ, 0, s^φ)`, up to the pullback of the line primitive `γ`. -/
theorem boundaryValueP_eq_cone (z : Ch RationalGL3 (Flags .plane → HomogeneousPoly n) 2)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .line)
    (s : Ch RationalGL3 (Edges → HomogeneousPoly n) 1)
    (γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ) :
    boundaryValueP T w y γ =
      (modelCupP T (a := 1) (b := 1) (m := 3) rfl (planeCone z w.val) (twistPlane T y.val.val s)).c -
        Ch.map (endRestr .plane) γ := by
  funext x e
  have hf : x ∘ frontIdx 1 3 (by omega) = ![x 0, x 1] := by
    funext j; fin_cases j <;> rfl
  have hb : (fun i => T.φ ((x ∘ backIdx 1 2 3 rfl) i)) = ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] := by
    funext j; fin_cases j <;> rfl
  have h0 : Ch.map (endRestr (M := HomogeneousPoly n) .line)
      (0 : Ch RationalGL3 (Flags .line → HomogeneousPoly n) 2) = 0 := rfl
  simp only [boundaryValueP, modelCupP, coneCup, planeCone, twistPlane]
  rw [h0, cup_zero_left]
  simp only [Pi.sub_apply, smul_zero, add_zero]
  change _ - _ = pwPair Edges (BhomP T) (w.val (x ∘ frontIdx 1 3 (by omega)))
    (fun e' => y.val.val (fun i => T.φ ((x ∘ backIdx 1 2 3 rfl) i)) (T.dualFlag (endpoint .plane e'))) e - _
  rw [hf, hb, pwPair_apply]
  rfl


/-- The line cone `(z, 0, w)` of a line cocycle with an edge primitive is a cone cocycle. -/
theorem planeCone_isCocycle (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1)
    (hw : EdgePrimitiveP z w) :
    (planeCone z.val.val w.val).IsCocycle (endRestr (M := HomogeneousPoly n) .plane)
      (endRestr (M := HomogeneousPoly n) .line) := by
  refine ⟨dif_of_mem_cocycles z, by funext x; simp [dif, planeCone], ?_⟩
  funext x e
  have h := hw x e
  simp only [planeCone, Pi.sub_apply, Ch.map, endRestr, AddMonoidHom.mk'_apply, Pi.zero_apply, sub_zero]
  rw [dif_one]
  exact sub_eq_zero.mpr (by simpa [differentialOneRaw] using h)


/-- The `φ`-transported plane cone `(y^φ, 0, s^φ)` is a cone cocycle when `s` is an edge primitive of `y`. -/
theorem twistPlane_isCocycle (y : MaximalCycles n χ .line) (s : EdgeCochains n χ 1)
    (hs : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e) :
    (twistPlane T y.val.val s.val).IsCocycle (endRestr (M := HomogeneousPoly n) .plane)
      (endRestr (M := HomogeneousPoly n) .line) := by
  refine ⟨?_, by funext x; simp [dif, twistPlane], ?_⟩
  · change dif (Ch.pre T.φ T.dualFlag (y.val.val : Ch RationalGL3 (Flags .line → HomogeneousPoly n) 2)) = 0
    rw [dif_pre, dif_of_mem_cocycles y]
    funext x F
    rfl
  · funext x e
    change y.val.val (fun i => T.φ (x i)) (T.dualFlag (endpoint .plane e)) - 0 -
      dif (Ch.pre T.φ T.dualEdge (s.val : Ch RationalGL3 (Edges → HomogeneousPoly n) 1)) x e = 0
    rw [dif_pre]
    change _ - 0 - dif (s.val : Ch RationalGL3 (Edges → HomogeneousPoly n) 1) (fun i => T.φ (x i))
      (T.dualEdge e) = 0
    rw [dif_one, ← T.endpoint_dualEdge, hs]
    simp

/-- The model cone cup product of the two cone cocycles is a cone cocycle. -/
theorem modelCupP_isCocycle (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1)
    (hw : EdgePrimitiveP z w) (y : MaximalCycles n χ .line) (s : EdgeCochains n χ 1)
    (hs : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e) :
    (modelCupP T (a := 1) (b := 1) (m := 3) rfl (planeCone z.val.val w.val)
      (twistPlane T y.val.val s.val)).IsCocycle (endRestr .plane) (endRestr .line) :=
  coneCup_isCocycle (pwPair _ (BhomP T)) (pwPair _ (BhomP T)) (pwPair _ (BhomP T)) _ _ _ _ _ _
    (fun _ _ => rfl) (fun _ _ => rfl) rfl _ _ (planeCone_isCocycle z w hw) (twistPlane_isCocycle T y s hs)


/-- **The cone cup product of the two line-supported cone cocycles is the coboundary of `(γ, 0, 0)` plus the
corner cochain `boundaryValueP`**: the corner cochain of the model's face pairing represents the cone cup product. -/
theorem modelCupP_eq (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1)
    (y : MaximalCycles n χ .line) (s : EdgeCochains n χ 1)
    (γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ) (hγ : VertexPrimitiveP T z y γ) :
    modelCupP T (a := 1) (b := 1) (m := 3) rfl (planeCone z.val.val w.val) (twistPlane T y.val.val s.val) =
      ⟨dif γ, 0, Ch.map (endRestr .plane) γ + boundaryValueP T w y γ⟩ := by
  refine Cone.ext ?_ ?_ ?_
  · funext x F
    have hf : x ∘ frontIdx 2 4 (by omega) = ![x 0, x 1, x 2] := by
      funext j; fin_cases j <;> rfl
    have hb : (fun i => T.φ ((x ∘ backIdx 2 2 4 rfl) i)) = ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] := by
      funext j; fin_cases j <;> rfl
    change _ = dif γ x F
    rw [dif_three]
    change BhomP T ((z.val.val : Ch RationalGL3 (Flags .plane → HomogeneousPoly n) 2)
        (x ∘ frontIdx 2 4 (by omega)) F)
      ((y.val.val : Ch RationalGL3 (Flags .line → HomogeneousPoly n) 2)
        (fun i => T.φ ((x ∘ backIdx 2 2 4 rfl) i)) (T.dualFlag F)) = _
    rw [hf, hb, hγ.2 x F]
    rfl
  · exact cup_zero_left _ _ _
  · rw [boundaryValueP_eq_cone T z.val.val w y s γ]
    exact (add_sub_cancel _ _).symm


end Model

open TernaryPeriodPolynomials.Argument.FacePairingFull.Swap in
/-- **The plane face pairing is `c` times the evaluation on `Ω` of the corner cochain of the cone cup product**
(`Ω` and `c` from the whole-boundary trace comparison). -/
theorem traceValueP_eq_evalOmega :
    ∃ (Ω : MonoidAlgebra ℚ ((Fin 4 → RationalGL3) × Flag)) (c : ℂ), c ≠ 0 ∧
      ∀ {n : ℕ} (z : MaximalCycles n trivialCharacter .plane) (w : EdgeCochains n trivialCharacter 1)
        (y : MaximalCycles n trivialCharacter .line) (s : EdgeCochains n trivialCharacter 1)
        (γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
        (_hw : EdgePrimitiveP z w) (_hγ : VertexPrimitiveP (dualityDataP n trivialCharacter) z y γ),
        traceValueP z w y = c * evalOmega Ω
          ((modelCupP (dualityDataP n trivialCharacter) (a := 1) (b := 1) (m := 3) rfl
              (planeCone z.val.val w.val)
              (twistPlane (dualityDataP n trivialCharacter) y.val.val s.val)).c -
            Ch.map (endRestr .plane) γ) := by
  obtain ⟨Ω, c, κ, hc, hκ, htr, -, -⟩ := traceComparison
  refine ⟨Ω, c, hc, fun {n} z w y s γ hw hγ => ?_⟩
  rw [← boundaryValueP_eq_cone (dualityDataP n trivialCharacter) z.val.val w y s γ,
    ← trace_boundaryValue_eq_traceValueP hγ]
  exact htr ⟨boundaryValueP (dualityDataP n trivialCharacter) w y γ, boundaryValueP_mem_closed _ hw hγ⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
