module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Diagonal
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceRepresentatives

@[expose] public section


/-!
# The model boundary cup product is the corner component of the cone cup product

`ModelDiagonal` constructs, for homogeneous cochains on a vertex set `V`, the Alexander-Whitney cup product, the
homotopy-pullback cone of a line complex and a plane complex over a corner complex, and its cup product with the
Leibniz rule.  Here it is instantiated for the cochain model of the arithmetic boundary: `V = GL₃(ℚ)`, line, plane and
corner values `Flags .line → M`, `Flags .plane → M`, `Edges → M` (`M = HomogeneousPoly n`), restrictions along the
endpoint maps (`endRestr`) and the coefficient pairing `T.B` of a `DualityData` taken pointwise (`pwPair`, `Bhom`).

* `lineCone z w = (z, 0, w)`: the line-supported cone cochain of a line cocycle `z` with edge primitive `w`
  (`lineCone_isCocycle`); `twistLine T y s = (y^φ, 0, s^φ)`: the `φ`-transport of a plane cocycle `y` with edge primitive
  `s` to a line-supported cone cochain for the twisted coefficient (`twistLine_isCocycle`).
* `modelCup`: the cone cup product with the pointwise pairing; `modelCup_isCocycle`: it is a cone cocycle (Leibniz).
* `boundaryValue_eq_cone`: the model's boundary cup product `boundaryValue T w y γ = w ⌣ y^φ - γ`
  (`TraceRepresentatives`) is the corner component of `modelCup (lineCone z w) (twistLine T y s)` minus the pullback
  of the line cochain `γ`.
* `modelCup_eq`: for a vertex primitive `γ` (`dγ = z ⌣ y^φ`), `modelCup (lineCone z w) (twistLine T y s) =
  (dγ, 0, rₗ γ + boundaryValue T w y γ)`, i.e. the cone cup product is cohomologous (by the cone coboundary of
  `(γ, 0, 0)`) to the cocycle whose only non-zero component is the corner cochain whose trace is the face pairing.
  Hence the face pairing is the trace of the corner component of a cone cup product of two cone cocycles.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable {n : ℕ} {χ : RankOneCharacter}

/-- Pointwise product of functions on a set `S` along a biadditive pairing. -/
def pwPair {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    (S : Type) (β : M₁ →+ M₂ →+ M₃) : (S → M₁) →+ (S → M₂) →+ (S → M₃) :=
  AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun v s => β (u s) (v s))
    (fun a b => by funext s; simp)) (fun a b => by ext v s; simp)

theorem pwPair_apply {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    (S : Type) (β : M₁ →+ M₂ →+ M₃) (u : S → M₁) (v : S → M₂) (s : S) :
    pwPair S β u v s = β (u s) (v s) := rfl

/-- Restriction of functions on flags to complete flags along an endpoint map. -/
def endRestr {M : Type} [AddCommGroup M] (s : Side) : (Flags s → M) →+ (Edges → M) :=
  AddMonoidHom.mk' (fun u e => u (endpoint s e)) (fun _ _ => rfl)


section Raw

variable {G : Type} {A : Type} [AddCommGroup A]

theorem dif_one (f : Ch G A 1) (x : Fin 3 → G) : dif f x = differentialOneRaw f x := by
  have h0 : x ∘ Fin.succAbove (0 : Fin 3) = ![x 1, x 2] := by
    funext j; fin_cases j <;> rfl
  have h1 : x ∘ Fin.succAbove (1 : Fin 3) = ![x 0, x 2] := by
    funext j; fin_cases j <;> rfl
  have h2 : x ∘ Fin.succAbove (2 : Fin 3) = ![x 0, x 1] := by
    funext j; fin_cases j <;> rfl
  have : dif f x = ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • f (x ∘ i.succAbove) := rfl
  rw [this, Fin.sum_univ_three, h0, h1, h2]
  simp only [differentialOneRaw, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_smul, pow_one,
    neg_smul, ← sub_eq_add_neg]
  have h2' : ((-1 : ℤ) ^ 2) = 1 := by norm_num
  rw [h2', one_smul]

theorem dif_two (f : Ch G A 2) (x : Fin 4 → G) :
    dif f x = f ![x 1, x 2, x 3] - f ![x 0, x 2, x 3] + f ![x 0, x 1, x 3] - f ![x 0, x 1, x 2] := by
  have h0 : x ∘ Fin.succAbove (0 : Fin 4) = ![x 1, x 2, x 3] := by
    funext j; fin_cases j <;> rfl
  have h1 : x ∘ Fin.succAbove (1 : Fin 4) = ![x 0, x 2, x 3] := by
    funext j; fin_cases j <;> rfl
  have h2 : x ∘ Fin.succAbove (2 : Fin 4) = ![x 0, x 1, x 3] := by
    funext j; fin_cases j <;> rfl
  have h3 : x ∘ Fin.succAbove (3 : Fin 4) = ![x 0, x 1, x 2] := by
    funext j; fin_cases j <;> rfl
  have : dif f x = ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • f (x ∘ i.succAbove) := rfl
  rw [this, Fin.sum_univ_four, h0, h1, h2, h3]
  norm_num
  abel

theorem dif_three (f : Ch G A 3) (x : Fin 5 → G) : dif f x = differentialThreeRaw f x := by
  have h0 : x ∘ Fin.succAbove (0 : Fin 5) = ![x 1, x 2, x 3, x 4] := by
    funext j; fin_cases j <;> rfl
  have h1 : x ∘ Fin.succAbove (1 : Fin 5) = ![x 0, x 2, x 3, x 4] := by
    funext j; fin_cases j <;> rfl
  have h2 : x ∘ Fin.succAbove (2 : Fin 5) = ![x 0, x 1, x 3, x 4] := by
    funext j; fin_cases j <;> rfl
  have h3 : x ∘ Fin.succAbove (3 : Fin 5) = ![x 0, x 1, x 2, x 4] := by
    funext j; fin_cases j <;> rfl
  have h4 : x ∘ Fin.succAbove (4 : Fin 5) = ![x 0, x 1, x 2, x 3] := by
    funext j; fin_cases j <;> rfl
  have : dif f x = ∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • f (x ∘ i.succAbove) := rfl
  rw [this, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  simp only [differentialThreeRaw]
  norm_num
  abel

end Raw


section Model

variable (T : DualityData n χ)

/-- The coefficient pairing as a biadditive map. -/
def Bhom : HomogeneousPoly n →+ HomogeneousPoly n →+ ℂ :=
  AddMonoidHom.mk' (fun u => (T.B u).toAddMonoidHom) (fun a b => by ext v; simp)

/-- The line-supported cone cochain `(z, 0, w)`. -/
def lineCone (z : Ch RationalGL3 (Flags .line → HomogeneousPoly n) 2)
    (w : Ch RationalGL3 (Edges → HomogeneousPoly n) 1) :
    Cone RationalGL3 (Flags .line → HomogeneousPoly n) (Flags .plane → HomogeneousPoly n)
      (Edges → HomogeneousPoly n) 1 :=
  ⟨z, 0, w⟩

/-- The `φ`-transport of a plane cone class to a line-supported cone cochain: `(y^φ, 0, s^φ)`. -/
def twistLine (y : Ch RationalGL3 (Flags .plane → HomogeneousPoly n) 2)
    (s : Ch RationalGL3 (Edges → HomogeneousPoly n) 1) :
    Cone RationalGL3 (Flags .line → HomogeneousPoly n) (Flags .plane → HomogeneousPoly n)
      (Edges → HomogeneousPoly n) 1 :=
  ⟨Ch.pre T.φ T.dualFlag y, 0, Ch.pre T.φ T.dualEdge s⟩

/-- The cone cup product of the model, for the coefficient pairing `B`. -/
def modelCup {a b m : ℕ} (h : a + b + 1 = m)
    (U : Cone RationalGL3 (Flags .line → HomogeneousPoly n) (Flags .plane → HomogeneousPoly n)
      (Edges → HomogeneousPoly n) a)
    (U' : Cone RationalGL3 (Flags .line → HomogeneousPoly n) (Flags .plane → HomogeneousPoly n)
      (Edges → HomogeneousPoly n) b) :
    Cone RationalGL3 (Flags .line → ℂ) (Flags .plane → ℂ) (Edges → ℂ) m :=
  coneCup (pwPair _ (Bhom T)) (pwPair _ (Bhom T)) (pwPair _ (Bhom T)) (endRestr .line)
    (endRestr .plane) h U U'

/-- **The boundary cup product of the model is the corner component of the cone cup product** `(z, 0, w) ⌣
(y^φ, 0, s^φ)`, up to the pullback of the line primitive `γ`. -/
theorem boundaryValue_eq_cone (z : Ch RationalGL3 (Flags .line → HomogeneousPoly n) 2)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (s : Ch RationalGL3 (Edges → HomogeneousPoly n) 1)
    (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ) :
    boundaryValue T w y γ =
      (modelCup T (a := 1) (b := 1) (m := 3) rfl (lineCone z w.val) (twistLine T y.val.val s)).c -
        Ch.map (endRestr .line) γ := by
  funext x e
  have hf : x ∘ frontIdx 1 3 (by omega) = ![x 0, x 1] := by
    funext j; fin_cases j <;> rfl
  have hb : (fun i => T.φ ((x ∘ backIdx 1 2 3 rfl) i)) = ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] := by
    funext j; fin_cases j <;> rfl
  have h0 : Ch.map (endRestr (M := HomogeneousPoly n) .plane)
      (0 : Ch RationalGL3 (Flags .plane → HomogeneousPoly n) 2) = 0 := rfl
  simp only [boundaryValue, modelCup, coneCup, lineCone, twistLine]
  rw [h0, cup_zero_left]
  simp only [Pi.sub_apply, smul_zero, add_zero]
  change _ - _ = pwPair Edges (Bhom T) (w.val (x ∘ frontIdx 1 3 (by omega)))
    (fun e' => y.val.val (fun i => T.φ ((x ∘ backIdx 1 2 3 rfl) i)) (T.dualFlag (endpoint .line e'))) e - _
  rw [hf, hb, pwPair_apply]
  rfl


/-- A model degree-two cocycle is a cocycle of the homogeneous cochain complex. -/
theorem dif_of_mem_cocycles {s : Side} (z : MaximalCycles n χ s) :
    dif (z.val.val : Ch RationalGL3 (Flags s → HomogeneousPoly n) 2) = 0 := by
  funext x F
  have h := congrFun (congrArg (fun f => f x) z.property) F
  rw [dif_two]
  simpa [differentialTwo] using h

/-- The line cone `(z, 0, w)` of a line cocycle with an edge primitive is a cone cocycle. -/
theorem lineCone_isCocycle (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (hw : EdgePrimitive z w) :
    (lineCone z.val.val w.val).IsCocycle (endRestr (M := HomogeneousPoly n) .line)
      (endRestr (M := HomogeneousPoly n) .plane) := by
  refine ⟨dif_of_mem_cocycles z, by funext x; simp [dif, lineCone], ?_⟩
  funext x e
  have h := hw x e
  simp only [lineCone, Pi.sub_apply, Ch.map, endRestr, AddMonoidHom.mk'_apply, Pi.zero_apply, sub_zero]
  rw [dif_one]
  exact sub_eq_zero.mpr (by simpa [differentialOneRaw] using h)


/-- The `φ`-transported plane cone `(y^φ, 0, s^φ)` is a cone cocycle when `s` is an edge primitive of `y`. -/
theorem twistLine_isCocycle (y : MaximalCycles n χ .plane) (s : EdgeCochains n χ 1)
    (hs : ∀ x e, y.val.val x (endpoint .plane e) = differentialOneRaw s.val x e) :
    (twistLine T y.val.val s.val).IsCocycle (endRestr (M := HomogeneousPoly n) .line)
      (endRestr (M := HomogeneousPoly n) .plane) := by
  refine ⟨?_, by funext x; simp [dif, twistLine], ?_⟩
  · change dif (Ch.pre T.φ T.dualFlag (y.val.val : Ch RationalGL3 (Flags .plane → HomogeneousPoly n) 2)) = 0
    rw [dif_pre, dif_of_mem_cocycles y]
    funext x F
    rfl
  · funext x e
    change y.val.val (fun i => T.φ (x i)) (T.dualFlag (endpoint .line e)) - 0 -
      dif (Ch.pre T.φ T.dualEdge (s.val : Ch RationalGL3 (Edges → HomogeneousPoly n) 1)) x e = 0
    rw [dif_pre]
    change _ - 0 - dif (s.val : Ch RationalGL3 (Edges → HomogeneousPoly n) 1) (fun i => T.φ (x i))
      (T.dualEdge e) = 0
    rw [dif_one, ← T.endpoint_dualEdge, hs]
    simp

/-- The model cone cup product of the two cone cocycles is a cone cocycle. -/
theorem modelCup_isCocycle (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (hw : EdgePrimitive z w) (y : MaximalCycles n χ .plane) (s : EdgeCochains n χ 1)
    (hs : ∀ x e, y.val.val x (endpoint .plane e) = differentialOneRaw s.val x e) :
    (modelCup T (a := 1) (b := 1) (m := 3) rfl (lineCone z.val.val w.val)
      (twistLine T y.val.val s.val)).IsCocycle (endRestr .line) (endRestr .plane) :=
  coneCup_isCocycle (pwPair _ (Bhom T)) (pwPair _ (Bhom T)) (pwPair _ (Bhom T)) _ _ _ _ _ _
    (fun _ _ => rfl) (fun _ _ => rfl) rfl _ _ (lineCone_isCocycle z w hw) (twistLine_isCocycle T y s hs)


/-- **The cone cup product of the two line-supported cone cocycles is the coboundary of `(γ, 0, 0)` plus the
corner cochain `boundaryValue`**: the corner cochain of the model's face pairing represents the cone cup product. -/
theorem modelCup_eq (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (y : MaximalCycles n χ .plane) (s : EdgeCochains n χ 1)
    (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ) (hγ : VertexPrimitive T z y γ) :
    modelCup T (a := 1) (b := 1) (m := 3) rfl (lineCone z.val.val w.val) (twistLine T y.val.val s.val) =
      ⟨dif γ, 0, Ch.map (endRestr .line) γ + boundaryValue T w y γ⟩ := by
  refine Cone.ext ?_ ?_ ?_
  · funext x F
    have hf : x ∘ frontIdx 2 4 (by omega) = ![x 0, x 1, x 2] := by
      funext j; fin_cases j <;> rfl
    have hb : (fun i => T.φ ((x ∘ backIdx 2 2 4 rfl) i)) = ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] := by
      funext j; fin_cases j <;> rfl
    change _ = dif γ x F
    rw [dif_three]
    change Bhom T ((z.val.val : Ch RationalGL3 (Flags .line → HomogeneousPoly n) 2)
        (x ∘ frontIdx 2 4 (by omega)) F)
      ((y.val.val : Ch RationalGL3 (Flags .plane → HomogeneousPoly n) 2)
        (fun i => T.φ ((x ∘ backIdx 2 2 4 rfl) i)) (T.dualFlag F)) = _
    rw [hf, hb, hγ.2 x F]
    rfl
  · exact cup_zero_left _ _ _
  · rw [boundaryValue_eq_cone T z.val.val w y s γ]
    exact (add_sub_cancel _ _).symm

end Model

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
