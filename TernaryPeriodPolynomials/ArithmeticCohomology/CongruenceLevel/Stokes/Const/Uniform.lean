module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Rel
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Graph

@[expose] public section


/-!
# Uniformity of the corner functional over the flag orbits

Formalized by Claude Sonnet 5.5.

`flagPhi o` is a linear functional on the (one dimensional) group `H³(Stab o.out; ℚ)`.  Given classes `G o` spanning these groups (`H3FlagData`, the output of step (ii) of the face factorisation),
`λ o = flagPhi o (G o)` is the coefficient of the corner functional against the fundamental class of the flag group.

* the relations (R) `line_relation`, `plane_relation`: `Φ` kills all classes coming from line and plane stabilizers;
* `LineImageSumZero`, `PlaneImageSumZero`: the hypotheses (B_L), (B_P) that the joint restriction images of the line (plane) stabilizers in the flag groups over one line (plane) orbit are the sum-zero hyperplanes
  with respect to the classes `G o`;
* `line_lambda_eq`, `plane_lambda_eq`: `λ` is constant on the flag orbits over one line (plane) orbit; `lambda_universal`: by connectivity of the orbit graph it is constant altogether.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFaceFactor
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.OrdinaryIncidence (Line Plane)
open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

/-- **Fibrewise constancy from the sum-zero relations**: if `∑ x o * λ o = 0` for every `x` whose sum over each fibre of `ν` vanishes, then `λ` is constant on the fibres of `ν`. -/
theorem fibre_const {O A : Type} [Fintype O] [DecidableEq O] [DecidableEq A] (ν : O → A) (lam : O → ℚ)
    (H : ∀ x : O → ℚ, (∀ a, ∑ o ∈ Finset.univ.filter (fun o => ν o = a), x o = 0) → ∑ o, x o * lam o = 0)
    {o o' : O} (h : ν o = ν o') : lam o = lam o' := by
  by_cases hoo : o = o'
  · rw [hoo]
  · have hx := H (Pi.single o 1 - Pi.single o' 1) (fun a => by
      rw [Finset.sum_filter]
      have e : ∀ x, (if ν x = a then (Pi.single o (1:ℚ) - Pi.single o' 1 : O → ℚ) x else 0) =
          (Pi.single o (if ν o = a then (1:ℚ) else 0) : O → ℚ) x - (Pi.single o' (if ν o' = a then (1:ℚ) else 0) : O → ℚ) x := by
        intro x
        by_cases hxo : x = o
        · subst hxo
          by_cases hxo' : x = o'
          · exact absurd hxo' hoo
          · simp [hxo']
        · by_cases hxo' : x = o'
          · subst hxo'
            simp [hxo]
            split_ifs <;> simp
          · simp [hxo, hxo']
      simp only [e, Finset.sum_sub_distrib, Finset.sum_pi_single']
      simp only [Finset.mem_univ, ite_true]
      by_cases ha : ν o = a
      · have ha' : ν o' = a := h ▸ ha
        simp [ha, ha']
      · have ha' : ¬ ν o' = a := fun h' => ha (h.trans h')
        simp [ha, ha'])
    simpa [sub_mul, Finset.sum_sub_distrib, Pi.single_apply, sub_eq_zero] using hx

/-- Elements of `Γ(6)` carrying the representative of the line (plane) orbit of each flag orbit to the line (plane) of the representative flag: the frames along which the cohomology of the line
(plane) stabilizers is transported to the flag groups. -/
structure ConjFrames where
  γL : labelOrbits Γ6 Flag → Γ6
  hL : ∀ o, γL o • (flagLineOrbit o).out = flagLineOf o.out
  γP : labelOrbits Γ6 Flag → Γ6
  hP : ∀ o, γP o • (flagPlaneOrbit o).out = flagPlaneOf o.out

/-- The frames given by the chosen conjugating elements. -/
def ConjFrames.default : ConjFrames where
  γL := lineConj
  hL := lineConj_smul
  γP := planeConj
  hP := planeConj_smul

/-- Classes `G o ∈ H³(Stab o.out; ℚ)` spanning the (one dimensional) cohomology of the flag groups: the output of the evaluation functional of step (ii). -/
structure H3FlagData where
  G : ∀ o : labelOrbits Γ6 Flag, groupCohomology (Rep.res (MulAction.stabilizer Γ6 o.out).subtype Wq) 3
  span : ∀ (o : labelOrbits Γ6 Flag) (y : groupCohomology (Rep.res (MulAction.stabilizer Γ6 o.out).subtype Wq) 3),
    ∃ r : ℚ, y = r • G o

open Classical in
/-- **(B_L)**: the joint restriction of the line stabilizers to the flag groups over each line orbit hits every vector `(x o • G o)` with `x` summing to zero over each line orbit. -/
def LineImageSumZero (D : H3FlagData) (F : ConjFrames) : Prop :=
  ∀ x : labelOrbits Γ6 Flag → ℚ, (∀ a : labelOrbits Γ6 Line, ∑ o ∈ Finset.univ.filter (fun o => flagLineOrbit o = a), x o = 0) →
    ∃ σ : (∀ a : labelOrbits Γ6 Line, groupCohomology (Rep.res (MulAction.stabilizer Γ6 a.out).subtype Wq) 3),
      ∀ o, (lineTransportAt o (F.γL o) (F.hL o)).hom (σ (flagLineOrbit o)) = x o • D.G o

open Classical in
/-- **(B_P)**: the plane analogue. -/
def PlaneImageSumZero (D : H3FlagData) (F : ConjFrames) : Prop :=
  ∀ x : labelOrbits Γ6 Flag → ℚ, (∀ a : labelOrbits Γ6 Plane, ∑ o ∈ Finset.univ.filter (fun o => flagPlaneOrbit o = a), x o = 0) →
    ∃ σ : (∀ a : labelOrbits Γ6 Plane, groupCohomology (Rep.res (MulAction.stabilizer Γ6 a.out).subtype Wq) 3),
      ∀ o, (planeTransportAt o (F.γP o) (F.hP o)).hom (σ (flagPlaneOrbit o)) = x o • D.G o

/-- The coefficient of the corner functional against the class `G o`. -/
def flagLambda (D : H3FlagData) (o : labelOrbits Γ6 Flag) : ℚ := flagPhi o (D.G o)

variable {D : H3FlagData} {F : ConjFrames}

theorem flagLineOrbit_of_mem {o : labelOrbits Γ6 Flag} {F : Flag} (h : F ∈ labelOrbit Γ6 Flag o) :
    (Quotient.mk'' F.val.1 : labelOrbits Γ6 Line) = flagLineOrbit o := by
  obtain ⟨γ, hγ⟩ := h
  have h1 := TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant γ o.out
  have h2 : F.val.1 = γ • flagLineOf o.out := by
    rw [← h1]
    exact congrArg (fun F : Flag => F.val.1) hγ.symm
  change (Quotient.mk'' F.val.1 : labelOrbits Γ6 Line) = Quotient.mk'' (flagLineOf o.out)
  rw [h2]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq

theorem flagPlaneOrbit_of_mem {o : labelOrbits Γ6 Flag} {F : Flag} (h : F ∈ labelOrbit Γ6 Flag o) :
    (Quotient.mk'' F.val.2 : labelOrbits Γ6 Plane) = flagPlaneOrbit o := by
  obtain ⟨γ, hγ⟩ := h
  have h1 := TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant γ o.out
  have h2 : F.val.2 = γ • flagPlaneOf o.out := by
    rw [← h1]
    exact congrArg (fun F : Flag => F.val.2) hγ.symm
  change (Quotient.mk'' F.val.2 : labelOrbits Γ6 Plane) = Quotient.mk'' (flagPlaneOf o.out)
  rw [h2]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq


open Classical in
theorem line_lambda_eq (hL : LineImageSumZero D F) {o o' : labelOrbits Γ6 Flag} (h : flagLineOrbit o = flagLineOrbit o') :
    flagLambda D o = flagLambda D o' := by
  classical
  refine fibre_const flagLineOrbit (flagLambda D) (fun x hx => ?_) h
  obtain ⟨σ, hσ⟩ := hL x hx
  have := line_relation F.γL F.hL σ
  rw [← this]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [hσ o, map_smul, smul_eq_mul]
  rfl

open Classical in
theorem plane_lambda_eq (hP : PlaneImageSumZero D F) {o o' : labelOrbits Γ6 Flag} (h : flagPlaneOrbit o = flagPlaneOrbit o') :
    flagLambda D o = flagLambda D o' := by
  classical
  refine fibre_const flagPlaneOrbit (flagLambda D) (fun x hx => ?_) h
  obtain ⟨σ, hσ⟩ := hP x hx
  have := plane_relation F.γP F.hP σ
  rw [← this]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [hσ o, map_smul, smul_eq_mul]
  rfl

/-- **The coefficient of the corner functional is the same on all flag orbits** (line and plane relations, and connectivity of the orbit graph). -/
theorem lambda_universal (hL : LineImageSumZero D F) (hP : PlaneImageSumZero D F) (o o' : labelOrbits Γ6 Flag) :
    flagLambda D o = flagLambda D o' := by
  classical
  let f : labelOrbits Γ6 Line → ℚ := fun a => if h : ∃ o, flagLineOrbit o = a then flagLambda D h.choose else 0
  let g : labelOrbits Γ6 Plane → ℚ := fun a => if h : ∃ o, flagPlaneOrbit o = a then flagLambda D h.choose else 0
  have hf : ∀ o, f (flagLineOrbit o) = flagLambda D o := fun o => by
    have h : ∃ o', flagLineOrbit o' = flagLineOrbit o := ⟨o, rfl⟩
    simp only [f, dite_eq_left h]
    exact line_lambda_eq hL h.choose_spec
  have hg : ∀ o, g (flagPlaneOrbit o) = flagLambda D o := fun o => by
    have h : ∃ o', flagPlaneOrbit o' = flagPlaneOrbit o := ⟨o, rfl⟩
    simp only [g, dite_eq_left h]
    exact plane_lambda_eq hP h.choose_spec
  have hl : ∀ F : Flag, flagLineOrbit (Quotient.mk'' F : labelOrbits Γ6 Flag) = Quotient.mk'' F.val.1 :=
    fun F => (flagLineOrbit_of_mem ((mem_labelOrbit_iff _ F).2 rfl)).symm
  have hp : ∀ F : Flag, flagPlaneOrbit (Quotient.mk'' F : labelOrbits Γ6 Flag) = Quotient.mk'' F.val.2 :=
    fun F => (flagPlaneOrbit_of_mem ((mem_labelOrbit_iff _ F).2 rfl)).symm
  have key : ∀ F : Flag, f (Quotient.mk'' F.val.1) = g (Quotient.mk'' F.val.2) := by
    intro F
    rw [← hl F, ← hp F, hf, hg]
  have hc := (orbit_invariant_const f g key).1
  rw [← hf o, ← hf o']
  exact hc _ _

/-- The common value of the coefficients of the corner functional against the classes `G o`. -/
def flagLambda0 (D : H3FlagData) : ℚ := flagLambda D (Quotient.mk'' (flagOf 1))

theorem flagLambda_eq_const (hL : LineImageSumZero D F) (hP : PlaneImageSumZero D F) (o : labelOrbits Γ6 Flag) :
    flagLambda D o = flagLambda0 D :=
  lambda_universal hL hP o _

end TernaryPeriodPolynomials.Argument.GammaNStokes
