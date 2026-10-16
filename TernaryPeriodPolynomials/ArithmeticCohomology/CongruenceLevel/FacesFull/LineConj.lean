module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.Flags
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.Rational
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.EdgeSurjective

@[expose] public section


/-!
# Change of conjugator within a line cusp of `Γ(N)`: independence of the representative of a face

Formalized by Claude Sonnet 5.5.
Paper: Appendix C, ("`𝒞_R(E)` is the direct sum over
faces of type `R`"; "we use the same letters for rational conjugates at the other cusps").

This is the line analogue (`R = Q`) of `SeedC3S4c.FaceFrameChange` / `FaceConjugation` / `PlaneFaces`:

* `lineBorel`: the integral stabilizer `Q(ℚ) ∩ SL₃(ℤ)` of the line `ℚ e₁`; `gammaNQAt_mul_left`: `h⁻¹Qh` and `(qh)⁻¹Q(qh)` have the same
  line group; `lineFlagStab_mul_left`: the families of flag stabilizers coincide (the frame is only a parametrization of the cusps of
  the binary Levi), via the lower right block `botRight` of `q`;
* `map_lineFaceCuspidalInH2_frame` (change `h ↦ qh`) and `map_lineFaceCuspidalInH2_conj` (change `h ↦ hγ`);
* `lineFaceCuspidalInH2_orbit`: for `h' = q h γ` the canonical transport carries the classes with cuspidal edge onto those of `h'`.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFacesFull

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

section Borel

/-- The elements of `SL₃(ℤ)` with first column `(±1, 0, 0)ᵗ`: the integral stabilizer `Q(ℚ) ∩ SL₃(ℤ)` of the line `ℚ e₁`. -/
def lineBorel : Subgroup SL(3, ℤ) where
  carrier := {q | (q : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧ (q : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro q q' ⟨h0, h1⟩ ⟨k0, k1⟩
    refine ⟨?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, k0, k1]
  inv_mem' := by
    rintro q ⟨h0, h1⟩
    have hq : ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
    show ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧
      ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0
    generalize ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = Y at hq ⊢
    have e0 := congrFun (congrFun hq 0) 0
    have e1 := congrFun (congrFun hq 1) 0
    have e2 := congrFun (congrFun hq 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1] at e0 e1 e2
    have u : IsUnit ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0) :=
      ⟨⟨_, Y 0 0, by rw [mul_comm]; exact e0, e0⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rcases e1 with h | h
      · exact h
      · exact absurd h u.ne_zero
    · rcases e2 with h | h
      · exact h
      · exact absurd h u.ne_zero

theorem mem_lineBorel_of_mem_lineStab {X : SL(3, ℤ)} (hX : X ∈ lineStab) : X ∈ lineBorel :=
  ⟨hX.2.1, hX.2.2⟩

theorem conj_mem_lineStab {q X : SL(3, ℤ)} (hq : q ∈ lineBorel) (hX : X ∈ lineStab) :
    q * X * q⁻¹ ∈ lineStab := by
  obtain ⟨h0, h1⟩ := hq
  obtain ⟨x0, x1, x2⟩ := hX
  have hY : q⁻¹ ∈ lineBorel := lineBorel.inv_mem ⟨h0, h1⟩
  obtain ⟨y0, y1⟩ := hY
  have hqY : (q : Matrix (Fin 3) (Fin 3) ℤ) * ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  show ((q * X * q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧
    ((q * X * q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧
    ((q * X * q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  generalize ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = Y at hqY y0 y1 ⊢
  have e0 := congrFun (congrFun hqY 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, y0, y1] at e0
  refine ⟨?_, ?_, ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_three, x0, x1, x2, y0, y1]
    linear_combination e0
  · simp [Matrix.mul_apply, Fin.sum_univ_three, h0, x1, x2, y0, y1]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, h1, x1, x2, y0, y1]

theorem conj_mem_gammaNQ (N : ℕ) {q X : SL(3, ℤ)} (hq : q ∈ lineBorel) (hX : X ∈ gammaNQ N) :
    q * X * q⁻¹ ∈ gammaNQ N :=
  ⟨(gammaN_normal N).conj_mem X hX.1 q |> fun h => by simpa using h, conj_mem_lineStab hq hX.2⟩

end Borel

section Frame

/-- The lower right `2 × 2` block of an element of `SL₃(ℤ)`. -/
def botRight (X : SL(3, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(X : Matrix (Fin 3) (Fin 3) ℤ) 1 1, (X : Matrix (Fin 3) (Fin 3) ℤ) 1 2;
    (X : Matrix (Fin 3) (Fin 3) ℤ) 2 1, (X : Matrix (Fin 3) (Fin 3) ℤ) 2 2]

theorem botRight_mul {A B : SL(3, ℤ)} (hA : A ∈ lineBorel) :
    botRight (A * B) = botRight A * botRight B := by
  obtain ⟨a0, a1⟩ := hA
  rw [botRight, botRight, botRight, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a0, a1]

theorem botRight_one : botRight (1 : SL(3, ℤ)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [botRight]

theorem botRight_inv_mul (q : SL(3, ℤ)) (hq : q ∈ lineBorel) :
    botRight q * botRight q⁻¹ = 1 ∧ botRight q⁻¹ * botRight q = 1 := by
  have hq' : q⁻¹ ∈ lineBorel := lineBorel.inv_mem hq
  constructor
  · rw [← botRight_mul hq, mul_inv_cancel, botRight_one]
  · rw [← botRight_mul hq', inv_mul_cancel, botRight_one]

theorem botRight_conj (q X : SL(3, ℤ)) (hq : q ∈ lineBorel) (hX : X ∈ lineBorel) :
    botRight (q * X * q⁻¹) = botRight q * botRight X * botRight q⁻¹ := by
  rw [mul_assoc, botRight_mul hq, botRight_mul hX]
  simp only [mul_assoc]

theorem gammaNQAt_mul_left (N : ℕ) (h q : SL(3, ℤ)) (hq : q ∈ lineBorel) :
    gammaNQAt N (q * h) = gammaNQAt N h := by
  ext p
  rw [mem_gammaNQAt, mem_gammaNQAt]
  have e : q * h * p * (q * h)⁻¹ = q * (h * p * h⁻¹) * q⁻¹ := by group
  rw [e]
  constructor
  · intro hp
    have := conj_mem_gammaNQ N (lineBorel.inv_mem hq) hp
    simpa [mul_assoc] using this
  · intro hp
    exact conj_mem_gammaNQ N hq hp

variable (N : ℕ) [NeZero N]

theorem mem_lineFlagStab_iff (h p : SL(3, ℤ)) (hp : p ∈ gammaNQAt N h) (F : GL (Fin 2) ℚ) :
    (⟨p, hp⟩ : gammaNQAt N h) ∈ lineFlagStab N h F ↔
      (((F⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
        (Int.castRingHom ℚ).mapMatrix (botRight (h * p * h⁻¹)) * (F : Matrix (Fin 2) (Fin 2) ℚ))
          1 0 = 0 := by
  change ((F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (leviBlockQ (h * p * h⁻¹) hp.2) * F :
    GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 ↔ _
  have : ((Matrix.SpecialLinearGroup.mapGL ℚ (leviBlockQ (h * p * h⁻¹) hp.2) : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) = (Int.castRingHom ℚ).mapMatrix (botRight (h * p * h⁻¹)) := by
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Units.val_mul, Units.val_mul, this]

/-- **Change of frame within a line.** For `q ∈ Q(ℚ) ∩ SL₃(ℤ)` the cusps `h⁻¹Qh` and `(qh)⁻¹Q(qh)` are the same line, with the same
line group, and the families of stabilizers of complete flags (one for each frame `F ∈ GL₂(ℚ)`) coincide. -/
theorem lineFlagStab_mul_left (h q : SL(3, ℤ)) (hq : q ∈ lineBorel) (F : GL (Fin 2) ℚ) :
    ∃ F' : GL (Fin 2) ℚ,
      (lineFlagStab N (q * h) F).map (gammaNQAt N (q * h)).subtype =
        (lineFlagStab N h F').map (gammaNQAt N h).subtype := by
  obtain ⟨h1, h2⟩ := botRight_inv_mul q hq
  refine ⟨castGL (botRight q⁻¹) (botRight q) h2 h1 * F, ?_⟩
  ext p
  constructor
  · rintro ⟨⟨p, hp⟩, hmem, rfl⟩
    have hp' : p ∈ gammaNQAt N h := by rwa [← gammaNQAt_mul_left N h q hq]
    have hmem2 := (mem_lineFlagStab_iff N (q * h) p hp F).mp hmem
    refine ⟨⟨p, hp'⟩, (mem_lineFlagStab_iff N h p hp' _).mpr ?_, rfl⟩
    have hX : h * p * h⁻¹ ∈ lineStab := hp'.2
    have e : q * h * p * (q * h)⁻¹ = q * (h * p * h⁻¹) * q⁻¹ := by group
    rw [e, botRight_conj q _ hq (mem_lineBorel_of_mem_lineStab hX)] at hmem2
    rw [← cond_conj F (botRight q) (botRight q⁻¹) _ h1 h2]
    exact hmem2
  · rintro ⟨⟨p, hp⟩, hmem, rfl⟩
    have hp' : p ∈ gammaNQAt N (q * h) := by rwa [gammaNQAt_mul_left N h q hq]
    have hmem2 := (mem_lineFlagStab_iff N h p hp _).mp hmem
    refine ⟨⟨p, hp'⟩, (mem_lineFlagStab_iff N (q * h) p hp' F).mpr ?_, rfl⟩
    have hX : h * p * h⁻¹ ∈ lineStab := hp.2
    have e : q * h * p * (q * h)⁻¹ = q * (h * p * h⁻¹) * q⁻¹ := by group
    rw [e, botRight_conj q _ hq (mem_lineBorel_of_mem_lineStab hX)]
    rw [cond_conj F (botRight q) (botRight q⁻¹) _ h1 h2]
    exact hmem2

end Frame

section FrameChange

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ) (q : SL(3, ℤ)) (hq : q ∈ lineBorel)

/-- The identification `Γ_{(qh)⁻¹Q(qh)} = Γ_{h⁻¹Qh}` of the line groups. -/
def frameHomQ : gammaNQAt N (q * h) →* gammaNQAt N h :=
  Subgroup.inclusion (le_of_eq (gammaNQAt_mul_left N h q hq))

omit [NeZero N] in
theorem frameHomQ_bijective : Function.Bijective (frameHomQ N h q hq) := by
  constructor
  · exact Subgroup.inclusion_injective _
  · intro g
    exact ⟨⟨g.1, by rw [gammaNQAt_mul_left N h q hq]; exact g.2⟩, rfl⟩

omit [NeZero N] in
theorem coe_frameHomQ (g : gammaNQAt N (q * h)) :
    ((frameHomQ N h q hq g : gammaNQAt N h) : SL(3, ℤ)) = (g : SL(3, ℤ)) :=
  Subgroup.coe_inclusion (le_of_eq (gammaNQAt_mul_left N h q hq)) g

omit [NeZero N] in
theorem frameTQ_intertwines (g : gammaNQAt N (q * h)) (v : GeneralEisenstein.HomogeneousPoly n) :
    frameT n ((lineFaceRep N h n).ρ (frameHomQ N h q hq g) v) =
      (lineFaceRep N (q * h) n).ρ g (frameT n v) := by
  change ambRep n ((frameHomQ N h q hq g : gammaNQAt N h) : SL(3, ℤ)) v = ambRep n (g : SL(3, ℤ)) v
  rw [coe_frameHomQ]

theorem frameHomQ_mem_flag (F F' : GL (Fin 2) ℚ)
    (hF : (lineFlagStab N (q * h) F).map (gammaNQAt N (q * h)).subtype =
      (lineFlagStab N h F').map (gammaNQAt N h).subtype) (s : lineFlagStab N (q * h) F) :
    frameHomQ N h q hq s.1 ∈ lineFlagStab N h F' := by
  have h1 : (s.1 : SL(3, ℤ)) ∈ (lineFlagStab N (q * h) F).map (gammaNQAt N (q * h)).subtype :=
    ⟨s.1, s.2, rfl⟩
  rw [hF] at h1
  obtain ⟨t, ht, hts⟩ := h1
  have : t = frameHomQ N h q hq s.1 := Subtype.ext (hts.trans (coe_frameHomQ N h q hq s.1).symm)
  rw [← this]; exact ht

/-- The identification of the two flag stabilizers. -/
def frameKappaQ (F F' : GL (Fin 2) ℚ)
    (hF : (lineFlagStab N (q * h) F).map (gammaNQAt N (q * h)).subtype =
      (lineFlagStab N h F').map (gammaNQAt N h).subtype) :
    lineFlagStab N (q * h) F →* lineFlagStab N h F' :=
  ((frameHomQ N h q hq).comp (lineFlagStab N (q * h) F).subtype).codRestrict _
    (frameHomQ_mem_flag N h q hq F F' hF)

theorem frameKappaQ_coe (F F' : GL (Fin 2) ℚ)
    (hF : (lineFlagStab N (q * h) F).map (gammaNQAt N (q * h)).subtype =
      (lineFlagStab N h F').map (gammaNQAt N h).subtype) (k : lineFlagStab N (q * h) F) :
    (((frameKappaQ N h q hq F F' hF k : lineFlagStab N h F') : gammaNQAt N h) : SL(3, ℤ)) =
      ((k : gammaNQAt N (q * h)) : SL(3, ℤ)) :=
  coe_frameHomQ N h q hq k.1

theorem frameKappaQ_bijective (F F' : GL (Fin 2) ℚ)
    (hF : (lineFlagStab N (q * h) F).map (gammaNQAt N (q * h)).subtype =
      (lineFlagStab N h F').map (gammaNQAt N h).subtype) :
    Function.Bijective (frameKappaQ N h q hq F F' hF) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun x : lineFlagStab N h F' => ((x : gammaNQAt N h) : SL(3, ℤ))) hab
    simp only [frameKappaQ_coe] at this
    exact this
  · intro t
    have h1 : ((t.1 : gammaNQAt N h) : SL(3, ℤ)) ∈
        (lineFlagStab N h F').map (gammaNQAt N h).subtype := ⟨t.1, t.2, rfl⟩
    rw [← hF] at h1
    obtain ⟨s, hs, hst⟩ := h1
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [frameKappaQ_coe]
    exact hst

theorem frameQ_flag_iff (F F' : GL (Fin 2) ℚ)
    (hF : (lineFlagStab N (q * h) F).map (gammaNQAt N (q * h)).subtype =
      (lineFlagStab N h F').map (gammaNQAt N h).subtype)
    (y : groupCohomology.H2 (lineFaceRep N h n)) :
    twoCohomologyRestriction (lineFlagStab N (q * h) F).subtype (lineFaceRep N (q * h) n)
        (EdgeNat.h2Map (frameHomQ N h q hq) (lineFaceRep N h n) (lineFaceRep N (q * h) n)
          (frameT n) (frameTQ_intertwines N h n q hq) y) = 0 ↔
      twoCohomologyRestriction (lineFlagStab N h F').subtype (lineFaceRep N h n) y = 0 :=
  EdgeNat.restriction_h2Map_eq_zero_iff (frameHomQ N h q hq) (lineFaceRep N h n)
    (lineFaceRep N (q * h) n) (frameT n) (frameTQ_intertwines N h n q hq)
    (lineFlagStab N h F').subtype (lineFlagStab N (q * h) F).subtype
    (frameKappaQ N h q hq F F' hF) (fun _ => rfl) (frameKappaQ_bijective N h q hq F F' hF)
    Function.bijective_id y

include hq in
theorem lineFlagStab_mul_left_symm (F' : GL (Fin 2) ℚ) :
    ∃ F : GL (Fin 2) ℚ, (lineFlagStab N (q * h) F).map (gammaNQAt N (q * h)).subtype =
      (lineFlagStab N h F').map (gammaNQAt N h).subtype := by
  obtain ⟨F, hF⟩ := lineFlagStab_mul_left N (q * h) q⁻¹ (lineBorel.inv_mem hq) F'
  rw [inv_mul_cancel_left] at hF
  exact ⟨F, hF.symm⟩

/-- **Change of the integral conjugator within the line.** For `q ∈ Q(ℚ) ∩ SL₃(ℤ)` the transport
`H²(Γ_{h⁻¹Qh}, E_n) → H²(Γ_{(qh)⁻¹Q(qh)}, E_n)` along the identification of the (equal) line groups maps the classes with edge in the
mixed cuspidal group of the frame `h` onto those of the frame `qh`. -/
theorem map_lineFaceCuspidalInH2_frame :
    Submodule.map (EdgeNat.h2Map (frameHomQ N h q hq) (lineFaceRep N h n) (lineFaceRep N (q * h) n)
        (frameT n) (frameTQ_intertwines N h n q hq)) (lineFaceCuspidalInH2 N h n) =
      lineFaceCuspidalInH2 N (q * h) n := by
  rw [lineFaceCuspidalInH2_eq_locallyInner, lineFaceCuspidalInH2_eq_locallyInner,
    lineLocallyInner_eq_iInf, lineLocallyInner_eq_iInf]
  have hbij := EdgeNat.h2Map_surjective (frameHomQ N h q hq) (lineFaceRep N h n) (lineFaceRep N (q * h) n)
    (frameT n) (frameTQ_intertwines N h n q hq) (frameHomQ_bijective N h q hq) Function.bijective_id
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine (Submodule.mem_iInf _).mpr fun F => ?_
    obtain ⟨F', hF⟩ := lineFlagStab_mul_left N h q hq F
    exact (frameQ_flag_iff N h n q hq F F' hF y).mpr (LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hy F'))
  · intro hz
    obtain ⟨y, rfl⟩ := hbij z
    refine ⟨y, (Submodule.mem_iInf _).mpr fun F' => ?_, rfl⟩
    obtain ⟨F, hF⟩ := lineFlagStab_mul_left_symm N h q hq F'
    exact (frameQ_flag_iff N h n q hq F F' hF y).mp (LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hz F))

end FrameChange

section Conj

variable (N : ℕ) (h γ : SL(3, ℤ))

/-- Conjugation by `γ`: `Γ_{(hγ)⁻¹Q(hγ)} → Γ_{h⁻¹Qh}`, `p ↦ γ p γ⁻¹`. -/
def conjGammaHomQ : gammaNQAt N (h * γ) →* gammaNQAt N h where
  toFun p := ⟨γ * p.1 * γ⁻¹, by
    have hp := p.2
    rw [mem_gammaNQAt] at hp ⊢
    have e : h * (γ * p.1 * γ⁻¹) * h⁻¹ = h * γ * p.1 * (h * γ)⁻¹ := by group
    rw [e]; exact hp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

theorem conjGammaHomQ_apply (p : gammaNQAt N (h * γ)) :
    ((conjGammaHomQ N h γ p : gammaNQAt N h) : SL(3, ℤ)) = γ * p.1 * γ⁻¹ := rfl

theorem conjGammaHomQ_bijective : Function.Bijective (conjGammaHomQ N h γ) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have h1 : γ * a.1 * γ⁻¹ = γ * b.1 * γ⁻¹ := by
      have := congrArg (fun x : gammaNQAt N h => (x : SL(3, ℤ))) hab
      simpa only [conjGammaHomQ_apply] using this
    exact mul_left_cancel (mul_right_cancel h1)
  · intro b
    have hb : h * b.1 * h⁻¹ ∈ gammaNQ N := b.2
    have hmem : γ⁻¹ * b.1 * γ ∈ gammaNQAt N (h * γ) := by
      show h * γ * (γ⁻¹ * b.1 * γ) * (h * γ)⁻¹ ∈ gammaNQ N
      have e : h * γ * (γ⁻¹ * b.1 * γ) * (h * γ)⁻¹ = h * b.1 * h⁻¹ := by group
      rw [e]; exact hb
    refine ⟨⟨γ⁻¹ * b.1 * γ, hmem⟩, ?_⟩
    apply Subtype.ext
    show γ * (γ⁻¹ * b.1 * γ) * γ⁻¹ = b.1
    group

end Conj

section ConjFace

variable (N : ℕ) [NeZero N] (h γ : SL(3, ℤ)) (n : ℕ)

omit [NeZero N] in
theorem faceConjTQ_intertwines (g : gammaNQAt N (h * γ)) (v : GeneralEisenstein.HomogeneousPoly n) :
    faceConjT γ n ((lineFaceRep N h n).ρ (conjGammaHomQ N h γ g) v) =
      (lineFaceRep N (h * γ) n).ρ g (faceConjT γ n v) := by
  change ambRep n γ⁻¹ (ambRep n (γ * g.1 * γ⁻¹) v) = ambRep n g.1 (ambRep n γ⁻¹ v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

theorem conjGammaHomQ_inl (r : RadicalLattice) :
    conjGammaHomQ N h γ ((lineFaceExt N (h * γ)).inl r) =
      (lineFaceExt N h).inl ((MonoidHom.id RadicalLattice) r) := by
  apply Subtype.ext
  show γ * ((h * γ)⁻¹ * (gammaNQInl N r).1 * (h * γ)) * γ⁻¹ = h⁻¹ * (gammaNQInl N r).1 * h
  group

theorem conjGammaHomQ_split (m : CongruenceSubgroup.Gamma N) :
    conjGammaHomQ N h γ ((lineFaceSplitting N (h * γ)).toMonoidHom m) =
      (lineFaceSplitting N h).toMonoidHom ((MonoidHom.id _) m) := by
  apply Subtype.ext
  show γ * ((h * γ)⁻¹ * (gammaNQSect N m).1 * (h * γ)) * γ⁻¹ = h⁻¹ * (gammaNQSect N m).1 * h
  group

/-- **Change of the integral conjugator by `γ ∈ SL₃(ℤ)`** (in particular the choice of a representative in a `Γ(N)`-orbit of lines):
the pullback by conjugation `H²(Γ_{h⁻¹Qh}, E_n) → H²(Γ_{(hγ)⁻¹Q(hγ)}, E_n)` is an isomorphism carrying the group of classes with
edge in the mixed cuspidal group of the cusp `h⁻¹Qh` onto that of `(hγ)⁻¹Q(hγ)`. -/
theorem map_lineFaceCuspidalInH2_conj :
    Submodule.map (EdgeNat.h2Map (conjGammaHomQ N h γ) (lineFaceRep N h n) (lineFaceRep N (h * γ) n)
        (faceConjT γ n) (faceConjTQ_intertwines N h γ n)) (lineFaceCuspidalInH2 N h n) =
      lineFaceCuspidalInH2 N (h * γ) n := by
  have hα := conjGammaHomQ_bijective N h γ
  have hTb := faceConjT_bijective γ n
  have hτ : Function.Bijective (MonoidHom.id RadicalLattice) := Function.bijective_id
  have hinl := conjGammaHomQ_inl N h γ
  have hsplit := conjGammaHomQ_split N h γ
  have hbij := EdgeNat.radH1Map_bijective (conjGammaHomQ N h γ) (lineFaceRep N h n)
    (lineFaceRep N (h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N h γ n)
    (MonoidHom.id RadicalLattice) hinl hτ hTb
  have hcusp : ∀ x : groupCohomology.H1 (lineFaceRadH1 N h n), x ∈ lineFaceCuspidal N h n ↔
      (groupCohomology.map (MonoidHom.id (CongruenceSubgroup.Gamma N))
        (EdgeNat.modMor (lineFaceSplitting N h) (lineFaceSplitting N (h * γ)) (conjGammaHomQ N h γ)
          (MonoidHom.id _) (MonoidHom.id RadicalLattice) hinl hsplit (lineFaceRep N h n)
          (lineFaceRep N (h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N h γ n)) 1).hom x ∈
        lineFaceCuspidal N (h * γ) n := fun x =>
    EdgeNat.mem_cuspidalFamily_map_id_iff (leviCuspStab (CongruenceSubgroup.Gamma N)) _ hbij x
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨EdgeNat.kerMap (conjGammaHomQ N h γ) (MonoidHom.id RadicalLattice) hinl (lineFaceRep N h n)
      (lineFaceRep N (h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N h γ n) x, ?_, rfl⟩
    show lineFaceEdge N (h * γ) n _ ∈ lineFaceCuspidal N (h * γ) n
    rw [EdgeNat.edge_kerMap (lineFaceSplitting N h) (lineFaceSplitting N (h * γ)) (conjGammaHomQ N h γ)
      (MonoidHom.id _) (MonoidHom.id RadicalLattice) hinl hsplit (lineFaceRep N h n)
      (lineFaceRep N (h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N h γ n) x]
    exact (hcusp _).mp hx
  · rintro ⟨x₂, hx₂, rfl⟩
    obtain ⟨x₁, rfl⟩ := EdgeNat.kerMap_surjective (conjGammaHomQ N h γ) (MonoidHom.id RadicalLattice)
      hinl (lineFaceRep N h n) (lineFaceRep N (h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N h γ n) hα
      hTb hτ x₂
    refine ⟨x₁.val, ⟨x₁, ?_, rfl⟩, rfl⟩
    have h2 : lineFaceEdge N (h * γ) n
        (EdgeNat.kerMap (conjGammaHomQ N h γ) (MonoidHom.id RadicalLattice) hinl (lineFaceRep N h n)
          (lineFaceRep N (h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N h γ n) x₁) ∈
        lineFaceCuspidal N (h * γ) n := hx₂
    rw [EdgeNat.edge_kerMap (lineFaceSplitting N h) (lineFaceSplitting N (h * γ)) (conjGammaHomQ N h γ)
      (MonoidHom.id _) (MonoidHom.id RadicalLattice) hinl hsplit (lineFaceRep N h n)
      (lineFaceRep N (h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N h γ n) x₁] at h2
    exact (hcusp _).mpr h2

end ConjFace

section Orbit

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **Independence of the conjugator within a face of type `Q`.** If `h' = q h γ` with `q ∈ Q(ℚ) ∩ SL₃(ℤ)` and `γ ∈ SL₃(ℤ)` (in
particular for two representatives of the same `Γ(N)`-orbit of lines), the canonical isomorphism
`H²(Γ_{h⁻¹Qh}, E_n) → H²(Γ_{(qh)⁻¹Q(qh)}, E_n) → H²(Γ_{h'⁻¹Qh'}, E_n)` maps the classes with edge in the mixed cuspidal group of
`h⁻¹Qh` onto those of `h'⁻¹Qh'`. -/
theorem lineFaceCuspidalInH2_orbit (h q γ : SL(3, ℤ)) (hq : q ∈ lineBorel) :
    Submodule.map (EdgeNat.h2Map (conjGammaHomQ N (q * h) γ) (lineFaceRep N (q * h) n)
        (lineFaceRep N (q * h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N (q * h) γ n))
      (Submodule.map (EdgeNat.h2Map (frameHomQ N h q hq) (lineFaceRep N h n) (lineFaceRep N (q * h) n)
        (frameT n) (frameTQ_intertwines N h n q hq)) (lineFaceCuspidalInH2 N h n)) =
      lineFaceCuspidalInH2 N (q * h * γ) n := by
  rw [map_lineFaceCuspidalInH2_frame, map_lineFaceCuspidalInH2_conj]

end Orbit

end TernaryPeriodPolynomials.Argument.GammaNFacesFull
