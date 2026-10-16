module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Cover

@[expose] public section


/-!
# (C), step 7: the integrand of `eq:intertwiner` for the induced section

Formalized by Claude Sonnet 5.5.

`adelicSectionG` is the adelic induced section on `GL₃(𝔸)`; `printedIntegrand g u` is the `(x; e_p, e_q)`-coordinate, `m`-th
monomial coefficient, of the pullback to the standard line face along `jFace` of `φ(w₀⁻¹ u(s,t) g)`, `u = (s,t) ∈ 𝔸²`.
* `printedIntegrand_one`: at `g = 1` it is `Fz` of the regrouped coordinates `((s_f,t_f), (s_∞,t_∞))`.
* `Fz_eq_zero_of_not`: it vanishes where `w₀⁻¹ u(σ) ∉ P(ℚ) K(N)`.
* `Fz_on_piece`: on the cell of the free orbit `o` it is `PhiQ0(coset of o)(shiftV r_o w)`, the summand of `lineA1K`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The real component of an adelic matrix. -/
def realMatOf (g : AdelicGL) : Matrix (Fin 3) (Fin 3) ℝ := ((realGroup g : GL3 ℝ) : Matrix (Fin 3) (Fin 3) ℝ)

/-- **The adelic induced section on `GL₃(𝔸)`.** -/
def adelicSectionG (h : ℂ → ℂ) (g : AdelicGL) (y : Fin 5 → ℝ) (a b : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  adelicSection N n h (realMatOf g) (finiteGroup g) y a b

/-- **The integrand of the printed intertwiner**, in the coordinates `(x; e_p, e_q)`, coefficient `m`, of
the pullback to the standard line face: the pullback of `φ(w₀⁻¹ u(s,t) g)`. -/
def printedIntegrand (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (g : AdelicGL) (u : Adeles × Adeles) : ℂ :=
  (fPull jFace (fun y a b => adelicSectionG N n (hfun f) (weyl⁻¹ * lineUnipotent u.1 u.2 * g) y a b) x p q).coeff m

/-- The integrand in the regrouped coordinates `((s_f, t_f), (s_∞, t_∞))`. -/
def Fz (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (z : (FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ)) : ℂ :=
  (fPull jFace (fun y a b => adelicSection N n (hfun f) (gReal z.2) (gFin z.1) y a b) x p q).coeff m

omit [NeZero N] in
theorem realMatOf_unip (u : Adeles × Adeles) :
    realMatOf (weyl⁻¹ * lineUnipotent u.1 u.2 * 1) = gReal ![u.1.1, u.2.1] := by
  unfold realMatOf gReal realGroup
  rw [mul_one, map_mul, map_inv]
  have h1 : GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (weyl : GL3 Adeles) = weyl := map_weyl _
  have h2 : GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (lineUnipotent u.1 u.2) = upperUnipotent u.1.1 u.2.1 :=
    map_upperUnipotent _ _ _
  rw [h1, h2]
  rfl

omit [NeZero N] in
theorem finiteGroup_unip (u : Adeles × Adeles) :
    finiteGroup (weyl⁻¹ * lineUnipotent u.1 u.2 * 1) = gFin (u.1.2, u.2.2) := by
  unfold finiteGroup gFin
  rw [mul_one, map_mul, map_inv]
  have h1 : GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (weyl : GL3 Adeles) = weyl := map_weyl _
  have h2 : GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (lineUnipotent u.1 u.2) = upperUnipotent u.1.2 u.2.2 :=
    map_upperUnipotent _ _ _
  rw [h1, h2]

theorem printedIntegrand_one (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (u : Adeles × Adeles) :
    printedIntegrand N n f x p q m 1 u = Fz N n f x p q m (radicalEquiv u) := by
  unfold printedIntegrand Fz adelicSectionG
  rw [realMatOf_unip, finiteGroup_unip]
  rfl

theorem Fz_eq_zero_of_not (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (σ : FiniteAdeles × FiniteAdeles)
    (w : Fin 2 → ℝ) (hd : ¬∃ π κ, IsDecomp N (gFin σ) π κ) : Fz N n f x p q m (σ, w) = 0 := by
  unfold Fz fPull
  simp [adelicSection_of_not N n _ (gReal w) hd]

/-- **On the cell of the free orbit `o` the integrand is the summand `PhiQ0` of `lineA1K`**, evaluated at the real shift
`shiftV r_o w` (the real coordinate `w` of the integration against `w₀⁻¹ u(σ, w)`). -/
theorem Fz_on_piece (hN : 3 ≤ N) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrb N)
    {σ : FiniteAdeles × FiniteAdeles} (hσ : σ ∈ pieceFin N o) (w : Fin 2 → ℝ) :
    Fz N n f x p q m (σ, w) = PhiQ0 N 1 n f x p q m (orbCoset N o) (shiftV (orbPt N o) w) := by
  set c := orbCoset N o with hc
  set b : SL(3, ℤ) := (Quotient.out c).1 with hb
  have hr : orbPt N o = slRowPt b := ptC_out N c
  have hbN : b ∈ gammaN N := (Quotient.out c).2
  have hb0 : (b : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0 := (cuspRow_ne_zero_iff N c).1 (orbCoset_r0 N o)
  set a : FiniteAdeles × FiniteAdeles :=
    (algebraMap ℚ FiniteAdeles (slRowPt b).1, algebraMap ℚ FiniteAdeles (slRowPt b).2) with ha
  have h1 : σ.1 - a.1 ∈ latSet N := by
    have := (mem_latCoset N).1 hσ.1
    rwa [hr] at this
  have h2 : σ.2 - a.2 ∈ latSet N := by
    have := (mem_latCoset N).1 hσ.2
    rwa [hr] at this
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  have hσe : σ = a + (σ - a) := by abel
  unfold Fz PhiQ0
  refine congrArg (fun F => F.coeff m) (fPull_congr_at jFace _ _ x (fun a' b' => ?_) p q)
  have e1 := adelicSection_gFin_add_lat N hN n f w a (σ - a) h1 h2 hy a' b'
  rw [← hσe] at e1
  simp only
  rw [e1, adelicSection_gFin_rational N hN n f hbN hb0 w hy a' b', realMat_one, Matrix.one_mul, hr]

end TernaryPeriodPolynomials.Argument.FormClassK
