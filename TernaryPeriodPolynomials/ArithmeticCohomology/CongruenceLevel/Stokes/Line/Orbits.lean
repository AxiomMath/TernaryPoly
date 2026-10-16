module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FaceOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitPairing

@[expose] public section


/-!
# The `Γ(6)`-orbits of rational lines are the faces of type `Q` of `Γ(6)`

Formalized by Claude Sonnet 5.5.

The line `ℓ_h = h⁻¹ ℚ e₁` of an integral change of basis `h ∈ SL₃(ℤ)` is a point of the label set `Line` of the model of `Γ(6)`.  The map `h ↦ ℓ_h` identifies the faces
`LineFaces 6` (`h ~ q h γ`, `q ∈ lineBorel`, `γ ∈ Γ(6)`) with the `Γ(6)`-orbits of rational lines (`lineFacesEquivOrbits`), and the stabilizer of `ℓ_h` is the line group
`gammaNQAt 6 h` (`mem_stabilizer_lineOf_iff`).
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPoly.IntegralGL3Congruence
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.OrdinaryFullAction (lineAction subspaceAction vectorAction)

section Lines

/-- The first basis vector of rational three-space. -/
def e0 : Fin 3 → ℚ := Pi.single 0 1

theorem e0_ne_zero : e0 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [e0] at this

/-- The standard line `ℚ e₁`. -/
def stdLine : Line :=
  ⟨Submodule.span ℚ {e0}, by rw [finrank_span_singleton e0_ne_zero], trivial⟩

theorem lineAction_val (g : GL (Fin 3) ℚ) (ℓ : Line) :
    (lineAction g ℓ).val = ℓ.val.map (vectorAction g).toLinearMap := rfl

theorem lineAction_mul (g h : GL (Fin 3) ℚ) (ℓ : Line) :
    lineAction (g * h) ℓ = lineAction g (lineAction h ℓ) :=
  Subtype.ext (TernaryPoly.OrdinaryFullAction.subspaceAction_mul g h ℓ.val)

theorem lineAction_one (ℓ : Line) : lineAction 1 ℓ = ℓ :=
  Subtype.ext (TernaryPoly.OrdinaryFullAction.subspaceAction_one ℓ.val)

theorem vectorAction_apply (g : GL (Fin 3) ℚ) (v : Fin 3 → ℚ) :
    vectorAction g v = (g : Matrix (Fin 3) (Fin 3) ℚ).mulVec v := by
  change (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv v = _
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, Matrix.GeneralLinearGroup.toLin_apply]
  rfl


/-- The line `h⁻¹ ℚ e₁` of an integral change of basis. -/
def lineOf (h : SL(3, ℤ)) : Line := lineAction (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) stdLine

theorem mulVec_e0 (q : SL(3, ℤ)) (i : Fin 3) :
    ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 i =
      ((q : Matrix (Fin 3) (Fin 3) ℤ) i 0 : ℚ) := by
  simp [e0, Matrix.mulVec, dotProduct, Matrix.SpecialLinearGroup.mapGL, Pi.single_apply]

theorem lineAction_mapGL_stdLine_val (q : SL(3, ℤ)) :
    (lineAction (Matrix.SpecialLinearGroup.mapGL ℚ q) stdLine).val =
      Submodule.span ℚ {((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0} := by
  rw [lineAction_val, stdLine, Submodule.map_span, Set.image_singleton]
  have hv : (vectorAction (Matrix.SpecialLinearGroup.mapGL ℚ q)).toLinearMap e0 =
      ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 :=
    vectorAction_apply _ _
  rw [hv]

/-- The stabilizer of the standard line in `SL₃(ℤ)` is `lineBorel` (first column `(*, 0, 0)ᵗ`). -/
theorem lineAction_stdLine_eq_iff (q : SL(3, ℤ)) :
    lineAction (Matrix.SpecialLinearGroup.mapGL ℚ q) stdLine = stdLine ↔ q ∈ lineBorel := by
  have hval : (lineAction (Matrix.SpecialLinearGroup.mapGL ℚ q) stdLine).val =
      Submodule.span ℚ {((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0} := by
    rw [lineAction_val, stdLine, Submodule.map_span, Set.image_singleton]
    have hv : (vectorAction (Matrix.SpecialLinearGroup.mapGL ℚ q)).toLinearMap e0 =
        ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 :=
      vectorAction_apply _ _
    rw [hv]
  have hne : ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 ≠ 0 := by
    intro h0
    have hinj := (Matrix.mulVec_injective_iff_isUnit (A := ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) :
      Matrix (Fin 3) (Fin 3) ℚ))).2 (Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ).isUnit
    exact e0_ne_zero (hinj (h0.trans (Matrix.mulVec_zero _).symm))
  constructor
  · intro h
    have h1 : ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 ∈
        Submodule.span ℚ {e0} := by
      have : ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 ∈
          (lineAction (Matrix.SpecialLinearGroup.mapGL ℚ q) stdLine).val := by
        rw [hval]; exact Submodule.mem_span_singleton_self _
      rw [h] at this
      exact this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    refine ⟨?_, ?_⟩
    · have := congrFun hc 1
      rw [mulVec_e0] at this
      simp [e0] at this
      exact_mod_cast this.symm
    · have := congrFun hc 2
      rw [mulVec_e0] at this
      simp [e0] at this
      exact_mod_cast this.symm
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    rw [hval]
    have hmem : ((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 ∈
        Submodule.span ℚ {e0} := by
      refine Submodule.mem_span_singleton.2 ⟨((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ), ?_⟩
      funext i
      rw [mulVec_e0]
      fin_cases i
      · simp [e0]
      · simp [e0, h1]
      · simp [e0, h2]
    have hle : Submodule.span ℚ {((Matrix.SpecialLinearGroup.mapGL ℚ q : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0} ≤
        Submodule.span ℚ {e0} := (Submodule.span_singleton_le_iff_mem _ _).2 hmem
    exact Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_span_singleton hne]
      exact stdLine.2.1.symm)


theorem lineOf_eq_iff (h h' : SL(3, ℤ)) : lineOf h = lineOf h' ↔ h' * h⁻¹ ∈ lineBorel := by
  rw [← lineAction_stdLine_eq_iff]
  have e1 : lineAction (Matrix.SpecialLinearGroup.mapGL ℚ (h' * h⁻¹)) stdLine =
      lineAction (Matrix.SpecialLinearGroup.mapGL ℚ h') (lineOf h) := by
    rw [lineOf, ← lineAction_mul, ← map_mul]
  have e2 : lineAction (Matrix.SpecialLinearGroup.mapGL ℚ h') (lineOf h') = stdLine := by
    rw [lineOf, ← lineAction_mul, ← map_mul, mul_inv_cancel, map_one, lineAction_one]
  rw [e1]
  constructor
  · intro heq
    rw [heq, e2]
  · intro heq
    apply (lineAction (Matrix.SpecialLinearGroup.mapGL ℚ h')).injective
    rw [heq, e2]

/-- The action of `γ ∈ Γ(6)` on the lines `ℓ_h`. -/
theorem smul_lineOf (p : gammaN 6) (h : SL(3, ℤ)) :
    gammaSixEquiv p • lineOf h = lineOf (h * p.1⁻¹) := by
  have key : gammaSixEquiv p • lineOf h =
      lineAction (Matrix.SpecialLinearGroup.mapGL ℚ p.1) (lineOf h) := by
    change lineAction (TernaryPoly.OrdinaryFullAction.integral (gammaSixEquiv p).val) (lineOf h) = _
    have : TernaryPoly.OrdinaryFullAction.integral (gammaSixEquiv p).val =
        Matrix.SpecialLinearGroup.mapGL ℚ p.1 := iotaQ_gammaSix p
    rw [this]
  rw [key, lineOf, lineOf, ← lineAction_mul, ← map_mul]
  congr 3
  group

theorem exists_primitive_row (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    ∃ r : Fin 3 → ℤ, Int.gcd (Int.gcd (r 0) (r 1)) (r 2) = 1 ∧ ∃ c : ℚ, c ≠ 0 ∧ ∀ i, (r i : ℚ) = c * v i := by
  classical
  set D : ℕ := ∏ i, (v i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => Rat.den_pos _
  set r' : Fin 3 → ℤ := fun i => (v i).num * (((D / (v i).den : ℕ)) : ℤ) with hr'
  have hr'cast : ∀ i, (r' i : ℚ) = (D : ℚ) * v i := by
    intro i
    have hdvd : (v i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have h1 : ((D / (v i).den : ℕ) : ℚ) * ((v i).den : ℚ) = (D : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have h2 : (v i).num = v i * ((v i).den : ℚ) := by
      exact (Rat.mul_den_eq_num (v i)).symm
    simp only [hr', Int.cast_mul, Int.cast_natCast]
    rw [h2]
    rw [← h1]; ring
  have hne : (Finset.univ : Finset (Fin 3)).Nonempty := Finset.univ_nonempty
  obtain ⟨r, hr, hgcd⟩ := Finset.extract_gcd r' hne
  set G : ℤ := Finset.univ.gcd r' with hG
  obtain ⟨j0, hj0⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    exact hv (funext fun i => by_contra fun hi => hcon ⟨i, hi⟩)
  have hr'0 : r' j0 ≠ 0 := by
    intro h0
    have := hr'cast j0
    rw [h0] at this
    simp only [Int.cast_zero] at this
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    exact hj0 ((mul_eq_zero.1 this.symm).resolve_left hDq)
  have hG0 : G ≠ 0 := by
    intro h0
    have := hr j0 (Finset.mem_univ _)
    rw [h0, zero_mul] at this
    exact hr'0 this
  have hprim : Int.gcd (Int.gcd (r 0) (r 1)) (r 2) = 1 := by
    set k : ℕ := Int.gcd (Int.gcd (r 0) (r 1)) (r 2) with hk
    have hk0 : (k : ℤ) ∣ r 0 := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
    have hk1 : (k : ℤ) ∣ r 1 := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
    have hk2 : (k : ℤ) ∣ r 2 := Int.gcd_dvd_right _ _
    have hdvd : (k : ℤ) ∣ Finset.univ.gcd r := by
      refine Finset.dvd_gcd fun b _ => ?_
      fin_cases b <;> assumption
    rw [hgcd] at hdvd
    have h1 : (k : ℤ) ∣ 1 := by simpa using hdvd
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1
  refine ⟨r, hprim, (D : ℚ) / G, ?_, fun i => ?_⟩
  · have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have hGq : (G : ℚ) ≠ 0 := by exact_mod_cast hG0
    exact div_ne_zero hDq hGq
  · have hGq : (G : ℚ) ≠ 0 := by exact_mod_cast hG0
    have h1 : ((r' i : ℤ) : ℚ) = (G : ℚ) * (r i : ℚ) := by
      have := congrArg (Int.cast : ℤ → ℚ) (hr i (Finset.mem_univ _))
      simpa using this
    rw [hr'cast i] at h1
    field_simp
    linear_combination -h1


theorem gcd_rev_of_gcd (r : Fin 3 → ℤ) (h : Int.gcd (Int.gcd (r 0) (r 1)) (r 2) = 1) :
    Int.gcd (Int.gcd (r 2) (r 1)) (r 0) = 1 := by
  set k : ℕ := Int.gcd (Int.gcd (r 2) (r 1)) (r 0) with hk
  have hk2 : (k : ℤ) ∣ r 2 := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have hk1 : (k : ℤ) ∣ r 1 := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have hk0 : (k : ℤ) ∣ r 0 := Int.gcd_dvd_right _ _
  have hdvd : (k : ℤ) ∣ ((Int.gcd (Int.gcd (r 0) (r 1)) (r 2) : ℕ) : ℤ) :=
    Int.dvd_coe_gcd (Int.dvd_coe_gcd hk0 hk1) hk2
  rw [h] at hdvd
  have h1 : (k : ℤ) ∣ 1 := by simpa using hdvd
  exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1

/-- Every rational line is `ℓ_h` for an integral change of basis `h ∈ SL₃(ℤ)`. -/
theorem exists_lineOf (ℓ : Line) : ∃ h : SL(3, ℤ), lineOf h = ℓ := by
  have hpos : 0 < Module.finrank ℚ ℓ.val := by rw [ℓ.2.1]; exact Nat.one_pos
  obtain ⟨v, hvℓ, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.1 hpos)
  have hspan : ℓ.val = Submodule.span ℚ {v} := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 hvℓ
    · rw [finrank_span_singleton hv0, ℓ.2.1]
  obtain ⟨r, hprim, c, hc, hrc⟩ := exists_primitive_row v hv0
  obtain ⟨H, h0, h1, h2⟩ := exists_SL3_bottom_row (r 2) (r 1) (r 0) (gcd_rev_of_gcd r hprim)
  refine ⟨(rtSL H)⁻¹, Subtype.ext ?_⟩
  rw [lineOf, inv_inv]
  change (lineAction (Matrix.SpecialLinearGroup.mapGL ℚ (rtSL H)) stdLine).val = ℓ.val
  rw [lineAction_mapGL_stdLine_val, hspan]
  have hcol : ((Matrix.SpecialLinearGroup.mapGL ℚ (rtSL H) : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec e0 =
      c • v := by
    funext i
    rw [mulVec_e0]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hrc i]
    fin_cases i
    · simp [coe_rtSL, rt, Fin.rev, h2]
    · simp [coe_rtSL, rt, Fin.rev, h1]
    · simp [coe_rtSL, rt, Fin.rev, h0]
  rw [hcol]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) v


theorem lineOf_rel {h h' : SL(3, ℤ)} (hr : (lineFaceSetoid 6).r h h') :
    (Quotient.mk'' (lineOf h') : labelOrbits Γ6 Line) = Quotient.mk'' (lineOf h) := by
  obtain ⟨q, hq, γ, hγ, rfl⟩ := hr
  have h1 : lineOf (q * h * γ) = lineOf (h * γ) := by
    symm
    rw [lineOf_eq_iff]
    simpa [mul_assoc] using hq
  have h2 : lineOf (h * γ) = gammaSixEquiv ⟨γ⁻¹, (gammaN 6).inv_mem hγ⟩ • lineOf h := by
    rw [smul_lineOf]
    simp
  rw [h1, h2]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq

/-- The map from the faces of type `Q` of `Γ(6)` to the `Γ(6)`-orbits of rational lines. -/
def lineFaceToOrbit : LineFaces 6 → labelOrbits Γ6 Line :=
  Quotient.lift (fun h => (Quotient.mk'' (lineOf h) : labelOrbits Γ6 Line)) (fun _ _ hr => (lineOf_rel hr).symm)

theorem lineFaceToOrbit_mk (h : SL(3, ℤ)) :
    lineFaceToOrbit (LineFaces.mk h) = Quotient.mk'' (lineOf h) := rfl

theorem lineFaceToOrbit_surjective : Function.Surjective lineFaceToOrbit := by
  intro o
  induction o using Quotient.inductionOn' with
  | h ℓ =>
    obtain ⟨h, rfl⟩ := exists_lineOf ℓ
    exact ⟨LineFaces.mk h, rfl⟩

theorem lineFaceToOrbit_injective : Function.Injective lineFaceToOrbit := by
  intro i j hij
  induction i using Quotient.inductionOn with
  | h h =>
    induction j using Quotient.inductionOn with
    | h h' =>
      have heq : (Quotient.mk'' (lineOf h) : labelOrbits Γ6 Line) = Quotient.mk'' (lineOf h') := hij
      have hrel := Quotient.exact heq
      obtain ⟨g, hg⟩ := (MulAction.orbitRel_apply).1 hrel
      -- `g • lineOf h' = lineOf h`
      obtain ⟨p, rfl⟩ := gammaSixEquiv.surjective g
      have hg' : lineOf (h' * p.1⁻¹) = lineOf h := by
        rw [← smul_lineOf]; exact hg
      rw [lineOf_eq_iff] at hg'
      apply Quotient.sound
      refine ⟨(h * (h' * p.1⁻¹)⁻¹)⁻¹, lineBorel.inv_mem hg', p.1, p.2, ?_⟩
      group

/-- **The faces of type `Q` of `Γ(6)` are the `Γ(6)`-orbits of rational lines.** -/
def lineFacesEquivOrbits : LineFaces 6 ≃ labelOrbits Γ6 Line :=
  Equiv.ofBijective lineFaceToOrbit ⟨lineFaceToOrbit_injective, lineFaceToOrbit_surjective⟩

/-- **The stabilizer of the line `ℓ_h` in `Γ(6)` is the line group `gammaNQAt 6 h`.** -/
theorem mem_stabilizer_lineOf_iff (p : gammaN 6) (h : SL(3, ℤ)) :
    gammaSixEquiv p ∈ MulAction.stabilizer Γ6 (lineOf h) ↔ p.1 ∈ gammaNQAt 6 h := by
  rw [MulAction.mem_stabilizer_iff, smul_lineOf, lineOf_eq_iff]
  have e : h * (h * p.1⁻¹)⁻¹ = h * p.1 * h⁻¹ := by group
  rw [e]
  constructor
  · intro hq
    have hmem : h * p.1 * h⁻¹ ∈ gammaN 6 := by
      have := (gammaN_normal 6).conj_mem _ p.2 h
      simpa [mul_assoc] using this
    exact ⟨hmem, mem_lineStab_of_gammaN (by norm_num) hmem hq.1 hq.2⟩
  · intro hq
    exact mem_lineBorel_of_mem_lineStab hq.2

end Lines

end TernaryPeriodPolynomials.Argument.GammaNStokes
