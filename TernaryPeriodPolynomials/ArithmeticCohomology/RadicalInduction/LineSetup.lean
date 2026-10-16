module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.CanIdent
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadEdge

@[expose] public section


/-!
# The extensions of the face group `S_i` and of its stabilizer, and the compatibility `Compat`, for lines at `q = 1`

Formalized by Claude Sonnet 5.5.

`extS i` is the extension `ℤ² → S_i → Γ(6)` transported from `lineFaceExt 6 i.rep` along `S_i ≅ K_i` (`lineSubEquiv`), `extStab D` the extension of the stabilizer `Stab_{S_i}(u'Δ)` transported from
`lineFaceExt M i'.rep` along `μ`.  For `D.q = 1` the inclusion `Stab ≤ S_i` is compatible (`Compat`) with radical map `r ↦ r^{M/6}`.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3

/-- The extension `ℤ² → S_i → Γ(6)` of the face group `S_i ⊂ Γ(6)`. -/
def extS (i : LineFaces 6) : GroupExtension RadicalLattice ↥(lineSub i) ↥(CongruenceSubgroup.Gamma 6) :=
  FaceTransport.pullbackExt (lineFaceExt 6 i.rep) (lineSubEquiv i)

/-- Its Levi splitting. -/
def splS (i : LineFaces 6) : (extS i).Splitting :=
  FaceTransport.splitting (FaceTransport.pullbackEquiv (lineFaceExt 6 i.rep) (lineSubEquiv i)) (lineFaceSplitting 6 i.rep)

theorem radInput_splS (i : LineFaces 6) (m : ↥(CongruenceSubgroup.Gamma 6)) (r : RadicalLattice) :
    splitRadicalInput (splS i) m r = splitRadicalInput (lineFaceSplitting 6 i.rep) m r :=
  FaceTransport.radicalInput_eq (FaceTransport.pullbackEquiv (lineFaceExt 6 i.rep) (lineSubEquiv i)) (lineFaceSplitting 6 i.rep) m r

theorem hdetS (i : LineFaces 6) (A : ↥(CongruenceSubgroup.Gamma 6)) : radDet (splitRadicalInput (splS i) A) = 1 := by
  have := lineFaceRadicalInput_det 6 i.rep A
  unfold radDet at this ⊢
  simpa [radInput_splS] using this

theorem gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA ⊢
  have key : ∀ x : ℤ, ((x : ZMod M)) = 1 → (x : ZMod N) = 1 := fun x hx => by
    have := congrArg (ZMod.castHom h (ZMod N)) hx
    rwa [map_intCast, map_one] at this
  have key0 : ∀ x : ℤ, ((x : ZMod M)) = 0 → (x : ZMod N) = 0 := fun x hx => by
    have := congrArg (ZMod.castHom h (ZMod N)) hx
    rwa [map_intCast, map_zero] at this
  exact ⟨key _ hA.1, key0 _ hA.2.1, key0 _ hA.2.2.1, key _ hA.2.2.2⟩

section Stab

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') (h6 : 6 ∣ M)

/-- The stabilizer of the coset `u' Δ` in the face group `S_i`. -/
abbrev StabD : Subgroup ↥(lineSub D.i) := StabS (Δ6 M) (lineSub D.i) D.u

/-- `μ` as an isomorphism `Stab_{S_i}(u'Δ) ≃ Γ(M) ∩ i'.rep⁻¹ Q i'.rep`. -/
def muEquiv : ↥(StabD D) ≃* ↥(gammaNQAt M i'.rep) := MulEquiv.ofBijective D.mu (D.mu_bijective h6)

omit [NeZero M] in
theorem muEquiv_symm_val (p : ↥(gammaNQAt M i'.rep)) :
    ((((muEquiv D h6).symm p : ↥(StabD D)) : ↥(lineSub D.i)) : ↥(gammaN 6)).1 =
      (D.u : SL(3, ℤ)) * p.1 * (D.u : SL(3, ℤ))⁻¹ := by
  have h := congrArg (fun q : ↥(gammaNQAt M i'.rep) => q.1) ((muEquiv D h6).apply_symm_apply p)
  change (D.u : SL(3, ℤ))⁻¹ * ((((muEquiv D h6).symm p : ↥(StabD D)) : ↥(lineSub D.i)) : ↥(gammaN 6)).1 * (D.u : SL(3, ℤ)) = p.1 at h
  rw [← h]
  group

/-- The extension `ℤ² → Stab → Γ(M)` of the stabilizer, transported from `lineFaceExt M i'.rep` along `μ`. -/
def extStab : GroupExtension RadicalLattice ↥(StabD D) ↥(CongruenceSubgroup.Gamma M) :=
  FaceTransport.pullbackExt (lineFaceExt M i'.rep) (muEquiv D h6)

/-- Its Levi splitting. -/
def splStab : (extStab D h6).Splitting :=
  FaceTransport.splitting (FaceTransport.pullbackEquiv (lineFaceExt M i'.rep) (muEquiv D h6)) (lineFaceSplitting M i'.rep)

theorem hdetStab (A : ↥(CongruenceSubgroup.Gamma M)) : radDet (splitRadicalInput (splStab D h6) A) = 1 := by
  have e : ∀ r, splitRadicalInput (splStab D h6) A r = splitRadicalInput (lineFaceSplitting M i'.rep) A r := fun r =>
    FaceTransport.radicalInput_eq (FaceTransport.pullbackEquiv (lineFaceExt M i'.rep) (muEquiv D h6)) (lineFaceSplitting M i'.rep) A r
  have := lineFaceRadicalInput_det M i'.rep A
  unfold radDet at this ⊢
  rw [e rl1, e rl2]
  exact this

end Stab

section Helpers

theorem lineFaceExt_inl_val (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (r : RadicalLattice) :
    (((lineFaceExt N h).inl r : ↥(gammaNQAt N h)) : SL(3, ℤ)) = h⁻¹ * radEltQ N r * h := rfl

theorem lineFaceSplitting_val (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (m : ↥(CongruenceSubgroup.Gamma N)) :
    (((lineFaceSplitting N h) m : ↥(gammaNQAt N h)) : SL(3, ℤ)) = h⁻¹ * blockDiagQ m.1 * h := rfl

theorem radEltQ_mul_pow (m0 : ℕ) (r : RadicalLattice) : radEltQ (6 * m0) r = radEltQ 6 (r ^ m0) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radEltQ, toAdd_pow] <;> ring

theorem radEltQ_div {M : ℕ} (h6 : 6 ∣ M) (r : RadicalLattice) : radEltQ M r = radEltQ 6 (r ^ (M / 6)) := by
  obtain ⟨m0, rfl⟩ := h6
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  exact radEltQ_mul_pow m0 r

end Helpers

section CompatLine

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') (h6 : 6 ∣ M)

omit [NeZero M] in
theorem rep_eq_of_q (hq : D.q = 1) : i'.rep = D.i.rep * (D.u : SL(3, ℤ)) := by
  have := D.hrep
  rwa [hq, one_mul] at this

/-- **`Compat` for lines at `q = 1`**: the inclusion of the stabilizer of `u'Δ` in the face group `S_i` is a morphism of split extensions, with radical map `r ↦ r^{M/6}` and the inclusion `Γ(M) ≤ Γ(6)` on the Levi. -/
theorem compat_line (hq : D.q = 1) :
    Compat (extS D.i) (splS D.i) (StabD D) (StabD D).subtype (extStab D h6) (splStab D h6)
      (Subgroup.inclusion (gamma_le_of_dvd h6)) (M / 6) where
  range_eq := Subgroup.range_subtype _
  inl_eq r := by
    have hrep := rep_eq_of_q D hq
    apply Subtype.ext
    apply Subtype.ext
    change ((((muEquiv D h6).symm ((lineFaceExt M i'.rep).inl r) : ↥(StabD D)) : ↥(lineSub D.i)) : ↥(gammaN 6)).1 =
      (((lineFaceExt 6 D.i.rep).inl (r ^ (M / 6)) : ↥(gammaNQAt 6 D.i.rep)) : SL(3, ℤ))
    rw [muEquiv_symm_val, lineFaceExt_inl_val, lineFaceExt_inl_val, radEltQ_div h6, hrep]
    group
  split_eq m := by
    have hrep := rep_eq_of_q D hq
    apply Subtype.ext
    apply Subtype.ext
    change ((((muEquiv D h6).symm ((lineFaceSplitting M i'.rep) (m : ↥(CongruenceSubgroup.Gamma M))) : ↥(StabD D)) : ↥(lineSub D.i)) :
        ↥(gammaN 6)).1 = (((lineFaceSplitting 6 D.i.rep) (Subgroup.inclusion (gamma_le_of_dvd h6) m) : ↥(gammaNQAt 6 D.i.rep)) : SL(3, ℤ))
    rw [muEquiv_symm_val, lineFaceSplitting_val, lineFaceSplitting_val, hrep]
    change _ = _ * blockDiagQ (m.1 : SL(2, ℤ)) * _
    group
  inj := Subgroup.inclusion_injective _
  det := hdetS D.i

end CompatLine

end TernaryPeriodPolynomials.Argument.RadicalInduction
