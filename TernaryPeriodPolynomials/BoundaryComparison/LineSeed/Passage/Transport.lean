module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.CompleteFamilies
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Faces

@[expose] public section


/-!
# The Shapiro coordinate of a stratum class at a line cusp, through the standard good line (Passage 5)

Let `std = [Π] = ⟨e₃⟩` be the standard good line, `h ∈ SL₃(ℤ)` a conjugator and `q ∈ K†` a transporter with `q • std = h⁻¹⟨e₁⟩` (`lineFlagAt h`).  Conjugation by `q` carries the group
`Γ_{h⁻¹Qh}` of the line cusp into the stabilizer `Δ_s = Γ_{std} ∩ Γ(N)` (`faceToStd`), and

`phiLineAt_transport`: the face coordinate `phiLineAt h a` of a stratum class `a` is the pullback along `faceToStd` (with the coefficient map `ρ(q)`) of the Mathlib `H²` class of the restriction to
`Δ_s` of the coordinate of `a` at `std`.  (Uses the naturality `bridge_conj` of the model-to-Mathlib bridge and the transport of the fixed point classes.)

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The standard good line `ℚ e₃`, as a rational line flag. -/
abbrev stdLine : Flags .line := (QuotientGroup.mk rationalGoodLine : Flags .line)

section Hom

omit [NeZero N] in
theorem faceToStd_mem (h3 : 3 ∣ N) (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel) (hF : q • stdLine = lineFlagAt h)
    (p : ↥(gammaNQAt N h)) :
    q⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ p.1 * q ∈ fixedPointLevel (levelPrincipal N) stdLine := by
  refine ⟨?_, ?_⟩
  · have h1 := mapGL_mem_levelPrincipal N h3 (gammaNQAt_le_gammaN N h p.2)
    have := levelPrincipal_norm N q hq _ h1
    simpa [mul_assoc] using this
  · have h2 := MulAction.mem_stabilizer_iff.mp (mapGL_mem_stabL N h p.2)
    apply MulAction.mem_stabilizer_iff.mpr
    rw [mul_smul, mul_smul, hF, h2, ← hF, inv_smul_smul]

/-- Conjugation `p ↦ q⁻¹ p q` of the line group of the cusp `h⁻¹ Q h` into the stabilizer of the standard good line in `Γ ∩ Γ(N)`. -/
def faceToStd (h3 : 3 ∣ N) (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel) (hF : q • stdLine = lineFlagAt h) :
    ↥(gammaNQAt N h) →* ↥(fixedPointLevel (levelPrincipal N) stdLine) where
  toFun p := ⟨q⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ p.1 * q, faceToStd_mem N h3 h hq hF p⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

omit [NeZero N] in
theorem faceToStd_val (h3 : 3 ∣ N) (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel) (hF : q • stdLine = lineFlagAt h)
    (p : ↥(gammaNQAt N h)) :
    ((faceToStd N h3 h hq hF p).1 : RationalGL3) = q⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ p.1 * q := rfl

omit [NeZero N] in
/-- The conjugation relation `IsConj` between the stabilizers of `std` and of `h⁻¹⟨e₁⟩` in `Γ ∩ Γ(N)`. -/
theorem isConj_faceToStd (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel) (hF : q • stdLine = lineFlagAt h) :
    IsConj (fixedPointLevel (levelPrincipal N) stdLine) (fixedPointLevel (levelPrincipal N) (lineFlagAt h)) q :=
  isConj_stab_principal_side N hq (by rw [← hF, inv_smul_smul])

omit [NeZero N] in
theorem conjHom_faceToStd (h3 : 3 ∣ N) (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel) (hF : q • stdLine = lineFlagAt h)
    (p : ↥(gammaNQAt N h)) :
    conjHom q (isConj_faceToStd N h hq hF) (faceToStd N h3 h hq hF p) = lineEmbed N h3 h p := by
  apply Subtype.ext
  change q * (q⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ p.1 * q) * q⁻¹ = _
  rw [lineEmbed_val]
  group

end Hom

section Main

/-- The coefficient representation of the level group restricted to the stabilizer of the standard good line in `Γ ∩ Γ(N)`. -/
abbrev stdRep : Rep ℂ ↥(fixedPointLevel (levelPrincipal N) stdLine) :=
  Rep.of ((rationalCoefficientComponent n trivialCharacter).comp (fixedPointLevel (levelPrincipal N) stdLine).subtype)

omit [NeZero N] in
theorem faceToStd_hT (h3 : 3 ∣ N) (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel)
    (hF : q • stdLine = lineFlagAt h) (g : ↥(gammaNQAt N h)) (v : stdRep N n) :
    (rationalCoefficientComponent n trivialCharacter q : stdRep N n →ₗ[ℂ] lineFaceRep N h n)
        ((stdRep N n).ρ (faceToStd N h3 h hq hF g) v) =
      (lineFaceRep N h n).ρ g ((rationalCoefficientComponent n trivialCharacter q : stdRep N n →ₗ[ℂ] lineFaceRep N h n) v) := by
  change rationalCoefficientComponent n trivialCharacter q
      (rationalCoefficientComponent n trivialCharacter (q⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ g.1 * q) v) =
    ambRep n g.1 (rationalCoefficientComponent n trivialCharacter q v)
  rw [← coeff_mapGL n trivialCharacter g.1, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

omit [NeZero N] in
/-- The two comparisons of the line group of the cusp `h⁻¹ Q h` with a group of stabilizer type agree after conjugation. -/
theorem h2Map_lineEmbed_eq (h3 : 3 ∣ N) (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel)
    (hF : q • stdLine = lineFlagAt h) (W : groupCohomology.H2 (lineRep N h n trivialCharacter)) :
    EdgeNat.h2Map (lineEmbed N h3 h) (lineRep N h n trivialCharacter) (lineFaceRep N h n) LinearMap.id
        (lineEmbed_hT N h3 h n trivialCharacter) W =
      EdgeNat.h2Map (faceToStd N h3 h hq hF) (stdRep N n) (lineFaceRep N h n)
        (rationalCoefficientComponent n trivialCharacter q) (faceToStd_hT N n h3 h hq hF)
        ((groupCohomology.map (conjHom q (isConj_faceToStd N h hq hF))
          (conjRep (rationalCoefficientComponent n trivialCharacter) q (isConj_faceToStd N h hq hF)) 2).hom W) := by
  induction W using groupCohomology.H2_induction_on with | _ β => ?_
  have e1 := EdgeNat.h2Map_π (lineEmbed N h3 h) (lineRep N h n trivialCharacter) (lineFaceRep N h n) LinearMap.id
    (lineEmbed_hT N h3 h n trivialCharacter) β
  have e2 := groupCohomology.H2π_comp_map_apply (conjHom q (isConj_faceToStd N h hq hF))
    (conjRep (rationalCoefficientComponent n trivialCharacter) q (isConj_faceToStd N h hq hF)) β
  have e3 := EdgeNat.h2Map_π (faceToStd N h3 h hq hF) (stdRep N n) (lineFaceRep N h n)
    (rationalCoefficientComponent n trivialCharacter q) (faceToStd_hT N n h3 h hq hF)
    (groupCohomology.mapCocycles₂ (conjHom q (isConj_faceToStd N h hq hF))
      (conjRep (rationalCoefficientComponent n trivialCharacter) q (isConj_faceToStd N h hq hF)) β)
  rw [e1, e2, e3]
  congr 1
  apply Subtype.ext
  funext p
  change (β.1 (lineEmbed N h3 h p.1, lineEmbed N h3 h p.2) : lineFaceRep N h n) = _
  have f1 := conjHom_faceToStd N h3 h hq hF p.1
  have f2 := conjHom_faceToStd N h3 h hq hF p.2
  change _ = rationalCoefficientComponent n trivialCharacter q
    (rationalCoefficientComponent n trivialCharacter q⁻¹
      (β.1 (conjHom q (isConj_faceToStd N h hq hF) (faceToStd N h3 h hq hF p.1),
        conjHom q (isConj_faceToStd N h hq hF) (faceToStd N h3 h hq hF p.2))))
  rw [f1, f2, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

omit [NeZero N] in
theorem lineH2Equiv_apply (h3 : 3 ∣ N) (hN : 3 ≤ N) (h : SL(3, ℤ))
    (x : H2 (fixedPointLevel (levelPrincipal N) (lineFlagAt h)) (rationalCoefficientComponent n trivialCharacter)) :
    lineH2Equiv N h3 h n trivialCharacter hN x =
      EdgeNat.h2Map (lineEmbed N h3 h) (lineRep N h n trivialCharacter) (lineFaceRep N h n) LinearMap.id
        (lineEmbed_hT N h3 h n trivialCharacter)
        (bridge (rationalCoefficientComponent n trivialCharacter)
          (fixedPointLevel (levelPrincipal N) (lineFlagAt h)) x) := rfl

omit [NeZero N] in
/-- **The face coordinate of a stratum class at the line cusp `h⁻¹ Q h`, through the standard good line.**  For a transporter `q ∈ K†` with `q • std = h⁻¹⟨e₁⟩`,
`phiLineAt h a` is the pullback along `p ↦ q⁻¹ p q` (with coefficient map `ρ(q)`) of the Mathlib class of the restriction to `Γ_{std} ∩ Γ(N)` of the
coordinate `X = fixedPointH2 std a` of `a` at the standard good line. -/
theorem phiLineAt_transport (h3 : 3 ∣ N) (hN : 3 ≤ N) (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel)
    (hF : q • stdLine = lineFlagAt h) (a : StratumH2 n trivialCharacter .line) :
    phiLineAt N h3 hN n h a =
      EdgeNat.h2Map (faceToStd N h3 h hq hF) (stdRep N n) (lineFaceRep N h n)
        (rationalCoefficientComponent n trivialCharacter q) (faceToStd_hT N n h3 h hq hF)
        (bridge (rationalCoefficientComponent n trivialCharacter)
          (fixedPointLevel (levelPrincipal N) stdLine)
          (resPrincipal N stdLine (rationalCoefficientComponent n trivialCharacter)
            (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) stdLine a))) := by
  have hg := isConj_faceToStd N h hq hF
  have e1 := stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
    ⟨q, hq⟩ stdLine (lineFlagAt h) hF a
  have e2 := resPrincipal_transport_side N n ⟨q, hq⟩ hF hg
    (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) stdLine a)
  rw [e1] at e2
  have e3 : phiLineAt N h3 hN n h a = lineH2Equiv N h3 h n trivialCharacter hN
      (resPrincipal N (lineFlagAt h) (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (lineFlagAt h) a)) := rfl
  rw [e3, e2, lineH2Equiv_apply, h2Map_lineEmbed_eq N n h3 h hq hF, bridge_conj]

end Main

end TernaryPeriodPolynomials.Argument.KDaggerComparison
