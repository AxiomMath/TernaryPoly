module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaceTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FlagDictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj

@[expose] public section


/-!
# Level descent at every line cusp: the locally inner classes versus `𝒞_{h⁻¹Qh}(E)` of `Γ(N)`

Formalized by Claude Sonnet 5.5.
Paper: Appendix C, ("`Γ(N) ⊂ K†` ... all coefficient
pairings and restriction maps commute with this averaging; `𝒞_R^{K†}(E)` are the invariants of the sum of the `𝒞_R(E)` of `Γ(N)`").

This is the line analogue (`R = Q`) of `SeedC3S4c.PlaneFaceDescent` and `PlaneFaceTransfer`.  For `N ≥ 3`, `3 ∣ N` and an integral change of
basis `h ∈ SL₃(ℤ)`, let `F = h⁻¹ ℚ e₁` (`lineFlagAt h`) be the corresponding rational line.

* `lineEmbed`: the line group `Γ(N) ∩ h⁻¹Qh` (`gammaNQAt N h`) is isomorphic (`lineEmbed_injective`, `lineEmbed_surjective`) to the stabilizer
  of `F` in `Γ ∩ Γ(N)`, `Γ` the paper's level group;
* `lineH2Equiv`: Mathlib's `H²(Γ(N) ∩ h⁻¹Qh, E_n)` is the face library's homogeneous `H²` of that stabilizer;
* `lineStabAt_iff`, `exists_frame_of_edge_line`, `exists_edge_of_frame_line`: the stabilizers in the line group of the complete flags over `F`
  are exactly the flag stabilizers `lineFlagStab N h F'`, `F'` a frame of the binary Levi (`conj_mem_borel_iff_line` is the matrix computation);
* `mem_locallyInnerAt_iff_lineLocallyInner`: under `lineH2Equiv`, the locally inner classes for the level `Γ ∩ Γ(N)` are `lineLocallyInner N h n`;
* **`locallyInnerClasses_lineFlag_iff`**: a class of the face library's `H²(Γ_F, E)` is locally inner iff its restriction to `Γ_F ∩ Γ(N)`, read in
  Mathlib's `H²` of the line group, lies in `lineFaceCuspidalInH2 N h n`, the image of the literal mixed cuspidal group `𝒞_{h⁻¹Qh}(E)`;
* `lineTransfer`, **`locallyInnerClasses_lineFlag_eq_transfer`**: `𝒞(Γ_F)` is the set of transfers of `lineFaceCuspidalInH2 N h n`;
* **`mem_map_locallyInnerClasses_lineFlag_iff`**: `𝒞(Γ) = 𝒞(Γ(N))^{invariants}`.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFacesFull

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFaces

section LineFlag

variable (N : ℕ)

/-- The line `h⁻¹ ℚ e₁` of the integral change of basis `h`, as a rational line flag. -/
def lineFlagAt (h : SL(3, ℤ)) : Flags .line :=
  QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)

theorem gammaNQAt_le_gammaN (h : SL(3, ℤ)) {p : SL(3, ℤ)} (hp : p ∈ gammaNQAt N h) :
    p ∈ gammaN N := by
  have hq : h * p * h⁻¹ ∈ gammaN N := hp.1
  have := (gammaN_normal N).conj_mem _ hq h⁻¹
  simpa [mul_assoc] using this

theorem mapGL_mem_stabL (h : SL(3, ℤ)) {p : SL(3, ℤ)} (hp : p ∈ gammaNQAt N h) :
    Matrix.SpecialLinearGroup.mapGL ℚ p ∈ MulAction.stabilizer RationalGL3 (lineFlagAt h) := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ p *
    Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .line) = QuotientGroup.mk _
  apply QuotientGroup.eq.mpr
  have hq : (h * p * h⁻¹)⁻¹ ∈ gammaNQ N := (gammaNQ N).inv_mem hp
  have h10 : ((h * p * h⁻¹)⁻¹ : SL(3, ℤ)) 1 0 = 0 := hq.2.2.1
  have h20 : ((h * p * h⁻¹)⁻¹ : SL(3, ℤ)) 2 0 = 0 := hq.2.2.2
  have : (Matrix.SpecialLinearGroup.mapGL ℚ p * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ *
      Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ = Matrix.SpecialLinearGroup.mapGL ℚ (h * p * h⁻¹)⁻¹ := by
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  rw [this]
  refine ⟨?_, ?_⟩
  · change (((h * p * h⁻¹)⁻¹ : SL(3, ℤ)) 1 0 : ℚ) = 0
    rw [h10]; simp
  · change (((h * p * h⁻¹)⁻¹ : SL(3, ℤ)) 2 0 : ℚ) = 0
    rw [h20]; simp

/-- Every element of the principal congruence subgroup of the level group is `mapGL p` for a unique `p ∈ Γ(N)` (`N ≥ 3`). -/
theorem levelPrincipal_eq_mapGL (hN : 3 ≤ N) {x : RationalGL3} (hxM : x ∈ levelPrincipal N) :
    ∃ p : SL(3, ℤ), p ∈ gammaN N ∧ x = Matrix.SpecialLinearGroup.mapGL ℚ p := by
  obtain ⟨g, hg, hgx⟩ := hxM
  have hred : ∀ i j, (((g.1.val i j : ℤ)) : ZMod N) = (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := by
    intro i j
    have := congrArg (fun y : GL (Fin 3) (ZMod N) => (y.val : Matrix (Fin 3) (Fin 3) (ZMod N)) i j)
      (MonoidHom.mem_ker.mp hg)
    exact this
  have hdet1 : g.1.val.det = 1 := by
    have hu : IsUnit g.1.val.det := (Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit
    have hmod : ((g.1.val.det : ℤ) : ZMod N) = 1 := by
      have : (g.1.val.map (Int.castRingHom (ZMod N))).det = ((g.1.val.det : ℤ) : ZMod N) :=
        (RingHom.map_det (Int.castRingHom (ZMod N)) g.1.val).symm
      rw [← this]
      have hm : g.1.val.map (Int.castRingHom (ZMod N)) = 1 := by
        ext i j; exact hred i j
      rw [hm, Matrix.det_one]
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact h1
    · rw [h1] at hmod
      have h2 : ((-1 : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by simpa using hmod
      have h3' := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) 1 N).mp h2
      have h4 : (N : ℤ) ∣ 2 := by
        have : (1 : ℤ) - -1 = 2 := by norm_num
        rwa [this] at h3'
      have h5 := Int.le_of_dvd (by norm_num) h4
      omega
  let p : SL(3, ℤ) := ⟨g.1.val, hdet1⟩
  have hpN : p ∈ gammaN N := by
    rw [mem_gammaN]
    intro i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    rw [Int.cast_sub, sub_eq_zero]
    have h1 : (((1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N) =
        (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [h1]
    exact hred i j
  refine ⟨p, hpN, ?_⟩
  rw [← hgx]
  apply Units.ext
  ext i j
  rfl

variable (h3 : 3 ∣ N) (h : SL(3, ℤ))

/-- **The line group of `Γ(N)` at the cusp `h⁻¹Qh` inside the stabilizer of the line `h⁻¹ℚe₁` in `Γ ∩ Γ(N)`.** -/
def lineEmbed : ↥(gammaNQAt N h) →*
    ↥(fixedPointLevel (levelPrincipal N) (lineFlagAt h)) where
  toFun p := ⟨Matrix.SpecialLinearGroup.mapGL ℚ p.1,
    mapGL_mem_levelPrincipal N h3 (gammaNQAt_le_gammaN N h p.2), mapGL_mem_stabL N h p.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem lineEmbed_val (p : ↥(gammaNQAt N h)) :
    ((lineEmbed N h3 h p).1 : RationalGL3) = Matrix.SpecialLinearGroup.mapGL ℚ p.1 := rfl

theorem lineEmbed_injective : Function.Injective (lineEmbed N h3 h) := by
  intro a b hab
  have h1 := congrArg (fun x : ↥(fixedPointLevel (levelPrincipal N) (lineFlagAt h)) =>
    ((x.1 : RationalGL3).val : Matrix (Fin 3) (Fin 3) ℚ)) hab
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h1 i) j
  change (((a.1 : SL(3, ℤ)) i j : ℤ) : ℚ) = (((b.1 : SL(3, ℤ)) i j : ℤ) : ℚ) at this
  exact_mod_cast this

theorem lineEmbed_surjective (hN : 3 ≤ N) : Function.Surjective (lineEmbed N h3 h) := by
  rintro ⟨x, hxM, hxS⟩
  obtain ⟨p, hpN, hxp⟩ := levelPrincipal_eq_mapGL N hN hxM
  have hstab : Matrix.SpecialLinearGroup.mapGL ℚ p ∈ MulAction.stabilizer RationalGL3
      (lineFlagAt h) := hxp ▸ hxS
  have hinv : (h * p⁻¹ * h⁻¹ : SL(3, ℤ)) 1 0 = 0 ∧ (h * p⁻¹ * h⁻¹ : SL(3, ℤ)) 2 0 = 0 := by
    rw [MulAction.mem_stabilizer_iff] at hstab
    change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ p *
      Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .line) = QuotientGroup.mk _ at hstab
    have h1 := QuotientGroup.eq.mp hstab
    have : (Matrix.SpecialLinearGroup.mapGL ℚ p * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ *
        Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ = Matrix.SpecialLinearGroup.mapGL ℚ (h * p⁻¹ * h⁻¹) := by
      simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [this] at h1
    have h2 : Matrix.SpecialLinearGroup.mapGL ℚ (h * p⁻¹ * h⁻¹) ∈ lineParabolic ℚ := h1
    obtain ⟨e0, e1⟩ := h2
    constructor
    · have : (((h * p⁻¹ * h⁻¹ : SL(3, ℤ)) 1 0 : ℤ) : ℚ) = 0 := e0
      exact_mod_cast this
    · have : (((h * p⁻¹ * h⁻¹ : SL(3, ℤ)) 2 0 : ℤ) : ℚ) = 0 := e1
      exact_mod_cast this
  have hpinvN : p⁻¹ ∈ gammaN N := (gammaN N).inv_mem hpN
  have hconjN : h * p⁻¹ * h⁻¹ ∈ gammaN N := by
    have := (gammaN_normal N).conj_mem _ hpinvN h
    simpa [mul_assoc] using this
  have hq' : h * p⁻¹ * h⁻¹ ∈ lineStab := mem_lineStab_of_gammaN hN hconjN hinv.1 hinv.2
  have hq : h * p * h⁻¹ ∈ lineStab := by
    have := lineStab.inv_mem hq'
    simpa [mul_assoc] using this
  have hqN : h * p * h⁻¹ ∈ gammaN N := by
    have := (gammaN_normal N).conj_mem p hpN h
    simpa [mul_assoc] using this
  exact ⟨⟨p, hqN, hq⟩, Subtype.ext hxp.symm⟩

end LineFlag

section Binary

/-- The lower right `2 × 2` block of an element of the rational line parabolic. -/
def lineParabolicBinaryMatrix (matrix : lineParabolic ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun row column => matrix.val.val row.succ column.succ

theorem lineParabolicBinaryMatrix_one :
    lineParabolicBinaryMatrix (1 : lineParabolic ℚ) = 1 := by
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem lineParabolicBinaryMatrix_mul (first second : lineParabolic ℚ) :
    lineParabolicBinaryMatrix (first * second) =
      lineParabolicBinaryMatrix first * lineParabolicBinaryMatrix second := by
  funext row column
  change (∑ position : Fin 3, first.val.val row.succ position * second.val.val position column.succ) =
    ∑ position : Fin 2, first.val.val row.succ position.succ * second.val.val position.succ column.succ
  fin_cases row <;> fin_cases column <;>
    simp [Fin.sum_univ_three, Fin.sum_univ_two, first.property.1, first.property.2]

/-- The binary Levi quotient `Q(ℚ) → GL₂(ℚ)` of the rational line parabolic (lower right block). -/
def lineParabolicBinary : lineParabolic ℚ →* GL (Fin 2) ℚ where
  toFun matrix :=
    ⟨lineParabolicBinaryMatrix matrix, lineParabolicBinaryMatrix matrix⁻¹, by
      rw [← lineParabolicBinaryMatrix_mul, mul_inv_cancel, lineParabolicBinaryMatrix_one], by
      rw [← lineParabolicBinaryMatrix_mul, inv_mul_cancel, lineParabolicBinaryMatrix_one]⟩
  map_one' := Units.ext lineParabolicBinaryMatrix_one
  map_mul' first second := Units.ext (lineParabolicBinaryMatrix_mul first second)

theorem lineParabolicBinary_apply (matrix : lineParabolic ℚ) (row column : Fin 2) :
    (lineParabolicBinary matrix).val row column = matrix.val.val row.succ column.succ := rfl

/-- Conjugation of a line-parabolic element by a line-parabolic element lies in the Borel group iff the lower left entry of the
conjugated binary block vanishes. -/
theorem conj_mem_borel_iff_line (g q : RationalGL3) (hg : g ∈ lineParabolic ℚ) (hq : q ∈ lineParabolic ℚ) :
    g⁻¹ * q * g ∈ parabolic .plane ⊓ parabolic .line ↔
      ((lineParabolicBinary (⟨g, hg⟩ : lineParabolic ℚ))⁻¹ *
        lineParabolicBinary (⟨q, hq⟩ : lineParabolic ℚ) *
        lineParabolicBinary (⟨g, hg⟩ : lineParabolic ℚ)).val 1 0 = 0 := by
  let pg : lineParabolic ℚ := ⟨g, hg⟩
  let pq : lineParabolic ℚ := ⟨q, hq⟩
  let P : lineParabolic ℚ := pg⁻¹ * pq * pg
  have hP : P.val = g⁻¹ * q * g := rfl
  have hbin : lineParabolicBinary P =
      (lineParabolicBinary pg)⁻¹ * lineParabolicBinary pq * lineParabolicBinary pg := by
    rw [show P = pg⁻¹ * pq * pg from rfl, map_mul, map_mul, map_inv]
  have h10 : (lineParabolicBinary P).val 1 0 = P.val.val 2 1 := rfl
  rw [← hP, ← hbin, h10]
  constructor
  · intro h
    exact h.1.2
  · intro h
    exact ⟨⟨P.property.2, h⟩, P.property⟩

end Binary

section Edges

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

/-- The subgroup of the line group `Γ(N) ∩ h⁻¹Qh` stabilizing the complete flag `e`. -/
def lineStabAt (e : Edges) : Subgroup ↥(gammaNQAt N h) :=
  (MulAction.stabilizer RationalGL3 e).comap
    ((Matrix.SpecialLinearGroup.mapGL ℚ).comp (gammaNQAt N h).subtype)

theorem mapGL_mem_lineParabolic {q : SL(3, ℤ)} (hq : q ∈ lineStab) :
    Matrix.SpecialLinearGroup.mapGL ℚ q ∈ lineParabolic ℚ := by
  refine ⟨?_, ?_⟩
  · change (((q : Matrix (Fin 3) (Fin 3) ℤ) 1 0 : ℤ) : ℚ) = 0
    rw [hq.2.1]; simp
  · change (((q : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℤ) : ℚ) = 0
    rw [hq.2.2]; simp

theorem binary_mapGL_line {q : SL(3, ℤ)} (hq : q ∈ lineStab) :
    ((lineParabolicBinary (⟨Matrix.SpecialLinearGroup.mapGL ℚ q, mapGL_mem_lineParabolic hq⟩ :
      lineParabolic ℚ)).val : Matrix (Fin 2) (Fin 2) ℚ) =
      (Int.castRingHom ℚ).mapMatrix (botRight q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem lineStabAt_iff (g : RationalGL3) (hg : g ∈ lineParabolic ℚ) (p : ↥(gammaNQAt N h)) :
    p ∈ lineStabAt N h (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g)) ↔
      p ∈ lineFlagStab N h (lineParabolicBinary (⟨g, hg⟩ : lineParabolic ℚ)) := by
  have hq : h * p.1 * h⁻¹ ∈ lineStab := p.2.2
  rw [mem_lineFlagStab_iff N h p.1 p.2]
  have hbin := binary_mapGL_line hq
  have key := conj_mem_borel_iff_line g (Matrix.SpecialLinearGroup.mapGL ℚ (h * p.1 * h⁻¹)) hg
    (mapGL_mem_lineParabolic hq)
  have hstep : p ∈ lineStabAt N h
      (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g)) ↔
      g⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (h * p.1 * h⁻¹) * g ∈
        parabolic .plane ⊓ parabolic .line := by
    change (Matrix.SpecialLinearGroup.mapGL ℚ p.1) • (QuotientGroup.mk
      (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g) : Edges) = QuotientGroup.mk _ ↔ _
    change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ p.1 *
      (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g)) : Edges) = QuotientGroup.mk _ ↔ _
    rw [QuotientGroup.eq, ← inv_mem_iff]
    have : ((Matrix.SpecialLinearGroup.mapGL ℚ p.1 *
        (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g))⁻¹ *
        (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g))⁻¹ =
        g⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (h * p.1 * h⁻¹) * g := by
      simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
  rw [hstep, key, Units.val_mul, Units.val_mul]
  have hB : (lineParabolicBinary (⟨Matrix.SpecialLinearGroup.mapGL ℚ (h * p.1 * h⁻¹),
      mapGL_mem_lineParabolic hq⟩ : lineParabolic ℚ)).val =
      (Int.castRingHom ℚ).mapMatrix (botRight (h * p.1 * h⁻¹)) := hbin
  rw [hB]

theorem exists_frame_of_edge_line (e : Edges) (he : endpoint .line e = lineFlagAt h) :
    ∃ F : GL (Fin 2) ℚ, lineStabAt N h e = lineFlagStab N h F := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective e
  have h1 : (QuotientGroup.mk c : Flags .line) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) := he
  have h2 : c⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ ∈ parabolic .line :=
    QuotientGroup.eq.mp h1
  have h3 : (c⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ ∈ parabolic .line :=
    (parabolic .line).inv_mem h2
  have hg : (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ * c ∈ lineParabolic ℚ := by
    have : (c⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ =
        (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ * c := by group
    rw [this] at h3
    exact h3
  obtain ⟨g, hgmem, hc⟩ : ∃ g, g ∈ lineParabolic ℚ ∧
      c = Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g :=
    ⟨_, hg, by group⟩
  subst hc
  refine ⟨lineParabolicBinary (⟨g, hgmem⟩ : lineParabolic ℚ), ?_⟩
  ext p
  exact lineStabAt_iff N h g hgmem p

/-- The line-parabolic element `diag(1, g)` of an integral frame. -/
theorem lineParabolicBinary_blockDiagQ (g : SL(2, ℤ)) :
    lineParabolicBinary (⟨Matrix.SpecialLinearGroup.mapGL ℚ (blockDiagQ g),
      mapGL_mem_lineParabolic (blockDiagQ_mem_lineStab g)⟩ : lineParabolic ℚ) =
      Matrix.SpecialLinearGroup.mapGL ℚ g := by
  apply Units.ext
  rw [binary_mapGL_line (blockDiagQ_mem_lineStab g)]
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [botRight, blockDiagQ]

theorem lineFlagStab_eq_of_cusp_basis (F : GL (Fin 2) ℚ) (g : SL(2, ℤ))
    (hg : ∀ γ : SL(2, ℤ),
      ((F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ * F : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 ↔
        ((g⁻¹ * γ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    lineFlagStab N h F = lineFlagStab N h (Matrix.SpecialLinearGroup.mapGL ℚ g) := by
  ext p
  change (lineFaceExt N h).rightHom p ∈ leviCuspStab (CongruenceSubgroup.Gamma N) F ↔
    (lineFaceExt N h).rightHom p ∈ leviCuspStab (CongruenceSubgroup.Gamma N) (Matrix.SpecialLinearGroup.mapGL ℚ g)
  rw [mem_leviCuspStab_iff, mem_leviCuspStab_iff, hg, mapGL_conj_apply10]

theorem exists_edge_of_frame_line (F : GL (Fin 2) ℚ) :
    ∃ e : Edges, endpoint .line e = lineFlagAt h ∧ lineStabAt N h e = lineFlagStab N h F := by
  obtain ⟨g, hg⟩ := exists_cusp_basis F
  have hgm : Matrix.SpecialLinearGroup.mapGL ℚ (blockDiagQ g) ∈ lineParabolic ℚ :=
    mapGL_mem_lineParabolic (blockDiagQ_mem_lineStab g)
  refine ⟨QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ *
    Matrix.SpecialLinearGroup.mapGL ℚ (blockDiagQ g)), ?_, ?_⟩
  · change (QuotientGroup.mk _ : Flags .line) = QuotientGroup.mk _
    apply QuotientGroup.eq.mpr
    simpa using (parabolic .line).inv_mem hgm
  · ext p
    rw [lineStabAt_iff N h _ hgm p]
    have := lineParabolicBinary_blockDiagQ g
    rw [this, lineFlagStab_eq_of_cusp_basis N h F g hg]

end Edges



section Descent

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (h : SL(3, ℤ)) (n : ℕ) (character : RankOneCharacter)

/-- The coefficient representation of the level group restricted to `Γ_F ∩ Γ(N)` (lines), in Mathlib's language. -/
abbrev lineRep : Rep ℂ ↥(fixedPointLevel (levelPrincipal N) (lineFlagAt h)) :=
  Rep.of ((rationalCoefficientComponent n character).comp
    (fixedPointLevel (levelPrincipal N) (lineFlagAt h)).subtype)

omit [NeZero N] in
theorem lineEmbed_hT (g : ↥(gammaNQAt N h)) (v : lineRep N h n character) :
    (LinearMap.id : lineRep N h n character →ₗ[ℂ] lineFaceRep N h n)
      ((lineRep N h n character).ρ (lineEmbed N h3 h g) v) =
    (lineFaceRep N h n).ρ g ((LinearMap.id : lineRep N h n character →ₗ[ℂ] lineFaceRep N h n) v) := by
  change rationalCoefficientComponent n character (Matrix.SpecialLinearGroup.mapGL ℚ g.1) v =
    ambRep n g.1 v
  rw [coeff_mapGL]

/-- **Mathlib's `H²` of the line group `Γ(N) ∩ h⁻¹Qh` is the homogeneous `H²` of the stabilizer of the line `h⁻¹ℚe₁` in
`Γ ∩ Γ(N)`** (`N ≥ 3`, `3 ∣ N`). -/
def lineH2Equiv (hN : 3 ≤ N) :
    GeneralEisenstein.Homogeneous.H2 (fixedPointLevel (levelPrincipal N) (lineFlagAt h))
        (rationalCoefficientComponent n character) ≃ₗ[ℂ]
      groupCohomology.H2 (lineFaceRep N h n) :=
  (LevelTransfer.bridge (rationalCoefficientComponent n character)
    (fixedPointLevel (levelPrincipal N) (lineFlagAt h))).trans
    (LinearEquiv.ofBijective
      (EdgeNat.h2Map (lineEmbed N h3 h) (lineRep N h n character) (lineFaceRep N h n)
        LinearMap.id (lineEmbed_hT N h3 h n character))
      ⟨EdgeNat.h2Map_injective (lineEmbed N h3 h) (lineRep N h n character) (lineFaceRep N h n)
          LinearMap.id (lineEmbed_hT N h3 h n character)
          ⟨lineEmbed_injective N h3 h, lineEmbed_surjective N h3 h hN⟩ Function.bijective_id,
        EdgeNat.h2Map_surjective (lineEmbed N h3 h) (lineRep N h n character) (lineFaceRep N h n)
          LinearMap.id (lineEmbed_hT N h3 h n character)
          ⟨lineEmbed_injective N h3 h, lineEmbed_surjective N h3 h hN⟩ Function.bijective_id⟩)

omit [NeZero N] in
theorem res_zero_iff_lineStab (hN : 3 ≤ N) (e : Edges)
    (he : endpoint .line e = lineFlagAt h)
    (x : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel (levelPrincipal N) (lineFlagAt h))
      (rationalCoefficientComponent n character)) :
    LevelTransfer.resH2 (rationalCoefficientComponent n character)
        (fixedPointLevel_edge_le_flag' (levelPrincipal N) .line e (lineFlagAt h) he) x = 0 ↔
      twoCohomologyRestriction (lineStabAt N h e).subtype (lineFaceRep N h n)
        (lineH2Equiv N h3 h n character hN x) = 0 := by
  let le := fixedPointLevel_edge_le_flag' (levelPrincipal N) .line e (lineFlagAt h) he
  let κ : ↥(lineStabAt N h e) →* ↥(fixedPointLevel (levelPrincipal N) e) :=
    { toFun := fun p => ⟨(lineEmbed N h3 h p.1).1, (lineEmbed N h3 h p.1).2.1, p.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hκ : ∀ k : ↥(lineStabAt N h e),
      lineEmbed N h3 h ((lineStabAt N h e).subtype k) =
        (Subgroup.inclusion le) (κ k) := fun k => rfl
  have hκb : Function.Bijective κ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply lineEmbed_injective N h3 h
      exact Subtype.ext (congrArg (fun y : ↥(fixedPointLevel (levelPrincipal N) e) =>
        (y.1 : RationalGL3)) hab)
    · intro y
      obtain ⟨p, hp⟩ := lineEmbed_surjective N h3 h hN ⟨y.1, le y.2⟩
      refine ⟨⟨p, ?_⟩, ?_⟩
      · have := y.2.2
        have h1 : (lineEmbed N h3 h p).1 = y.1 := congrArg Subtype.val hp
        change Matrix.SpecialLinearGroup.mapGL ℚ p.1 ∈ MulAction.stabilizer RationalGL3 e
        rw [← lineEmbed_val N h3 h, h1]
        exact this
      · apply Subtype.ext
        exact congrArg (fun z : ↥(fixedPointLevel (levelPrincipal N) (lineFlagAt h)) =>
          (z.1 : RationalGL3)) hp
  have key := EdgeNat.restriction_h2Map_eq_zero_iff (lineEmbed N h3 h)
    (lineRep N h n character) (lineFaceRep N h n) LinearMap.id (lineEmbed_hT N h3 h n character)
    (Subgroup.inclusion le) (lineStabAt N h e).subtype κ hκ hκb Function.bijective_id
    (LevelTransfer.bridge (rationalCoefficientComponent n character)
      (fixedPointLevel (levelPrincipal N) (lineFlagAt h)) x)
  refine Iff.trans ?_ key.symm
  have hbr := LevelTransfer.bridge_res (rationalCoefficientComponent n character) le x
  constructor
  · intro h0
    have : twoCohomologyRestriction (Subgroup.inclusion le) (lineRep N h n character)
        (LevelTransfer.bridge (rationalCoefficientComponent n character)
          (fixedPointLevel (levelPrincipal N) (lineFlagAt h)) x) = 0 := by
      refine hbr.trans ?_
      rw [h0, LinearEquiv.map_zero]
      rfl
    exact this
  · intro h0
    have h1 : LevelTransfer.bridge (rationalCoefficientComponent n character)
        (fixedPointLevel (levelPrincipal N) e)
        (LevelTransfer.resH2 (rationalCoefficientComponent n character) le x) = 0 := by
      refine hbr.symm.trans ?_
      exact h0
    exact (LevelTransfer.bridge (rationalCoefficientComponent n character)
      (fixedPointLevel (levelPrincipal N) e)).map_eq_zero_iff.mp h1

/-- **The face library's locally inner classes at the line `h⁻¹ℚe₁`, for the level `Γ ∩ Γ(N)`, are the classes of `𝒞_{h⁻¹Qh}(E)`**:
under `lineH2Equiv`, `locallyInnerAt` is `lineLocallyInner N h n`. -/
theorem mem_locallyInnerAt_iff_lineLocallyInner (hN : 3 ≤ N)
    (x : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel (levelPrincipal N) (lineFlagAt h))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerAt (rationalCoefficientComponent n character) (levelPrincipal N)
        (lineFlagAt h) ↔
      lineH2Equiv N h3 h n character hN x ∈ lineLocallyInner N h n := by
  rw [lineLocallyInner_eq_iInf]
  simp only [locallyInnerAt, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  constructor
  · intro H F
    obtain ⟨e, he, hK⟩ := exists_edge_of_frame_line N h F
    have h1 := (res_zero_iff_lineStab N h3 h n character hN e he x).mp (H e he)
    exact (res_congr _ hK _).mp h1
  · intro H e he
    obtain ⟨F, hF⟩ := exists_frame_of_edge_line N h e he
    exact (res_zero_iff_lineStab N h3 h n character hN e he x).mpr
      ((res_congr _ hF _).mpr (H F))

/-- **Level descent at every line cusp.**  For `N ≥ 3` with `3 ∣ N`, an integral change of basis `h` and a class `x` of the homogeneous
`H²` of the stabilizer `Γ_F` of the line `F = h⁻¹ℚe₁` in the level group: `x` is locally inner iff its restriction to `Γ_F ∩ Γ(N)`,
read in Mathlib's `H²` of the line group, lies in `lineFaceCuspidalInH2 N h n`, the image of the mixed cuspidal group
`𝒞_{h⁻¹Qh}(E)`. -/
theorem locallyInnerClasses_lineFlag_iff (hN : 3 ≤ N)
    (x : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel rationalLevel (lineFlagAt h))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerClasses n character .line (lineFlagAt h) ↔
      lineH2Equiv N h3 h n character hN
        (resPrincipal N (lineFlagAt h) (rationalCoefficientComponent n character) x) ∈
        lineFaceCuspidalInH2 N h n := by
  rw [locallyInnerClasses_level_descent N n character (lineFlagAt h) x,
    mem_locallyInnerAt_iff_lineLocallyInner N h3 h n character hN,
    lineFaceCuspidalInH2_eq_locallyInner]

variable (hN : 3 ≤ N)

/-- **Transfer back at a line cusp.**  The transfer of Mathlib's `H²(Γ(N) ∩ h⁻¹Qh, E_n)` to the stabilizer `Γ_F` of the line in the level
group (read on the homogeneous side through `lineH2Equiv`). -/
def lineTransfer :
    groupCohomology.H2 (lineFaceRep N h n) →ₗ[ℂ]
      GeneralEisenstein.Homogeneous.H2 (fixedPointLevel rationalLevel (lineFlagAt h))
        (rationalCoefficientComponent n character) :=
  (trLevel (rationalCoefficientComponent n character) (levelPrincipal N) (levelPrincipal_le N)
    (levelPrincipal_norm N) (lineFlagAt h)).comp
    (lineH2Equiv N h3 h n character hN).symm.toLinearMap

/-- **`𝒞(Γ_F) = tr(𝒞(Γ(N)))` at a line cusp.**  A class of the face library's `H²(Γ_F, E)` is locally inner iff it is the transfer of an
element of `lineFaceCuspidalInH2 N h n`, the image of the mixed cuspidal group of the line group of `Γ(N)`. -/
theorem locallyInnerClasses_lineFlag_eq_transfer
    (x : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel rationalLevel (lineFlagAt h))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerClasses n character .line (lineFlagAt h) ↔
      ∃ y ∈ lineFaceCuspidalInH2 N h n, lineTransfer N h3 h n character hN y = x := by
  constructor
  · intro hx
    refine ⟨lineH2Equiv N h3 h n character hN
        (resPrincipal N (lineFlagAt h) (rationalCoefficientComponent n character) x),
      (locallyInnerClasses_lineFlag_iff N h3 h n character hN x).mp hx, ?_⟩
    change trLevel (rationalCoefficientComponent n character) (levelPrincipal N)
      (levelPrincipal_le N) (levelPrincipal_norm N) (lineFlagAt h)
      ((lineH2Equiv N h3 h n character hN).symm (lineH2Equiv N h3 h n character hN _)) = x
    rw [LinearEquiv.symm_apply_apply]
    exact trLevel_resH2 _ _ _ _ _ x
  · rintro ⟨y, hy, rfl⟩
    rw [locallyInnerClasses_eq]
    have hy' : (lineH2Equiv N h3 h n character hN).symm y ∈
        locallyInnerAt (rationalCoefficientComponent n character) (levelPrincipal N)
          (lineFlagAt h) := by
      rw [mem_locallyInnerAt_iff_lineLocallyInner N h3 h n character hN,
        LinearEquiv.apply_symm_apply, ← lineFaceCuspidalInH2_eq_locallyInner]
      exact hy
    exact trH2_mem_locallyInnerAt _ (levelPrincipal N) (levelPrincipal_le N)
      (levelPrincipal_norm N) (lineFlagAt h) _ hy'

/-- **`𝒞(Γ) = 𝒞(Γ(N))^{invariants}` at every line cusp.**  A class `y` of Mathlib's `H²(Γ(N) ∩ h⁻¹Qh, E_n)` is the restriction of a
locally inner class of the level group iff it lies in `lineFaceCuspidalInH2 N h n` and is invariant under conjugation by the stabilizer
`Γ_F` of the line in the level group (read on the homogeneous side through `lineH2Equiv`). -/
theorem mem_map_locallyInnerClasses_lineFlag_iff
    (y : groupCohomology.H2 (lineFaceRep N h n)) :
    y ∈ Submodule.map
        ((lineH2Equiv N h3 h n character hN).toLinearMap ∘ₗ
          resPrincipal N (lineFlagAt h) (rationalCoefficientComponent n character))
        (locallyInnerClasses n character .line (lineFlagAt h)) ↔
      y ∈ lineFaceCuspidalInH2 N h n ∧
        (lineH2Equiv N h3 h n character hN).symm y ∈
          LevelTransfer.invariantsH2 (rationalCoefficientComponent n character)
            (fixedPointLevel_hnorm (levelPrincipal N) (levelPrincipal_norm N) (lineFlagAt h)) := by
  have hmap := map_locallyInnerClasses_eq N n character (lineFlagAt h)
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (locallyInnerClasses_lineFlag_iff N h3 h n character hN x).mp hx
    · have : resPrincipal N (lineFlagAt h) (rationalCoefficientComponent n character) x ∈
          Submodule.map (resPrincipal N (lineFlagAt h) (rationalCoefficientComponent n character))
            (locallyInnerClasses n character .line (lineFlagAt h)) := ⟨x, hx, rfl⟩
      rw [hmap] at this
      simpa using this.2
  · rintro ⟨hy, hinv⟩
    set z := (lineH2Equiv N h3 h n character hN).symm y with hz
    have hzLI : z ∈ locallyInnerAt (rationalCoefficientComponent n character) (levelPrincipal N)
        (lineFlagAt h) := by
      rw [mem_locallyInnerAt_iff_lineLocallyInner N h3 h n character hN, hz,
        LinearEquiv.apply_symm_apply, ← lineFaceCuspidalInH2_eq_locallyInner]
      exact hy
    have hmem : z ∈ Submodule.map (resPrincipal N (lineFlagAt h)
        (rationalCoefficientComponent n character))
        (locallyInnerClasses n character .line (lineFlagAt h)) := by
      rw [hmap]; exact ⟨hzLI, hinv⟩
    obtain ⟨x, hx, hxz⟩ := hmem
    refine ⟨x, hx, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hxz, hz, LinearEquiv.apply_symm_apply]

end Descent

end TernaryPeriodPolynomials.Argument.GammaNFacesFull
