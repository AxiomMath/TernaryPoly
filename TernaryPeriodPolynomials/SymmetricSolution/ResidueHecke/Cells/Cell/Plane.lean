module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Tuple
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.PHLevi
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Setup

@[expose] public section


/-!
# Lemma B.1, boundary route: the plane `x₀ = 0` and the action of `P_H`

`pl y` is the line `(0, y₀, y₁)` of the plane `Π = {x₀ = 0}`, `wl u` the line `(1, u₀, u₁)` and `e₀Line` the line
of the first basis vector.  An element `g ∈ P_H` with block `C` acts on `Π` by `C` (`PH_smul_pl`) and sends `e₀` to a
line `(1, λ u)` that is a radical translate of `e₀` (`PH_smul_e0`); the radical `U` fixes every line of `Π`.
In the `U`-coinvariants `Φ(RG_n)`, the class of an ordered cell `(e₀, m)` with `m ⊂ Π` is therefore transported
by `g` to the class of `(e₀, C m)` (`phi_twist_cons_e0`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

/-- The line `(0, y₀, y₁)` of the plane `x₀ = 0`. -/
def pl (y : Fin 2 → ℤ) : Line := Line.mk ![0, y 0, y 1]

/-- The line `(1, u₀, u₁)`. -/
def wl (u : Fin 2 → ℤ) : Line := Line.mk ![1, u 0, u 1]

theorem pl_eq_iff (y y' : Fin 2 → ℤ) : pl y = pl y' ↔ y' = y ∨ y' = -y := by
  unfold pl
  rw [Line.mk_eq_mk]
  constructor
  · rintro (h | h)
    · left; funext i; fin_cases i
      · exact congrFun h 1
      · exact congrFun h 2
    · right; funext i; fin_cases i
      · exact congrFun h 1
      · exact congrFun h 2
  · rintro (h | h)
    · left; funext i; fin_cases i
      · simp
      · simpa using congrFun h 0
      · simpa using congrFun h 1
    · right; funext i; fin_cases i
      · simp
      · simpa using congrFun h 0
      · simpa using congrFun h 1

theorem mv_PH (g : PH) (x : Vec) :
    mv g.1 x = ![(lamHom g : ℤ) * x 0, uvec g 0 * x 0 + (pi g).val 0 0 * x 1 + (pi g).val 0 1 * x 2,
      uvec g 1 * x 0 + (pi g).val 1 0 * x 1 + (pi g).val 1 1 * x 2] := by
  unfold mv
  rw [PH_matrix g]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- An element of `P_H` acts on the plane `x₀ = 0` through its block. -/
theorem PH_smul_pl (g : PH) (y : Fin 2 → ℤ) : g.1 • pl y = pl ((pi g).val.mulVec y) := by
  unfold pl
  rw [smul_mk, mv_PH]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The image of `e₀` under `g ∈ P_H` is a radical translate of `e₀`. -/
theorem PH_smul_e0 (g : PH) :
    g.1 • Line.mk ![1, 0, 0] = wl (fun i => (lamHom g : ℤ) * uvec g i) := by
  unfold wl
  rw [smul_mk, mv_PH]
  rcases lam_cases g with h | h
  · congr 1
    funext i
    fin_cases i <;> simp [h]
  · rw [Line.mk_eq_mk]
    right
    funext i
    fin_cases i <;> simp [h]

theorem mv_radZ (w : Fin 2 → ℤ) (x : Vec) :
    mv (radZ w) x = ![x 0, w 0 * x 0 + x 1, w 1 * x 0 + x 2] := by
  unfold mv
  rw [radZ_val]
  funext i
  fin_cases i <;> simp [radMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem radZ_smul_pl (w : Fin 2 → ℤ) (y : Fin 2 → ℤ) : radZ w • pl y = pl y := by
  unfold pl
  rw [smul_mk, mv_radZ]
  congr 1
  funext i
  fin_cases i <;> simp

theorem radZ_smul_wl (w u : Fin 2 → ℤ) : radZ w • wl u = wl (w + u) := by
  unfold wl
  rw [smul_mk, mv_radZ]
  congr 1
  funext i
  fin_cases i <;> simp

theorem wl_zero : wl 0 = Line.mk ![1, 0, 0] := by
  unfold wl
  congr 1

/-- The `(P_H ⧸ U)`-representation `Φ(RG_n)`. -/
abbrev RGXph (n : ℕ) : Rep.{0} ℚ PH := (Rep.resFunctor PH.subtype).obj (RGX n)

/-- `Φ(RG_n)`. -/
abbrev PhiX (n : ℕ) : Rep.{0} ℚ (PH ⧸ U) := (TernaryPeriodPolynomials.Argument.HochschildSerre.Phi U).obj (RGXph n)

/-- The class of a chain in the `U`-coinvariants. -/
def clsU (n : ℕ) (v : Graded n →₀ ℚ) : (PhiX n).V :=
  Representation.Coinvariants.mk ((RGXph n).ρ.comp U.subtype) v

theorem clsU_add (n : ℕ) (v w : Graded n →₀ ℚ) : clsU n (v + w) = clsU n v + clsU n w :=
  map_add (Representation.Coinvariants.mk ((RGXph n).ρ.comp U.subtype)) v w

theorem clsU_smul (n : ℕ) (a : ℚ) (v : Graded n →₀ ℚ) : clsU n (a • v) = a • clsU n v :=
  map_smul (Representation.Coinvariants.mk ((RGXph n).ρ.comp U.subtype)) a v

theorem clsU_zero (n : ℕ) : clsU n 0 = 0 :=
  map_zero (Representation.Coinvariants.mk ((RGXph n).ρ.comp U.subtype))

theorem clsU_sum (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → Graded n →₀ ℚ) :
    clsU n (∑ i ∈ s, f i) = ∑ i ∈ s, clsU n (f i) :=
  map_sum (Representation.Coinvariants.mk ((RGXph n).ρ.comp U.subtype)) f s

/-- The quotient group acts on `Φ(RG_n)` through the twisted action. -/
theorem phi_act (n : ℕ) (g : PH) (v : Graded n →₀ ℚ) :
    (PhiX n).ρ (QuotientGroup.mk g) (clsU n v) = clsU n (twistLin n g.1 v) := rfl

/-- The radical acts trivially on `Φ(RG_n)`. -/
theorem clsU_radZ (n : ℕ) (w : Fin 2 → ℤ) (x : Graded n →₀ ℚ) :
    clsU n (twistLin n (radZ w) x) = clsU n x :=
  Representation.Coinvariants.mk_self_apply ((RGXph n).ρ.comp U.subtype)
    (eU (Multiplicative.ofAdd w)) x

/-- The image of `Φ(d)` on classes. -/
theorem phi_d (n : ℕ) (v : Graded (n + 1) →₀ ℚ) :
    ((TernaryPeriodPolynomials.Argument.HochschildSerre.Phi U).map
      ((Rep.resFunctor PH.subtype).map (dRG n))).hom (clsU (n + 1) v) = clsU n (dLin n v) := rfl

/-- The line of the first basis vector. -/
def e0L : Line := Line.mk ![1, 0, 0]

theorem e0L_eq : e0L = wl 0 := wl_zero.symm

theorem smul_cons {k : ℕ} (g : IntegralGL3) (a : Line) (m : Fin k → Line) :
    (fun i => g • (Fin.cons a m : Fin (k + 1) → Line) i) =
      (Fin.cons (g • a) (fun i => g • m i) : Fin (k + 1) → Line) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- **Transport in `Φ`**: `g ∈ P_H` sends the class of `(e₀, m)` (with `m` in the plane) to the class of `(e₀, g m)`. -/
theorem phi_twist_cons_e0 (g : PH) {n k : ℕ} (m : Fin k → Line) (hm : ∀ i, ∃ y, m i = pl y)
    (h : TupleOK n (Fin.cons e0L m : Fin (k + 1) → Line)) :
    (PhiX n).ρ (QuotientGroup.mk g) (clsU n (tupleVec n (Fin.cons e0L m : Fin (k + 1) → Line))) =
      clsU n (tupleVec n (Fin.cons e0L (fun i => g.1 • m i) : Fin (k + 1) → Line)) := by
  rw [phi_act, tupleVec_twist h g.1, smul_cons]
  set v : Fin 2 → ℤ := fun i => (lamHom g : ℤ) * uvec g i with hv
  have hge : g.1 • e0L = radZ v • e0L := by
    change g.1 • Line.mk ![1, 0, 0] = radZ v • Line.mk ![1, 0, 0]
    rw [PH_smul_e0, ← wl_zero, radZ_smul_wl, add_zero]
  have hfix : ∀ i, radZ v • (g.1 • m i) = g.1 • m i := by
    intro i
    obtain ⟨y, hy⟩ := hm i
    rw [hy, PH_smul_pl, radZ_smul_pl]
  have hok : TupleOK n (Fin.cons (g.1 • e0L) (fun i => g.1 • m i) : Fin (k + 1) → Line) := by
    have := h.smul g.1
    rwa [smul_cons] at this
  set A : Fin (k + 1) → Line := Fin.cons e0L (fun i => g.1 • m i) with hA
  have hB : ∀ i, (Fin.cons (g.1 • e0L) (fun i => g.1 • m i) : Fin (k + 1) → Line) i = radZ v • A i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hA, hge]
    · simp [hA, hfix]
  have hBeq : (Fin.cons (g.1 • e0L) (fun i => g.1 • m i) : Fin (k + 1) → Line) = fun i => radZ v • A i :=
    funext hB
  have hokA : TupleOK n A := by
    have h2 := hok.smul (radZ v)⁻¹
    have : (fun i => (radZ v)⁻¹ • (Fin.cons (g.1 • e0L) (fun i => g.1 • m i) : Fin (k + 1) → Line) i) = A := by
      funext i
      rw [hB i, inv_smul_smul]
    rwa [this] at h2
  rw [hBeq, ← tupleVec_twist hokA (radZ v), clsU_radZ]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
