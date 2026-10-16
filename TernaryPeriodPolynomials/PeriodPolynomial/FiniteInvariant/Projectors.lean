module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodNormMap

@[expose] public section

noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant

@[simp] theorem swap_swap (d : ℕ) (q : H d) : swap d (swap d q)=q :=
  LinearMap.congr_fun (swap_sq d) q

@[simp] theorem negateFirst_negateFirst (d : ℕ) (q : H d) : negateFirst d (negateFirst d q)=q :=
  LinearMap.congr_fun (negateFirst_sq d) q

@[simp] theorem rotation_rotation_rotation (d : ℕ) (q : H d) :
    rotation d (rotation d (rotation d q))=q := LinearMap.congr_fun (rotation_cube d) q

theorem negateFirst_swap (d : ℕ) (hd : Even d) (q : H d) :
    negateFirst d (swap d q)=swap d (negateFirst d q) :=
  (LinearMap.congr_fun (swap_negateFirst_comm d hd) q).symm

/-- The actual two-involution averaging projector onto symmetric separately odd polynomials. -/
def oddProjector (d : ℕ) : Module.End ℚ (H d) :=
  (1/4 : ℚ) • ((1+swap d)*(1-negateFirst d))

/-- The literal six-term finite-group average. -/
def invariantProjector (d : ℕ) : Module.End ℚ (H d) :=
  (1/6 : ℚ) • ((1+swap d)*norm d)

theorem oddProjector_apply (d : ℕ) (q : H d) :
    oddProjector d q = (1/4 : ℚ) • (q + swap d q - negateFirst d q - swap d (negateFirst d q)) := by
  simp only [oddProjector,LinearMap.smul_apply,Module.End.mul_apply,LinearMap.add_apply,
    LinearMap.sub_apply,Module.End.one_apply,map_sub]
  module

theorem invariantProjector_apply (d : ℕ) (q : H d) :
    invariantProjector d q = (1/6 : ℚ) • (norm d q + swap d (norm d q)) := rfl

/-- The first average has precisely the claimed range, on every even homogeneous degree. -/
theorem oddProjector_isProj (d : ℕ) (hd : Even d) : LinearMap.IsProj (oddSymmetric d) (oddProjector d) := by
  constructor
  · intro q
    constructor
    · simp only [oddProjector_apply,map_smul,map_sub,map_add,swap_swap]
      module
    · simp only [oddProjector_apply,map_smul,map_sub,map_add,negateFirst_swap d hd,
        negateFirst_negateFirst]
      module
  · intro q hq
    rcases hq with ⟨hs,hn⟩
    rw [oddProjector_apply,hs,hn,map_neg,hs]
    module

/-- The full finite-group average has precisely the simultaneous invariant range. -/
theorem invariantProjector_isProj (d : ℕ) : LinearMap.IsProj (invariants d) (invariantProjector d) := by
  constructor
  · intro q
    have hn : rotation d (norm d q)=norm d q := LinearMap.congr_fun (rotation_norm d) q
    have hsn : rotation d (swap d (norm d q))=swap d (norm d q) := by
      have hrel : rotation d * swap d = swap d * (rotation d * rotation d) :=
        (swap_rotation_sq d).symm
      change (rotation d * swap d) (norm d q)=_
      rw [hrel]
      change swap d (rotation d (rotation d (norm d q)))=_
      rw [hn,hn]
    constructor
    · simp only [invariantProjector_apply,map_smul,map_add,swap_swap]
      module
    · simp only [invariantProjector_apply,map_smul,map_add,hn,hsn]
  · intro q hq
    rcases hq with ⟨hs,ha⟩
    simp only [invariantProjector_apply,norm_apply,ha,map_add,hs]
    module

end TernaryPoly.BinaryFiniteInvariant
