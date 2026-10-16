module

/-
SPDX-License-Identifier: Apache-2.0
Adapted from akopjan/HamSandwich.
Original module: HamSandwich.SphereOddDegree.AlgebraicTopology.AffineLastFaceIdentity
Ported to the Lean 4.33.0.
-/
public import TernaryPeriodPolynomials.Topology.SingularHomology.AffineBarycentricSubdivision

@[expose] public section

/-!
# Last-face affine identity for barycentric subdivision

This file isolates the affine part of the last-face calculation in the proof
that barycentric subdivision commutes with the singular boundary.

The theorem is stated in a face-data form.  Suppose

* `π : Equiv.Perm (Fin (n+2))` is a top-dimensional subdivision summand;
* `ι : Fin (n+1) -> Fin (n+2)` is the vertex inclusion of the codimension-one
  face missing the last vertex `π last`;
* `ρ : Equiv.Perm (Fin (n+1))` is the induced permutation on that face;
* `ι (ρ t) = π (Fin.castSucc t)` for every `t`.

Then the restriction of the affine subdivision map for `π` to the final domain
face is the inclusion of the affine subdivision map for `ρ` on the boundary
face.

This deliberately avoids fixing the project's eventual coface-map API.  Later,
one instantiates `ι` with the ordinary order-preserving injection missing
`π last`, and `ρ` with the induced ordering of the remaining vertices.
-/

open scoped BigOperators
open Finset Convexity

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-
Compatibility of prefix barycenters with the last-face boundary data.

If the first `n+1` values of `π` factor through a face inclusion `ι` by an
induced permutation `ρ`, then the `k`-th prefix barycenter of the
`π`-subdivision of `Δ^(n+1)` is the image under `ι` of the corresponding
`k`-th prefix barycenter of the `ρ`-subdivision of the boundary `Δ^n`.
-/
theorem prefixBarycenter_castSucc_eq_map_of_prefix {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2)))
    (ι : Fin (n + 1) → Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hιρ : ∀ t : Fin (n + 1), ι (ρ t) = π (Fin.castSucc t))
    (k : Fin (n + 1)) :
    prefixBarycenter (n + 1) π (Fin.castSucc k)
      = StdSimplex.map ι (prefixBarycenter n ρ k) := by
  classical
  -- By definition of `prefixVertex`, we can rewrite the left-hand side using the hypothesis `hιρ`.
  have h_prefixVertex : prefixVertex (n + 1) π (Fin.castSucc k) = fun i => ι (ρ ⟨i.val, by
    exact lt_of_lt_of_le i.2 ( Nat.succ_le_of_lt k.2 )⟩) := by
    ext i; simp +decide [ prefixVertex, hιρ ] ;
  rw [prefixBarycenter, prefixBarycenter, h_prefixVertex, StdSimplex.map_map]
  rfl

/-
Last-face affine identity, in coordinate-face form.

Let `x : Δ^(n+1)` lie on the final domain face, so its last coordinate is zero.
Let `y : Δ^n` be the point obtained by deleting that last coordinate, expressed
here by the coordinate equality `hy`.

Under face data `(ι,ρ)` satisfying `ι (ρ t) = π (Fin.castSucc t)`, the affine
subdivision map for `π` on `x` equals the face inclusion `ι` applied to the
affine subdivision map for `ρ` on `y`.
-/
theorem affineSubdiv_face_last_eq_boundary_subdiv_of_faceData {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2)))
    (ι : Fin (n + 1) → Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hιρ : ∀ t : Fin (n + 1), ι (ρ t) = π (Fin.castSucc t))
    (x : Delta (n + 1)) (y : Delta n)
    (hxlast : x.weights ⟨n + 1, by omega⟩ = 0)
    (hy : ∀ k : Fin (n + 1), y.weights k = x.weights (Fin.castSucc k)) :
    affineSubdivMap (n + 1) π x
      = StdSimplex.map ι (affineSubdivMap n ρ y) := by
  classical
  ext j
  rw [affineSubdivMap_apply, weights_map_apply, Fin.sum_univ_castSucc]
  have hlast : x.weights (Fin.last (n + 1)) = 0 := hxlast
  rw [hlast, zero_mul, add_zero]
  simp_rw [affineSubdivMap_apply, prefixBarycenter_castSucc_eq_map_of_prefix π ι ρ hιρ,
    weights_map_apply, ← hy, Finset.mul_sum]
  exact Finset.sum_comm

/-- A slightly shorter alias for the last-face affine identity. -/
theorem affineSubdiv_face_last_eq_boundary_subdiv {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2)))
    (ι : Fin (n + 1) → Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hιρ : ∀ t : Fin (n + 1), ι (ρ t) = π (Fin.castSucc t))
    (x : Delta (n + 1)) (y : Delta n)
    (hxlast : x.weights ⟨n + 1, by omega⟩ = 0)
    (hy : ∀ k : Fin (n + 1), y.weights k = x.weights (Fin.castSucc k)) :
    affineSubdivMap (n + 1) π x
      = StdSimplex.map ι (affineSubdivMap n ρ y) :=
  affineSubdiv_face_last_eq_boundary_subdiv_of_faceData π ι ρ hιρ x y hxlast hy

end AffineBarycentricSubdivision
end SphereOddDegree