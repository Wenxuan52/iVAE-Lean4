/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Ivae.Basic

/-!
# Theorem 1: the finite auxiliary variation system

The true model supplies nk+1 distinct auxiliary values. Only its variation
matrix L is assumed nonsingular; invertibility of the affine witness is
proved separately in Step III.
-/

namespace IVAE

/-- The nk-by-nk matrix L; columns are the differences from the pivot u₀. -/
def auxiliaryVariationMatrix {n d m k : ℕ} (θ : RawParams n d m k)
    (u₀ : Vec m) (points : StatIdx n k → Vec m) : Matrix (StatIdx n k) (StatIdx n k) ℝ :=
  Matrix.of (fun row col => lambdaVec θ (points col) row - lambdaVec θ u₀ row)

/--
Theorem 1 (iv), with general n,m,k. `none` indexes u₀ and `some ij` indexes
the other nk points. The matrix L is required nonsingular; no condition on
the future affine witness A is assumed or proved.
-/
structure AuxiliaryVariation {n d m k : ℕ} (θ : RawParams n d m k) (U : Set (Vec m)) where
  pivot : U
  points : StatIdx n k → U
  distinct : Function.Injective (fun t : Option (StatIdx n k) =>
    (t.elim pivot points).1)
  det_ne_zero : (auxiliaryVariationMatrix θ pivot.1 (fun ij => (points ij).1)).det ≠ 0

/-- The auxiliary-point representation really has nk+1 indices. -/
theorem auxiliaryPointIndex_card (n k : ℕ) :
    Fintype.card (Option (StatIdx n k)) = n * k + 1 := by
  simp [StatIdx]

namespace AuxiliaryVariation

variable {n d m k : ℕ} {θ : RawParams n d m k} {U : Set (Vec m)}

/-- The pivot and nk remaining auxiliary values, indexed by a finite type. -/
def selected (V : AuxiliaryVariation θ U) (r : Option (StatIdx n k)) : U :=
  r.elim V.pivot V.points

@[simp] theorem selected_none (V : AuxiliaryVariation θ U) : V.selected none = V.pivot := rfl

@[simp] theorem selected_some (V : AuxiliaryVariation θ U) (r : StatIdx n k) :
    V.selected (some r) = V.points r := rfl

end AuxiliaryVariation

end IVAE
