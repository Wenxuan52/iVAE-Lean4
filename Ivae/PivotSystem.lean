/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Ivae.AuxiliaryVariation
import Ivae.IdentifiabilityAE

/-!
# Theorem 1, Step II: solve the pivot system

Multiplying the a.e. finite-point equation by the inverse of Lᵀ produces
one fixed affine witness. Its invertibility is established in Step III.
-/

namespace IVAE
open MeasureTheory
open scoped Matrix
noncomputable section

/-- Step II: solve the finite-point equation; this does not prove A invertible. -/
theorem simAE_of_pivot_equation {n d m k : ℕ}
    {Z : Set (Vec n)} {X : Set (Vec d)} {θ θ' : Params n d m k Z X} (μ : Measure X)
    (L L' : Matrix (StatIdx n k) (StatIdx n k) ℝ) (b : StatSpace n k)
    (hL : L.det ≠ 0)
    (h : ∀ᵐ x ∂μ, L.transpose.mulVec (latentStat θ x) =
      L'.transpose.mulVec (latentStat θ' x) + b) : SimAE μ θ θ' := by
  classical
  refine ⟨(L.transpose⁻¹ * L'.transpose).mulVecLin, L.transpose⁻¹.mulVec b, ?_⟩
  filter_upwards [h] with x hx
  have hunit : IsUnit L.transpose.det := isUnit_iff_ne_zero.mpr (by simpa using hL)
  have hs := congrArg (fun v => L.transpose⁻¹.mulVec v) hx
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec] at hs
  exact hs

end
end IVAE
