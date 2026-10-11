/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Ivae.IdentifiabilityAE

/-!
# Corrected Theorem 1, Step III

The explicit, approved extra assumption is essential affine nondegeneracy
under the actual pivot prior. Linear functionals represent dot products with
coefficient vectors. No differentiating of an a.e. equality is used.
-/

namespace IVAE
open MeasureTheory
noncomputable section

/-- No nonzero linear functional of the statistic is constant almost surely. -/
def AEAffineNondegenerate {α E : Type*} [MeasurableSpace α]
    [AddCommGroup E] [Module ℝ E] (μ : Measure α) (t : α → E) : Prop :=
  ∀ (ℓ : E →ₗ[ℝ] ℝ) (b : ℝ), (∀ᵐ x ∂μ, ℓ (t x) = b) → ℓ = 0

/-- Coordinate form of a linear functional, used to match the mathematical statement. -/
theorem linearFunctional_eq_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (w : ι → ℝ) :
    ℓ w = dotProduct (fun i => ℓ (Pi.single i 1)) w := by
  have hw : w = ∑ i, w i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum, dotProduct, mul_comm]

/-- The definition is exactly the approved coefficient-vector formulation. -/
theorem aeAffineNondegenerate_iff_dotProduct {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) (t : α → ι → ℝ) :
    AEAffineNondegenerate μ t ↔
      ∀ (v : ι → ℝ) (b : ℝ), (∀ᵐ x ∂μ, dotProduct v (t x) = b) → v = 0 := by
  classical
  constructor
  · intro h v b hv
    let ℓ : (ι → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := dotProduct v
        map_add' := fun x y => dotProduct_add v x y
        map_smul' := fun a x => by simp [dotProduct, Finset.mul_sum, mul_left_comm] }
    have hℓ := h ℓ b hv
    funext i
    have hi := congrArg (fun f : (ι → ℝ) →ₗ[ℝ] ℝ => f (Pi.single i 1)) hℓ
    simpa [ℓ] using hi
  · intro h ℓ b hℓ
    have hv : (fun i => ℓ (Pi.single i 1)) = 0 := h _ b (by
      filter_upwards [hℓ] with x hx
      rw [← linearFunctional_eq_dotProduct]
      exact hx)
    apply LinearMap.ext
    intro w
    rw [linearFunctional_eq_dotProduct ℓ w, hv, zero_dotProduct]
    rfl

/-- Step III: the very same affine witness is bijective. -/
theorem affineWitness_bijective {α E : Type*} [MeasurableSpace α]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {μ : Measure α} {t t' : α → E} (hnd : AEAffineNondegenerate μ t)
    (A : E →ₗ[ℝ] E) (c : E) (h : ∀ᵐ x ∂μ, t x = A (t' x) + c) :
    Function.Bijective A := by
  have hsurj : Function.Surjective A := by
    apply LinearMap.dualMap_injective_iff.mp
    apply (LinearMap.ker_eq_bot).mp
    apply (LinearMap.ker_eq_bot').mpr
    intro ℓ hℓ
    apply hnd ℓ (ℓ c)
    filter_upwards [h] with x hx
    rw [hx, map_add]
    have hz : ℓ (A (t' x)) = 0 := congrArg (fun f : E →ₗ[ℝ] ℝ => f (t' x)) hℓ
    rw [hz, zero_add]
  exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

/-- Essential affine nondegeneracy upgrades an a.e. relation to invertible equivalence. -/
theorem simAAE_of_simAE_of_nondegenerate {n d m k : ℕ}
    {Z : Set (Vec n)} {X : Set (Vec d)} {θ θ' : Params n d m k Z X}
    {μ : Measure X} (hnd : AEAffineNondegenerate μ (latentStat θ))
    (h : SimAE μ θ θ') : SimAAE μ θ θ' := by
  rcases h with ⟨A, c, h⟩
  exact ⟨LinearEquiv.ofBijective A (affineWitness_bijective hnd A c h), c, h⟩

/-- Once obtained at the pivot law, equivalence transfers to every dominated measure. -/
theorem simAAE_of_absolutelyContinuous {n d m k : ℕ}
    {Z : Set (Vec n)} {X : Set (Vec d)} {θ θ' : Params n d m k Z X}
    {μ σ : Measure X} (hμ : μ ≪ σ) (h : SimAAE σ θ θ') : SimAAE μ θ θ' := by
  rcases h with ⟨A, c, h⟩
  exact ⟨A, c, hμ.ae_le h⟩

end
end IVAE
