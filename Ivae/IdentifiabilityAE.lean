/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Ivae.Basic

/-!
# Almost-everywhere affine relations

These are explicitly measure-relative variants, not replacements for paper
Definition 2. The same supplied measure is kept fixed when composing relations.
No observation law, pivot law, or ambient Lebesgue measure is chosen here.
-/

namespace IVAE

open MeasureTheory

/-- An a.e. affine relation with a general, possibly singular, linear map. -/
def SimAE {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    (μ : Measure X) (θ θ' : Params n d m k Z X) : Prop :=
  ∃ A : StatSpace n k →ₗ[ℝ] StatSpace n k,
  ∃ c : StatSpace n k,
    ∀ᵐ x ∂μ, latentStat θ x = A (latentStat θ' x) + c

/-- The measure-relative invertible affine relation `~A^{ae}`. -/
def SimAAE {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    (μ : Measure X) (θ θ' : Params n d m k Z X) : Prop :=
  ∃ A : StatSpace n k ≃ₗ[ℝ] StatSpace n k,
  ∃ c : StatSpace n k,
    ∀ᵐ x ∂μ, latentStat θ x = A (latentStat θ' x) + c

/-- The defining statement of the measure-relative relation `SimAE`. -/
theorem simAE_iff {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    (μ : Measure X) (θ θ' : Params n d m k Z X) :
    SimAE μ θ θ' ↔ ∃ A : StatSpace n k →ₗ[ℝ] StatSpace n k,
      ∃ c : StatSpace n k, ∀ᵐ x ∂μ, latentStat θ x = A (latentStat θ' x) + c :=
  Iff.rfl

theorem simAAE_simAE {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    {μ : Measure X} {θ θ' : Params n d m k Z X} (h : SimAAE μ θ θ') :
    SimAE μ θ θ' := by
  rcases h with ⟨A, c, h⟩
  exact ⟨A.toLinearMap, c, h⟩

theorem simAE_refl {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    (μ : Measure X) (θ : Params n d m k Z X) : SimAE μ θ θ := by
  refine ⟨LinearMap.id, 0, ?_⟩
  exact ae_of_all μ (fun x => by simp)

/-- Singular maps can be composed; symmetry is deliberately not asserted for `SimAE`. -/
theorem simAE_trans {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    {μ : Measure X} {θ₁ θ₂ θ₃ : Params n d m k Z X}
    (h₁₂ : SimAE μ θ₁ θ₂) (h₂₃ : SimAE μ θ₂ θ₃) : SimAE μ θ₁ θ₃ := by
  rcases h₁₂ with ⟨A, c, hA⟩
  rcases h₂₃ with ⟨B, e, hB⟩
  refine ⟨A.comp B, A e + c, ?_⟩
  filter_upwards [hA, hB] with x hxA hxB
  rw [hxA, hxB, map_add]
  simp only [LinearMap.comp_apply]
  abel

theorem simAAE_refl {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    (μ : Measure X) (θ : Params n d m k Z X) : SimAAE μ θ θ := by
  refine ⟨LinearEquiv.refl ℝ (StatSpace n k), 0, ?_⟩
  exact ae_of_all μ (fun x => by simp)

theorem simAAE_symm {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    {μ : Measure X} {θ θ' : Params n d m k Z X} (h : SimAAE μ θ θ') :
    SimAAE μ θ' θ := by
  rcases h with ⟨A, c, hA⟩
  refine ⟨A.symm, -A.symm c, ?_⟩
  filter_upwards [hA] with x hx
  have hinv : A.symm (latentStat θ x) = latentStat θ' x + A.symm c := by
    rw [hx, map_add, A.symm_apply_apply]
  rw [hinv]
  abel

theorem simAAE_trans {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    {μ : Measure X} {θ₁ θ₂ θ₃ : Params n d m k Z X}
    (h₁₂ : SimAAE μ θ₁ θ₂) (h₂₃ : SimAAE μ θ₂ θ₃) :
    SimAAE μ θ₁ θ₃ := by
  rcases h₁₂ with ⟨A, c, hA⟩
  rcases h₂₃ with ⟨B, e, hB⟩
  refine ⟨B.trans A, A e + c, ?_⟩
  -- Intersect the two full-measure sets; the reference measure stays fixed.
  filter_upwards [hA, hB] with x hxA hxB
  rw [hxA, hxB, map_add]
  simp only [LinearEquiv.trans_apply]
  abel

/-- The a.e. invertible affine relation is an equivalence for every fixed μ. -/
theorem simAAE_equivalence {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    (μ : Measure X) :
    Equivalence (SimAAE (n := n) (d := d) (m := m) (k := k) (Z := Z) (X := X) μ) :=
  ⟨simAAE_refl μ, simAAE_symm, simAAE_trans⟩

end IVAE
