/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Ivae.Basic

/-!
# Measure transport for the almost-everywhere theorem

Latent Lebesgue measure is restricted to the domain subtype. Weighting
commutes with a measurable equivalence from the latent domain to its image;
this is used to transport the conditional density ratio to the image law.
-/

namespace IVAE
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Ambient Lebesgue measure transported to the domain subtype. -/
def domainVolume {n : ℕ} (S : Set (Vec n)) : Measure S :=
  Measure.comap Subtype.val volume

/-- Weighting commutes with transport by a measurable equivalence. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (p : β → ℝ≥0∞) :
    (μ.withDensity (fun x => p (e x))).map e = (μ.map e).withDensity p := by
  ext A hA
  rw [Measure.map_apply e.measurable hA, withDensity_apply _ (e.measurable hA),
    withDensity_apply _ hA, e.measurableEmbedding.restrict_map,
    e.measurableEmbedding.lintegral_map]

end
end IVAE
