/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Ivae.MeasureModel
import Ivae.PivotSystem
import Ivae.AffineNondegeneracy

/-!
# Corrected Theorem 1, Steps I–III on measurable images

The pivot measure is the true noiseless law at u₀. The conclusion reference
measure remains explicit, dominated by this law. This works for n < d as
well as n = d, without an ambient image density or an area formula.

Extra assumptions are explicit: measurable mixing and inverse, normalized
equation-(7) priors, full-frequency noise nonvanishing, and essential affine
nondegeneracy under the actual true pivot prior (approved 2026-10-04).
Nondegeneracy is NOT claimed to follow from the original paper's (iii).
No pointwise upgrade or proof of the original pointwise claim is asserted.
-/

namespace IVAE
open MeasureTheory
open scoped ENNReal Matrix
noncomputable section

namespace MeasureModel
variable {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)} {U : Set (Vec m)}
    {θ θ' : Params n d m k Z X}

/-- Equal laws and equal pivot laws identify their measurable density ratios a.e. -/
theorem imageRatio_ae_eq (M : MeasureModel θ U) (M' : MeasureModel θ' U) (u₀ u : U)
    (h₀ : M.imageLaw u₀ = M'.imageLaw u₀) (hu : M.imageLaw u = M'.imageLaw u) :
    M.imageRatio u₀ u =ᵐ[M.imageLaw u₀] M'.imageRatio u₀ u := by
  have hw : (M.imageLaw u₀).withDensity (fun x => ENNReal.ofReal (M.imageRatio u₀ u x)) =
      (M.imageLaw u₀).withDensity (fun x => ENNReal.ofReal (M'.imageRatio u₀ u x)) := by
    rw [M.imageLaw_ratio, h₀, M'.imageLaw_ratio, hu]
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (M.imageRatio_measurable u₀ u).ennreal_ofReal.aemeasurable
    (M'.imageRatio_measurable u₀ u).ennreal_ofReal.aemeasurable).mp hw
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff
    (M.latentRatio_nonneg u₀ u _) (M'.latentRatio_nonneg u₀ u _)).mp hx

/-- The finite pivot system, derived from actual laws via their density ratios. -/
theorem pivot_equation (M : MeasureModel θ U) (M' : MeasureModel θ' U)
    (V : AuxiliaryVariation θ.toRawParams U)
    (hlaw : ∀ r, M.imageLaw (V.selected r) = M'.imageLaw (V.selected r)) :
    ∀ᵐ x ∂M.imageLaw V.pivot,
      (auxiliaryVariationMatrix θ.toRawParams V.pivot.1
        (fun r => (V.points r).1)).transpose.mulVec (latentStat θ x) =
      (auxiliaryVariationMatrix θ'.toRawParams V.pivot.1
        (fun r => (V.points r).1)).transpose.mulVec (latentStat θ' x) +
      (fun r => (Real.log (M.normalizerProduct (V.points r)) -
        Real.log (M.normalizerProduct V.pivot)) -
        (Real.log (M'.normalizerProduct (V.points r)) -
        Real.log (M'.normalizerProduct V.pivot))) := by
  have h₀ : M.imageLaw V.pivot = M'.imageLaw V.pivot := hlaw none
  have hpoint (r : StatIdx n k) : ∀ᵐ x ∂M.imageLaw V.pivot,
      dotProduct (latentStat θ x)
          (lambdaVec θ.toRawParams (V.points r).1 - lambdaVec θ.toRawParams V.pivot.1) -
        (Real.log (M.normalizerProduct (V.points r)) - Real.log (M.normalizerProduct V.pivot)) =
      dotProduct (latentStat θ' x)
          (lambdaVec θ'.toRawParams (V.points r).1 - lambdaVec θ'.toRawParams V.pivot.1) -
        (Real.log (M'.normalizerProduct (V.points r)) -
          Real.log (M'.normalizerProduct V.pivot)) := by
    have hlog' := M'.log_imageRatio_ae V.pivot (V.points r)
    rw [← h₀] at hlog'
    filter_upwards [M.imageRatio_ae_eq M' V.pivot (V.points r) h₀ (hlaw (some r)),
      M.log_imageRatio_ae V.pivot (V.points r), hlog'] with x hx hxlog hxlog'
    rw [← hxlog, ← hxlog', hx]
  filter_upwards [ae_all_iff.mpr hpoint] with x hx
  funext r
  have hr := hx r
  change dotProduct (fun a => lambdaVec θ.toRawParams (V.points r).1 a -
      lambdaVec θ.toRawParams V.pivot.1 a) (latentStat θ x) =
    dotProduct (fun a => lambdaVec θ'.toRawParams (V.points r).1 a -
      lambdaVec θ'.toRawParams V.pivot.1 a) (latentStat θ' x) + _
  rw [dotProduct_comm _ (latentStat θ x), dotProduct_comm _ (latentStat θ' x)]
  have rearrange (a b c d : ℝ) (h : a - b = c - d) : a = c + (b - d) := by
    linarith
  exact rearrange _ _ _ _ hr

/-- Step II: a single fixed affine map on a common full-pivot-measure set. -/
theorem stepII (M : MeasureModel θ U) (M' : MeasureModel θ' U)
    (V : AuxiliaryVariation θ.toRawParams U)
    (hlaw : ∀ r, M.imageLaw (V.selected r) = M'.imageLaw (V.selected r)) :
    SimAE (M.imageLaw V.pivot) θ θ' :=
  simAE_of_pivot_equation _ _ _ _ V.det_ne_zero (M.pivot_equation M' V hlaw)

/-- Nondegeneracy is assumed at the true latent prior and transported, not re-assumed at X. -/
theorem image_nondegenerate (M : MeasureModel θ U) (u₀ : U)
    (hnd : AEAffineNondegenerate (M.priorLaw u₀) (fun z : Z => statVec θ.toRawParams z.1)) :
    AEAffineNondegenerate (M.imageLaw u₀) (latentStat θ) := by
  intro ℓ b h
  apply hnd ℓ b
  have h' := M.mixing.measurableEmbedding.ae_map_iff.mp h
  simpa [latentStat] using h'

/-- Steps II–III: invertibility is established at the full pivot law. -/
theorem stepII_III (M : MeasureModel θ U) (M' : MeasureModel θ' U)
    (V : AuxiliaryVariation θ.toRawParams U)
    (hnd : AEAffineNondegenerate (M.priorLaw V.pivot)
      (fun z : Z => statVec θ.toRawParams z.1))
    (hlaw : ∀ r, M.imageLaw (V.selected r) = M'.imageLaw (V.selected r)) :
    SimAAE (M.imageLaw V.pivot) θ θ' :=
  simAAE_of_simAE_of_nondegenerate (M.image_nondegenerate V.pivot hnd) (M.stepII M' V hlaw)

end MeasureModel

/--
Corrected Theorem 1, Steps I–III. The explicit additional hypothesis is
a.e. affine nondegeneracy under the TRUE pivot prior. Generic n,d,m,k;
in particular the theorem applies whenever n ≤ d. Only a.e. invertible
affine identifiability is concluded, never pointwise equality.
-/
theorem correctedTheorem1_stepI_II_III {n d m k : ℕ}
    {Z : Set (Vec n)} {X : Set (Vec d)} {U : Set (Vec m)}
    {θ θ' : Params n d m k Z X}
    (M : MeasureModel θ U) (M' : MeasureModel θ' U)
    (V : AuxiliaryVariation θ.toRawParams U)
    (hnd : AEAffineNondegenerate (M.priorLaw V.pivot)
      (fun z : Z => statVec θ.toRawParams z.1))
    (η : Measure (Vec d)) [IsFiniteMeasure η] (hη : FullFrequencyNoiseCondition η)
    (hobs : ∀ r, M.observationLaw η (V.selected r) = M'.observationLaw η (V.selected r))
    (μ : Measure X) (hμ : μ ≪ M.imageLaw V.pivot) : SimAAE μ θ θ' := by
  apply simAAE_of_absolutelyContinuous hμ
  apply M.stepII_III M' V hnd
  intro r
  exact M.imageLaw_eq_of_observationLaw_eq M' η hη _ (hobs r)

/-- The same witnesses work under every conditional noiseless law of either model. -/
theorem correctedTheorem1_all_conditional_laws {n d m k : ℕ}
    {Z : Set (Vec n)} {X : Set (Vec d)} {U : Set (Vec m)}
    {θ θ' : Params n d m k Z X}
    (M : MeasureModel θ U) (M' : MeasureModel θ' U)
    (V : AuxiliaryVariation θ.toRawParams U)
    (hnd : AEAffineNondegenerate (M.priorLaw V.pivot)
      (fun z : Z => statVec θ.toRawParams z.1))
    (η : Measure (Vec d)) [IsFiniteMeasure η] (hη : FullFrequencyNoiseCondition η)
    (hobs : ∀ r, M.observationLaw η (V.selected r) = M'.observationLaw η (V.selected r)) :
    ∃ A : StatSpace n k ≃ₗ[ℝ] StatSpace n k, ∃ c : StatSpace n k,
      (∀ᵐ x ∂M.imageLaw V.pivot, latentStat θ x = A (latentStat θ' x) + c) ∧
      (∀ u, ∀ᵐ x ∂M.imageLaw u, latentStat θ x = A (latentStat θ' x) + c) ∧
      (∀ u, ∀ᵐ x ∂M'.imageLaw u, latentStat θ x = A (latentStat θ' x) + c) := by
  obtain ⟨A, c, h⟩ := correctedTheorem1_stepI_II_III M M' V hnd η hη hobs
    (M.imageLaw V.pivot) Measure.AbsolutelyContinuous.rfl
  refine ⟨A, c, h, fun u => (M.imageLaw_absolutelyContinuous V.pivot u).ae_le h, ?_⟩
  have h₀ := M.imageLaw_eq_of_observationLaw_eq M' η hη V.pivot (hobs none)
  rw [h₀] at h
  exact fun u => (M'.imageLaw_absolutelyContinuous V.pivot u).ae_le h

end
end IVAE
