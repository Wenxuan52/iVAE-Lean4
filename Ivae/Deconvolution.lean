/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Ivae.Basic

/-!
# Theorem 1, Step I: measure-level deconvolution

The corrected noise hypothesis concerns the entire frequency space. The result
identifies finite measures, not pointwise density representatives. It makes no
assumption about mixing maps, latent dimension, or an image reference measure.

`Vec` keeps the project's coordinate-function representation. A continuous
linear equivalence with Euclidean space is used only to access Mathlib's
inner-product characteristic function.
-/

namespace IVAE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A norm-compatible bridge, without changing the model's coordinate vectors. -/
def vecToEuclidean (d : ℕ) : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm

/-- Characteristic function evaluated at coordinate frequencies in ℝ^d. -/
def vectorCharFun {d : ℕ} (ν : Measure (Vec d)) (ω : Vec d) : ℂ :=
  charFun (ν.map (vecToEuclidean d)) (vecToEuclidean d ω)

/-- Corrected Step I condition: the zero set is null on all of ℝ^d. -/
def FullFrequencyNoiseCondition {d : ℕ} (η : Measure (Vec d)) : Prop :=
  volume {ω : Vec d | vectorCharFun η ω = 0} = 0

theorem continuous_vectorCharFun {d : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν] :
    Continuous (vectorCharFun ν) :=
  continuous_charFun.comp (vecToEuclidean d).continuous

theorem vectorCharFun_conv {d : ℕ} (ν η : Measure (Vec d))
    [IsFiniteMeasure ν] [IsFiniteMeasure η] (ω : Vec d) :
    vectorCharFun (ν ∗ η) ω = vectorCharFun ν ω * vectorCharFun η ω := by
  unfold vectorCharFun
  have hmap := Measure.map_conv_continuousLinearMap
    (vecToEuclidean d).toContinuousLinearMap (μ := ν) (ν := η)
  change (ν ∗ η).map (vecToEuclidean d) =
    ν.map (vecToEuclidean d) ∗ η.map (vecToEuclidean d) at hmap
  rw [hmap]
  exact charFun_conv _

/-- Fourier uniqueness for the project's original `Vec` representation. -/
theorem measure_eq_of_vectorCharFun_eq {d : ℕ} {ν ν' : Measure (Vec d)}
    [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : vectorCharFun ν = vectorCharFun ν') : ν = ν' := by
  have hmap : ν.map (vecToEuclidean d) = ν'.map (vecToEuclidean d) := by
    apply Measure.ext_of_charFun
    ext ω
    obtain ⟨w, rfl⟩ := (vecToEuclidean d).surjective ω
    exact congrFun h w
  exact (MeasurableEquiv.toLp 2 (Vec d)).map_measurableEquiv_injective hmap

/-- Theorem 1, Step I: cancel noise a.e. in frequency, then use continuity and uniqueness. -/
theorem deconvolution_of_vectorCharFun_ae_ne_zero {d : ℕ}
    (ν ν' η : Measure (Vec d))
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] [IsFiniteMeasure η]
    (hη : ∀ᵐ ω ∂volume, vectorCharFun η ω ≠ 0)
    (hobs : ν ∗ η = ν' ∗ η) : ν = ν' := by
  have hcharAE : vectorCharFun ν =ᵐ[volume] vectorCharFun ν' := by
    filter_upwards [hη] with ω hω
    have hproduct := congrArg (fun ξ => vectorCharFun ξ ω) hobs
    rw [vectorCharFun_conv, vectorCharFun_conv] at hproduct
    exact mul_right_cancel₀ hω hproduct
  -- Characteristic functions are continuous; their a.e. equality becomes everywhere equality.
  have hchar : vectorCharFun ν = vectorCharFun ν' :=
    Measure.eq_of_ae_eq hcharAE (continuous_vectorCharFun ν) (continuous_vectorCharFun ν')
  exact measure_eq_of_vectorCharFun_eq hchar

/-- The standalone corrected Step I, with the zero set measured on the entire ℝ^d. -/
theorem deconvolution_of_vectorCharFun_zeroSet_null {d : ℕ}
    (ν ν' η : Measure (Vec d))
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] [IsFiniteMeasure η]
    (hη : volume {ω : Vec d | vectorCharFun η ω = 0} = 0)
    (hobs : ν ∗ η = ν' ∗ η) : ν = ν' := by
  apply deconvolution_of_vectorCharFun_ae_ne_zero ν ν' η
  · simpa only [ae_iff, not_not] using hη
  · exact hobs

end

end IVAE
