/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Ivae.MeasureTransport
import Ivae.Deconvolution

/-!
# Equation-(7) models on measurable images, including n < d

No density with respect to ambient image Lebesgue measure is assumed.
The mixing map and its image-level inverse are measurable. The prior is
normalized with respect to latent Lebesgue measure. Density ratios use an
actual pivot prior, not a separately postulated log-density representation.
-/

namespace IVAE
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Paper equation (7), with arbitrary latent and observation dimensions. -/
def modelPrior {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    {U : Set (Vec m)} (θ : Params n d m k Z X)
    (Q : Fin n → ℝ → ℝ) (N : Fin n → U → ℝ) (u : U) (z : Z) : ℝ :=
  (∏ i, Q i (z.1 i)) / (∏ i, N i u) *
    Real.exp (dotProduct (statVec θ.toRawParams z.1) (lambdaVec θ.toRawParams u.1))

theorem modelPrior_eq_product {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    {U : Set (Vec m)} (θ : Params n d m k Z X)
    (Q : Fin n → ℝ → ℝ) (N : Fin n → U → ℝ) (u : U) (z : Z) :
    modelPrior θ Q N u z = ∏ i, Q i (z.1 i) / N i u *
      Real.exp (∑ j, θ.toRawParams.T i j (z.1 i) * θ.toRawParams.lam u.1 i j) := by
  classical
  simp [modelPrior, dotProduct, statVec, lambdaVec, Fintype.sum_prod_type,
    Real.exp_sum, Finset.prod_mul_distrib, Finset.prod_div_distrib]

/-- Measurable model validity; no differentiability, Jacobian, or affine conclusion. -/
structure MeasureModel {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)}
    (θ : Params n d m k Z X) (U : Set (Vec m)) where
  latent_measurable : MeasurableSet Z
  image_measurable : MeasurableSet X
  mixing_measurable : Measurable θ.mixingEquiv
  inverse_measurable : Measurable θ.mixingInv
  base : Fin n → ℝ → ℝ
  normalizer : Fin n → U → ℝ
  base_nonneg : ∀ i z, 0 ≤ base i z
  normalizer_pos : ∀ i u, 0 < normalizer i u
  prior_measurable : ∀ u, Measurable (modelPrior θ base normalizer u)
  prior_normalized : ∀ u,
    (∫⁻ z, ENNReal.ofReal (modelPrior θ base normalizer u z) ∂domainVolume Z) = 1

namespace MeasureModel
variable {n d m k : ℕ} {Z : Set (Vec n)} {X : Set (Vec d)} {U : Set (Vec m)}
  {θ : Params n d m k Z X}

def mixing (M : MeasureModel θ U) : Z ≃ᵐ X where
  toEquiv := θ.mixingEquiv
  measurable_toFun := M.mixing_measurable
  measurable_invFun := M.inverse_measurable

@[simp] theorem mixing_apply (M : MeasureModel θ U) (z : Z) :
    M.mixing z = θ.mixingEquiv z := rfl

def priorDensity (M : MeasureModel θ U) (u : U) : Z → ℝ :=
  modelPrior θ M.base M.normalizer u

def normalizerProduct (M : MeasureModel θ U) (u : U) : ℝ := ∏ i, M.normalizer i u

theorem normalizerProduct_pos (M : MeasureModel θ U) (u : U) :
    0 < M.normalizerProduct u := Finset.prod_pos (fun i _ => M.normalizer_pos i u)

theorem priorDensity_nonneg (M : MeasureModel θ U) (u : U) (z : Z) :
    0 ≤ M.priorDensity u z :=
  mul_nonneg (div_nonneg (Finset.prod_nonneg (fun i _ => M.base_nonneg i _))
    (M.normalizerProduct_pos u).le) (Real.exp_pos _).le

theorem priorDensity_integrable (M : MeasureModel θ U) (u : U) :
    Integrable (M.priorDensity u) (domainVolume Z) := by
  refine ⟨(M.prior_measurable u).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp_rw [Real.enorm_eq_ofReal (M.priorDensity_nonneg u _)]
  rw [show (∫⁻ z, ENNReal.ofReal (M.priorDensity u z) ∂domainVolume Z) = 1 from
    M.prior_normalized u]
  exact ENNReal.one_lt_top

theorem priorDensity_integral (M : MeasureModel θ U) (u : U) :
    (∫ z, M.priorDensity u z ∂domainVolume Z) = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal (M.priorDensity_integrable u)
    (ae_of_all _ (M.priorDensity_nonneg u))
  rw [show (∫⁻ z, ENNReal.ofReal (M.priorDensity u z) ∂domainVolume Z) = 1 from
    M.prior_normalized u] at h
  exact ENNReal.ofReal_eq_one.mp h

def priorLaw (M : MeasureModel θ U) (u : U) : Measure Z :=
  (domainVolume Z).withDensity (fun z => ENNReal.ofReal (M.priorDensity u z))

instance priorLaw_isProbabilityMeasure (M : MeasureModel θ U) (u : U) :
    IsProbabilityMeasure (M.priorLaw u) := by
  constructor
  rw [priorLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact M.prior_normalized u

def imageLaw (M : MeasureModel θ U) (u : U) : Measure X := (M.priorLaw u).map M.mixing

instance imageLaw_isProbabilityMeasure (M : MeasureModel θ U) (u : U) :
    IsProbabilityMeasure (M.imageLaw u) :=
  Measure.isProbabilityMeasure_map M.mixing.measurable.aemeasurable

def ambientLaw (M : MeasureModel θ U) (u : U) : Measure (Vec d) :=
  (M.imageLaw u).map Subtype.val

instance ambientLaw_isProbabilityMeasure (M : MeasureModel θ U) (u : U) :
    IsProbabilityMeasure (M.ambientLaw u) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

def observationLaw (M : MeasureModel θ U) (η : Measure (Vec d)) (u : U) : Measure (Vec d) :=
  M.ambientLaw u ∗ η

/-- Corrected Step I: deconvolve actual model laws, then restrict to the common image. -/
theorem imageLaw_eq_of_observationLaw_eq {θ' : Params n d m k Z X}
    (M : MeasureModel θ U) (M' : MeasureModel θ' U) (η : Measure (Vec d))
    [IsFiniteMeasure η] (hη : FullFrequencyNoiseCondition η) (u : U)
    (h : M.observationLaw η u = M'.observationLaw η u) : M.imageLaw u = M'.imageLaw u := by
  have h' := deconvolution_of_vectorCharFun_zeroSet_null
    (M.ambientLaw u) (M'.ambientLaw u) η hη h
  exact (MeasurableEmbedding.subtype_coe M.image_measurable).map_injective h'

/-- A measurable version of the density ratio, set to zero off the pivot support. -/
def latentRatio (M : MeasureModel θ U) (u₀ u : U) (z : Z) : ℝ :=
  M.priorDensity u z / M.priorDensity u₀ z

def imageRatio (M : MeasureModel θ U) (u₀ u : U) (x : X) : ℝ :=
  M.latentRatio u₀ u (θ.mixingInv x)

theorem latentRatio_measurable (M : MeasureModel θ U) (u₀ u : U) :
    Measurable (M.latentRatio u₀ u) := (M.prior_measurable u).div (M.prior_measurable u₀)

theorem imageRatio_measurable (M : MeasureModel θ U) (u₀ u : U) :
    Measurable (M.imageRatio u₀ u) :=
  (M.latentRatio_measurable u₀ u).comp M.inverse_measurable

theorem latentRatio_nonneg (M : MeasureModel θ U) (u₀ u : U) (z : Z) :
    0 ≤ M.latentRatio u₀ u z := div_nonneg (M.priorDensity_nonneg u z) (M.priorDensity_nonneg u₀ z)

/-- All conditional priors have the same zero set; the base may vanish. -/
theorem priorDensity_eq_zero_iff (M : MeasureModel θ U) (u₀ u : U) (z : Z) :
    M.priorDensity u z = 0 ↔ M.priorDensity u₀ z = 0 := by
  simp only [priorDensity, modelPrior, mul_eq_zero, div_eq_zero_iff,
    show (∏ i, M.normalizer i u) ≠ 0 from ne_of_gt (M.normalizerProduct_pos u),
    show (∏ i, M.normalizer i u₀) ≠ 0 from ne_of_gt (M.normalizerProduct_pos u₀),
    Real.exp_ne_zero, or_false]

theorem density_mul_latentRatio (M : MeasureModel θ U) (u₀ u : U) (z : Z) :
    M.priorDensity u₀ z * M.latentRatio u₀ u z = M.priorDensity u z := by
  by_cases hz : M.priorDensity u₀ z = 0
  · rw [hz, zero_mul, (M.priorDensity_eq_zero_iff u₀ u z).mpr hz]
  · exact mul_div_cancel₀ _ hz

theorem priorLaw_ratio (M : MeasureModel θ U) (u₀ u : U) :
    (M.priorLaw u₀).withDensity (fun z => ENNReal.ofReal (M.latentRatio u₀ u z)) =
      M.priorLaw u := by
  have hp : Measurable (fun z => ENNReal.ofReal (M.priorDensity u₀ z)) :=
    (M.prior_measurable u₀).ennreal_ofReal
  unfold priorLaw
  rw [← withDensity_mul _ hp (M.latentRatio_measurable u₀ u).ennreal_ofReal]
  congr 1
  funext z
  change ENNReal.ofReal (M.priorDensity u₀ z) * ENNReal.ofReal (M.latentRatio u₀ u z) = _
  rw [← ENNReal.ofReal_mul (M.priorDensity_nonneg u₀ z), M.density_mul_latentRatio]

/-- The image law has this density relative to the actual pivot image law. -/
theorem imageLaw_ratio (M : MeasureModel θ U) (u₀ u : U) :
    (M.imageLaw u₀).withDensity (fun x => ENNReal.ofReal (M.imageRatio u₀ u x)) =
      M.imageLaw u := by
  have h := map_withDensity_equiv M.mixing (M.priorLaw u₀)
    (fun x => ENNReal.ofReal (M.imageRatio u₀ u x))
  have heq : (fun z => ENNReal.ofReal (M.imageRatio u₀ u (M.mixing z))) =
      (fun z => ENNReal.ofReal (M.latentRatio u₀ u z)) := by
    funext z
    simp [imageRatio]
  rw [heq, M.priorLaw_ratio] at h
  exact h.symm

/-- Every auxiliary conditional law is dominated by the pivot law. -/
theorem imageLaw_absolutelyContinuous (M : MeasureModel θ U) (u₀ u : U) :
    M.imageLaw u ≪ M.imageLaw u₀ := by
  rw [← M.imageLaw_ratio u₀ u]
  exact withDensity_absolutelyContinuous _ _

theorem priorDensity_pos_ae (M : MeasureModel θ U) (u₀ : U) :
    ∀ᵐ z ∂M.priorLaw u₀, 0 < M.priorDensity u₀ z := by
  apply (ae_withDensity_iff (M.prior_measurable u₀).ennreal_ofReal).mpr
  exact ae_of_all _ (fun z hz => by
    change 0 < modelPrior θ M.base M.normalizer u₀ z
    simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hz)

/-- Log of the ratio: the base factor cancels without a Jacobian formula. -/
theorem log_latentRatio (M : MeasureModel θ U) (u₀ u : U) (z : Z)
    (hz : 0 < M.priorDensity u₀ z) :
    Real.log (M.latentRatio u₀ u z) =
      dotProduct (statVec θ.toRawParams z.1)
        (lambdaVec θ.toRawParams u.1 - lambdaVec θ.toRawParams u₀.1) -
      (Real.log (M.normalizerProduct u) - Real.log (M.normalizerProduct u₀)) := by
  have hbase : (∏ i, M.base i (z.1 i)) ≠ 0 := by
    intro h
    simp [priorDensity, modelPrior, h] at hz
  have hratio : M.latentRatio u₀ u z =
      M.normalizerProduct u₀ / M.normalizerProduct u *
        Real.exp (dotProduct (statVec θ.toRawParams z.1)
          (lambdaVec θ.toRawParams u.1 - lambdaVec θ.toRawParams u₀.1)) := by
    unfold latentRatio priorDensity modelPrior
    rw [dotProduct_sub, Real.exp_sub]
    change (_ / M.normalizerProduct u * _) / (_ / M.normalizerProduct u₀ * _) = _
    field_simp [hbase, ne_of_gt (M.normalizerProduct_pos u),
      ne_of_gt (M.normalizerProduct_pos u₀), Real.exp_ne_zero]
  rw [hratio, Real.log_mul (div_ne_zero (ne_of_gt (M.normalizerProduct_pos u₀))
    (ne_of_gt (M.normalizerProduct_pos u))) (Real.exp_ne_zero _),
    Real.log_div (ne_of_gt (M.normalizerProduct_pos u₀))
      (ne_of_gt (M.normalizerProduct_pos u)), Real.log_exp]
  ring

theorem log_imageRatio_ae (M : MeasureModel θ U) (u₀ u : U) :
    ∀ᵐ x ∂M.imageLaw u₀, Real.log (M.imageRatio u₀ u x) =
      dotProduct (latentStat θ x)
        (lambdaVec θ.toRawParams u.1 - lambdaVec θ.toRawParams u₀.1) -
      (Real.log (M.normalizerProduct u) - Real.log (M.normalizerProduct u₀)) := by
  apply M.mixing.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [M.priorDensity_pos_ae u₀] with z hz
  simpa [imageRatio, latentStat] using M.log_latentRatio u₀ u z hz

end MeasureModel
end
end IVAE
