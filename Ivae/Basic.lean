/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Mathlib

/-!
# Basic model objects for the iVAE formalization

This file contains the ambient vector spaces, raw functional parameters, and
the domain-aware form of model parameters whose mixing function is a
bijection onto its image.
-/

namespace IVAE

/-- A finite-dimensional real vector ℝⁿ. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- Index for the nk sufficient statistics. -/
abbrev StatIdx (n k : ℕ) := Fin n × Fin k

/-- The space ℝ^(nk) containing the full sufficient-statistic vector. -/
abbrev StatSpace (n k : ℕ) := StatIdx n k → ℝ

/-- Unconstrained functional data θ = (f, T, λ) of the iVAE model. -/
structure RawParams (n d m k : ℕ) where
  f : Vec n → Vec d
  T : Fin n → Fin k → ℝ → ℝ
  lam : Vec m → Fin n → Fin k → ℝ

/--
Parameters whose mixing function is a bijection from the latent domain `Z`
onto the noiseless observation domain `X`.

This is the precise subtype-level form of the paper's assumption that `f` is
injective and that `X` is its image.  It does not assert that `f` is a
bijection between the ambient spaces `Vec n` and `Vec d`, so it also covers
the undercomplete case `n < d`.
-/
structure Params
    (n d m k : ℕ)
    (Z : Set (Vec n))
    (X : Set (Vec d)) where
  toRawParams : RawParams n d m k
  f_bijOn : Set.BijOn toRawParams.f Z X

namespace Params

/--
The mixing function restricted to the latent domain and its image.

Unlike a global equivalence `Vec n ≃ Vec d`, this equivalence only identifies
`Z` with `X`, exactly as an injective function is a bijection onto its image.
-/
noncomputable def mixingEquiv
    {n d m k : ℕ}
    {Z : Set (Vec n)}
    {X : Set (Vec d)}
    (θ : Params n d m k Z X) :
    Z ≃ X :=
  Set.BijOn.equiv θ.toRawParams.f θ.f_bijOn

/-- The inverse mixing function, defined only on the image `X`. -/
noncomputable def mixingInv
    {n d m k : ℕ}
    {Z : Set (Vec n)}
    {X : Set (Vec d)}
    (θ : Params n d m k Z X)
    (x : X) :
    Z :=
  θ.mixingEquiv.symm x

/-- On underlying vectors, `mixingEquiv` agrees with the original mixing function. -/
@[simp]
theorem mixingEquiv_apply_val
    {n d m k : ℕ}
    {Z : Set (Vec n)}
    {X : Set (Vec d)}
    (θ : Params n d m k Z X)
    (z : Z) :
    (θ.mixingEquiv z).1 = θ.toRawParams.f z.1 :=
  rfl

/-- Applying the image-level inverse after the mixing equivalence recovers the latent point. -/
@[simp]
theorem mixingInv_mixingEquiv
    {n d m k : ℕ}
    {Z : Set (Vec n)}
    {X : Set (Vec d)}
    (θ : Params n d m k Z X)
    (z : Z) :
    θ.mixingInv (θ.mixingEquiv z) = z :=
  θ.mixingEquiv.symm_apply_apply z

/-- Mixing an image-level inverse recovers the observation in `X`. -/
@[simp]
theorem mixingEquiv_mixingInv
    {n d m k : ℕ}
    {Z : Set (Vec n)}
    {X : Set (Vec d)}
    (θ : Params n d m k Z X)
    (x : X) :
    θ.mixingEquiv (θ.mixingInv x) = x :=
  θ.mixingEquiv.apply_symm_apply x

/-- Applying the original mixing function to its image-level inverse recovers `x`. -/
@[simp]
theorem mixing_mixingInv
    {n d m k : ℕ}
    {Z : Set (Vec n)}
    {X : Set (Vec d)}
    (θ : Params n d m k Z X)
    (x : X) :
    θ.toRawParams.f (θ.mixingInv x).1 = x.1 := by
  exact congrArg Subtype.val (θ.mixingEquiv_mixingInv x)

end Params

/-- T(z), viewed as a vector in ℝ^(nk). -/
def statVec {n d m k : ℕ}
    (θ : RawParams n d m k)
    (z : Vec n) :
    StatIdx n k → ℝ :=
  fun ij => θ.T ij.1 ij.2 (z ij.1)

/-- λ(u), viewed as a vector in ℝ^(nk). -/
def lambdaVec {n d m k : ℕ}
    (θ : RawParams n d m k)
    (u : Vec m) :
    StatIdx n k → ℝ :=
  fun ij => θ.lam u ij.1 ij.2

/--
The sufficient-statistic representation of a noiseless observation `x ∈ X`:

    T(f⁻¹(x))

The inverse is the inverse of the equivalence `Z ≃ X` supplied by
`Params`.  Consequently, this definition cannot be applied to points
outside the image of the mixing function.
-/
noncomputable def latentStat {n d m k : ℕ}
    {Z : Set (Vec n)}
    {X : Set (Vec d)}
    (θ : Params n d m k Z X)
    (x : X) :
    StatSpace n k :=
  statVec θ.toRawParams (θ.mixingInv x).1

end IVAE
