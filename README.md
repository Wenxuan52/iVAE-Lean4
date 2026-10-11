# iVAE: Almost-Everywhere Identifiability in Lean 4

This repository formalizes a corrected **almost-everywhere affine identifiability theorem for iVAE (Theorem 1, Steps I–III)** using Lean 4 and Mathlib. It contains the complete proof, its supporting definitions and lemmas, and accompanying mathematical proof documents.

The mathematical source is Khemakhem, Kingma, Monti, and Hyvärinen, *Variational Autoencoders and Nonlinear ICA: A Unifying Framework*, corrected [arXiv v4](https://arxiv.org/abs/1907.04809v4).

The main theorem is in [`Ivae/Theorem1.lean`](Ivae/Theorem1.lean):

```lean
IVAE.correctedTheorem1_stepI_II_III
```

Under the assumptions below, equality of the noisy observation laws at the selected `nk+1` auxiliary values implies the existence of a fixed invertible linear map `A` and a vector `c` such that

```text
T(f⁻¹(x)) = A T′(f′⁻¹(x)) + c, μ-almost everywhere.
```

The reference measure satisfies `μ ≪ M.imageLaw V.pivot`. Each inverse is defined on the common noiseless mixing image `X`. The formalization retains general dimensions `n,d,m,k`, including `n < d`.

## Build and verify

After installing the Lean toolchain manager Elan, run the following commands from the repository root. On a fresh checkout, first download Mathlib's precompiled cache:

```bash
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean
```

The toolchain is pinned to `leanprover/lean4:v4.34.0-rc2`, and `lake-manifest.json` locks the Mathlib revision and its dependencies. Mathlib is the project's only direct dependency. The default build target is the `Ivae` library.

The final command checks the axiom dependencies of the main theorem, its consequence for all conditional laws, Step III invertibility, the two formulations of nondegeneracy, and the a.e. equivalence relation. It allows only Lean's usual foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`. Any dependency on `sorryAx` or another axiom causes an error. GitHub Actions runs the build and this check.

## Assumptions and conclusion

- **Models and domains:** both models share measurable latent and image domains `Z` and `X`. `Params.f_bijOn` states that the mixing function restricted to `Z` is a bijection onto `X`. The restricted mixing map and its image-level inverse are measurable.
- **Valid priors:** the priors have the product form of equation (7), with nonnegative base functions, positive normalizers, and measurable conditional densities whose integrals are 1.
- **Noise:** both models use the same finite noise measure. Its characteristic function has a Lebesgue-null zero set on the entire frequency space `ℝᵈ`.
- **Auxiliary variation:** the true model supplies `nk+1` distinct auxiliary values, and its difference matrix `L` has nonzero determinant.
- **Additional Step III assumption:** `AEAffineNondegenerate` holds under the true pivot prior. No nonzero linear functional of the sufficient-statistic vector is constant almost surely under that prior.
- **Reference measure:** `μ` is absolutely continuous with respect to the true model's noiseless pivot image law.

The conclusion is `SimAAE μ θ θ′`. Essential affine nondegeneracy is an explicit additional assumption; the formalization does not derive it from the paper's assumption (iii). The result is a corrected a.e. theorem and does not establish the original pointwise conclusion.

The companion theorem [`correctedTheorem1_all_conditional_laws`](Ivae/Theorem1.lean) proves that the same witnesses `A,c` work almost everywhere under every conditional noiseless law of either model.

## Repository layout

```text
Ivae.lean                       Library entry point; imports Ivae.Theorem1
Ivae/
├── Basic.lean                  Vectors, parameters, image-level inverse, statistics
├── IdentifiabilityAE.lean      SimAE / SimAAE and relation properties for a fixed measure
├── Deconvolution.lean          Step I: characteristic functions and deconvolution
├── MeasureTransport.lean       Domain Lebesgue measure and weighted-measure transport
├── MeasureModel.lean           Equation-(7) models, probability laws, and density ratios
├── AuxiliaryVariation.lean     nk+1 auxiliary values and the variation matrix L
├── PivotSystem.lean            Step II: solve the pivot system for a fixed affine map
├── AffineNondegeneracy.lean     Step III: nondegeneracy and invertibility
└── Theorem1.lean               Assemble Steps I–III and the conditional-law consequence
scripts/CheckAxioms.lean        Check foundational axiom dependencies
docs/                          English and Chinese mathematical proofs (TeX / PDF)
```

## Reading the proof

| Step | Main declarations | Mathematical role |
| --- | --- | --- |
| Step I | `deconvolution_of_vectorCharFun_zeroSet_null`; `MeasureModel.imageLaw_eq_of_observationLaw_eq` | Cancel the common noise and recover equality of noiseless image laws. |
| Density ratios | `MeasureModel.imageLaw_ratio`; `MeasureModel.log_imageRatio_ae` | Use the actual pivot image law as the reference measure and cancel base factors without an image-space Jacobian. |
| Step II | `MeasureModel.imageRatio_ae_eq`; `MeasureModel.pivot_equation` | Obtain a finite linear system on a common set of full pivot measure. |
| Solve the system | `simAE_of_pivot_equation`; `MeasureModel.stepII` | Multiply by the inverse of `Lᵀ` to obtain fixed witnesses `A,c`. |
| Step III | `MeasureModel.image_nondegenerate`; `affineWitness_bijective` | Transport nondegeneracy to the image law and prove that the same affine witness is invertible. |
| Assemble | `correctedTheorem1_stepI_II_III` | Transfer the invertible affine relation from the pivot law to any dominated reference measure `μ`. |

For Step III, let a linear functional `ℓ` satisfy `ℓ ∘ A = 0`. The relation `t = A t′ + c` then gives `ℓ(t) = ℓ(c)` almost everywhere, so nondegeneracy forces `ℓ = 0`. Mathlib's `LinearMap.dualMap_injective_iff` yields surjectivity of `A`; finite dimensionality and `LinearMap.injective_iff_surjective` then give bijectivity. This implements the contradiction argument by showing that the dual map has trivial kernel.

## Mathematical proof documents

- English: [PDF](docs/theorem1-ae-proof.pdf) / [TeX](docs/theorem1-ae-proof.tex).
- Chinese: [PDF](docs/theorem1-ae-proof-zh.pdf) / [TeX](docs/theorem1-ae-proof-zh.tex).

Both documents describe the same current theorem. Rebuilding the PDFs is independent of the Lean build. Install Tectonic separately (the existing PDFs were built with version 0.17.0), then run:

```bash
tectonic -X compile docs/theorem1-ae-proof.tex --outdir docs
tectonic -X compile docs/theorem1-ae-proof-zh.tex --outdir docs
```

Tectonic may download TeX support files on its first run. PDF generation is optional for building and checking the Lean proof. The local `tools/` directory is excluded by `.gitignore` and is not distributed with the repository.
