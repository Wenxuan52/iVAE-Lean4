# iVAE：almost everywhere 定理一的 Lean 4 形式化

本仓库只维护当前已形式化的 **a.e. 仿射可识别性定理一（Step I–III）** 及其必要的定义、引理和证明文档。数学来源是 Khemakhem、Kingma、Monti、Hyvärinen 的 iVAE 论文 corrected arXiv v4。

主定理位于 [`Ivae/Theorem1.lean`](Ivae/Theorem1.lean)：

```lean
IVAE.correctedTheorem1_stepI_II_III
```

若两个模型在选定的 `nk+1` 个辅助值处具有相同的含噪观测分布，在下面列出的假设下，存在一个固定的可逆线性映射 `A` 和向量 `c`，使

```text
T(f⁻¹(x)) = A T′(f′⁻¹(x)) + c，μ-almost everywhere。
```

这里 `μ ≪ M.imageLaw V.pivot`。逆函数只定义在共同无噪声像域 `X` 上，维数保持一般的 `n,d,m,k`，包括 `n < d`。主定理名称、数学假设及证明正文在仓库整理中均保持不变。

## 构建与验证

安装 Lean 工具链管理器 Elan 后，在本目录运行。首次获取项目时，先下载
Mathlib 的预编译缓存，再构建证明：

```bash
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean
```

工具链固定为 `leanprover/lean4:v4.34.0-rc2`，Mathlib 版本由 `lake-manifest.json` 锁定。项目直接依赖只有 Mathlib；`lake build` 构建唯一的 `Ivae` 库。

第二条命令检查主定理、所有条件分布的推论、Step III 可逆性、非退化性的两种表述以及 a.e. 等价关系的公理依赖，只允许 Lean 的 `propext`、`Classical.choice` 和 `Quot.sound`。发现 `sorryAx` 或任何其他公理时会报错。CI 同样执行构建和该检查。

## 当前定理的假设和结论

- **模型与像域：** 两模型使用共同的可测潜域 `Z` 和像域 `X`。`Params.f_bijOn` 表示混合函数限制到 `Z` 后是到 `X` 的双射；正向映射和像上逆映射可测。
- **有效先验：** 论文 equation (7) 的乘积形式；基函数非负、正规化因子为正、每个条件先验可测且积分为 1。
- **噪声：** 共同的有限噪声测度，其特征函数的零集在整个频域 `ℝᵈ` 上是 Lebesgue 零测集。
- **辅助变化：** 真实模型提供 `nk+1` 个不同的辅助值，其差分矩阵 `L` 的行列式非零。
- **Step III 的额外假设：** 真实 pivot 先验下的 `AEAffineNondegenerate`：统计量的任意几乎处处常数线性泛函必须为零。
- **参考测度：** `μ` 对真实模型的 pivot 无噪声像分布绝对连续。

结论是 `SimAAE μ θ θ′`。额外的仿射非退化性仍是显式前提，未从原论文 assumption (iii) 推导；当前结果是修正版的 a.e. 定理，不声称原论文的逐点结论。

[`correctedTheorem1_all_conditional_laws`](Ivae/Theorem1.lean) 进一步证明：同一组 `A,c` 在两模型的每个条件无噪声分布下都几乎处处成立。

## 文件导航

```text
Ivae.lean                       唯一库入口，导入 Ivae.Theorem1
Ivae/
├── Basic.lean                  向量、参数、像上逆、统计量
├── IdentifiabilityAE.lean      SimAE / SimAAE 与固定测度下的等价关系
├── Deconvolution.lean          Step I：特征函数与去卷积
├── MeasureTransport.lean       域上 Lebesgue 测度及加权测度的传输
├── MeasureModel.lean           equation (7) 模型、概率分布与密度比
├── AuxiliaryVariation.lean     nk+1 个辅助点与差分矩阵 L
├── PivotSystem.lean            Step II：由 pivot 方程求出固定仿射映射
├── AffineNondegeneracy.lean     Step III：非退化性与仿射映射可逆性
└── Theorem1.lean               组装 Step I–III；主定理及条件分布推论
scripts/CheckAxioms.lean        公理依赖检查
docs/                          当前定理的中英文数学证明（TeX / PDF）
```

## 按数学步骤阅读

| 步骤 | 主要声明 | 数学作用 |
| --- | --- | --- |
| Step I | `deconvolution_of_vectorCharFun_zeroSet_null`；`MeasureModel.imageLaw_eq_of_observationLaw_eq` | 消去共同噪声，从含噪分布相等得到像分布相等 |
| 密度比 | `MeasureModel.imageLaw_ratio`；`MeasureModel.log_imageRatio_ae` | 使用真实 pivot 像分布作参考，消去基函数，无需像空间 Jacobian |
| Step II | `MeasureModel.imageRatio_ae_eq`；`MeasureModel.pivot_equation` | 在共同的满测集上得到有限辅助点线性方程组 |
| 求解 | `simAE_of_pivot_equation`；`MeasureModel.stepII` | 左乘 `Lᵀ` 的逆，得到一组固定的 `A,c` |
| Step III | `MeasureModel.image_nondegenerate`；`affineWitness_bijective` | 推前非退化性，排除非零左零空间泛函，证明同一个 `A` 可逆 |
| 组装 | `correctedTheorem1_stepI_II_III` | 将 pivot 分布下的可逆仿射关系传递到任意受其支配的 `μ` |

Step III 的核心是：若线性泛函 `ℓ` 满足 `ℓ ∘ A = 0`，则由 `t = A t′ + c` 得到 `ℓ(t) = ℓ(c)` a.e.；非退化性迫使 `ℓ = 0`。Mathlib 的 `LinearMap.dualMap_injective_iff` 给出 `A` 满射，再由有限维的 `LinearMap.injective_iff_surjective` 得到双射。这就是原来讨论的反证思路在 Lean 中的实现。

## 数学证明文档

- 中文：[PDF](docs/theorem1-ae-proof-zh.pdf) / [TeX](docs/theorem1-ae-proof-zh.tex)。
- 英文：[PDF](docs/theorem1-ae-proof.pdf) / [TeX](docs/theorem1-ae-proof.tex)。

文档对应同一个当前定理。PDF 重建独立于 Lean 构建；自行安装 Tectonic
（现有 PDF 使用 0.17.0），然后运行：

```bash
tectonic -X compile docs/theorem1-ae-proof.tex --outdir docs
tectonic -X compile docs/theorem1-ae-proof-zh.tex --outdir docs
```

首次生成 PDF 时，Tectonic 可能需要下载 TeX 支持文件；这不影响 `lake build` 或公理检查。
本机的 `tools/` 目录由 `.gitignore` 排除，不随仓库发布。
