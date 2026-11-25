# A machine-checked Gaussian counterexample / 高斯反例的形式化证明

The four sites in each period have signs $(+,-,+,-)$. Both cells have period four. We compare the equally spaced cell $U=(0,1,2,3)$ with $X=(0,3/2,2,5/2)$, using the energy per particle and ordered-pair convention of the manuscript. 两个周期单元各有四个粒子，种类交替、顺序相同。两种构型都沿整条实轴周期延伸。

$$
E(P)=-\frac14\sum_{i,j=0}^3\ \sum_{m\in\mathbb Z}^{\prime}
\sigma_i\sigma_j\exp\!\left[-\frac{(x_j+4m-x_i)^2}{4}\right].
$$

The prime omits the single central self-interaction for each label, $i=j$ and $m=0$. Images of that label in all other periods contribute. 撇号只略去每个粒子与自身在同一周期中的相互作用。下面的定理直接比较完整无穷链的能量。

| Theorem in [Counterexample.lean](Counterexample.lean) | What Lean checks / 验证内容 |
| --- | --- |
| `admissible_gaussian_counterexample` | The Gaussian has a profile $F$ in the squared distance with $(-1)^n F^{(n)}(s)>0$ for every $n\geq 0$ and $s\geq 0$. A Fourier proof in the literal coordinates gives $E(X)<E(U)$. 高斯势满足猜想的完全单调条件，移动后的构型能量严格更低。 |
| `admissible_cells_and_energy_gap` | A direct real-space proof gives $E(U)-E(X)>1/36$. Both cells begin at zero and are strictly ordered. 两个构型满足位置约束，能量差有严格的有理数下界。 |

The Fourier proof periodizes the Gaussian, computes the signed sum over all sixteen ordered pairs, and controls the remaining Fourier modes. The real-space proof groups all images by their distance and bounds the series tail. 两条证明分别在傅里叶空间和实空间控制无穷级数。论文中关于任意小位移的局部不稳定性、指数混合势和里斯势的结论未收入本次形式化。

## Reproduce / 复现

Install the Lean toolchain manager `elan`, then run the following from the repository root. The toolchain is Lean 4.28.0. The Lake manifest pins mathlib and its dependencies.

```sh
cd lean
lake exe cache get
lake build
lake env lean Counterexample.lean
```

The last command prints the axiom dependencies of both top-level theorems. Both reports list exactly `propext`, `Classical.choice`, and `Quot.sound`. 最后一条命令打印两个主定理所依赖的公理。两份报告均只含上述三个标准公理，证明中没有 `sorry` 占位符。

| Definitions and proofs | Source |
| --- | --- |
| Squared-distance profile and all derivative signs | [GaussianClass.lean](GaussianClass.lean) |
| Periodization, structure factors and literal-coordinate Fourier comparison | [PeriodFourGaussian.lean](PeriodFourGaussian.lean) · [GaussianFourier.lean](GaussianFourier.lean) · [FourPointCounterexample.lean](FourPointCounterexample.lean) |
| Real-space Gaussian bounds and infinite-series estimate | [ArithmeticBounds.lean](ArithmeticBounds.lean) · [Direct.lean](Direct.lean) |
| Labeled cells, periodic images, physical energy and strict gap | [PhysicalCellCore.lean](PhysicalCellCore.lean) · [ImageReindex.lean](ImageReindex.lean) · [ParticleEnergy.lean](ParticleEnergy.lean) · [PeriodicGaussian.lean](PeriodicGaussian.lean) · [GaussianMargin.lean](GaussianMargin.lean) |
