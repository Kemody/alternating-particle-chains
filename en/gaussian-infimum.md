# The infimum of the Gaussian alternating-chain energy and the sharp cost of a minimum spacing

## Abstract

For a one-dimensional periodic cell with an even number of alternating sites, we determine the exact infimum of the periodized Gaussian energy in an explicit range of Gaussian widths. In the closure allowing coincident sites, all extremizers reduce, after cancellation, to two opposite signs half a period apart. With four or more distinct sites the infimum is unattained. A quantitative estimate describes near minimizers. If adjacent sites must be at least $h$ apart, the minimum exists and we compute the exact leading coefficient of its quadratic excess energy. Minimizers then separate into two nearly antipodal clusters with explicitly selected odd multiplicities. At the parameters of the repository's four-site counterexample the infimum is $0.849687099565508$ to fifteen decimal places.

## 1. Periodic cell and results

Fix $L,\alpha>0$ and an even $N=2m$. Write $0\le x_0<\cdots<x_{N-1}<L$, repeat the cell with $x_{j+N}=x_j+L$, and set $\sigma_j=(-1)^j$. All gaps include the wrap-around gap. Put

$$
G(x)=\sum_{k\in\mathbb Z}e^{-\alpha(x+kL)^2},\qquad
Q=\sum_{i,j=0}^{N-1}\sigma_i\sigma_jG(x_i-x_j),\qquad E=1-Q/N.
$$

This is the directed energy per particle in Definition 2.1 of [1], with like-species potential $-e^{-\alpha r^2}$ and unlike-species potential $+e^{-\alpha r^2}$. The $1$ removes the single zero-distance self term of each site. Self images from all other cells are included. At a collision $E$ denotes the continuous extension of this same formula.

Set $q=e^{-\pi^2/(\alpha L^2)}$ and $c=\sqrt{\pi/\alpha}/L$. We use the sufficient, dimensionless condition $q\le 1/3$. It holds for $\alpha=1/4,L=4$ and imposes no restriction on the even integer $N$ at fixed $L$. Increasing $N$ at fixed density changes $L$.

**Theorem 1 (infimum and equality).** For $q\le 1/3$,

$$
I_N=\inf E=1-\frac{2}{N}\,[G(0)-G(L/2)]
    =1-\frac{8c}{N}\sum_{j\ge0}q^{(2j+1)^2}.
$$

In the collision closure, equality holds exactly when the signed atomic measure reduces to $\delta_b-\delta_{b+L/2}$ for some $b$ modulo $L$. Neutral coincident pairs may occur at other locations. For $N=2$ the antipodal configuration attains the minimum. For $N\ge4$ no strictly ordered configuration attains it.

**Theorem 2 (stability and a spacing constraint).** In angular coordinates $\theta=2\pi x/L$, let $A$ be the union of the arcs from each positive site to the following negative site. Let $d(A)$ be the least angular length of $A\triangle H$ over all semicircles $H$. With $\beta=q/3$,

$$
E-I_N\ \ge\ \frac{16c\beta}{N}\left[1-\cos\!\left(\frac{d(A)}4\right)\right].
\tag{1}
$$

For fixed $N\ge4,L,\alpha$ in this regime, let $M_N(h)$ denote the minimum over physical gaps at least $h$, where $0<h\le L/N$. Then

$$
M_N(h)-I_N=\Theta_{N,L,\alpha}(h^2)\qquad(h\downarrow0).
\tag{2}
$$

In particular (2) controls the **optimal** constrained energy, allowing all sites to move. Section 4 gives the leading coefficient and the cluster sizes selected by the constraint.

## 2. Reduction to a circle inequality

Write $g(\theta)=G(L\theta/(2\pi))$. Poisson summation gives the absolutely differentiable Fourier series (of every order)

$$
g(\theta)=c\left(1+2\sum_{n\ge1}q^{n^2}\cos(n\theta)\right).
$$

The distributional derivative of the indicator of $A$ is the signed site measure $\mu$. Integration by parts in both variables, with ordinary angular Lebesgue measure, gives

$$
Q_g(A)=\iint g(s-t)\,d\mu(s)d\mu(t)
      =\int_A\int_A[-g''(s-t)]\,ds\,dt.
\tag{3}
$$

The formula extends continuously to collisions; zero-length arcs vanish and adjacent occupied arcs may merge. For any single arc of angular length $a$ its two endpoints give $Q_g=2[g(0)-g(a)]$.

We record the comparison used twice below. For an even smooth periodic function $v$, suppose both $v$ and $-v''$ are nonincreasing on $[0,\pi]$. With $|A|$ fixed, the circle rearrangement inequality applied to (3) gives $Q_v(A)\le Q_v(J)$ for a single arc $J$ of the same length [2, Theorem 4.1]. The theorem requires a nonnegative kernel. Add a constant to $-v''$ to enforce this: both integrals increase by the same constant times $|A|^2$. Now $Q_v(J)=2[v(0)-v(|A|)]$ is at most $2[v(0)-v(\pi)]$ by symmetry and monotonicity. Thus a semicircle maximizes $Q_v$ even when the length of $A$ varies.

## 3. Separating the first Fourier mode

Subtract a fraction of the first mode and put $v(\theta)=g(\theta)-2c\beta\cos\theta$. To apply the comparison to $v$, it suffices to show

$$
R(q)=\sum_{n\ge2}n^4q^{n^2-1}<1-\beta/q.
$$

Indeed $|\sin(n\theta)|\le n\sin\theta$ for $0<\theta<\pi$. The contribution of the higher modes to the derivative of $-v''$ has magnitude at most $2cqR(q)\sin\theta$. For $v'$ the same bound holds with $n^2$ in place of $n^4$. In both derivatives the first mode contributes $-2c(q-\beta)\sin\theta$.

For $q\le1/3$, the first term of $R$ is at most $16/27$ and successive term ratios are at most $(3/2)^4(1/3)^5=1/48$. Hence $R\le(16/27)(48/47)<2/3$. This proves the comparison for $v$ with $\beta=q/3$. The cutoff is sufficient; no optimal threshold is asserted.

Set $z=\int_A e^{i\theta}\,d\theta$. The subtracted mode contributes exactly $2c\beta |z|^2$ to (3). The modulus for a semicircle is $2$. Since the residual $Q_v$ also has a semicircle as a maximizer,

$$
Q_g(H)-Q_g(A)\ge 2c\beta(4-|z|^2)
\quad\text{for every semicircle }H.
\tag{4}
$$

Take $\phi=\arg z$ (any $\phi$ if $z=0$) and $H_\phi=\{\cos(\theta-\phi)>0\}$. Then

$$
2-|z|=\int_{A\triangle H_\phi}|\cos(\theta-\phi)|\,d\theta.
$$

Among sets of length $s$, this last integrand has its smallest integral on the neighborhoods of its two zeros of half-width $s/4$. The integral there is $4[1-\cos(s/4)]$, by direct integration on the four flanks. Taking $s=|A\triangle H_\phi|\ge d(A)$ and using $4-|z|^2\ge2(2-|z|)$ proves (1).

Equality requires $A$ to be a semicircle up to null sets, and every such $A$ gives equality. Equivalently its distributional derivative is exactly an antipodal dipole (the reverse implication follows because two primitives with the same derivative differ by a constant). This gives the formula and equality classification of Theorem 1. Distinct sites give exactly $N$ jumps. For any even $N$, a signed dipole can be approached by leaving a positive site at zero and taking the remaining $N-1$ sites, with signs $-,+,\ldots,-$, in a shrinking neighborhood of $\pi$. This proves sharpness within the original admissible class. Inequality (1) also shows that at fixed parameters every minimizing sequence approaches the family of semicircle indicators in $L^1$, up to rotation.

## 4. The sharp cost of excluding collisions

Put $\eta=2\pi h/L$ and $D=g''(\pi)-g''(0)=4c\sum_{n>0,\ n\ {\rm odd}}n^2q^{n^2}$. Both $D>0$ and $g''(\pi)>0$; for the latter, the first Fourier term dominates the remaining second derivatives by the same $R(q)<1$ bound as above. Fix $L,N,\alpha$ throughout the limit.

**Theorem 3 (sharp expansion).** For even $N=2m\ge4$,

$$
M_N(h)=I_N+\frac{\lfloor m^2/2\rfloor}{N}\,D\,\eta^2
       +O_{N,L,\alpha}(\eta^4).
\tag{5}
$$

For all sufficiently small $h$, a minimizing cell consists, after rotation, of two groups within $O(\eta)$ in angular distance of antipodal points. Their sizes are $2k+1$ and $2l+1$, where $k+l=m-1$ and $|k-l|\le1$. This describes the multiplicities and the leading energy; it leaves higher-order site positions undetermined.

**Existence and a trial bound.** Pin one site by translation. The simplex of cyclic gaps at least $h$ is compact and nonempty for $h\le L/N$, so the minimum exists. Place one positive site at zero and a symmetric, alternating cluster of $N-1$ sites spaced by $\eta$ about $\pi$, starting and ending with a negative site. Its end gaps are $\pi-(m-1)\eta\ge\eta$. Its energy is a smooth even function of $\eta$, equal to $I_N$ at zero. Thus $0\le M_N(h)-I_N=O(\eta^2)$.

**Localization of every site.** Rotate a minimizing configuration so that the semicircle selected by the first mode in Section 3 is $H=(0,\pi)$. From (4) and the identity for $2-|z|$ we obtain

$$
\int_{A\triangle H}|\sin\theta|\,d\theta=O(\eta^2).
\tag{6}
$$

Consider a site at angular distance $r\in[\eta,\pi/2]$ from the nearer endpoint. Its two neighboring gaps are both at least $\eta$ long. On one of the two adjacent intervals of length $\eta/2$, the indicators of $A$ and $H$ disagree throughout: $A$ jumps at the site and $H$ is constant there. On this interval $|\sin\theta|\ge 2(r-\eta/2)/\pi$ by the distance-to-the-nearest-endpoint bound. By (6), $r=O(\eta)$, uniformly for all sites; sites with $r<\eta$ already satisfy the claim. Away from the two groups $A$ is constant on each of the two complementary bulk arcs. Those constant values match $H$ for small $\eta$, since a mismatch on, for example, $[\pi/4,3\pi/4]$ or its antipode would contradict (6). The jumps in the group near zero therefore start and end positive and have net sign $+1$. The signs near $\pi$ start and end negative and have net sign $-1$. Their counts have the asserted odd form with $k+l=m-1$.

**A signed variance identity.** In either group normalize its signs to start with $+1$. For its ordered offsets $u_0,\ldots,u_{2k}$ from the group endpoint, define $P=\sum_i(-1)^i u_i$ and $V=\sum_i(-1)^iu_i^2-P^2$. The sum of the signs is one, so $V$ is invariant under translating all offsets. Write its successive gaps as $a_1,b_1,\ldots,a_k,b_k$. With $u_0=0$, $P=\sum_j b_j$ and subtraction of $P^2$ gives

$$
V=2\sum_{j=1}^k b_j\sum_{i=1}^j a_i
  \ \ge\ k(k+1)\eta^2 .
\tag{7}
$$

Indeed $\sum_i(-1)^i u_i^2=\sum_j(2u_{2j-1}b_j+b_j^2)$. Formula (7) includes a singleton, for which $V=0$.

**Expansion and optimization.** Use indices $0,\pi$ for the quantities $P,V$ of the two normalized groups. Taylor expand the two within-group sums in $Q$ about zero and the between-group sum about $\pi$. The odd derivatives at both centers vanish. Localization bounds every offset by a constant times $\eta$, so the error is uniformly $O(\eta^4)$ over minimizers. Each within-group sum contributes $g(0)+g''(0)V$. The cross term contributes $-2g(\pi)-g''(\pi)[V_0+V_\pi+(P_0-P_\pi)^2]$. Hence

$$
N(E-I_N)=D(V_0+V_\pi)+g''(\pi)(P_0-P_\pi)^2+O(\eta^4).
\tag{8}
$$

The minimum of $k(k+1)+l(l+1)$ for nonnegative integers $k+l=m-1$ is $\lfloor m^2/2\rfloor$, and occurs precisely at $|k-l|\le1$. Equations (7)–(8) give the required lower bound. For an upper bound choose these balanced counts, center the two odd groups at $0,\pi$ and set every internal gap equal to $\eta$. Both $P$'s vanish by symmetry and both variances attain (7). The gaps between groups are $\pi-(m-1)\eta\ge\eta$. Applying the same Taylor expansion proves (5). Any unbalanced integer split costs a fixed positive multiple of $\eta^2$ more, which the uniform fourth-order remainder cannot offset for small $\eta$. This proves the count statement and (2).

For $N=4$ the coefficient of physical $h^2$ is $D(2\pi/L)^2/2$. For $N=6$ the balanced $3+3$ split has coefficient $4D(2\pi/L)^2/6$; a $1+5$ split with tight symmetric groups has coefficient $6D(2\pi/L)^2/6$. Thus even an admissible family reaching the unconstrained infimum can have the wrong leading coefficient once a minimum gap is imposed.

## 5. Numerical example and scope

At $(N,L,\alpha)=(4,4,1/4)$ the two original cells have energies $0.999633292157728$ and $0.924751872822186$. The limit of $(0,2-h,2,2+h)$ is $I_4=0.849687099565508$ (rounded). Several different coordinate limits may give the same signed dipole, because a neutral coincident pair can cancel anywhere in the cell. For finite positive $h$, inequality (2) addresses the best four-site placement, including nonsymmetric trials.

For the same $L,\alpha$, six sites illustrate the selection effect. The sharp coefficient of physical $h^2$ is 0.49450963 to eight decimals. Putting a singleton opposite a tight five-site cluster gives 0.74176445. On grids of 16, 24 and 32 equally spaced nodes, exhaustive enumeration gives minima 0.927980536870, 0.912984112405 and 0.907345330218, respectively. Each equals the grid energy of the symmetric $3+3$ trial to the numerical precision used. These are finite-grid checks; (5) follows from the continuous estimates.

The width condition has mathematical content. At fixed $N\ge4,L$ and $\alpha\to\infty$, the equidistant energy tends to zero: all non-self distances are bounded away from zero and the Gaussian image sums decay. Meanwhile the antipodal collision energy tends to $1-2/N>0$. Thus the same limit configuration cannot minimize for all widths. The behavior between the two regimes is left open.

The companion script checks direct image sums against Fourier sums, tests the stability estimate and inspects the spacing asymptotics. The inequalities above constitute the proof.

## References and relation to earlier work

1. L. Bétermin, H. Knüpfer and F. Nolte, *Note on crystallization for alternating particle chains*, J. Stat. Phys. 181 (2020), 803–815. The periodic cell, energy normalization and conjecture are from this paper. [DOI](https://doi.org/10.1007/s10955-020-02603-2)
2. X. Cabré, G. Csató and A. Mas, *Periodic solutions to integro-differential equations: variational formulation, symmetry, and regularity*, Theorem 4.1. We use the classical circle rearrangement inequality as stated there. Its historical sources include Baernstein–Taylor and Friedberg–Luttinger. [Article](https://doi.org/10.1080/03605302.2024.2441851)
3. M. Christ and M. Iliopoulou, *Inequalities of Riesz–Sobolev type for compact connected Abelian groups*. Quantitative stability of rearrangements on groups has a substantial prior literature. The first-mode bound here gives an explicit constant for this Gaussian energy and a freely varying occupied length. [arXiv](https://arxiv.org/abs/1808.08368)
4. P. Buttà, R. Esposito, A. Giuliani and R. Marra, *Froth-like minimizers of a nonlocal free energy functional with competing interactions*. The upstream manuscript relates its exponential-in-distance estimate to block bounds in this work. Here the differentiated periodized Gaussian is the kernel used in the circle comparison. [DOI](https://doi.org/10.1007/s00220-013-1740-z)
5. *A Gaussian counterexample and a Riesz bound for alternating particle chains*, repository manuscript. The four-site example and its local instability motivate the global minimization question here. [Revision examined](https://github.com/xiujiang4/alternating-particle-chains/tree/a48fe4c2623a29dd45edd227410a07baba400250)
