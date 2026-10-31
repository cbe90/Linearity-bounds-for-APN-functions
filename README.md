# Linearity bounds for APN functions

**Authors:** Christof Beierle and Lukas Kölsch

## Proven theorems

Let $F:\mathbb F_2^n\to\mathbb F_2^n$ be APN and $N=2^n$.
Write $\mathcal L_k(F)$ for the $k$-th largest absolute Walsh coefficient over
all nonzero components, counted with multiplicity, and $\mathcal L(F)=\mathcal L_1(F)$.
Let $q$ count the nonplateaued nonzero components; a component is plateaued when
all its nonzero Walsh coefficients have the same absolute value.

1. **Upper bounds on the linearity.** If $n\ge5$, then
   $$\mathcal L(F)\le N-6.$$
   If $n$ is also even, then
   $$\mathcal L(F)\le N-\frac{\sqrt N}{4}-2.$$

2. **Improved odd-dimensional bound.** If $n\ge5$ is odd,
   $p\in\{\lfloor\sqrt N\rfloor,\lceil\sqrt N\rceil\}$,
   $2^s\mid p$, $2^{s+1}\nmid p$, and $s\ge5$, then
   $$\mathcal L(F)\le N-2^{s-2}-2.$$

3. **Bounds on the largest absolute Walsh coefficients.** If $n\ge4$ and $1\le k\le N(N-1)$ is an integer, then
   $$\mathcal L_k(F)\le\frac{N}{\sqrt k}
     \sqrt{1+\frac{2^{k-1}-1}{N}}.$$
   Moreover,
   $$\mathcal L_2(F)\le2\left\lfloor\frac N3\right\rfloor<\frac{2N}{3},
   \qquad\mathcal L_4(F)\le\frac N2.$$

4. **A high absolute Walsh coefficient is isolated.** If $n\ge4$, $0<\varepsilon<1$, and
   $\mathcal L(F)=(1-\varepsilon)N$, then
   $$\frac{\mathcal L_2(F)}N\le\frac\varepsilon2+
     \sqrt{\varepsilon-\frac{3\varepsilon^2}{4}+\frac1N}.$$

5. **Linearity bounds from nonplateaued components.** Suppose $n\ge4$.
   If $n$ is odd and $q>0$, then
   $$\mathcal L(F)^2\le N\bigl(1+\sqrt{q(N-1)}\bigr).$$
   If $n$ is even, $1/2\le C<1$, and
   $q\le\frac{4C-C^2-1}{4}N+1$, then $\mathcal L(F)\le CN$.

## Verification

Run

```sh
lake exe cache get
lake build
lake env lean Verification.lean
./scripts/verify-comparator.sh
```

## Disclosure of AI Use
The formalization was created with ChatGPT Pro (GPT-6 Astra and Codex). 
Besides the correctness of the metadata, the authors reviewed the Challenge.lean file to make sure it faithfully encodes the intended meaning of the theorems.
