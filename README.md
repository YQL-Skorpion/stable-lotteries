AI-generated supplementary material for [*Stable Voting Rules on the Edge of Optimal Metric Distortion*](https://arxiv.org/abs/2609.08259) with limited human input, including this README :)

Everything here concerns $M(g)$, the worst-case metric distortion over all $g$-stable lotteries in all finite elections. This directory contains the certificate checkers for Section 6 and Appendix B of the paper, a manuscript on the exact optimal distortion, and a Lean formalization of narrow bounds on it. Run the commands below from this directory.

### `section_6_checker`

`section_6_checker/` contains Python scripts that verify the certificates for the paper's Section 6 and Appendix B bounds,

$$
2.1232\leq\inf_g M(g)\leq 2.1248,
$$

where $g$ ranges over continuous, nondecreasing, nonconstant activations. Python 3 and NumPy required.

```sh
python3 section_6_checker/verify.py                # upper bound; about 3 minutes
python3 section_6_checker/verify_lower_weights.py  # lower bound; about 2 seconds
```

Successful runs end with `Certificate verified` and `Lower certificate verified`, respectively, followed by the verified bound.

Each checker reads its own certificate:

- [`certificate.json`](section_6_checker/certificate.json) contains the upper-bound parameter $\lambda$, score function $\phi^\star$, and coefficients $\beta,c$. The checker uses exact rational and interval arithmetic.
- [`lower_certificate.json`](section_6_checker/lower_certificate.json) contains the lower-bound parameter $\lambda$, grid size, and dual multipliers. The checker verifies the infeasibility certificate using exact rational arithmetic.

### `optimal_g`

`optimal_g/` contains the manuscript *The Exact Optimal Metric Distortion of $g$-Stable Lotteries*, available as a [PDF](optimal_g/optimal_g.pdf) and [LaTeX source](optimal_g/optimal_g.tex). It goes beyond these bounds and finds the exact optimal distortion, over the wider class of all continuous activations $g:[0,1]\to[0,1]$. Its main result is

$$
M(g^\star)=\min_g M(g)=1+2\lambda^\star\approx 2.1246569,
\qquad 0.56232844<\lambda^\star<0.56232847.
$$

To certify the finite-dimensional inequalities that its proof reduces to, the manuscript's Appendix D uses the reference data and verification scripts in [numerical_certificates/](optimal_g/numerical_certificates/). Python 3.10+ and NumPy required, with Python optimization disabled so assertions remain active. Check the supplied file hashes before the first replay, then run all 43 checks:

```sh
python3 optimal_g/numerical_certificates/research/closure/simplified/replay_certificates.py --check-hashes
python3 optimal_g/numerical_certificates/research/closure/simplified/replay_certificates.py --all
```

A successful replay reports `All 43 selected certificate commands exited successfully.`

### `optimal_g_lean_verification`

`g-stable-lotteries-lean/` contains a Lean project that brackets this value formally, proving

$$
2.12465\leq\inf_g M(g)\leq 2.12466
$$

over all continuous activations, as in the manuscript. To read the proof, start with the main theorem, [`certified_optimalDistortion_bounds`](optimal_g_lean_verification/g-stable-lotteries-lean/OptimalG/CertifiedApproximateOptimality.lean).

macOS or Linux, Git, Python 3.8 or newer, and Lean's toolchain manager `elan` required. The project pins Lean and mathlib to version 4.32.0.

```sh
python3 optimal_g_lean_verification/g-stable-lotteries-lean/verify.py
```

The first run downloads dependencies and needs several gigabytes of disk space and several hours. Rerun the same command to resume an interrupted build. Logs are written to `optimal_g_lean_verification/g-stable-lotteries-lean/verification/`, and a successful run ends with:

```text
Verified [2.12465, 2.12466]. All 8 theorem axiom checks passed.
```
