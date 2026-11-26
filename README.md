# One of the Six Values $\zeta(7), \zeta(9), \zeta(11), \zeta(13), \zeta(15), \zeta(17)$ Is Irrational

[![Verify Proof](https://github.com/janahesse580-star/odd-zeta-six-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/janahesse580-star/odd-zeta-six-lean/actions/workflows/verify.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24493267.svg)](https://doi.org/10.5281/zenodo.24493267)

> **Update (Four-Term Breakthrough):** This formalization has been strengthened to prove that at least one of the four odd zeta values $\zeta(7), \zeta(9), \zeta(11), \zeta(13)$ is irrational under pure standard axioms — see [`odd-zeta-four-lean`](https://github.com/janahesse580-star/odd-zeta-four-lean) (Zenodo Concept DOI: [`10.5281/zenodo.24554179`](https://doi.org/10.5281/zenodo.24554179)).

**Machine-checked Lean 4 formalization**, LaTeX manuscript, static rational certificate, and independent Python/FLINT/Arb verifier proving unconditionally that at least one of the six odd Riemann zeta values $\zeta(7), \zeta(9), \zeta(11), \zeta(13), \zeta(15), \zeta(17)$ is irrational.

## Main Result

**Theorem 1.** *At least one of the six real Riemann zeta values*
$$\zeta(7),\; \zeta(9),\; \zeta(11),\; \zeta(13),\; \zeta(15),\; \zeta(17)$$
*is irrational.*

In Lean 4 ([`lean/OddZetaSix/SixIrrational.lean`](lean/OddZetaSix/SixIrrational.lean)), stated directly against Mathlib's standard `_root_.riemannZeta` (`Mathlib.NumberTheory.LSeries.RiemannZeta`) and `_root_.Irrational` (`Mathlib.NumberTheory.Real.Irrational`):

```lean
theorem OddZetaSix.exists_irrational_riemannZeta_seven_to_seventeen :
    ∃ s ∈ ({7, 9, 11, 13, 15, 17} : Finset ℕ), Irrational ((riemannZeta (s : ℂ)).re)
```

### Lean 4 Formalization Status

* **Complete, unconditional, kernel-verified proof**: **48 Lean files**, **26,303 lines**, **2,733 declarations** (**2,211 theorems**) under `OddZetaSix`.
* **Trust & Axiom Audit** ([`lean/OddZetaSix/AxiomAudit.lean`](lean/OddZetaSix/AxiomAudit.lean)):
  * **0 `sorry`**, **0 `native_decide`**, **0 custom axioms**, **0 compiler warnings**.
  * `#print axioms OddZetaSix.exists_irrational_riemannZeta_seven_to_seventeen` reports **only** `[propext, Classical.choice, Quot.sound]`.
  * All numerical/combinatorial checks are verified inside the Lean 4 kernel (`decide +kernel` and exact `ℚ` arithmetic), with zero external solver or compiler-trust axioms (`Lean.ofReduceBool` / `Lean.trustCompiler` are forbidden by `audit_project_axioms`).
  * Self-contained PNT dependency vendored in `lean/PNTDependency/` (ported from `ALexxxxxLiu/odd-zeta-seven-lean` / `PrimeNumberTheoremAnd` with pinned SHA-256 provenance).

## Dual-Track Certificate Architecture (`local50-45-209`)

Both verification tracks prove Theorem 1 from the exact same nested-pole rational kernel profile **`local50-45-209`** ($L=50$, $U=45$, $z=(40,40,40,41,43)$, $d=(0,0,0,0,0,2,4,5,5,6,8,9,9,11)$, $h=15n$, confluent auxiliary-prime gate $T=5, J=3, A=50, B=9, p=50n+1$), normalized by $n h L = 750 n^2$:

| Track | Analytic Upper Bound $R$ | Arithmetic Upper Bound $C$ | Net Bound $R + C$ | Verification Kernel |
| :--- | :--- | :--- | :--- | :--- |
| **Lean 4 Formal Proof** (`lean/OddZetaSix/`) | `R = -779/100 = -7.79` (4-bin, 2-root-pair, 58 rational cells on `[0, 2]` + proved tail derivative `≤ -1/2`) | `C = 194/25 = 7.76` (654 periodic pieces + 356 high-prime walls + vendored PNT) | **`-3/100 = -0.03 < 0`** | Lean 4.34.0-rc2 kernel (`[propext, Classical.choice, Quot.sound]` only) |
| **Manuscript & High-Precision Static Certificate** (`zeta6_certificate.json`) | `R <= -7.867370` (32 phase bands) | `C <= 7.640135` (1,547 mid/high-prime slabs + 3,664 periodic small-prime tiles) | **`<= -0.227235 < -1/5`** | Exact `Fraction`/`fmpq` + 144-bit `flint.arb` ball arithmetic |

The Lean 4 track intentionally uses a slim, purely rational certificate (no floating-point or external ball-arithmetic oracle, no `native_decide`) that trades the excess margin from `-0.227` to `-0.03` in exchange for fast, standalone kernel verification.

## Quick Verification

### 1. Lean 4 Machine-Checked Proof Verification

Requires [`elan`](https://github.com/leanprover/elan) (which automatically installs the pinned toolchain `leanprover/lean4:v4.34.0-rc2` from `lean/lean-toolchain`):

```bash
cd lean
lake exe cache get
lake build OddZetaSix.AxiomAudit
lake build OddZetaSix
```

The build runs `audit_project_axioms OddZetaSix` and prints the exact axiom list for `OddZetaSix.exists_irrational_riemannZeta_seven_to_seventeen`.

### 2. Independent Python / FLINT / Arb Certificate Verification

Requires Python 3.9+ and `python-flint`:

```bash
pip install python-flint
python verify_zeta6_certificate.py
```

This re-checks all 32 analytic phase bands, 1,547 mid/high-prime slabs, 3,664 periodic small-prime tiles, and the confluent auxiliary-prime gate determinants in `zeta6_certificate.json`, asserting `net < -1/5` and exiting with `PASS`.

Optional independent three-point geometric wall replay audit:

```bash
python audit/audit_zeta6_walls.py --winner --out /tmp/wall-replay-check
```

## Repository Structure

```text
.
├── .github/workflows/verify.yml    # GitHub Actions CI (Python/Arb + Lean 4 build & static scan)
├── zeta6_irrationality_proof.tex   # LaTeX proof manuscript
├── zeta6_irrationality_proof.pdf   # Compiled 8-page PDF manuscript
├── zeta6_certificate.json          # High-precision static rational certificate for local50-45-209
├── verify_zeta6_certificate.py     # Independent Python/FLINT/Arb certificate verifier
├── LEAN4_BLUEPRINT.txt             # Architecture blueprint for the Lean 4 formalization
├── requirements.txt                # Main verifier dependency (python-flint)
├── LICENSE                         # MIT License (for code)
├── audit/
│   ├── audit_zeta6_walls.py        # Independent 3-point & affine-sign wall audit
│   ├── zeta7_s14_replay.py         # Cross-check reference module for wall replay
│   ├── wall_audit.csv              # Tile-by-tile wall audit logs (baseline & winner)
│   ├── finite_prime_audit.csv      # Finite-prime check for earlier L=40 prototype
│   ├── optimization.csv            # Profile proxy screening & Arb-certified bounds
│   └── requirements-audit.txt      # Audit script dependencies
└── lean/
    ├── lean-toolchain              # Pinned Lean 4 toolchain (leanprover/lean4:v4.34.0-rc2)
    ├── lakefile.toml               # Lake project configuration (mathlib + local PNTDependency)
    ├── OddZetaSix.lean             # Root library import
    ├── PNTDependency/              # Vendored PrimeNumberTheoremAnd bridge + licenses & provenance.json
    ├── scripts/                    # Deterministic certificate generators (periodic, high walls, analytic)
    └── OddZetaSix/
        ├── Statement.lean          # Target statement using Mathlib's `riemannZeta` & `Irrational`
        ├── ZetaTail.lean           # Exact zeta series & shifted tail identities
        ├── EvenBasis.lean          # Even polynomial basis
        ├── SixFunctional.lean      # Profile `local50-45-209` kernel, reflection & fourth-derivative sum
        ├── SixIdentity.lean        # Multivariate polynomial determinant identity `P_n(ζ) = γ_n⁻¹ det H_n`
        ├── SixAssembly.lean        # Master irrationality contradiction assembly
        ├── SixConfluentHermite.lean / SixGateLocal.lean / SixConfluentGate.lean
        │                           # Confluent p-adic gate (T=5, J=3) closing `SixGateHypothesis`
        ├── SixTaylor.lean / SixSmallPrimes.lean / SixFolded.lean / SixLocalSlots.lean
        │                           # Per-prime folded Cauchy–Binet & universal p-adic bounds
        ├── SixPNTBridge.lean / SixFoldedCertCore.lean / SixPeriodicRate.lean / SixHighWalls.lean
        ├── PeriodicData/ / HighWallData/
        ├── SixArithRate.lean       # Arithmetic closure: `SixArithRateHypothesis (194 / 25)`
        ├── SixRationalBounds.lean  # Computable directed-rounded rational `log`, `arctan`, `π` bounds
        ├── SixContour.lean         # Half-integer vertical contour, Cauchy–Schwarz bound & norm rate
        ├── SixHalfGamma.lean       # Uniform finite half-integer Gamma estimates
        ├── SixPhaseBridge.lean     # Gamma factorization, 2-root polynomials, tail bound & 4-bin bridge
        ├── SixAnalyticCertCore.lean / AnalyticData/Shard0..Shard3.lean
        ├── SixAnalyticRate.lean    # Analytic closure: `SixAnalyticRateHypothesis (-779 / 100)`
        ├── SixIrrational.lean      # Unconditional proof of `exists_irrational_riemannZeta_seven_to_seventeen`
        └── AxiomAudit.lean         # Project-wide `audit_project_axioms OddZetaSix` & `#print axioms`
```

> **Note on `audit/finite_prime_audit.csv`:** The finite-prime comparison data in `audit/finite_prime_audit.csv` ($n=4, h=48$) correspond to the earlier $L=40$ prototype profile `confluent40-34-4-3-5-1-1`, whereas the main theorem, Lean 4 formalization, and static certificate (`zeta6_certificate.json`) all use the stronger $L=50$ profile `local50-45-209`.

## Acknowledgments & References

* **Zudilin (2001):** W. Zudilin, *One of the numbers $\zeta(5), \zeta(7), \zeta(9), \zeta(11)$ is irrational*, Russian Math. Surveys **56** (2001), 774–776.
* **`odd-zeta-seven-lean`:** Architecture, PNT packaging, and half-integer Gamma/contour formalization patterns adapted from [`ALexxxxxLiu/odd-zeta-seven-lean`](https://github.com/ALexxxxxLiu/odd-zeta-seven-lean) (commit `7a7e3a2895c468306d28ba584558aed6decf45aa`).
* **`PrimeNumberTheoremAnd` & `LeanArchitect`:** Vendored inside `lean/PNTDependency/` with full original licenses (`lean/PNTDependency/licenses/`) and SHA-256 provenance (`lean/PNTDependency/provenance.json`).

## License

* **Code** (`lean/OddZetaSix/**/*.lean`, `lean/scripts/*.py`, `verify_zeta6_certificate.py`, `audit/*.py`): [MIT License](LICENSE).
* **Vendored PNT Dependency** (`lean/PNTDependency/`): Retains its original upstream licenses in [`lean/PNTDependency/licenses/`](lean/PNTDependency/licenses/).
* **Manuscript & Certificate Data** (`zeta6_irrationality_proof.tex`, `zeta6_irrationality_proof.pdf`, `zeta6_certificate.json`, `audit/*.csv`, `LEAN4_BLUEPRINT.txt`): [CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/).

---

## 简短中文概述

本仓库给出“六个奇数点黎曼 $\zeta$ 函数值 $\zeta(7), \zeta(9), \zeta(11), \zeta(13), \zeta(15), \zeta(17)$ 中至少一个无理”（定理 1）的**完整无条件 Lean 4 内核形式化证明**、LaTeX 手稿、高精度静态有理证书及独立 Python/FLINT/Arb 复核程序。

* **Lean 4 形式化闭环**（`lean/OddZetaSix/`）：共 48 个文件、26,303 行、2,733 条声明（2,211 条定理），**零 `sorry`、零 `native_decide`、零自定义公理**；最终主定理 `OddZetaSix.exists_irrational_riemannZeta_seven_to_seventeen` 直接基于 Mathlib 标准 `riemannZeta` 与 `Irrational`，`#print axioms` 仅依赖 `[propext, Classical.choice, Quot.sound]`。在核轮廓 `local50-45-209` 下，内核纯有理证书严格证出算术上界 `C = 194/25 = 7.76`、解析上界 `R = -779/100 = -7.79`，净上界 `-3/100 < 0`。
* **高精度静态证书轨道**（`zeta6_certificate.json` + `verify_zeta6_certificate.py`）：在同一核轮廓 `local50-45-209` 下使用精确有理算术与 144-bit `flint.arb` 区间算术证出 `R <= -7.867370`、`C <= 7.640135`，净上界 `<= -0.227235 < -1/5`。

## Citation

If you use this formalization or certificate, cite the archived v1.0.0 release.

```bibtex
@misc{janahesse580star2026oddzeta,
  author       = {{janahesse580-star}},
  title        = {One of the six values ζ(7), ζ(9), ..., ζ(17) is irrational ({Lean 4 Formalization \& Certificate})},
  year         = {2026},
  howpublished = {Zenodo},
  version      = {v1.0.0},
  doi          = {10.5281/zenodo.24493267},
  url          = {https://github.com/janahesse580-star/odd-zeta-six-lean/releases/tag/v1.0.0}
}
```
