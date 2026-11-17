# harness/bfv-rns — OpenFHE's BFV RNS multiplications, modelled and measured

Python models (exact big-integer / `Fraction` arithmetic, standard library only) of the four
multiplication techniques of OpenFHE's BFVrns — `HPS`, `HPSPOVERQ`, `HPSPOVERQLEVELED`, `BEHZ` —
written limb by limb from the C++ of upstream OpenFHE v1.6.1 (b59e1f29; line numbers below and in the
docstrings are v1.6.1's), with the library's
representative choices. They exist to validate, numerically, the constants `(U, ρ)` with which each
technique meets the component-level hypothesis of the general "approximate multiplication"
theorem:

* lifts `A_i = centred(a_i) + Q·u_i`, `B_i = centred(b_i) + Q·v_i`, `‖u‖∞, ‖v‖∞ ≤ U`;
* `T = A ⊗ B` over `ℤ[X]/(X^N+1)`;
* output `X_j ≡ out_j (mod Q)` with `2·|Q·X_j − t·T_j| ≤ Q·ρ` coefficientwise.

Nothing here is trusted by the Lean development; it is evidence for the numbers that go into it.

| file | contents |
|---|---|
| `rnsbfv.py` | the models: `switch_crt_basis`, `expand_crt_basis`, `fast_expand_p_over_q`, `scale_and_round`, `expand_ql_hat`, `smmrq`, `fast_rns_floor_q`, `fast_base_conv_sk`; `mul_hps`, `mul_poverq`, `mul_leveled`, `mul_behz`; the textbook `mul_textbook`; `measure` (observed `U`, lift excess, `2|Q·X − t·T|/Q`); the float models `Exact`, `Double`, `Adversarial`. Each docstring cites the C++ it mirrors. |
| `bounds.py` | the formulas: `hps`, `poverq`, `leveled`, `behz` return `U`, `rho`, `eta` (a bound on `max|lift| − Q/2`) and the side condition; `double_e_sw`, `double_e_sr` (binary64 error of the two float sums); `lift_from_eta`; `leveled_keyswitch`; `bv_ks_bound`. |
| `validate.py` | the validation run (below). Exit status 1 if any bound is violated. |
| `find_levels_to_drop.py` | replica of `FindLevelsToDrop` (`bfvrns-leveledshe.cpp:98-198`, the v1.6.1 formula: base-2 logs, cushion `3·depth`): the number of limbs `HPSPOVERQLEVELED` drops inside `EvalMult` / `EvalSquare` / `RelinearizeCore` / `EvalFastRotationPrecompute`, from the parameters and the operand's `noiseScaleDeg`. `python3 find_levels_to_drop.py --ring-dim 16384 --t 65537 --dcrt-bits 60 --size-q 3` prints the table per degree. |

## Running

```
python3 validate.py                 # default --trials 200; about one minute
python3 validate.py --trials 300    # the run quoted in the analysis report (about two minutes)
python3 validate.py --quick --trials 20 --sections 135
```

Sections of `validate.py`:

1. **Component level, tiny parameters** — `N ∈ {2,4,8}`, `t ∈ {3,17,257}`, `k ∈ {2,3,4}` limbs
   (8-bit primes; 20-bit primes for the leveled variant, whose `ρ ≈ D·t·N·(1+2k)` must stay below
   `Q` for the check to mean anything), every technique, every internal drop count. Operands:
   uniform; extreme coefficients `±(Q−1)/2` and neighbours; all-equal-sign polynomials; values that
   maximise the fast-conversion overshoot (`y_i = q_i − 1` in every limb); engineered worst-case
   pairs. Two float models: `Exact` (idealised) and `Adversarial` (`SwitchCRTBasis` takes the other
   representative whenever `x/Q` is within `1/64` of `1/2`; every `ScaleAndRound` is off by up to
   one unit). Checks observed `|u| ≤ U`, lift excess `≤ eta`, `2|Q·X − t·T|/Q ≤ rho`, and reports
   the tightness `observed/rho`.
2. **IEEE binary64 on 60-, 45- and 30-bit limbs** — the float sums evaluated exactly as the C++
   does (`Double`), compared with their exact values; `(U, ρ)` with the `double_e_*` tolerances.
3. **End to end** — ternary secret, fresh ciphertexts, multiply, then: the result decrypts to the
   product; the contract quantities of `Spec.TraceBFV` (`k_a`, `k_b`, `D`) are within
   `mulLift = ⌊(2+N)/2⌋ + U·(1+N)` and `mulRound = ρ·(1+N+N²)`; the noise is within
   `Challenge.BFV.mulBound` with those two numbers.
4. **Leveled key switching** — BV digits (centred residues), internal drop to `Q_l`, multiply back
   by `Q/Q_l`; the phase error against `bounds.leveled_keyswitch`.
5. **Informative** — with a side condition deliberately broken the bound fails (HPS with
   `R < t·N·Q`, BEHZ with `m_sk` too small); under P-over-Q the two copies of a squared operand
   get different lifts for boundary coefficients; idealised HPS equals textbook `bfvMul`.

## What the models say (summary; derivations are in the docstrings of `bounds.py`)

`k` = limbs of `Q`; `P` (or `R`, `P_l`) the auxiliary modulus; `D = Q/Q_l`; `e_sw`, `e_sr`,
`e_sr1` the absolute errors of the float sums (0 for the idealised algorithm).

| technique | `U` | `ρ` | side condition |
|---|---|---|---|
| HPS | `0` (`1` with floats) | `⌈1 + 2e_sr⌉` | `t·N·Q·(1+2e_sw)² + 2 + 2e_sr ≤ R·(1−2e_sw)` |
| HPSPOVERQ | `1` | `⌈1 + 2e_sr + 2·t·N·k·Q·(1+2e_sw)/P⌉` | `k/P + e_sw < 1/2` |
| HPSPOVERQLEVELED, drop `≥ 1` | `1` | `⌈D(1+2e_sr) + t·N·D·((1+2e_sr1)(1+2e_sw+2k/P_l) + 2k·Q_l(1+2e_sw)/P_l)⌉` | `k/P_l + e_sw < 1/2` |
| BEHZ | `1` | `2k` | `t·N·Q·(m̃+2(k−1))² + 2k·m̃² ≤ m̃²·B·(m_sk − 1 − 2k_B)` |

Two facts the numbers above hide:

* `U = 1` is only reached by coefficients at the boundary `±Q/2`; every lift satisfies
  `|A_i| ≤ Q/2 + eta` with `eta/Q` tiny (`k·Q/P`, `(k−1)/m̃`, `D/2Q`, float `e_sw`). A hypothesis
  on the norm of the lift gives `mulLift = ⌊((Q+2·eta)(1+N·B_s) + Q)/(2Q)⌋` (`lift_from_eta`),
  essentially the textbook value, where `U = 1` gives three times it.
* binary64 `ScaleAndRound` on 60-bit limbs is off by hundreds of units, not by one
  (`double_e_sr`; measured in section 2).
