# OEIS A211417 in Lean 4

This repository is a Lean 4 proof-development workspace for the five mathematically substantive
`research open` declarations for [OEIS A211417](https://oeis.org/A211417) in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/211417.lean).

Try it in Lean4Web: [Open the standalone proof in Lean4Web](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Foeis-a211417%2Frefs%2Fheads%2Fmain%2Flean4web%2FOeisA211417Lean4Web.lean)

For

```text
a(n) = (30n)! n! / ((15n)! (10n)! (6n)!),
```

the targets are:

```text
(2n + 1) | 7a(n)
(3n + 1) | a(n)
(5n + 1) | a(n)
(2n + 1)(3n + 1)(5n + 1) | 42a(n)
a(p^k) = a(p^(k-1)) (mod p^(3k)),  p >= 5, k > 0.
```

The current FC declaration `general_divisibility` is intentionally out of scope: as written it
is vacuous because its existential integer may be `D = 0`. This repository does not count that
statement as a solution and does not include it as a target.

## Current status

Both Lean projects build successfully with Lean `v4.27.0`. All four divisibility declarations
now have complete local kernel-checked proofs. Only the independent supercongruence target still
contains an explicit `sorry`:

| Target | Status in this repository |
|---|---|
| `(2n+1) | 7a(n)` | **proved locally**; exact FC statement, no `sorryAx` |
| `(3n+1) | a(n)` | **proved locally**; exact FC statement, no `sorryAx` |
| `(5n+1) | a(n)` | **proved locally**; exact FC statement, no `sorryAx` |
| product divisibility | **proved locally** from the preceding three targets, no `sorryAx` |
| supercongruence | open; requires Jacobsthal--Kazandzidis machinery absent from mathlib |

The product theorem is therefore **not independently open**. The checked Lean lemma
`forty_two_mul_a_dvd_product_from_atomic` proves it without `sorry` from the three atomic
hypotheses. Its axiom audit is:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, both the structural lemma and the exact zero-hypothesis product wrapper now have
no `sorryAx`.

## Mathematical Explanation (AI generated)

### Why the product target follows

Set `x = 2n+1`, `y = 3n+1`, and `z = 5n+1`. Lean now checks:

```text
gcd(x,y) = 1
gcd(x,z) | 3
gcd(y,z) | 2
```

Thus `x*y | 7a(n)`, while the overlap between `x*y` and `z` divides `6`. Combining this with
`z | a(n)` gives `x*y*z | 6*7*a(n) = 42a(n)`.

### Atomic divisibility proof route

The existing proof of `(30n-1) | a(n)` uses Legendre's formula. Its reusable local term is

```text
F(n,m) = floor(30n/m) + floor(n/m)
       - floor(15n/m) - floor(10n/m) - floor(6n/m).
```

It is always nonnegative, and

```text
v_p(a(n)) = sum_j F(n,p^j).
```

Both facts are now Lean-checked in `landauTerm_nonneg` and `valuation_gap_eq_sum`. The first
atomic target also has a checked general-contribution lemma:

```text
Odd d, 9 <= d, d | 2n+1  ==>  F(n,d) = 1.
```

This is `landauTerm_eq_one_of_dvd_two_mul_add_one`, proved without `sorryAx` in both projects.

A residue audit isolates the only failures of the naive pointwise implication
`p^j | kn+1 -> F(n,p^j) = 1`:

| Atomic target | Exceptional prime powers |
|---|---|
| `k = 2` | `3`, `5`, `7` |
| `k = 3` | `2`, `5`, `8` |
| `k = 5` | `2`, `3`, `4` |

All other prime-power contributions are pointwise sufficient. For `k = 2`, the complete proof is
now formalized: a binomial-coefficient identity handles `p = 5`, the coefficient `7` handles the
first `7`-adic level, and `three_extra_landau_term` constructs a higher `3`-power whose Landau
contribution supplies the missing `p = 3` carry. The exact theorem
`seven_mul_a_dvd_two_mul_add_one_target` then follows by prime-power factorization of the defining
factorial ratio.

Its axiom audit is:

```text
[propext, Classical.choice, Quot.sound]
```

The other atomic targets use two further reductions:

```text
v₂(a(n)) = v₂(C(8n,3n))
v₅(a(n)) = v₅(C(5n,2n))
```

Adjacent-binomial identities supply the full `2`- and `5`-primary parts of `3n+1`. The same
`C(8n,3n)` identity handles the `2`-primary part of `5n+1`; its missing `3`-adic level is supplied
by a universal Landau contribution at a power of three between `9n` and `27n`.

### Supercongruence route

OEIS records the congruence as a consequence of equation (39) in Meštrović's survey, using

```text
a(n) = C(30n,15n) C(15n,5n) / C(6n,n).
```

The intended formal route is:

1. formalize the required Jacobsthal--Kazandzidis binomial congruence;
2. apply it to `(30,15)`, `(15,5)`, and `(6,1)`;
3. show `C(6p^k,p^k)` is a `p`-adic unit for `p >= 5`;
4. cancel the denominator modulo `p^(3k)` and recover the FC integer-divisibility statement.

Mathlib currently contains Lucas-style binomial congruences but not the needed full
Jacobsthal--Kazandzidis theorem, so this is mathematically known but a larger formalization task
than the original one-target scaffold suggested.

## Files

| Directory | Purpose |
|---|---|
| `lean/` | Exact FC statements, pinned to Formal Conjectures commit `638da20e...` |
| `lean4web/` | Standalone mathlib-only copies suitable for Lean4Web |

The two source files are:

```text
lean/OeisA211417FC.lean
lean4web/OeisA211417Lean4Web.lean
```

## Verification

Formal Conjectures version:

```bash
cd lean
lake build
```

Standalone version:

```bash
cd lean4web
lake build
```

Audit remaining trust placeholders with:

```bash
rg -n '^\s*(axiom\b|sorry\b|admit\b)|native_decide|^\s*unsafe\b' lean lean4web --glob '*.lean'
```

The current expected result is one `sorry` occurrence per target file, belonging only to the
supercongruence. Full completion requires
zero such placeholders and `#print axioms` output with no `sorryAx` or custom axioms.

### One-screen solved-target audit

For a deliberately obvious audit, the end of each Lean source collects thin aliases of all four
completed exact targets:

```text
target_seven_mul_a_dvd_two_mul_add_one_target
target_a_dvd_three_mul_add_one_target
target_a_dvd_five_mul_add_one_target
target_forty_two_mul_a_dvd_product_target
```

Each alias is followed immediately by `#check` and `#print axioms`. Running `lake build` prints
the four exact statements together, followed by this axiom set for every one of them:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, none of these four audit targets depends on `sorryAx`. The separate
`supercongruence_target` audit appears before this solved block and still reports `sorryAx`, so
the remaining gap is explicit rather than hidden among the solved targets.

## Sources

- [OEIS A211417](https://oeis.org/A211417)
- [Formal Conjectures `OEIS/211417.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/211417.lean)
- [The existing `(30n-1) | a(n)` Lean proof](https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/211417.wip.lean)
- Romeo Meštrović, [*Wolstenholme's theorem: Its Generalizations and Extensions in the Last
  Hundred and Fifty Years*](https://arxiv.org/abs/1111.3057), equation (39)

## AI Usage Disclosure

This formalization is assisted by ChatGPT 5.6 sol and Codex GPT 5.6 sol with xhigh reasoning.
