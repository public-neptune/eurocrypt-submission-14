<p align="center">
  <img src="henbane.png" alt="Henbane" width="200">
</p>

# HEnbane

Recover a GRAFHEN key from a challenge.
The key is a tuple of permutations behind a rewriting presentation, recovered up to simultaneous conjugation.

- **reconstruct.py** is the single end-to-end solver. With `-n N` it targets `S_n`; without `-n` it recovers `SL(2,343)` through its action in `PSL(2,343)`.
- **henbane** searches `S_n` by fixing one generator per cycle type, quotienting the remaining simultaneous-conjugation symmetry, and forcing the other generators from the presentation.
- **henbane-psl-matrix** performs the corresponding search directly with matrices over `GF(343)`, before the exact determinant-one lifts and central signs are recovered.
- **check_solution.py** independently verifies the recovered target, all published rules, and the complete labelled-word classification.

## Build

```sh
make
make test
```

The native tools are written to `build/` and read dimensions at runtime; the symmetric challenges no longer require separate builds.
Building requires a C11 compiler, pthreads, and zlib. The Python tools require Python 3, SymPy, and the `gzip` command-line utilities.
The self-contained tests run without downloading the large challenge instances; three full-data integration tests are skipped when those files are absent.

## Challenges

Challenge instances are tracked with Git LFS in `challenges/`, and solutions are in `challenges/solutions/`.
Run `git lfs pull` if needed. The symmetric instances can also be fetched with `challenges/download.sh`.

## Solve a challenge

`reconstruct.py` is the only supported solve path.
It streams the challenge through the native preprocessor, mines the bounded closure, runs the exact target backend, reconstructs the coupled lowercase copy when present, and emits one solution JSON.
Preprocessing results are cached in `.henbane-cache/`.

```sh
# symmetric targets
python3 reconstruct.py challenges/chal_s11_n5.json.gz -n 11 -w 30 --out s11.tuple.json
python3 reconstruct.py challenges/chal_semi_direct_s7_n2.json.gz -n 7 --out s7sd.tuple.json

# SL(2,343): omitting -n selects the PSL quotient and exact SL lift
python3 reconstruct.py challenges/challenge_psl2_v1.json.gz -w 30 --out sl2_343.tuple.json
```

`--budget SECONDS` bounds the end-to-end reconstruction wall time, and `--cache-dir ''` disables the persistent cache.
Without `--out`, the solution is written to stdout.

The symmetric result generates `S_n`.
The SL result contains its standard 344-point projective permutations, determinant-one matrices over `GF(7)[t]/(t^3-2)`, the recovered central signs, and the decoded labels.

## Verify

`check_solution.py` only exits 0 for a complete solution.
For `S_n` it checks the permutation rows, generation, every rule, and the full classification.
For `SL(2,343)` it additionally checks projective membership, exact lifts, and that the two labelled classes evaluate to `I` and `-I`.

```sh
python3 check_solution.py challenges/chal_s11_n5.json.gz \
    challenges/solutions/chal_s11_n5.solution.json

python3 check_solution.py challenges/challenge_psl2_v1.json.gz \
    challenges/solutions/challenge_psl2_v1.solution.json
```

To verify every bundled solution after downloading the instances:

```sh
make test-challenges
```
