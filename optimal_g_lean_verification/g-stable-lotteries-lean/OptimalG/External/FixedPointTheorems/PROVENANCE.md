# Vendored Brouwer fixed-point theorem

Source: https://github.com/harfe/fixed-point-theorems-lean4

Pinned commit: `770940ddf9878cf61952ed53d910b92bca841838` (Lean and Mathlib v4.32.0).

License: MIT, copyright (c) 2026 harfe; see `LICENSE`.

Only the five source files needed for Brouwer are included. Imports of sibling
files are rewritten from `FixedPointTheorems.` to
`OptimalG.External.FixedPointTheorems.`; their proof bodies are unchanged.
These files are compiled against this project's pinned Mathlib and Lean kernel.

Original source hashes:

- `cubical_sperner_prep.lean`: upstream SHA256 `dbc747f080b54b79ffc77f1adacec7c964daf56dc5210c0ddff1350b42343f43`
- `cubical_sperner.lean`: upstream SHA256 `edd0295e8f0ae1e572d82705e89594f7069796877572563c9750a3d82ab0b005`
- `apply_cubical_sperner.lean`: upstream SHA256 `d059b34aa7ad20cd07020eed07fa7a217f67fe7c2c6324e94345ab85d68b50ee`
- `convex_homeos.lean`: upstream SHA256 `c9ee9d5b6ce22a8d84d1b391f7a77de2e12a5a13c5cb12f723b61e287436269a`
- `brouwer.lean`: upstream SHA256 `b014d761a559abbb87eebe4299191571c85de37f2d967ef0ee16e1ec2148d7de`
