# Busy Beaver in Bend

- Run `bend guide` before writing Bend. The installed compiler, `~/.bend/bin/bend` 2.0.38, is the authority on syntax and Base.
- `LAWS.bend` is William's. Bring any change to a law to him as a proposal, with the reason.
- The gate is `bend PROOF.bend --verdict`. Report its exact output.
- In laws, use helpers from imported modules, declared above their use, and write constructors qualified (`TM.Stop{}`). Keep proof content out of erased (`-`) fields.
- Write runtime code first-order: pass state through named functions, not closures.
- Give numbers the checker must evaluate a binary representation once they pass a few thousand.
- Record decisions, measurements and their sources in `DEVELOPMENT.md`.
