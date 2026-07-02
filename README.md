# delay

A Rocq formalisation of the delay monad and a small monadic metalanguage,
using enhanced coinduction (`rocq-coinduction`).

## Build

```sh
make
```

Requires `rocq-coinduction`. Sources live in `theories/` under the `Delay` namespace.

## Layout (in dependency order)

| File | Contents |
|------|----------|
| `theories/Utils.v`       | general tactics (some from the coinduction framework, some hand-rolled by Roger) |
| `theories/Core.v`        | the `delay` datatype and the `observe` layer |
| `theories/Eq.v`          | termination, equitermination `==`, strong bisimilarity `~=`; `==` is an equivalence (`Proper_equi_equi`), and `equi_char` characterizes it by termination behavior |
| `theories/Bind.v`        | `bind` and its laws (`terminates_bind`, `bind_cong`) |
| `theories/MonadLang.v`   | the metalanguage `mon`, its denotation `run`, and the four monad laws |
| `theories/OldMonadLang.v`| the old delay prototype for reference |

## Notes

- We prove `==` (equitermination) is an equivalence via 
  reflexivity and symmetry properties of the transfinite chain of `equi_mon`
  and transitivity of `equi`. 
- `run_Bind`/`Mon_law_2` are proved via a big-step `evals` relation. 
Because `run`'s `Bind` re-association resist structural induction, 

and up-to-bind is unsound for weak bisimilarity.
- The development is axiom-free except `run_Bind`/`Mon_law_2`, which use
  `Eq_rect_eq` (UIP) for one GADT inversion, as in ITrees. See header of `MonadLang.v`.
