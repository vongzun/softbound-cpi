# softbound-cpi

## Environment

coq 8.4pl3 / ocaml 4.01.0 / ubuntu 14.04

## Execution

```
coq_makefile Axioms.v CSemantics.v CSyntax.v Envs.v Libs.v Props.v Types.v
make
```

## Results

Compilation will fail because the proof is not complete yet. 
But we fixed some part of proofs to fit CPI (code-pointer intergrity).
