# lean4-nlp

Algebra-first classical natural-language processing in Lean 4.

> **Status: pre-alpha.** The library has substantial verified kernels, but it is not yet a
> drop-in Stanford CoreNLP replacement and does not ship pretrained language models.

`lean4-nlp` keeps reusable algorithms functional and exposes loading, cancellation, validation,
and bounded corpus concurrency through the `Nlp.NLP` effect API. It is dependency-free beyond
Lean's standard library and is pinned to Lean 4.33.1.

## Implemented today

- typed algebra and distinct score domains for recognition, counting, probability, Viterbi, and
  min-plus costs;
- immutable annotation layers and both functional and effectful annotator surfaces;
- CFG/CNF structures, lossless tree binarization, dense treebank induction, and checked grammar
  compilation;
- semiring-generic CKY, compiled sparse/dense CKY, one-best extraction, and source-preserving
  Viterbi derivations;
- linear-chain dynamic programming and a smoothed bigram HMM tagger;
- CoNLL-U and Penn Treebank readers, bracket/chunk/tagging metrics, and EVALB-compatible scoring;
- cancellation-aware, order-preserving bounded parallel corpus traversal.

The broader CoreNLP surface—tokenization, morphology, NER, dependency parsing, model formats, and
production CLI/package ergonomics—is still incomplete.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run:

```text
lake build NlpCore
lake build NlpTests
lake build parallel-benchmark
```

`lake build` builds the public `NlpCore` library. `NlpTests` compiles the full theorem and
regression suite. The benchmark is intentionally separate from the library.

## A checked functional example

This HMM example is mirrored by `NlpTests.Readme`, so CI compiles the API and checks its result.

```lean
import Nlp

open Nlp Nlp.Sequence

def training : Array (Array (Tok × Nat)) :=
  #[#[(10, 0), (11, 1)], #[(10, 0), (11, 1)], #[(10, 0), (10, 0)]]

#eval
  let model := Hmm.estimate training 2
  model.decode #[10, 11]
-- #[0, 1]
```

Pure kernels remain available under `Nlp.IO`, `Nlp.Parse`, `Nlp.Sequence`, and `Nlp.Eval`. For
applications, `Nlp.NLP` is the preferred boundary: it provides typed failures, configuration,
cancellation, model validation, effectful annotation, parsing, file operations, and bounded
parallel traversal. `Nlp.Ann.lift` and `Nlp.NLP.annotatePure` expose the same pure annotators
without moving effects into their hot path.

## Algorithm sources and implementation contributions

The established algorithms are credited to their primary specifications:

- semiring parsing and generalized inside computation: Joshua Goodman,
  [“Semiring Parsing”](https://aclanthology.org/J99-4004/), 1999;
- parsing as deduction: Stuart Shieber, Yves Schabes, and Fernando Pereira,
  [“Principles and Implementation of Deductive Parsing”](https://doi.org/10.1016/0743-1066(95)00035-I),
  1995;
- hidden Markov estimation and decoding: Lawrence Rabiner,
  [“A Tutorial on Hidden Markov Models”](https://doi.org/10.1109/5.18626), 1989;
- CoNLL-U syntax: the [Universal Dependencies format specification](https://universaldependencies.org/format.html);
- constituency scoring: Sekine and Collins' [EVALB](https://nlp.cs.nyu.edu/evalb/), including
  the Brooks and Ellis updates.

Repository-specific implementation work is kept explicit in code and history:

- adaptive compiled CNF storage chooses a flat dense pair-offset table or a sparse hash index;
- lexical buckets and nonzero-cell lists avoid scanning irrelevant productions and chart rows;
- width-major triangular charts use flat storage with checked layout theorems;
- Viterbi backpointers preserve source production ordinals and deterministic tie-breaking;
- imperative array kernels are related to functional folds by refinement theorems;
- typed score newtypes prevent accidental cross-domain arithmetic while retaining specialized hot
  paths;
- the effectful scheduler balances coarse chunks, caps dedicated threads, suppresses nested
  fan-out, observes cooperative cancellation, and preserves input/error order.

These are engineering and verification contributions in this repository, not claims to have
invented CKY, Viterbi decoding, HMMs, semiring parsing, CoNLL-U, or EVALB.

## Correctness and trust boundary

The production library contains no `sorry`, `admit`, `axiom`, `partial`, or `unsafe`
declarations. Structural laws and optimized/reference equivalences are proved where their stated
hypotheses hold. Numerical Float APIs state narrower operational contracts rather than pretending
IEEE-754 arithmetic satisfies exact semiring laws.

The test suite also uses `native_decide` for executable regression properties. Those checks rely
on Lean's native compiler/runtime for evaluation; they should not be confused with fully
kernel-reduced proof terms.

## Relationship to Stanford CoreNLP

This is an independent implementation inspired by classical NLP tasks and published algorithm
specifications. It is not affiliated with Stanford University or the Stanford CoreNLP project.
No CoreNLP source code, model files, or generated model artifacts are included.

## Licensing

A project-wide license has not yet been selected; until a root `LICENSE` is added, normal
copyright restrictions apply. The public-domain EVALB regression fixtures retain their own
license in `NlpTests/Fixtures/Evalb/LICENSE.txt` and are listed in `THIRD_PARTY_NOTICES.txt`.
