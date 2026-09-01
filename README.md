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
- CFG/CNF structures, lossless tree binarization, dense treebank induction, bounded acyclic unary
  elimination with exact rule provenance, and checked grammar compilation;
- semiring-generic CKY, compiled sparse/dense CKY, one-best extraction, and source-preserving
  Viterbi derivations with adaptive pair indexing and exact unary-tree restoration;
- linear-chain dynamic programming, a smoothed bigram HMM, and a validated named POS tagger with
  exact vocabulary lookup, reserved OOV handling, and sentence-boundary resets;
- source-preserving UTF-8 tokenization with source-byte spans, a persistent streaming cursor, exact
  whitespace mode, configurable English/UD-style rules, and deterministic sentence splitting;
- POS-aware English lemmatization with exception-first lexical validation, ambiguous candidate
  analyses, reversible suffix-rule witnesses, and automatically derived generator candidates;
- CoNLL-U and Penn Treebank readers, bracket/chunk/tagging metrics, and EVALB-compatible scoring;
- cancellation-aware, order-preserving bounded parallel corpus traversal with byte-weighted work
  planning for skewed corpora.

The broader CoreNLP surface—full PTB tokenizer compatibility, morphological feature analysis,
collocations, pretrained lexical data, NER, dependency parsing, model formats, and production
CLI/package ergonomics—is still incomplete.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run:

```text
lake build NlpCore
lake build NlpTests
lake build parallel-benchmark
lake build tokenize-benchmark
lake build morphology-benchmark
lake build pos-benchmark
lake build unary-benchmark
lake build compiled-viterbi-benchmark
```

`lake build` builds the public `NlpCore` library. `NlpTests` compiles the full theorem and
regression suite. Benchmarks are intentionally separate from the library.

## A checked functional example

This named HMM example is mirrored by `NlpTests.Readme`, so CI compiles the API and checks its
result.

```lean
import Nlp

open Nlp Nlp.Sequence

def training : Array (Array (String × String)) :=
  #[#[("dogs", "NOUN"), ("run", "VERB")],
    #[("cats", "NOUN"), ("sleep", "VERB")],
    #[("dogs", "NOUN"), ("sleep", "VERB")]]

#eval
  (PosTagger.estimate training).map fun tagger ↦
    tagger.tagForms #["dogs", "sleep"]
-- Except.ok #["NOUN", "VERB"]
```

Tokenization is also available as a pure value-level API:

```lean
import Nlp

open Nlp Nlp.Tokenize

#eval
  let doc := Tokenizer.default.process "Hi. Bye!"
  (doc.forms, doc.sentEnd)
-- (#["Hi", ".", "Bye", "!"], #[2, 4])
```

Pure kernels remain available under `Nlp.IO`, `Nlp.Parse`, `Nlp.Sequence`, and `Nlp.Eval`. For
applications, `Nlp.NLP` is the preferred boundary: it provides typed failures, configuration,
cancellation, model validation, effectful annotation, parsing, file operations, and bounded
parallel traversal. `Nlp.Ann.lift` and `Nlp.NLP.annotatePure` expose the same pure annotators
without moving effects into their hot path. `Nlp.NLP.tokenizeText`, `processText`, `tokenizeTexts`,
and `processTexts` provide checked effectful tokenization; corpus operations preserve order and
schedule by UTF-8 byte weight. `Config.parallelMinGrain` is measured in items, while
`Config.parallelMinWeight` is measured in caller-defined cost units; the tokenizer's
`*WithMinBytes` APIs set the latter explicitly. Policy-aware parsing also caps dense allocation
through `Config.maxChartEntries`, independently of sentence length. English morphology is
available functionally via
`Morphology.Model.analyses`, `generate`, `lemmaOrSelf`, and `annotator`; `NLP.lemmatize` and
`lemmatizeMany` add checked cancellation-aware application and token-weighted corpus traversal.
Named POS tagging is available through `PosTagger.compile`, `estimate`, `tagForms`, and `annotator`;
`NLP.compilePosTagger`, `estimatePosTagger`, `tag`, and `tagMany` add checked effectful model and
corpus boundaries. Advertised sentence spans decode independently, while token-only documents are
one HMM sequence. `English.analyzeText` is the pure tokenize/split/POS/lemma path, and
`NLP.analyzeEnglishText` plus its ordered byte-weighted corpus variants provide the fused effectful
path with one semantic validation scan per input. Models remain caller-supplied: the repository
bundles neither a pretrained tagger nor a morphology dictionary, and lookup is exact and
case-sensitive.

Unary-aware one-best parsing is functional through `UnaryViterbiModel.compile` and `parse?`.
`NLP.compileUnaryViterbiModel`, `parseUnaryTree`, and `parseUnaryTrees` add typed model failures,
cancellation, sentence-length policy, and ordered bounded batches. The adaptive Viterbi compiler
uses a compact sparse pair index for large nonterminal spaces while preserving exact emitted rule
ordinals for restoration.

The morphology model exposes ambiguity rather than hiding it, while `lemmaOrSelf` provides the
conservative single-column policy used by the document annotator:

```lean
import Nlp

open Nlp

#eval
  (Morphology.Model.compile #[⟨.noun, "dog"⟩] #[]).map fun model =>
    model.lemmaOrSelf .noun "dogs"
-- Except.ok "dog"
```

## Algorithm sources and implementation contributions

The established algorithms are credited to their primary specifications:

- semiring parsing and generalized inside computation: Joshua Goodman,
  [“Semiring Parsing”](https://aclanthology.org/J99-4004/), 1999;
- parsing as deduction: Stuart Shieber, Yves Schabes, and Fernando Pereira,
  [“Principles and Implementation of Deductive Parsing”](https://doi.org/10.1016/0743-1066(95)00035-I),
  1995;
- hidden Markov estimation and decoding: Lawrence Rabiner,
  [“A Tutorial on Hidden Markov Models”](https://doi.org/10.1109/5.18626), 1989;
- English inflectional detachment and exception-first lexical validation: Princeton WordNet's
  [Morphy reference](https://wordnet.princeton.edu/documentation/morphy7wn);
- CoNLL-U syntax: the [Universal Dependencies format specification](https://universaldependencies.org/format.html);
- constituency scoring: Sekine and Collins' [EVALB](https://nlp.cs.nyu.edu/evalb/), including
  the Brooks and Ellis updates;
- tokenizer behavior and compatibility vocabulary: Stanford's
  [tokenization](https://stanfordnlp.github.io/CoreNLP/tokenize.html) and
  [sentence splitting](https://stanfordnlp.github.io/CoreNLP/ssplit.html) documentation;
- Unicode decimal-number and whitespace classifications: the Unicode 17
  [Derived General Category](https://www.unicode.org/Public/UCD/latest/ucd/extracted/DerivedGeneralCategory.txt)
  and [property](https://www.unicode.org/Public/UCD/latest/ucd/PropList.txt) data files.

Repository-specific implementation work is kept explicit in code and history:

- adaptive compiled CNF storage chooses a flat dense pair-offset table or a sparse hash index;
- lexical buckets and nonzero-cell lists avoid scanning irrelevant productions and chart rows;
- width-major triangular charts use flat storage with checked layout theorems;
- Viterbi backpointers preserve source production ordinals and deterministic tie-breaking;
- acyclic unary elimination shares path prefixes in a reverse-linked arena, retains distinct
  positional derivations, enforces explicit expansion budgets, and restores exact unary chains
  from emitted rule ordinals;
- named POS model compilation validates dense HMM storage, numeric costs, vocabularies, packed
  emission identifiers, and a collision-free OOV observation before the decoding hot path;
- sentence-aware POS annotation resets HMM state at declared boundaries and falls back to a
  length-preserving whole-document decode only for malformed unchecked segmentation;
- imperative array kernels are related to functional folds by refinement theorems;
- tokenizer spans use proof-carrying `String.Pos` endpoints, preserve exact source spelling, and
  avoid converting the whole input to a character list;
- morphology keeps productive rules as invertible suffix relations with provenance, while the
  lexicon-filtered analyzer remains explicitly many-valued and makes no bijectivity claim;
- typed score newtypes prevent accidental cross-domain arithmetic while retaining specialized hot
  paths;
- the effectful scheduler supports count- and weight-balanced chunks, caps dedicated threads,
  suppresses nested fan-out, observes cooperative cancellation, and preserves input/error order.

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
The tokenizer follows documented behavior where implemented, but does not claim exact PTBTokenizer
or CoreNLP compatibility. No CoreNLP source code, model files, or generated model artifacts are
included. No WordNet database or exception-list data is included.

## Licensing

A project-wide license has not yet been selected; until a root `LICENSE` is added, normal
copyright restrictions apply. The public-domain EVALB regression fixtures retain their own
license in `NlpTests/Fixtures/Evalb/LICENSE.txt` and are listed in `THIRD_PARTY_NOTICES.txt`.
