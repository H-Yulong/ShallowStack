# Fully Dependent Abstract Machines: Agda Implementation

This repository contains an Agda implementation of the dependent SECD machine and the Dependent Abstract Machine (DAM), with a formalization of their type safety and dependent SECD machine's termination.

## Getting started (Kick the tires)

To start, install Agda version 2.8.0 ([instructions](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html)).

Download and unzip the artifact,
then run the following command from the artifact directory:

```cmd
agda Main.agda
```

If you are using Emacs or Agda mode of VS Code, open `Main.agda` and load the file with `C-c C-l` (pressing Ctrl-C immediately followed by Ctrl-L).

## Evaluation instructions

The root file `Main.agda` imports all other files contained in this repository. All claims are validated if type-checking this file is successful without any error. It should only take a few minutes.

The following table lists all the claims in the paper supported by the artifact. Nevigate to the directory containing the associated file to check if the claim is loyal to the paper.

| Section | Item                | File                           | Name                                 |
| ------- | ------------------- | ----------------------         | -------------------------------      |
| §2.1    | Lemma 2.2           | `Model.Universe`               | `inj₁`, `inj₂`, `Σ-inj₁`, `Σ-inj₂`   |
| §2.4    | Definition 2.6      | `SECD.Config`                  | `Config`                             |
| §2.5    | Definition 2.9      | `SECD.Opsem`                   | `_⇓_`, `⇓!`                          |
| §2.5    | Theorem 2.10        | `SECD.Progress`                | `Progress`                           |
| §2.6    | Definition 2.14     | `SECD.Theorem.Halting`         | `↓`                                  |
| §2.6    | Definition 2.15     | `SECD.Theorem.Halting`         | `H`                                  |
| §2.6    | Definition 2.17     | `SECD.Theorem.Halting`         | `Hᵉ`                                 |
| §2.6    | Definition 2.18     | `SECD.Theorem.Halting`         | `Hˢ`                                 |
| §2.6    | Lemma 2.19          | `SECD.Theorem.Fundamental`     | `Fund`                               |
| §2.6    | Lemma 2.20          | `SECD.Theorem.Termination`     | `all-H`                              |
| §2.6    | Lemma 2.21          | `SECD.Theorem.Termination`     | `halts-frame`                        |
| §2.6    | Theorem 2.22        | `SECD.Theorem.Termination`     | `Termination`                        |
| §2.6    | Corollary 2.23      | `SECD.Theorem.Termination`     | `TotalCorrectness`                   |
| §2.6    | Corollary 2.24      | `SECD.Theorem.Termination`     | `TotalCorrectness-program`           |
| §3.4    | Definition 3.2      | `DAM.Config`                   | `Config`                             |
| §3.4    | Theorem 3.4         | `DAM.Theorem.Progress`         | `Progress`                           |

Additionally, you can view the example DAM code contained in `DAM.Main` and see the trace of machine execution. Load the file with Emacs or VS code Agda mode , then press `C-c C-n`, the system will ask for a term and evaluates its normal form. Enter `Add23.run` or `Add23.run-trace` to see the result or the result with trace.

## Additional artifact information

### File structure

The repository is structured as follows:

```cmd
.
├── Lib
├── Model
│   ├── Context.agda
│   ├── Shallow.agda
│   ├── Stack.agda
│   └── Universe.agda
├── SECD
│   ├── Theorem
│   │     ├── Fundamental.agda
│   │     ├── Halting.agda
│   │     ├── Progress.agda
│   │     └── Termination.agda
│   ├── Config.agda
│   ├── Main.agda
│   ├── Opsem.agda
│   ├── Syntax.agda
│   └── Value.agda
├── DAM
│   ├── Theorem
│   │     ├── Fundamental.agda
│   │     ├── Halting.agda
│   │     ├── Progress.agda
│   │     └── Termination.agda
│   ├── Examples
│   ├── Config.agda
│   ├── Labels.agda 
│   ├── Main.agda
│   ├── Opsem.agda
│   ├── Syntax.agda
│   └── Value.agda
└── Main.agda
```

- [`Main`] imports all other files.
- [`Lib`] defines a custom library of utility functions and types.
- [`Model`] implements the source theory CCw as a shallow embedding.
  - [`Model.Universe`] defines an inductive-recursive universe hierarchy.
  - [`Model.Shallow`] gives the shallow embedding.
  - [`Model.Context`] defines a deep embedded syntax for contexts, indexed by the shallow embedding.
  - [`Model.Stack`] defines *abstrack stack*, lists of well-typed terms.
- [`SECD`] contains the implementation of the dependent SECD machine with proofs of its type safety and termination.
  - [`SECD.Syntax`] gives the intrinsic syntax of the machine instructions.
  - [`SECD.Values`] defines well-typed values, runtime environment, and stack of the machine.
  - [`SECD.Config`] defines well-formed machine configurations.
  - [`SECD.Opsem`] gives well-formed machine transitions; type preservation holds automatically under this definition.
  - [`SECD.Theorem`] contains proofs of progress (`SECD.Theorem.Progress`) and termination (`SECD.Theorem.Termination`), which includes a definition of the halting relation (`SECD.Theorem.Halting`) and a fundamental lemma (`SECD.Theorem.Fundamental`).
  - [`SECD.Main`] imports all files in this folder and defines an interpreter for the machine using the termination proof.
- [`DAM`] contains an encoding of abstract defunctionalization and the Dependent Abstract Machine (DAM), with proofs of its type safety and that the encoding is terminating. The structure is similar to that of `SECD`.
  - [`DAM.Labels`] encodes the DCC's label context with the shallow embedded source language.
  - [`DAM.Syntax`] gives the intrinsic syntax of the machine instructions.
  - [`DAM.Values`] defines well-typed values, runtime environment, and stack of the machine.
  - [`DAM.Config`] defines well-formed machine configurations.
  - [`DAM.Opsem`] gives well-formed machine transitions; type preservation again holds automatically under this definition.
  - [`DAM.Theorem`] contains proofs of progress (`DAM.Theorem.Progress`). It also contain a proof of termination of the encoding (`DAM.Theorem.Termination`), which includes a definition of the halting relation (`DAM.Theorem.Halting`) and a fundamental lemma (`DAM.Theorem.Fundamental`).
  - [`DAM.Examples`] contain example codes of DAM.
  - [`DAM.Main`] imports all files in this folder and defines an interpreter for the machine using the termination proof.

### The halting relation on values

The submitted version of the paper contains an imprecise (and therefore seemingly ill-founded) definition of the halting relation (Definition 2.15). Precisely, the logical relation $H(A)$ should be given as a recursive definition over the normal form of $A$. Our formalization is based on the precise definition (`L104` in `SECD.Theorem.Halting`), where the halting relation `H` is defined by pattern matching on the type `A`. We have fixed this problem in the revised version of the paper.

### Encodings of DCC and DAM

The Defunctionalized Calculus of Constructions (Section 3.2) is defined as an encoding, in order to avoid the many restrictions Agda pocesses on defunctionalization. We encode DCC's label context as the type signature `DCC.Labels.LCon`, which contains a set of labels `Pi` and meanings of each label `interp` that corresponds to the label's pointed function body. We encode label application `lapp` with shallow embedding, which has the substitution rule `lapp[]` and beta-reduction rule `lapp-β` as expected. Each label also contains an index such that labels of smaller indices cannot refer to labels of larger indices, which encodes the structural requirement of DCC that previous labels cannot refer to later labels. `DAM.Examples` contain concrete examples of defunctionalized label contexts, where `Pi` is defined as a datatype and `interp` maps each label to its shallow-embedded function body, much like traditional defunctionalization.

Since the specification language DCC is an encoding, the abstract machine DAM is also an encoding of the machine described in the paper, but they have the exact same operational semantics and typing rules. We are able to prove termination of the encoded DAM directly instead of by contradiction as in the paper, and therefore obtain a working interpreter from the termination proof.

### Acknowledgments

This formalization is inspired by prior works, including:

- Kaposi A, Kovács A, Kraus N. Shallow embedding of type theory is morally correct. International Conference on Mathematics of Program Construction. Cham: Springer International Publishing, 2019: 329-365.
- L. Diehl, T. Sheard. Leveling up dependent types: generic programming over a predicative hierarchy of universes.
In Proceedings of the 2013 ACM SIGPLAN Workshop on Dependently-typed Programming, 2013. ACM.

The authors have used Fable 5 to assist in mechanizing the proofs of the fundamental lemma and termination.
