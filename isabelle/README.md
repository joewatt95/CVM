# Verification of the CVM algorithm

This directory formalises and verifies the
[CVM algorithm](https://arxiv.org/abs/2301.10191)
in the [Isabelle proof assistant](https://isabelle.in.tum.de/),
as presented in the paper
"Verification of the CVM algorithm with a Functional Probabilistic Invariant".

# Project structure

- [CVM_Invariant](CVM_Invariant)
  formalises a new, unbiased, variant of the CVM algorithm, along with an
  invariant based proof of its correctness, as described in the paper.

- [Neg_Assoc](Neg_Assoc)
  formalises a theory of negatively associated random variables, which is used
  by the formalisation in [CVM_Invariant](CVM_Invariant)

- [CVM_Transforms](CVM_Transforms)
  formalises the original CVM algorithm, along with the original
  transformation-based proof.

# Setup instructions

To build and run the various formalisations, one must first install Isabelle
(specifically the 2024 release version, Isabelle2024), along with the AFP,
a collection of libraries and formalisations in Isabelle.
The AFP contains other formalisations which we depend on in our work.

## Installing Isabelle2024

Instructions on installing Isabelle on various platforms can be found on the official
Isabelle website [here](https://isabelle.in.tum.de/installation.html).

## Installing the Archive of Formal Proofs (AFP)

To install the AFP, one can clone the AFP repository with
[mercurial](https://www.mercurial-scm.org/)
and then register it with the Isabelle system, so that it can find and import
the various formalisation in the AFP which our work depends on.

This can be done via the following commands:

```shell
# Clone the AFP repository
$ hg clone https://foss.heptapod.net/isa-afp/afp-2024

# Register the AFP repository with Isabelle
$ isabelle components -u afp-2024 
```

## Registering and building the formalisations with Isabelle

One can then register our formalisations with Isabelle as with the AFP, and then build them:

```shell
# Register formalisations with Isabelle
$ isabelle components -u . 

# Build the Isabelle formalisations
$ isabelle build -v -b -g CVM
```

This will also generate $\LaTeX$ sources and corresponding pdf documents for
each formalisation.
These will appear in the `document_out` subdirectory in the formalisations'
subdirectories.

## Interactively viewing and editing the formalisations

To interact with our formalisations, one can use the built-in jedit based
editor provided by Isabelle:

```shell
$ isabelle jedit -R $d
```

where `$d` is either `Neg_Assoc`, `CVM_Invariant` or `CVM_Transforms`.