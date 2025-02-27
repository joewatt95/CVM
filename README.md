# Verification of the CVM algorithm

This repository formalises and verifies the
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

- [paper](paper) contains LaTeX sources for our paper.
- [tools](tools) contains miscellaneous tool.s

# Setup instructions

## Installing Isabelle2024 and the Archive of Formal Proofs (AFP)

To build and run the various formalisations, one must first install Isabelle
(specifically the 2024 release version, Isabelle2024), along with the AFP,
a collection of libraries and formalisations in Isabelle.
The AFP contains other formalisations which we depend on in our work.

Instructions on installing Isabelle can be found on the official
Isabelle website [here](https://isabelle.in.tum.de/installation.html).

To install the AFP, one can clone the AFP repository and then register it with
the Isabelle system, so that it can find and import the various formalisation 
in the AFP which we depend on.

This can be done via the following commands:

```shell
# Clone the AFP repository
$ git clone https://github.com/isabelle-prover/mirror-afp-2024
# Register the AFP repository with Isabelle
$ isabelle components -u mirror-afp-2024 
```

## Registering and building the formalisations with Isabelle

One can then register our formalisations with Isabelle using the
`isabelle components` command as with the AFP, and then build them via
`isabelle build`:

```shell
$ for dir in Neg_Assoc CVM_Invariant CVM_Transforms; do \
    isabelle components -u isabelle/$dir && isabelle build -b -v $dir \
  done
```

## Interactively viewing and editing the formalisations