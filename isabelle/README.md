# Verification of the CVM algorithm

This directory formalises and verifies the
[CVM algorithm](https://arxiv.org/abs/2301.10191)
in the [Isabelle proof assistant](https://isabelle.in.tum.de/),
as presented in the paper
"Verification of the CVM algorithm with a Functional Probabilistic Invariant" (ITP 2025).

# Project structure

- [CVM_Invariant](CVM_Invariant)
  formalises both the original and a new unbiased variant of the CVM algorithm, using the
  new proof technique (functional probabilistic invariants) described in the paper.

- [Neg_Assoc](Neg_Assoc)
  formalises a theory of negatively associated random variables, which is used
  by the formalisation in [CVM_Invariant](CVM_Invariant)

- [CVM_Transforms](CVM_Transforms)
  formalises the original CVM algorithm using the original
  transformation-based proof.

> [!NOTE]
> The frist two subprojects [CVM_Invariant](CVM_Invariant) and [Neg_Assoc](Neg_Assoc) have been
> added to the (Archive of Formal Proofs) [AFP](https://www.isa-afp.org/) and are being
> maintained in that repository.
> See [Verification of the CVM algorithm with a New Recursive Analysis Technique](https://www.isa-afp.org/entries/CVM_Distinct_Elements.html) and
> [Negatively Associated Random Variables](https://www.isa-afp.org/entries/Negative_Association.html)
> for the most recent version of these subprojects.

# Setup instructions

To build and run the various formalisations, one must first install Isabelle
(specifically the 2025 release version, Isabelle2025), along with the AFP,
a collection of libraries and formalisations in Isabelle.
The AFP contains other formalisations which we depend on in our work.

## Installing Isabelle2025

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
$ hg clone https://foss.heptapod.net/isa-afp/afp-2025

# Register the AFP repository with Isabelle
$ isabelle components -u afp-2025/thys
```

## Registering and building the formalisations with Isabelle

One can then register our formalisations with Isabelle as with the AFP, and then build them:

```shell
# Register formalisations with Isabelle
$ isabelle components -u . 

# Build the Isabelle formalisations
$ isabelle build -v -b -g CVM
```

(These commands should be executed from the directory in which this README.md file resides.)

A successful build should display output similar to the following.
The order and time taken to build the sessions may differ.

```shell
$ isabelle build -v -b -g CVM

Started at ...
...
Building CVM_Transforms ...
...
Finished CVM_Transforms (0:02:05 elapsed time, 0:06:52 cpu time, factor 3.27)
Building Neg_Assoc ...
...
Finished Neg_Assoc (0:05:23 elapsed time, 0:18:23 cpu time, factor 3.41)
Building CVM_Invariant ...
...
Finished CVM_Invariant (0:05:27 elapsed time, 0:18:58 cpu time, factor 3.48)

Finished at ...
0:13:34 elapsed time, 0:44:14 cpu time, factor 3.26
```

The build process will also generate $\LaTeX$ sources and corresponding pdf documents for
each formalisation.
These will appear in the `document_out` subdirectory in the formalisations'
subdirectories.

## Main results

The following is an overview of the main results presented in the paper.

- [CVM_Invariant/CVM_Original_Algorithm.thy](CVM_Invariant/CVM_Original_Algorithm.thy)
  
  Defines the original CVM algorithm and the `correctness` theorem shows that its output estimate is probably-approximately correct.
- [CVM_Invariant/CVM_New_Unbiased_Algorithm.thy](CVM_Invariant/CVM_New_Unbiased_Algorithm.thy)
  
  Defines the new CVM variant. The `unbiasedness` theorem shows its unbiasedness while the `correctness` theorem shows that its output estimate is probably-approximately correct.

- [Neg_Assoc](Neg_Assoc)
  
  Formalizes a theory of negatively associated random variables, including results such as [Chernoff bounds](Neg_Assoc/Neg_Assoc_Chernoff_Bounds.thy), negative association of [permutation distributions](Neg_Assoc/Neg_Assoc_Permutation_Distributions.thy), and an example application on [Bloom filters](Neg_Assoc/Neg_Assoc_Bloom_Filters.thy).

- [CVM_Transforms/CVM_Correctness_Instance.thy](CVM_Transforms/CVM_Correctness_Instance.thy)
  
  Formalises the original CVM algorithm via its original transformation-based proof. The main theorem is `prob_cvm_incorrect_le_delta`.

## Interactively viewing and editing the formalisations

To interact with our formalisations, one can use the built-in jedit based
editor provided by Isabelle:

```shell
$ isabelle jedit -R $d
```

where `$d` is either `Neg_Assoc`, `CVM_Invariant` or `CVM_Transforms`.
