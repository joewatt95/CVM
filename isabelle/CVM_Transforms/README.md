# Verification of the CVM algorithm using the Transformation-based Proof

This directory formalises and verifies the
[CVM algorithm](https://arxiv.org/abs/2301.10191)
in the [Isabelle proof assistant](https://isabelle.in.tum.de/),
using the transformation-based proof as presented Section 7 of the paper
"Verification of the CVM algorithm with a Functional Probabilistic Invariant" (ITP 2025).

# Setup instructions

To build and run the formalisation, one must first install Isabelle
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

## Building the formalisation with Isabelle

One can then build the formalisations with the following command:

```shell
# Build the Isabelle formalisation
$ isabelle build -v -D .
```
This command should be executed from the directory in which this README.md file resides.

A successful build should display output similar to the following.
The order and time taken to build the sessions may differ.

```shell
$ isabelle build -v -D .

Started at ...
...
Building CVM_Transforms ...
...
Finished CVM_Transforms (0:02:05 elapsed time, 0:06:52 cpu time, factor 3.27)
```

The build process will also generate $\LaTeX$ sources and corresponding pdf documents for
each formalisation.
These will appear in the `document_out` subdirectory.

## Main result
The main theorem is `prob_cvm_incorrect_le_delta` in the [CVM_Transforms/CVM_Correctness_Instance.thy](CVM_Transforms/CVM_Correctness_Instance.thy) file.

# Authors
* Seng Joe Watt <Watt_Seng_Joe@i2r.a-star.edu.sg>
* Derek Khu <derek_khu@i2r.a-star.edu.sg>
* Emin Karayel <me@eminkarayel.de>
* Kuldeep S. Meel <meel@cs.toronto.edu>
* Yong Kiam Tan <yongkiam.tan@ntu.edu.sg>

