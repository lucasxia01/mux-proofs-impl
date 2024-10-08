# MuxProofs Succinct Vector Lookup

Rust implementation of the Succinct Vector Lookup protocol from MuxProofs, as well as a Naive Vector Lookup protocol for comparison.

The Succinct Vector Lookup protocol, _CosetLkup_ in the paper, is a protocol which proves that a multiset of lookup vectors is a subset of a set of table vectors. The proof size and verification time is succinct with respect to vector size, lookup size, and table size.

The Naive Vector Lookup protocol, which is not described by the paper, is not succinct with respect to vector size. The prover views the vector lookup as vector_size single-scalar lookups, which means the verifier will be linear on the order of vector_size.

**AsiaCrypt 2024** Zijing Di, Lucas Xia, Wilson Nguyen, Nirvan Tyagi. _MUXProofs: Succinct Arguments for Machine Computation from Tuple Lookups_. IACR AsiaCrypt 2024.

**ePrint (full version):**
Zijing Di, Lucas Xia, Wilson Nguyen, Nirvan Tyagi. _MUXProofs: Succinct Arguments for Machine Computation from Tuple Lookups_. Cryptology ePrint Archive, Report 2023/974. https://eprint.iacr.org/2023/974. 2023.

## Overview

This repository is organized as follows:
* [`src/succinct_lookup.rs`](src/succinct_lookup.rs): Implementation of Succinct Vector Lookup protocol.
* [`src/naive.rs`](src/naive.rs): Implementation of Naive Vector Lookup protocol, which takes a linear combination approach, essentially combining vector_size single-scalar lookups.
* [`src/lib.rs`](src/lib.rs): Trait for VectorLookup.
* [`src/test.rs`](`src/test.rs`): Tests for Succinct Lookup.
* [`benches/bench.rs`](benches/bench.rs): Benchmark suite for both Succinct and Naive protocols.
* [`descs/naive_lc.txt`](descs/naive_lc.txt): Round by round description of the Naive protocol.

## Installation/Build

The packages and benchmarks are easy to compile from source. The following sequence of commands may be helpful especially if on a fresh machine.

Install basic prerequisites and dependencies:
```
apt update && apt install -y curl
apt install git m4 z3 cmake libboost-all-dev build-essential
```
Install rust using any method ([Rust offical installation site](https://www.rust-lang.org/tools/install)):
```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source "$HOME/.cargo/env"
```

Clone the repository:
```bash
git clone https://github.com/lucasxia01/mux-proofs-impl.git
cd mux-proofs-impl/
```

Build using `cargo`:
```bash
cargo build
```

## Tests and Benchmarks

The `mux-proofs-impl` package come with a suite of tests and benchmarks.

### Running Tests
To run the tests:
```bash
cargo test
```
### Running Benchmark
To run a benchmark:
```bash
cargo bench --bench mux_proofs_benches -- [--vec_size <vec_size1>...][--lookup_size <lookup_size1>...][--table_size <table_size1>...]
```

The default vec_size is 64, the default lookup_size is 1024, and the default table_size is 256.

## Reproducing Benchmarks

To generate the values used for the plots in the paper, you can run:
```
cargo bench --bench mux_proofs_benches -- --vec_size 2 4 6 8 10 12 --lookup_size 10 --table_size 6 | tee experiment_1.csv
cargo bench --bench mux_proofs_benches -- --vec_size 10 --lookup_size 2 4 6 8 10 12 --table_size 6 | tee experiment_2.csv
cargo bench --bench mux_proofs_benches -- --vec_size 10 --lookup_size 10 --table_size 2 4 6 8 10 12 | tee experiment_3.csv
```
