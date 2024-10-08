# MuxProofs Succinct Vector Lookup

Rust implementation of the Succinct Vector Lookup protocol from MuxProofs, as well as a Naive Vector Lookup protocol for comparison.

**AsiaCrypt 2024** Zijing Di, Lucas Xia, Wilson Nguyen, Nirvan Tyagi. MUXProofs: Succinct Arguments for Machine Computation from Tuple Lookups. 

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

The `muxproofs` packages come with a suite of tests and benchmarks.

### Running Tests
To run the tests:
```bash
cargo test
```
### Running Benchmarks
To run a benchmark:
```bash
cargo bench --bench name_of_benchmark -- [--optional-arg arg1 arg2...]
```
## Reproducing Benchmarks

To generate the values used for the plots in the paper, you can run:
```
cargo bench --bench mux_proofs_benches -- --vec_size 2 4 6 8 10 12 --lookup_size 10 --table_size 6 | tee experiment_1.csv
cargo bench --bench mux_proofs_benches -- --vec_size 10 --lookup_size 2 4 6 8 10 12 --table_size 6 | tee experiment_2.csv
cargo bench --bench mux_proofs_benches -- --vec_size 10 --lookup_size 10 --table_size 2 4 6 8 10 12 | tee experiment_3.csv
```
