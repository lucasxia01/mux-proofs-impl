# MuxProofs Coset Lookup

Rust implementation of the Coset Lookup protocol from MuxProofs.

**AsiaCrypt 2024** Zijing Di, Lucas Xia, Wilson Nguyen, Nirvan Tyagi. MUXProofs: Succinct Arguments for Machine Computation from Tuple Lookups. 

## Tests and Benchmarks

The `muxproofs` packages come with a suite of tests and benchmarks.

### Running Tests
To run the tests:
```
cargo test
```
### Running Benchmarks
To run a benchmark:
```
cargo bench --bench name_of_benchmark -- [--optional-arg arg1 arg2...]
```
## Reproducing Benchmarks

To generate the values used for the plots in the paper, you can run:
```
cargo bench --bench mux_proofs_benches -- --vec_size 2 4 6 8 10 12 --lookup_size 10 --table_size 6 | tee experiment_1.csv
cargo bench --bench mux_proofs_benches -- --vec_size 10 --lookup_size 2 4 6 8 10 12 --table_size 6 | tee experiment_2.csv
cargo bench --bench mux_proofs_benches -- --vec_size 10 --lookup_size 10 --table_size 2 4 6 8 10 12 | tee experiment_3.csv
```