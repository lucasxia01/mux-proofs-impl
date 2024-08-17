
To generate the values used for the plots in the paper, you can run:
```
cargo bench --bench mux_proofs_benches -- --vec_size 2 4 6 8 10 12 --lookup_size 10 --table_size 6 | tee experiment_1.csv
cargo bench --bench mux_proofs_benches -- --vec_size 10 --lookup_size 2 4 6 8 10 12 --table_size 6 | tee experiment_2.csv
cargo bench --bench mux_proofs_benches -- --vec_size 10 --lookup_size 10 --table_size 2 4 6 8 10 12 | tee experiment_3.csv
```