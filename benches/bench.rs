// For benchmark, run: 
// ``cargo bench --bench mux_proofs_benches --  [--vec_size <vec_size1>...][--lookup_size <lookup_size1>...][--table_size <table_size1>...]``

use std::{io::stdout, string::String, time::Instant, mem::size_of_val};
use csv::Writer;

use ark_ff::{Field, UniformRand};

use mux_proofs_impl::{
    VectorLookup,
};

fn benchmark<F: Field, VLkup: VectorLookup<F>>(
    scheme_name: String,
    vec_sizes: &Vec<usize>,
    lookup_sizes: &Vec<usize>,
    table_sizes: &Vec<usize>,
) {
    let mut csv_writer = Writer::from_writer(stdout());
    csv_writer
        .write_record(&["scheme", "operation", "vec_size", "lookup_size", "table_size", "measure"])
        .unwrap();
    csv_writer.flush().unwrap();

    // Assume size vectors are passed in increasing order
    let max_size = vec_sizes.last().unwrap() * lookup_sizes.last().unwrap() * table_sizes.last().unwrap(); 
    let rng = &mut ark_std::test_rng();
    let mut start = Instant::now();
    let srs = VLkup::universal_setup(max_size, rng).unwrap();
    let mut end = start.elapsed().as_millis();
    csv_writer
        .write_record(&[
            scheme_name.clone(),
            "setup".to_string(),
            vec_sizes.last().unwrap().to_string(),
            lookup_sizes.last().unwrap().to_string(),
            table_sizes.last().unwrap().to_string(),
            end.to_string(),
        ])
        .unwrap();
    csv_writer.flush().unwrap();
    
    let dummy_value = F::rand(rng);
    for vec_size in vec_sizes.iter() {
        for lookup_size in lookup_sizes.iter() {
            for table_size in table_sizes.iter() {
                // Generate dummy lookup and table max sizes
                let lookup_vals = vec![dummy_value; vec_size * lookup_size];
                let table_vals = vec![dummy_value; vec_size * table_size];

                // Generate prover and verifier keys
                start = Instant::now();
                let (pk, vk) = VLkup::index(&srs, *vec_size, *lookup_size, *table_size).unwrap();
                end = start.elapsed().as_millis();
                csv_writer
                    .write_record(&[
                        scheme_name.clone(),
                        "index".to_string(),
                        vec_size.to_string(),
                        lookup_size.to_string(),
                        table_size.to_string(),
                        end.to_string(),
                    ])
                    .unwrap();
                csv_writer.flush().unwrap();

                // Commit 
                // TODO: Inefficient since lookup comm and table comm can be reused over the for loop
                let (lookup_comm, lookup_repr) = VLkup::commit_lookup(&pk, lookup_vals.clone()).unwrap();
                let (table_comm, table_repr) = VLkup::commit_table(&pk, table_vals.clone()).unwrap();

                // Prove
                start = Instant::now();
                let proof = VLkup::prove(
                    &pk, 
                    &lookup_comm,
                    &table_comm,
                    lookup_vals.clone(),
                    table_vals.clone(),
                    lookup_repr.clone(),
                    table_repr.clone(),
                ).unwrap();
                end = start.elapsed().as_millis();
                csv_writer
                    .write_record(&[
                        scheme_name.clone(),
                        "prove".to_string(),
                        vec_size.to_string(),
                        lookup_size.to_string(),
                        table_size.to_string(),
                        end.to_string(),
                    ])
                    .unwrap();
                csv_writer.flush().unwrap();

                // Verify
                start = Instant::now();
                VLkup::verify(
                    &vk, 
                    &proof,
                    &lookup_comm,
                    &table_comm,
                ).unwrap();
                end = start.elapsed().as_millis();
                csv_writer
                    .write_record(&[
                        scheme_name.clone(),
                        "verify".to_string(),
                        vec_size.to_string(),
                        lookup_size.to_string(),
                        table_size.to_string(),
                        end.to_string(),
                    ])
                    .unwrap();
                csv_writer.flush().unwrap();

                // Proof size
                csv_writer
                    .write_record(&[
                        scheme_name.clone(),
                        "proof_size".to_string(),
                        vec_size.to_string(),
                        lookup_size.to_string(),
                        table_size.to_string(),
                        size_of_val(&proof).to_string(),
                    ])
                    .unwrap();
                csv_writer.flush().unwrap();
            }
        }
    }

}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    if args.last().unwrap() == "--bench" {
        args.pop();
    }
    let (mut vec_sizes, mut lookup_sizes, mut table_sizes): (Vec<usize>, Vec<usize>, Vec<usize>) = if args.len() > 1
        && (args[1] == "-h" || args[1] == "--help")
    {
        println!("Usage: ``cargo bench --bench mux_proofs_benches --  [--vec_size <vec_size1>...][--lookup_size <lookup_size1>...][--table_size <table_size1>...]``");
        return;
    } else {
        let mut args = args.into_iter().skip(1);
        let mut next_arg = args.next();
        let mut vec_sizes = vec![];
        let mut lookup_sizes = vec![];
        let mut table_sizes = vec![];
        while let Some(arg) = next_arg.clone() {
            match arg.as_str() {
                "--vec_size" => {
                    next_arg = args.next();
                    'vec_size: while let Some(vec_arg) = next_arg.clone() {
                        match vec_arg.parse::<usize>() {
                            Ok(vec_size) => vec_sizes.push(vec_size),
                            Err(_) => break 'vec_size,
                        }
                        next_arg = args.next();
                    }
                }
                "--lookup_size" => {
                    next_arg = args.next();
                    'lookup_size: while let Some(lookup_arg) = next_arg.clone() {
                        match lookup_arg.parse::<usize>() {
                            Ok(lookup_size) => lookup_sizes.push(lookup_size),
                            Err(_) => break 'lookup_size,
                        }
                        next_arg = args.next();
                    }
                }
                "--table_size" => {
                    next_arg = args.next();
                    'table_size: while let Some(table_arg) = next_arg.clone() {
                        match table_arg.parse::<usize>() {
                            Ok(table_size) => table_sizes.push(table_size),
                            Err(_) => break 'table_size,
                        }
                        next_arg = args.next();
                    }
                }
                _ => {
                    println!("Invalid argument: {}", arg);
                    return;
                }
            }
        }
        (vec_sizes, lookup_sizes, table_sizes)
    };
    if vec_sizes.len() == 0 {
        vec_sizes.push(64);
    }
    if lookup_sizes.len() == 0 {
        lookup_sizes.push(1024);
    }
    if table_sizes.len() == 0 {
        table_sizes.push(256);
    }

    //benchmark::<CosetLookup<MarlinKZG, etc>>(
    //    "coset_lookup".to_string(),
    //    &vec_sizes,
    //    &lookup_sizes,
    //    &table_sizes,
    //);
}