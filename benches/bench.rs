#![allow(unused_variables)]
#![allow(non_snake_case)]
#![allow(unused_imports)]

// For benchmark, run:
// ``cargo bench --bench mux_proofs_benches --  [--vec_size <vec_size1>...][--lookup_size <lookup_size1>...][--table_size <table_size1>...]``

use csv::Writer;
use std::{io::stdout, mem::size_of_val, string::String, time::Instant};

use ark_ff::{Field, UniformRand};
use ark_std::rand::Rng;

use mux_proofs_impl::{
    coset_lookup::CosetLookup, naive::NaiveLookup, rng::SimpleHashFiatShamirRng, VectorLookup,
};

// Generates n random values such that they sum up to total
fn generate_random_frequencies<R: Rng>(n: usize, total: usize, rng: &mut R) -> Vec<u32> {
    
    // Generate `n-1` random points within the range [0, m)
    let mut points: Vec<u32> = (0..n-1).map(|_| rng.gen_range(0..total) as u32).collect();
    
    // Sort the points
    points.sort();
    
    // Initialize the vector of random values
    let mut values = Vec::with_capacity(n);
    
    // Calculate the intervals between sorted points
    let mut last_point = 0;
    for &point in &points {
        values.push(point - last_point);
        last_point = point;
    }
    
    // The last value is the interval between the last point and `m`
    values.push(total as u32 - last_point);
    
    values
}

fn benchmark<F: Field, VLkup: VectorLookup<F>>(
    scheme_name: String,
    vec_sizes: &Vec<usize>,
    lookup_sizes: &Vec<usize>,
    table_sizes: &Vec<usize>,
) {
    let mut csv_writer = Writer::from_writer(stdout());
    csv_writer
        .write_record(&[
            "scheme",
            "operation",
            "vec_size",
            "lookup_size",
            "table_size",
            "measure",
        ])
        .unwrap();
    csv_writer.flush().unwrap();

    let CAPPED_SIZE = 1 << 24;
    // Assume size vectors are passed in increasing order
    let max_size = std::cmp::min(
        vec_sizes.last().unwrap()
            * std::cmp::max(lookup_sizes.last().unwrap(), table_sizes.last().unwrap()),
        CAPPED_SIZE,
    ) * 2;
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

    for vec_size in vec_sizes.iter() {
        for lookup_size in lookup_sizes.iter() {
            for table_size in table_sizes.iter() {
                if *vec_size > CAPPED_SIZE / *lookup_size {
                    continue;
                }
                if *vec_size > CAPPED_SIZE / *table_size {
                    continue;
                }                
                // freqs is the frequency of each table subvector in the lookup vector
                let freqs = generate_random_frequencies(*table_size, *lookup_size, rng);

                let table_vals: Vec<F> = (0..*vec_size * table_size)
                    .cycle()
                    .map(|i| F::from(i as u64))
                    .take(vec_size * table_size)
                    .collect(); // TODO: make this unique
                let mut lookup_vals: Vec<F> = vec![];
                for i in 0..*table_size {
                    for j in 0..freqs[i] {
                        // generate the vector from i*vec_size to (i+1)*vec_size
                        for k in 0..*vec_size {
                            lookup_vals.push(F::from((i * *vec_size + k) as u64));
                        }
                    }
                }

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
                start = Instant::now();
                let (lookup_comm, lookup_repr) =
                    VLkup::commit_lookup(&pk, lookup_vals.clone()).unwrap();
                end = start.elapsed().as_millis();
                csv_writer
                    .write_record(&[
                        scheme_name.clone(),
                        "precommit".to_string(),
                        vec_size.to_string(),
                        lookup_size.to_string(),
                        table_size.to_string(),
                        end.to_string(),
                    ])
                    .unwrap();
                csv_writer.flush().unwrap();

                let (table_comm, table_repr) =
                    VLkup::commit_table(&pk, table_vals.clone()).unwrap();

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
                )
                .unwrap();

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
                VLkup::verify(&vk, &proof, &lookup_comm, &table_comm).unwrap();
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
    let (mut vec_sizes, mut lookup_sizes, mut table_sizes): (Vec<usize>, Vec<usize>, Vec<usize>) =
        if args.len() > 1 && (args[1] == "-h" || args[1] == "--help") {
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
                                Ok(vec_size) => vec_sizes.push(1 << vec_size),
                                Err(_) => break 'vec_size,
                            }
                            next_arg = args.next();
                        }
                    }
                    "--lookup_size" => {
                        next_arg = args.next();
                        'lookup_size: while let Some(lookup_arg) = next_arg.clone() {
                            match lookup_arg.parse::<usize>() {
                                Ok(lookup_size) => lookup_sizes.push(1 << lookup_size),
                                Err(_) => break 'lookup_size,
                            }
                            next_arg = args.next();
                        }
                    }
                    "--table_size" => {
                        next_arg = args.next();
                        'table_size: while let Some(table_arg) = next_arg.clone() {
                            match table_arg.parse::<usize>() {
                                Ok(table_size) => table_sizes.push(1 << table_size),
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

    use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Radix2EvaluationDomain};
    use blake2::Blake2s;

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
    use rand_chacha::ChaChaRng;

    use ark_poly_commit::marlin_pc::MarlinKZG10;
    type PC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>>;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type CosetLookupInst = CosetLookup<Fr, PC, FS>;
    benchmark::<Fr, CosetLookupInst>(
        "coset_lookup".to_string(),
        &vec_sizes,
        &lookup_sizes,
        &table_sizes,
    );
    type NaiveLookupInst = NaiveLookup<Fr, PC, FS, Bls12_381>;
    benchmark::<Fr, NaiveLookupInst>(
        "naive_lookup".to_string(),
        &vec_sizes,
        &lookup_sizes,
        &table_sizes,
    );
}
