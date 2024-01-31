use bulletproofs::LinearProof;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar;
use core::iter;
use std::ops::Add;
use std::vec;
use criterion::{criterion_group, criterion_main, Criterion};
use curve25519_dalek::traits::VartimeMultiscalarMul;
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use merlin::Transcript;
use std::mem::{size_of, size_of_val};
use blake3;

criterion_main!(bench);
criterion_group!(bench, benches);

// let hash1 = blake3::hash("daffadghgr".as_bytes());

fn u8_to_scalar(x: u8) -> Scalar {
    let mut bits = [0; 32];
    bits[0] = x;
    Scalar::from_bits(bits)
}

// generate the inner product of vectors a and b
fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {

    let mut out = Scalar::zero();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

fn nearest_power_of_two(num: usize) -> (usize, usize) {

    let mut power_of_two = 1;
    let mut power = 0;

    while power_of_two < num {
        power_of_two <<= 1;
        power += 1;
    }

    let lower_power_of_two = power_of_two >> 1;
    if num - lower_power_of_two < power_of_two - num {
        (lower_power_of_two, power - 1)
    }
    else{
        (power_of_two, power)
    }
}


fn prove(criterion: &mut Criterion, log_n: usize) {

    let (instance_num, power) = nearest_power_of_two(log_n);
    let vector_len = 2 * (1 << log_n) / instance_num;
    let double_vector_len = 2 * vector_len;
    let polynomial_size = instance_num * (vector_len - 1);

    let mut rng = rand::thread_rng();

    // generate the parameters of first half
    let bp_gens_first = BulletproofGens::new(vector_len, 1);
    let G_first: Vec<RistrettoPoint> = bp_gens_first.share(0).G(vector_len).cloned().collect();
    let pedersen_gens_first = PedersenGens::default();
    let F_first = pedersen_gens_first.B;
    let B_first = pedersen_gens_first.B_blinding;

    // generate commitments with instance_number
    let mut a_first_vec: Vec<Vec<_>> = Vec::with_capacity(instance_num);
    let mut b_first_vec: Vec<Vec<_>> = Vec::with_capacity(instance_num);
    for i in 0..instance_num{
        let a_first: Vec<_> = (0..vector_len).map(|_| Scalar::random(&mut rng)).collect();
        a_first_vec.push(a_first);
    }


    for j in 0..instance_num{
        let point_first = (0..(log_n - power + 1))
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
        let mut b_first = vec![u8_to_scalar(1)];
        for i in point_first {
            let len = b_first.len();
            for j in 0..len {
                b_first.push(b_first[j] * i);
            }
        }
        b_first_vec.push(b_first);
    }

    let r_first = Scalar::random(&mut rng);
    let mut c_first_vec: Vec<_> = Vec::with_capacity(instance_num);
    let mut C_first_vec: Vec<_> = Vec::with_capacity(instance_num);


    for i in 0..instance_num {
        c_first_vec.push(inner_product(&a_first_vec[i], &b_first_vec[i]));
        C_first_vec.push(RistrettoPoint::vartime_multiscalar_mul(
            a_first_vec[i].iter().chain(iter::once(&r_first)).chain(iter::once(&c_first_vec[i])),
            G_first.iter().chain(iter::once(&B_first)).chain(iter::once(&F_first)),
        ));
    }

    let mut C_first = C_first_vec[0];

    // for i in 1..instance_num{
    //     C_first = RistrettoPoint::add(C_first_vec[i-1], C_first_vec[i]);
    // }

    // C_first.compress();

    // generate the second (double_vector_len)
    let bp_gens = BulletproofGens::new(double_vector_len, 1);
    let G: Vec<RistrettoPoint> = bp_gens.share(0).G(double_vector_len).cloned().collect();
    let pedersen_gens = PedersenGens::default();
    let F = pedersen_gens.B;
    let B = pedersen_gens.B_blinding;

    let a: Vec<_> = (0..double_vector_len).map(|_| Scalar::random(&mut rng)).collect();

    let point = (0..(log_n - power + 2))
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let mut b = vec![u8_to_scalar(1)];
    for i in point {
        let len = b.len();
        for j in 0..len {
            b.push(b[j] * i);
        }
    }

    let mut transcript = Transcript::new(b"LinearProofBenchmark");

    // C = <a, G> + r * B + <a, b> * F
    let r = Scalar::random(&mut rng);
    let c = inner_product(&a, &b);
    let C = RistrettoPoint::vartime_multiscalar_mul(
        a.iter().chain(iter::once(&r)).chain(iter::once(&c)),
        G.iter().chain(iter::once(&B)).chain(iter::once(&F)),
    )
    .compress();

    // let C = RistrettoPoint::vartime_multiscalar_mul(
    //     a.iter().chain(iter::once(&r)).chain(iter::once(&c)),
    //     G.iter().chain(iter::once(&B)).chain(iter::once(&F)),
    // );

    // let C_test = RistrettoPoint::add(C, C);
    // let C_test_compressed = C_test.compress();

    let mut group = criterion.benchmark_group("prove");
    group.sample_size(10);
    group.bench_function(format!("namedl-pad open point {}", log_n), move |bencher| {
        bencher.iter(|| {
            // compute the final commitment
            for i in 1..instance_num{
                C_first = RistrettoPoint::add(C_first_vec[i-1], C_first_vec[i]);
            }
        
            C_first.compress();

            // generate a double-size proof
            LinearProof::create(
                &mut transcript,
                &mut rng,
                &C,
                r,
                a.clone(),
                b.clone(),
                G.clone(),
                &F,
                &B,
            )
            .unwrap();
        })
    });
}

fn benches(c: &mut Criterion) {
    for i in 5..5 {
        commit(c, i);
    }
    for i in 5..5 {
        prove(c, i);
    }
    for i in 21..25 {
        verify(c, i);
    }
}

fn commit(criterion: &mut Criterion, log_n: usize) {

    let (instance_num, power) = nearest_power_of_two(log_n);
    let vector_len = (1 << log_n) / instance_num;
    let polynomial_size = instance_num * (vector_len - 1);

    let bp_gens = BulletproofGens::new(vector_len, 1);
    let mut rng = rand::thread_rng();

    // Calls `.G()` on generators, which should be a pub(crate) function only.
    // For now, make that function public so it can be accessed from benches.
    // We can't simply use bp_gens directly because we don't need the H generators.
    let G: Vec<RistrettoPoint> = bp_gens.share(0).G(vector_len).cloned().collect();
    let pedersen_gens = PedersenGens::default();
    let F = pedersen_gens.B;
    let B = pedersen_gens.B_blinding;

    let point = (0..(log_n - power + 1))
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let mut b = vec![u8_to_scalar(1)];
    for i in &point {
        let len = b.len();
        for j in 0..len {
            b.push(b[j] * i);
        }
    }

    // Generate the proof in its own scope to prevent reuse of
    // prover variables by the verifier
    // a and b are the vectors for which we want to prove c = <a,b>
    let mut a_vec: Vec<Vec<_>> = Vec::with_capacity(instance_num);
    for i in 1..=instance_num {
        let a: Vec<_> = (0..vector_len).map(|_| Scalar::random(&mut rng)).collect();
        a_vec.push(a);
    }

    // C' = <a, G> + r * B
    // C = <a, G> + r * B + <a, b> * F, where F is chosen by the verifier
    let r = Scalar::random(&mut rng);

    // generate parameters for the final commitment
    let bp_gens_final = BulletproofGens::new(instance_num, 1);

    let G_final: Vec<RistrettoPoint> = bp_gens_final.share(0).G(instance_num).cloned().collect();
    let pedersen_gens_final = PedersenGens::default();
    let B_final = pedersen_gens_final.B_blinding;

    let a_final: Vec<_> = (0..instance_num).map(|_| Scalar::random(&mut rng)).collect();

    let point_final = (0..power)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let mut b_final = vec![u8_to_scalar(1)];
    for i in &point_final {
        let len = b_final.len();
        for j in 0..len {
            b_final.push(b_final[j] * i);
        }
    }
    let r_final = Scalar::random(&mut rng);

    let mut group = criterion.benchmark_group("prove");
    group.sample_size(10);
    group.bench_function(format!("namedl-pad commit {}", log_n), move |bencher| {
        bencher.iter(|| {
            for i in 0..instance_num{  
                let com = RistrettoPoint::vartime_multiscalar_mul(
                    a_vec[i].iter().chain(iter::once(&r)),
                    G.iter().chain(iter::once(&B)),
                )
                .compress();
                let hash = blake3::hash(com.as_bytes());
            }
            RistrettoPoint::vartime_multiscalar_mul(
                a_final.iter().chain(iter::once(&r_final)),
                G_final.iter().chain(iter::once(&B_final)),
            )
            .compress();
        })
    });
}

fn verify(criterion: &mut Criterion, log_n: usize) {

    let (instance_num, power) = nearest_power_of_two(log_n);
    let vector_len = 2 * (1 << log_n) / instance_num;
    let double_vector_len = 2 * vector_len;
    let polynomial_size = instance_num * (vector_len - 1);
    let mut rng = rand::thread_rng();

    // generate the parameters of first half
    let bp_gens_first = BulletproofGens::new(vector_len, 1);
    let G_first: Vec<RistrettoPoint> = bp_gens_first.share(0).G(vector_len).cloned().collect();
    let pedersen_gens_first = PedersenGens::default();
    let F_first = pedersen_gens_first.B;
    let B_first = pedersen_gens_first.B_blinding;

    // generate commitments with instance_number
    let mut a_first_vec: Vec<Vec<_>> = Vec::with_capacity(instance_num);
    for i in 0..instance_num{
        let a_first: Vec<_> = (0..vector_len).map(|_| Scalar::random(&mut rng)).collect();
        a_first_vec.push(a_first);
    }
    let point_first = (0..(log_n - power + 1))
    .map(|_| Scalar::random(&mut rng))
    .collect::<Vec<_>>();
    let mut b_first = vec![u8_to_scalar(1)];
    for i in point_first {
        let len = b_first.len();
        for j in 0..len {
            b_first.push(b_first[j] * i);
        }
    }
    let r_first = Scalar::random(&mut rng);
    let mut c_first_vec: Vec<_> = Vec::with_capacity(instance_num);
    let mut C_first_vec: Vec<_> = Vec::with_capacity(instance_num);

    for i in 0..instance_num {
        c_first_vec.push(inner_product(&a_first_vec[i], &b_first));
        C_first_vec.push(RistrettoPoint::vartime_multiscalar_mul(
            a_first_vec[i].iter().chain(iter::once(&r_first)).chain(iter::once(&c_first_vec[i])),
            G_first.iter().chain(iter::once(&B_first)).chain(iter::once(&F_first)),
        ));
    }
    let mut C_first = C_first_vec[0];

    // generate the second commitment
    let bp_gens = BulletproofGens::new(double_vector_len, 1);
    let mut rng = rand::thread_rng();

    // Calls `.G()` on generators, which should be a pub(crate) function only.
    // For now, make that function public so it can be accessed from benches.
    // We can't simply use bp_gens directly because we don't need the H generators.
    let G: Vec<RistrettoPoint> = bp_gens.share(0).G(double_vector_len).cloned().collect();
    let pedersen_gens = PedersenGens::default();
    let F = pedersen_gens.B;
    let B = pedersen_gens.B_blinding;

    let point = (0..(log_n - power + 2))
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let mut b = vec![u8_to_scalar(1)];
    for i in &point {
        let len = b.len();
        for j in 0..len {
            b.push(b[j] * i);
        }
    }

    // Generate the proof in its own scope to prevent reuse of
    // prover variables by the verifier
    let (proof, C) = {
        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..double_vector_len).map(|_| Scalar::random(&mut rng)).collect();

        let mut transcript = Transcript::new(b"LinearProofBenchmark");

        // C = <a, G> + r * B + <a, b> * F
        let r = Scalar::random(&mut rng);
        let c = inner_product(&a, &b);
        let C = RistrettoPoint::vartime_multiscalar_mul(
            a.iter().chain(iter::once(&r)).chain(iter::once(&c)),
            G.iter().chain(iter::once(&B)).chain(iter::once(&F)),
        )
        .compress();

        let proof = LinearProof::create(
            &mut transcript,
            &mut rng,
            &C,
            r,
            a.clone(),
            b.clone(),
            G.clone(),
            &F,
            &B,
        )
        .unwrap();

        (proof, C)
    };
    println!(
        "proof size of {} variables is {} bytes",
        log_n,
        proof.serialized_size() + 32 * instance_num + 32 * instance_num
    );

    let mut group = criterion.benchmark_group("prove");
    group.sample_size(10);
    group.bench_function(format!("namedl-pad verify point value {}", log_n), move |bencher| {
        bencher.iter(|| {

            // compute the final commitment
            for i in 1..instance_num{
                C_first = RistrettoPoint::add(C_first_vec[i-1], C_first_vec[i]);
                let hash = blake3::hash(C_first_vec[i-1].compress().as_bytes());
            }
        
            C_first.compress();

            // generate a double-size proof
            let mut verifier_transcript = Transcript::new(b"LinearProofBenchmark");
            let mut b = vec![u8_to_scalar(1)];
            for i in &point {
                let len = b.len();
                for j in 0..len {
                    b.push(b[j] * i);
                }
            }
            proof
                .verify(&mut verifier_transcript, &C, &G, &F, &B, b)
                .unwrap();
        })
    });
}
