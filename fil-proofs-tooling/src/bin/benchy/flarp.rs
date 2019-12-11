use bellperson::Circuit;
use fil_proofs_tooling::{measure, Metadata};
use filecoin_proofs::generate_candidates;
use filecoin_proofs::types::PaddedBytesAmount;
use filecoin_proofs::types::*;
use filecoin_proofs::types::{PoStConfig, SectorSize};
use log::info;
use paired::bls12_381::Bls12;
use rand_xorshift::XorShiftRng;
use serde::{Deserialize, Serialize};
use storage_proofs::circuit::bench::BenchCS;
use storage_proofs::compound_proof::CompoundProof;
use storage_proofs::hasher::{PedersenHasher, Sha256Hasher};
#[cfg(feature = "measurements")]
use storage_proofs::measurements::Operation;
#[cfg(feature = "measurements")]
use storage_proofs::measurements::OP_MEASUREMENTS;
use storage_proofs::proof::ProofScheme;
use storage_proofs::sector::SectorId;

use crate::shared::{
    create_replicas, prove_replicas, CommitReplicaOutput, PreCommitReplicaOutput, CHALLENGE_COUNT,
    PROVER_ID, RANDOMNESS,
};
use filecoin_proofs::constants::SectorInfo;
use std::sync::atomic::Ordering::Relaxed;

/*
cat config.json \
    jq 'def round: . + 0.5 | floor; . | { "post_challenges": .["post_challenges"] | round, "window_size_bytes": .["window_size_bytes"] | round, "sector_size_bytes": .["sector_size_bytes"] | round, "drg_parents": .["drg_parents"] | round, "expander_parents": .["expander_parents"] | round, "graph_name": .["graph_name"] | round, "graph_parents": .["graph_parents"] | round, "porep_challenges": .["porep_challenges"] | round, "stacked_layers": .["stacked_layers"] | round, "wrapper_parents": .["wrapper_parents"] | round, "wrapper_parents_all": .["wrapper_parents_all"] | round }' \
    | RUST_BACKTRACE=1 RUST_LOG=info cargo run --release --package fil-proofs-tooling --bin=benchy  -- flarp
*/

const SEED: [u8; 16] = [
    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc, 0xe5,
];

#[derive(Default, Debug, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct FlarpReport {
    inputs: FlarpInputs,
    outputs: FlarpOutputs,
}

#[derive(Default, Debug, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct FlarpInputs {
    window_size_bytes: usize,
    sector_size_bytes: usize,
    drg_parents: usize,
    expander_parents: usize,
    porep_challenges: usize,
    post_challenges: usize,
    post_challenged_nodes: usize,
    stacked_layers: usize,
    wrapper_parents_all: usize,
}

#[derive(Default, Debug, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct FlarpOutputs {
    encoding_cpu_time_ms: u64,
    encoding_wall_time_ms: u64,
    generate_tree_c_cpu_time_ms: u64,
    generate_tree_c_wall_time_ms: u64,
    porep_proof_gen_cpu_time_ms: u64,
    porep_proof_gen_wall_time_ms: u64,
    tree_r_last_cpu_time_ms: u64,
    tree_r_last_wall_time_ms: u64,
    comm_d_cpu_time_ms: u64,
    comm_d_wall_time_ms: u64,
    encode_window_time_all_cpu_time_ms: u64,
    encode_window_time_all_wall_time_ms: u64,
    window_comm_leaves_time_cpu_time_ms: u64,
    window_comm_leaves_time_wall_time_ms: u64,
    porep_commit_time_cpu_time_ms: u64,
    porep_commit_time_wall_time_ms: u64,
    post_inclusion_proofs_cpu_time_ms: u64,
    post_inclusion_proofs_time_ms: u64,
    post_finalize_ticket_cpu_time_ms: u64,
    post_finalize_ticket_time_ms: u64,
    post_read_challenged_range_cpu_time_ms: u64,
    post_read_challenged_range_time_ms: u64,
    post_partial_ticket_hash_cpu_time_ms: u64,
    post_partial_ticket_hash_time_ms: u64,
    #[serde(flatten)]
    circuits: CircuitOutputs,
}

#[cfg(not(feature = "measurements"))]
fn augment_with_op_measurements(mut _output: &mut FlarpOutputs) {}

#[cfg(feature = "measurements")]
fn augment_with_op_measurements(mut output: &mut FlarpOutputs) {
    // drop the tx side of the channel, causing the iterator to yield None
    // see also: https://doc.rust-lang.org/src/std/sync/mpsc/mod.rs.html#368
    OP_MEASUREMENTS
        .0
        .lock()
        .expect("failed to acquire mutex")
        .take();

    let measurements = OP_MEASUREMENTS
        .1
        .lock()
        .expect("failed to acquire lock on rx side of perf channel");

    for m in measurements.iter() {
        use Operation::*;
        let cpu_time = m.cpu_time.as_millis() as u64;
        let wall_time = m.wall_time.as_millis() as u64;

        match m.op {
            GenerateTreeC => {
                output.generate_tree_c_cpu_time_ms = cpu_time;
                output.generate_tree_c_wall_time_ms = wall_time;
            }
            GenerateTreeRLast => {
                output.tree_r_last_cpu_time_ms = cpu_time;
                output.tree_r_last_wall_time_ms = wall_time;
            }
            CommD => {
                output.comm_d_cpu_time_ms = cpu_time;
                output.comm_d_wall_time_ms = wall_time;
            }
            EncodeWindowTimeAll => {
                output.encode_window_time_all_cpu_time_ms = cpu_time;
                output.encode_window_time_all_wall_time_ms = wall_time;
            }
            WindowCommLeavesTime => {
                output.window_comm_leaves_time_cpu_time_ms = cpu_time;
                output.window_comm_leaves_time_wall_time_ms = wall_time;
            }
            PorepCommitTime => {
                output.porep_commit_time_cpu_time_ms = cpu_time;
                output.porep_commit_time_wall_time_ms = wall_time;
            }
            PostInclusionProofs => {
                output.post_inclusion_proofs_cpu_time_ms = cpu_time;
                output.post_inclusion_proofs_time_ms = wall_time;
            }
            PostFinalizeTicket => {
                output.post_finalize_ticket_cpu_time_ms = cpu_time;
                output.post_finalize_ticket_time_ms = wall_time;
            }
            PostReadChallengedRange => {
                output.post_read_challenged_range_cpu_time_ms = cpu_time;
                output.post_read_challenged_range_time_ms = wall_time;
            }
            PostPartialTicketHash => {
                output.post_partial_ticket_hash_cpu_time_ms = cpu_time;
                output.post_partial_ticket_hash_time_ms = wall_time;
            }
        }
    }
}

fn configure_global_config(inputs: &FlarpInputs) {
    let mut x = filecoin_proofs::constants::DEFAULT_WINDOWS
        .write()
        .expect("failed to acquire write lock on DEFAULT_WINDOWS");

    x.insert(
        inputs.sector_size_bytes as u64,
        SectorInfo {
            size: inputs.sector_size_bytes as u64,
            window_size: inputs.window_size_bytes,
        },
    );

    filecoin_proofs::constants::LAYERS.store(inputs.stacked_layers, Relaxed);
    filecoin_proofs::constants::WRAPPER_EXP_DEGREE.store(inputs.wrapper_parents_all, Relaxed);
    filecoin_proofs::constants::WINDOW_EXP_DEGREE.store(inputs.expander_parents, Relaxed);
    filecoin_proofs::constants::WINDOW_DRG_DEGREE.store(inputs.drg_parents, Relaxed);
    filecoin_proofs::constants::POREP_WINDOW_MINIMUM_CHALLENGES
        .store(inputs.porep_challenges, Relaxed);
    filecoin_proofs::constants::POREP_WRAPPER_MINIMUM_CHALLENGES
        .store(inputs.porep_challenges, Relaxed);
}

pub fn run(
    inputs: FlarpInputs,
    skip_seal_proof: bool,
    skip_post_proof: bool,
) -> Metadata<FlarpReport> {
    configure_global_config(&inputs);
    generate_params(&inputs);

    let mut outputs = FlarpOutputs::default();

    let sector_size = SectorSize(inputs.sector_size_bytes as u64);

    let (cfg, mut created) = create_replicas(sector_size, 1);

    let sector_id: SectorId = *created
        .keys()
        .nth(0)
        .expect("create_replicas produced no replicas");

    if !skip_seal_proof {
        let mut proved = prove_replicas(cfg, &created);

        let seal_commit: CommitReplicaOutput = proved
            .remove(&sector_id)
            .expect("failed to get seal commit from map");

        outputs.porep_proof_gen_cpu_time_ms = seal_commit.measurement.cpu_time.as_millis() as u64;
        outputs.porep_proof_gen_wall_time_ms = seal_commit.measurement.wall_time.as_millis() as u64;
    }

    let replica_info: PreCommitReplicaOutput = created
        .remove(&sector_id)
        .expect("failed to get replica from map");

    // replica_info is moved into the PoSt scope
    let encoding_wall_time_ms = replica_info.measurement.wall_time.as_millis() as u64;
    let encoding_cpu_time_ms = replica_info.measurement.cpu_time.as_millis() as u64;

    if !skip_post_proof {
        // Measure PoSt generation and verification.
        let post_config = PoStConfig {
            sector_size,
            challenge_count: inputs.post_challenges,
            challenged_nodes: inputs.post_challenged_nodes,
        };

        let _gen_candidates_measurement = measure(|| {
            generate_candidates(
                post_config,
                &RANDOMNESS,
                CHALLENGE_COUNT,
                &vec![(sector_id, replica_info.private_replica_info)]
                    .into_iter()
                    .collect(),
                PROVER_ID,
            )
        })
        .expect("failed to generate post candidates");

        //    let candidates = &gen_candidates_measurement.return_value;
        //
        //    let gen_post_measurement = measure(|| {
        //        generate_post(
        //            post_config,
        //            &CHALLENGE_SEED,
        //            &priv_replica_info,
        //            candidates
        //                .iter()
        //                .cloned()
        //                .map(Into::into)
        //                .collect::<Vec<_>>(),
        //            PROVER_ID,
        //        )
        //    })
        //    .expect("failed to generate PoSt");
        //
        //    let verify_post_measurement = measure(|| {
        //        verify_post(
        //            post_config,
        //            &CHALLENGE_SEED,
        //            CHALLENGE_COUNT,
        //            &gen_post_measurement.return_value,
        //            &pub_replica_info,
        //            &candidates
        //                .iter()
        //                .cloned()
        //                .map(Into::into)
        //                .collect::<Vec<_>>(),
        //            PROVER_ID,
        //        )
        //    })
        //    .expect("verify_post function returned an error");
        //
        //    assert!(
        //        verify_post_measurement.return_value,
        //        "generated PoSt was invalid"
        //    );
    }

    outputs.encoding_wall_time_ms = encoding_wall_time_ms;
    outputs.encoding_cpu_time_ms = encoding_cpu_time_ms;

    augment_with_op_measurements(&mut outputs);
    outputs.circuits = run_measure_circuits(&inputs);

    Metadata::wrap(FlarpReport { inputs, outputs }).expect("failed to retrieve metadata")
}

#[derive(Default, Debug, Serialize)]
struct CircuitOutputs {
    // porep_snark_partition_constraints
    pub porep_constraints: usize,
    // post_snark_constraints
    pub post_constraints: usize,
    // replica_inclusion (constraints: single merkle path pedersen)
    // data_inclusion (constraints: sha merklepath)
    // window_inclusion (constraints: merkle inclusion path in comm_c)
    // ticket_constraints - (skip)
    // replica_inclusion (constraints: single merkle path pedersen)
    // column_leaf_hash_constraints - (64 byte * stacked layers) pedersen_md
    // kdf_constraints
    pub kdf_constraints: usize,
    // merkle_tree_datahash_constraints - sha2 constraints 64
    // merkle_tree_hash_constraints - 64 byte pedersen
    // ticket_proofs (constraints: pedersen_md inside the election post)
}

fn run_measure_circuits(i: &FlarpInputs) -> CircuitOutputs {
    let porep_constraints = measure_porep_circuit(i);
    let post_constraints = measure_post_circuit(i);
    let kdf_constraints = measure_kdf_circuit(i);

    CircuitOutputs {
        porep_constraints,
        post_constraints,
        kdf_constraints,
    }
}

fn measure_porep_circuit(i: &FlarpInputs) -> usize {
    use storage_proofs::circuit::stacked::StackedCompound;
    use storage_proofs::drgraph::new_seed;
    use storage_proofs::stacked::{SetupParams, StackedConfig, StackedDrg};

    let layers = i.stacked_layers;
    let window_challenge_count = i.porep_challenges;
    let wrapper_challenge_count = i.porep_challenges;
    let window_drg_degree = i.drg_parents;
    let window_expansion_degree = i.expander_parents;
    let wrapper_expansion_degree = i.wrapper_parents_all;
    let window_size_nodes = i.window_size_bytes / 32;
    let nodes = i.sector_size_bytes / 32;

    let config =
        StackedConfig::new(layers, window_challenge_count, wrapper_challenge_count).unwrap();

    let sp = SetupParams {
        nodes,
        window_drg_degree,
        window_expansion_degree,
        wrapper_expansion_degree,
        seed: new_seed(),
        config,
        window_size_nodes,
    };

    let pp = StackedDrg::<PedersenHasher, Sha256Hasher>::setup(&sp).unwrap();

    let mut cs = BenchCS::<Bls12>::new();
    <StackedCompound as CompoundProof<_, StackedDrg<PedersenHasher, Sha256Hasher>, _>>::blank_circuit(&pp)
        .synthesize(&mut cs).unwrap();

    cs.num_constraints()
}

fn measure_post_circuit(i: &FlarpInputs) -> usize {
    use filecoin_proofs::parameters::post_setup_params;
    use storage_proofs::circuit::election_post::ElectionPoStCompound;
    use storage_proofs::election_post;

    let post_config = PoStConfig {
        sector_size: SectorSize(i.sector_size_bytes as u64),
        challenge_count: i.post_challenges,
        challenged_nodes: i.post_challenged_nodes,
    };

    let vanilla_params = post_setup_params(post_config);
    let pp = election_post::ElectionPoSt::<PedersenHasher>::setup(&vanilla_params).unwrap();

    let mut cs = BenchCS::<Bls12>::new();
    ElectionPoStCompound::<PedersenHasher>::blank_circuit(&pp)
        .synthesize(&mut cs)
        .unwrap();

    cs.num_constraints()
}

fn measure_kdf_circuit(i: &FlarpInputs) -> usize {
    use bellperson::gadgets::boolean::Boolean;
    use bellperson::ConstraintSystem;
    use ff::Field;
    use paired::bls12_381::Fr;
    use rand::thread_rng;
    use storage_proofs::circuit::uint64;
    use storage_proofs::fr32::fr_into_bytes;
    use storage_proofs::util::bytes_into_boolean_vec_be;

    let mut cs = BenchCS::<Bls12>::new();
    let rng = &mut thread_rng();

    let parents = i.drg_parents + i.expander_parents;

    let id: Vec<u8> = fr_into_bytes::<Bls12>(&Fr::random(rng));
    let parents: Vec<Vec<u8>> = (0..parents)
        .map(|_| fr_into_bytes::<Bls12>(&Fr::random(rng)))
        .collect();

    let id_bits: Vec<Boolean> = {
        let mut cs = cs.namespace(|| "id");
        bytes_into_boolean_vec_be(&mut cs, Some(id.as_slice()), id.len()).unwrap()
    };
    let parents_bits: Vec<Vec<Boolean>> = parents
        .clone()
        .iter()
        .enumerate()
        .map(|(i, p)| {
            let mut cs = cs.namespace(|| format!("parents {}", i));
            bytes_into_boolean_vec_be(&mut cs, Some(p.as_slice()), p.len()).unwrap()
        })
        .collect();

    let window_index_raw = 12u64;
    let node_raw = 123456789u64;
    let window_index = uint64::UInt64::constant(window_index_raw);
    let node = uint64::UInt64::constant(node_raw);

    storage_proofs::circuit::create_label::create_label(
        cs.namespace(|| "create_label"),
        &id_bits,
        parents_bits,
        Some(window_index),
        Some(node),
    )
    .expect("key derivation function failed");

    cs.num_constraints()
}

fn generate_params(i: &FlarpInputs) {
    info!("generating params: porep");

    cache_porep_params(PoRepConfig {
        sector_size: SectorSize(i.sector_size_bytes),
        partitions: 10, // TODO: use from inputs
    });

    info!("generating params: post");
    cache_post_params(PoStConfig {
        sector_size: SectorSize(i.sector_size_bytes),
        challenge_count: i.post_challenges,
        challenged_nodes: i.post_challenged_nodes,
    });
}

fn cache_porep_params(porep_config: PoRepConfig) {
    use filecoin_proofs::parameters::public_params;
    use storage_proofs::circuit::stacked::StackedCompound;
    use storage_proofs::stacked::StackedDrg;

    let n = u64::from(PaddedBytesAmount::from(porep_config));
    let public_params = public_params(
        PaddedBytesAmount::from(porep_config),
        usize::from(PoRepProofPartitions::from(porep_config)),
    )
    .unwrap();

    {
        let circuit = <StackedCompound as CompoundProof<
            _,
            StackedDrg<PedersenHasher, Sha256Hasher>,
            _,
        >>::blank_circuit(&public_params);
        StackedCompound::get_param_metadata(circuit, &public_params);
    }
    {
        let circuit = <StackedCompound as CompoundProof<
            _,
            StackedDrg<PedersenHasher, Sha256Hasher>,
            _,
        >>::blank_circuit(&public_params);
        StackedCompound::get_groth_params(
            Some(&mut XorShiftRng::from_seed(SEED)),
            circuit,
            &public_params,
        )
        .expect("failed to get groth params");
    }
    {
        let circuit = <StackedCompound as CompoundProof<
            _,
            StackedDrg<PedersenHasher, Sha256Hasher>,
            _,
        >>::blank_circuit(&public_params);

        let rando: Option<&mut XorShiftRng> = None;
        StackedCompound::get_verifying_key(rando, circuit, &public_params)
            .expect("failed to get verifying key");
    }
}

fn cache_post_params(post_config: PoStConfig) {
    let n = u64::from(PaddedBytesAmount::from(post_config));

    let post_public_params = post_public_params(post_config).unwrap();

    {
        let post_circuit: ElectionPoStCircuit<Bls12, PedersenHasher> =
            <ElectionPoStCompound<PedersenHasher> as CompoundProof<
                Bls12,
                ElectionPoSt<PedersenHasher>,
                ElectionPoStCircuit<Bls12, PedersenHasher>,
            >>::blank_circuit(&post_public_params);
        let _ = <ElectionPoStCompound<PedersenHasher>>::get_param_metadata(
            post_circuit,
            &post_public_params,
        )
        .expect("failed to get metadata");
    }
    {
        let post_circuit: ElectionPoStCircuit<Bls12, PedersenHasher> =
            <ElectionPoStCompound<PedersenHasher> as CompoundProof<
                Bls12,
                ElectionPoSt<PedersenHasher>,
                ElectionPoStCircuit<Bls12, PedersenHasher>,
            >>::blank_circuit(&post_public_params);
        <ElectionPoStCompound<PedersenHasher>>::get_groth_params(
            Some(&mut XorShiftRng::from_seed(SEED)),
            post_circuit,
            &post_public_params,
        )
        .expect("failed to get groth params");
    }
    {
        let post_circuit: ElectionPoStCircuit<Bls12, PedersenHasher> =
            <ElectionPoStCompound<PedersenHasher> as CompoundProof<
                Bls12,
                ElectionPoSt<PedersenHasher>,
                ElectionPoStCircuit<Bls12, PedersenHasher>,
            >>::blank_circuit(&post_public_params);

        let rando: Option<&mut OsRng> = None;
        <ElectionPoStCompound<PedersenHasher>>::get_verifying_key(
            rando,
            post_circuit,
            &post_public_params,
        )
        .expect("failed to get verifying key");
    }
}