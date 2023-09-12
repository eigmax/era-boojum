#![feature(generic_const_exprs)]
use boojum::algebraic_props::round_function::AbsorptionModeOverwrite;
use boojum::algebraic_props::sponge::GoldilocksPoseidonSponge;
use boojum::config::DevCSConfig;
use boojum::cs::cs_builder::CsBuilder;
use boojum::cs::cs_builder::{new_builder, CsBuilderImpl};
use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
use boojum::cs::cs_builder_verifier::CsVerifierBuilder;
use boojum::cs::gates::ConstantAllocatableCS;
use boojum::cs::gates::ConstantsAllocatorGate;
use boojum::cs::gates::FmaGateInBaseFieldWithoutConstant;
use boojum::cs::gates::ReductionByPowersGate;
use boojum::cs::gates::U32AddGate;
use boojum::cs::gates::{
    fma_gate_without_constant::*, BooleanConstraintGate, NopGate, ReductionGate, ZeroCheckGate,
};
use boojum::cs::implementations::pow::NoPow;
use boojum::cs::implementations::prover::ProofConfig;
use boojum::cs::implementations::transcript::GoldilocksPoisedonTranscript;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::cs::traits::gate::GatePlacementStrategy;
use boojum::cs::GateConfigurationHolder;
use boojum::cs::StaticToolboxHolder;
use boojum::field::goldilocks::GoldilocksExt2;
use boojum::field::goldilocks::GoldilocksField;
use boojum::field::Field;
use boojum::field::U64Representable;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::num::Num;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::traits::witnessable::WitnessHookable;
use boojum::gadgets::u32::UInt32;
use boojum::worker::Worker;

type F = GoldilocksField;

fn configure<T: CsBuilderImpl<F, T>, GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>(
    builder: CsBuilder<T, F, GC, TB>,
) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
    let builder = ConstantsAllocatorGate::configure_builder(
        builder,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
        builder,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    /*
    let builder = ZeroCheckGate::configure_builder(
        builder,
        GatePlacementStrategy::UseGeneralPurposeColumns,
        false,
    );
    */
    let builder =
        NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);
    //let builder = BooleanConstraintGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

    builder
}

/// Given input f(0) = 0, f(1) = 1, calculate f(x) = f(x-1) + f(x-2), compute f(2**16)
///     let i0' = i1, i1' = i0 + i1
fn multiplex() {
    let geometry = boojum::cs::CSGeometry {
        num_columns_under_copy_permutation: 8,
        num_witness_columns: 2,
        num_constant_columns: 2,
        max_allowed_constraint_degree: 16,
    };
    let max_variables = 1 << 8;
    let max_trace_len = 1 << 18;
    let builder = new_builder::<_, F>(CsReferenceImplementationBuilder::<
        GoldilocksField,
        GoldilocksField,
        DevCSConfig,
    >::new(geometry, max_variables, max_trace_len));
    let builder = configure(builder);
    let mut cs = builder.build(());

    let mut i0 = None;
    let mut i1 = None;
    let mut xx0 = 0;
    let mut xx1 = 0;

    let one_variable = cs.allocate_constant(F::ONE);

    for i in 0..1 {
        let x0 = if let Some(i0) = i0.take() {
            i0
        } else {
            xx0 = 0;
            cs.alloc_single_variable_from_witness(F::ZERO)
        };
        let x1 = if let Some(i1) = i1.take() {
            i1
        } else {
            xx1 = 1;
            cs.alloc_single_variable_from_witness(F::ONE)
        };
        let x00 = FmaGateInBaseFieldWithoutConstant::compute_fma(
            &mut cs,
            F::ZERO,
            (one_variable, one_variable),
            F::ONE,
            x1,
        );
        let x1 = FmaGateInBaseFieldWithoutConstant::compute_fma(
            &mut cs,
            F::ONE,
            (x0, one_variable),
            F::ONE,
            x1,
        );
        let tmp = xx0;
        xx0 = xx1;
        xx1 = tmp + xx1;

        i0 = Some(x00);
        i1 = Some(x1);
    }
    cs.set_public(0, 0);
    cs.set_public(1, 0);
    cs.set_public(2, 0);
    cs.set_public(3, 0);
    cs.set_public(4, 0);
    cs.set_public(5, 0);

    assert_eq!((Num::from_variable(i0.unwrap()).witness_hook(&cs))().unwrap(), xx0);
    assert_eq!((Num::from_variable(i1.unwrap()).witness_hook(&cs))().unwrap(), xx1);

    let worker = Worker::new();
    cs.pad_and_shrink();
    let cs = cs.into_assembly();

    let lde_factor_to_use = 4;
    let mut proof_config = ProofConfig::default();
    proof_config.fri_lde_factor = lde_factor_to_use;
    proof_config.pow_bits = 0;
    proof_config.merkle_tree_cap_size = 4;
    proof_config.security_level = 2;

    let now = std::time::Instant::now();

    let (proof, vk) = cs.prove_one_shot::<
        GoldilocksExt2,
        GoldilocksPoisedonTranscript,
        GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
        NoPow,
        >(&worker, proof_config, ());
    let elapsed_time = now.elapsed();
    println!("Running prove_one_shot() took {} seconds.", elapsed_time.as_secs());
    let str_proof = serde_json::to_string(&proof).unwrap();
    println!("proof size: {} KB", str_proof.len() as f32 / 1000.0);
    for i in &proof.public_inputs {
        println!("output: {}", i);
    }

    let builder_impl = CsVerifierBuilder::<F, GoldilocksExt2>::new_from_parameters(geometry);
    let builder = new_builder::<_, F>(builder_impl);

    let builder = configure(builder);

    let verifier = builder.build(());
    let is_valid = verifier.verify::<
        GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
        GoldilocksPoisedonTranscript,
        NoPow
            >(
                (),
                &vk,
                &proof,
            );
    assert!(is_valid);
    println!("{is_valid}");
}

fn main() {
    multiplex();
}
