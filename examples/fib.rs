#![feature(generic_const_exprs)]
use boojum::algebraic_props::round_function::AbsorptionModeOverwrite;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::algebraic_props::sponge::GoldilocksPoseidonSponge;
use boojum::field::U64Representable;
use boojum::cs::gates::ConstantAllocatableCS;
use boojum::config::DevCSConfig;
use boojum::cs::cs_builder::CsBuilder;
use boojum::cs::cs_builder::{new_builder, CsBuilderImpl};
use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
use boojum::cs::cs_builder_verifier::CsVerifierBuilder;
use boojum::cs::gates::ConstantsAllocatorGate;
use boojum::cs::gates::FmaGateInBaseFieldWithoutConstant;
use boojum::cs::gates::ReductionByPowersGate;
use boojum::cs::gates::U32AddGate;
use boojum::cs::gates::{fma_gate_without_constant::*, NopGate, ReductionGate, ZeroCheckGate, BooleanConstraintGate};
use boojum::cs::implementations::pow::NoPow;
use boojum::cs::implementations::prover::ProofConfig;
use boojum::cs::implementations::transcript::GoldilocksPoisedonTranscript;
use boojum::cs::traits::gate::GatePlacementStrategy;
use boojum::cs::GateConfigurationHolder;
use boojum::cs::StaticToolboxHolder;
use boojum::field::goldilocks::GoldilocksExt2;
use boojum::field::goldilocks::GoldilocksField;
use boojum::field::Field;
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
    //let builder = ConstantsAllocatorGate::configure_builder(
    //    builder,
    //    GatePlacementStrategy::UseGeneralPurposeColumns,
    //);
    //let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
    //    builder,
    //    GatePlacementStrategy::UseGeneralPurposeColumns,
    //);
    let builder = ZeroCheckGate::configure_builder(
        builder,
        GatePlacementStrategy::UseGeneralPurposeColumns,
        false,
    );
    let builder =
        NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);
    //let builder = BooleanConstraintGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

    builder
}

/// Given input instruct, b, c, d, guarantee:
///    is_zero(x) = 1 - x * x^{-1}
///    sel_0 = is_zero(instruct);
///    sel_1 = is_zero(instruct - 1);
///    sel_2 = is_zero(instruct - 2);
///    sel_3 = (1 - sel_0) * (1 - sel_1) * (1 - sel_2);
///    d = sel_0 * (b + c) + sel_1*(b/c) + sel_2*(b-c) + sel_3*0xFFFFFFFF
fn multiplex() {
    let geometry = boojum::cs::CSGeometry {
        num_columns_under_copy_permutation: 8,
        num_witness_columns: 3,
        num_constant_columns: 3,
        max_allowed_constraint_degree: 8,
    };
    let max_variables = 100;
    let max_trace_len = 8;
    let builder = new_builder::<_, F>(CsReferenceImplementationBuilder::<
        GoldilocksField,
        GoldilocksField,
        DevCSConfig,
    >::new(geometry, max_variables, max_trace_len));
    let builder = configure(builder);
    let mut cs = builder.build(());

    let mut i0 = cs.alloc_single_variable_from_witness(F::ZERO);
    let mut i1 = cs.alloc_single_variable_from_witness(F::ONE);

    for i in 0..20 {
        let one_variable = cs.allocate_constant(F::ONE);
        let x0 = FmaGateInBaseFieldWithoutConstant::compute_fma(
            &mut cs,
            F::ONE,
            (i0, one_variable),
            F::ONE,
            i1,
        );
        let x1 = FmaGateInBaseFieldWithoutConstant::compute_fma(
            &mut cs,
            F::ONE,
            (x0, one_variable),
            F::ONE,
            i1,
        );
        i0 = x0;
        i1 = x1;
    }

    // let i = cs.alloc_single_variable_from_witness(GoldilocksField::ZERO);
    // ZeroCheckGate::check_if_zero(&mut cs, i);

    let worker = Worker::new();
    cs.pad_and_shrink();
    let cs = cs.into_assembly();

    let lde_factor_to_use = 2;
    let mut proof_config = ProofConfig::default();
    proof_config.fri_lde_factor = lde_factor_to_use;
    proof_config.pow_bits = 0;

    let (proof, vk) = cs.prove_one_shot::<
        GoldilocksExt2,
        GoldilocksPoisedonTranscript,
        GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
        NoPow,
        >(&worker, proof_config, ());

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
}

fn main() {
    multiplex();
}
