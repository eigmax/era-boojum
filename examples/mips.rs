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
use boojum::cs::gates::SelectionGate;
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
    let builder = ZeroCheckGate::configure_builder(
        builder,
        GatePlacementStrategy::UseGeneralPurposeColumns,
        false,
    );
    let builder =
        SelectionGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);
    let builder =
        NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);
    // let builder = BooleanConstraintGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

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
        num_columns_under_copy_permutation: 16,
        num_witness_columns: 32,
        num_constant_columns: 8,
        max_allowed_constraint_degree: 8,
    };
    let max_variables = 100;
    let max_trace_len = 16;
    let builder = new_builder::<_, F>(CsReferenceImplementationBuilder::<
        GoldilocksField,
        GoldilocksField,
        DevCSConfig,
    >::new(geometry, max_variables, max_trace_len));
    let builder = configure(builder);
    let mut cs = builder.build(());

    let i_out = 0;
    let b_add_c_out = 3;
    let i = cs.alloc_single_variable_from_witness(GoldilocksField(i_out));
    let b = cs.alloc_single_variable_from_witness(GoldilocksField(2));
    let c = cs.alloc_single_variable_from_witness(GoldilocksField(1));
    let d = cs.alloc_single_variable_from_witness(GoldilocksField(b_add_c_out));

    let zero = cs.allocate_constant(GoldilocksField::ZERO);
    let one = cs.allocate_constant(GoldilocksField::ONE);
    let two = cs.allocate_constant(GoldilocksField::TWO);

    // i is 0
    let tt = Num::equals(&mut cs, &Num::from_variable(i), &Num::from_variable(zero));
    let i_0_ = Num::conditionally_select(
        &mut cs,
        tt,
        &Num::from_variable(one),
        &Num::from_variable(zero),
    )
    .get_variable();

    let i_sub_1 = FmaGateInBaseFieldWithoutConstant::compute_fma(
        &mut cs,
        F::ONE,
        (one, i),
        F::MINUS_ONE,
        one,
    ); // i - 1 is 0
    let tt = Num::equals(
        &mut cs,
        &Num::from_variable(i_sub_1),
        &Num::from_variable(zero),
    );
    let i_1_ = Num::conditionally_select(
        &mut cs,
        tt,
        &Num::from_variable(one),
        &Num::from_variable(zero),
    )
    .get_variable();

    let i_sub_2 = FmaGateInBaseFieldWithoutConstant::compute_fma(
        &mut cs,
        F::ONE,
        (one, i),
        F::MINUS_ONE,
        two,
    ); // i - 2 is 0
    let tt = Num::equals(
        &mut cs,
        &Num::from_variable(i_sub_2),
        &Num::from_variable(zero),
    );
    let i_2_ = Num::conditionally_select(
        &mut cs,
        tt,
        &Num::from_variable(one),
        &Num::from_variable(zero),
    )
    .get_variable();

    let i_mul_isub1 =
        FmaGateInBaseFieldWithoutConstant::compute_fma(&mut cs, F::ONE, (i_sub_1, i), F::ONE, zero);
    let i_mul_isub1_mul_isub2 = FmaGateInBaseFieldWithoutConstant::compute_fma(
        &mut cs,
        F::ONE,
        (i_sub_2, i_mul_isub1),
        F::ONE,
        zero,
    ); // i * (i-1) * (i-2) is NOT zero
    let tt = Num::equals(
        &mut cs,
        &Num::from_variable(i_mul_isub1_mul_isub2),
        &Num::from_variable(one),
    );
    let i_3_ = Num::conditionally_select(
        &mut cs,
        tt,
        &Num::from_variable(one),
        &Num::from_variable(zero),
    )
    .get_variable();

    // b + c
    let b_add_c =
        FmaGateInBaseFieldWithoutConstant::compute_fma(&mut cs, F::ONE, (one, b), F::ONE, c);

    // b - c
    let b_sub_c =
        FmaGateInBaseFieldWithoutConstant::compute_fma(&mut cs, F::ONE, (one, b), F::MINUS_ONE, c);

    // b / c
    let c_inv = FmaGateInBaseFieldWithoutConstant::create_inversion_constraint(&mut cs, c, one); // assume c is not 0
    let b_div_c =
        FmaGateInBaseFieldWithoutConstant::compute_fma(&mut cs, F::ONE, (b, c_inv), F::ONE, zero);

    let f6f = cs.allocate_constant(GoldilocksField(0xFFFFFFFF));

    // final = sel_0 * (b+c)
    let final_ = FmaGateInBaseFieldWithoutConstant::compute_fma(
        &mut cs,
        F::ONE,
        (i_0_, b_add_c),
        F::ONE,
        zero,
    );
    // final += sel_1 * (b/c)
    let final_ = FmaGateInBaseFieldWithoutConstant::compute_fma(
        &mut cs,
        F::ONE,
        (i_1_, b_div_c),
        F::ONE,
        final_,
    );
    // final += sel_2 * (b-c)
    let final_ = FmaGateInBaseFieldWithoutConstant::compute_fma(
        &mut cs,
        F::ONE,
        (i_2_, b_sub_c),
        F::ONE,
        final_,
    );
    // final += sel_3 * 0xFFFFFFFF
    let final_ = FmaGateInBaseFieldWithoutConstant::compute_fma(
        &mut cs,
        F::ONE,
        (i_3_, f6f),
        F::ONE,
        final_,
    );

    let final_ = FmaGateInBaseFieldWithoutConstant::compute_fma(
        &mut cs,
        F::ONE,
        (one, final_),
        F::MINUS_ONE,
        d
    );

    cs.set_public(0, 0);
    cs.set_public(1, 0);
    cs.set_public(2, 0);
    cs.set_public(3, 0);

    assert_eq!((Num::from_variable(i).witness_hook(&cs))().unwrap(), i_out);
    assert_eq!((Num::from_variable(b_add_c).witness_hook(&cs))().unwrap(), b_add_c_out);
    let final_out = 0;
    assert_eq!((Num::from_variable(final_).witness_hook(&cs))().unwrap(), final_out);

    let worker = Worker::new();
    cs.pad_and_shrink();
    let cs = cs.into_assembly();

    let lde_factor_to_use = 16;
    let mut proof_config = ProofConfig::default();
    proof_config.fri_lde_factor = lde_factor_to_use;
    proof_config.pow_bits = 0;

    let (proof, vk) = cs.prove_one_shot::<
        GoldilocksExt2,
        GoldilocksPoisedonTranscript,
        GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
        NoPow,
        >(&worker, proof_config, ());

    let str_proof = serde_json::to_string(&proof).unwrap();
    println!("proof size: {}KB", str_proof.len() / 1000);
    for pi in &proof.public_inputs {
        println!("{}", pi);
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
}

fn main() {
    multiplex();
}
