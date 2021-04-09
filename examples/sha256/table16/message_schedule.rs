use std::convert::TryInto;

use super::{super::BLOCK_SIZE, BlockWord, CellValue16, SpreadInputs, Table16Assignment, ROUNDS};
use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Config, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Permutation},
    poly::Rotation,
};

mod schedule_gates;
mod schedule_util;
mod subregion1;
mod subregion2;
mod subregion3;

use schedule_gates::ScheduleGate;
use schedule_util::*;

#[cfg(test)]
pub use schedule_util::get_msg_schedule_test_input;

#[derive(Clone, Debug)]
pub(super) struct MessageWord {
    var: Cell,
    value: Option<u32>,
}

#[derive(Clone, Debug)]
pub(super) struct MessageScheduleConfigured {
    lookup: SpreadInputs,
    message_schedule: Column<Advice>,
    extras: [Column<Advice>; 6],

    /// Construct a word using reduce_4.
    s_word: Column<Fixed>,
    /// Decomposition gate for W_0, W_62, W_63.
    s_decompose_0: Column<Fixed>,
    /// Decomposition gate for W_[1..14]
    s_decompose_1: Column<Fixed>,
    /// Decomposition gate for W_[14..49]
    s_decompose_2: Column<Fixed>,
    /// Decomposition gate for W_[49..62]
    s_decompose_3: Column<Fixed>,
    /// sigma_0 gate for W_[1..14]
    s_lower_sigma_0: Column<Fixed>,
    /// sigma_1 gate for W_[49..62]
    s_lower_sigma_1: Column<Fixed>,
    /// sigma_0_v2 gate for W_[14..49]
    s_lower_sigma_0_v2: Column<Fixed>,
    /// sigma_1_v2 gate for W_[14..49]
    s_lower_sigma_1_v2: Column<Fixed>,
    perm: Permutation,
}

pub(super) struct MessageScheduleConfig<'a, F: FieldExt, L: Layouter> {
    pub configured: MessageScheduleConfigured,
    pub layouter: &'a mut L,
    pub marker: std::marker::PhantomData<F>,
}

impl<F: FieldExt, L: Layouter<Field = F>> Config for MessageScheduleConfig<'_, F, L> {
    type Root = Self;
    type Configured = MessageScheduleConfigured;
    type Loaded = ();
    type Field = F;
    type Layouter = L;

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

    fn configured(&self) -> &Self::Configured {
        &self.configured
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }

    fn load(&mut self) -> Result<(), halo2::plonk::Error> {
        // None of the instructions implemented by this config have any fixed state.
        // But if we required e.g. a lookup table, this is where we would load it.
        Ok(())
    }

    fn layouter(&mut self) -> &mut Self::Layouter {
        self.layouter
    }

    fn push_namespace<NR, N>(&mut self, _name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // TODO
    }

    /// Exits out of the existing namespace.
    ///
    /// Not intended for downstream consumption; use [`Layouter::namespace`] instead.
    fn pop_namespace(&mut self, _gadget_name: Option<String>) {
        // TODO
    }
}

impl<F: FieldExt, L: Layouter<Field = F>> Table16Assignment<F, L>
    for MessageScheduleConfig<'_, F, L>
{
}

impl<F: FieldExt, L: Layouter<Field = F>> MessageScheduleConfig<'_, F, L> {
    /// Configures the message schedule.
    ///
    /// `message_schedule` is the column into which the message schedule will be placed.
    /// The caller must create appropriate permutations in order to load schedule words
    /// into the compression rounds.
    ///
    /// `extras` contains columns that the message schedule will only use for internal
    /// gates, and will not place any constraints on (such as lookup constraints) outside
    /// itself.
    #[allow(clippy::many_single_char_names)]
    pub(super) fn configure(
        meta: &mut ConstraintSystem<F>,
        lookup: SpreadInputs,
        message_schedule: Column<Advice>,
        extras: [Column<Advice>; 6],
        perm: Permutation,
    ) -> MessageScheduleConfigured {
        // Create fixed columns for the selectors we will require.
        let s_word = meta.fixed_column();
        let s_decompose_0 = meta.fixed_column();
        let s_decompose_1 = meta.fixed_column();
        let s_decompose_2 = meta.fixed_column();
        let s_decompose_3 = meta.fixed_column();
        let s_lower_sigma_0 = meta.fixed_column();
        let s_lower_sigma_1 = meta.fixed_column();
        let s_lower_sigma_0_v2 = meta.fixed_column();
        let s_lower_sigma_1_v2 = meta.fixed_column();

        // Rename these here for ease of matching the gates to the specification.
        let a_0 = lookup.tag;
        let a_1 = lookup.dense;
        let a_2 = lookup.spread;
        let a_3 = extras[0];
        let a_4 = extras[1];
        let a_5 = message_schedule;
        let a_6 = extras[2];
        let a_7 = extras[3];
        let a_8 = extras[4];
        let a_9 = extras[5];

        // s_word for W_[16..64]
        meta.create_gate("s_word for W_[16..64]", |meta| {
            let s_word = meta.query_fixed(s_word, Rotation::cur());

            let sigma_0_lo = meta.query_advice(a_6, Rotation::prev());
            let sigma_0_hi = meta.query_advice(a_6, Rotation::cur());

            let sigma_1_lo = meta.query_advice(a_7, Rotation::prev());
            let sigma_1_hi = meta.query_advice(a_7, Rotation::cur());

            let w_minus_9_lo = meta.query_advice(a_8, Rotation::prev());
            let w_minus_9_hi = meta.query_advice(a_8, Rotation::cur());

            let w_minus_16_lo = meta.query_advice(a_3, Rotation::prev());
            let w_minus_16_hi = meta.query_advice(a_4, Rotation::prev());

            let word = meta.query_advice(a_5, Rotation::cur());
            let carry = meta.query_advice(a_9, Rotation::cur());

            ScheduleGate::s_word(
                s_word,
                sigma_0_lo,
                sigma_0_hi,
                sigma_1_lo,
                sigma_1_hi,
                w_minus_9_lo,
                w_minus_9_hi,
                w_minus_16_lo,
                w_minus_16_hi,
                word,
                carry,
            )
            .0
        });

        // s_decompose_0 for all words
        meta.create_gate("s_decompose_0", |meta| {
            let s_decompose_0 = meta.query_fixed(s_decompose_0, Rotation::cur());
            let lo = meta.query_advice(a_3, Rotation::cur());
            let hi = meta.query_advice(a_4, Rotation::cur());
            let word = meta.query_advice(a_5, Rotation::cur());

            ScheduleGate::s_decompose_0(s_decompose_0, lo, hi, word).0
        });

        // s_decompose_1 for W_[1..14]
        // (3, 4, 11, 14)-bit chunks
        meta.create_gate("s_decompose_1", |meta| {
            let s_decompose_1 = meta.query_fixed(s_decompose_1, Rotation::cur());
            let a = meta.query_advice(a_3, Rotation::next()); // 3-bit chunk
            let b = meta.query_advice(a_4, Rotation::next()); // 4-bit chunk
            let c = meta.query_advice(a_1, Rotation::next()); // 11-bit chunk
            let tag_c = meta.query_advice(a_0, Rotation::next());
            let d = meta.query_advice(a_1, Rotation::cur()); // 14-bit chunk
            let tag_d = meta.query_advice(a_0, Rotation::cur());
            let word = meta.query_advice(a_5, Rotation::cur());

            ScheduleGate::s_decompose_1(s_decompose_1, a, b, c, tag_c, d, tag_d, word).0
        });

        // s_decompose_2 for W_[14..49]
        // (3, 4, 3, 7, 1, 1, 13)-bit chunks
        meta.create_gate("s_decompose_2", |meta| {
            let s_decompose_2 = meta.query_fixed(s_decompose_2, Rotation::cur());
            let a = meta.query_advice(a_3, Rotation::prev()); // 3-bit chunk
            let b = meta.query_advice(a_1, Rotation::next()); // 4-bit chunk
            let c = meta.query_advice(a_4, Rotation::prev()); // 3-bit chunk
            let d = meta.query_advice(a_1, Rotation::cur()); // 7-bit chunk
            let tag_d = meta.query_advice(a_0, Rotation::cur());
            let e = meta.query_advice(a_3, Rotation::next()); // 1-bit chunk
            let f = meta.query_advice(a_4, Rotation::next()); // 1-bit chunk
            let g = meta.query_advice(a_1, Rotation::prev()); // 13-bit chunk
            let tag_g = meta.query_advice(a_0, Rotation::prev());
            let word = meta.query_advice(a_5, Rotation::cur());

            ScheduleGate::s_decompose_2(s_decompose_2, a, b, c, d, tag_d, e, f, g, tag_g, word).0
        });

        // s_decompose_3 for W_49 to W_61
        // (10, 7, 2, 13)-bit chunks
        meta.create_gate("s_decompose_3", |meta| {
            let s_decompose_3 = meta.query_fixed(s_decompose_3, Rotation::cur());
            let a = meta.query_advice(a_1, Rotation::next()); // 10-bit chunk
            let tag_a = meta.query_advice(a_0, Rotation::next());
            let b = meta.query_advice(a_4, Rotation::next()); // 7-bit chunk
            let c = meta.query_advice(a_3, Rotation::next()); // 2-bit chunk
            let d = meta.query_advice(a_1, Rotation::cur()); // 13-bit chunk
            let tag_d = meta.query_advice(a_0, Rotation::cur());
            let word = meta.query_advice(a_5, Rotation::cur());

            ScheduleGate::s_decompose_3(s_decompose_3, a, tag_a, b, c, d, tag_d, word).0
        });

        // sigma_0 v1 on W_[1..14]
        // (3, 4, 11, 14)-bit chunks
        meta.create_gate("sigma_0 v1", |meta| {
            ScheduleGate::s_lower_sigma_0(
                meta.query_fixed(s_lower_sigma_0, Rotation::cur()), // s_lower_sigma_0
                meta.query_advice(a_2, Rotation::prev()),           // spread_r0_even
                meta.query_advice(a_2, Rotation::cur()),            // spread_r0_odd
                meta.query_advice(a_2, Rotation::next()),           // spread_r1_even
                meta.query_advice(a_3, Rotation::cur()),            // spread_r1_odd
                meta.query_advice(a_5, Rotation::next()),           // a
                meta.query_advice(a_6, Rotation::next()),           // spread_a
                meta.query_advice(a_6, Rotation::cur()),            // b
                meta.query_advice(a_3, Rotation::prev()),           // b_lo
                meta.query_advice(a_4, Rotation::prev()),           // spread_b_lo
                meta.query_advice(a_5, Rotation::prev()),           // b_hi
                meta.query_advice(a_6, Rotation::prev()),           // spread_b_hi
                meta.query_advice(a_4, Rotation::cur()),            // spread_c
                meta.query_advice(a_5, Rotation::cur()),            // spread_d
            )
            .0
        });

        // sigma_0 v2 on W_[14..49]
        // (3, 4, 3, 7, 1, 1, 13)-bit chunks
        meta.create_gate("sigma_0 v2", |meta| {
            ScheduleGate::s_lower_sigma_0_v2(
                meta.query_fixed(s_lower_sigma_0_v2, Rotation::cur()), // s_lower_sigma_0_v2
                meta.query_advice(a_2, Rotation::prev()),              // spread_r0_even
                meta.query_advice(a_2, Rotation::cur()),               // spread_r0_odd
                meta.query_advice(a_2, Rotation::next()),              // spread_r1_even
                meta.query_advice(a_3, Rotation::cur()),               // spread_r1_odd
                meta.query_advice(a_3, Rotation::next()),              // a
                meta.query_advice(a_4, Rotation::next()),              // spread_a
                meta.query_advice(a_6, Rotation::cur()),               // b
                meta.query_advice(a_3, Rotation::prev()),              // b_lo
                meta.query_advice(a_4, Rotation::prev()),              // spread_b_lo
                meta.query_advice(a_5, Rotation::prev()),              // b_hi
                meta.query_advice(a_6, Rotation::prev()),              // spread_b_hi
                meta.query_advice(a_5, Rotation::next()),              // c
                meta.query_advice(a_6, Rotation::next()),              // spread_c
                meta.query_advice(a_4, Rotation::cur()),               // spread_d
                meta.query_advice(a_7, Rotation::cur()),               // spread_e
                meta.query_advice(a_7, Rotation::next()),              // spread_f
                meta.query_advice(a_5, Rotation::cur()),               // spread_g
            )
            .0
        });

        // sigma_1 v2 on W_14 to W_48
        // (3, 4, 3, 7, 1, 1, 13)-bit chunks
        meta.create_gate("sigma_1 v2", |meta| {
            ScheduleGate::s_lower_sigma_1_v2(
                meta.query_fixed(s_lower_sigma_1_v2, Rotation::cur()), // s_lower_sigma_1_v2
                meta.query_advice(a_2, Rotation::prev()),              // spread_r0_even
                meta.query_advice(a_2, Rotation::cur()),               // spread_r0_odd
                meta.query_advice(a_2, Rotation::next()),              // spread_r1_even
                meta.query_advice(a_3, Rotation::cur()),               // spread_r1_odd
                meta.query_advice(a_3, Rotation::next()),              // a
                meta.query_advice(a_4, Rotation::next()),              // spread_a
                meta.query_advice(a_6, Rotation::cur()),               // b
                meta.query_advice(a_3, Rotation::prev()),              // b_lo
                meta.query_advice(a_4, Rotation::prev()),              // spread_b_lo
                meta.query_advice(a_5, Rotation::prev()),              // b_hi
                meta.query_advice(a_6, Rotation::prev()),              // spread_b_hi
                meta.query_advice(a_5, Rotation::next()),              // c
                meta.query_advice(a_6, Rotation::next()),              // spread_c
                meta.query_advice(a_4, Rotation::cur()),               // spread_d
                meta.query_advice(a_7, Rotation::cur()),               // spread_e
                meta.query_advice(a_7, Rotation::next()),              // spread_f
                meta.query_advice(a_5, Rotation::cur()),               // spread_g
            )
            .0
        });

        // sigma_1 v1 on W_49 to W_61
        // (10, 7, 2, 13)-bit chunks
        meta.create_gate("sigma_1 v1", |meta| {
            ScheduleGate::s_lower_sigma_1(
                meta.query_fixed(s_lower_sigma_1, Rotation::cur()), // s_lower_sigma_1
                meta.query_advice(a_2, Rotation::prev()),           // spread_r0_even
                meta.query_advice(a_2, Rotation::cur()),            // spread_r0_odd
                meta.query_advice(a_2, Rotation::next()),           // spread_r1_even
                meta.query_advice(a_3, Rotation::cur()),            // spread_r1_odd
                meta.query_advice(a_4, Rotation::cur()),            // spread_a
                meta.query_advice(a_6, Rotation::cur()),            // b
                meta.query_advice(a_3, Rotation::prev()),           // b_lo
                meta.query_advice(a_4, Rotation::prev()),           // spread_b_lo
                meta.query_advice(a_5, Rotation::prev()),           // b_mid
                meta.query_advice(a_6, Rotation::prev()),           // spread_b_mid
                meta.query_advice(a_5, Rotation::next()),           // b_hi
                meta.query_advice(a_6, Rotation::next()),           // spread_b_hi
                meta.query_advice(a_3, Rotation::next()),           // c
                meta.query_advice(a_4, Rotation::next()),           // spread_c
                meta.query_advice(a_5, Rotation::cur()),            // spread_d
            )
            .0
        });

        MessageScheduleConfigured {
            lookup,
            message_schedule,
            extras,
            s_word,
            s_decompose_0,
            s_decompose_1,
            s_decompose_2,
            s_decompose_3,
            s_lower_sigma_0,
            s_lower_sigma_1,
            s_lower_sigma_0_v2,
            s_lower_sigma_1_v2,
            perm,
        }
    }

    #[allow(clippy::type_complexity)]
    pub(super) fn process(
        &mut self,
        input: [BlockWord; BLOCK_SIZE],
    ) -> Result<([MessageWord; ROUNDS], [(CellValue16, CellValue16); ROUNDS]), Error> {
        let configured = self.configured().clone();
        let mut w = Vec::<MessageWord>::with_capacity(ROUNDS);
        let mut w_halves = Vec::<(CellValue16, CellValue16)>::with_capacity(ROUNDS);

        self.layouter().assign_region(
            || "process message block",
            |mut region: Region<'_, Self>| {
                w = Vec::<MessageWord>::with_capacity(ROUNDS);
                w_halves = Vec::<(CellValue16, CellValue16)>::with_capacity(ROUNDS);

                // Assign all fixed columns
                for index in 1..14 {
                    let row = get_word_row(index);
                    region.assign_fixed(
                        || "s_decompose_1",
                        configured.s_decompose_1,
                        row,
                        || Ok(F::one()),
                    )?;
                    region.assign_fixed(
                        || "s_lower_sigma_0",
                        configured.s_lower_sigma_0,
                        row + 3,
                        || Ok(F::one()),
                    )?;
                }

                for index in 14..49 {
                    let row = get_word_row(index);
                    region.assign_fixed(
                        || "s_decompose_2",
                        configured.s_decompose_2,
                        row,
                        || Ok(F::one()),
                    )?;
                    region.assign_fixed(
                        || "s_lower_sigma_0_v2",
                        configured.s_lower_sigma_0_v2,
                        row + 3,
                        || Ok(F::one()),
                    )?;
                    region.assign_fixed(
                        || "s_lower_sigma_1_v2",
                        configured.s_lower_sigma_1_v2,
                        row + SIGMA_0_V2_ROWS + 3,
                        || Ok(F::one()),
                    )?;

                    let new_word_idx = index + 2;
                    region.assign_fixed(
                        || "s_word",
                        configured.s_word,
                        get_word_row(new_word_idx - 16) + 1,
                        || Ok(F::one()),
                    )?;
                }

                for index in 49..62 {
                    let row = get_word_row(index);
                    region.assign_fixed(
                        || "s_decompose_3",
                        configured.s_decompose_3,
                        row,
                        || Ok(F::one()),
                    )?;
                    region.assign_fixed(
                        || "s_lower_sigma_1",
                        configured.s_lower_sigma_1,
                        row + 3,
                        || Ok(F::one()),
                    )?;

                    let new_word_idx = index + 2;
                    region.assign_fixed(
                        || "s_word",
                        configured.s_word,
                        get_word_row(new_word_idx - 16) + 1,
                        || Ok(F::one()),
                    )?;
                }

                for index in 0..64 {
                    let row = get_word_row(index);
                    region.assign_fixed(
                        || "s_decompose_0",
                        configured.s_decompose_0,
                        row,
                        || Ok(F::one()),
                    )?;
                }
                Ok(())
            },
        )?;

        // Assign W[0..16]
        for (i, word) in input.iter().enumerate() {
            let (var, halves) = self.assign_word_and_halves(word.value.unwrap(), i)?;
            w.push(MessageWord {
                var,
                value: word.value,
            });
            w_halves.push(halves);
        }

        // Returns the output of sigma_0 on W_[1..14]
        let lower_sigma_0_output = self.assign_subregion1(&input[1..14])?;

        // sigma_0_v2 and sigma_1_v2 on W_[14..49]
        // Returns the output of sigma_0_v2 on W_[36..49], to be used in subregion3
        let lower_sigma_0_v2_output =
            self.assign_subregion2(lower_sigma_0_output, &mut w, &mut w_halves)?;

        // sigma_1 v1 on W[49..62]
        self.assign_subregion3(lower_sigma_0_v2_output, &mut w, &mut w_halves)?;

        Ok((w.try_into().unwrap(), w_halves.try_into().unwrap()))
    }

    /// Empty configuration without gates. Useful for fast testing
    #[cfg(test)]
    pub(super) fn empty_configure<F: FieldExt>(
        meta: &mut ConstraintSystem<F>,
        lookup: SpreadInputs,
        message_schedule: Column<Advice>,
        extras: [Column<Advice>; 6],
        perm: Permutation,
    ) -> Self {
        // Create fixed columns for the selectors we will require.
        let s_word = meta.fixed_column();
        let s_decompose_0 = meta.fixed_column();
        let s_decompose_1 = meta.fixed_column();
        let s_decompose_2 = meta.fixed_column();
        let s_decompose_3 = meta.fixed_column();
        let s_lower_sigma_0 = meta.fixed_column();
        let s_lower_sigma_1 = meta.fixed_column();
        let s_lower_sigma_0_v2 = meta.fixed_column();
        let s_lower_sigma_1_v2 = meta.fixed_column();

        MessageSchedule {
            lookup,
            message_schedule,
            extras,
            s_word,
            s_decompose_0,
            s_decompose_1,
            s_decompose_2,
            s_decompose_3,
            s_lower_sigma_0,
            s_lower_sigma_1,
            s_lower_sigma_0_v2,
            s_lower_sigma_1_v2,
            perm,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{
        super::BLOCK_SIZE, BlockWord, Compression, SpreadTable, Table16Config, Table16Configured,
    };
    use super::{schedule_util::*, MessageSchedule};
    use halo2::{
        arithmetic::FieldExt,
        circuit::{layouter, Layouter},
        dev::MockProver,
        pasta::Fp,
        plonk::{Assignment, Circuit, ConstraintSystem, Error, Permutation},
    };

    #[test]
    fn message_schedule() {
        struct MyCircuit {}

        impl<F: FieldExt> Circuit<F> for MyCircuit {
            type Configured = Table16Configured;

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Configured {
                let a = meta.advice_column();
                let b = meta.advice_column();
                let c = meta.advice_column();

                let (lookup_inputs, lookup_table) = SpreadTable::configure(meta, a, b, c);

                let message_schedule = meta.advice_column();
                let extras = [
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                ];

                // Rename these here for ease of matching the gates to the specification.
                let _a_0 = lookup_inputs.tag;
                let a_1 = lookup_inputs.dense;
                let a_2 = lookup_inputs.spread;
                let a_3 = extras[0];
                let a_4 = extras[1];
                let a_5 = message_schedule;
                let a_6 = extras[2];
                let a_7 = extras[3];
                let a_8 = extras[4];
                let _a_9 = extras[5];

                let perm = Permutation::new(
                    meta,
                    &[
                        a_1.into(),
                        a_2.into(),
                        a_3.into(),
                        a_4.into(),
                        a_5.into(),
                        a_6.into(),
                        a_7.into(),
                        a_8.into(),
                    ],
                );

                let compression = Compression::empty_configure(
                    meta,
                    lookup_inputs.clone(),
                    message_schedule,
                    extras,
                    perm.clone(),
                );

                let message_schedule =
                    MessageSchedule::configure(meta, lookup_inputs, message_schedule, extras, perm);

                Table16Configured {
                    lookup_table,
                    message_schedule,
                    compression,
                }
            }

            fn synthesize(
                &self,
                cs: &mut impl Assignment<F>,
                configured: Self::Configured,
            ) -> Result<(), Error> {
                let mut layouter =
                    layouter::SingleConfigLayouter::<Table16Config<F>, _>::new(cs, configured)?;

                // Load table
                let table = layouter.configured().lookup_table.clone();
                table.load(&mut layouter)?;

                // Provide input
                // Test vector: "abc"
                let inputs: [BlockWord; BLOCK_SIZE] = get_msg_schedule_test_input();

                // Run message_scheduler to get W_[0..64]
                let message_schedule = layouter.configured().message_schedule.clone();
                let (w, _) = message_schedule.process(&mut layouter, inputs)?;
                for (word, test_word) in w.iter().zip(MSG_SCHEDULE_TEST_OUTPUT.iter()) {
                    let word = word.value.unwrap();
                    assert_eq!(word, *test_word);
                }
                Ok(())
            }
        }

        let circuit: MyCircuit = MyCircuit {};

        let prover = match MockProver::<Fp>::run(16, &circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }
}
