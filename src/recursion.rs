use anyhow::Result;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, VerifierCircuitData};
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::access_set::AccessSet;
use crate::signal::{Digest, PlonkyProof, Signal, C, F};

impl AccessSet {
    pub fn aggregate_signals(
        &self,
        topic0: Digest,
        signal0: Signal,
        topic1: Digest,
        signal1: Signal,
        verifier_data: &VerifierCircuitData<F, C, 2>,
    ) -> Result<(Digest, Digest, PlonkyProof, VerifierCircuitData<F, C, 2>)> {
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::new(config);
        let mut pw = PartialWitness::new();

        let public_inputs0: Vec<F> = self
            .0
            .cap
            .0
            .iter()
            .flat_map(|h| h.elements)
            .chain(signal0.nullifier)
            .chain(topic0)
            .collect();
        let public_inputs1: Vec<F> = self
            .0
            .cap
            .0
            .iter()
            .flat_map(|h| h.elements)
            .chain(signal1.nullifier)
            .chain(topic1)
            .collect();

        // `add_virtual_proof_with_pis` is an extended version of the `add_virtual_target`, but
        // that takes care of adding all the values of the proof and the public inputs (pis).
        let proof_target0 = builder.add_virtual_proof_with_pis(&verifier_data.common);
        // set the public inputs
        builder.register_public_inputs(&proof_target0.public_inputs);
        // `set_proof_with_pis_target` is an extended version of the `set_target`, but that takes
        // care of adding all the values of the proof and the public inputs.
        pw.set_proof_with_pis_target(
            &proof_target0,
            &ProofWithPublicInputs {
                proof: signal0.proof,
                public_inputs: public_inputs0,
            },
        )?;
        // add & set the verifier data
        let vd_target =
            builder.add_virtual_verifier_data(verifier_data.common.config.fri_config.cap_height);
        pw.set_verifier_data_target(&vd_target, &verifier_data.verifier_only)?;

        // now, the same as we did with the proof0, with the proof1 related values:
        let proof_target1 = builder.add_virtual_proof_with_pis(&verifier_data.common);
        builder.register_public_inputs(&proof_target1.public_inputs);
        pw.set_proof_with_pis_target(
            &proof_target1,
            &ProofWithPublicInputs {
                proof: signal1.proof,
                public_inputs: public_inputs1,
            },
        )?;
        let vd_target =
            builder.add_virtual_verifier_data(verifier_data.common.config.fri_config.cap_height);
        pw.set_verifier_data_target(&vd_target, &verifier_data.verifier_only)?;

        pw.set_cap_target(
            &vd_target.constants_sigmas_cap,
            &verifier_data.verifier_only.constants_sigmas_cap,
        )?;

        builder.verify_proof::<C>(&proof_target0, &vd_target, &verifier_data.common);
        builder.verify_proof::<C>(&proof_target1, &vd_target, &verifier_data.common);

        let data = builder.build();
        let recursive_proof = data.prove(pw)?;

        data.verify(recursive_proof.clone())?;

        Ok((
            signal0.nullifier,
            signal1.nullifier,
            recursive_proof.proof,
            data.verifier_data(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::types::{Field, Sample};
    use plonky2::hash::merkle_tree::MerkleTree;
    use plonky2::hash::poseidon::PoseidonHash;
    use plonky2::plonk::config::Hasher;
    use plonky2::plonk::proof::ProofWithPublicInputs;

    use crate::access_set::AccessSet;
    use crate::signal::{Digest, F};

    #[test]
    fn test_recursion() -> Result<()> {
        let n = 1 << 20;
        let private_keys: Vec<Digest> = (0..n).map(|_| F::rand_array()).collect();
        let public_keys: Vec<Vec<F>> = private_keys
            .iter()
            .map(|&sk| {
                PoseidonHash::hash_no_pad(&[sk, [F::ZERO; 4]].concat())
                    .elements
                    .to_vec()
            })
            .collect();
        let access_set = AccessSet(MerkleTree::new(public_keys, 0));

        // first proof
        let i0 = 12;
        let topic0 = F::rand_array();
        let (signal0, vd0) = access_set.make_signal(private_keys[i0], topic0, i0)?;
        access_set.verify_signal(topic0, signal0.clone(), &vd0)?;

        // second proof
        let i1 = 42;
        let topic1 = F::rand_array();
        let (signal1, vd1) = access_set.make_signal(private_keys[i1], topic1, i1)?;
        access_set.verify_signal(topic1, signal1.clone(), &vd1)?;

        // generate recursive proof
        let (nullifier0, nullifier1, recursive_proof, vd2) =
            access_set.aggregate_signals(topic0, signal0, topic1, signal1, &vd0)?;

        // verify recursive proof
        let public_inputs: Vec<F> = access_set
            .0
            .cap
            .0
            .iter()
            .flat_map(|h| h.elements)
            .chain(nullifier0)
            .chain(topic0)
            .chain(access_set.0.cap.0.iter().flat_map(|h| h.elements))
            .chain(nullifier1)
            .chain(topic1)
            .collect();

        vd2.verify(ProofWithPublicInputs {
            proof: recursive_proof,
            public_inputs,
        })?;
        Ok(())
    }
}
