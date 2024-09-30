/// Experimental IVC (Incremental Verifiable Computation) using Plonky2
///
///        w_1     w_2     w_3     w_4     
///        │       │       │       │      
///        ▼       ▼       ▼       ▼      
///       ┌─┐     ┌─┐     ┌─┐     ┌─┐     
/// ─────►│F├────►│F├────►│F├────►│F├────►
///  z_1  └─┘ z_2 └─┘ z_3 └─┘ z_4 └─┘ z_5
///
///
/// where each F is:
///    w_i                                        
///     │     ┌───────────────────────────────┐              
///     │     │                               │              
///     │     │ verify previous plonky2 proof │              
///     └────►│              +                │              
///  ────────►│ verify current semaphore proof├───────►      
///   z_i     │                               │  z_{i+1}
///           │                               │              
///           └───────────────────────────────┘
///
/// where each w_i value are the values of the new instance being verified at the step i.
///
/// The last state z_i is used together with the external input w_i as inputs to compute the new
/// state z_{i+1}.
///
/// To run the test that checks this logic:
/// cargo test --release test_ivc -- --nocapture
///
use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, VerifierCircuitData};
use plonky2::plonk::config::Hasher;
use plonky2::plonk::proof::ProofWithPublicInputs;
use std::time::Instant;

use crate::access_set::AccessSet;
use crate::signal::{Digest, PlonkyProof, C, F};

#[derive(Debug, Clone)]
pub struct IVC {
    // current step of the recursion
    i: u64,
    // previous IVC proof values
    prev_nullifiers: Vec<Digest>,
    prev_topics: Vec<Digest>,
    // previous IVC proof
    prev_ivc_proof: Option<PlonkyProof>,
    // verifier data for the prev_ivc_proof
    verifier_data: Option<VerifierCircuitData<F, C, 2>>,
}

impl IVC {
    pub fn new() -> Self {
        Self {
            i: 0_u64,
            prev_nullifiers: vec![],
            prev_topics: vec![],
            prev_ivc_proof: None,
            verifier_data: None,
        }
    }

    // `public_inputs` returns
    // [
    //  0, merkle_root, nullifier[0], topic[0],
    //  1, merkle_root, nullifier[1], topic[1],
    //  2, merkle_root, nullifier[2], topic[2],
    //  ...
    // ].rev()
    pub fn public_inputs(&self, merkle_root: Vec<F>) -> Vec<F> {
        self.prev_nullifiers
            .iter()
            .enumerate()
            .rev()
            .zip(self.prev_topics.iter().rev())
            .flat_map(|((i, n), t)| {
                vec![
                    vec![F::from_canonical_u64((i + 1) as u64)],
                    merkle_root.clone(),
                    n.to_vec(),
                    t.to_vec(),
                ]
                .concat()
            })
            .collect()
    }

    pub fn prove_step(
        &mut self,
        // merkle proof membership values
        access_set: &AccessSet,
        private_key: Digest,
        public_key_index: usize,
        topic: Digest,
    ) -> Result<()> {
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::new(config);
        let mut pw = PartialWitness::new();

        // ivc_i, as public input
        let i1_F = F::from_canonical_u64(self.i + 1); // next i
        let i_target: Target = builder.add_virtual_target();
        builder.register_public_input(i_target);
        pw.set_target(i_target, i1_F)?;

        let nullifier = PoseidonHash::hash_no_pad(&[private_key, topic].concat()).elements;
        // semaphore gadget. Notice that internally it registers public inputs:
        // merkle_root, nullifier, topic
        let semaphore_targets = access_set.semaphore_circuit(&mut builder);
        access_set.fill_semaphore_targets(
            &mut pw,
            private_key,
            topic,
            public_key_index,
            semaphore_targets,
        )?;

        // verify the previous IVC proof in-circuit when we're not at the first iteration
        if self.i != 0 {
            let verifier_data = self.verifier_data.clone().unwrap();

            let merkle_root: Vec<F> = access_set.0.cap.0.iter().flat_map(|h| h.elements).collect();
            let public_inputs = self.public_inputs(merkle_root);

            // verify the proof natively in rust before doing the in-circuit verification
            #[cfg(test)]
            verifier_data.clone().verify(ProofWithPublicInputs {
                proof: self.prev_ivc_proof.clone().unwrap(),
                public_inputs: public_inputs.clone(),
            })?;

            // ivc proof verification gadget
            let proof_target = builder.add_virtual_proof_with_pis(&verifier_data.common);
            builder.register_public_inputs(&proof_target.public_inputs);
            pw.set_proof_with_pis_target(
                &proof_target,
                &ProofWithPublicInputs {
                    proof: self.prev_ivc_proof.clone().unwrap(),
                    public_inputs,
                },
            )?;
            let vd_target = builder
                .add_virtual_verifier_data(verifier_data.common.config.fri_config.cap_height);
            pw.set_verifier_data_target(&vd_target, &verifier_data.verifier_only)?;

            pw.set_cap_target(
                &vd_target.constants_sigmas_cap,
                &verifier_data.verifier_only.constants_sigmas_cap,
            )?;

            builder.verify_proof::<C>(&proof_target, &vd_target, &verifier_data.common);
            dbg!("in-circuit prev_ivc_proof verification added");
        }

        dbg!(builder.num_public_inputs());

        // Build the actual proof, notice that:
        // - if i==0: prove only the semaphore data
        // - if i>0: prove the semaphore data + the verification of the previous IVC proof
        let start = Instant::now();
        let data = builder.build::<C>();
        println!("builder.build(): {:?}", start.elapsed());
        let start = Instant::now();
        let new_ivc_proof = data.prove(pw)?;
        println!("generate new_ivc_proof: {:?}", start.elapsed());

        let start = Instant::now();
        data.verify(new_ivc_proof.clone())?;
        println!("verify new_ivc_proof: {:?}", start.elapsed());

        #[cfg(test)]
        data.verifier_data().verify(ProofWithPublicInputs {
            proof: new_ivc_proof.proof.clone(),
            public_inputs: new_ivc_proof.public_inputs.clone(),
        })?;

        self.prev_nullifiers.push(nullifier);
        self.prev_topics.push(topic);
        self.prev_ivc_proof = Some(new_ivc_proof.proof);
        // store the verifier data of the generated plonky2 proof, which will be used for the
        // last proof verification
        self.verifier_data = Some(data.verifier_data());

        #[cfg(test)]
        if self.i > 0 {
            let merkle_root: Vec<F> = access_set.0.cap.0.iter().flat_map(|h| h.elements).collect();
            let public_inputs = self.public_inputs(merkle_root);
            data.verifier_data().verify(ProofWithPublicInputs {
                proof: self.prev_ivc_proof.clone().unwrap(),
                public_inputs: public_inputs.clone(),
            })?;
        }

        self.i += 1;

        Ok(())
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
    use std::time::Instant;

    use crate::access_set::AccessSet;
    use crate::ivc::IVC;
    use crate::signal::{Digest, F};

    /// to run:
    /// cargo test --release test_ivc -- --nocapture
    #[test]
    fn test_ivc() -> Result<()> {
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
        let merkle_root: Vec<F> = access_set.0.cap.0.iter().flat_map(|h| h.elements).collect();
        let topic0 = F::rand_array();

        let mut ivc = IVC::new();
        dbg!(&ivc.i);
        dbg!(&ivc);

        // 1st recursive step
        println!("\n----- ivc.prove_step i=0");
        let key_index = 42;
        ivc.prove_step(&access_set, private_keys[key_index], key_index, topic0)?;
        // verify the proof at i=0 (now ivc.i=1, but the proof is for ivc.i=0)
        let i_F = F::from_canonical_u64(ivc.i);
        dbg!(&i_F);
        let public_inputs: Vec<F> = vec![i_F]
            .into_iter()
            .chain(access_set.0.cap.0.iter().flat_map(|h| h.elements)) // merkle_root
            .chain(ivc.prev_nullifiers[0])
            .chain(ivc.prev_topics[0])
            .collect();
        dbg!(&public_inputs);
        ivc.verifier_data
            .clone()
            .unwrap()
            .verify(ProofWithPublicInputs {
                proof: ivc.prev_ivc_proof.clone().unwrap(),
                public_inputs,
            })?;

        // 2nd recursive step
        println!("\n----- ivc.prove_step i=1");
        let key_index = 24;
        ivc.prove_step(&access_set, private_keys[key_index], key_index, topic0)?;
        dbg!(&ivc.i);
        let prev_i_F = F::from_canonical_u64(ivc.i - 1);
        let i_F = F::from_canonical_u64(ivc.i);
        // notice, here public_inputs will contain
        // - the current step values that are verified in the current circuit
        // - the previous step values in order to verify the previous plonky2 proof in-circuit
        let public_inputs: Vec<F> = vec![i_F]
            .into_iter()
            .chain(access_set.0.cap.0.iter().flat_map(|h| h.elements)) // merkle_root
            .chain(ivc.prev_nullifiers[1])
            .chain(ivc.prev_topics[1])
            .chain(vec![prev_i_F])
            .chain(access_set.0.cap.0.iter().flat_map(|h| h.elements)) // merkle_root
            .chain(ivc.prev_nullifiers[0])
            .chain(ivc.prev_topics[0])
            .collect();
        dbg!(&public_inputs);
        ivc.verifier_data
            .clone()
            .unwrap()
            .verify(ProofWithPublicInputs {
                proof: ivc.prev_ivc_proof.clone().unwrap(),
                public_inputs,
            })?;

        // 3rd step
        println!("\n----- ivc.prove_step i=2");
        let key_index = 25;
        ivc.prove_step(&access_set, private_keys[key_index], key_index, topic0)?;
        dbg!(&ivc.i);
        let public_inputs = ivc.public_inputs(merkle_root.clone());
        dbg!(&public_inputs);
        ivc.verifier_data
            .clone()
            .unwrap()
            .verify(ProofWithPublicInputs {
                proof: ivc.prev_ivc_proof.clone().unwrap(),
                public_inputs,
            })?;

        for i in 0..10 {
            println!("\n----- ivc.prove_step i={}", 3 + i);
            let key_index = i;
            let start = Instant::now();
            ivc.prove_step(&access_set, private_keys[key_index], key_index, topic0)?;
            println!("prove_step (i={}) took: {:?}", 3 + i, start.elapsed());
            let public_inputs = ivc.public_inputs(merkle_root.clone());
            dbg!(&public_inputs);
            ivc.verifier_data
                .clone()
                .unwrap()
                .verify(ProofWithPublicInputs {
                    proof: ivc.prev_ivc_proof.clone().unwrap(),
                    public_inputs,
                })?;
            // TODO: print (bytes length) proof size, verifier_data size, public inputs size
        }

        Ok(())
    }
}
