use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::HashOutTarget;
use plonky2::hash::merkle_proofs::MerkleProofTarget;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::access_set::AccessSet;
use crate::signal::{Digest, F};

pub struct SemaphoreTargets {
    merkle_root: HashOutTarget,
    topic: [Target; 4],
    merkle_proof: MerkleProofTarget,
    private_key: [Target; 4],
    public_key_index: Target,
}

impl AccessSet {
    pub fn tree_height(&self) -> usize {
        self.0.leaves.len().trailing_zeros() as usize
    }

    pub fn semaphore_circuit(&self, builder: &mut CircuitBuilder<F, 2>) -> SemaphoreTargets {
        // To create the circuit 'values', we call the `add_virtual_target` and it's variants (ie.
        // `add_virtual_target_arr`, or `add_virtual_hash` which internally calls it for the 4
        // field values that conform the hash.
        // The method `add_virtual_target` keeps an incremental index for each new virtual target
        // created, and returns a new `VirtualTarget`, used for intermediate values in witness
        // generation (which when needed can be copied to specific witness location (Wire)).
        //
        // The `register_public_input` and it's variants, append to the CircuitBuilder's
        // `public_inputs` vector the given Target (either VirtualTarget or Wire).
        //
        // Notice that when created, the targets are not given any value, and they will be set later
        // at the method `fill_semaphore_targets`.

        // Register public inputs.
        let merkle_root = builder.add_virtual_hash();
        builder.register_public_inputs(&merkle_root.elements);
        let nullifier = builder.add_virtual_hash();
        builder.register_public_inputs(&nullifier.elements);
        let topic: [Target; 4] = builder.add_virtual_targets(4).try_into().unwrap();
        builder.register_public_inputs(&topic);

        // Merkle proof
        let merkle_proof = MerkleProofTarget {
            siblings: builder.add_virtual_hashes(self.tree_height()),
        };

        // Verify public key Merkle proof.
        let private_key: [Target; 4] = builder.add_virtual_targets(4).try_into().unwrap();
        let public_key_index = builder.add_virtual_target();
        let public_key_index_bits = builder.split_le(public_key_index, self.tree_height());
        let zero = builder.zero();
        builder.verify_merkle_proof::<PoseidonHash>(
            [private_key, [zero; 4]].concat(),
            &public_key_index_bits,
            merkle_root,
            &merkle_proof,
        );

        // Check nullifier.
        let should_be_nullifier =
            builder.hash_n_to_hash_no_pad::<PoseidonHash>([private_key, topic].concat());
        for i in 0..4 {
            builder.connect(nullifier.elements[i], should_be_nullifier.elements[i]);
        }

        SemaphoreTargets {
            merkle_root,
            topic,
            merkle_proof,
            private_key,
            public_key_index,
        }
    }

    // Fill the semaphore targets that we defined at the method `semaphore_circuit` with the given
    // values.
    pub fn fill_semaphore_targets(
        &self,
        pw: &mut PartialWitness<F>,
        private_key: Digest,
        topic: Digest,
        public_key_index: usize,
        targets: SemaphoreTargets,
    ) -> Result<()> {
        let SemaphoreTargets {
            merkle_root,
            topic: topic_target,
            merkle_proof: merkle_proof_target,
            private_key: private_key_target,
            public_key_index: public_key_index_target,
        } = targets;

        pw.set_hash_target(merkle_root, self.0.cap.0[0])?;
        pw.set_target_arr(&private_key_target, &private_key)?;
        pw.set_target_arr(&topic_target, &topic)?;
        pw.set_target(
            public_key_index_target,
            F::from_canonical_usize(public_key_index),
        )?;

        let merkle_proof = self.0.prove(public_key_index);
        for (ht, h) in merkle_proof_target
            .siblings
            .into_iter()
            .zip(merkle_proof.siblings)
        {
            pw.set_hash_target(ht, h)?;
        }
        Ok(())
    }
}
