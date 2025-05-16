use std::collections::{BTreeMap, BTreeSet};

use borsh::{BorshDeserialize, BorshSerialize};
use borsh_derive::{BorshDeserialize, BorshSerialize};
use trie::{
    get_child_node_fragment_and_hash_from_db, get_node_from_db, Nibble, NibblePatriciaTrieDb,
    NibblePatriciaTrieError, NibblePatriciaTrieMemoryDb, NibblePatriciaTrieNode,
    NibblePatriciaTrieNodeBranch, NibblePatriciaTrieNodeLeaf, NibblePatriciaTrieRootPath,
};

mod trie;

pub use sha2;

#[derive(Clone, Debug, BorshSerialize, BorshDeserialize)]
pub struct Setup {
    pub path: NibblePatriciaTrieRootPath,
    pub leaf_values_for_inclusion_proof: BTreeMap<Vec<Nibble>, Vec<u8>>,
}

fn setup_trie_and_db() -> (
    BTreeMap<Vec<Nibble>, Vec<u8>>,
    NibblePatriciaTrieMemoryDb,
    NibblePatriciaTrieMemoryDb,
    NibblePatriciaTrieNode,
) {
    // Prepare simple key-value pairs
    let mut entries = BTreeMap::new();
    entries.insert(vec![Nibble::from(1), Nibble::from(2)], b"a".to_vec());
    entries.insert(vec![Nibble::from(1), Nibble::from(3)], b"b".to_vec());
    entries.insert(vec![Nibble::from(2), Nibble::from(2)], b"c".to_vec());

    // Manually construct nodes
    // leaf [1,2]
    let leaf_12 = NibblePatriciaTrieNodeLeaf::new(vec![Nibble::from(2)], b"a".to_vec());
    let leaf_13 = NibblePatriciaTrieNodeLeaf::new(vec![Nibble::from(3)], b"b".to_vec());
    let leaf_22 =
        NibblePatriciaTrieNodeLeaf::new(vec![Nibble::from(2), Nibble::from(2)], b"c".to_vec());

    // branch [1]
    let mut branch_1_children = BTreeSet::new();
    branch_1_children.insert(Nibble::from(2));
    branch_1_children.insert(Nibble::from(3));
    let branch_1 = NibblePatriciaTrieNodeBranch::new(vec![Nibble::from(1)], branch_1_children);

    // root
    let mut root_children = BTreeSet::new();
    root_children.insert(Nibble::from(1)); // [1] branch
    root_children.insert(Nibble::from(2)); // [2,2] leaf
    let root = NibblePatriciaTrieNodeBranch::new(vec![], root_children);

    // Prepare node_db and hash_db
    let mut node_db = NibblePatriciaTrieMemoryDb::new();
    let mut hash_db = NibblePatriciaTrieMemoryDb::new();

    // Serialize and store nodes
    let mut buf = Vec::new();
    // leaf [1,2]
    buf.clear();
    hash_db.set(&[Nibble::from(1), Nibble::from(2)], &leaf_12.hash()[..]);
    NibblePatriciaTrieNode::Leaf(leaf_12)
        .serialize(&mut buf)
        .unwrap();
    node_db.set(&[Nibble::from(1), Nibble::from(2)], &buf);
    // leaf [1,3]
    buf.clear();
    hash_db.set(&[Nibble::from(1), Nibble::from(3)], &leaf_13.hash()[..]);
    NibblePatriciaTrieNode::Leaf(leaf_13)
        .serialize(&mut buf)
        .unwrap();
    node_db.set(&[Nibble::from(1), Nibble::from(3)], &buf);
    // leaf [2,2]
    buf.clear();
    hash_db.set(&[Nibble::from(2), Nibble::from(2)], &leaf_22.hash()[..]);
    NibblePatriciaTrieNode::Leaf(leaf_22)
        .serialize(&mut buf)
        .unwrap();
    node_db.set(&[Nibble::from(2), Nibble::from(2)], &buf);
    // branch [1]
    buf.clear();
    // branch [1] hash
    let branch_1_hash = branch_1
        .hash(|nib| {
            let child_key = match nib.as_u8() {
                2 => vec![Nibble::from(1), Nibble::from(2)],
                3 => vec![Nibble::from(1), Nibble::from(3)],
                _ => return None,
            };
            Some(<[u8; 32]>::try_from(hash_db.get(&child_key).unwrap().as_slice()).unwrap())
        })
        .unwrap();
    hash_db.set(&[Nibble::from(1)], &branch_1_hash[..]);
    NibblePatriciaTrieNode::Branch(branch_1)
        .serialize(&mut buf)
        .unwrap();
    node_db.set(&[Nibble::from(1)], &buf);
    // root
    buf.clear();
    // root hash
    let root_hash = root
        .hash(|nib| {
            let child_key = match nib.as_u8() {
                1 => vec![Nibble::from(1)],
                2 => vec![Nibble::from(2), Nibble::from(2)],
                _ => return None,
            };
            Some(<[u8; 32]>::try_from(hash_db.get(&child_key).unwrap().as_slice()).unwrap())
        })
        .unwrap();
    hash_db.set(&[], &root_hash[..]);
    let root_node = NibblePatriciaTrieNode::Branch(root);
    root_node.serialize(&mut buf).unwrap();
    node_db.set(&[], &buf);

    (entries, node_db, hash_db, root_node)
}

pub fn setup_bench() -> Vec<u8> {
    let (entries, node_db, hash_db, _root_node) = setup_trie_and_db();

    let get_node = |key: &[Nibble]| get_node_from_db(key, &node_db);
    let get_child_node_fragment_and_hash = |key: &[Nibble], index: Nibble| {
        get_child_node_fragment_and_hash_from_db(key, index, &hash_db)
    };

    let leaf_key = vec![Nibble::from(1), Nibble::from(2)];
    let leaf_keys = BTreeSet::from([leaf_key.clone()]);
    let proof = NibblePatriciaTrieRootPath::from_leafs(
        leaf_keys,
        get_node,
        get_child_node_fragment_and_hash,
    )
    .unwrap();

    let setup = Setup {
        path: proof,
        leaf_values_for_inclusion_proof: entries,
    };

    let mut buf = Vec::new();
    setup.serialize(&mut buf).unwrap();
    buf
}

fn load_setup(input: &[u8]) -> Setup {
    let setup: Setup = Setup::try_from_slice(input).unwrap();
    setup
}

pub fn bench(input: &[u8]) {
    let setup = load_setup(input);

    let leaves = setup
        .leaf_values_for_inclusion_proof
        .into_iter()
        .map(|(key, value)| {
            let leaf = setup.path.node_for_inclusion_proof(&key, value)?;
            Ok((key, leaf))
        })
        .collect::<Result<_, NibblePatriciaTrieError>>()
        .unwrap();
    let root = setup.path.root(leaves, None);
}
