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

fn setup_trie_and_db_large() -> (
    BTreeMap<Vec<Nibble>, Vec<u8>>,
    NibblePatriciaTrieMemoryDb,
    NibblePatriciaTrieMemoryDb,
    NibblePatriciaTrieNode,
) {
    // Prepare key-value pairs with 1000 elements
    let mut entries = BTreeMap::new();
    for i in 0..1000 {
        let key = vec![
            Nibble::from((i / 100) as u8),
            Nibble::from(((i % 100) / 10) as u8),
            Nibble::from((i % 10) as u8),
        ];
        let value = format!("value_{}", i).into_bytes();
        entries.insert(key, value);
    }

    // Prepare node_db and hash_db
    let mut node_db = NibblePatriciaTrieMemoryDb::new();
    let mut hash_db = NibblePatriciaTrieMemoryDb::new();
    let mut buf = Vec::new();

    // Create and store all leaf nodes
    for (key, value) in entries.iter() {
        // All leaf nodes have a parent branch node at level 2, so use only the last nibble
        let key_fragment = vec![key[2]];
        let leaf = NibblePatriciaTrieNodeLeaf::new(key_fragment, value.clone());
        buf.clear();
        hash_db.set(key, &leaf.hash()[..]);
        NibblePatriciaTrieNode::Leaf(leaf)
            .serialize(&mut buf)
            .unwrap();
        node_db.set(key, &buf);
    }

    // Create branch nodes for each level
    // Level 2 (last level before leaves)
    for i in 0..10 {
        for j in 0..10 {
            let mut children = BTreeSet::new();
            for k in 0..10 {
                children.insert(Nibble::from(k as u8));
            }
            // For level 2 branch nodes, key_fragment is the second nibble
            let branch = NibblePatriciaTrieNodeBranch::new(vec![Nibble::from(j as u8)], children);
            buf.clear();
            let branch_hash = branch
                .hash(|nib| {
                    let child_key = vec![Nibble::from(i as u8), Nibble::from(j as u8), *nib];
                    Some(<[u8; 32]>::try_from(hash_db.get(&child_key).unwrap().as_slice()).unwrap())
                })
                .unwrap();
            let branch_key = vec![Nibble::from(i as u8), Nibble::from(j as u8)];
            hash_db.set(&branch_key, &branch_hash[..]);
            NibblePatriciaTrieNode::Branch(branch)
                .serialize(&mut buf)
                .unwrap();
            node_db.set(&branch_key, &buf);
        }
    }

    // Level 1
    for i in 0..10 {
        let mut children = BTreeSet::new();
        for j in 0..10 {
            children.insert(Nibble::from(j as u8));
        }
        // For level 1 branch nodes, key_fragment is the first nibble
        let branch = NibblePatriciaTrieNodeBranch::new(vec![Nibble::from(i as u8)], children);
        buf.clear();
        let branch_hash = branch
            .hash(|nib| {
                let child_key = vec![Nibble::from(i as u8), *nib];
                Some(<[u8; 32]>::try_from(hash_db.get(&child_key).unwrap().as_slice()).unwrap())
            })
            .unwrap();
        let branch_key = vec![Nibble::from(i as u8)];
        hash_db.set(&branch_key, &branch_hash[..]);
        NibblePatriciaTrieNode::Branch(branch)
            .serialize(&mut buf)
            .unwrap();
        node_db.set(&branch_key, &buf);
    }

    // Root level
    let mut root_children = BTreeSet::new();
    for i in 0..10 {
        root_children.insert(Nibble::from(i as u8));
    }
    // Root node has empty key_fragment
    let root = NibblePatriciaTrieNodeBranch::new(vec![], root_children);
    buf.clear();
    let root_hash = root
        .hash(|nib| {
            let child_key = vec![*nib];
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
    let (entries, node_db, hash_db, _root_node) = setup_trie_and_db_large();

    let get_node = |key: &[Nibble]| get_node_from_db(key, &node_db);
    let get_child_node_fragment_and_hash = |key: &[Nibble], index: Nibble| {
        get_child_node_fragment_and_hash_from_db(key, index, &hash_db)
    };

    let leaf_key1 = vec![Nibble::from(1), Nibble::from(2), Nibble::from(3)];
    let leaf_key2 = vec![Nibble::from(2), Nibble::from(3), Nibble::from(4)];
    let leaf_key3 = vec![Nibble::from(3), Nibble::from(4), Nibble::from(5)];
    let leaf_key4 = vec![Nibble::from(1), Nibble::from(2), Nibble::from(4)];
    let leaf_key5 = vec![Nibble::from(2), Nibble::from(3), Nibble::from(5)];
    let leaf_key6 = vec![Nibble::from(3), Nibble::from(4), Nibble::from(6)];
    let leaf_key7 = vec![Nibble::from(3), Nibble::from(4), Nibble::from(7)];
    let leaf_key8 = vec![Nibble::from(3), Nibble::from(4), Nibble::from(8)];
    let leaf_key9 = vec![Nibble::from(3), Nibble::from(4), Nibble::from(9)];
    let leaf_keys = BTreeSet::from([
        leaf_key1, leaf_key2, leaf_key3, leaf_key4, leaf_key5, leaf_key6, leaf_key7, leaf_key8,
        leaf_key9,
    ]);
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
