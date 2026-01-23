
use bitcoin::{Transaction, TxOut};
use bitcoin::consensus::encode::Encodable;
use bitcoin::hashes::{sha256, Hash, HashEngine};

pub const TXFS_VERSION: u8 = 1 << 0;
pub const TXFS_LOCKTIME: u8 = 1 << 1;
pub const TXFS_CURRENT_INPUT_IDX: u8 = 1 << 2;
pub const TXFS_CURRENT_INPUT_CONTROL_BLOCK: u8 = 1 << 3;
pub const TXFS_CURRENT_INPUT_LAST_CODESEPARATOR_POS: u8 = 1 << 4;
pub const TXFS_INPUTS: u8 = 1 << 5;
pub const TXFS_OUTPUTS: u8 = 1 << 6;

pub const TXFS_CONTROL: u8 = 1 << 7;

pub const TXFS_ALL: u8 = TXFS_VERSION
    | TXFS_LOCKTIME
    | TXFS_CURRENT_INPUT_IDX
    | TXFS_CURRENT_INPUT_CONTROL_BLOCK
    | TXFS_CURRENT_INPUT_LAST_CODESEPARATOR_POS
    | TXFS_INPUTS
    | TXFS_OUTPUTS
    | TXFS_CONTROL;

pub const TXFS_INPUTS_PREVOUTS: u8 = 1 << 0;
pub const TXFS_INPUTS_SEQUENCES: u8 = 1 << 1;
pub const TXFS_INPUTS_SCRIPTSIGS: u8 = 1 << 2;
pub const TXFS_INPUTS_PREV_SCRIPTPUBKEYS: u8 = 1 << 3;
pub const TXFS_INPUTS_PREV_VALUES: u8 = 1 << 4;
pub const TXFS_INPUTS_TAPROOT_ANNEXES: u8 = 1 << 5;
pub const TXFS_OUTPUTS_SCRIPTPUBKEYS: u8 = 1 << 6;
pub const TXFS_OUTPUTS_VALUES: u8 = 1 << 7;

pub const TXFS_INPUTS_ALL: u8 = TXFS_INPUTS_PREVOUTS
    | TXFS_INPUTS_SEQUENCES
    | TXFS_INPUTS_SCRIPTSIGS
    | TXFS_INPUTS_PREV_SCRIPTPUBKEYS
    | TXFS_INPUTS_PREV_VALUES
    | TXFS_INPUTS_TAPROOT_ANNEXES;
pub const TXFS_INPUTS_TEMPLATE: u8 = TXFS_INPUTS_SEQUENCES
    | TXFS_INPUTS_SCRIPTSIGS
    | TXFS_INPUTS_PREV_VALUES
    | TXFS_INPUTS_TAPROOT_ANNEXES;
pub const TXFS_OUTPUTS_ALL: u8 = TXFS_OUTPUTS_SCRIPTPUBKEYS | TXFS_OUTPUTS_VALUES;

pub const TXFS_INOUT_NUMBER: u8 = 1 << 7;
pub const TXFS_INOUT_SELECTION_NONE: u8 = 0x00;
pub const TXFS_INOUT_SELECTION_CURRENT: u8 = 0x40;
pub const TXFS_INOUT_SELECTION_ALL: u8 = 0x3f;
pub const TXFS_INOUT_SELECTION_MODE: u8 = 1 << 6;
pub const TXFS_INOUT_SELECTION_SIZE: u8 = 1 << 5;
pub const TXFS_INOUT_SELECTION_MASK: u8 = 
        0xff ^ TXFS_INOUT_NUMBER ^ TXFS_INOUT_SELECTION_MODE ^ TXFS_INOUT_SELECTION_SIZE;


pub const TXFS_SPECIAL_ALL: [u8; 4] = [
    TXFS_ALL,
    TXFS_INPUTS_ALL | TXFS_OUTPUTS_ALL,
    TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL,
    TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL,
];
pub const TXFS_SPECIAL_TEMPLATE: [u8; 4] = [
    TXFS_ALL,
    TXFS_INPUTS_TEMPLATE | TXFS_OUTPUTS_ALL,
    TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL,
    TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL,
];

const SHA256_EMPTY: sha256::Hash = sha256::Hash::const_hash(&[]);

/// Parse an input or output selection from the TxFieldSelector bytes.
///
/// Returns the selected indices and a flag whether to commit the number of items.
fn parse_inout_selection(
    bytes: &mut impl Iterator<Item = u8>,
    nb_items: usize,
    current_input_idx: u32,
) -> Result<(Vec<usize>, bool), &'static str> {
    let first = bytes.next().ok_or("in/output bit set but selection byte missing")?;
    let commit_number = (first & TXFS_INOUT_NUMBER) != 0;
    let selection = first & (0xff ^ TXFS_INOUT_NUMBER);

    let selected = if selection == TXFS_INOUT_SELECTION_NONE {
        if !commit_number {
            return Err("no in/output selection given and nb_items bitflag also unset");
        }
        vec![]
    } else if selection == TXFS_INOUT_SELECTION_ALL {
        (0..nb_items).collect()
    } else if selection == TXFS_INOUT_SELECTION_CURRENT {
        if current_input_idx as usize >= nb_items {
            // NB can only happen for outputs
            return Err("current input index exceeds number of outputs and current output selected");
        }
        vec![current_input_idx as usize]
    } else if (selection & TXFS_INOUT_SELECTION_MODE) == 0 { // leading mode
        let count = if (selection & TXFS_INOUT_SELECTION_SIZE) == 0 {
            (selection & TXFS_INOUT_SELECTION_MASK) as usize
        } else {
            if (selection & TXFS_INOUT_SELECTION_MASK) == 0 {
                return Err("non-minimal leading selection");
            }
            let next_byte = bytes.next().ok_or("second leading selection byte missing")?;
            (((selection & TXFS_INOUT_SELECTION_MASK) as usize) << 8) + next_byte as usize
        };
        assert_ne!(count, 0, "this should be interpreted as NONE above");
        if count > nb_items {
            return Err("selected number of leading in/outputs out of bounds");
        }
        (0..count).collect()
    } else { // individual mode
        let count = (selection & TXFS_INOUT_SELECTION_MASK) as usize;
        if count == 0 {
            return Err("can't select 0 in/outputs in individual mode");
        }

        let mut selected = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let idx = if (selection & TXFS_INOUT_SELECTION_SIZE) == 0 {
                bytes.next().ok_or("not enough single-byte indices")? as usize
            } else {
                let first = bytes.next().ok_or("first byte of two-byte index missing")?;
                let second = bytes.next().ok_or("second byte of two-byte index missing")?;
                (first as usize) << 8 + (second as usize)
            };
            if idx > nb_items {
                return Err("selected index out of bounds");
            }
            if let Some(last) = selected.last() {
                if idx <= *last {
                    return Err("selected indices not in increasing order")
                }
            }
            selected.push(idx);
        }
        selected
    };
    Ok((selected, commit_number))
}

/// 
///
/// Assumes that TxFieldSelector is valid.
pub fn calculate_txhash(
    txfs: &[u8],
    tx: &Transaction,
    prevouts: &[TxOut],
    current_input_idx: u32,
    current_input_last_codeseparator_pos: Option<u32>,
) -> Result<sha256::Hash, &'static str> {
    assert_eq!(tx.input.len(), prevouts.len());

    let txfs = if txfs.is_empty() {
        &TXFS_SPECIAL_TEMPLATE
    } else if txfs.len() == 1 && txfs[0] == 0x00 {
        &TXFS_SPECIAL_ALL
    } else {
        txfs
    };

    let mut engine = sha256::Hash::engine();

    if (txfs[0] & TXFS_CONTROL) != 0 {
        engine.input(txfs);
    }

    let mut bytes = txfs.iter().copied();
    let global = bytes.next().unwrap();
    if (global & TXFS_VERSION) != 0 {
        tx.version.consensus_encode(&mut engine).unwrap();
    }
    if (global & TXFS_LOCKTIME) != 0 {
        tx.lock_time.consensus_encode(&mut engine).unwrap();
    }
    if (global & TXFS_CURRENT_INPUT_IDX) != 0 {
        (current_input_idx as u32).consensus_encode(&mut engine).unwrap();
    }
    let cur = current_input_idx as usize;
    if (global & TXFS_CURRENT_INPUT_CONTROL_BLOCK) != 0 {
        let cb = if prevouts[cur].script_pubkey.is_p2tr() {
            tx.input[cur].witness.taproot_control_block().unwrap_or(&[])
        } else {
            &[]
        };
        engine.input(&sha256::Hash::hash(&cb)[..]);
    }
    if (global & TXFS_CURRENT_INPUT_LAST_CODESEPARATOR_POS) != 0 {
        let pos = current_input_last_codeseparator_pos.unwrap_or(u32::MAX);
        (pos as u32).consensus_encode(&mut engine).unwrap();
    }

    // Stop early if no inputs or outputs are selected.
    if (global & TXFS_INPUTS) == 0 && (global & TXFS_OUTPUTS) == 0 {
        if txfs.len() > 1 {
            return Err("input and output bit unset and more than one byte in txfs");
        }
        return Ok(sha256::Hash::from_engine(engine));
    }

    // Now that we know we have some inputs and/or some outputs to commit.
    let inout_fields = bytes.next().ok_or("in- or output bit set but only one byte")?;

    if (global & TXFS_INPUTS) == 0 {
        if (inout_fields & TXFS_INPUTS_ALL) != 0 {
            return Err("inputs bit not set but some input field bits set");
        }
    } else {
        let (selection, commit_number) = parse_inout_selection(
            &mut bytes, tx.input.len(), current_input_idx,
        )?;

        if (inout_fields & TXFS_INPUTS_ALL) == 0 && !selection.is_empty() {
            return Err("input selection given but no input field bits set");
        }

        if commit_number {
            (tx.input.len() as u32).consensus_encode(&mut engine).unwrap();
        }

        if !selection.is_empty() && (inout_fields & TXFS_INPUTS_PREVOUTS) != 0 {
            let hash = {
                let mut engine = sha256::Hash::engine();
                for i in &selection {
                    tx.input[*i].previous_output.consensus_encode(&mut engine).unwrap();
                }
                sha256::Hash::from_engine(engine)
            };
            engine.input(&hash[..]);
        }

        if !selection.is_empty() && (inout_fields & TXFS_INPUTS_SEQUENCES) != 0 {
            let hash = {
                let mut engine = sha256::Hash::engine();
                for i in &selection {
                    tx.input[*i].sequence.consensus_encode(&mut engine).unwrap();
                }
                sha256::Hash::from_engine(engine)
            };
            engine.input(&hash[..]);
        }

        if !selection.is_empty() && (inout_fields & TXFS_INPUTS_SCRIPTSIGS) != 0 {
            let hash = {
                let mut engine = sha256::Hash::engine();
                for i in &selection {
                    engine.input(&sha256::Hash::hash(&tx.input[*i].script_sig.as_bytes())[..]);
                }
                sha256::Hash::from_engine(engine)
            };
            engine.input(&hash[..]);
        }

        if !selection.is_empty() && (inout_fields & TXFS_INPUTS_PREV_SCRIPTPUBKEYS) != 0 {
            let hash = {
                let mut engine = sha256::Hash::engine();
                for i in &selection {
                    engine.input(&sha256::Hash::hash(&prevouts[*i].script_pubkey.as_bytes())[..]);
                }
                sha256::Hash::from_engine(engine)
            };
            engine.input(&hash[..]);
        }

        if !selection.is_empty() && (inout_fields & TXFS_INPUTS_PREV_VALUES) != 0 {
            let hash = {
                let mut engine = sha256::Hash::engine();
                for i in &selection {
                    prevouts[*i].value.consensus_encode(&mut engine).unwrap();
                }
                sha256::Hash::from_engine(engine)
            };
            engine.input(&hash[..]);
        }

        if !selection.is_empty() && (inout_fields & TXFS_INPUTS_TAPROOT_ANNEXES) != 0 {
            let hash = {
                let mut engine = sha256::Hash::engine();
                for i in &selection {
                    if prevouts[*i].script_pubkey.is_p2tr() {
                        if let Some(annex) = tx.input[*i].witness.taproot_annex() {
                            engine.input(&sha256::Hash::hash(annex)[..]);
                        } else {
                            engine.input(&SHA256_EMPTY[..]);
                        }
                    } else {
                        engine.input(&SHA256_EMPTY[..]);
                    }
                }
                sha256::Hash::from_engine(engine)
            };
            engine.input(&hash[..]);
        }
    }

    if (global & TXFS_OUTPUTS) == 0 {
        if (inout_fields & TXFS_OUTPUTS_ALL) != 0 {
            return Err("outputs bit not set but some output field bits set");
        }
    } else {
        let (selection, commit_number) = parse_inout_selection(
            &mut bytes, tx.output.len(), current_input_idx,
        )?;

        if (inout_fields & TXFS_OUTPUTS_ALL) == 0 && !selection.is_empty() {
            return Err("output selection given but no output field bits set");
        }

        if commit_number {
            (tx.output.len() as u32).consensus_encode(&mut engine).unwrap();
        }

        if !selection.is_empty() && (inout_fields & TXFS_OUTPUTS_SCRIPTPUBKEYS) != 0 {
            let hash = {
                let mut engine = sha256::Hash::engine();
                for i in &selection {
                    engine.input(&sha256::Hash::hash(&tx.output[*i].script_pubkey.as_bytes())[..]);
                }
                sha256::Hash::from_engine(engine)
            };
            hash.consensus_encode(&mut engine).unwrap();
        }

        if !selection.is_empty() && (inout_fields & TXFS_OUTPUTS_VALUES) != 0 {
            let hash = {
                let mut engine = sha256::Hash::engine();
                for i in &selection {
                    tx.output[*i].value.consensus_encode(&mut engine).unwrap();
                }
                sha256::Hash::from_engine(engine)
            };
            hash.consensus_encode(&mut engine).unwrap();
        }
    }

    Ok(sha256::Hash::from_engine(engine))
}

mod test_vectors {
    use super::*;
    use bitcoin::hex::DisplayHex;
    use bitcoin::{Amount, ScriptBuf, Sequence, Witness};
    use bitcoin::blockdata::transaction::{self, TxIn};
    use bitcoin::opcodes::all::*;

    fn test_vector_tx() -> (Transaction, Vec<TxOut>) {
        let tx = Transaction {
            version: transaction::Version::TWO,
            lock_time: bitcoin::absolute::LockTime::from_consensus(42),
            input: vec![
                TxIn {
                    previous_output: "1111111111111111111111111111111111111111111111111111111111111111:1".parse().unwrap(),
                    script_sig: vec![0x23].into(),
                    sequence: Sequence::from_consensus(1),
                    witness: Witness::new(),
                },
                TxIn {
                    previous_output: "2222222222222222222222222222222222222222222222222222222222222222:2".parse().unwrap(),
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::from_consensus(3),
                    witness: { // p2wsh annex-like stack element
                        let mut buf = Witness::new();
                        buf.push(vec![0x13]);
                        buf.push(vec![0x14]);
                        buf.push(vec![0x50, 0x42]); // annex
                        buf
                    },
                },
                TxIn {
                    previous_output: "3333333333333333333333333333333333333333333333333333333333333333:3".parse().unwrap(),
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::from_consensus(2),
                    witness: {
                        let mut buf = Witness::new();
                        buf.push(vec![0x12]);
                        buf
                    },
                },
                TxIn {
                    previous_output: "4444444444444444444444444444444444444444444444444444444444444444:4".parse().unwrap(),
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::from_consensus(3),
                    witness: {
                        let mut buf = Witness::new();
                        buf.push(vec![0x13]);
                        buf.push(vec![0x14]);
                        buf.push(vec![0x50, 0x42]); // annex
                        buf
                    },
                },
            ],
            output: vec![
                TxOut {
                    script_pubkey: vec![OP_PUSHNUM_6.to_u8()].into(),
                    value: Amount::from_sat(350),
                },
                TxOut {
                    script_pubkey: vec![OP_PUSHNUM_7.to_u8()].into(),
                    value: Amount::from_sat(351),
                },
                TxOut {
                    script_pubkey: vec![OP_PUSHNUM_8.to_u8()].into(),
                    value: Amount::from_sat(353),
                },
            ],
        };
        let prevs = vec![
            TxOut {
                script_pubkey: vec![OP_PUSHNUM_16.to_u8()].into(),
                value: Amount::from_sat(360),
            },
            TxOut {
                script_pubkey: vec![ // p2wsh
                    0x00, 0x20, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                ].into(),
                value: Amount::from_sat(361),
            },
            TxOut {
                script_pubkey: vec![ // p2tr
                    0x51, 0x20, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                ].into(),
                value: Amount::from_sat(361),
            },
            TxOut {
                script_pubkey: vec![ // p2tr
                    0x51, 0x20, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                ].into(),
                value: Amount::from_sat(362),
            },
        ];
        (tx, prevs)
    }

    #[derive(Debug)]
    struct TestCase {
        tx: Transaction,
        prevs: Vec<TxOut>,
        vectors: Vec<TestVector>
    }

    #[derive(Debug)]
    struct TestVector {
        txfs: Vec<u8>,
        input: usize,
        codeseparator: Option<u32>,
        txhash: sha256::Hash,
    }

    fn generate_vectors() -> Vec<TestCase> {
        let selectors: &[&[u8]] = &[
            // global
            &[1 << 0],
            &[1 << 1],
            &[1 << 2],
            &[1 << 3],
            &[1 << 4],
            &[0x9f],
            // outputs
            &[0xdf, TXFS_OUTPUTS_SCRIPTPUBKEYS, TXFS_INOUT_SELECTION_CURRENT],
            &[0xdf, TXFS_OUTPUTS_VALUES,         TXFS_INOUT_SELECTION_CURRENT],
            &[0xdf, TXFS_OUTPUTS_ALL,            TXFS_INOUT_SELECTION_CURRENT],
            &[0xdf, TXFS_OUTPUTS_SCRIPTPUBKEYS, TXFS_INOUT_SELECTION_ALL],
            &[0xdf, TXFS_OUTPUTS_VALUES,         TXFS_INOUT_SELECTION_ALL],
            &[0xdf, TXFS_OUTPUTS_ALL,            TXFS_INOUT_SELECTION_ALL],
            &[0xdf, TXFS_OUTPUTS_SCRIPTPUBKEYS, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xdf, TXFS_OUTPUTS_VALUES,         TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xdf, TXFS_OUTPUTS_ALL,            TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xdf, TXFS_OUTPUTS_SCRIPTPUBKEYS, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xdf, TXFS_OUTPUTS_VALUES,         TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xdf, TXFS_OUTPUTS_ALL,            TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xdf, TXFS_OUTPUTS_SCRIPTPUBKEYS, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            &[0xdf, TXFS_OUTPUTS_VALUES,         TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            &[0xdf, TXFS_OUTPUTS_ALL,            TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            // inputs
            &[0xbf, TXFS_INPUTS_PREVOUTS,           TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_SEQUENCES,          TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_SCRIPTSIGS,         TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_PREV_SCRIPTPUBKEYS, TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_PREV_VALUES,        TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_TAPROOT_ANNEXES,    TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_ALL,                TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_PREVOUTS,           TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_SEQUENCES,          TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_SCRIPTSIGS,         TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_PREV_SCRIPTPUBKEYS, TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_PREV_VALUES,        TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_TAPROOT_ANNEXES,    TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_ALL,                TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_PREVOUTS,           TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xbf, TXFS_INPUTS_SEQUENCES,          TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xbf, TXFS_INPUTS_SCRIPTSIGS,         TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xbf, TXFS_INPUTS_PREV_SCRIPTPUBKEYS, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xbf, TXFS_INPUTS_PREV_VALUES,        TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xbf, TXFS_INPUTS_TAPROOT_ANNEXES,    TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xbf, TXFS_INPUTS_ALL,                TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xbf, TXFS_INPUTS_PREVOUTS,           TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_SEQUENCES,          TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_SCRIPTSIGS,         TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_PREV_SCRIPTPUBKEYS, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_PREV_VALUES,        TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_TAPROOT_ANNEXES,    TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_ALL,                TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xbf, TXFS_INPUTS_PREVOUTS,           TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_SEQUENCES,          TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_SCRIPTSIGS,         TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_PREV_SCRIPTPUBKEYS, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_PREV_VALUES,        TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_TAPROOT_ANNEXES,    TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            &[0xbf, TXFS_INPUTS_ALL,                TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            // both
            &[0xff, 0xff, TXFS_INOUT_SELECTION_ALL,     TXFS_INOUT_SELECTION_ALL],
            &[0xff, 0xff, TXFS_INOUT_SELECTION_CURRENT, TXFS_INOUT_SELECTION_CURRENT],
            &[0xff, 0xff, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE,
                          TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_NONE],
            &[0xff, 0xff, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL,
                          TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_ALL],
            &[0xff, 0xff, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT,
                          TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_CURRENT],
            &[0xff, 0xff, TXFS_INOUT_SELECTION_CURRENT, TXFS_INOUT_SELECTION_ALL],
            &[0xff, 0xff, TXFS_INOUT_SELECTION_ALL,     TXFS_INOUT_SELECTION_CURRENT],
            // leading
            &[0xff, 0xff, 0x01, 0x02],
            // individual
            &[0xff, 0xff, TXFS_INOUT_SELECTION_MODE | 0x01, 0x01,
                          TXFS_INOUT_SELECTION_MODE | 0x02, 0x00, 0x02],
            &[0xff, 0xff, TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_MODE | 0x01, 0x01,
                          TXFS_INOUT_NUMBER | TXFS_INOUT_SELECTION_MODE | 0x02, 0x00, 0x02],
            //TODO(stevenroose) test index size, but for that we need > 32 in/outputs
            // special cases
            &[],
            &[0x00],
        ];

        let cases = vec![
            test_vector_tx(),
        ];

        let out_selector = |txfs: &[u8]| {
            if txfs == &[0x00] || txfs.get(0)? & TXFS_OUTPUTS == 0 {
                None
            } else if txfs.get(0)? & TXFS_INPUTS == 0 {
                Some(txfs[2])
            } else {
                Some(txfs[3])
            }
        };

        cases.into_iter().map(|(tx, prevs)| {
            let mut vectors = Vec::new();
            for txfs in selectors {
                for i in 0..tx.input.len() {
                    if i >= tx.output.len() {
                        if let Some(outs) = out_selector(txfs) {
                            if (outs & (0xff ^ TXFS_INOUT_NUMBER)) == TXFS_INOUT_SELECTION_CURRENT {
                                continue;
                            }
                        }
                    }

                    vectors.push(TestVector {
                        txfs: txfs.to_vec(),
                        input: i,
                        codeseparator: None,
                        txhash: calculate_txhash(txfs, &tx, &prevs, i as u32, None).unwrap(),
                    });
                }
            }
            TestCase { tx, prevs, vectors }
        }).collect()
    }

    pub fn write_vector_file(path: impl AsRef<std::path::Path>) {
        use bitcoin::consensus::encode::serialize_hex;

        let ret = generate_vectors().into_iter().map(|c| serde_json::json!({
            "tx": serialize_hex(&c.tx),
            "prevs": c.prevs.iter().map(|p| serialize_hex(p)).collect::<Vec<_>>(),
            "vectors": c.vectors.into_iter().map(|v| serde_json::json!({
                "txfs": v.txfs.as_hex().to_string(),
                "input": v.input,
                "codeseparator": v.codeseparator,
                "txhash": v.txhash,
            })).collect::<Vec<_>>(),
        })).collect::<Vec<_>>();

        let mut file = std::fs::File::create(path).unwrap();
        serde_json::to_writer_pretty(&mut file, &ret).unwrap();
    }
}

fn main() {
    test_vectors::write_vector_file("./txhash_vectors.json");
}
