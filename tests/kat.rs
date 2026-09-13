//! NIST CAVP SHAKE known-answer tests, byte-oriented
//! (`shakebytetestvectors.zip`, CAVS 19.0, generated 2016-01-28), transcribed
//! unchanged into `tests/vectors/`. `ShortMsg` covers every input length from
//! 0 to a few blocks, `VariableOut` every output length from the minimum to
//! the maximum in the file's header, and `Monte` chains 100 × 1000
//! variable-length squeezes (the SHAKE Monte Carlo Test of the SHA-3
//! validation system). `LongMsg` is not checked in; inputs of that size are
//! covered by the `sha3` differential in `shake.rs`.

use solana_shake::Shake;

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// `key = value` lines of one CAVP file, grouped per output block.
fn records(file: &str) -> Vec<Vec<(String, String)>> {
    let mut out = Vec::new();
    let mut cur = Vec::new();
    for line in file.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (key, value) = match line.split_once('=') {
            Some((k, v)) => (
                k.trim().trim_start_matches('['),
                v.trim().trim_end_matches(']'),
            ),
            None => continue,
        };
        cur.push((key.to_string(), value.to_string()));
        if key == "Output" {
            out.push(core::mem::take(&mut cur));
        }
    }
    out
}

fn field<'a>(rec: &'a [(String, String)], key: &str) -> &'a str {
    &rec.iter()
        .find(|(k, _)| k == key)
        .unwrap_or_else(|| panic!("missing {key}"))
        .1
}

fn shake<const BITS: usize>(input: &[u8], out_len: usize) -> Vec<u8> {
    let mut s = Shake::<BITS>::new();
    s.absorb(input);
    let mut s = s.finalize();
    let mut out = vec![0u8; out_len];
    for byte in out.iter_mut() {
        let mut b = [0u8; 1];
        s.squeeze(&mut b);
        *byte = b[0];
    }
    out
}

fn msg_file<const BITS: usize>(file: &str) {
    let recs = records(file);
    assert!(recs.len() > 100, "{} records", recs.len());
    for rec in &recs {
        let len_bits: usize = field(rec, "Len").parse().unwrap();
        let msg = if len_bits == 0 {
            Vec::new()
        } else {
            unhex(field(rec, "Msg"))
        };
        assert_eq!(msg.len() * 8, len_bits);
        let expected = unhex(field(rec, "Output"));
        assert_eq!(
            shake::<BITS>(&msg, expected.len()),
            expected,
            "Len = {len_bits}"
        );
    }
}

fn variable_out_file<const BITS: usize>(file: &str) {
    let recs = records(file);
    assert!(recs.len() > 1000, "{} records", recs.len());
    for rec in &recs {
        let out_bits: usize = field(rec, "Outputlen").parse().unwrap();
        let msg = unhex(field(rec, "Msg"));
        let expected = unhex(field(rec, "Output"));
        assert_eq!(expected.len() * 8, out_bits);
        assert_eq!(
            shake::<BITS>(&msg, expected.len()),
            expected,
            "Outputlen = {out_bits}"
        );
    }
}

/// SHAKE Monte Carlo Test (SHA-3 validation system §6.3), byte oriented:
///
/// ```text
/// Output[0] = Msg; OutputLen = maxoutbytes
/// for j in 0..100:
///     for i in 1..=1000:
///         M = leftmost 16 bytes of Output[i-1], zero-padded on the right
///         Output[i] = SHAKE(M, OutputLen)
///         r = rightmost 16 bits of Output[i] as a big-endian integer
///         OutputLen = minoutbytes + (r mod (maxoutbytes - minoutbytes + 1))
///     checkpoint j = Output[1000]; Output[0] = Output[1000]
/// ```
fn monte_file<const BITS: usize>(file: &str) {
    let mut min_bytes = 0;
    let mut max_bytes = 0;
    let mut seed = Vec::new();
    for line in file.lines() {
        let line = line.trim();
        if let Some(v) = line.strip_prefix("[Minimum Output Length (bits) = ") {
            min_bytes = v.trim_end_matches(']').parse::<usize>().unwrap() / 8;
        } else if let Some(v) = line.strip_prefix("[Maximum Output Length (bits) = ") {
            max_bytes = v.trim_end_matches(']').parse::<usize>().unwrap() / 8;
        } else if let Some(v) = line.strip_prefix("Msg = ") {
            seed = unhex(v);
            break;
        }
    }
    assert!(min_bytes > 0 && max_bytes > min_bytes && seed.len() == 16);
    let checkpoints = records(file);
    assert_eq!(checkpoints.len(), 100);

    let range = max_bytes - min_bytes + 1;
    let mut output = seed;
    let mut out_len = max_bytes;
    for (j, rec) in checkpoints.iter().enumerate() {
        for _ in 0..1000 {
            let mut m = [0u8; 16];
            let take = output.len().min(16);
            m[..take].copy_from_slice(&output[..take]);
            output = shake::<BITS>(&m, out_len);
            let r = ((output[output.len() - 2] as usize) << 8) | output[output.len() - 1] as usize;
            out_len = min_bytes + (r % range);
        }
        assert_eq!(field(rec, "COUNT").parse::<usize>().unwrap(), j);
        let expected_bits: usize = field(rec, "Outputlen").parse().unwrap();
        assert_eq!(output.len() * 8, expected_bits, "COUNT = {j}");
        assert_eq!(output, unhex(field(rec, "Output")), "COUNT = {j}");
    }
}

#[test]
fn shake128_short_msg() {
    msg_file::<128>(include_str!("vectors/SHAKE128ShortMsg.rsp"));
}

#[test]
fn shake256_short_msg() {
    msg_file::<256>(include_str!("vectors/SHAKE256ShortMsg.rsp"));
}

#[test]
fn shake128_variable_out() {
    variable_out_file::<128>(include_str!("vectors/SHAKE128VariableOut.rsp"));
}

#[test]
fn shake256_variable_out() {
    variable_out_file::<256>(include_str!("vectors/SHAKE256VariableOut.rsp"));
}

#[test]
fn shake128_monte() {
    monte_file::<128>(include_str!("vectors/SHAKE128Monte.rsp"));
}

#[test]
fn shake256_monte() {
    monte_file::<256>(include_str!("vectors/SHAKE256Monte.rsp"));
}
