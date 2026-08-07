//! Base64url (RFC 4648 §5) decoding, unpadded — the JWT alphabet.
//! Hand-rolled so the dependency tree stays at one crate; ~40 lines is
//! cheaper to audit than a transitive feature-set.

pub fn decode(input: &str) -> Result<Vec<u8>, String> {
    fn val(c: u8) -> Result<u32, String> {
        match c {
            b'A'..=b'Z' => Ok((c - b'A') as u32),
            b'a'..=b'z' => Ok((c - b'a' + 26) as u32),
            b'0'..=b'9' => Ok((c - b'0' + 52) as u32),
            b'-' => Ok(62),
            b'_' => Ok(63),
            _ => Err(format!("invalid base64url byte 0x{c:02x}")),
        }
    }
    let input = input.trim_end_matches('=');
    let bytes = input.as_bytes();
    if bytes.len() % 4 == 1 {
        return Err("truncated base64url input".into());
    }
    let mut out = Vec::with_capacity(bytes.len() * 3 / 4);
    for chunk in bytes.chunks(4) {
        let mut acc: u32 = 0;
        for &c in chunk {
            acc = (acc << 6) | val(c)?;
        }
        acc <<= 6 * (4 - chunk.len());
        let produced = match chunk.len() {
            2 => 1,
            3 => 2,
            4 => 3,
            _ => unreachable!("len % 4 == 1 rejected above"),
        };
        let all = acc.to_be_bytes();
        out.extend_from_slice(&all[1..1 + produced]);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::decode;

    #[test]
    fn rfc_vectors() {
        assert_eq!(decode("").unwrap(), b"");
        assert_eq!(decode("Zg").unwrap(), b"f");
        assert_eq!(decode("Zm8").unwrap(), b"fo");
        assert_eq!(decode("Zm9v").unwrap(), b"foo");
        assert_eq!(decode("Zm9vYg").unwrap(), b"foob");
        assert_eq!(decode("Zm9vYmE").unwrap(), b"fooba");
        assert_eq!(decode("Zm9vYmFy").unwrap(), b"foobar");
    }

    #[test]
    fn url_alphabet() {
        // 0xfb 0xff -> "-_8" in the url-safe alphabet
        assert_eq!(decode("-_8").unwrap(), vec![0xfb, 0xff]);
    }

    #[test]
    fn padding_tolerated() {
        assert_eq!(decode("Zm9v").unwrap(), decode("Zm9v==").unwrap());
    }

    #[test]
    fn rejects_standard_alphabet_and_junk() {
        assert!(decode("+/").is_err());
        assert!(decode("Zg{").is_err());
        assert!(decode("Zzzzz").is_err()); // len % 4 == 1
    }
}
