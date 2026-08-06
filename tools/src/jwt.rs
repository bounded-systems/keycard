//! Decode a JWT's header and claims for inspection. Decode, not verify:
//! no signature check happens here, and the output says so.
//!
//! The one rule this module exists to keep: **the raw token never reaches
//! stdout or stderr.** A live OIDC token in a CI log is a replayable
//! credential; errors talk about shape, never content.

use crate::b64;

#[derive(Debug)]
pub struct Decoded {
    pub header: serde_json::Value,
    pub claims: serde_json::Value,
}

pub fn decode(token: &str) -> Result<Decoded, String> {
    let token = token.trim();
    let parts: Vec<&str> = token.split('.').collect();
    if parts.len() != 3 {
        // Shape only — never echo the input.
        return Err(format!(
            "expected a compact JWT (3 dot-separated parts), got {} part(s)",
            parts.len()
        ));
    }
    let header = part_json(parts[0]).map_err(|e| format!("header: {e}"))?;
    let claims = part_json(parts[1]).map_err(|e| format!("claims: {e}"))?;
    // parts[2] — the signature — is deliberately dropped: this tool cannot
    // verify it (no network, no keys), so it must not reproduce it either.
    Ok(Decoded { header, claims })
}

fn part_json(part: &str) -> Result<serde_json::Value, String> {
    let bytes = b64::decode(part)?;
    serde_json::from_slice(&bytes).map_err(|e| format!("not JSON ({e})"))
}

#[cfg(test)]
mod tests {
    use super::decode;

    // Header {"alg":"RS256"}, claims with a mutable-format sub. Signature is
    // a placeholder — decode() must not care and must not surface it.
    const TOKEN: &str = concat!(
        "eyJhbGciOiJSUzI1NiJ9",
        ".",
        "eyJzdWIiOiJyZXBvOmFjbWUvd2lkZ2V0OnJlZjpyZWZzL2hlYWRzL21haW4iLCJyZXBvc2l0b3J5X2lkIjo5MDUxM30",
        ".",
        "c2ln"
    );

    #[test]
    fn decodes_header_and_claims() {
        let d = decode(TOKEN).unwrap();
        assert_eq!(d.header["alg"], "RS256");
        assert_eq!(d.claims["sub"], "repo:acme/widget:ref:refs/heads/main");
        assert_eq!(d.claims["repository_id"], 90513);
    }

    #[test]
    fn rejects_wrong_shape_without_echoing() {
        let err = decode("only.two").unwrap_err();
        assert!(err.contains("2 part(s)"));
        assert!(!err.contains("only"), "error must not echo input");
    }

    #[test]
    fn rejects_non_json_payload() {
        assert!(decode("Zm9v.Zm9v.Zm9v").is_err());
    }
}
