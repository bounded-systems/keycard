//! keycard — decode OIDC token claims; lint trust policies.
//!
//! Posture: no network, ever, in this version (a future JWKS fetch would be
//! an explicit opt-in flag, never a default). Input comes from stdin or a
//! named file; the raw token is never written to any output stream. Argument
//! parsing is hand-rolled: two subcommands do not earn a dependency.

mod b64;
mod jwt;
mod lint;

use std::io::Read;
use std::process::ExitCode;

const USAGE: &str = "\
keycard — the OIDC model's little tool (decode claims, lint trust policies)

USAGE:
    keycard decode [FILE]   decode a JWT's header and claims (token from
                            FILE or stdin). Decode, NOT verify: no signature
                            check. The raw token is never printed.
    keycard lint [FILE]     lint subject patterns (one per line, from FILE
                            or stdin) for recyclable-name matchers.
                            Exit 1 on errors, 0 on warnings only.

The rules are the proved theorems' deployment shadow — see Keycard/ in
https://github.com/bounded-systems/keycard
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("decode") => run_decode(args.get(1).map(String::as_str)),
        Some("lint") => run_lint(args.get(1).map(String::as_str)),
        Some("--help") | Some("-h") | None => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("keycard: unknown subcommand `{other}`\n\n{USAGE}");
            ExitCode::from(2)
        }
    }
}

fn read_input(path: Option<&str>) -> Result<String, String> {
    match path {
        Some(p) => std::fs::read_to_string(p).map_err(|e| format!("{p}: {e}")),
        None => {
            let mut buf = String::new();
            std::io::stdin()
                .read_to_string(&mut buf)
                .map_err(|e| format!("stdin: {e}"))?;
            Ok(buf)
        }
    }
}

fn run_decode(path: Option<&str>) -> ExitCode {
    let input = match read_input(path) {
        Ok(s) => s,
        Err(e) => return fail(&e),
    };
    match jwt::decode(&input) {
        Ok(d) => {
            let out = serde_json::json!({ "header": d.header, "claims": d.claims });
            println!("{}", serde_json::to_string_pretty(&out).expect("valid JSON"));
            eprintln!("keycard: decoded, NOT verified — no signature check was performed");
            ExitCode::SUCCESS
        }
        Err(e) => fail(&e),
    }
}

fn run_lint(path: Option<&str>) -> ExitCode {
    let input = match read_input(path) {
        Ok(s) => s,
        Err(e) => return fail(&e),
    };
    let findings = lint::lint(&input);
    let mut errors = 0usize;
    for f in &findings {
        let tag = match f.severity {
            lint::Severity::Error => {
                errors += 1;
                "error"
            }
            lint::Severity::Warning => "warning",
        };
        println!("line {}: {tag} [{}] {}", f.line, f.rule, f.message);
    }
    if findings.is_empty() {
        println!("keycard: no findings");
    }
    if errors > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn fail(msg: &str) -> ExitCode {
    eprintln!("keycard: {msg}");
    ExitCode::FAILURE
}
