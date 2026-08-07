//! Lint trust-policy subject patterns for the recyclable-name trap.
//!
//! Input: one subject pattern per line (`#` comments and blank lines
//! skipped) — the strings a sub-only relying party matches, e.g.
//! `repo:acme/widget:ref:refs/heads/main` or `repo:acme/*`.
//!
//! The rules are the proved theorems' deployment shadow (Keycard/, this
//! repo): a matcher pinned to a recyclable name trusts the *label*, not
//! the identity — `Recycling.lean`'s counterexample; `repo:ORG/*` written
//! against mutable subs silently stops matching after the immutable flip —
//! `Matcher.lean`'s `wildcard_misses_immutable`.

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Severity {
    Error,
    Warning,
}

pub struct Finding {
    pub line: usize,
    pub severity: Severity,
    pub rule: &'static str,
    pub message: String,
}

pub fn lint(policy: &str) -> Vec<Finding> {
    let mut findings = Vec::new();
    for (idx, raw) in policy.lines().enumerate() {
        let line = idx + 1;
        let pat = raw.trim();
        if pat.is_empty() || pat.starts_with('#') {
            continue;
        }
        let Some(rest) = pat.strip_prefix("repo:") else {
            findings.push(Finding {
                line,
                severity: Severity::Warning,
                rule: "unrecognized-pattern",
                message: format!("`{pat}`: not a repo:… subject pattern; not analyzed"),
            });
            continue;
        };
        // repo:<owner>/<repo>[:<rest>] — the segment before the first ':'
        // names the repository; everything after is ref/environment detail.
        let repo_part = rest.split(':').next().unwrap_or("");
        if repo_part == "*" || repo_part.is_empty() {
            findings.push(Finding {
                line,
                severity: Severity::Error,
                rule: "unbounded-wildcard",
                message: format!("`{pat}`: matches every repository the issuer signs for"),
            });
            continue;
        }
        let (owner, repo) = match repo_part.split_once('/') {
            Some(pair) => pair,
            None => (repo_part, ""),
        };
        let owner_pinned = owner.contains('@');
        let repo_pinned = repo.contains('@') || repo == "*";
        if repo == "*" && !owner_pinned {
            findings.push(Finding {
                line,
                severity: Severity::Error,
                rule: "wildcard-mutable-org",
                message: format!(
                    "`{pat}`: org wildcard over a recyclable name — trusts whoever \
                     holds `{owner}`, and silently stops matching once subjects \
                     flip to `{owner}@ID/…`"
                ),
            });
            continue;
        }
        if !owner_pinned || !repo_pinned {
            findings.push(Finding {
                line,
                severity: Severity::Warning,
                rule: "mutable-name-matcher",
                message: format!(
                    "`{pat}`: pins names, not identities — a deleted or renamed \
                     `{owner}{}` frees the label for a stranger; pin `NAME@ID` \
                     (or match the `repository_id` claim instead)",
                    if repo.is_empty() { String::new() } else { format!("/{repo}") }
                ),
            });
        }
    }
    findings
}

#[cfg(test)]
mod tests {
    use super::{lint, Severity};

    #[test]
    fn clean_immutable_policy() {
        let f = lint("# prod\nrepo:acme@7241/widget@90513:ref:refs/heads/main\n");
        assert!(f.is_empty(), "{:?}", f.iter().map(|x| x.rule).collect::<Vec<_>>());
    }

    #[test]
    fn org_wildcard_over_mutable_name_is_an_error() {
        let f = lint("repo:acme/*");
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].rule, "wildcard-mutable-org");
        assert_eq!(f[0].severity, Severity::Error);
    }

    #[test]
    fn org_wildcard_with_pinned_org_passes() {
        assert!(lint("repo:acme@7241/*").is_empty());
    }

    #[test]
    fn mutable_exact_match_warns() {
        let f = lint("repo:acme/widget:ref:refs/heads/main");
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].rule, "mutable-name-matcher");
        assert_eq!(f[0].severity, Severity::Warning);
    }

    #[test]
    fn half_pinned_still_warns() {
        let f = lint("repo:acme@7241/widget");
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].rule, "mutable-name-matcher");
    }

    #[test]
    fn bare_star_is_unbounded() {
        let f = lint("repo:*");
        assert_eq!(f[0].rule, "unbounded-wildcard");
        assert_eq!(f[0].severity, Severity::Error);
    }

    #[test]
    fn non_repo_patterns_are_flagged_not_guessed() {
        let f = lint("https://token.actions.githubusercontent.com");
        assert_eq!(f[0].rule, "unrecognized-pattern");
    }

    #[test]
    fn comments_and_blanks_skipped() {
        assert!(lint("\n# repo:acme/*\n\n").is_empty());
    }
}
