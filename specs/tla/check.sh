#!/usr/bin/env bash
# Run the disclosure model through TLC and ASSERT each config's outcome.
#
#   bash specs/tla/check.sh
#
# WHY THIS ASSERTS RATHER THAN REPORTS. Two of the three configs are supposed
# to FAIL — they exist to exhibit counterexamples. A runner that merely printed
# TLC's output would go green if a future edit accidentally made the racy
# config pass, which is precisely the case worth catching: a spec whose
# counterexamples have stopped reproducing is a spec that has stopped saying
# anything. This is the TLA+ half of the anti-vacuity discipline the Lean side
# gets from its named counterexample policies.
#
# tla2tools.jar is not vendored. Point $TLA2TOOLS at a copy, or let this script
# fetch the pinned release. The digest is checked, so a wrong-bytes response is
# refused whatever served it — same posture as the org bootstrap's
# fetch_verified.
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$here" || exit 1

JAR="${TLA2TOOLS:-$here/.tla2tools.jar}"
JAR_URL="https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
JAR_SHA="ab323b79802aedc3203b3f9af37c6aca3ed43f4e0225b36f2aa77b26de46c05f"

if [ ! -f "$JAR" ]; then
  echo "fetching tla2tools v1.8.0 -> $JAR"
  curl -fsSL --retry 3 --max-time 180 "$JAR_URL" -o "$JAR" || {
    echo "FAIL: could not fetch tla2tools; set \$TLA2TOOLS to a local copy" >&2; exit 1; }
fi
echo "$JAR_SHA  $JAR" | sha256sum -c --status - || {
  echo "FAIL: $JAR does not match the pinned digest — refusing to run it" >&2; exit 1; }

command -v java >/dev/null 2>&1 || { echo "FAIL: no java on PATH" >&2; exit 1; }

pass=0
fail=0
ok()  { pass=$((pass + 1)); echo "  ok   — $1"; }
bad() { fail=$((fail + 1)); echo "  FAIL — $1"; }

# run <spec> <config> [extra TLC flags…] — TLC output on stdout, artifacts
# cleaned up after.
run() {
  local spec="$1" cfg="$2"
  shift 2
  java -cp "$JAR" tlc2.TLC "$@" -config "$cfg" "$spec.tla" 2>&1 | grep -vE '^Picked up'
  rm -rf states
  rm -f "$spec"_TTrace_*.tla "$spec"_TTrace_*.bin
}

echo "disclosure.tla"

# --- racy: the behaviour shipped today -------------------------------------
out="$(run disclosure disclosure-racy.cfg)"
case "$out" in
  *"Invariant NoUnconsentedDisclosure is violated"*)
    ok "racy: TOCTOU reproduces — consent withdrawn during the derive window is not seen" ;;
  *) bad "racy: expected NoUnconsentedDisclosure to be violated; it was not" ;;
esac

# --- anon: the independence result ------------------------------------------
# Atomic = TRUE closes the race. The fallback is still live, so the
# unretractable upload still happens. If this config ever reports
# NoUnconsentedDisclosure instead, the two faults are no longer separated and
# the config has stopped making its point.
out="$(run disclosure disclosure-anon.cfg)"
case "$out" in
  *"Invariant NoAnonUpload is violated"*)
    ok "anon: anonymous fallback reproduces even with an atomic check" ;;
  *) bad "anon: expected NoAnonUpload to be violated; it was not" ;;
esac
case "$out" in
  *"Invariant NoUnconsentedDisclosure is violated"*)
    bad "anon: NoUnconsentedDisclosure broke too — the config no longer isolates the fallback" ;;
  *) ok "anon: NoUnconsentedDisclosure holds — the two faults are independent" ;;
esac

# --- safe: every invariant and the liveness property -------------------------
out="$(run disclosure disclosure-safe.cfg)"
case "$out" in
  *"Model checking completed. No error has been found"*)
    ok "safe: all invariants and Termination hold across the full state space" ;;
  *) bad "safe: expected a clean run; TLC reported an error" ;;
esac
case "$out" in
  *"Deadlock"*) bad "safe: deadlock reported — the Terminating stutter is not covering the terminal state" ;;
  *)            ok "safe: no deadlock" ;;
esac

echo
echo "degradation.tla"

# --- shipped: both faults live — the behaviour that degraded on 2026-08-16 ---
# Both invariants break here, so which one TLC reports first is an artifact of
# its search order. Assert only that a violation is found; the per-fault
# assertions belong to the two isolating configs below, where exactly one
# invariant CAN break and the assertion is therefore stable.
out="$(run degradation degradation-shipped.cfg)"
case "$out" in
  *"is violated"*)
    ok "shipped: the degradation reproduces — revocation did not close the door" ;;
  *) bad "shipped: expected an invariant violation; the config came back clean" ;;
esac

# --- fallback / partial: the independence result ----------------------------
# -continue makes TLC explore the FULL state space and report EVERY violated
# invariant rather than halting at the first. That is what turns "the other
# invariant holds" into a checked statement: without it, an unreported
# invariant might simply break in a state the search stopped short of, and the
# independence claim would be an artifact of the halt rather than a result.
out="$(run degradation degradation-fallback.cfg -continue)"
case "$out" in
  *"Invariant NoUndernamedEffect is violated"*)
    ok "fallback: substitution reproduces even when partials are reported honestly" ;;
  *) bad "fallback: expected NoUndernamedEffect to be violated; it was not" ;;
esac
case "$out" in
  *"Invariant NoSilentPartial is violated"*)
    bad "fallback: NoSilentPartial broke too — the config no longer isolates substitution" ;;
  *) ok "fallback: NoSilentPartial holds over the whole state space" ;;
esac

out="$(run degradation degradation-partial.cfg -continue)"
case "$out" in
  *"Invariant NoSilentPartial is violated"*)
    ok "partial: a mid-run revocation still ships green with the || removed" ;;
  *) bad "partial: expected NoSilentPartial to be violated; it was not" ;;
esac
case "$out" in
  *"Invariant NoUndernamedEffect is violated"*)
    bad "partial: NoUndernamedEffect broke too — the config no longer isolates the partial" ;;
  *) ok "partial: NoUndernamedEffect holds over the whole state space" ;;
esac

# --- safe: every invariant and the liveness property -------------------------
out="$(run degradation degradation-safe.cfg)"
case "$out" in
  *"Model checking completed. No error has been found"*)
    ok "safe: all invariants and Termination hold across the full state space" ;;
  *) bad "safe: expected a clean run; TLC reported an error" ;;
esac
case "$out" in
  *"Deadlock"*) bad "safe: deadlock reported — the Terminating stutter is not covering the terminal state" ;;
  *)            ok "safe: no deadlock" ;;
esac

echo
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ] || exit 1
