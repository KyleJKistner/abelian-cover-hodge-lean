# Contributing and audit protocol

Changes to a verified theorem should include:

1. a precise manuscript/certificate mapping in `docs/CLAIMS.md`;
2. a new `#audit_axioms` entry for any headline declaration;
3. no proof placeholders or global project postulates;
4. a regression theorem for finite enumerations, with the range stated; and
5. an explicit classification using the status vocabulary in
   `docs/CLAIMS.md`.

Do not move an obligation from `Bridge.UnformalizedDeductions` into
`External.ProspectiveCitationInputs` solely because a nearby general theorem
exists. The exact hypotheses and the exact arrow used by the eventual concrete
assembly must be supported by a pinned source or by a Lean proof. Remember that
`Bridge.PublishedInputs` is still an unrelated abstract scaffold.

Run `./scripts/audit.sh` before opening a pull request.
