# Contributing and audit protocol

Changes to a verified theorem should include:

1. a precise manuscript/certificate mapping in `docs/CLAIMS.md`;
2. a new `#print axioms` entry for any headline declaration;
3. no proof placeholders or global project postulates;
4. a regression theorem for finite enumerations, with the range stated; and
5. an explicit classification as verified, published input, research input, or
   regression only.

Do not move a field from `ResearchInputs` to `PublishedInputs` solely because a
nearby general theorem exists. The exact hypotheses and the exact arrow used by
the assembly must be supported by a source or by a Lean proof.

Run `./scripts/audit.sh` before opening a pull request.
