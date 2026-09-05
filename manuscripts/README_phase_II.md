# Historical Phase II package

The recovered package described itself as complete. That description is
superseded: the audit found mathematical defects and unproved general
representation/generator steps. The original TeX and claim ledger are retained
unchanged as provenance; their presence is not an endorsement of their claims.

Use [the manuscript index](README.md) for the current revisions and PDFs, and
[the controlling claim matrix](../docs/CLAIMS.md) for the exact boundary.
The standalone fusion revision proves a more precisely stated mixed
balanced-determinant result. It does not, by itself, establish the general
all-powers Hodge theorem or the full generic Hodge group of every elementary
prime cover family.

The original Phase II certificate and frozen report live under
[`legacy/certificates/`](../legacy/certificates/). The report is now reproduced
byte for byte by the pinned combined runner, without modifying the original
source or report:

```bash
.venv-audit/bin/python scripts/replay_certificates.py
```

See [provenance and setup](../docs/PROVENANCE.md) and the root README for the
required environment. Successful finite arithmetic does not establish the
geometric theorem claimed in the historical package.
