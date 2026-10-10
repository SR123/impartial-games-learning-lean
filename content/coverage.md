## Scope: what is and is not covered

This page records, claim by claim, how the paper's statements are supported. It is a map of evidence, not a
certificate for the paper as a whole.

- **What Lean checks.** The Lean development states formal versions of the paper's definitions, theorems and
  constructions, and the Lean kernel checks every proof. A successful build establishes the *formal statement*.
  Whether that statement says the same thing as an English sentence is a separate question; each claim record
  answers it in plain language under *How this is formalised* and names any gap.
- **Named classical inputs.** The classical circuit lower bounds are not proved here. Håstad's negligible
  parity-correlation theorem enters as an explicit hypothesis, `HastadNegl`, of the theorems that need it; the
  worst-case statement `ParityNotAC0` is derived from it. Results that use it are marked *checked conditional
  theorem using named classical input*. The Linial–Mansour–Nisan and Tal spectral bounds are cited only: the
  Fourier-tail hypothesis `TailPremise` is used in a checked implication, but it has not been connected to a
  precise published statement with reconciled conventions.
- **What the counts mean.** The counts further down include helper lemmas, adapters and auxiliary definitions;
  they measure the size of the development, not the number of results in the paper.
- **What is not certified.** Training runs, learning curves, checkpoint diagnostics and the cause of the
  plateau near 0.54 are empirical. They rest on saved run records and are marked *empirical result*. The
  experiments do not show that AlphaZero-style self-play discovers any of the constructions. Background
  literature and interpretive remarks are marked *external cited result* or *informal interpretation*.
- **Bridges that are absent.** The recurrent replay and board-storage strategies are proved to win in their own
  stateful game semantics. A bridge from that semantics to the newer general history model of weak mastery
  (`Mastery.Hist`) has not been built; the audit lists it as optional. Until it exists, those guarantees hold in the
  controller's own semantics only. The website reports this rather than hiding it.
- **The full sequential bypasses are not AC⁰.** Each bypass keeps *individual* updates shallow while adding
  information or processing time. The complete multi-head and recurrent board-to-move maps are proved not to be
  AC⁰ families (conditional on `ParityNotAC0`); nothing here says that full parity computation is in AC⁰.
