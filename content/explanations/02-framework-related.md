<!-- Section 2 (framework) and Section 3 (related work). -->

<!-- explain: c-qset -->
**Inhibitory effects are allowed.** Negating an input makes a positive literal weight act negatively on the original input. The restriction is the fixed bound on the threshold after this rewriting. A firing gate then has a bounded-size witness of satisfied literals; a general majority gate does not. This is why the threshold bound matters computationally.

**The grid.** Every weight and threshold is a multiple of $1/D$ between $0$ and $W/D$: for example, with $D=4$
and $W=8$ the allowed values are $0, 0.25, 0.5, \dots, 2$. The point is that this set is *fixed*: it does not grow
when the input gets longer.

**Why negative terms matter.** The model only has nonnegative weights on literals (an input $x$ or its negation
$1-x$). A signed term $-a\,x$ can be rewritten as $a(1-x) - a$, so it becomes a nonnegative weight on the negated
literal, but the threshold rises by $a$. With many negative terms the threshold can grow with the input length and
leave the grid. So "signed weights" are not automatically inside the model.

<!-- formal: c-qset -->
A gate in Lean ({{lean:NimAudit.AC0.Gate}}) stores integer coefficients $a_j$, negation flags and an integer
threshold $b$; with denominator $D$ the paper's weights are $a_j/D$ and the threshold is $b/D$.
{{lean:NimAudit.AC0.gate_rat_iff}} proves that the paper's rational Heaviside form fires exactly when the integer
form $b\le\sum_j a_j[z_j\oplus\eta_j]$ does (for $D>0$). Fixed-scale validity,
{{lean:NimAudit.AC0.Gate.Valid}}, bounds the threshold and coefficients by $W$.

The remark about signed terms is the identity {{lean:NimAudit.Windows.literal_shift}}: over the integers,
$\theta\le s-a x \iff \theta+a\le s+a(1-x)$.

<!-- explain: def:quantised-inference -->
**Effective precision.** The motivation is the scale of distinctions a computation can use reliably, potentially limited by noise and much coarser than float32 rounding. Ordinary finite-precision storage alone does not establish the model's hypotheses. Noise does not automatically imply a Boolean literal-threshold implementation either.

This definition fixes the class of networks the lower bound is about:

- **constant depth** (a fixed number of layers, independent of the input length);
- **polynomially many** threshold neurons;
- **weights and thresholds on the fixed grid** $\mathcal Q_{W,D}$;
- for recurrent and attention-style models, a fixed time window $T$ that bounds the **entire** unrolled
  computation, including anything used to form a retained state.

Example: a 3-layer network on $n$ inputs with $n^2$ neurons, all weights in $\{0,1/2,1\}$ and thresholds at most
$2$, is in the class for every $n$.

Caveat: this is a restricted *logical* model inspired by bounded numerical resources. It is not equivalent to
arbitrary INT8 or fixed-point inference, and ordinary floating-point layers with signed weights are not
automatically covered.

<!-- formal: def:quantised-inference -->
The formal model is the literal-threshold gate network of Appendix A ({{claim:def:NN-formal}}): gates
({{lean:NimAudit.AC0.Gate}}) arranged in layers ({{lean:NimAudit.AC0.Layer}}), evaluated by
{{lean:NimAudit.AC0.evalNet}}, with every gate valid for the grid bound $W$ ({{lean:NimAudit.AC0.NetValid}}).
Two checked facts support the definition's use:

- {{lean:NimAudit.AC0.gate_ac0}}: one valid gate is computed exactly by a formula of depth at most 3 (counting NOT)
  and size at most $1+(m+1)^W(2W+1)$ for fan-in $m$;
- {{lean:NimAudit.FiniteNet.netFormula_spec}}: a network of $L$ layers on an $n$-bit input is computed output by
  output by one formula of depth at most $3L$ and size at most $2(2W+3)^L(M+1)^{WL}$, reading only the $n$ inputs.

The recurrent and attention-style parts of the definition are covered by {{claim:def:RNN-formal}} and
{{claim:def:LTST-formal}}.

<!-- explain: c-window-insufficient -->
A recurrent update that looks only at its previous state is still very powerful if it is allowed to run for
many steps. The update $h_{r+1}=h_r\oplus x_r$ consults one previous state, yet after $n$ steps $h_n$ is the
parity of all inputs, which no AC⁰ circuit computes.

So the right restriction for the simulation theorem is on the *total* number of unrolled steps $T$, not on how
far back each update looks. Section 5.5 uses exactly this loophole on purpose: it lets the number of updates grow
with the number of heaps.

<!-- formal: c-window-insufficient -->
{{lean:NimAudit.scan_invariant}} proves that folding XOR over a list of rows from an initial value gives that
value XOR the nim-sum of the rows, for any length: a one-step dependency accumulates the global XOR. A single
update is shallow: {{lean:NimAudit.Recurrent.circuit_resources}} bounds one recurrent update by depth 4 and size
$28B+8$. The bounded-unrolling restriction under which the simulation theorem does apply is
{{claim:def:RNN-formal}}.

<!-- explain: c-witness -->
**The idea.** With fixed scale, the smallest positive weight is $1/D$ and the largest threshold is $W/D$. If a unit
fires, its weighted sum reached the threshold; each active literal contributes at least $1/D$, so at most $W$ of
them already suffice. Such a small set of literals is a *witness*.

**Consequence.** A unit fires exactly when some witness of at most $W$ literals is fully true: an OR over at most
$\binom{m}{\le W}$ ANDs of at most $W$ literals. That is a DNF of polynomial size $O(m^W)$ and depth 2, an AC⁰
circuit. Composing a constant number of layers keeps everything in AC⁰.

**Caveat.** If thresholds could grow with fan-in (for example majority, threshold $m/2$), witnesses would grow too,
and this argument would fail.

<!-- formal: c-witness -->
{{lean:NimAudit.AC0.Gate.bounded_witness}}: whenever a gate fires, an initial segment of its active literals of
length at most the integer threshold $b\le W$ already has coefficient sum at least $b$.
{{lean:NimAudit.AC0.gate_ac0}} turns this into the DNF, with exact semantics and the explicit size and depth
bounds. See {{claim:lem:unit-ac0}} for the full lemma.

<!-- explain: c-not-floating -->
TC⁰ means constant-depth, polynomial-size circuits with general threshold gates, including majority gates. It can compute parity, so constant depth alone cannot support the paper's lower bound.

The result is about **fixed scale**, not about floating-point formats as such. What breaks the argument is
*scale adaptation*: thresholds or biases that grow with the fan-in, or weights that shrink like $1/n$ or
$1/\sqrt n$ (as in many normalisation schemes). Those regimes behave like threshold circuits ($\mathrm{TC}^0$),
which can count and hence compute parity.

<!-- formal: c-not-floating -->
An interpretive paragraph. Its precise counterpart is the scope remark that follows, where Lean checks the
boundary example: a majority gate violates the fixed-scale validity condition once its fan-in exceeds $2W$
({{claim:rem:ac0-scope.model}}).

<!-- explain: rem:ac0-scope.model -->
The remark says what the abstraction deliberately leaves out: fan-in-dependent re-scaling, large signed biases
that grow with dimension, and computations whose depth grows with $n$.

Concrete example: majority of $m$ bits is a threshold gate with all weights $1$ and threshold $\lceil m/2\rceil$.
Its weights are on the grid, but its threshold grows with $m$. So majority is *not* in the model once $m>2W$, even
though "all coefficients lie in a finite set". This is why the model bounds thresholds, not only weights.

<!-- formal: rem:ac0-scope.model -->
{{lean:NimAudit.Windows.majGate_not_valid}}: for every $W$ and every $m>2W$, the $\{0,1\}$-coefficient majority gate
{{lean:NimAudit.Windows.majGate}} is not valid for the grid bound $W$ ({{lean:NimAudit.AC0.Gate.Valid}}). This checks
the precise reason why finite coefficient sets alone do not give the constant-witness property.

<!-- explain: rem:ac0-scope.tc0 -->
Once thresholds may scale with fan-in, constant-depth threshold circuits (the class $\mathrm{TC}^0$) can count and
therefore compute parity. The remark mentions this to explain what the model excludes and why: the lower bound
holds only for fixed-scale gates.

<!-- formal: rem:ac0-scope.tc0 -->
A classical fact about threshold circuits, cited and not formalised here.

<!-- explain: rem:local-vs-global-parity.local -->
"Parity is hard" always means *global* parity of all $n=NB$ input bits. Parity of a constant number of bits is
easy: a fixed truth table, or a short chain of two-input XORs. Bitwise XOR of a constant number $t$ of $B$-bit
blocks is equally easy, since each output bit is the XOR of $t$ bits.

This is what both bypasses exploit: the two-frame difference XORs two heaps, and the recurrent update XORs the
accumulator with one row.

<!-- formal: rem:local-vs-global-parity.local -->
{{lean:NimAudit.Windows.xorChain_res}}: XOR of $t$ formulas of depth at most $d$ and size at most $s$ has depth at
most $d+3t$ and size at most $6^t(s+1)$. {{lean:NimAudit.Windows.blockXor_res}}: bitwise XOR of $t$ blocks has depth
at most $3t$ and size at most $2\cdot6^t$. For fixed $t$ these are constants.

<!-- explain: rem:local-vs-global-parity.global -->
Global parity of all $n$ bits cannot be computed by constant-depth, polynomial-size circuits of AND, OR and NOT
gates. This is the classical lower bound behind every negative result of the paper.

<!-- formal: rem:local-vs-global-parity.global -->
The classical theorem is not proved in Lean. It enters as the named hypothesis
{{lean:NimAudit.ClassicalBoundary.HastadNegl}}, the negligible-correlation form of Håstad (2014), Corollary 3.2, in
the classical circuit conventions. {{lean:NimAudit.ClassicalBoundary.parityNotAC0_of_hastad}} proves that it implies
the worst-case family statement {{lean:NimAudit.Barrier.ParityNotAC0}} (no family of fixed-depth,
polynomial-size formulas computes parity of $m$ bits for all large $m$), including the convention adapters between
classical and Lean circuit measures.

<!-- explain: c-model-table -->
The table lines up four properties of deployed inference with what the model captures:

- **fixed latency**: constant depth (and window $T$), not depth growing with $n$;
- **fixed-scale quantisation**: weights and thresholds on a fixed grid, not fan-in-dependent scaling;
- **parallel bit operations**: unbounded fan-in AND, OR, NOT, but not exact global counting or parity;
- **signed effects**: through input negations, not large signed dot products.

<!-- formal: c-model-table -->
A summary table. The formal content is the gate model and its simulation: {{claim:def:quantised-inference}},
{{claim:lem:unit-ac0}} and {{claim:thm:sim-ac0}}.

<!-- explain: c-primer -->
Background in one paragraph: AC⁰ is constant depth, polynomial size, unbounded fan-in AND, OR and NOT; PARITY is
not in AC⁰ (a classical theorem); TC⁰ adds threshold gates of unbounded fan-in and can compute parity. In the
fixed-scale regime each threshold unit has a constant-size witness, so the computation collapses to AC⁰.

<!-- formal: c-primer -->
The definitions and the PARITY lower bound are classical background (the lower bound enters Lean as the named
input `HastadNegl`, {{claim:rem:local-vs-global-parity.global}}). The collapse statement is
{{claim:thm:sim-ac0}}.

<!-- explain: thm:sim-ac0 -->
**Board sizes and attention.** Within a game the input layout stays aligned: $N$ heap rows with $B$ bits each, including zero rows for emptied heaps. The theorem concerns a family of these layouts as $NB$ grows. An attention extension must implement scoring, coefficient selection and aggregation using the permitted gates; alignment alone does not establish this.

**What it says.** Take any family of networks, one for each input length $n$, in which: the number of units is
polynomial in $n$; the number of layers is a fixed constant (and recurrent or attention-style models run for at
most $T$ steps in total); every operation is a literal-threshold gate with weights and threshold on the fixed
grid. Then the function each network computes is computed by an AC⁰ circuit family, with depth depending only on
$L,T,W,D$.

**How.** Each unit becomes a small DNF (its witness expansion), each layer becomes a constant number of circuit
layers, and a recurrent model with at most $T$ steps is unrolled into a feedforward one.

**Why it matters.** Combined with the parity lower bound, it rules out any network of this kind that computes a
function whose computation requires global parity, such as winning-move selection in NIM
([[thm:singleframe-impossible]]).

**Caveats.** The model needs nonnegative literal weights, bounded thresholds and Boolean intermediate states.
Floating-point networks with signed weights, normalisation that rescales with fan-in, or softmax attention are not
covered unless separately reduced to these gates.

<!-- formal: thm:sim-ac0 -->
**Objects.** Formulas (Boolean trees with constants, NOT and unbounded fan-in AND/OR) stand for circuits; *size*
counts every node and *depth* counts NOT nodes as well, which is conservative. Networks are lists of layers of
valid gates.

**Main steps checked.**

1. One gate: {{lean:NimAudit.AC0.gate_ac0}} (the DNF, from the bounded witness lemma).
2. One network: {{lean:NimAudit.AC0.network_ac0}}: a valid network of $L$ layers with fan-ins and widths at most
   $M$ is computed output by output by formulas of depth at most $3L$ and size at most $2(2W+3)^L(M+1)^{WL}$,
   reading only its inputs.
3. Families: {{lean:NimAudit.FiniteNet.family_finite}} for networks whose widths are polynomial in the input
   length, with a single formula per output carrying the semantics, depth, size and input bounds;
   {{lean:NimAudit.Family.netFam_ac0}} packages this as an AC⁰ family certificate
   ({{lean:NimAudit.Family.AC0Fam}}) for every network family certificate ({{lean:NimAudit.Family.NetFam}}).
4. Recurrence: {{lean:NimAudit.Windows.window_ac0}}: $T$ updates of a cell that reads its input block and the $w$
   most recent states unroll to formulas of depth at most $3LT$, reading only the $T$ input blocks.
5. Attention-style models: {{lean:NimAudit.Windows.staged_ac0}}: a model given as $K$ stages, each a valid gate
   network, is one network of depth at most $3KL$.

**Relationship to the paper.** The denominator $D$ disappears after clearing denominators: the integer threshold is
at most $W$. The theorem's hypothesis (3) "permitted primitives" is the validity of every gate. The Lean statements
are nonuniform (they assert existence of formulas for each size); the paper makes no uniformity claim either.

<!-- explain: c-rw-circuits -->
Related work on circuits and neural models: parity is outside AC⁰ but inside $\mathrm{TC}^0$; results on attention
depend on the exact model (hard attention can be in AC⁰; other variants have $\mathrm{TC}^0$ bounds that do not rule
out parity). The sequential-computation view of chain-of-thought work is mentioned because it resembles the
recurrent bypass, though the formal settings differ.

<!-- formal: c-rw-circuits -->
Cited literature, not formalised here. The paper's own use of these distinctions is in {{claim:thm:sim-ac0}} and
{{claim:prop:streaming-nimsum}}.

<!-- explain: c-rw-quant -->
Low-bit inference is the practical motivation, but the theorem needs more than a low-bit format: nonnegative
weights on Boolean literals, bounded thresholds and Boolean intermediate states. These are mathematical
assumptions, not consequences of using INT8. Standard signed linear layers and scale-adaptive normalisation are
outside the theorem unless reduced to the permitted gates.

<!-- formal: c-rw-quant -->
A statement of scope. The assumptions it lists are exactly the hypotheses of {{claim:thm:sim-ac0}} and the
validity condition of {{claim:def:NN-formal}}.

<!-- explain: c-rw-rl -->
Impartial games are a stress test for reinforcement learning because optimal play is governed by an exact algebraic
invariant rather than by approximate patterns. The paragraph cites the earlier studies by Zhou and Riis and
separates two questions: a representational obstruction in a restricted model (this paper) and the mechanisms
behind failures of ordinary training (which need separate experiments).

<!-- formal: c-rw-rl -->
Cited background and a scope remark; nothing here is formalised.

<!-- explain: c-rw-history -->
Frame stacking is usually justified by partial observability: velocity cannot be read off one frame. NIM is fully
observable, so the previous board is informationally redundant. The point here is different: the previous board
can still reduce the *computation* needed, because it carries a promise (its nim-sum is zero) established by an
earlier correct move. Given that promise, the local difference is enough for the next reply.

Caveat: establishing the promise in the first place is a separate task ([[par-the-initialisation-boundary-for-restoration|the initialisation boundary]]).

<!-- formal: c-rw-history -->
An interpretive paragraph. The formal content is {{claim:prop:restore}} (restoration under the promise) and
{{claim:c-init-boundary}} (why the promise matters).
