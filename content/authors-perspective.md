The starting point for this paper goes back to my thesis work in mathematical
logic, on feasible reasoning in bounded arithmetic and the strength of counting
principles. What interested me was a striking gap: a principle can be almost
obvious when viewed through the right abstraction, yet remain inaccessible to a
system restricted to a particular kind of elementary reasoning. That gap has
remained a thread through my work.

## Bounded arithmetic, counting and circuits

In my thesis, *Independence in Bounded Arithmetic*, I studied formal systems
whose restrictions reflect limits on the resources available for reasoning.
One of the surprises in this area is that elementary counting principles can,
in suitable formulations, be unprovable in certain weak systems of bounded
arithmetic. Examples include the pigeonhole principle and the parity principle
that an odd-sized set cannot be partitioned into pairs. These are statements
we readily understand from a higher-level perspective. What a formal system
can establish depends on its resources and on how the principle is represented.
My [work on modular counting principles](https://doi.org/10.1016/S0168-0072%2897%2900029-8)
explores how even different forms of counting can have different logical strengths.

The methods behind these independence results connect to Boolean circuit
complexity. Constant-depth, polynomial-size circuits built from AND, OR and NOT
gates cannot compute parity on arbitrarily long inputs. Related switching
arguments and probabilistic techniques play a role in proving limitations on
restricted reasoning. Computing the parity of a bit string and proving a
counting principle are different tasks, but the connection between their lower-bound
methods was an important part of this intellectual background. My later
[joint work with Paul Beame](https://doi.org/10.1090/dimacs/039/02)
also develops this connection through lower bounds for proofs of counting principles.

## The frog's-eye perspective

I think of restricted reasoning of this kind as a *frog's-eye perspective*:
working close to the individual pieces, without ready access to the abstraction
that makes the overall structure clear. This is a metaphor for the contrast
that interested me, rather than a technical definition of a proof system.
My later work in proof complexity, including resolution and other proof systems,
continued to explore this contrast.

A particularly vivid example is the mutilated chessboard. Remove two opposite
corners from an even-by-even chessboard and ask whether dominoes can cover the
remaining squares. Each domino covers one black and one white square, while
the two removed corners have the same colour. The colour imbalance settles
the question immediately. Yet in
[work with my former student Stefan Dantchev](https://doi.org/10.1109/SFCS.2001.959896),
we proved exponential lower bounds for resolution proofs of the standard
propositional encoding of this impossibility as the board grows. The short
colour-counting argument and the long resolution proofs concern the same
combinatorial obstruction, approached with very different reasoning resources.

## The question raised by AlphaZero

When AlphaZero appeared, I brought this background to the question of what its
neural networks could discover. How would they handle a game whose solution is
easy once a global invariant is recognised, but difficult to recover from
restricted computations? NIM offered a clear test: its optimal strategy has a
concise, efficient algorithm, and parity is at the heart of that algorithm.

A neural network is not simply a Boolean circuit. Its activations can be
real-valued, whereas Boolean gates work with zeros and ones; the available
operations and precision matter. Circuit lower bounds therefore need an explicit
bridge to the neural model. The present paper builds that bridge for a restricted
model of quantised inference. The broader question that motivated me remains
how a learning system can discover and use the abstraction that makes an
otherwise difficult task easy.

## The earlier FOM discussion

Harvey Friedman's [“AI Challenge” (28 September 2017)](https://fomarchive.ugent.be/2017-September/020612.html)
asked whether a computer could discover perfect play in NIM without being given
the winning strategy. His [“NIM Challenges” (30 September 2017)](https://fomarchive.ugent.be/2017-September/020619.html)
expanded the discussion to learning protocols and harder variants of the game.

A further post, [“NIM/Deep Learning” (15 October 2017)](https://fomarchive.ugent.be/2017-October/020642.html),
reproduces correspondence from John Schulman proposing a recurrent network that
reads the heaps one at a time, together with preliminary supervised nim-sum
experiments. This is an important antecedent of the broad row-wise recurrent
idea. It should be distinguished from the specific separator, state and
move-selection protocols, circuit bounds and correctness proofs developed in
this paper. The post also distinguishes supervised learning of the nim-sum from
learning a strategy through self-play. In [“NIM/AI challenges” (17 October 2017)](https://fomarchive.ugent.be/2017-October/020648.html),
the discussion turns to generalisation and to how the game is presented to a
learner, including whether its representation supplies a hint about binary
arithmetic.

The [earlier NIM preprint](https://arxiv.org/html/2411.06403v1#S1) discusses
Friedman's challenge in its introduction and cites it as reference [8]. The
archive links above identify the original posts more precisely than that
bibliographic entry did.

## Experiments with Bei Zhou

My subsequent work with Bei Zhou made this question concrete through experiments
on impartial games and parity-related learning tasks. My recollection is that
the reception was mixed. Some reactions questioned whether there was a real
limitation; others regarded the underlying difficulty as already obvious. I found
that the distinction I wanted to make was not easy to communicate. Saying that a
neural network can in principle compute a function does not settle whether a
particular architecture can represent it under specified resource constraints,
or whether a training procedure will discover it.

The joint work referred to here, with bibliographic details as given in the paper's reference list:

- Bei Zhou and Søren Riis. Impartial games: A challenge for reinforcement learning. *Machine Learning* 115:54, 2026; first preprint 2022. <https://doi.org/10.1007/s10994-026-06996-1>
- Bei Zhou and Søren Riis. Exploring parity challenges in reinforcement learning through curriculum learning with noisy labels. arXiv:2312.05379, 2023.
- Bei Zhou. *Reinforcement Learning for Impartial Games and Complex Combinatorial Optimisation Problems*. PhD thesis, Queen Mary University of London, 2024.

## From an obstruction to possible ways forward

The present paper isolates one precise computational obstruction in a restricted
model of neural inference. Its purpose is also constructive: once the missing
resource is clear, we can ask how to supply it. A transition between positions,
complementary rollout information, or a recurrent scan with retained state can
change what is computationally available to the learner. These constructions do
not settle the learning problem. They separate an obstacle in representation
from the further questions of training, generalisation and discovery through
self-play. The interactive edition lets readers follow that distinction from
the informal idea through the mathematics to the exact formal statements.

## Publication history and the present version

This paper has not yet undergone journal peer review. An earlier version received a desk rejection. A subsequent intended submission was not properly completed because of a misunderstanding, which I discovered only six months later. My emphasis in preparing the present version has been on making its arguments open to scrutiny, through detailed explanations, AI-assisted critical review, and machine-checked proofs.
