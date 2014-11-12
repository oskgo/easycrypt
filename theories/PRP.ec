(*** A formalization of pseudo-random permutations **)
require import Fun.
require import Int.
require import Real.
require import Distr.
require import FSet.
(*---*) import Dexcepted.
require import FMap.

(** A PRP is a family of permutations F on domain D indexed by a
    keyspace K equipped with a distribution dK. *)
type D.

type K.

op dK: K distr.
axiom dK_ll: mu dK True = 1%r.

op P:K -> D -> D.

axiom bijective_P k:
  support dK k =>
  bijective (P k).

(** The Real PRP is defined as follows *)
module PRPr = {
  var k:K
  proc init(): unit = { k = $dK; }
  proc p(x:D): D = { return P k x; }
}.

(** Security is expressed with respect to the Random Permutation defined
    by some distribution on D. *)
op dD:D distr.
axiom dD_ll: mu dD True = 1%r.

module type PRP = {
  proc init(): unit
  proc p(x:D): D
}.

module type PRPA = {
  proc p(x:D): D
}.

module type Distinguisher(F:PRPA) = {
  proc distinguish(): bool
}.

module IND (P:PRP,D:Distinguisher) = {
  module D = D(P)

  proc main(): bool = {
    var b;

    P.init();
    b = D.distinguish();
    return b;
  }
}.

module PRPi = {
  var m:(D,D) map

  proc init(): unit = { m = FMap.empty; }

  proc p(x:D): D = {
    if (!mem x (dom m)) m.[x] = $dD \ (rng m);
    return (oget m.[x]);
  }
}.

(*** TODO: define notations ***)
(** Advantage of a distinguisher against a PRP oracle P:
      Adv^PRP_P(&m,D) = `|Pr[IND(P,D) @ &m: res] - Pr[IND(PRPi,D) @ &m: res]| **)
(** Advantage of a distinguisher against **the** PRP operator P:
      Adv^PRP_P(&m,D) = `|Pr[IND(PRPr,D) @ &m: res] - Pr[IND(PRPi,D) @ &m: res]| **)

(** Useful lemmas **)
lemma PRPr_init_ll: islossless PRPr.init.
proof. by proc; auto; smt. qed.

lemma PRPr_p_ll: islossless PRPr.p.
proof. by proc. qed.


(*** TODO: define strong PRP ***)