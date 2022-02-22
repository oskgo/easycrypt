require import AllCore Distr.

type t, u.

module BiSample = {
  proc sample(dt : t distr, du : u distr) = {
    var t, u;

    t <$ dt;
    u <$ du;
    return (t, u);
  }
}.

module Prod = {
  proc sample(dt : t distr, du : u distr) = {
    var tu;

    tu <$ dt `*` du;
    return tu;
  }
}.

equiv eq: BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof. admitted.

equiv eq': BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof.
proc.
rewrite equiv [{1} 1 eq (dt,du) (t,u)].
+ by move=> /> &1; exists dt{1} du{1}.
+ done.
+ by inline *; auto.
+ by move=> /> &2; exists dt{2} du{2}.
+ done.
+ exact: eq. (* This one should be automated *)
+ done.      (* This one as well *)
(* This is the end of the tactic's work *)
(* unless we want to re-inline the RHS *)
inline *; wp.
conseq (: ={tu})=> [/#|].
by sim.
qed.

equiv eq2: BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof.
proc.
rewrite equiv[{1} 1 eq (dt, du) (t, u)].


 admitted.



(** seq 1: (={tout}). by sim.
    seq 2: (={tout} avec substitution); last by sim.
    transitivity ...
**)
