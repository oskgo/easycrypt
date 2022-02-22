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
+ admit (* use a fresh memory on the right *).
+ admit (* use a fresh memory on the right *).
+ admit.

(**                 s  _  l   arg     res   **)
transitivity {1} { (t, u) <@ BiSample.sample(dt, du); }
(**           s      res        LHS of l    **)
  ((dt,du){1} = (dt,du){2} ==> (t,u){1} = (t,u){2})
(**  arg{1}   =   arg{2}        res{1}  =  res{2} **)
  ((dt,du){1} = (dt,du){2} ==> (t,u){1} = tu{2})=> //.
(**         pre            ==>      post    **)
+ by move=> /> &2; exists dt{2} du{2}. (** Why are dt and du separated? **)
+ by inline *; sim.
transitivity {1} { (t, u) <@ Prod.sample(dt, du); }
(**           s      res        RHS of l    **)
  ((dt,du){1} = (dt,du){2} ==> (t,u){1} = (t,u){2})
(**  arg{1}   =   arg{2}         res{1} =  res{2} **)
  ((dt,du){1} = (dt,du){2} ==> (t,u){1} = tu{2})=> //.
(**          pre                      post  **)
+ by move=> /> &2; exists dt{2} du{2}.
+ by call eq.
(** This is the end of the tactic's work **)
(** unless we want to re-inline the RHS **)
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
