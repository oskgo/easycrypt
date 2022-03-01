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
transitivity {1} { (t,u) <@ BiSample.sample(dt,du); }
  (={dt,du} ==> ={t,u})
  (={dt,du} ==> (t,u){1} = tu{2});
  [ 4:transitivity {1} { (t,u) <@ Prod.sample(dt,du); }
        (={dt,du} ==> ={t,u})
        (={dt,du} ==> (t,u){1} = tu{2})];
  [   3:by inline *; auto
  | 2,5:done
  |   6:by call eq ].
+ smt().
+ smt().
by inline *; auto=> /#.
qed.

equiv eq2: BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof.
proc.
rewrite equiv [{1} 1 eq (dt,du) (t,u)].
+ by move=> /> &1; exists dt{1} du{1}.
+ by move=> /> &2; exists dt{2} du{2}.
inline *; wp.
conseq (: ={tu})=> [/#|].
by sim.
qed.
