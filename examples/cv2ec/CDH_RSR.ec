require import AllCore List Distr DBool DInterval DList SDist SmtMap.
require import FinType FSet NominalGroup PROM SplitRO2.

import Distr.MRat.
import DBool.Biased.
import StdOrder.RealOrder.
import RField.

require import LibExt.

clone import NominalGroup.NominalGroup as N.

op e : Z.
axiom e_EU : e \in EU.

op elog (x : G) = choiceb (fun a => a \in EU /\ x = exp g a) e.

op elogr (y : Z) (b : G) = choiceb (fun x => x \in EU /\ b = exp g (y * x)) e.

lemma exprK (x y : Z) : x \in EU => y \in EU => elogr y (exp g (y * x)) = x.
proof.
move => x_EU y_EU; rewrite /elogr /=.
have := choicebP (fun a : Z => a \in EU /\ exp g (y * x) = exp g (y * a)) e _;
[by exists x | move => [E1 E2]].
by apply (exp_inj' y) => //; rewrite -E2.
qed.

(* we only get one cancelation law *)
lemma expK (x : Z) : x \in EU => elog (exp g x) = x.
proof.
move => x_EU; rewrite /elog /=.
have [E1 E2] := choicebP (fun a : Z => a \in EU /\ exp g x = exp g a) e _;
[by exists x | by apply exp_inj => //; rewrite -E2].
qed.

(* Does not seem to be used. *)
lemma elog_EU x : elog x \in EU.
proof.
rewrite /elog; case (exists a, a \in EU /\ x = exp g a) => [E | nE].
- by have /= := choicebP (fun a => a \in EU /\ x = exp g a) e E.
by rewrite choiceb_dfl ?e_EU // /#.
qed.

(* Does not seem to be used. *)
lemma dlist_EU n x xs :
  xs \in dlist (duniform (elems EU)) n => x \in xs => x \in EU.
proof.
move => xs_d x_xs; rewrite memE -supp_duniform.
move: xs_d; case (0 <= n) => Hn; 2: by rewrite supp_dlist0; smt().
by rewrite supp_dlist // => -[? /allP H]; exact: H.
qed.

lemma fcard_oflist (s : 'a list) : card (oflist s) <= size s.
proof.
elim: s => [|x s IHs]; 1: by rewrite -set0E fcards0.
by rewrite oflist_cons fcardU fcard1 /=; smt(fcard_ge0).
qed.

(* The CDH Game for Nominal Groups, with and without the factor for exponentiation *)
theory NCDH.

module type Adversary = {
  proc solve (gx gy : G) : G
}.

module Game (A:Adversary) = {
  proc main () : bool = {
  var x, y, r;

  x <$ duniform (elems EU);
  y <$ duniform (elems EU);
  r <@ A.solve(exp g x, exp g y);
  return (r = exp g (x * y));
  }
}.

module Game' (A:Adversary) = {
  proc main () : bool = {
  var x, y, r;

  x <$ duniform (elems EU);
  y <$ duniform (elems EU);
  r <@ A.solve(g ^ x, g ^ y);
  return (r = g ^ (x * y));
  }
}.

module B (A : Adversary) = {
  proc solve (gx gy : G) : G = {
    var r;

    r <@ A.solve(gx ^ inv f, gy ^ inv f);
    return (r ^ f);
  }
}.

(* If A wins against the "factor game", B(A) wins against the game w/o factors *)
(* Should we relate to Game' for the final lemma? *)
lemma unfactor (A <: Adversary) :
  equiv[Game(A).main ~ Game'(B(A)).main : ={glob A} ==> res{1} => res{2}].
proof.
proc; inline *; auto.
by call (: true) => //; auto; rewrite /exp => />; smt(mulA mulC powM pow_inv_f).
qed.

end NCDH.

op na    : {int | 0 <= na}    as na_ge0.
op nb    : {int | 0 <= nb}    as nb_ge0.
op q_oa  : {int | 0 <= q_oa}  as q_oa_ge0.
op q_ob  : {int | 0 <= q_ob}  as q_ob_ge0.
op q_ddh : {int | 1 <= q_ddh} as q_ddh_ge1.

module type CDH_RSR_Oracles = {
  proc oA  (i : int) : G
  proc oB  (j : int) : G
  proc oa  (j : int) : Z
  proc ob  (j : int) : Z
  proc ddh (m : G, i j : int) : bool
}.

module type CDH_RSR_Oracles_i = {
  include CDH_RSR_Oracles
  proc init () : unit
}.

module type CDH_RSR_Oracles_i_xy = {
  include CDH_RSR_Oracles
  proc init (x y : Z) : unit
}.

module type Adversary (O : CDH_RSR_Oracles) = {
  proc guess () : bool
}.

(* Counting wrapper for CDH_RSR Oracles *)
module Count (O : CDH_RSR_Oracles) = {
  var ca, cb, cddh : int

  proc init () = {
    ca   <- 0;
    cb   <- 0;
    cddh <- 0;
  }

  proc oa (i : int) = {
    var r;

    ca <- ca + 1;
    r <@ O.oa(i);
    return r;
  }

  proc ob (i : int) = {
    var r;

    cb <- cb + 1;
    r <@ O.ob(i);
    return r;
  }

  proc oA = O.oA
  proc oB = O.oB

  proc ddh (m, i, j) = {
    var r;

    cddh <- cddh + 1;
    r <@ O.ddh(m, i, j);
    return r;
  }
}.

(* The actual CDH_RSR game: initialize oracles and counters and
dispatach to adversary *)
module Game (O : CDH_RSR_Oracles_i) (A : Adversary) = {
  module O' = Count(O)

  proc main () = {
    var r;

    O.init();
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

module Game_xy (O : CDH_RSR_Oracles_i_xy) (A : Adversary) = {
  module O' = Count(O)

  proc main (x y : Z) = {
    var r;

    O.init(x, y);
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

(* The games G1 and G2 are the "real" and the "ideal" game defined in
cryptoprim.pdf *)
clone import FullRO as FROZ with
  type in_t    <- int,
  type out_t   <- Z,
  op dout      <- fun _ => dZ,
  type d_in_t  <- unit,
  type d_out_t <- bool.

clone FROZ.MkRO as RAZ.
clone FROZ.MkRO as RBZ.
module OAZ = RAZ.RO.
module OBZ = RBZ.RO.

module G1 : CDH_RSR_Oracles  = {
  proc init () = {
    OAZ.init();
    OBZ.init();
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) a <@ OAZ.get(i);
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) b <@ OBZ.get(j);
    return b;
  }

  proc oA (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) a <@ OAZ.get(i);
    return exp g a;
  }

  proc oB (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) b <@ OBZ.get(j);
    return exp g b;
  }

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OAZ.get(i);
      b <@ OBZ.get(j);
      r <- m = exp g (a * b);
    }
    return r;
  }
}.

module G2 : CDH_RSR_Oracles = {
  include G1 [oA, oB]
  var ca, cb : int list

  proc init () = {
    G1.init();
    ca <- [];
    cb <- [];
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      ca <- i :: ca;
      a <@ OAZ.get(i);
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      cb <- j :: cb;
      b <@ OBZ.get(j);
    }
    return b;
  }

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OAZ.get(i);
      b <@ OBZ.get(j);
      if (i \in ca \/ j \in cb) {
        r <- m = exp g (a * b);
      }
    }
    return r;
  }
}.

(* Intermediate games:
- G sets "bad" where G1 and G2 differ
- once "bad" has been set, G no longer logs queries to oa/ob *)
module G (OA : FROZ.RO, OB : FROZ.RO) : CDH_RSR_Oracles = {
  import var G2
  var bad : bool

  proc init () = {
    OA.init();
    OB.init();
    ca  <- [];
    cb  <- [];
    bad <- false;
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      ca <- i :: ca;
      a <@ OA.get(i);
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      cb <- j :: cb;
      b <@ OB.get(j);
    }
    return b;
  }

  proc oA (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) a <@ OA.get(i);
    return exp g a;
  }

  proc oB (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) b <@ OB.get(j);
    return exp g b;
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
        bad <- bad \/ t;
      }
    }
    return r;
  }
}.

(* G' behaves like G, but samples invertible exponents (i.e. from EU *)
clone import FullRO as FROEU with
  type in_t   <- int,
  type out_t  <- Z,
  op dout     <- fun _ => duniform (elems EU),
  type d_in_t <- unit,
  type d_out_t <- bool.

clone FROEU.MkRO as RAEU.
clone FROEU.MkRO as RBEU.
module OAEU = RAEU.RO.
module OBEU = RBEU.RO.

module G' = G(OAEU, OBEU).

clone import Split as FROEU_S with
  type in_t   <- int,
  type out_t  <- Z,
  op dout     <- fun _ => duniform (elems EU),
  type d_in_t <- Z * Z,
  type d_out_t <- bool.

(* We could do with only 2 oracles for sampling A in EU for our proofs but,
   with a view of having more meaningful names we do it with 3 oracles. *)

clone FROEU.MkRO as REU.
clone FROEU.MkRO as R0EU.
clone FROEU.MkRO as R1EU.
module OEU = REU.RO.
module O0EU = R0EU.RO.
module O1EU = R1EU.RO.

(* Proof outline:

1. |G1 - G2| = |G1b - G2b| <= G[bad]
2. G[bad] <= G'[bad] + "prob. of distinguishing dZ and duniform EU"
3. Define a game Gk that samples ia/ib and k \in [1..q_ddh] and show
   Stop if oa(i) or ob(j) gets logged where ia[i]/ib[j] is true
   G'[bad] <= q_ddh / ((1-pa)^q_oa * pa * (1 - pb)^q_ob * pb) Gk[ bad set at k-th call /\ !stop]
4. Define simulation S and an adversary B against the NCDH games
   Gk[ bad set at k-th call /\ !stop] <= S receives critical ddh call <= B wins NCDH game.
*)

(* Inner theory, parametric in the probability of inserting the NCDH problem *)
abstract theory Inner.

op pa, pb : real.
axiom pa_bound : 0%r < pa && if q_oa = 0 then pa <= 1%r else pa < 1%r.
axiom pb_bound : 0%r < pb && if q_ob = 0 then pb <= 1%r else pb < 1%r.

(* the "simulation", called "A" in cryptoprim.pdf :

We take gx and gy as parameters and use gx (rather than g) for
oA(i) when ia[i] = true. In order for the simulation to remain in sync
with the game G' (more precisely the intermediate game Gk' below), we
need to align the randomness for a and b by multiplying/dividing by x
(resp y) whenever ia[i] (resp ib[j]) is true. *)
module S = {
  import var G2
  var cddh, k : int
  var ia, ib  : bool list
  var gx, gy  : G
  var m_crit  : G

  proc init (gx' : G, gy' : G) = {
    ca   <- [];
    cb   <- [];
    cddh <- 0;
    k    <$ [1..q_ddh];
    ia   <$ dlist (dbiased pa) na;
    ib   <$ dlist (dbiased pb) nb;
    gx   <- gx';
    gy   <- gy';
    OAEU.init();
    OBEU.init();
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      if (! nth false ia i){
        ca <- i :: ca;
        a <@ OAEU.get(i);
      }
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      if (! nth false ib j){
        cb <- j :: cb;
        b <@ OBEU.get(j);
      }
    }
    return b;
  }

  proc oA (i : int) = {
    var a, ga;

    ga <- exp g e;
    if (0 <= i < na) {
      a <@ OAEU.get(i);
      ga <- if nth false ia i then gx ^ a else exp g a;
    }
    return ga;
  }

  proc oB (j : int) = {
    var b, gb;

    gb <- exp g e;
    if (0 <= j < nb) {
      b <@ OBEU.get(j);
      gb <- if nth false ib j then gy ^ b else exp g b;
    }
    return gb;
  }

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OAEU.get(i);
      b <@ OBEU.get(j);
      if (i \in ca \/ j \in cb) {
        if (i \in ca) {
          r <- m = (if nth false ib j then gy ^ b else exp g b) ^ a;
        }
        if (j \in cb) {
          r <- m = (if nth false ia i then gx ^ a else exp g a) ^ b;
        }
      } else {
          if (cddh = k) {
            m_crit <- m ^ (inv a * inv b);
        }
      }
    }
    return r;
  }
}.

module GameS (A : Adversary) = {
  module O' = Count(S)

  proc main(gx : G, gy : G) = {
    var r;

    S.init(gx, gy);
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

(* adversary against CDH problem for nominal groups *)
module B (A : Adversary) : NCDH.Adversary = {
  proc solve(gx gy : G) : G = {
    GameS(A).main(gx, gy);
    return S.m_crit;
  }
}.

clone import FullRO as FROG with
  type in_t   <- int,
  type out_t  <- G,
  op dout     <- fun _ => dmap (duniform (elems EU)) (exp g),
  type d_in_t <- unit,
  type d_out_t <- bool.

clone FROG.MkRO as R1G.
module O1G = R1G.RO.

op DELTA = (na + nb)%r * sdist dZ (duniform (elems EU)).

lemma dEU_ll : is_lossless (duniform (elems EU)).
proof. by smt(duniform_ll e_EU). qed.
hint exact random : dEU_ll.

lemma dG_ll : is_lossless (dmap (duniform (elems EU)) (exp g)).
proof. by smt(dEU_ll dmap_ll). qed.

section.

declare module A <: Adversary {G1, G2, G, S, Count,
                              OAEU, OBEU, OEU, O0EU, O1EU, O1G}.

declare axiom A_ll : forall (O <: CDH_RSR_Oracles{A}),
  islossless O.oA =>
  islossless O.oB =>
  islossless O.oa =>
  islossless O.ob =>
  islossless O.ddh =>
  islossless A(O).guess.

declare axiom A_bound : forall (O <: CDH_RSR_Oracles{A}),
  hoare [A(Count(O)).guess :
         Count.ca = 0 /\ Count.cb = 0 /\ Count.cddh = 0 ==>
         Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh].

local module G1b = {
  import var G2
  include var G(OAZ, OBZ) [- ddh]

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OAZ.get(i);
      b <@ OBZ.get(j);
      r <- m = exp g (a * b);
      bad <- bad \/ (r /\ ! (i \in ca \/ j \in cb));
    }
    return r;
  }
}.

local lemma G1G2_Gbad &m :
  `| Pr[Game(G1, A).main() @ &m : res] - Pr[Game(G2, A).main() @ &m : res] | <=
  Pr[Game(G(OAZ, OBZ), A).main() @ &m : G.bad].
proof.
(* Introduce bad events into G1 and G2 *)
have -> : Pr[Game(G1,  A).main() @ &m : res] =
          Pr[Game(G1b, A).main() @ &m : res].
- by byequiv => //; proc; inline *; sim.
have -> : Pr[Game(G2,          A).main() @ &m : res] =
          Pr[Game(G(OAZ, OBZ), A).main() @ &m : res].
- byequiv => //; proc; inline *.
  call (: ={OAZ.m, OBZ.m, G2.ca, G2.cb}); 1..4: (by sim); 2: by auto.
  by proc; inline *; sp; if; auto.
(* we can continue logging oa/ob queries once bad happens *)
byequiv (_ : ={glob A} ==> ={G.bad} /\ (! G.bad{2} => ={res})) : G.bad => //;
[proc; inline * | smt()].
call (_ : G.bad, ={OAZ.m, OBZ.m, G2.ca, G2.cb, G.bad}, ={G.bad});
  2..13: by (sim /> || (move => *; conseq />; islossless)).
- by exact: A_ll.
- proc; inline G1b.ddh G(OAZ, OBZ).ddh; sp.
  if => //; 2: by auto.
  wp; call (: ={OBZ.m}); 1: by sim.
  call (: ={OAZ.m}); 1: by sim.
  by auto => /> /#.
- move => *; proc.
  inline G1b.ddh; sp; if; auto.
  by conseq (: true); [smt() | islossless].
- move => *; proc.
  inline G(OAZ, OBZ).ddh; sp; if; auto.
  by conseq (: true); [smt() | islossless].
- by auto => /> /#.
qed.

(** Expressing the games G, G' and G'' as distinguishers for statistical distance *)

(* require import SDist. *)

local clone SDist.Dist as D with
  type a <- Z
  proof*.



local clone D.ROM as D1 with
  type in_t    <- int,
  op d1        <- dZ,
  op d2        <- duniform (elems EU),
  op N         <- na
proof* by smt(dZ_ll dEU_ll na_ge0).

local clone D.ROM as D2 with
  type in_t    <- int,
  op d1        <- dZ,
  op d2        <- duniform (elems EU),
  op N         <- nb
proof * by smt(dZ_ll dEU_ll nb_ge0).

local module DisA (O : FROZ.RO) = {
  module CG = Count(G(O, OBZ))

  proc distinguish () = {
    OBZ.init();
    CG.init();
    G2.ca <- [];
    G2.cb <- [];
    G.bad <- false;
    A(CG).guess();
    return G.bad;
  }
}.

local module DisB (O : FROZ.RO) = {
  module CG = Count(G(OAEU, O))

  proc distinguish () = {
    OAEU.init();
    CG.init();
    G2.ca <- [];
    G2.cb <- [];
    G.bad <- false;
    A(CG).guess();
    return G.bad;
  }
}.

local lemma G_G' &m :
  `| Pr[Game(G(OAZ, OBZ), A).main() @ &m : G.bad] -
     Pr[Game(G',          A).main() @ &m : G.bad] | <= DELTA.
proof.
rewrite /DELTA.
suff: `| Pr[Game(G(OAZ,  OBZ), A).main() @ &m : G.bad] -
         Pr[Game(G(OAEU, OBZ), A).main() @ &m : G.bad] | <=
      na%r * sdist dZ (duniform (elems EU)) /\
      `| Pr[Game(G(OAEU, OBZ),  A).main() @ &m : G.bad] -
         Pr[Game(G(OAEU, OBEU), A).main() @ &m : G.bad] | <=
      nb%r * sdist dZ (duniform (elems EU)) by smt().
split.
- have -> : Pr[Game(G(OAZ,  OBZ), A).main() @ &m : G.bad] =
            Pr[D1.R1.MainD(DisA, D1.R1.RO).distinguish() @ &m : res].
  + byequiv => //; proc; inline *; auto.
    call (: ={m}(OAZ, D1.R1.RO) /\ ={OBZ.m, G2.ca, G2.cb, G.bad}); 1..5: by sim.
    by auto.
  have -> : Pr[Game(G(OAEU, OBZ), A).main() @ &m : G.bad] =
            Pr[D1.R1.MainD(DisA, D1.R2.RO).distinguish() @ &m : res].
  + byequiv => //; proc; inline *; auto.
    call (: ={m}(OAEU, D1.R2.RO) /\ ={OBZ.m, G2.ca, G2.cb, G.bad}); 1..5: by sim.
    by auto.
  apply (D1.sdist_ROM DisA _ &m _) => // O. 
    by move => get_ll; islossless; apply (A_ll (Count(G(O, RBZ.RO)))); islossless.
  proc; inline *; auto.
  conseq (:_ ==> D1.Wrap.dom \subset rangeset 0 na) => [_ _ I Isub|].
  + apply (StdOrder.IntOrder.ler_trans (card (rangeset 0 na)));
    [exact subset_leq_fcard | by rewrite card_rangeset /=; smt(na_ge0)].
  call (: D1.Wrap.dom \subset rangeset 0 na) => //.
  + proc; inline *; sp; if; 2: (by auto); wp; call (: true); auto.
    smt(in_fsetU in_fset1 mem_rangeset).
  + proc; inline *; sp; if; by auto.
  + proc; inline *; sp; if; 2: (by auto); wp; call (: true); auto.
    smt(in_fsetU in_fset1 mem_rangeset).
  + proc; inline *; sp; if; by auto.
  + proc; inline *; sp; if; 2: (by auto); wp; rnd; wp.
    call (: true); auto; smt(in_fsetU in_fset1 mem_rangeset).
  + by inline *; auto; smt(in_fset0).
- have -> : Pr[Game(G(OAEU, OBZ), A).main() @ &m : G.bad] =
            Pr[D2.R1.MainD(DisB, D2.R1.RO).distinguish() @ &m : res].
  + byequiv => //; proc; inline *; auto.
    call (: ={m}(OBZ, D2.R1.RO) /\ ={OAEU.m, G2.ca, G2.cb, G.bad}); 1..5: by sim.
    by auto.
  have -> : Pr[Game(G(OAEU, OBEU), A).main() @ &m : G.bad] =
            Pr[D2.R1.MainD(DisB, D2.R2.RO).distinguish() @ &m : res].
  + byequiv => //; proc; inline *; auto.
    call (: ={m}(OBEU, D2.R2.RO) /\ ={OAEU.m, G2.ca, G2.cb, G.bad}); 1..5: by sim.
    by auto.
  apply (D2.sdist_ROM DisB _ &m _) => // O. 
    by move => get_ll; islossless; apply (A_ll (Count(G(OAEU,O)))); islossless.
  proc; inline*; auto.
  conseq (:_ ==> D2.Wrap.dom \subset rangeset 0 nb) => [_ _ I Isub|].
  + apply (StdOrder.IntOrder.ler_trans (card (rangeset 0 nb)));
    [exact subset_leq_fcard | by rewrite card_rangeset /=; smt(nb_ge0)].
  call (: D2.Wrap.dom \subset rangeset 0 nb) => //.
  + proc; inline *; sp; if; by auto.
  + proc; inline *; sp; if; 2: (by auto); wp; call (: true); auto.
    smt(in_fsetU in_fset1 mem_rangeset).
  + proc; inline *; sp; if; by auto.
  + proc; inline *; sp; if; 2: (by auto); wp; call (: true); auto.
    smt(in_fsetU in_fset1 mem_rangeset).
  + proc; inline *; sp; if; 2: (by auto); wp.
    call (: true); auto; smt(in_fsetU in_fset1 mem_rangeset).
  + by inline *; auto; smt(in_fset0).
qed.

local module Gk (OA : FROEU.RO, OB : FROEU.RO) : CDH_RSR_Oracles_i = {
  import var G2 G
  include var G(OA, OB) [oA, oB]
  var cddh, i_k, j_k, k : int
  var ia, ib            : bool list

  proc init () = {
    G(OA, OB).init();
    cddh  <- 0;
    i_k   <- -1;
    j_k   <- -1;
    k     <$ [1..q_ddh];
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      if (i <> i_k) {
        ca <- i :: ca;
        a <@ OA.get(i);
      }
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      if (j <> j_k) {
        cb <- j :: cb;
        b <@ OB.get(j);
      }
    }
    return b;
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

(* Same as Gk, but record number of ddh query that sets bad. *)
local module Gk_bad (OA : FROEU.RO, OB : FROEU.RO) : CDH_RSR_Oracles_i = {
  import var G2 G
  include var Gk(OA, OB) [oA, oB]
  var k_bad   : int
  var query_k : bool

  proc init () = {
    Gk(OA, OB).init();
    k_bad   <- -1;
    query_k <- false;
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      if (i <> i_k) {
        ca <- i :: ca;
        a <@ OA.get(i);
      } else {
        query_k <- true;
      }
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      if (j <> j_k) {
        cb <- j :: cb;
        b <@ OB.get(j);
      } else {
        query_k <- true;
      }
    }
    return b;
  }

  proc ddh(m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! bad) {
            bad <- true;
            k_bad <- cddh;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

op cs_all_false (bs : bool list) (il : int list) =
  (forall i, i \in il => ! nth false bs i).

op is_ok (bs : bool list) (il : int list) (i : int) =
  cs_all_false bs il /\ nth false bs i.

op nstop (ia ib : bool list) (ca cb : int list) =
  cs_all_false ia ca /\ cs_all_false ib cb.

(* should be an equality, but this suffices *)
local lemma Gk_Gk_bad &m :
  Pr[Game(Gk_bad(OAEU, OBEU), A).main() @ &m :
     Gk.k = Gk_bad.k_bad /\
     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k] <=
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k].
proof.
byequiv => //; proc; inline *; symmetry.
call (: G.bad /\ Gk.k <> Gk_bad.k_bad,

        ={OAEU.m, OBEU.m, G2.ca, G2.cb, G.bad} /\
        ={cddh, i_k, j_k, k}(Gk, Gk) /\
        (G.bad <=> Gk.k = Gk_bad.k_bad){2});
  try by (sim /> || (move => *; conseq />; islossless)).
- by exact A_ll.
- by proc; inline *; sp; if; auto => /#.
- move => {&m} &m; proc; inline *; sp; if; auto; smt(dEU_ll).
- by auto; smt(supp_dinter).
qed.

local lemma guess_bound &m :
  1%r / q_ddh%r * (1%r - pa) ^ q_oa * (1%r - pb) ^ q_ob * pa * pb *
  Pr[Game(G', A).main() @ &m : G.bad] <=
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k].
proof.
pose p := Pr[Game(G', A).main() @ &m : G.bad].
pose c := (1%r - pa) ^ q_oa * pa * (1%r - pb) ^ q_ob * pb.
apply (ler_trans _ _ _ _ (Gk_Gk_bad &m)).
byphoare (_ : glob A = (glob A){m} ==> _) => //.
proc; inline *; swap [10..11] 6; swap 9 6.
seq 14 : G.bad p (1%r / q_ddh%r * c) _ 0%r
         (size G2.ca <= q_oa /\ size G2.cb <= q_ob /\
          (G.bad => Gk_bad.k_bad \in [1..q_ddh] /\
                    0 <= Gk.i_k < na /\ 0 <= Gk.j_k < nb) /\
         ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb));
  4, 5: by auto; smt().
- conseq (: _ ==> Count.cddh = Gk.cddh /\  0 <= Gk.cddh /\
                  size G2.ca <= Count.ca /\ size G2.cb <= Count.cb /\
                  (G.bad => (Gk.cddh <= q_ddh => Gk_bad.k_bad \in [1..q_ddh]) /\
                            0 <= Gk.i_k < na /\ 0 <= Gk.j_k < nb) /\
                  ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb))
         (: _ ==> Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh);
  [ | smt () | seq 13 : (Count.ca = 0 /\ Count.cb = 0 /\ Count.cddh = 0) | ];
  auto; 1: by call (A_bound (Gk_bad(OAEU, OBEU))).
  call (: Count.cddh = Gk.cddh /\ 0 <= Gk.cddh /\
          size G2.ca <= Count.ca /\ size G2.cb <= Count.cb /\
          (G.bad => (Gk.cddh <= q_ddh => Gk_bad.k_bad \in [1..q_ddh]) /\
                    0 <= Gk.i_k < na /\ 0 <= Gk.j_k < nb) /\
          ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb));
    1, 2: (by proc; sp; if; [call (: true) | auto]); 4: by auto.
  + proc; inline Gk_bad(OAEU, OBEU).oa; sp; wp.
    by if; [if; [call (: true) | ] | ]; auto; smt().
  + proc; inline Gk_bad(OAEU, OBEU).ob; sp; wp.
    by if; [if; [call (: true) | ] | ]; auto; smt().
  + proc; inline Gk_bad(OAEU, OBEU).ddh; sp; wp; if; 2: by auto; smt().
    by auto; call (: true) => //; call (: true) => //; auto; smt(supp_dinter).
- call (: (glob A) = (glob A){m} /\ OAEU.m = empty /\ OBEU.m = empty /\
          G2.ca = [] /\ G2.cb = [] /\ G.bad = false /\
          Gk.i_k = -1 /\ Gk.j_k = -1 /\
          Gk_bad.query_k = false ==> G.bad); 2: by inline *; auto.
  bypr=> &m' gA; rewrite /p.
  byequiv (: ={glob A} /\ OAEU.m{2} = empty /\ OBEU.m{2} = empty /\
             G2.ca{2} = [] /\ G2.cb{2} = [] /\ G.bad{2} = false /\
             Gk.i_k{2} = -1 /\ Gk.j_k{2} = -1 /\
             Gk_bad.query_k{2} = false ==> _); [ | smt() | done].
  proc *; inline *; wp.
  call (: Gk_bad.query_k,

          ={OAEU.m, OBEU.m, G2.ca, G2.cb, G.bad} /\
          ((0 <= Gk.i_k < na \/ 0 <= Gk.j_k < nb) => G.bad){2},

          G.bad{2});
    2..7, 9, 12: (by move => *; proc; inline *; sp; if; auto; smt(dEU_ll)).
  + by exact A_ll.
  + by proc; inline *; sp; if; [ | if{2} | ]; auto; smt().
  + by move => *; proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll).
  + by proc; inline *; sp; if; [ | if{2} | ]; auto; smt().
  + by move => *; proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll).
  + by proc; inline *; sp; if; auto; smt().
  + by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
  + by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
  + by auto; smt().
- seq 1 : (Gk.k = Gk_bad.k_bad) (1%r / q_ddh%r) c _ 0%r
          (G.bad /\ size G2.ca <= q_oa /\ size G2.cb <= q_ob /\
           0 <= Gk.i_k && Gk.i_k < na /\ 0 <= Gk.j_k && Gk.j_k < nb /\
           ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb));
    1, 4, 5: by auto; smt().
  + rnd; skip => &m' /> *; rewrite (mu_eq _ _ (pred1 Gk_bad.k_bad{m'})) //.
    by rewrite dinter1E; smt (supp_dinter).
  + rewrite /c => {c p}; pose p := (fun b => b = false).
    pose IP := fun (cs : int list) (il : bool list) (n : int) =>
                 forall (i : int), i \in oflist cs `&` oflist (range 0 n) =>
                                     p (nth false il i).
    pose JP := fun (c : int) (il : bool list) (n : int) =>
                 forall (j : int), j \in fset1 c `&` oflist (range 0 n) =>
                                   ! p (nth false il j).
    have ? := pa_bound; have ? := pb_bound; have ? := na_ge0; have ? := nb_ge0.
    seq 1 : (is_ok Gk.ia G2.ca Gk.i_k)
            ((1%r - pa) ^ q_oa * pa) ((1%r - pb) ^ q_ob * pb) _ 0%r
            (G.bad /\ Gk.k = Gk_bad.k_bad /\ size G2.cb <= q_ob /\
             0 <= Gk.j_k && Gk.j_k < nb /\ ! (Gk.j_k \in G2.cb));
      1, 4, 5: by auto; smt().
    * rnd; skip => {&m} &m /> _ s_ca _ ik_ge0 ik_ltna _ _ ik_nca _.
      rewrite (mu_eq_support _ _ (fun (x : bool list) =>
                                    IP G2.ca{m} x na /\ JP Gk.i_k{m} x na));
        1: by move => ia /= /(supp_dlist_size _ _ _ na_ge0) size_ia;
              smt (fset1I in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_set2E //; 1: (by exact: dbiased_ll);
        1..3: smt(mem_oflist mem_range in_fsetI in_fset1).
      rewrite !dbiasedE /p /predC /= fset1I clamp_id 1: /#.
      rewrite mem_oflist mem_range ik_ge0 ik_ltna /= fcard1 expr1.
      apply ler_wpmul2r; 1: smt().
      apply ler_wiexpn2l; smt(fcard_ge0 fcard_oflist subsetIl subset_leq_fcard).
    * seq 1 : (is_ok Gk.ib G2.cb Gk.j_k)
              ((1%r - pb) ^ q_ob * pb) 1%r _ 0%r
              (G.bad /\ Gk.k = Gk_bad.k_bad /\ is_ok Gk.ia G2.ca Gk.i_k);
        1, 3..5: by auto; smt().
      rnd; skip => &m' /> _ s_cb jk_ge0 jk_ltnb jk_ncb _ _.
      rewrite (mu_eq_support _ _ (fun (x : bool list) =>
                                    IP G2.cb{m'} x nb /\ JP Gk.j_k{m'} x nb));
        1: by move => ia /= /(supp_dlist_size _ _ _ nb_ge0) size_ia;
              smt (fset1I in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_set2E //; 1: (by exact: dbiased_ll);
        1..3: smt(mem_oflist mem_range in_fsetI in_fset1).
      rewrite !dbiasedE /p /predC /= fset1I clamp_id 1: /#.
      rewrite mem_oflist mem_range jk_ge0 jk_ltnb /= fcard1 expr1.
      apply ler_wpmul2r; 1: smt().
      apply ler_wiexpn2l; smt(fcard_ge0 fcard_oflist subsetIl subset_leq_fcard).
qed.

(* We want to express Gk(OAEU,OBEU) as a distinguisher applied to
Ok(OAEU) and, and then change the implementation of Ok to Okx, where
we rerandomize with respect to some value x (Ok_Okx). We then expesss
the resulting game as a distinguisher for Ok(OBEU) and use Ok_Okx
again to rerandomize OBEU with respect to some value y.  Thus, we have
the following chain of game equivalences :

  Gk(OAEU,OBEU) 
~ MainDO(Dk, Ok(OAEU))
~ MainDO(Dk, Okx(OAEU)) *Ok_Okx 
~ Gkx(OA,OB)
~ MainDO(Dkx, Ok(OBEU))   
~ MainDO(Dkx, Okx(OBEU)) *Ok_Okx 
~ Gkxy(OAEU,OBEU) 
*)

module type O = {
  proc get_cs  ()        : int list
  proc set_bad (i : int) : unit
  proc oZ      (i : int) : Z
  proc oG      (i : int) : G
}.

module type O_i = {
  include O
  proc init (n : int, il : bool list, x : Z) : unit
}.

module type DistinguisherO_i (O : O) = {
  proc init   (x y : Z) : unit      {}
  proc get_n  ()        : int       {}
  proc get_il ()        : bool list {}
  proc get_x  ()        : Z         {}
  proc main   ()        : bool
}.

module D_i_D (D : DistinguisherO_i) (O : O) = {
  proc main = D(O).main
}.

module MainDO (D : DistinguisherO_i) (O : O_i) = {
  module D' = D(O)

  proc init (x' y' : Z) = {
    var il, n, x;

    D'.init(x', y');
    il <@ D'.get_il();
    n  <@ D'.get_n();
    x  <@ D'.get_x();
    O.init(n, il, x);
  }

  proc main (x y : Z) = {
    var r;

    init(x, y);
    r  <@ D(O).main();
    return r;
  }
}.


local module Ok (O : FROEU.RO) : O_i = {
  var n   : int
  var cs  : int list
  var bad : bool
  var ik  : int
  var il  : bool list
  var x   : Z

  proc init (n' : int, il' : bool list, x' : Z) = {
    n   <- n';
    il  <- il';
    x   <- x';
    cs  <- [];
    bad <- false;
    ik  <- -1;
    O.init();
  }

  proc get_cs () = {
    return cs;
  }

  proc set_bad (i : int) = {
    if (0 <= i < n) {
      if (! bad) {
        bad <- true;
        ik  <- i;
      }
    }
  }

  proc oZ (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) {
      if (i <> ik) {
        cs <- i :: cs;
        a <@ O.get(i);
      }
    }
    return a;
  }

  proc oG (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) a <@ O.get(i);
    return exp g a;
  }
}.

(* This is too lengthy and should be automated as
   using RO_split is more tedious (due to having to define the various modules)
   than redoing the same proof in the precise context.
   Indeed Okt is about the same size as Ok2.
   One would then need to add two lemmas to relate to a distinguisher.
   Both of them would be about as short/long as Okt_Ok2.
*)

(*
local module Okt (O : FROEUt.ROt) : O_i = {
  import var G2 Gk Ok

  proc init (n' : int, il' : bool list, x' : Z) = {
    n   <- n';
    il  <- il';
    x   <- x';
    cs  <- [];
    bad <- false;
    ik  <- -1;
    O.init(nth false il);
  }

  proc get_cs () = {
    return cs;
  }

  proc set_bad (i : int) = {
    if (0 <= i < n) {
      if (! bad) {
        bad <- true;
        ik  <- i;
      }
    }
  }

  proc oZ (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) {
      if (i <> ik) {
        cs <- i :: cs;
        a <@ O.get(i);
      }
    }
    return a;
  }

  proc oG (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) a <@ O.get(i);
    return exp g a;
  }
}.
*)

local module Ok2 (O0 : FROEU.RO, O1 : FROEU.RO) : O_i = {
  import var Ok

  proc init (n' : int, il' : bool list, x' : Z) = {
    n   <- n';
    il  <- il';
    x   <- x';
    cs  <- [];
    bad <- false;
    ik  <- -1;
    O0.init();
    O1.init();
  }

  proc get_cs () = {
    return cs;
  }

  proc set_bad (i : int) = {
    if (0 <= i < n) {
      if (! bad) {
        bad <- true;
        ik  <- i;
      }
    }
  }

  proc oZ (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) {
      if (i <> ik) {
        cs <- i :: cs;
        if (nth false il i) a <@ O1.get(i);
        else                a <@ O0.get(i);
      }
    }
    return a;
  }

  proc oG (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) {
      if (nth false il i) a <@ O1.get(i);
      else                a <@ O0.get(i);
    }
    return exp g a;
  }
}.

op splitO (m m0 m1 : (int, Z) fmap) (t : int -> bool) =
  m = union_map m0 m1 /\
  (forall x, x \in m1 =>   t x) /\
  (forall x, x \in m0 => ! t x).

local equiv Ok_Ok2 &m (D <: DistinguisherO_i {OEU, O0EU, O1EU, Ok}) :
  MainDO(D, Ok(OEU)).main ~ MainDO(D, Ok2(O0EU, O1EU)).main :
  ={arg, glob D} ==>
  ={glob D} /\ ((is_ok Ok.il Ok.cs Ok.ik){1} <=> (is_ok Ok.il Ok.cs Ok.ik){2}).
proof.
proc *; inline *; wp.
call (: ={glob Ok} /\ splitO OEU.m{1} O0EU.m{2} O1EU.m{2} (nth false Ok.il){2}).
- by proc; auto.
- by proc; auto.
- proc; inline *; sp; if; [ | if; [ | sp; if{2} | ] | ]; auto.
  + by smt(get_setE mergeE set_union_map_r).
  + by smt(get_setE mergeE set_union_map_l).
- proc; inline *; sp; if; 1, 3: by auto.
  if{2}; auto; 1: smt(get_setE mem_set mergeE set_union_map_r).
  by smt(get_setE mem_set mergeE set_union_map_l).
- wp; call (: true); call (: true); call (: true); call (: true).
  by auto; smt(mem_empty merge_empty).
qed.

local module Ok2X (O0 : FROEU.RO, O1 : FROG.RO) : O_i = {
  import var Ok

  proc init (n' : int, il' : bool list, x' : Z) = {
    n   <- n';
    il  <- il';
    x   <- x';
    cs  <- [];
    bad <- false;
    ik  <- -1;
    O0.init();
    O1.init();
  }

  proc get_cs () = {
    return cs;
  }

  proc set_bad (i : int) = {
    if (0 <= i < n) {
      if (! bad) {
        bad <- true;
        ik  <- i;
      }
    }
  }

  proc oZ (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) {
      if (! nth false il i) {
        cs <- i :: cs;
        a <@ O0.get(i);
      }
    }
    return a;
  }

  proc oG (i : int) = {
    var a, ga;

    a <- e;
    ga <- exp g a;
    if (0 <= i < n) {
      if (nth false il i) { ga <@ O1.get(i); }
      else                { a  <@ O0.get(i); ga <- exp g a; }
    }
    return ga;
  }
}.

(* The up to bad reasoning that results in having a => and not a <=>
   in the postcondition of the following equiv statement. *)
local lemma Ok2_Ok2X &m (D <: DistinguisherO_i {O0EU, O1EU, O1G, Ok}) :
  (forall (O <: O{D}),
     islossless O.get_cs => islossless O.set_bad =>
     islossless O.oZ => islossless O.oG =>
     islossless D(O).main) =>
  equiv[MainDO(D, Ok2(O0EU, O1EU)).main ~ MainDO(D, Ok2X(O0EU, O1G)).main :
        ={arg, glob D} ==>
        (is_ok Ok.il Ok.cs Ok.ik){1} => (is_ok Ok.il Ok.cs Ok.ik){2} /\
                                        ={glob D}].
proof.
move => D_ll; proc *; inline *; wp; symmetry.
call (: ! (cs_all_false Ok.il Ok.cs) \/
        (Ok.bad /\ ! nth false Ok.il Ok.ik),

        ={glob Ok, O0EU.m} /\ O1G.m{1} = map (fun _ => exp g) O1EU.m{2} /\
        (forall r, r \in O1EU.m => oget (O1EU.m.[r]) \in EU){2} /\
        (Ok.bad <=> 0 <= Ok.ik < Ok.n){2}).
- by proc; auto.
- by move => *; proc; auto.
- by move => *; proc; auto.
- by proc; auto.
- by move => *; proc; auto.
- by move => *; proc; auto => /#.
- proc; inline *; sp; if; [auto | sp | auto].
  if{2}; if{1}; try (sp; if{2}); auto; smt().
- by move => *; proc; inline *; sp; if; [sp; if | ]; auto; smt(dEU_ll).
- move => *; proc; inline *; sp.
  by if; [sp; if; [sp; if | ] | ]; auto; smt(dEU_ll).
- proc; inline *; sp; if; [ | if | ]; 1, 2, 4, 5: by auto.
  seq 2 2 : (={x} /\ r{1} = exp g r{2} /\ r{2} \in EU /\
             ((cs_all_false Ok.il Ok.cs) \/
             (0 <= Ok.ik < Ok.n /\ ! nth false Ok.il Ok.ik)){2} /\
             ={glob Ok, O0EU.m} /\ O1G.m{1} = map (fun _ => exp g) O1EU.m{2} /\
             (forall r, r \in O1EU.m => oget (O1EU.m.[r]) \in EU){2} /\
             (Ok.bad <=> 0 <= Ok.ik < Ok.n){2});
    2: by if; auto; smt(get_setE get_set_sameE mapE map_set).
  rnd elog (exp g); auto => /> *.
  split => [|_]; 1: smt(expK supp_dmap supp_duniform).
  split => [|_]; 2: smt(expK supp_dmap supp_duniform).
  smt(dmap1E exp_inj mu_eq_support supp_duniform).
- by move => *; proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll dmap_ll).
- by move => *; proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll).
- wp; call (: true); call (: true); call (: true); call (: true).
  by auto; smt(mem_empty map_empty).
qed.

local module Ok2x (O0 : FROEU.RO, O1 : FROEU.RO) : O_i = {
  import var Ok
  include var Ok2(O0, O1) [- oZ, oG]

  proc oZ (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) {
      if (! nth false il i) {
        cs <- i :: cs;
        a <@ O0.get(i);
      }
    }
    return a;
  }

  proc oG (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) {
      if (nth false il i) { a <@ O1.get(i); a <- x * a; }
      else                  a <@ O0.get(i);
    }
    return exp g a;
  }
}.

lemma exp_exp_x x :
  x \in EU =>
  dmap (duniform (elems EU)) (exp g) =
  dmap (duniform (elems EU)) (fun z => exp g (x * z)).
proof.
move => x_EU; rewrite !dmap_duniform; 1, 2: smt(exp_inj exp_inj').
by apply eq_duniformP; move: (img_exp _ x_EU); smt(mem_oflist).
qed.

local lemma Ok2X_Ok2x &m x y (D <: DistinguisherO_i {O0EU, O1EU, O1G, Ok}) :
  x \in EU =>
  y \in EU =>
  hoare [MainDO(D, Ok2x(O0EU, O1EU)).init :
         fst arg \in EU /\ snd arg \in EU ==> Ok.x \in EU] =>
  equiv[MainDO(D, Ok2X(O0EU, O1G)).main ~ MainDO(D, Ok2x(O0EU, O1EU)).main :
        ={arg, glob D} /\ arg{1} = (x, y) ==>
        ={glob D} /\
        ((is_ok Ok.il Ok.cs Ok.ik){1} <=> (is_ok Ok.il Ok.cs Ok.ik){2})].
proof.
move => x_EU y_EU initP; proc *.
inline MainDO(D, Ok2X(O0EU, O1G)).main MainDO(D, Ok2x(O0EU, O1EU)).main; wp.
call (: ={glob Ok, O0EU.m} /\ Ok.x{1} \in EU /\
        O1G.m{1} = (map (fun _ z => exp g (Ok.x * z)) O1EU.m){2}).
- by proc; auto.
- by proc; auto.
- by proc; inline *; sp; if; [ | if | ]; auto => />.
- proc; inline *; sp; if; [ | if; [ | sp | ] | ]; 1, 2, 4, 5: by auto.
  seq 1 1 : (={x} /\ r{1} = exp g (Ok.x * r){2} /\
             ={glob Ok, O0EU.m} /\ Ok.x{1} \in EU /\
             O1G.m{1} = map (fun _ z => exp g (Ok.x{2} * z)) O1EU.m{2});
    2: by if; auto; smt(get_setE get_set_sameE mapE map_set).
  transitivity{1} { r <$ dmap (duniform (elems EU))
                              (fun z => exp g (Ok.x * z)); }

                  (={glob Ok, O0EU.m, O1G.m, x} /\ Ok.x{1} \in EU ==>
                   ={glob Ok, O0EU.m, O1G.m, x, r} /\ Ok.x{1} \in EU)

                  (={glob Ok, O0EU.m, x} /\ Ok.x{1} \in EU /\
                   O1G.m{1} = map (fun _ z => exp g (Ok.x{2} * z)) O1EU.m{2} ==>
                   r{1} = exp g (Ok.x{2} * r{2}) /\
                   ={glob Ok, O0EU.m, x} /\ Ok.x{1} \in EU /\
                   O1G.m{1} = map (fun _ z => exp g (Ok.x{2} * z)) O1EU.m{2});
  [smt() | done | by auto => /> &2 *; rewrite (exp_exp_x Ok.x{2}); smt() | ].
  rnd (elogr Ok.x{2}) (fun z => exp g (Ok.x{2} * z)); auto => /> *.
  split => [|_]; 1: smt(exprK supp_dmap supp_duniform).
  split => [*|_ r /supp_dmap [rx [/supp_duniform ? -> /=]]];
    2: smt(exprK memE supp_duniform).
  by rewrite dmap1E; smt(exp_inj' mu_eq_support supp_duniform).
- conseq (: ={arg, glob D} ==>
            ={glob D, glob Ok, O0EU.m} /\
            O1G.m{1} = (map (fun _ z => exp g (Ok.x * z)) O1EU.m){2})
         (: true ==> true) (: arg = (x, y) ==> Ok.x \in EU);
  [by auto | by auto | by auto | by call initP; auto | inline *; wp].
  call (: true); call (: true); call (: true); call (: true).
  by auto; smt(map_empty).
qed.

local module Okx (O : FROEU.RO) : O_i = {
  include var Ok(O) [- oZ, oG]

  proc oZ (i : int) = {
    var a;

    a <- e;
    if (0 <= i < n) {
      if (! nth false il i) {
        cs <- i :: cs;
        a <@ O.get(i);
      }
    }
    return a;
  }

  proc oG (i : int) = {
    var a;

    a  <- if (nth false il i) then inv x * e else e;
    if (0 <= i < n) a <@ O.get(i);
    return (exp g (if (nth false il i) then x * a else a));
  }
}.

local lemma Ok2x_Okx &m x y (D <: DistinguisherO_i {OEU, O0EU, O1EU, Ok}) :
  x \in EU =>
  y \in EU =>
  hoare [MainDO(D, Ok2x(O0EU, O1EU)).init :
         fst arg \in EU /\ snd arg \in EU ==> Ok.x \in EU] =>
  equiv[MainDO(D, Ok2x(O0EU, O1EU)).main ~ MainDO(D, Okx(OEU)).main :
        ={arg, glob D} /\ arg{1} = (x, y) ==>
        ={glob D} /\
        ((is_ok Ok.il Ok.cs Ok.ik){1} <=> (is_ok Ok.il Ok.cs Ok.ik){2})].
proof.
move => x_EU y_EU initP; proc *.
inline MainDO(D, Ok2x(O0EU, O1EU)).main MainDO(D, Okx(OEU)).main; wp.
call (: Ok.x{1} \in EU /\ ={glob Ok} /\
        splitO OEU.m{2} O0EU.m{1} O1EU.m{1} (nth false Ok.il){1}).
- by proc; auto.
- by proc; auto.
- proc; inline *; sp; if; [ | if | ]; 1, 2, 4, 5: by auto.
  by auto => />; smt(get_setE mergeE set_union_map_l).
- proc; inline *; sp; if; 1, 3: by auto; smt(exp_inv mulA).
  if{1}; auto; 1: smt(get_setE mem_set mergeE set_union_map_r).
  by smt(get_setE mem_set mergeE set_union_map_l).
- conseq (: ={arg, glob D} ==>
            ={glob D, glob Ok} /\
            splitO OEU.m{2} O0EU.m{1} O1EU.m{1} (nth false Ok.il){1})
         (: arg = (x, y) ==> Ok.x \in EU) (: _ ==> _);
  [by auto | by call initP; auto | by auto | inline *].
  wp; call (: true); call (: true); call (: true); call (: true).
  by auto; smt(mem_empty merge_empty).
qed.

local lemma Ok_Okx &m x y (D <: DistinguisherO_i {OEU, O0EU, O1EU, O1G, Ok}) :
  x \in EU =>
  y \in EU =>
  (forall (O <: O{D}),
     islossless O.get_cs => islossless O.set_bad =>
     islossless O.oZ => islossless O.oG =>
     islossless D(O).main) =>
  hoare [MainDO(D, Ok2x(O0EU, O1EU)).init :
         fst arg \in EU /\ snd arg \in EU ==> Ok.x \in EU] =>
  equiv [MainDO(D, Ok(OEU)).main ~ MainDO(D, Okx(OEU)).main :
        ={arg, glob D} /\ arg{1} = (x, y) ==>
        (is_ok Ok.il Ok.cs Ok.ik){1} => (is_ok Ok.il Ok.cs Ok.ik){2} /\
                                        ={glob D}].
proof.
move => x_EU y_EU D_ll initP.
transitivity MainDO(D, Ok2(O0EU, O1EU)).main

             (={arg, glob D} ==>
              ={glob D} /\
              ((is_ok Ok.il Ok.cs Ok.ik){1} <=> (is_ok Ok.il Ok.cs Ok.ik){2}))

             (={arg, glob D} /\ arg{1} = (x, y) ==>
              (is_ok Ok.il Ok.cs Ok.ik){1} => (is_ok Ok.il Ok.cs Ok.ik){2} /\
                                              ={glob D});
  1, 2: smt(); 1: by exact (Ok_Ok2 &m D).
transitivity MainDO(D, Ok2X(O0EU, O1G)).main

             (={arg, glob D} ==>
              (is_ok Ok.il Ok.cs Ok.ik){1} => (is_ok Ok.il Ok.cs Ok.ik){2} /\
                                              ={glob D})

             (={arg, glob D} /\ arg{1} = (x, y) ==>
              ={glob D} /\
              ((is_ok Ok.il Ok.cs Ok.ik){1} <=> (is_ok Ok.il Ok.cs Ok.ik){2}));
  1, 2: smt(); 1: by exact (Ok2_Ok2X &m D D_ll).
transitivity MainDO(D, Ok2x(O0EU, O1EU)).main

             (={arg, glob D} /\ arg{1} = (x, y) ==>
              ={glob D} /\
              ((is_ok Ok.il Ok.cs Ok.ik){1} <=> (is_ok Ok.il Ok.cs Ok.ik){2}))

             (={arg, glob D} /\ arg{1} = (x, y) ==>
              ={glob D} /\
              ((is_ok Ok.il Ok.cs Ok.ik){1} <=> (is_ok Ok.il Ok.cs Ok.ik){2}));
  1, 2: smt(); 1: by exact (Ok2X_Ok2x &m x y D x_EU y_EU initP).
by exact (Ok2x_Okx &m x y D x_EU y_EU initP).
qed.

local module GkD (OA : O, OB : FROEU.RO) = {
  import var G2 G Gk
  var x, y : Z

  proc init_var (x' y' : Z) = {
    ca    <- [];
    cb    <- [];
    bad   <- false;
    cddh  <- 0;
    i_k   <- -1;
    j_k   <- -1;
    k     <$ [1..q_ddh];
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
    x     <- x';
    y     <- y';
  }

  proc get_n () = {
    return na;
  }

  proc get_il () = {
    return ia;
  }

  proc get_x () = {
    return x;
  }

  proc oa = OA.oZ

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      if (j <> j_k) {
        cb <- j :: cb;
        b <@ OB.get(j);
      }
    }
    return b;
  }

  proc oA = OA.oG

  proc oB (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) b <@ OB.get(j);
    return exp g b;
  }

  proc ddh (m, i, j) = {
    var a, b, ca, r, t;

    a <- g;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a  <@ OA.oG(i);
      b  <@ OB.get(j);
      ca <@ OA.get_cs();
      t <- m = a ^ b;
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
            OA.set_bad(i);
        }
      }
    }
    return r;
  }
}.

local module Dk (OA : O) = {
  module O  = GkD(OA, OBEU)
  module CO = Count(O)

  proc init (x y : Z) = {
    O.init_var(x, y);
    OBEU.init();
  }

  proc get_n = O.get_n
  proc get_il = O.get_il
  proc get_x = O.get_x

  proc main () = {
    var r;

    CO.init();
    r <@ A(Count(CO)).guess();
    return r;
  }
}.

local lemma Dk_ll (O <: O{Dk}) :
  islossless O.get_cs =>
  islossless O.set_bad =>
  islossless O.oZ =>
  islossless O.oG =>
  islossless Dk(O).main.
proof.
move => get_cs_ll set_bad_ll oZ_ll oG_ll; proc; inline *; call (: true); auto.
- by exact A_ll.
- by proc; inline *; sp; if; auto; smt(dEU_ll).
- by proc; inline *; wp; call (oZ_ll); auto.
- by proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll).
- proc; inline *; sp; if; 2: by auto; smt(dEU_ll).
  seq 7 : true; auto; 2: by if; [ | if]; auto; call set_bad_ll; auto.
  by swap 1 2; call (get_cs_ll); wp; call (oG_ll); auto; smt(dEU_ll).
qed.

local lemma Dk_initP :
  hoare [MainDO(Dk, Ok2x(O0EU, O1EU)).init :
         fst arg \in EU /\ snd arg \in EU ==> Ok.x \in EU].
proof. by proc; inline *; auto. qed.

local module Gkx (OA : FROEU.RO, OB : FROEU.RO) : CDH_RSR_Oracles_i_xy = {
  import var G2 G Gk
  include var Gk(OA, OB) [ob, oB]
  var x, y : Z

  proc init (x' y' : Z) = {
    Gk(OA, OB).init();
    x <- x';
    y <- y';
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      if (! nth false ia i) {
        ca <- i :: ca;
        a <@ OA.get(i);
      }
    }
    return a;
  }

  proc oA(i : int) = {
    var a;

    a  <- if (nth false ia i) then inv x * e else e;
    if (0 <= i < na) a <@ OA.get(i);
    return (exp g (if (nth false ia i) then x * a else a));
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g ((if (nth false ia i) then x * a else a) * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

local lemma Gk_Gkx &m x y :
  x \in EU =>
  y \in EU =>
  Pr[Game   (Gk (OAEU, OBEU), A).main(    ) @ &m :
     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k] <=
  Pr[Game_xy(Gkx(OAEU, OBEU), A).main(x, y) @ &m :
     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k].
proof.
move => x_EU y_EU.
have -> :   Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
               G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k] =
            Pr[MainDO(Dk, Ok(OEU)).main(x, y) @ &m :
               G.bad /\ is_ok Ok.il Ok.cs Ok.ik /\ is_ok Gk.ib G2.cb Gk.j_k].
- byequiv => //; proc; inline *; wp.
  call (: ={OBEU.m, G2.cb, G.bad} /\ ={m}(OAEU, OEU) /\
          ={cddh, j_k, k, ia, ib}(Gk, Gk) /\
          G2.ca{1} = Ok.cs{2} /\ Gk.i_k{1} = Ok.ik{2} /\ Gk.ia{1} = Ok.il{2} /\
          (G.bad = Ok.bad /\ Ok.n = na){2});
    1, 2, 4: (by proc; inline *; sp; if; try if; auto); 3: by auto.
  + by proc; inline *; sp; if; [ | if | ]; auto; smt().
  + proc; inline Gk(OAEU, OBEU).ddh Count(GkD(Ok(OEU), OBEU)).ddh.
    inline GkD(Ok(OEU), OBEU).ddh Ok(OEU).get_cs.
    sp; if; 1, 3: by auto.
    seq 3 4 : (={OBEU.m, G2.cb, G.bad, t} /\ ={m}(OAEU, OEU) /\
               ={cddh, j_k, k, ia, ib}(Gk, Gk) /\
               G2.ca{1} = Ok.cs{2} /\ Gk.i_k{1} = Ok.ik{2} /\
               Gk.ia{1} = Ok.il{2} /\
               (G.bad = Ok.bad /\ Ok.n = na){2} /\
               i0{1} = i1{2} /\ j0{1} = j1{2} /\ r0{1} = r1{2} /\
               G2.ca{1} = ca{2} /\ 0 <= i0{1} < na);
      2: by inline *; auto => />.
    wp; call (: ={OBEU.m}); auto.
    by inline *; sp; rcondt{2} 1; auto; smt(expM).
apply (ler_trans (Pr[MainDO(Dk, Okx(OEU)).main(x, y) @ &m :
                     G.bad /\ is_ok Ok.il Ok.cs Ok.ik /\
                              is_ok Gk.ib G2.cb Gk.j_k])).
byequiv (: ={arg, glob Dk} /\ arg{1} = (x, y) ==> _) => //.
conseq (Ok_Okx &m x y Dk x_EU y_EU Dk_ll Dk_initP); smt().
byequiv (: ={glob A, x, y} /\ fst arg{1} = x /\ snd arg{1} = y ==> _) => //.
proc; inline *; wp.
call (: ={OBEU.m, G2.cb, G.bad} /\ ={m}(OEU, OAEU) /\
        ={cddh, j_k, k, ia, ib}(Gk, Gk) /\
        Ok.cs{1} = G2.ca{2} /\ Ok.ik{1} = Gk.i_k{2} /\
        Ok.il{1} = Gk.ia{2} /\ Ok.x{1} = Gkx.x{2} /\
        (G.bad = Ok.bad /\ Ok.n = na){1});
  1..4: (by proc; inline *; sp; if; try if; auto); 2: by auto.
- proc; inline Gkx(OAEU, OBEU).ddh Count(GkD(Okx(OEU), OBEU)).ddh.
  inline GkD(Okx(OEU), OBEU).ddh Ok(OEU).get_cs.
  sp; if; 1, 3: by auto.
  seq 4 3 : (={OBEU.m, G2.cb, G.bad, t} /\ ={m}(OEU, OAEU) /\
             ={cddh, j_k, k, ia, ib}(Gk, Gk) /\
             Ok.cs{1} = G2.ca{2} /\ Ok.ik{1} = Gk.i_k{2} /\
             Ok.il{1} = Gk.ia{2} /\ Ok.x{1} = Gkx.x{2} /\
             (G.bad = Ok.bad /\ Ok.n = na){1} /\
             i1{1} = i0{2} /\ j1{1} = j0{2} /\ r1{1} = r0{2} /\
             ca{1} = G2.ca{2} /\ 0 <= i1{1} < na); 2: by inline *; auto => />.
  wp; call (: ={OBEU.m}); auto.
  by inline *; sp; rcondt{1} 1; auto; smt(expM).
qed.

local module GkxD (OA : FROEU.RO, OB : O) = {
  import var G2 G Gk
  var x, y : Z

  proc init_var (x' y' : Z) = {
    ca    <- [];
    cb    <- [];
    bad   <- false;
    cddh  <- 0;
    i_k   <- -1;
    j_k   <- -1;
    k     <$ [1..q_ddh];
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
    x     <- x';
    y     <- y';
  }

  proc get_n () = {
    return nb;
  }

  proc get_il () = {
    return ib;
  }

  proc get_x () = {
    return y;
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      if (! nth false ia i) {
        ca <- i :: ca;
        a <@ OA.get(i);
      }
    }
    return a;
  }

  proc ob = OB.oZ

  proc oA(i : int) = {
    var a;

    a  <- if (nth false ia i) then inv x * e else e;
    if (0 <= i < na) a <@ OA.get(i);
    return (exp g (if (nth false ia i) then x * a else a));
  }

  proc oB = OB.oG

  proc ddh (m, i, j) = {
    var a, b, cb, r, t;

    a <- e;
    b <- g;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a  <@ OA.get(i);
      b  <@ OB.oG(j);
      cb <@ OB.get_cs();
      t <- m = b ^ (if (nth false ia i) then x * a else a);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
            OB.set_bad(j);
        }
      }
    }
    return r;
  }
}.

local module Dkx (OB : O) = {
  module O  = GkxD(OAEU, OB)
  module CO = Count(O)

  proc init (x y : Z) = {
    O.init_var(x, y);
    OAEU.init();
  }

  proc get_n = O.get_n
  proc get_il = O.get_il
  proc get_x = O.get_x

  proc main () = {
    var r;

    CO.init();
    r <@ A(Count(CO)).guess();
    return r;
  }
}.

local lemma Dkx_ll (O <: O{Dkx}) :
  islossless O.get_cs =>
  islossless O.set_bad =>
  islossless O.oZ =>
  islossless O.oG =>
  islossless Dkx(O).main.
proof.
move => get_cs_ll set_bad_ll oZ_ll oG_ll; proc; inline *; call (: true); auto.
- by exact A_ll.
- by proc; inline *; sp; if; auto; smt(dEU_ll).
- by proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll).
- by proc; inline *; wp; call (oZ_ll); auto.
- proc; inline *; sp; if; 2: by auto; smt(dEU_ll).
  seq 7 : true; auto; 2: by if; [ | if]; auto; call set_bad_ll; auto.
  by call (get_cs_ll); wp; call (oG_ll); auto; smt(dEU_ll).
qed.

local lemma Dkx_initP :
  hoare [MainDO(Dkx, Ok2x(O0EU, O1EU)).init :
         fst arg \in EU /\ snd arg \in EU ==> Ok.x \in EU].
proof. by proc; inline *; auto. qed.

local module Gkxy (OA : FROEU.RO, OB : FROEU.RO) : CDH_RSR_Oracles_i_xy = {
  import var G2 G Gk GkD
  include var Gkx(OA, OB) [- ob, oB, ddh]

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      if (! nth false ib j) {
        cb <- j :: cb;
        b <@ OB.get(j);
      }
    }
    return b;
  }

  proc oB(j : int) = {
    var b;

    b  <- if (nth false ib j) then inv y * e else e;
    if (0 <= j < nb) {
      b <@ OB.get(j);
    }
    return (exp g (if (nth false ib j) then y * b else b));
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g ((if (nth false ia i) then x * a else a) *
                      (if (nth false ib j) then y * b else b));
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

local lemma Gkx_Gkxy &m x y :
  x \in EU =>
  y \in EU =>
  Pr[Game_xy(Gkx (OAEU, OBEU), A).main(x, y) @ &m :
     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k] <=
  Pr[Game_xy(Gkxy(OAEU, OBEU), A).main(x, y) @ &m :
     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k].
proof.
move => x_EU y_EU.
have -> :   Pr[Game_xy(Gkx(OAEU, OBEU), A).main(x, y) @ &m :
               G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k] =
            Pr[MainDO(Dkx, Ok(OEU)).main(x, y) @ &m :
               G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Ok.il Ok.cs Ok.ik].
- byequiv => //; proc; inline *; wp.
  call (: ={OAEU.m, G2.ca, G.bad} /\ ={m}(OBEU, OEU) /\
          ={cddh, i_k, k, ia, ib}(Gk, Gk) /\ ={x}(Gkx, GkxD) /\
          G2.cb{1} = Ok.cs{2} /\ Gk.j_k{1} = Ok.ik{2} /\ Gk.ib{1} = Ok.il{2} /\
          (G.bad = Ok.bad /\ Ok.n = nb){2});
    2..4: (by proc; inline *; sp; if; try if; auto); 3: by auto.
  + by proc; inline *; sp; if; auto; smt().
  + proc; inline Gkx(OAEU, OBEU).ddh Count(GkxD(OAEU, Ok(OEU))).ddh.
    inline GkxD(OAEU, Ok(OEU)).ddh Ok(OEU).get_cs.
    sp; if; 1, 3: by auto.
    seq 3 4 : (={OAEU.m, G2.ca, G.bad, t} /\ ={m}(OBEU, OEU) /\
               ={cddh, i_k, k, ia, ib}(Gk, Gk) /\ ={x}(Gkx, GkxD) /\
               G2.cb{1} = Ok.cs{2} /\ Gk.j_k{1} = Ok.ik{2} /\
               Gk.ib{1} = Ok.il{2} /\
               (G.bad = Ok.bad /\ Ok.n = nb){2} /\
               i0{1} = i1{2} /\ j0{1} = j1{2} /\ r0{1} = r1{2} /\
               G2.cb{1} = cb{2} /\ 0 <= j0{1} < nb);
      2: by inline *; auto => />.
    swap 1 1; wp; call (: ={OAEU.m}); auto.
    by inline *; sp; rcondt{2} 1; auto; smt(expM mulC).
apply (ler_trans (Pr[MainDO(Dkx, Okx(OEU)).main(x, y) @ &m :
                     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\
                              is_ok Ok.il Ok.cs Ok.ik])).
byequiv (: ={arg, glob Dkx} /\ arg{1} = (x, y) ==> _) => //.
conseq (Ok_Okx &m x y Dkx x_EU y_EU Dkx_ll Dkx_initP); smt().
byequiv (: ={glob A, x, y} /\ fst arg{1} = x /\ snd arg{1} = y ==> _) => //.
proc; inline *; wp.
call (: ={OAEU.m, G2.ca, G.bad} /\ ={m}(OEU, OBEU) /\
        ={cddh, i_k, k, ia, ib}(Gk, Gk) /\ ={x}(GkxD, Gkx) /\
        Ok.cs{1} = G2.cb{2} /\ Ok.ik{1} = Gk.j_k{2} /\
        Ok.il{1} = Gk.ib{2} /\ Ok.x{1} = Gkx.y{2} /\
        (G.bad = Ok.bad /\ Ok.n = nb){1});
  1..4: (by proc; inline *; sp; if; try if; auto); 2: by auto.
- proc; inline Gkxy(OAEU, OBEU).ddh Count(GkxD(OAEU, Okx(OEU))).ddh.
  inline GkxD(OAEU, Okx(OEU)).ddh Ok(OEU).get_cs.
  sp; if; 1, 3: by auto.
  seq 4 3 : (={OAEU.m, G2.ca, G.bad, t} /\ ={m}(OEU, OBEU) /\
             ={cddh, i_k, k, ia, ib}(Gk, Gk) /\ ={x}(GkxD, Gkx) /\
             Ok.cs{1} = G2.cb{2} /\ Ok.ik{1} = Gk.j_k{2} /\
             Ok.il{1} = Gk.ib{2} /\ Ok.x{1} = Gkx.y{2} /\
             (G.bad = Ok.bad /\ Ok.n = nb){1} /\
             i1{1} = i0{2} /\ j1{1} = j0{2} /\ r1{1} = r0{2} /\
             cb{1} = G2.cb{2} /\ 0 <= j1{1} < nb); 2: by inline *; auto => />.
  swap 1 1; wp; call (: ={OAEU.m}); auto.
  by inline *; sp; rcondt{1} 1; auto; smt(expM mulC).
qed.

local lemma Gkxy_S &m x y :
  x \in EU =>
  y \in EU =>
  Pr[Game_xy(Gkxy(OAEU, OBEU), A).main(x, y) @ &m :
     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k] <=
  Pr[GameS(A).main(exp g x, exp g y) @ &m : S.m_crit = exp g (x * y)].
proof.
move => x_EU y_EU; byequiv => //; proc; inline *; symmetry.
call (: ! nstop Gk.ia Gk.ib G2.ca G2.cb \/
        ! (G.bad => nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k) \/
        Gk.k <= Gk.cddh,

        ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={cddh, k, ia, ib}(S, Gk) /\
        (S.gx = exp g x /\ S.gy = exp g y){1} /\
        (Gkx.x = x /\ Gkx.y = y){2} /\
        (G.bad{2} => S.m_crit{1} = exp g (x * y)) /\
        (G.bad <=> Gk.k <= Gk.cddh){2} /\
        (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
        (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2},

        ! ( nstop Gk.ia Gk.ib G2.ca G2.cb){2} \/
        ! (G.bad => nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k){2} \/
        (S.k <= S.cddh /\ S.m_crit = exp g (x * y)){1} \/
        (Gk.k <= Gk.cddh /\ ! G.bad){2});
  2, 5: by proc; inline *; sp; if; auto;
           smt(expM exp_inv get_setE get_set_sameE memE mulA supp_duniform).
- by exact A_ll.
- by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
- by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
- by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
- by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
- by proc; inline *; sp; if; [ | if; auto | ]; auto;
     smt(expM get_setE get_set_sameE supp_duniform memE).
- by move => *; proc; inline *; sp; if; auto; if; auto; smt(dEU_ll).
- by move => *; proc; inline *; sp; if; auto; if; auto; smt(dEU_ll).
- by proc; inline *; sp; if; [ | if; auto | ]; auto;
     smt(expM get_setE get_set_sameE supp_duniform memE).
- by move => *; proc; inline *; sp; if; auto; if; auto; smt(dEU_ll).
- by move => *; proc; inline *; sp; if; auto; if; auto; smt(dEU_ll).
- proc; inline S.ddh Gkxy(RAEU.RO, RBEU.RO).ddh.
  sp 8 9; if; [smt() | | auto; smt()].
  seq 2 2 : (={m0, i0, j0, a, b, r0} /\ a{2} \in EU /\ b{2} \in EU /\
             ( nstop Gk.ia Gk.ib G2.ca G2.cb){2} /\
             ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={cddh, k, ia, ib}(S, Gk) /\
             (S.gx = exp g x /\ S.gy = exp g y){1} /\
             (Gkx.x = x /\ Gkx.y = y){2} /\
             (! G.bad /\ Gk.cddh <= Gk.k){2} /\
             (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
             (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2});
    1: by inline *; auto; smt(get_setE get_set_sameE memE supp_duniform).
  auto => /> &2; move: (i0{2}) (j0{2}) (G2.ca{2}) (G2.cb{2}) => i j ca cb *.
  (case: (i \in ca) => [i_ca | iNca]); (case: (j \in cb) => [j_cb | jNcb] /=);
    1..3: smt(expM mulA mulC).
  rewrite -implybE -!expM => [cddh_k [-> ->] /=].
  have -> : x * a{2} * (y * b{2}) * (inv a{2} * inv b{2}) =
            (a{2} * inv a{2}) * (b{2} * inv b{2} * (x * y)) by smt(mulA mulC).
  by rewrite !exp_inv.
- move => &2 *.
  conseq (: _ ==> true) (: _ ==> _) => //; 2: by islossless.
  proc; inline S.ddh; sp; elim * => cddh Ccddh.
  if; 2: by auto; smt().
  by inline *; auto; smt(get_setE get_set_sameE memE supp_duniform).
- move => &1.
  conseq (: _ ==> true) (: _ ==> _) => //; 2: by islossless.
  proc; inline Gkxy(RAEU.RO, RBEU.RO).ddh; sp; elim * => cddh Ccddh.
  if; 2: by auto; smt().
  by inline *; auto; smt(get_setE get_set_sameE memE supp_duniform).
- auto => />; smt(mem_empty supp_dinter).
qed.

local lemma A_B &m :
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k] <=
  Pr[NCDH.Game(B(A)).main() @ &m : res].
proof.
pose p := Pr[Game(Gk(OAEU,OBEU), A).main() @ &m :
             G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k].
byphoare (: (glob A, Gk.i_k, Gk.j_k) = (glob A, Gk.i_k, Gk.j_k){m} ==> _) => //.
proc; inline B(A).solve; wp.
seq 4 : true 1%r p 0%r _
        (x \in EU /\ y \in EU /\ gx = exp g x /\ gy = exp g y /\
        (glob A, Gk.i_k, Gk.j_k) = (glob A, Gk.i_k, Gk.j_k){m}) => //.
- by auto => />; smt(memE supp_duniform).
- by islossless; apply duniform_ll; smt(e_EU).
exlim x, y => x' y'.
call (: (x' \in EU) /\ (y' \in EU) /\ gx = exp g x' /\ gy = exp g y' /\
        (glob A, Gk.i_k, Gk.j_k) = (glob A, Gk.i_k, Gk.j_k){m} ==>
        S.m_crit = exp g (x' * y')); 2: by auto.
bypr => &m' /> 2? -> -> *.
have -> : p = Pr[Game(Gk(OAEU,OBEU), A).main() @ &m' :
                 G.bad /\ is_ok Gk.ia G2.ca Gk.i_k /\ is_ok Gk.ib G2.cb Gk.j_k].
  by rewrite /p; byequiv => //; sim => /> /#.
by apply (ler_trans _ _ _ _ (Gkxy_S &m' x' y' _ _)) => //; smt(Gk_Gkx Gkx_Gkxy).
qed.

lemma G1G2_NCDH &m :
  `| Pr[ Game(G1, A).main() @ &m : res] - Pr[ Game(G2, A).main() @ &m : res] | <=
  q_ddh%r / ((1%r - pa) ^ q_oa * (1%r - pb) ^ q_ob * pa * pb) *
  Pr[NCDH.Game(B(A)).main() @ &m : res] + DELTA.
proof.
apply (ler_trans _ _ _ (G1G2_Gbad &m) _).
suff: Pr[Game(G', A).main() @ &m : G.bad] <=
      q_ddh%r / ((1%r - pa) ^ q_oa * (1%r - pb) ^ q_ob * pa * pb) *
      Pr[NCDH.Game(B(A)).main() @ &m : res] by smt(G_G').
have H1 := guess_bound &m; have H2 := A_B &m.
have {H1 H2} H := ler_trans _ _ _ H1 H2.
rewrite -ler_pdivr_mull; 2: by rewrite invf_div; smt().
by smt(divr_gt0 expr0 expr_gt0 mulr_gt0 pa_bound pb_bound q_ddh_ge1).
qed.

end section.

end Inner.

(* The optimal bound is obtained by setting pa = 1/(q_oa + 1) and likewise for pb *)

lemma pa_bound :
  0%r < (1%r/(q_oa + 1)%r) &&
  if q_oa = 0 then (1%r/(q_oa + 1)%r) <= 1%r else (1%r/(q_oa + 1)%r) < 1%r.
proof. smt. qed.

lemma pb_bound :
  0%r < (1%r/(q_ob + 1)%r) &&
  if q_ob = 0 then (1%r/(q_ob + 1)%r) <= 1%r else (1%r/(q_ob + 1)%r) < 1%r.
proof. smt. qed.

clone import Inner as I with
  op pa <- (1%r/(q_oa + 1)%r),
  op pb <- (1%r/(q_ob + 1)%r),
  axiom pa_bound <- pa_bound, (* does anything break/change if we remove this? *)
  axiom pb_bound <- pb_bound.

(* Need to find a better name *)
lemma foo_monotone (n m : int) :
  0 <= n => n <= m => (n%r/(n+1)%r)^(n+1) <= (m%r/(m+1)%r)^(m+1).
proof.
suff nP : forall n, 0 <= n =>
                    (n%r / (n + 1)%r) ^ (n + 1) <=
                    ((n + 1)%r / (n + 1 + 1)%r) ^ (n + 1 + 1).
- move => n_ge0; rewrite StdOrder.IntOrder.ler_eqVlt; move => [<- /#|mP].
  have {mP} [q] : (exists q, m - n = q /\ 0 < q) by smt ().
  have [p] : exists p, p = q - 1 by smt().
  rewrite eq_sym subr_eq => ->; rewrite subr_eq addrC.
  move => {q} [-> pP]; have {pP} pP : 0 <= p by smt().
  elim: p pP; 1: smt().
  move => i i_ge0 iP; apply (ler_trans _ _ _ iP).
  apply (ler_trans (((n+i+1)%r/((n+i+1)+1)%r)^((n+i+1)+1))); 1: smt().
  have {i_ge0 n_ge0} n_ge0 : 0<= n + i + 1 by smt().
  by apply (ler_trans _ _ _ (nP _ n_ge0)); smt().
- move => {m n} n; rewrite StdOrder.IntOrder.ler_eqVlt; move => [<-|n_gt0];
    1: by rewrite add0r mul0r exprSr // !expr1; smt(mulr_ge0).
  have -> : ((n + 1)%r / (n + 1 + 1)%r) ^ (n + 1 + 1) =
            (n%r / (n + 1)%r) ^ (n + 1) * ((n + 1)%r / (n + 2)%r) *
            ((n + 1)%r ^2 / (n%r * (n + 2)%r)) ^ (n + 1).
  + rewrite mulrAC -exprMn; 1: smt().
    suff -> : n%r / (n + 1)%r * ((n + 1)%r ^ 2 / (n%r * (n + 2)%r)) =
              (n + 1)%r / (n + 2)%r by smt(exprSr).
    by rewrite expr2; algebra; smt(expr2).
  have {1}-> : (n%r/(n+1)%r)^(n+1) = (n%r/(n+1)%r)^(n+1)*1%r by smt().
  rewrite -subr_ge0 -!mulrA -mulrBr mulr_ge0; 1: smt(expr_gt0).
  rewrite subr_ge0 -ler_pdivr_mull; 1: smt().
  rewrite -ler_pdivr_mull; 1: smt().
  apply (ler_trans (1%r + 1%r / (n + 1)%r));
    1: by rewrite -subr_ge0 le0r; left; algebra; smt().
  have -> : (n + 1)%r ^ 2 / (n%r * (n + 2)%r) = 1%r + 1%r / (n%r * (n + 2)%r)
    by algebra; smt(expr2).
  apply (ler_trans (1%r + (n + 1)%r / (n%r * (n + 2)%r))).
  + suff : 1%r / (n + 1)%r <= (n + 1)%r / (n%r * (n + 2)%r) by smt().
    rewrite -ler_pdivl_mulr; 1: smt().
    apply (ler_trans ((n + 1)%r ^ 2 / (n%r * (n + 2)%r))).
    * move: (subr_sqr_1 (n + 1)%r); rewrite subr_eq => ->.
      rewrite ler_pdivl_mulr ?mul1r; 1: smt().
      suff: n%r * (n + 2)%r <= ((n + 1)%r - 1%r) * ((n + 1)%r + 1%r); 1: smt().
      by rewrite -fromintD -fromintB; smt().
    * by rewrite -subr_ge0 le0r; left; algebra; smt(expr2).
  + rewrite Binomial.BCR.binomial; 1: smt().
    rewrite 2?rangeSr; 1, 2: smt().
    rewrite !StdBigop.Bigreal.BRA.big_rcons /predT /=.
    rewrite -addrA Binomial.binn; 1: smt().
    apply ler_paddl.
    * apply StdBigop.Bigreal.sumr_ge0_seq.
      move => a aP _; rewrite mulr_ge0; 1: smt(Binomial.ge0_bin).
      by rewrite expr1z mul1r; smt(expr_gt0).
    * have -> : n + 1 - n = 1 by algebra.
      rewrite !expr1z expr0 expr1 !mul1r.
      suff -> : (Binomial.bin (n + 1) n)%Binomial = n + 1 by smt().
      have {n_gt0} n_ge0 : 0 <= n by smt().
      elim: n n_ge0; 1: smt(Binomial.bin0).
      move => n n_ge0 nP; rewrite Binomial.binSn; 1, 2: smt().
      by rewrite nP Binomial.binn; smt().
qed.

section.

declare module A <: Adversary {G1, G2, G, S, Count,
                              OAEU, OBEU, OEU, O0EU, O1EU, O1G}.

declare axiom A_ll : forall (O <: CDH_RSR_Oracles{A}),
  islossless O.oA =>
  islossless O.oB =>
  islossless O.oa =>
  islossless O.ob =>
  islossless O.ddh =>
  islossless A(O).guess.

declare axiom A_bound : forall (O <: CDH_RSR_Oracles{A}),
  hoare [A(Count(O)).guess :
         Count.ca = 0 /\ Count.cb = 0 /\ Count.cddh = 0 ==>
         Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh].

lemma G1G2_NCDH &m :
  `| Pr[Game(G1,A).main() @ &m : res] - Pr[ Game(G2,A).main() @ &m : res] | <=
  q_ddh%r * (max 1 (4*q_oa))%r * (max 1 (4 * q_ob))%r *
  Pr[NCDH.Game(B(A)).main() @ &m : res] + DELTA.
proof.
have H := I.G1G2_NCDH (<:A) A_ll A_bound &m.
apply (ler_trans _ _ _ H) => {H}.
suff Hmax : forall (n : int),
              0 <= n =>
              1%r/((1%r-1%r/(n+1)%r)^n*(1%r/(n+1)%r)) <= (max 1 (4*n))%r.
- rewrite ler_add2r ler_wpmul2r; 1: smt.
  rewrite -!mulrA ler_wpmul2l; 1: smt(q_ddh_ge1).
  apply (ler_trans ((1%r/((1%r-1%r/(q_oa+1)%r)^q_oa*(1%r/(q_oa+1)%r))) *
                    (1%r/((1%r-1%r/(q_ob+1)%r)^q_ob*(1%r/(q_ob+1)%r)))));
    1: smt.
  apply ler_pmul; smt(q_oa_ge0 q_ob_ge0 divr_ge0 expr_ge0 invr_ge0 mulr_ge0).
- move => n n_ge0; case (n = 0) => [-> /=|H]; 1: smt(expr0).
  have {H n_ge0} n_gt0 : 1 <= n by smt().
  apply (ler_trans (4 * n)%r); 2: smt().
  rewrite ler_pdivr_mulr; 1: smt (divr_gt0 expr_gt0 mulr_gt0).
  rewrite mulrC -ler_pdivr_mulr; 1: smt().
  have -> : 1%r / (4 * n)%r = (1%r /(1 + 1)%r)^(1 + 1) * (1%r / n%r)
    by rewrite !div1r expr2 -!invfM fromintD fromintM mulrDl mul1r -addrA.
  suff -> : (1%r - 1%r / (n + 1)%r) ^ n * (1%r / (n + 1)%r) =
            (n%r / (n + 1)%r)^(n + 1) * (1%r / n%r)
    by rewrite ler_wpmul2r; [smt(divr_ge0)|by apply foo_monotone].
  apply (can2_eq (fun x, x * (1%r / (n + 1)%r)) (fun x, x * (n + 1)%r)) => /=;
    1, 2: by move => x; smt(divrr).
  rewrite -mulrA exprSr; 1: smt().
  rewrite- mulrA -{2}invf_div divrr ?mulr1; 1: smt().
  suff: 1%r - inv (n + 1)%r = n%r / (n + 1)%r; smt.
qed.

end section.
