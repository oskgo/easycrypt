require import AllCore List Distr DBool DInterval DList SDist SmtMap.
require import FinType FSet NominalGroup PROM SplitRO2.

import Distr.MRat.
import DBool.Biased.
import StdOrder.RealOrder.
import RField.

require import LibExt.

theory GDH_RSR.

clone import NominalGroup.NominalGroup as N.

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

lemma dlist_EU n x xs :
  xs \in dlist (duniform (elems EU)) n => x \in xs => x \in EU.
proof.
move => xs_d x_xs; rewrite memE -supp_duniform.
move: xs_d; case (0 <= n) => Hn; 2: by rewrite supp_dlist0; smt().
by rewrite supp_dlist // => -[? /allP H]; exact: H.
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
lemma unfactor (A <: Adversary) :
  equiv[Game(A).main ~ Game'(B(A)).main : ={glob A} ==> res{1} => res{2}].
proof.
proc; inline *; auto.
by call (: true) => //; auto; rewrite /exp => />; smt(mulA mulC powM pow_inv_f).
qed.

end NCDH.

op na       : {int | 0 <= na}       as na_ge0.
op nb       : {int | 0 <= nb}       as nb_ge0.
op q_oa     : {int | 0 <= q_oa}     as q_oa_ge0.
op q_ob     : {int | 0 <= q_ob}     as q_ob_ge0.
(* 0 or 1? *)
op q_ddhm   : {int | 0 <= q_ddhm}   as q_ddhm_ge0.
op q_ddhma  : {int | 0 <= q_ddhma}  as q_ddhma_ge0.
op q_ddhmb  : {int | 0 <= q_ddhmb}  as q_ddhmb_ge0.
op q_ddhgen : {int | 0 <= q_ddhgen} as q_ddhgen_ge0.

module type GDH_RSR_Oracles = {
  proc oA  (i : int) : G
  proc oB  (j : int) : G
  proc oa  (j : int) : Z
  proc ob  (j : int) : Z
  proc ddhm   (m : G, i j : int)     : bool
  proc ddhma  (m : G, i' i j : int)  : bool
  proc ddhmb  (m : G, j' i j : int)  : bool
  proc ddhgen (i i' : int, Y Z : G) : bool
}.

module type GDH_RSR_Oracles_i = {
  include GDH_RSR_Oracles
  proc init () : unit
}.

module type GDH_RSR_Oracles_i_xy = {
  include GDH_RSR_Oracles
  proc init (x y : Z) : unit
}.

module type Adversary (O : GDH_RSR_Oracles) = {
  proc guess () : bool
}.

(* Counting wrapper for CDH_RSR Oracles *)
module Count (O : GDH_RSR_Oracles) = {
  var ca, cb, cddhm, cddhma, cddhmb, cddhgen : int

  proc init () = {
    ca      <- 0;
    cb      <- 0;
    cddhm   <- 0;
    cddhma  <- 0;
    cddhmb  <- 0;
    cddhgen <- 0;
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

  proc ddhm (m, i, j) = {
    var r;

    cddhm <- cddhm + 1;
    r <@ O.ddhm(m, i, j);
    return r;
  }

  proc ddhma (m, i', i, j) = {
    var r;

    cddhma <- cddhma + 1;
    r <@ O.ddhma(m, i', i, j);
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var r;

    cddhmb <- cddhmb + 1;
    r <@ O.ddhmb(m, j', i, j);
    return r;
  }

  proc ddhgen (i, i', Y, Z) = {
    var r;

    cddhgen <- cddhgen + 1;
    r <@ O.ddhgen(i, i', Y, Z);
    return r;
  }
}.

(* The actual CDH_RSR game: initialize oracles and counters and
dispatach to adversary *)
module Game (O : GDH_RSR_Oracles_i) (A : Adversary) = {
  module O' = Count(O)

  proc main () = {
    var r;

    O.init();
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

module Game_xy (O : GDH_RSR_Oracles_i_xy) (A : Adversary) = {
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

module G1 : GDH_RSR_Oracles  = {
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

  proc ddhm (m, i, j) = {
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

  proc ddhma (m, i', i, j) = {
    var a', a, b, r;

    a' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OAZ.get(i');
      a  <@ OAZ.get(i);
      b  <@ OBZ.get(j);
      r  <- exp m a' = exp g (a * b);
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, r;

    b' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OBZ.get(j');
      a  <@ OAZ.get(i);
      b  <@ OBZ.get(j);
      r  <- exp m b' = exp g (a * b);
    }
    return r;
  }

  proc elem (i : int) : Z = {
    var mi, pi, r;

    mi <- - (i + 1);
    pi <- i - 1;
    r  <- e;
    if (i = 0)        r <- f;
    (* 1 <= i < na + 1 *)
    if (0 <= pi < na) r <@ OAZ.get(pi);
    (* 1 <= - i < nb + 1 *)
    if (0 <= mi < nb) r <@ OBZ.get(mi);
    return r;
  }

  proc ddhgen (i, i', Y, Z) = {
    var a, a';

    a  <@ elem(i);
    a' <@ elem(i');
    return (exp Z a = exp Y a');
  }
}.

module G2 : GDH_RSR_Oracles = {
  include G1 [oA, oB, ddhgen]
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

  proc ddhm (m, i, j) = {
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

  proc ddhma (m, i', i, j) = {
    var a', a, b, r;

    a' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OAZ.get(i');
      a  <@ OAZ.get(i);
      b  <@ OBZ.get(j);
      if (i \in ca \/ j \in cb) {
        r <- exp m a' = exp g (a * b);
      } else {
        r <- (i = i') /\ exp m a = exp g (a * b);
      }
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, r;

    b' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OBZ.get(j');
      a  <@ OAZ.get(i);
      b  <@ OBZ.get(j);
      if (i \in ca \/ j \in cb) {
        r <- exp m b' = exp g (a * b);
      } else {
        r <- (j = j') /\ exp m b = exp g (a * b);
      }
    }
    return r;
  }
}.

(* Intermediate games:
- G sets "bad" where G1 and G2 differ
- once "bad" has been set, G no longer logs queries to oa/ob *)

module G (OA : FROZ.RO, OB : FROZ.RO) : GDH_RSR_Oracles = {
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

  proc ddhm (m, i, j) = {
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

  proc ddhma (m, i', i, j) = {
    var a', a, b, r, t;

    a' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OA.get(i');
      a  <@ OA.get(i);
      b  <@ OB.get(j);
      t <- exp m a' = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
        bad <- bad \/ (! (i = i') /\ t);
        r   <- (i = i') /\ exp m a = exp g (a * b);
      }
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, r, t;

    b' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OB.get(j');
      a  <@ OA.get(i);
      b  <@ OB.get(j);
      t <- exp m b' = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
        bad <- bad \/ (! (j = j') /\ t);
        r   <- (j = j') /\ exp m b = exp g (a * b);
      }
    }
    return r;
  }

  proc elem (i : int) : Z = {
    var mi, pi, r;

    mi <- - (i + 1);
    pi <- i - 1;
    r  <- e;
    if (i = 0)        r <- f;
    (* 1 <= i < na + 1 *)
    if (0 <= pi < na) r <@ OA.get(pi);
    (* 1 <= - i < nb + 1 *)
    if (0 <= mi < nb) r <@ OB.get(mi);
    return r;
  }

  proc ddhgen (i i', Y, Z) = {
    var a, a';

    a  <@ elem(i);
    a' <@ elem(i');
    return (exp Z a = exp Y a');
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
axiom pa_bound : 0%r < pa &&
                 if (q_oa = 0) && (q_ddhma = 0) then pa <= 1%r else pa < 1%r.
axiom pb_bound : 0%r < pb &&
                 if (q_ob = 0) && (q_ddhmb = 0) then pb <= 1%r else pb < 1%r.

(* the "simulation", called "A" in cryptoprim.pdf :

We take gx and gy as parameters and use gx (rather than g) for
oA(i) when ia[i] = true. In order for the simulation to remain in sync
with the game G' (more precisely the intermediate game Gk' below), we
need to align the randomness for a and b by multiplying/dividing by x
(resp y) whenever ia[i] (resp ib[j]) is true. *)

module S = {
  import var G2
  var ia, ib  : bool list
  var gx, gy  : G
  var m_crit  : G
  var set     : bool

  proc init (gx' : G, gy' : G) = {
    ca  <- [];
    cb  <- [];
    ia  <$ dlist (dbiased pa) na;
    ib  <$ dlist (dbiased pb) nb;
    gx  <- gx';
    gy  <- gy';
    set <- false;
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

  proc ddh (w : G option, x : G option, y : G, z : G) = {
    var r <- false;

    if (is_none w /\ is_none x) {
      r <- z = y;
    }
    if (is_none w /\ is_some x) {
      r <- exists b, b \in EU /\ oget x = exp g b /\ z = exp y b;
    }
    if (is_some w /\ is_none x) {
      r <- exists a, a \in EU /\ oget w = exp g a /\ exp z a = y;
    }
    if (is_some w /\ is_some x) {
      r <- exists a b, a \in EU /\ oget w = exp g a /\
                       b \in EU /\ oget x = exp g b /\
                       exp z a = exp y b;
    }
    return r;
  }

  proc ddhm (m, i, j) = {
    var a, b, ga, gb, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OAEU.get(i);
      ga <- if (nth false ia i) then gx ^ a else exp g a;
      b <@ OBEU.get(j);
      gb <- if (nth false ib j) then gy ^ b else exp g b;
      t <- ddh(None, Some ga, gb ^ f, m);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! set) {
            m_crit <- m ^ (inv a * inv b);
            set    <- true;
        }
      }
    }
    return r;
  }

  proc ddhma (m, i', i, j) = {
    var a', a, b, ga', ga, gb, r, t;

    a' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OAEU.get(i');
      ga' <- if (nth false ia i') then gx ^ a' else exp g a';
      a <@ OAEU.get(i);
      ga <- if (nth false ia i) then gx ^ a else exp g a;
      b <@ OBEU.get(j);
      gb <- if (nth false ib j) then gy ^ b else exp g b;
      t  <- ddh(Some ga, Some ga', m, gb ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (i = i') /\ ! set) {
            m_crit <- exp m (a' * inv a * inv b);
            set    <- true;
          }
        r <- (i = i') /\ t;
      }
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, gb', ga, gb, r, t;

    b' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OBEU.get(j');
      gb' <- if (nth false ib j') then gy ^ b' else exp g b';
      a <@ OAEU.get(i);
      ga <- if (nth false ia i) then gx ^ a else exp g a;
      b <@ OBEU.get(j);
      gb <- if (nth false ib j) then gy ^ b else exp g b;
      t  <- ddh(Some ga, Some gb', m, gb ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (j = j') /\ ! set) {
            m_crit <- exp m (b' * inv a * inv b);
            set    <- true;
          }
        r <- (j = j') /\ t;
      }
    }
    return r;
  }

  proc pubelem (i : int) : G option = {
    var a, b, ga, gb, mi, pi, r;

    mi <- - (i + 1);
    pi <- i - 1;
    r  <- Some (exp g e);
    if (i = 0) r <- None;
    (* 1 <= i < na + 1 *)
    if (0 <= pi < na) {
      a <@ OAEU.get(pi);
      ga <- if (nth false ia pi) then gx ^ a else exp g a;
      r <- Some ga;
    }
    (* 1 <= - i < nb + 1 *)
    if (0 <= mi < nb) {
      b <@ OBEU.get(mi);
      gb <- if (nth false ib mi) then gy ^ b else exp g b;
      r <- Some gb;
    }
    return r;
  }

  proc ddhgen (i i', Y, Z) = {
    var a, a', r;

    a  <@ pubelem(i);
    a' <@ pubelem(i');
    r <@ ddh(a, a', Y, Z);
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

declare axiom A_ll : forall (O <: GDH_RSR_Oracles{A}),
  islossless O.oA =>
  islossless O.oB =>
  islossless O.oa =>
  islossless O.ob =>
  islossless O.ddhm =>
  islossless O.ddhma =>
  islossless O.ddhmb =>
  islossless O.ddhgen =>
  islossless A(O).guess.

declare axiom A_bound : forall (O <: GDH_RSR_Oracles{Count, A}),
  hoare [A(Count(O)).guess :
         Count.ca      = 0       /\ Count.cb      = 0 /\
         Count.cddhma  = 0       /\ Count.cddhmb  = 0 ==>
         Count.ca     <= q_oa    /\ Count.cb     <= q_ob /\
         Count.cddhma <= q_ddhma /\ Count.cddhmb <= q_ddhmb].

local module G1b = {
  import var G2
  include var G(OAZ, OBZ) [- ddhm, ddhma, ddhmb]

  proc ddhm (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <- OAZ.get(i);
      b <- OBZ.get(j);
      r <- m = exp g (a * b);
      bad <- bad \/ (r /\ ! (i \in ca \/ j \in cb));
    }
    return r;
  }

  proc ddhma (m, i', i, j) = {
    var a', a, b, r;

    a' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OAZ.get(i');
      a  <@ OAZ.get(i);
      b  <@ OBZ.get(j);
      r  <- exp m a' = exp g (a * b);
      bad <- bad \/ (! (i = i') /\ r /\ ! (i \in ca \/ j \in cb));
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, r;

    b' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OBZ.get(j');
      a  <@ OAZ.get(i);
      b  <@ OBZ.get(j);
      r  <- exp m b' = exp g (a * b);
      bad <- bad \/ (! (j = j') /\ r /\ ! (i \in ca \/ j \in cb));
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
  call (: ={OAZ.m, OBZ.m, G2.ca, G2.cb});
  5..7: (by proc; inline *; sp; if; auto); 1..5: (by sim); by auto.
byequiv (_ : ={glob A} ==> ={G.bad} /\ (! G.bad{2} => ={res})) : G.bad => //;
[proc; inline * | smt()].
call (_ : G.bad, ={OAZ.m, OBZ.m, G2.ca, G2.cb, G.bad}, ={G.bad});
  2..13, 23..25: by (sim /> || (move => *; conseq />; islossless)).
- by exact: A_ll.
- proc; inline G1b.ddhm G(OAZ, OBZ).ddhm; sp.
  if; 1, 3: by auto.
  wp; call (: ={OBZ.m}); 1: by sim.
  call (: ={OAZ.m}); 1: by sim.
  by auto => /> /#.
- move => *; proc.
  inline G1b.ddhm; sp; if; auto.
  by conseq (: true); [smt() | islossless].
- move => *; proc.
  inline G(OAZ, OBZ).ddhm; sp; if; auto.
  by conseq (: true); [smt() | islossless].
- proc; inline G1b.ddhma G(OAZ, OBZ).ddhma; sp; if; 1, 3: by auto.
  by case: (i'0{1} = i0{1}); inline *; auto => />; smt(mem_set).
- move => *; proc.
  inline G1b.ddhma; sp; if; auto.
  by conseq (: true); [smt() | islossless].
- move => *; proc.
  inline G(OAZ, OBZ).ddhma; sp; if; auto.
  by conseq (: true); [smt() | islossless].
- proc; inline G1b.ddhmb G(OAZ, OBZ).ddhmb; sp; if; 1, 3: by auto.
  by case: (j'0{1} = j0{1}); inline *; auto => />; smt(mem_set).
- move => *; proc.
  inline G1b.ddhmb; sp; if; auto.
  by conseq (: true); [smt() | islossless].
- move => *; proc.
  inline G(OAZ, OBZ).ddhmb; sp; if; auto.
  by conseq (: true); [smt() | islossless].
- by auto => /> /#.
qed.

(** Expressing the games G, G' and G'' as distinguishers for statistical distance *)

local clone SDist.Dist as D with
  type a <- Z
  proof*.

local clone D.ROM as D1 with
  type in_t <- int,
  op d1     <- dZ,
  op d2     <- duniform (elems EU),
  op N      <- na
proof* by smt(dZ_ll dEU_ll na_ge0).

local clone D.ROM as D2 with
  type in_t <- int,
  op d1     <- dZ,
  op d2     <- duniform (elems EU),
  op N      <- nb
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
    call (: ={m}(OAZ, D1.R1.RO) /\ ={OBZ.m, G2.ca, G2.cb, G.bad}); 1..8: by sim.
    by auto.
  have -> : Pr[Game(G(OAEU, OBZ), A).main() @ &m : G.bad] =
            Pr[D1.R1.MainD(DisA, D1.R2.RO).distinguish() @ &m : res].
  + byequiv => //; proc; inline *; auto.
    call (: ={m}(OAEU, D1.R2.RO) /\ ={OBZ.m, G2.ca, G2.cb, G.bad});
      1..8: (by sim); by auto.
  apply (D1.sdist_ROM DisA _ &m _) => // O; [move => get_ll; islossless | ].
    by apply (A_ll (Count(G(O, OBZ)))); islossless.
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
  + proc; inline *; sp; if; 2: (by auto); wp; rnd; wp.
    call (: true); auto; call (: true); auto.
    smt(in_fsetU in_fset1 mem_rangeset).
  + proc; inline *; sp; if; 2: (by auto); wp; rnd; wp.
    call (: true); auto; smt(in_fsetU in_fset1 mem_rangeset).
  + proc; inline *; seq 13 : (D1.Wrap.dom \subset rangeset 0 na).
    * sp; if; 2: by if; auto => /#.
      seq 3 : (D1.Wrap.dom \subset rangeset 0 na); 2: by sp; if; auto.
      call (: true); auto; smt(in_fsetU in_fset1 mem_rangeset).
    * sp; if; 2: by if; auto => /#.
      seq 3 : (D1.Wrap.dom \subset rangeset 0 na); 2: by sp; if; auto.
      call (: true); auto; smt(in_fsetU in_fset1 mem_rangeset).
  + by inline *; auto; smt(in_fset0).
- have -> : Pr[Game(G(OAEU, OBZ), A).main() @ &m : G.bad] =
            Pr[D2.R1.MainD(DisB, D2.R1.RO).distinguish() @ &m : res].
  + byequiv => //; proc; inline *; auto.
    call (: ={m}(OBZ, D2.R1.RO) /\ ={OAEU.m, G2.ca, G2.cb, G.bad});
      1..8: (by sim); by auto.
  have -> : Pr[Game(G(OAEU, OBEU), A).main() @ &m : G.bad] =
            Pr[D2.R1.MainD(DisB, D2.R2.RO).distinguish() @ &m : res].
  + byequiv => //; proc; inline *; auto.
    call (: ={m}(OBEU, D2.R2.RO) /\ ={OAEU.m, G2.ca, G2.cb, G.bad});
      1..8: (by sim); by auto.
  apply (D2.sdist_ROM DisB _ &m _) => // O; [move => get_ll; islossless | ].
    by apply (A_ll (Count(G(OAEU, O)))); islossless.
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
  + proc; inline *; sp; if; 2: (by auto); wp.
    call (: true); auto; smt(in_fsetU in_fset1 mem_rangeset).
  + proc; inline *; sp; if; 2: (by auto); wp.
    call (: true); auto; call (: true); auto.
    smt(in_fsetU in_fset1 mem_rangeset).
  + proc; inline *; seq 13 : (D2.Wrap.dom \subset rangeset 0 nb).
    * seq 11 : (D2.Wrap.dom \subset rangeset 0 nb); sp; if; auto;
      [ | | call (: true); auto]; smt(in_fsetU in_fset1 mem_rangeset).
    * seq 6 : (D2.Wrap.dom \subset rangeset 0 nb); sp; if; auto;
      [ | | call (: true); auto]; smt(in_fsetU in_fset1 mem_rangeset).
  + by inline *; auto; smt(in_fset0).
qed.

local module Gs (OA : FROEU.RO, OB : FROEU.RO) : GDH_RSR_Oracles = {
  import var G2 G
  include var G(OA, OB) [oA, oB, ddhgen]
  var i_k, j_k, i'_k, j'_k : int
  var ia, ib   : bool list

  proc init () = {
    G(OA, OB).init();
    i_k  <- -1;
    j_k  <- -1;
    i'_k <- -1;
    j'_k <- -1;
    ia   <$ dlist (dbiased pa) na;
    ib   <$ dlist (dbiased pb) nb;
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

  proc ddhm (m, i, j) = {
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
          if (t /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
          }
      }
    }
    return r;
  }

  proc ddhma (m, i', i, j) = {
    var a', a, b, r, t;

    a' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OA.get(i');
      a  <@ OA.get(i);
      b  <@ OB.get(j);
      t <- exp m a' = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (i = i') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            i'_k <- i';
          }
        r <- (i = i') /\ t;
      }
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, r, t;

    b' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OB.get(j');
      a  <@ OA.get(i);
      b  <@ OB.get(j);
      t <- exp m b' = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (j = j') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            j'_k <- j';
          }
        r <- (j = j') /\ t;
      }
    }
    return r;
  }
}.

op cs_all_false (bs : bool list) (il : int list) =
  (forall i, i \in il => ! nth false bs i).

op is_ok (bs : bool list) (il : int list) (i : int) (i' : int) =
  cs_all_false bs il /\ nth false bs i /\ ! nth false bs i'.

op nstop (ia ib : bool list) (ca cb : int list) =
  cs_all_false ia ca /\ cs_all_false ib cb.

local lemma guess_bound &m :
  (1%r - pa) ^ (q_oa + (min 1 q_ddhma)) * pa *
  (1%r - pb) ^ (q_ob + (min 1 q_ddhmb)) * pb *
  Pr[Game(G', A).main() @ &m : G.bad] <=
  Pr[Game(Gs(OAEU, OBEU), A).main() @ &m :
     G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
              is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k].
proof.
pose p := Pr[Game(G', A).main() @ &m : G.bad].
byphoare (_ : glob A = (glob A){m} ==> _) => //.
proc; inline *; swap [10..11] 7.
seq 16 : G.bad p ((1%r - pa) ^ (q_oa + (min 1 q_ddhma)) * pa *
                  (1%r - pb) ^ (q_ob + (min 1 q_ddhmb)) * pb) _ 0%r
         (size G2.ca <= q_oa /\ size G2.cb <= q_ob /\
          (G.bad => 0 <= Gs.i_k < na /\ 0 <= Gs.j_k < nb /\
                    Gs.i_k <> Gs.i'_k /\ Gs.j_k <> Gs.j'_k) /\
          (0 <= Gs.i'_k < na => 0 < q_ddhma) /\
          (0 <= Gs.j'_k < nb => 0 < q_ddhmb) /\
          ! (Gs.i_k \in G2.ca) /\ ! (Gs.j_k \in G2.cb));
  4, 5: by auto; smt().
- conseq (: _ ==> size G2.ca <= Count.ca /\ size G2.cb <= Count.cb /\
                  (G.bad => 0 <= Gs.i_k < na /\ 0 <= Gs.j_k < nb /\
                            Gs.i_k <> Gs.i'_k /\ Gs.j_k <> Gs.j'_k) /\
                  (0 <= Gs.i'_k < na => 0 < Count.cddhma) /\
                  (0 <= Gs.j'_k < nb => 0 < Count.cddhmb) /\
                  ! (Gs.i_k \in G2.ca) /\ ! (Gs.j_k \in G2.cb))
         (: _ ==> Count.ca <= q_oa /\ Count.cb <= q_ob /\
                  Count.cddhma <= q_ddhma /\ Count.cddhmb <= q_ddhmb);
  [ | smt () | seq 15 : (Count.ca = 0 /\ Count.cb = 0 /\
                         Count.cddhma = 0 /\ Count.cddhmb = 0 /\
                         Count.cddhm = 0 /\ Count.cddhgen = 0) | ];
  auto; 1: by call (A_bound (Gs(OAEU, OBEU))).
  call (: size G2.ca <= Count.ca /\ size G2.cb <= Count.cb /\
          (G.bad => 0 <= Gs.i_k < na /\ 0 <= Gs.j_k < nb /\
                    Gs.i_k <> Gs.i'_k /\ Gs.j_k <> Gs.j'_k) /\
          (! G.bad => Gs.i'_k = -1 /\ Gs.j'_k = -1) /\
          (0 <= Gs.i'_k < na => 0 < Count.cddhma) /\
          (0 <= Gs.j'_k < nb => 0 < Count.cddhmb) /\
          0 <= Count.cddhma /\ 0 <= Count.cddhmb /\
          ! (Gs.i_k \in G2.ca) /\ ! (Gs.j_k \in G2.cb));
    1, 2: (by proc; sp; if; [call (: true) | auto]); 7: by auto.
  + proc; inline Gs(OAEU, OBEU).oa; sp; wp.
    by if; [if; [call (: true) | ] | ]; auto; smt().
  + proc; inline Gs(OAEU, OBEU).ob; sp; wp.
    by if; [if; [call (: true) | ] | ]; auto; smt().
  + proc; inline Gs(OAEU, OBEU).ddhm; sp; wp; if; 2: by auto; smt().
    auto; call (: true) => //; call (: true) => //; auto; smt().
  + proc; inline Gs(OAEU, OBEU).ddhma; sp; wp; if; 2: by auto; smt().
    auto; call (: true) => //; call (: true) => //; call (: true) => //.
    by auto; smt().
  + proc; inline Gs(OAEU, OBEU).ddhmb; sp; wp; if; 2: by auto; smt().
    auto; call (: true) => //; call (: true) => //; call (: true) => //.
    by auto; smt().
  + proc; inline Gs(OAEU, OBEU).ddhgen; sp; wp.
    by call (: true) => //; call (: true).
- call (: (glob A) = (glob A){m} /\ OAEU.m = empty /\ OBEU.m = empty /\
          G2.ca = [] /\ G2.cb = [] /\ G.bad = false /\
          Gs.i_k = -1 /\ Gs.j_k = -1 ==> G.bad); 2: by inline *; auto.
  bypr=> &m' gA; rewrite /p.
  byequiv (: ={glob A} /\ OAEU.m{2} = empty /\ OBEU.m{2} = empty /\
             G2.ca{2} = [] /\ G2.cb{2} = [] /\ G.bad{2} = false /\
             Gs.i_k{2} = -1 /\ Gs.j_k{2} = -1 ==> _); [ | smt() | done].
  proc *; inline *; wp.
  call (: G.bad,

          ={OAEU.m, OBEU.m, G2.ca, G2.cb, G.bad} /\
          ((0 <= Gs.i_k < na \/ 0 <= Gs.j_k < nb) => G.bad){2});
    2..7, 9, 12: (by move => *; proc; inline *; sp; if; auto; smt(dEU_ll)).
  + by exact A_ll.
  + by proc; inline *; sp; if; [ | if{2} | ]; auto; smt().
  + by move => *; proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll).
  + by proc; inline *; sp; if; [ | if{2} | ]; auto; smt().
  + by move => *; proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll).
  + by proc; inline *; sp; if; auto; smt().
  + by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
  + by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
  + proc; inline G(OAEU, OBEU).ddhma Gs(OAEU, OBEU).ddhma.
    sp; if; 1, 3: by auto.
    seq 4 4: (! G.bad{2} /\ ={OAEU.m, OBEU.m, G2.ca, G2.cb, G.bad} /\
              ((0 <= Gs.i_k < na \/ 0 <= Gs.j_k < nb) => G.bad){2} /\
              (0 <= i0 < na /\ 0 <= j0 < nb){2} /\
              (i0 = i'0 => t = (exp m0 a = exp g (a * b))){2} /\
              ={m0, i'0, i0, j0, a, b, t}); 2: by auto => /#.
    wp; call (: ={OBEU.m}); 1: by sim.
    exlim i{1}, i'{1} => i i'; case: (i = i'); 2: by inline*; auto => />.
    by inline *; auto; smt(get_set_sameE).
  + by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
  + by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
  + proc; inline G(OAEU, OBEU).ddhmb Gs(OAEU, OBEU).ddhmb.
    sp; if; [by auto | swap 2 1 | by auto].
    seq 4 4: (! G.bad{2} /\ ={OAEU.m, OBEU.m, G2.ca, G2.cb, G.bad} /\
              ((0 <= Gs.i_k < na \/ 0 <= Gs.j_k < nb) => G.bad){2} /\
              (0 <= i0 < na /\ 0 <= j0 < nb){2} /\
              (j0 = j'0 => t = (exp m0 b = exp g (a * b))){2} /\
              ={m0, j'0, i0, j0, a, b, t}); 2: by auto => /#.
    wp; call (: ={OAEU.m}); 1: by sim.
    exlim j{1}, j'{1} => j j'; case: (j = j'); 2: by inline*; auto => />.
    by inline *; auto; smt(get_set_sameE).
  + by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
  + by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
  + proc; inline G(OAEU, OBEU).ddhgen Gs(OAEU, OBEU).ddhgen; sp; wp.
    by call (: ={OAEU.m, OBEU.m}); 2: call (: ={OAEU.m, OBEU.m}); 1, 2: by sim.
  + by move => *; proc; inline *; islossless.
  + move => *; proc; inline Gs(OAEU, OBEU).ddhgen; sp; wp.
    call (: G.bad); 2: (call (: G.bad)); 3: (by auto);
    sp; wp; seq 1: G.bad; 5, 10: (by smt()); 4, 8: hoare;
    by if; inline *; auto; smt(dEU_ll).
  + by auto; smt().
- move => {p}; pose p := (fun b => b = false).
  pose IP := fun (cs : int list) (il : bool list) (n : int) =>
               forall (i : int), i \in oflist cs `&` oflist (range 0 n) =>
                                   p (nth false il i).
  pose JP := fun (c : int) (il : bool list) (n : int) =>
               forall (j : int), j \in fset1 c `&` oflist (range 0 n) =>
                                 ! p (nth false il j).
  have ? := pa_bound; have ? := pb_bound.
  have ? := na_ge0; have ? := nb_ge0.
  have ? :=q_oa_ge0; have ? := q_ob_ge0.
  have ? := q_ddhma_ge0; have ? := q_ddhmb_ge0.
  seq 1 : (is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k)
          ((1%r - pa) ^ (q_oa + min 1 q_ddhma) * pa)
          ((1%r - pb) ^ (q_ob + min 1 q_ddhmb) * pb) _ 0%r
          (G.bad /\ size G2.cb <= q_ob /\
           0 <= Gs.j_k < nb /\ ! (Gs.j_k \in G2.cb) /\ Gs.j_k <> Gs.j'_k /\
           (0 <= Gs.j'_k < nb => 0 < q_ddhmb));
    1, 4, 5: by auto; smt().
  + conseq (: size G2.ca <= q_oa /\ 0 <= Gs.i_k < na /\
              ! (Gs.i_k \in G2.ca) /\ Gs.i_k <> Gs.i'_k /\
              (0 <= Gs.i'_k < na => 0 < q_ddhma)
               ==> _) => //; 1: by smt().
    rnd; skip => {&m} &m /> s_ca ik_ge0 ik_ltna ik_nca ii'P i'kP.
    case: ((0 <= Gs.i'_k < na && ! Gs.i'_k \in G2.ca){m}) => i'kP'.
    * rewrite (mu_eq_support _ _ (fun (x : bool list) =>
                                    IP (Gs.i'_k{m} :: G2.ca{m}) x na /\
                                    JP Gs.i_k{m} x na));
        1: by move => ia /= /(supp_dlist_size _ _ _ na_ge0) size_ia;
              smt (fset1I in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_set2E //; 1: (by exact: dbiased_ll);
        1..3: smt(mem_oflist mem_range in_fsetI in_fset1).
      rewrite !dbiasedE /p /predC /= fset1I clamp_id 1: /#.
      rewrite mem_oflist mem_range ik_ge0 ik_ltna /= fcard1 expr1.
      apply ler_wpmul2r; 1: smt().
      apply ler_wiexpn2l; smt(fcard_ge0 fcard_oflist subsetIl subset_leq_fcard).
    * apply (ler_trans ((1%r - pa) ^ q_oa * pa)); 1: by smt.
      rewrite (mu_eq_support _ _ (fun (x : bool list) =>
                                    IP G2.ca{m} x na /\ JP Gs.i_k{m} x na));
        1: by move => ia /= /(supp_dlist_size _ _ _ na_ge0) size_ia;
              smt (fset1I in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_set2E //; 1: (by exact: dbiased_ll);
        1..3: smt(mem_oflist mem_range in_fsetI in_fset1).
      rewrite !dbiasedE /p /predC /= fset1I clamp_id 1: /#.
      rewrite mem_oflist mem_range ik_ge0 ik_ltna /= fcard1 expr1.
      apply ler_wpmul2r; 1: smt().
      apply ler_wiexpn2l; smt(fcard_ge0 fcard_oflist subsetIl subset_leq_fcard).
  + seq 1 : (is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k)
            ((1%r - pb) ^ (q_ob + min 1 q_ddhmb) * pb) 1%r _ 0%r
            (G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k);
      1, 3..5: by auto; smt().
    rnd; skip => {&m} &m /> _ s_cb jk_ge0 jk_ltnb jk_ncb jj'P j'kP _ _ _.
    case: ((0 <= Gs.j'_k < nb && ! Gs.j'_k \in G2.cb){m}) => j'kP'.
    * rewrite (mu_eq_support _ _ (fun (x : bool list) =>
                                    IP (Gs.j'_k{m} :: G2.cb{m}) x nb /\
                                    JP Gs.j_k{m} x nb));
        1: by move => ib /= /(supp_dlist_size _ _ _ nb_ge0) size_ib;
              smt (fset1I in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_set2E //; 1: (by exact: dbiased_ll);
        1..3: smt(mem_oflist mem_range in_fsetI in_fset1).
      rewrite !dbiasedE /p /predC /= fset1I clamp_id 1: /#.
      rewrite mem_oflist mem_range jk_ge0 jk_ltnb /= fcard1 expr1.
      apply ler_wpmul2r; 1: smt().
      apply ler_wiexpn2l; smt(fcard_ge0 fcard_oflist subsetIl subset_leq_fcard).
    * apply (ler_trans ((1%r - pb) ^ q_ob * pb)); 1: by smt.
      rewrite (mu_eq_support _ _ (fun (x : bool list) =>
                                    IP G2.cb{m} x nb /\ JP Gs.j_k{m} x nb));
        1: by move => ib /= /(supp_dlist_size _ _ _ nb_ge0) size_ib;
              smt (fset1I in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_set2E //; 1: (by exact: dbiased_ll);
        1..3: smt(mem_oflist mem_range in_fsetI in_fset1).
      rewrite !dbiasedE /p /predC /= fset1I clamp_id 1: /#.
      rewrite mem_oflist mem_range jk_ge0 jk_ltnb /= fcard1 expr1.
      apply ler_wpmul2r; 1: smt().
      apply ler_wiexpn2l; smt(fcard_ge0 fcard_oflist subsetIl subset_leq_fcard).
qed.

local module G'' (OA : FROEU.RO, OB : FROEU.RO) : GDH_RSR_Oracles = {
  import var G2 G Gs
  include var Gs(OA, OB) [init, oa, ob, oA, oB]

  proc ddh (w : G option, x : G option, y : G, z : G) = {
    var r <- false;

    if (is_none w /\ is_none x) {
      r <- z = y;
    }
    if (is_none w /\ is_some x) {
      r <- exists b, b \in EU /\ oget x = exp g b /\ z = exp y b;
    }
    if (is_some w /\ is_none x) {
      r <- exists a, a \in EU /\ oget w = exp g a /\ exp z a = y;
    }
    if (is_some w /\ is_some x) {
      r <- exists a b, a \in EU /\ oget w = exp g a /\
                       b \in EU /\ oget x = exp g b /\
                       exp z a = exp y b;
    }
    return r;
  }

  proc ddhm (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- ddh(None, Some (exp g a), (exp g b) ^ f, m);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
          }
      }
    }
    return r;
  }

  proc ddhma (m, i', i, j) = {
    var a', a, b, r, t;

    a' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OA.get(i');
      a  <@ OA.get(i);
      b  <@ OB.get(j);
      t <- ddh(Some (exp g a), Some (exp g a'), m, (exp g b) ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (i = i') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            i'_k <- i';
          }
        r <- (i = i') /\ t;
      }
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, r, t;

    b' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OB.get(j');
      a  <@ OA.get(i);
      b  <@ OB.get(j);
      t <- ddh(Some (exp g a), Some (exp g b'), m, (exp g b) ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (j = j') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            j'_k <- j';
          }
        r <- (j = j') /\ t;
      }
    }
    return r;
  }

  proc pubelem (i : int) : G option = {
    var mi, pi, p, v;

    mi <- - (i + 1);
    pi <- i - 1;
    p  <- Some e;
    if (i = 0) p <- None;
    (* 1 <= i < na + 1 *)
    if (0 <= pi < na) {
      v <@ OA.get(pi);
      p <- Some v;
    }
    (* 1 <= - i < nb + 1 *)
    if (0 <= mi < nb) {
      v <@ OB.get(mi);
      p <- Some v;
    }
    return omap (exp g) p;
  }

  proc ddhgen (i i', Y, Z) = {
    var a, a', r;

    a  <@ pubelem(i);
    a' <@ pubelem(i');
    r <@ ddh(a, a', Y, Z);
    return r;
  }
}.

local equiv Gs_G'' &m :
  Game(Gs(OAEU, OBEU), A).main ~ Game(G''(OAEU, OBEU), A).main :
  ={glob A} ==> ={glob A, G2.ca, G2.cb, glob G, glob Gs}.
proof.
proc *; inline *; wp.
call (: ={OAEU.m, OBEU.m, G2.ca, G2.cb, glob G, glob Gs} /\
        (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){2} /\
        (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){2}).
- by proc; inline *; sp; if; auto; smt(get_setE supp_duniform).
- by proc; inline *; sp; if; auto; smt(get_setE supp_duniform).
- by proc; inline *; sp; if; [ | if | ]; auto; smt(get_setE supp_duniform).
- by proc; inline *; sp; if; [ | if | ]; auto; smt(get_setE supp_duniform).
- proc; inline Gs(OAEU, OBEU).ddhm G''(OAEU, OBEU).ddhm.
  sp; wp; if; 1, 3: by auto.
  seq 3 3: (={OAEU.m, OBEU.m, G2.ca, G2.cb, glob G, glob Gs} /\
            (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){2} /\
            (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){2} /\
            ={m0, i0, j0, r0, t}); 2: by inline *; auto.
  seq 2 2: (={OAEU.m, OBEU.m, G2.ca, G2.cb, glob G, glob Gs} /\
            (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){2} /\
            (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){2} /\
            ={m0, i0, j0, r0, a, b} /\ a{1} \in EU);
    1: by inline *; auto; smt(get_setE supp_duniform).
  by inline *; auto; smt(expM exp_inj mulA mulC powM pow_inv_f).
- proc; inline Gs(OAEU, OBEU).ddhma G''(OAEU, OBEU).ddhma.
  sp; wp; if; 1, 3: by auto.
  seq 4 4: (={OAEU.m, OBEU.m, G2.ca, G2.cb, glob G, glob Gs} /\
            (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){2} /\
            (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){2} /\
            ={m0, i'0 , i0, j0, r0, t}); 2: by inline *; auto.
  seq 3 3: (={OAEU.m, OBEU.m, G2.ca, G2.cb, glob G, glob Gs} /\
            (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){2} /\
            (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){2} /\
            ={m0, i'0, i0, j0, r0, a', a, b} /\ a'{1} \in EU /\ a{1} \in EU);
    1: by inline *; auto; smt(get_setE supp_duniform).
  inline *; auto => /> &2 _ _ a'EU aEU.
  by smt(expM exp_inj mulA mulC powM pow_inv_f).
- proc; inline Gs(OAEU, OBEU).ddhmb G''(OAEU, OBEU).ddhmb.
  sp; wp; if; 1, 3: by auto.
  seq 4 4: (={OAEU.m, OBEU.m, G2.ca, G2.cb, glob G, glob Gs} /\
            (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){2} /\
            (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){2} /\
            ={m0, j'0 , i0, j0, r0, t}); 2: by inline *; auto.
  seq 3 3: (={OAEU.m, OBEU.m, G2.ca, G2.cb, glob G, glob Gs} /\
            (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){2} /\
            (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){2} /\
            ={m0, j'0, i0, j0, r0, b', a, b} /\ b'{1} \in EU /\ a{1} \in EU);
    1: by inline *; auto; smt(N.dZ_ll get_setE supp_duniform).
  inline *; auto => /> &2 _ _ b'EU aEU.
  by smt(expM exp_inj mulA mulC powM pow_inv_f).
- proc; inline Gs(OAEU, OBEU).ddhgen G''(OAEU, OBEU).ddhgen.
  seq 7 7: (={OAEU.m, OBEU.m, G2.ca, G2.cb, glob G, glob Gs, Y0, Z0} /\
            (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){2} /\
            (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){2} /\
            (is_none a{2} => (a{1} = f)) /\
            (is_some a{2} => oget a{2} = exp g a{1} /\ a{1} \in EU) /\
            (is_none a'{2} => (a'{1} = f)) /\
            (is_some a'{2} => oget a'{2} = exp g a'{1} /\ a'{1} \in EU));
    2: by inline *; auto; smt(exp_inj pow_inv_f).
  swap 6 -3; inline G(OAEU, OBEU).elem G''(OAEU, OBEU).pubelem.
  seq 9 9: (={OAEU.m, OBEU.m, G2.ca, G2.cb, glob G, glob Gs, i', Y, Z} /\
            (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){2} /\
            (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){2} /\
            (is_none p{2} => (r0{1} = f)) /\
            (is_some p{2} => oget p{2} = r0{1} /\ r0{1} \in EU)).
  + sp 6 6; if; [smt() | rcondf{1} 2; auto; rcondf{1} 2; auto;
                         rcondf{2} 2; auto; rcondf{2} 2; auto | ].
    if; [smt() | rcondf{1} 2; 1: (by auto; call (: true); auto; smt());
                 rcondf{2} 3; 1: (by auto; call (: true); auto; smt());
                 by inline *; auto; smt(get_setE supp_duniform) | ].
    if; 1, 3: by auto; smt(e_EU).
    by inline *; auto; smt(get_setE supp_duniform).
  + sp 8 8; if; [smt() | rcondf{1} 2; auto; rcondf{1} 2; auto;
                         rcondf{2} 2; auto; rcondf{2} 2; auto; smt() | ].
    if; [smt() | rcondf{1} 2; 1: (by auto; call (: true); auto; smt());
                 rcondf{2} 3; 1: (by auto; call (: true); auto; smt());
                 by inline *; auto; smt(get_setE supp_duniform) | ].
    if; 1, 3: by auto; smt(e_EU).
    by inline *; auto; smt(get_setE supp_duniform).
- by auto; smt(mem_empty).
qed.

module type O = {
  proc get_cs   ()           : int list
  proc set_bad  (i : int)    : unit
  proc set_bad' (i i' : int) : unit
  proc oZ       (i : int)    : Z
  proc oG       (i : int)    : G
}.

module type O_i = {
  include O
  proc init (n : int, il : bool list, x : Z) : unit
}.

module O_i_O (O : O_i) : O = {
  proc get_cs   = O.get_cs
  proc set_bad  = O.set_bad
  proc set_bad' = O.set_bad'
  proc oZ       = O.oZ
  proc oG       = O.oG
}.

module type DistinguisherO_i (O : O) = {
  proc init   (x y : Z) : unit      {}
  proc get_n  ()        : int       {}
  proc get_is ()        : bool list {}
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
    il <@ D'.get_is();
    n  <@ D'.get_n();
    x  <@ D'.get_x();
    O.init(n, il, x);
  }

  proc main (x y : Z) = {
    var r;

    init(x, y);
    r  <@ D(O_i_O(O)).main();
    return r;
  }
}.

local module Ok (O : FROEU.RO) : O_i = {
  var n        : int
  var cs       : int list
  var bad      : bool
  var ik, i'k  : int
  var il       : bool list
  var x        : Z

  proc init (n' : int, is' : bool list, x' : Z) = {
    n   <- n';
    il  <- is';
    x   <- x';
    cs  <- [];
    bad <- false;
    ik  <- -1;
    i'k <- -1;
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

  proc set_bad' (i i' : int) = {
    if (0 <= i < n /\ 0 <= i' < n) {
      if (! bad) {
        bad <- true;
        ik  <- i;
        i'k <- i';
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

local module Ok2 (O0 : FROEU.RO, O1 : FROEU.RO) : O_i = {
  import var Ok

  proc init (n' : int, is' : bool list, x' : Z) = {
    n   <- n';
    il  <- is';
    x   <- x';
    cs  <- [];
    bad <- false;
    ik  <- -1;
    i'k <- -1;
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

  proc set_bad' (i i' : int) = {
    if (0 <= i < n /\ 0 <= i' < n) {
      if (! bad) {
        bad <- true;
        ik  <- i;
        i'k <- i';
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
  ={glob D} /\
  ((is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} <=> (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2}).
proof.
proc *; inline *; wp.
call (: ={glob Ok} /\ splitO OEU.m{1} O0EU.m{2} O1EU.m{2} (nth false Ok.il){2}).
- by proc; auto.
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

  proc init (n' : int, is' : bool list, x' : Z) = {
    n   <- n';
    il  <- is';
    x   <- x';
    cs  <- [];
    bad <- false;
    ik  <- -1;
    i'k <- -1;
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

  proc set_bad' (i i' : int) = {
    if (0 <= i < n /\ 0 <= i' < n) {
      if (! bad) {
        bad <- true;
        ik  <- i;
        i'k <- i';
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
     islossless O.get_cs => islossless O.set_bad => islossless O.set_bad' =>
     islossless O.oZ => islossless O.oG =>
     islossless D(O).main) =>
  equiv[MainDO(D, Ok2(O0EU, O1EU)).main ~ MainDO(D, Ok2X(O0EU, O1G)).main :
        ={arg, glob D} ==>
        (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} =>
        (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2} /\ ={glob D}].
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
        ((is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} <=>
         (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2})].
proof.
move => x_EU y_EU initP; proc *.
inline MainDO(D, Ok2X(O0EU, O1G)).main MainDO(D, Ok2x(O0EU, O1EU)).main; wp.
call (: ={glob Ok, O0EU.m} /\ Ok.x{1} \in EU /\
        O1G.m{1} = (map (fun _ z => exp g (Ok.x * z)) O1EU.m){2}).
- by proc; auto.
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
        ((is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} <=>
         (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2})].
proof.
move => x_EU y_EU initP; proc *.
inline MainDO(D, Ok2x(O0EU, O1EU)).main MainDO(D, Okx(OEU)).main; wp.
call (: Ok.x{1} \in EU /\ ={glob Ok} /\
        splitO OEU.m{2} O0EU.m{1} O1EU.m{1} (nth false Ok.il){1}).
- by proc; auto.
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
     islossless O.get_cs => islossless O.set_bad => islossless O.set_bad' =>
     islossless O.oZ => islossless O.oG =>
     islossless D(O).main) =>
  hoare [MainDO(D, Ok2x(O0EU, O1EU)).init :
         fst arg \in EU /\ snd arg \in EU ==> Ok.x \in EU] =>
  equiv [MainDO(D, Ok(OEU)).main ~ MainDO(D, Okx(OEU)).main :
        ={arg, glob D} /\ arg{1} = (x, y) ==>
        (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} =>
        (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2} /\ ={glob D}].
proof.
move => x_EU y_EU D_ll initP.
transitivity MainDO(D, Ok2(O0EU, O1EU)).main

             (={arg, glob D} ==>
              ={glob D} /\
              ((is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} <=>
               (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2}))

             (={arg, glob D} /\ arg{1} = (x, y) ==>
              (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} =>
              (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2} /\ ={glob D});
  1, 2: smt(); 1: by exact (Ok_Ok2 &m D).
transitivity MainDO(D, Ok2X(O0EU, O1G)).main

             (={arg, glob D} ==>
              (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} =>
              (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2} /\ ={glob D})

             (={arg, glob D} /\ arg{1} = (x, y) ==>
              ={glob D} /\
              ((is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} <=>
               (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2}));
  1, 2: smt(); 1: by exact (Ok2_Ok2X &m D D_ll).
transitivity MainDO(D, Ok2x(O0EU, O1EU)).main

             (={arg, glob D} /\ arg{1} = (x, y) ==>
              ={glob D} /\
              ((is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} <=>
               (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2}))

             (={arg, glob D} /\ arg{1} = (x, y) ==>
              ={glob D} /\
              ((is_ok Ok.il Ok.cs Ok.ik Ok.i'k){1} <=>
               (is_ok Ok.il Ok.cs Ok.ik Ok.i'k){2}));
  1, 2: smt(); 1: by exact (Ok2X_Ok2x &m x y D x_EU y_EU initP).
by exact (Ok2x_Okx &m x y D x_EU y_EU initP).
qed.

local module GD (OA : O, OB : FROEU.RO) = {
  import var G2 G Gs
  var x, y : Z

  proc init_var (x' y' : Z) = {
    ca   <- [];
    cb   <- [];
    bad  <- false;
    i_k  <- -1;
    j_k  <- -1;
    i'_k <- -1;
    j'_k <- -1;
    ia   <$ dlist (dbiased pa) na;
    ib   <$ dlist (dbiased pb) nb;
    x    <- x';
    y    <- y';
  }

  proc get_n () = {
    return na;
  }

  proc get_is () = {
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

  proc ddh (w : G option, x : G option, y : G, z : G) = {
    var r <- false;

    if (is_none w /\ is_none x) {
      r <- z = y;
    }
    if (is_none w /\ is_some x) {
      r <- exists b, b \in EU /\ oget x = exp g b /\ z = exp y b;
    }
    if (is_some w /\ is_none x) {
      r <- exists a, a \in EU /\ oget w = exp g a /\ exp z a = y;
    }
    if (is_some w /\ is_some x) {
      r <- exists a b, a \in EU /\ oget w = exp g a /\
                       b \in EU /\ oget x = exp g b /\
                       exp z a = exp y b;
    }
    return r;
  }

  proc ddhm (m, i, j) = {
    var a, b, ca, r, t;

    a <- g;
    b <- e;
    r <- false;
    t <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.oG(i);
      b <@ OB.get(j);
      ca <@ OA.get_cs();
      t <- ddh(None, Some a, (exp g b) ^ f, m);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
            OA.set_bad(i);
          }
      }
    }
    return r;
  }

  proc ddhma (m, i', i, j) = {
    var a', a, b, ca, r, t;

    a' <- g;
    a  <- g;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OA.oG(i');
      a  <@ OA.oG(i);
      b  <@ OB.get(j);
      ca <@ OA.get_cs();
      t <- ddh(Some a, Some a', m, (exp g b) ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (i = i') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            i'_k <- i';
            OA.set_bad'(i, i');
          }
        r <- (i = i') /\ t;
      }
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, ca, r, t;

    b' <- e;
    a  <- g;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OB.get(j');
      a  <@ OA.oG(i);
      b  <@ OB.get(j);
      ca <@ OA.get_cs();
      t <- ddh(Some a, Some (exp g b'), m, (exp g b) ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (j = j') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            j'_k <- j';
            OA.set_bad(i);
          }
        r <- (j = j') /\ t;
      }
    }
    return r;
  }

  proc pubelem (i : int) : G option = {
    var a, b, mi, pi, r;

    mi <- - (i + 1);
    pi <- i - 1;
    r  <- Some (exp g e);
    if (i = 0) r <- None;
    (* 1 <= i < na + 1 *)
    if (0 <= pi < na) {
      a <@ OA.oG(pi);
      r <- Some a;
    }
    (* 1 <= - i < nb + 1 *)
    if (0 <= mi < nb) {
      b <@ OB.get(mi);
      r <- Some (exp g b);
    }
    return r;
  }

  proc ddhgen (i i', Y, Z) = {
    var a, a', r;

    a  <@ pubelem(i);
    a' <@ pubelem(i');
    r <@ ddh(a, a', Y, Z);
    return r;
  }
}.

local module Ds (OA : O) = {
  module O  = GD(OA, OBEU)
  module CO = Count(O)

  proc init (x y : Z) = {
    O.init_var(x, y);
    OBEU.init();
  }

  proc get_n  = O.get_n
  proc get_is = O.get_is
  proc get_x  = O.get_x

  proc main () = {
    var r;

    CO.init();
    r <@ A(CO).guess();
    return r;
  }
}.

local lemma Ds_ll (O <: O{Ds}) :
  islossless O.get_cs =>
  islossless O.set_bad =>
  islossless O.set_bad' =>
  islossless O.oZ =>
  islossless O.oG =>
  islossless Ds(O).main.
proof.
move => get_cs_ll set_bad_ll set_bad'_ll oZ_ll oG_ll.
proc; inline *; call (: true); auto.
- by exact A_ll.
- by proc; inline *; sp; if; auto; smt(dEU_ll).
- by proc; inline *; wp; call (oZ_ll); auto.
- by proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll).
- proc; inline *; sp; if; 2: by auto; smt(dEU_ll).
  seq 16 : true; auto; 2: by if; [ | if]; auto; call set_bad_ll; auto.
  by swap 1 2; call (get_cs_ll); wp; call (oG_ll); auto; smt(dEU_ll).
- proc; inline *; sp; if; 2: by auto; smt(dEU_ll).
  seq 17 : true; auto; 2: by if; [ | if]; auto; call set_bad'_ll; auto.
  by swap [1..2] 2; call (get_cs_ll); wp;
     call (oG_ll); call (oG_ll); auto; smt(dEU_ll).
- proc; inline *; sp; if; 2: by auto; smt(dEU_ll).
  seq 20 : true; auto; 2: by if; [ | if]; auto; call set_bad_ll; auto.
  by swap 5 2; call (get_cs_ll); wp; call (oG_ll); auto; smt(dEU_ll).
- proc; inline *; sp 9; seq 11 : true; auto; if; [ | if].
  + rcondf 2; auto; rcondf 2; auto; sp 6; if;
      1: by rcondf 2; auto; rcondf 2; auto.
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 3; auto; [call (: true) | call (oG_ll)]; auto; smt().
  + rcondf 3; auto; 1: by call (: true); auto; smt().
    seq 1 : true; auto; 1: by call (oG_ll); auto.
    sp 6; if; 1: by rcondf 2; auto; rcondf 2; auto.
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 3; auto; [call (: true) | call (oG_ll)]; auto; smt().
  + seq 1 : true; auto; 1: by if; auto; smt(dEU_ll).
    sp 5; if; 1: by rcondf 2; auto; rcondf 2; auto.
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 3; auto; [call (: true) | call (oG_ll)]; auto; smt().
qed.

local lemma Ds_initP :
  hoare [MainDO(Ds, Ok2x(O0EU, O1EU)).init :
         fst arg \in EU /\ snd arg \in EU ==> Ok.x \in EU].
proof. by proc; inline *; auto. qed.

local module Gx (OA : FROEU.RO, OB : FROEU.RO) : GDH_RSR_Oracles_i_xy = {
  import var G2 G Gs
  include var G''(OA, OB) [ob, oB, ddh]
  var x, y : Z

  proc init (x' y' : Z) = {
    Gs(OA, OB).init();
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

  proc oA (i : int) = {
    var a;

    a  <- if (nth false ia i) then inv x * e else e;
    if (0 <= i < na) a <@ OA.get(i);
    return (exp g (if (nth false ia i) then x * a else a));
  }

  proc ddhm (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      a <- if (nth false ia i) then x * a else a;
      b <@ OB.get(j);
      t <- ddh(None, Some (exp g a), (exp g b) ^ f, m);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
          }
      }
    }
    return r;
  }

  proc ddhma (m, i', i, j) = {
    var a', a, b, r, t;

    a' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OA.get(i');
      a' <- if (nth false ia i') then x * a' else a';
      a  <@ OA.get(i);
      a  <- if (nth false ia i) then x * a else a;
      b  <@ OB.get(j);
      t <- ddh(Some (exp g a), Some (exp g a'), m, (exp g b) ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (i = i') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            i'_k <- i';
          }
        r <- (i = i') /\ t;
      }
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, r, t;

    b' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OB.get(j');
      a  <@ OA.get(i);
      a  <- if (nth false ia i) then x * a else a;
      b  <@ OB.get(j);
      t <- ddh(Some (exp g a), Some (exp g b'), m, (exp g b) ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (j = j') /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
            j'_k <- j';
          }
        r <- (j = j') /\ t;
      }
    }
    return r;
  }

  proc pubelem (i : int) : G option = {
    var a, b, mi, pi, r;

    mi <- - (i + 1);
    pi <- i - 1;
    r  <- Some (exp g e);
    if (i = 0) r <- None;
    (* 1 <= i < na + 1 *)
    if (0 <= pi < na) {
      a <@ OA.get(pi);
      a <- if (nth false ia pi) then x * a else a;
      r <- Some (exp g a);
    }
    (* 1 <= - i < nb + 1 *)
    if (0 <= mi < nb) {
      b <@ OB.get(mi);
      r <- Some (exp g b);
    }
    return r;
  }

  proc ddhgen (i i', Y, Z) = {
    var a, a', r;

    a  <@ pubelem(i);
    a' <@ pubelem(i');
    r <@ ddh(a, a', Y, Z);
    return r;
  }
}.

local module GameGxy (G : GDH_RSR_Oracles_i_xy) (A : Adversary) = {
  module O' = Count(G)

  proc main (x y : Z) = {
    var r;

    G.init(x, y);
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

local lemma Gs_Gx &m x y :
  x \in EU =>
  y \in EU =>
  Pr[Game   (Gs(OAEU, OBEU), A).main(    ) @ &m :
     G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
              is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k] <=
  Pr[GameGxy(Gx(OAEU, OBEU), A).main(x, y) @ &m :
     G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
              is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k].
proof.
move => x_EU y_EU.
have -> : Pr[Game(Gs (OAEU, OBEU), A).main() @ &m :
             G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
             is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k] =
          Pr[Game(G''(OAEU, OBEU), A).main() @ &m :
             G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
             is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k]
  by byequiv => //; conseq (Gs_G'' &m).
have -> : Pr[Game(G''(OAEU, OBEU), A).main() @ &m :
             G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
                      is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k] =
          Pr[MainDO(Ds, Ok(OEU)).main(x, y) @ &m :
             G.bad /\ is_ok Ok.il Ok.cs Ok.ik Ok.i'k /\
                      is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k].
- byequiv => //; proc; inline *; wp.
  call (: ={OBEU.m, G2.cb, G.bad} /\ ={m}(OAEU, OEU) /\
          ={j_k, j'_k, ia, ib}(Gs, Gs) /\
          G2.ca{1} = Ok.cs{2} /\ Gs.i_k{1} = Ok.ik{2} /\
          Gs.ia{1} = Ok.il{2} /\ Gs.i'_k{1} = Ok.i'k{2} /\
          (G.bad = Ok.bad /\ Ok.n = na){2});
    1, 2, 4: (by proc; inline *; sp; if; try if; auto); 6: by auto.
  + by proc; inline *; sp; if; [ | if | ]; auto; smt().
  + proc; inline G''(OAEU, OBEU).ddhm GD(O_i_O(Ok(OEU)), OBEU).ddhm.
    inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
    seq 3 4 : (={OBEU.m, G2.cb, G.bad, t} /\ ={m}(OAEU, OEU) /\
               ={j_k, j'_k, ia, ib}(Gs, Gs) /\ ={i0, j0, r0} /\
               G2.ca{1} = Ok.cs{2} /\ Gs.i_k{1} = Ok.ik{2} /\
               Gs.ia{1} = Ok.il{2} /\ Gs.i'_k{1} = Ok.i'k{2} /\
               (G.bad = Ok.bad /\ Ok.n = na){2} /\
               G2.ca{1} = ca{2} /\ 0 <= i0{1} < na);
      2: by inline *; auto => />.
    by call (: true); auto; inline *; sp; rcondt{2} 1; auto.
  + proc; inline G''(OAEU, OBEU).ddhma GD(O_i_O(Ok(OEU)), OBEU).ddhma.
    inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
    seq 4 5 : (={OBEU.m, G2.cb, G.bad, t} /\ ={m}(OAEU, OEU) /\
               ={j_k, j'_k, ia, ib}(Gs, Gs) /\ ={i'0, i0, j0, r0} /\
               G2.ca{1} = Ok.cs{2} /\ Gs.i_k{1} = Ok.ik{2} /\
               Gs.ia{1} = Ok.il{2} /\ Gs.i'_k{1} = Ok.i'k{2} /\
               (G.bad = Ok.bad /\ Ok.n = na){2} /\
               G2.ca{1} = ca{2} /\ 0 <= i0{1} < na /\ 0 <= i'0{1} < na);
      2: by inline *; auto => />.
    call (: true); auto; call (: ={OBEU.m}); auto.
    by inline *; sp; rcondt{2} 1; [ | rcondt{2} 8]; auto.
  + proc; inline G''(OAEU, OBEU).ddhmb GD(O_i_O(Ok(OEU)), OBEU).ddhmb.
    inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
    seq 4 5 : (={OBEU.m, G2.cb, G.bad, t} /\ ={m}(OAEU, OEU) /\
               ={j_k, j'_k, ia, ib}(Gs, Gs) /\ ={j'0, i0, j0, r0} /\
               G2.ca{1} = Ok.cs{2} /\ Gs.i_k{1} = Ok.ik{2} /\
               Gs.ia{1} = Ok.il{2} /\ Gs.i'_k{1} = Ok.i'k{2} /\
               (G.bad = Ok.bad /\ Ok.n = na){2} /\
               G2.ca{1} = ca{2} /\ 0 <= i0{1} < na);
      2: by inline *; auto => />.
    call (: true); auto; call (: ={OBEU.m}); auto.
    swap 1 1; call (: ={OBEU.m}); auto.
    by inline *; sp; rcondt{2} 1; auto.
  + proc; inline G''(OAEU, OBEU).ddhgen GD(O_i_O(Ok(OEU)), OBEU).ddhgen.
    inline O_i_O(Ok(OEU)).get_cs.
    seq 7 7 : (={OBEU.m, G2.cb, G.bad, a, a'} /\ ={m}(OAEU, OEU) /\
               ={j_k, j'_k, ia, ib}(Gs, Gs) /\ ={Y0, Z0} /\
               G2.ca{1} = Ok.cs{2} /\ Gs.i_k{1} = Ok.ik{2} /\
               Gs.ia{1} = Ok.il{2} /\ Gs.i'_k{1} = Ok.i'k{2} /\
               (G.bad = Ok.bad /\ Ok.n = na){2});
      2: by inline *; auto => />.
    call (: ={OBEU.m} /\ ={m}(OAEU, OEU) /\ Ok.n{2} = na).
    * sp 3 3; if; auto; [rcondf{1} 2; auto; rcondf{1} 2; auto;
                         rcondf{2} 2; auto; rcondf{2} 2; auto| ].
      if; auto; 2: by if; auto; inline *; auto.
      rcondf{1} 3; 1: by auto; call (: true); auto; smt().
      rcondf{2} 3; 1: by auto; call (: true); auto; smt().
      by inline *; rcondt{2} 3; auto.
    * call (: ={OBEU.m} /\ ={m}(OAEU, OEU) /\ Ok.n{2} = na); auto.
      sp 3 3; if; auto; [rcondf{1} 2; auto; rcondf{1} 2; auto;
                         rcondf{2} 2; auto; rcondf{2} 2; auto| ].
      if; auto; 2: by if; auto; inline *; auto.
      rcondf{1} 3; 1: by auto; call (: true); auto; smt().
      rcondf{2} 3; 1: by auto; call (: true); auto; smt().
      by inline *; rcondt{2} 3; auto.
apply (ler_trans (Pr[MainDO(Ds, Okx(OEU)).main(x, y) @ &m :
                     G.bad /\ is_ok Ok.il Ok.cs Ok.ik Ok.i'k /\
                              is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k])).
- byequiv (: ={arg, glob Ds} /\ arg{1} = (x, y) ==> _) => //.
  by conseq (Ok_Okx &m x y Ds x_EU y_EU Ds_ll Ds_initP); smt().
byequiv (: ={glob A, x, y} /\ fst arg{1} = x /\ snd arg{1} = y ==> _) => //.
proc; inline *; wp.
call (: ={OBEU.m, G2.cb, G.bad} /\ ={m}(OEU, OAEU) /\
        ={j_k, j'_k, ia, ib}(Gs, Gs) /\
        Ok.cs{1} = G2.ca{2} /\ Ok.ik{1} = Gs.i_k{2} /\
        Ok.il{1} = Gs.ia{2} /\ Ok.i'k{1} = Gs.i'_k{2} /\
        Ok.x{1} = Gx.x{2} /\ (G.bad = Ok.bad /\ Ok.n = na){1});
  1..4: (by proc; inline *; sp; if; try if; auto); 5: by auto.
- proc; inline Gx(OAEU, OBEU).ddhm GD(O_i_O(Okx(OEU)), OBEU).ddhm.
  inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
  seq 4 4 : (={OBEU.m, G2.cb, G.bad, t} /\ ={m}(OEU, OAEU) /\
             ={j_k, j'_k, ia, ib}(Gs, Gs) /\ ={i0, j0, r0} /\
             Ok.cs{1} = G2.ca{2} /\ Ok.ik{1} = Gs.i_k{2} /\
             Ok.il{1} = Gs.ia{2} /\ Ok.i'k{1} = Gs.i'_k{2} /\
             Ok.x{1} = Gx.x{2} /\ (G.bad = Ok.bad /\ Ok.n = na){1} /\
             ca{1} = G2.ca{2} /\ 0 <= i0{1} < na);
    2: by inline *; auto => />.
  by call (: true); auto; inline *; sp; rcondt{1} 1; auto.
- proc; inline Gx(OAEU, OBEU).ddhma GD(O_i_O(Okx(OEU)), OBEU).ddhma.
  inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
  seq 5 6 : (={OBEU.m, G2.cb, G.bad, t} /\ ={m}(OEU, OAEU) /\
             ={j_k, j'_k, ia, ib}(Gs, Gs) /\ ={i'0, i0, j0, r0} /\
             Ok.cs{1} = G2.ca{2} /\ Ok.ik{1} = Gs.i_k{2} /\
             Ok.il{1} = Gs.ia{2} /\ Ok.i'k{1} = Gs.i'_k{2} /\
             Ok.x{1} = Gx.x{2} /\ (G.bad = Ok.bad /\ Ok.n = na){1} /\
             ca{1} = G2.ca{2} /\ 0 <= i0{1} < na /\ 0 <= i'0{1} < na);
    2: by inline *; auto => />.
  call (: true); auto; call (: ={OBEU.m}); auto.
  by inline *; sp; rcondt{1} 1; [ | rcondt{1} 8]; auto.
- proc; inline Gx(OAEU, OBEU).ddhmb GD(O_i_O(Okx(OEU)), OBEU).ddhmb.
  inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
  seq 5 5 : (={OBEU.m, G2.cb, G.bad, t} /\ ={m}(OEU, OAEU) /\
             ={j_k, j'_k, ia, ib}(Gs, Gs) /\ ={j'0, i0, j0, r0} /\
             Ok.cs{1} = G2.ca{2} /\ Ok.ik{1} = Gs.i_k{2} /\
             Ok.il{1} = Gs.ia{2} /\ Ok.i'k{1} = Gs.i'_k{2} /\
             Ok.x{1} = Gx.x{2} /\ (G.bad = Ok.bad /\ Ok.n = na){1} /\
             ca{1} = G2.ca{2} /\ 0 <= i0{1} < na);
    2: by inline *; auto => />.
  call (: true); auto; call (: ={OBEU.m}); auto.
  swap 1 1; call (: ={OBEU.m}); auto.
  by inline *; sp; rcondt{1} 1; auto.
- proc; inline Gx(OAEU, OBEU).ddhgen GD(O_i_O(Okx(OEU)), OBEU).ddhgen.
  inline O_i_O(Ok(OEU)).get_cs.
  seq 7 7 : (={OBEU.m, G2.cb, G.bad, a, a'} /\ ={m}(OEU, OAEU) /\
             ={j_k, j'_k, ia, ib}(Gs, Gs) /\ ={Y0, Z0} /\
             Ok.cs{1} = G2.ca{2} /\ Ok.ik{1} = Gs.i_k{2} /\
             Ok.il{1} = Gs.ia{2} /\ Ok.i'k{1} = Gs.i'_k{2} /\
             Ok.x{1} = Gx.x{2} /\ (G.bad = Ok.bad /\ Ok.n = na){1});
    2: by inline *; auto => />.
  call (: ={OBEU.m} /\ ={m}(OEU, OAEU) /\ Ok.x{1} = Gx.x{2} /\
          Ok.n{1} = na /\ Ok.il{1} = Gs.ia{2}).
  + sp 3 3; if; auto; [rcondf{1} 2; auto; rcondf{1} 2; auto;
                       rcondf{2} 2; auto; rcondf{2} 2; auto| ].
    if; auto; 2: by if; auto; inline *; auto.
    rcondf{1} 3; 1: by auto; call (: true); auto; smt().
    rcondf{2} 4; 1: by auto; call (: true); auto; smt().
    by inline *; rcondt{1} 3; auto.
  + call (: ={OBEU.m} /\ ={m}(OEU, OAEU) /\ Ok.x{1} = Gx.x{2} /\
            Ok.n{1} = na /\ Ok.il{1} = Gs.ia{2}); auto.
    sp 3 3; if; auto; [rcondf{1} 2; auto; rcondf{1} 2; auto;
                       rcondf{2} 2; auto; rcondf{2} 2; auto| ].
    if; auto; 2: by if; auto; inline *; auto.
    rcondf{1} 3; 1: by auto; call (: true); auto; smt().
    rcondf{2} 4; 1: by auto; call (: true); auto; smt().
    by inline *; rcondt{1} 3; auto.
qed.

local module GxD (OA : FROEU.RO, OB : O) = {
  import var G2 G Gs Gx

  proc init_var (x' y' : Z) = {
    ca   <- [];
    cb   <- [];
    bad  <- false;
    i_k  <- -1;
    j_k  <- -1;
    i'_k <- -1;
    j'_k <- -1;
    ia   <$ dlist (dbiased pa) na;
    ib   <$ dlist (dbiased pb) nb;
    x    <- x';
    y    <- y';
  }

  proc get_n () = {
    return nb;
  }

  proc get_is () = {
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

  proc oA (i : int) = {
    var a;

    a  <- if (nth false ia i) then inv x * e else e;
    if (0 <= i < na) a <@ OA.get(i);
    return (exp g (if (nth false ia i) then x * a else a));
  }

  proc oB = OB.oG

  proc ddh (w : G option, x : G option, y : G, z : G) = {
    var r <- false;

    if (is_none w /\ is_none x) {
      r <- z = y;
    }
    if (is_none w /\ is_some x) {
      r <- exists b, b \in EU /\ oget x = exp g b /\ z = exp y b;
    }
    if (is_some w /\ is_none x) {
      r <- exists a, a \in EU /\ oget w = exp g a /\ exp z a = y;
    }
    if (is_some w /\ is_some x) {
      r <- exists a b, a \in EU /\ oget w = exp g a /\
                       b \in EU /\ oget x = exp g b /\
                       exp z a = exp y b;
    }
    return r;
  }

  proc ddhm (m, i, j) = {
    var a, b, cb, r, t;

    a <- e;
    b <- g;
    r <- false;
    t <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      a <- if (nth false ia i) then x * a else a;
      b <@ OB.oG(j);
      cb <@ OB.get_cs();
      t <- ddh(None, Some (exp g a), b ^ f, m);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
            OB.set_bad(j);
          }
      }
    }
    return r;
  }

  proc ddhma (m, i', i, j) = {
    var a', a, b, cb, r, t;

    a' <- e;
    a  <- e;
    b  <- g;
    r  <- false;
    t  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OA.get(i');
      a' <- if (nth false ia i') then x * a' else a';
      a <@ OA.get(i);
      a <- if (nth false ia i) then x * a else a;
      b  <@ OB.oG(j);
      cb <@ OB.get_cs();
      t <- ddh(Some (exp g a), Some (exp g a'), m, b ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (i = i') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            i'_k <- i';
            OB.set_bad(j);
          }
        r <- (i = i') /\ t;
      }
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, cb, r, t;

    b' <- g;
    a  <- e;
    b  <- g;
    r  <- false;
    t  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OB.oG(j');
      a <@ OA.get(i);
      a <- if (nth false ia i) then x * a else a;
      b  <@ OB.oG(j);
      cb <@ OB.get_cs();
      t <- ddh(Some (exp g a), Some b', m, b ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (j = j') /\ ! bad) {
            bad <- true;
            i_k  <- i;
            j_k  <- j;
            j'_k <- j';
            OB.set_bad'(j, j');
          }
        r <- (j = j') /\ t;
      }
    }
    return r;
  }

  proc pubelem (i : int) : G option = {
    var a, b, mi, pi, r;

    mi <- - (i + 1);
    pi <- i - 1;
    r  <- Some (exp g e);
    if (i = 0) r <- None;
    (* 1 <= i < na + 1 *)
    if (0 <= pi < na) {
      a <@ OA.get(pi);
      a <- if (nth false ia pi) then x * a else a;
      r <- Some (exp g a);
    }
    (* 1 <= - i < nb + 1 *)
    if (0 <= mi < nb) {
      b <@ OB.oG(mi);
      r <- Some b;
    }
    return r;
  }

  proc ddhgen (i i', Y, Z) = {
    var a, a', r;

    a  <@ pubelem(i);
    a' <@ pubelem(i');
    r <@ ddh(a, a', Y, Z);
    return r;
  }
}.

local module Dx (OB : O) = {
  module O  = GxD(OAEU, OB)
  module CO = Count(O)

  proc init (x y : Z) = {
    O.init_var(x, y);
    OAEU.init();
  }

  proc get_n = O.get_n
  proc get_is = O.get_is
  proc get_x = O.get_x

  proc main () = {
    var r;

    CO.init();
    r <@ A(CO).guess();
    return r;
  }
}.

local lemma Dx_ll (O <: O{Dx}) :
  islossless O.get_cs =>
  islossless O.set_bad =>
  islossless O.set_bad' =>
  islossless O.oZ =>
  islossless O.oG =>
  islossless Dx(O).main.
proof.
move => get_cs_ll set_bad_ll set_bad'_ll oZ_ll oG_ll.
proc; inline *; call (: true); auto.
- by exact A_ll.
- by proc; inline *; sp; if; auto; smt(dEU_ll).
- by proc; inline *; sp; if; [if | ]; auto; smt(dEU_ll).
- by proc; inline *; wp; call (oZ_ll); auto.
- proc; inline *; sp; if; 2: by auto; smt(dEU_ll).
  seq 17 : true; auto; 2: by if; [ | if]; auto; call set_bad_ll; auto.
  by call (get_cs_ll); wp; call (oG_ll); auto; smt(dEU_ll).
- proc; inline *; sp; if; 2: by auto; smt(dEU_ll).
  seq 22 : true; auto; 2: by if; [ | if]; auto; call set_bad_ll; auto.
  by call (get_cs_ll); wp; call (oG_ll); auto; smt(dEU_ll).
- proc; inline *; sp; if; 2: by auto; smt(dEU_ll).
  seq 18 : true; auto; 2: by if; [ | if]; auto; call set_bad'_ll; auto.
  by swap 1 5; call (get_cs_ll); call (oG_ll); call (oG_ll); auto; smt(dEU_ll).
- proc; inline *; sp 9; seq 11 : true; auto; if; [ | if].
  + rcondf 2; auto; rcondf 2; auto; sp 6; if;
      1: by rcondf 2; auto; rcondf 2; auto.
    if; 2: by if; auto; call (oG_ll); auto.
    by rcondf 7; auto; smt(dEU_ll).
  + rcondf 7; auto; 1: smt().
    seq 7 : true; auto; 1: smt(dEU_ll).
    sp 4; if; 1: by rcondf 2; auto; rcondf 2; auto.
    if; 2: by if; auto; call (oG_ll); auto.
    by rcondf 7; auto; smt(dEU_ll).
  + seq 2 : true; auto; 1: by if; auto; call (oG_ll); auto.
    sp 4; if; 1: by rcondf 2; auto; rcondf 2; auto.
    if; 2: by if; auto; call (oG_ll); auto.
    by rcondf 7; auto; smt(dEU_ll).
qed.

local lemma Dx_initP :
  hoare [MainDO(Dx, Ok2x(O0EU, O1EU)).init :
         fst arg \in EU /\ snd arg \in EU ==> Ok.x \in EU].
proof. by proc; inline *; auto. qed.

local module Gxy (OA : FROEU.RO, OB : FROEU.RO) : GDH_RSR_Oracles_i_xy = {
  import var G2 G Gs Gx
  include var Gx(OA, OB) [init, oa, oA, ddh]

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

  proc ddhm (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      a <- if (nth false ia i) then x * a else a;
      b <@ OB.get(j);
      b <- if (nth false ib j) then y * b else b;
      t <- ddh(None, Some (exp g a), (exp g b) ^ f, m);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
          }
      }
    }
    return r;
  }

  proc ddhma (m, i', i, j) = {
    var a', a, b, r, t;

    a' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= i' < na /\ 0 <= i < na /\ 0 <= j < nb) {
      a' <@ OA.get(i');
      a' <- if (nth false ia i') then x * a' else a';
      a  <@ OA.get(i);
      a  <- if (nth false ia i) then x * a else a;
      b  <@ OB.get(j);
      b  <- if (nth false ib j) then y * b else b;
      t  <- ddh(Some (exp g a), Some (exp g a'), m, (exp g b) ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (i = i') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            i'_k <- i';
          }
        r <- (i = i') /\ t;
      }
    }
    return r;
  }

  proc ddhmb (m, j', i, j) = {
    var b', a, b, r, t;

    b' <- e;
    a  <- e;
    b  <- e;
    r  <- false;
    t  <- false;
    if (0 <= j' < nb /\ 0 <= i < na /\ 0 <= j < nb) {
      b' <@ OB.get(j');
      b' <- if (nth false ib j') then y * b' else b';
      a  <@ OA.get(i);
      a  <- if (nth false ia i) then x * a else a;
      b  <@ OB.get(j);
      b  <- if (nth false ib j) then y * b else b;
      t  <- ddh(Some (exp g a), Some (exp g b'), m, (exp g b) ^ f);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! (j = j') /\ ! bad) {
            bad  <- true;
            i_k  <- i;
            j_k  <- j;
            j'_k <- j';
          }
        r <- (j = j') /\ t;
      }
    }
    return r;
  }

  proc pubelem (i : int) : G option = {
    var a, b, mi, pi, r;

    mi <- - (i + 1);
    pi <- i - 1;
    r  <- Some (exp g e);
    if (i = 0) r <- None;
    (* 1 <= i < na + 1 *)
    if (0 <= pi < na) {
      a <@ OA.get(pi);
      a <- if (nth false ia pi) then x * a else a;
      r <- Some (exp g a);
    }
    (* 1 <= - i < nb + 1 *)
    if (0 <= mi < nb) {
      b <@ OB.get(mi);
      b <- if (nth false ib mi) then y * b else b;
      r <- Some (exp g b);
    }
    return r;
  }

  proc ddhgen (i i', Y, Z) = {
    var a, a', r;

    a  <@ pubelem(i);
    a' <@ pubelem(i');
    r <@ ddh(a, a', Y, Z);
    return r;
  }
}.

local lemma Gx_Gxy &m x y :
  x \in EU =>
  y \in EU =>
  Pr[GameGxy(Gx (OAEU, OBEU), A).main(x, y) @ &m :
     G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
              is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k] <=
  Pr[GameGxy(Gxy(OAEU, OBEU), A).main(x, y) @ &m :
     G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
              is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k].
proof.
move => x_EU y_EU.
have -> :   Pr[GameGxy(Gx(OAEU, OBEU), A).main(x, y) @ &m :
               G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
                        is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k] =
            Pr[MainDO(Dx, Ok(OEU)).main(x, y) @ &m :
               G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
                        is_ok Ok.il Ok.cs Ok.ik Ok.i'k].
- byequiv => //; proc; inline *; wp.
  call (: ={OAEU.m, G2.ca, G.bad, Gx.x} /\ ={m}(OBEU, OEU) /\
          ={i_k, i'_k, ia, ib}(Gs, Gs) /\
          G2.cb{1} = Ok.cs{2} /\ Gs.j_k{1} = Ok.ik{2} /\
          Gs.ib{1} = Ok.il{2} /\ Gs.j'_k{1} = Ok.i'k{2} /\
          (G.bad = Ok.bad /\ Ok.n = nb){2});
    2..4: (by proc; inline *; sp; if; try if; auto); 6: by auto.
  + by proc; inline *; sp; if; auto; smt().
  + proc. inline Gx(OAEU, OBEU).ddhm GxD(OAEU, O_i_O(Ok(OEU))).ddhm.
    inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
    seq 4 5 : (={OAEU.m, G2.ca, G.bad, Gx.x, t} /\ ={m}(OBEU, OEU) /\
               ={i_k, i'_k, ia, ib}(Gs, Gs) /\ ={i0, j0, r0} /\
               G2.cb{1} = Ok.cs{2} /\ Gs.j_k{1} = Ok.ik{2} /\
               Gs.ib{1} = Ok.il{2} /\ Gs.j'_k{1} = Ok.i'k{2} /\
               (G.bad = Ok.bad /\ Ok.n = nb){2} /\
               G2.cb{1} = cb{2} /\ 0 <= j0{1} < nb);
      2: by inline *; auto => />.
    by call (: true); auto; inline *; sp; rcondt{2} 7; auto.
  + proc; inline Gx(OAEU, OBEU).ddhma GxD(OAEU, O_i_O(Ok(OEU))).ddhma.
    inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
    seq 6 7 : (={OAEU.m, G2.ca, G.bad, Gx.x, t} /\ ={m}(OBEU, OEU) /\
               ={i_k, i'_k, ia, ib}(Gs, Gs) /\ ={i'0, i0, j0, r0} /\
               G2.cb{1} = Ok.cs{2} /\ Gs.j_k{1} = Ok.ik{2} /\
               Gs.ib{1} = Ok.il{2} /\ Gs.j'_k{1} = Ok.i'k{2} /\
               (G.bad = Ok.bad /\ Ok.n = nb){2} /\
               G2.cb{1} = cb{2} /\ 0 <= j0{1} < nb);
      2: by inline *; auto => />.
    call (: true); auto; swap [1..4] 1.
    wp; call (: ={OAEU.m}); auto; call (: ={OAEU.m}); auto.
    by inline *; rcondt{2} 3; auto.
  + proc; inline Gx(OAEU, OBEU).ddhmb GxD(OAEU, O_i_O(Ok(OEU))).ddhmb.
    inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
    seq 5 6 : (={OAEU.m, G2.ca, G.bad, Gx.x, t} /\ ={m}(OBEU, OEU) /\
               ={i_k, i'_k, ia, ib}(Gs, Gs) /\ ={j'0, i0, j0, r0} /\
               G2.cb{1} = Ok.cs{2} /\ Gs.j_k{1} = Ok.ik{2} /\
               Gs.ib{1} = Ok.il{2} /\ Gs.j'_k{1} = Ok.i'k{2} /\
               (G.bad = Ok.bad /\ Ok.n = nb){2} /\
               G2.cb{1} = cb{2} /\ 0 <= j0{1} < nb /\ 0 <= j'0{1} < nb);
      2: by inline *; auto => />.
    call (: true); auto; swap [2..3] 1; wp; call (: ={OAEU.m}); auto.
    by inline *; sp; rcondt{2} 1; [ | rcondt{2} 8]; auto.
  + proc; inline Gx(OAEU, OBEU).ddhgen GxD(OAEU, O_i_O(Ok(OEU))).ddhgen.
    inline O_i_O(Ok(OEU)).get_cs.
    seq 7 7 : (={OAEU.m, G2.ca, G.bad, Gx.x, a, a'} /\ ={m}(OBEU, OEU) /\
              ={i_k, i'_k, ia, ib}(Gs, Gs) /\ ={Y0, Z0} /\
              G2.cb{1} = Ok.cs{2} /\ Gs.j_k{1} = Ok.ik{2} /\
              Gs.ib{1} = Ok.il{2} /\ Gs.j'_k{1} = Ok.i'k{2} /\
              (G.bad = Ok.bad /\ Ok.n = nb){2});
      2: by inline *; auto => />.
    call (: ={OAEU.m, Gs.ia, Gx.x} /\ ={m}(OBEU, OEU) /\ Ok.n{2} = nb).
    * sp 3 3; if; auto; [rcondf{1} 2; auto; rcondf{1} 2; auto;
                         rcondf{2} 2; auto; rcondf{2} 2; auto| ].
      if; auto; 2: by if; auto; inline *; rcondt{2} 3; auto.
      rcondf{1} 4; 1: by auto; call (: true); auto; smt().
      rcondf{2} 4; 1: by auto; call (: true); auto; smt().
      by inline *; auto.
    * call (: ={OAEU.m, Gs.ia, Gx.x} /\ ={m}(OBEU, OEU) /\ Ok.n{2} = nb); auto.
      sp 3 3; if; auto; [rcondf{1} 2; auto; rcondf{1} 2; auto;
                         rcondf{2} 2; auto; rcondf{2} 2; auto| ].
      if; auto; 2: by if; auto; inline *; rcondt{2} 3; auto.
      rcondf{1} 4; 1: by auto; call (: true); auto; smt().
      rcondf{2} 4; 1: by auto; call (: true); auto; smt().
      by inline *; auto.
apply (ler_trans (Pr[MainDO(Dx, Okx(OEU)).main(x, y) @ &m :
                     G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
                              is_ok Ok.il Ok.cs Ok.ik Ok.i'k])).
- byequiv (: ={arg, glob Dx} /\ arg{1} = (x, y) ==> _) => //.
  by conseq (Ok_Okx &m x y Dx x_EU y_EU Dx_ll Dx_initP); smt().
byequiv (: ={glob A, x, y} /\ fst arg{1} = x /\ snd arg{1} = y ==> _) => //.
proc; inline *; wp.
call (: ={OAEU.m, G2.ca, G.bad, Gx.x} /\ ={m}(OEU, OBEU) /\
        ={i_k, i'_k, ia, ib}(Gs, Gs) /\
        Ok.cs{1} = G2.cb{2} /\ Ok.ik{1} = Gs.j_k{2} /\
        Ok.il{1} = Gs.ib{2} /\ Ok.i'k{1} = Gs.j'_k{2} /\
        Ok.x{1} = Gx.y{2} /\ (G.bad = Ok.bad /\ Ok.n = nb){1});
  1..4: (by proc; inline *; sp; if; try if; auto); 5: by auto.
- proc; inline Gxy(OAEU, OBEU).ddhm GxD(OAEU, O_i_O(Okx(OEU))).ddhm.
  inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
  seq 5 5 : (={OAEU.m, G2.ca, G.bad, Gx.x, t} /\ ={m}(OEU, OBEU) /\
             ={i_k, i'_k, ia, ib}(Gs, Gs) /\ ={i0, j0, r0} /\
             Ok.cs{1} = G2.cb{2} /\ Ok.ik{1} = Gs.j_k{2} /\
             Ok.il{1} = Gs.ib{2} /\ Ok.i'k{1} = Gs.j'_k{2} /\
             Ok.x{1} = Gx.y{2} /\ (G.bad = Ok.bad /\ Ok.n = nb){1} /\
             cb{1} = G2.cb{2} /\ 0 <= j0{1} < nb);
    2: by inline *; auto => />.
  by call (: true); auto; inline *; sp; rcondt{1} 7; auto.
- proc; inline Gxy(OAEU, OBEU).ddhma GxD(OAEU, O_i_O(Okx(OEU))).ddhma.
  inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
  seq 7 7 : (={OAEU.m, G2.ca, G.bad, Gx.x, t} /\ ={m}(OEU, OBEU) /\
             ={i_k, i'_k, ia, ib}(Gs, Gs) /\ ={i'0, i0, j0, r0} /\
             Ok.cs{1} = G2.cb{2} /\ Ok.ik{1} = Gs.j_k{2} /\
             Ok.il{1} = Gs.ib{2} /\ Ok.i'k{1} = Gs.j'_k{2} /\
             Ok.x{1} = Gx.y{2} /\ (G.bad = Ok.bad /\ Ok.n = nb){1} /\
             cb{1} = G2.cb{2} /\ 0 <= j0{1} < nb);
    2: by inline *; auto => />.
  swap [1..4] 2; call (: true); auto.
  call (: ={OAEU.m}); auto; call (: ={OAEU.m}); auto.
  by inline *; rcondt{1} 3; auto.
- proc; inline Gxy(OAEU, OBEU).ddhmb GxD(OAEU, O_i_O(Okx(OEU))).ddhmb.
  inline O_i_O(Ok(OEU)).get_cs; sp; if; 1, 3: by auto.
  seq 6 7 : (={OAEU.m, G2.ca, G.bad, Gx.x, t} /\ ={m}(OEU, OBEU) /\
             ={i_k, i'_k, ia, ib}(Gs, Gs) /\ ={j'0, i0, j0, r0} /\
             Ok.cs{1} = G2.cb{2} /\ Ok.ik{1} = Gs.j_k{2} /\
             Ok.il{1} = Gs.ib{2} /\ Ok.i'k{1} = Gs.j'_k{2} /\
             Ok.x{1} = Gx.y{2} /\ (G.bad = Ok.bad /\ Ok.n = nb){1} /\
             cb{1} = G2.cb{2} /\ 0 <= j0{1} < nb /\ 0 <= j'0{1} < nb);
    2: by inline *; auto => />.
  swap{1} [2..3] 2; swap{2} [3..4] 2; call (: true); auto.
  call (: ={OAEU.m}); auto.
  by inline *; rcondt{1} 3; 1: (by auto); rcondt{1} 10; auto.
- proc; inline Gxy(OAEU, OBEU).ddhgen GxD(OAEU, O_i_O(Okx(OEU))).ddhgen.
  inline O_i_O(Ok(OEU)).get_cs.
  seq 7 7 : (={OAEU.m, G2.ca, G.bad, Gs.i_k, Gx.x, a, a'} /\ ={m}(OEU, OBEU) /\
             ={i_k, i'_k, ia, ib}(Gs, Gs) /\ ={Y0, Z0} /\
             Ok.cs{1} = G2.cb{2} /\ Ok.ik{1} = Gs.j_k{2} /\
             Ok.il{1} = Gs.ib{2} /\ Ok.i'k{1} = Gs.j'_k{2} /\
             Ok.x{1} = Gx.y{2} /\ (G.bad = Ok.bad /\ Ok.n = nb){1});
    2: by inline *; auto => />.
  call (: ={OAEU.m, Gs.ia, Gx.x} /\ ={m}(OEU, OBEU) /\
          Ok.il{1} = Gs.ib{2} /\ Ok.x{1} = Gx.y{2} /\ Ok.n{1} = nb).
  + sp 3 3; if; auto; [rcondf{1} 2; auto; rcondf{1} 2; auto;
                       rcondf{2} 2; auto; rcondf{2} 2; auto| ].
    if; auto; 2: by if; auto; inline *; rcondt{1} 3; auto.
    rcondf{1} 4; 1: by auto; call (: true); auto; smt().
    rcondf{2} 4; 1: by auto; call (: true); auto; smt().
    by inline *; auto.
  + call (: ={OAEU.m, Gs.ia, Gx.x} /\ ={m}(OEU, OBEU) /\
            Ok.il{1} = Gs.ib{2} /\ Ok.x{1} = Gx.y{2} /\ Ok.n{1} = nb); auto.
    sp 3 3; if; auto; [rcondf{1} 2; auto; rcondf{1} 2; auto;
                       rcondf{2} 2; auto; rcondf{2} 2; auto| ].
    if; auto; 2: by if; auto; inline *; rcondt{1} 3; auto.
    rcondf{1} 4; 1: by auto; call (: true); auto; smt().
    rcondf{2} 4; 1: by auto; call (: true); auto; smt().
    by inline *; auto.
qed.

local lemma Gxy_S &m x y :
  x \in EU =>
  y \in EU =>
  Pr[GameGxy(Gxy(OAEU, OBEU), A).main(x, y) @ &m :
     G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
              is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k] <=
  Pr[GameS(A).main(exp g x, exp g y) @ &m : S.m_crit = exp g (x * y)].
proof.
move => x_EU y_EU; byequiv => //; proc; inline *; symmetry.
call (: ! nstop Gs.ia Gs.ib G2.ca G2.cb \/
        ! (G.bad =>   nth false Gs.ia Gs.i_k  /\   nth false Gs.ib Gs.j_k /\
                    ! nth false Gs.ia Gs.i'_k /\ ! nth false Gs.ib Gs.j'_k),

        ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={ia, ib}(S, Gs) /\
        (S.gx = exp g x /\ S.gy = exp g y){1} /\ (Gx.x = x /\ Gx.y = y){2} /\
        (G.bad{2} => S.m_crit{1} = exp g (x * y)) /\ S.set{1} = G.bad{2} /\
        (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
        (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2});
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
- proc; inline S.ddhm Gxy(OAEU, OBEU).ddhm.
  sp; if; [smt() | swap 2 1 | auto; smt()].
  seq 2 2 : (={m0, i0, j0, r0, a, b} /\ a{2} \in EU /\ b{2} \in EU /\
             (nstop Gs.ia Gs.ib G2.ca G2.cb){2} /\
             ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={ia, ib}(S, Gs) /\
             (S.gx = exp g x /\ S.gy = exp g y){1} /\
             (G.bad{2} => S.m_crit{1} = exp g (x * y)) /\
             (Gx.x = x /\ Gx.y = y){2} /\ S.set{1} = G.bad{2} /\
             (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
             (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2});
    1: by inline *; auto; smt(get_setE get_set_sameE memE supp_duniform).
  inline *; auto => /> &1 &2.
  move: (i0{2}) (j0{2}) (G2.ca{2}) (G2.cb{2}) => i j ca cb *.
  (case: (i \in ca) => [i_ca | iNca]); (case: (j \in cb) => [j_cb | jNcb] /=);
    1..3: smt(expM mulA mulC).
  split; 2: by smt(expM mulA mulC).
  move => ga *; split => *; 2: by smt(expM mulA mulC).
  suff: exp (exp g (y * b{2}) ^ f) ga ^ (inv a{2} * inv b{2}) =
        exp g (ga * inv a{2}) ^ y /\
        exp g (ga * inv a{2}) = exp g x by smt(expM).
  split.
  + rewrite /exp -!expM /exp -!expM /exp.
    have: g ^ (y * b{2} * f * (ga * (inv a{2} * inv b{2}) * inv f) * inv f) =
          g ^ (b{2} * inv b{2}) ^ (ga * inv a{2} * y * inv f) ^ (f * inv f)
      by smt(mulA mulC powM).
    by rewrite pow_inv_f pow_inv.
  + suff: exp g ga = exp g (x * a{2}); 2: by smt(expM exp_inj).
    by rewrite !expM => ->; rewrite -!expM; smt(exp_inv mulA mulC).
- move => &2 *; proc; inline S.ddhm.
  by sp; if; auto; inline *; auto; smt(dEU_ll).
- move => &1 *; proc; inline Gxy(OAEU, OBEU).ddhm.
  sp; if; auto; inline *; auto.
  by smt(dEU_ll get_setE get_set_sameE memE supp_duniform).
- proc; inline S.ddhma Gxy(OAEU, OBEU).ddhma.
  sp; if; [smt() | swap 2 3; swap 3 1 | auto; smt()].
  seq 3 3 : (={m0, i'0, i0, j0, r0, a', a, b} /\
             a'{2} \in EU /\ a{2} \in EU /\ b{2} \in EU /\
             (nstop Gs.ia Gs.ib G2.ca G2.cb){2} /\
             ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={ia, ib}(S, Gs) /\
             (S.gx = exp g x /\ S.gy = exp g y){1} /\
             (G.bad{2} => S.m_crit{1} = exp g (x * y)) /\
             (Gx.x = x /\ Gx.y = y){2} /\ S.set{1} = G.bad{2} /\
             (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
             (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2});
    1: by inline *; auto => />; smt(get_setE get_set_sameE memE supp_duniform).
  inline *; auto => /> &1 &2.
  move: (i0{2}) (j0{2}) (G2.ca{2}) (G2.cb{2}) => i j ca cb *.
  (case: (i \in ca) => [i_ca | iNca]); (case: (j \in cb) => [j_cb | jNcb] /=);
    1..3: smt(expM mulA mulC).
  split; 2: by smt(expM mulA mulC).
  move => ga ga' *; split => *; 2: by smt(expM mulA mulC).
  suff: exp m0{2} a'{2} = exp g (a{2} * x * (b{2} * y)).
  + rewrite !expM => ->; rewrite -!expM.
    have: exp g (a{2} * x * (b{2} * y) * inv a{2} * inv b{2}) =
          exp g (a{2} * inv a{2} * ((b{2} * inv b{2}) * (x * y)));
    smt(exp_inv mulA mulC).
  + have -> : a'{2} = ga' by smt(exp_inj).
    have -> : exp m0{2} ga' = exp (exp g (b{2} * y) ^ f) ga by smt(mulC).
    have -> : exp (exp g (b{2} * y) ^ f) ga = exp (exp g ga) (b{2} * y) ^ f
      by smt(expM mulC mulA).
    have -> : exp g ga = exp g (a{2} * x) by smt(mulC).
    have: exp (exp g (a{2} * x)) (b{2} * y) ^ f =
          exp g (a{2} * x * (b{2} * y)) ^ (f * inv f) by smt(expM mulA mulC).
    by smt(pow_inv_f).
- move => &2 *; proc; inline S.ddhma.
  by sp; if; auto; inline *; auto; smt(dEU_ll).
- move => &1 *; proc; inline Gxy(OAEU, OBEU).ddhma.
  sp; if; auto; inline *; auto.
  by smt(dEU_ll get_setE get_set_sameE memE supp_duniform).
- proc; inline S.ddhmb Gxy(OAEU, OBEU).ddhmb.
  sp; if; [smt() | swap 2 3; swap 3 1 | auto; smt()].
  seq 3 3 : (={m0, j'0, i0, j0, r0, b', a, b} /\
             b'{2} \in EU /\ a{2} \in EU /\ b{2} \in EU /\
             (nstop Gs.ia Gs.ib G2.ca G2.cb){2} /\
             ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={ia, ib}(S, Gs) /\
             (S.gx = exp g x /\ S.gy = exp g y){1} /\
             (G.bad{2} => S.m_crit{1} = exp g (x * y)) /\
             (Gx.x = x /\ Gx.y = y){2} /\ S.set{1} = G.bad{2} /\
             (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
             (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2});
    1: by inline *; auto => /> *; split;
          smt(get_setE get_set_sameE memE supp_duniform).
  inline *; auto => /> &1 &2.
  move: (i0{2}) (j0{2}) (G2.ca{2}) (G2.cb{2}) => i j ca cb *.
  (case: (i \in ca) => [i_ca | iNca]); (case: (j \in cb) => [j_cb | jNcb] /=);
    1..3: smt(expM mulA mulC).
  split; 2: by smt(expM mulA mulC).
  move => ga gb' *; split => *; 2: by smt(expM mulA mulC).
  suff: exp m0{2} b'{2} = exp g (a{2} * x * (b{2} * y)).
  + rewrite !expM => ->; rewrite -!expM.
    have: exp g (a{2} * x * (b{2} * y) * inv a{2} * inv b{2}) =
          exp g (a{2} * inv a{2} * ((b{2} * inv b{2}) * (x * y)));
    smt(exp_inv mulA mulC).
  + have -> : b'{2} = gb' by smt(exp_inj).
    have -> : exp m0{2} gb' = exp (exp g (b{2} * y) ^ f) ga by smt(mulC).
    have -> : exp (exp g (b{2} * y) ^ f) ga = exp (exp g ga) (b{2} * y) ^ f
      by smt(expM mulC mulA).
    have -> : exp g ga = exp g (a{2} * x) by smt(mulC).
    have: exp (exp g (a{2} * x)) (b{2} * y) ^ f =
          exp g (a{2} * x * (b{2} * y)) ^ (f * inv f) by smt(expM mulA mulC).
    by smt(pow_inv_f).
- move => &2 *; proc; inline S.ddhmb.
  by sp; if; auto; inline *; auto; smt(dEU_ll).
- move => &1 *; proc; inline Gxy(OAEU, OBEU).ddhmb.
  sp; if; auto; inline *; auto.
  by smt(dEU_ll get_setE get_set_sameE memE supp_duniform).
- proc; inline S.ddhgen Gxy(OAEU, OBEU).ddhgen.
  seq 7 7 : ((nstop Gs.ia Gs.ib G2.ca G2.cb){2} /\
             ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={ia, ib}(S, Gs) /\
             (S.gx = exp g x /\ S.gy = exp g y){1} /\
             (G.bad{2} => S.m_crit{1} = exp g (x * y)) /\
             (Gx.x = x /\ Gx.y = y){2} /\ S.set{1} = G.bad{2} /\
             (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
             (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2} /\
             ={Y0, Z0, a, a'}); 2: by inline *; auto.
  seq 6 6 : ((nstop Gs.ia Gs.ib G2.ca G2.cb){2} /\
             ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={ia, ib}(S, Gs) /\
             (S.gx = exp g x /\ S.gy = exp g y){1} /\
             (G.bad{2} => S.m_crit{1} = exp g (x * y)) /\
             (Gx.x = x /\ Gx.y = y){2} /\ S.set{1} = G.bad{2} /\
             (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
             (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2} /\
             ={i'0, Y0, Z0, a}); inline *.
  + sp 9 9; if; [smt() | rcondf{1} 2; auto; rcondf{1} 2; auto;
                         rcondf{2} 2; auto; rcondf{2} 2; auto; smt() | ].
    if; [smt() | | if; auto; smt(expM get_setE supp_duniform)].
    rcondf{1} 7; 1: by auto; smt().
    by rcondf{2} 7; auto; smt(expM get_setE supp_duniform).
  + sp 4 4; if; [smt() | rcondf{1} 2; auto; rcondf{1} 2; auto;
                         rcondf{2} 2; auto; rcondf{2} 2; auto; smt() | ].
    if; [smt() | | if; auto; smt(expM get_setE supp_duniform)].
    rcondf{1} 7; 1: by auto; smt().
    by rcondf{2} 7; auto; smt(expM get_setE supp_duniform).
- move => &2 *; proc; inline S.ddhgen.
  seq 7 : true; auto; [seq 6 : true; auto | by inline *; auto].
  + inline *; sp 9; if; [rcondf 2; auto; rcondf 2; auto | ].
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 7; auto; smt(dEU_ll).
  + inline *; sp 4; if; [rcondf 2; auto; rcondf 2; auto | ].
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 7; auto; smt(dEU_ll).
- move => &1 *; proc; inline Gxy(OAEU, OBEU).ddhgen.
  seq 7 : (! nstop Gs.ia Gs.ib G2.ca G2.cb \/
           ! (G.bad =>   nth false Gs.ia Gs.i_k  /\   nth false Gs.ib Gs.j_k /\
                       ! nth false Gs.ia Gs.i'_k /\ ! nth false Gs.ib Gs.j'_k));
  auto; [ | by inline *; auto | hoare; auto];
  seq 6 : (! nstop Gs.ia Gs.ib G2.ca G2.cb \/
           ! (G.bad =>   nth false Gs.ia Gs.i_k  /\   nth false Gs.ib Gs.j_k /\
                       ! nth false Gs.ia Gs.i'_k /\ ! nth false Gs.ib Gs.j'_k));
  auto; 3: hoare; auto.
  + inline *; sp 9; if; [rcondf 2; auto; rcondf 2; auto | ].
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 7; auto; smt(dEU_ll).
  + inline *; sp 4; if; [rcondf 2; auto; rcondf 2; auto | ].
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 7; auto; smt(dEU_ll).
  + inline *; sp 9; if; [rcondf 2; auto; rcondf 2; auto | ].
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 7; auto; smt(dEU_ll).
  + inline *; sp 9; if; [rcondf 2; auto; rcondf 2; auto | ].
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 7; auto; smt(dEU_ll).
  + inline *; sp 4; if; [rcondf 2; auto; rcondf 2; auto | ].
    if; 2: by if; auto; smt(dEU_ll).
    by rcondf 7; auto; smt(dEU_ll).
- by auto => />; smt(mem_empty supp_dinter).
qed.

local lemma A_B &m :
  Pr[Game(Gs(OAEU, OBEU), A).main() @ &m :
     G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
              is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k] <=
  Pr[NCDH.Game(B(A)).main() @ &m : res].
proof.
pose p := Pr[Game(Gs(OAEU,OBEU), A).main() @ &m :
             G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
                      is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k].
byphoare (: (glob A, Gs.i_k, Gs.i'_k, Gs.j_k, Gs.j'_k) =
            (glob A, Gs.i_k, Gs.i'_k, Gs.j_k, Gs.j'_k){m} ==> _) => //.
proc; inline B(A).solve; wp.
seq 4 : true 1%r p 0%r _
        (x \in EU /\ y \in EU /\ gx = exp g x /\ gy = exp g y /\
        (glob A, Gs.i_k, Gs.i'_k, Gs.j_k, Gs.j'_k) =
        (glob A, Gs.i_k, Gs.i'_k, Gs.j_k, Gs.j'_k){m}) => //.
- by auto => />; smt(memE supp_duniform).
- by islossless; apply duniform_ll; smt(e_EU).
exlim x, y => x' y'.
call (: (x' \in EU) /\ (y' \in EU) /\ gx = exp g x' /\ gy = exp g y' /\
        (glob A, Gs.i_k, Gs.i'_k, Gs.j_k, Gs.j'_k) =
        (glob A, Gs.i_k, Gs.i'_k, Gs.j_k, Gs.j'_k){m} ==>
        S.m_crit = exp g (x' * y')); 2: by auto.
bypr => &m' /> 2? -> -> *.
have -> : p = Pr[Game(Gs(OAEU,OBEU), A).main() @ &m' :
                 G.bad /\ is_ok Gs.ia G2.ca Gs.i_k Gs.i'_k /\
                          is_ok Gs.ib G2.cb Gs.j_k Gs.j'_k].
  by rewrite /p; byequiv => //; sim => /> /#.
by apply (ler_trans _ _ _ _ (Gxy_S &m' x' y' _ _)) => //; smt(Gs_Gx Gx_Gxy).
qed.

lemma G1G2_NCDH &m :
  `| Pr[ Game(G1, A).main() @ &m : res] - Pr[ Game(G2, A).main() @ &m : res] | <=
  Pr[NCDH.Game(B(A)).main() @ &m : res] /
  ((1%r - pa) ^ (q_oa + min 1 q_ddhma) * pa *
   (1%r - pb) ^ (q_ob + min 1 q_ddhmb) * pb) + DELTA.
proof.
apply (ler_trans _ _ _ (G1G2_Gbad &m) _).
suff: Pr[Game(G', A).main() @ &m : G.bad] <=
      Pr[NCDH.Game(B(A)).main() @ &m : res] /
      ((1%r - pa) ^ (q_oa + min 1 q_ddhma) * pa *
       (1%r - pb) ^ (q_ob + min 1 q_ddhmb) * pb) by smt(G_G').
have H1 := guess_bound &m; have H2 := A_B &m.
have {H1 H2} H := ler_trans _ _ _ H1 H2.
rewrite mulrC -ler_pdivr_mull; 2: by smt().
by smt(invr_gt0 expr0 expr_gt0 mulr_gt0 pa_bound pb_bound).
qed.

end section.

end Inner.

(* The optimal bound is obtained by setting pa = 1/(q_oa + 1) and likewise for pb *)

lemma pa_bound :
  0%r < (1%r / (q_oa + min 1 q_ddhma + 1)%r) &&
  if (q_oa = 0) && (q_ddhma = 0) then
                                   (1%r / (q_oa + min 1 q_ddhma + 1)%r) <= 1%r
                                 else
                                   (1%r / (q_oa + min 1 q_ddhma + 1)%r) <  1%r.
proof. smt. qed.

lemma pb_bound :
  0%r < (1%r / (q_ob + min 1 q_ddhmb + 1)%r) &&
  if (q_ob = 0) && (q_ddhmb = 0) then
                                   (1%r / (q_ob + min 1 q_ddhmb + 1)%r) <= 1%r
                                 else
                                   (1%r / (q_ob + min 1 q_ddhmb + 1)%r) <  1%r.
proof. smt. qed.

clone import Inner as I with
  op pa <- (1%r / (q_oa + min 1 q_ddhma + 1)%r),
  op pb <- (1%r / (q_ob + min 1 q_ddhmb + 1)%r),
  axiom pa_bound <- pa_bound, (* does anything break/change if we remove this? *)
  axiom pb_bound <- pb_bound.

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

declare axiom A_ll : forall (O <: GDH_RSR_Oracles{A}),
  islossless O.oA =>
  islossless O.oB =>
  islossless O.oa =>
  islossless O.ob =>
  islossless O.ddhm =>
  islossless O.ddhma =>
  islossless O.ddhmb =>
  islossless O.ddhgen =>
  islossless A(O).guess.

declare axiom A_bound : forall (O <: GDH_RSR_Oracles{Count, A}),
  hoare [A(Count(O)).guess :
         Count.ca      = 0       /\ Count.cb      = 0 /\
         Count.cddhma  = 0       /\ Count.cddhmb  = 0 ==>
         Count.ca     <= q_oa    /\ Count.cb     <= q_ob /\
         Count.cddhma <= q_ddhma /\ Count.cddhmb <= q_ddhmb].

lemma G1G2_NCDH &m :
  `| Pr[Game(G1,A).main() @ &m : res] - Pr[ Game(G2,A).main() @ &m : res] | <=
  (max 1 (4 * (q_oa + min 1 q_ddhma)))%r *
  (max 1 (4 * (q_ob + min 1 q_ddhmb)))%r *
  Pr[NCDH.Game(B(A)).main() @ &m : res] + DELTA.
proof.
have H := I.G1G2_NCDH (<:A) A_ll A_bound &m.
apply (ler_trans _ _ _ H) => {H}.
suff Hmax : forall (n : int),
              0 <= n =>
              1%r/((1%r-1%r/(n+1)%r)^n*(1%r/(n+1)%r)) <= (max 1 (4*n))%r.
- apply ler_add2r; rewrite mulrC ler_wpmul2r; 1: by smt.
  pose qa := q_oa + min 1 q_ddhma; pose qb := q_ob + min 1 q_ddhmb.
  apply (ler_trans ((1%r/((1%r-1%r/(qa+1)%r)^qa*(1%r/(qa+1)%r))) *
                    (1%r/((1%r-1%r/(qb+1)%r)^qb*(1%r/(qb+1)%r))))); 1: smt.
  apply ler_pmul; smt(q_oa_ge0 q_ob_ge0 q_ddhma_ge0 q_ddhmb_ge0
                      divr_ge0 expr_ge0 invr_ge0 mulr_ge0).
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

end GDH_RSR.
