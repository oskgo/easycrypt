require import AllCore List Finite Distr DBool DInterval DList LorR FSet SmtMap.
require (****) StdBigop PROM Means.

require import LibExt. 

import StdBigop.Bigreal.BRA.

(**********************************************)
(* Authenticated Key Encapsulation Mechanisms *)
(**********************************************)

type keyseed.
type pkey.
type skey.
type encseed.
type key.
type ciphertext.

op [lossless] dkeyseed : keyseed distr.
op [lossless] dencseed : encseed distr.

op pkgen : keyseed -> pkey.
op skgen : keyseed -> skey.

op encap : encseed -> skey -> pkey -> ciphertext * key.
op decap : skey -> pkey -> ciphertext -> key option.

axiom encapK (ks1 ks2 : keyseed) (es : encseed) :
  let (c,k) = encap es (skgen ks1) (pkgen ks2) in
  decap (skgen ks2) (pkgen ks1) c = Some k.


op [lossless] dkey : key distr.
op pk_coll n = mu (dlist dkeyseed n) 
                  (fun ks => !uniq (map pkgen ks)).

(********************************************)
(** * 2-participant version of Outsider-CCA *)
(********************************************)

(* A finite type for the two participants/users *)
type user = [u1|u2].

clone import FinType.FinType as UserFinType with
  type t = user,
  op enum = [u1;u2]
proof*.
realize enum_spec by case.

theory Outsider2CCA.

(* these need to be parameters of the theory, since B depends on qc
and is part of the final statement *)
op qe : int.
op qd : int.
op qc : { int | 0 < qc } as qc_gt0.

module type Oracle = { 
  proc pkey  (_ : user) : pkey
  proc encap (_ : user * pkey) : ciphertext * key
  proc decap (_ : user * pkey * ciphertext) : key option
  proc chall (_ : user * user) : ciphertext * key
}.

module type Oracle_i = { 
  include Oracle
  proc init() : unit
}.

abstract theory MkCount.
module Count (O : Oracle) = { 
  var ce, cd, cc : int

  proc init() = {
    ce <- 0;
    cd <- 0;
    cc <- 0;
  } 

  proc pkey = O.pkey

  proc encap(x) = { 
    var r; 
    ce <- ce + 1 ;
    r <@ O.encap(x);
    return r;
  }

  proc decap(x) = { 
    var r; 
    cd <- cd + 1 ;
    r <@ O.decap(x);
    return r;
  }

  proc chall(x) = { 
    var r; 
    cc <- cc + 1 ;
    r <@ O.chall(x);
    return r;
  }
}.
end MkCount.
clone import MkCount as C.

module type Adversary (O : Oracle) = { 
  proc guess() : bool
}.

module Game (O : Oracle_i) (A : Adversary) = {
  proc main() = {
    var r;

    O.init();
    Count(O).init();
    r <@ A(Count(O)).guess();
    return r;
  }
}.

(* real game *)
module Oreal : Oracle_i = {
  var pk1, pk2 : pkey
  var sk1, sk2 : skey

  proc init() = {
    var ks1,ks2;

    ks1 <$ dkeyseed;
    ks2 <$ dkeyseed;

    sk1 <- skgen ks1;
    pk1 <- pkgen ks1;
    
    sk2 <- skgen ks2;
    pk2 <- pkgen ks2;
  }

  proc pkey (u : user) = { 
    return (if u = u1 then pk1 else pk2);
  }

  proc skey (u : user) = {
    return (if u = u1 then sk1 else sk2);
  }

  proc encap (u : user, pk : pkey) = {
    var c,k,sk,es;
   
    sk <@ skey(u);
    es <$ dencseed;
    (c,k) <- encap es sk pk;
    return (c,k);  
  }

  proc decap (u : user, pk : pkey, c : ciphertext) = {
    var k,sk;

    sk <@ skey(u);
    k <- decap sk pk c;
    return k;
  }

  proc chall (snd : user, rcv : user) = {
    var pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed;

    (c,k) <- encap es sk pk;
    return (c,k);
  }

}.

(* ideal game - challenge oracle yields random keys *)
module Oideal = {
  include var Oreal [-init,chall,decap]
  var m : (pkey * pkey * ciphertext, key) fmap

  proc init() = {
    Oreal.init();
    m <- empty;
  }

  proc decap (u : user, pk : pkey, c : ciphertext) = {
    var k,sku,pku;

    sku <@ skey(u);
    pku <@ pkey(u); 

    if ((pk,pku,c) \in m) {
      k <- m.[(pk,pku,c)];
    } else { 
      k <- decap sku pk c;
    }
    return k;
  }

  proc chall (snd : user, rcv : user) = {
    var pks, pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed;
    (c,k) <- encap es sk pk;
    k <$ dkey;
    pks <@ pkey(snd); 
    m.[(pks,pk,c)] <- k;
    return (c,k);
  }
}.

module (B (A : Adversary) : Adversary) (O : Oracle) = { 
  module OB : Oracle = { 
    var m : (pkey * pkey * ciphertext, key) fmap
    var q,ctr : int
    
    proc encap = O.encap

    proc pkey = O.pkey

    proc decap (u : user, pk : pkey, c : ciphertext) = {
      var k,pku;

      pku <@ pkey(u); 
      if ((pk,pku,c) \in m) {
        k <- m.[(pk,pku,c)];
      } else { 
        k <@ O.decap(u,pk,c);
    }
      return k;
    }

    proc chall (snd : user, rcv : user) : ciphertext * key = { 
      var pk,pks,c,k;
      
      pk <@ pkey(rcv);
      ctr <- ctr + 1;
      if   (ctr < q) { (c,k) <@ O.encap(snd,pk); }
      elif (ctr = q) { (c,k) <@ O.chall(snd,rcv); }
      else { 
        (c,k) <@ O.encap(snd,pk);
        k <$ dkey;
      }
      pks <@ pkey(snd);
      m.[(pks,pk,c)] <- k;
      return (c,k);
    }
  }

  proc guess() = { 
    var r; 
    OB.q <$ [1..qc];
    OB.ctr <- 0;
    OB.m <- empty;
    r <@ A(OB).guess() ; return r;
  }
}.

op counts0 (e d c : int) = e = 0 /\ d = 0 /\ c = 0.
op counts qe qd qc (e d c : int) = e <= qe /\ d <= qd /\ c <= qc.

clone MkCount as CB.

section PROOF.

declare module A <: Adversary{Oreal,Oideal,Count,B,CB.Count}.

declare axiom A_ll : forall (O <: Oracle{A}),
  islossless O.pkey =>
  islossless O.encap =>
  islossless O.decap => 
  islossless O.chall => 
  islossless A(O).guess.

local clone Means as M1 with
  type input <- int,
  type output <- bool,
  op d <- [1..qc]
proof*.

local clone Means as M0 with
  type input <- int,
  type output <- bool,
  op d <- [0..qc-1]
proof*.

local module OG : Oracle_i = { 
  import var Oreal
  include var Oideal [-init,chall]
  var q,ctr : int
  
  proc init () = { 
    Oreal.init();
    m <- empty;
    ctr <- 0;
  }

  proc chall (snd : user, rcv : user) = {
    var pks, pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed; 
    (c,k) <- encap es sk pk;
    ctr <- ctr + 1;
    if (q < ctr) { k <$ dkey; }
    pks <@ pkey(snd); 
    m.[(pks,pk,c)] <- k;
    return (c,k);
  }
}.

local module G : M1.Worker = { 
  proc work (q : int) = {
    var r;

    OG.init();
    OG.q <- q;
    Count(OG).init();
    r <@ A(Count(OG)).guess();
    return r;
  }
}.

declare axiom A_bound (O <: Oracle{A,Count}) :
  hoare [ A(Count(O)).guess : 
  counts0 Count.ce Count.cd Count.cc ==> 
  counts qe qd qc Count.ce Count.cd Count.cc].

(* The ideal game corresponds to G.work(0), where k is always randomized *)
local lemma Oideal_Gqc &m : 
  Pr [ Game(Oideal,A).main() @ &m : res ] = 
  Pr [ G.work(0) @ &m : res ].
proof.
byequiv => //; proc; inline *.
call (: ={glob Oreal, Oideal.m, glob Count} /\ OG.q{2} = 0 /\ 0 <= OG.ctr{2}).
- conseq />; sim.
- conseq />; sim.
- conseq />; sim.
- proc; inline*; conseq />. 
  rcondt{2} 10; first by auto => /> /#. 
  by auto => /#.
- auto; smt().
qed.

(* The real game corresponds to G.work(qc), where k is never randomized 
There are two complications:

1. The proof relies on A making at most qc challenge queries. For this
we turn [qc < OG.ctr] into a bad event and prove that this does not
happen.

2. In Oreal, the decap oracle always calls the decap operation, in
G.work(), challenge queries are logged and the decap orcale uses the
log to answer. So we need to maintain the invariant that answering
using the log is equivalent to running decap. This relies on
correctness of the AKEM scheme. *)
local lemma Oreal_G0 &m : 
  Pr [ Game(Oreal,A).main() @ &m : res ] = 
  Pr [ G.work(qc) @ &m : res ].
proof.
byequiv => //; proc; inline *.
conseq (: _ ==> OG.ctr{2} <= qc => ={r}) _ (: _ ==> OG.ctr <= qc); 1:smt().
- conseq (: _ ==> OG.ctr = Count.cc) 
         (: _ ==> counts qe qd qc Count.ce Count.cd Count.cc); 1: smt().
  + by call (A_bound OG); auto.
  + call(: OG.ctr = Count.cc); 1..3: by conseq />. 
    proc; inline*; auto. swap 9 -7.
    seq 2 : (#pre); [by auto|by conseq />].
  + by auto.
call (: qc < OG.ctr, 
       ={glob Oreal} /\ OG.q{2} = qc /\
       (forall pks c k, Oideal.m.[pks,Oreal.pk1,c] = Some k => 
                        decap Oreal.sk1 pks c = Some k){2} /\
       (forall pks c k, Oideal.m.[pks,Oreal.pk2,c] = Some k => 
                        decap Oreal.sk2 pks c = Some k){2} /\ 
       (exists ks1 ks2, 
         (Oreal.pk1,Oreal.pk2,Oreal.sk1,Oreal.sk2) = 
         (pkgen ks1,pkgen ks2, skgen ks1, skgen ks2)){2}).
- exact A_ll.
(* pkey *)
- conseq />; proc; auto. 
- move => *. islossless. 
- move => *; proc; auto.
(* encap *)
- proc; inline*; conseq />. auto.
- move => *. islossless; apply encap_ll.
- move=> *; proc; inline*. auto => />; smt(dencseed_ll).
(* decap *)
- proc; inline*; auto => /> &2 H1 H2 H3 H4.
  by move: (x{2}) H4 => [u pk c] /= /#. 
- move =>*; islossless.
- move=> *; proc; inline*. auto => />.
(* chall *)
- proc; inline*. conseq />.
  swap 7 -6. seq 1 1 : (#pre /\ ={es}); first by conseq />; auto. 
  wp. sp. if{2}; first by auto. auto => /> &1 ? E _ H1 H2 ks1 ks2 /> _. 
  move: E. case (snd{1} = u1) => _; case (rcv{1} = u1) => _ /> /= E.
  + split; 1:smt(); split => pks c' k; rewrite get_setE /=.
    case: (pks = pkgen ks1 /\ c' = c{1}) => />; smt(encapK). 
    case: (pks = pkgen ks1 /\ pkgen ks2 = pkgen ks1 /\ c' = c{1}) => />; smt(encapK).
  + split; 1:smt(); split => pks c' k; rewrite get_setE /=.
    case: (pks = pkgen ks1 /\ pkgen ks1 = pkgen ks2 /\ c' = c{1}) => />; smt(encapK).
    case: (pks = pkgen ks1 /\ c' = c{1}) => />; smt(encapK). 
  + split; 1:smt(); split => pks c' k; rewrite get_setE /=.
    case: (pks = pkgen ks2 /\ c' = c{1}) => />; smt(encapK). 
    case: (pks = pkgen ks2 /\ pkgen ks2 = pkgen ks1 /\ c' = c{1}) => />; smt(encapK).
  + split; 1:smt(); split => pks c' k; rewrite get_setE /=.
    case: (pks = pkgen ks2 /\ pkgen ks1 = pkgen ks2 /\ c' = c{1}) => />; smt(encapK).
    case: (pks = pkgen ks2 /\ c' = c{1}) => />; smt(encapK). 
- move=>*; islossless.
- move=> *; proc; inline*. swap 9 -8.
  conseq (:_ ==> true) (:_ ==> _); auto; last by islossless.
  seq 1 : #pre; [by auto;smt()| by conseq />].
by auto => />; smt(emptyE).
qed.

(* In the real game, B(A) corresponds to the game 
   q <$ [1..qc]; G.work(q) *)
local lemma OrealB_Gq &m : 
  Pr [ Game(Oreal, B(A)).main() @ &m : res] = 
  Pr [ M1.Rand(G).main() @ &m : res.`2].
proof.
byequiv => //; proc; inline *; auto.
call (: ={glob Oreal} /\ 
        ={m}(B.OB,Oideal) /\ 
        ={ctr,q}(B.OB,OG)
      ).
- sim.
- sim.
- proc. inline*. sp 2 6.
  by if; [move => />|auto|auto; call(:true); auto]. 
- proc; inline OG.chall B(A, Count(Oreal)).OB.pkey OG.skey OG.pkey.
  wp. sp 3 6. 
  if{1}. 
  + rcondf{2} 4; first by auto => /> /#.
    inline*; by auto. 
  if{1}. 
  + rcondf{2} 4; first by auto => /> /#.
    by inline*; auto. 
  rcondt{2} 4; first by auto => /> /#.
  by inline*; auto. 
- by swap{1} 10 -9; auto.
qed.

(* In the ideal game, B(A) corresponds to the game 
   q <$ [0..qc-1]; G.work(q) *)
local lemma OidealB_Gq1 &m : 
  Pr [ Game(Oideal,B(A)).main() @ &m : res] = 
  Pr [ M0.Rand(G).main() @ &m : res.`2 ].
proof.
byequiv => //; proc; inline *; auto.
call (: ={glob Oreal} /\ ={m}(B.OB,Oideal) /\ ={ctr}(B.OB,OG) /\
  (B.OB.q{1} = OG.q{2} + 1) /\ 
  (forall x, x \in Oideal.m => x \in B.OB.m){1} ).
- conseq />; sim.
- conseq />; sim.
- proc. 
  inline OG.decap B(A, Count(Oideal)).OB.pkey Oideal.skey. 
  sp 2 6. 
  if; [by move => />|by auto|]. inline*. 
  rcondf{1} 8. move => &m0; auto => /> /#.
  by auto.
- proc; inline OG.chall B(A, Count(Oreal)).OB.pkey OG.skey OG.pkey.
  wp. sp 3 6. 
  if{1}. 
  + rcondf{2} 4; first by auto => /> /#. 
    by inline*; auto; smt(mem_set).
  if{1}. 
  + rcondt{2} 4; first by auto => /> /#.
    by inline*; auto; smt(mem_set).
  rcondt{2} 4; first by auto => /> /#.
  by inline*; auto; smt(mem_set).
- swap{1} 11 -10; wp; rnd; rnd; wp. 
  rnd (fun n => n - 1) (fun n => n + 1). 
  auto => />; smt(supp_dinter dinter1E).
qed.

(* Variant of B which counts its own queries *)
local module Bc(O:Oracle) = {
  proc guess() = {
    var r;
    B.OB.q <$ [1..qc];                   
    B.OB.ctr <- 0;                       
    B.OB.m <- empty;
    Count(B(A,CB.Count(O)).OB).init();
    r <@ A(Count(B(A, CB.Count(O)).OB)).guess();
  }
}.

local equiv B_Bc (O<:Oracle{A,B,CB.Count,Count}) : 
    B(A,CB.Count(O)).guess ~ Bc(O).guess : 
    ={glob A, glob B, glob O, glob CB.Count} ==> ={glob A, glob B, glob CB.Count}.
proof.
proc; call (: ={glob B, glob CB.Count, glob O}); last by inline *; auto.
- by sim.
- by proc; inline*; sim.
- by proc; inline*; sim; auto.
proc; inline*; auto.
sim / true : (={glob B, glob CB.Count, glob O,c,k,pks,pk}). 
by auto.
qed.

lemma B_bound:
  forall (O <: Oracle{A,B,CB.Count,Count}),
    hoare[ B(A,CB.Count(O)).guess :
            counts0 CB.Count.ce CB.Count.cd CB.Count.cc ==>
            counts (qe+qc) qd 1 CB.Count.ce CB.Count.cd CB.Count.cc].
proof.
move => O.
conseq (B_Bc(O)) 
(: counts0 CB.Count.ce CB.Count.cd CB.Count.cc ==> 
   counts (qe+qc) qd 1 CB.Count.ce CB.Count.cd CB.Count.cc); 1,2: smt().
proc.
conseq 
  (: _ ==> counts qe qd qc Count.ce Count.cd Count.cc) 
  (: _ ==> counts qe qd qc Count.ce Count.cd Count.cc => 
             counts (qe + qc) qd 1 CB.Count.ce CB.Count.cd CB.Count.cc); 1,2: smt().
- call (: CB.Count.cc = b2i (B.OB.q <= B.OB.ctr) /\
          CB.Count.ce <= Count.ce + Count.cc /\
          CB.Count.cd <= Count.cd).
  + by conseq />.
  + proc; inline*; auto; call(: true); auto => /> /#.
  + proc; inline*; auto; conseq />. 
    seq 3 : (CB.Count.cd < Count.cd); 1: by call(:true); auto => /> /#.
    by if; [auto=>/> /#|wp; call(:true); auto => /> /#].
  + proc; inline*; auto; conseq />. 
    seq 3 : (#[1]pre /\  CB.Count.ce < Count.ce + Count.cc).
      by call(:true); auto => /> /#.
    sp; if; 1: by call(:true); auto; call(:true); auto => /> /#.
    if; 1: by call(:true); auto; call(:true); auto => /> /#.
    by call(:true); auto; call(:true); auto => /> /#.
  + inline*; auto => />; smt(supp_dinter).
- by call (A_bound (<: B(A,CB.Count(O)).OB)); inline*; auto.
qed.

lemma lemma2 &m : 
  `| Pr[ Game(Oreal ,A).main() @ &m : res ] - 
     Pr[ Game(Oideal,A).main() @ &m : res] |
= qc%r * `| Pr[ Game(Oreal ,B(A)).main() @ &m : res] - 
            Pr[ Game(Oideal,B(A)).main() @ &m : res]|.
proof.
rewrite Oreal_G0 Oideal_Gqc OrealB_Gq OidealB_Gq1.
pose ev (_:int) (_:glob G) (b : bool) := b.
have /= -> := M1.Mean_uni G &m ev (1%r/qc%r) _ (finite_dinter 1 qc). 
  by move=> x /supp_dinter1E -> /#.
have /= -> := M0.Mean_uni G &m ev (1%r/qc%r) _ (finite_dinter 0 (qc-1)). 
  by move=> x /supp_dinter1E -> /#.
rewrite /ev /=.
rewrite (eq_big_perm _ _ _ _ (perm_eq_dinter 1 qc)).
rewrite (eq_big_perm _ _ _ _ (perm_eq_dinter_pred 0 qc)).
rewrite [range 0 _]range_ltn 1:#smt big_cons {2}/predT /=. 
rewrite rangeSr 1:#smt big_rcons {1}/predT /=.
rewrite -StdOrder.RealOrder.normrZ; smt(qc_gt0).
qed.

end section PROOF.
  
end Outsider2CCA.

(********************************************)
(** * n-participant version of Outsider-CCA *)
(********************************************)

theory OutsiderCCA.

op n : { int | 0 < n } as n_gt0.
op qe : { int | 0 < qe } as qe_gt0.
op qd : int.

module type Oracle = {
  proc encap (i : int, pk : pkey) : ciphertext * key
  proc decap (j : int, pk : pkey, c : ciphertext) : key option
  proc pkey(i : int) : pkey
}.

module type Oracle_i = {
  proc init () : unit
  include Oracle
}.

module type Adversary (O : Oracle) = {
  proc guess () : bool
}.

abstract theory MkCount.
module Count (O : Oracle) = { 
  var ce, cd : int

  proc init() = {
    ce <- 0;
    cd <- 0;
  } 

  proc pkey = O.pkey

  proc encap(x) = { 
    var r; 
    ce <- ce + 1 ;
    r <@ O.encap(x);
    return r;
  }

  proc decap(x) = { 
    var r; 
    cd <- cd + 1 ;
    r <@ O.decap(x);
    return r;
  }
}.
end MkCount.
clone import MkCount as C.

module Game (O : Oracle_i, A : Adversary) = {
  proc main() = {
    var r;

    O.init();
    Count(O).init();
    r <@ A(Count(O)).guess();
    return r;
  }
}.

(* We are formalizing an on-line version of the Outsider-CCA game,
where the participants are created on-demand. This is relegated to a
PROM which manages the keyseeds of the participants, and from which we
derive keys as needed *)
clone import PROM.FullRO as K with
  type in_t    <- int,
  type out_t   <- keyseed,
  op dout      <- fun _ => dkeyseed,
  type d_in_t  <- unit,
  type d_out_t <- bool
proof*.
module KS = K.RO.

(* We don't want to use an oracle for encseeds at this point 
clone import PROM.FullRO as E with
  type in_t    <- int,
  type out_t   <- encseed,
  op dout      <- fun _ => dencseed,
  type d_in_t  <- unit,
  type d_out_t <- bool.
module ES = E.RO. *)

(* The "real" game: encap and decap answer faithfully. Note that,
unlike in the paper, participants (i.e., their associated keyseed) are
generated "on-demand" whenever the adversary calls an oracle with the
index of a given participant. This matches the behavior of the CV
code. *)
module Oreal : Oracle_i = { 
  proc init() : unit = { 
    KS.init();
  }

  (* provide oracle access to public keys *)
  proc pkey (i : int) = {
    var ks;
    var pk:pkey <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      pk <- pkgen(ks);
    }
    return pk;
  }

  proc encap (i : int,  pk : pkey) : ciphertext * key = { 
    var es,ks,sk;
    var c <-witness;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      es <$ dencseed;
      sk <- skgen(ks);
      (c,k) <- encap es sk pk;
    }
    return (c,k);
  }

  proc decap (i : int, pk : pkey, c : ciphertext) : key option = {
    var ks,sk;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      sk <- skgen(ks);
      k <- decap sk pk c;
    }
    return k;
  } 
}.

(* The "ideal" game: we radmomize the shared key if the revceiver
public key belongs to a participant of the game. *)
module Oideal : Oracle_i = { 
  include Oreal [pkey]
  var m : (pkey * pkey * ciphertext, key) fmap
  
  proc init() = {
    KS.init();
    m <- empty;
  }

  proc encap (i : int,  pk : pkey) : ciphertext * key = { 
    var es,ks,sk,pks,m_ks;
    var c <-witness;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      es <$ dencseed;
      sk <- skgen(ks);
      (c,k) <- encap es sk pk;
      m_ks <@ KS.restrK();
      if (find (fun _ ks => pk = pkgen ks) m_ks <> None)
      { 
        k <$ dkey; 
        pks <- pkgen(ks);
        m.[(pks,pk,c)] <- k;
      }
    }
    return (c,k);
  }

  proc decap (i : int, pk : pkey, c : ciphertext) : key option = {
    var ks,sk,pki;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      pki <- pkgen(ks);
      if ((pk,pki,c) \in m) { 
        k <- m.[pk,pki,c];
      } else {
        sk <- skgen(ks);      
        k <- decap sk pk c;
      }
    }
    return k;
  } 
}.

clone Outsider2CCA as O2 with
  op qe <- qe,
  op qd <- qd,
  op qc <- qe,
  axiom qc_gt0 = qe_gt0
proof*.

(* B is an adversary against the Outsider-2-CCA game. The latter does
not not use KS. Hence, we can use KS to manange keyseeds in B. In
addition, B maintains (redundant) maps from int (user IDs) to public
keys ([mpk]) and (where known) also sekret keys ([msk]). The reason for
this is that two randomly chosen public keys are generated by the 2p
game, making the [pkey] and [skey] procedures cumbersome to reason
about. Moreover, having [mpk] simiplifies reasoning about the bad
event (i.e., collisions among public keys) *)
module (B (A : Adversary) : O2.Adversary) (O2 : O2.Oracle) = {
  module O = {
    var u,v : int
    var f : int -> user
    var m : (pkey * pkey * ciphertext, key) fmap

    (* map of participants and their keys. The map [mpk] enables us to
    express bad_k for B solely in terms of the memory of B (and allows
    us to easyly check whether bad_k has occurred *)
    var mpk : (int, pkey) fmap
    var msk : (int, skey) fmap

    (* internal - don't call on u or v *)
    proc skey (i : int) = {
      var ks;
      
      ks <$ dkeyseed;
      if (i \notin msk) { 
        msk.[i] <- skgen(ks);
        mpk.[i] <- pkgen(ks); (* also generate and store pkey *)
      } 
      return oget (msk.[i]);
    }

    proc pkey (i : int) = {
      var ks,pki;
      if (1 <= i <= n) { 
        if (i \notin mpk) {
          if (i = u \/ i = v) { 
            pki <@ O2.pkey(f i);
            mpk.[i] <- pki;
          } else {
            ks <$ dkeyseed;
            msk.[i] <- skgen(ks); (* also generate and store skey *)
            mpk.[i] <- pkgen(ks); 
          }
        }
      }
      return oget mpk.[i];
    }

    proc encap (i : int, pk : pkey) = {
      var ski,pki,oj,es;
      var c <- witness;
      var k <- witness;
      if (1 <= i <= n) { 
        (* get pkey for i and ensure it has been sampled *)
        pki <@ pkey(i);
        (* determine whether pk belongs to some participant *)
        oj <- find (fun _ pkj => pk = pkj) mpk;
        
        if   (i = u /\ oj = Some v) 
        { (c,k) <- O2.chall(f u, f v); }
        elif (i = u \/ i = v) 
        { (c,k) <- O2.encap(f i, pk); }
        else 
        { (* msk.[i] defined due to pkey call and i <> u,v *) 
          ski <- oget (msk.[i]); 
          es <$ dencseed;
          (c,k) <- encap es ski pk; }
        
        if (oj <> None /\ (u < i \/ i = u /\ v < oget oj)) {
           k <$ dkey;
           pki <- oget (mpk.[i]);
           m.[(pki,pk,c)] <-k;
        }
      }
      return (c,k);
    }

    proc decap (i : int, pk : pkey, c : ciphertext) : key option = { 
      var sk,pki;
      var k <- witness;
      if (1 <= i <= n) {
        pki <@ pkey(i);
        if ((pk,pki,c) \in m) { 
          k <- m.[pk,pki,c];
        } else {
          if (i = u \/ i = v) {
            k <@ O2.decap(f i,pk, c);
          } else {
            sk <- oget msk.[i];
            k <- decap sk pk c;
          }
        }
      }
      return k;
    }
  }
      
  proc guess() = { 
    var r:bool <- witness;
    (O.u,O.v) <$ [1..n] `*` [1..n];
    O.m <- empty;
    O.mpk <- empty;
    O.msk <- empty;
    O.f <- fun x => if x = O.u then u1 else u2;
    r <@ A(O).guess();
    return r;
  }
}.

op bad_k' (m : (int,pkey) fmap) = 
  exists i j, i <> j /\ i \in m /\ j \in m /\ m.[i] = m.[j].

module (Bbad (A : Adversary) : O2.Adversary) (O2 : O2.Oracle) = { 
  proc guess() = {
    var r; 

    (* We don't actually do any counting, but calling Count(..).init()
    here makes it part of glob Bbad, allowing us to to later slip in a
    counting wrapper *)
    Count(B(A,O2).O).init();

    r <@ B(A,O2).guess();
    return r /\ !bad_k' B.O.mpk;
  }
}.

section PROOF.

declare module A <: Adversary{Oreal,Oideal,Count,B,
                              O2.C.Count, O2.Oreal, O2.Oideal,O2.B, O2.CB.Count}.

declare axiom A_ll : forall (O <: Oracle{A}),
  islossless O.encap =>
  islossless O.decap => 
  islossless O.pkey =>
  islossless A(O).guess.

(* A makes at most qe encap queres, qd decap queries, and 0 challenge
queres (there is no challenge oracle) *)
declare axiom A_bound (O <: Oracle) :
  hoare [ A(Count(O)).guess : 
    O2.counts0 Count.ce Count.cd 0 ==> 
    O2.counts qe qd 0 Count.ce Count.cd 0].

(* We define an indexed collection of games G_{u,v} where 1<=u<=n
and 0<=v<= n. We will then prove 4 main lemmas:

1) G_{n,n} perfectly simulates Game(Oreal,A)
2) G_{1,0} perfectly simulates Game(Oideal,A)
3) O2.Game(O2real,B(A)) can be simulated by 
   sampling 1<=u,v<=n randomly and then running G_{u,v}
4) O2.Game(O2ideal,B(A)) can be simulated by 
   sampling 1<=u<=n and 0<=v<=n-1 randomly and then running G_{u,v}
   (which is equivalent to sampling 1<=u,v<=n then running G_{u,v-1})
5) G_{u,n} perfectly simulates G_{u+1,0} whenever 1 <= u < n

Here, O2real and O2ideal are variants of the 2p games where, as in the
n-participant games, keys are generated on-demand. For (3) and (4) it
is convenient to express G_{u,v} as a [Worker] module for the [Means]
game, allowing us to apply the [Mean_uni] lemma. 

For all five claims, we prove the equivalence assuming that there are
no collisions among the public keys. However, only the proof of Claim
4 depends on this *)

(* bad key event: there are two participants i and j sharing a public
key (i.e. sharing keyseeds leading to the same public key *)
op bad_k (m : (int, keyseed) fmap) = fcoll pkgen m.


local lemma bad_bad' m : bad_k m <=> bad_k' (map (fun _ ks => pkgen ks) m).
proof. 
by rewrite /bad_k /bad_k' /fcoll; smt(mem_map mapE oget_omap_some).
qed.

(* Need two clones, since the distribution is an operator of the theory *)
local clone Means as M1 with
  type input <- int * int,
  type output <- bool,
  op d <- [1..n] `*` [1..n]
proof *.

local clone Means as M0 with
  type input <- int * int,
  type output <- bool,
  op d <- [1..n] `*` [0..n-1]
proof *.

local module OG : Oracle = {
  include Oreal [init,pkey]
  include var Oideal[decap]
  var u,v : int

  proc encap (i : int,  pk : pkey) : ciphertext * key = { 
    var es,ks,sk,pks,m_ks,oj;
    var c <-witness;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      es <$ dencseed;
      sk <- skgen(ks);
      (c,k) <- encap es sk pk;
      m_ks <@ KS.restrK();
      oj <- find (fun _ ks => pk = pkgen ks) m_ks;
      if (oj <> None /\ (u < i \/ i = u /\ v < oget oj))
      { 
        k <$ dkey; 
        pks <- pkgen(ks);
        m.[(pks,pk,c)] <- k;
      }
    }
    return (c,k);
  }
}.

local module G : M1.Worker = {

  proc work(u:int,v:int) = {
    var r;

    Oideal.init();
    OG.u <- u;
    OG.v <- v;
    r <@ A(OG).guess();
    return r;
  }
}.

(* Claim 1 *)
local lemma Oreal_Gnn &m : 
  Pr[ Game(Oreal ,A).main() @ &m : res /\ !bad_k KS.m ] = 
  Pr[ G.work(n,n) @ &m : res /\ !bad_k KS.m ].
proof.
byequiv => //; proc; inline*.
call(: OG.u{2} = n /\ OG.v{2} = n /\ ={KS.m} /\ (Oideal.m = empty){2} /\
       forall i, i \in KS.m{2} => 1 <= i <= n ).
- proc; inline Oreal.encap; sp; if; 1,3: by auto. 
  seq 4 5 : (={pk,i,ks,es,c,k} /\ ={KS.m} /\ (Oideal.m = empty){2} /\
             OG.u{2} = n /\ OG.v{2} = n /\ (i \in KS.m){2} /\ (m_ks = KS.m){2} /\ 
             (forall i, i \in KS.m => 1 <= i <= n){2}).
    inline*; auto => />; smt(mem_set).
  rcondf{2} 2; last by auto.
  auto => &2 /> ? ks_bound; rewrite negb_and -implybE => /find_not_none /> j ks -> /#.
- proc; inline Oreal.decap; sp; if; 1,3: by auto.
  by inline KS.get; auto => />; smt(mem_set mem_empty).
- proc; inline*; sp; if; 1,3: by auto. auto => />; smt(mem_set).
auto => />; smt(mem_empty).
qed.

(* Claim 2 *)
local lemma Oideal_G10 &m : 
   Pr[ Game(Oideal ,A).main() @ &m : res /\ !bad_k KS.m ] = 
   Pr[ G.work(1,0) @ &m : res /\ !bad_k KS.m ].
proof.
byequiv => //; proc; inline*.
call(: OG.u{2} = 1 /\ OG.v{2} = 0 /\ ={KS.m, Oideal.m} /\ 
       forall i, i \in KS.m{2} => 1 <= i <= n ).
- proc; inline Oideal.encap; sp; if; 1,3: by auto. 
  seq 5 5 : (={pk,i,ks,es,c,k,m_ks} /\ ={KS.m, Oideal.m} /\
             OG.u{2} = 1 /\ OG.v{2} = 0 /\ (m_ks = KS.m){2} /\ (i \in KS.m){2} /\ 
             (forall i, i \in KS.m => 1 <= i <= n){2}).
  + by inline*; auto => />; smt(mem_set).
  sp; if; 2,3: by auto. 
  by move => &1 &2 /> ? ks_bound /find_not_none /> j ks -> /#.
- proc; inline Oideal.decap; sp; if; 1,3: by auto.
  by inline KS.get; auto => />; smt(mem_set).
- proc; inline*; sp; if; 1,3: by auto. auto => />; smt(mem_set).
auto => />; smt(mem_empty).
qed.

(* For Claims (3) and (4), we first need to show the equivalence
bewtween the standard (offline) 2p game (i.e., where the two keypairs
are sampled initially) and an online version where keys are sampled
on-demand. *)

local clone PROM.FullRO as K2 with
  type in_t    <- user,
  type out_t   <- keyseed,
  op dout      <- fun _ => dkeyseed,
  type d_in_t  <- unit,
  type d_out_t <- bool
proof*.

local clone K2.FinEager as EK2 with
  theory FinFrom <- UserFinType
proof*.

local module ERO = EK2.FinRO.

(* Variant of the 2p real game where the keys are handled by an oracle *)
local module O2real(K2 : K2.RO) : O2.Oracle_i = {
  proc init() = {
    K2.init();
  }

  proc pkey (u : user) = { 
    var ks;

    ks <@ K2.get(u);
    return (pkgen ks);
  }

  proc skey (u : user) = {
    var ks;

    ks <@ K2.get(u);
    return (skgen ks);
  }

    proc encap (u : user, pk : pkey) = {
    var c,k,sk,es;
   
    sk <@ skey(u);
    es <$ dencseed;
    (c,k) <- encap es sk pk;
    return (c,k);  
  }

  proc decap (u : user, pk : pkey, c : ciphertext) = {
    var k,sk;

    sk <@ skey(u);
    k <- decap sk pk c;
    return k;
  }

  proc chall (snd : user, rcv : user) = {
    var pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed;

    (c,k) <- encap es sk pk;
    return (c,k);
  }

}.

(* Variant of the 2p ideal game where the keys are handled by an oracle *)
local module O2ideal (K2 : K2.RO) : O2.Oracle_i = {
  include var O2real(K2)[-init,chall,decap]
  var m : (pkey * pkey * ciphertext, key) fmap

  proc init() = {
    K2.init();
    m <- empty;
  }

  proc decap (u : user, pk : pkey, c : ciphertext) = {
    var k,sku,pku;

    sku <@ skey(u);
    pku <@ pkey(u); 

    if ((pk,pku,c) \in m) {
      k <- m.[(pk,pku,c)];
    } else { 
      k <- decap sku pk c;
    }
    return k;
  }

  proc chall (snd : user, rcv : user) = {
    var pks, pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed;
    (c,k) <- encap es sk pk;
    k <$ dkey;
    pks <@ pkey(snd); 
    m.[(pks,pk,c)] <- k;
    return (c,k);
  }
}.

(* To prove the equivalences, we express both sides as
[FinRO_Distinguisher] and then use the [RO_FinRO_D] lemma to
transition from an eager oracle to a lazy one *)

local module (Dreal (C : O2.Adversary) : EK2.FinRO_Distinguisher) (K2 : K2.RO) = {
  proc distinguish() = {
    var r;
    O2.C.Count(O2real(K2)).init();
    r <@ C(O2.C.Count(O2real(K2))).guess();
    return r;
  }
}.

local equiv O2real_lazy (C <: O2.Adversary{K2.RO,O2.Oreal,O2real,O2.C.Count,K2.FRO}) :
  O2.Game(O2.Oreal, C).main ~ O2.Game(O2real(K2.RO), C).main 
  : ={glob C,glob O2.C.Count} ==> ={res,glob C}.
proof.
transitivity O2.Game(O2real(ERO),C).main 
  (={glob C,glob O2.C.Count} ==> ={res,glob C}) 
  (={glob C,glob O2.C.Count} ==> ={res,glob C}); 1,2: smt().
- proc; inline*. 
  rcondt{2} 3; 1: by auto.
  rcondt{2} 6; 1: by auto; smt(emptyE).
  rcondt{2} 8; 1: by auto.
  rcondt{2} 11; 1: by auto => />; smt(get_setE emptyE).
  rcondf{2} 13; 1: by auto.
  wp.
  call (: (forall u, u \in K2.RO.m){2} 
          /\ O2.Oreal.sk1{1} = skgen (oget K2.RO.m.[u1]{2})
          /\ O2.Oreal.pk1{1} = pkgen (oget K2.RO.m.[u1]{2})
          /\ O2.Oreal.sk2{1} = skgen (oget K2.RO.m.[u2]{2})
          /\ O2.Oreal.pk2{1} = pkgen (oget K2.RO.m.[u2]{2})
    ); 1..4: by proc; inline*; auto => />; smt(get_setE).
  by auto => /> /=; smt(get_setE).
transitivity K2.MainD(Dreal(C),ERO).distinguish
  (={glob C,glob O2.C.Count} ==> ={res,glob C}) 
  (={glob C,glob O2.C.Count} ==> ={res,glob C}); 
    1,2: smt(); first by proc; inline*; sim.
transitivity K2.MainD(Dreal(C),K2.RO).distinguish
  (={glob C,glob O2.C.Count} ==> ={res,glob C}) 
  (={glob C,glob O2.C.Count} ==> ={res,glob C}); 
    1,2: smt(); last by proc; inline*; sim.
have X := EK2.RO_FinRO_D _ (Dreal(C)); 1: smt(dkeyseed_ll). 
by symmetry; conseq X; auto. 
qed.

local module (Dideal (C : O2.Adversary) : EK2.FinRO_Distinguisher) (K2 : K2.RO) = {
  proc distinguish() = {
    var r;
    O2ideal.m <- empty;
    O2.C.Count(O2ideal(K2)).init();
    r <@ C(O2.C.Count(O2ideal(K2))).guess();
    return r;
  }
}.

local equiv O2ideal_lazy (C <: O2.Adversary{K2.RO,O2.Oideal,O2ideal,O2.C.Count,K2.FRO}) :  
  O2.Game(O2.Oideal, C).main ~ O2.Game(O2ideal(K2.RO), C).main 
  : ={glob C,glob O2.C.Count} ==> ={res, glob C}.
proof.
transitivity O2.Game(O2ideal(ERO),C).main 
  (={glob C,glob O2.C.Count} ==> ={res,glob C}) 
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res,glob C}); 1,2: smt().
- proc; inline*. 
  rcondt{2} 3; 1: by auto.
  rcondt{2} 6; 1: by auto; smt(emptyE).
  rcondt{2} 8; 1: by auto.
  rcondt{2} 11; 1: by auto => />; smt(get_setE emptyE).
  rcondf{2} 13; 1: by auto.
  wp.
  call (: (forall u, u \in K2.RO.m){2} 
          /\ O2.Oreal.sk1{1} = skgen (oget K2.RO.m.[u1]{2})
          /\ O2.Oreal.pk1{1} = pkgen (oget K2.RO.m.[u1]{2})
          /\ O2.Oreal.sk2{1} = skgen (oget K2.RO.m.[u2]{2})
          /\ O2.Oreal.pk2{1} = pkgen (oget K2.RO.m.[u2]{2})
          /\ ={m}(O2.Oideal,O2ideal)
    ); 1..4: by proc; inline*; auto => />; smt(get_setE).
  by auto => /> /=; smt(get_setE).
transitivity K2.MainD(Dideal(C),ERO).distinguish
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res,glob C}) 
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res,glob C}); 
    1,2: smt(); first by proc; inline*; sim.
transitivity K2.MainD(Dideal(C),K2.RO).distinguish
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res,glob C}) 
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res,glob C}); 
    1,2: smt(); last by proc; inline*; sim.
have X := EK2.RO_FinRO_D _ (Dideal(C)); 1: smt(dkeyseed_ll). 
by symmetry; conseq X; auto => />.
qed.

(* Claim 3 *)
local lemma OrealB_Guv &m : 
  Pr [ O2.Game(O2.Oreal, B(A)).main() @ &m : res /\ !bad_k' B.O.mpk] = 
  Pr [ M1.Rand(G).main() @ &m : res.`2 /\ !bad_k KS.m].
proof.
have -> : Pr[O2.Game(O2.Oreal, B(A)).main() @ &m : res /\ !bad_k' B.O.mpk ] =
          Pr[O2.Game(O2real(K2.RO), B(A)).main() @ &m : res /\ !bad_k' B.O.mpk ].
  by byequiv (O2real_lazy (B(A))); smt().
byequiv => //; proc; inline *. 
wp. call (: ={u,v}(B.O,OG)  
            /\ (B.O.f{1} = fun i => if i = B.O.u then u1 else u2){1}
            /\ B.O.mpk{1} = map (fun _ ks => pkgen ks) RO.m{2}
            /\ (forall i, i <> OG.u{2} => i <> OG.v{2} => B.O.msk.[i]{1} = omap skgen RO.m.[i]{2})
            /\ (forall i, !(1 <= i <= n) => B.O.mpk.[i] = None){1}
            /\ (forall i, i = OG.u{2} \/ i = OG.v{2} => K2.RO.m.[B.O.f i]{1} = RO.m.[i]{2})
            /\ ={m}(B.O,Oideal)
          ). 
- proc; sp; if; 1,3: by auto.
  seq 1 1 : (#[/5:]pre /\ pki{1} = pkgen ks{2} /\ KS.m.[i]{2} = Some ks{2}). 
  + (* redo pkey proof ... *) 
    inline*. rcondt{1} 2; 1: by auto. sp.
    if{1}. 
    + rcondt{2} 2; first by auto => />; smt(mem_map).
      if{1}. 
      * rcondt{1} 4; 1: by auto => />; smt(fmapP mem_map oget_map).
        wp. rnd. auto. move => /> &1 &2; smt(get_setE map_set). 
      * wp. rnd. auto. move => />; smt(fmapP get_setE map_set). 
    + rcondf{2} 2; first by auto => />; smt(mem_map). 
      auto => />; smt(oget_map mem_map).
  seq 2 3 : (#pre /\ ={c,k} /\ (oj = find (fun (_ : int) (pkj : pkey) => pk = pkj) B.O.mpk){1}).
  + sp; if{1}; last if{1}.
    * (* challenge oracle query *)
      inline*. (* TODO: cleanup *)
      rcondf{1} 7; first by auto => />; smt(fmapP). 
      rcondf{1} 12. 
        auto => />. progress. case (OG.v{m0} = OG.u{m0}) => ?. smt(). 
        move/find_some : H5 => -[pku]. rewrite mapE /= -H1 //= ifF //. smt().
      auto => /> &1 &2 2? HK2 2? Hu Hv 4? es _. rewrite !HK2 //. have /= -> := HK2 (OG.u{2}).
      rewrite Hu. case/find_some: Hv => pk'. rewrite mapE /=. smt().
    * (* encap oracle query *)
      inline*. 
      rcondf{1} 7; first by auto => />; smt(fmapP). 
      by auto => /> &1 &2 ? ? HK2 ? ? ? ? ? _ _ es _; rewrite HK2 // /#. 
    * (* encapsulate locally *)
      by auto => />; smt(). 
  inline KS.restrK; sp. 
  if; 2,3: by auto => />; smt(oget_map mem_map). 
  by move => /> ? ?; rewrite !find_map /#.
- proc; sp; if; 1,3: by auto.
  inline B(A, O2.C.Count(O2real(K2.RO))).O.pkey KS.get; sp.
  seq 2 4 : (#pre /\ ={pki} /\ pki{1} = pkgen ks{2} /\ KS.m.[i]{2} = Some ks{2}). 
  (* redo pkey proof once again *)
  + inline*. rcondt{1} 1; first by auto. 
    if{1}.
    + rcondt{2} 2; first by auto => />; smt(mem_map).
      if{1}.
      * rcondt{1} 4; 1: by auto => />; smt(fmapP mem_map oget_map).
        wp. rnd. auto. move => /> &1 &2; smt(get_setE map_set).
      * wp. rnd. auto. move => />; smt(fmapP get_setE map_set).
    + rcondf{2} 2; first by auto => />; smt(mem_map).
      auto => />; smt(oget_map mem_map).
  if; 1,2: by auto. 
  if{1}. 
  + inline*.
    rcondf{1} 7; first by auto => /> /#.
    by auto => /> &1 &2 ? ? HK2 ? ? ? ? ? _ _; rewrite HK2 //= /#. 
  + inline*. 
    by auto => /> &1 &2 Hmsk ? HK2 ? ? ? ? ?; rewrite Hmsk //= /#. 
- proc. sp. inline*. if; 1,3: by auto => /#.
  if{1}. 
  + rcondt{2} 3; first by auto => />; smt(mem_map).
    if{1}. 
    * rcondt{1} 4; 1: by auto => />; smt(fmapP mem_map oget_map).
      wp. rnd. auto. move => /> &1 &2; smt(get_setE map_set). 
    * wp. rnd. auto. move => />; smt(fmapP get_setE map_set). 
  + rcondf{2} 3; first by auto => />; smt(mem_map). 
    auto => />; smt(oget_map mem_map).
auto => />. progress; 1..4: smt(map_empty emptyE). 
apply: contra H8 => -[i j] *; exists i j; smt(mapE mem_map). 
apply: contra H8 => -[i j] *; exists i j; smt(mapE mem_map). 
qed.

(*** Claim 4 ***) 

(* For Claim 4 we need to maintain the connection between the log of
randomized encapsulation queries in the Oideal game on the one side
and the log maintained by B (for queries it randomizes) and the log
maintained by O2ideal for the randomized challenge queries. Note that
the logging is based on public keys, and those are only sampled during
the game. 

More precisely, an entry (pki,pkj,c) gets logged to O2ideal when the
keys for both u and v (u and v being sampled by B) have already been
sampled, and pki (pkj) is the public key of participant u (v). All
other queries are logged by B itself 

The absence of public key collisions is required to ensure that the
mapping between (active) users and public keys remains bijective. This
ensures that the stored answers (c,k) to [encap(i,pk_j)] are correctly
retrieved when answering queries to [decap(j,pk_i,c)].

Moreover, this is required to rule out that queries already logged in
B are suddenly in the wrong log if u or v gets assigned a pre-existing
public key, or the other way around for queries logged in O2ideal *)

local op p (mpk : (int,pkey) fmap) u v (x : pkey*pkey*ciphertext) (_ : key) = 
  u \in mpk /\ v \in mpk /\ x.`1 = oget mpk.[u] /\ x.`2 = oget mpk.[v].

local op q (mpk : (int,pkey) fmap) u v (x : pkey*pkey*ciphertext) (_ : key) = 
  u \notin mpk \/ v \notin mpk \/ x.`1 <> oget mpk.[u] \/ x.`2 <> oget mpk.[v].

(* We first show that sampling a new public key preserves the
invariants on the keyseed oracles, the logs, as well as as [mpk] and
[msk]. This is used multiple times *)
local equiv eqv_pki_ks i : 
  B(A, O2.C.Count(O2ideal(K2.RO))).O.pkey ~ KS.get : 
     arg{1} = i /\ arg{2} = i /\ 1 <= i <= n
  /\ ! bad_k KS.m{2}
  /\ (B.O.f{1} = fun i => if i = B.O.u then u1 else u2){1}
  /\ B.O.mpk{1} = map (fun _ ks => pkgen ks) RO.m{2}
  /\ (forall i, i <> B.O.u{1} => i <> B.O.v{1} => B.O.msk.[i]{1} = omap skgen RO.m.[i]{2})
  /\ (forall i, !(1 <= i <= n) => RO.m.[i] = None){2}
  /\ (forall i, i = B.O.u{1} \/ i = B.O.v{1} => K2.RO.m.[B.O.f i]{1} = RO.m.[i]{2})
  /\ (O2ideal.m{1} = filter (p B.O.mpk B.O.u B.O.v){1} Oideal.m{2}) 
  /\ ( B.O.m{1} = filter (q B.O.mpk B.O.u B.O.v){1} Oideal.m{2})
  /\ (forall pki pkj c, (pki,pkj,c) \in Oideal.m{2} =>
        pki \in frng B.O.mpk{1} /\ pkj \in frng B.O.mpk{1})
  ==> 
     ! bad_k KS.m{2}
  /\ (B.O.f{1} = fun i => if i = B.O.u then u1 else u2){1}
  /\ B.O.mpk{1} = map (fun _ ks => pkgen ks) RO.m{2}
  /\ (forall i, i <> B.O.u{1} => i <> B.O.v{1} => B.O.msk.[i]{1} = omap skgen RO.m.[i]{2})
  /\ (forall i, !(1 <= i <= n) => RO.m.[i] = None){2}
  /\ (forall i, i = B.O.u{1} \/ i = B.O.v{1} => K2.RO.m.[B.O.f i]{1} = RO.m.[i]{2})
  /\ (res{1} = pkgen res{2} /\ KS.m.[i]{2} = Some res{2})
  /\ (O2ideal.m{1} = filter (p B.O.mpk B.O.u B.O.v){1} Oideal.m{2}) 
  /\ ( B.O.m{1} = filter (q B.O.mpk B.O.u B.O.v){1} Oideal.m{2})
  /\ (forall pki pkj c, (pki,pkj,c) \in Oideal.m{2} =>
        pki \in frng B.O.mpk{1} /\ pkj \in frng B.O.mpk{1})
  /\ res{1} = pkgen res{2} /\ KS.m.[i]{2} = Some res{2} 
  \/ (bad_k' B.O.mpk{1} /\ bad_k KS.m{2}).
proof.
proc; rcondt{1} 1; first by auto => />.
if{1}; last first.
(* known key *)
rcondf{2} 2; first by auto => />; smt(mem_map). 
conseq />. auto => /> &1 &2 7?. rewrite mem_map => /fmapP [ks_i Hi] *. 
by rewrite oget_map 1:/# /= Hi.
(* new key *)
rcondt{2} 2. auto => />. smt(mem_map). 
if{1}.
- (* sampling in O2 *)
  inline*. rcondt{1} 4; first by auto => />; smt(mem_map).
  auto => &1 &2 /=. 
  rewrite -!andbA => -[?] [?] [?] [?] [?] [?] [?] [HK2] [?] [?] [?] [logP] [iNm] i_uv ks -> /=.
  rewrite get_set_sameE /=. 
  case: (bad_k RO.m{2}.[x{2} <- ks]) => [bad_k | nbad_k] /=.
    move/bad_bad' : bad_k; smt(map_set).
  do ! split; 1..7,11..12: smt(map_set get_setE oget_omap_some); last first. 
    smt(frng_set fmap_eqP remE in_fsetU1).
  + subst. apply eq_in_filter => -[pki pkj c k] Hk. 
    rewrite mem_map in iNm. rewrite /p !mem_map /=.
    case: i_uv => ?; subst; rewrite iNm /=. 
    * apply: contra nbad_k. rewrite get_set_sameE /= => -[_] [_] [Hi] _.
      have [/mem_frng @/rng [x]] := logP pki pkj c _;1: smt(). 
      rewrite mapE /= => /omap_some [ks' [x_ks' ks'_pki]] _. exists B.O.u{1} x; smt(mem_set get_setE).
    * apply: contra nbad_k. rewrite get_set_sameE /= => -[_] [_] [_] Hi.
      have [_ /mem_frng @/rng [x]] := logP pki pkj c _;1: smt(). 
      rewrite mapE /= => /omap_some [ks' [x_ks' ks'_pki]]. exists B.O.v{1} x; smt(mem_set get_setE). 
  + subst. apply eq_in_filter => -[pki pkj c k] Hk. 
    rewrite mem_map in iNm. rewrite /q !mem_set !mem_map !negb_or /=. 
    have := logP pki pkj c _; 1: smt().
    rewrite !mem_frng /rng => -[[x_i ks_i] [x_j ks_j]]. 
    move: ks_i. rewrite mapE => /omap_some [ks_i [m_xi /= pksi]]. 
    move: ks_j. rewrite mapE => /omap_some [ks_j [m_xj /= pksj]]. subst.
    case: i_uv => ?; subst; rewrite iNm get_set_sameE /=. 
    * apply: contraR nbad_k; rewrite !negb_or !negb_and !negbK => -[_ [Hi _]].
      exists B.O.u{1} x_i; smt(mem_set get_setE). 
    * apply: contraR nbad_k; rewrite !negb_or !negb_and !negbK => -[_ [_ Hi]].
      exists B.O.v{1} x_j; smt(mem_set get_setE). 
- (* sampling in B *)
  auto => &1 &2 /=. 
  rewrite !andbA; do ! case => 8? HK2 2? logP iNm i_uv ks -> /=.
  rewrite !get_set_sameE /=. 
  case: (bad_k RO.m{2}.[x{2} <- ks]) => [bad_k | nbad_k] /=.
    subst. case: bad_k => u v X. exists u v. 
    rewrite !mem_set !mem_map. rewrite !mem_set in X. 
    rewrite !get_setE !mapE /=; smt(get_setE).
  do ! split; 1..6,10: smt(map_set get_setE oget_omap_some); last first.
    smt(frng_set fmap_eqP remE in_fsetU1).
  + subst. apply eq_in_filter => -[pki pkj c k] Hk. 
    rewrite mem_map in iNm. rewrite /p !mem_map /=.
    rewrite !get_setE !ifF 1,2:/#. rewrite !mem_set; smt(mem_map).
  + subst. apply eq_in_filter => -[pki pkj c k] Hk. 
    rewrite mem_map in iNm. rewrite /q !mem_map /=.
    rewrite !get_setE !ifF 1,2:/#. rewrite !mem_set; smt(mem_map).
qed.

(* sampling new keys perserves key collisions - B.pkey *)
local lemma pkey_bad' : 
  hoare [B(A, O2.C.Count(O2ideal(K2.RO))).O.pkey : bad_k' B.O.mpk ==> bad_k' B.O.mpk].
proof.
proc; do 2! (if; last by auto). 
if; last by auto => &m /> i j *; exists i j; smt(mem_set get_setE).
inline*; seq 6 : #pre; first by auto. 
auto => &m /> i j *. exists i j; smt(mem_set get_setE).
qed.

(* sampling new keys perserves key collisions -KS.get *)
local lemma get_bad : hoare [KS.get : bad_k KS.m ==> bad_k KS.m ].
proof. 
proc; seq 1 : #pre; first by auto. 
if; last by auto. 
auto => &m /> i j *; exists i j; smt(mem_set get_setE).
qed.

(* Claim 4 *)
local lemma OidealB_Guv1 &m : 
  Pr [ O2.Game(O2.Oideal, B(A)).main() @ &m : res /\ !bad_k' B.O.mpk ] = 
  Pr [ M0.Rand(G).main() @ &m : res.`2 /\ !bad_k KS.m].
proof.
have -> : Pr[O2.Game(O2.Oideal, B(A)).main() @ &m : res /\ !bad_k' B.O.mpk] =
          Pr[O2.Game(O2ideal(K2.RO), B(A)).main() @ &m : res  /\ !bad_k' B.O.mpk ].
  by byequiv (O2ideal_lazy (B(A))); smt(). 
byequiv => //; proc; inline *. 
wp.
call (:  bad_k KS.m, 
         ={u}(B.O,OG) /\ B.O.v{1} - 1 = OG.v{2}
      /\ (B.O.f{1} = fun i => if i = B.O.u then u1 else u2){1}
      /\ B.O.mpk{1} = map (fun _ ks => pkgen ks) RO.m{2}
      /\ (forall i, i <> B.O.u{1} => i <> B.O.v{1} => B.O.msk.[i]{1} = omap skgen RO.m.[i]{2})
      /\ (forall i, !(1 <= i <= n) => RO.m.[i] = None){2}
      /\ (forall i, i = B.O.u{1} \/ i = B.O.v{1} => K2.RO.m.[B.O.f i]{1} = RO.m.[i]{2})
      /\ (O2ideal.m{1} = filter (p B.O.mpk B.O.u B.O.v){1} Oideal.m{2}) 
      /\ ( B.O.m{1} = filter (q B.O.mpk B.O.u B.O.v){1} Oideal.m{2})
      /\ (forall pki pkj c, (pki,pkj,c) \in Oideal.m{2} =>
              pki \in frng B.O.mpk{1} /\ pkj \in frng B.O.mpk{1}),
        (* B.O.mpk and KS.m may diverge after bad has been triggered, 
           but then both bad_k' and bad_k hold and are preserved *)
        bad_k' B.O.mpk{1} /\ bad_k KS.m{2}
      ).
- exact A_ll. 
- (* encap *)
  proc; sp; if; 1,3: by auto.
  seq 1 1 : (#[/5:]pre /\ pki{1} = pkgen ks{2} /\ KS.m.[i]{2} = Some ks{2} 
            \/ bad_k' B.O.mpk{1} /\ bad_k KS.m{2}). 
  + exlim i{2} => i; call (eqv_pki_ks i); auto; smt(). 
  case (bad_k' B.O.mpk{1} /\ bad_k KS.m{2}). 
  + conseq (: bad_k' B.O.mpk{1} /\ bad_k KS.m{2} ==> 
              bad_k' B.O.mpk{1} /\ bad_k KS.m{2}); 1,2: smt().
    conseq />. 
    seq 0 6 : true. 
      by conseq (: true ==> _) _ (: true ==> true : =1%r); islossless. 
    by conseq (: true ==> _) (: true ==> true : =1%r); islossless. 
          (* (equi)termination *) 
  conseq (: !bad_k KS.m{2} /\ ={i,pk}
      /\ ={u}(B.O,OG) /\ B.O.v{1} - 1 = OG.v{2}
      /\ (B.O.f{1} = fun i => if i = B.O.u then u1 else u2){1}
      /\ B.O.mpk{1} = map (fun _ ks => pkgen ks) RO.m{2}
      /\ (forall i, i <> B.O.u{1} => i <> B.O.v{1} => B.O.msk.[i]{1} = omap skgen RO.m.[i]{2})
      /\ (forall i, !(1 <= i <= n) => RO.m.[i] = None){2}
      /\ (forall i, i = B.O.u{1} \/ i = B.O.v{1} => K2.RO.m.[B.O.f i]{1} = RO.m.[i]{2})
      /\ (O2ideal.m{1} = filter (p B.O.mpk B.O.u B.O.v){1} Oideal.m{2}) 
      /\ ( B.O.m{1} = filter (q B.O.mpk B.O.u B.O.v){1} Oideal.m{2})
      /\ (forall pki pkj c, (pki,pkj,c) \in Oideal.m{2} =>
              pki \in frng B.O.mpk{1} /\ pkj \in frng B.O.mpk{1})
      /\ pki{1} = pkgen ks{2} /\ KS.m.[i]{2} = Some ks{2} ==> _); 1: smt().
  sp. 
  if{1}.
  + (* challenge query (with randomized k) *)
    inline*.
    rcondf{1} 7; first by auto => /> /#.
    rcondf{1} 12. 
      auto => /> &hr 3? HK2 2?; rewrite find_map /= => /find_some [ksv] [? ?] *.
      by rewrite fmapP; exists ksv; rewrite HK2.
    rcondf{1} 20; first by auto => /> /#.
    rcondf{1} 25; first by auto => /> /#. 
    rcondt{2} 6; first by auto => /> &1; rewrite !find_map /#.
    wp. rnd{1}; wp. rnd. auto => /> &1 &2; rewrite !find_map. progress. 
    * rewrite H2 //=; smt(find_some). 
    * case/find_some: H5 => ks_y [/= Hy1 Hy2]. 
      rewrite filter_set /= {2}/p !oget_map 1,2:/# /=. 
      rewrite [if _ /\ _ then _ else _]ifT; smt(mem_map). 
    * case/find_some: H5 => ks_y [/= Hy1 Hy2] /=.
      rewrite filter_set /= {2}/q !oget_map 1,2:/# /=.
      rewrite [if _ \/ _ then _ else _]ifF. smt(mem_map). 
      rewrite rem_filterE /q //=. rewrite !oget_map 1,2:/#. smt(mem_map).
    * case/mem_set: H11 => [/#|]. move => />.  
      rewrite mem_frng /rng; exists OG.u{2}; by rewrite mapE H4.
    * case/mem_set: H11 => [/#|]. move => />.  
      case/find_some: H5 => ks_y [/= Hy1 Hy2] /=. 
      by rewrite mem_frng /rng; exists B.O.v{1}; rewrite mapE Hy1 /= Hy2.
   + seq 1 3 : (#pre /\ ={c,k}). 
     * if{1}. 
       - inline*. 
         rcondf{1} 7; first by auto => /> /#. 
         conseq />. auto => /> &1 &2 nbad 2? HK2 *. 
         by have -> := HK2 i{2} _; smt().  
       - swap{1} 2 -1. auto => /> &1 &2 nbad Hmsk 3? m_i *. 
         rewrite Hmsk 1,2:/#. by rewrite m_i.
     inline KS.restrK. sp.
     if. 
     * move => &1 &2; rewrite !andbA; do ! case => ? oj1 oj2 15? ioj *.
       have {oj1 oj2} ? : oj{1} = oj{2}; subst; 1: by rewrite find_map.
       case: (oj{2}) ioj => //= j. 
       rewrite [i{2} = _]eq_sym; case (OG.u{2} = i{2}) => //= ?; smt().
     * auto => &1 &2; rewrite !andbA; do ! case => ? oj1 oj2 Hbad 11? logP ? m_i ioj 2? ojN *.
       have ? : oj{1} = oj{2}; 1: by subst; rewrite find_map.
       subst i{2} pk{2} c{2} k{2} oj{2}.
       have Hbad' : forall i j, i \in B.O.mpk{1} => j \in B.O.mpk{1} => 
                                B.O.mpk{1}.[i] = B.O.mpk{1}.[j] => i = j.
         rewrite bad_bad' in Hbad; smt().
       rewrite /= ifF //. split => [//|_]. do ! split => //. 
       - suff pF : forall k, !p B.O.mpk{1} B.O.u{1} B.O.v{1} (pkgen ks{2},pk{1},c{1}) k.
           by subst O2ideal.m{1}; rewrite filter_set pF /= rem_filterE.
         move=> k @/p /=. apply: contra ioj => /> u_m v_m E. 
         split; first by apply Hbad'; smt(mem_map mapE).
         subst oj{1}. by apply uniq_find_some => //= /#. 
       - suff qT : forall k, q B.O.mpk{1} B.O.u{1} B.O.v{1} (pkgen ks{2},pk{1},c{1}) k.
           subst B.O.m{1}; rewrite filter_set qT //=. by subst B.O.mpk{1}; rewrite mapE m_i.
         move => k @/q /=; rewrite -!negb_and. apply: contra ioj => /> u_m v_m E1.
         split; first by apply Hbad'; smt(mem_map mapE).
         subst oj{1}. by apply uniq_find_some => //= /#.
       - move => pki pkj c. case/mem_set => [|/=/>]; 1: exact logP. 
         rewrite !mem_frng /rng; split; [exists i{1}|exists (oget oj{1})]. smt(mapE). 
         by move: ojN; rewrite oj2 => /find_not_none => -[x ks_x [-> />]].
     * by conseq/>.
- move => &2 bk. conseq />. proc.
  conseq (:_ ==> true : 1%r) (:_ ==> _); 1,2: smt(); 2: islossless.
  sp; if; last by auto. 
  seq 1 : #post; [by call pkey_bad'| by conseq />]. 
- move => &1; conseq />; proc; sp.  
  conseq (:_ ==> true : 1%r) (:_ ==> _); 1,2: smt(); 2: islossless.
  sp; if; last by auto. 
  seq 1 : #post; [by call get_bad| by conseq />]. 
- proc; sp; if; 1,3: by auto => /> /#.
  (* (almost) same as encap *)
  seq 1 1 : (#[/2:]pre /\ pki{1} = pkgen ks{2} /\ KS.m.[i]{2} = Some ks{2} 
            \/ bad_k' B.O.mpk{1} /\ bad_k KS.m{2}). 
  + exlim i{2} => i; call (eqv_pki_ks i); auto; smt(). 
  case (bad_k' B.O.mpk{1} /\ bad_k KS.m{2}). 
  + conseq (: bad_k' B.O.mpk{1} /\ bad_k KS.m{2} ==> 
              bad_k' B.O.mpk{1} /\ bad_k KS.m{2}); 1,2: smt().
    conseq />. 
    seq 0 2 : true. 
      by conseq (: true ==> _) _ (: true ==> true : =1%r); islossless. 
    by conseq (: true ==> _) (: true ==> true : =1%r); islossless. 
    conseq (: !bad_k KS.m{2} /\ ={i,pk,c}
      /\ ={u}(B.O,OG) /\ B.O.v{1} - 1 = OG.v{2}
      /\ (B.O.f{1} = fun i => if i = B.O.u then u1 else u2){1}
      /\ B.O.mpk{1} = map (fun _ ks => pkgen ks) RO.m{2}
      /\ (forall i, i <> B.O.u{1} => i <> B.O.v{1} => B.O.msk.[i]{1} = omap skgen RO.m.[i]{2})
      /\ (forall i, !(1 <= i <= n) => RO.m.[i] = None){2}
      /\ (forall i, i = B.O.u{1} \/ i = B.O.v{1} => K2.RO.m.[B.O.f i]{1} = RO.m.[i]{2})
      /\ (O2ideal.m{1} = filter (p B.O.mpk B.O.u B.O.v){1} Oideal.m{2}) 
      /\ ( B.O.m{1} = filter (q B.O.mpk B.O.u B.O.v){1} Oideal.m{2})
      /\ (forall pki pkj c, (pki,pkj,c) \in Oideal.m{2} =>
              pki \in frng B.O.mpk{1} /\ pkj \in frng B.O.mpk{1})
      /\ pki{1} = pkgen ks{2} /\ KS.m.[i]{2} = Some ks{2} ==> _); 1: smt().
  conseq />. (* we no longer sample keys (also not in O2) *)
  sp 0 1; if{1}. 
  + (* log hit in B *) 
    rcondt{2} 1; first by auto => />; smt(mem_filter).
    auto => /> &1 &2 6?. exact mem_filterE. 
  if{1}. 
  + (* receiver (i) is either u or v *)
    inline O2.C.Count(O2ideal(K2.RO)).decap O2ideal(K2.RO).decap.
    (* since pki was obtained, no sampling occurs in O2.decap *)
    inline O2ideal(K2.RO).skey K2.RO.get. rcondf{1} 7. 
      move => &2. auto => &1 /> 3? HK2 3? Hi. 
      have := HK2 i{2} Hi. smt().
    inline O2ideal(K2.RO).pkey K2.RO.get. rcondf{1} 12. 
      move => &2. auto => &1 /> 3? HK2 3? Hi. 
      have := HK2 i{2} Hi. smt(). 
    conseq />. (* really no more key sampling *)
    if{2}. 
    (* log hit (in Oideal) *)
    rcondt{1} 14. 
      move => &2. auto => &1 /> 3? HK2 ? m_i ? Hi *. 
      have /= -> := HK2 _ Hi. smt(mem_filter).
    auto => /> &1 &2 3? HK2 ? m_i ? Hi *. have /= -> := HK2 _ Hi. 
    by rewrite m_i /=; apply mem_filterE; smt(mem_filter).
    (* honest decapsulation *)
    rcondf{1} 14. 
      move => &2. auto => &1 /> 3? HK2 ? m_i ? Hi *. 
      have /= -> := HK2 _ Hi. smt(mem_filter).
    auto => /> &1 &2 3? HK2 ? m_i ? Hi *. have /= -> /# := HK2 _ Hi. 
  (* no log hit in B and no O2 query *)
  rcondf{2} 1.
    (* a log hit in Oideal would require pkey collision *)
    move=> &1. auto => /> &2 /> Hbad 2? HK2 ? m_i X Hi. 
    apply: contra X. rewrite mem_filter /q => /> c_m. 
    apply: contraR Hbad. rewrite !mem_map !negb_or !negbK.
    move => /> /fmapP [ks_u m_u] /fmapP [ks_v m_v]. 
    rewrite oget_map 1:/# m_v /= => coll_ks_v. 
    exists i{1} B.O.v{1}. smt().
  auto => /> &1 &2 ? Hmsk 3? m_i *. by rewrite Hmsk 1,2:/# m_i.
- move => &2 bk. conseq />. proc.
  conseq (:_ ==> true : 1%r) (:_ ==> _); 1,2: smt(); 2: islossless.
  sp; if; last by auto. 
  seq 1 : #post; [by call pkey_bad'| by conseq />]. 
- move => &1; conseq />; proc; sp.  
  conseq (:_ ==> true : 1%r) (:_ ==> _); 1,2: smt(); 2: islossless.
  sp; if; last by auto. 
  seq 1 : #post; [by call get_bad| by conseq />]. 
- proc*. inline OG.pkey. 
  sp. if{2}. 
  + exlim i0{2} => i. wp. call (eqv_pki_ks i). auto. smt(). 
  + inline B(A, O2.C.Count(O2ideal(K2.RO))).O.pkey. sp. 
    rcondf{1} 1; first by auto => /> /#. 
    auto => />. move => &1 &2 2? Hout *. by rewrite mapE Hout.
- move => &2 bk. conseq />. 
  conseq (:_ ==> true : 1%r) (:_ ==> _); 1,2: smt(); 2: islossless.
  by proc*; call pkey_bad'.
- move => &1; conseq />; proc.
  conseq (:_ ==> true : 1%r) (:_ ==> _); 1,2: smt(); 2: islossless.
  sp; if; last by auto. 
  seq 1 : #post; [by call get_bad| by conseq />]. 
(* set up the invariant*)
wp. 
rnd (fun x : int*int => (x.`1,x.`2 - 1))
    (fun x : int*int => (x.`1,x.`2 + 1)). 
auto => &1 &2 [? ?]; split => [/#|_]. 
split => [[u v]|_]; 1: smt(supp_dprod supp_dinter dprod1E dinter1E).
move => [u v] /supp_dprod /= [/supp_dinter ? /supp_dinter ?].
split => [|_]; 1: smt(supp_dprod supp_dinter).
have -> /= : bad_k empty = false by smt(mem_empty).
do ! split; smt(map_empty emptyE filter_empty bad_bad'). 
qed.

(* Claim 5 *)
local lemma G_shift &m u : 1 <= u < n =>
  Pr [G.work(u,n) @ &m : res /\ !bad_k KS.m ] = 
  Pr [G.work(u+1,0) @ &m : res /\ !bad_k KS.m].
proof.
move => I1n. 
byequiv => //; proc; inline*. 
call(: ={RO.m,Oideal.m} 
     /\ (OG.u = u /\ OG.v = n){1} 
     /\ (OG.u = u+1 /\ OG.v = 0){2} 
     /\ (forall i, i \in fdom RO.m{1} => 1 <= i <= n)).
- proc; inline*; sp; if; [smt()| |by auto].
  seq 7 7 : (#[/5:]pre /\ ={c,k,ks}). 
    by auto => />; smt(fdom_set in_fsetU1).
  sp; if; 2,3: (by auto => />); move => /> &2.
  case (findP (fun (_ : int) (ks : keyseed) => pk{2} = pkgen ks) RO.m{2}) => [-> //|]. 
  move => j ks_j -> /= m_j pk_j /(_ j _); smt(mem_fdom).
- proc; inline*; sp; if; [smt()| |by auto].
  seq 5 5 : (#[/3:]pre /\ ={ks,pki}). 
    by auto => />; smt(fdom_set in_fsetU1).
  by if; auto => />.
- proc; inline*; sp; if; [smt()| |by auto].
  by auto => />; smt(fdom_set in_fsetU1).
auto => />; smt(fdom0 in_fset0).
qed.

(* Putting everything together *)
lemma lemma3 &m : 
  `| Pr[ Game(Oreal ,A).main() @ &m : res /\ !bad_k KS.m] - 
     Pr[ Game(Oideal,A).main() @ &m : res /\ !bad_k KS.m] |
=  (n^2)%r * `| Pr[ O2.Game(O2.Oreal ,B(A)).main() @ &m : res /\ !bad_k' B.O.mpk] - 
                Pr[ O2.Game(O2.Oideal,B(A)).main() @ &m : res /\ !bad_k' B.O.mpk]|.
proof.
rewrite Oreal_Gnn Oideal_G10 OrealB_Guv OidealB_Guv1.
have fin_prod : forall a b, is_finite (support ([1..n] `*` [a..b])).
  by move => a b; apply/finite_dprod; apply/finite_dinter.
have -> /= := M1.Mean_uni G &m (fun _ (gG:glob G) b => b /\ !bad_k gG.`4) (1%r/(n^2)%r) _ _.
- case => u v. rewrite supp_dprod => /= -[u1n v1n]. rewrite dprod1E !supp_dinter1E //=.
  by rewrite -fromintM expr2. 
- exact fin_prod.
have -> /= := M0.Mean_uni G &m (fun _ (gG:glob G) b => b /\ !bad_k gG.`4) (1%r/(n^2)%r) _ _.
- case => u v. rewrite supp_dprod => /= -[u1n v1n]. rewrite dprod1E !supp_dinter1E //=.
  by rewrite -fromintM expr2. 
- exact fin_prod.
pose s1 := to_seq _; pose s0 := to_seq _.
have uniq_s1 : uniq s1 by apply/uniq_to_seq/fin_prod.
have uniq_s0 : uniq s0 by apply/uniq_to_seq/fin_prod.
rewrite (big_rem _ _ s1 (n,n)) {1}/predT /=. 
  by rewrite /s1 mem_to_seq ?fin_prod supp_dprod /= supp_dinter; smt(n_gt0).
rewrite (big_rem _ _ s0 (1,0)) {2}/predT /=.
  by rewrite /s0 mem_to_seq ?fin_prod supp_dprod /= !supp_dinter; smt(n_gt0).
rewrite -StdOrder.RealOrder.normrZ; 1: smt(StdOrder.IntOrder.ge0_sqr).
rewrite RField.mulrBr ![(n^2)%r * _]RField.mulrC -!RField.mulrA RField.mulVf /=; 1: smt(n_gt0 expf_eq0).
suff -> : big predT (fun (v : int * int) => Pr[G.work(v) @ &m : res /\ !bad_k RO.m]) (rem (n, n) s1)
        = big predT (fun (v : int * int) => Pr[G.work(v) @ &m : res /\ !bad_k RO.m]) (rem (1, 0) s0).
by have -> : forall (a b c : real), b + a - (c + a) = b - c by smt().
pose f (v : int * int) := if v.`2 = n then (v.`1+1,0) else v.
pose g (v : int * int) := if v.`2 = 0 then (v.`1-1,n) else v.
have can_f : forall x, x \in rem (1,0) s0 => f (g x) = x. 
  case => u v. rewrite uniq_mem_rem // /s1 mem_to_seq ?fin_prod /=.
  by rewrite supp_dprod /= !supp_dinter /f /g /= /#.
rewrite (LibExt.big_reindex _ _ _ _ _ can_f) /(\o).
rewrite [big _ _ (List.map _ _)](eq_big_perm _ _ _ (rem (n, n) s1)).
- (* TODO: clean this up *)
  apply uniq_perm_eq; 2: by rewrite rem_uniq uniq_to_seq fin_prod.
  + rewrite map_inj_in_uniq 1:/# rem_uniq uniq_to_seq fin_prod.
  + case => u v. rewrite uniq_mem_rem // mem_to_seq ?fin_prod supp_dprod !supp_dinter /=.
    split => [/mapP [[u' v']]|]. 
    * rewrite uniq_mem_rem // mem_to_seq ?fin_prod supp_dprod !supp_dinter /=. smt().
    * move => ?. apply/mapP; exists (f (u,v)). 
      rewrite uniq_mem_rem // mem_to_seq ?fin_prod supp_dprod !supp_dinter /=. smt().
apply eq_big_seq => // -[u v]. 
rewrite uniq_mem_rem // mem_to_seq ?fin_prod supp_dprod !supp_dinter /=.
rewrite /f /=. case (v = n) => // -> {v} ?. apply: G_shift. smt().
qed.

local lemma B_Bbad_real &m : 
  Pr[ O2.Game(O2.Oreal ,B(A)).main() @ &m : res /\ !bad_k' B.O.mpk] = 
  Pr[ O2.Game(O2.Oreal ,Bbad(A)).main() @ &m : res].
proof. by byequiv => //; proc; inline*; wp; sim. qed.

local lemma B_Bbad_ideal &m : 
  Pr[ O2.Game(O2.Oideal ,B(A)).main() @ &m : res /\ !bad_k' B.O.mpk] = 
  Pr[ O2.Game(O2.Oideal ,Bbad(A)).main() @ &m : res].
proof. by byequiv => //; proc; inline*; wp; sim. qed.

(* Variant of Bbad that counts calls to the oracle it provices to A *)
local module Bc (O : O2.Oracle) = { 
  proc guess() = { 
    var r:bool <- witness;
    (B.O.u,B.O.v) <$ [1..n] `*` [1..n];
    B.O.m <- empty;
    B.O.mpk <- empty;
    B.O.msk <- empty;
    B.O.f <- fun x => if x = B.O.u then u1 else u2;
    Count(B(A,O).O).init();
    r <@ A(Count(B(A,O).O)).guess();
    return r;
  }
}.

local equiv B_Bc (O<: O2.Oracle{A,B,Count}) : 
    Bbad(A,O).guess ~ Bc(O).guess : 
    ={glob A, glob B, glob O} ==> ={glob A, glob B, glob O}.
proof. 
proc; inline B(A,O).guess ; wp. call(: ={glob B, glob O}). 
- proc; inline*; wp. 
  by sim / true : (={c,k,glob B,glob O}); auto => />. 
- proc; inline*; sim; auto.
- by sim.
by inline*; auto.
qed.

local lemma Bbad_bound (O <: O2.Oracle{Count,O2.C.Count,A,B}) :
  hoare[ Bbad(A, O2.C.Count(O)).guess :
          (O2.counts0 O2.C.Count.ce O2.C.Count.cd O2.C.Count.cc) ==>
          (O2.counts qe qd qe O2.C.Count.ce O2.C.Count.cd O2.C.Count.cc)].
proof.
(* Insert counting of calls to Bbad *)
conseq (B_Bc(O2.C.Count(O))) 
 (: O2.counts0 O2.C.Count.ce O2.C.Count.cd O2.C.Count.cc ==>
    O2.counts qe qd qe O2.C.Count.ce O2.C.Count.cd O2.C.Count.cc); 1,2: smt(). 
(* Obtain the call bounds for A *)
conseq (: true ==> O2.counts qe qd 0 Count.ce Count.cd 0)  
       (: O2.counts0 O2.C.Count.ce O2.C.Count.cd O2.C.Count.cc ==>
          O2.counts qe qd 0 Count.ce Count.cd 0 => 
          O2.counts qe qd qe O2.C.Count.ce O2.C.Count.cd O2.C.Count.cc); 1: smt(); 
  last by proc; call (A_bound (<: B(A, O2.C.Count(O)).O)); inline*; auto.
proc. 
call (: O2.C.Count.ce <= Count.ce /\ O2.C.Count.cd <= Count.cd /\ O2.C.Count.cc <= Count.ce).
- proc; swap 1 1; wp. inline*; sp. 
  if; last by auto => /> /#. 
  seq 4 : #pre; 1: by conseq />.
  seq 1 : #post; 2: by conseq />. 
  do 2! (if; 1: by wp; call(:true); auto => /> /#).
  by auto => /> /#. 
- proc; swap 1 1; wp. inline*; sp. 
  if; last by auto => /> /#. 
  seq 3 : #pre; 1: by conseq />.
  wp. if; 1: by auto => /> /#. 
  if; 2: by auto => /> /#. 
  wp; call(:true); auto => /> /#. 
- by conseq />.
by inline*; auto => /> /#. 
qed.

local lemma Bbad_ll (O <: O2.Oracle{Bbad(A)}) : 
  islossless O.pkey =>
  islossless O.encap => islossless O.decap => islossless O.chall => islossless Bbad(A, O).guess.
proof.
move => *. 
islossless; first by apply (A_ll (<: B(A,O).O)); islossless. 
smt(weight_dprod weight_dinter n_gt0).
qed.

(* combining everything to get the theorem for Outsider-CCA *)
module B11 (A : Adversary) : O2.Adversary = O2.B(Bbad(A)).

(* The advantage of A is [n^2 * qc] times the advantage of B11 ...  *)
lemma theorem11 &m : 
  `| Pr[ Game(Oreal ,A).main() @ &m : res /\ !bad_k KS.m] - 
     Pr[ Game(Oideal,A).main() @ &m : res /\ !bad_k KS.m] | 
= (n^2 * qe)%r * `| Pr[ O2.Game(O2.Oreal ,B11(A)).main() @ &m : res] - 
                    Pr[ O2.Game(O2.Oideal,B11(A)).main() @ &m : res]|.
proof. 
have l2 := O2.lemma2 (Bbad(A)) Bbad_ll Bbad_bound &m.
by rewrite lemma3 B_Bbad_real B_Bbad_ideal l2 /#.
qed.

(* ... and B11 makes at most 2*qe queries to encap, at most qd queries
to decap, and at most one challenge querey. *)
lemma B11_bound : 
  forall (O <: O2.Oracle{A,O2.CB.Count,O2.C.Count,Count,O2.B(Bbad(A)).OB}),
    hoare[ B11(A,O2.CB.Count(O)).guess :
            O2.counts0 O2.CB.Count.ce O2.CB.Count.cd O2.CB.Count.cc ==>
            O2.counts (2*qe) qd 1 O2.CB.Count.ce O2.CB.Count.cd O2.CB.Count.cc].
proof.
by move => O; conseq (O2.B_bound (Bbad(A)) Bbad_ll Bbad_bound O) => /#.
qed.

end section PROOF.  

end OutsiderCCA.
