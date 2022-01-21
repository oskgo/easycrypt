require import AllCore List Distr DBool DInterval.
require (*--*) Oracle_PKE.

import Distr.MRat.

(* This file provides games for the Real/Ideal variant of
IND-CCA2. The Real game provides the adversary with access to an
encryption oracle, in the Ideal game the encryption oracle always
encrypts the same (fixed) message. 

Unlike Oracle_PKE, we do not work with an abstract [Scheme]
module. Instead, we require distributions [dkeyseed, dencseed] and
operators that allow implementing a [Scheme] module *) 

(* FIXME: We use an inner theory to avoid the name-clash with the Real theory. *)
theory CCA.

type pkey, skey, plaintext, ciphertext, encseed, keyseed.

op dkeyseed : { keyseed distr | is_uniform dkeyseed } as dkeyseed_d.
op dencseed : { encseed distr | is_uniform dencseed } as dencseed_d.

op Ndec : int.
op Nenc : { int | 0 < Nenc } as Nenc_gt0.

op enc : plaintext * pkey * encseed -> ciphertext.
op dec : ciphertext * skey -> plaintext option.
op pkgen : keyseed -> pkey.
op skgen : keyseed -> skey.
op m0 : plaintext.

axiom encK (k : keyseed) (m : plaintext) (e : encseed) :
  dec (enc(m, pkgen k, e), skgen k) = Some m.

clone import Oracle_PKE as PKE with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext
  proof*.

clone import IND_CCA2 as C with
  op Ndec <- Ndec,
  op Nenc <- Nenc,
  axiom Nenc_gt0 <- Nenc_gt0
  proof*.

module type Oracle = {
  proc pk () : pkey
  proc enc (_ : plaintext) : ciphertext
  proc dec (_ : ciphertext)  : plaintext option
}.

module type Oracle_i = {
  include Oracle
  proc init() : unit
}.

(* "Real" oracle, enc encrypts the given message *)
module Real : Oracle = {
  var pk : pkey
  var sk : skey

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
  }

  proc pk () = {
    return pk;
  }

  proc enc (m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc(m, pk, e);
    return c;
  }
  proc dec (c : ciphertext) : plaintext option = {
    var m;

    m <- dec(c, sk);
    return m;
  }
}.

(* Ideal orcale, discards m and always encrypts m0 

In the case of a ciphertext collision (e.g. a collision in dencseed),
the last given message is returned *)

module Ideal : Oracle = {
  import var Real
  var cs : (ciphertext * plaintext) list

  proc init() : unit = {
    var ks;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
    cs <- [];
  }

  proc pk () = {
    return pk;
  }

  proc enc (m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc(m0, pk, e);
    cs <- (c, m) :: cs;
    return c;
  }

  proc dec (c : ciphertext) : plaintext option = {
    var m;

    m <- assoc cs c;
    if (m = None) {
      m <- dec(c, sk);
    }
    return m;
  }
}.

(* Same as above, but in the case of a ciphertext collision, the
message returned by decryption is chosen randomly. *) 

module IdealS : Oracle = {
  import var Real
  include var Ideal [-dec]

  proc dec (c : ciphertext) : plaintext option = {
    var fcs, m, p;

    fcs <- List.filter (fun p => fst p = c) cs;
    if (fcs <> []) {
      p <$ drat fcs;
      m <- Some (snd p);
    } else {
      m <- dec(c, sk);
    }
    return m;
  }
}.

module type Adversary (G : Oracle) = {
  proc main () : bool
}.

module Game (O : Oracle_i, A : Adversary) = {

  proc main() = {
    var r;

    O.init();
    r <@ A(O).main();
    return r;
  }
}.

(*-------------------------------*)

module CountICCA (O : Oracle) = {
  var ndec, nenc : int

  proc init () : unit = {
    ndec <- 0;
    nenc <- 0;
  }

  proc pk = O.pk

  proc enc (m : plaintext) : ciphertext = {
    var c;

    c <@ O.enc(m);
    nenc <- nenc + 1;
    return c;
  }

  proc dec (c : ciphertext) : plaintext option = {
    var m;

    m <@ O.dec(c);
    ndec <- ndec + 1;
    return m;
  }
}.

module CountAdv (A : Adversary) (O : Oracle) = {
  proc main() = {
    var b;

    CountICCA(O).init();
    b <@ A(CountICCA(O)).main();
    return b;
  }
}.

(* Adversary for the bound |Real - Ideal| < |CCA_L - CCA_R| *)
module B (A : Adversary) (O : CCA_Oracle) = {
  var cs : (ciphertext * plaintext) list
  var pk : pkey

  module O' : Oracle = {

    proc init (p : pkey) = { pk <- p; }

    proc pk () = { return pk; }

    proc enc (m : plaintext) = {
      var c;

      c <- O.l_or_r(m, m0);
      cs <- (c, m) :: cs;
      return c;
    }

    proc dec (c : ciphertext) = {
      var m;

      m <- assoc cs c;
      if (m = None) {
        m <- O.dec(c);
      }
      return m;
    }
  }

  proc main (pk : pkey) : bool = {
    var r;

    cs <- [];
    O'.init(pk);
    r <@ A(O').main();
    return r;
  }
}.

(* Adversary for the bound |Real - IdealS| < |CCA_L - CCA_R| *)
module BS (A : Adversary) (O : CCA_Oracle) = {
  var cs : (ciphertext * plaintext) list
  var pk : pkey

  module O' : Oracle = {

    proc init (p : pkey) = { pk <- p; }

    proc pk () = { return pk; }

    proc enc (m : plaintext) = {
      var c;

      c <- O.l_or_r(m, m0);
      cs <- (c, m) :: cs;
      return c;
    }

    proc dec (c : ciphertext) : plaintext option = {
      var fcs, m, p;

      fcs <- List.filter (fun p => fst p = c) cs;
      if (fcs <> []) {
        p <$ drat fcs;
        m <- Some (snd p);
      } else {
        m <- O.dec(c);
      }
      return m;
    }
  }

  proc main (pk : pkey) : bool = {
    var r;

    cs <- [];
    O'.init(pk);
    r <@ A(O').main();
    return r;
  }
}.

section.

declare module A <: Adversary {Real, Ideal, IdealS,
                              C.CCA_Oracle, B, BS, CountCCA, CountICCA}.

module S : Scheme = {
  proc kg () : pkey * skey = {
    var ks, pk, sk;

    ks <$ dkeyseed;
    pk <- pkgen ks;
    sk <- skgen ks;
    return (pk, sk);
  }

  proc enc (pk : pkey, m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc (m, pk, e);
    return c;
  }

  proc dec(sk : skey, c : ciphertext) : plaintext option = {
    var m;

    m <- dec (c, sk);
    return m;
  }
}.

declare axiom A_bound (O <: Oracle {A, CountICCA}) : hoare [CountAdv(A, O).main :
               true ==> CountICCA.ndec <= Ndec /\ CountICCA.nenc <= Nenc].

equiv AB_bound (O <: CCA_Oracle{CountICCA, CountCCA, A, B}) :
  C.CountAdv(B(A), O).main ~ CountAdv(A, B(A, O).O').main :
  ={glob A, glob O} /\ B.cs{2} = [] /\ arg{1} = B.pk{2} ==>
  CountCCA.ndec{1} <= CountICCA.ndec{2} /\ CountCCA.nenc{1} = CountICCA.nenc{2}.
proof.
proc. inline*; sp; auto.
call (: ={glob O, glob B} /\ CountCCA.ndec{1} <= CountICCA.ndec{2} /\
        CountCCA.nenc{1} = CountICCA.nenc{2}) => //.
- by proc; auto.
- by proc; inline *; sp; auto; call (: true); auto => /> /#.
- proc; inline *; sp; auto.
  if; auto => />; 2: by smt().
  by sp; call (: true); auto => /> /#.
qed.

lemma B_bound (O <: CCA_Oracle{CountCCA, CountICCA, A, B}) :
  hoare [C.CountAdv(B(A), O).main :
    true ==> CountCCA.ndec <= Ndec /\ CountCCA.nenc <= Nenc].
proof.
by conseq (AB_bound (<: O)) (A_bound (<: B(A, O).O')) => // /#.
qed.

local module Real' : Oracle = {
  import var Real
  include var Ideal [-enc]

  proc enc (m : plaintext) : ciphertext = {
    var e, c;

    e <$ dencseed;
    c <- enc(m, pk, e);
    cs <- (c, m) :: cs;
    return c;
  }
}.

local module RealS' : Oracle = {
  import var Real
  import var Ideal
  include Real' [-dec]

  proc dec (c : ciphertext) : plaintext option = {
    var fcs, m, p;

    fcs <- List.filter (fun p => fst p = c) cs;
    if (fcs <> []) {
      p <$ drat fcs;
      m <- Some (snd p);
    } else {
      m <- dec(c, sk);
    }
    return m;
  }
}.

local equiv Real_Real' :
  Game(Real, A).main ~ Game(Real', A).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
call (: ={glob Real} /\
        (exists ks, (Real.pk, Real.sk){2} = (pkgen ks, skgen ks)) /\
        (forall c m, assoc Ideal.cs c = Some m => dec(c, Real.sk) = Some m){2}).
- by proc; auto.
- proc; wp; rnd; auto=> /> &m2 ks Hcs e _ c m'.
  rewrite assoc_cons.
  case: (c = enc (m{m2}, pkgen ks, e)) => />; 1: by rewrite encK.
  by move => _; apply: Hcs.
- by proc; wp; skip => /> &m2 ks Hcs /#.
- by wp; rnd; skip => /> /#.
qed.

local equiv Real'_CCA_L :
  Game(Real', A).main ~ CCA_L(S, B(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={pk, sk}(Real, CCA_Oracle) /\ unzip1 Ideal.cs{1} = CCA_Oracle.cs{2} /\
        (forall c m,assoc Ideal.cs c = Some m => dec(c, Real.sk) = Some m){1} /\
        (exists ks, (CCA_Oracle.pk, CCA_Oracle.sk){2} = (pkgen ks, skgen ks)) /\
        Ideal.cs{1} = B.cs{2} /\ B.pk{2} = CCA_Oracle.pk{2}).
- by proc; inline *; auto => />.
- proc; inline *; auto => /> &m1 &m2 Hcs ks ? ? e _ c m'.
  by rewrite assoc_cons; case : (c = enc (m{m2}, pkgen ks, e)) => />; smt(encK).
- proc; inline *; auto => /> &m1 &m2 Hcs ks ? ?.
  by rewrite -assocTP.
- by wp; rnd; skip => /> /#.
qed.

equiv Ideal_CCA_R :
  Game(Ideal, A).main ~ CCA_R(S, B(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={pk, sk}(Real, CCA_Oracle) /\ unzip1 Ideal.cs{1} = CCA_Oracle.cs{2} /\
        (forall c m,
           assoc Ideal.cs c = Some m => dec(c, Real.sk) = Some m0){1} /\
        (exists ks, (CCA_Oracle.pk, CCA_Oracle.sk){2} = (pkgen ks, skgen ks)) /\
        Ideal.cs{1} = B.cs{2} /\ B.pk{2} = CCA_Oracle.pk{2}).
- by proc; inline *; auto => />.
- proc; inline *; auto => /> &m1 &m2 Hcs ks ? ? e _ c m'.
  by rewrite assoc_cons; case : (c = enc (m0, pkgen ks, e)) => />; smt(encK).
- proc; inline *; auto => /> &m1 &m2 Hcs ks ? ?.
  by rewrite -assocTP.
- by wp; rnd; skip => /> /#.
qed.

lemma ICCA_CCALR &m :
  Pr[Game(Real, A).main() @ &m : res] - Pr[Game(Ideal, A).main() @ &m : res] =
  Pr[CCA_L(S, B(A)).main() @ &m : res] - Pr[CCA_R(S, B(A)).main() @ &m : res].
proof.
have -> : Pr[Game(Real, A).main() @ &m : res] = Pr[Game(Real', A).main() @ &m : res].
  by byequiv => //; conseq Real_Real'.
have -> : Pr[Game(Real', A).main() @ &m : res] = Pr[CCA_L(S, B(A)).main() @ &m : res].
  by byequiv => //; conseq  Real'_CCA_L.
have -> : Pr[Game(Ideal, A).main() @ &m : res] = Pr[CCA_R(S, B(A)).main() @ &m : res]. 
  by byequiv => //; conseq Ideal_CCA_R.
smt().
qed.

local equiv Real_RealS' :
  Game(Real, A).main ~ Game(RealS', A).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
call (: ={glob Real} /\
        (exists ks, (Real.pk, Real.sk){2} = (pkgen ks, skgen ks)) /\
        (forall c p,
           p \in drat (List.filter (fun p => fst p = c) Ideal.cs) =>
           dec(c, Real.sk) = Some (snd p)){2}).
- by proc; auto.
- proc; wp; rnd; auto => /> &m2 ks csP e ? c ?.
  case: (enc (m{m2}, pkgen ks, e) = c); 2: by move => _; apply csP.
  rewrite supp_drat in_cons.
  move => ? [|]; 1: smt(encK).
  by rewrite -supp_drat; apply csP.
- proc; sp; if{2}; 2: by auto => />.
  auto => /> &m2 ? Hcs ?; split; 1: smt(drat_ll).
  by move => _; apply Hcs.
- by wp; rnd; skip => />; smt(supp_drat).
qed.

local equiv RealS'_CCA_L :
  Game(RealS', A).main ~ CCA_L(S, BS(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={pk, sk}(Real, CCA_Oracle) /\ unzip1 Ideal.cs{1} = CCA_Oracle.cs{2} /\
        (forall c m, (c, m) \in List.filter (fun p => fst p = c) Ideal.cs =>
                       dec(c, Real.sk) = Some m){1} /\
        (exists ks, (CCA_Oracle.pk, CCA_Oracle.sk){2} = (pkgen ks, skgen ks)) /\
        Ideal.cs{1} = BS.cs{2} /\ BS.pk{2} = CCA_Oracle.pk{2}).
- by proc; inline *; auto => />.
- proc; inline *; auto => /> &m1 &m2 Hcs ks skP ? e _ c ?.
  case: (enc (m{m2}, pkgen ks, e) = c).
  + move => ? [|?]; 1: smt(encK).
    by rewrite -skP; apply (Hcs c); smt().
  + by move => _ ?; rewrite -skP; apply (Hcs c); smt().
- proc; inline *; sp; auto; if; auto => /> &m1 &m2 5?.
  rewrite mem_map_fst; smt(mem_filter).
- by wp; rnd; skip => /> /#.
qed.

equiv IdealS_CCA_R :
  Game(IdealS, A).main ~ CCA_R(S, BS(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={pk, sk}(Real, CCA_Oracle) /\ unzip1 Ideal.cs{1} = CCA_Oracle.cs{2} /\
        (forall c m, (c, m) \in List.filter (fun p => fst p = c)
                                                   Ideal.cs =>
                       dec(c, Real.sk) = Some m0){1} /\
        (exists ks, (CCA_Oracle.pk, CCA_Oracle.sk){2} = (pkgen ks, skgen ks)) /\
        Ideal.cs{1} = BS.cs{2} /\ BS.pk{2} = CCA_Oracle.pk{2}).
- by proc; inline *; auto => />.
- proc; inline *; auto => /> &m1 &m2 Hcs ks skP ? e _ c m'.
  case: (enc (m0, pkgen ks, e) = c); 1: smt(encK).
  by move => _ ?; rewrite -skP; apply (Hcs c m'); smt().
- proc; inline *; sp; auto; if; auto => /> &m1 &m2 5?.
  rewrite mem_map_fst; smt(mem_filter).
- by wp; rnd; skip => /> /#.
qed.

lemma ICCA_CCALR' &m :
  Pr[Game(Real, A).main() @ &m : res] - Pr[Game(IdealS, A).main() @ &m : res] =
  Pr[CCA_L(S, BS(A)).main() @ &m : res] - Pr[CCA_R(S, BS(A)).main() @ &m : res].
proof.
have -> : Pr[Game(Real, A).main() @ &m : res] =
          Pr[Game(RealS', A).main() @ &m : res].
- byequiv => //; conseq (: ={glob A} ==> ={res}) => //; exact Real_RealS'.
have -> : Pr[Game(RealS', A).main() @ &m : res] =
          Pr[CCA_L(S, BS(A)).main() @ &m : res].
- byequiv => //; conseq (: ={glob A} ==> ={res}) => //; exact RealS'_CCA_L.
have -> : Pr[Game(IdealS, A).main() @ &m : res] =
          Pr[CCA_R(S, BS(A)).main() @ &m : res]; 2: by smt().
byequiv => //; conseq (: ={glob A} ==> ={res}) => //; exact IdealS_CCA_R.
qed.

end section.

end CCA.
