require import AllCore List Finite Distr DBool DInterval DList LorR FSet SmtMap.

(* * Preliminaries *)

(* Logic.ec *)

type ('a, 'b) sum = [Left of 'a | Right of 'b].

op is_left ['a 'b] (s : ('a,'b) sum) =
  with s = Left _ => true
  with s = Right _ => false.

op left ['a 'b] (s : ('a,'b) sum) =
  with s = Left x => x
  with s = Right _ => witness.

op right ['a 'b] (s : ('a,'b) sum) =
  with s = Right x => x
  with s = Left _ => witness.

lemma ifT (b : bool) (e1 e2 : 'a) : b => (if b then e1 else e2) = e1. 
proof. smt(). qed.

lemma ifF (b : bool) (e1 e2 : 'a) : !b => (if b then e1 else e2) = e2. 
proof. smt(). qed.

lemma omap_some (ox : 'a option) (y : 'b) (f : 'a -> 'b) : 
  omap f ox = Some y => exists x, ox = Some x /\ f x = y. 
proof. by case: ox => /#. qed.

(* List.ec *)

lemma subseq_map (s1 s2 : 'a list) (f : 'a -> 'b) : 
  subseq s1 s2 => subseq (map f s1) (map f s2).
proof. 
elim: s2 s1 => [|y s2 IHs2] [|x s1] //= /IHs2. 
smt(subseq_refl subseq_cons subseq_trans).
qed.

lemma subseq_uniq (s1 s2 : 'a list) : 
  subseq s1 s2 => uniq s2 => uniq s1.
proof. 
elim: s2 s1 => [|y s2 IHs2] [|x s1] //=; smt(subseq_mem). 
qed.

lemma subseq_map_uniq (s1 s2 : 'a list) (f : 'a -> 'b) : 
  subseq s1 s2 => uniq (map f s2) => uniq (map f s1).
proof. by move/(subseq_map _ _ f); apply: subseq_uniq. qed.

lemma uniq_mem_rem (y x : 'a) (s : 'a list) : 
  uniq s => y \in rem x s <=> y \in s /\ y <> x.
proof. by elim: s => //= /#. qed.

(* FSet.ec *)

lemma fcard_oflist (s : 'a list) : card (oflist s) <= size s.
proof. by rewrite /card -(perm_eq_size _ _ (oflistK s)) size_undup. qed.

lemma uniq_card_oflist (s : 'a list) : uniq s => card (oflist s) = size s.
proof. by rewrite /card => /oflist_uniq/perm_eq_size => <-. qed.

lemma card_iota (n : int) : 0 <= n => card (oflist (iota_ 1 n)) = n.
proof. by move=> n_ge0; rewrite uniq_card_oflist ?iota_uniq size_iota /#. qed.


op rangeset (m n : int) = oflist (range m n).

lemma card_rangeset m n : card (rangeset m n) = max 0 (n - m).
proof. by rewrite uniq_card_oflist ?range_uniq size_range. qed.

lemma mem_rangeset m n i : i \in rangeset m n <=> m <= i && i < n.
proof. by rewrite mem_oflist mem_range. qed.

(* Distr.ec *)
lemma finite_dprod (d1 d2 : 'a distr) : 
  is_finite (support d1) => is_finite (support d2) => 
  is_finite (support (d1 `*` d2)).
proof.
move=> fin_d1 fin_d2; rewrite dprod_dlet finite_dlet // => x x_d1.
by apply finite_dlet => // y y_d2; apply finite_dunit.
qed.

import MRat.
lemma perm_eq_drat ['a] (s1 s2 : 'a list) : 
  perm_eq s1 s2 => drat s1 = drat s2.
proof. by move => P; apply/eq_dratP/perm_eq_ratl. qed.

(* DInterval.ec *)
lemma finite_dinter (a b : int) : is_finite (support [a..b]).
proof.
rewrite is_finiteE; exists (range a (b+1)).
by rewrite range_uniq /= => x; rewrite mem_range supp_dinter /#.
qed.

lemma supp_dinter1E (x : int) (a b : int) :
  x \in [a..b] => mu1 [a..b] x = 1%r / (b - a + 1)%r.
proof. by rewrite supp_dinter dinter1E => ->. qed.

lemma perm_eq_dinter (a b : int) : 
  perm_eq (to_seq (support [a..b])) (range a (b+1)).
proof. 
apply: uniq_perm_eq; first exact/uniq_to_seq/finite_dinter.
+ exact: range_uniq.
by move=> x; rewrite mem_to_seq ?finite_dinter // supp_dinter mem_range /#.
qed.

lemma perm_eq_dinter_pred (a b : int) : 
  perm_eq (to_seq (support [a..b-1])) (range a b).
proof. by have /# := perm_eq_dinter a (b-1). qed.  

(* SmtMap.ec *)
lemma find_map (m : ('a, 'b) fmap) (f : 'a -> 'b -> 'c) P : 
  find P (map f m) = find (fun x y => P x (f x y)) m.
proof.
rewrite !findE fdom_map; congr; apply find_eq_in => x /=.
by rewrite -memE fdomP /= mapE; case(m.[x]).
qed.

lemma find_not_none (P : 'a -> 'b -> bool) (m : ('a,'b) fmap) : 
  find P m <> None => exists x y, find P m = Some x /\ m.[x] = Some y /\ P x y.
proof. by case: (findP P m) => // x y ? ? ? _; exists x y. qed.

lemma oget_map (m : ('a,'b) fmap) (f : 'a -> 'b -> 'c) i :
  i \in m => oget (map f m).[i] = f i (oget m.[i]).
proof. by rewrite mapE fmapP => -[y ->]. qed.

lemma rem_filterE (m : ('a,'b) fmap) x (p : 'a -> 'b -> bool) :
  (forall y, !p x y) => rem (filter p m) x = filter p m.
proof.
move => Hpx; apply/fmap_eqP => z; rewrite remE. 
by case(z = x) => // ->; rewrite filterE /#. 
qed.

lemma eq_in_filter ['a 'b] (p1 p2 : 'a -> 'b -> bool) (m : ('a,'b) fmap) :
  (forall (x : 'a) y , m.[x] = Some y => p1 x y <=> p2 x y) => filter p1 m = filter p2 m.
proof. 
move=> eq_p; apply/fmap_eqP => x; rewrite !filterE /#.
qed.

lemma find_none (p : 'a -> 'b -> bool) (m : ('a,'b) fmap): 
  (forall x, x \in m => !p x (oget m.[x])) => find p m = None.
proof. by move=> np; apply contraT => /find_not_none /#. qed.

lemma nosmt uniq_find_some z (P : 'a -> 'b -> bool) (m : ('a, 'b) fmap) :
  (forall (x : 'a) (y : 'b), m.[x] = Some y => P x y => x = z) =>
  z \in m => P z (oget m.[z]) => find P m = Some z.
proof.
move => uniq_m z_m p_z; case (findP P m) => [/#|x y fmx mx p_xy]. 
by have <- := find_some_unique _ _ _ _ uniq_m fmx.
qed.

lemma nosmt uniq_find_set (p : 'a -> 'b -> bool) (m : ('a,'b) fmap) x y : 
  (forall x1 x2, x1 \in m => x2 \in m => 
    p x1 (oget m.[x1]) => p x2 (oget m.[x2]) => x1 = x2) =>
  x \notin m => !p x y => find p m.[x <- y] = find p m.
proof.
move=> x_m uniq_m p_xy. case (findP p m) => [-> npm|a b E m_a p_ab]. 
- apply find_none; smt(mem_set get_setE).
rewrite E. apply uniq_find_some; smt(mem_set get_setE). 
qed.

lemma mem_filter (m : ('a,'b) fmap) (p : 'a -> 'b -> bool) x : 
   x \in filter p m <=> x \in m /\ p x (oget m.[x]).
proof. smt(filterE). qed.

lemma mem_filterE (m : ('a,'b) fmap) (p : 'a -> 'b -> bool) x : 
  x \in filter p m => (filter p m).[x] = m.[x].
proof. smt(filterE). qed.

lemma filter_empty (p:'a -> 'b -> bool) : filter p empty = empty.
proof. by apply/fmap_eqP => x; rewrite filterE emptyE. qed.


(* f-collisions (i.e. collisions under some function f) *)
op fcoll (f : 'b -> 'c) (m : ('a,'b) fmap)  =
  exists i j, i \in m /\ j \in m /\ i <> j /\ 
              f (oget m.[i]) = f (oget m.[j]).

lemma fcollPn (f : 'b -> 'c) (m : ('a,'b) fmap) : 
    !fcoll f m <=> 
    forall i j, i \in m => j \in m => i <> j => f (oget m.[i]) <> f (oget m.[j]).
proof. smt(). qed.

require StdBigop.
import StdBigop.Bigreal.BRA.

(* shadows more restrictive big_reindex from theories *)
lemma nosmt big_reindex ['a 'b]
  (P : 'a -> bool) (F : 'a -> real) (f : 'b -> 'a) (f' : 'a -> 'b) (s : 'a list) :
  (forall x, x \in s => f (f' x) = x) => big P F s = big (P \o f) (F \o f) (map f' s).
proof. 
by move => /eq_in_map id_ff'; rewrite -big_map -map_comp id_ff' id_map.
qed.

(* end preliminaries *)
