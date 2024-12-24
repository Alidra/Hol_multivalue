Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_ADD2_term_abbrevs.
Require Import ADD_AC_spec.
Require Import LE_EXISTS_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem101180 (m : nat) : term0 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem101181 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem101182 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem101181 m) (@lem101180 m)). Qed.
Lemma lem101183 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem101182 m n). Qed.
Lemma lem101184 (n : nat) (m : nat) : (term2 m n) = ((Peano.le m n) = (term3 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem101191 (n : nat) (m : nat) : (Peano.le m n) = (term3 n m).
Proof. exact (EQ_MP (@lem101184 n m) (@lem101183 m n)). Qed.
Lemma lem101192 (p : nat) (m : nat) : (Peano.le m p) = (term3 p m).
Proof. exact (@lem101191 p m). Qed.
Lemma lem101199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem101200 (p : nat) (m : nat) : (term4 m p) = (term5 p m).
Proof. exact (MK_COMB (@lem101199) (@lem101192 p m)). Qed.
Lemma lem101202 (n : nat) (m : nat) : (Peano.le m n) = (term3 n m).
Proof. exact (EQ_MP (@lem101184 n m) (@lem101183 m n)). Qed.
Lemma lem101203 (q : nat) (n : nat) : (Peano.le n q) = (term3 q n).
Proof. exact (@lem101202 q n). Qed.
Lemma lem101210 (p : nat) (m : nat) (q : nat) (n : nat) : (term6 m p n q) = (term7 p m q n).
Proof. exact (MK_COMB (@lem101200 p m) (@lem101203 q n)). Qed.
Lemma lem101213 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem101214 (p : nat) (m : nat) (q : nat) (n : nat) : (term8 m p n q) = (term9 p m q n).
Proof. exact (MK_COMB (@lem101213) (@lem101210 p m q n)). Qed.
Lemma lem101216 (n : nat) (m : nat) : (Peano.le m n) = (term3 n m).
Proof. exact (EQ_MP (@lem101184 n m) (@lem101183 m n)). Qed.
Lemma lem101217 (p : nat) (q : nat) (m : nat) (n : nat) : (term10 m n p q) = (term11 p q m n).
Proof. exact (@lem101216 (Nat.add p q) (Nat.add m n)). Qed.
Lemma lem101224 (p : nat) (q : nat) (m : nat) (n : nat) : (term12 m n p q) = (term13 p q m n).
Proof. exact (MK_COMB (@lem101214 p m q n) (@lem101217 p q m n)). Qed.
Lemma lem101227 (m : nat) (n : nat) (p : nat) (q : nat) : (term13 p q m n) = (term12 m n p q).
Proof. exact (SYM (@lem101224 p q m n)). Qed.
Lemma lem101228 (p : nat) (m : nat) (q : nat) (n : nat) (h1 : term7 p m q n) : term7 p m q n.
Proof. exact (h1). Qed.
Lemma lem101229 (q : nat) (n : nat) (h1 : term3 q n) : term3 q n.
Proof. exact (h1). Qed.
Lemma lem101231 (p : nat) (m : nat) (h1 : term3 p m) : term3 p m.
Proof. exact (h1). Qed.
Lemma lem101233 (n : nat) (m : nat) (p : nat) : term14 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem101243 (p : nat) (m : nat) (a : nat) (h1 : p = (Nat.add m a)) : p = (Nat.add m a).
Proof. exact (h1). Qed.
Lemma lem101245 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem101246 (a : nat) (m : nat) : (Nat.add m a) = (Nat.add a m).
Proof. exact (@lem101245 a m). Qed.
Lemma lem101250 (p : nat) (m : nat) (a : nat) (h1 : p = (Nat.add m a)) : p = (Nat.add a m).
Proof. exact (TRANS (@lem101243 p m a h1) (@lem101246 a m)). Qed.
Lemma lem101251 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem101252 (p : nat) (m : nat) (a : nat) (h1 : p = (Nat.add m a)) : (Nat.add p) = (term15 a m).
Proof. exact (MK_COMB (@lem101251) (@lem101250 p m a h1)). Qed.
Lemma lem101254 (q : nat) (n : nat) (b : nat) (h1 : q = (Nat.add n b)) : q = (Nat.add n b).
Proof. exact (h1). Qed.
Lemma lem101256 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem101257 (b : nat) (n : nat) : (Nat.add n b) = (Nat.add b n).
Proof. exact (@lem101256 b n). Qed.
Lemma lem101261 (q : nat) (n : nat) (b : nat) (h1 : q = (Nat.add n b)) : q = (Nat.add b n).
Proof. exact (TRANS (@lem101254 q n b h1) (@lem101257 b n)). Qed.
Lemma lem101262 (p : nat) (m : nat) (a : nat) (q : nat) (n : nat) (b : nat) (h1 : p = (Nat.add m a)) (h2 : q = (Nat.add n b)) : (Nat.add p q) = (term16 a m b n).
Proof. exact (MK_COMB (@lem101252 p m a h1) (@lem101261 q n b h2)). Qed.
Lemma lem101264 (m : nat) (n : nat) (p : nat) : (term17 m n p) = (term18 m n p).
Proof. exact (proj1 (@lem101233 n m p)). Qed.
Lemma lem101265 (a : nat) (m : nat) (b : nat) (n : nat) : (term16 a m b n) = (term19 a m b n).
Proof. exact (@lem101264 a m (Nat.add b n)). Qed.
Lemma lem101273 (n : nat) (m : nat) (p : nat) : (term18 m n p) = (term18 n m p).
Proof. exact (proj2 (@lem101233 n m p)). Qed.
Lemma lem101274 (b : nat) (m : nat) (n : nat) : (term18 m b n) = (term18 b m n).
Proof. exact (@lem101273 b m n). Qed.
Lemma lem101283 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem101284 (a : nat) (b : nat) (m : nat) (n : nat) : (term19 a m b n) = (term19 a b m n).
Proof. exact (MK_COMB (@lem101283 a) (@lem101274 b m n)). Qed.
Lemma lem101291 (a : nat) (b : nat) (m : nat) (n : nat) : (term16 a m b n) = (term19 a b m n).
Proof. exact (TRANS (@lem101265 a m b n) (@lem101284 a b m n)). Qed.
Lemma lem101292 (p : nat) (m : nat) (a : nat) (q : nat) (n : nat) (b : nat) (h1 : p = (Nat.add m a)) (h2 : q = (Nat.add n b)) : (Nat.add p q) = (term19 a b m n).
Proof. exact (TRANS (@lem101262 p m a q n b h1 h2) (@lem101291 a b m n)). Qed.
Lemma lem101293 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem101294 (p : nat) (m : nat) (a : nat) (q : nat) (n : nat) (b : nat) (h1 : p = (Nat.add m a)) (h2 : q = (Nat.add n b)) : (term20 p q) = (term21 a b m n).
Proof. exact (MK_COMB (@lem101293) (@lem101292 p m a q n b h1 h2)). Qed.
Lemma lem101296 (m : nat) (n : nat) (p : nat) : (term17 m n p) = (term18 m n p).
Proof. exact (proj1 (@lem101233 n m p)). Qed.
Lemma lem101297 (m : nat) (n : nat) (a : nat) (b : nat) : (term16 m n a b) = (term19 m n a b).
Proof. exact (@lem101296 m n (Nat.add a b)). Qed.
Lemma lem101305 (n : nat) (m : nat) (p : nat) : (term18 m n p) = (term18 n m p).
Proof. exact (proj2 (@lem101233 n m p)). Qed.
Lemma lem101306 (a : nat) (n : nat) (b : nat) : (term18 n a b) = (term18 a n b).
Proof. exact (@lem101305 a n b). Qed.
Lemma lem101314 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem101315 (b : nat) (n : nat) : (Nat.add n b) = (Nat.add b n).
Proof. exact (@lem101314 b n). Qed.
Lemma lem101319 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem101320 (a : nat) (b : nat) (n : nat) : (term18 a n b) = (term18 a b n).
Proof. exact (MK_COMB (@lem101319 a) (@lem101315 b n)). Qed.
Lemma lem101327 (a : nat) (b : nat) (n : nat) : (term18 n a b) = (term18 a b n).
Proof. exact (TRANS (@lem101306 a n b) (@lem101320 a b n)). Qed.
Lemma lem101328 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem101329 (m : nat) (a : nat) (b : nat) (n : nat) : (term19 m n a b) = (term19 m a b n).
Proof. exact (MK_COMB (@lem101328 m) (@lem101327 a b n)). Qed.
Lemma lem101331 (n : nat) (m : nat) (p : nat) : (term18 m n p) = (term18 n m p).
Proof. exact (proj2 (@lem101233 n m p)). Qed.
Lemma lem101332 (a : nat) (m : nat) (b : nat) (n : nat) : (term19 m a b n) = (term19 a m b n).
Proof. exact (@lem101331 a m (Nat.add b n)). Qed.
Lemma lem101340 (n : nat) (m : nat) (p : nat) : (term18 m n p) = (term18 n m p).
Proof. exact (proj2 (@lem101233 n m p)). Qed.
Lemma lem101341 (b : nat) (m : nat) (n : nat) : (term18 m b n) = (term18 b m n).
Proof. exact (@lem101340 b m n). Qed.
Lemma lem101350 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem101351 (a : nat) (b : nat) (m : nat) (n : nat) : (term19 a m b n) = (term19 a b m n).
Proof. exact (MK_COMB (@lem101350 a) (@lem101341 b m n)). Qed.
Lemma lem101358 (a : nat) (b : nat) (m : nat) (n : nat) : (term19 m a b n) = (term19 a b m n).
Proof. exact (TRANS (@lem101332 a m b n) (@lem101351 a b m n)). Qed.
Lemma lem101359 (a : nat) (b : nat) (m : nat) (n : nat) : (term19 m n a b) = (term19 a b m n).
Proof. exact (TRANS (@lem101329 m a b n) (@lem101358 a b m n)). Qed.
Lemma lem101360 (a : nat) (b : nat) (m : nat) (n : nat) : (term16 m n a b) = (term19 a b m n).
Proof. exact (TRANS (@lem101297 m n a b) (@lem101359 a b m n)). Qed.
Lemma lem101361 (p : nat) (m : nat) (a : nat) (q : nat) (n : nat) (b : nat) (h1 : p = (Nat.add m a)) (h2 : q = (Nat.add n b)) : ((Nat.add p q) = (term16 m n a b)) = ((term19 a b m n) = (term19 a b m n)).
Proof. exact (MK_COMB (@lem101294 p m a q n b h1 h2) (@lem101360 a b m n)). Qed.
Lemma lem101363 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem101364 (x : nat) : (x = x) = True.
Proof. exact (@lem101363 nat x). Qed.
Lemma lem101365 (a : nat) (b : nat) (m : nat) (n : nat) : ((term19 a b m n) = (term19 a b m n)) = True.
Proof. exact (@lem101364 (term19 a b m n)). Qed.
Lemma lem101366 (p : nat) (m : nat) (a : nat) (q : nat) (n : nat) (b : nat) (h1 : p = (Nat.add m a)) (h2 : q = (Nat.add n b)) : ((Nat.add p q) = (term16 m n a b)) = True.
Proof. exact (TRANS (@lem101361 p m a q n b h1 h2) (@lem101365 a b m n)). Qed.
Lemma lem101367 (p : nat) (m : nat) (a : nat) (q : nat) (n : nat) (b : nat) (h1 : p = (Nat.add m a)) (h2 : q = (Nat.add n b)) : True = ((Nat.add p q) = (term16 m n a b)).
Proof. exact (SYM (@lem101366 p m a q n b h1 h2)). Qed.
Lemma lem101368 (p : nat) (m : nat) (a : nat) (q : nat) (n : nat) (b : nat) (h1 : p = (Nat.add m a)) (h2 : q = (Nat.add n b)) : (Nat.add p q) = (term16 m n a b).
Proof. exact (EQ_MP (@lem101367 p m a q n b h1 h2) (@lem0)). Qed.
Lemma lem101369 (p : nat) (m : nat) (a : nat) (q : nat) (n : nat) (b : nat) (h1 : p = (Nat.add m a)) (h2 : q = (Nat.add n b)) : term11 p q m n.
Proof. exact (ex_intro (term22 p q m n) (Nat.add a b) (@lem101368 p m a q n b h1 h2)). Qed.
Lemma lem101370 (p : nat) (m : nat) (q : nat) (n : nat) (h1 : term7 p m q n) : term3 q n.
Proof. exact (proj2 (@lem101228 p m q n h1)). Qed.
Lemma lem101371 (p : nat) (m : nat) (q : nat) (n : nat) (h1 : term7 p m q n) : term3 p m.
Proof. exact (proj1 (@lem101228 p m q n h1)). Qed.
Lemma lem101372 (q : nat) (n : nat) (p : nat) (m : nat) (a : nat) (h1 : term3 q n) (h2 : p = (Nat.add m a)) : term11 p q m n.
Proof. exact (ex_elim (@lem101229 q n h1) (fun b : nat => fun h0 : term23 q n b => @lem101369 p m a q n b h2 h0)). Qed.
Lemma lem101373 (p : nat) (m : nat) (q : nat) (n : nat) (h1 : term3 p m) (h2 : term3 q n) : term11 p q m n.
Proof. exact (ex_elim (@lem101231 p m h1) (fun a : nat => fun h0 : term23 p m a => @lem101372 q n p m a h2 h0)). Qed.
Lemma lem101374 (p : nat) (m : nat) (q : nat) (n : nat) (h1 : term3 p m) (h2 : term7 p m q n) : (term3 q n) = (term11 p q m n).
Proof. exact (prop_ext (fun h3 : term3 q n => @lem101373 p m q n h1 h3) (fun h3 : term11 p q m n => @lem101370 p m q n h2)). Qed.
Lemma lem101375 (p : nat) (m : nat) (q : nat) (n : nat) (h1 : term3 p m) (h2 : term7 p m q n) : term11 p q m n.
Proof. exact (EQ_MP (@lem101374 p m q n h1 h2) (@lem101370 p m q n h2)). Qed.
Lemma lem101376 (p : nat) (m : nat) (q : nat) (n : nat) (h1 : term7 p m q n) : (term3 p m) = (term11 p q m n).
Proof. exact (prop_ext (fun h2 : term3 p m => @lem101375 p m q n h2 h1) (fun h2 : term11 p q m n => @lem101371 p m q n h1)). Qed.
Lemma lem101377 (p : nat) (m : nat) (q : nat) (n : nat) (h1 : term7 p m q n) : term11 p q m n.
Proof. exact (EQ_MP (@lem101376 p m q n h1) (@lem101371 p m q n h1)). Qed.
Lemma lem101378 (p : nat) (q : nat) (m : nat) (n : nat) : term13 p q m n.
Proof. exact (fun h0 : term7 p m q n => @lem101377 p m q n h0). Qed.
Lemma lem101379 (m : nat) (n : nat) (p : nat) (q : nat) : term12 m n p q.
Proof. exact (EQ_MP (@lem101227 m n p q) (@lem101378 p q m n)). Qed.
Lemma lem101384 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (fun q : nat => @lem101379 m n p q). Qed.
Lemma lem101389 (m : nat) (n : nat) : term25 m n.
Proof. exact (fun p : nat => @lem101384 m n p). Qed.
Lemma lem101394 (m : nat) : term26 m.
Proof. exact (fun n : nat => @lem101389 m n). Qed.
Lemma lem101399 : term27.
Proof. exact (fun m : nat => @lem101394 m). Qed.
