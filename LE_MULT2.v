Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_MULT2_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_EXISTS_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem102216 (m : nat) : term0 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem102217 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem102218 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem102217 m) (@lem102216 m)). Qed.
Lemma lem102219 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem102218 m n). Qed.
Lemma lem102220 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem102221 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem102220 m n) (@lem102219 m n)). Qed.
Lemma lem102222 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem102221 m n p). Qed.
Lemma lem102223 (m : nat) (n : nat) (p : nat) : (term4 m n p) = ((term5 m n p) = (term6 m n p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem102225 (m : nat) : term7 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem102226 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem102227 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem102226 m) (@lem102225 m)). Qed.
Lemma lem102228 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem102227 m n). Qed.
Lemma lem102229 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem102230 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem102229 m n) (@lem102228 m n)). Qed.
Lemma lem102231 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem102230 m n p). Qed.
Lemma lem102232 (m : nat) (n : nat) (p : nat) : (term11 m n p) = ((term12 m n p) = (term13 m n p)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem102243 (m : nat) : term14 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem102244 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem102245 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem102244 m) (@lem102243 m)). Qed.
Lemma lem102246 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem102245 m n). Qed.
Lemma lem102247 (n : nat) (m : nat) : (term16 m n) = ((Peano.le m n) = (term17 n m)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem102254 (n : nat) (m : nat) : (Peano.le m n) = (term17 n m).
Proof. exact (EQ_MP (@lem102247 n m) (@lem102246 m n)). Qed.
Lemma lem102261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102262 (n : nat) (m : nat) : (term18 m n) = (term19 n m).
Proof. exact (MK_COMB (@lem102261) (@lem102254 n m)). Qed.
Lemma lem102264 (n : nat) (m : nat) : (Peano.le m n) = (term17 n m).
Proof. exact (EQ_MP (@lem102247 n m) (@lem102246 m n)). Qed.
Lemma lem102265 (q : nat) (p : nat) : (Peano.le p q) = (term17 q p).
Proof. exact (@lem102264 q p). Qed.
Lemma lem102272 (n : nat) (m : nat) (q : nat) (p : nat) : (term20 m n p q) = (term21 n m q p).
Proof. exact (MK_COMB (@lem102262 n m) (@lem102265 q p)). Qed.
Lemma lem102275 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102276 (n : nat) (m : nat) (q : nat) (p : nat) : (term22 m n p q) = (term23 n m q p).
Proof. exact (MK_COMB (@lem102275) (@lem102272 n m q p)). Qed.
Lemma lem102278 (n : nat) (m : nat) : (Peano.le m n) = (term17 n m).
Proof. exact (EQ_MP (@lem102247 n m) (@lem102246 m n)). Qed.
Lemma lem102279 (n : nat) (q : nat) (m : nat) (p : nat) : (term24 m p n q) = (term25 n q m p).
Proof. exact (@lem102278 (Nat.mul n q) (Nat.mul m p)). Qed.
Lemma lem102286 (n : nat) (q : nat) (m : nat) (p : nat) : (term26 m p n q) = (term27 n q m p).
Proof. exact (MK_COMB (@lem102276 n m q p) (@lem102279 n q m p)). Qed.
Lemma lem102289 (m : nat) (p : nat) (n : nat) (q : nat) : (term27 n q m p) = (term26 m p n q).
Proof. exact (SYM (@lem102286 n q m p)). Qed.
Lemma lem102290 (n : nat) (m : nat) (q : nat) (p : nat) (h1 : term21 n m q p) : term21 n m q p.
Proof. exact (h1). Qed.
Lemma lem102291 (q : nat) (p : nat) (h1 : term17 q p) : term17 q p.
Proof. exact (h1). Qed.
Lemma lem102293 (n : nat) (m : nat) (h1 : term17 n m) : term17 n m.
Proof. exact (h1). Qed.
Lemma lem102295 (m : nat) : term28 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem102296 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem102297 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem102296 m) (@lem102295 m)). Qed.
Lemma lem102298 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem102297 m n). Qed.
Lemma lem102299 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem102300 (n : nat) (m : nat) : term31 n m.
Proof. exact (EQ_MP (@lem102299 n m) (@lem102298 m n)). Qed.
Lemma lem102301 (n : nat) (m : nat) (p : nat) : term32 n m p.
Proof. exact (@lem102300 n m p). Qed.
Lemma lem102302 (n : nat) (m : nat) (p : nat) : (term32 n m p) = ((term33 m n p) = (term34 n m p)).
Proof. exact (eq_refl (term32 n m p)). Qed.
Lemma lem102307 (n : nat) (m : nat) (a : nat) (h1 : n = (Nat.add m a)) : n = (Nat.add m a).
Proof. exact (h1). Qed.
Lemma lem102308 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem102309 (n : nat) (m : nat) (a : nat) (h1 : n = (Nat.add m a)) : (Nat.mul n) = (term35 m a).
Proof. exact (MK_COMB (@lem102308) (@lem102307 n m a h1)). Qed.
Lemma lem102311 (q : nat) (p : nat) (b : nat) (h1 : q = (Nat.add p b)) : q = (Nat.add p b).
Proof. exact (h1). Qed.
Lemma lem102312 (n : nat) (m : nat) (a : nat) (q : nat) (p : nat) (b : nat) (h1 : n = (Nat.add m a)) (h2 : q = (Nat.add p b)) : (Nat.mul n q) = (term36 m a p b).
Proof. exact (MK_COMB (@lem102309 n m a h1) (@lem102311 q p b h2)). Qed.
Lemma lem102314 (n : nat) (m : nat) (p : nat) : (term33 m n p) = (term34 n m p).
Proof. exact (EQ_MP (@lem102302 n m p) (@lem102301 n m p)). Qed.
Lemma lem102315 (p : nat) (m : nat) (a : nat) (b : nat) : (term36 m a p b) = (term37 p m a b).
Proof. exact (@lem102314 p (Nat.add m a) b). Qed.
Lemma lem102316 (n : nat) (m : nat) (a : nat) (q : nat) (p : nat) (b : nat) (h1 : n = (Nat.add m a)) (h2 : q = (Nat.add p b)) : (Nat.mul n q) = (term37 p m a b).
Proof. exact (TRANS (@lem102312 n m a q p b h1 h2) (@lem102315 p m a b)). Qed.
Lemma lem102317 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem102318 (n : nat) (m : nat) (a : nat) (q : nat) (p : nat) (b : nat) (h1 : n = (Nat.add m a)) (h2 : q = (Nat.add p b)) : (term38 n q) = (term39 p m a b).
Proof. exact (MK_COMB (@lem102317) (@lem102316 n m a q p b h1 h2)). Qed.
Lemma lem102319 (p : nat) (m : nat) (a : nat) (b : nat) : (term40 p m a b) = (term40 p m a b).
Proof. exact (eq_refl (term40 p m a b)). Qed.
Lemma lem102320 (n : nat) (m : nat) (a : nat) (q : nat) (p : nat) (b : nat) (h1 : n = (Nat.add m a)) (h2 : q = (Nat.add p b)) : ((Nat.mul n q) = (term40 p m a b)) = ((term37 p m a b) = (term40 p m a b)).
Proof. exact (MK_COMB (@lem102318 n m a q p b h1 h2) (@lem102319 p m a b)). Qed.
Lemma lem102323 (n : nat) (m : nat) (a : nat) (q : nat) (p : nat) (b : nat) (h1 : n = (Nat.add m a)) (h2 : q = (Nat.add p b)) : ((term37 p m a b) = (term40 p m a b)) = ((Nat.mul n q) = (term40 p m a b)).
Proof. exact (SYM (@lem102320 n m a q p b h1 h2)). Qed.
Lemma lem102327 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem102232 m n p) (@lem102231 m n p)). Qed.
Lemma lem102328 (m : nat) (a : nat) (p : nat) : (term12 m a p) = (term13 m a p).
Proof. exact (@lem102327 m a p). Qed.
Lemma lem102329 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem102330 (m : nat) (a : nat) (p : nat) : (term41 m a p) = (term42 m a p).
Proof. exact (MK_COMB (@lem102329) (@lem102328 m a p)). Qed.
Lemma lem102332 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem102232 m n p) (@lem102231 m n p)). Qed.
Lemma lem102333 (m : nat) (a : nat) (b : nat) : (term12 m a b) = (term13 m a b).
Proof. exact (@lem102332 m a b). Qed.
Lemma lem102334 (p : nat) (m : nat) (a : nat) (b : nat) : (term37 p m a b) = (term43 p m a b).
Proof. exact (MK_COMB (@lem102330 m a p) (@lem102333 m a b)). Qed.
Lemma lem102336 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem102223 m n p) (@lem102222 m n p)). Qed.
Lemma lem102337 (p : nat) (m : nat) (a : nat) (b : nat) : (term43 p m a b) = (term44 p m a b).
Proof. exact (@lem102336 (term13 m a p) (Nat.mul m b) (Nat.mul a b)). Qed.
Lemma lem102338 (p : nat) (m : nat) (a : nat) (b : nat) : (term37 p m a b) = (term44 p m a b).
Proof. exact (TRANS (@lem102334 p m a b) (@lem102337 p m a b)). Qed.
Lemma lem102339 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem102340 (p : nat) (m : nat) (a : nat) (b : nat) : (term39 p m a b) = (term45 p m a b).
Proof. exact (MK_COMB (@lem102339) (@lem102338 p m a b)). Qed.
Lemma lem102342 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem102223 m n p) (@lem102222 m n p)). Qed.
Lemma lem102343 (p : nat) (m : nat) (a : nat) (b : nat) : (term40 p m a b) = (term43 p m a b).
Proof. exact (@lem102342 (Nat.mul m p) (Nat.mul a p) (term13 m a b)). Qed.
Lemma lem102345 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem102223 m n p) (@lem102222 m n p)). Qed.
Lemma lem102346 (p : nat) (m : nat) (a : nat) (b : nat) : (term43 p m a b) = (term44 p m a b).
Proof. exact (@lem102345 (term13 m a p) (Nat.mul m b) (Nat.mul a b)). Qed.
Lemma lem102347 (p : nat) (m : nat) (a : nat) (b : nat) : (term40 p m a b) = (term44 p m a b).
Proof. exact (TRANS (@lem102343 p m a b) (@lem102346 p m a b)). Qed.
Lemma lem102348 (p : nat) (m : nat) (a : nat) (b : nat) : ((term37 p m a b) = (term40 p m a b)) = ((term44 p m a b) = (term44 p m a b)).
Proof. exact (MK_COMB (@lem102340 p m a b) (@lem102347 p m a b)). Qed.
Lemma lem102350 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem102351 (x : nat) : (x = x) = True.
Proof. exact (@lem102350 nat x). Qed.
Lemma lem102352 (p : nat) (m : nat) (a : nat) (b : nat) : ((term44 p m a b) = (term44 p m a b)) = True.
Proof. exact (@lem102351 (term44 p m a b)). Qed.
Lemma lem102353 (p : nat) (m : nat) (a : nat) (b : nat) : ((term37 p m a b) = (term40 p m a b)) = True.
Proof. exact (TRANS (@lem102348 p m a b) (@lem102352 p m a b)). Qed.
Lemma lem102354 (p : nat) (m : nat) (a : nat) (b : nat) : True = ((term37 p m a b) = (term40 p m a b)).
Proof. exact (SYM (@lem102353 p m a b)). Qed.
Lemma lem102355 (p : nat) (m : nat) (a : nat) (b : nat) : (term37 p m a b) = (term40 p m a b).
Proof. exact (EQ_MP (@lem102354 p m a b) (@lem0)). Qed.
Lemma lem102356 (n : nat) (m : nat) (a : nat) (q : nat) (p : nat) (b : nat) (h1 : n = (Nat.add m a)) (h2 : q = (Nat.add p b)) : (Nat.mul n q) = (term40 p m a b).
Proof. exact (EQ_MP (@lem102323 n m a q p b h1 h2) (@lem102355 p m a b)). Qed.
Lemma lem102357 (n : nat) (m : nat) (a : nat) (q : nat) (p : nat) (b : nat) (h1 : n = (Nat.add m a)) (h2 : q = (Nat.add p b)) : term25 n q m p.
Proof. exact (ex_intro (term46 n q m p) (term47 p m a b) (@lem102356 n m a q p b h1 h2)). Qed.
Lemma lem102358 (n : nat) (m : nat) (q : nat) (p : nat) (h1 : term21 n m q p) : term17 q p.
Proof. exact (proj2 (@lem102290 n m q p h1)). Qed.
Lemma lem102359 (n : nat) (m : nat) (q : nat) (p : nat) (h1 : term21 n m q p) : term17 n m.
Proof. exact (proj1 (@lem102290 n m q p h1)). Qed.
Lemma lem102360 (q : nat) (p : nat) (n : nat) (m : nat) (a : nat) (h1 : term17 q p) (h2 : n = (Nat.add m a)) : term25 n q m p.
Proof. exact (ex_elim (@lem102291 q p h1) (fun b : nat => fun h0 : term48 q p b => @lem102357 n m a q p b h2 h0)). Qed.
Lemma lem102361 (n : nat) (m : nat) (q : nat) (p : nat) (h1 : term17 n m) (h2 : term17 q p) : term25 n q m p.
Proof. exact (ex_elim (@lem102293 n m h1) (fun a : nat => fun h0 : term48 n m a => @lem102360 q p n m a h2 h0)). Qed.
Lemma lem102362 (n : nat) (m : nat) (q : nat) (p : nat) (h1 : term17 n m) (h2 : term21 n m q p) : (term17 q p) = (term25 n q m p).
Proof. exact (prop_ext (fun h3 : term17 q p => @lem102361 n m q p h1 h3) (fun h3 : term25 n q m p => @lem102358 n m q p h2)). Qed.
Lemma lem102363 (n : nat) (m : nat) (q : nat) (p : nat) (h1 : term17 n m) (h2 : term21 n m q p) : term25 n q m p.
Proof. exact (EQ_MP (@lem102362 n m q p h1 h2) (@lem102358 n m q p h2)). Qed.
Lemma lem102364 (n : nat) (m : nat) (q : nat) (p : nat) (h1 : term21 n m q p) : (term17 n m) = (term25 n q m p).
Proof. exact (prop_ext (fun h2 : term17 n m => @lem102363 n m q p h2 h1) (fun h2 : term25 n q m p => @lem102359 n m q p h1)). Qed.
Lemma lem102365 (n : nat) (m : nat) (q : nat) (p : nat) (h1 : term21 n m q p) : term25 n q m p.
Proof. exact (EQ_MP (@lem102364 n m q p h1) (@lem102359 n m q p h1)). Qed.
Lemma lem102366 (n : nat) (q : nat) (m : nat) (p : nat) : term27 n q m p.
Proof. exact (fun h0 : term21 n m q p => @lem102365 n m q p h0). Qed.
Lemma lem102367 (m : nat) (p : nat) (n : nat) (q : nat) : term26 m p n q.
Proof. exact (EQ_MP (@lem102289 m p n q) (@lem102366 n q m p)). Qed.
Lemma lem102372 (m : nat) (p : nat) (n : nat) : term49 m p n.
Proof. exact (fun q : nat => @lem102367 m p n q). Qed.
Lemma lem102377 (m : nat) (n : nat) : term50 m n.
Proof. exact (fun p : nat => @lem102372 m p n). Qed.
Lemma lem102382 (m : nat) : term51 m.
Proof. exact (fun n : nat => @lem102377 m n). Qed.
Lemma lem102387 : term52.
Proof. exact (fun m : nat => @lem102382 m). Qed.
