Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LT_1_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_POS_spec.
Require Import REAL_POW_LT2_spec.
Require Import REAL_POW_ONE_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1638322 (n : nat) : term0 n.
Proof. exact (@lem1638321 n). Qed.
Lemma lem1638323 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1638324 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1638323 n) (@lem1638322 n)). Qed.
Lemma lem1638325 (n : nat) : term2 n.
Proof. exact (@lem1638324 n term3). Qed.
Lemma lem1638326 (n : nat) : (term2 n) = (term4 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1638327 (n : nat) : term4 n.
Proof. exact (EQ_MP (@lem1638326 n) (@lem1638325 n)). Qed.
Lemma lem1638328 (n : nat) (x : real) : term5 n x.
Proof. exact (@lem1638327 n x). Qed.
Lemma lem1638329 (x : real) (n : nat) : (term5 n x) = (term6 x n).
Proof. exact (eq_refl (term5 n x)). Qed.
Lemma lem1638330 (x : real) (n : nat) : term6 x n.
Proof. exact (EQ_MP (@lem1638329 x n) (@lem1638328 n x)). Qed.
Lemma lem1638331 (n : nat) (x : real) (h1 : term7 n x) : term7 n x.
Proof. exact (h1). Qed.
Lemma lem1638332 (x : real) (h1 : term8 x) : term8 x.
Proof. exact (h1). Qed.
Lemma lem1638333 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem1638334 (n : nat) : term10 n.
Proof. exact (@lem1384343 n). Qed.
Lemma lem1638335 (n : nat) : (term10 n) = (term11 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1638336 (n : nat) : term11 n.
Proof. exact (EQ_MP (@lem1638335 n) (@lem1638334 n)). Qed.
Lemma lem1638337 (n : nat) : (term11 n) = ((term11 n) = True).
Proof. exact (@lem7 (term11 n)). Qed.
Lemma lem1638339 (n : nat) : term12 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem1638340 (n : nat) : (term12 n) = ((term13 n) = term3).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem1638342 (n : nat) : term14 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1638355 (x : real) : (term8 x) = ((term8 x) = True).
Proof. exact (@lem7 (term8 x)). Qed.
Lemma lem1638364 (n : nat) (h1 : term9 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1638342 n (@lem1638333 n h1)). Qed.
Lemma lem1638365 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1638366 (n : nat) (h1 : term9 n) : (term9 n) = (~ False).
Proof. exact (MK_COMB (@lem1638365) (@lem1638364 n h1)). Qed.
Lemma lem1638368 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1638369 (n : nat) (h1 : term9 n) : (term9 n) = True.
Proof. exact (TRANS (@lem1638366 n h1) (@lem1638368)). Qed.
Lemma lem1638370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1638371 (n : nat) (h1 : term9 n) : (term15 n) = (and True).
Proof. exact (MK_COMB (@lem1638370) (@lem1638369 n h1)). Qed.
Lemma lem1638375 (n : nat) : (term11 n) = True.
Proof. exact (EQ_MP (@lem1638337 n) (@lem1638336 n)). Qed.
Lemma lem1638376 : term16 = True.
Proof. exact (@lem1638375 term17). Qed.
Lemma lem1638377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1638378 : term18 = (and True).
Proof. exact (MK_COMB (@lem1638377) (@lem1638376)). Qed.
Lemma lem1638380 (x : real) (h1 : term8 x) : (term8 x) = True.
Proof. exact (EQ_MP (@lem1638355 x) (@lem1638332 x h1)). Qed.
Lemma lem1638381 (x : real) (h1 : term8 x) : (term19 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1638378) (@lem1638380 x h1)). Qed.
Lemma lem1638383 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1638384 : (True /\ True) = True.
Proof. exact (@lem1638383 True). Qed.
Lemma lem1638385 (x : real) (h1 : term8 x) : (term19 x) = True.
Proof. exact (TRANS (@lem1638381 x h1) (@lem1638384)). Qed.
Lemma lem1638386 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term20 n x) = (True /\ True).
Proof. exact (MK_COMB (@lem1638371 n h1) (@lem1638385 x h2)). Qed.
Lemma lem1638388 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1638389 : (True /\ True) = True.
Proof. exact (@lem1638388 True). Qed.
Lemma lem1638390 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term20 n x) = True.
Proof. exact (TRANS (@lem1638386 n x h1 h2) (@lem1638389)). Qed.
Lemma lem1638391 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1638392 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term21 n x) = (imp True).
Proof. exact (MK_COMB (@lem1638391) (@lem1638390 n x h1 h2)). Qed.
Lemma lem1638394 (n : nat) : (term13 n) = term3.
Proof. exact (EQ_MP (@lem1638340 n) (@lem1638339 n)). Qed.
Lemma lem1638395 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1638396 (n : nat) : (term22 n) = term23.
Proof. exact (MK_COMB (@lem1638395) (@lem1638394 n)). Qed.
Lemma lem1638397 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1638398 (x : real) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem1638396 n) (@lem1638397 x n)). Qed.
Lemma lem1638399 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term6 x n) = (term26 x n).
Proof. exact (MK_COMB (@lem1638392 n x h1 h2) (@lem1638398 x n)). Qed.
Lemma lem1638401 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1638402 (x : real) (n : nat) : (term26 x n) = (term25 x n).
Proof. exact (@lem1638401 (term25 x n)). Qed.
Lemma lem1638403 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term6 x n) = (term25 x n).
Proof. exact (TRANS (@lem1638399 n x h1 h2) (@lem1638402 x n)). Qed.
Lemma lem1638404 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1638405 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term27 x n) = (term28 x n).
Proof. exact (MK_COMB (@lem1638404) (@lem1638403 n x h1 h2)). Qed.
Lemma lem1638406 (x : real) (n : nat) : (term25 x n) = (term25 x n).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem1638407 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term29 x n) = (term30 x n).
Proof. exact (MK_COMB (@lem1638405 n x h1 h2) (@lem1638406 x n)). Qed.
Lemma lem1638409 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1638410 (x : real) (n : nat) : (term30 x n) = True.
Proof. exact (@lem1638409 (term25 x n)). Qed.
Lemma lem1638411 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term29 x n) = True.
Proof. exact (TRANS (@lem1638407 n x h1 h2) (@lem1638410 x n)). Qed.
Lemma lem1638412 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : True = (term29 x n).
Proof. exact (SYM (@lem1638411 n x h1 h2)). Qed.
Lemma lem1638413 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : term29 x n.
Proof. exact (EQ_MP (@lem1638412 n x h1 h2) (@lem0)). Qed.
Lemma lem1638414 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : term25 x n.
Proof. exact (@lem1638413 n x h1 h2 (@lem1638330 x n)). Qed.
Lemma lem1638415 (n : nat) (x : real) (h1 : term7 n x) : term8 x.
Proof. exact (proj2 (@lem1638331 n x h1)). Qed.
Lemma lem1638416 (n : nat) (x : real) (h1 : term7 n x) : term9 n.
Proof. exact (proj1 (@lem1638331 n x h1)). Qed.
Lemma lem1638417 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term8 x) = (term25 x n).
Proof. exact (prop_ext (fun h3 : term8 x => @lem1638414 n x h1 h2) (fun h3 : term25 x n => @lem1638332 x h2)). Qed.
Lemma lem1638418 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : term25 x n.
Proof. exact (EQ_MP (@lem1638417 n x h1 h2) (@lem1638332 x h2)). Qed.
Lemma lem1638419 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term9 n) = (term25 x n).
Proof. exact (prop_ext (fun h3 : term9 n => @lem1638418 n x h1 h2) (fun h3 : term25 x n => @lem1638333 n h1)). Qed.
Lemma lem1638420 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : term25 x n.
Proof. exact (EQ_MP (@lem1638419 n x h1 h2) (@lem1638333 n h1)). Qed.
Lemma lem1638421 (n : nat) (x : real) (h1 : term9 n) (h2 : term7 n x) : (term8 x) = (term25 x n).
Proof. exact (prop_ext (fun h3 : term8 x => @lem1638420 n x h1 h3) (fun h3 : term25 x n => @lem1638415 n x h2)). Qed.
Lemma lem1638422 (n : nat) (x : real) (h1 : term9 n) (h2 : term7 n x) : term25 x n.
Proof. exact (EQ_MP (@lem1638421 n x h1 h2) (@lem1638415 n x h2)). Qed.
Lemma lem1638423 (n : nat) (x : real) (h1 : term7 n x) : (term9 n) = (term25 x n).
Proof. exact (prop_ext (fun h2 : term9 n => @lem1638422 n x h2 h1) (fun h2 : term25 x n => @lem1638416 n x h1)). Qed.
Lemma lem1638424 (n : nat) (x : real) (h1 : term7 n x) : term25 x n.
Proof. exact (EQ_MP (@lem1638423 n x h1) (@lem1638416 n x h1)). Qed.
Lemma lem1638425 (x : real) (n : nat) : term31 x n.
Proof. exact (fun h0 : term7 n x => @lem1638424 n x h0). Qed.
Lemma lem1638430 (n : nat) : term32 n.
Proof. exact (fun x : real => @lem1638425 x n). Qed.
Lemma lem1638435 : term33.
Proof. exact (fun n : nat => @lem1638430 n). Qed.
