Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm76380_term_abbrevs.
Require Import thm75635_spec.
Require Import thm76296_spec.
Require Import thm9396_spec.
Lemma lem76297 : term0.
Proof. exact (@lem75635 nat). Qed.
Lemma lem76298 : term1.
Proof. exact (@lem76297 (NUMERAL 0)). Qed.
Lemma lem76299 : term1 = term2.
Proof. exact (eq_refl term1). Qed.
Lemma lem76300 : term2.
Proof. exact (EQ_MP (@lem76299) (@lem76298)). Qed.
Lemma lem76301 : term3.
Proof. exact (@lem76300 term4). Qed.
Lemma lem76302 : term3 = term5.
Proof. exact (eq_refl term3). Qed.
Lemma lem76303 : term5.
Proof. exact (EQ_MP (@lem76302) (@lem76301)). Qed.
Lemma lem76304 (fn : nat -> nat) (n : nat) : (term6 fn n) = (term7 fn n).
Proof. exact (eq_refl (term6 fn n)). Qed.
Lemma lem76305 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem76306 (fn : nat -> nat) (n : nat) : (term8 fn n) = (term9 fn n).
Proof. exact (MK_COMB (@lem76304 fn n) (@lem76305 n)). Qed.
Lemma lem76307 (fn : nat -> nat) (n : nat) : (term9 fn n) = (term10 fn n).
Proof. exact (eq_refl (term9 fn n)). Qed.
Lemma lem76308 (fn : nat -> nat) (n : nat) : (term8 fn n) = (term10 fn n).
Proof. exact (TRANS (@lem76306 fn n) (@lem76307 fn n)). Qed.
Lemma lem76309 (fn : nat -> nat) (n : nat) : (term11 fn n) = (term11 fn n).
Proof. exact (eq_refl (term11 fn n)). Qed.
Lemma lem76310 (fn : nat -> nat) (n : nat) : ((term12 fn n) = (term8 fn n)) = ((term12 fn n) = (term10 fn n)).
Proof. exact (MK_COMB (@lem76309 fn n) (@lem76308 fn n)). Qed.
Lemma lem76311 (fn : nat -> nat) : (term13 fn) = (term14 fn).
Proof. exact (fun_ext (fun n : nat => @lem76310 fn n)). Qed.
Lemma lem76312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem76313 (fn : nat -> nat) : (term15 fn) = (term16 fn).
Proof. exact (MK_COMB (@lem76312) (@lem76311 fn)). Qed.
Lemma lem76314 (fn : nat -> nat) : (term17 fn) = (term17 fn).
Proof. exact (eq_refl (term17 fn)). Qed.
Lemma lem76315 (fn : nat -> nat) : (term18 fn) = (term19 fn).
Proof. exact (MK_COMB (@lem76314 fn) (@lem76313 fn)). Qed.
Lemma lem76316 : term20 = term21.
Proof. exact (fun_ext (fun fn : nat -> nat => @lem76315 fn)). Qed.
Lemma lem76317 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem76318 : term5 = term22.
Proof. exact (MK_COMB (@lem76317) (@lem76316)). Qed.
Lemma lem76319 : term22.
Proof. exact (EQ_MP (@lem76318) (@lem76303)). Qed.
Lemma lem76320 (P : type1002) : term23 P.
Proof. exact (@lem9396 (nat -> nat) P). Qed.
Lemma lem76321 : term24.
Proof. exact (@lem76320 term21). Qed.
Lemma lem76322 : term25.
Proof. exact (@lem76321 (@lem76319)). Qed.
Lemma lem76323 : term25 = term26.
Proof. exact (eq_refl term25). Qed.
Lemma lem76324 : term26.
Proof. exact (EQ_MP (@lem76323) (@lem76322)). Qed.
Lemma lem76325 (h1 : BIT0 = term27) : BIT0 = term27.
Proof. exact (h1). Qed.
Lemma lem76326 (h1 : BIT0 = term27) : term27 = BIT0.
Proof. exact (SYM (@lem76325 h1)). Qed.
Lemma lem76327 (h1 : term27 = BIT0) : term27 = BIT0.
Proof. exact (h1). Qed.
Lemma lem76328 (h1 : term27 = BIT0) : BIT0 = term27.
Proof. exact (SYM (@lem76327 h1)). Qed.
Lemma lem76329 : (BIT0 = term27) = (term27 = BIT0).
Proof. exact (prop_ext (fun h1 : BIT0 = term27 => @lem76326 h1) (fun h1 : term27 = BIT0 => @lem76328 h1)). Qed.
Lemma lem76336 : term27 = BIT0.
Proof. exact (EQ_MP (@lem76329) (@lem76296)). Qed.
Lemma lem76337 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem76338 : term28 = term29.
Proof. exact (MK_COMB (@lem76336) (@lem76337)). Qed.
Lemma lem76339 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem76340 : term30 = term31.
Proof. exact (MK_COMB (@lem76339) (@lem76338)). Qed.
Lemma lem76341 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem76342 : (term28 = (NUMERAL 0)) = (term29 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem76340) (@lem76341)). Qed.
Lemma lem76345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem76346 : term32 = term33.
Proof. exact (MK_COMB (@lem76345) (@lem76342)). Qed.
Lemma lem76354 : term27 = BIT0.
Proof. exact (EQ_MP (@lem76329) (@lem76296)). Qed.
Lemma lem76355 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem76356 (n : nat) : (term34 n) = (term35 n).
Proof. exact (MK_COMB (@lem76354) (@lem76355 n)). Qed.
Lemma lem76357 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem76358 (n : nat) : (term36 n) = (term37 n).
Proof. exact (MK_COMB (@lem76357) (@lem76356 n)). Qed.
Lemma lem76360 : term27 = BIT0.
Proof. exact (EQ_MP (@lem76329) (@lem76296)). Qed.
Lemma lem76361 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem76362 (n : nat) : (term38 n) = (BIT0 n).
Proof. exact (MK_COMB (@lem76360) (@lem76361 n)). Qed.
Lemma lem76363 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem76364 (n : nat) : (term39 n) = (term40 n).
Proof. exact (MK_COMB (@lem76363) (@lem76362 n)). Qed.
Lemma lem76365 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem76366 (n : nat) : (term41 n) = (term42 n).
Proof. exact (MK_COMB (@lem76365) (@lem76364 n)). Qed.
Lemma lem76367 (n : nat) : ((term34 n) = (term41 n)) = ((term35 n) = (term42 n)).
Proof. exact (MK_COMB (@lem76358 n) (@lem76366 n)). Qed.
Lemma lem76370 : term43 = term44.
Proof. exact (fun_ext (fun n : nat => @lem76367 n)). Qed.
Lemma lem76371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem76372 : term45 = term46.
Proof. exact (MK_COMB (@lem76371) (@lem76370)). Qed.
Lemma lem76377 : term26 = term47.
Proof. exact (MK_COMB (@lem76346) (@lem76372)). Qed.
Lemma lem76380 : term47.
Proof. exact (EQ_MP (@lem76377) (@lem76324)). Qed.
