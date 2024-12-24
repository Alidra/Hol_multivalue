Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINREC_FUN_LEMMA_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SELECT_UNIQUE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm9425_spec.
Lemma lem3808360 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3808361 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3808362 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3808361 t1) (@lem3808360 t1)). Qed.
Lemma lem3808363 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3808362 t1 t2). Qed.
Lemma lem3808364 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3808365 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3808364 t1 t2) (@lem3808363 t1 t2)). Qed.
Lemma lem3808366 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3808365 t1 t2 t3). Qed.
Lemma lem3808367 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3808368 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3808367 t1 t2 t3) (@lem3808366 t1 t2 t3)). Qed.
Lemma lem3808369 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3808368 t1 t2 t3)). Qed.
Lemma lem3808370 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem3808371 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term8 A P.
Proof. exact (@lem3808370 A h1 P). Qed.
Lemma lem3808372 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem3808373 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term9 A P.
Proof. exact (EQ_MP (@lem3808372 A P) (@lem3808371 A P h1)). Qed.
Lemma lem3808374 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term10 A P x.
Proof. exact (@lem3808373 A P h1 x). Qed.
Lemma lem3808375 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem3808376 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term11 A P x.
Proof. exact (EQ_MP (@lem3808375 A P x) (@lem3808374 A P x h1)). Qed.
Lemma lem3808377 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) : term12 A P x.
Proof. exact (h1). Qed.
Lemma lem3808378 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) (h2 : term7 A) : (@ε A P) = x.
Proof. exact (@lem3808376 A P x h2 (@lem3808377 A P x h1)). Qed.
Lemma lem3808379 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) : term13 A P x.
Proof. exact (fun h0 : term7 A => @lem3808378 A P x h1 h0). Qed.
Lemma lem3808380 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem3808381 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) (h2 : term7 A) : (@ε A P) = x.
Proof. exact (@lem3808379 A P x h1 (@lem3808380 A h2)). Qed.
Lemma lem3808382 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term11 A P x.
Proof. exact (fun h0 : term12 A P x => @lem3808381 A P x h0 h1). Qed.
Lemma lem3808383 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term9 A P.
Proof. exact (fun x : A => @lem3808382 A P x h1). Qed.
Lemma lem3808384 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (fun P : A -> Prop => @lem3808383 A P h1). Qed.
Lemma lem3808385 {A : Type'} : term14 A.
Proof. exact (fun h0 : term7 A => @lem3808384 A h0). Qed.
Lemma lem3808386 {A : Type'} : term7 A.
Proof. exact (@lem3808385 A (@lem9522 A)). Qed.
Lemma lem3808387 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (@lem3808386 A P). Qed.
Lemma lem3808388 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem3808389 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (EQ_MP (@lem3808388 A P) (@lem3808387 A P)). Qed.
Lemma lem3808390 {A : Type'} (P : A -> Prop) (x : A) : term10 A P x.
Proof. exact (@lem3808389 A P x). Qed.
Lemma lem3808391 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem3808393 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term15 A B C P R) : term15 A B C P R.
Proof. exact (h1). Qed.
Lemma lem3808394 {A B C : Type'} (R : type1408 A B C) (h1 : term16 A B C R) : term16 A B C R.
Proof. exact (h1). Qed.
Lemma lem3808395 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term17 A B C P R.
Proof. exact (h1). Qed.
Lemma lem3808396 {A : Type'} (P : A -> Prop) (s : A) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3808397 {A B C : Type'} (R : type1408 A B C) (s : A) : (term18 A B C R s) = (term19 A B C R s).
Proof. exact (eq_refl (term18 A B C R s)). Qed.
Lemma lem3808398 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3808399 {A B C : Type'} (R : type1408 A B C) (s : A) : (term20 A B C R s) = (term21 A B C R s).
Proof. exact (MK_COMB (@lem3808398 B) (@lem3808397 A B C R s)). Qed.
Lemma lem3808400 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3808401 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : ((term18 A B C R s) = a) = ((term19 A B C R s) = a).
Proof. exact (MK_COMB (@lem3808399 A B C R s) (@lem3808400 B a)). Qed.
Lemma lem3808402 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term22 A B C R s a) = (term22 A B C R s a).
Proof. exact (eq_refl (term22 A B C R s a)). Qed.
Lemma lem3808403 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : ((term23 A B C R s a) = ((term18 A B C R s) = a)) = ((term23 A B C R s a) = ((term19 A B C R s) = a)).
Proof. exact (MK_COMB (@lem3808402 A B C R s a) (@lem3808401 A B C R s a)). Qed.
Lemma lem3808404 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : ((term23 A B C R s a) = ((term19 A B C R s) = a)) = ((term23 A B C R s a) = ((term18 A B C R s) = a)).
Proof. exact (SYM (@lem3808403 A B C R s a)). Qed.
Lemma lem3808405 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (h1 : term23 A B C R s a) : term23 A B C R s a.
Proof. exact (h1). Qed.
Lemma lem3808406 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3808408 {A : Type'} (P : A -> Prop) (x : A) : term11 A P x.
Proof. exact (EQ_MP (@lem3808391 A P x) (@lem3808390 A P x)). Qed.
Lemma lem3808409 {B : Type'} (P : B -> Prop) (x : B) : term11 B P x.
Proof. exact (@lem3808408 B P x). Qed.
Lemma lem3808410 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : term24 A B C R s a.
Proof. exact (@lem3808409 B (term25 A B C R s) a). Qed.
Lemma lem3808412 (p : Prop) : p = (term26 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3808413 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term27 A B C R s a) = (term28 A B C R s a).
Proof. exact (@lem3808412 (term27 A B C R s a)). Qed.
Lemma lem3808414 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term28 A B C R s a) = (term27 A B C R s a).
Proof. exact (SYM (@lem3808413 A B C R s a)). Qed.
Lemma lem3808415 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (h1 : term29 A B C R s a) : term29 A B C R s a.
Proof. exact (h1). Qed.
Lemma lem3808418 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) (h1 : term30 A B C P n R s a) : term30 A B C P n R s a.
Proof. exact (h1). Qed.
Lemma lem3808419 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : term31 A B C P n R s a.
Proof. exact (fun h0 : term30 A B C P n R s a => @lem3808418 A B C P n R s a h0). Qed.
Lemma lem3808420 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) (h1 : term31 A B C P n R s a) : term31 A B C P n R s a.
Proof. exact (h1). Qed.
Lemma lem3808421 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) (h1 : term30 A B C P n R s a) : term30 A B C P n R s a.
Proof. exact (h1). Qed.
Lemma lem3808422 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) (h1 : term30 A B C P n R s a) (h2 : term31 A B C P n R s a) : term30 A B C P n R s a.
Proof. exact (@lem3808420 A B C P n R s a h2 (@lem3808421 A B C P n R s a h1)). Qed.
Lemma lem3808423 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) (h1 : term30 A B C P n R s a) : term32 A B C P n R s a.
Proof. exact (fun h0 : term31 A B C P n R s a => @lem3808422 A B C P n R s a h1 h0). Qed.
Lemma lem3808424 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) (h1 : term31 A B C P n R s a) : term31 A B C P n R s a.
Proof. exact (h1). Qed.
Lemma lem3808425 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) (h1 : term30 A B C P n R s a) (h2 : term31 A B C P n R s a) : term30 A B C P n R s a.
Proof. exact (@lem3808423 A B C P n R s a h1 (@lem3808424 A B C P n R s a h2)). Qed.
Lemma lem3808426 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) (h1 : term31 A B C P n R s a) : term31 A B C P n R s a.
Proof. exact (fun h0 : term30 A B C P n R s a => @lem3808425 A B C P n R s a h0 h1). Qed.
Lemma lem3808427 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : term33 A B C P n R s a.
Proof. exact (fun h0 : term31 A B C P n R s a => @lem3808426 A B C P n R s a h0). Qed.
Lemma lem3808430 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : term31 A B C P n R s a.
Proof. exact (@lem3808427 A B C P n R s a (@lem3808419 A B C P n R s a)). Qed.
Lemma lem3808431 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : term31 A B C P n R s a.
Proof. exact (@lem3808430 A B C P n R s a). Qed.
Lemma lem3808501 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3808502 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term28 A B C R s a) = (term34 A B C R s a).
Proof. exact (@lem3808501 (term29 A B C R s a)). Qed.
Lemma lem3808504 (t : Prop) : (term35 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3808505 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term34 A B C R s a) = (term27 A B C R s a).
Proof. exact (@lem3808504 (term27 A B C R s a)). Qed.
Lemma lem3808510 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term28 A B C R s a) = (term27 A B C R s a).
Proof. exact (TRANS (@lem3808502 A B C R s a) (@lem3808505 A B C R s a)). Qed.
Lemma lem3808515 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term36 A B C R s a n) = (term36 A B C R s a n).
Proof. exact (eq_refl (term36 A B C R s a n)). Qed.
Lemma lem3808516 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term37 A B C n R s a) = (term38 A B C n R s a).
Proof. exact (MK_COMB (@lem3808515 A B C R s a n) (@lem3808510 A B C R s a)). Qed.
Lemma lem3808519 {A : Type'} (P : A -> Prop) (s : A) : (term39 A P s) = (term39 A P s).
Proof. exact (eq_refl (term39 A P s)). Qed.
Lemma lem3808520 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term40 A B C P n R s a) = (term41 A B C P n R s a).
Proof. exact (MK_COMB (@lem3808519 A P s) (@lem3808516 A B C n R s a)). Qed.
Lemma lem3808523 {A B C : Type'} (R : type1408 A B C) : (term42 A B C R) = (term42 A B C R).
Proof. exact (eq_refl (term42 A B C R)). Qed.
Lemma lem3808524 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term43 A B C P n R s a) = (term44 A B C P n R s a).
Proof. exact (MK_COMB (@lem3808523 A B C R) (@lem3808520 A B C P n R s a)). Qed.
Lemma lem3808527 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term45 A B C P R) = (term45 A B C P R).
Proof. exact (eq_refl (term45 A B C P R)). Qed.
Lemma lem3808528 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term30 A B C P n R s a) = (term46 A B C P n R s a).
Proof. exact (MK_COMB (@lem3808527 A B C P R) (@lem3808524 A B C P n R s a)). Qed.
Lemma lem3808531 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term47 A B C n R s a) = (term48 A B C n R s a).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3808528 A B C P n R s a)). Qed.
Lemma lem3808532 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3808533 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term49 A B C n R s a) = (term50 A B C n R s a).
Proof. exact (MK_COMB (@lem3808532 A) (@lem3808531 A B C n R s a)). Qed.
Lemma lem3808538 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term51 A B C R s a) = (term52 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3808533 A B C n R s a)). Qed.
Lemma lem3808539 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3808540 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term53 A B C R s a) = (term54 A B C R s a).
Proof. exact (MK_COMB (@lem3808539 C) (@lem3808538 A B C R s a)). Qed.
Lemma lem3808545 {A B C : Type'} (s : A) (a : B) : (term55 A B C s a) = (term56 A B C s a).
Proof. exact (fun_ext (fun R : type1408 A B C => @lem3808540 A B C R s a)). Qed.
Lemma lem3808546 {A B C : Type'} : (@all (A -> B -> C -> Prop)) = (@all (A -> B -> C -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> C -> Prop))). Qed.
Lemma lem3808547 {A B C : Type'} (s : A) (a : B) : (term57 A B C s a) = (term58 A B C s a).
Proof. exact (MK_COMB (@lem3808546 A B C) (@lem3808545 A B C s a)). Qed.
Lemma lem3808552 {A B C : Type'} (a : B) : (term59 A B C a) = (term60 A B C a).
Proof. exact (fun_ext (fun s : A => @lem3808547 A B C s a)). Qed.
Lemma lem3808553 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808554 {A B C : Type'} (a : B) : (term61 A B C a) = (term62 A B C a).
Proof. exact (MK_COMB (@lem3808553 A) (@lem3808552 A B C a)). Qed.
Lemma lem3808559 {A B C : Type'} : (term63 A B C) = (term64 A B C).
Proof. exact (fun_ext (fun a : B => @lem3808554 A B C a)). Qed.
Lemma lem3808560 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3808561 {A B C : Type'} : (term65 A B C) = (term66 A B C).
Proof. exact (MK_COMB (@lem3808560 B) (@lem3808559 A B C)). Qed.
Lemma lem3808566 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term67 A B C R s y) = (term23 A B C R s y).
Proof. exact (eq_refl (term67 A B C R s y)). Qed.
Lemma lem3808567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3808568 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term68 A B C R s y) = (term22 A B C R s y).
Proof. exact (MK_COMB (@lem3808567) (@lem3808566 A B C R s y)). Qed.
Lemma lem3808569 {B : Type'} (y : B) (a : B) : (y = a) = (y = a).
Proof. exact (eq_refl (y = a)). Qed.
Lemma lem3808570 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : ((term67 A B C R s y) = (y = a)) = ((term23 A B C R s y) = (y = a)).
Proof. exact (MK_COMB (@lem3808568 A B C R s y) (@lem3808569 B y a)). Qed.
Lemma lem3808571 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term69 A B C R s a) = (term70 A B C R s a).
Proof. exact (fun_ext (fun y : B => @lem3808570 A B C R s y a)). Qed.
Lemma lem3808572 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3808573 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term27 A B C R s a) = (term71 A B C R s a).
Proof. exact (MK_COMB (@lem3808572 B) (@lem3808571 A B C R s a)). Qed.
Lemma lem3808574 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term36 A B C R s a n) = (term36 A B C R s a n).
Proof. exact (eq_refl (term36 A B C R s a n)). Qed.
Lemma lem3808575 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term38 A B C n R s a) = (term72 A B C n R s a).
Proof. exact (MK_COMB (@lem3808574 A B C R s a n) (@lem3808573 A B C R s a)). Qed.
Lemma lem3808576 {A : Type'} (P : A -> Prop) (s : A) : (term39 A P s) = (term39 A P s).
Proof. exact (eq_refl (term39 A P s)). Qed.
Lemma lem3808577 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term41 A B C P n R s a) = (term73 A B C P n R s a).
Proof. exact (MK_COMB (@lem3808576 A P s) (@lem3808575 A B C n R s a)). Qed.
Lemma lem3808578 {A B C : Type'} (R : type1408 A B C) : (term42 A B C R) = (term42 A B C R).
Proof. exact (eq_refl (term42 A B C R)). Qed.
Lemma lem3808579 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term44 A B C P n R s a) = (term74 A B C P n R s a).
Proof. exact (MK_COMB (@lem3808578 A B C R) (@lem3808577 A B C P n R s a)). Qed.
Lemma lem3808580 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term45 A B C P R) = (term45 A B C P R).
Proof. exact (eq_refl (term45 A B C P R)). Qed.
Lemma lem3808581 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term46 A B C P n R s a) = (term75 A B C P n R s a).
Proof. exact (MK_COMB (@lem3808580 A B C P R) (@lem3808579 A B C P n R s a)). Qed.
Lemma lem3808582 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term48 A B C n R s a) = (term76 A B C n R s a).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3808581 A B C P n R s a)). Qed.
Lemma lem3808583 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3808584 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term50 A B C n R s a) = (term77 A B C n R s a).
Proof. exact (MK_COMB (@lem3808583 A) (@lem3808582 A B C n R s a)). Qed.
Lemma lem3808585 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term52 A B C R s a) = (term78 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3808584 A B C n R s a)). Qed.
Lemma lem3808586 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3808587 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term54 A B C R s a) = (term79 A B C R s a).
Proof. exact (MK_COMB (@lem3808586 C) (@lem3808585 A B C R s a)). Qed.
Lemma lem3808588 {A B C : Type'} (s : A) (a : B) : (term56 A B C s a) = (term80 A B C s a).
Proof. exact (fun_ext (fun R : type1408 A B C => @lem3808587 A B C R s a)). Qed.
Lemma lem3808589 {A B C : Type'} : (@all (A -> B -> C -> Prop)) = (@all (A -> B -> C -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> C -> Prop))). Qed.
Lemma lem3808590 {A B C : Type'} (s : A) (a : B) : (term58 A B C s a) = (term81 A B C s a).
Proof. exact (MK_COMB (@lem3808589 A B C) (@lem3808588 A B C s a)). Qed.
Lemma lem3808591 {A B C : Type'} (a : B) : (term60 A B C a) = (term82 A B C a).
Proof. exact (fun_ext (fun s : A => @lem3808590 A B C s a)). Qed.
Lemma lem3808592 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808593 {A B C : Type'} (a : B) : (term62 A B C a) = (term83 A B C a).
Proof. exact (MK_COMB (@lem3808592 A) (@lem3808591 A B C a)). Qed.
Lemma lem3808594 {A B C : Type'} : (term64 A B C) = (term84 A B C).
Proof. exact (fun_ext (fun a : B => @lem3808593 A B C a)). Qed.
Lemma lem3808595 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3808596 {A B C : Type'} : (term66 A B C) = (term85 A B C).
Proof. exact (MK_COMB (@lem3808595 B) (@lem3808594 A B C)). Qed.
Lemma lem3808599 {A B C : Type'} : (term65 A B C) = (term85 A B C).
Proof. exact (TRANS (@lem3808561 A B C) (@lem3808596 A B C)). Qed.
Lemma lem3808600 {B : Type'} (y : B) (a : B) : (y = a) = (y = a).
Proof. exact (eq_refl (y = a)). Qed.
Lemma lem3808601 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n : C) : (R s y n) = (R s y n).
Proof. exact (eq_refl (R s y n)). Qed.
Lemma lem3808602 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term86 A B C R s y) = (term86 A B C R s y).
Proof. exact (fun_ext (fun n : C => @lem3808601 A B C R s y n)). Qed.
Lemma lem3808603 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3808604 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term23 A B C R s y) = (term23 A B C R s y).
Proof. exact (MK_COMB (@lem3808603 C) (@lem3808602 A B C R s y)). Qed.
Lemma lem3808605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3808606 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term22 A B C R s y) = (term22 A B C R s y).
Proof. exact (MK_COMB (@lem3808605) (@lem3808604 A B C R s y)). Qed.
Lemma lem3808607 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : ((term23 A B C R s y) = (y = a)) = ((term23 A B C R s y) = (y = a)).
Proof. exact (MK_COMB (@lem3808606 A B C R s y) (@lem3808600 B y a)). Qed.
Lemma lem3808608 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term70 A B C R s a) = (term70 A B C R s a).
Proof. exact (fun_ext (fun y : B => @lem3808607 A B C R s y a)). Qed.
Lemma lem3808609 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3808610 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term71 A B C R s a) = (term71 A B C R s a).
Proof. exact (MK_COMB (@lem3808609 B) (@lem3808608 A B C R s a)). Qed.
Lemma lem3808613 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term36 A B C R s a n) = (term36 A B C R s a n).
Proof. exact (eq_refl (term36 A B C R s a n)). Qed.
Lemma lem3808614 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term72 A B C n R s a) = (term72 A B C n R s a).
Proof. exact (MK_COMB (@lem3808613 A B C R s a n) (@lem3808610 A B C R s a)). Qed.
Lemma lem3808617 {A : Type'} (P : A -> Prop) (s : A) : (term39 A P s) = (term39 A P s).
Proof. exact (eq_refl (term39 A P s)). Qed.
Lemma lem3808618 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term73 A B C P n R s a) = (term73 A B C P n R s a).
Proof. exact (MK_COMB (@lem3808617 A P s) (@lem3808614 A B C n R s a)). Qed.
Lemma lem3808631 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (a2 : B) (n1 : C) (n2 : C) : (term87 A B C R s a1 a2 n1 n2) = (term87 A B C R s a1 a2 n1 n2).
Proof. exact (eq_refl (term87 A B C R s a1 a2 n1 n2)). Qed.
Lemma lem3808632 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (n1 : C) (n2 : C) : (term88 A B C R s a1 n1 n2) = (term88 A B C R s a1 n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3808631 A B C R s a1 a2 n1 n2)). Qed.
Lemma lem3808633 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3808634 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (n1 : C) (n2 : C) : (term89 A B C R s a1 n1 n2) = (term89 A B C R s a1 n1 n2).
Proof. exact (MK_COMB (@lem3808633 B) (@lem3808632 A B C R s a1 n1 n2)). Qed.
Lemma lem3808635 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term90 A B C R s n1 n2) = (term90 A B C R s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3808634 A B C R s a1 n1 n2)). Qed.
Lemma lem3808636 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3808637 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term91 A B C R s n1 n2) = (term91 A B C R s n1 n2).
Proof. exact (MK_COMB (@lem3808636 B) (@lem3808635 A B C R s n1 n2)). Qed.
Lemma lem3808638 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term92 A B C R n1 n2) = (term92 A B C R n1 n2).
Proof. exact (fun_ext (fun s : A => @lem3808637 A B C R s n1 n2)). Qed.
Lemma lem3808639 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808640 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term93 A B C R n1 n2) = (term93 A B C R n1 n2).
Proof. exact (MK_COMB (@lem3808639 A) (@lem3808638 A B C R n1 n2)). Qed.
Lemma lem3808641 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term94 A B C R n1) = (term94 A B C R n1).
Proof. exact (fun_ext (fun n2 : C => @lem3808640 A B C R n1 n2)). Qed.
Lemma lem3808642 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3808643 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term95 A B C R n1) = (term95 A B C R n1).
Proof. exact (MK_COMB (@lem3808642 C) (@lem3808641 A B C R n1)). Qed.
Lemma lem3808644 {A B C : Type'} (R : type1408 A B C) : (term96 A B C R) = (term96 A B C R).
Proof. exact (fun_ext (fun n1 : C => @lem3808643 A B C R n1)). Qed.
Lemma lem3808645 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3808646 {A B C : Type'} (R : type1408 A B C) : (term16 A B C R) = (term16 A B C R).
Proof. exact (MK_COMB (@lem3808645 C) (@lem3808644 A B C R)). Qed.
Lemma lem3808647 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3808648 {A B C : Type'} (R : type1408 A B C) : (term42 A B C R) = (term42 A B C R).
Proof. exact (MK_COMB (@lem3808647) (@lem3808646 A B C R)). Qed.
Lemma lem3808649 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term74 A B C P n R s a) = (term74 A B C P n R s a).
Proof. exact (MK_COMB (@lem3808648 A B C R) (@lem3808618 A B C P n R s a)). Qed.
Lemma lem3808650 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (R s a n) = (R s a n).
Proof. exact (eq_refl (R s a n)). Qed.
Lemma lem3808651 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term86 A B C R s a) = (term86 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3808650 A B C R s a n)). Qed.
Lemma lem3808652 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3808653 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term23 A B C R s a) = (term23 A B C R s a).
Proof. exact (MK_COMB (@lem3808652 C) (@lem3808651 A B C R s a)). Qed.
Lemma lem3808654 {A B C : Type'} (R : type1408 A B C) (s : A) : (term25 A B C R s) = (term25 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3808653 A B C R s a)). Qed.
Lemma lem3808655 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3808656 {A B C : Type'} (R : type1408 A B C) (s : A) : (term97 A B C R s) = (term97 A B C R s).
Proof. exact (MK_COMB (@lem3808655 B) (@lem3808654 A B C R s)). Qed.
Lemma lem3808659 {A : Type'} (P : A -> Prop) (s : A) : (term39 A P s) = (term39 A P s).
Proof. exact (eq_refl (term39 A P s)). Qed.
Lemma lem3808660 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term98 A B C P R s) = (term98 A B C P R s).
Proof. exact (MK_COMB (@lem3808659 A P s) (@lem3808656 A B C R s)). Qed.
Lemma lem3808661 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term99 A B C P R) = (term99 A B C P R).
Proof. exact (fun_ext (fun s : A => @lem3808660 A B C P R s)). Qed.
Lemma lem3808662 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808663 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term17 A B C P R) = (term17 A B C P R).
Proof. exact (MK_COMB (@lem3808662 A) (@lem3808661 A B C P R)). Qed.
Lemma lem3808664 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3808665 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term45 A B C P R) = (term45 A B C P R).
Proof. exact (MK_COMB (@lem3808664) (@lem3808663 A B C P R)). Qed.
Lemma lem3808666 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term75 A B C P n R s a) = (term75 A B C P n R s a).
Proof. exact (MK_COMB (@lem3808665 A B C P R) (@lem3808649 A B C P n R s a)). Qed.
Lemma lem3808667 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term76 A B C n R s a) = (term76 A B C n R s a).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3808666 A B C P n R s a)). Qed.
Lemma lem3808668 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3808669 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term77 A B C n R s a) = (term77 A B C n R s a).
Proof. exact (MK_COMB (@lem3808668 A) (@lem3808667 A B C n R s a)). Qed.
Lemma lem3808670 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term78 A B C R s a) = (term78 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3808669 A B C n R s a)). Qed.
Lemma lem3808671 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3808672 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term79 A B C R s a) = (term79 A B C R s a).
Proof. exact (MK_COMB (@lem3808671 C) (@lem3808670 A B C R s a)). Qed.
Lemma lem3808673 {A B C : Type'} (s : A) (a : B) : (term80 A B C s a) = (term80 A B C s a).
Proof. exact (fun_ext (fun R : type1408 A B C => @lem3808672 A B C R s a)). Qed.
Lemma lem3808674 {A B C : Type'} : (@all (A -> B -> C -> Prop)) = (@all (A -> B -> C -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> C -> Prop))). Qed.
Lemma lem3808675 {A B C : Type'} (s : A) (a : B) : (term81 A B C s a) = (term81 A B C s a).
Proof. exact (MK_COMB (@lem3808674 A B C) (@lem3808673 A B C s a)). Qed.
Lemma lem3808676 {A B C : Type'} (a : B) : (term82 A B C a) = (term82 A B C a).
Proof. exact (fun_ext (fun s : A => @lem3808675 A B C s a)). Qed.
Lemma lem3808677 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808678 {A B C : Type'} (a : B) : (term83 A B C a) = (term83 A B C a).
Proof. exact (MK_COMB (@lem3808677 A) (@lem3808676 A B C a)). Qed.
Lemma lem3808679 {A B C : Type'} : (term84 A B C) = (term84 A B C).
Proof. exact (fun_ext (fun a : B => @lem3808678 A B C a)). Qed.
Lemma lem3808680 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3808681 {A B C : Type'} : (term85 A B C) = (term85 A B C).
Proof. exact (MK_COMB (@lem3808680 B) (@lem3808679 A B C)). Qed.
Lemma lem3808790 {A B C : Type'} : (term65 A B C) = (term85 A B C).
Proof. exact (TRANS (@lem3808599 A B C) (@lem3808681 A B C)). Qed.
Lemma lem3808791 {A B C : Type'} : (term85 A B C) = (term65 A B C).
Proof. exact (SYM (@lem3808790 A B C)). Qed.
Lemma lem3808792 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term17 A B C P R.
Proof. exact (h1). Qed.
Lemma lem3808793 {A B C : Type'} (R : type1408 A B C) (h1 : term16 A B C R) : term16 A B C R.
Proof. exact (h1). Qed.
Lemma lem3808797 (p : Prop) : p = (term26 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3808798 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : ((term23 A B C R s y) = (y = a)) = (term100 A B C R s y a).
Proof. exact (@lem3808797 ((term23 A B C R s y) = (y = a))). Qed.
Lemma lem3808799 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term100 A B C R s y a) = ((term23 A B C R s y) = (y = a)).
Proof. exact (SYM (@lem3808798 A B C R s y a)). Qed.
Lemma lem3808800 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term101 A B C R s y a) : term101 A B C R s y a.
Proof. exact (h1). Qed.
Lemma lem3808802 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (R s a n) = (R s a n).
Proof. exact (eq_refl (R s a n)). Qed.
Lemma lem3808803 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term86 A B C R s a) = (term86 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3808802 A B C R s a n)). Qed.
Lemma lem3808804 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3808805 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term23 A B C R s a) = (term23 A B C R s a).
Proof. exact (MK_COMB (@lem3808804 C) (@lem3808803 A B C R s a)). Qed.
Lemma lem3808806 {A B C : Type'} (R : type1408 A B C) (s : A) : (term25 A B C R s) = (term25 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3808805 A B C R s a)). Qed.
Lemma lem3808807 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3808808 {A B C : Type'} (R : type1408 A B C) (s : A) : (term97 A B C R s) = (term97 A B C R s).
Proof. exact (MK_COMB (@lem3808807 B) (@lem3808806 A B C R s)). Qed.
Lemma lem3808810 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3808811 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term103 A B C P R s) = (term103 A B C P R s).
Proof. exact (MK_COMB (@lem3808810 A P s) (@lem3808808 A B C R s)). Qed.
Lemma lem3808812 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term98 A B C P R s) = (term103 A B C P R s).
Proof. exact (@lem17265 (P s) (term97 A B C R s)). Qed.
Lemma lem3808813 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term98 A B C P R s) = (term103 A B C P R s).
Proof. exact (TRANS (@lem3808812 A B C P R s) (@lem3808811 A B C P R s)). Qed.
Lemma lem3808814 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term99 A B C P R) = (term104 A B C P R).
Proof. exact (fun_ext (fun s : A => @lem3808813 A B C P R s)). Qed.
Lemma lem3808815 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808816 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term17 A B C P R) = (term105 A B C P R).
Proof. exact (MK_COMB (@lem3808815 A) (@lem3808814 A B C P R)). Qed.
Lemma lem3808875 {A : Type'} (P : Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3808876 {B : Type'} (P : Prop) (Q : B -> Prop) : (term106 B P Q) = (term107 B P Q).
Proof. exact (@lem3808875 B P Q). Qed.
Lemma lem3808877 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term108 A B C P R s) = (term109 A B C P R s).
Proof. exact (@lem3808876 B (term110 A P s) (term25 A B C R s)). Qed.
Lemma lem3808878 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term67 A B C R s a) = (term23 A B C R s a).
Proof. exact (eq_refl (term67 A B C R s a)). Qed.
Lemma lem3808879 {A B C : Type'} (R : type1408 A B C) (s : A) : (term111 A B C R s) = (term25 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3808878 A B C R s a)). Qed.
Lemma lem3808880 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3808881 {A B C : Type'} (R : type1408 A B C) (s : A) : (term112 A B C R s) = (term97 A B C R s).
Proof. exact (MK_COMB (@lem3808880 B) (@lem3808879 A B C R s)). Qed.
Lemma lem3808882 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3808883 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term108 A B C P R s) = (term103 A B C P R s).
Proof. exact (MK_COMB (@lem3808882 A P s) (@lem3808881 A B C R s)). Qed.
Lemma lem3808884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3808885 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term113 A B C P R s) = (term114 A B C P R s).
Proof. exact (MK_COMB (@lem3808884) (@lem3808883 A B C P R s)). Qed.
Lemma lem3808886 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term67 A B C R s a) = (term23 A B C R s a).
Proof. exact (eq_refl (term67 A B C R s a)). Qed.
Lemma lem3808887 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3808888 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term115 A B C P R s a) = (term116 A B C P R s a).
Proof. exact (MK_COMB (@lem3808887 A P s) (@lem3808886 A B C R s a)). Qed.
Lemma lem3808889 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term117 A B C P R s) = (term118 A B C P R s).
Proof. exact (fun_ext (fun a : B => @lem3808888 A B C P R s a)). Qed.
Lemma lem3808890 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3808891 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term109 A B C P R s) = (term119 A B C P R s).
Proof. exact (MK_COMB (@lem3808890 B) (@lem3808889 A B C P R s)). Qed.
Lemma lem3808892 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : ((term108 A B C P R s) = (term109 A B C P R s)) = ((term103 A B C P R s) = (term119 A B C P R s)).
Proof. exact (MK_COMB (@lem3808885 A B C P R s) (@lem3808891 A B C P R s)). Qed.
Lemma lem3808893 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term103 A B C P R s) = (term119 A B C P R s).
Proof. exact (EQ_MP (@lem3808892 A B C P R s) (@lem3808877 A B C P R s)). Qed.
Lemma lem3808895 {A : Type'} (P : Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3808896 {C : Type'} (P : Prop) (Q : C -> Prop) : (term106 C P Q) = (term107 C P Q).
Proof. exact (@lem3808895 C P Q). Qed.
Lemma lem3808897 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term120 A B C P R s a) = (term121 A B C P R s a).
Proof. exact (@lem3808896 C (term110 A P s) (term86 A B C R s a)). Qed.
Lemma lem3808898 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term122 A B C R s a n) = (R s a n).
Proof. exact (eq_refl (term122 A B C R s a n)). Qed.
Lemma lem3808899 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term123 A B C R s a) = (term86 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3808898 A B C R s a n)). Qed.
Lemma lem3808900 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3808901 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term124 A B C R s a) = (term23 A B C R s a).
Proof. exact (MK_COMB (@lem3808900 C) (@lem3808899 A B C R s a)). Qed.
Lemma lem3808902 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3808903 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term120 A B C P R s a) = (term116 A B C P R s a).
Proof. exact (MK_COMB (@lem3808902 A P s) (@lem3808901 A B C R s a)). Qed.
Lemma lem3808904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3808905 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term125 A B C P R s a) = (term126 A B C P R s a).
Proof. exact (MK_COMB (@lem3808904) (@lem3808903 A B C P R s a)). Qed.
Lemma lem3808906 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term122 A B C R s a n) = (R s a n).
Proof. exact (eq_refl (term122 A B C R s a n)). Qed.
Lemma lem3808907 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3808908 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) : (term127 A B C P R s a n) = (term128 A B C P R s a n).
Proof. exact (MK_COMB (@lem3808907 A P s) (@lem3808906 A B C R s a n)). Qed.
Lemma lem3808909 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term129 A B C P R s a) = (term130 A B C P R s a).
Proof. exact (fun_ext (fun n : C => @lem3808908 A B C P R s a n)). Qed.
Lemma lem3808910 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3808911 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term121 A B C P R s a) = (term131 A B C P R s a).
Proof. exact (MK_COMB (@lem3808910 C) (@lem3808909 A B C P R s a)). Qed.
Lemma lem3808912 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : ((term120 A B C P R s a) = (term121 A B C P R s a)) = ((term116 A B C P R s a) = (term131 A B C P R s a)).
Proof. exact (MK_COMB (@lem3808905 A B C P R s a) (@lem3808911 A B C P R s a)). Qed.
Lemma lem3808913 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term116 A B C P R s a) = (term131 A B C P R s a).
Proof. exact (EQ_MP (@lem3808912 A B C P R s a) (@lem3808897 A B C P R s a)). Qed.
Lemma lem3808914 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term118 A B C P R s) = (term132 A B C P R s).
Proof. exact (fun_ext (fun a : B => @lem3808913 A B C P R s a)). Qed.
Lemma lem3808915 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3808916 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term119 A B C P R s) = (term133 A B C P R s).
Proof. exact (MK_COMB (@lem3808915 B) (@lem3808914 A B C P R s)). Qed.
Lemma lem3808917 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term103 A B C P R s) = (term133 A B C P R s).
Proof. exact (TRANS (@lem3808893 A B C P R s) (@lem3808916 A B C P R s)). Qed.
Lemma lem3808918 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term104 A B C P R) = (term134 A B C P R).
Proof. exact (fun_ext (fun s : A => @lem3808917 A B C P R s)). Qed.
Lemma lem3808919 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808920 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term105 A B C P R) = (term135 A B C P R).
Proof. exact (MK_COMB (@lem3808919 A) (@lem3808918 A B C P R)). Qed.
Lemma lem3808922 {A B : Type'} (P : type1413 A B) : (term136 A B P) = (term137 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3808923 {A B : Type'} (P : type1413 A B) : (term136 A B P) = (term137 A B P).
Proof. exact (@lem3808922 A B P). Qed.
Lemma lem3808924 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term138 A B C P R) = (term139 A B C P R).
Proof. exact (@lem3808923 A B (term140 A B C P R)). Qed.
Lemma lem3808925 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term141 A B C P R s) = (term132 A B C P R s).
Proof. exact (eq_refl (term141 A B C P R s)). Qed.
Lemma lem3808926 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3808927 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term142 A B C P R s a) = (term143 A B C P R s a).
Proof. exact (MK_COMB (@lem3808925 A B C P R s) (@lem3808926 B a)). Qed.
Lemma lem3808928 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term143 A B C P R s a) = (term131 A B C P R s a).
Proof. exact (eq_refl (term143 A B C P R s a)). Qed.
Lemma lem3808929 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term142 A B C P R s a) = (term131 A B C P R s a).
Proof. exact (TRANS (@lem3808927 A B C P R s a) (@lem3808928 A B C P R s a)). Qed.
Lemma lem3808930 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term144 A B C P R s) = (term132 A B C P R s).
Proof. exact (fun_ext (fun a : B => @lem3808929 A B C P R s a)). Qed.
Lemma lem3808931 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3808932 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term145 A B C P R s) = (term133 A B C P R s).
Proof. exact (MK_COMB (@lem3808931 B) (@lem3808930 A B C P R s)). Qed.
Lemma lem3808933 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term146 A B C P R) = (term134 A B C P R).
Proof. exact (fun_ext (fun s : A => @lem3808932 A B C P R s)). Qed.
Lemma lem3808934 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808935 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term138 A B C P R) = (term135 A B C P R).
Proof. exact (MK_COMB (@lem3808934 A) (@lem3808933 A B C P R)). Qed.
Lemma lem3808936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3808937 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term147 A B C P R) = (term148 A B C P R).
Proof. exact (MK_COMB (@lem3808936) (@lem3808935 A B C P R)). Qed.
Lemma lem3808938 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term141 A B C P R s) = (term132 A B C P R s).
Proof. exact (eq_refl (term141 A B C P R s)). Qed.
Lemma lem3808939 {A B : Type'} (a : A -> B) (s : A) : (a s) = (a s).
Proof. exact (eq_refl (a s)). Qed.
Lemma lem3808940 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term149 A B C P R a s) = (term150 A B C P R a s).
Proof. exact (MK_COMB (@lem3808938 A B C P R s) (@lem3808939 A B a s)). Qed.
Lemma lem3808941 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term150 A B C P R a s) = (term151 A B C P R a s).
Proof. exact (eq_refl (term150 A B C P R a s)). Qed.
Lemma lem3808942 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term149 A B C P R a s) = (term151 A B C P R a s).
Proof. exact (TRANS (@lem3808940 A B C P R a s) (@lem3808941 A B C P R a s)). Qed.
Lemma lem3808943 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term152 A B C P R a) = (term153 A B C P R a).
Proof. exact (fun_ext (fun s : A => @lem3808942 A B C P R a s)). Qed.
Lemma lem3808944 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808945 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term154 A B C P R a) = (term155 A B C P R a).
Proof. exact (MK_COMB (@lem3808944 A) (@lem3808943 A B C P R a)). Qed.
Lemma lem3808946 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term156 A B C P R) = (term157 A B C P R).
Proof. exact (fun_ext (fun a : A -> B => @lem3808945 A B C P R a)). Qed.
Lemma lem3808947 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3808948 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term139 A B C P R) = (term158 A B C P R).
Proof. exact (MK_COMB (@lem3808947 A B) (@lem3808946 A B C P R)). Qed.
Lemma lem3808949 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : ((term138 A B C P R) = (term139 A B C P R)) = ((term135 A B C P R) = (term158 A B C P R)).
Proof. exact (MK_COMB (@lem3808937 A B C P R) (@lem3808948 A B C P R)). Qed.
Lemma lem3808950 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term135 A B C P R) = (term158 A B C P R).
Proof. exact (EQ_MP (@lem3808949 A B C P R) (@lem3808924 A B C P R)). Qed.
Lemma lem3808952 {A B : Type'} (P : type1413 A B) : (term136 A B P) = (term137 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3808953 {A C : Type'} (P : type1413 A C) : (term136 A C P) = (term137 A C P).
Proof. exact (@lem3808952 A C P). Qed.
Lemma lem3808954 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term159 A B C P R a) = (term160 A B C P R a).
Proof. exact (@lem3808953 A C (term161 A B C P R a)). Qed.
Lemma lem3808955 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term162 A B C P R a s) = (term163 A B C P R a s).
Proof. exact (eq_refl (term162 A B C P R a s)). Qed.
Lemma lem3808956 {C : Type'} (n : C) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3808957 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) (n : C) : (term164 A B C P R a s n) = (term165 A B C P R a s n).
Proof. exact (MK_COMB (@lem3808955 A B C P R a s) (@lem3808956 C n)). Qed.
Lemma lem3808958 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) (n : C) : (term165 A B C P R a s n) = (term166 A B C P R a s n).
Proof. exact (eq_refl (term165 A B C P R a s n)). Qed.
Lemma lem3808959 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) (n : C) : (term164 A B C P R a s n) = (term166 A B C P R a s n).
Proof. exact (TRANS (@lem3808957 A B C P R a s n) (@lem3808958 A B C P R a s n)). Qed.
Lemma lem3808960 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term167 A B C P R a s) = (term163 A B C P R a s).
Proof. exact (fun_ext (fun n : C => @lem3808959 A B C P R a s n)). Qed.
Lemma lem3808961 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3808962 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term168 A B C P R a s) = (term151 A B C P R a s).
Proof. exact (MK_COMB (@lem3808961 C) (@lem3808960 A B C P R a s)). Qed.
Lemma lem3808963 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term169 A B C P R a) = (term153 A B C P R a).
Proof. exact (fun_ext (fun s : A => @lem3808962 A B C P R a s)). Qed.
Lemma lem3808964 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808965 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term159 A B C P R a) = (term155 A B C P R a).
Proof. exact (MK_COMB (@lem3808964 A) (@lem3808963 A B C P R a)). Qed.
Lemma lem3808966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3808967 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term170 A B C P R a) = (term171 A B C P R a).
Proof. exact (MK_COMB (@lem3808966) (@lem3808965 A B C P R a)). Qed.
Lemma lem3808968 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term162 A B C P R a s) = (term163 A B C P R a s).
Proof. exact (eq_refl (term162 A B C P R a s)). Qed.
Lemma lem3808969 {A C : Type'} (n : A -> C) (s : A) : (n s) = (n s).
Proof. exact (eq_refl (n s)). Qed.
Lemma lem3808970 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (s : A) : (term172 A B C P R a n s) = (term173 A B C P R a n s).
Proof. exact (MK_COMB (@lem3808968 A B C P R a s) (@lem3808969 A C n s)). Qed.
Lemma lem3808971 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (s : A) : (term173 A B C P R a n s) = (term174 A B C P R a n s).
Proof. exact (eq_refl (term173 A B C P R a n s)). Qed.
Lemma lem3808972 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (s : A) : (term172 A B C P R a n s) = (term174 A B C P R a n s).
Proof. exact (TRANS (@lem3808970 A B C P R a n s) (@lem3808971 A B C P R a n s)). Qed.
Lemma lem3808973 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) : (term175 A B C P R a n) = (term176 A B C P R a n).
Proof. exact (fun_ext (fun s : A => @lem3808972 A B C P R a n s)). Qed.
Lemma lem3808974 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808975 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) : (term177 A B C P R a n) = (term178 A B C P R a n).
Proof. exact (MK_COMB (@lem3808974 A) (@lem3808973 A B C P R a n)). Qed.
Lemma lem3808976 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term179 A B C P R a) = (term180 A B C P R a).
Proof. exact (fun_ext (fun n : A -> C => @lem3808975 A B C P R a n)). Qed.
Lemma lem3808977 {A C : Type'} : (@ex (A -> C)) = (@ex (A -> C)).
Proof. exact (eq_refl (@ex (A -> C))). Qed.
Lemma lem3808978 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term160 A B C P R a) = (term181 A B C P R a).
Proof. exact (MK_COMB (@lem3808977 A C) (@lem3808976 A B C P R a)). Qed.
Lemma lem3808979 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : ((term159 A B C P R a) = (term160 A B C P R a)) = ((term155 A B C P R a) = (term181 A B C P R a)).
Proof. exact (MK_COMB (@lem3808967 A B C P R a) (@lem3808978 A B C P R a)). Qed.
Lemma lem3808980 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term155 A B C P R a) = (term181 A B C P R a).
Proof. exact (EQ_MP (@lem3808979 A B C P R a) (@lem3808954 A B C P R a)). Qed.
Lemma lem3808981 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term157 A B C P R) = (term182 A B C P R).
Proof. exact (fun_ext (fun a : A -> B => @lem3808980 A B C P R a)). Qed.
Lemma lem3808982 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3808983 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term158 A B C P R) = (term183 A B C P R).
Proof. exact (MK_COMB (@lem3808982 A B) (@lem3808981 A B C P R)). Qed.
Lemma lem3808984 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term135 A B C P R) = (term183 A B C P R).
Proof. exact (TRANS (@lem3808950 A B C P R) (@lem3808983 A B C P R)). Qed.
Lemma lem3808986 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term105 A B C P R) = (term183 A B C P R).
Proof. exact (TRANS (@lem3808920 A B C P R) (@lem3808984 A B C P R)). Qed.
Lemma lem3808987 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term17 A B C P R) = (term183 A B C P R).
Proof. exact (TRANS (@lem3808816 A B C P R) (@lem3808986 A B C P R)). Qed.
Lemma lem3808988 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term183 A B C P R.
Proof. exact (EQ_MP (@lem3808987 A B C P R) (@lem3808792 A B C P R h1)). Qed.
Lemma lem3808995 {A B C : Type'} (a1 : B) (n1 : C) (R : type1408 A B C) (s : A) (a2 : B) (n2 : C) : (term184 A B C a1 n1 R s a2 n2) = (term185 A B C a1 n1 R s a2 n2).
Proof. exact (@lem17045 (R s a1 n1) (R s a2 n2)). Qed.
Lemma lem3809000 {B C : Type'} (a1 : B) (a2 : B) (n1 : C) (n2 : C) : (term186 B C a1 a2 n1 n2) = (term186 B C a1 a2 n1 n2).
Proof. exact (eq_refl (term186 B C a1 a2 n1 n2)). Qed.
Lemma lem3809001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3809002 {A B C : Type'} (a1 : B) (n1 : C) (R : type1408 A B C) (s : A) (a2 : B) (n2 : C) : (term187 A B C a1 n1 R s a2 n2) = (term188 A B C a1 n1 R s a2 n2).
Proof. exact (MK_COMB (@lem3809001) (@lem3808995 A B C a1 n1 R s a2 n2)). Qed.
Lemma lem3809003 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (a2 : B) (n1 : C) (n2 : C) : (term189 A B C R s a1 a2 n1 n2) = (term190 A B C R s a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3809002 A B C a1 n1 R s a2 n2) (@lem3809000 B C a1 a2 n1 n2)). Qed.
Lemma lem3809004 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (a2 : B) (n1 : C) (n2 : C) : (term87 A B C R s a1 a2 n1 n2) = (term189 A B C R s a1 a2 n1 n2).
Proof. exact (@lem17265 (term191 A B C a1 n1 R s a2 n2) (term186 B C a1 a2 n1 n2)). Qed.
Lemma lem3809005 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (a2 : B) (n1 : C) (n2 : C) : (term87 A B C R s a1 a2 n1 n2) = (term190 A B C R s a1 a2 n1 n2).
Proof. exact (TRANS (@lem3809004 A B C R s a1 a2 n1 n2) (@lem3809003 A B C R s a1 a2 n1 n2)). Qed.
Lemma lem3809006 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (n1 : C) (n2 : C) : (term88 A B C R s a1 n1 n2) = (term192 A B C R s a1 n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3809005 A B C R s a1 a2 n1 n2)). Qed.
Lemma lem3809007 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3809008 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (n1 : C) (n2 : C) : (term89 A B C R s a1 n1 n2) = (term193 A B C R s a1 n1 n2).
Proof. exact (MK_COMB (@lem3809007 B) (@lem3809006 A B C R s a1 n1 n2)). Qed.
Lemma lem3809009 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term90 A B C R s n1 n2) = (term194 A B C R s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3809008 A B C R s a1 n1 n2)). Qed.
Lemma lem3809010 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3809011 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term91 A B C R s n1 n2) = (term195 A B C R s n1 n2).
Proof. exact (MK_COMB (@lem3809010 B) (@lem3809009 A B C R s n1 n2)). Qed.
Lemma lem3809012 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term92 A B C R n1 n2) = (term196 A B C R n1 n2).
Proof. exact (fun_ext (fun s : A => @lem3809011 A B C R s n1 n2)). Qed.
Lemma lem3809013 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3809014 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term93 A B C R n1 n2) = (term197 A B C R n1 n2).
Proof. exact (MK_COMB (@lem3809013 A) (@lem3809012 A B C R n1 n2)). Qed.
Lemma lem3809015 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term94 A B C R n1) = (term198 A B C R n1).
Proof. exact (fun_ext (fun n2 : C => @lem3809014 A B C R n1 n2)). Qed.
Lemma lem3809016 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3809017 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term95 A B C R n1) = (term199 A B C R n1).
Proof. exact (MK_COMB (@lem3809016 C) (@lem3809015 A B C R n1)). Qed.
Lemma lem3809018 {A B C : Type'} (R : type1408 A B C) : (term96 A B C R) = (term200 A B C R).
Proof. exact (fun_ext (fun n1 : C => @lem3809017 A B C R n1)). Qed.
Lemma lem3809019 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3809088 {A B C : Type'} (R : type1408 A B C) : (term16 A B C R) = (term201 A B C R).
Proof. exact (MK_COMB (@lem3809019 C) (@lem3809018 A B C R)). Qed.
Lemma lem3809089 {A B C : Type'} (R : type1408 A B C) (h1 : term16 A B C R) : term201 A B C R.
Proof. exact (EQ_MP (@lem3809088 A B C R) (@lem3808793 A B C R h1)). Qed.
Lemma lem3809101 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3809103 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n : C) : (R s y n) = (R s y n).
Proof. exact (eq_refl (R s y n)). Qed.
Lemma lem3809104 {C : Type'} (P : C -> Prop) : (term202 C P) = (term203 C P).
Proof. exact (@lem18394 C P). Qed.
Lemma lem3809105 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term204 A B C R s y) = (term205 A B C R s y).
Proof. exact (@lem3809104 C (term86 A B C R s y)). Qed.
Lemma lem3809106 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n : C) : (term122 A B C R s y n) = (R s y n).
Proof. exact (eq_refl (term122 A B C R s y n)). Qed.
Lemma lem3809107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3809109 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n : C) : (term206 A B C R s y n) = (term207 A B C R s y n).
Proof. exact (MK_COMB (@lem3809107) (@lem3809106 A B C R s y n)). Qed.
Lemma lem3809110 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term208 A B C R s y) = (term209 A B C R s y).
Proof. exact (fun_ext (fun n : C => @lem3809109 A B C R s y n)). Qed.
Lemma lem3809111 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3809112 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term205 A B C R s y) = (term210 A B C R s y).
Proof. exact (MK_COMB (@lem3809111 C) (@lem3809110 A B C R s y)). Qed.
Lemma lem3809113 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term204 A B C R s y) = (term210 A B C R s y).
Proof. exact (TRANS (@lem3809105 A B C R s y) (@lem3809112 A B C R s y)). Qed.
Lemma lem3809114 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term86 A B C R s y) = (term86 A B C R s y).
Proof. exact (fun_ext (fun n : C => @lem3809103 A B C R s y n)). Qed.
Lemma lem3809115 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3809116 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term23 A B C R s y) = (term23 A B C R s y).
Proof. exact (MK_COMB (@lem3809115 C) (@lem3809114 A B C R s y)). Qed.
Lemma lem3809117 {B : Type'} (y : B) (a : B) : (term211 B y a) = (term211 B y a).
Proof. exact (eq_refl (term211 B y a)). Qed.
Lemma lem3809118 {B : Type'} (y : B) (a : B) : (y = a) = (y = a).
Proof. exact (eq_refl (y = a)). Qed.
Lemma lem3809119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3809120 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term212 A B C R s y) = (term213 A B C R s y).
Proof. exact (MK_COMB (@lem3809119) (@lem3809113 A B C R s y)). Qed.
Lemma lem3809121 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term214 A B C R s y a) = (term215 A B C R s y a).
Proof. exact (MK_COMB (@lem3809120 A B C R s y) (@lem3809118 B y a)). Qed.
Lemma lem3809122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3809123 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term216 A B C R s y) = (term216 A B C R s y).
Proof. exact (MK_COMB (@lem3809122) (@lem3809116 A B C R s y)). Qed.
Lemma lem3809124 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term217 A B C R s y a) = (term217 A B C R s y a).
Proof. exact (MK_COMB (@lem3809123 A B C R s y) (@lem3809117 B y a)). Qed.
Lemma lem3809125 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3809126 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term218 A B C R s y a) = (term218 A B C R s y a).
Proof. exact (MK_COMB (@lem3809125) (@lem3809124 A B C R s y a)). Qed.
Lemma lem3809127 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term219 A B C R s y a) = (term220 A B C R s y a).
Proof. exact (MK_COMB (@lem3809126 A B C R s y a) (@lem3809121 A B C R s y a)). Qed.
Lemma lem3809128 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term101 A B C R s y a) = (term219 A B C R s y a).
Proof. exact (@lem17646 (term23 A B C R s y) (y = a)). Qed.
Lemma lem3809129 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term101 A B C R s y a) = (term220 A B C R s y a).
Proof. exact (TRANS (@lem3809128 A B C R s y a) (@lem3809127 A B C R s y a)). Qed.
Lemma lem3809140 {A : Type'} (P : A -> Prop) (Q : Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3809141 {C : Type'} (P : C -> Prop) (Q : Prop) : (term221 C P Q) = (term222 C P Q).
Proof. exact (@lem3809140 C P Q). Qed.
Lemma lem3809142 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term223 A B C R s y a) = (term224 A B C R s y a).
Proof. exact (@lem3809141 C (term86 A B C R s y) (term211 B y a)). Qed.
Lemma lem3809143 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n : C) : (term122 A B C R s y n) = (R s y n).
Proof. exact (eq_refl (term122 A B C R s y n)). Qed.
Lemma lem3809144 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term123 A B C R s y) = (term86 A B C R s y).
Proof. exact (fun_ext (fun n : C => @lem3809143 A B C R s y n)). Qed.
Lemma lem3809145 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3809146 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term124 A B C R s y) = (term23 A B C R s y).
Proof. exact (MK_COMB (@lem3809145 C) (@lem3809144 A B C R s y)). Qed.
Lemma lem3809147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3809148 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term225 A B C R s y) = (term216 A B C R s y).
Proof. exact (MK_COMB (@lem3809147) (@lem3809146 A B C R s y)). Qed.
Lemma lem3809149 {B : Type'} (y : B) (a : B) : (term211 B y a) = (term211 B y a).
Proof. exact (eq_refl (term211 B y a)). Qed.
Lemma lem3809150 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term223 A B C R s y a) = (term217 A B C R s y a).
Proof. exact (MK_COMB (@lem3809148 A B C R s y) (@lem3809149 B y a)). Qed.
Lemma lem3809151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3809152 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term226 A B C R s y a) = (term227 A B C R s y a).
Proof. exact (MK_COMB (@lem3809151) (@lem3809150 A B C R s y a)). Qed.
Lemma lem3809153 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n : C) : (term122 A B C R s y n) = (R s y n).
Proof. exact (eq_refl (term122 A B C R s y n)). Qed.
Lemma lem3809154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3809155 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n : C) : (term228 A B C R s y n) = (term229 A B C R s y n).
Proof. exact (MK_COMB (@lem3809154) (@lem3809153 A B C R s y n)). Qed.
Lemma lem3809156 {B : Type'} (y : B) (a : B) : (term211 B y a) = (term211 B y a).
Proof. exact (eq_refl (term211 B y a)). Qed.
Lemma lem3809157 {A B C : Type'} (R : type1408 A B C) (s : A) (n : C) (y : B) (a : B) : (term230 A B C R s n y a) = (term231 A B C R s n y a).
Proof. exact (MK_COMB (@lem3809155 A B C R s y n) (@lem3809156 B y a)). Qed.
Lemma lem3809158 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term232 A B C R s y a) = (term233 A B C R s y a).
Proof. exact (fun_ext (fun n : C => @lem3809157 A B C R s n y a)). Qed.
Lemma lem3809159 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3809160 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term224 A B C R s y a) = (term234 A B C R s y a).
Proof. exact (MK_COMB (@lem3809159 C) (@lem3809158 A B C R s y a)). Qed.
Lemma lem3809161 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : ((term223 A B C R s y a) = (term224 A B C R s y a)) = ((term217 A B C R s y a) = (term234 A B C R s y a)).
Proof. exact (MK_COMB (@lem3809152 A B C R s y a) (@lem3809160 A B C R s y a)). Qed.
Lemma lem3809162 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term217 A B C R s y a) = (term234 A B C R s y a).
Proof. exact (EQ_MP (@lem3809161 A B C R s y a) (@lem3809142 A B C R s y a)). Qed.
Lemma lem3809163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3809164 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term218 A B C R s y a) = (term235 A B C R s y a).
Proof. exact (MK_COMB (@lem3809163) (@lem3809162 A B C R s y a)). Qed.
Lemma lem3809165 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term215 A B C R s y a) = (term215 A B C R s y a).
Proof. exact (eq_refl (term215 A B C R s y a)). Qed.
Lemma lem3809166 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term220 A B C R s y a) = (term236 A B C R s y a).
Proof. exact (MK_COMB (@lem3809164 A B C R s y a) (@lem3809165 A B C R s y a)). Qed.
Lemma lem3809168 {A : Type'} (P : A -> Prop) (Q : Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3809169 {C : Type'} (P : C -> Prop) (Q : Prop) : (term237 C P Q) = (term238 C P Q).
Proof. exact (@lem3809168 C P Q). Qed.
Lemma lem3809170 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term239 A B C R s y a) = (term240 A B C R s y a).
Proof. exact (@lem3809169 C (term233 A B C R s y a) (term215 A B C R s y a)). Qed.
Lemma lem3809171 {A B C : Type'} (R : type1408 A B C) (s : A) (n : C) (y : B) (a : B) : (term241 A B C R s y a n) = (term231 A B C R s n y a).
Proof. exact (eq_refl (term241 A B C R s y a n)). Qed.
Lemma lem3809172 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term242 A B C R s y a) = (term233 A B C R s y a).
Proof. exact (fun_ext (fun n : C => @lem3809171 A B C R s n y a)). Qed.
Lemma lem3809173 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3809174 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term243 A B C R s y a) = (term234 A B C R s y a).
Proof. exact (MK_COMB (@lem3809173 C) (@lem3809172 A B C R s y a)). Qed.
Lemma lem3809175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3809176 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term244 A B C R s y a) = (term235 A B C R s y a).
Proof. exact (MK_COMB (@lem3809175) (@lem3809174 A B C R s y a)). Qed.
Lemma lem3809177 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term215 A B C R s y a) = (term215 A B C R s y a).
Proof. exact (eq_refl (term215 A B C R s y a)). Qed.
Lemma lem3809178 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term239 A B C R s y a) = (term236 A B C R s y a).
Proof. exact (MK_COMB (@lem3809176 A B C R s y a) (@lem3809177 A B C R s y a)). Qed.
Lemma lem3809179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3809180 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term245 A B C R s y a) = (term246 A B C R s y a).
Proof. exact (MK_COMB (@lem3809179) (@lem3809178 A B C R s y a)). Qed.
Lemma lem3809181 {A B C : Type'} (R : type1408 A B C) (s : A) (n : C) (y : B) (a : B) : (term241 A B C R s y a n) = (term231 A B C R s n y a).
Proof. exact (eq_refl (term241 A B C R s y a n)). Qed.
Lemma lem3809182 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3809183 {A B C : Type'} (R : type1408 A B C) (s : A) (n : C) (y : B) (a : B) : (term247 A B C R s y a n) = (term248 A B C R s n y a).
Proof. exact (MK_COMB (@lem3809182) (@lem3809181 A B C R s n y a)). Qed.
Lemma lem3809184 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term215 A B C R s y a) = (term215 A B C R s y a).
Proof. exact (eq_refl (term215 A B C R s y a)). Qed.
Lemma lem3809185 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (y : B) (a : B) : (term249 A B C n R s y a) = (term250 A B C n R s y a).
Proof. exact (MK_COMB (@lem3809183 A B C R s n y a) (@lem3809184 A B C R s y a)). Qed.
Lemma lem3809186 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term251 A B C R s y a) = (term252 A B C R s y a).
Proof. exact (fun_ext (fun n : C => @lem3809185 A B C n R s y a)). Qed.
Lemma lem3809187 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3809188 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term240 A B C R s y a) = (term253 A B C R s y a).
Proof. exact (MK_COMB (@lem3809187 C) (@lem3809186 A B C R s y a)). Qed.
Lemma lem3809189 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : ((term239 A B C R s y a) = (term240 A B C R s y a)) = ((term236 A B C R s y a) = (term253 A B C R s y a)).
Proof. exact (MK_COMB (@lem3809180 A B C R s y a) (@lem3809188 A B C R s y a)). Qed.
Lemma lem3809190 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term236 A B C R s y a) = (term253 A B C R s y a).
Proof. exact (EQ_MP (@lem3809189 A B C R s y a) (@lem3809170 A B C R s y a)). Qed.
Lemma lem3809192 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term220 A B C R s y a) = (term253 A B C R s y a).
Proof. exact (TRANS (@lem3809166 A B C R s y a) (@lem3809190 A B C R s y a)). Qed.
Lemma lem3809193 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term101 A B C R s y a) = (term253 A B C R s y a).
Proof. exact (TRANS (@lem3809129 A B C R s y a) (@lem3809192 A B C R s y a)). Qed.
Lemma lem3809194 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term101 A B C R s y a) : term253 A B C R s y a.
Proof. exact (EQ_MP (@lem3809193 A B C R s y a) (@lem3808800 A B C R s y a h1)). Qed.
Lemma lem3809195 {A B C : Type'} (n' : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term250 A B C n' R s y a) : term250 A B C n' R s y a.
Proof. exact (h1). Qed.
Lemma lem3809196 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a' : A -> B) (h1 : term181 A B C P R a') : term181 A B C P R a'.
Proof. exact (h1). Qed.
Lemma lem3809234 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (a2 : B) (n1 : C) (n2 : C) : (term190 A B C R s a1 a2 n1 n2) = (term190 A B C R s a1 a2 n1 n2).
Proof. exact (eq_refl (term190 A B C R s a1 a2 n1 n2)). Qed.
Lemma lem3809235 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (n1 : C) (n2 : C) : (term192 A B C R s a1 n1 n2) = (term192 A B C R s a1 n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3809234 A B C R s a1 a2 n1 n2)). Qed.
Lemma lem3809236 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3809237 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (n1 : C) (n2 : C) : (term193 A B C R s a1 n1 n2) = (term193 A B C R s a1 n1 n2).
Proof. exact (MK_COMB (@lem3809236 B) (@lem3809235 A B C R s a1 n1 n2)). Qed.
Lemma lem3809238 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term194 A B C R s n1 n2) = (term194 A B C R s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3809237 A B C R s a1 n1 n2)). Qed.
Lemma lem3809239 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3809240 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term195 A B C R s n1 n2) = (term195 A B C R s n1 n2).
Proof. exact (MK_COMB (@lem3809239 B) (@lem3809238 A B C R s n1 n2)). Qed.
Lemma lem3809241 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term196 A B C R n1 n2) = (term196 A B C R n1 n2).
Proof. exact (fun_ext (fun s : A => @lem3809240 A B C R s n1 n2)). Qed.
Lemma lem3809242 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3809243 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term197 A B C R n1 n2) = (term197 A B C R n1 n2).
Proof. exact (MK_COMB (@lem3809242 A) (@lem3809241 A B C R n1 n2)). Qed.
Lemma lem3809244 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term198 A B C R n1) = (term198 A B C R n1).
Proof. exact (fun_ext (fun n2 : C => @lem3809243 A B C R n1 n2)). Qed.
Lemma lem3809245 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3809246 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term199 A B C R n1) = (term199 A B C R n1).
Proof. exact (MK_COMB (@lem3809245 C) (@lem3809244 A B C R n1)). Qed.
Lemma lem3809247 {A B C : Type'} (R : type1408 A B C) : (term200 A B C R) = (term200 A B C R).
Proof. exact (fun_ext (fun n1 : C => @lem3809246 A B C R n1)). Qed.
Lemma lem3809248 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3809249 {A B C : Type'} (R : type1408 A B C) : (term201 A B C R) = (term201 A B C R).
Proof. exact (MK_COMB (@lem3809248 C) (@lem3809247 A B C R)). Qed.
Lemma lem3809250 {A B C : Type'} (R : type1408 A B C) (h1 : term16 A B C R) : term201 A B C R.
Proof. exact (EQ_MP (@lem3809249 A B C R) (@lem3809089 A B C R h1)). Qed.
Lemma lem3809262 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3809267 {B : Type'} (y : B) (a : B) : (y = a) = (y = a).
Proof. exact (eq_refl (y = a)). Qed.
Lemma lem3809276 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n : C) : (term207 A B C R s y n) = (term207 A B C R s y n).
Proof. exact (eq_refl (term207 A B C R s y n)). Qed.
Lemma lem3809277 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term209 A B C R s y) = (term209 A B C R s y).
Proof. exact (fun_ext (fun n : C => @lem3809276 A B C R s y n)). Qed.
Lemma lem3809278 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3809279 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term210 A B C R s y) = (term210 A B C R s y).
Proof. exact (MK_COMB (@lem3809278 C) (@lem3809277 A B C R s y)). Qed.
Lemma lem3809280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3809281 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term213 A B C R s y) = (term213 A B C R s y).
Proof. exact (MK_COMB (@lem3809280) (@lem3809279 A B C R s y)). Qed.
Lemma lem3809282 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) : (term215 A B C R s y a) = (term215 A B C R s y a).
Proof. exact (MK_COMB (@lem3809281 A B C R s y) (@lem3809267 B y a)). Qed.
Lemma lem3809301 {A B C : Type'} (R : type1408 A B C) (s : A) (n' : C) (y : B) (a : B) : (term248 A B C R s n' y a) = (term248 A B C R s n' y a).
Proof. exact (eq_refl (term248 A B C R s n' y a)). Qed.
Lemma lem3809302 {A B C : Type'} (n' : C) (R : type1408 A B C) (s : A) (y : B) (a : B) : (term250 A B C n' R s y a) = (term250 A B C n' R s y a).
Proof. exact (MK_COMB (@lem3809301 A B C R s n' y a) (@lem3809282 A B C R s y a)). Qed.
Lemma lem3809303 {A B C : Type'} (n' : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term250 A B C n' R s y a) : term250 A B C n' R s y a.
Proof. exact (EQ_MP (@lem3809302 A B C n' R s y a) (@lem3809195 A B C n' R s y a h1)). Qed.
Lemma lem3809327 {A B C : Type'} (R : type1408 A B C) (s : A) (n' : C) (y : B) (a : B) (h1 : term231 A B C R s n' y a) : term231 A B C R s n' y a.
Proof. exact (h1). Qed.
Lemma lem3809328 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : term215 A B C R s y a.
Proof. exact (h1). Qed.
Lemma lem3809332 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : term210 A B C R s y.
Proof. exact (proj1 (@lem3809328 A B C R s y a h1)). Qed.
Lemma lem3809356 {A B C : Type'} (a1 : B) (R : type1408 A B C) (s : A) (a2 : B) (n1 : C) (n2 : C) : (term190 A B C R s a1 a2 n1 n2) = (term254 A B C a1 R s a2 n1 n2).
Proof. exact (@lem19490 (a1 = a2) (term185 A B C a1 n1 R s a2 n2) (n1 = n2)). Qed.
Lemma lem3809357 {A B C : Type'} (a1 : B) (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term192 A B C R s a1 n1 n2) = (term255 A B C a1 R s n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3809356 A B C a1 R s a2 n1 n2)). Qed.
Lemma lem3809358 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3809359 {A B C : Type'} (a1 : B) (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term193 A B C R s a1 n1 n2) = (term256 A B C a1 R s n1 n2).
Proof. exact (MK_COMB (@lem3809358 B) (@lem3809357 A B C a1 R s n1 n2)). Qed.
Lemma lem3809360 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term194 A B C R s n1 n2) = (term257 A B C R s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3809359 A B C a1 R s n1 n2)). Qed.
Lemma lem3809361 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3809362 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term195 A B C R s n1 n2) = (term258 A B C R s n1 n2).
Proof. exact (MK_COMB (@lem3809361 B) (@lem3809360 A B C R s n1 n2)). Qed.
Lemma lem3809363 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term196 A B C R n1 n2) = (term259 A B C R n1 n2).
Proof. exact (fun_ext (fun s : A => @lem3809362 A B C R s n1 n2)). Qed.
Lemma lem3809364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3809365 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term197 A B C R n1 n2) = (term260 A B C R n1 n2).
Proof. exact (MK_COMB (@lem3809364 A) (@lem3809363 A B C R n1 n2)). Qed.
Lemma lem3809366 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term198 A B C R n1) = (term261 A B C R n1).
Proof. exact (fun_ext (fun n2 : C => @lem3809365 A B C R n1 n2)). Qed.
Lemma lem3809367 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3809368 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term199 A B C R n1) = (term262 A B C R n1).
Proof. exact (MK_COMB (@lem3809367 C) (@lem3809366 A B C R n1)). Qed.
Lemma lem3809369 {A B C : Type'} (R : type1408 A B C) : (term200 A B C R) = (term263 A B C R).
Proof. exact (fun_ext (fun n1 : C => @lem3809368 A B C R n1)). Qed.
Lemma lem3809370 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3809372 {A B C : Type'} (R : type1408 A B C) : (term201 A B C R) = (term264 A B C R).
Proof. exact (MK_COMB (@lem3809370 C) (@lem3809369 A B C R)). Qed.
Lemma lem3809373 {A B C : Type'} (R : type1408 A B C) (h1 : term16 A B C R) : term264 A B C R.
Proof. exact (EQ_MP (@lem3809372 A B C R) (@lem3809250 A B C R h1)). Qed.
Lemma lem3809381 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3809451 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3809466 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n : C) : (term207 A B C R s y n) = (term207 A B C R s y n).
Proof. exact (eq_refl (term207 A B C R s y n)). Qed.
Lemma lem3809467 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term209 A B C R s y) = (term209 A B C R s y).
Proof. exact (fun_ext (fun n : C => @lem3809466 A B C R s y n)). Qed.
Lemma lem3809468 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3809470 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) : (term210 A B C R s y) = (term210 A B C R s y).
Proof. exact (MK_COMB (@lem3809468 C) (@lem3809467 A B C R s y)). Qed.
Lemma lem3809471 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : term210 A B C R s y.
Proof. exact (EQ_MP (@lem3809470 A B C R s y) (@lem3809332 A B C R s y a h1)). Qed.
Lemma lem3809476 {A B C : Type'} (_44189 : C) (R : type1408 A B C) (h1 : term16 A B C R) : term265 A B C R _44189.
Proof. exact (@lem3809373 A B C R h1 _44189). Qed.
Lemma lem3809477 {A B C : Type'} (R : type1408 A B C) (_44189 : C) : (term265 A B C R _44189) = (term262 A B C R _44189).
Proof. exact (eq_refl (term265 A B C R _44189)). Qed.
Lemma lem3809478 {A B C : Type'} (_44189 : C) (R : type1408 A B C) (h1 : term16 A B C R) : term262 A B C R _44189.
Proof. exact (EQ_MP (@lem3809477 A B C R _44189) (@lem3809476 A B C _44189 R h1)). Qed.
Lemma lem3809479 {A B C : Type'} (_44189 : C) (_44190 : C) (R : type1408 A B C) (h1 : term16 A B C R) : term266 A B C R _44189 _44190.
Proof. exact (@lem3809478 A B C _44189 R h1 _44190). Qed.
Lemma lem3809480 {A B C : Type'} (R : type1408 A B C) (_44189 : C) (_44190 : C) : (term266 A B C R _44189 _44190) = (term260 A B C R _44189 _44190).
Proof. exact (eq_refl (term266 A B C R _44189 _44190)). Qed.
Lemma lem3809481 {A B C : Type'} (_44189 : C) (_44190 : C) (R : type1408 A B C) (h1 : term16 A B C R) : term260 A B C R _44189 _44190.
Proof. exact (EQ_MP (@lem3809480 A B C R _44189 _44190) (@lem3809479 A B C _44189 _44190 R h1)). Qed.
Lemma lem3809482 {A B C : Type'} (_44189 : C) (_44190 : C) (_44191 : A) (R : type1408 A B C) (h1 : term16 A B C R) : term267 A B C R _44189 _44190 _44191.
Proof. exact (@lem3809481 A B C _44189 _44190 R h1 _44191). Qed.
Lemma lem3809483 {A B C : Type'} (R : type1408 A B C) (_44191 : A) (_44189 : C) (_44190 : C) : (term267 A B C R _44189 _44190 _44191) = (term258 A B C R _44191 _44189 _44190).
Proof. exact (eq_refl (term267 A B C R _44189 _44190 _44191)). Qed.
Lemma lem3809484 {A B C : Type'} (_44191 : A) (_44189 : C) (_44190 : C) (R : type1408 A B C) (h1 : term16 A B C R) : term258 A B C R _44191 _44189 _44190.
Proof. exact (EQ_MP (@lem3809483 A B C R _44191 _44189 _44190) (@lem3809482 A B C _44189 _44190 _44191 R h1)). Qed.
Lemma lem3809485 {A B C : Type'} (_44191 : A) (_44189 : C) (_44190 : C) (_44192 : B) (R : type1408 A B C) (h1 : term16 A B C R) : term268 A B C R _44191 _44189 _44190 _44192.
Proof. exact (@lem3809484 A B C _44191 _44189 _44190 R h1 _44192). Qed.
Lemma lem3809486 {A B C : Type'} (_44192 : B) (R : type1408 A B C) (_44191 : A) (_44189 : C) (_44190 : C) : (term268 A B C R _44191 _44189 _44190 _44192) = (term256 A B C _44192 R _44191 _44189 _44190).
Proof. exact (eq_refl (term268 A B C R _44191 _44189 _44190 _44192)). Qed.
Lemma lem3809487 {A B C : Type'} (_44192 : B) (_44191 : A) (_44189 : C) (_44190 : C) (R : type1408 A B C) (h1 : term16 A B C R) : term256 A B C _44192 R _44191 _44189 _44190.
Proof. exact (EQ_MP (@lem3809486 A B C _44192 R _44191 _44189 _44190) (@lem3809485 A B C _44191 _44189 _44190 _44192 R h1)). Qed.
Lemma lem3809488 {A B C : Type'} (_44192 : B) (_44191 : A) (_44189 : C) (_44190 : C) (_44193 : B) (R : type1408 A B C) (h1 : term16 A B C R) : term269 A B C _44192 R _44191 _44189 _44190 _44193.
Proof. exact (@lem3809487 A B C _44192 _44191 _44189 _44190 R h1 _44193). Qed.
Lemma lem3809489 {A B C : Type'} (_44192 : B) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44189 : C) (_44190 : C) : (term269 A B C _44192 R _44191 _44189 _44190 _44193) = (term254 A B C _44192 R _44191 _44193 _44189 _44190).
Proof. exact (eq_refl (term269 A B C _44192 R _44191 _44189 _44190 _44193)). Qed.
Lemma lem3809490 {A B C : Type'} (_44192 : B) (_44191 : A) (_44193 : B) (_44189 : C) (_44190 : C) (R : type1408 A B C) (h1 : term16 A B C R) : term254 A B C _44192 R _44191 _44193 _44189 _44190.
Proof. exact (EQ_MP (@lem3809489 A B C _44192 R _44191 _44193 _44189 _44190) (@lem3809488 A B C _44192 _44191 _44189 _44190 _44193 R h1)). Qed.
Lemma lem3809512 {A B C : Type'} (_44201 : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : term270 A B C R s y _44201.
Proof. exact (@lem3809471 A B C R s y a h1 _44201). Qed.
Lemma lem3809513 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (_44201 : C) : (term270 A B C R s y _44201) = (term207 A B C R s y _44201).
Proof. exact (eq_refl (term270 A B C R s y _44201)). Qed.
Lemma lem3809516 {A B C : Type'} (_44189 : C) (_44191 : A) (_44190 : C) (_44192 : B) (_44193 : B) (R : type1408 A B C) (h1 : term16 A B C R) : term271 A B C _44189 R _44191 _44190 _44192 _44193.
Proof. exact (proj1 (@lem3809490 A B C _44192 _44191 _44193 _44189 _44190 R h1)). Qed.
Lemma lem3809522 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3809532 {A B C : Type'} (R : type1408 A B C) (s : A) (n' : C) (y : B) (a : B) (h1 : term231 A B C R s n' y a) : term211 B y a.
Proof. exact (proj2 (@lem3809327 A B C R s n' y a h1)). Qed.
Lemma lem3809543 {A B C : Type'} (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44190 : C) (_44192 : B) (_44193 : B) : (term271 A B C _44189 R _44191 _44190 _44192 _44193) = (term272 A B C _44189 R _44191 _44190 _44192 _44193).
Proof. exact (@lem3808369 (term207 A B C R _44191 _44192 _44189) (term207 A B C R _44191 _44193 _44190) (_44192 = _44193)). Qed.
Lemma lem3809544 {A B C : Type'} (_44189 : C) (_44191 : A) (_44190 : C) (_44192 : B) (_44193 : B) (R : type1408 A B C) (h1 : term16 A B C R) : term272 A B C _44189 R _44191 _44190 _44192 _44193.
Proof. exact (EQ_MP (@lem3809543 A B C _44189 R _44191 _44190 _44192 _44193) (@lem3809516 A B C _44189 _44191 _44190 _44192 _44193 R h1)). Qed.
Lemma lem3809560 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3809568 {A B C : Type'} (_44201 : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : term207 A B C R s y _44201.
Proof. exact (EQ_MP (@lem3809513 A B C R s y _44201) (@lem3809512 A B C _44201 R s y a h1)). Qed.
Lemma lem3809570 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : y = a.
Proof. exact (proj2 (@lem3809328 A B C R s y a h1)). Qed.
Lemma lem3809636 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3809651 {A B C : Type'} (R : type1408 A B C) (s : A) (_44201 : C) : (term273 A B C R s _44201) = (term273 A B C R s _44201).
Proof. exact (eq_refl (term273 A B C R s _44201)). Qed.
Lemma lem3809652 {A B C : Type'} (_44201 : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : (term274 A B C R s _44201 y) = (term274 A B C R s _44201 a).
Proof. exact (MK_COMB (@lem3809651 A B C R s _44201) (@lem3809570 A B C R s y a h1)). Qed.
Lemma lem3809653 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (_44201 : C) : (term274 A B C R s _44201 a) = (term207 A B C R s a _44201).
Proof. exact (eq_refl (term274 A B C R s _44201 a)). Qed.
Lemma lem3809654 {A B C : Type'} (R : type1408 A B C) (s : A) (_44201 : C) (y : B) : (term275 A B C R s _44201 y) = (term275 A B C R s _44201 y).
Proof. exact (eq_refl (term275 A B C R s _44201 y)). Qed.
Lemma lem3809655 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (_44201 : C) : ((term274 A B C R s _44201 y) = (term274 A B C R s _44201 a)) = ((term274 A B C R s _44201 y) = (term207 A B C R s a _44201)).
Proof. exact (MK_COMB (@lem3809654 A B C R s _44201 y) (@lem3809653 A B C R s a _44201)). Qed.
Lemma lem3809656 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (_44201 : C) : (term274 A B C R s _44201 y) = (term207 A B C R s y _44201).
Proof. exact (eq_refl (term274 A B C R s _44201 y)). Qed.
Lemma lem3809657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3809658 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (_44201 : C) : (term275 A B C R s _44201 y) = (term276 A B C R s y _44201).
Proof. exact (MK_COMB (@lem3809657) (@lem3809656 A B C R s y _44201)). Qed.
Lemma lem3809659 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (_44201 : C) : (term207 A B C R s a _44201) = (term207 A B C R s a _44201).
Proof. exact (eq_refl (term207 A B C R s a _44201)). Qed.
Lemma lem3809660 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (_44201 : C) : ((term274 A B C R s _44201 y) = (term207 A B C R s a _44201)) = ((term207 A B C R s y _44201) = (term207 A B C R s a _44201)).
Proof. exact (MK_COMB (@lem3809658 A B C R s y _44201) (@lem3809659 A B C R s a _44201)). Qed.
Lemma lem3809661 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (_44201 : C) : ((term274 A B C R s _44201 y) = (term274 A B C R s _44201 a)) = ((term207 A B C R s y _44201) = (term207 A B C R s a _44201)).
Proof. exact (TRANS (@lem3809655 A B C y R s a _44201) (@lem3809660 A B C y R s a _44201)). Qed.
Lemma lem3809662 {A B C : Type'} (_44201 : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : (term207 A B C R s y _44201) = (term207 A B C R s a _44201).
Proof. exact (EQ_MP (@lem3809661 A B C y R s a _44201) (@lem3809652 A B C _44201 R s y a h1)). Qed.
Lemma lem3809663 {A B C : Type'} (_44201 : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : term207 A B C R s a _44201.
Proof. exact (EQ_MP (@lem3809662 A B C _44201 R s y a h1) (@lem3809568 A B C _44201 R s y a h1)). Qed.
Lemma lem3809753 {A B C : Type'} (R : type1408 A B C) (s : A) (n' : C) (y : B) (a : B) (h1 : term231 A B C R s n' y a) : R s y n'.
Proof. exact (proj1 (@lem3809327 A B C R s n' y a h1)). Qed.
Lemma lem3809754 {A B C : Type'} (R : type1408 A B C) (s : A) (n' : C) (y : B) (a : B) (h1 : term231 A B C R s n' y a) : term277 A B C R s y n'.
Proof. exact (fun h0 : term207 A B C R s y n' => @lem3809753 A B C R s n' y a h1). Qed.
Lemma lem3809756 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3809757 {A B C : Type'} (R : type1408 A B C) (s : A) (y : B) (n' : C) : (term277 A B C R s y n') = (R s y n').
Proof. exact (@lem3809756 (R s y n')). Qed.
Lemma lem3809758 {A B C : Type'} (R : type1408 A B C) (s : A) (n' : C) (y : B) (a : B) (h1 : term231 A B C R s n' y a) : R s y n'.
Proof. exact (EQ_MP (@lem3809757 A B C R s y n') (@lem3809754 A B C R s n' y a h1)). Qed.
Lemma lem3809760 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3809761 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : term277 A B C R s a n.
Proof. exact (fun h0 : term207 A B C R s a n => @lem3809760 A B C R s a n h1). Qed.
Lemma lem3809763 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3809764 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term277 A B C R s a n) = (R s a n).
Proof. exact (@lem3809763 (R s a n)). Qed.
Lemma lem3809765 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (EQ_MP (@lem3809764 A B C R s a n) (@lem3809761 A B C R s a n h1)). Qed.
Lemma lem3809781 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3809782 {A B C : Type'} (_44192 : B) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term279 A B C R _44191 _44190 _44192 _44193) = (term280 A B C _44192 R _44191 _44193 _44190).
Proof. exact (@lem3809781 (_44192 = _44193) (term207 A B C R _44191 _44193 _44190)). Qed.
Lemma lem3809790 {A B C : Type'} (R : type1408 A B C) (_44191 : A) (_44192 : B) (_44189 : C) : (term281 A B C R _44191 _44192 _44189) = (term281 A B C R _44191 _44192 _44189).
Proof. exact (eq_refl (term281 A B C R _44191 _44192 _44189)). Qed.
Lemma lem3809791 {A B C : Type'} (_44189 : C) (_44192 : B) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term272 A B C _44189 R _44191 _44190 _44192 _44193) = (term282 A B C _44189 _44192 R _44191 _44193 _44190).
Proof. exact (MK_COMB (@lem3809790 A B C R _44191 _44192 _44189) (@lem3809782 A B C _44192 R _44191 _44193 _44190)). Qed.
Lemma lem3809795 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3809796 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term282 A B C _44189 _44192 R _44191 _44193 _44190) = (term283 A B C _44192 _44189 R _44191 _44193 _44190).
Proof. exact (@lem3809795 (_44192 = _44193) (term207 A B C R _44191 _44192 _44189) (term207 A B C R _44191 _44193 _44190)). Qed.
Lemma lem3809814 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term272 A B C _44189 R _44191 _44190 _44192 _44193) = (term283 A B C _44192 _44189 R _44191 _44193 _44190).
Proof. exact (TRANS (@lem3809791 A B C _44189 _44192 R _44191 _44193 _44190) (@lem3809796 A B C _44192 _44189 R _44191 _44193 _44190)). Qed.
Lemma lem3809815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3809816 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term284 A B C _44189 R _44191 _44190 _44192 _44193) = (term285 A B C _44192 _44189 R _44191 _44193 _44190).
Proof. exact (MK_COMB (@lem3809815) (@lem3809814 A B C _44192 _44189 R _44191 _44193 _44190)). Qed.
Lemma lem3809834 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term283 A B C _44192 _44189 R _44191 _44193 _44190) = (term283 A B C _44192 _44189 R _44191 _44193 _44190).
Proof. exact (eq_refl (term283 A B C _44192 _44189 R _44191 _44193 _44190)). Qed.
Lemma lem3809835 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : ((term272 A B C _44189 R _44191 _44190 _44192 _44193) = (term283 A B C _44192 _44189 R _44191 _44193 _44190)) = ((term283 A B C _44192 _44189 R _44191 _44193 _44190) = (term283 A B C _44192 _44189 R _44191 _44193 _44190)).
Proof. exact (MK_COMB (@lem3809816 A B C _44192 _44189 R _44191 _44193 _44190) (@lem3809834 A B C _44192 _44189 R _44191 _44193 _44190)). Qed.
Lemma lem3809837 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3809838 (x : Prop) : (x = x) = True.
Proof. exact (@lem3809837 Prop x). Qed.
Lemma lem3809839 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : ((term283 A B C _44192 _44189 R _44191 _44193 _44190) = (term283 A B C _44192 _44189 R _44191 _44193 _44190)) = True.
Proof. exact (@lem3809838 (term283 A B C _44192 _44189 R _44191 _44193 _44190)). Qed.
Lemma lem3809840 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : ((term272 A B C _44189 R _44191 _44190 _44192 _44193) = (term283 A B C _44192 _44189 R _44191 _44193 _44190)) = True.
Proof. exact (TRANS (@lem3809835 A B C _44192 _44189 R _44191 _44193 _44190) (@lem3809839 A B C _44192 _44189 R _44191 _44193 _44190)). Qed.
Lemma lem3809841 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : True = ((term272 A B C _44189 R _44191 _44190 _44192 _44193) = (term283 A B C _44192 _44189 R _44191 _44193 _44190)).
Proof. exact (SYM (@lem3809840 A B C _44192 _44189 R _44191 _44193 _44190)). Qed.
Lemma lem3809842 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term272 A B C _44189 R _44191 _44190 _44192 _44193) = (term283 A B C _44192 _44189 R _44191 _44193 _44190).
Proof. exact (EQ_MP (@lem3809841 A B C _44192 _44189 R _44191 _44193 _44190) (@lem0)). Qed.
Lemma lem3809843 {A B C : Type'} (_44192 : B) (_44189 : C) (_44191 : A) (_44193 : B) (_44190 : C) (R : type1408 A B C) (h1 : term16 A B C R) : term283 A B C _44192 _44189 R _44191 _44193 _44190.
Proof. exact (EQ_MP (@lem3809842 A B C _44192 _44189 R _44191 _44193 _44190) (@lem3809544 A B C _44189 _44191 _44190 _44192 _44193 R h1)). Qed.
Lemma lem3809845 (b : Prop) (a : Prop) : (a \/ b) = (term286 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3809846 {A B C : Type'} (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44190 : C) (_44192 : B) (_44193 : B) : (term283 A B C _44192 _44189 R _44191 _44193 _44190) = (term287 A B C _44189 R _44191 _44190 _44192 _44193).
Proof. exact (@lem3809845 (term185 A B C _44192 _44189 R _44191 _44193 _44190) (_44192 = _44193)). Qed.
Lemma lem3809848 (a : Prop) (b : Prop) : (term288 a b) = (term289 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3809849 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term290 A B C _44192 _44189 R _44191 _44193 _44190) = (term291 A B C _44192 _44189 R _44191 _44193 _44190).
Proof. exact (@lem3809848 (term207 A B C R _44191 _44192 _44189) (term207 A B C R _44191 _44193 _44190)). Qed.
Lemma lem3809851 (a : Prop) : (term35 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3809852 {A B C : Type'} (R : type1408 A B C) (_44191 : A) (_44192 : B) (_44189 : C) : (term292 A B C R _44191 _44192 _44189) = (R _44191 _44192 _44189).
Proof. exact (@lem3809851 (R _44191 _44192 _44189)). Qed.
Lemma lem3809853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3809854 {A B C : Type'} (R : type1408 A B C) (_44191 : A) (_44192 : B) (_44189 : C) : (term293 A B C R _44191 _44192 _44189) = (term229 A B C R _44191 _44192 _44189).
Proof. exact (MK_COMB (@lem3809853) (@lem3809852 A B C R _44191 _44192 _44189)). Qed.
Lemma lem3809856 (a : Prop) : (term35 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3809857 {A B C : Type'} (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term292 A B C R _44191 _44193 _44190) = (R _44191 _44193 _44190).
Proof. exact (@lem3809856 (R _44191 _44193 _44190)). Qed.
Lemma lem3809858 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term291 A B C _44192 _44189 R _44191 _44193 _44190) = (term191 A B C _44192 _44189 R _44191 _44193 _44190).
Proof. exact (MK_COMB (@lem3809854 A B C R _44191 _44192 _44189) (@lem3809857 A B C R _44191 _44193 _44190)). Qed.
Lemma lem3809859 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term290 A B C _44192 _44189 R _44191 _44193 _44190) = (term191 A B C _44192 _44189 R _44191 _44193 _44190).
Proof. exact (TRANS (@lem3809849 A B C _44192 _44189 R _44191 _44193 _44190) (@lem3809858 A B C _44192 _44189 R _44191 _44193 _44190)). Qed.
Lemma lem3809860 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3809861 {A B C : Type'} (_44192 : B) (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44193 : B) (_44190 : C) : (term294 A B C _44192 _44189 R _44191 _44193 _44190) = (term295 A B C _44192 _44189 R _44191 _44193 _44190).
Proof. exact (MK_COMB (@lem3809860) (@lem3809859 A B C _44192 _44189 R _44191 _44193 _44190)). Qed.
Lemma lem3809862 {B : Type'} (_44192 : B) (_44193 : B) : (_44192 = _44193) = (_44192 = _44193).
Proof. exact (eq_refl (_44192 = _44193)). Qed.
Lemma lem3809863 {A B C : Type'} (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44190 : C) (_44192 : B) (_44193 : B) : (term287 A B C _44189 R _44191 _44190 _44192 _44193) = (term296 A B C _44189 R _44191 _44190 _44192 _44193).
Proof. exact (MK_COMB (@lem3809861 A B C _44192 _44189 R _44191 _44193 _44190) (@lem3809862 B _44192 _44193)). Qed.
Lemma lem3809864 {A B C : Type'} (_44189 : C) (R : type1408 A B C) (_44191 : A) (_44190 : C) (_44192 : B) (_44193 : B) : (term283 A B C _44192 _44189 R _44191 _44193 _44190) = (term296 A B C _44189 R _44191 _44190 _44192 _44193).
Proof. exact (TRANS (@lem3809846 A B C _44189 R _44191 _44190 _44192 _44193) (@lem3809863 A B C _44189 R _44191 _44190 _44192 _44193)). Qed.
Lemma lem3809866 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term231 A B C R s n' y a) (h2 : R s a n) : term191 A B C y n' R s a n.
Proof. exact (conj (@lem3809758 A B C R s n' y a h1) (@lem3809765 A B C R s a n h2)). Qed.
Lemma lem3809868 {A B C : Type'} (_44189 : C) (_44191 : A) (_44190 : C) (_44192 : B) (_44193 : B) (R : type1408 A B C) (h1 : term16 A B C R) : term296 A B C _44189 R _44191 _44190 _44192 _44193.
Proof. exact (EQ_MP (@lem3809864 A B C _44189 R _44191 _44190 _44192 _44193) (@lem3809843 A B C _44192 _44189 _44191 _44193 _44190 R h1)). Qed.
Lemma lem3809869 {A B C : Type'} (_44189 : C) (_44191 : A) (_44190 : C) (_44192 : B) (_44193 : B) (R : type1408 A B C) (h1 : term16 A B C R) : term296 A B C _44189 R _44191 _44190 _44192 _44193.
Proof. exact (@lem3809868 A B C _44189 _44191 _44190 _44192 _44193 R h1). Qed.
Lemma lem3809870 {A B C : Type'} (n' : C) (s : A) (n : C) (y : B) (a : B) (R : type1408 A B C) (h1 : term16 A B C R) : term296 A B C n' R s n y a.
Proof. exact (@lem3809869 A B C n' s n y a R h1). Qed.
Lemma lem3809873 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : y = a.
Proof. exact (@lem3809870 A B C n' s n y a R h1 (@lem3809866 A B C n' y R s a n h2 h3)). Qed.
Lemma lem3809874 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : term297 B y a.
Proof. exact (fun h0 : term211 B y a => @lem3809873 A B C n' y R s a n h1 h2 h3). Qed.
Lemma lem3809876 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3809877 {B : Type'} (y : B) (a : B) : (term297 B y a) = (y = a).
Proof. exact (@lem3809876 (y = a)). Qed.
Lemma lem3809878 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : y = a.
Proof. exact (EQ_MP (@lem3809877 B y a) (@lem3809874 A B C n' y R s a n h1 h2 h3)). Qed.
Lemma lem3809881 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3809883 {B : Type'} (y : B) (a : B) : (term211 B y a) = (term298 B y a).
Proof. exact (@lem3809881 (y = a)). Qed.
Lemma lem3809886 {A B C : Type'} (R : type1408 A B C) (s : A) (n' : C) (y : B) (a : B) (h1 : term231 A B C R s n' y a) : term298 B y a.
Proof. exact (EQ_MP (@lem3809883 B y a) (@lem3809532 A B C R s n' y a h1)). Qed.
Lemma lem3809889 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : False.
Proof. exact (@lem3809886 A B C R s n' y a h2 (@lem3809878 A B C n' y R s a n h1 h2 h3)). Qed.
Lemma lem3809890 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : term299.
Proof. exact (fun h0 : ~ False => @lem3809889 A B C n' y R s a n h1 h2 h3). Qed.
Lemma lem3809892 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3809893 : term299 = False.
Proof. exact (@lem3809892 False). Qed.
Lemma lem3809894 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809893) (@lem3809890 A B C n' y R s a n h1 h2 h3)). Qed.
Lemma lem3809956 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (h1). Qed.
Lemma lem3809957 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : term277 A B C R s a n.
Proof. exact (fun h0 : term207 A B C R s a n => @lem3809956 A B C R s a n h1). Qed.
Lemma lem3809959 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3809960 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term277 A B C R s a n) = (R s a n).
Proof. exact (@lem3809959 (R s a n)). Qed.
Lemma lem3809961 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : R s a n) : R s a n.
Proof. exact (EQ_MP (@lem3809960 A B C R s a n) (@lem3809957 A B C R s a n h1)). Qed.
Lemma lem3809964 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3809966 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (_44201 : C) : (term207 A B C R s a _44201) = (term300 A B C R s a _44201).
Proof. exact (@lem3809964 (R s a _44201)). Qed.
Lemma lem3809969 {A B C : Type'} (_44201 : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : term300 A B C R s a _44201.
Proof. exact (EQ_MP (@lem3809966 A B C R s a _44201) (@lem3809663 A B C _44201 R s y a h1)). Qed.
Lemma lem3809970 {A B C : Type'} (_44201 : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : term300 A B C R s a _44201.
Proof. exact (@lem3809969 A B C _44201 R s y a h1). Qed.
Lemma lem3809971 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (y : B) (a : B) (h1 : term215 A B C R s y a) : term300 A B C R s a n.
Proof. exact (@lem3809970 A B C n R s y a h1). Qed.
Lemma lem3809974 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : False.
Proof. exact (@lem3809971 A B C n R s y a h1 (@lem3809961 A B C R s a n h2)). Qed.
Lemma lem3809975 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : term299.
Proof. exact (fun h0 : ~ False => @lem3809974 A B C y R s a n h1 h2). Qed.
Lemma lem3809977 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3809978 : term299 = False.
Proof. exact (@lem3809977 False). Qed.
Lemma lem3809979 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809978) (@lem3809975 A B C y R s a n h1 h2)). Qed.
Lemma lem3809980 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : (R s a n) = False.
Proof. exact (prop_ext (fun h3 : R s a n => @lem3809979 A B C y R s a n h1 h2) (fun h3 : False => @lem3809636 A B C R s a n h2)). Qed.
Lemma lem3809982 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809980 A B C y R s a n h1 h2) (@lem3809636 A B C R s a n h2)). Qed.
Lemma lem3809983 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : (R s a n) = False.
Proof. exact (prop_ext (fun h3 : R s a n => @lem3809982 A B C y R s a n h1 h2) (fun h3 : False => @lem3809560 A B C R s a n h2)). Qed.
Lemma lem3809984 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809983 A B C y R s a n h1 h2) (@lem3809560 A B C R s a n h2)). Qed.
Lemma lem3809985 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : (R s a n) = False.
Proof. exact (prop_ext (fun h4 : R s a n => @lem3809894 A B C n' y R s a n h1 h2 h3) (fun h4 : False => @lem3809522 A B C R s a n h3)). Qed.
Lemma lem3809986 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809985 A B C n' y R s a n h1 h2 h3) (@lem3809522 A B C R s a n h3)). Qed.
Lemma lem3809987 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : (R s a n) = False.
Proof. exact (prop_ext (fun h3 : R s a n => @lem3809984 A B C y R s a n h1 h2) (fun h3 : False => @lem3809451 A B C R s a n h2)). Qed.
Lemma lem3809988 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809987 A B C y R s a n h1 h2) (@lem3809451 A B C R s a n h2)). Qed.
Lemma lem3809989 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : (R s a n) = False.
Proof. exact (prop_ext (fun h4 : R s a n => @lem3809986 A B C n' y R s a n h1 h2 h3) (fun h4 : False => @lem3809381 A B C R s a n h3)). Qed.
Lemma lem3809990 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809989 A B C n' y R s a n h1 h2 h3) (@lem3809381 A B C R s a n h3)). Qed.
Lemma lem3809991 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : (R s a n) = False.
Proof. exact (prop_ext (fun h3 : R s a n => @lem3809988 A B C y R s a n h1 h2) (fun h3 : False => @lem3809451 A B C R s a n h2)). Qed.
Lemma lem3809992 {A B C : Type'} (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term215 A B C R s y a) (h2 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809991 A B C y R s a n h1 h2) (@lem3809451 A B C R s a n h2)). Qed.
Lemma lem3809993 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : (R s a n) = False.
Proof. exact (prop_ext (fun h4 : R s a n => @lem3809990 A B C n' y R s a n h1 h2 h3) (fun h4 : False => @lem3809381 A B C R s a n h3)). Qed.
Lemma lem3809994 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term231 A B C R s n' y a) (h3 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809993 A B C n' y R s a n h1 h2 h3) (@lem3809381 A B C R s a n h3)). Qed.
Lemma lem3809995 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term250 A B C n' R s y a) (h3 : R s a n) : False.
Proof. exact (or_elim (@lem3809303 A B C n' R s y a h2) (fun h0 : term231 A B C R s n' y a => @lem3809994 A B C n' y R s a n h1 h0 h3) (fun h0 : term215 A B C R s y a => @lem3809992 A B C y R s a n h0 h3)). Qed.
Lemma lem3809996 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term250 A B C n' R s y a) (h3 : R s a n) : (term250 A B C n' R s y a) = False.
Proof. exact (prop_ext (fun h4 : term250 A B C n' R s y a => @lem3809995 A B C n' y R s a n h1 h2 h3) (fun h4 : False => @lem3809303 A B C n' R s y a h2)). Qed.
Lemma lem3809997 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term250 A B C n' R s y a) (h3 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809996 A B C n' y R s a n h1 h2 h3) (@lem3809303 A B C n' R s y a h2)). Qed.
Lemma lem3809998 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term250 A B C n' R s y a) (h3 : R s a n) : (R s a n) = False.
Proof. exact (prop_ext (fun h4 : R s a n => @lem3809997 A B C n' y R s a n h1 h2 h3) (fun h4 : False => @lem3809262 A B C R s a n h3)). Qed.
Lemma lem3809999 {A B C : Type'} (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term250 A B C n' R s y a) (h3 : R s a n) : False.
Proof. exact (EQ_MP (@lem3809998 A B C n' y R s a n h1 h2 h3) (@lem3809262 A B C R s a n h3)). Qed.
Lemma lem3810000 {A B C : Type'} (P : A -> Prop) (a' : A -> B) (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term16 A B C R) (h2 : term181 A B C P R a') (h3 : term250 A B C n' R s y a) (h4 : R s a n) : False.
Proof. exact (ex_elim (@lem3809196 A B C P R a' h2) (fun n'' : A -> C => fun h0 : term180 A B C P R a' n'' => @lem3809999 A B C n' y R s a n h1 h3 h4)). Qed.
Lemma lem3810001 {A B C : Type'} (P : A -> Prop) (n' : C) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term250 A B C n' R s y a) (h4 : R s a n) : False.
Proof. exact (ex_elim (@lem3808988 A B C P R h1) (fun a' : A -> B => fun h0 : term182 A B C P R a' => @lem3810000 A B C P a' n' y R s a n h2 h0 h3 h4)). Qed.
Lemma lem3810002 {A B C : Type'} (P : A -> Prop) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term101 A B C R s y a) (h4 : R s a n) : False.
Proof. exact (ex_elim (@lem3809194 A B C R s y a h3) (fun n' : C => fun h0 : term252 A B C R s y a n' => @lem3810001 A B C P n' y R s a n h1 h2 h0 h4)). Qed.
Lemma lem3810003 {A B C : Type'} (P : A -> Prop) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term101 A B C R s y a) (h4 : R s a n) : (R s a n) = False.
Proof. exact (prop_ext (fun h5 : R s a n => @lem3810002 A B C P y R s a n h1 h2 h3 h4) (fun h5 : False => @lem3809101 A B C R s a n h4)). Qed.
Lemma lem3810004 {A B C : Type'} (P : A -> Prop) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term101 A B C R s y a) (h4 : R s a n) : False.
Proof. exact (EQ_MP (@lem3810003 A B C P y R s a n h1 h2 h3 h4) (@lem3809101 A B C R s a n h4)). Qed.
Lemma lem3810005 {A B C : Type'} (P : A -> Prop) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term101 A B C R s y a) (h4 : R s a n) : (term101 A B C R s y a) = False.
Proof. exact (prop_ext (fun h5 : term101 A B C R s y a => @lem3810004 A B C P y R s a n h1 h2 h3 h4) (fun h5 : False => @lem3808800 A B C R s y a h3)). Qed.
Lemma lem3810006 {A B C : Type'} (P : A -> Prop) (y : B) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term101 A B C R s y a) (h4 : R s a n) : False.
Proof. exact (EQ_MP (@lem3810005 A B C P y R s a n h1 h2 h3 h4) (@lem3808800 A B C R s y a h3)). Qed.
Lemma lem3810007 {A B C : Type'} (y : B) (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : R s a n) : term100 A B C R s y a.
Proof. exact (fun h0 : term101 A B C R s y a => @lem3810006 A B C P y R s a n h1 h2 h0 h3). Qed.
Lemma lem3810008 {A B C : Type'} (y : B) (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : R s a n) : (term23 A B C R s y) = (y = a).
Proof. exact (EQ_MP (@lem3808799 A B C R s y a) (@lem3810007 A B C y P R s a n h1 h2 h3)). Qed.
Lemma lem3810013 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : R s a n) : term71 A B C R s a.
Proof. exact (fun y : B => @lem3810008 A B C y P R s a n h1 h2 h3). Qed.
Lemma lem3810014 {A B C : Type'} (n : C) (s : A) (a : B) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term72 A B C n R s a.
Proof. exact (fun h0 : R s a n => @lem3810013 A B C P R s a n h1 h2 h0). Qed.
Lemma lem3810015 {A B C : Type'} (n : C) (s : A) (a : B) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term73 A B C P n R s a.
Proof. exact (fun h0 : P s => @lem3810014 A B C n s a P R h1 h2). Qed.
Lemma lem3810016 {A B C : Type'} (n : C) (s : A) (a : B) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term74 A B C P n R s a.
Proof. exact (fun h0 : term16 A B C R => @lem3810015 A B C n s a P R h1 h0). Qed.
Lemma lem3810017 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : term75 A B C P n R s a.
Proof. exact (fun h0 : term17 A B C P R => @lem3810016 A B C n s a P R h0). Qed.
Lemma lem3810022 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : term77 A B C n R s a.
Proof. exact (fun P : A -> Prop => @lem3810017 A B C P n R s a). Qed.
Lemma lem3810027 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : term79 A B C R s a.
Proof. exact (fun n : C => @lem3810022 A B C n R s a). Qed.
Lemma lem3810032 {A B C : Type'} (s : A) (a : B) : term81 A B C s a.
Proof. exact (fun R : type1408 A B C => @lem3810027 A B C R s a). Qed.
Lemma lem3810037 {A B C : Type'} (a : B) : term83 A B C a.
Proof. exact (fun s : A => @lem3810032 A B C s a). Qed.
Lemma lem3810042 {A B C : Type'} : term85 A B C.
Proof. exact (fun a : B => @lem3810037 A B C a). Qed.
Lemma lem3810043 {A B C : Type'} : term65 A B C.
Proof. exact (EQ_MP (@lem3808791 A B C) (@lem3810042 A B C)). Qed.
Lemma lem3810044 {A B C : Type'} (a : B) : term301 A B C a.
Proof. exact (@lem3810043 A B C a). Qed.
Lemma lem3810045 {A B C : Type'} (a : B) : (term301 A B C a) = (term61 A B C a).
Proof. exact (eq_refl (term301 A B C a)). Qed.
Lemma lem3810046 {A B C : Type'} (a : B) : term61 A B C a.
Proof. exact (EQ_MP (@lem3810045 A B C a) (@lem3810044 A B C a)). Qed.
Lemma lem3810047 {A B C : Type'} (a : B) (s : A) : term302 A B C a s.
Proof. exact (@lem3810046 A B C a s). Qed.
Lemma lem3810048 {A B C : Type'} (s : A) (a : B) : (term302 A B C a s) = (term57 A B C s a).
Proof. exact (eq_refl (term302 A B C a s)). Qed.
Lemma lem3810049 {A B C : Type'} (s : A) (a : B) : term57 A B C s a.
Proof. exact (EQ_MP (@lem3810048 A B C s a) (@lem3810047 A B C a s)). Qed.
Lemma lem3810050 {A B C : Type'} (s : A) (a : B) (R : type1408 A B C) : term303 A B C s a R.
Proof. exact (@lem3810049 A B C s a R). Qed.
Lemma lem3810051 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term303 A B C s a R) = (term53 A B C R s a).
Proof. exact (eq_refl (term303 A B C s a R)). Qed.
Lemma lem3810052 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : term53 A B C R s a.
Proof. exact (EQ_MP (@lem3810051 A B C R s a) (@lem3810050 A B C s a R)). Qed.
Lemma lem3810053 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : term304 A B C R s a n.
Proof. exact (@lem3810052 A B C R s a n). Qed.
Lemma lem3810054 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : (term304 A B C R s a n) = (term49 A B C n R s a).
Proof. exact (eq_refl (term304 A B C R s a n)). Qed.
Lemma lem3810055 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) : term49 A B C n R s a.
Proof. exact (EQ_MP (@lem3810054 A B C n R s a) (@lem3810053 A B C R s a n)). Qed.
Lemma lem3810056 {A B C : Type'} (n : C) (R : type1408 A B C) (s : A) (a : B) (P : A -> Prop) : term305 A B C n R s a P.
Proof. exact (@lem3810055 A B C n R s a P). Qed.
Lemma lem3810057 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : (term305 A B C n R s a P) = (term30 A B C P n R s a).
Proof. exact (eq_refl (term305 A B C n R s a P)). Qed.
Lemma lem3810058 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : term30 A B C P n R s a.
Proof. exact (EQ_MP (@lem3810057 A B C P n R s a) (@lem3810056 A B C n R s a P)). Qed.
Lemma lem3810060 {A B C : Type'} (P : A -> Prop) (n : C) (R : type1408 A B C) (s : A) (a : B) : term30 A B C P n R s a.
Proof. exact (@lem3808431 A B C P n R s a (@lem3810058 A B C P n R s a)). Qed.
Lemma lem3810061 {A B C : Type'} (n : C) (s : A) (a : B) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term43 A B C P n R s a.
Proof. exact (@lem3810060 A B C P n R s a (@lem3808395 A B C P R h1)). Qed.
Lemma lem3810062 {A B C : Type'} (n : C) (s : A) (a : B) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term40 A B C P n R s a.
Proof. exact (@lem3810061 A B C n s a P R h1 (@lem3808394 A B C R h2)). Qed.
Lemma lem3810063 {A B C : Type'} (n : C) (a : B) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : term37 A B C n R s a.
Proof. exact (@lem3810062 A B C n s a P R h1 h2 (@lem3808396 A P s h3)). Qed.
Lemma lem3810064 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) (h4 : R s a n) : term28 A B C R s a.
Proof. exact (@lem3810063 A B C n a R P s h1 h2 h3 (@lem3808406 A B C R s a n h4)). Qed.
Lemma lem3810065 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term29 A B C R s a) (h4 : P s) (h5 : R s a n) : False.
Proof. exact (@lem3810064 A B C P R s a n h1 h2 h4 h5 (@lem3808415 A B C R s a h3)). Qed.
Lemma lem3810066 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term29 A B C R s a) (h4 : P s) (h5 : R s a n) : (term29 A B C R s a) = False.
Proof. exact (prop_ext (fun h6 : term29 A B C R s a => @lem3810065 A B C P R s a n h1 h2 h3 h4 h5) (fun h6 : False => @lem3808415 A B C R s a h3)). Qed.
Lemma lem3810067 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term29 A B C R s a) (h4 : P s) (h5 : R s a n) : False.
Proof. exact (EQ_MP (@lem3810066 A B C P R s a n h1 h2 h3 h4 h5) (@lem3808415 A B C R s a h3)). Qed.
Lemma lem3810068 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) (h4 : R s a n) : term28 A B C R s a.
Proof. exact (fun h0 : term29 A B C R s a => @lem3810067 A B C P R s a n h1 h2 h0 h3 h4). Qed.
Lemma lem3810069 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) (h4 : R s a n) : term27 A B C R s a.
Proof. exact (EQ_MP (@lem3808414 A B C R s a) (@lem3810068 A B C P R s a n h1 h2 h3 h4)). Qed.
Lemma lem3810070 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) (h4 : R s a n) : (term19 A B C R s) = a.
Proof. exact (@lem3808410 A B C R s a (@lem3810069 A B C P R s a n h1 h2 h3 h4)). Qed.
Lemma lem3810071 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) (h4 : R s a n) : (R s a n) = ((term19 A B C R s) = a).
Proof. exact (prop_ext (fun h5 : R s a n => @lem3810070 A B C P R s a n h1 h2 h3 h4) (fun h5 : (term19 A B C R s) = a => @lem3808406 A B C R s a n h4)). Qed.
Lemma lem3810072 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) (h4 : R s a n) : (term19 A B C R s) = a.
Proof. exact (EQ_MP (@lem3810071 A B C P R s a n h1 h2 h3 h4) (@lem3808406 A B C R s a n h4)). Qed.
Lemma lem3810073 {A B C : Type'} (R : type1408 A B C) (a : B) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term23 A B C R s a) (h4 : P s) : (term19 A B C R s) = a.
Proof. exact (ex_elim (@lem3808405 A B C R s a h3) (fun n : C => fun h0 : term86 A B C R s a n => @lem3810072 A B C P R s a n h1 h2 h4 h0)). Qed.
Lemma lem3810074 {A B C : Type'} (a : B) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : term306 A B C R s a.
Proof. exact (fun h0 : term23 A B C R s a => @lem3810073 A B C R a P s h1 h2 h0 h3). Qed.
Lemma lem3810075 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (h1 : (term19 A B C R s) = a) : (term19 A B C R s) = a.
Proof. exact (h1). Qed.
Lemma lem3810076 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (h1 : (term19 A B C R s) = a) : a = (term19 A B C R s).
Proof. exact (SYM (@lem3810075 A B C R s a h1)). Qed.
Lemma lem3810077 {A B C : Type'} (R : type1408 A B C) (s : A) : (term25 A B C R s) = (term25 A B C R s).
Proof. exact (eq_refl (term25 A B C R s)). Qed.
Lemma lem3810078 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (h1 : (term19 A B C R s) = a) : (term67 A B C R s a) = (term307 A B C R s).
Proof. exact (MK_COMB (@lem3810077 A B C R s) (@lem3810076 A B C R s a h1)). Qed.
Lemma lem3810079 {A B C : Type'} (R : type1408 A B C) (s : A) : (term307 A B C R s) = (term308 A B C R s).
Proof. exact (eq_refl (term307 A B C R s)). Qed.
Lemma lem3810080 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term68 A B C R s a) = (term68 A B C R s a).
Proof. exact (eq_refl (term68 A B C R s a)). Qed.
Lemma lem3810081 {A B C : Type'} (a : B) (R : type1408 A B C) (s : A) : ((term67 A B C R s a) = (term307 A B C R s)) = ((term67 A B C R s a) = (term308 A B C R s)).
Proof. exact (MK_COMB (@lem3810080 A B C R s a) (@lem3810079 A B C R s)). Qed.
Lemma lem3810082 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term67 A B C R s a) = (term23 A B C R s a).
Proof. exact (eq_refl (term67 A B C R s a)). Qed.
Lemma lem3810083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3810084 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term68 A B C R s a) = (term22 A B C R s a).
Proof. exact (MK_COMB (@lem3810083) (@lem3810082 A B C R s a)). Qed.
Lemma lem3810085 {A B C : Type'} (R : type1408 A B C) (s : A) : (term308 A B C R s) = (term308 A B C R s).
Proof. exact (eq_refl (term308 A B C R s)). Qed.
Lemma lem3810086 {A B C : Type'} (a : B) (R : type1408 A B C) (s : A) : ((term67 A B C R s a) = (term308 A B C R s)) = ((term23 A B C R s a) = (term308 A B C R s)).
Proof. exact (MK_COMB (@lem3810084 A B C R s a) (@lem3810085 A B C R s)). Qed.
Lemma lem3810087 {A B C : Type'} (a : B) (R : type1408 A B C) (s : A) : ((term67 A B C R s a) = (term307 A B C R s)) = ((term23 A B C R s a) = (term308 A B C R s)).
Proof. exact (TRANS (@lem3810081 A B C a R s) (@lem3810086 A B C a R s)). Qed.
Lemma lem3810088 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (h1 : (term19 A B C R s) = a) : (term23 A B C R s a) = (term308 A B C R s).
Proof. exact (EQ_MP (@lem3810087 A B C a R s) (@lem3810078 A B C R s a h1)). Qed.
Lemma lem3810089 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (h1 : (term19 A B C R s) = a) : (term308 A B C R s) = (term23 A B C R s a).
Proof. exact (SYM (@lem3810088 A B C R s a h1)). Qed.
Lemma lem3810090 {B : Type'} (P : B -> Prop) : (term309 B P) = (ex P).
Proof. exact (@lem9425 B P). Qed.
Lemma lem3810091 {A B C : Type'} (R : type1408 A B C) (s : A) : (term307 A B C R s) = (term97 A B C R s).
Proof. exact (@lem3810090 B (term25 A B C R s)). Qed.
Lemma lem3810092 {A B C : Type'} (R : type1408 A B C) (s : A) : (term307 A B C R s) = (term308 A B C R s).
Proof. exact (eq_refl (term307 A B C R s)). Qed.
Lemma lem3810093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3810094 {A B C : Type'} (R : type1408 A B C) (s : A) : (term310 A B C R s) = (term311 A B C R s).
Proof. exact (MK_COMB (@lem3810093) (@lem3810092 A B C R s)). Qed.
Lemma lem3810095 {A B C : Type'} (R : type1408 A B C) (s : A) : (term97 A B C R s) = (term97 A B C R s).
Proof. exact (eq_refl (term97 A B C R s)). Qed.
Lemma lem3810096 {A B C : Type'} (R : type1408 A B C) (s : A) : ((term307 A B C R s) = (term97 A B C R s)) = ((term308 A B C R s) = (term97 A B C R s)).
Proof. exact (MK_COMB (@lem3810094 A B C R s) (@lem3810095 A B C R s)). Qed.
Lemma lem3810097 {A B C : Type'} (R : type1408 A B C) (s : A) : (term308 A B C R s) = (term97 A B C R s).
Proof. exact (EQ_MP (@lem3810096 A B C R s) (@lem3810091 A B C R s)). Qed.
Lemma lem3810098 {A B C : Type'} (R : type1408 A B C) (s : A) : (term97 A B C R s) = (term308 A B C R s).
Proof. exact (SYM (@lem3810097 A B C R s)). Qed.
Lemma lem3810100 (p : Prop) : p = (term26 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3810101 {A B C : Type'} (R : type1408 A B C) (s : A) : (term97 A B C R s) = (term312 A B C R s).
Proof. exact (@lem3810100 (term97 A B C R s)). Qed.
Lemma lem3810102 {A B C : Type'} (R : type1408 A B C) (s : A) : (term312 A B C R s) = (term97 A B C R s).
Proof. exact (SYM (@lem3810101 A B C R s)). Qed.
Lemma lem3810103 {A B C : Type'} (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term313 A B C R s.
Proof. exact (h1). Qed.
Lemma lem3810106 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (h1 : term314 A B C P R s) : term314 A B C P R s.
Proof. exact (h1). Qed.
Lemma lem3810107 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : term315 A B C P R s.
Proof. exact (fun h0 : term314 A B C P R s => @lem3810106 A B C P R s h0). Qed.
Lemma lem3810108 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (h1 : term315 A B C P R s) : term315 A B C P R s.
Proof. exact (h1). Qed.
Lemma lem3810109 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (h1 : term314 A B C P R s) : term314 A B C P R s.
Proof. exact (h1). Qed.
Lemma lem3810110 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (h1 : term314 A B C P R s) (h2 : term315 A B C P R s) : term314 A B C P R s.
Proof. exact (@lem3810108 A B C P R s h2 (@lem3810109 A B C P R s h1)). Qed.
Lemma lem3810111 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (h1 : term314 A B C P R s) : term316 A B C P R s.
Proof. exact (fun h0 : term315 A B C P R s => @lem3810110 A B C P R s h1 h0). Qed.
Lemma lem3810112 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (h1 : term315 A B C P R s) : term315 A B C P R s.
Proof. exact (h1). Qed.
Lemma lem3810113 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (h1 : term314 A B C P R s) (h2 : term315 A B C P R s) : term314 A B C P R s.
Proof. exact (@lem3810111 A B C P R s h1 (@lem3810112 A B C P R s h2)). Qed.
Lemma lem3810114 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (h1 : term315 A B C P R s) : term315 A B C P R s.
Proof. exact (fun h0 : term314 A B C P R s => @lem3810113 A B C P R s h0 h1). Qed.
Lemma lem3810115 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : term317 A B C P R s.
Proof. exact (fun h0 : term315 A B C P R s => @lem3810114 A B C P R s h0). Qed.
Lemma lem3810118 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : term315 A B C P R s.
Proof. exact (@lem3810115 A B C P R s (@lem3810107 A B C P R s)). Qed.
Lemma lem3810119 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : term315 A B C P R s.
Proof. exact (@lem3810118 A B C P R s). Qed.
Lemma lem3810179 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3810180 {A B C : Type'} (R : type1408 A B C) (s : A) : (term312 A B C R s) = (term318 A B C R s).
Proof. exact (@lem3810179 (term313 A B C R s)). Qed.
Lemma lem3810182 (t : Prop) : (term35 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3810183 {A B C : Type'} (R : type1408 A B C) (s : A) : (term318 A B C R s) = (term97 A B C R s).
Proof. exact (@lem3810182 (term97 A B C R s)). Qed.
Lemma lem3810188 {A B C : Type'} (R : type1408 A B C) (s : A) : (term312 A B C R s) = (term97 A B C R s).
Proof. exact (TRANS (@lem3810180 A B C R s) (@lem3810183 A B C R s)). Qed.
Lemma lem3810193 {A : Type'} (P : A -> Prop) (s : A) : (term39 A P s) = (term39 A P s).
Proof. exact (eq_refl (term39 A P s)). Qed.
Lemma lem3810194 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term319 A B C P R s) = (term98 A B C P R s).
Proof. exact (MK_COMB (@lem3810193 A P s) (@lem3810188 A B C R s)). Qed.
Lemma lem3810197 {A B C : Type'} (R : type1408 A B C) : (term42 A B C R) = (term42 A B C R).
Proof. exact (eq_refl (term42 A B C R)). Qed.
Lemma lem3810198 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term320 A B C P R s) = (term321 A B C P R s).
Proof. exact (MK_COMB (@lem3810197 A B C R) (@lem3810194 A B C P R s)). Qed.
Lemma lem3810201 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term45 A B C P R) = (term45 A B C P R).
Proof. exact (eq_refl (term45 A B C P R)). Qed.
Lemma lem3810202 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term314 A B C P R s) = (term322 A B C P R s).
Proof. exact (MK_COMB (@lem3810201 A B C P R) (@lem3810198 A B C P R s)). Qed.
Lemma lem3810205 {A B C : Type'} (R : type1408 A B C) (s : A) : (term323 A B C R s) = (term324 A B C R s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3810202 A B C P R s)). Qed.
Lemma lem3810206 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3810207 {A B C : Type'} (R : type1408 A B C) (s : A) : (term325 A B C R s) = (term326 A B C R s).
Proof. exact (MK_COMB (@lem3810206 A) (@lem3810205 A B C R s)). Qed.
Lemma lem3810212 {A B C : Type'} (s : A) : (term327 A B C s) = (term328 A B C s).
Proof. exact (fun_ext (fun R : type1408 A B C => @lem3810207 A B C R s)). Qed.
Lemma lem3810213 {A B C : Type'} : (@all (A -> B -> C -> Prop)) = (@all (A -> B -> C -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> C -> Prop))). Qed.
Lemma lem3810214 {A B C : Type'} (s : A) : (term329 A B C s) = (term330 A B C s).
Proof. exact (MK_COMB (@lem3810213 A B C) (@lem3810212 A B C s)). Qed.
Lemma lem3810219 {A B C : Type'} : (term331 A B C) = (term332 A B C).
Proof. exact (fun_ext (fun s : A => @lem3810214 A B C s)). Qed.
Lemma lem3810220 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810229 {A B C : Type'} : (term333 A B C) = (term334 A B C).
Proof. exact (MK_COMB (@lem3810220 A) (@lem3810219 A B C)). Qed.
Lemma lem3810230 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (R s a n) = (R s a n).
Proof. exact (eq_refl (R s a n)). Qed.
Lemma lem3810231 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term86 A B C R s a) = (term86 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3810230 A B C R s a n)). Qed.
Lemma lem3810232 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3810233 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term23 A B C R s a) = (term23 A B C R s a).
Proof. exact (MK_COMB (@lem3810232 C) (@lem3810231 A B C R s a)). Qed.
Lemma lem3810234 {A B C : Type'} (R : type1408 A B C) (s : A) : (term25 A B C R s) = (term25 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3810233 A B C R s a)). Qed.
Lemma lem3810235 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3810236 {A B C : Type'} (R : type1408 A B C) (s : A) : (term97 A B C R s) = (term97 A B C R s).
Proof. exact (MK_COMB (@lem3810235 B) (@lem3810234 A B C R s)). Qed.
Lemma lem3810239 {A : Type'} (P : A -> Prop) (s : A) : (term39 A P s) = (term39 A P s).
Proof. exact (eq_refl (term39 A P s)). Qed.
Lemma lem3810240 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term98 A B C P R s) = (term98 A B C P R s).
Proof. exact (MK_COMB (@lem3810239 A P s) (@lem3810236 A B C R s)). Qed.
Lemma lem3810253 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (a2 : B) (n1 : C) (n2 : C) : (term87 A B C R s a1 a2 n1 n2) = (term87 A B C R s a1 a2 n1 n2).
Proof. exact (eq_refl (term87 A B C R s a1 a2 n1 n2)). Qed.
Lemma lem3810254 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (n1 : C) (n2 : C) : (term88 A B C R s a1 n1 n2) = (term88 A B C R s a1 n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3810253 A B C R s a1 a2 n1 n2)). Qed.
Lemma lem3810255 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3810256 {A B C : Type'} (R : type1408 A B C) (s : A) (a1 : B) (n1 : C) (n2 : C) : (term89 A B C R s a1 n1 n2) = (term89 A B C R s a1 n1 n2).
Proof. exact (MK_COMB (@lem3810255 B) (@lem3810254 A B C R s a1 n1 n2)). Qed.
Lemma lem3810257 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term90 A B C R s n1 n2) = (term90 A B C R s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3810256 A B C R s a1 n1 n2)). Qed.
Lemma lem3810258 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3810259 {A B C : Type'} (R : type1408 A B C) (s : A) (n1 : C) (n2 : C) : (term91 A B C R s n1 n2) = (term91 A B C R s n1 n2).
Proof. exact (MK_COMB (@lem3810258 B) (@lem3810257 A B C R s n1 n2)). Qed.
Lemma lem3810260 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term92 A B C R n1 n2) = (term92 A B C R n1 n2).
Proof. exact (fun_ext (fun s : A => @lem3810259 A B C R s n1 n2)). Qed.
Lemma lem3810261 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810262 {A B C : Type'} (R : type1408 A B C) (n1 : C) (n2 : C) : (term93 A B C R n1 n2) = (term93 A B C R n1 n2).
Proof. exact (MK_COMB (@lem3810261 A) (@lem3810260 A B C R n1 n2)). Qed.
Lemma lem3810263 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term94 A B C R n1) = (term94 A B C R n1).
Proof. exact (fun_ext (fun n2 : C => @lem3810262 A B C R n1 n2)). Qed.
Lemma lem3810264 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3810265 {A B C : Type'} (R : type1408 A B C) (n1 : C) : (term95 A B C R n1) = (term95 A B C R n1).
Proof. exact (MK_COMB (@lem3810264 C) (@lem3810263 A B C R n1)). Qed.
Lemma lem3810266 {A B C : Type'} (R : type1408 A B C) : (term96 A B C R) = (term96 A B C R).
Proof. exact (fun_ext (fun n1 : C => @lem3810265 A B C R n1)). Qed.
Lemma lem3810267 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3810268 {A B C : Type'} (R : type1408 A B C) : (term16 A B C R) = (term16 A B C R).
Proof. exact (MK_COMB (@lem3810267 C) (@lem3810266 A B C R)). Qed.
Lemma lem3810269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3810270 {A B C : Type'} (R : type1408 A B C) : (term42 A B C R) = (term42 A B C R).
Proof. exact (MK_COMB (@lem3810269) (@lem3810268 A B C R)). Qed.
Lemma lem3810271 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term321 A B C P R s) = (term321 A B C P R s).
Proof. exact (MK_COMB (@lem3810270 A B C R) (@lem3810240 A B C P R s)). Qed.
Lemma lem3810272 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (R s a n) = (R s a n).
Proof. exact (eq_refl (R s a n)). Qed.
Lemma lem3810273 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term86 A B C R s a) = (term86 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3810272 A B C R s a n)). Qed.
Lemma lem3810274 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3810275 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term23 A B C R s a) = (term23 A B C R s a).
Proof. exact (MK_COMB (@lem3810274 C) (@lem3810273 A B C R s a)). Qed.
Lemma lem3810276 {A B C : Type'} (R : type1408 A B C) (s : A) : (term25 A B C R s) = (term25 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3810275 A B C R s a)). Qed.
Lemma lem3810277 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3810278 {A B C : Type'} (R : type1408 A B C) (s : A) : (term97 A B C R s) = (term97 A B C R s).
Proof. exact (MK_COMB (@lem3810277 B) (@lem3810276 A B C R s)). Qed.
Lemma lem3810281 {A : Type'} (P : A -> Prop) (s : A) : (term39 A P s) = (term39 A P s).
Proof. exact (eq_refl (term39 A P s)). Qed.
Lemma lem3810282 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term98 A B C P R s) = (term98 A B C P R s).
Proof. exact (MK_COMB (@lem3810281 A P s) (@lem3810278 A B C R s)). Qed.
Lemma lem3810283 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term99 A B C P R) = (term99 A B C P R).
Proof. exact (fun_ext (fun s : A => @lem3810282 A B C P R s)). Qed.
Lemma lem3810284 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810285 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term17 A B C P R) = (term17 A B C P R).
Proof. exact (MK_COMB (@lem3810284 A) (@lem3810283 A B C P R)). Qed.
Lemma lem3810286 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3810287 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term45 A B C P R) = (term45 A B C P R).
Proof. exact (MK_COMB (@lem3810286) (@lem3810285 A B C P R)). Qed.
Lemma lem3810288 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term322 A B C P R s) = (term322 A B C P R s).
Proof. exact (MK_COMB (@lem3810287 A B C P R) (@lem3810271 A B C P R s)). Qed.
Lemma lem3810289 {A B C : Type'} (R : type1408 A B C) (s : A) : (term324 A B C R s) = (term324 A B C R s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3810288 A B C P R s)). Qed.
Lemma lem3810290 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3810291 {A B C : Type'} (R : type1408 A B C) (s : A) : (term326 A B C R s) = (term326 A B C R s).
Proof. exact (MK_COMB (@lem3810290 A) (@lem3810289 A B C R s)). Qed.
Lemma lem3810292 {A B C : Type'} (s : A) : (term328 A B C s) = (term328 A B C s).
Proof. exact (fun_ext (fun R : type1408 A B C => @lem3810291 A B C R s)). Qed.
Lemma lem3810293 {A B C : Type'} : (@all (A -> B -> C -> Prop)) = (@all (A -> B -> C -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> C -> Prop))). Qed.
Lemma lem3810294 {A B C : Type'} (s : A) : (term330 A B C s) = (term330 A B C s).
Proof. exact (MK_COMB (@lem3810293 A B C) (@lem3810292 A B C s)). Qed.
Lemma lem3810295 {A B C : Type'} : (term332 A B C) = (term332 A B C).
Proof. exact (fun_ext (fun s : A => @lem3810294 A B C s)). Qed.
Lemma lem3810296 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810297 {A B C : Type'} : (term334 A B C) = (term334 A B C).
Proof. exact (MK_COMB (@lem3810296 A) (@lem3810295 A B C)). Qed.
Lemma lem3810392 {A B C : Type'} : (term333 A B C) = (term334 A B C).
Proof. exact (TRANS (@lem3810229 A B C) (@lem3810297 A B C)). Qed.
Lemma lem3810393 {A B C : Type'} : (term334 A B C) = (term333 A B C).
Proof. exact (SYM (@lem3810392 A B C)). Qed.
Lemma lem3810394 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term17 A B C P R.
Proof. exact (h1). Qed.
Lemma lem3810398 (p : Prop) : p = (term26 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3810399 {A B C : Type'} (R : type1408 A B C) (s : A) : (term97 A B C R s) = (term312 A B C R s).
Proof. exact (@lem3810398 (term97 A B C R s)). Qed.
Lemma lem3810400 {A B C : Type'} (R : type1408 A B C) (s : A) : (term312 A B C R s) = (term97 A B C R s).
Proof. exact (SYM (@lem3810399 A B C R s)). Qed.
Lemma lem3810401 {A B C : Type'} (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term313 A B C R s.
Proof. exact (h1). Qed.
Lemma lem3810403 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (R s a n) = (R s a n).
Proof. exact (eq_refl (R s a n)). Qed.
Lemma lem3810404 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term86 A B C R s a) = (term86 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3810403 A B C R s a n)). Qed.
Lemma lem3810405 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3810406 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term23 A B C R s a) = (term23 A B C R s a).
Proof. exact (MK_COMB (@lem3810405 C) (@lem3810404 A B C R s a)). Qed.
Lemma lem3810407 {A B C : Type'} (R : type1408 A B C) (s : A) : (term25 A B C R s) = (term25 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3810406 A B C R s a)). Qed.
Lemma lem3810408 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3810409 {A B C : Type'} (R : type1408 A B C) (s : A) : (term97 A B C R s) = (term97 A B C R s).
Proof. exact (MK_COMB (@lem3810408 B) (@lem3810407 A B C R s)). Qed.
Lemma lem3810411 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3810412 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term103 A B C P R s) = (term103 A B C P R s).
Proof. exact (MK_COMB (@lem3810411 A P s) (@lem3810409 A B C R s)). Qed.
Lemma lem3810413 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term98 A B C P R s) = (term103 A B C P R s).
Proof. exact (@lem17265 (P s) (term97 A B C R s)). Qed.
Lemma lem3810414 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term98 A B C P R s) = (term103 A B C P R s).
Proof. exact (TRANS (@lem3810413 A B C P R s) (@lem3810412 A B C P R s)). Qed.
Lemma lem3810415 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term99 A B C P R) = (term104 A B C P R).
Proof. exact (fun_ext (fun s : A => @lem3810414 A B C P R s)). Qed.
Lemma lem3810416 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810417 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term17 A B C P R) = (term105 A B C P R).
Proof. exact (MK_COMB (@lem3810416 A) (@lem3810415 A B C P R)). Qed.
Lemma lem3810476 {A : Type'} (P : Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3810477 {B : Type'} (P : Prop) (Q : B -> Prop) : (term106 B P Q) = (term107 B P Q).
Proof. exact (@lem3810476 B P Q). Qed.
Lemma lem3810478 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term108 A B C P R s) = (term109 A B C P R s).
Proof. exact (@lem3810477 B (term110 A P s) (term25 A B C R s)). Qed.
Lemma lem3810479 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term67 A B C R s a) = (term23 A B C R s a).
Proof. exact (eq_refl (term67 A B C R s a)). Qed.
Lemma lem3810480 {A B C : Type'} (R : type1408 A B C) (s : A) : (term111 A B C R s) = (term25 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3810479 A B C R s a)). Qed.
Lemma lem3810481 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3810482 {A B C : Type'} (R : type1408 A B C) (s : A) : (term112 A B C R s) = (term97 A B C R s).
Proof. exact (MK_COMB (@lem3810481 B) (@lem3810480 A B C R s)). Qed.
Lemma lem3810483 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3810484 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term108 A B C P R s) = (term103 A B C P R s).
Proof. exact (MK_COMB (@lem3810483 A P s) (@lem3810482 A B C R s)). Qed.
Lemma lem3810485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3810486 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term113 A B C P R s) = (term114 A B C P R s).
Proof. exact (MK_COMB (@lem3810485) (@lem3810484 A B C P R s)). Qed.
Lemma lem3810487 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term67 A B C R s a) = (term23 A B C R s a).
Proof. exact (eq_refl (term67 A B C R s a)). Qed.
Lemma lem3810488 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3810489 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term115 A B C P R s a) = (term116 A B C P R s a).
Proof. exact (MK_COMB (@lem3810488 A P s) (@lem3810487 A B C R s a)). Qed.
Lemma lem3810490 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term117 A B C P R s) = (term118 A B C P R s).
Proof. exact (fun_ext (fun a : B => @lem3810489 A B C P R s a)). Qed.
Lemma lem3810491 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3810492 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term109 A B C P R s) = (term119 A B C P R s).
Proof. exact (MK_COMB (@lem3810491 B) (@lem3810490 A B C P R s)). Qed.
Lemma lem3810493 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : ((term108 A B C P R s) = (term109 A B C P R s)) = ((term103 A B C P R s) = (term119 A B C P R s)).
Proof. exact (MK_COMB (@lem3810486 A B C P R s) (@lem3810492 A B C P R s)). Qed.
Lemma lem3810494 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term103 A B C P R s) = (term119 A B C P R s).
Proof. exact (EQ_MP (@lem3810493 A B C P R s) (@lem3810478 A B C P R s)). Qed.
Lemma lem3810496 {A : Type'} (P : Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3810497 {C : Type'} (P : Prop) (Q : C -> Prop) : (term106 C P Q) = (term107 C P Q).
Proof. exact (@lem3810496 C P Q). Qed.
Lemma lem3810498 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term120 A B C P R s a) = (term121 A B C P R s a).
Proof. exact (@lem3810497 C (term110 A P s) (term86 A B C R s a)). Qed.
Lemma lem3810499 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term122 A B C R s a n) = (R s a n).
Proof. exact (eq_refl (term122 A B C R s a n)). Qed.
Lemma lem3810500 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term123 A B C R s a) = (term86 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3810499 A B C R s a n)). Qed.
Lemma lem3810501 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3810502 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term124 A B C R s a) = (term23 A B C R s a).
Proof. exact (MK_COMB (@lem3810501 C) (@lem3810500 A B C R s a)). Qed.
Lemma lem3810503 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3810504 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term120 A B C P R s a) = (term116 A B C P R s a).
Proof. exact (MK_COMB (@lem3810503 A P s) (@lem3810502 A B C R s a)). Qed.
Lemma lem3810505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3810506 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term125 A B C P R s a) = (term126 A B C P R s a).
Proof. exact (MK_COMB (@lem3810505) (@lem3810504 A B C P R s a)). Qed.
Lemma lem3810507 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term122 A B C R s a n) = (R s a n).
Proof. exact (eq_refl (term122 A B C R s a n)). Qed.
Lemma lem3810508 {A : Type'} (P : A -> Prop) (s : A) : (term102 A P s) = (term102 A P s).
Proof. exact (eq_refl (term102 A P s)). Qed.
Lemma lem3810509 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (n : C) : (term127 A B C P R s a n) = (term128 A B C P R s a n).
Proof. exact (MK_COMB (@lem3810508 A P s) (@lem3810507 A B C R s a n)). Qed.
Lemma lem3810510 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term129 A B C P R s a) = (term130 A B C P R s a).
Proof. exact (fun_ext (fun n : C => @lem3810509 A B C P R s a n)). Qed.
Lemma lem3810511 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3810512 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term121 A B C P R s a) = (term131 A B C P R s a).
Proof. exact (MK_COMB (@lem3810511 C) (@lem3810510 A B C P R s a)). Qed.
Lemma lem3810513 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : ((term120 A B C P R s a) = (term121 A B C P R s a)) = ((term116 A B C P R s a) = (term131 A B C P R s a)).
Proof. exact (MK_COMB (@lem3810506 A B C P R s a) (@lem3810512 A B C P R s a)). Qed.
Lemma lem3810514 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term116 A B C P R s a) = (term131 A B C P R s a).
Proof. exact (EQ_MP (@lem3810513 A B C P R s a) (@lem3810498 A B C P R s a)). Qed.
Lemma lem3810515 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term118 A B C P R s) = (term132 A B C P R s).
Proof. exact (fun_ext (fun a : B => @lem3810514 A B C P R s a)). Qed.
Lemma lem3810516 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3810517 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term119 A B C P R s) = (term133 A B C P R s).
Proof. exact (MK_COMB (@lem3810516 B) (@lem3810515 A B C P R s)). Qed.
Lemma lem3810518 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term103 A B C P R s) = (term133 A B C P R s).
Proof. exact (TRANS (@lem3810494 A B C P R s) (@lem3810517 A B C P R s)). Qed.
Lemma lem3810519 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term104 A B C P R) = (term134 A B C P R).
Proof. exact (fun_ext (fun s : A => @lem3810518 A B C P R s)). Qed.
Lemma lem3810520 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810521 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term105 A B C P R) = (term135 A B C P R).
Proof. exact (MK_COMB (@lem3810520 A) (@lem3810519 A B C P R)). Qed.
Lemma lem3810523 {A B : Type'} (P : type1413 A B) : (term136 A B P) = (term137 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3810524 {A B : Type'} (P : type1413 A B) : (term136 A B P) = (term137 A B P).
Proof. exact (@lem3810523 A B P). Qed.
Lemma lem3810525 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term138 A B C P R) = (term139 A B C P R).
Proof. exact (@lem3810524 A B (term140 A B C P R)). Qed.
Lemma lem3810526 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term141 A B C P R s) = (term132 A B C P R s).
Proof. exact (eq_refl (term141 A B C P R s)). Qed.
Lemma lem3810527 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3810528 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term142 A B C P R s a) = (term143 A B C P R s a).
Proof. exact (MK_COMB (@lem3810526 A B C P R s) (@lem3810527 B a)). Qed.
Lemma lem3810529 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term143 A B C P R s a) = (term131 A B C P R s a).
Proof. exact (eq_refl (term143 A B C P R s a)). Qed.
Lemma lem3810530 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) : (term142 A B C P R s a) = (term131 A B C P R s a).
Proof. exact (TRANS (@lem3810528 A B C P R s a) (@lem3810529 A B C P R s a)). Qed.
Lemma lem3810531 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term144 A B C P R s) = (term132 A B C P R s).
Proof. exact (fun_ext (fun a : B => @lem3810530 A B C P R s a)). Qed.
Lemma lem3810532 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3810533 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term145 A B C P R s) = (term133 A B C P R s).
Proof. exact (MK_COMB (@lem3810532 B) (@lem3810531 A B C P R s)). Qed.
Lemma lem3810534 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term146 A B C P R) = (term134 A B C P R).
Proof. exact (fun_ext (fun s : A => @lem3810533 A B C P R s)). Qed.
Lemma lem3810535 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810536 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term138 A B C P R) = (term135 A B C P R).
Proof. exact (MK_COMB (@lem3810535 A) (@lem3810534 A B C P R)). Qed.
Lemma lem3810537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3810538 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term147 A B C P R) = (term148 A B C P R).
Proof. exact (MK_COMB (@lem3810537) (@lem3810536 A B C P R)). Qed.
Lemma lem3810539 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term141 A B C P R s) = (term132 A B C P R s).
Proof. exact (eq_refl (term141 A B C P R s)). Qed.
Lemma lem3810540 {A B : Type'} (a : A -> B) (s : A) : (a s) = (a s).
Proof. exact (eq_refl (a s)). Qed.
Lemma lem3810541 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term149 A B C P R a s) = (term150 A B C P R a s).
Proof. exact (MK_COMB (@lem3810539 A B C P R s) (@lem3810540 A B a s)). Qed.
Lemma lem3810542 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term150 A B C P R a s) = (term151 A B C P R a s).
Proof. exact (eq_refl (term150 A B C P R a s)). Qed.
Lemma lem3810543 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term149 A B C P R a s) = (term151 A B C P R a s).
Proof. exact (TRANS (@lem3810541 A B C P R a s) (@lem3810542 A B C P R a s)). Qed.
Lemma lem3810544 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term152 A B C P R a) = (term153 A B C P R a).
Proof. exact (fun_ext (fun s : A => @lem3810543 A B C P R a s)). Qed.
Lemma lem3810545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810546 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term154 A B C P R a) = (term155 A B C P R a).
Proof. exact (MK_COMB (@lem3810545 A) (@lem3810544 A B C P R a)). Qed.
Lemma lem3810547 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term156 A B C P R) = (term157 A B C P R).
Proof. exact (fun_ext (fun a : A -> B => @lem3810546 A B C P R a)). Qed.
Lemma lem3810548 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3810549 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term139 A B C P R) = (term158 A B C P R).
Proof. exact (MK_COMB (@lem3810548 A B) (@lem3810547 A B C P R)). Qed.
Lemma lem3810550 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : ((term138 A B C P R) = (term139 A B C P R)) = ((term135 A B C P R) = (term158 A B C P R)).
Proof. exact (MK_COMB (@lem3810538 A B C P R) (@lem3810549 A B C P R)). Qed.
Lemma lem3810551 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term135 A B C P R) = (term158 A B C P R).
Proof. exact (EQ_MP (@lem3810550 A B C P R) (@lem3810525 A B C P R)). Qed.
Lemma lem3810553 {A B : Type'} (P : type1413 A B) : (term136 A B P) = (term137 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3810554 {A C : Type'} (P : type1413 A C) : (term136 A C P) = (term137 A C P).
Proof. exact (@lem3810553 A C P). Qed.
Lemma lem3810555 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term159 A B C P R a) = (term160 A B C P R a).
Proof. exact (@lem3810554 A C (term161 A B C P R a)). Qed.
Lemma lem3810556 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term162 A B C P R a s) = (term163 A B C P R a s).
Proof. exact (eq_refl (term162 A B C P R a s)). Qed.
Lemma lem3810557 {C : Type'} (n : C) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3810558 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) (n : C) : (term164 A B C P R a s n) = (term165 A B C P R a s n).
Proof. exact (MK_COMB (@lem3810556 A B C P R a s) (@lem3810557 C n)). Qed.
Lemma lem3810559 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) (n : C) : (term165 A B C P R a s n) = (term166 A B C P R a s n).
Proof. exact (eq_refl (term165 A B C P R a s n)). Qed.
Lemma lem3810560 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) (n : C) : (term164 A B C P R a s n) = (term166 A B C P R a s n).
Proof. exact (TRANS (@lem3810558 A B C P R a s n) (@lem3810559 A B C P R a s n)). Qed.
Lemma lem3810561 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term167 A B C P R a s) = (term163 A B C P R a s).
Proof. exact (fun_ext (fun n : C => @lem3810560 A B C P R a s n)). Qed.
Lemma lem3810562 {C : Type'} : (@ex C) = (@ex C).
Proof. exact (eq_refl (@ex C)). Qed.
Lemma lem3810563 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term168 A B C P R a s) = (term151 A B C P R a s).
Proof. exact (MK_COMB (@lem3810562 C) (@lem3810561 A B C P R a s)). Qed.
Lemma lem3810564 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term169 A B C P R a) = (term153 A B C P R a).
Proof. exact (fun_ext (fun s : A => @lem3810563 A B C P R a s)). Qed.
Lemma lem3810565 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810566 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term159 A B C P R a) = (term155 A B C P R a).
Proof. exact (MK_COMB (@lem3810565 A) (@lem3810564 A B C P R a)). Qed.
Lemma lem3810567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3810568 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term170 A B C P R a) = (term171 A B C P R a).
Proof. exact (MK_COMB (@lem3810567) (@lem3810566 A B C P R a)). Qed.
Lemma lem3810569 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (s : A) : (term162 A B C P R a s) = (term163 A B C P R a s).
Proof. exact (eq_refl (term162 A B C P R a s)). Qed.
Lemma lem3810570 {A C : Type'} (n : A -> C) (s : A) : (n s) = (n s).
Proof. exact (eq_refl (n s)). Qed.
Lemma lem3810571 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (s : A) : (term172 A B C P R a n s) = (term173 A B C P R a n s).
Proof. exact (MK_COMB (@lem3810569 A B C P R a s) (@lem3810570 A C n s)). Qed.
Lemma lem3810572 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (s : A) : (term173 A B C P R a n s) = (term174 A B C P R a n s).
Proof. exact (eq_refl (term173 A B C P R a n s)). Qed.
Lemma lem3810573 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (s : A) : (term172 A B C P R a n s) = (term174 A B C P R a n s).
Proof. exact (TRANS (@lem3810571 A B C P R a n s) (@lem3810572 A B C P R a n s)). Qed.
Lemma lem3810574 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) : (term175 A B C P R a n) = (term176 A B C P R a n).
Proof. exact (fun_ext (fun s : A => @lem3810573 A B C P R a n s)). Qed.
Lemma lem3810575 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810576 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) : (term177 A B C P R a n) = (term178 A B C P R a n).
Proof. exact (MK_COMB (@lem3810575 A) (@lem3810574 A B C P R a n)). Qed.
Lemma lem3810577 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term179 A B C P R a) = (term180 A B C P R a).
Proof. exact (fun_ext (fun n : A -> C => @lem3810576 A B C P R a n)). Qed.
Lemma lem3810578 {A C : Type'} : (@ex (A -> C)) = (@ex (A -> C)).
Proof. exact (eq_refl (@ex (A -> C))). Qed.
Lemma lem3810579 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term160 A B C P R a) = (term181 A B C P R a).
Proof. exact (MK_COMB (@lem3810578 A C) (@lem3810577 A B C P R a)). Qed.
Lemma lem3810580 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : ((term159 A B C P R a) = (term160 A B C P R a)) = ((term155 A B C P R a) = (term181 A B C P R a)).
Proof. exact (MK_COMB (@lem3810568 A B C P R a) (@lem3810579 A B C P R a)). Qed.
Lemma lem3810581 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) : (term155 A B C P R a) = (term181 A B C P R a).
Proof. exact (EQ_MP (@lem3810580 A B C P R a) (@lem3810555 A B C P R a)). Qed.
Lemma lem3810582 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term157 A B C P R) = (term182 A B C P R).
Proof. exact (fun_ext (fun a : A -> B => @lem3810581 A B C P R a)). Qed.
Lemma lem3810583 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3810584 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term158 A B C P R) = (term183 A B C P R).
Proof. exact (MK_COMB (@lem3810583 A B) (@lem3810582 A B C P R)). Qed.
Lemma lem3810585 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term135 A B C P R) = (term183 A B C P R).
Proof. exact (TRANS (@lem3810551 A B C P R) (@lem3810584 A B C P R)). Qed.
Lemma lem3810587 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term105 A B C P R) = (term183 A B C P R).
Proof. exact (TRANS (@lem3810521 A B C P R) (@lem3810585 A B C P R)). Qed.
Lemma lem3810588 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term17 A B C P R) = (term183 A B C P R).
Proof. exact (TRANS (@lem3810417 A B C P R) (@lem3810587 A B C P R)). Qed.
Lemma lem3810589 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term183 A B C P R.
Proof. exact (EQ_MP (@lem3810588 A B C P R) (@lem3810394 A B C P R h1)). Qed.
Lemma lem3810696 {A : Type'} (P : A -> Prop) (s : A) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3810698 {C : Type'} (P : C -> Prop) : (term202 C P) = (term203 C P).
Proof. exact (@lem18394 C P). Qed.
Lemma lem3810699 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term204 A B C R s a) = (term205 A B C R s a).
Proof. exact (@lem3810698 C (term86 A B C R s a)). Qed.
Lemma lem3810700 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term122 A B C R s a n) = (R s a n).
Proof. exact (eq_refl (term122 A B C R s a n)). Qed.
Lemma lem3810701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3810703 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term206 A B C R s a n) = (term207 A B C R s a n).
Proof. exact (MK_COMB (@lem3810701) (@lem3810700 A B C R s a n)). Qed.
Lemma lem3810704 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term208 A B C R s a) = (term209 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3810703 A B C R s a n)). Qed.
Lemma lem3810705 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3810706 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term205 A B C R s a) = (term210 A B C R s a).
Proof. exact (MK_COMB (@lem3810705 C) (@lem3810704 A B C R s a)). Qed.
Lemma lem3810707 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term204 A B C R s a) = (term210 A B C R s a).
Proof. exact (TRANS (@lem3810699 A B C R s a) (@lem3810706 A B C R s a)). Qed.
Lemma lem3810708 {B : Type'} (P : B -> Prop) : (term202 B P) = (term203 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem3810709 {A B C : Type'} (R : type1408 A B C) (s : A) : (term313 A B C R s) = (term335 A B C R s).
Proof. exact (@lem3810708 B (term25 A B C R s)). Qed.
Lemma lem3810710 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term67 A B C R s a) = (term23 A B C R s a).
Proof. exact (eq_refl (term67 A B C R s a)). Qed.
Lemma lem3810711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3810712 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term336 A B C R s a) = (term204 A B C R s a).
Proof. exact (MK_COMB (@lem3810711) (@lem3810710 A B C R s a)). Qed.
Lemma lem3810713 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term336 A B C R s a) = (term210 A B C R s a).
Proof. exact (TRANS (@lem3810712 A B C R s a) (@lem3810707 A B C R s a)). Qed.
Lemma lem3810714 {A B C : Type'} (R : type1408 A B C) (s : A) : (term337 A B C R s) = (term338 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3810713 A B C R s a)). Qed.
Lemma lem3810715 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3810716 {A B C : Type'} (R : type1408 A B C) (s : A) : (term335 A B C R s) = (term339 A B C R s).
Proof. exact (MK_COMB (@lem3810715 B) (@lem3810714 A B C R s)). Qed.
Lemma lem3810729 {A B C : Type'} (R : type1408 A B C) (s : A) : (term313 A B C R s) = (term339 A B C R s).
Proof. exact (TRANS (@lem3810709 A B C R s) (@lem3810716 A B C R s)). Qed.
Lemma lem3810730 {A B C : Type'} (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term339 A B C R s.
Proof. exact (EQ_MP (@lem3810729 A B C R s) (@lem3810401 A B C R s h1)). Qed.
Lemma lem3810731 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (h1 : term181 A B C P R a) : term181 A B C P R a.
Proof. exact (h1). Qed.
Lemma lem3810732 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (h1 : term178 A B C P R a n) : term178 A B C P R a n.
Proof. exact (h1). Qed.
Lemma lem3810789 {A : Type'} (P : A -> Prop) (s : A) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3810798 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term207 A B C R s a n) = (term207 A B C R s a n).
Proof. exact (eq_refl (term207 A B C R s a n)). Qed.
Lemma lem3810799 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term209 A B C R s a) = (term209 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3810798 A B C R s a n)). Qed.
Lemma lem3810800 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3810801 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term210 A B C R s a) = (term210 A B C R s a).
Proof. exact (MK_COMB (@lem3810800 C) (@lem3810799 A B C R s a)). Qed.
Lemma lem3810802 {A B C : Type'} (R : type1408 A B C) (s : A) : (term338 A B C R s) = (term338 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3810801 A B C R s a)). Qed.
Lemma lem3810803 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3810804 {A B C : Type'} (R : type1408 A B C) (s : A) : (term339 A B C R s) = (term339 A B C R s).
Proof. exact (MK_COMB (@lem3810803 B) (@lem3810802 A B C R s)). Qed.
Lemma lem3810805 {A B C : Type'} (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term339 A B C R s.
Proof. exact (EQ_MP (@lem3810804 A B C R s) (@lem3810730 A B C R s h1)). Qed.
Lemma lem3810824 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (s : A) : (term174 A B C P R a n s) = (term174 A B C P R a n s).
Proof. exact (eq_refl (term174 A B C P R a n s)). Qed.
Lemma lem3810825 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) : (term176 A B C P R a n) = (term176 A B C P R a n).
Proof. exact (fun_ext (fun s : A => @lem3810824 A B C P R a n s)). Qed.
Lemma lem3810826 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810827 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) : (term178 A B C P R a n) = (term178 A B C P R a n).
Proof. exact (MK_COMB (@lem3810826 A) (@lem3810825 A B C P R a n)). Qed.
Lemma lem3810828 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (h1 : term178 A B C P R a n) : term178 A B C P R a n.
Proof. exact (EQ_MP (@lem3810827 A B C P R a n) (@lem3810732 A B C P R a n h1)). Qed.
Lemma lem3810873 {A : Type'} (P : A -> Prop) (s : A) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3810875 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) (n : C) : (term207 A B C R s a n) = (term207 A B C R s a n).
Proof. exact (eq_refl (term207 A B C R s a n)). Qed.
Lemma lem3810876 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term209 A B C R s a) = (term209 A B C R s a).
Proof. exact (fun_ext (fun n : C => @lem3810875 A B C R s a n)). Qed.
Lemma lem3810877 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3810878 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term210 A B C R s a) = (term210 A B C R s a).
Proof. exact (MK_COMB (@lem3810877 C) (@lem3810876 A B C R s a)). Qed.
Lemma lem3810879 {A B C : Type'} (R : type1408 A B C) (s : A) : (term338 A B C R s) = (term338 A B C R s).
Proof. exact (fun_ext (fun a : B => @lem3810878 A B C R s a)). Qed.
Lemma lem3810880 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3810882 {A B C : Type'} (R : type1408 A B C) (s : A) : (term339 A B C R s) = (term339 A B C R s).
Proof. exact (MK_COMB (@lem3810880 B) (@lem3810879 A B C R s)). Qed.
Lemma lem3810883 {A B C : Type'} (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term339 A B C R s.
Proof. exact (EQ_MP (@lem3810882 A B C R s) (@lem3810805 A B C R s h1)). Qed.
Lemma lem3810891 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (s : A) : (term174 A B C P R a n s) = (term174 A B C P R a n s).
Proof. exact (eq_refl (term174 A B C P R a n s)). Qed.
Lemma lem3810892 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) : (term176 A B C P R a n) = (term176 A B C P R a n).
Proof. exact (fun_ext (fun s : A => @lem3810891 A B C P R a n s)). Qed.
Lemma lem3810893 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3810895 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) : (term178 A B C P R a n) = (term178 A B C P R a n).
Proof. exact (MK_COMB (@lem3810893 A) (@lem3810892 A B C P R a n)). Qed.
Lemma lem3810896 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (h1 : term178 A B C P R a n) : term178 A B C P R a n.
Proof. exact (EQ_MP (@lem3810895 A B C P R a n) (@lem3810828 A B C P R a n h1)). Qed.
Lemma lem3810912 {A B C : Type'} (_44247 : B) (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term340 A B C R s _44247.
Proof. exact (@lem3810883 A B C R s h1 _44247). Qed.
Lemma lem3810913 {A B C : Type'} (R : type1408 A B C) (s : A) (_44247 : B) : (term340 A B C R s _44247) = (term210 A B C R s _44247).
Proof. exact (eq_refl (term340 A B C R s _44247)). Qed.
Lemma lem3810914 {A B C : Type'} (_44247 : B) (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term210 A B C R s _44247.
Proof. exact (EQ_MP (@lem3810913 A B C R s _44247) (@lem3810912 A B C _44247 R s h1)). Qed.
Lemma lem3810915 {A B C : Type'} (_44247 : B) (_44248 : C) (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term270 A B C R s _44247 _44248.
Proof. exact (@lem3810914 A B C _44247 R s h1 _44248). Qed.
Lemma lem3810916 {A B C : Type'} (R : type1408 A B C) (s : A) (_44247 : B) (_44248 : C) : (term270 A B C R s _44247 _44248) = (term207 A B C R s _44247 _44248).
Proof. exact (eq_refl (term270 A B C R s _44247 _44248)). Qed.
Lemma lem3810918 {A B C : Type'} (_44249 : A) (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (h1 : term178 A B C P R a n) : term341 A B C P R a n _44249.
Proof. exact (@lem3810896 A B C P R a n h1 _44249). Qed.
Lemma lem3810919 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (_44249 : A) : (term341 A B C P R a n _44249) = (term174 A B C P R a n _44249).
Proof. exact (eq_refl (term341 A B C P R a n _44249)). Qed.
Lemma lem3810924 {A : Type'} (P : A -> Prop) (s : A) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3810926 {A B C : Type'} (_44247 : B) (_44248 : C) (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term207 A B C R s _44247 _44248.
Proof. exact (EQ_MP (@lem3810916 A B C R s _44247 _44248) (@lem3810915 A B C _44247 _44248 R s h1)). Qed.
Lemma lem3810932 {A B C : Type'} (_44249 : A) (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (h1 : term178 A B C P R a n) : term174 A B C P R a n _44249.
Proof. exact (EQ_MP (@lem3810919 A B C P R a n _44249) (@lem3810918 A B C _44249 P R a n h1)). Qed.
Lemma lem3811018 {A : Type'} (P : A -> Prop) (s : A) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3811019 {A : Type'} (P : A -> Prop) (s : A) (h1 : P s) : term342 A P s.
Proof. exact (fun h0 : term110 A P s => @lem3811018 A P s h1). Qed.
Lemma lem3811021 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3811022 {A : Type'} (P : A -> Prop) (s : A) : (term342 A P s) = (P s).
Proof. exact (@lem3811021 (P s)). Qed.
Lemma lem3811023 {A : Type'} (P : A -> Prop) (s : A) (h1 : P s) : P s.
Proof. exact (EQ_MP (@lem3811022 A P s) (@lem3811019 A P s h1)). Qed.
Lemma lem3811029 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3811030 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (_44249 : A) : (term174 A B C P R a n _44249) = (term343 A B C R a n P _44249).
Proof. exact (@lem3811029 (term344 A B C R a n _44249) (term110 A P _44249)). Qed.
Lemma lem3811036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3811037 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (_44249 : A) : (term345 A B C P R a n _44249) = (term346 A B C R a n P _44249).
Proof. exact (MK_COMB (@lem3811036) (@lem3811030 A B C R a n P _44249)). Qed.
Lemma lem3811043 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (_44249 : A) : (term343 A B C R a n P _44249) = (term343 A B C R a n P _44249).
Proof. exact (eq_refl (term343 A B C R a n P _44249)). Qed.
Lemma lem3811044 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (_44249 : A) : ((term174 A B C P R a n _44249) = (term343 A B C R a n P _44249)) = ((term343 A B C R a n P _44249) = (term343 A B C R a n P _44249)).
Proof. exact (MK_COMB (@lem3811037 A B C R a n P _44249) (@lem3811043 A B C R a n P _44249)). Qed.
Lemma lem3811046 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3811047 (x : Prop) : (x = x) = True.
Proof. exact (@lem3811046 Prop x). Qed.
Lemma lem3811048 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (_44249 : A) : ((term343 A B C R a n P _44249) = (term343 A B C R a n P _44249)) = True.
Proof. exact (@lem3811047 (term343 A B C R a n P _44249)). Qed.
Lemma lem3811049 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (_44249 : A) : ((term174 A B C P R a n _44249) = (term343 A B C R a n P _44249)) = True.
Proof. exact (TRANS (@lem3811044 A B C R a n P _44249) (@lem3811048 A B C R a n P _44249)). Qed.
Lemma lem3811050 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (_44249 : A) : True = ((term174 A B C P R a n _44249) = (term343 A B C R a n P _44249)).
Proof. exact (SYM (@lem3811049 A B C R a n P _44249)). Qed.
Lemma lem3811051 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (_44249 : A) : (term174 A B C P R a n _44249) = (term343 A B C R a n P _44249).
Proof. exact (EQ_MP (@lem3811050 A B C R a n P _44249) (@lem0)). Qed.
Lemma lem3811052 {A B C : Type'} (_44249 : A) (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (h1 : term178 A B C P R a n) : term343 A B C R a n P _44249.
Proof. exact (EQ_MP (@lem3811051 A B C R a n P _44249) (@lem3810932 A B C _44249 P R a n h1)). Qed.
Lemma lem3811054 (b : Prop) (a : Prop) : (a \/ b) = (term286 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3811055 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (_44249 : A) : (term343 A B C R a n P _44249) = (term347 A B C P R a n _44249).
Proof. exact (@lem3811054 (term110 A P _44249) (term344 A B C R a n _44249)). Qed.
Lemma lem3811057 (a : Prop) : (term35 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3811058 {A : Type'} (P : A -> Prop) (_44249 : A) : (term348 A P _44249) = (P _44249).
Proof. exact (@lem3811057 (P _44249)). Qed.
Lemma lem3811059 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811060 {A : Type'} (P : A -> Prop) (_44249 : A) : (term349 A P _44249) = (term39 A P _44249).
Proof. exact (MK_COMB (@lem3811059) (@lem3811058 A P _44249)). Qed.
Lemma lem3811061 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (_44249 : A) : (term344 A B C R a n _44249) = (term344 A B C R a n _44249).
Proof. exact (eq_refl (term344 A B C R a n _44249)). Qed.
Lemma lem3811062 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (_44249 : A) : (term347 A B C P R a n _44249) = (term350 A B C P R a n _44249).
Proof. exact (MK_COMB (@lem3811060 A P _44249) (@lem3811061 A B C R a n _44249)). Qed.
Lemma lem3811063 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (_44249 : A) : (term343 A B C R a n P _44249) = (term350 A B C P R a n _44249).
Proof. exact (TRANS (@lem3811055 A B C P R a n _44249) (@lem3811062 A B C P R a n _44249)). Qed.
Lemma lem3811066 {A B C : Type'} (_44249 : A) (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (h1 : term178 A B C P R a n) : term350 A B C P R a n _44249.
Proof. exact (EQ_MP (@lem3811063 A B C P R a n _44249) (@lem3811052 A B C _44249 P R a n h1)). Qed.
Lemma lem3811067 {A B C : Type'} (_44249 : A) (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (h1 : term178 A B C P R a n) : term350 A B C P R a n _44249.
Proof. exact (@lem3811066 A B C _44249 P R a n h1). Qed.
Lemma lem3811068 {A B C : Type'} (s : A) (P : A -> Prop) (R : type1408 A B C) (a : A -> B) (n : A -> C) (h1 : term178 A B C P R a n) : term350 A B C P R a n s.
Proof. exact (@lem3811067 A B C s P R a n h1). Qed.
Lemma lem3811071 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : P s) : term344 A B C R a n s.
Proof. exact (@lem3811068 A B C s P R a n h1 (@lem3811023 A P s h2)). Qed.
Lemma lem3811072 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : P s) : term351 A B C R a n s.
Proof. exact (fun h0 : term352 A B C R a n s => @lem3811071 A B C R a n P s h1 h2). Qed.
Lemma lem3811074 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3811075 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (s : A) : (term351 A B C R a n s) = (term344 A B C R a n s).
Proof. exact (@lem3811074 (term344 A B C R a n s)). Qed.
Lemma lem3811076 {A B C : Type'} (R : type1408 A B C) (a : A -> B) (n : A -> C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : P s) : term344 A B C R a n s.
Proof. exact (EQ_MP (@lem3811075 A B C R a n s) (@lem3811072 A B C R a n P s h1 h2)). Qed.
Lemma lem3811079 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3811081 {A B C : Type'} (R : type1408 A B C) (s : A) (_44247 : B) (_44248 : C) : (term207 A B C R s _44247 _44248) = (term300 A B C R s _44247 _44248).
Proof. exact (@lem3811079 (R s _44247 _44248)). Qed.
Lemma lem3811084 {A B C : Type'} (_44247 : B) (_44248 : C) (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term300 A B C R s _44247 _44248.
Proof. exact (EQ_MP (@lem3811081 A B C R s _44247 _44248) (@lem3810926 A B C _44247 _44248 R s h1)). Qed.
Lemma lem3811085 {A B C : Type'} (_44247 : B) (_44248 : C) (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term300 A B C R s _44247 _44248.
Proof. exact (@lem3811084 A B C _44247 _44248 R s h1). Qed.
Lemma lem3811086 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (s : A) (h1 : term313 A B C R s) : term353 A B C R a n s.
Proof. exact (@lem3811085 A B C (a s) (n s) R s h1). Qed.
Lemma lem3811089 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (@lem3811086 A B C a n R s h2 (@lem3811076 A B C R a n P s h1 h3)). Qed.
Lemma lem3811090 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : term299.
Proof. exact (fun h0 : ~ False => @lem3811089 A B C a n R P s h1 h2 h3). Qed.
Lemma lem3811092 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3811093 : term299 = False.
Proof. exact (@lem3811092 False). Qed.
Lemma lem3811094 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (EQ_MP (@lem3811093) (@lem3811090 A B C a n R P s h1 h2 h3)). Qed.
Lemma lem3811095 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : (P s) = False.
Proof. exact (prop_ext (fun h4 : P s => @lem3811094 A B C a n R P s h1 h2 h3) (fun h4 : False => @lem3810924 A P s h3)). Qed.
Lemma lem3811096 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (EQ_MP (@lem3811095 A B C a n R P s h1 h2 h3) (@lem3810924 A P s h3)). Qed.
Lemma lem3811097 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : (P s) = False.
Proof. exact (prop_ext (fun h4 : P s => @lem3811096 A B C a n R P s h1 h2 h3) (fun h4 : False => @lem3810873 A P s h3)). Qed.
Lemma lem3811098 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (EQ_MP (@lem3811097 A B C a n R P s h1 h2 h3) (@lem3810873 A P s h3)). Qed.
Lemma lem3811099 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : (term178 A B C P R a n) = False.
Proof. exact (prop_ext (fun h4 : term178 A B C P R a n => @lem3811098 A B C a n R P s h1 h2 h3) (fun h4 : False => @lem3810896 A B C P R a n h1)). Qed.
Lemma lem3811100 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (EQ_MP (@lem3811099 A B C a n R P s h1 h2 h3) (@lem3810896 A B C P R a n h1)). Qed.
Lemma lem3811101 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : (P s) = False.
Proof. exact (prop_ext (fun h4 : P s => @lem3811100 A B C a n R P s h1 h2 h3) (fun h4 : False => @lem3810873 A P s h3)). Qed.
Lemma lem3811102 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (EQ_MP (@lem3811101 A B C a n R P s h1 h2 h3) (@lem3810873 A P s h3)). Qed.
Lemma lem3811103 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : (term178 A B C P R a n) = False.
Proof. exact (prop_ext (fun h4 : term178 A B C P R a n => @lem3811102 A B C a n R P s h1 h2 h3) (fun h4 : False => @lem3810828 A B C P R a n h1)). Qed.
Lemma lem3811104 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (EQ_MP (@lem3811103 A B C a n R P s h1 h2 h3) (@lem3810828 A B C P R a n h1)). Qed.
Lemma lem3811105 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : (P s) = False.
Proof. exact (prop_ext (fun h4 : P s => @lem3811104 A B C a n R P s h1 h2 h3) (fun h4 : False => @lem3810789 A P s h3)). Qed.
Lemma lem3811106 {A B C : Type'} (a : A -> B) (n : A -> C) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term178 A B C P R a n) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (EQ_MP (@lem3811105 A B C a n R P s h1 h2 h3) (@lem3810789 A P s h3)). Qed.
Lemma lem3811107 {A B C : Type'} (a : A -> B) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term181 A B C P R a) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (ex_elim (@lem3810731 A B C P R a h1) (fun n : A -> C => fun h0 : term180 A B C P R a n => @lem3811106 A B C a n R P s h0 h2 h3)). Qed.
Lemma lem3811108 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (ex_elim (@lem3810589 A B C P R h1) (fun a : A -> B => fun h0 : term182 A B C P R a => @lem3811107 A B C a R P s h0 h2 h3)). Qed.
Lemma lem3811109 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term313 A B C R s) (h3 : P s) : (P s) = False.
Proof. exact (prop_ext (fun h4 : P s => @lem3811108 A B C R P s h1 h2 h3) (fun h4 : False => @lem3810696 A P s h3)). Qed.
Lemma lem3811110 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (EQ_MP (@lem3811109 A B C R P s h1 h2 h3) (@lem3810696 A P s h3)). Qed.
Lemma lem3811111 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term313 A B C R s) (h3 : P s) : (term313 A B C R s) = False.
Proof. exact (prop_ext (fun h4 : term313 A B C R s => @lem3811110 A B C R P s h1 h2 h3) (fun h4 : False => @lem3810401 A B C R s h2)). Qed.
Lemma lem3811112 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term313 A B C R s) (h3 : P s) : False.
Proof. exact (EQ_MP (@lem3811111 A B C R P s h1 h2 h3) (@lem3810401 A B C R s h2)). Qed.
Lemma lem3811113 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : P s) : term312 A B C R s.
Proof. exact (fun h0 : term313 A B C R s => @lem3811112 A B C R P s h1 h0 h2). Qed.
Lemma lem3811114 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : P s) : term97 A B C R s.
Proof. exact (EQ_MP (@lem3810400 A B C R s) (@lem3811113 A B C R P s h1 h2)). Qed.
Lemma lem3811115 {A B C : Type'} (s : A) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term98 A B C P R s.
Proof. exact (fun h0 : P s => @lem3811114 A B C R P s h1 h0). Qed.
Lemma lem3811116 {A B C : Type'} (s : A) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term321 A B C P R s.
Proof. exact (fun h0 : term16 A B C R => @lem3811115 A B C s P R h1). Qed.
Lemma lem3811117 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : term322 A B C P R s.
Proof. exact (fun h0 : term17 A B C P R => @lem3811116 A B C s P R h0). Qed.
Lemma lem3811122 {A B C : Type'} (R : type1408 A B C) (s : A) : term326 A B C R s.
Proof. exact (fun P : A -> Prop => @lem3811117 A B C P R s). Qed.
Lemma lem3811127 {A B C : Type'} (s : A) : term330 A B C s.
Proof. exact (fun R : type1408 A B C => @lem3811122 A B C R s). Qed.
Lemma lem3811132 {A B C : Type'} : term334 A B C.
Proof. exact (fun s : A => @lem3811127 A B C s). Qed.
Lemma lem3811133 {A B C : Type'} : term333 A B C.
Proof. exact (EQ_MP (@lem3810393 A B C) (@lem3811132 A B C)). Qed.
Lemma lem3811134 {A B C : Type'} (s : A) : term354 A B C s.
Proof. exact (@lem3811133 A B C s). Qed.
Lemma lem3811135 {A B C : Type'} (s : A) : (term354 A B C s) = (term329 A B C s).
Proof. exact (eq_refl (term354 A B C s)). Qed.
Lemma lem3811136 {A B C : Type'} (s : A) : term329 A B C s.
Proof. exact (EQ_MP (@lem3811135 A B C s) (@lem3811134 A B C s)). Qed.
Lemma lem3811137 {A B C : Type'} (s : A) (R : type1408 A B C) : term355 A B C s R.
Proof. exact (@lem3811136 A B C s R). Qed.
Lemma lem3811138 {A B C : Type'} (R : type1408 A B C) (s : A) : (term355 A B C s R) = (term325 A B C R s).
Proof. exact (eq_refl (term355 A B C s R)). Qed.
Lemma lem3811139 {A B C : Type'} (R : type1408 A B C) (s : A) : term325 A B C R s.
Proof. exact (EQ_MP (@lem3811138 A B C R s) (@lem3811137 A B C s R)). Qed.
Lemma lem3811140 {A B C : Type'} (R : type1408 A B C) (s : A) (P : A -> Prop) : term356 A B C R s P.
Proof. exact (@lem3811139 A B C R s P). Qed.
Lemma lem3811141 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : (term356 A B C R s P) = (term314 A B C P R s).
Proof. exact (eq_refl (term356 A B C R s P)). Qed.
Lemma lem3811142 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : term314 A B C P R s.
Proof. exact (EQ_MP (@lem3811141 A B C P R s) (@lem3811140 A B C R s P)). Qed.
Lemma lem3811144 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) : term314 A B C P R s.
Proof. exact (@lem3810119 A B C P R s (@lem3811142 A B C P R s)). Qed.
Lemma lem3811145 {A B C : Type'} (s : A) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) : term320 A B C P R s.
Proof. exact (@lem3811144 A B C P R s (@lem3808395 A B C P R h1)). Qed.
Lemma lem3811146 {A B C : Type'} (s : A) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term319 A B C P R s.
Proof. exact (@lem3811145 A B C s P R h1 (@lem3808394 A B C R h2)). Qed.
Lemma lem3811147 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : term312 A B C R s.
Proof. exact (@lem3811146 A B C s P R h1 h2 (@lem3808396 A P s h3)). Qed.
Lemma lem3811148 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term313 A B C R s) (h4 : P s) : False.
Proof. exact (@lem3811147 A B C R P s h1 h2 h4 (@lem3810103 A B C R s h3)). Qed.
Lemma lem3811149 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term313 A B C R s) (h4 : P s) : (term313 A B C R s) = False.
Proof. exact (prop_ext (fun h5 : term313 A B C R s => @lem3811148 A B C R P s h1 h2 h3 h4) (fun h5 : False => @lem3810103 A B C R s h3)). Qed.
Lemma lem3811150 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : term313 A B C R s) (h4 : P s) : False.
Proof. exact (EQ_MP (@lem3811149 A B C R P s h1 h2 h3 h4) (@lem3810103 A B C R s h3)). Qed.
Lemma lem3811151 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : term312 A B C R s.
Proof. exact (fun h0 : term313 A B C R s => @lem3811150 A B C R P s h1 h2 h0 h3). Qed.
Lemma lem3811152 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : term97 A B C R s.
Proof. exact (EQ_MP (@lem3810102 A B C R s) (@lem3811151 A B C R P s h1 h2 h3)). Qed.
Lemma lem3811153 {A B C : Type'} (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : term308 A B C R s.
Proof. exact (EQ_MP (@lem3810098 A B C R s) (@lem3811152 A B C R P s h1 h2 h3)). Qed.
Lemma lem3811154 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (s : A) (a : B) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) (h4 : (term19 A B C R s) = a) : term23 A B C R s a.
Proof. exact (EQ_MP (@lem3810089 A B C R s a h4) (@lem3811153 A B C R P s h1 h2 h3)). Qed.
Lemma lem3811155 {A B C : Type'} (a : B) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : term357 A B C R s a.
Proof. exact (fun h0 : (term19 A B C R s) = a => @lem3811154 A B C P R s a h1 h2 h3 h0). Qed.
Lemma lem3811156 {A B C : Type'} (a : B) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : term358 A B C R s a.
Proof. exact (conj (@lem3810074 A B C a R P s h1 h2 h3) (@lem3811155 A B C a R P s h1 h2 h3)). Qed.
Lemma lem3811157 {A B C : Type'} (R : type1408 A B C) (s : A) (a : B) : (term358 A B C R s a) = ((term23 A B C R s a) = ((term19 A B C R s) = a)).
Proof. exact (@lem32 (term23 A B C R s a) ((term19 A B C R s) = a)). Qed.
Lemma lem3811158 {A B C : Type'} (a : B) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : (term23 A B C R s a) = ((term19 A B C R s) = a).
Proof. exact (EQ_MP (@lem3811157 A B C R s a) (@lem3811156 A B C a R P s h1 h2 h3)). Qed.
Lemma lem3811159 {A B C : Type'} (a : B) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : (term23 A B C R s a) = ((term18 A B C R s) = a).
Proof. exact (EQ_MP (@lem3808404 A B C R s a) (@lem3811158 A B C a R P s h1 h2 h3)). Qed.
Lemma lem3811160 {A B C : Type'} (a : B) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : (P s) = ((term23 A B C R s a) = ((term18 A B C R s) = a)).
Proof. exact (prop_ext (fun h4 : P s => @lem3811159 A B C a R P s h1 h2 h3) (fun h4 : (term23 A B C R s a) = ((term18 A B C R s) = a) => @lem3808396 A P s h3)). Qed.
Lemma lem3811161 {A B C : Type'} (a : B) (R : type1408 A B C) (P : A -> Prop) (s : A) (h1 : term17 A B C P R) (h2 : term16 A B C R) (h3 : P s) : (term23 A B C R s a) = ((term18 A B C R s) = a).
Proof. exact (EQ_MP (@lem3811160 A B C a R P s h1 h2 h3) (@lem3808396 A P s h3)). Qed.
Lemma lem3811162 {A B C : Type'} (s : A) (a : B) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term359 A B C P R s a.
Proof. exact (fun h0 : P s => @lem3811161 A B C a R P s h1 h2 h0). Qed.
Lemma lem3811167 {A B C : Type'} (s : A) (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term360 A B C P R s.
Proof. exact (fun a : B => @lem3811162 A B C s a P R h1 h2). Qed.
Lemma lem3811172 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term361 A B C P R.
Proof. exact (fun s : A => @lem3811167 A B C s P R h1 h2). Qed.
Lemma lem3811173 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term362 A B C P R.
Proof. exact (ex_intro (term363 A B C P R) (term364 A B C R) (@lem3811172 A B C P R h1 h2)). Qed.
Lemma lem3811174 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term15 A B C P R) : term16 A B C R.
Proof. exact (proj2 (@lem3808393 A B C P R h1)). Qed.
Lemma lem3811175 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term15 A B C P R) : term17 A B C P R.
Proof. exact (proj1 (@lem3808393 A B C P R h1)). Qed.
Lemma lem3811176 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : (term16 A B C R) = (term362 A B C P R).
Proof. exact (prop_ext (fun h3 : term16 A B C R => @lem3811173 A B C P R h1 h2) (fun h3 : term362 A B C P R => @lem3808394 A B C R h2)). Qed.
Lemma lem3811177 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term362 A B C P R.
Proof. exact (EQ_MP (@lem3811176 A B C P R h1 h2) (@lem3808394 A B C R h2)). Qed.
Lemma lem3811178 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : (term17 A B C P R) = (term362 A B C P R).
Proof. exact (prop_ext (fun h3 : term17 A B C P R => @lem3811177 A B C P R h1 h2) (fun h3 : term362 A B C P R => @lem3808395 A B C P R h1)). Qed.
Lemma lem3811179 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term16 A B C R) : term362 A B C P R.
Proof. exact (EQ_MP (@lem3811178 A B C P R h1 h2) (@lem3808395 A B C P R h1)). Qed.
Lemma lem3811180 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term15 A B C P R) : (term16 A B C R) = (term362 A B C P R).
Proof. exact (prop_ext (fun h3 : term16 A B C R => @lem3811179 A B C P R h1 h3) (fun h3 : term362 A B C P R => @lem3811174 A B C P R h2)). Qed.
Lemma lem3811181 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term17 A B C P R) (h2 : term15 A B C P R) : term362 A B C P R.
Proof. exact (EQ_MP (@lem3811180 A B C P R h1 h2) (@lem3811174 A B C P R h2)). Qed.
Lemma lem3811182 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term15 A B C P R) : (term17 A B C P R) = (term362 A B C P R).
Proof. exact (prop_ext (fun h2 : term17 A B C P R => @lem3811181 A B C P R h2 h1) (fun h2 : term362 A B C P R => @lem3811175 A B C P R h1)). Qed.
Lemma lem3811183 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) (h1 : term15 A B C P R) : term362 A B C P R.
Proof. exact (EQ_MP (@lem3811182 A B C P R h1) (@lem3811175 A B C P R h1)). Qed.
Lemma lem3811184 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : term365 A B C P R.
Proof. exact (fun h0 : term15 A B C P R => @lem3811183 A B C P R h0). Qed.
Lemma lem3811189 {A B C : Type'} (P : A -> Prop) : term366 A B C P.
Proof. exact (fun R : type1408 A B C => @lem3811184 A B C P R). Qed.
Lemma lem3811194 {A B C : Type'} : term367 A B C.
Proof. exact (fun P : A -> Prop => @lem3811189 A B C P). Qed.
