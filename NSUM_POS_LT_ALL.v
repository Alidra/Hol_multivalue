Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_POS_LT_ALL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import NSUM_POS_LT_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem6958329 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6958330 {A : Type'} (f : A -> nat) (h1 : term0 A) : term1 A f.
Proof. exact (@lem6958329 A h1 f). Qed.
Lemma lem6958331 {A : Type'} (f : A -> nat) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem6958332 {A : Type'} (f : A -> nat) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem6958331 A f) (@lem6958330 A f h1)). Qed.
Lemma lem6958333 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term0 A) : term3 A f s.
Proof. exact (@lem6958332 A f h1 s). Qed.
Lemma lem6958334 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term3 A f s) = (term4 A s f).
Proof. exact (eq_refl (term3 A f s)). Qed.
Lemma lem6958335 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term0 A) : term4 A s f.
Proof. exact (EQ_MP (@lem6958334 A s f) (@lem6958333 A f s h1)). Qed.
Lemma lem6958336 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term5 A s f) : term5 A s f.
Proof. exact (h1). Qed.
Lemma lem6958337 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term0 A) (h2 : term5 A s f) : term6 A s f.
Proof. exact (@lem6958335 A s f h1 (@lem6958336 A s f h2)). Qed.
Lemma lem6958338 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term5 A s f) : term7 A s f.
Proof. exact (fun h0 : term0 A => @lem6958337 A s f h0 h1). Qed.
Lemma lem6958339 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6958340 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term0 A) (h2 : term5 A s f) : term6 A s f.
Proof. exact (@lem6958338 A s f h2 (@lem6958339 A h1)). Qed.
Lemma lem6958341 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term0 A) : term4 A s f.
Proof. exact (fun h0 : term5 A s f => @lem6958340 A s f h1 h0). Qed.
Lemma lem6958342 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term8 A s.
Proof. exact (fun f : A -> nat => @lem6958341 A s f h1). Qed.
Lemma lem6958343 {A : Type'} (h1 : term0 A) : term9 A.
Proof. exact (fun s : A -> Prop => @lem6958342 A s h1). Qed.
Lemma lem6958344 {A : Type'} : term10 A.
Proof. exact (fun h0 : term0 A => @lem6958343 A h0). Qed.
Lemma lem6958345 {A : Type'} : term9 A.
Proof. exact (@lem6958344 A (@lem6958318 A)). Qed.
Lemma lem6958346 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem6958345 A s). Qed.
Lemma lem6958347 {A : Type'} (s : A -> Prop) : (term11 A s) = (term8 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem6958348 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem6958347 A s) (@lem6958346 A s)). Qed.
Lemma lem6958349 {A : Type'} (s : A -> Prop) (f : A -> nat) : term12 A s f.
Proof. exact (@lem6958348 A s f). Qed.
Lemma lem6958350 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term12 A s f) = (term4 A s f).
Proof. exact (eq_refl (term12 A s f)). Qed.
Lemma lem6958352 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term13 A s f) : term13 A s f.
Proof. exact (h1). Qed.
Lemma lem6958353 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term14 A s f) : term14 A s f.
Proof. exact (h1). Qed.
Lemma lem6958354 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6958355 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term15 A s f.
Proof. exact (h1). Qed.
Lemma lem6958356 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem6958358 {A : Type'} (s : A -> Prop) (f : A -> nat) : term4 A s f.
Proof. exact (EQ_MP (@lem6958350 A s f) (@lem6958349 A s f)). Qed.
Lemma lem6958359 {A : Type'} (s : A -> Prop) (f : A -> nat) : term4 A s f.
Proof. exact (@lem6958358 A s f). Qed.
Lemma lem6958361 (p : Prop) : p = (term17 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6958362 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term5 A s f) = (term18 A s f).
Proof. exact (@lem6958361 (term5 A s f)). Qed.
Lemma lem6958363 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term18 A s f) = (term5 A s f).
Proof. exact (SYM (@lem6958362 A s f)). Qed.
Lemma lem6958364 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term19 A s f) : term19 A s f.
Proof. exact (h1). Qed.
Lemma lem6958365 {A : Type'} : term20 A.
Proof. exact (@lem3216368 A). Qed.
Lemma lem6958370 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term21 A s f) : term21 A s f.
Proof. exact (h1). Qed.
Lemma lem6958371 {A : Type'} (s : A -> Prop) (f : A -> nat) : term22 A s f.
Proof. exact (fun h0 : term21 A s f => @lem6958370 A s f h0). Qed.
Lemma lem6958372 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term22 A s f) : term22 A s f.
Proof. exact (h1). Qed.
Lemma lem6958373 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term21 A s f) : term21 A s f.
Proof. exact (h1). Qed.
Lemma lem6958374 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term21 A s f) (h2 : term22 A s f) : term21 A s f.
Proof. exact (@lem6958372 A s f h2 (@lem6958373 A s f h1)). Qed.
Lemma lem6958375 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term21 A s f) : term23 A s f.
Proof. exact (fun h0 : term22 A s f => @lem6958374 A s f h1 h0). Qed.
Lemma lem6958376 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term22 A s f) : term22 A s f.
Proof. exact (h1). Qed.
Lemma lem6958377 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term21 A s f) (h2 : term22 A s f) : term21 A s f.
Proof. exact (@lem6958375 A s f h1 (@lem6958376 A s f h2)). Qed.
Lemma lem6958378 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term22 A s f) : term22 A s f.
Proof. exact (fun h0 : term21 A s f => @lem6958377 A s f h0 h1). Qed.
Lemma lem6958379 {A : Type'} (s : A -> Prop) (f : A -> nat) : term24 A s f.
Proof. exact (fun h0 : term22 A s f => @lem6958378 A s f h0). Qed.
Lemma lem6958382 {A : Type'} (s : A -> Prop) (f : A -> nat) : term22 A s f.
Proof. exact (@lem6958379 A s f (@lem6958371 A s f)). Qed.
Lemma lem6958383 {A : Type'} (s : A -> Prop) (f : A -> nat) : term22 A s f.
Proof. exact (@lem6958382 A s f). Qed.
Lemma lem6958471 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6958472 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem6958471 (term20 A)). Qed.
Lemma lem6958481 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem6958482 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem6958481) (@lem6958472 A)). Qed.
Lemma lem6958485 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term30 A s f) = (term30 A s f).
Proof. exact (eq_refl (term30 A s f)). Qed.
Lemma lem6958486 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term31 A s f) = (term32 A s f).
Proof. exact (MK_COMB (@lem6958485 A s f) (@lem6958482 A)). Qed.
Lemma lem6958489 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term33 A s f) = (term33 A s f).
Proof. exact (eq_refl (term33 A s f)). Qed.
Lemma lem6958490 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term34 A s f) = (term35 A s f).
Proof. exact (MK_COMB (@lem6958489 A s f) (@lem6958486 A s f)). Qed.
Lemma lem6958493 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (eq_refl (term36 A s)). Qed.
Lemma lem6958494 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term37 A s f) = (term38 A s f).
Proof. exact (MK_COMB (@lem6958493 A s) (@lem6958490 A s f)). Qed.
Lemma lem6958497 {A : Type'} (s : A -> Prop) : (term39 A s) = (term39 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem6958498 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term21 A s f) = (term40 A s f).
Proof. exact (MK_COMB (@lem6958497 A s) (@lem6958494 A s f)). Qed.
Lemma lem6958501 {A : Type'} (f : A -> nat) : (term41 A f) = (term42 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6958498 A s f)). Qed.
Lemma lem6958502 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6958503 {A : Type'} (f : A -> nat) : (term43 A f) = (term44 A f).
Proof. exact (MK_COMB (@lem6958502 A) (@lem6958501 A f)). Qed.
Lemma lem6958508 {A : Type'} : (term45 A) = (term46 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6958503 A f)). Qed.
Lemma lem6958509 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6958518 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (MK_COMB (@lem6958509 A) (@lem6958508 A)). Qed.
Lemma lem6958521 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem6958522 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6958523 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (fun_ext (fun x : A => @lem6958522 A x s)). Qed.
Lemma lem6958524 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6958525 {A : Type'} (s : A -> Prop) : (term50 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem6958524 A) (@lem6958523 A s)). Qed.
Lemma lem6958526 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6958527 {A : Type'} (s : A -> Prop) : (term51 A s) = (term51 A s).
Proof. exact (MK_COMB (@lem6958526) (@lem6958525 A s)). Qed.
Lemma lem6958528 {A : Type'} (s : A -> Prop) : ((term50 A s) = (term16 A s)) = ((term50 A s) = (term16 A s)).
Proof. exact (MK_COMB (@lem6958527 A s) (@lem6958521 A s)). Qed.
Lemma lem6958529 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6958528 A s)). Qed.
Lemma lem6958530 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6958531 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem6958530 A) (@lem6958529 A)). Qed.
Lemma lem6958532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6958533 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem6958532) (@lem6958531 A)). Qed.
Lemma lem6958538 (x : real) (y : real) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem6958539 (x : real) : (term54 x) = (term54 x).
Proof. exact (fun_ext (fun y : real => @lem6958538 x y)). Qed.
Lemma lem6958540 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6958541 (x : real) : (term55 x) = (term55 x).
Proof. exact (MK_COMB (@lem6958540) (@lem6958539 x)). Qed.
Lemma lem6958542 : term56 = term56.
Proof. exact (fun_ext (fun x : real => @lem6958541 x)). Qed.
Lemma lem6958543 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6958544 : term57 = term57.
Proof. exact (MK_COMB (@lem6958543) (@lem6958542)). Qed.
Lemma lem6958545 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6958546 : term27 = term27.
Proof. exact (MK_COMB (@lem6958545) (@lem6958544)). Qed.
Lemma lem6958547 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem6958546) (@lem6958533 A)). Qed.
Lemma lem6958552 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term58 A s f x) = (term58 A s f x).
Proof. exact (eq_refl (term58 A s f x)). Qed.
Lemma lem6958553 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term59 A s f) = (term59 A s f).
Proof. exact (fun_ext (fun x : A => @lem6958552 A s f x)). Qed.
Lemma lem6958554 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6958555 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term60 A s f) = (term60 A s f).
Proof. exact (MK_COMB (@lem6958554 A) (@lem6958553 A s f)). Qed.
Lemma lem6958558 {A : Type'} (s : A -> Prop) : (term61 A s) = (term61 A s).
Proof. exact (eq_refl (term61 A s)). Qed.
Lemma lem6958559 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term5 A s f) = (term5 A s f).
Proof. exact (MK_COMB (@lem6958558 A s) (@lem6958555 A s f)). Qed.
Lemma lem6958560 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6958561 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term19 A s f) = (term19 A s f).
Proof. exact (MK_COMB (@lem6958560) (@lem6958559 A s f)). Qed.
Lemma lem6958562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6958563 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term30 A s f) = (term30 A s f).
Proof. exact (MK_COMB (@lem6958562) (@lem6958561 A s f)). Qed.
Lemma lem6958564 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term32 A s f) = (term32 A s f).
Proof. exact (MK_COMB (@lem6958563 A s f) (@lem6958547 A)). Qed.
Lemma lem6958569 {A : Type'} (s : A -> Prop) (f : A -> nat) (i : A) : (term62 A s f i) = (term62 A s f i).
Proof. exact (eq_refl (term62 A s f i)). Qed.
Lemma lem6958570 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term63 A s f) = (term63 A s f).
Proof. exact (fun_ext (fun i : A => @lem6958569 A s f i)). Qed.
Lemma lem6958571 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6958572 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term15 A s f) = (term15 A s f).
Proof. exact (MK_COMB (@lem6958571 A) (@lem6958570 A s f)). Qed.
Lemma lem6958573 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6958574 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term33 A s f) = (term33 A s f).
Proof. exact (MK_COMB (@lem6958573) (@lem6958572 A s f)). Qed.
Lemma lem6958575 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term35 A s f) = (term35 A s f).
Proof. exact (MK_COMB (@lem6958574 A s f) (@lem6958564 A s f)). Qed.
Lemma lem6958580 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (eq_refl (term36 A s)). Qed.
Lemma lem6958581 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term38 A s f) = (term38 A s f).
Proof. exact (MK_COMB (@lem6958580 A s) (@lem6958575 A s f)). Qed.
Lemma lem6958584 {A : Type'} (s : A -> Prop) : (term39 A s) = (term39 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem6958585 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term40 A s f) = (term40 A s f).
Proof. exact (MK_COMB (@lem6958584 A s) (@lem6958581 A s f)). Qed.
Lemma lem6958586 {A : Type'} (f : A -> nat) : (term42 A f) = (term42 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6958585 A s f)). Qed.
Lemma lem6958587 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6958588 {A : Type'} (f : A -> nat) : (term44 A f) = (term44 A f).
Proof. exact (MK_COMB (@lem6958587 A) (@lem6958586 A f)). Qed.
Lemma lem6958589 {A : Type'} : (term46 A) = (term46 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6958588 A f)). Qed.
Lemma lem6958590 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6958591 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (MK_COMB (@lem6958590 A) (@lem6958589 A)). Qed.
Lemma lem6958660 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (TRANS (@lem6958518 A) (@lem6958591 A)). Qed.
Lemma lem6958661 {A : Type'} : (term48 A) = (term47 A).
Proof. exact (SYM (@lem6958660 A)). Qed.
Lemma lem6958664 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term15 A s f.
Proof. exact (h1). Qed.
Lemma lem6958665 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term19 A s f) : term19 A s f.
Proof. exact (h1). Qed.
Lemma lem6958667 {A : Type'} (h1 : term20 A) : term20 A.
Proof. exact (h1). Qed.
Lemma lem6958673 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6958679 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem6958686 {A : Type'} (s : A -> Prop) (f : A -> nat) (i : A) : (term62 A s f i) = (term64 A s f i).
Proof. exact (@lem17265 (@IN A i s) (term65 A f i)). Qed.
Lemma lem6958687 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term63 A s f) = (term66 A s f).
Proof. exact (fun_ext (fun i : A => @lem6958686 A s f i)). Qed.
Lemma lem6958688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6958741 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term15 A s f) = (term67 A s f).
Proof. exact (MK_COMB (@lem6958688 A) (@lem6958687 A s f)). Qed.
Lemma lem6958742 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term67 A s f.
Proof. exact (EQ_MP (@lem6958741 A s f) (@lem6958664 A s f h1)). Qed.
Lemma lem6958750 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term68 A s f x) = (term69 A s f x).
Proof. exact (@lem17045 (@IN A x s) (term65 A f x)). Qed.
Lemma lem6958751 {A : Type'} (P : A -> Prop) : (term70 A P) = (term71 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem6958752 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term72 A s f) = (term73 A s f).
Proof. exact (@lem6958751 A (term59 A s f)). Qed.
Lemma lem6958753 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term74 A s f x) = (term58 A s f x).
Proof. exact (eq_refl (term74 A s f x)). Qed.
Lemma lem6958754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6958755 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term75 A s f x) = (term68 A s f x).
Proof. exact (MK_COMB (@lem6958754) (@lem6958753 A s f x)). Qed.
Lemma lem6958756 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term75 A s f x) = (term69 A s f x).
Proof. exact (TRANS (@lem6958755 A s f x) (@lem6958750 A s f x)). Qed.
Lemma lem6958757 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term76 A s f) = (term77 A s f).
Proof. exact (fun_ext (fun x : A => @lem6958756 A s f x)). Qed.
Lemma lem6958758 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6958759 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term73 A s f) = (term78 A s f).
Proof. exact (MK_COMB (@lem6958758 A) (@lem6958757 A s f)). Qed.
Lemma lem6958760 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term72 A s f) = (term78 A s f).
Proof. exact (TRANS (@lem6958752 A s f) (@lem6958759 A s f)). Qed.
Lemma lem6958762 {A : Type'} (s : A -> Prop) : (term79 A s) = (term79 A s).
Proof. exact (eq_refl (term79 A s)). Qed.
Lemma lem6958763 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term80 A s f) = (term81 A s f).
Proof. exact (MK_COMB (@lem6958762 A s) (@lem6958760 A s f)). Qed.
Lemma lem6958764 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term19 A s f) = (term80 A s f).
Proof. exact (@lem17045 (@FINITE A s) (term60 A s f)). Qed.
Lemma lem6958817 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term19 A s f) = (term81 A s f).
Proof. exact (TRANS (@lem6958764 A s f) (@lem6958763 A s f)). Qed.
Lemma lem6958818 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term19 A s f) : term81 A s f.
Proof. exact (EQ_MP (@lem6958817 A s f) (@lem6958665 A s f h1)). Qed.
Lemma lem6958890 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6958891 {A : Type'} (P : A -> Prop) : (term70 A P) = (term71 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem6958892 {A : Type'} (s : A -> Prop) : (term82 A s) = (term83 A s).
Proof. exact (@lem6958891 A (term49 A s)). Qed.
Lemma lem6958893 {A : Type'} (x : A) (s : A -> Prop) : (term84 A s x) = (@IN A x s).
Proof. exact (eq_refl (term84 A s x)). Qed.
Lemma lem6958894 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6958896 {A : Type'} (x : A) (s : A -> Prop) : (term85 A s x) = (term86 A x s).
Proof. exact (MK_COMB (@lem6958894) (@lem6958893 A x s)). Qed.
Lemma lem6958897 {A : Type'} (s : A -> Prop) : (term87 A s) = (term88 A s).
Proof. exact (fun_ext (fun x : A => @lem6958896 A x s)). Qed.
Lemma lem6958898 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6958899 {A : Type'} (s : A -> Prop) : (term83 A s) = (term89 A s).
Proof. exact (MK_COMB (@lem6958898 A) (@lem6958897 A s)). Qed.
Lemma lem6958900 {A : Type'} (s : A -> Prop) : (term82 A s) = (term89 A s).
Proof. exact (TRANS (@lem6958892 A s) (@lem6958899 A s)). Qed.
Lemma lem6958901 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (fun_ext (fun x : A => @lem6958890 A x s)). Qed.
Lemma lem6958902 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6958903 {A : Type'} (s : A -> Prop) : (term50 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem6958902 A) (@lem6958901 A s)). Qed.
Lemma lem6958904 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem6958907 {A : Type'} (s : A -> Prop) : (term90 A s) = (s = (@EMPTY A)).
Proof. exact (@lem16933 (s = (@EMPTY A))). Qed.
Lemma lem6958908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6958909 {A : Type'} (s : A -> Prop) : (term91 A s) = (term92 A s).
Proof. exact (MK_COMB (@lem6958908) (@lem6958900 A s)). Qed.
Lemma lem6958910 {A : Type'} (s : A -> Prop) : (term93 A s) = (term94 A s).
Proof. exact (MK_COMB (@lem6958909 A s) (@lem6958904 A s)). Qed.
Lemma lem6958911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6958912 {A : Type'} (s : A -> Prop) : (term95 A s) = (term95 A s).
Proof. exact (MK_COMB (@lem6958911) (@lem6958903 A s)). Qed.
Lemma lem6958913 {A : Type'} (s : A -> Prop) : (term96 A s) = (term97 A s).
Proof. exact (MK_COMB (@lem6958912 A s) (@lem6958907 A s)). Qed.
Lemma lem6958914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6958915 {A : Type'} (s : A -> Prop) : (term98 A s) = (term99 A s).
Proof. exact (MK_COMB (@lem6958914) (@lem6958913 A s)). Qed.
Lemma lem6958916 {A : Type'} (s : A -> Prop) : (term100 A s) = (term101 A s).
Proof. exact (MK_COMB (@lem6958915 A s) (@lem6958910 A s)). Qed.
Lemma lem6958917 {A : Type'} (s : A -> Prop) : ((term50 A s) = (term16 A s)) = (term100 A s).
Proof. exact (@lem17784 (term50 A s) (term16 A s)). Qed.
Lemma lem6958918 {A : Type'} (s : A -> Prop) : ((term50 A s) = (term16 A s)) = (term101 A s).
Proof. exact (TRANS (@lem6958917 A s) (@lem6958916 A s)). Qed.
Lemma lem6958919 {A : Type'} : (term52 A) = (term102 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6958918 A s)). Qed.
Lemma lem6958920 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6958921 {A : Type'} : (term20 A) = (term103 A).
Proof. exact (MK_COMB (@lem6958920 A) (@lem6958919 A)). Qed.
Lemma lem6958923 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6958924 {A : Type'} (P : type686 A) (Q : type686 A) : (term106 A P Q) = (term107 A P Q).
Proof. exact (@lem6958923 (A -> Prop) P Q). Qed.
Lemma lem6958925 {A : Type'} : (term108 A) = (term109 A).
Proof. exact (@lem6958924 A (term110 A) (term111 A)). Qed.
Lemma lem6958926 {A : Type'} (s : A -> Prop) : (term112 A s) = (term97 A s).
Proof. exact (eq_refl (term112 A s)). Qed.
Lemma lem6958927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6958928 {A : Type'} (s : A -> Prop) : (term113 A s) = (term99 A s).
Proof. exact (MK_COMB (@lem6958927) (@lem6958926 A s)). Qed.
Lemma lem6958929 {A : Type'} (s : A -> Prop) : (term114 A s) = (term94 A s).
Proof. exact (eq_refl (term114 A s)). Qed.
Lemma lem6958930 {A : Type'} (s : A -> Prop) : (term115 A s) = (term101 A s).
Proof. exact (MK_COMB (@lem6958928 A s) (@lem6958929 A s)). Qed.
Lemma lem6958931 {A : Type'} : (term116 A) = (term102 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6958930 A s)). Qed.
Lemma lem6958932 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6958933 {A : Type'} : (term108 A) = (term103 A).
Proof. exact (MK_COMB (@lem6958932 A) (@lem6958931 A)). Qed.
Lemma lem6958934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6958935 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem6958934) (@lem6958933 A)). Qed.
Lemma lem6958936 {A : Type'} (s : A -> Prop) : (term112 A s) = (term97 A s).
Proof. exact (eq_refl (term112 A s)). Qed.
Lemma lem6958937 {A : Type'} : (term119 A) = (term110 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6958936 A s)). Qed.
Lemma lem6958938 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6958939 {A : Type'} : (term120 A) = (term121 A).
Proof. exact (MK_COMB (@lem6958938 A) (@lem6958937 A)). Qed.
Lemma lem6958940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6958941 {A : Type'} : (term122 A) = (term123 A).
Proof. exact (MK_COMB (@lem6958940) (@lem6958939 A)). Qed.
Lemma lem6958942 {A : Type'} (s : A -> Prop) : (term114 A s) = (term94 A s).
Proof. exact (eq_refl (term114 A s)). Qed.
Lemma lem6958943 {A : Type'} : (term124 A) = (term111 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6958942 A s)). Qed.
Lemma lem6958944 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6958945 {A : Type'} : (term125 A) = (term126 A).
Proof. exact (MK_COMB (@lem6958944 A) (@lem6958943 A)). Qed.
Lemma lem6958946 {A : Type'} : (term109 A) = (term127 A).
Proof. exact (MK_COMB (@lem6958941 A) (@lem6958945 A)). Qed.
Lemma lem6958947 {A : Type'} : ((term108 A) = (term109 A)) = ((term103 A) = (term127 A)).
Proof. exact (MK_COMB (@lem6958935 A) (@lem6958946 A)). Qed.
Lemma lem6958948 {A : Type'} : (term103 A) = (term127 A).
Proof. exact (EQ_MP (@lem6958947 A) (@lem6958925 A)). Qed.
Lemma lem6959054 {A : Type'} (P : A -> Prop) (Q : Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6959055 {A : Type'} (P : A -> Prop) (Q : Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (@lem6959054 A P Q). Qed.
Lemma lem6959056 {A : Type'} (s : A -> Prop) : (term130 A s) = (term131 A s).
Proof. exact (@lem6959055 A (term49 A s) (s = (@EMPTY A))). Qed.
Lemma lem6959057 {A : Type'} (x : A) (s : A -> Prop) : (term84 A s x) = (@IN A x s).
Proof. exact (eq_refl (term84 A s x)). Qed.
Lemma lem6959058 {A : Type'} (s : A -> Prop) : (term132 A s) = (term49 A s).
Proof. exact (fun_ext (fun x : A => @lem6959057 A x s)). Qed.
Lemma lem6959059 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6959060 {A : Type'} (s : A -> Prop) : (term133 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem6959059 A) (@lem6959058 A s)). Qed.
Lemma lem6959061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6959062 {A : Type'} (s : A -> Prop) : (term134 A s) = (term95 A s).
Proof. exact (MK_COMB (@lem6959061) (@lem6959060 A s)). Qed.
Lemma lem6959063 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem6959064 {A : Type'} (s : A -> Prop) : (term130 A s) = (term97 A s).
Proof. exact (MK_COMB (@lem6959062 A s) (@lem6959063 A s)). Qed.
Lemma lem6959065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6959066 {A : Type'} (s : A -> Prop) : (term135 A s) = (term136 A s).
Proof. exact (MK_COMB (@lem6959065) (@lem6959064 A s)). Qed.
Lemma lem6959067 {A : Type'} (x : A) (s : A -> Prop) : (term84 A s x) = (@IN A x s).
Proof. exact (eq_refl (term84 A s x)). Qed.
Lemma lem6959068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6959069 {A : Type'} (x : A) (s : A -> Prop) : (term137 A s x) = (term138 A x s).
Proof. exact (MK_COMB (@lem6959068) (@lem6959067 A x s)). Qed.
Lemma lem6959070 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem6959071 {A : Type'} (x : A) (s : A -> Prop) : (term139 A x s) = (term140 A x s).
Proof. exact (MK_COMB (@lem6959069 A x s) (@lem6959070 A s)). Qed.
Lemma lem6959072 {A : Type'} (s : A -> Prop) : (term141 A s) = (term142 A s).
Proof. exact (fun_ext (fun x : A => @lem6959071 A x s)). Qed.
Lemma lem6959073 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6959074 {A : Type'} (s : A -> Prop) : (term131 A s) = (term143 A s).
Proof. exact (MK_COMB (@lem6959073 A) (@lem6959072 A s)). Qed.
Lemma lem6959075 {A : Type'} (s : A -> Prop) : ((term130 A s) = (term131 A s)) = ((term97 A s) = (term143 A s)).
Proof. exact (MK_COMB (@lem6959066 A s) (@lem6959074 A s)). Qed.
Lemma lem6959076 {A : Type'} (s : A -> Prop) : (term97 A s) = (term143 A s).
Proof. exact (EQ_MP (@lem6959075 A s) (@lem6959056 A s)). Qed.
Lemma lem6959077 {A : Type'} : (term110 A) = (term144 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6959076 A s)). Qed.
Lemma lem6959078 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6959079 {A : Type'} : (term121 A) = (term145 A).
Proof. exact (MK_COMB (@lem6959078 A) (@lem6959077 A)). Qed.
Lemma lem6959081 {A B : Type'} (P : type1413 A B) : (term146 A B P) = (term147 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6959082 {A : Type'} (P : type672 A) : (term148 A P) = (term149 A P).
Proof. exact (@lem6959081 (A -> Prop) A P). Qed.
Lemma lem6959083 {A : Type'} : (term150 A) = (term151 A).
Proof. exact (@lem6959082 A (term152 A)). Qed.
Lemma lem6959084 {A : Type'} (s : A -> Prop) : (term153 A s) = (term142 A s).
Proof. exact (eq_refl (term153 A s)). Qed.
Lemma lem6959085 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6959086 {A : Type'} (s : A -> Prop) (x : A) : (term154 A s x) = (term155 A s x).
Proof. exact (MK_COMB (@lem6959084 A s) (@lem6959085 A x)). Qed.
Lemma lem6959087 {A : Type'} (x : A) (s : A -> Prop) : (term155 A s x) = (term140 A x s).
Proof. exact (eq_refl (term155 A s x)). Qed.
Lemma lem6959088 {A : Type'} (x : A) (s : A -> Prop) : (term154 A s x) = (term140 A x s).
Proof. exact (TRANS (@lem6959086 A s x) (@lem6959087 A x s)). Qed.
Lemma lem6959089 {A : Type'} (s : A -> Prop) : (term156 A s) = (term142 A s).
Proof. exact (fun_ext (fun x : A => @lem6959088 A x s)). Qed.
Lemma lem6959090 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6959091 {A : Type'} (s : A -> Prop) : (term157 A s) = (term143 A s).
Proof. exact (MK_COMB (@lem6959090 A) (@lem6959089 A s)). Qed.
Lemma lem6959092 {A : Type'} : (term158 A) = (term144 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6959091 A s)). Qed.
Lemma lem6959093 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6959094 {A : Type'} : (term150 A) = (term145 A).
Proof. exact (MK_COMB (@lem6959093 A) (@lem6959092 A)). Qed.
Lemma lem6959095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6959096 {A : Type'} : (term159 A) = (term160 A).
Proof. exact (MK_COMB (@lem6959095) (@lem6959094 A)). Qed.
Lemma lem6959097 {A : Type'} (s : A -> Prop) : (term153 A s) = (term142 A s).
Proof. exact (eq_refl (term153 A s)). Qed.
Lemma lem6959098 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6959099 {A : Type'} (x : type684 A) (s : A -> Prop) : (term161 A x s) = (term162 A x s).
Proof. exact (MK_COMB (@lem6959097 A s) (@lem6959098 A x s)). Qed.
Lemma lem6959100 {A : Type'} (x : type684 A) (s : A -> Prop) : (term162 A x s) = (term163 A x s).
Proof. exact (eq_refl (term162 A x s)). Qed.
Lemma lem6959101 {A : Type'} (x : type684 A) (s : A -> Prop) : (term161 A x s) = (term163 A x s).
Proof. exact (TRANS (@lem6959099 A x s) (@lem6959100 A x s)). Qed.
Lemma lem6959102 {A : Type'} (x : type684 A) : (term164 A x) = (term165 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6959101 A x s)). Qed.
Lemma lem6959103 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6959104 {A : Type'} (x : type684 A) : (term166 A x) = (term167 A x).
Proof. exact (MK_COMB (@lem6959103 A) (@lem6959102 A x)). Qed.
Lemma lem6959105 {A : Type'} : (term168 A) = (term169 A).
Proof. exact (fun_ext (fun x : type684 A => @lem6959104 A x)). Qed.
Lemma lem6959106 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6959107 {A : Type'} : (term151 A) = (term170 A).
Proof. exact (MK_COMB (@lem6959106 A) (@lem6959105 A)). Qed.
Lemma lem6959108 {A : Type'} : ((term150 A) = (term151 A)) = ((term145 A) = (term170 A)).
Proof. exact (MK_COMB (@lem6959096 A) (@lem6959107 A)). Qed.
Lemma lem6959109 {A : Type'} : (term145 A) = (term170 A).
Proof. exact (EQ_MP (@lem6959108 A) (@lem6959083 A)). Qed.
Lemma lem6959110 {A : Type'} : (term121 A) = (term170 A).
Proof. exact (TRANS (@lem6959079 A) (@lem6959109 A)). Qed.
Lemma lem6959111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6959112 {A : Type'} : (term123 A) = (term171 A).
Proof. exact (MK_COMB (@lem6959111) (@lem6959110 A)). Qed.
Lemma lem6959113 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (eq_refl (term126 A)). Qed.
Lemma lem6959114 {A : Type'} : (term127 A) = (term172 A).
Proof. exact (MK_COMB (@lem6959112 A) (@lem6959113 A)). Qed.
Lemma lem6959116 {A : Type'} (P : A -> Prop) (Q : Prop) : (term173 A P Q) = (term174 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6959117 {A : Type'} (P : type162 A) (Q : Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (@lem6959116 (type684 A) P Q). Qed.
Lemma lem6959118 {A : Type'} : (term177 A) = (term178 A).
Proof. exact (@lem6959117 A (term169 A) (term126 A)). Qed.
Lemma lem6959119 {A : Type'} (x : type684 A) : (term179 A x) = (term167 A x).
Proof. exact (eq_refl (term179 A x)). Qed.
Lemma lem6959120 {A : Type'} : (term180 A) = (term169 A).
Proof. exact (fun_ext (fun x : type684 A => @lem6959119 A x)). Qed.
Lemma lem6959121 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6959122 {A : Type'} : (term181 A) = (term170 A).
Proof. exact (MK_COMB (@lem6959121 A) (@lem6959120 A)). Qed.
Lemma lem6959123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6959124 {A : Type'} : (term182 A) = (term171 A).
Proof. exact (MK_COMB (@lem6959123) (@lem6959122 A)). Qed.
Lemma lem6959125 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (eq_refl (term126 A)). Qed.
Lemma lem6959126 {A : Type'} : (term177 A) = (term172 A).
Proof. exact (MK_COMB (@lem6959124 A) (@lem6959125 A)). Qed.
Lemma lem6959127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6959128 {A : Type'} : (term183 A) = (term184 A).
Proof. exact (MK_COMB (@lem6959127) (@lem6959126 A)). Qed.
Lemma lem6959129 {A : Type'} (x : type684 A) : (term179 A x) = (term167 A x).
Proof. exact (eq_refl (term179 A x)). Qed.
Lemma lem6959130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6959131 {A : Type'} (x : type684 A) : (term185 A x) = (term186 A x).
Proof. exact (MK_COMB (@lem6959130) (@lem6959129 A x)). Qed.
Lemma lem6959132 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (eq_refl (term126 A)). Qed.
Lemma lem6959133 {A : Type'} (x : type684 A) : (term187 A x) = (term188 A x).
Proof. exact (MK_COMB (@lem6959131 A x) (@lem6959132 A)). Qed.
Lemma lem6959134 {A : Type'} : (term189 A) = (term190 A).
Proof. exact (fun_ext (fun x : type684 A => @lem6959133 A x)). Qed.
Lemma lem6959135 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6959136 {A : Type'} : (term178 A) = (term191 A).
Proof. exact (MK_COMB (@lem6959135 A) (@lem6959134 A)). Qed.
Lemma lem6959137 {A : Type'} : ((term177 A) = (term178 A)) = ((term172 A) = (term191 A)).
Proof. exact (MK_COMB (@lem6959128 A) (@lem6959136 A)). Qed.
Lemma lem6959138 {A : Type'} : (term172 A) = (term191 A).
Proof. exact (EQ_MP (@lem6959137 A) (@lem6959118 A)). Qed.
Lemma lem6959139 {A : Type'} : (term127 A) = (term191 A).
Proof. exact (TRANS (@lem6959114 A) (@lem6959138 A)). Qed.
Lemma lem6959140 {A : Type'} : (term103 A) = (term191 A).
Proof. exact (TRANS (@lem6958948 A) (@lem6959139 A)). Qed.
Lemma lem6959141 {A : Type'} : (term20 A) = (term191 A).
Proof. exact (TRANS (@lem6958921 A) (@lem6959140 A)). Qed.
Lemma lem6959142 {A : Type'} (h1 : term20 A) : term191 A.
Proof. exact (EQ_MP (@lem6959141 A) (@lem6958667 A h1)). Qed.
Lemma lem6959143 {A : Type'} (x : type684 A) (h1 : term188 A x) : term188 A x.
Proof. exact (h1). Qed.
Lemma lem6959147 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6959155 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem6959174 {A : Type'} (s : A -> Prop) (f : A -> nat) (i : A) : (term64 A s f i) = (term64 A s f i).
Proof. exact (eq_refl (term64 A s f i)). Qed.
Lemma lem6959175 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term66 A s f) = (term66 A s f).
Proof. exact (fun_ext (fun i : A => @lem6959174 A s f i)). Qed.
Lemma lem6959176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6959177 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term67 A s f) = (term67 A s f).
Proof. exact (MK_COMB (@lem6959176 A) (@lem6959175 A s f)). Qed.
Lemma lem6959178 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term67 A s f.
Proof. exact (EQ_MP (@lem6959177 A s f) (@lem6958742 A s f h1)). Qed.
Lemma lem6959199 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term69 A s f x) = (term69 A s f x).
Proof. exact (eq_refl (term69 A s f x)). Qed.
Lemma lem6959200 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term77 A s f) = (term77 A s f).
Proof. exact (fun_ext (fun x : A => @lem6959199 A s f x)). Qed.
Lemma lem6959201 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6959202 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term78 A s f) = (term78 A s f).
Proof. exact (MK_COMB (@lem6959201 A) (@lem6959200 A s f)). Qed.
Lemma lem6959209 {A : Type'} (s : A -> Prop) : (term79 A s) = (term79 A s).
Proof. exact (eq_refl (term79 A s)). Qed.
Lemma lem6959210 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term81 A s f) = (term81 A s f).
Proof. exact (MK_COMB (@lem6959209 A s) (@lem6959202 A s f)). Qed.
Lemma lem6959211 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term19 A s f) : term81 A s f.
Proof. exact (EQ_MP (@lem6959210 A s f) (@lem6958818 A s f h1)). Qed.
Lemma lem6959240 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem6959247 {A : Type'} (x : A) (s : A -> Prop) : (term86 A x s) = (term86 A x s).
Proof. exact (eq_refl (term86 A x s)). Qed.
Lemma lem6959248 {A : Type'} (s : A -> Prop) : (term88 A s) = (term88 A s).
Proof. exact (fun_ext (fun x : A => @lem6959247 A x s)). Qed.
Lemma lem6959249 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6959250 {A : Type'} (s : A -> Prop) : (term89 A s) = (term89 A s).
Proof. exact (MK_COMB (@lem6959249 A) (@lem6959248 A s)). Qed.
Lemma lem6959251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6959252 {A : Type'} (s : A -> Prop) : (term92 A s) = (term92 A s).
Proof. exact (MK_COMB (@lem6959251) (@lem6959250 A s)). Qed.
Lemma lem6959253 {A : Type'} (s : A -> Prop) : (term94 A s) = (term94 A s).
Proof. exact (MK_COMB (@lem6959252 A s) (@lem6959240 A s)). Qed.
Lemma lem6959254 {A : Type'} : (term111 A) = (term111 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6959253 A s)). Qed.
Lemma lem6959255 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6959256 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (MK_COMB (@lem6959255 A) (@lem6959254 A)). Qed.
Lemma lem6959271 {A : Type'} (x : type684 A) (s : A -> Prop) : (term163 A x s) = (term163 A x s).
Proof. exact (eq_refl (term163 A x s)). Qed.
Lemma lem6959272 {A : Type'} (x : type684 A) : (term165 A x) = (term165 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6959271 A x s)). Qed.
Lemma lem6959273 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6959274 {A : Type'} (x : type684 A) : (term167 A x) = (term167 A x).
Proof. exact (MK_COMB (@lem6959273 A) (@lem6959272 A x)). Qed.
Lemma lem6959275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6959276 {A : Type'} (x : type684 A) : (term186 A x) = (term186 A x).
Proof. exact (MK_COMB (@lem6959275) (@lem6959274 A x)). Qed.
Lemma lem6959277 {A : Type'} (x : type684 A) : (term188 A x) = (term188 A x).
Proof. exact (MK_COMB (@lem6959276 A x) (@lem6959256 A)). Qed.
Lemma lem6959278 {A : Type'} (x : type684 A) (h1 : term188 A x) : term188 A x.
Proof. exact (EQ_MP (@lem6959277 A x) (@lem6959143 A x h1)). Qed.
Lemma lem6959280 {A : Type'} (x : type684 A) (h1 : term188 A x) : term167 A x.
Proof. exact (proj1 (@lem6959278 A x h1)). Qed.
Lemma lem6959282 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term78 A s f) : term78 A s f.
Proof. exact (h1). Qed.
Lemma lem6959286 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6959378 {A : Type'} (s : A -> Prop) (h1 : term192 A s) : term192 A s.
Proof. exact (h1). Qed.
Lemma lem6959386 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem6959394 {A : Type'} (s : A -> Prop) (f : A -> nat) (i : A) : (term64 A s f i) = (term64 A s f i).
Proof. exact (eq_refl (term64 A s f i)). Qed.
Lemma lem6959395 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term66 A s f) = (term66 A s f).
Proof. exact (fun_ext (fun i : A => @lem6959394 A s f i)). Qed.
Lemma lem6959396 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6959398 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term67 A s f) = (term67 A s f).
Proof. exact (MK_COMB (@lem6959396 A) (@lem6959395 A s f)). Qed.
Lemma lem6959399 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term67 A s f.
Proof. exact (EQ_MP (@lem6959398 A s f) (@lem6959178 A s f h1)). Qed.
Lemma lem6959423 {A : Type'} (x : type684 A) (s : A -> Prop) : (term163 A x s) = (term163 A x s).
Proof. exact (eq_refl (term163 A x s)). Qed.
Lemma lem6959424 {A : Type'} (x : type684 A) : (term165 A x) = (term165 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6959423 A x s)). Qed.
Lemma lem6959425 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6959427 {A : Type'} (x : type684 A) : (term167 A x) = (term167 A x).
Proof. exact (MK_COMB (@lem6959425 A) (@lem6959424 A x)). Qed.
Lemma lem6959428 {A : Type'} (x : type684 A) (h1 : term188 A x) : term167 A x.
Proof. exact (EQ_MP (@lem6959427 A x) (@lem6959280 A x h1)). Qed.
Lemma lem6959478 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term69 A s f x) = (term69 A s f x).
Proof. exact (eq_refl (term69 A s f x)). Qed.
Lemma lem6959479 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term77 A s f) = (term77 A s f).
Proof. exact (fun_ext (fun x : A => @lem6959478 A s f x)). Qed.
Lemma lem6959480 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6959482 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term78 A s f) = (term78 A s f).
Proof. exact (MK_COMB (@lem6959480 A) (@lem6959479 A s f)). Qed.
Lemma lem6959483 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term78 A s f) : term78 A s f.
Proof. exact (EQ_MP (@lem6959482 A s f) (@lem6959282 A s f h1)). Qed.
Lemma lem6959502 {A : Type'} (_92674 : A) (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term193 A s f _92674.
Proof. exact (@lem6959399 A s f h1 _92674). Qed.
Lemma lem6959503 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92674 : A) : (term193 A s f _92674) = (term64 A s f _92674).
Proof. exact (eq_refl (term193 A s f _92674)). Qed.
Lemma lem6959511 {A : Type'} (_92677 : A -> Prop) (x : type684 A) (h1 : term188 A x) : term194 A x _92677.
Proof. exact (@lem6959428 A x h1 _92677). Qed.
Lemma lem6959512 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : (term194 A x _92677) = (term163 A x _92677).
Proof. exact (eq_refl (term194 A x _92677)). Qed.
Lemma lem6959520 {A : Type'} (_92680 : A) (s : A -> Prop) (f : A -> nat) (h1 : term78 A s f) : term195 A s f _92680.
Proof. exact (@lem6959483 A s f h1 _92680). Qed.
Lemma lem6959521 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92680 : A) : (term195 A s f _92680) = (term69 A s f _92680).
Proof. exact (eq_refl (term195 A s f _92680)). Qed.
Lemma lem6959524 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6959552 {A : Type'} (s : A -> Prop) (h1 : term192 A s) : term192 A s.
Proof. exact (h1). Qed.
Lemma lem6959556 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem6959562 {A : Type'} (_92674 : A) (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term64 A s f _92674.
Proof. exact (EQ_MP (@lem6959503 A s f _92674) (@lem6959502 A _92674 s f h1)). Qed.
Lemma lem6959574 {A : Type'} (_92677 : A -> Prop) (x : type684 A) (h1 : term188 A x) : term163 A x _92677.
Proof. exact (EQ_MP (@lem6959512 A x _92677) (@lem6959511 A _92677 x h1)). Qed.
Lemma lem6959586 {A : Type'} (_92680 : A) (s : A -> Prop) (f : A -> nat) (h1 : term78 A s f) : term69 A s f _92680.
Proof. exact (EQ_MP (@lem6959521 A s f _92680) (@lem6959520 A _92680 s f h1)). Qed.
Lemma lem6959708 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6959709 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term196 A s.
Proof. exact (fun h0 : term192 A s => @lem6959708 A s h1). Qed.
Lemma lem6959711 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6959712 {A : Type'} (s : A -> Prop) : (term196 A s) = (@FINITE A s).
Proof. exact (@lem6959711 (@FINITE A s)). Qed.
Lemma lem6959713 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6959712 A s) (@lem6959709 A s h1)). Qed.
Lemma lem6959716 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6959718 {A : Type'} (s : A -> Prop) : (term192 A s) = (term198 A s).
Proof. exact (@lem6959716 (@FINITE A s)). Qed.
Lemma lem6959721 {A : Type'} (s : A -> Prop) (h1 : term192 A s) : term198 A s.
Proof. exact (EQ_MP (@lem6959718 A s) (@lem6959552 A s h1)). Qed.
Lemma lem6959724 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : False.
Proof. exact (@lem6959721 A s h2 (@lem6959713 A s h1)). Qed.
Lemma lem6959725 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : term199.
Proof. exact (fun h0 : ~ False => @lem6959724 A s h1 h2). Qed.
Lemma lem6959727 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6959728 : term199 = False.
Proof. exact (@lem6959727 False). Qed.
Lemma lem6959729 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : False.
Proof. exact (EQ_MP (@lem6959728) (@lem6959725 A s h1 h2)). Qed.
Lemma lem6959852 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem6959853 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term200 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem6959852 A s h1). Qed.
Lemma lem6959855 (p : Prop) : (term201 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6959856 {A : Type'} (s : A -> Prop) : (term200 A s) = (term16 A s).
Proof. exact (@lem6959855 (s = (@EMPTY A))). Qed.
Lemma lem6959857 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (EQ_MP (@lem6959856 A s) (@lem6959853 A s h1)). Qed.
Lemma lem6959859 (b : Prop) (a : Prop) : (a \/ b) = (term202 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6959862 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : (term163 A x _92677) = (term203 A x _92677).
Proof. exact (@lem6959859 (_92677 = (@EMPTY A)) (term204 A x _92677)). Qed.
Lemma lem6959865 {A : Type'} (_92677 : A -> Prop) (x : type684 A) (h1 : term188 A x) : term203 A x _92677.
Proof. exact (EQ_MP (@lem6959862 A x _92677) (@lem6959574 A _92677 x h1)). Qed.
Lemma lem6959866 {A : Type'} (_92677 : A -> Prop) (x : type684 A) (h1 : term188 A x) : term203 A x _92677.
Proof. exact (@lem6959865 A _92677 x h1). Qed.
Lemma lem6959867 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term188 A x) : term203 A x s.
Proof. exact (@lem6959866 A s x h1). Qed.
Lemma lem6959870 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term16 A s) (h2 : term188 A x) : term204 A x s.
Proof. exact (@lem6959867 A s x h2 (@lem6959857 A s h1)). Qed.
Lemma lem6959871 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term16 A s) (h2 : term188 A x) : term205 A x s.
Proof. exact (fun h0 : term206 A x s => @lem6959870 A s x h1 h2). Qed.
Lemma lem6959873 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6959874 {A : Type'} (x : type684 A) (s : A -> Prop) : (term205 A x s) = (term204 A x s).
Proof. exact (@lem6959873 (term204 A x s)). Qed.
Lemma lem6959875 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term16 A s) (h2 : term188 A x) : term204 A x s.
Proof. exact (EQ_MP (@lem6959874 A x s) (@lem6959871 A s x h1 h2)). Qed.
Lemma lem6959881 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6959882 {A : Type'} (f : A -> nat) (_92674 : A) (s : A -> Prop) : (term64 A s f _92674) = (term207 A f _92674 s).
Proof. exact (@lem6959881 (term65 A f _92674) (term86 A _92674 s)). Qed.
Lemma lem6959888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6959889 {A : Type'} (f : A -> nat) (_92674 : A) (s : A -> Prop) : (term208 A s f _92674) = (term209 A f _92674 s).
Proof. exact (MK_COMB (@lem6959888) (@lem6959882 A f _92674 s)). Qed.
Lemma lem6959895 {A : Type'} (f : A -> nat) (_92674 : A) (s : A -> Prop) : (term207 A f _92674 s) = (term207 A f _92674 s).
Proof. exact (eq_refl (term207 A f _92674 s)). Qed.
Lemma lem6959896 {A : Type'} (f : A -> nat) (_92674 : A) (s : A -> Prop) : ((term64 A s f _92674) = (term207 A f _92674 s)) = ((term207 A f _92674 s) = (term207 A f _92674 s)).
Proof. exact (MK_COMB (@lem6959889 A f _92674 s) (@lem6959895 A f _92674 s)). Qed.
Lemma lem6959898 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6959899 (x : Prop) : (x = x) = True.
Proof. exact (@lem6959898 Prop x). Qed.
Lemma lem6959900 {A : Type'} (f : A -> nat) (_92674 : A) (s : A -> Prop) : ((term207 A f _92674 s) = (term207 A f _92674 s)) = True.
Proof. exact (@lem6959899 (term207 A f _92674 s)). Qed.
Lemma lem6959901 {A : Type'} (f : A -> nat) (_92674 : A) (s : A -> Prop) : ((term64 A s f _92674) = (term207 A f _92674 s)) = True.
Proof. exact (TRANS (@lem6959896 A f _92674 s) (@lem6959900 A f _92674 s)). Qed.
Lemma lem6959902 {A : Type'} (f : A -> nat) (_92674 : A) (s : A -> Prop) : True = ((term64 A s f _92674) = (term207 A f _92674 s)).
Proof. exact (SYM (@lem6959901 A f _92674 s)). Qed.
Lemma lem6959903 {A : Type'} (f : A -> nat) (_92674 : A) (s : A -> Prop) : (term64 A s f _92674) = (term207 A f _92674 s).
Proof. exact (EQ_MP (@lem6959902 A f _92674 s) (@lem0)). Qed.
Lemma lem6959904 {A : Type'} (_92674 : A) (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term207 A f _92674 s.
Proof. exact (EQ_MP (@lem6959903 A f _92674 s) (@lem6959562 A _92674 s f h1)). Qed.
Lemma lem6959906 (b : Prop) (a : Prop) : (a \/ b) = (term202 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6959907 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92674 : A) : (term207 A f _92674 s) = (term210 A s f _92674).
Proof. exact (@lem6959906 (term86 A _92674 s) (term65 A f _92674)). Qed.
Lemma lem6959909 (a : Prop) : (term211 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6959910 {A : Type'} (_92674 : A) (s : A -> Prop) : (term212 A _92674 s) = (@IN A _92674 s).
Proof. exact (@lem6959909 (@IN A _92674 s)). Qed.
Lemma lem6959911 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6959912 {A : Type'} (_92674 : A) (s : A -> Prop) : (term213 A _92674 s) = (term214 A _92674 s).
Proof. exact (MK_COMB (@lem6959911) (@lem6959910 A _92674 s)). Qed.
Lemma lem6959913 {A : Type'} (f : A -> nat) (_92674 : A) : (term65 A f _92674) = (term65 A f _92674).
Proof. exact (eq_refl (term65 A f _92674)). Qed.
Lemma lem6959914 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92674 : A) : (term210 A s f _92674) = (term62 A s f _92674).
Proof. exact (MK_COMB (@lem6959912 A _92674 s) (@lem6959913 A f _92674)). Qed.
Lemma lem6959915 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92674 : A) : (term207 A f _92674 s) = (term62 A s f _92674).
Proof. exact (TRANS (@lem6959907 A s f _92674) (@lem6959914 A s f _92674)). Qed.
Lemma lem6959918 {A : Type'} (_92674 : A) (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term62 A s f _92674.
Proof. exact (EQ_MP (@lem6959915 A s f _92674) (@lem6959904 A _92674 s f h1)). Qed.
Lemma lem6959919 {A : Type'} (_92674 : A) (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term62 A s f _92674.
Proof. exact (@lem6959918 A _92674 s f h1). Qed.
Lemma lem6959920 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> nat) (h1 : term15 A s f) : term215 A f x s.
Proof. exact (@lem6959919 A (x s) s f h1). Qed.
Lemma lem6959923 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term16 A s) (h3 : term188 A x) : term216 A f x s.
Proof. exact (@lem6959920 A x s f h1 (@lem6959875 A s x h2 h3)). Qed.
Lemma lem6959924 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term16 A s) (h3 : term188 A x) : term217 A f x s.
Proof. exact (fun h0 : term218 A f x s => @lem6959923 A f s x h1 h2 h3). Qed.
Lemma lem6959926 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6959927 {A : Type'} (f : A -> nat) (x : type684 A) (s : A -> Prop) : (term217 A f x s) = (term216 A f x s).
Proof. exact (@lem6959926 (term216 A f x s)). Qed.
Lemma lem6959928 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term16 A s) (h3 : term188 A x) : term216 A f x s.
Proof. exact (EQ_MP (@lem6959927 A f x s) (@lem6959924 A f s x h1 h2 h3)). Qed.
Lemma lem6959930 (b : Prop) (a : Prop) : (a \/ b) = (term202 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6959931 {A : Type'} (f : A -> nat) (_92680 : A) (s : A -> Prop) : (term69 A s f _92680) = (term219 A f _92680 s).
Proof. exact (@lem6959930 (term220 A f _92680) (term86 A _92680 s)). Qed.
Lemma lem6959933 (a : Prop) : (term211 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6959934 {A : Type'} (f : A -> nat) (_92680 : A) : (term221 A f _92680) = (term65 A f _92680).
Proof. exact (@lem6959933 (term65 A f _92680)). Qed.
Lemma lem6959935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6959936 {A : Type'} (f : A -> nat) (_92680 : A) : (term222 A f _92680) = (term223 A f _92680).
Proof. exact (MK_COMB (@lem6959935) (@lem6959934 A f _92680)). Qed.
Lemma lem6959937 {A : Type'} (_92680 : A) (s : A -> Prop) : (term86 A _92680 s) = (term86 A _92680 s).
Proof. exact (eq_refl (term86 A _92680 s)). Qed.
Lemma lem6959938 {A : Type'} (f : A -> nat) (_92680 : A) (s : A -> Prop) : (term219 A f _92680 s) = (term224 A f _92680 s).
Proof. exact (MK_COMB (@lem6959936 A f _92680) (@lem6959937 A _92680 s)). Qed.
Lemma lem6959939 {A : Type'} (f : A -> nat) (_92680 : A) (s : A -> Prop) : (term69 A s f _92680) = (term224 A f _92680 s).
Proof. exact (TRANS (@lem6959931 A f _92680 s) (@lem6959938 A f _92680 s)). Qed.
Lemma lem6959942 {A : Type'} (_92680 : A) (s : A -> Prop) (f : A -> nat) (h1 : term78 A s f) : term224 A f _92680 s.
Proof. exact (EQ_MP (@lem6959939 A f _92680 s) (@lem6959586 A _92680 s f h1)). Qed.
Lemma lem6959943 {A : Type'} (_92680 : A) (s : A -> Prop) (f : A -> nat) (h1 : term78 A s f) : term224 A f _92680 s.
Proof. exact (@lem6959942 A _92680 s f h1). Qed.
Lemma lem6959944 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> nat) (h1 : term78 A s f) : term225 A f x s.
Proof. exact (@lem6959943 A (x s) s f h1). Qed.
Lemma lem6959947 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : term206 A x s.
Proof. exact (@lem6959944 A x s f h2 (@lem6959928 A f s x h1 h3 h4)). Qed.
Lemma lem6959948 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : term226 A x s.
Proof. exact (fun h0 : term204 A x s => @lem6959947 A f s x h1 h2 h3 h4). Qed.
Lemma lem6959950 (p : Prop) : (term201 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6959951 {A : Type'} (x : type684 A) (s : A -> Prop) : (term226 A x s) = (term206 A x s).
Proof. exact (@lem6959950 (term204 A x s)). Qed.
Lemma lem6959952 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : term206 A x s.
Proof. exact (EQ_MP (@lem6959951 A x s) (@lem6959948 A f s x h1 h2 h3 h4)). Qed.
Lemma lem6959958 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6959959 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : (term163 A x _92677) = (term227 A x _92677).
Proof. exact (@lem6959958 (_92677 = (@EMPTY A)) (term204 A x _92677)). Qed.
Lemma lem6959967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6959968 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : (term228 A x _92677) = (term229 A x _92677).
Proof. exact (MK_COMB (@lem6959967) (@lem6959959 A x _92677)). Qed.
Lemma lem6959976 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : (term227 A x _92677) = (term227 A x _92677).
Proof. exact (eq_refl (term227 A x _92677)). Qed.
Lemma lem6959977 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : ((term163 A x _92677) = (term227 A x _92677)) = ((term227 A x _92677) = (term227 A x _92677)).
Proof. exact (MK_COMB (@lem6959968 A x _92677) (@lem6959976 A x _92677)). Qed.
Lemma lem6959979 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6959980 (x : Prop) : (x = x) = True.
Proof. exact (@lem6959979 Prop x). Qed.
Lemma lem6959981 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : ((term227 A x _92677) = (term227 A x _92677)) = True.
Proof. exact (@lem6959980 (term227 A x _92677)). Qed.
Lemma lem6959982 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : ((term163 A x _92677) = (term227 A x _92677)) = True.
Proof. exact (TRANS (@lem6959977 A x _92677) (@lem6959981 A x _92677)). Qed.
Lemma lem6959983 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : True = ((term163 A x _92677) = (term227 A x _92677)).
Proof. exact (SYM (@lem6959982 A x _92677)). Qed.
Lemma lem6959984 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : (term163 A x _92677) = (term227 A x _92677).
Proof. exact (EQ_MP (@lem6959983 A x _92677) (@lem0)). Qed.
Lemma lem6959985 {A : Type'} (_92677 : A -> Prop) (x : type684 A) (h1 : term188 A x) : term227 A x _92677.
Proof. exact (EQ_MP (@lem6959984 A x _92677) (@lem6959574 A _92677 x h1)). Qed.
Lemma lem6959987 (b : Prop) (a : Prop) : (a \/ b) = (term202 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6959990 {A : Type'} (x : type684 A) (_92677 : A -> Prop) : (term227 A x _92677) = (term230 A x _92677).
Proof. exact (@lem6959987 (term204 A x _92677) (_92677 = (@EMPTY A))). Qed.
Lemma lem6959993 {A : Type'} (_92677 : A -> Prop) (x : type684 A) (h1 : term188 A x) : term230 A x _92677.
Proof. exact (EQ_MP (@lem6959990 A x _92677) (@lem6959985 A _92677 x h1)). Qed.
Lemma lem6959994 {A : Type'} (_92677 : A -> Prop) (x : type684 A) (h1 : term188 A x) : term230 A x _92677.
Proof. exact (@lem6959993 A _92677 x h1). Qed.
Lemma lem6959995 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term188 A x) : term230 A x s.
Proof. exact (@lem6959994 A s x h1). Qed.
Lemma lem6959998 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : s = (@EMPTY A).
Proof. exact (@lem6959995 A s x h4 (@lem6959952 A f s x h1 h2 h3 h4)). Qed.
Lemma lem6959999 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term188 A x) : term231 A s.
Proof. exact (fun h0 : term16 A s => @lem6959998 A f s x h1 h2 h0 h3). Qed.
Lemma lem6960001 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6960002 {A : Type'} (s : A -> Prop) : (term231 A s) = (s = (@EMPTY A)).
Proof. exact (@lem6960001 (s = (@EMPTY A))). Qed.
Lemma lem6960003 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term188 A x) : s = (@EMPTY A).
Proof. exact (EQ_MP (@lem6960002 A s) (@lem6959999 A s f x h1 h2 h3)). Qed.
Lemma lem6960006 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6960008 {A : Type'} (s : A -> Prop) : (term16 A s) = (term232 A s).
Proof. exact (@lem6960006 (s = (@EMPTY A))). Qed.
Lemma lem6960011 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term232 A s.
Proof. exact (EQ_MP (@lem6960008 A s) (@lem6959556 A s h1)). Qed.
Lemma lem6960014 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : False.
Proof. exact (@lem6960011 A s h3 (@lem6960003 A s f x h1 h2 h4)). Qed.
Lemma lem6960015 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : term199.
Proof. exact (fun h0 : ~ False => @lem6960014 A f s x h1 h2 h3 h4). Qed.
Lemma lem6960017 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6960018 : term199 = False.
Proof. exact (@lem6960017 False). Qed.
Lemma lem6960019 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : False.
Proof. exact (EQ_MP (@lem6960018) (@lem6960015 A f s x h1 h2 h3 h4)). Qed.
Lemma lem6960020 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : (term16 A s) = False.
Proof. exact (prop_ext (fun h5 : term16 A s => @lem6960019 A f s x h1 h2 h3 h4) (fun h5 : False => @lem6959556 A s h3)). Qed.
Lemma lem6960021 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : False.
Proof. exact (EQ_MP (@lem6960020 A f s x h1 h2 h3 h4) (@lem6959556 A s h3)). Qed.
Lemma lem6960022 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : (term192 A s) = False.
Proof. exact (prop_ext (fun h3 : term192 A s => @lem6959729 A s h1 h2) (fun h3 : False => @lem6959552 A s h2)). Qed.
Lemma lem6960023 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : False.
Proof. exact (EQ_MP (@lem6960022 A s h1 h2) (@lem6959552 A s h2)). Qed.
Lemma lem6960024 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6960023 A s h1 h2) (fun h3 : False => @lem6959524 A s h1)). Qed.
Lemma lem6960025 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : False.
Proof. exact (EQ_MP (@lem6960024 A s h1 h2) (@lem6959524 A s h1)). Qed.
Lemma lem6960026 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : (term16 A s) = False.
Proof. exact (prop_ext (fun h5 : term16 A s => @lem6960021 A f s x h1 h2 h3 h4) (fun h5 : False => @lem6959386 A s h3)). Qed.
Lemma lem6960027 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : False.
Proof. exact (EQ_MP (@lem6960026 A f s x h1 h2 h3 h4) (@lem6959386 A s h3)). Qed.
Lemma lem6960028 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : (term192 A s) = False.
Proof. exact (prop_ext (fun h3 : term192 A s => @lem6960025 A s h1 h2) (fun h3 : False => @lem6959378 A s h2)). Qed.
Lemma lem6960029 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : False.
Proof. exact (EQ_MP (@lem6960028 A s h1 h2) (@lem6959378 A s h2)). Qed.
Lemma lem6960030 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6960029 A s h1 h2) (fun h3 : False => @lem6959286 A s h1)). Qed.
Lemma lem6960031 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : False.
Proof. exact (EQ_MP (@lem6960030 A s h1 h2) (@lem6959286 A s h1)). Qed.
Lemma lem6960032 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : (term78 A s f) = False.
Proof. exact (prop_ext (fun h5 : term78 A s f => @lem6960027 A f s x h1 h2 h3 h4) (fun h5 : False => @lem6959483 A s f h2)). Qed.
Lemma lem6960033 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : False.
Proof. exact (EQ_MP (@lem6960032 A f s x h1 h2 h3 h4) (@lem6959483 A s f h2)). Qed.
Lemma lem6960034 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : (term16 A s) = False.
Proof. exact (prop_ext (fun h5 : term16 A s => @lem6960033 A f s x h1 h2 h3 h4) (fun h5 : False => @lem6959386 A s h3)). Qed.
Lemma lem6960035 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term78 A s f) (h3 : term16 A s) (h4 : term188 A x) : False.
Proof. exact (EQ_MP (@lem6960034 A f s x h1 h2 h3 h4) (@lem6959386 A s h3)). Qed.
Lemma lem6960036 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : (term192 A s) = False.
Proof. exact (prop_ext (fun h3 : term192 A s => @lem6960031 A s h1 h2) (fun h3 : False => @lem6959378 A s h2)). Qed.
Lemma lem6960037 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : False.
Proof. exact (EQ_MP (@lem6960036 A s h1 h2) (@lem6959378 A s h2)). Qed.
Lemma lem6960038 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6960037 A s h1 h2) (fun h3 : False => @lem6959286 A s h1)). Qed.
Lemma lem6960039 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term192 A s) : False.
Proof. exact (EQ_MP (@lem6960038 A s h1 h2) (@lem6959286 A s h1)). Qed.
Lemma lem6960040 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) (h5 : term188 A x) : False.
Proof. exact (or_elim (@lem6959211 A s f h3) (fun h0 : term192 A s => @lem6960039 A s h2 h0) (fun h0 : term78 A s f => @lem6960035 A f s x h1 h0 h4 h5)). Qed.
Lemma lem6960041 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) (h5 : term188 A x) : (term188 A x) = False.
Proof. exact (prop_ext (fun h6 : term188 A x => @lem6960040 A f s x h1 h2 h3 h4 h5) (fun h6 : False => @lem6959278 A x h5)). Qed.
Lemma lem6960042 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) (h5 : term188 A x) : False.
Proof. exact (EQ_MP (@lem6960041 A f s x h1 h2 h3 h4 h5) (@lem6959278 A x h5)). Qed.
Lemma lem6960043 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) (h5 : term188 A x) : (term16 A s) = False.
Proof. exact (prop_ext (fun h6 : term16 A s => @lem6960042 A f s x h1 h2 h3 h4 h5) (fun h6 : False => @lem6959155 A s h4)). Qed.
Lemma lem6960044 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) (h5 : term188 A x) : False.
Proof. exact (EQ_MP (@lem6960043 A f s x h1 h2 h3 h4 h5) (@lem6959155 A s h4)). Qed.
Lemma lem6960045 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) (h5 : term188 A x) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A s => @lem6960044 A f s x h1 h2 h3 h4 h5) (fun h6 : False => @lem6959147 A s h2)). Qed.
Lemma lem6960046 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) (h5 : term188 A x) : False.
Proof. exact (EQ_MP (@lem6960045 A f s x h1 h2 h3 h4 h5) (@lem6959147 A s h2)). Qed.
Lemma lem6960047 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : @FINITE A s) (h4 : term19 A s f) (h5 : term16 A s) : False.
Proof. exact (ex_elim (@lem6959142 A h2) (fun x : type684 A => fun h0 : term190 A x => @lem6960046 A f s x h1 h3 h4 h5 h0)). Qed.
Lemma lem6960048 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : @FINITE A s) (h4 : term19 A s f) (h5 : term16 A s) : (term16 A s) = False.
Proof. exact (prop_ext (fun h6 : term16 A s => @lem6960047 A f s h1 h2 h3 h4 h5) (fun h6 : False => @lem6958679 A s h5)). Qed.
Lemma lem6960049 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : @FINITE A s) (h4 : term19 A s f) (h5 : term16 A s) : False.
Proof. exact (EQ_MP (@lem6960048 A f s h1 h2 h3 h4 h5) (@lem6958679 A s h5)). Qed.
Lemma lem6960050 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : @FINITE A s) (h4 : term19 A s f) (h5 : term16 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A s => @lem6960049 A f s h1 h2 h3 h4 h5) (fun h6 : False => @lem6958673 A s h3)). Qed.
Lemma lem6960051 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : @FINITE A s) (h4 : term19 A s f) (h5 : term16 A s) : False.
Proof. exact (EQ_MP (@lem6960050 A f s h1 h2 h3 h4 h5) (@lem6958673 A s h3)). Qed.
Lemma lem6960052 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : term25 A.
Proof. exact (fun h0 : term20 A => @lem6960051 A f s h1 h0 h2 h3 h4). Qed.
Lemma lem6960053 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem69 (term20 A)). Qed.
Lemma lem6960054 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : term26 A.
Proof. exact (EQ_MP (@lem6960053 A) (@lem6960052 A f s h1 h2 h3 h4)). Qed.
Lemma lem6960055 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : term29 A.
Proof. exact (fun h0 : term57 => @lem6960054 A f s h1 h2 h3 h4). Qed.
Lemma lem6960056 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term32 A s f.
Proof. exact (fun h0 : term19 A s f => @lem6960055 A f s h1 h2 h0 h3). Qed.
Lemma lem6960057 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term16 A s) : term35 A s f.
Proof. exact (fun h0 : term15 A s f => @lem6960056 A f s h0 h1 h2). Qed.
Lemma lem6960058 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : term38 A s f.
Proof. exact (fun h0 : term16 A s => @lem6960057 A f s h1 h0). Qed.
Lemma lem6960059 {A : Type'} (s : A -> Prop) (f : A -> nat) : term40 A s f.
Proof. exact (fun h0 : @FINITE A s => @lem6960058 A f s h0). Qed.
Lemma lem6960064 {A : Type'} (f : A -> nat) : term44 A f.
Proof. exact (fun s : A -> Prop => @lem6960059 A s f). Qed.
Lemma lem6960069 {A : Type'} : term48 A.
Proof. exact (fun f : A -> nat => @lem6960064 A f). Qed.
Lemma lem6960070 {A : Type'} : term47 A.
Proof. exact (EQ_MP (@lem6958661 A) (@lem6960069 A)). Qed.
Lemma lem6960071 {A : Type'} (f : A -> nat) : term233 A f.
Proof. exact (@lem6960070 A f). Qed.
Lemma lem6960072 {A : Type'} (f : A -> nat) : (term233 A f) = (term43 A f).
Proof. exact (eq_refl (term233 A f)). Qed.
Lemma lem6960073 {A : Type'} (f : A -> nat) : term43 A f.
Proof. exact (EQ_MP (@lem6960072 A f) (@lem6960071 A f)). Qed.
Lemma lem6960074 {A : Type'} (f : A -> nat) (s : A -> Prop) : term234 A f s.
Proof. exact (@lem6960073 A f s). Qed.
Lemma lem6960075 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term234 A f s) = (term21 A s f).
Proof. exact (eq_refl (term234 A f s)). Qed.
Lemma lem6960076 {A : Type'} (s : A -> Prop) (f : A -> nat) : term21 A s f.
Proof. exact (EQ_MP (@lem6960075 A s f) (@lem6960074 A f s)). Qed.
Lemma lem6960078 {A : Type'} (s : A -> Prop) (f : A -> nat) : term21 A s f.
Proof. exact (@lem6958383 A s f (@lem6960076 A s f)). Qed.
Lemma lem6960079 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : term37 A s f.
Proof. exact (@lem6960078 A s f (@lem6958354 A s h1)). Qed.
Lemma lem6960080 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term16 A s) : term34 A s f.
Proof. exact (@lem6960079 A f s h1 (@lem6958356 A s h2)). Qed.
Lemma lem6960081 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term31 A s f.
Proof. exact (@lem6960080 A f s h2 h3 (@lem6958355 A s f h1)). Qed.
Lemma lem6960082 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : term28 A.
Proof. exact (@lem6960081 A f s h1 h2 h4 (@lem6958364 A s f h3)). Qed.
Lemma lem6960083 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : term25 A.
Proof. exact (@lem6960082 A f s h1 h2 h3 h4 (@lem1369133)). Qed.
Lemma lem6960084 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : False.
Proof. exact (@lem6960083 A f s h1 h2 h3 h4 (@lem6958365 A)). Qed.
Lemma lem6960085 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : (term19 A s f) = False.
Proof. exact (prop_ext (fun h5 : term19 A s f => @lem6960084 A f s h1 h2 h3 h4) (fun h5 : False => @lem6958364 A s f h3)). Qed.
Lemma lem6960086 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : False.
Proof. exact (EQ_MP (@lem6960085 A f s h1 h2 h3 h4) (@lem6958364 A s f h3)). Qed.
Lemma lem6960087 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term18 A s f.
Proof. exact (fun h0 : term19 A s f => @lem6960086 A f s h1 h2 h0 h3). Qed.
Lemma lem6960088 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term5 A s f.
Proof. exact (EQ_MP (@lem6958363 A s f) (@lem6960087 A f s h1 h2 h3)). Qed.
Lemma lem6960089 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term6 A s f.
Proof. exact (@lem6958359 A s f (@lem6960088 A f s h1 h2 h3)). Qed.
Lemma lem6960090 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term13 A s f) : term14 A s f.
Proof. exact (proj2 (@lem6958352 A s f h1)). Qed.
Lemma lem6960091 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term13 A s f) : @FINITE A s.
Proof. exact (proj1 (@lem6958352 A s f h1)). Qed.
Lemma lem6960092 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term14 A s f) : term15 A s f.
Proof. exact (proj2 (@lem6958353 A s f h1)). Qed.
Lemma lem6960093 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term14 A s f) : term16 A s.
Proof. exact (proj1 (@lem6958353 A s f h1)). Qed.
Lemma lem6960094 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : (term15 A s f) = (term6 A s f).
Proof. exact (prop_ext (fun h4 : term15 A s f => @lem6960089 A f s h1 h2 h3) (fun h4 : term6 A s f => @lem6958355 A s f h1)). Qed.
Lemma lem6960095 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term6 A s f.
Proof. exact (EQ_MP (@lem6960094 A f s h1 h2 h3) (@lem6958355 A s f h1)). Qed.
Lemma lem6960096 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : (term16 A s) = (term6 A s f).
Proof. exact (prop_ext (fun h4 : term16 A s => @lem6960095 A f s h1 h2 h3) (fun h4 : term6 A s f => @lem6958356 A s h3)). Qed.
Lemma lem6960097 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term6 A s f.
Proof. exact (EQ_MP (@lem6960096 A f s h1 h2 h3) (@lem6958356 A s h3)). Qed.
Lemma lem6960098 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term16 A s) (h3 : term14 A s f) : (term15 A s f) = (term6 A s f).
Proof. exact (prop_ext (fun h4 : term15 A s f => @lem6960097 A f s h4 h1 h2) (fun h4 : term6 A s f => @lem6960092 A s f h3)). Qed.
Lemma lem6960099 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term16 A s) (h3 : term14 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem6960098 A s f h1 h2 h3) (@lem6960092 A s f h3)). Qed.
Lemma lem6960100 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term14 A s f) : (term16 A s) = (term6 A s f).
Proof. exact (prop_ext (fun h3 : term16 A s => @lem6960099 A s f h1 h3 h2) (fun h3 : term6 A s f => @lem6960093 A s f h2)). Qed.
Lemma lem6960101 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term14 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem6960100 A s f h1 h2) (@lem6960093 A s f h2)). Qed.
Lemma lem6960102 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term14 A s f) : (@FINITE A s) = (term6 A s f).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6960101 A s f h1 h2) (fun h3 : term6 A s f => @lem6958354 A s h1)). Qed.
Lemma lem6960103 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term14 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem6960102 A s f h1 h2) (@lem6958354 A s h1)). Qed.
Lemma lem6960104 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term13 A s f) : (term14 A s f) = (term6 A s f).
Proof. exact (prop_ext (fun h3 : term14 A s f => @lem6960103 A s f h1 h3) (fun h3 : term6 A s f => @lem6960090 A s f h2)). Qed.
Lemma lem6960105 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : @FINITE A s) (h2 : term13 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem6960104 A s f h1 h2) (@lem6960090 A s f h2)). Qed.
Lemma lem6960106 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term13 A s f) : (@FINITE A s) = (term6 A s f).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem6960105 A s f h2 h1) (fun h2 : term6 A s f => @lem6960091 A s f h1)). Qed.
Lemma lem6960107 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term13 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem6960106 A s f h1) (@lem6960091 A s f h1)). Qed.
Lemma lem6960108 {A : Type'} (s : A -> Prop) (f : A -> nat) : term235 A s f.
Proof. exact (fun h0 : term13 A s f => @lem6960107 A s f h0). Qed.
Lemma lem6960113 {A : Type'} (s : A -> Prop) : term236 A s.
Proof. exact (fun f : A -> nat => @lem6960108 A s f). Qed.
Lemma lem6960118 {A : Type'} : term237 A.
Proof. exact (fun s : A -> Prop => @lem6960113 A s). Qed.
