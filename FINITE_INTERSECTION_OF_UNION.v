Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INTERSECTION_OF_UNION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INTERSECTION_OF_INC_spec.
Require Import FINITE_INTERSECTION_OF_UNION_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm69_spec.
Lemma lem4894290 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4894291 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4894292 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4894291 t1) (@lem4894290 t1)). Qed.
Lemma lem4894293 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4894292 t1 t2). Qed.
Lemma lem4894294 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4894295 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4894294 t1 t2) (@lem4894293 t1 t2)). Qed.
Lemma lem4894296 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4894295 t1 t2 t3). Qed.
Lemma lem4894297 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4894298 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4894297 t1 t2 t3) (@lem4894296 t1 t2 t3)). Qed.
Lemma lem4894299 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4894298 t1 t2 t3)). Qed.
Lemma lem4894300 {A : Type'} (P : type686 A) : term7 A P.
Proof. exact (@lem4894289 A P). Qed.
Lemma lem4894301 {A : Type'} (P : type686 A) : (term7 A P) = ((term8 A P) = (term9 A P)).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem4894322 {A : Type'} (P : type686 A) : (term8 A P) = (term9 A P).
Proof. exact (EQ_MP (@lem4894301 A P) (@lem4894300 A P)). Qed.
Lemma lem4894323 {A : Type'} (P : type686 A) : (term8 A P) = (term9 A P).
Proof. exact (@lem4894322 A P). Qed.
Lemma lem4894336 {A : Type'} (P : type686 A) : (term10 A P) = (term10 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem4894337 {A : Type'} (P : type686 A) : (term11 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem4894336 A P) (@lem4894323 A P)). Qed.
Lemma lem4894340 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4894337 A P)). Qed.
Lemma lem4894341 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4894342 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem4894341 A) (@lem4894340 A)). Qed.
Lemma lem4894347 {A : Type'} : (term16 A) = (term15 A).
Proof. exact (SYM (@lem4894342 A)). Qed.
Lemma lem4894349 (p : Prop) : p = (term17 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4894350 {A : Type'} : (term16 A) = (term18 A).
Proof. exact (@lem4894349 (term16 A)). Qed.
Lemma lem4894351 {A : Type'} : (term18 A) = (term16 A).
Proof. exact (SYM (@lem4894350 A)). Qed.
Lemma lem4894352 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (h1). Qed.
Lemma lem4894353 {A : Type'} : term20 A.
Proof. exact (@lem4876895 A). Qed.
Lemma lem4894357 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem4894358 {A : Type'} : term22 A.
Proof. exact (fun h0 : term21 A => @lem4894357 A h0). Qed.
Lemma lem4894359 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem4894360 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem4894361 {A : Type'} (h1 : term21 A) (h2 : term22 A) : term21 A.
Proof. exact (@lem4894359 A h2 (@lem4894360 A h1)). Qed.
Lemma lem4894362 {A : Type'} (h1 : term21 A) : term23 A.
Proof. exact (fun h0 : term22 A => @lem4894361 A h1 h0). Qed.
Lemma lem4894363 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem4894364 {A : Type'} (h1 : term21 A) (h2 : term22 A) : term21 A.
Proof. exact (@lem4894362 A h1 (@lem4894363 A h2)). Qed.
Lemma lem4894365 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (fun h0 : term21 A => @lem4894364 A h0 h1). Qed.
Lemma lem4894366 {A : Type'} : term24 A.
Proof. exact (fun h0 : term22 A => @lem4894365 A h0). Qed.
Lemma lem4894369 {A : Type'} : term22 A.
Proof. exact (@lem4894366 A (@lem4894358 A)). Qed.
Lemma lem4894370 {A : Type'} : term22 A.
Proof. exact (@lem4894369 A). Qed.
Lemma lem4894404 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4894405 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem4894404 (term20 A)). Qed.
Lemma lem4894416 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (eq_refl (term27 A)). Qed.
Lemma lem4894423 {A : Type'} : (term21 A) = (term28 A).
Proof. exact (MK_COMB (@lem4894416 A) (@lem4894405 A)). Qed.
Lemma lem4894428 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term29 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4894429 {A : Type'} (P : type686 A) : (term30 A P) = (term30 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894428 A P s)). Qed.
Lemma lem4894430 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894431 {A : Type'} (P : type686 A) : (term31 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4894430 A) (@lem4894429 A P)). Qed.
Lemma lem4894432 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4894431 A P)). Qed.
Lemma lem4894433 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4894434 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem4894433 A) (@lem4894432 A)). Qed.
Lemma lem4894435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4894436 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem4894435) (@lem4894434 A)). Qed.
Lemma lem4894445 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term33 A P s t) = (term33 A P s t).
Proof. exact (eq_refl (term33 A P s t)). Qed.
Lemma lem4894446 {A : Type'} (P : type686 A) (s : A -> Prop) : (term34 A P s) = (term34 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4894445 A P s t)). Qed.
Lemma lem4894447 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894448 {A : Type'} (P : type686 A) (s : A -> Prop) : (term35 A P s) = (term35 A P s).
Proof. exact (MK_COMB (@lem4894447 A) (@lem4894446 A P s)). Qed.
Lemma lem4894449 {A : Type'} (P : type686 A) : (term36 A P) = (term36 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894448 A P s)). Qed.
Lemma lem4894450 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894451 {A : Type'} (P : type686 A) : (term9 A P) = (term9 A P).
Proof. exact (MK_COMB (@lem4894450 A) (@lem4894449 A P)). Qed.
Lemma lem4894460 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term37 A P s t).
Proof. exact (eq_refl (term37 A P s t)). Qed.
Lemma lem4894461 {A : Type'} (P : type686 A) (s : A -> Prop) : (term38 A P s) = (term38 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4894460 A P s t)). Qed.
Lemma lem4894462 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894463 {A : Type'} (P : type686 A) (s : A -> Prop) : (term39 A P s) = (term39 A P s).
Proof. exact (MK_COMB (@lem4894462 A) (@lem4894461 A P s)). Qed.
Lemma lem4894464 {A : Type'} (P : type686 A) : (term40 A P) = (term40 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894463 A P s)). Qed.
Lemma lem4894465 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894466 {A : Type'} (P : type686 A) : (term41 A P) = (term41 A P).
Proof. exact (MK_COMB (@lem4894465 A) (@lem4894464 A P)). Qed.
Lemma lem4894467 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4894468 {A : Type'} (P : type686 A) : (term10 A P) = (term10 A P).
Proof. exact (MK_COMB (@lem4894467) (@lem4894466 A P)). Qed.
Lemma lem4894469 {A : Type'} (P : type686 A) : (term12 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem4894468 A P) (@lem4894451 A P)). Qed.
Lemma lem4894470 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4894469 A P)). Qed.
Lemma lem4894471 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4894472 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4894471 A) (@lem4894470 A)). Qed.
Lemma lem4894473 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4894474 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem4894473) (@lem4894472 A)). Qed.
Lemma lem4894475 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4894476 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem4894475) (@lem4894474 A)). Qed.
Lemma lem4894477 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem4894476 A) (@lem4894436 A)). Qed.
Lemma lem4894536 {A : Type'} : (term21 A) = (term28 A).
Proof. exact (TRANS (@lem4894423 A) (@lem4894477 A)). Qed.
Lemma lem4894537 {A : Type'} : (term28 A) = (term21 A).
Proof. exact (SYM (@lem4894536 A)). Qed.
Lemma lem4894538 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (h1). Qed.
Lemma lem4894539 {A : Type'} (h1 : term20 A) : term20 A.
Proof. exact (h1). Qed.
Lemma lem4894546 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term42 A s P t) = (term43 A s P t).
Proof. exact (@lem17045 (P s) (P t)). Qed.
Lemma lem4894547 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term44 A P s t).
Proof. exact (eq_refl (term44 A P s t)). Qed.
Lemma lem4894548 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4894549 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term45 A s P t) = (term46 A s P t).
Proof. exact (MK_COMB (@lem4894548) (@lem4894546 A s P t)). Qed.
Lemma lem4894550 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term47 A P s t) = (term48 A P s t).
Proof. exact (MK_COMB (@lem4894549 A s P t) (@lem4894547 A P s t)). Qed.
Lemma lem4894551 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term47 A P s t).
Proof. exact (@lem17265 (term49 A s P t) (term44 A P s t)). Qed.
Lemma lem4894552 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term48 A P s t).
Proof. exact (TRANS (@lem4894551 A P s t) (@lem4894550 A P s t)). Qed.
Lemma lem4894553 {A : Type'} (P : type686 A) (s : A -> Prop) : (term38 A P s) = (term50 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4894552 A P s t)). Qed.
Lemma lem4894554 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894555 {A : Type'} (P : type686 A) (s : A -> Prop) : (term39 A P s) = (term51 A P s).
Proof. exact (MK_COMB (@lem4894554 A) (@lem4894553 A P s)). Qed.
Lemma lem4894556 {A : Type'} (P : type686 A) : (term40 A P) = (term52 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894555 A P s)). Qed.
Lemma lem4894557 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894558 {A : Type'} (P : type686 A) : (term41 A P) = (term53 A P).
Proof. exact (MK_COMB (@lem4894557 A) (@lem4894556 A P)). Qed.
Lemma lem4894569 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term55 A P s t).
Proof. exact (@lem17362 (term49 A s P t) (term56 A P s t)). Qed.
Lemma lem4894570 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4894571 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term60 A P s).
Proof. exact (@lem4894570 A (term34 A P s)). Qed.
Lemma lem4894572 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term61 A P s t) = (term33 A P s t).
Proof. exact (eq_refl (term61 A P s t)). Qed.
Lemma lem4894573 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4894574 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term62 A P s t) = (term54 A P s t).
Proof. exact (MK_COMB (@lem4894573) (@lem4894572 A P s t)). Qed.
Lemma lem4894575 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term62 A P s t) = (term55 A P s t).
Proof. exact (TRANS (@lem4894574 A P s t) (@lem4894569 A P s t)). Qed.
Lemma lem4894576 {A : Type'} (P : type686 A) (s : A -> Prop) : (term63 A P s) = (term64 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4894575 A P s t)). Qed.
Lemma lem4894577 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4894578 {A : Type'} (P : type686 A) (s : A -> Prop) : (term60 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4894577 A) (@lem4894576 A P s)). Qed.
Lemma lem4894579 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term65 A P s).
Proof. exact (TRANS (@lem4894571 A P s) (@lem4894578 A P s)). Qed.
Lemma lem4894580 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4894581 {A : Type'} (P : type686 A) : (term66 A P) = (term67 A P).
Proof. exact (@lem4894580 A (term36 A P)). Qed.
Lemma lem4894582 {A : Type'} (P : type686 A) (s : A -> Prop) : (term68 A P s) = (term35 A P s).
Proof. exact (eq_refl (term68 A P s)). Qed.
Lemma lem4894583 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4894584 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term59 A P s).
Proof. exact (MK_COMB (@lem4894583) (@lem4894582 A P s)). Qed.
Lemma lem4894585 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term65 A P s).
Proof. exact (TRANS (@lem4894584 A P s) (@lem4894579 A P s)). Qed.
Lemma lem4894586 {A : Type'} (P : type686 A) : (term70 A P) = (term71 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894585 A P s)). Qed.
Lemma lem4894587 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4894588 {A : Type'} (P : type686 A) : (term67 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem4894587 A) (@lem4894586 A P)). Qed.
Lemma lem4894589 {A : Type'} (P : type686 A) : (term66 A P) = (term72 A P).
Proof. exact (TRANS (@lem4894581 A P) (@lem4894588 A P)). Qed.
Lemma lem4894590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4894591 {A : Type'} (P : type686 A) : (term73 A P) = (term74 A P).
Proof. exact (MK_COMB (@lem4894590) (@lem4894558 A P)). Qed.
Lemma lem4894592 {A : Type'} (P : type686 A) : (term75 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem4894591 A P) (@lem4894589 A P)). Qed.
Lemma lem4894593 {A : Type'} (P : type686 A) : (term77 A P) = (term75 A P).
Proof. exact (@lem17362 (term41 A P) (term9 A P)). Qed.
Lemma lem4894594 {A : Type'} (P : type686 A) : (term77 A P) = (term76 A P).
Proof. exact (TRANS (@lem4894593 A P) (@lem4894592 A P)). Qed.
Lemma lem4894595 {A : Type'} (P : type180 A) : (term78 A P) = (term79 A P).
Proof. exact (@lem18392 (type686 A) P). Qed.
Lemma lem4894596 {A : Type'} : (term19 A) = (term80 A).
Proof. exact (@lem4894595 A (term14 A)). Qed.
Lemma lem4894597 {A : Type'} (P : type686 A) : (term81 A P) = (term12 A P).
Proof. exact (eq_refl (term81 A P)). Qed.
Lemma lem4894598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4894599 {A : Type'} (P : type686 A) : (term82 A P) = (term77 A P).
Proof. exact (MK_COMB (@lem4894598) (@lem4894597 A P)). Qed.
Lemma lem4894600 {A : Type'} (P : type686 A) : (term82 A P) = (term76 A P).
Proof. exact (TRANS (@lem4894599 A P) (@lem4894594 A P)). Qed.
Lemma lem4894601 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4894600 A P)). Qed.
Lemma lem4894602 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4894603 {A : Type'} : (term80 A) = (term85 A).
Proof. exact (MK_COMB (@lem4894602 A) (@lem4894601 A)). Qed.
Lemma lem4894604 {A : Type'} : (term19 A) = (term85 A).
Proof. exact (TRANS (@lem4894596 A) (@lem4894603 A)). Qed.
Lemma lem4894759 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4894760 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem4894759 (A -> Prop) P Q). Qed.
Lemma lem4894761 {A : Type'} (P : type686 A) : (term90 A P) = (term91 A P).
Proof. exact (@lem4894760 A (term53 A P) (term71 A P)). Qed.
Lemma lem4894762 {A : Type'} (P : type686 A) (s : A -> Prop) : (term92 A P s) = (term65 A P s).
Proof. exact (eq_refl (term92 A P s)). Qed.
Lemma lem4894763 {A : Type'} (P : type686 A) : (term93 A P) = (term71 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894762 A P s)). Qed.
Lemma lem4894764 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4894765 {A : Type'} (P : type686 A) : (term94 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem4894764 A) (@lem4894763 A P)). Qed.
Lemma lem4894766 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4894767 {A : Type'} (P : type686 A) : (term90 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem4894766 A P) (@lem4894765 A P)). Qed.
Lemma lem4894768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4894769 {A : Type'} (P : type686 A) : (term95 A P) = (term96 A P).
Proof. exact (MK_COMB (@lem4894768) (@lem4894767 A P)). Qed.
Lemma lem4894770 {A : Type'} (P : type686 A) (s : A -> Prop) : (term92 A P s) = (term65 A P s).
Proof. exact (eq_refl (term92 A P s)). Qed.
Lemma lem4894771 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4894772 {A : Type'} (P : type686 A) (s : A -> Prop) : (term97 A P s) = (term98 A P s).
Proof. exact (MK_COMB (@lem4894771 A P) (@lem4894770 A P s)). Qed.
Lemma lem4894773 {A : Type'} (P : type686 A) : (term99 A P) = (term100 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894772 A P s)). Qed.
Lemma lem4894774 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4894775 {A : Type'} (P : type686 A) : (term91 A P) = (term101 A P).
Proof. exact (MK_COMB (@lem4894774 A) (@lem4894773 A P)). Qed.
Lemma lem4894776 {A : Type'} (P : type686 A) : ((term90 A P) = (term91 A P)) = ((term76 A P) = (term101 A P)).
Proof. exact (MK_COMB (@lem4894769 A P) (@lem4894775 A P)). Qed.
Lemma lem4894777 {A : Type'} (P : type686 A) : (term76 A P) = (term101 A P).
Proof. exact (EQ_MP (@lem4894776 A P) (@lem4894761 A P)). Qed.
Lemma lem4894779 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4894780 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem4894779 (A -> Prop) P Q). Qed.
Lemma lem4894781 {A : Type'} (P : type686 A) (s : A -> Prop) : (term102 A P s) = (term103 A P s).
Proof. exact (@lem4894780 A (term53 A P) (term64 A P s)). Qed.
Lemma lem4894782 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term104 A P s t) = (term55 A P s t).
Proof. exact (eq_refl (term104 A P s t)). Qed.
Lemma lem4894783 {A : Type'} (P : type686 A) (s : A -> Prop) : (term105 A P s) = (term64 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4894782 A P s t)). Qed.
Lemma lem4894784 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4894785 {A : Type'} (P : type686 A) (s : A -> Prop) : (term106 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4894784 A) (@lem4894783 A P s)). Qed.
Lemma lem4894786 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4894787 {A : Type'} (P : type686 A) (s : A -> Prop) : (term102 A P s) = (term98 A P s).
Proof. exact (MK_COMB (@lem4894786 A P) (@lem4894785 A P s)). Qed.
Lemma lem4894788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4894789 {A : Type'} (P : type686 A) (s : A -> Prop) : (term107 A P s) = (term108 A P s).
Proof. exact (MK_COMB (@lem4894788) (@lem4894787 A P s)). Qed.
Lemma lem4894790 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term104 A P s t) = (term55 A P s t).
Proof. exact (eq_refl (term104 A P s t)). Qed.
Lemma lem4894791 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4894792 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term109 A P s t) = (term110 A P s t).
Proof. exact (MK_COMB (@lem4894791 A P) (@lem4894790 A P s t)). Qed.
Lemma lem4894793 {A : Type'} (P : type686 A) (s : A -> Prop) : (term111 A P s) = (term112 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4894792 A P s t)). Qed.
Lemma lem4894794 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4894795 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term113 A P s).
Proof. exact (MK_COMB (@lem4894794 A) (@lem4894793 A P s)). Qed.
Lemma lem4894796 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term102 A P s) = (term103 A P s)) = ((term98 A P s) = (term113 A P s)).
Proof. exact (MK_COMB (@lem4894789 A P s) (@lem4894795 A P s)). Qed.
Lemma lem4894797 {A : Type'} (P : type686 A) (s : A -> Prop) : (term98 A P s) = (term113 A P s).
Proof. exact (EQ_MP (@lem4894796 A P s) (@lem4894781 A P s)). Qed.
Lemma lem4894798 {A : Type'} (P : type686 A) : (term100 A P) = (term114 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894797 A P s)). Qed.
Lemma lem4894799 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4894800 {A : Type'} (P : type686 A) : (term101 A P) = (term115 A P).
Proof. exact (MK_COMB (@lem4894799 A) (@lem4894798 A P)). Qed.
Lemma lem4894801 {A : Type'} (P : type686 A) : (term76 A P) = (term115 A P).
Proof. exact (TRANS (@lem4894777 A P) (@lem4894800 A P)). Qed.
Lemma lem4894802 {A : Type'} : (term84 A) = (term116 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4894801 A P)). Qed.
Lemma lem4894803 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4894805 {A : Type'} : (term85 A) = (term117 A).
Proof. exact (MK_COMB (@lem4894803 A) (@lem4894802 A)). Qed.
Lemma lem4894806 {A : Type'} : (term19 A) = (term117 A).
Proof. exact (TRANS (@lem4894604 A) (@lem4894805 A)). Qed.
Lemma lem4894807 {A : Type'} (h1 : term19 A) : term117 A.
Proof. exact (EQ_MP (@lem4894806 A) (@lem4894538 A h1)). Qed.
Lemma lem4894814 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term118 A P s).
Proof. exact (@lem17265 (P s) (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s)). Qed.
Lemma lem4894815 {A : Type'} (P : type686 A) : (term30 A P) = (term119 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894814 A P s)). Qed.
Lemma lem4894816 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894817 {A : Type'} (P : type686 A) : (term31 A P) = (term120 A P).
Proof. exact (MK_COMB (@lem4894816 A) (@lem4894815 A P)). Qed.
Lemma lem4894818 {A : Type'} : (term32 A) = (term121 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4894817 A P)). Qed.
Lemma lem4894819 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4894876 {A : Type'} : (term20 A) = (term122 A).
Proof. exact (MK_COMB (@lem4894819 A) (@lem4894818 A)). Qed.
Lemma lem4894877 {A : Type'} (h1 : term20 A) : term122 A.
Proof. exact (EQ_MP (@lem4894876 A) (@lem4894539 A h1)). Qed.
Lemma lem4894878 {A : Type'} (P : type686 A) (h1 : term115 A P) : term115 A P.
Proof. exact (h1). Qed.
Lemma lem4894879 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term113 A P s) : term113 A P s.
Proof. exact (h1). Qed.
Lemma lem4894880 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term110 A P s t.
Proof. exact (h1). Qed.
Lemma lem4894889 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894890 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4894889 (type180 A) (type174 A) f x). Qed.
Lemma lem4894891 {A : Type'} : (@INTERSECTION_OF A (@FINITE (A -> Prop))) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@FINITE (A -> Prop))).
Proof. exact (@lem4894890 A (@INTERSECTION_OF A) (@FINITE (A -> Prop))). Qed.
Lemma lem4894892 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4894893 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4894891 A) (@lem4894892 A P)). Qed.
Lemma lem4894895 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894896 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4894895 (type686 A) (type686 A) f x). Qed.
Lemma lem4894897 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@FINITE (A -> Prop)) P) = (term123 A P).
Proof. exact (@lem4894896 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@FINITE (A -> Prop))) P). Qed.
Lemma lem4894898 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term123 A P).
Proof. exact (TRANS (@lem4894893 A P) (@lem4894897 A P)). Qed.
Lemma lem4894899 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4894900 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term124 A P s).
Proof. exact (MK_COMB (@lem4894898 A P) (@lem4894899 A s)). Qed.
Lemma lem4894902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894903 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4894902 (A -> Prop) Prop f x). Qed.
Lemma lem4894904 {A : Type'} (P : type686 A) (s : A -> Prop) : (term124 A P s) = (term125 A P s).
Proof. exact (@lem4894903 A (term123 A P) s). Qed.
Lemma lem4894906 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term125 A P s).
Proof. exact (TRANS (@lem4894900 A P s) (@lem4894904 A P s)). Qed.
Lemma lem4894907 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4894912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894913 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4894912 (A -> Prop) Prop f x). Qed.
Lemma lem4894915 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4894913 A P s). Qed.
Lemma lem4894916 {A : Type'} (P : type686 A) (s : A -> Prop) : (term126 A P s) = (term127 A P s).
Proof. exact (MK_COMB (@lem4894907) (@lem4894915 A P s)). Qed.
Lemma lem4894917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4894918 {A : Type'} (P : type686 A) (s : A -> Prop) : (term128 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4894917) (@lem4894916 A P s)). Qed.
Lemma lem4894919 {A : Type'} (P : type686 A) (s : A -> Prop) : (term118 A P s) = (term130 A P s).
Proof. exact (MK_COMB (@lem4894918 A P s) (@lem4894906 A P s)). Qed.
Lemma lem4894920 {A : Type'} (P : type686 A) : (term119 A P) = (term131 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894919 A P s)). Qed.
Lemma lem4894921 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894922 {A : Type'} (P : type686 A) : (term120 A P) = (term132 A P).
Proof. exact (MK_COMB (@lem4894921 A) (@lem4894920 A P)). Qed.
Lemma lem4894923 {A : Type'} : (term121 A) = (term133 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4894922 A P)). Qed.
Lemma lem4894924 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4894925 {A : Type'} : (term122 A) = (term134 A).
Proof. exact (MK_COMB (@lem4894924 A) (@lem4894923 A)). Qed.
Lemma lem4894926 {A : Type'} (h1 : term20 A) : term134 A.
Proof. exact (EQ_MP (@lem4894925 A) (@lem4894877 A h1)). Qed.
Lemma lem4894927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4894937 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894938 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4894937 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4894939 {A : Type'} (s : A -> Prop) : (@UNION A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s).
Proof. exact (@lem4894938 A (@UNION A) s). Qed.
Lemma lem4894940 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4894941 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t).
Proof. exact (MK_COMB (@lem4894939 A s) (@lem4894940 A t)). Qed.
Lemma lem4894943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894944 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4894943 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4894945 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t) = (term135 A s t).
Proof. exact (@lem4894944 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s) t). Qed.
Lemma lem4894947 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (term135 A s t).
Proof. exact (TRANS (@lem4894941 A s t) (@lem4894945 A s t)). Qed.
Lemma lem4894949 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (eq_refl (@INTERSECTION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4894950 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term56 A P s t) = (term136 A P s t).
Proof. exact (MK_COMB (@lem4894949 A P) (@lem4894947 A s t)). Qed.
Lemma lem4894952 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894953 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4894952 (type180 A) (type174 A) f x). Qed.
Lemma lem4894954 {A : Type'} : (@INTERSECTION_OF A (@FINITE (A -> Prop))) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@FINITE (A -> Prop))).
Proof. exact (@lem4894953 A (@INTERSECTION_OF A) (@FINITE (A -> Prop))). Qed.
Lemma lem4894955 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4894956 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4894954 A) (@lem4894955 A P)). Qed.
Lemma lem4894958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894959 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4894958 (type686 A) (type686 A) f x). Qed.
Lemma lem4894960 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@FINITE (A -> Prop)) P) = (term123 A P).
Proof. exact (@lem4894959 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@FINITE (A -> Prop))) P). Qed.
Lemma lem4894961 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term123 A P).
Proof. exact (TRANS (@lem4894956 A P) (@lem4894960 A P)). Qed.
Lemma lem4894962 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term135 A s t) = (term135 A s t).
Proof. exact (eq_refl (term135 A s t)). Qed.
Lemma lem4894963 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term137 A P s t).
Proof. exact (MK_COMB (@lem4894961 A P) (@lem4894962 A s t)). Qed.
Lemma lem4894965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894966 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4894965 (A -> Prop) Prop f x). Qed.
Lemma lem4894967 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term137 A P s t) = (term138 A P s t).
Proof. exact (@lem4894966 A (term123 A P) (term135 A s t)). Qed.
Lemma lem4894968 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term138 A P s t).
Proof. exact (TRANS (@lem4894963 A P s t) (@lem4894967 A P s t)). Qed.
Lemma lem4894969 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term56 A P s t) = (term138 A P s t).
Proof. exact (TRANS (@lem4894950 A P s t) (@lem4894968 A P s t)). Qed.
Lemma lem4894970 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term139 A P s t) = (term140 A P s t).
Proof. exact (MK_COMB (@lem4894927) (@lem4894969 A P s t)). Qed.
Lemma lem4894975 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894976 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4894975 (A -> Prop) Prop f x). Qed.
Lemma lem4894978 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4894976 A P t). Qed.
Lemma lem4894983 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4894984 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4894983 (A -> Prop) Prop f x). Qed.
Lemma lem4894986 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4894984 A P s). Qed.
Lemma lem4894987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4894988 {A : Type'} (P : type686 A) (s : A -> Prop) : (term141 A P s) = (term142 A P s).
Proof. exact (MK_COMB (@lem4894987) (@lem4894986 A P s)). Qed.
Lemma lem4894989 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term49 A s P t) = (term143 A s P t).
Proof. exact (MK_COMB (@lem4894988 A P s) (@lem4894978 A P t)). Qed.
Lemma lem4894990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4894991 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term144 A s P t) = (term145 A s P t).
Proof. exact (MK_COMB (@lem4894990) (@lem4894989 A s P t)). Qed.
Lemma lem4894992 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term55 A P s t) = (term146 A P s t).
Proof. exact (MK_COMB (@lem4894991 A s P t) (@lem4894970 A P s t)). Qed.
Lemma lem4894993 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4895000 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4895001 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4895000 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4895002 {A : Type'} (s : A -> Prop) : (@UNION A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s).
Proof. exact (@lem4895001 A (@UNION A) s). Qed.
Lemma lem4895003 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4895004 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t).
Proof. exact (MK_COMB (@lem4895002 A s) (@lem4895003 A t)). Qed.
Lemma lem4895006 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4895007 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4895006 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4895008 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t) = (term135 A s t).
Proof. exact (@lem4895007 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s) t). Qed.
Lemma lem4895010 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (term135 A s t).
Proof. exact (TRANS (@lem4895004 A s t) (@lem4895008 A s t)). Qed.
Lemma lem4895011 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term147 A P s t).
Proof. exact (MK_COMB (@lem4894993 A P) (@lem4895010 A s t)). Qed.
Lemma lem4895013 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4895014 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4895013 (A -> Prop) Prop f x). Qed.
Lemma lem4895015 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term147 A P s t) = (term148 A P s t).
Proof. exact (@lem4895014 A P (term135 A s t)). Qed.
Lemma lem4895016 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term148 A P s t).
Proof. exact (TRANS (@lem4895011 A P s t) (@lem4895015 A P s t)). Qed.
Lemma lem4895017 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4895022 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4895023 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4895022 (A -> Prop) Prop f x). Qed.
Lemma lem4895025 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4895023 A P t). Qed.
Lemma lem4895026 {A : Type'} (P : type686 A) (t : A -> Prop) : (term126 A P t) = (term127 A P t).
Proof. exact (MK_COMB (@lem4895017) (@lem4895025 A P t)). Qed.
Lemma lem4895027 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4895032 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4895033 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4895032 (A -> Prop) Prop f x). Qed.
Lemma lem4895035 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4895033 A P s). Qed.
Lemma lem4895036 {A : Type'} (P : type686 A) (s : A -> Prop) : (term126 A P s) = (term127 A P s).
Proof. exact (MK_COMB (@lem4895027) (@lem4895035 A P s)). Qed.
Lemma lem4895037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4895038 {A : Type'} (P : type686 A) (s : A -> Prop) : (term128 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4895037) (@lem4895036 A P s)). Qed.
Lemma lem4895039 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term43 A s P t) = (term149 A s P t).
Proof. exact (MK_COMB (@lem4895038 A P s) (@lem4895026 A P t)). Qed.
Lemma lem4895040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4895041 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term46 A s P t) = (term150 A s P t).
Proof. exact (MK_COMB (@lem4895040) (@lem4895039 A s P t)). Qed.
Lemma lem4895042 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term48 A P s t) = (term151 A P s t).
Proof. exact (MK_COMB (@lem4895041 A s P t) (@lem4895016 A P s t)). Qed.
Lemma lem4895043 {A : Type'} (P : type686 A) (s : A -> Prop) : (term50 A P s) = (term152 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4895042 A P s t)). Qed.
Lemma lem4895044 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4895045 {A : Type'} (P : type686 A) (s : A -> Prop) : (term51 A P s) = (term153 A P s).
Proof. exact (MK_COMB (@lem4895044 A) (@lem4895043 A P s)). Qed.
Lemma lem4895046 {A : Type'} (P : type686 A) : (term52 A P) = (term154 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4895045 A P s)). Qed.
Lemma lem4895047 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4895048 {A : Type'} (P : type686 A) : (term53 A P) = (term155 A P).
Proof. exact (MK_COMB (@lem4895047 A) (@lem4895046 A P)). Qed.
Lemma lem4895049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4895050 {A : Type'} (P : type686 A) : (term74 A P) = (term156 A P).
Proof. exact (MK_COMB (@lem4895049) (@lem4895048 A P)). Qed.
Lemma lem4895051 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term110 A P s t) = (term157 A P s t).
Proof. exact (MK_COMB (@lem4895050 A P) (@lem4894992 A P s t)). Qed.
Lemma lem4895052 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term157 A P s t.
Proof. exact (EQ_MP (@lem4895051 A P s t) (@lem4894880 A P s t h1)). Qed.
Lemma lem4895053 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term146 A P s t.
Proof. exact (proj2 (@lem4895052 A P s t h1)). Qed.
Lemma lem4895054 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term155 A P.
Proof. exact (proj1 (@lem4895052 A P s t h1)). Qed.
Lemma lem4895056 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term143 A s P t.
Proof. exact (proj1 (@lem4895053 A P s t h1)). Qed.
Lemma lem4895066 {A : Type'} (P : type686 A) (s : A -> Prop) : (term130 A P s) = (term130 A P s).
Proof. exact (eq_refl (term130 A P s)). Qed.
Lemma lem4895067 {A : Type'} (P : type686 A) : (term131 A P) = (term131 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4895066 A P s)). Qed.
Lemma lem4895068 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4895069 {A : Type'} (P : type686 A) : (term132 A P) = (term132 A P).
Proof. exact (MK_COMB (@lem4895068 A) (@lem4895067 A P)). Qed.
Lemma lem4895070 {A : Type'} : (term133 A) = (term133 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4895069 A P)). Qed.
Lemma lem4895071 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4895073 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (MK_COMB (@lem4895071 A) (@lem4895070 A)). Qed.
Lemma lem4895074 {A : Type'} (h1 : term20 A) : term134 A.
Proof. exact (EQ_MP (@lem4895073 A) (@lem4894926 A h1)). Qed.
Lemma lem4895088 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term151 A P s t) = (term151 A P s t).
Proof. exact (eq_refl (term151 A P s t)). Qed.
Lemma lem4895089 {A : Type'} (P : type686 A) (s : A -> Prop) : (term152 A P s) = (term152 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4895088 A P s t)). Qed.
Lemma lem4895090 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4895091 {A : Type'} (P : type686 A) (s : A -> Prop) : (term153 A P s) = (term153 A P s).
Proof. exact (MK_COMB (@lem4895090 A) (@lem4895089 A P s)). Qed.
Lemma lem4895092 {A : Type'} (P : type686 A) : (term154 A P) = (term154 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4895091 A P s)). Qed.
Lemma lem4895093 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4895095 {A : Type'} (P : type686 A) : (term155 A P) = (term155 A P).
Proof. exact (MK_COMB (@lem4895093 A) (@lem4895092 A P)). Qed.
Lemma lem4895096 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term155 A P.
Proof. exact (EQ_MP (@lem4895095 A P) (@lem4895054 A P s t h1)). Qed.
Lemma lem4895109 {A : Type'} (_60481 : type686 A) (h1 : term20 A) : term158 A _60481.
Proof. exact (@lem4895074 A h1 _60481). Qed.
Lemma lem4895110 {A : Type'} (_60481 : type686 A) : (term158 A _60481) = (term132 A _60481).
Proof. exact (eq_refl (term158 A _60481)). Qed.
Lemma lem4895111 {A : Type'} (_60481 : type686 A) (h1 : term20 A) : term132 A _60481.
Proof. exact (EQ_MP (@lem4895110 A _60481) (@lem4895109 A _60481 h1)). Qed.
Lemma lem4895112 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) (h1 : term20 A) : term159 A _60481 _60482.
Proof. exact (@lem4895111 A _60481 h1 _60482). Qed.
Lemma lem4895113 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term159 A _60481 _60482) = (term130 A _60481 _60482).
Proof. exact (eq_refl (term159 A _60481 _60482)). Qed.
Lemma lem4895115 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term160 A P _60483.
Proof. exact (@lem4895096 A P s t h1 _60483). Qed.
Lemma lem4895116 {A : Type'} (P : type686 A) (_60483 : A -> Prop) : (term160 A P _60483) = (term153 A P _60483).
Proof. exact (eq_refl (term160 A P _60483)). Qed.
Lemma lem4895117 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term153 A P _60483.
Proof. exact (EQ_MP (@lem4895116 A P _60483) (@lem4895115 A _60483 P s t h1)). Qed.
Lemma lem4895118 {A : Type'} (_60483 : A -> Prop) (_60484 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term161 A P _60483 _60484.
Proof. exact (@lem4895117 A _60483 P s t h1 _60484). Qed.
Lemma lem4895119 {A : Type'} (P : type686 A) (_60483 : A -> Prop) (_60484 : A -> Prop) : (term161 A P _60483 _60484) = (term151 A P _60483 _60484).
Proof. exact (eq_refl (term161 A P _60483 _60484)). Qed.
Lemma lem4895120 {A : Type'} (_60483 : A -> Prop) (_60484 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term151 A P _60483 _60484.
Proof. exact (EQ_MP (@lem4895119 A P _60483 _60484) (@lem4895118 A _60483 _60484 P s t h1)). Qed.
Lemma lem4895126 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) (h1 : term20 A) : term130 A _60481 _60482.
Proof. exact (EQ_MP (@lem4895113 A _60481 _60482) (@lem4895112 A _60481 _60482 h1)). Qed.
Lemma lem4895137 {A : Type'} (P : type686 A) (_60483 : A -> Prop) (_60484 : A -> Prop) : (term151 A P _60483 _60484) = (term162 A P _60483 _60484).
Proof. exact (@lem4894299 (term127 A P _60483) (term127 A P _60484) (term148 A P _60483 _60484)). Qed.
Lemma lem4895138 {A : Type'} (_60483 : A -> Prop) (_60484 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term162 A P _60483 _60484.
Proof. exact (EQ_MP (@lem4895137 A P _60483 _60484) (@lem4895120 A _60483 _60484 P s t h1)). Qed.
Lemma lem4895140 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term140 A P s t.
Proof. exact (proj2 (@lem4895053 A P s t h1)). Qed.
Lemma lem4895146 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (proj1 (@lem4895056 A P s t h1)). Qed.
Lemma lem4895147 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term163 A P s.
Proof. exact (fun h0 : term127 A P s => @lem4895146 A P s t h1). Qed.
Lemma lem4895149 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4895150 {A : Type'} (P : type686 A) (s : A -> Prop) : (term163 A P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4895149 (@I ((A -> Prop) -> Prop) P s)). Qed.
Lemma lem4895151 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (EQ_MP (@lem4895150 A P s) (@lem4895147 A P s t h1)). Qed.
Lemma lem4895153 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (proj2 (@lem4895056 A P s t h1)). Qed.
Lemma lem4895154 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term163 A P t.
Proof. exact (fun h0 : term127 A P t => @lem4895153 A P s t h1). Qed.
Lemma lem4895156 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4895157 {A : Type'} (P : type686 A) (t : A -> Prop) : (term163 A P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4895156 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4895158 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (EQ_MP (@lem4895157 A P t) (@lem4895154 A P s t h1)). Qed.
Lemma lem4895174 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4895175 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term165 A P _60483 _60484) = (term166 A _60483 P _60484).
Proof. exact (@lem4895174 (term148 A P _60483 _60484) (term127 A P _60484)). Qed.
Lemma lem4895181 {A : Type'} (P : type686 A) (_60483 : A -> Prop) : (term129 A P _60483) = (term129 A P _60483).
Proof. exact (eq_refl (term129 A P _60483)). Qed.
Lemma lem4895182 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term162 A P _60483 _60484) = (term167 A _60483 P _60484).
Proof. exact (MK_COMB (@lem4895181 A P _60483) (@lem4895175 A _60483 P _60484)). Qed.
Lemma lem4895186 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4895187 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term167 A _60483 P _60484) = (term168 A _60483 P _60484).
Proof. exact (@lem4895186 (term148 A P _60483 _60484) (term127 A P _60483) (term127 A P _60484)). Qed.
Lemma lem4895203 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term162 A P _60483 _60484) = (term168 A _60483 P _60484).
Proof. exact (TRANS (@lem4895182 A _60483 P _60484) (@lem4895187 A _60483 P _60484)). Qed.
Lemma lem4895204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4895205 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term169 A P _60483 _60484) = (term170 A _60483 P _60484).
Proof. exact (MK_COMB (@lem4895204) (@lem4895203 A _60483 P _60484)). Qed.
Lemma lem4895221 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term168 A _60483 P _60484) = (term168 A _60483 P _60484).
Proof. exact (eq_refl (term168 A _60483 P _60484)). Qed.
Lemma lem4895222 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : ((term162 A P _60483 _60484) = (term168 A _60483 P _60484)) = ((term168 A _60483 P _60484) = (term168 A _60483 P _60484)).
Proof. exact (MK_COMB (@lem4895205 A _60483 P _60484) (@lem4895221 A _60483 P _60484)). Qed.
Lemma lem4895224 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4895225 (x : Prop) : (x = x) = True.
Proof. exact (@lem4895224 Prop x). Qed.
Lemma lem4895226 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : ((term168 A _60483 P _60484) = (term168 A _60483 P _60484)) = True.
Proof. exact (@lem4895225 (term168 A _60483 P _60484)). Qed.
Lemma lem4895227 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : ((term162 A P _60483 _60484) = (term168 A _60483 P _60484)) = True.
Proof. exact (TRANS (@lem4895222 A _60483 P _60484) (@lem4895226 A _60483 P _60484)). Qed.
Lemma lem4895228 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : True = ((term162 A P _60483 _60484) = (term168 A _60483 P _60484)).
Proof. exact (SYM (@lem4895227 A _60483 P _60484)). Qed.
Lemma lem4895229 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term162 A P _60483 _60484) = (term168 A _60483 P _60484).
Proof. exact (EQ_MP (@lem4895228 A _60483 P _60484) (@lem0)). Qed.
Lemma lem4895230 {A : Type'} (_60483 : A -> Prop) (_60484 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term168 A _60483 P _60484.
Proof. exact (EQ_MP (@lem4895229 A _60483 P _60484) (@lem4895138 A _60483 _60484 P s t h1)). Qed.
Lemma lem4895232 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4895233 {A : Type'} (P : type686 A) (_60483 : A -> Prop) (_60484 : A -> Prop) : (term168 A _60483 P _60484) = (term172 A P _60483 _60484).
Proof. exact (@lem4895232 (term149 A _60483 P _60484) (term148 A P _60483 _60484)). Qed.
Lemma lem4895235 (a : Prop) (b : Prop) : (term173 a b) = (term174 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4895236 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term175 A _60483 P _60484) = (term176 A _60483 P _60484).
Proof. exact (@lem4895235 (term127 A P _60483) (term127 A P _60484)). Qed.
Lemma lem4895238 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4895239 {A : Type'} (P : type686 A) (_60483 : A -> Prop) : (term178 A P _60483) = (@I ((A -> Prop) -> Prop) P _60483).
Proof. exact (@lem4895238 (@I ((A -> Prop) -> Prop) P _60483)). Qed.
Lemma lem4895240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4895241 {A : Type'} (P : type686 A) (_60483 : A -> Prop) : (term179 A P _60483) = (term142 A P _60483).
Proof. exact (MK_COMB (@lem4895240) (@lem4895239 A P _60483)). Qed.
Lemma lem4895243 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4895244 {A : Type'} (P : type686 A) (_60484 : A -> Prop) : (term178 A P _60484) = (@I ((A -> Prop) -> Prop) P _60484).
Proof. exact (@lem4895243 (@I ((A -> Prop) -> Prop) P _60484)). Qed.
Lemma lem4895245 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term176 A _60483 P _60484) = (term143 A _60483 P _60484).
Proof. exact (MK_COMB (@lem4895241 A P _60483) (@lem4895244 A P _60484)). Qed.
Lemma lem4895246 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term175 A _60483 P _60484) = (term143 A _60483 P _60484).
Proof. exact (TRANS (@lem4895236 A _60483 P _60484) (@lem4895245 A _60483 P _60484)). Qed.
Lemma lem4895247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4895248 {A : Type'} (_60483 : A -> Prop) (P : type686 A) (_60484 : A -> Prop) : (term180 A _60483 P _60484) = (term181 A _60483 P _60484).
Proof. exact (MK_COMB (@lem4895247) (@lem4895246 A _60483 P _60484)). Qed.
Lemma lem4895249 {A : Type'} (P : type686 A) (_60483 : A -> Prop) (_60484 : A -> Prop) : (term148 A P _60483 _60484) = (term148 A P _60483 _60484).
Proof. exact (eq_refl (term148 A P _60483 _60484)). Qed.
Lemma lem4895250 {A : Type'} (P : type686 A) (_60483 : A -> Prop) (_60484 : A -> Prop) : (term172 A P _60483 _60484) = (term182 A P _60483 _60484).
Proof. exact (MK_COMB (@lem4895248 A _60483 P _60484) (@lem4895249 A P _60483 _60484)). Qed.
Lemma lem4895251 {A : Type'} (P : type686 A) (_60483 : A -> Prop) (_60484 : A -> Prop) : (term168 A _60483 P _60484) = (term182 A P _60483 _60484).
Proof. exact (TRANS (@lem4895233 A P _60483 _60484) (@lem4895250 A P _60483 _60484)). Qed.
Lemma lem4895253 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term143 A s P t.
Proof. exact (conj (@lem4895151 A P s t h1) (@lem4895158 A P s t h1)). Qed.
Lemma lem4895255 {A : Type'} (_60483 : A -> Prop) (_60484 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P _60483 _60484.
Proof. exact (EQ_MP (@lem4895251 A P _60483 _60484) (@lem4895230 A _60483 _60484 P s t h1)). Qed.
Lemma lem4895256 {A : Type'} (_60483 : A -> Prop) (_60484 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P _60483 _60484.
Proof. exact (@lem4895255 A _60483 _60484 P s t h1). Qed.
Lemma lem4895257 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P s t.
Proof. exact (@lem4895256 A s t P s t h1). Qed.
Lemma lem4895260 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term148 A P s t.
Proof. exact (@lem4895257 A P s t h1 (@lem4895253 A P s t h1)). Qed.
Lemma lem4895261 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term183 A P s t.
Proof. exact (fun h0 : term184 A P s t => @lem4895260 A P s t h1). Qed.
Lemma lem4895263 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4895264 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term183 A P s t) = (term148 A P s t).
Proof. exact (@lem4895263 (term148 A P s t)). Qed.
Lemma lem4895265 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term148 A P s t.
Proof. exact (EQ_MP (@lem4895264 A P s t) (@lem4895261 A P s t h1)). Qed.
Lemma lem4895271 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4895272 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term130 A _60481 _60482) = (term185 A _60481 _60482).
Proof. exact (@lem4895271 (term125 A _60481 _60482) (term127 A _60481 _60482)). Qed.
Lemma lem4895278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4895279 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term186 A _60481 _60482) = (term187 A _60481 _60482).
Proof. exact (MK_COMB (@lem4895278) (@lem4895272 A _60481 _60482)). Qed.
Lemma lem4895285 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term185 A _60481 _60482) = (term185 A _60481 _60482).
Proof. exact (eq_refl (term185 A _60481 _60482)). Qed.
Lemma lem4895286 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : ((term130 A _60481 _60482) = (term185 A _60481 _60482)) = ((term185 A _60481 _60482) = (term185 A _60481 _60482)).
Proof. exact (MK_COMB (@lem4895279 A _60481 _60482) (@lem4895285 A _60481 _60482)). Qed.
Lemma lem4895288 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4895289 (x : Prop) : (x = x) = True.
Proof. exact (@lem4895288 Prop x). Qed.
Lemma lem4895290 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : ((term185 A _60481 _60482) = (term185 A _60481 _60482)) = True.
Proof. exact (@lem4895289 (term185 A _60481 _60482)). Qed.
Lemma lem4895291 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : ((term130 A _60481 _60482) = (term185 A _60481 _60482)) = True.
Proof. exact (TRANS (@lem4895286 A _60481 _60482) (@lem4895290 A _60481 _60482)). Qed.
Lemma lem4895292 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : True = ((term130 A _60481 _60482) = (term185 A _60481 _60482)).
Proof. exact (SYM (@lem4895291 A _60481 _60482)). Qed.
Lemma lem4895293 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term130 A _60481 _60482) = (term185 A _60481 _60482).
Proof. exact (EQ_MP (@lem4895292 A _60481 _60482) (@lem0)). Qed.
Lemma lem4895294 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) (h1 : term20 A) : term185 A _60481 _60482.
Proof. exact (EQ_MP (@lem4895293 A _60481 _60482) (@lem4895126 A _60481 _60482 h1)). Qed.
Lemma lem4895296 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4895297 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term185 A _60481 _60482) = (term188 A _60481 _60482).
Proof. exact (@lem4895296 (term127 A _60481 _60482) (term125 A _60481 _60482)). Qed.
Lemma lem4895299 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4895300 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term178 A _60481 _60482) = (@I ((A -> Prop) -> Prop) _60481 _60482).
Proof. exact (@lem4895299 (@I ((A -> Prop) -> Prop) _60481 _60482)). Qed.
Lemma lem4895301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4895302 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term189 A _60481 _60482) = (term190 A _60481 _60482).
Proof. exact (MK_COMB (@lem4895301) (@lem4895300 A _60481 _60482)). Qed.
Lemma lem4895303 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term125 A _60481 _60482) = (term125 A _60481 _60482).
Proof. exact (eq_refl (term125 A _60481 _60482)). Qed.
Lemma lem4895304 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term188 A _60481 _60482) = (term191 A _60481 _60482).
Proof. exact (MK_COMB (@lem4895302 A _60481 _60482) (@lem4895303 A _60481 _60482)). Qed.
Lemma lem4895305 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) : (term185 A _60481 _60482) = (term191 A _60481 _60482).
Proof. exact (TRANS (@lem4895297 A _60481 _60482) (@lem4895304 A _60481 _60482)). Qed.
Lemma lem4895308 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) (h1 : term20 A) : term191 A _60481 _60482.
Proof. exact (EQ_MP (@lem4895305 A _60481 _60482) (@lem4895294 A _60481 _60482 h1)). Qed.
Lemma lem4895309 {A : Type'} (_60481 : type686 A) (_60482 : A -> Prop) (h1 : term20 A) : term191 A _60481 _60482.
Proof. exact (@lem4895308 A _60481 _60482 h1). Qed.
Lemma lem4895310 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) : term192 A P s t.
Proof. exact (@lem4895309 A P (term135 A s t) h1). Qed.
Lemma lem4895313 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term138 A P s t.
Proof. exact (@lem4895310 A P s t h1 (@lem4895265 A P s t h2)). Qed.
Lemma lem4895314 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term193 A P s t.
Proof. exact (fun h0 : term140 A P s t => @lem4895313 A P s t h1 h2). Qed.
Lemma lem4895316 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4895317 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term193 A P s t) = (term138 A P s t).
Proof. exact (@lem4895316 (term138 A P s t)). Qed.
Lemma lem4895318 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term138 A P s t.
Proof. exact (EQ_MP (@lem4895317 A P s t) (@lem4895314 A P s t h1 h2)). Qed.
Lemma lem4895321 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4895323 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term140 A P s t) = (term194 A P s t).
Proof. exact (@lem4895321 (term138 A P s t)). Qed.
Lemma lem4895326 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term194 A P s t.
Proof. exact (EQ_MP (@lem4895323 A P s t) (@lem4895140 A P s t h1)). Qed.
Lemma lem4895329 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : False.
Proof. exact (@lem4895326 A P s t h2 (@lem4895318 A P s t h1 h2)). Qed.
Lemma lem4895330 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term195.
Proof. exact (fun h0 : ~ False => @lem4895329 A P s t h1 h2). Qed.
Lemma lem4895332 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4895333 : term195 = False.
Proof. exact (@lem4895332 False). Qed.
Lemma lem4895334 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : False.
Proof. exact (EQ_MP (@lem4895333) (@lem4895330 A P s t h1 h2)). Qed.
Lemma lem4895335 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term20 A) (h2 : term113 A P s) : False.
Proof. exact (ex_elim (@lem4894879 A P s h2) (fun t : A -> Prop => fun h0 : term112 A P s t => @lem4895334 A P s t h1 h0)). Qed.
Lemma lem4895336 {A : Type'} (P : type686 A) (h1 : term20 A) (h2 : term115 A P) : False.
Proof. exact (ex_elim (@lem4894878 A P h2) (fun s : A -> Prop => fun h0 : term114 A P s => @lem4895335 A P s h1 h0)). Qed.
Lemma lem4895337 {A : Type'} (h1 : term20 A) (h2 : term19 A) : False.
Proof. exact (ex_elim (@lem4894807 A h2) (fun P : type686 A => fun h0 : term116 A P => @lem4895336 A P h1 h0)). Qed.
Lemma lem4895338 {A : Type'} (h1 : term19 A) : term25 A.
Proof. exact (fun h0 : term20 A => @lem4895337 A h0 h1). Qed.
Lemma lem4895339 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem69 (term20 A)). Qed.
Lemma lem4895340 {A : Type'} (h1 : term19 A) : term26 A.
Proof. exact (EQ_MP (@lem4895339 A) (@lem4895338 A h1)). Qed.
Lemma lem4895341 {A : Type'} : term28 A.
Proof. exact (fun h0 : term19 A => @lem4895340 A h0). Qed.
Lemma lem4895342 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem4894537 A) (@lem4895341 A)). Qed.
Lemma lem4895344 {A : Type'} : term21 A.
Proof. exact (@lem4894370 A (@lem4895342 A)). Qed.
Lemma lem4895345 {A : Type'} (h1 : term19 A) : term25 A.
Proof. exact (@lem4895344 A (@lem4894352 A h1)). Qed.
Lemma lem4895346 {A : Type'} (h1 : term19 A) : False.
Proof. exact (@lem4895345 A h1 (@lem4894353 A)). Qed.
Lemma lem4895347 {A : Type'} (h1 : term19 A) : (term19 A) = False.
Proof. exact (prop_ext (fun h2 : term19 A => @lem4895346 A h1) (fun h2 : False => @lem4894352 A h1)). Qed.
Lemma lem4895348 {A : Type'} (h1 : term19 A) : False.
Proof. exact (EQ_MP (@lem4895347 A h1) (@lem4894352 A h1)). Qed.
Lemma lem4895349 {A : Type'} : term18 A.
Proof. exact (fun h0 : term19 A => @lem4895348 A h0). Qed.
Lemma lem4895350 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem4894351 A) (@lem4895349 A)). Qed.
Lemma lem4895351 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem4894347 A) (@lem4895350 A)). Qed.
