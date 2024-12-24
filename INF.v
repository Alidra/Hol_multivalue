Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IN_IMAGE_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import REAL_LE_NEG2_spec.
Require Import REAL_NEG_NEG_spec.
Require Import SUP_spec.
Require Import inf_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19699_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm9425_spec.
Lemma lem5205409 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5205410 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5205411 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5205410 t1) (@lem5205409 t1)). Qed.
Lemma lem5205412 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5205411 t1 t2). Qed.
Lemma lem5205413 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5205414 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5205413 t1 t2) (@lem5205412 t1 t2)). Qed.
Lemma lem5205415 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5205414 t1 t2 t3). Qed.
Lemma lem5205416 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5205417 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5205416 t1 t2 t3) (@lem5205415 t1 t2 t3)). Qed.
Lemma lem5205418 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5205417 t1 t2 t3)). Qed.
Lemma lem5205420 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term7 A s) = (term8 A s).
Proof. exact (h1). Qed.
Lemma lem5205421 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term8 A s) = (term7 A s).
Proof. exact (SYM (@lem5205420 A s h1)). Qed.
Lemma lem5205422 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term8 A s) = (term7 A s).
Proof. exact (h1). Qed.
Lemma lem5205423 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term7 A s) = (term8 A s).
Proof. exact (SYM (@lem5205422 A s h1)). Qed.
Lemma lem5205424 {A : Type'} (s : A -> Prop) : ((term7 A s) = (term8 A s)) = ((term8 A s) = (term7 A s)).
Proof. exact (prop_ext (fun h1 : (term7 A s) = (term8 A s) => @lem5205421 A s h1) (fun h1 : (term8 A s) = (term7 A s) => @lem5205423 A s h1)). Qed.
Lemma lem5205425 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5205424 A s)). Qed.
Lemma lem5205426 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5205427 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem5205426 A) (@lem5205425 A)). Qed.
Lemma lem5205428 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem5205427 A) (@lem3216368 A)). Qed.
Lemma lem5205429 {A B : Type'} (y : B) : term13 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem5205430 {A B : Type'} (y : B) : (term13 A B y) = (term14 A B y).
Proof. exact (eq_refl (term13 A B y)). Qed.
Lemma lem5205431 {A B : Type'} (y : B) : term14 A B y.
Proof. exact (EQ_MP (@lem5205430 A B y) (@lem5205429 A B y)). Qed.
Lemma lem5205432 {A B : Type'} (y : B) (s : A -> Prop) : term15 A B y s.
Proof. exact (@lem5205431 A B y s). Qed.
Lemma lem5205433 {A B : Type'} (y : B) (s : A -> Prop) : (term15 A B y s) = (term16 A B y s).
Proof. exact (eq_refl (term15 A B y s)). Qed.
Lemma lem5205434 {A B : Type'} (y : B) (s : A -> Prop) : term16 A B y s.
Proof. exact (EQ_MP (@lem5205433 A B y s) (@lem5205432 A B y s)). Qed.
Lemma lem5205435 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term17 A B y s f.
Proof. exact (@lem5205434 A B y s f). Qed.
Lemma lem5205436 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term17 A B y s f) = ((term18 A B y f s) = (term19 A B y f s)).
Proof. exact (eq_refl (term17 A B y s f)). Qed.
Lemma lem5205438 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (@lem5205428 A s). Qed.
Lemma lem5205439 {A : Type'} (s : A -> Prop) : (term20 A s) = ((term8 A s) = (term7 A s)).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem5205441 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5205442 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : term22 s.
Proof. exact (ex_intro (term23 s) a (@lem5205441 s a h1)). Qed.
Lemma lem5205443 (s : real -> Prop) (h1 : term22 s) : term22 s.
Proof. exact (h1). Qed.
Lemma lem5205444 (s : real -> Prop) (h1 : term22 s) : term22 s.
Proof. exact (ex_elim (@lem5205443 s h1) (fun a : real => fun h0 : term23 s a => @lem5205442 s a h0)). Qed.
Lemma lem5205445 (s : real -> Prop) : (term21 s) = (term21 s).
Proof. exact (eq_refl (term21 s)). Qed.
Lemma lem5205446 (s : real -> Prop) : term22 s.
Proof. exact (ex_intro (term23 s) (term21 s) (@lem5205445 s)). Qed.
Lemma lem5205447 (s : real -> Prop) : (term22 s) = (term22 s).
Proof. exact (prop_ext (fun h1 : term22 s => @lem5205444 s h1) (fun h1 : term22 s => @lem5205446 s)). Qed.
Lemma lem5205448 (s : real -> Prop) : term22 s.
Proof. exact (EQ_MP (@lem5205447 s) (@lem5205446 s)). Qed.
Lemma lem5205449 (x : real) : term24 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem5205450 (x : real) : (term24 x) = ((term25 x) = x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem5205452 (s : real -> Prop) : term26 s.
Proof. exact (@lem5136700 (@IMAGE real real real_neg s)). Qed.
Lemma lem5205453 (s : real -> Prop) : (term26 s) = (term27 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5205454 (s : real -> Prop) : term27 s.
Proof. exact (EQ_MP (@lem5205453 s) (@lem5205452 s)). Qed.
Lemma lem5205457 (y : real) (x : real) (h1 : (term28 x y) = (real_le y x)) : (term28 x y) = (real_le y x).
Proof. exact (h1). Qed.
Lemma lem5205458 (y : real) (x : real) (h1 : (term28 x y) = (real_le y x)) : (real_le y x) = (term28 x y).
Proof. exact (SYM (@lem5205457 y x h1)). Qed.
Lemma lem5205459 (x : real) (y : real) (h1 : (real_le y x) = (term28 x y)) : (real_le y x) = (term28 x y).
Proof. exact (h1). Qed.
Lemma lem5205460 (x : real) (y : real) (h1 : (real_le y x) = (term28 x y)) : (term28 x y) = (real_le y x).
Proof. exact (SYM (@lem5205459 x y h1)). Qed.
Lemma lem5205461 (x : real) (y : real) : ((term28 x y) = (real_le y x)) = ((real_le y x) = (term28 x y)).
Proof. exact (prop_ext (fun h1 : (term28 x y) = (real_le y x) => @lem5205458 y x h1) (fun h1 : (real_le y x) = (term28 x y) => @lem5205460 x y h1)). Qed.
Lemma lem5205462 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem5205461 x y)). Qed.
Lemma lem5205463 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205464 (x : real) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem5205463) (@lem5205462 x)). Qed.
Lemma lem5205465 : term33 = term34.
Proof. exact (fun_ext (fun x : real => @lem5205464 x)). Qed.
Lemma lem5205466 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205467 : term35 = term36.
Proof. exact (MK_COMB (@lem5205466) (@lem5205465)). Qed.
Lemma lem5205468 : term36.
Proof. exact (EQ_MP (@lem5205467) (@lem1362291)). Qed.
Lemma lem5205469 (x : real) : term37 x.
Proof. exact (@lem5205468 x). Qed.
Lemma lem5205470 (x : real) : (term37 x) = (term32 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem5205471 (x : real) : term32 x.
Proof. exact (EQ_MP (@lem5205470 x) (@lem5205469 x)). Qed.
Lemma lem5205472 (x : real) (y : real) : term38 x y.
Proof. exact (@lem5205471 x y). Qed.
Lemma lem5205473 (x : real) (y : real) : (term38 x y) = ((real_le y x) = (term28 x y)).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem5205475 (s : real -> Prop) : term39 s.
Proof. exact (@lem5204233 s). Qed.
Lemma lem5205476 (s : real -> Prop) : (term39 s) = ((inf s) = (term40 s)).
Proof. exact (eq_refl (term39 s)). Qed.
Lemma lem5205478 (s : real -> Prop) (h1 : term41 s) : term41 s.
Proof. exact (h1). Qed.
Lemma lem5205479 (s : real -> Prop) (h1 : term42 s) : term42 s.
Proof. exact (h1). Qed.
Lemma lem5205480 (s : real -> Prop) (h1 : term43 s) : term43 s.
Proof. exact (h1). Qed.
Lemma lem5205481 (s : real -> Prop) (b : real) (h1 : term44 s b) : term44 s b.
Proof. exact (h1). Qed.
Lemma lem5205491 (s : real -> Prop) : (inf s) = (term40 s).
Proof. exact (EQ_MP (@lem5205476 s) (@lem5205475 s)). Qed.
Lemma lem5205512 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5205513 (s : real -> Prop) : (term45 s) = (term46 s).
Proof. exact (MK_COMB (@lem5205512) (@lem5205491 s)). Qed.
Lemma lem5205514 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5205515 (s : real -> Prop) (x : real) : (term47 s x) = (term48 s x).
Proof. exact (MK_COMB (@lem5205513 s) (@lem5205514 x)). Qed.
Lemma lem5205516 (x : real) (s : real -> Prop) : (term49 x s) = (term49 x s).
Proof. exact (eq_refl (term49 x s)). Qed.
Lemma lem5205517 (s : real -> Prop) (x : real) : (term50 s x) = (term51 s x).
Proof. exact (MK_COMB (@lem5205516 x s) (@lem5205515 s x)). Qed.
Lemma lem5205520 (s : real -> Prop) : (term52 s) = (term53 s).
Proof. exact (fun_ext (fun x : real => @lem5205517 s x)). Qed.
Lemma lem5205521 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205522 (s : real -> Prop) : (term54 s) = (term55 s).
Proof. exact (MK_COMB (@lem5205521) (@lem5205520 s)). Qed.
Lemma lem5205527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5205528 (s : real -> Prop) : (term56 s) = (term57 s).
Proof. exact (MK_COMB (@lem5205527) (@lem5205522 s)). Qed.
Lemma lem5205542 (s : real -> Prop) : (inf s) = (term40 s).
Proof. exact (EQ_MP (@lem5205476 s) (@lem5205475 s)). Qed.
Lemma lem5205563 (b : real) : (real_le b) = (real_le b).
Proof. exact (eq_refl (real_le b)). Qed.
Lemma lem5205564 (b : real) (s : real -> Prop) : (term58 b s) = (term59 b s).
Proof. exact (MK_COMB (@lem5205563 b) (@lem5205542 s)). Qed.
Lemma lem5205565 (s : real -> Prop) (b : real) : (term60 s b) = (term60 s b).
Proof. exact (eq_refl (term60 s b)). Qed.
Lemma lem5205566 (b : real) (s : real -> Prop) : (term61 b s) = (term62 b s).
Proof. exact (MK_COMB (@lem5205565 s b) (@lem5205564 b s)). Qed.
Lemma lem5205569 (s : real -> Prop) : (term63 s) = (term64 s).
Proof. exact (fun_ext (fun b : real => @lem5205566 b s)). Qed.
Lemma lem5205570 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205571 (s : real -> Prop) : (term65 s) = (term66 s).
Proof. exact (MK_COMB (@lem5205570) (@lem5205569 s)). Qed.
Lemma lem5205576 (s : real -> Prop) : (term67 s) = (term68 s).
Proof. exact (MK_COMB (@lem5205528 s) (@lem5205571 s)). Qed.
Lemma lem5205579 (s : real -> Prop) : (term68 s) = (term67 s).
Proof. exact (SYM (@lem5205576 s)). Qed.
Lemma lem5205580 (P : real -> Prop) : (term69 P) = (ex P).
Proof. exact (@lem9425 real P). Qed.
Lemma lem5205581 (s : real -> Prop) : (term70 s) = (term71 s).
Proof. exact (@lem5205580 (term72 s)). Qed.
Lemma lem5205582 (s : real -> Prop) : (term70 s) = (term68 s).
Proof. exact (eq_refl (term70 s)). Qed.
Lemma lem5205583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5205584 (s : real -> Prop) : (term73 s) = (term74 s).
Proof. exact (MK_COMB (@lem5205583) (@lem5205582 s)). Qed.
Lemma lem5205585 (s : real -> Prop) : (term71 s) = (term71 s).
Proof. exact (eq_refl (term71 s)). Qed.
Lemma lem5205586 (s : real -> Prop) : ((term70 s) = (term71 s)) = ((term68 s) = (term71 s)).
Proof. exact (MK_COMB (@lem5205584 s) (@lem5205585 s)). Qed.
Lemma lem5205587 (s : real -> Prop) : (term68 s) = (term71 s).
Proof. exact (EQ_MP (@lem5205586 s) (@lem5205581 s)). Qed.
Lemma lem5205588 (s : real -> Prop) : (term71 s) = (term68 s).
Proof. exact (SYM (@lem5205587 s)). Qed.
Lemma lem5205602 (x : real) (y : real) : (real_le y x) = (term28 x y).
Proof. exact (EQ_MP (@lem5205473 x y) (@lem5205472 x y)). Qed.
Lemma lem5205603 (x : real) (a : real) : (real_le a x) = (term28 x a).
Proof. exact (@lem5205602 x a). Qed.
Lemma lem5205604 (x : real) (s : real -> Prop) : (term49 x s) = (term49 x s).
Proof. exact (eq_refl (term49 x s)). Qed.
Lemma lem5205605 (s : real -> Prop) (x : real) (a : real) : (term75 s a x) = (term76 s x a).
Proof. exact (MK_COMB (@lem5205604 x s) (@lem5205603 x a)). Qed.
Lemma lem5205606 (s : real -> Prop) (a : real) : (term77 s a) = (term78 s a).
Proof. exact (fun_ext (fun x : real => @lem5205605 s x a)). Qed.
Lemma lem5205607 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205608 (s : real -> Prop) (a : real) : (term44 s a) = (term79 s a).
Proof. exact (MK_COMB (@lem5205607) (@lem5205606 s a)). Qed.
Lemma lem5205609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5205610 (s : real -> Prop) (a : real) : (term80 s a) = (term81 s a).
Proof. exact (MK_COMB (@lem5205609) (@lem5205608 s a)). Qed.
Lemma lem5205624 (x : real) (y : real) : (real_le y x) = (term28 x y).
Proof. exact (EQ_MP (@lem5205473 x y) (@lem5205472 x y)). Qed.
Lemma lem5205625 (x : real) (b : real) : (real_le b x) = (term28 x b).
Proof. exact (@lem5205624 x b). Qed.
Lemma lem5205626 (x : real) (s : real -> Prop) : (term49 x s) = (term49 x s).
Proof. exact (eq_refl (term49 x s)). Qed.
Lemma lem5205627 (s : real -> Prop) (x : real) (b : real) : (term75 s b x) = (term76 s x b).
Proof. exact (MK_COMB (@lem5205626 x s) (@lem5205625 x b)). Qed.
Lemma lem5205628 (s : real -> Prop) (b : real) : (term77 s b) = (term78 s b).
Proof. exact (fun_ext (fun x : real => @lem5205627 s x b)). Qed.
Lemma lem5205629 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205630 (s : real -> Prop) (b : real) : (term44 s b) = (term79 s b).
Proof. exact (MK_COMB (@lem5205629) (@lem5205628 s b)). Qed.
Lemma lem5205631 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5205632 (s : real -> Prop) (b : real) : (term60 s b) = (term82 s b).
Proof. exact (MK_COMB (@lem5205631) (@lem5205630 s b)). Qed.
Lemma lem5205634 (x : real) (y : real) : (real_le y x) = (term28 x y).
Proof. exact (EQ_MP (@lem5205473 x y) (@lem5205472 x y)). Qed.
Lemma lem5205635 (a : real) (b : real) : (real_le b a) = (term28 a b).
Proof. exact (@lem5205634 a b). Qed.
Lemma lem5205636 (s : real -> Prop) (a : real) (b : real) : (term83 s b a) = (term84 s a b).
Proof. exact (MK_COMB (@lem5205632 s b) (@lem5205635 a b)). Qed.
Lemma lem5205637 (s : real -> Prop) (a : real) : (term85 s a) = (term86 s a).
Proof. exact (fun_ext (fun b : real => @lem5205636 s a b)). Qed.
Lemma lem5205638 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205639 (s : real -> Prop) (a : real) : (term87 s a) = (term88 s a).
Proof. exact (MK_COMB (@lem5205638) (@lem5205637 s a)). Qed.
Lemma lem5205640 (s : real -> Prop) (a : real) : (term89 s a) = (term90 s a).
Proof. exact (MK_COMB (@lem5205610 s a) (@lem5205639 s a)). Qed.
Lemma lem5205641 (s : real -> Prop) : (term72 s) = (term91 s).
Proof. exact (fun_ext (fun a : real => @lem5205640 s a)). Qed.
Lemma lem5205642 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5205643 (s : real -> Prop) : (term71 s) = (term92 s).
Proof. exact (MK_COMB (@lem5205642) (@lem5205641 s)). Qed.
Lemma lem5205644 (s : real -> Prop) : (term92 s) = (term71 s).
Proof. exact (SYM (@lem5205643 s)). Qed.
Lemma lem5205692 (x : real) : (term25 x) = x.
Proof. exact (EQ_MP (@lem5205450 x) (@lem5205449 x)). Qed.
Lemma lem5205693 (s : real -> Prop) : (term93 s) = (term21 s).
Proof. exact (@lem5205692 (term21 s)). Qed.
Lemma lem5205694 (x : real) : (term94 x) = (term94 x).
Proof. exact (eq_refl (term94 x)). Qed.
Lemma lem5205695 (x : real) (s : real -> Prop) : (term95 x s) = (term96 x s).
Proof. exact (MK_COMB (@lem5205694 x) (@lem5205693 s)). Qed.
Lemma lem5205696 (x : real) (s : real -> Prop) : (term49 x s) = (term49 x s).
Proof. exact (eq_refl (term49 x s)). Qed.
Lemma lem5205697 (x : real) (s : real -> Prop) : (term97 x s) = (term98 x s).
Proof. exact (MK_COMB (@lem5205696 x s) (@lem5205695 x s)). Qed.
Lemma lem5205700 (s : real -> Prop) : (term99 s) = (term100 s).
Proof. exact (fun_ext (fun x : real => @lem5205697 x s)). Qed.
Lemma lem5205701 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205702 (s : real -> Prop) : (term101 s) = (term102 s).
Proof. exact (MK_COMB (@lem5205701) (@lem5205700 s)). Qed.
Lemma lem5205707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5205708 (s : real -> Prop) : (term103 s) = (term104 s).
Proof. exact (MK_COMB (@lem5205707) (@lem5205702 s)). Qed.
Lemma lem5205722 (x : real) : (term25 x) = x.
Proof. exact (EQ_MP (@lem5205450 x) (@lem5205449 x)). Qed.
Lemma lem5205723 (s : real -> Prop) : (term93 s) = (term21 s).
Proof. exact (@lem5205722 (term21 s)). Qed.
Lemma lem5205724 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5205725 (s : real -> Prop) : (term105 s) = (term106 s).
Proof. exact (MK_COMB (@lem5205724) (@lem5205723 s)). Qed.
Lemma lem5205726 (b : real) : (real_neg b) = (real_neg b).
Proof. exact (eq_refl (real_neg b)). Qed.
Lemma lem5205727 (s : real -> Prop) (b : real) : (term107 s b) = (term108 s b).
Proof. exact (MK_COMB (@lem5205725 s) (@lem5205726 b)). Qed.
Lemma lem5205728 (s : real -> Prop) (b : real) : (term82 s b) = (term82 s b).
Proof. exact (eq_refl (term82 s b)). Qed.
Lemma lem5205729 (s : real -> Prop) (b : real) : (term109 s b) = (term110 s b).
Proof. exact (MK_COMB (@lem5205728 s b) (@lem5205727 s b)). Qed.
Lemma lem5205732 (s : real -> Prop) : (term111 s) = (term112 s).
Proof. exact (fun_ext (fun b : real => @lem5205729 s b)). Qed.
Lemma lem5205733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205734 (s : real -> Prop) : (term113 s) = (term114 s).
Proof. exact (MK_COMB (@lem5205733) (@lem5205732 s)). Qed.
Lemma lem5205739 (s : real -> Prop) : (term115 s) = (term116 s).
Proof. exact (MK_COMB (@lem5205708 s) (@lem5205734 s)). Qed.
Lemma lem5205742 (s : real -> Prop) : (term117 s) = (term117 s).
Proof. exact (eq_refl (term117 s)). Qed.
Lemma lem5205743 (s : real -> Prop) : (term118 s) = (term119 s).
Proof. exact (MK_COMB (@lem5205742 s) (@lem5205739 s)). Qed.
Lemma lem5205746 (s : real -> Prop) : (term119 s) = (term118 s).
Proof. exact (SYM (@lem5205743 s)). Qed.
Lemma lem5205747 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5205749 (s : real -> Prop) (h1 : term43 s) : term43 s.
Proof. exact (h1). Qed.
Lemma lem5205751 (s : real -> Prop) (b : real) (h1 : term44 s b) : term44 s b.
Proof. exact (h1). Qed.
Lemma lem5205753 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5205754 (x : real) : (real_le x) = (real_le x).
Proof. exact (eq_refl (real_le x)). Qed.
Lemma lem5205755 (x : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term120 x s) = (real_le x a).
Proof. exact (MK_COMB (@lem5205754 x) (@lem5205753 s a h1)). Qed.
Lemma lem5205756 (x : real) (s : real -> Prop) : (term121 x s) = (term121 x s).
Proof. exact (eq_refl (term121 x s)). Qed.
Lemma lem5205757 (x : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term122 x s) = (term123 s x a).
Proof. exact (MK_COMB (@lem5205756 x s) (@lem5205755 x s a h1)). Qed.
Lemma lem5205758 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term124 s) = (term125 s a).
Proof. exact (fun_ext (fun x : real => @lem5205757 x s a h1)). Qed.
Lemma lem5205759 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205760 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term126 s) = (term127 s a).
Proof. exact (MK_COMB (@lem5205759) (@lem5205758 s a h1)). Qed.
Lemma lem5205761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5205762 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term128 s) = (term129 s a).
Proof. exact (MK_COMB (@lem5205761) (@lem5205760 s a h1)). Qed.
Lemma lem5205764 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5205765 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5205766 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term106 s) = (real_le a).
Proof. exact (MK_COMB (@lem5205765) (@lem5205764 s a h1)). Qed.
Lemma lem5205767 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5205768 (b : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term130 s b) = (real_le a b).
Proof. exact (MK_COMB (@lem5205766 s a h1) (@lem5205767 b)). Qed.
Lemma lem5205769 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (eq_refl (term131 s b)). Qed.
Lemma lem5205770 (b : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term132 s b) = (term133 s a b).
Proof. exact (MK_COMB (@lem5205769 s b) (@lem5205768 b s a h1)). Qed.
Lemma lem5205771 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term134 s) = (term135 s a).
Proof. exact (fun_ext (fun b : real => @lem5205770 b s a h1)). Qed.
Lemma lem5205772 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205773 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term136 s) = (term137 s a).
Proof. exact (MK_COMB (@lem5205772) (@lem5205771 s a h1)). Qed.
Lemma lem5205774 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term138 s) = (term139 s a).
Proof. exact (MK_COMB (@lem5205762 s a h1) (@lem5205773 s a h1)). Qed.
Lemma lem5205775 (s : real -> Prop) : (term140 s) = (term140 s).
Proof. exact (eq_refl (term140 s)). Qed.
Lemma lem5205776 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term27 s) = (term141 s a).
Proof. exact (MK_COMB (@lem5205775 s) (@lem5205774 s a h1)). Qed.
Lemma lem5205777 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5205778 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term117 s) = (term142 s a).
Proof. exact (MK_COMB (@lem5205777) (@lem5205776 s a h1)). Qed.
Lemma lem5205780 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5205781 (x : real) : (term94 x) = (term94 x).
Proof. exact (eq_refl (term94 x)). Qed.
Lemma lem5205782 (x : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term96 x s) = (term143 x a).
Proof. exact (MK_COMB (@lem5205781 x) (@lem5205780 s a h1)). Qed.
Lemma lem5205783 (x : real) (s : real -> Prop) : (term49 x s) = (term49 x s).
Proof. exact (eq_refl (term49 x s)). Qed.
Lemma lem5205784 (x : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term98 x s) = (term144 s x a).
Proof. exact (MK_COMB (@lem5205783 x s) (@lem5205782 x s a h1)). Qed.
Lemma lem5205785 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term100 s) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5205784 x s a h1)). Qed.
Lemma lem5205786 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205787 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term102 s) = (term146 s a).
Proof. exact (MK_COMB (@lem5205786) (@lem5205785 s a h1)). Qed.
Lemma lem5205788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5205789 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term104 s) = (term147 s a).
Proof. exact (MK_COMB (@lem5205788) (@lem5205787 s a h1)). Qed.
Lemma lem5205791 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5205792 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5205793 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term106 s) = (real_le a).
Proof. exact (MK_COMB (@lem5205792) (@lem5205791 s a h1)). Qed.
Lemma lem5205794 (b : real) : (real_neg b) = (real_neg b).
Proof. exact (eq_refl (real_neg b)). Qed.
Lemma lem5205795 (b : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term108 s b) = (term148 a b).
Proof. exact (MK_COMB (@lem5205793 s a h1) (@lem5205794 b)). Qed.
Lemma lem5205796 (s : real -> Prop) (b : real) : (term82 s b) = (term82 s b).
Proof. exact (eq_refl (term82 s b)). Qed.
Lemma lem5205797 (b : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term110 s b) = (term149 s a b).
Proof. exact (MK_COMB (@lem5205796 s b) (@lem5205795 b s a h1)). Qed.
Lemma lem5205798 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term112 s) = (term150 s a).
Proof. exact (fun_ext (fun b : real => @lem5205797 b s a h1)). Qed.
Lemma lem5205799 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205800 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term114 s) = (term151 s a).
Proof. exact (MK_COMB (@lem5205799) (@lem5205798 s a h1)). Qed.
Lemma lem5205801 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term116 s) = (term152 s a).
Proof. exact (MK_COMB (@lem5205789 s a h1) (@lem5205800 s a h1)). Qed.
Lemma lem5205802 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term119 s) = (term153 s a).
Proof. exact (MK_COMB (@lem5205778 s a h1) (@lem5205801 s a h1)). Qed.
Lemma lem5205803 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term153 s a) = (term119 s).
Proof. exact (SYM (@lem5205802 s a h1)). Qed.
Lemma lem5205811 {A : Type'} (s : A -> Prop) : (term8 A s) = (term7 A s).
Proof. exact (EQ_MP (@lem5205439 A s) (@lem5205438 A s)). Qed.
Lemma lem5205812 (s : real -> Prop) : (term43 s) = (term154 s).
Proof. exact (@lem5205811 real s). Qed.
Lemma lem5205813 (s : real -> Prop) : (term155 s) = (term156 s).
Proof. exact (@lem5205812 (@IMAGE real real real_neg s)). Qed.
Lemma lem5205819 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term18 A B y f s) = (term19 A B y f s).
Proof. exact (EQ_MP (@lem5205436 A B y f s) (@lem5205435 A B y s f)). Qed.
Lemma lem5205820 (y : real) (f : real -> real) (s : real -> Prop) : (term157 y f s) = (term158 y f s).
Proof. exact (@lem5205819 real real y f s). Qed.
Lemma lem5205821 (x : real) (s : real -> Prop) : (term159 x s) = (term160 x s).
Proof. exact (@lem5205820 x real_neg s). Qed.
Lemma lem5205830 (s : real -> Prop) : (term161 s) = (term162 s).
Proof. exact (fun_ext (fun x : real => @lem5205821 x s)). Qed.
Lemma lem5205831 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5205832 (s : real -> Prop) : (term156 s) = (term163 s).
Proof. exact (MK_COMB (@lem5205831) (@lem5205830 s)). Qed.
Lemma lem5205837 (s : real -> Prop) : (term155 s) = (term163 s).
Proof. exact (TRANS (@lem5205813 s) (@lem5205832 s)). Qed.
Lemma lem5205838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5205839 (s : real -> Prop) : (term164 s) = (term165 s).
Proof. exact (MK_COMB (@lem5205838) (@lem5205837 s)). Qed.
Lemma lem5205851 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term18 A B y f s) = (term19 A B y f s).
Proof. exact (EQ_MP (@lem5205436 A B y f s) (@lem5205435 A B y s f)). Qed.
Lemma lem5205852 (y : real) (f : real -> real) (s : real -> Prop) : (term157 y f s) = (term158 y f s).
Proof. exact (@lem5205851 real real y f s). Qed.
Lemma lem5205853 (x : real) (s : real -> Prop) : (term159 x s) = (term160 x s).
Proof. exact (@lem5205852 x real_neg s). Qed.
Lemma lem5205862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5205863 (x : real) (s : real -> Prop) : (term121 x s) = (term166 x s).
Proof. exact (MK_COMB (@lem5205862) (@lem5205853 x s)). Qed.
Lemma lem5205864 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5205865 (s : real -> Prop) (x : real) (b : real) : (term123 s x b) = (term167 s x b).
Proof. exact (MK_COMB (@lem5205863 x s) (@lem5205864 x b)). Qed.
Lemma lem5205868 (s : real -> Prop) (b : real) : (term125 s b) = (term168 s b).
Proof. exact (fun_ext (fun x : real => @lem5205865 s x b)). Qed.
Lemma lem5205869 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205870 (s : real -> Prop) (b : real) : (term127 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5205869) (@lem5205868 s b)). Qed.
Lemma lem5205875 (s : real -> Prop) : (term170 s) = (term171 s).
Proof. exact (fun_ext (fun b : real => @lem5205870 s b)). Qed.
Lemma lem5205876 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5205877 (s : real -> Prop) : (term172 s) = (term173 s).
Proof. exact (MK_COMB (@lem5205876) (@lem5205875 s)). Qed.
Lemma lem5205882 (s : real -> Prop) : (term174 s) = (term175 s).
Proof. exact (MK_COMB (@lem5205839 s) (@lem5205877 s)). Qed.
Lemma lem5205885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5205886 (s : real -> Prop) : (term140 s) = (term176 s).
Proof. exact (MK_COMB (@lem5205885) (@lem5205882 s)). Qed.
Lemma lem5205896 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term18 A B y f s) = (term19 A B y f s).
Proof. exact (EQ_MP (@lem5205436 A B y f s) (@lem5205435 A B y s f)). Qed.
Lemma lem5205897 (y : real) (f : real -> real) (s : real -> Prop) : (term157 y f s) = (term158 y f s).
Proof. exact (@lem5205896 real real y f s). Qed.
Lemma lem5205898 (x : real) (s : real -> Prop) : (term159 x s) = (term160 x s).
Proof. exact (@lem5205897 x real_neg s). Qed.
Lemma lem5205907 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5205908 (x : real) (s : real -> Prop) : (term121 x s) = (term166 x s).
Proof. exact (MK_COMB (@lem5205907) (@lem5205898 x s)). Qed.
Lemma lem5205909 (x : real) (a : real) : (real_le x a) = (real_le x a).
Proof. exact (eq_refl (real_le x a)). Qed.
Lemma lem5205910 (s : real -> Prop) (x : real) (a : real) : (term123 s x a) = (term167 s x a).
Proof. exact (MK_COMB (@lem5205908 x s) (@lem5205909 x a)). Qed.
Lemma lem5205913 (s : real -> Prop) (a : real) : (term125 s a) = (term168 s a).
Proof. exact (fun_ext (fun x : real => @lem5205910 s x a)). Qed.
Lemma lem5205914 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205915 (s : real -> Prop) (a : real) : (term127 s a) = (term169 s a).
Proof. exact (MK_COMB (@lem5205914) (@lem5205913 s a)). Qed.
Lemma lem5205920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5205921 (s : real -> Prop) (a : real) : (term129 s a) = (term177 s a).
Proof. exact (MK_COMB (@lem5205920) (@lem5205915 s a)). Qed.
Lemma lem5205935 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term18 A B y f s) = (term19 A B y f s).
Proof. exact (EQ_MP (@lem5205436 A B y f s) (@lem5205435 A B y s f)). Qed.
Lemma lem5205936 (y : real) (f : real -> real) (s : real -> Prop) : (term157 y f s) = (term158 y f s).
Proof. exact (@lem5205935 real real y f s). Qed.
Lemma lem5205937 (x : real) (s : real -> Prop) : (term159 x s) = (term160 x s).
Proof. exact (@lem5205936 x real_neg s). Qed.
Lemma lem5205946 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5205947 (x : real) (s : real -> Prop) : (term121 x s) = (term166 x s).
Proof. exact (MK_COMB (@lem5205946) (@lem5205937 x s)). Qed.
Lemma lem5205948 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5205949 (s : real -> Prop) (x : real) (b : real) : (term123 s x b) = (term167 s x b).
Proof. exact (MK_COMB (@lem5205947 x s) (@lem5205948 x b)). Qed.
Lemma lem5205952 (s : real -> Prop) (b : real) : (term125 s b) = (term168 s b).
Proof. exact (fun_ext (fun x : real => @lem5205949 s x b)). Qed.
Lemma lem5205953 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205954 (s : real -> Prop) (b : real) : (term127 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5205953) (@lem5205952 s b)). Qed.
Lemma lem5205959 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5205960 (s : real -> Prop) (b : real) : (term131 s b) = (term178 s b).
Proof. exact (MK_COMB (@lem5205959) (@lem5205954 s b)). Qed.
Lemma lem5205961 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5205962 (s : real -> Prop) (a : real) (b : real) : (term133 s a b) = (term179 s a b).
Proof. exact (MK_COMB (@lem5205960 s b) (@lem5205961 a b)). Qed.
Lemma lem5205965 (s : real -> Prop) (a : real) : (term135 s a) = (term180 s a).
Proof. exact (fun_ext (fun b : real => @lem5205962 s a b)). Qed.
Lemma lem5205966 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5205967 (s : real -> Prop) (a : real) : (term137 s a) = (term181 s a).
Proof. exact (MK_COMB (@lem5205966) (@lem5205965 s a)). Qed.
Lemma lem5205972 (s : real -> Prop) (a : real) : (term139 s a) = (term182 s a).
Proof. exact (MK_COMB (@lem5205921 s a) (@lem5205967 s a)). Qed.
Lemma lem5205975 (s : real -> Prop) (a : real) : (term141 s a) = (term183 s a).
Proof. exact (MK_COMB (@lem5205886 s) (@lem5205972 s a)). Qed.
Lemma lem5205978 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5205979 (s : real -> Prop) (a : real) : (term142 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5205978) (@lem5205975 s a)). Qed.
Lemma lem5206000 (s : real -> Prop) (a : real) : (term152 s a) = (term152 s a).
Proof. exact (eq_refl (term152 s a)). Qed.
Lemma lem5206001 (s : real -> Prop) (a : real) : (term153 s a) = (term185 s a).
Proof. exact (MK_COMB (@lem5205979 s a) (@lem5206000 s a)). Qed.
Lemma lem5206004 (s : real -> Prop) (a : real) : (term185 s a) = (term153 s a).
Proof. exact (SYM (@lem5206001 s a)). Qed.
Lemma lem5206006 (p : Prop) : p = (term186 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5206007 (s : real -> Prop) (a : real) : (term185 s a) = (term187 s a).
Proof. exact (@lem5206006 (term185 s a)). Qed.
Lemma lem5206008 (s : real -> Prop) (a : real) : (term187 s a) = (term185 s a).
Proof. exact (SYM (@lem5206007 s a)). Qed.
Lemma lem5206009 (s : real -> Prop) (a : real) (h1 : term188 s a) : term188 s a.
Proof. exact (h1). Qed.
Lemma lem5206010 : term189.
Proof. exact (@lem3216368 real). Qed.
Lemma lem5206015 (b : real) (s : real -> Prop) (a : real) (h1 : term190 b s a) : term190 b s a.
Proof. exact (h1). Qed.
Lemma lem5206016 (b : real) (s : real -> Prop) (a : real) : term191 b s a.
Proof. exact (fun h0 : term190 b s a => @lem5206015 b s a h0). Qed.
Lemma lem5206017 (b : real) (s : real -> Prop) (a : real) (h1 : term191 b s a) : term191 b s a.
Proof. exact (h1). Qed.
Lemma lem5206018 (b : real) (s : real -> Prop) (a : real) (h1 : term190 b s a) : term190 b s a.
Proof. exact (h1). Qed.
Lemma lem5206019 (b : real) (s : real -> Prop) (a : real) (h1 : term190 b s a) (h2 : term191 b s a) : term190 b s a.
Proof. exact (@lem5206017 b s a h2 (@lem5206018 b s a h1)). Qed.
Lemma lem5206020 (b : real) (s : real -> Prop) (a : real) (h1 : term190 b s a) : term192 b s a.
Proof. exact (fun h0 : term191 b s a => @lem5206019 b s a h1 h0). Qed.
Lemma lem5206021 (b : real) (s : real -> Prop) (a : real) (h1 : term191 b s a) : term191 b s a.
Proof. exact (h1). Qed.
Lemma lem5206022 (b : real) (s : real -> Prop) (a : real) (h1 : term190 b s a) (h2 : term191 b s a) : term190 b s a.
Proof. exact (@lem5206020 b s a h1 (@lem5206021 b s a h2)). Qed.
Lemma lem5206023 (b : real) (s : real -> Prop) (a : real) (h1 : term191 b s a) : term191 b s a.
Proof. exact (fun h0 : term190 b s a => @lem5206022 b s a h0 h1). Qed.
Lemma lem5206024 (b : real) (s : real -> Prop) (a : real) : term193 b s a.
Proof. exact (fun h0 : term191 b s a => @lem5206023 b s a h0). Qed.
Lemma lem5206027 (b : real) (s : real -> Prop) (a : real) : term191 b s a.
Proof. exact (@lem5206024 b s a (@lem5206016 b s a)). Qed.
Lemma lem5206335 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5206336 : term194 = term195.
Proof. exact (@lem5206335 term196). Qed.
Lemma lem5206341 : term197 = term197.
Proof. exact (eq_refl term197). Qed.
Lemma lem5206342 : term198 = term199.
Proof. exact (MK_COMB (@lem5206341) (@lem5206336)). Qed.
Lemma lem5206345 : term200 = term200.
Proof. exact (eq_refl term200). Qed.
Lemma lem5206346 : term201 = term202.
Proof. exact (MK_COMB (@lem5206345) (@lem5206342)). Qed.
Lemma lem5206349 (s : real -> Prop) (a : real) : (term203 s a) = (term203 s a).
Proof. exact (eq_refl (term203 s a)). Qed.
Lemma lem5206350 (s : real -> Prop) (a : real) : (term204 s a) = (term205 s a).
Proof. exact (MK_COMB (@lem5206349 s a) (@lem5206346)). Qed.
Lemma lem5206353 (s : real -> Prop) (a : real) : (term206 s a) = (term206 s a).
Proof. exact (eq_refl (term206 s a)). Qed.
Lemma lem5206354 (s : real -> Prop) (a : real) : (term207 s a) = (term208 s a).
Proof. exact (MK_COMB (@lem5206353 s a) (@lem5206350 s a)). Qed.
Lemma lem5206357 (s : real -> Prop) (b : real) : (term60 s b) = (term60 s b).
Proof. exact (eq_refl (term60 s b)). Qed.
Lemma lem5206358 (b : real) (s : real -> Prop) (a : real) : (term209 b s a) = (term210 b s a).
Proof. exact (MK_COMB (@lem5206357 s b) (@lem5206354 s a)). Qed.
Lemma lem5206361 (s : real -> Prop) : (term211 s) = (term211 s).
Proof. exact (eq_refl (term211 s)). Qed.
Lemma lem5206362 (b : real) (s : real -> Prop) (a : real) : (term190 b s a) = (term212 b s a).
Proof. exact (MK_COMB (@lem5206361 s) (@lem5206358 b s a)). Qed.
Lemma lem5206365 (s : real -> Prop) (a : real) : (term213 s a) = (term214 s a).
Proof. exact (fun_ext (fun b : real => @lem5206362 b s a)). Qed.
Lemma lem5206366 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206367 (s : real -> Prop) (a : real) : (term215 s a) = (term216 s a).
Proof. exact (MK_COMB (@lem5206366) (@lem5206365 s a)). Qed.
Lemma lem5206372 (a : real) : (term217 a) = (term218 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5206367 s a)). Qed.
Lemma lem5206373 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5206374 (a : real) : (term219 a) = (term220 a).
Proof. exact (MK_COMB (@lem5206373) (@lem5206372 a)). Qed.
Lemma lem5206379 : term221 = term222.
Proof. exact (fun_ext (fun a : real => @lem5206374 a)). Qed.
Lemma lem5206380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206389 : term223 = term224.
Proof. exact (MK_COMB (@lem5206380) (@lem5206379)). Qed.
Lemma lem5206390 (x : real) : ((term25 x) = x) = ((term25 x) = x).
Proof. exact (eq_refl ((term25 x) = x)). Qed.
Lemma lem5206391 : term225 = term225.
Proof. exact (fun_ext (fun x : real => @lem5206390 x)). Qed.
Lemma lem5206392 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206393 : term196 = term196.
Proof. exact (MK_COMB (@lem5206392) (@lem5206391)). Qed.
Lemma lem5206394 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206395 : term195 = term195.
Proof. exact (MK_COMB (@lem5206394) (@lem5206393)). Qed.
Lemma lem5206398 (s : real -> Prop) : (term43 s) = (term43 s).
Proof. exact (eq_refl (term43 s)). Qed.
Lemma lem5206399 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5206400 (s : real -> Prop) : (term226 s) = (term226 s).
Proof. exact (fun_ext (fun x : real => @lem5206399 x s)). Qed.
Lemma lem5206401 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206402 (s : real -> Prop) : (term154 s) = (term154 s).
Proof. exact (MK_COMB (@lem5206401) (@lem5206400 s)). Qed.
Lemma lem5206403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5206404 (s : real -> Prop) : (term227 s) = (term227 s).
Proof. exact (MK_COMB (@lem5206403) (@lem5206402 s)). Qed.
Lemma lem5206405 (s : real -> Prop) : ((term154 s) = (term43 s)) = ((term154 s) = (term43 s)).
Proof. exact (MK_COMB (@lem5206404 s) (@lem5206398 s)). Qed.
Lemma lem5206406 : term228 = term228.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5206405 s)). Qed.
Lemma lem5206407 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5206408 : term189 = term189.
Proof. exact (MK_COMB (@lem5206407) (@lem5206406)). Qed.
Lemma lem5206409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206410 : term197 = term197.
Proof. exact (MK_COMB (@lem5206409) (@lem5206408)). Qed.
Lemma lem5206411 : term199 = term199.
Proof. exact (MK_COMB (@lem5206410) (@lem5206395)). Qed.
Lemma lem5206416 (y : real) (x : real) : ((term28 x y) = (real_le y x)) = ((term28 x y) = (real_le y x)).
Proof. exact (eq_refl ((term28 x y) = (real_le y x))). Qed.
Lemma lem5206417 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem5206416 y x)). Qed.
Lemma lem5206418 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206419 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem5206418) (@lem5206417 x)). Qed.
Lemma lem5206420 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem5206419 x)). Qed.
Lemma lem5206421 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206422 : term35 = term35.
Proof. exact (MK_COMB (@lem5206421) (@lem5206420)). Qed.
Lemma lem5206423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206424 : term200 = term200.
Proof. exact (MK_COMB (@lem5206423) (@lem5206422)). Qed.
Lemma lem5206425 : term202 = term202.
Proof. exact (MK_COMB (@lem5206424) (@lem5206411)). Qed.
Lemma lem5206426 (a : real) (b : real) : (term148 a b) = (term148 a b).
Proof. exact (eq_refl (term148 a b)). Qed.
Lemma lem5206431 (s : real -> Prop) (x : real) (b : real) : (term76 s x b) = (term76 s x b).
Proof. exact (eq_refl (term76 s x b)). Qed.
Lemma lem5206432 (s : real -> Prop) (b : real) : (term78 s b) = (term78 s b).
Proof. exact (fun_ext (fun x : real => @lem5206431 s x b)). Qed.
Lemma lem5206433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206434 (s : real -> Prop) (b : real) : (term79 s b) = (term79 s b).
Proof. exact (MK_COMB (@lem5206433) (@lem5206432 s b)). Qed.
Lemma lem5206435 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206436 (s : real -> Prop) (b : real) : (term82 s b) = (term82 s b).
Proof. exact (MK_COMB (@lem5206435) (@lem5206434 s b)). Qed.
Lemma lem5206437 (s : real -> Prop) (a : real) (b : real) : (term149 s a b) = (term149 s a b).
Proof. exact (MK_COMB (@lem5206436 s b) (@lem5206426 a b)). Qed.
Lemma lem5206438 (s : real -> Prop) (a : real) : (term150 s a) = (term150 s a).
Proof. exact (fun_ext (fun b : real => @lem5206437 s a b)). Qed.
Lemma lem5206439 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206440 (s : real -> Prop) (a : real) : (term151 s a) = (term151 s a).
Proof. exact (MK_COMB (@lem5206439) (@lem5206438 s a)). Qed.
Lemma lem5206445 (s : real -> Prop) (x : real) (a : real) : (term144 s x a) = (term144 s x a).
Proof. exact (eq_refl (term144 s x a)). Qed.
Lemma lem5206446 (s : real -> Prop) (a : real) : (term145 s a) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5206445 s x a)). Qed.
Lemma lem5206447 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206448 (s : real -> Prop) (a : real) : (term146 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5206447) (@lem5206446 s a)). Qed.
Lemma lem5206449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5206450 (s : real -> Prop) (a : real) : (term147 s a) = (term147 s a).
Proof. exact (MK_COMB (@lem5206449) (@lem5206448 s a)). Qed.
Lemma lem5206451 (s : real -> Prop) (a : real) : (term152 s a) = (term152 s a).
Proof. exact (MK_COMB (@lem5206450 s a) (@lem5206440 s a)). Qed.
Lemma lem5206452 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5206453 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5206458 (x : real) (x' : real) (s : real -> Prop) : (term229 x x' s) = (term229 x x' s).
Proof. exact (eq_refl (term229 x x' s)). Qed.
Lemma lem5206459 (x : real) (s : real -> Prop) : (term230 x s) = (term230 x s).
Proof. exact (fun_ext (fun x' : real => @lem5206458 x x' s)). Qed.
Lemma lem5206460 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206461 (x : real) (s : real -> Prop) : (term160 x s) = (term160 x s).
Proof. exact (MK_COMB (@lem5206460) (@lem5206459 x s)). Qed.
Lemma lem5206462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206463 (x : real) (s : real -> Prop) : (term166 x s) = (term166 x s).
Proof. exact (MK_COMB (@lem5206462) (@lem5206461 x s)). Qed.
Lemma lem5206464 (s : real -> Prop) (x : real) (b : real) : (term167 s x b) = (term167 s x b).
Proof. exact (MK_COMB (@lem5206463 x s) (@lem5206453 x b)). Qed.
Lemma lem5206465 (s : real -> Prop) (b : real) : (term168 s b) = (term168 s b).
Proof. exact (fun_ext (fun x : real => @lem5206464 s x b)). Qed.
Lemma lem5206466 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206467 (s : real -> Prop) (b : real) : (term169 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5206466) (@lem5206465 s b)). Qed.
Lemma lem5206468 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206469 (s : real -> Prop) (b : real) : (term178 s b) = (term178 s b).
Proof. exact (MK_COMB (@lem5206468) (@lem5206467 s b)). Qed.
Lemma lem5206470 (s : real -> Prop) (a : real) (b : real) : (term179 s a b) = (term179 s a b).
Proof. exact (MK_COMB (@lem5206469 s b) (@lem5206452 a b)). Qed.
Lemma lem5206471 (s : real -> Prop) (a : real) : (term180 s a) = (term180 s a).
Proof. exact (fun_ext (fun b : real => @lem5206470 s a b)). Qed.
Lemma lem5206472 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206473 (s : real -> Prop) (a : real) : (term181 s a) = (term181 s a).
Proof. exact (MK_COMB (@lem5206472) (@lem5206471 s a)). Qed.
Lemma lem5206474 (x : real) (a : real) : (real_le x a) = (real_le x a).
Proof. exact (eq_refl (real_le x a)). Qed.
Lemma lem5206479 (x : real) (x' : real) (s : real -> Prop) : (term229 x x' s) = (term229 x x' s).
Proof. exact (eq_refl (term229 x x' s)). Qed.
Lemma lem5206480 (x : real) (s : real -> Prop) : (term230 x s) = (term230 x s).
Proof. exact (fun_ext (fun x' : real => @lem5206479 x x' s)). Qed.
Lemma lem5206481 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206482 (x : real) (s : real -> Prop) : (term160 x s) = (term160 x s).
Proof. exact (MK_COMB (@lem5206481) (@lem5206480 x s)). Qed.
Lemma lem5206483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206484 (x : real) (s : real -> Prop) : (term166 x s) = (term166 x s).
Proof. exact (MK_COMB (@lem5206483) (@lem5206482 x s)). Qed.
Lemma lem5206485 (s : real -> Prop) (x : real) (a : real) : (term167 s x a) = (term167 s x a).
Proof. exact (MK_COMB (@lem5206484 x s) (@lem5206474 x a)). Qed.
Lemma lem5206486 (s : real -> Prop) (a : real) : (term168 s a) = (term168 s a).
Proof. exact (fun_ext (fun x : real => @lem5206485 s x a)). Qed.
Lemma lem5206487 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206488 (s : real -> Prop) (a : real) : (term169 s a) = (term169 s a).
Proof. exact (MK_COMB (@lem5206487) (@lem5206486 s a)). Qed.
Lemma lem5206489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5206490 (s : real -> Prop) (a : real) : (term177 s a) = (term177 s a).
Proof. exact (MK_COMB (@lem5206489) (@lem5206488 s a)). Qed.
Lemma lem5206491 (s : real -> Prop) (a : real) : (term182 s a) = (term182 s a).
Proof. exact (MK_COMB (@lem5206490 s a) (@lem5206473 s a)). Qed.
Lemma lem5206492 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5206497 (x : real) (x' : real) (s : real -> Prop) : (term229 x x' s) = (term229 x x' s).
Proof. exact (eq_refl (term229 x x' s)). Qed.
Lemma lem5206498 (x : real) (s : real -> Prop) : (term230 x s) = (term230 x s).
Proof. exact (fun_ext (fun x' : real => @lem5206497 x x' s)). Qed.
Lemma lem5206499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206500 (x : real) (s : real -> Prop) : (term160 x s) = (term160 x s).
Proof. exact (MK_COMB (@lem5206499) (@lem5206498 x s)). Qed.
Lemma lem5206501 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206502 (x : real) (s : real -> Prop) : (term166 x s) = (term166 x s).
Proof. exact (MK_COMB (@lem5206501) (@lem5206500 x s)). Qed.
Lemma lem5206503 (s : real -> Prop) (x : real) (b : real) : (term167 s x b) = (term167 s x b).
Proof. exact (MK_COMB (@lem5206502 x s) (@lem5206492 x b)). Qed.
Lemma lem5206504 (s : real -> Prop) (b : real) : (term168 s b) = (term168 s b).
Proof. exact (fun_ext (fun x : real => @lem5206503 s x b)). Qed.
Lemma lem5206505 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206506 (s : real -> Prop) (b : real) : (term169 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5206505) (@lem5206504 s b)). Qed.
Lemma lem5206507 (s : real -> Prop) : (term171 s) = (term171 s).
Proof. exact (fun_ext (fun b : real => @lem5206506 s b)). Qed.
Lemma lem5206508 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206509 (s : real -> Prop) : (term173 s) = (term173 s).
Proof. exact (MK_COMB (@lem5206508) (@lem5206507 s)). Qed.
Lemma lem5206514 (x : real) (x' : real) (s : real -> Prop) : (term229 x x' s) = (term229 x x' s).
Proof. exact (eq_refl (term229 x x' s)). Qed.
Lemma lem5206515 (x : real) (s : real -> Prop) : (term230 x s) = (term230 x s).
Proof. exact (fun_ext (fun x' : real => @lem5206514 x x' s)). Qed.
Lemma lem5206516 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206517 (x : real) (s : real -> Prop) : (term160 x s) = (term160 x s).
Proof. exact (MK_COMB (@lem5206516) (@lem5206515 x s)). Qed.
Lemma lem5206518 (s : real -> Prop) : (term162 s) = (term162 s).
Proof. exact (fun_ext (fun x : real => @lem5206517 x s)). Qed.
Lemma lem5206519 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206520 (s : real -> Prop) : (term163 s) = (term163 s).
Proof. exact (MK_COMB (@lem5206519) (@lem5206518 s)). Qed.
Lemma lem5206521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5206522 (s : real -> Prop) : (term165 s) = (term165 s).
Proof. exact (MK_COMB (@lem5206521) (@lem5206520 s)). Qed.
Lemma lem5206523 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (MK_COMB (@lem5206522 s) (@lem5206509 s)). Qed.
Lemma lem5206524 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206525 (s : real -> Prop) : (term176 s) = (term176 s).
Proof. exact (MK_COMB (@lem5206524) (@lem5206523 s)). Qed.
Lemma lem5206526 (s : real -> Prop) (a : real) : (term183 s a) = (term183 s a).
Proof. exact (MK_COMB (@lem5206525 s) (@lem5206491 s a)). Qed.
Lemma lem5206527 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206528 (s : real -> Prop) (a : real) : (term184 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5206527) (@lem5206526 s a)). Qed.
Lemma lem5206529 (s : real -> Prop) (a : real) : (term185 s a) = (term185 s a).
Proof. exact (MK_COMB (@lem5206528 s a) (@lem5206451 s a)). Qed.
Lemma lem5206530 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206531 (s : real -> Prop) (a : real) : (term188 s a) = (term188 s a).
Proof. exact (MK_COMB (@lem5206530) (@lem5206529 s a)). Qed.
Lemma lem5206532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206533 (s : real -> Prop) (a : real) : (term203 s a) = (term203 s a).
Proof. exact (MK_COMB (@lem5206532) (@lem5206531 s a)). Qed.
Lemma lem5206534 (s : real -> Prop) (a : real) : (term205 s a) = (term205 s a).
Proof. exact (MK_COMB (@lem5206533 s a) (@lem5206425)). Qed.
Lemma lem5206537 (s : real -> Prop) (a : real) : (term206 s a) = (term206 s a).
Proof. exact (eq_refl (term206 s a)). Qed.
Lemma lem5206538 (s : real -> Prop) (a : real) : (term208 s a) = (term208 s a).
Proof. exact (MK_COMB (@lem5206537 s a) (@lem5206534 s a)). Qed.
Lemma lem5206543 (s : real -> Prop) (b : real) (x : real) : (term75 s b x) = (term75 s b x).
Proof. exact (eq_refl (term75 s b x)). Qed.
Lemma lem5206544 (s : real -> Prop) (b : real) : (term77 s b) = (term77 s b).
Proof. exact (fun_ext (fun x : real => @lem5206543 s b x)). Qed.
Lemma lem5206545 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206546 (s : real -> Prop) (b : real) : (term44 s b) = (term44 s b).
Proof. exact (MK_COMB (@lem5206545) (@lem5206544 s b)). Qed.
Lemma lem5206547 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5206548 (s : real -> Prop) (b : real) : (term60 s b) = (term60 s b).
Proof. exact (MK_COMB (@lem5206547) (@lem5206546 s b)). Qed.
Lemma lem5206549 (b : real) (s : real -> Prop) (a : real) : (term210 b s a) = (term210 b s a).
Proof. exact (MK_COMB (@lem5206548 s b) (@lem5206538 s a)). Qed.
Lemma lem5206554 (s : real -> Prop) : (term211 s) = (term211 s).
Proof. exact (eq_refl (term211 s)). Qed.
Lemma lem5206555 (b : real) (s : real -> Prop) (a : real) : (term212 b s a) = (term212 b s a).
Proof. exact (MK_COMB (@lem5206554 s) (@lem5206549 b s a)). Qed.
Lemma lem5206556 (s : real -> Prop) (a : real) : (term214 s a) = (term214 s a).
Proof. exact (fun_ext (fun b : real => @lem5206555 b s a)). Qed.
Lemma lem5206557 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206558 (s : real -> Prop) (a : real) : (term216 s a) = (term216 s a).
Proof. exact (MK_COMB (@lem5206557) (@lem5206556 s a)). Qed.
Lemma lem5206559 (a : real) : (term218 a) = (term218 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5206558 s a)). Qed.
Lemma lem5206560 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5206561 (a : real) : (term220 a) = (term220 a).
Proof. exact (MK_COMB (@lem5206560) (@lem5206559 a)). Qed.
Lemma lem5206562 : term222 = term222.
Proof. exact (fun_ext (fun a : real => @lem5206561 a)). Qed.
Lemma lem5206563 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206564 : term224 = term224.
Proof. exact (MK_COMB (@lem5206563) (@lem5206562)). Qed.
Lemma lem5206745 : term223 = term224.
Proof. exact (TRANS (@lem5206389) (@lem5206564)). Qed.
Lemma lem5206746 : term224 = term223.
Proof. exact (SYM (@lem5206745)). Qed.
Lemma lem5206748 (s : real -> Prop) (b : real) (h1 : term44 s b) : term44 s b.
Proof. exact (h1). Qed.
Lemma lem5206750 (s : real -> Prop) (a : real) (h1 : term188 s a) : term188 s a.
Proof. exact (h1). Qed.
Lemma lem5206751 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem5206752 (h1 : term189) : term189.
Proof. exact (h1). Qed.
Lemma lem5206753 (h1 : term196) : term196.
Proof. exact (h1). Qed.
Lemma lem5206759 (s : real -> Prop) (h1 : term43 s) : term43 s.
Proof. exact (h1). Qed.
Lemma lem5206766 (s : real -> Prop) (b : real) (x : real) : (term75 s b x) = (term231 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5206767 (s : real -> Prop) (b : real) : (term77 s b) = (term232 s b).
Proof. exact (fun_ext (fun x : real => @lem5206766 s b x)). Qed.
Lemma lem5206768 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206821 (s : real -> Prop) (b : real) : (term44 s b) = (term233 s b).
Proof. exact (MK_COMB (@lem5206768) (@lem5206767 s b)). Qed.
Lemma lem5206822 (s : real -> Prop) (b : real) (h1 : term44 s b) : term233 s b.
Proof. exact (EQ_MP (@lem5206821 s b) (@lem5206748 s b h1)). Qed.
Lemma lem5206828 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5206835 (x : real) (x' : real) (s : real -> Prop) : (term234 x x' s) = (term235 x x' s).
Proof. exact (@lem17045 (x = (real_neg x')) (@IN real x' s)). Qed.
Lemma lem5206836 (P : real -> Prop) : (term236 P) = (term237 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5206837 (x : real) (s : real -> Prop) : (term238 x s) = (term239 x s).
Proof. exact (@lem5206836 (term230 x s)). Qed.
Lemma lem5206838 (x : real) (x' : real) (s : real -> Prop) : (term240 x s x') = (term229 x x' s).
Proof. exact (eq_refl (term240 x s x')). Qed.
Lemma lem5206839 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206840 (x : real) (x' : real) (s : real -> Prop) : (term241 x s x') = (term234 x x' s).
Proof. exact (MK_COMB (@lem5206839) (@lem5206838 x x' s)). Qed.
Lemma lem5206841 (x : real) (x' : real) (s : real -> Prop) : (term241 x s x') = (term235 x x' s).
Proof. exact (TRANS (@lem5206840 x x' s) (@lem5206835 x x' s)). Qed.
Lemma lem5206842 (x : real) (s : real -> Prop) : (term242 x s) = (term243 x s).
Proof. exact (fun_ext (fun x' : real => @lem5206841 x x' s)). Qed.
Lemma lem5206843 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206844 (x : real) (s : real -> Prop) : (term239 x s) = (term244 x s).
Proof. exact (MK_COMB (@lem5206843) (@lem5206842 x s)). Qed.
Lemma lem5206845 (x : real) (s : real -> Prop) : (term238 x s) = (term244 x s).
Proof. exact (TRANS (@lem5206837 x s) (@lem5206844 x s)). Qed.
Lemma lem5206846 (P : real -> Prop) : (term236 P) = (term237 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5206847 (s : real -> Prop) : (term245 s) = (term246 s).
Proof. exact (@lem5206846 (term162 s)). Qed.
Lemma lem5206848 (x : real) (s : real -> Prop) : (term247 s x) = (term160 x s).
Proof. exact (eq_refl (term247 s x)). Qed.
Lemma lem5206849 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206850 (x : real) (s : real -> Prop) : (term248 s x) = (term238 x s).
Proof. exact (MK_COMB (@lem5206849) (@lem5206848 x s)). Qed.
Lemma lem5206851 (x : real) (s : real -> Prop) : (term248 s x) = (term244 x s).
Proof. exact (TRANS (@lem5206850 x s) (@lem5206845 x s)). Qed.
Lemma lem5206852 (s : real -> Prop) : (term249 s) = (term250 s).
Proof. exact (fun_ext (fun x : real => @lem5206851 x s)). Qed.
Lemma lem5206853 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206854 (s : real -> Prop) : (term246 s) = (term251 s).
Proof. exact (MK_COMB (@lem5206853) (@lem5206852 s)). Qed.
Lemma lem5206855 (s : real -> Prop) : (term245 s) = (term251 s).
Proof. exact (TRANS (@lem5206847 s) (@lem5206854 s)). Qed.
Lemma lem5206860 (x : real) (x' : real) (s : real -> Prop) : (term229 x x' s) = (term229 x x' s).
Proof. exact (eq_refl (term229 x x' s)). Qed.
Lemma lem5206861 (x : real) (s : real -> Prop) : (term230 x s) = (term230 x s).
Proof. exact (fun_ext (fun x' : real => @lem5206860 x x' s)). Qed.
Lemma lem5206862 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206863 (x : real) (s : real -> Prop) : (term160 x s) = (term160 x s).
Proof. exact (MK_COMB (@lem5206862) (@lem5206861 x s)). Qed.
Lemma lem5206864 (x : real) (b : real) : (term252 x b) = (term252 x b).
Proof. exact (eq_refl (term252 x b)). Qed.
Lemma lem5206865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5206866 (x : real) (s : real -> Prop) : (term253 x s) = (term253 x s).
Proof. exact (MK_COMB (@lem5206865) (@lem5206863 x s)). Qed.
Lemma lem5206867 (s : real -> Prop) (x : real) (b : real) : (term254 s x b) = (term254 s x b).
Proof. exact (MK_COMB (@lem5206866 x s) (@lem5206864 x b)). Qed.
Lemma lem5206868 (s : real -> Prop) (x : real) (b : real) : (term255 s x b) = (term254 s x b).
Proof. exact (@lem17362 (term160 x s) (real_le x b)). Qed.
Lemma lem5206869 (s : real -> Prop) (x : real) (b : real) : (term255 s x b) = (term254 s x b).
Proof. exact (TRANS (@lem5206868 s x b) (@lem5206867 s x b)). Qed.
Lemma lem5206870 (P : real -> Prop) : (term256 P) = (term257 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5206871 (s : real -> Prop) (b : real) : (term258 s b) = (term259 s b).
Proof. exact (@lem5206870 (term168 s b)). Qed.
Lemma lem5206872 (s : real -> Prop) (x : real) (b : real) : (term260 s b x) = (term167 s x b).
Proof. exact (eq_refl (term260 s b x)). Qed.
Lemma lem5206873 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206874 (s : real -> Prop) (x : real) (b : real) : (term261 s b x) = (term255 s x b).
Proof. exact (MK_COMB (@lem5206873) (@lem5206872 s x b)). Qed.
Lemma lem5206875 (s : real -> Prop) (x : real) (b : real) : (term261 s b x) = (term254 s x b).
Proof. exact (TRANS (@lem5206874 s x b) (@lem5206869 s x b)). Qed.
Lemma lem5206876 (s : real -> Prop) (b : real) : (term262 s b) = (term263 s b).
Proof. exact (fun_ext (fun x : real => @lem5206875 s x b)). Qed.
Lemma lem5206877 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206878 (s : real -> Prop) (b : real) : (term259 s b) = (term264 s b).
Proof. exact (MK_COMB (@lem5206877) (@lem5206876 s b)). Qed.
Lemma lem5206879 (s : real -> Prop) (b : real) : (term258 s b) = (term264 s b).
Proof. exact (TRANS (@lem5206871 s b) (@lem5206878 s b)). Qed.
Lemma lem5206880 (P : real -> Prop) : (term236 P) = (term237 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5206881 (s : real -> Prop) : (term265 s) = (term266 s).
Proof. exact (@lem5206880 (term171 s)). Qed.
Lemma lem5206882 (s : real -> Prop) (b : real) : (term267 s b) = (term169 s b).
Proof. exact (eq_refl (term267 s b)). Qed.
Lemma lem5206883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206884 (s : real -> Prop) (b : real) : (term268 s b) = (term258 s b).
Proof. exact (MK_COMB (@lem5206883) (@lem5206882 s b)). Qed.
Lemma lem5206885 (s : real -> Prop) (b : real) : (term268 s b) = (term264 s b).
Proof. exact (TRANS (@lem5206884 s b) (@lem5206879 s b)). Qed.
Lemma lem5206886 (s : real -> Prop) : (term269 s) = (term270 s).
Proof. exact (fun_ext (fun b : real => @lem5206885 s b)). Qed.
Lemma lem5206887 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206888 (s : real -> Prop) : (term266 s) = (term271 s).
Proof. exact (MK_COMB (@lem5206887) (@lem5206886 s)). Qed.
Lemma lem5206889 (s : real -> Prop) : (term265 s) = (term271 s).
Proof. exact (TRANS (@lem5206881 s) (@lem5206888 s)). Qed.
Lemma lem5206890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5206891 (s : real -> Prop) : (term272 s) = (term273 s).
Proof. exact (MK_COMB (@lem5206890) (@lem5206855 s)). Qed.
Lemma lem5206892 (s : real -> Prop) : (term274 s) = (term275 s).
Proof. exact (MK_COMB (@lem5206891 s) (@lem5206889 s)). Qed.
Lemma lem5206893 (s : real -> Prop) : (term276 s) = (term274 s).
Proof. exact (@lem17045 (term163 s) (term173 s)). Qed.
Lemma lem5206894 (s : real -> Prop) : (term276 s) = (term275 s).
Proof. exact (TRANS (@lem5206893 s) (@lem5206892 s)). Qed.
Lemma lem5206901 (x : real) (x' : real) (s : real -> Prop) : (term234 x x' s) = (term235 x x' s).
Proof. exact (@lem17045 (x = (real_neg x')) (@IN real x' s)). Qed.
Lemma lem5206902 (P : real -> Prop) : (term236 P) = (term237 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5206903 (x : real) (s : real -> Prop) : (term238 x s) = (term239 x s).
Proof. exact (@lem5206902 (term230 x s)). Qed.
Lemma lem5206904 (x : real) (x' : real) (s : real -> Prop) : (term240 x s x') = (term229 x x' s).
Proof. exact (eq_refl (term240 x s x')). Qed.
Lemma lem5206905 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206906 (x : real) (x' : real) (s : real -> Prop) : (term241 x s x') = (term234 x x' s).
Proof. exact (MK_COMB (@lem5206905) (@lem5206904 x x' s)). Qed.
Lemma lem5206907 (x : real) (x' : real) (s : real -> Prop) : (term241 x s x') = (term235 x x' s).
Proof. exact (TRANS (@lem5206906 x x' s) (@lem5206901 x x' s)). Qed.
Lemma lem5206908 (x : real) (s : real -> Prop) : (term242 x s) = (term243 x s).
Proof. exact (fun_ext (fun x' : real => @lem5206907 x x' s)). Qed.
Lemma lem5206909 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206910 (x : real) (s : real -> Prop) : (term239 x s) = (term244 x s).
Proof. exact (MK_COMB (@lem5206909) (@lem5206908 x s)). Qed.
Lemma lem5206911 (x : real) (s : real -> Prop) : (term238 x s) = (term244 x s).
Proof. exact (TRANS (@lem5206903 x s) (@lem5206910 x s)). Qed.
Lemma lem5206912 (x : real) (a : real) : (real_le x a) = (real_le x a).
Proof. exact (eq_refl (real_le x a)). Qed.
Lemma lem5206913 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5206914 (x : real) (s : real -> Prop) : (term277 x s) = (term278 x s).
Proof. exact (MK_COMB (@lem5206913) (@lem5206911 x s)). Qed.
Lemma lem5206915 (s : real -> Prop) (x : real) (a : real) : (term279 s x a) = (term280 s x a).
Proof. exact (MK_COMB (@lem5206914 x s) (@lem5206912 x a)). Qed.
Lemma lem5206916 (s : real -> Prop) (x : real) (a : real) : (term167 s x a) = (term279 s x a).
Proof. exact (@lem17265 (term160 x s) (real_le x a)). Qed.
Lemma lem5206917 (s : real -> Prop) (x : real) (a : real) : (term167 s x a) = (term280 s x a).
Proof. exact (TRANS (@lem5206916 s x a) (@lem5206915 s x a)). Qed.
Lemma lem5206918 (s : real -> Prop) (a : real) : (term168 s a) = (term281 s a).
Proof. exact (fun_ext (fun x : real => @lem5206917 s x a)). Qed.
Lemma lem5206919 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206920 (s : real -> Prop) (a : real) : (term169 s a) = (term282 s a).
Proof. exact (MK_COMB (@lem5206919) (@lem5206918 s a)). Qed.
Lemma lem5206925 (x : real) (x' : real) (s : real -> Prop) : (term229 x x' s) = (term229 x x' s).
Proof. exact (eq_refl (term229 x x' s)). Qed.
Lemma lem5206926 (x : real) (s : real -> Prop) : (term230 x s) = (term230 x s).
Proof. exact (fun_ext (fun x' : real => @lem5206925 x x' s)). Qed.
Lemma lem5206927 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206928 (x : real) (s : real -> Prop) : (term160 x s) = (term160 x s).
Proof. exact (MK_COMB (@lem5206927) (@lem5206926 x s)). Qed.
Lemma lem5206929 (x : real) (b : real) : (term252 x b) = (term252 x b).
Proof. exact (eq_refl (term252 x b)). Qed.
Lemma lem5206930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5206931 (x : real) (s : real -> Prop) : (term253 x s) = (term253 x s).
Proof. exact (MK_COMB (@lem5206930) (@lem5206928 x s)). Qed.
Lemma lem5206932 (s : real -> Prop) (x : real) (b : real) : (term254 s x b) = (term254 s x b).
Proof. exact (MK_COMB (@lem5206931 x s) (@lem5206929 x b)). Qed.
Lemma lem5206933 (s : real -> Prop) (x : real) (b : real) : (term255 s x b) = (term254 s x b).
Proof. exact (@lem17362 (term160 x s) (real_le x b)). Qed.
Lemma lem5206934 (s : real -> Prop) (x : real) (b : real) : (term255 s x b) = (term254 s x b).
Proof. exact (TRANS (@lem5206933 s x b) (@lem5206932 s x b)). Qed.
Lemma lem5206935 (P : real -> Prop) : (term256 P) = (term257 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5206936 (s : real -> Prop) (b : real) : (term258 s b) = (term259 s b).
Proof. exact (@lem5206935 (term168 s b)). Qed.
Lemma lem5206937 (s : real -> Prop) (x : real) (b : real) : (term260 s b x) = (term167 s x b).
Proof. exact (eq_refl (term260 s b x)). Qed.
Lemma lem5206938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206939 (s : real -> Prop) (x : real) (b : real) : (term261 s b x) = (term255 s x b).
Proof. exact (MK_COMB (@lem5206938) (@lem5206937 s x b)). Qed.
Lemma lem5206940 (s : real -> Prop) (x : real) (b : real) : (term261 s b x) = (term254 s x b).
Proof. exact (TRANS (@lem5206939 s x b) (@lem5206934 s x b)). Qed.
Lemma lem5206941 (s : real -> Prop) (b : real) : (term262 s b) = (term263 s b).
Proof. exact (fun_ext (fun x : real => @lem5206940 s x b)). Qed.
Lemma lem5206942 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206943 (s : real -> Prop) (b : real) : (term259 s b) = (term264 s b).
Proof. exact (MK_COMB (@lem5206942) (@lem5206941 s b)). Qed.
Lemma lem5206944 (s : real -> Prop) (b : real) : (term258 s b) = (term264 s b).
Proof. exact (TRANS (@lem5206936 s b) (@lem5206943 s b)). Qed.
Lemma lem5206945 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5206946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5206947 (s : real -> Prop) (b : real) : (term283 s b) = (term284 s b).
Proof. exact (MK_COMB (@lem5206946) (@lem5206944 s b)). Qed.
Lemma lem5206948 (s : real -> Prop) (a : real) (b : real) : (term285 s a b) = (term286 s a b).
Proof. exact (MK_COMB (@lem5206947 s b) (@lem5206945 a b)). Qed.
Lemma lem5206949 (s : real -> Prop) (a : real) (b : real) : (term179 s a b) = (term285 s a b).
Proof. exact (@lem17265 (term169 s b) (real_le a b)). Qed.
Lemma lem5206950 (s : real -> Prop) (a : real) (b : real) : (term179 s a b) = (term286 s a b).
Proof. exact (TRANS (@lem5206949 s a b) (@lem5206948 s a b)). Qed.
Lemma lem5206951 (s : real -> Prop) (a : real) : (term180 s a) = (term287 s a).
Proof. exact (fun_ext (fun b : real => @lem5206950 s a b)). Qed.
Lemma lem5206952 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206953 (s : real -> Prop) (a : real) : (term181 s a) = (term288 s a).
Proof. exact (MK_COMB (@lem5206952) (@lem5206951 s a)). Qed.
Lemma lem5206954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5206955 (s : real -> Prop) (a : real) : (term177 s a) = (term289 s a).
Proof. exact (MK_COMB (@lem5206954) (@lem5206920 s a)). Qed.
Lemma lem5206956 (s : real -> Prop) (a : real) : (term182 s a) = (term290 s a).
Proof. exact (MK_COMB (@lem5206955 s a) (@lem5206953 s a)). Qed.
Lemma lem5206957 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5206958 (s : real -> Prop) : (term291 s) = (term292 s).
Proof. exact (MK_COMB (@lem5206957) (@lem5206894 s)). Qed.
Lemma lem5206959 (s : real -> Prop) (a : real) : (term293 s a) = (term294 s a).
Proof. exact (MK_COMB (@lem5206958 s) (@lem5206956 s a)). Qed.
Lemma lem5206960 (s : real -> Prop) (a : real) : (term183 s a) = (term293 s a).
Proof. exact (@lem17265 (term175 s) (term182 s a)). Qed.
Lemma lem5206961 (s : real -> Prop) (a : real) : (term183 s a) = (term294 s a).
Proof. exact (TRANS (@lem5206960 s a) (@lem5206959 s a)). Qed.
Lemma lem5206968 (s : real -> Prop) (x : real) (a : real) : (term295 s x a) = (term296 s x a).
Proof. exact (@lem17362 (@IN real x s) (term143 x a)). Qed.
Lemma lem5206969 (P : real -> Prop) : (term256 P) = (term257 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5206970 (s : real -> Prop) (a : real) : (term297 s a) = (term298 s a).
Proof. exact (@lem5206969 (term145 s a)). Qed.
Lemma lem5206971 (s : real -> Prop) (x : real) (a : real) : (term299 s a x) = (term144 s x a).
Proof. exact (eq_refl (term299 s a x)). Qed.
Lemma lem5206972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206973 (s : real -> Prop) (x : real) (a : real) : (term300 s a x) = (term295 s x a).
Proof. exact (MK_COMB (@lem5206972) (@lem5206971 s x a)). Qed.
Lemma lem5206974 (s : real -> Prop) (x : real) (a : real) : (term300 s a x) = (term296 s x a).
Proof. exact (TRANS (@lem5206973 s x a) (@lem5206968 s x a)). Qed.
Lemma lem5206975 (s : real -> Prop) (a : real) : (term301 s a) = (term302 s a).
Proof. exact (fun_ext (fun x : real => @lem5206974 s x a)). Qed.
Lemma lem5206976 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5206977 (s : real -> Prop) (a : real) : (term298 s a) = (term303 s a).
Proof. exact (MK_COMB (@lem5206976) (@lem5206975 s a)). Qed.
Lemma lem5206978 (s : real -> Prop) (a : real) : (term297 s a) = (term303 s a).
Proof. exact (TRANS (@lem5206970 s a) (@lem5206977 s a)). Qed.
Lemma lem5206985 (s : real -> Prop) (x : real) (b : real) : (term76 s x b) = (term304 s x b).
Proof. exact (@lem17265 (@IN real x s) (term28 x b)). Qed.
Lemma lem5206986 (s : real -> Prop) (b : real) : (term78 s b) = (term305 s b).
Proof. exact (fun_ext (fun x : real => @lem5206985 s x b)). Qed.
Lemma lem5206987 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5206988 (s : real -> Prop) (b : real) : (term79 s b) = (term306 s b).
Proof. exact (MK_COMB (@lem5206987) (@lem5206986 s b)). Qed.
Lemma lem5206989 (a : real) (b : real) : (term307 a b) = (term307 a b).
Proof. exact (eq_refl (term307 a b)). Qed.
Lemma lem5206990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5206991 (s : real -> Prop) (b : real) : (term81 s b) = (term308 s b).
Proof. exact (MK_COMB (@lem5206990) (@lem5206988 s b)). Qed.
Lemma lem5206992 (s : real -> Prop) (a : real) (b : real) : (term309 s a b) = (term310 s a b).
Proof. exact (MK_COMB (@lem5206991 s b) (@lem5206989 a b)). Qed.
Lemma lem5206993 (s : real -> Prop) (a : real) (b : real) : (term311 s a b) = (term309 s a b).
Proof. exact (@lem17362 (term79 s b) (term148 a b)). Qed.
Lemma lem5206994 (s : real -> Prop) (a : real) (b : real) : (term311 s a b) = (term310 s a b).
Proof. exact (TRANS (@lem5206993 s a b) (@lem5206992 s a b)). Qed.
Lemma lem5206995 (P : real -> Prop) : (term256 P) = (term257 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5206996 (s : real -> Prop) (a : real) : (term312 s a) = (term313 s a).
Proof. exact (@lem5206995 (term150 s a)). Qed.
Lemma lem5206997 (s : real -> Prop) (a : real) (b : real) : (term314 s a b) = (term149 s a b).
Proof. exact (eq_refl (term314 s a b)). Qed.
Lemma lem5206998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5206999 (s : real -> Prop) (a : real) (b : real) : (term315 s a b) = (term311 s a b).
Proof. exact (MK_COMB (@lem5206998) (@lem5206997 s a b)). Qed.
Lemma lem5207000 (s : real -> Prop) (a : real) (b : real) : (term315 s a b) = (term310 s a b).
Proof. exact (TRANS (@lem5206999 s a b) (@lem5206994 s a b)). Qed.
Lemma lem5207001 (s : real -> Prop) (a : real) : (term316 s a) = (term317 s a).
Proof. exact (fun_ext (fun b : real => @lem5207000 s a b)). Qed.
Lemma lem5207002 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207003 (s : real -> Prop) (a : real) : (term313 s a) = (term318 s a).
Proof. exact (MK_COMB (@lem5207002) (@lem5207001 s a)). Qed.
Lemma lem5207004 (s : real -> Prop) (a : real) : (term312 s a) = (term318 s a).
Proof. exact (TRANS (@lem5206996 s a) (@lem5207003 s a)). Qed.
Lemma lem5207005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207006 (s : real -> Prop) (a : real) : (term319 s a) = (term320 s a).
Proof. exact (MK_COMB (@lem5207005) (@lem5206978 s a)). Qed.
Lemma lem5207007 (s : real -> Prop) (a : real) : (term321 s a) = (term322 s a).
Proof. exact (MK_COMB (@lem5207006 s a) (@lem5207004 s a)). Qed.
Lemma lem5207008 (s : real -> Prop) (a : real) : (term323 s a) = (term321 s a).
Proof. exact (@lem17045 (term146 s a) (term151 s a)). Qed.
Lemma lem5207009 (s : real -> Prop) (a : real) : (term323 s a) = (term322 s a).
Proof. exact (TRANS (@lem5207008 s a) (@lem5207007 s a)). Qed.
Lemma lem5207010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5207011 (s : real -> Prop) (a : real) : (term324 s a) = (term325 s a).
Proof. exact (MK_COMB (@lem5207010) (@lem5206961 s a)). Qed.
Lemma lem5207012 (s : real -> Prop) (a : real) : (term326 s a) = (term327 s a).
Proof. exact (MK_COMB (@lem5207011 s a) (@lem5207009 s a)). Qed.
Lemma lem5207013 (s : real -> Prop) (a : real) : (term188 s a) = (term326 s a).
Proof. exact (@lem17362 (term183 s a) (term152 s a)). Qed.
Lemma lem5207014 (s : real -> Prop) (a : real) : (term188 s a) = (term327 s a).
Proof. exact (TRANS (@lem5207013 s a) (@lem5207012 s a)). Qed.
Lemma lem5207553 {A : Type'} (P : A -> Prop) (Q : Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5207554 (P : real -> Prop) (Q : Prop) : (term330 P Q) = (term331 P Q).
Proof. exact (@lem5207553 real P Q). Qed.
Lemma lem5207555 (s : real -> Prop) (x : real) (b : real) : (term332 s x b) = (term333 s x b).
Proof. exact (@lem5207554 (term230 x s) (term252 x b)). Qed.
Lemma lem5207556 (x : real) (x' : real) (s : real -> Prop) : (term240 x s x') = (term229 x x' s).
Proof. exact (eq_refl (term240 x s x')). Qed.
Lemma lem5207557 (x : real) (s : real -> Prop) : (term334 x s) = (term230 x s).
Proof. exact (fun_ext (fun x' : real => @lem5207556 x x' s)). Qed.
Lemma lem5207558 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207559 (x : real) (s : real -> Prop) : (term335 x s) = (term160 x s).
Proof. exact (MK_COMB (@lem5207558) (@lem5207557 x s)). Qed.
Lemma lem5207560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5207561 (x : real) (s : real -> Prop) : (term336 x s) = (term253 x s).
Proof. exact (MK_COMB (@lem5207560) (@lem5207559 x s)). Qed.
Lemma lem5207562 (x : real) (b : real) : (term252 x b) = (term252 x b).
Proof. exact (eq_refl (term252 x b)). Qed.
Lemma lem5207563 (s : real -> Prop) (x : real) (b : real) : (term332 s x b) = (term254 s x b).
Proof. exact (MK_COMB (@lem5207561 x s) (@lem5207562 x b)). Qed.
Lemma lem5207564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207565 (s : real -> Prop) (x : real) (b : real) : (term337 s x b) = (term338 s x b).
Proof. exact (MK_COMB (@lem5207564) (@lem5207563 s x b)). Qed.
Lemma lem5207566 (x : real) (x' : real) (s : real -> Prop) : (term240 x s x') = (term229 x x' s).
Proof. exact (eq_refl (term240 x s x')). Qed.
Lemma lem5207567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5207568 (x : real) (x' : real) (s : real -> Prop) : (term339 x s x') = (term340 x x' s).
Proof. exact (MK_COMB (@lem5207567) (@lem5207566 x x' s)). Qed.
Lemma lem5207569 (x : real) (b : real) : (term252 x b) = (term252 x b).
Proof. exact (eq_refl (term252 x b)). Qed.
Lemma lem5207570 (x' : real) (s : real -> Prop) (x : real) (b : real) : (term341 s x' x b) = (term342 x' s x b).
Proof. exact (MK_COMB (@lem5207568 x x' s) (@lem5207569 x b)). Qed.
Lemma lem5207571 (s : real -> Prop) (x : real) (b : real) : (term343 s x b) = (term344 s x b).
Proof. exact (fun_ext (fun x' : real => @lem5207570 x' s x b)). Qed.
Lemma lem5207572 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207573 (s : real -> Prop) (x : real) (b : real) : (term333 s x b) = (term345 s x b).
Proof. exact (MK_COMB (@lem5207572) (@lem5207571 s x b)). Qed.
Lemma lem5207574 (s : real -> Prop) (x : real) (b : real) : ((term332 s x b) = (term333 s x b)) = ((term254 s x b) = (term345 s x b)).
Proof. exact (MK_COMB (@lem5207565 s x b) (@lem5207573 s x b)). Qed.
Lemma lem5207575 (s : real -> Prop) (x : real) (b : real) : (term254 s x b) = (term345 s x b).
Proof. exact (EQ_MP (@lem5207574 s x b) (@lem5207555 s x b)). Qed.
Lemma lem5207576 (s : real -> Prop) (b : real) : (term263 s b) = (term346 s b).
Proof. exact (fun_ext (fun x : real => @lem5207575 s x b)). Qed.
Lemma lem5207577 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207578 (s : real -> Prop) (b : real) : (term264 s b) = (term347 s b).
Proof. exact (MK_COMB (@lem5207577) (@lem5207576 s b)). Qed.
Lemma lem5207579 (s : real -> Prop) : (term270 s) = (term348 s).
Proof. exact (fun_ext (fun b : real => @lem5207578 s b)). Qed.
Lemma lem5207580 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207581 (s : real -> Prop) : (term271 s) = (term349 s).
Proof. exact (MK_COMB (@lem5207580) (@lem5207579 s)). Qed.
Lemma lem5207583 {A B : Type'} (P : type1413 A B) : (term350 A B P) = (term351 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5207584 (P : type1626) : (term352 P) = (term353 P).
Proof. exact (@lem5207583 real real P). Qed.
Lemma lem5207585 (s : real -> Prop) : (term354 s) = (term355 s).
Proof. exact (@lem5207584 (term356 s)). Qed.
Lemma lem5207586 (s : real -> Prop) (b : real) : (term357 s b) = (term346 s b).
Proof. exact (eq_refl (term357 s b)). Qed.
Lemma lem5207587 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5207588 (s : real -> Prop) (b : real) (x : real) : (term358 s b x) = (term359 s b x).
Proof. exact (MK_COMB (@lem5207586 s b) (@lem5207587 x)). Qed.
Lemma lem5207589 (s : real -> Prop) (x : real) (b : real) : (term359 s b x) = (term345 s x b).
Proof. exact (eq_refl (term359 s b x)). Qed.
Lemma lem5207590 (s : real -> Prop) (x : real) (b : real) : (term358 s b x) = (term345 s x b).
Proof. exact (TRANS (@lem5207588 s b x) (@lem5207589 s x b)). Qed.
Lemma lem5207591 (s : real -> Prop) (b : real) : (term360 s b) = (term346 s b).
Proof. exact (fun_ext (fun x : real => @lem5207590 s x b)). Qed.
Lemma lem5207592 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207593 (s : real -> Prop) (b : real) : (term361 s b) = (term347 s b).
Proof. exact (MK_COMB (@lem5207592) (@lem5207591 s b)). Qed.
Lemma lem5207594 (s : real -> Prop) : (term362 s) = (term348 s).
Proof. exact (fun_ext (fun b : real => @lem5207593 s b)). Qed.
Lemma lem5207595 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207596 (s : real -> Prop) : (term354 s) = (term349 s).
Proof. exact (MK_COMB (@lem5207595) (@lem5207594 s)). Qed.
Lemma lem5207597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207598 (s : real -> Prop) : (term363 s) = (term364 s).
Proof. exact (MK_COMB (@lem5207597) (@lem5207596 s)). Qed.
Lemma lem5207599 (s : real -> Prop) (b : real) : (term357 s b) = (term346 s b).
Proof. exact (eq_refl (term357 s b)). Qed.
Lemma lem5207600 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5207601 (s : real -> Prop) (x : real -> real) (b : real) : (term365 s x b) = (term366 s x b).
Proof. exact (MK_COMB (@lem5207599 s b) (@lem5207600 x b)). Qed.
Lemma lem5207602 (s : real -> Prop) (x : real -> real) (b : real) : (term366 s x b) = (term367 s x b).
Proof. exact (eq_refl (term366 s x b)). Qed.
Lemma lem5207603 (s : real -> Prop) (x : real -> real) (b : real) : (term365 s x b) = (term367 s x b).
Proof. exact (TRANS (@lem5207601 s x b) (@lem5207602 s x b)). Qed.
Lemma lem5207604 (s : real -> Prop) (x : real -> real) : (term368 s x) = (term369 s x).
Proof. exact (fun_ext (fun b : real => @lem5207603 s x b)). Qed.
Lemma lem5207605 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207606 (s : real -> Prop) (x : real -> real) : (term370 s x) = (term371 s x).
Proof. exact (MK_COMB (@lem5207605) (@lem5207604 s x)). Qed.
Lemma lem5207607 (s : real -> Prop) : (term372 s) = (term373 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5207606 s x)). Qed.
Lemma lem5207608 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207609 (s : real -> Prop) : (term355 s) = (term374 s).
Proof. exact (MK_COMB (@lem5207608) (@lem5207607 s)). Qed.
Lemma lem5207610 (s : real -> Prop) : ((term354 s) = (term355 s)) = ((term349 s) = (term374 s)).
Proof. exact (MK_COMB (@lem5207598 s) (@lem5207609 s)). Qed.
Lemma lem5207611 (s : real -> Prop) : (term349 s) = (term374 s).
Proof. exact (EQ_MP (@lem5207610 s) (@lem5207585 s)). Qed.
Lemma lem5207613 {A B : Type'} (P : type1413 A B) : (term350 A B P) = (term351 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5207614 (P : type1626) : (term352 P) = (term353 P).
Proof. exact (@lem5207613 real real P). Qed.
Lemma lem5207615 (s : real -> Prop) (x : real -> real) : (term375 s x) = (term376 s x).
Proof. exact (@lem5207614 (term377 s x)). Qed.
Lemma lem5207616 (s : real -> Prop) (x : real -> real) (b : real) : (term378 s x b) = (term379 s x b).
Proof. exact (eq_refl (term378 s x b)). Qed.
Lemma lem5207617 (x' : real) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5207618 (s : real -> Prop) (x : real -> real) (b : real) (x' : real) : (term380 s x b x') = (term381 s x b x').
Proof. exact (MK_COMB (@lem5207616 s x b) (@lem5207617 x')). Qed.
Lemma lem5207619 (x' : real) (s : real -> Prop) (x : real -> real) (b : real) : (term381 s x b x') = (term382 x' s x b).
Proof. exact (eq_refl (term381 s x b x')). Qed.
Lemma lem5207620 (x' : real) (s : real -> Prop) (x : real -> real) (b : real) : (term380 s x b x') = (term382 x' s x b).
Proof. exact (TRANS (@lem5207618 s x b x') (@lem5207619 x' s x b)). Qed.
Lemma lem5207621 (s : real -> Prop) (x : real -> real) (b : real) : (term383 s x b) = (term379 s x b).
Proof. exact (fun_ext (fun x' : real => @lem5207620 x' s x b)). Qed.
Lemma lem5207622 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207623 (s : real -> Prop) (x : real -> real) (b : real) : (term384 s x b) = (term367 s x b).
Proof. exact (MK_COMB (@lem5207622) (@lem5207621 s x b)). Qed.
Lemma lem5207624 (s : real -> Prop) (x : real -> real) : (term385 s x) = (term369 s x).
Proof. exact (fun_ext (fun b : real => @lem5207623 s x b)). Qed.
Lemma lem5207625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207626 (s : real -> Prop) (x : real -> real) : (term375 s x) = (term371 s x).
Proof. exact (MK_COMB (@lem5207625) (@lem5207624 s x)). Qed.
Lemma lem5207627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207628 (s : real -> Prop) (x : real -> real) : (term386 s x) = (term387 s x).
Proof. exact (MK_COMB (@lem5207627) (@lem5207626 s x)). Qed.
Lemma lem5207629 (s : real -> Prop) (x : real -> real) (b : real) : (term378 s x b) = (term379 s x b).
Proof. exact (eq_refl (term378 s x b)). Qed.
Lemma lem5207630 (x' : real -> real) (b : real) : (x' b) = (x' b).
Proof. exact (eq_refl (x' b)). Qed.
Lemma lem5207631 (s : real -> Prop) (x : real -> real) (x' : real -> real) (b : real) : (term388 s x x' b) = (term389 s x x' b).
Proof. exact (MK_COMB (@lem5207629 s x b) (@lem5207630 x' b)). Qed.
Lemma lem5207632 (x' : real -> real) (s : real -> Prop) (x : real -> real) (b : real) : (term389 s x x' b) = (term390 x' s x b).
Proof. exact (eq_refl (term389 s x x' b)). Qed.
Lemma lem5207633 (x' : real -> real) (s : real -> Prop) (x : real -> real) (b : real) : (term388 s x x' b) = (term390 x' s x b).
Proof. exact (TRANS (@lem5207631 s x x' b) (@lem5207632 x' s x b)). Qed.
Lemma lem5207634 (x' : real -> real) (s : real -> Prop) (x : real -> real) : (term391 s x x') = (term392 x' s x).
Proof. exact (fun_ext (fun b : real => @lem5207633 x' s x b)). Qed.
Lemma lem5207635 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207636 (x' : real -> real) (s : real -> Prop) (x : real -> real) : (term393 s x x') = (term394 x' s x).
Proof. exact (MK_COMB (@lem5207635) (@lem5207634 x' s x)). Qed.
Lemma lem5207637 (s : real -> Prop) (x : real -> real) : (term395 s x) = (term396 s x).
Proof. exact (fun_ext (fun x' : real -> real => @lem5207636 x' s x)). Qed.
Lemma lem5207638 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207639 (s : real -> Prop) (x : real -> real) : (term376 s x) = (term397 s x).
Proof. exact (MK_COMB (@lem5207638) (@lem5207637 s x)). Qed.
Lemma lem5207640 (s : real -> Prop) (x : real -> real) : ((term375 s x) = (term376 s x)) = ((term371 s x) = (term397 s x)).
Proof. exact (MK_COMB (@lem5207628 s x) (@lem5207639 s x)). Qed.
Lemma lem5207641 (s : real -> Prop) (x : real -> real) : (term371 s x) = (term397 s x).
Proof. exact (EQ_MP (@lem5207640 s x) (@lem5207615 s x)). Qed.
Lemma lem5207642 (s : real -> Prop) : (term373 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5207641 s x)). Qed.
Lemma lem5207643 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207644 (s : real -> Prop) : (term374 s) = (term399 s).
Proof. exact (MK_COMB (@lem5207643) (@lem5207642 s)). Qed.
Lemma lem5207645 (s : real -> Prop) : (term349 s) = (term399 s).
Proof. exact (TRANS (@lem5207611 s) (@lem5207644 s)). Qed.
Lemma lem5207646 (s : real -> Prop) : (term271 s) = (term399 s).
Proof. exact (TRANS (@lem5207581 s) (@lem5207645 s)). Qed.
Lemma lem5207647 (s : real -> Prop) : (term273 s) = (term273 s).
Proof. exact (eq_refl (term273 s)). Qed.
Lemma lem5207648 (s : real -> Prop) : (term275 s) = (term400 s).
Proof. exact (MK_COMB (@lem5207647 s) (@lem5207646 s)). Qed.
Lemma lem5207650 {A : Type'} (P : Prop) (Q : A -> Prop) : (term401 A P Q) = (term402 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5207651 (P : Prop) (Q : type1028) : (term403 P Q) = (term404 P Q).
Proof. exact (@lem5207650 (real -> real) P Q). Qed.
Lemma lem5207652 (s : real -> Prop) : (term405 s) = (term406 s).
Proof. exact (@lem5207651 (term251 s) (term398 s)). Qed.
Lemma lem5207653 (s : real -> Prop) (x : real -> real) : (term407 s x) = (term397 s x).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5207654 (s : real -> Prop) : (term408 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5207653 s x)). Qed.
Lemma lem5207655 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207656 (s : real -> Prop) : (term409 s) = (term399 s).
Proof. exact (MK_COMB (@lem5207655) (@lem5207654 s)). Qed.
Lemma lem5207657 (s : real -> Prop) : (term273 s) = (term273 s).
Proof. exact (eq_refl (term273 s)). Qed.
Lemma lem5207658 (s : real -> Prop) : (term405 s) = (term400 s).
Proof. exact (MK_COMB (@lem5207657 s) (@lem5207656 s)). Qed.
Lemma lem5207659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207660 (s : real -> Prop) : (term410 s) = (term411 s).
Proof. exact (MK_COMB (@lem5207659) (@lem5207658 s)). Qed.
Lemma lem5207661 (s : real -> Prop) (x : real -> real) : (term407 s x) = (term397 s x).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5207662 (s : real -> Prop) : (term273 s) = (term273 s).
Proof. exact (eq_refl (term273 s)). Qed.
Lemma lem5207663 (s : real -> Prop) (x : real -> real) : (term412 s x) = (term413 s x).
Proof. exact (MK_COMB (@lem5207662 s) (@lem5207661 s x)). Qed.
Lemma lem5207664 (s : real -> Prop) : (term414 s) = (term415 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5207663 s x)). Qed.
Lemma lem5207665 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207666 (s : real -> Prop) : (term406 s) = (term416 s).
Proof. exact (MK_COMB (@lem5207665) (@lem5207664 s)). Qed.
Lemma lem5207667 (s : real -> Prop) : ((term405 s) = (term406 s)) = ((term400 s) = (term416 s)).
Proof. exact (MK_COMB (@lem5207660 s) (@lem5207666 s)). Qed.
Lemma lem5207668 (s : real -> Prop) : (term400 s) = (term416 s).
Proof. exact (EQ_MP (@lem5207667 s) (@lem5207652 s)). Qed.
Lemma lem5207670 {A : Type'} (P : Prop) (Q : A -> Prop) : (term401 A P Q) = (term402 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5207671 (P : Prop) (Q : type1028) : (term403 P Q) = (term404 P Q).
Proof. exact (@lem5207670 (real -> real) P Q). Qed.
Lemma lem5207672 (s : real -> Prop) (x : real -> real) : (term417 s x) = (term418 s x).
Proof. exact (@lem5207671 (term251 s) (term396 s x)). Qed.
Lemma lem5207673 (x' : real -> real) (s : real -> Prop) (x : real -> real) : (term419 s x x') = (term394 x' s x).
Proof. exact (eq_refl (term419 s x x')). Qed.
Lemma lem5207674 (s : real -> Prop) (x : real -> real) : (term420 s x) = (term396 s x).
Proof. exact (fun_ext (fun x' : real -> real => @lem5207673 x' s x)). Qed.
Lemma lem5207675 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207676 (s : real -> Prop) (x : real -> real) : (term421 s x) = (term397 s x).
Proof. exact (MK_COMB (@lem5207675) (@lem5207674 s x)). Qed.
Lemma lem5207677 (s : real -> Prop) : (term273 s) = (term273 s).
Proof. exact (eq_refl (term273 s)). Qed.
Lemma lem5207678 (s : real -> Prop) (x : real -> real) : (term417 s x) = (term413 s x).
Proof. exact (MK_COMB (@lem5207677 s) (@lem5207676 s x)). Qed.
Lemma lem5207679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207680 (s : real -> Prop) (x : real -> real) : (term422 s x) = (term423 s x).
Proof. exact (MK_COMB (@lem5207679) (@lem5207678 s x)). Qed.
Lemma lem5207681 (x' : real -> real) (s : real -> Prop) (x : real -> real) : (term419 s x x') = (term394 x' s x).
Proof. exact (eq_refl (term419 s x x')). Qed.
Lemma lem5207682 (s : real -> Prop) : (term273 s) = (term273 s).
Proof. exact (eq_refl (term273 s)). Qed.
Lemma lem5207683 (x' : real -> real) (s : real -> Prop) (x : real -> real) : (term424 s x x') = (term425 x' s x).
Proof. exact (MK_COMB (@lem5207682 s) (@lem5207681 x' s x)). Qed.
Lemma lem5207684 (s : real -> Prop) (x : real -> real) : (term426 s x) = (term427 s x).
Proof. exact (fun_ext (fun x' : real -> real => @lem5207683 x' s x)). Qed.
Lemma lem5207685 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207686 (s : real -> Prop) (x : real -> real) : (term418 s x) = (term428 s x).
Proof. exact (MK_COMB (@lem5207685) (@lem5207684 s x)). Qed.
Lemma lem5207687 (s : real -> Prop) (x : real -> real) : ((term417 s x) = (term418 s x)) = ((term413 s x) = (term428 s x)).
Proof. exact (MK_COMB (@lem5207680 s x) (@lem5207686 s x)). Qed.
Lemma lem5207688 (s : real -> Prop) (x : real -> real) : (term413 s x) = (term428 s x).
Proof. exact (EQ_MP (@lem5207687 s x) (@lem5207672 s x)). Qed.
Lemma lem5207689 (s : real -> Prop) : (term415 s) = (term429 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5207688 s x)). Qed.
Lemma lem5207690 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207691 (s : real -> Prop) : (term416 s) = (term430 s).
Proof. exact (MK_COMB (@lem5207690) (@lem5207689 s)). Qed.
Lemma lem5207692 (s : real -> Prop) : (term400 s) = (term430 s).
Proof. exact (TRANS (@lem5207668 s) (@lem5207691 s)). Qed.
Lemma lem5207693 (s : real -> Prop) : (term275 s) = (term430 s).
Proof. exact (TRANS (@lem5207648 s) (@lem5207692 s)). Qed.
Lemma lem5207694 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207695 (s : real -> Prop) : (term292 s) = (term431 s).
Proof. exact (MK_COMB (@lem5207694) (@lem5207693 s)). Qed.
Lemma lem5207697 {A : Type'} (P : A -> Prop) (Q : Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5207698 (P : real -> Prop) (Q : Prop) : (term330 P Q) = (term331 P Q).
Proof. exact (@lem5207697 real P Q). Qed.
Lemma lem5207699 (s : real -> Prop) (x : real) (b : real) : (term332 s x b) = (term333 s x b).
Proof. exact (@lem5207698 (term230 x s) (term252 x b)). Qed.
Lemma lem5207700 (x : real) (x' : real) (s : real -> Prop) : (term240 x s x') = (term229 x x' s).
Proof. exact (eq_refl (term240 x s x')). Qed.
Lemma lem5207701 (x : real) (s : real -> Prop) : (term334 x s) = (term230 x s).
Proof. exact (fun_ext (fun x' : real => @lem5207700 x x' s)). Qed.
Lemma lem5207702 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207703 (x : real) (s : real -> Prop) : (term335 x s) = (term160 x s).
Proof. exact (MK_COMB (@lem5207702) (@lem5207701 x s)). Qed.
Lemma lem5207704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5207705 (x : real) (s : real -> Prop) : (term336 x s) = (term253 x s).
Proof. exact (MK_COMB (@lem5207704) (@lem5207703 x s)). Qed.
Lemma lem5207706 (x : real) (b : real) : (term252 x b) = (term252 x b).
Proof. exact (eq_refl (term252 x b)). Qed.
Lemma lem5207707 (s : real -> Prop) (x : real) (b : real) : (term332 s x b) = (term254 s x b).
Proof. exact (MK_COMB (@lem5207705 x s) (@lem5207706 x b)). Qed.
Lemma lem5207708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207709 (s : real -> Prop) (x : real) (b : real) : (term337 s x b) = (term338 s x b).
Proof. exact (MK_COMB (@lem5207708) (@lem5207707 s x b)). Qed.
Lemma lem5207710 (x : real) (x' : real) (s : real -> Prop) : (term240 x s x') = (term229 x x' s).
Proof. exact (eq_refl (term240 x s x')). Qed.
Lemma lem5207711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5207712 (x : real) (x' : real) (s : real -> Prop) : (term339 x s x') = (term340 x x' s).
Proof. exact (MK_COMB (@lem5207711) (@lem5207710 x x' s)). Qed.
Lemma lem5207713 (x : real) (b : real) : (term252 x b) = (term252 x b).
Proof. exact (eq_refl (term252 x b)). Qed.
Lemma lem5207714 (x' : real) (s : real -> Prop) (x : real) (b : real) : (term341 s x' x b) = (term342 x' s x b).
Proof. exact (MK_COMB (@lem5207712 x x' s) (@lem5207713 x b)). Qed.
Lemma lem5207715 (s : real -> Prop) (x : real) (b : real) : (term343 s x b) = (term344 s x b).
Proof. exact (fun_ext (fun x' : real => @lem5207714 x' s x b)). Qed.
Lemma lem5207716 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207717 (s : real -> Prop) (x : real) (b : real) : (term333 s x b) = (term345 s x b).
Proof. exact (MK_COMB (@lem5207716) (@lem5207715 s x b)). Qed.
Lemma lem5207718 (s : real -> Prop) (x : real) (b : real) : ((term332 s x b) = (term333 s x b)) = ((term254 s x b) = (term345 s x b)).
Proof. exact (MK_COMB (@lem5207709 s x b) (@lem5207717 s x b)). Qed.
Lemma lem5207719 (s : real -> Prop) (x : real) (b : real) : (term254 s x b) = (term345 s x b).
Proof. exact (EQ_MP (@lem5207718 s x b) (@lem5207699 s x b)). Qed.
Lemma lem5207720 (s : real -> Prop) (b : real) : (term263 s b) = (term346 s b).
Proof. exact (fun_ext (fun x : real => @lem5207719 s x b)). Qed.
Lemma lem5207721 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207722 (s : real -> Prop) (b : real) : (term264 s b) = (term347 s b).
Proof. exact (MK_COMB (@lem5207721) (@lem5207720 s b)). Qed.
Lemma lem5207723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207724 (s : real -> Prop) (b : real) : (term284 s b) = (term432 s b).
Proof. exact (MK_COMB (@lem5207723) (@lem5207722 s b)). Qed.
Lemma lem5207725 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5207726 (s : real -> Prop) (a : real) (b : real) : (term286 s a b) = (term433 s a b).
Proof. exact (MK_COMB (@lem5207724 s b) (@lem5207725 a b)). Qed.
Lemma lem5207728 {A : Type'} (P : A -> Prop) (Q : Prop) : (term434 A P Q) = (term435 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5207729 (P : real -> Prop) (Q : Prop) : (term436 P Q) = (term437 P Q).
Proof. exact (@lem5207728 real P Q). Qed.
Lemma lem5207730 (s : real -> Prop) (a : real) (b : real) : (term438 s a b) = (term439 s a b).
Proof. exact (@lem5207729 (term346 s b) (real_le a b)). Qed.
Lemma lem5207731 (s : real -> Prop) (x : real) (b : real) : (term359 s b x) = (term345 s x b).
Proof. exact (eq_refl (term359 s b x)). Qed.
Lemma lem5207732 (s : real -> Prop) (b : real) : (term440 s b) = (term346 s b).
Proof. exact (fun_ext (fun x : real => @lem5207731 s x b)). Qed.
Lemma lem5207733 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207734 (s : real -> Prop) (b : real) : (term441 s b) = (term347 s b).
Proof. exact (MK_COMB (@lem5207733) (@lem5207732 s b)). Qed.
Lemma lem5207735 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207736 (s : real -> Prop) (b : real) : (term442 s b) = (term432 s b).
Proof. exact (MK_COMB (@lem5207735) (@lem5207734 s b)). Qed.
Lemma lem5207737 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5207738 (s : real -> Prop) (a : real) (b : real) : (term438 s a b) = (term433 s a b).
Proof. exact (MK_COMB (@lem5207736 s b) (@lem5207737 a b)). Qed.
Lemma lem5207739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207740 (s : real -> Prop) (a : real) (b : real) : (term443 s a b) = (term444 s a b).
Proof. exact (MK_COMB (@lem5207739) (@lem5207738 s a b)). Qed.
Lemma lem5207741 (s : real -> Prop) (x : real) (b : real) : (term359 s b x) = (term345 s x b).
Proof. exact (eq_refl (term359 s b x)). Qed.
Lemma lem5207742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207743 (s : real -> Prop) (x : real) (b : real) : (term445 s b x) = (term446 s x b).
Proof. exact (MK_COMB (@lem5207742) (@lem5207741 s x b)). Qed.
Lemma lem5207744 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5207745 (s : real -> Prop) (x : real) (a : real) (b : real) : (term447 s x a b) = (term448 s x a b).
Proof. exact (MK_COMB (@lem5207743 s x b) (@lem5207744 a b)). Qed.
Lemma lem5207746 (s : real -> Prop) (a : real) (b : real) : (term449 s a b) = (term450 s a b).
Proof. exact (fun_ext (fun x : real => @lem5207745 s x a b)). Qed.
Lemma lem5207747 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207748 (s : real -> Prop) (a : real) (b : real) : (term439 s a b) = (term451 s a b).
Proof. exact (MK_COMB (@lem5207747) (@lem5207746 s a b)). Qed.
Lemma lem5207749 (s : real -> Prop) (a : real) (b : real) : ((term438 s a b) = (term439 s a b)) = ((term433 s a b) = (term451 s a b)).
Proof. exact (MK_COMB (@lem5207740 s a b) (@lem5207748 s a b)). Qed.
Lemma lem5207750 (s : real -> Prop) (a : real) (b : real) : (term433 s a b) = (term451 s a b).
Proof. exact (EQ_MP (@lem5207749 s a b) (@lem5207730 s a b)). Qed.
Lemma lem5207752 {A : Type'} (P : A -> Prop) (Q : Prop) : (term434 A P Q) = (term435 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5207753 (P : real -> Prop) (Q : Prop) : (term436 P Q) = (term437 P Q).
Proof. exact (@lem5207752 real P Q). Qed.
Lemma lem5207754 (s : real -> Prop) (x : real) (a : real) (b : real) : (term452 s x a b) = (term453 s x a b).
Proof. exact (@lem5207753 (term344 s x b) (real_le a b)). Qed.
Lemma lem5207755 (x' : real) (s : real -> Prop) (x : real) (b : real) : (term454 s x b x') = (term342 x' s x b).
Proof. exact (eq_refl (term454 s x b x')). Qed.
Lemma lem5207756 (s : real -> Prop) (x : real) (b : real) : (term455 s x b) = (term344 s x b).
Proof. exact (fun_ext (fun x' : real => @lem5207755 x' s x b)). Qed.
Lemma lem5207757 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207758 (s : real -> Prop) (x : real) (b : real) : (term456 s x b) = (term345 s x b).
Proof. exact (MK_COMB (@lem5207757) (@lem5207756 s x b)). Qed.
Lemma lem5207759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207760 (s : real -> Prop) (x : real) (b : real) : (term457 s x b) = (term446 s x b).
Proof. exact (MK_COMB (@lem5207759) (@lem5207758 s x b)). Qed.
Lemma lem5207761 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5207762 (s : real -> Prop) (x : real) (a : real) (b : real) : (term452 s x a b) = (term448 s x a b).
Proof. exact (MK_COMB (@lem5207760 s x b) (@lem5207761 a b)). Qed.
Lemma lem5207763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207764 (s : real -> Prop) (x : real) (a : real) (b : real) : (term458 s x a b) = (term459 s x a b).
Proof. exact (MK_COMB (@lem5207763) (@lem5207762 s x a b)). Qed.
Lemma lem5207765 (x' : real) (s : real -> Prop) (x : real) (b : real) : (term454 s x b x') = (term342 x' s x b).
Proof. exact (eq_refl (term454 s x b x')). Qed.
Lemma lem5207766 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207767 (x' : real) (s : real -> Prop) (x : real) (b : real) : (term460 s x b x') = (term461 x' s x b).
Proof. exact (MK_COMB (@lem5207766) (@lem5207765 x' s x b)). Qed.
Lemma lem5207768 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5207769 (x' : real) (s : real -> Prop) (x : real) (a : real) (b : real) : (term462 s x x' a b) = (term463 x' s x a b).
Proof. exact (MK_COMB (@lem5207767 x' s x b) (@lem5207768 a b)). Qed.
Lemma lem5207770 (s : real -> Prop) (x : real) (a : real) (b : real) : (term464 s x a b) = (term465 s x a b).
Proof. exact (fun_ext (fun x' : real => @lem5207769 x' s x a b)). Qed.
Lemma lem5207771 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207772 (s : real -> Prop) (x : real) (a : real) (b : real) : (term453 s x a b) = (term466 s x a b).
Proof. exact (MK_COMB (@lem5207771) (@lem5207770 s x a b)). Qed.
Lemma lem5207773 (s : real -> Prop) (x : real) (a : real) (b : real) : ((term452 s x a b) = (term453 s x a b)) = ((term448 s x a b) = (term466 s x a b)).
Proof. exact (MK_COMB (@lem5207764 s x a b) (@lem5207772 s x a b)). Qed.
Lemma lem5207774 (s : real -> Prop) (x : real) (a : real) (b : real) : (term448 s x a b) = (term466 s x a b).
Proof. exact (EQ_MP (@lem5207773 s x a b) (@lem5207754 s x a b)). Qed.
Lemma lem5207775 (s : real -> Prop) (a : real) (b : real) : (term450 s a b) = (term467 s a b).
Proof. exact (fun_ext (fun x : real => @lem5207774 s x a b)). Qed.
Lemma lem5207776 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207777 (s : real -> Prop) (a : real) (b : real) : (term451 s a b) = (term468 s a b).
Proof. exact (MK_COMB (@lem5207776) (@lem5207775 s a b)). Qed.
Lemma lem5207778 (s : real -> Prop) (a : real) (b : real) : (term433 s a b) = (term468 s a b).
Proof. exact (TRANS (@lem5207750 s a b) (@lem5207777 s a b)). Qed.
Lemma lem5207779 (s : real -> Prop) (a : real) (b : real) : (term286 s a b) = (term468 s a b).
Proof. exact (TRANS (@lem5207726 s a b) (@lem5207778 s a b)). Qed.
Lemma lem5207780 (s : real -> Prop) (a : real) : (term287 s a) = (term469 s a).
Proof. exact (fun_ext (fun b : real => @lem5207779 s a b)). Qed.
Lemma lem5207781 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207782 (s : real -> Prop) (a : real) : (term288 s a) = (term470 s a).
Proof. exact (MK_COMB (@lem5207781) (@lem5207780 s a)). Qed.
Lemma lem5207784 {A B : Type'} (P : type1413 A B) : (term350 A B P) = (term351 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5207785 (P : type1626) : (term352 P) = (term353 P).
Proof. exact (@lem5207784 real real P). Qed.
Lemma lem5207786 (s : real -> Prop) (a : real) : (term471 s a) = (term472 s a).
Proof. exact (@lem5207785 (term473 s a)). Qed.
Lemma lem5207787 (s : real -> Prop) (a : real) (b : real) : (term474 s a b) = (term467 s a b).
Proof. exact (eq_refl (term474 s a b)). Qed.
Lemma lem5207788 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5207789 (s : real -> Prop) (a : real) (b : real) (x : real) : (term475 s a b x) = (term476 s a b x).
Proof. exact (MK_COMB (@lem5207787 s a b) (@lem5207788 x)). Qed.
Lemma lem5207790 (s : real -> Prop) (x : real) (a : real) (b : real) : (term476 s a b x) = (term466 s x a b).
Proof. exact (eq_refl (term476 s a b x)). Qed.
Lemma lem5207791 (s : real -> Prop) (x : real) (a : real) (b : real) : (term475 s a b x) = (term466 s x a b).
Proof. exact (TRANS (@lem5207789 s a b x) (@lem5207790 s x a b)). Qed.
Lemma lem5207792 (s : real -> Prop) (a : real) (b : real) : (term477 s a b) = (term467 s a b).
Proof. exact (fun_ext (fun x : real => @lem5207791 s x a b)). Qed.
Lemma lem5207793 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207794 (s : real -> Prop) (a : real) (b : real) : (term478 s a b) = (term468 s a b).
Proof. exact (MK_COMB (@lem5207793) (@lem5207792 s a b)). Qed.
Lemma lem5207795 (s : real -> Prop) (a : real) : (term479 s a) = (term469 s a).
Proof. exact (fun_ext (fun b : real => @lem5207794 s a b)). Qed.
Lemma lem5207796 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207797 (s : real -> Prop) (a : real) : (term471 s a) = (term470 s a).
Proof. exact (MK_COMB (@lem5207796) (@lem5207795 s a)). Qed.
Lemma lem5207798 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207799 (s : real -> Prop) (a : real) : (term480 s a) = (term481 s a).
Proof. exact (MK_COMB (@lem5207798) (@lem5207797 s a)). Qed.
Lemma lem5207800 (s : real -> Prop) (a : real) (b : real) : (term474 s a b) = (term467 s a b).
Proof. exact (eq_refl (term474 s a b)). Qed.
Lemma lem5207801 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5207802 (s : real -> Prop) (a : real) (x : real -> real) (b : real) : (term482 s a x b) = (term483 s a x b).
Proof. exact (MK_COMB (@lem5207800 s a b) (@lem5207801 x b)). Qed.
Lemma lem5207803 (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term483 s a x b) = (term484 s x a b).
Proof. exact (eq_refl (term483 s a x b)). Qed.
Lemma lem5207804 (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term482 s a x b) = (term484 s x a b).
Proof. exact (TRANS (@lem5207802 s a x b) (@lem5207803 s x a b)). Qed.
Lemma lem5207805 (s : real -> Prop) (x : real -> real) (a : real) : (term485 s a x) = (term486 s x a).
Proof. exact (fun_ext (fun b : real => @lem5207804 s x a b)). Qed.
Lemma lem5207806 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207807 (s : real -> Prop) (x : real -> real) (a : real) : (term487 s a x) = (term488 s x a).
Proof. exact (MK_COMB (@lem5207806) (@lem5207805 s x a)). Qed.
Lemma lem5207808 (s : real -> Prop) (a : real) : (term489 s a) = (term490 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5207807 s x a)). Qed.
Lemma lem5207809 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207810 (s : real -> Prop) (a : real) : (term472 s a) = (term491 s a).
Proof. exact (MK_COMB (@lem5207809) (@lem5207808 s a)). Qed.
Lemma lem5207811 (s : real -> Prop) (a : real) : ((term471 s a) = (term472 s a)) = ((term470 s a) = (term491 s a)).
Proof. exact (MK_COMB (@lem5207799 s a) (@lem5207810 s a)). Qed.
Lemma lem5207812 (s : real -> Prop) (a : real) : (term470 s a) = (term491 s a).
Proof. exact (EQ_MP (@lem5207811 s a) (@lem5207786 s a)). Qed.
Lemma lem5207814 {A B : Type'} (P : type1413 A B) : (term350 A B P) = (term351 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5207815 (P : type1626) : (term352 P) = (term353 P).
Proof. exact (@lem5207814 real real P). Qed.
Lemma lem5207816 (s : real -> Prop) (x : real -> real) (a : real) : (term492 s x a) = (term493 s x a).
Proof. exact (@lem5207815 (term494 s x a)). Qed.
Lemma lem5207817 (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term495 s x a b) = (term496 s x a b).
Proof. exact (eq_refl (term495 s x a b)). Qed.
Lemma lem5207818 (x' : real) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5207819 (s : real -> Prop) (x : real -> real) (a : real) (b : real) (x' : real) : (term497 s x a b x') = (term498 s x a b x').
Proof. exact (MK_COMB (@lem5207817 s x a b) (@lem5207818 x')). Qed.
Lemma lem5207820 (x' : real) (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term498 s x a b x') = (term499 x' s x a b).
Proof. exact (eq_refl (term498 s x a b x')). Qed.
Lemma lem5207821 (x' : real) (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term497 s x a b x') = (term499 x' s x a b).
Proof. exact (TRANS (@lem5207819 s x a b x') (@lem5207820 x' s x a b)). Qed.
Lemma lem5207822 (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term500 s x a b) = (term496 s x a b).
Proof. exact (fun_ext (fun x' : real => @lem5207821 x' s x a b)). Qed.
Lemma lem5207823 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207824 (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term501 s x a b) = (term484 s x a b).
Proof. exact (MK_COMB (@lem5207823) (@lem5207822 s x a b)). Qed.
Lemma lem5207825 (s : real -> Prop) (x : real -> real) (a : real) : (term502 s x a) = (term486 s x a).
Proof. exact (fun_ext (fun b : real => @lem5207824 s x a b)). Qed.
Lemma lem5207826 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207827 (s : real -> Prop) (x : real -> real) (a : real) : (term492 s x a) = (term488 s x a).
Proof. exact (MK_COMB (@lem5207826) (@lem5207825 s x a)). Qed.
Lemma lem5207828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207829 (s : real -> Prop) (x : real -> real) (a : real) : (term503 s x a) = (term504 s x a).
Proof. exact (MK_COMB (@lem5207828) (@lem5207827 s x a)). Qed.
Lemma lem5207830 (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term495 s x a b) = (term496 s x a b).
Proof. exact (eq_refl (term495 s x a b)). Qed.
Lemma lem5207831 (x' : real -> real) (b : real) : (x' b) = (x' b).
Proof. exact (eq_refl (x' b)). Qed.
Lemma lem5207832 (s : real -> Prop) (x : real -> real) (a : real) (x' : real -> real) (b : real) : (term505 s x a x' b) = (term506 s x a x' b).
Proof. exact (MK_COMB (@lem5207830 s x a b) (@lem5207831 x' b)). Qed.
Lemma lem5207833 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term506 s x a x' b) = (term507 x' s x a b).
Proof. exact (eq_refl (term506 s x a x' b)). Qed.
Lemma lem5207834 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) (b : real) : (term505 s x a x' b) = (term507 x' s x a b).
Proof. exact (TRANS (@lem5207832 s x a x' b) (@lem5207833 x' s x a b)). Qed.
Lemma lem5207835 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term508 s x a x') = (term509 x' s x a).
Proof. exact (fun_ext (fun b : real => @lem5207834 x' s x a b)). Qed.
Lemma lem5207836 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5207837 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term510 s x a x') = (term511 x' s x a).
Proof. exact (MK_COMB (@lem5207836) (@lem5207835 x' s x a)). Qed.
Lemma lem5207838 (s : real -> Prop) (x : real -> real) (a : real) : (term512 s x a) = (term513 s x a).
Proof. exact (fun_ext (fun x' : real -> real => @lem5207837 x' s x a)). Qed.
Lemma lem5207839 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207840 (s : real -> Prop) (x : real -> real) (a : real) : (term493 s x a) = (term514 s x a).
Proof. exact (MK_COMB (@lem5207839) (@lem5207838 s x a)). Qed.
Lemma lem5207841 (s : real -> Prop) (x : real -> real) (a : real) : ((term492 s x a) = (term493 s x a)) = ((term488 s x a) = (term514 s x a)).
Proof. exact (MK_COMB (@lem5207829 s x a) (@lem5207840 s x a)). Qed.
Lemma lem5207842 (s : real -> Prop) (x : real -> real) (a : real) : (term488 s x a) = (term514 s x a).
Proof. exact (EQ_MP (@lem5207841 s x a) (@lem5207816 s x a)). Qed.
Lemma lem5207843 (s : real -> Prop) (a : real) : (term490 s a) = (term515 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5207842 s x a)). Qed.
Lemma lem5207844 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207845 (s : real -> Prop) (a : real) : (term491 s a) = (term516 s a).
Proof. exact (MK_COMB (@lem5207844) (@lem5207843 s a)). Qed.
Lemma lem5207846 (s : real -> Prop) (a : real) : (term470 s a) = (term516 s a).
Proof. exact (TRANS (@lem5207812 s a) (@lem5207845 s a)). Qed.
Lemma lem5207847 (s : real -> Prop) (a : real) : (term288 s a) = (term516 s a).
Proof. exact (TRANS (@lem5207782 s a) (@lem5207846 s a)). Qed.
Lemma lem5207848 (s : real -> Prop) (a : real) : (term289 s a) = (term289 s a).
Proof. exact (eq_refl (term289 s a)). Qed.
Lemma lem5207849 (s : real -> Prop) (a : real) : (term290 s a) = (term517 s a).
Proof. exact (MK_COMB (@lem5207848 s a) (@lem5207847 s a)). Qed.
Lemma lem5207851 {A : Type'} (P : Prop) (Q : A -> Prop) : (term518 A P Q) = (term519 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5207852 (P : Prop) (Q : type1028) : (term520 P Q) = (term521 P Q).
Proof. exact (@lem5207851 (real -> real) P Q). Qed.
Lemma lem5207853 (s : real -> Prop) (a : real) : (term522 s a) = (term523 s a).
Proof. exact (@lem5207852 (term282 s a) (term515 s a)). Qed.
Lemma lem5207854 (s : real -> Prop) (x : real -> real) (a : real) : (term524 s a x) = (term514 s x a).
Proof. exact (eq_refl (term524 s a x)). Qed.
Lemma lem5207855 (s : real -> Prop) (a : real) : (term525 s a) = (term515 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5207854 s x a)). Qed.
Lemma lem5207856 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207857 (s : real -> Prop) (a : real) : (term526 s a) = (term516 s a).
Proof. exact (MK_COMB (@lem5207856) (@lem5207855 s a)). Qed.
Lemma lem5207858 (s : real -> Prop) (a : real) : (term289 s a) = (term289 s a).
Proof. exact (eq_refl (term289 s a)). Qed.
Lemma lem5207859 (s : real -> Prop) (a : real) : (term522 s a) = (term517 s a).
Proof. exact (MK_COMB (@lem5207858 s a) (@lem5207857 s a)). Qed.
Lemma lem5207860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207861 (s : real -> Prop) (a : real) : (term527 s a) = (term528 s a).
Proof. exact (MK_COMB (@lem5207860) (@lem5207859 s a)). Qed.
Lemma lem5207862 (s : real -> Prop) (x : real -> real) (a : real) : (term524 s a x) = (term514 s x a).
Proof. exact (eq_refl (term524 s a x)). Qed.
Lemma lem5207863 (s : real -> Prop) (a : real) : (term289 s a) = (term289 s a).
Proof. exact (eq_refl (term289 s a)). Qed.
Lemma lem5207864 (s : real -> Prop) (x : real -> real) (a : real) : (term529 s a x) = (term530 s x a).
Proof. exact (MK_COMB (@lem5207863 s a) (@lem5207862 s x a)). Qed.
Lemma lem5207865 (s : real -> Prop) (a : real) : (term531 s a) = (term532 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5207864 s x a)). Qed.
Lemma lem5207866 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207867 (s : real -> Prop) (a : real) : (term523 s a) = (term533 s a).
Proof. exact (MK_COMB (@lem5207866) (@lem5207865 s a)). Qed.
Lemma lem5207868 (s : real -> Prop) (a : real) : ((term522 s a) = (term523 s a)) = ((term517 s a) = (term533 s a)).
Proof. exact (MK_COMB (@lem5207861 s a) (@lem5207867 s a)). Qed.
Lemma lem5207869 (s : real -> Prop) (a : real) : (term517 s a) = (term533 s a).
Proof. exact (EQ_MP (@lem5207868 s a) (@lem5207853 s a)). Qed.
Lemma lem5207871 {A : Type'} (P : Prop) (Q : A -> Prop) : (term518 A P Q) = (term519 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5207872 (P : Prop) (Q : type1028) : (term520 P Q) = (term521 P Q).
Proof. exact (@lem5207871 (real -> real) P Q). Qed.
Lemma lem5207873 (s : real -> Prop) (x : real -> real) (a : real) : (term534 s x a) = (term535 s x a).
Proof. exact (@lem5207872 (term282 s a) (term513 s x a)). Qed.
Lemma lem5207874 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term536 s x a x') = (term511 x' s x a).
Proof. exact (eq_refl (term536 s x a x')). Qed.
Lemma lem5207875 (s : real -> Prop) (x : real -> real) (a : real) : (term537 s x a) = (term513 s x a).
Proof. exact (fun_ext (fun x' : real -> real => @lem5207874 x' s x a)). Qed.
Lemma lem5207876 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207877 (s : real -> Prop) (x : real -> real) (a : real) : (term538 s x a) = (term514 s x a).
Proof. exact (MK_COMB (@lem5207876) (@lem5207875 s x a)). Qed.
Lemma lem5207878 (s : real -> Prop) (a : real) : (term289 s a) = (term289 s a).
Proof. exact (eq_refl (term289 s a)). Qed.
Lemma lem5207879 (s : real -> Prop) (x : real -> real) (a : real) : (term534 s x a) = (term530 s x a).
Proof. exact (MK_COMB (@lem5207878 s a) (@lem5207877 s x a)). Qed.
Lemma lem5207880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207881 (s : real -> Prop) (x : real -> real) (a : real) : (term539 s x a) = (term540 s x a).
Proof. exact (MK_COMB (@lem5207880) (@lem5207879 s x a)). Qed.
Lemma lem5207882 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term536 s x a x') = (term511 x' s x a).
Proof. exact (eq_refl (term536 s x a x')). Qed.
Lemma lem5207883 (s : real -> Prop) (a : real) : (term289 s a) = (term289 s a).
Proof. exact (eq_refl (term289 s a)). Qed.
Lemma lem5207884 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term541 s x a x') = (term542 x' s x a).
Proof. exact (MK_COMB (@lem5207883 s a) (@lem5207882 x' s x a)). Qed.
Lemma lem5207885 (s : real -> Prop) (x : real -> real) (a : real) : (term543 s x a) = (term544 s x a).
Proof. exact (fun_ext (fun x' : real -> real => @lem5207884 x' s x a)). Qed.
Lemma lem5207886 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207887 (s : real -> Prop) (x : real -> real) (a : real) : (term535 s x a) = (term545 s x a).
Proof. exact (MK_COMB (@lem5207886) (@lem5207885 s x a)). Qed.
Lemma lem5207888 (s : real -> Prop) (x : real -> real) (a : real) : ((term534 s x a) = (term535 s x a)) = ((term530 s x a) = (term545 s x a)).
Proof. exact (MK_COMB (@lem5207881 s x a) (@lem5207887 s x a)). Qed.
Lemma lem5207889 (s : real -> Prop) (x : real -> real) (a : real) : (term530 s x a) = (term545 s x a).
Proof. exact (EQ_MP (@lem5207888 s x a) (@lem5207873 s x a)). Qed.
Lemma lem5207890 (s : real -> Prop) (a : real) : (term532 s a) = (term546 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5207889 s x a)). Qed.
Lemma lem5207891 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207892 (s : real -> Prop) (a : real) : (term533 s a) = (term547 s a).
Proof. exact (MK_COMB (@lem5207891) (@lem5207890 s a)). Qed.
Lemma lem5207893 (s : real -> Prop) (a : real) : (term517 s a) = (term547 s a).
Proof. exact (TRANS (@lem5207869 s a) (@lem5207892 s a)). Qed.
Lemma lem5207894 (s : real -> Prop) (a : real) : (term290 s a) = (term547 s a).
Proof. exact (TRANS (@lem5207849 s a) (@lem5207893 s a)). Qed.
Lemma lem5207895 (s : real -> Prop) (a : real) : (term294 s a) = (term548 s a).
Proof. exact (MK_COMB (@lem5207695 s) (@lem5207894 s a)). Qed.
Lemma lem5207897 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term549 A P Q) = (term550 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5207898 (P : type1028) (Q : type1028) : (term551 P Q) = (term552 P Q).
Proof. exact (@lem5207897 (real -> real) P Q). Qed.
Lemma lem5207899 (s : real -> Prop) (a : real) : (term553 s a) = (term554 s a).
Proof. exact (@lem5207898 (term429 s) (term546 s a)). Qed.
Lemma lem5207900 (s : real -> Prop) (x : real -> real) : (term555 s x) = (term428 s x).
Proof. exact (eq_refl (term555 s x)). Qed.
Lemma lem5207901 (s : real -> Prop) : (term556 s) = (term429 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5207900 s x)). Qed.
Lemma lem5207902 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207903 (s : real -> Prop) : (term557 s) = (term430 s).
Proof. exact (MK_COMB (@lem5207902) (@lem5207901 s)). Qed.
Lemma lem5207904 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207905 (s : real -> Prop) : (term558 s) = (term431 s).
Proof. exact (MK_COMB (@lem5207904) (@lem5207903 s)). Qed.
Lemma lem5207906 (s : real -> Prop) (x : real -> real) (a : real) : (term559 s a x) = (term545 s x a).
Proof. exact (eq_refl (term559 s a x)). Qed.
Lemma lem5207907 (s : real -> Prop) (a : real) : (term560 s a) = (term546 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5207906 s x a)). Qed.
Lemma lem5207908 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207909 (s : real -> Prop) (a : real) : (term561 s a) = (term547 s a).
Proof. exact (MK_COMB (@lem5207908) (@lem5207907 s a)). Qed.
Lemma lem5207910 (s : real -> Prop) (a : real) : (term553 s a) = (term548 s a).
Proof. exact (MK_COMB (@lem5207905 s) (@lem5207909 s a)). Qed.
Lemma lem5207911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207912 (s : real -> Prop) (a : real) : (term562 s a) = (term563 s a).
Proof. exact (MK_COMB (@lem5207911) (@lem5207910 s a)). Qed.
Lemma lem5207913 (s : real -> Prop) (x : real -> real) : (term555 s x) = (term428 s x).
Proof. exact (eq_refl (term555 s x)). Qed.
Lemma lem5207914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207915 (s : real -> Prop) (x : real -> real) : (term564 s x) = (term565 s x).
Proof. exact (MK_COMB (@lem5207914) (@lem5207913 s x)). Qed.
Lemma lem5207916 (s : real -> Prop) (x : real -> real) (a : real) : (term559 s a x) = (term545 s x a).
Proof. exact (eq_refl (term559 s a x)). Qed.
Lemma lem5207917 (s : real -> Prop) (x : real -> real) (a : real) : (term566 s a x) = (term567 s x a).
Proof. exact (MK_COMB (@lem5207915 s x) (@lem5207916 s x a)). Qed.
Lemma lem5207918 (s : real -> Prop) (a : real) : (term568 s a) = (term569 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5207917 s x a)). Qed.
Lemma lem5207919 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207920 (s : real -> Prop) (a : real) : (term554 s a) = (term570 s a).
Proof. exact (MK_COMB (@lem5207919) (@lem5207918 s a)). Qed.
Lemma lem5207921 (s : real -> Prop) (a : real) : ((term553 s a) = (term554 s a)) = ((term548 s a) = (term570 s a)).
Proof. exact (MK_COMB (@lem5207912 s a) (@lem5207920 s a)). Qed.
Lemma lem5207922 (s : real -> Prop) (a : real) : (term548 s a) = (term570 s a).
Proof. exact (EQ_MP (@lem5207921 s a) (@lem5207899 s a)). Qed.
Lemma lem5207924 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term549 A P Q) = (term550 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5207925 (P : type1028) (Q : type1028) : (term551 P Q) = (term552 P Q).
Proof. exact (@lem5207924 (real -> real) P Q). Qed.
Lemma lem5207926 (s : real -> Prop) (x : real -> real) (a : real) : (term571 s x a) = (term572 s x a).
Proof. exact (@lem5207925 (term427 s x) (term544 s x a)). Qed.
Lemma lem5207927 (x' : real -> real) (s : real -> Prop) (x : real -> real) : (term573 s x x') = (term425 x' s x).
Proof. exact (eq_refl (term573 s x x')). Qed.
Lemma lem5207928 (s : real -> Prop) (x : real -> real) : (term574 s x) = (term427 s x).
Proof. exact (fun_ext (fun x' : real -> real => @lem5207927 x' s x)). Qed.
Lemma lem5207929 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207930 (s : real -> Prop) (x : real -> real) : (term575 s x) = (term428 s x).
Proof. exact (MK_COMB (@lem5207929) (@lem5207928 s x)). Qed.
Lemma lem5207931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207932 (s : real -> Prop) (x : real -> real) : (term576 s x) = (term565 s x).
Proof. exact (MK_COMB (@lem5207931) (@lem5207930 s x)). Qed.
Lemma lem5207933 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term577 s x a x') = (term542 x' s x a).
Proof. exact (eq_refl (term577 s x a x')). Qed.
Lemma lem5207934 (s : real -> Prop) (x : real -> real) (a : real) : (term578 s x a) = (term544 s x a).
Proof. exact (fun_ext (fun x' : real -> real => @lem5207933 x' s x a)). Qed.
Lemma lem5207935 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207936 (s : real -> Prop) (x : real -> real) (a : real) : (term579 s x a) = (term545 s x a).
Proof. exact (MK_COMB (@lem5207935) (@lem5207934 s x a)). Qed.
Lemma lem5207937 (s : real -> Prop) (x : real -> real) (a : real) : (term571 s x a) = (term567 s x a).
Proof. exact (MK_COMB (@lem5207932 s x) (@lem5207936 s x a)). Qed.
Lemma lem5207938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207939 (s : real -> Prop) (x : real -> real) (a : real) : (term580 s x a) = (term581 s x a).
Proof. exact (MK_COMB (@lem5207938) (@lem5207937 s x a)). Qed.
Lemma lem5207940 (x' : real -> real) (s : real -> Prop) (x : real -> real) : (term573 s x x') = (term425 x' s x).
Proof. exact (eq_refl (term573 s x x')). Qed.
Lemma lem5207941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207942 (x' : real -> real) (s : real -> Prop) (x : real -> real) : (term582 s x x') = (term583 x' s x).
Proof. exact (MK_COMB (@lem5207941) (@lem5207940 x' s x)). Qed.
Lemma lem5207943 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term577 s x a x') = (term542 x' s x a).
Proof. exact (eq_refl (term577 s x a x')). Qed.
Lemma lem5207944 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term584 s x a x') = (term585 x' s x a).
Proof. exact (MK_COMB (@lem5207942 x' s x) (@lem5207943 x' s x a)). Qed.
Lemma lem5207945 (s : real -> Prop) (x : real -> real) (a : real) : (term586 s x a) = (term587 s x a).
Proof. exact (fun_ext (fun x' : real -> real => @lem5207944 x' s x a)). Qed.
Lemma lem5207946 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207947 (s : real -> Prop) (x : real -> real) (a : real) : (term572 s x a) = (term588 s x a).
Proof. exact (MK_COMB (@lem5207946) (@lem5207945 s x a)). Qed.
Lemma lem5207948 (s : real -> Prop) (x : real -> real) (a : real) : ((term571 s x a) = (term572 s x a)) = ((term567 s x a) = (term588 s x a)).
Proof. exact (MK_COMB (@lem5207939 s x a) (@lem5207947 s x a)). Qed.
Lemma lem5207949 (s : real -> Prop) (x : real -> real) (a : real) : (term567 s x a) = (term588 s x a).
Proof. exact (EQ_MP (@lem5207948 s x a) (@lem5207926 s x a)). Qed.
Lemma lem5207950 (s : real -> Prop) (a : real) : (term569 s a) = (term589 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5207949 s x a)). Qed.
Lemma lem5207951 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5207952 (s : real -> Prop) (a : real) : (term570 s a) = (term590 s a).
Proof. exact (MK_COMB (@lem5207951) (@lem5207950 s a)). Qed.
Lemma lem5207953 (s : real -> Prop) (a : real) : (term548 s a) = (term590 s a).
Proof. exact (TRANS (@lem5207922 s a) (@lem5207952 s a)). Qed.
Lemma lem5207954 (s : real -> Prop) (a : real) : (term294 s a) = (term590 s a).
Proof. exact (TRANS (@lem5207895 s a) (@lem5207953 s a)). Qed.
Lemma lem5207955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5207956 (s : real -> Prop) (a : real) : (term325 s a) = (term591 s a).
Proof. exact (MK_COMB (@lem5207955) (@lem5207954 s a)). Qed.
Lemma lem5207958 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term549 A P Q) = (term550 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5207959 (P : real -> Prop) (Q : real -> Prop) : (term592 P Q) = (term593 P Q).
Proof. exact (@lem5207958 real P Q). Qed.
Lemma lem5207960 (s : real -> Prop) (a : real) : (term594 s a) = (term595 s a).
Proof. exact (@lem5207959 (term302 s a) (term317 s a)). Qed.
Lemma lem5207961 (s : real -> Prop) (b : real) (a : real) : (term596 s a b) = (term296 s b a).
Proof. exact (eq_refl (term596 s a b)). Qed.
Lemma lem5207962 (s : real -> Prop) (a : real) : (term597 s a) = (term302 s a).
Proof. exact (fun_ext (fun b : real => @lem5207961 s b a)). Qed.
Lemma lem5207963 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207964 (s : real -> Prop) (a : real) : (term598 s a) = (term303 s a).
Proof. exact (MK_COMB (@lem5207963) (@lem5207962 s a)). Qed.
Lemma lem5207965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207966 (s : real -> Prop) (a : real) : (term599 s a) = (term320 s a).
Proof. exact (MK_COMB (@lem5207965) (@lem5207964 s a)). Qed.
Lemma lem5207967 (s : real -> Prop) (a : real) (b : real) : (term600 s a b) = (term310 s a b).
Proof. exact (eq_refl (term600 s a b)). Qed.
Lemma lem5207968 (s : real -> Prop) (a : real) : (term601 s a) = (term317 s a).
Proof. exact (fun_ext (fun b : real => @lem5207967 s a b)). Qed.
Lemma lem5207969 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207970 (s : real -> Prop) (a : real) : (term602 s a) = (term318 s a).
Proof. exact (MK_COMB (@lem5207969) (@lem5207968 s a)). Qed.
Lemma lem5207971 (s : real -> Prop) (a : real) : (term594 s a) = (term322 s a).
Proof. exact (MK_COMB (@lem5207966 s a) (@lem5207970 s a)). Qed.
Lemma lem5207972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207973 (s : real -> Prop) (a : real) : (term603 s a) = (term604 s a).
Proof. exact (MK_COMB (@lem5207972) (@lem5207971 s a)). Qed.
Lemma lem5207974 (s : real -> Prop) (b : real) (a : real) : (term596 s a b) = (term296 s b a).
Proof. exact (eq_refl (term596 s a b)). Qed.
Lemma lem5207975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5207976 (s : real -> Prop) (b : real) (a : real) : (term605 s a b) = (term606 s b a).
Proof. exact (MK_COMB (@lem5207975) (@lem5207974 s b a)). Qed.
Lemma lem5207977 (s : real -> Prop) (a : real) (b : real) : (term600 s a b) = (term310 s a b).
Proof. exact (eq_refl (term600 s a b)). Qed.
Lemma lem5207978 (s : real -> Prop) (a : real) (b : real) : (term607 s a b) = (term608 s a b).
Proof. exact (MK_COMB (@lem5207976 s b a) (@lem5207977 s a b)). Qed.
Lemma lem5207979 (s : real -> Prop) (a : real) : (term609 s a) = (term610 s a).
Proof. exact (fun_ext (fun b : real => @lem5207978 s a b)). Qed.
Lemma lem5207980 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5207981 (s : real -> Prop) (a : real) : (term595 s a) = (term611 s a).
Proof. exact (MK_COMB (@lem5207980) (@lem5207979 s a)). Qed.
Lemma lem5207982 (s : real -> Prop) (a : real) : ((term594 s a) = (term595 s a)) = ((term322 s a) = (term611 s a)).
Proof. exact (MK_COMB (@lem5207973 s a) (@lem5207981 s a)). Qed.
Lemma lem5207983 (s : real -> Prop) (a : real) : (term322 s a) = (term611 s a).
Proof. exact (EQ_MP (@lem5207982 s a) (@lem5207960 s a)). Qed.
Lemma lem5207986 (s : real -> Prop) (a : real) : (term612 s a) = (term612 s a).
Proof. exact (eq_refl (term612 s a)). Qed.
Lemma lem5207987 (s : real -> Prop) (a : real) : (term612 s a) = ((term322 s a) = (term611 s a)).
Proof. exact (eq_refl (term612 s a)). Qed.
Lemma lem5207988 (s : real -> Prop) (a : real) : (term613 s a) = (term613 s a).
Proof. exact (eq_refl (term613 s a)). Qed.
Lemma lem5207989 (s : real -> Prop) (a : real) : ((term612 s a) = (term612 s a)) = ((term612 s a) = ((term322 s a) = (term611 s a))).
Proof. exact (MK_COMB (@lem5207988 s a) (@lem5207987 s a)). Qed.
Lemma lem5207990 (s : real -> Prop) (a : real) : (term612 s a) = ((term322 s a) = (term611 s a)).
Proof. exact (eq_refl (term612 s a)). Qed.
Lemma lem5207991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5207992 (s : real -> Prop) (a : real) : (term613 s a) = (term614 s a).
Proof. exact (MK_COMB (@lem5207991) (@lem5207990 s a)). Qed.
Lemma lem5207993 (s : real -> Prop) (a : real) : ((term322 s a) = (term611 s a)) = ((term322 s a) = (term611 s a)).
Proof. exact (eq_refl ((term322 s a) = (term611 s a))). Qed.
Lemma lem5207994 (s : real -> Prop) (a : real) : ((term612 s a) = ((term322 s a) = (term611 s a))) = (((term322 s a) = (term611 s a)) = ((term322 s a) = (term611 s a))).
Proof. exact (MK_COMB (@lem5207992 s a) (@lem5207993 s a)). Qed.
Lemma lem5207995 (s : real -> Prop) (a : real) : ((term612 s a) = (term612 s a)) = (((term322 s a) = (term611 s a)) = ((term322 s a) = (term611 s a))).
Proof. exact (TRANS (@lem5207989 s a) (@lem5207994 s a)). Qed.
Lemma lem5207996 (s : real -> Prop) (a : real) : ((term322 s a) = (term611 s a)) = ((term322 s a) = (term611 s a)).
Proof. exact (EQ_MP (@lem5207995 s a) (@lem5207986 s a)). Qed.
Lemma lem5207997 (s : real -> Prop) (a : real) : (term322 s a) = (term611 s a).
Proof. exact (EQ_MP (@lem5207996 s a) (@lem5207983 s a)). Qed.
Lemma lem5207998 (s : real -> Prop) (a : real) : (term327 s a) = (term615 s a).
Proof. exact (MK_COMB (@lem5207956 s a) (@lem5207997 s a)). Qed.
Lemma lem5208000 {A : Type'} (P : A -> Prop) (Q : Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5208001 (P : type1028) (Q : Prop) : (term616 P Q) = (term617 P Q).
Proof. exact (@lem5208000 (real -> real) P Q). Qed.
Lemma lem5208002 (s : real -> Prop) (a : real) : (term618 s a) = (term619 s a).
Proof. exact (@lem5208001 (term589 s a) (term611 s a)). Qed.
Lemma lem5208003 (s : real -> Prop) (x : real -> real) (a : real) : (term620 s a x) = (term588 s x a).
Proof. exact (eq_refl (term620 s a x)). Qed.
Lemma lem5208004 (s : real -> Prop) (a : real) : (term621 s a) = (term589 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5208003 s x a)). Qed.
Lemma lem5208005 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5208006 (s : real -> Prop) (a : real) : (term622 s a) = (term590 s a).
Proof. exact (MK_COMB (@lem5208005) (@lem5208004 s a)). Qed.
Lemma lem5208007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208008 (s : real -> Prop) (a : real) : (term623 s a) = (term591 s a).
Proof. exact (MK_COMB (@lem5208007) (@lem5208006 s a)). Qed.
Lemma lem5208009 (s : real -> Prop) (a : real) : (term611 s a) = (term611 s a).
Proof. exact (eq_refl (term611 s a)). Qed.
Lemma lem5208010 (s : real -> Prop) (a : real) : (term618 s a) = (term615 s a).
Proof. exact (MK_COMB (@lem5208008 s a) (@lem5208009 s a)). Qed.
Lemma lem5208011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5208012 (s : real -> Prop) (a : real) : (term624 s a) = (term625 s a).
Proof. exact (MK_COMB (@lem5208011) (@lem5208010 s a)). Qed.
Lemma lem5208013 (s : real -> Prop) (x : real -> real) (a : real) : (term620 s a x) = (term588 s x a).
Proof. exact (eq_refl (term620 s a x)). Qed.
Lemma lem5208014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208015 (s : real -> Prop) (x : real -> real) (a : real) : (term626 s a x) = (term627 s x a).
Proof. exact (MK_COMB (@lem5208014) (@lem5208013 s x a)). Qed.
Lemma lem5208016 (s : real -> Prop) (a : real) : (term611 s a) = (term611 s a).
Proof. exact (eq_refl (term611 s a)). Qed.
Lemma lem5208017 (x : real -> real) (s : real -> Prop) (a : real) : (term628 x s a) = (term629 x s a).
Proof. exact (MK_COMB (@lem5208015 s x a) (@lem5208016 s a)). Qed.
Lemma lem5208018 (s : real -> Prop) (a : real) : (term630 s a) = (term631 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5208017 x s a)). Qed.
Lemma lem5208019 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5208020 (s : real -> Prop) (a : real) : (term619 s a) = (term632 s a).
Proof. exact (MK_COMB (@lem5208019) (@lem5208018 s a)). Qed.
Lemma lem5208021 (s : real -> Prop) (a : real) : ((term618 s a) = (term619 s a)) = ((term615 s a) = (term632 s a)).
Proof. exact (MK_COMB (@lem5208012 s a) (@lem5208020 s a)). Qed.
Lemma lem5208022 (s : real -> Prop) (a : real) : (term615 s a) = (term632 s a).
Proof. exact (EQ_MP (@lem5208021 s a) (@lem5208002 s a)). Qed.
Lemma lem5208024 {A : Type'} (P : A -> Prop) (Q : Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5208025 (P : type1028) (Q : Prop) : (term616 P Q) = (term617 P Q).
Proof. exact (@lem5208024 (real -> real) P Q). Qed.
Lemma lem5208026 (x : real -> real) (s : real -> Prop) (a : real) : (term633 x s a) = (term634 x s a).
Proof. exact (@lem5208025 (term587 s x a) (term611 s a)). Qed.
Lemma lem5208027 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term635 s x a x') = (term585 x' s x a).
Proof. exact (eq_refl (term635 s x a x')). Qed.
Lemma lem5208028 (s : real -> Prop) (x : real -> real) (a : real) : (term636 s x a) = (term587 s x a).
Proof. exact (fun_ext (fun x' : real -> real => @lem5208027 x' s x a)). Qed.
Lemma lem5208029 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5208030 (s : real -> Prop) (x : real -> real) (a : real) : (term637 s x a) = (term588 s x a).
Proof. exact (MK_COMB (@lem5208029) (@lem5208028 s x a)). Qed.
Lemma lem5208031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208032 (s : real -> Prop) (x : real -> real) (a : real) : (term638 s x a) = (term627 s x a).
Proof. exact (MK_COMB (@lem5208031) (@lem5208030 s x a)). Qed.
Lemma lem5208033 (s : real -> Prop) (a : real) : (term611 s a) = (term611 s a).
Proof. exact (eq_refl (term611 s a)). Qed.
Lemma lem5208034 (x : real -> real) (s : real -> Prop) (a : real) : (term633 x s a) = (term629 x s a).
Proof. exact (MK_COMB (@lem5208032 s x a) (@lem5208033 s a)). Qed.
Lemma lem5208035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5208036 (x : real -> real) (s : real -> Prop) (a : real) : (term639 x s a) = (term640 x s a).
Proof. exact (MK_COMB (@lem5208035) (@lem5208034 x s a)). Qed.
Lemma lem5208037 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term635 s x a x') = (term585 x' s x a).
Proof. exact (eq_refl (term635 s x a x')). Qed.
Lemma lem5208038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208039 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term641 s x a x') = (term642 x' s x a).
Proof. exact (MK_COMB (@lem5208038) (@lem5208037 x' s x a)). Qed.
Lemma lem5208040 (s : real -> Prop) (a : real) : (term611 s a) = (term611 s a).
Proof. exact (eq_refl (term611 s a)). Qed.
Lemma lem5208041 (x' : real -> real) (x : real -> real) (s : real -> Prop) (a : real) : (term643 x x' s a) = (term644 x' x s a).
Proof. exact (MK_COMB (@lem5208039 x' s x a) (@lem5208040 s a)). Qed.
Lemma lem5208042 (x : real -> real) (s : real -> Prop) (a : real) : (term645 x s a) = (term646 x s a).
Proof. exact (fun_ext (fun x' : real -> real => @lem5208041 x' x s a)). Qed.
Lemma lem5208043 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5208044 (x : real -> real) (s : real -> Prop) (a : real) : (term634 x s a) = (term647 x s a).
Proof. exact (MK_COMB (@lem5208043) (@lem5208042 x s a)). Qed.
Lemma lem5208045 (x : real -> real) (s : real -> Prop) (a : real) : ((term633 x s a) = (term634 x s a)) = ((term629 x s a) = (term647 x s a)).
Proof. exact (MK_COMB (@lem5208036 x s a) (@lem5208044 x s a)). Qed.
Lemma lem5208046 (x : real -> real) (s : real -> Prop) (a : real) : (term629 x s a) = (term647 x s a).
Proof. exact (EQ_MP (@lem5208045 x s a) (@lem5208026 x s a)). Qed.
Lemma lem5208048 {A : Type'} (P : Prop) (Q : A -> Prop) : (term518 A P Q) = (term519 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5208049 (P : Prop) (Q : real -> Prop) : (term648 P Q) = (term649 P Q).
Proof. exact (@lem5208048 real P Q). Qed.
Lemma lem5208050 (x' : real -> real) (x : real -> real) (s : real -> Prop) (a : real) : (term650 x' x s a) = (term651 x' x s a).
Proof. exact (@lem5208049 (term585 x' s x a) (term610 s a)). Qed.
Lemma lem5208051 (s : real -> Prop) (a : real) (b : real) : (term652 s a b) = (term608 s a b).
Proof. exact (eq_refl (term652 s a b)). Qed.
Lemma lem5208052 (s : real -> Prop) (a : real) : (term653 s a) = (term610 s a).
Proof. exact (fun_ext (fun b : real => @lem5208051 s a b)). Qed.
Lemma lem5208053 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5208054 (s : real -> Prop) (a : real) : (term654 s a) = (term611 s a).
Proof. exact (MK_COMB (@lem5208053) (@lem5208052 s a)). Qed.
Lemma lem5208055 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term642 x' s x a) = (term642 x' s x a).
Proof. exact (eq_refl (term642 x' s x a)). Qed.
Lemma lem5208056 (x' : real -> real) (x : real -> real) (s : real -> Prop) (a : real) : (term650 x' x s a) = (term644 x' x s a).
Proof. exact (MK_COMB (@lem5208055 x' s x a) (@lem5208054 s a)). Qed.
Lemma lem5208057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5208058 (x' : real -> real) (x : real -> real) (s : real -> Prop) (a : real) : (term655 x' x s a) = (term656 x' x s a).
Proof. exact (MK_COMB (@lem5208057) (@lem5208056 x' x s a)). Qed.
Lemma lem5208059 (s : real -> Prop) (a : real) (b : real) : (term652 s a b) = (term608 s a b).
Proof. exact (eq_refl (term652 s a b)). Qed.
Lemma lem5208060 (x' : real -> real) (s : real -> Prop) (x : real -> real) (a : real) : (term642 x' s x a) = (term642 x' s x a).
Proof. exact (eq_refl (term642 x' s x a)). Qed.
Lemma lem5208061 (x' : real -> real) (x : real -> real) (s : real -> Prop) (a : real) (b : real) : (term657 x' x s a b) = (term658 x' x s a b).
Proof. exact (MK_COMB (@lem5208060 x' s x a) (@lem5208059 s a b)). Qed.
Lemma lem5208062 (x' : real -> real) (x : real -> real) (s : real -> Prop) (a : real) : (term659 x' x s a) = (term660 x' x s a).
Proof. exact (fun_ext (fun b : real => @lem5208061 x' x s a b)). Qed.
Lemma lem5208063 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5208064 (x' : real -> real) (x : real -> real) (s : real -> Prop) (a : real) : (term651 x' x s a) = (term661 x' x s a).
Proof. exact (MK_COMB (@lem5208063) (@lem5208062 x' x s a)). Qed.
Lemma lem5208065 (x' : real -> real) (x : real -> real) (s : real -> Prop) (a : real) : ((term650 x' x s a) = (term651 x' x s a)) = ((term644 x' x s a) = (term661 x' x s a)).
Proof. exact (MK_COMB (@lem5208058 x' x s a) (@lem5208064 x' x s a)). Qed.
Lemma lem5208066 (x' : real -> real) (x : real -> real) (s : real -> Prop) (a : real) : (term644 x' x s a) = (term661 x' x s a).
Proof. exact (EQ_MP (@lem5208065 x' x s a) (@lem5208050 x' x s a)). Qed.
Lemma lem5208067 (x : real -> real) (s : real -> Prop) (a : real) : (term646 x s a) = (term662 x s a).
Proof. exact (fun_ext (fun x' : real -> real => @lem5208066 x' x s a)). Qed.
Lemma lem5208068 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5208069 (x : real -> real) (s : real -> Prop) (a : real) : (term647 x s a) = (term663 x s a).
Proof. exact (MK_COMB (@lem5208068) (@lem5208067 x s a)). Qed.
Lemma lem5208070 (x : real -> real) (s : real -> Prop) (a : real) : (term629 x s a) = (term663 x s a).
Proof. exact (TRANS (@lem5208046 x s a) (@lem5208069 x s a)). Qed.
Lemma lem5208071 (s : real -> Prop) (a : real) : (term631 s a) = (term664 s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5208070 x s a)). Qed.
Lemma lem5208072 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5208073 (s : real -> Prop) (a : real) : (term632 s a) = (term665 s a).
Proof. exact (MK_COMB (@lem5208072) (@lem5208071 s a)). Qed.
Lemma lem5208074 (s : real -> Prop) (a : real) : (term615 s a) = (term665 s a).
Proof. exact (TRANS (@lem5208022 s a) (@lem5208073 s a)). Qed.
Lemma lem5208076 (s : real -> Prop) (a : real) : (term327 s a) = (term665 s a).
Proof. exact (TRANS (@lem5207998 s a) (@lem5208074 s a)). Qed.
Lemma lem5208077 (s : real -> Prop) (a : real) : (term188 s a) = (term665 s a).
Proof. exact (TRANS (@lem5207014 s a) (@lem5208076 s a)). Qed.
Lemma lem5208078 (s : real -> Prop) (a : real) (h1 : term188 s a) : term665 s a.
Proof. exact (EQ_MP (@lem5208077 s a) (@lem5206750 s a h1)). Qed.
Lemma lem5208093 (y : real) (x : real) : ((term28 x y) = (real_le y x)) = (term666 y x).
Proof. exact (@lem17784 (term28 x y) (real_le y x)). Qed.
Lemma lem5208094 (x : real) : (term29 x) = (term667 x).
Proof. exact (fun_ext (fun y : real => @lem5208093 y x)). Qed.
Lemma lem5208095 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208096 (x : real) : (term31 x) = (term668 x).
Proof. exact (MK_COMB (@lem5208095) (@lem5208094 x)). Qed.
Lemma lem5208097 : term33 = term669.
Proof. exact (fun_ext (fun x : real => @lem5208096 x)). Qed.
Lemma lem5208098 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208099 : term35 = term670.
Proof. exact (MK_COMB (@lem5208098) (@lem5208097)). Qed.
Lemma lem5208105 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term671 A P Q) = (term672 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5208106 (P : real -> Prop) (Q : real -> Prop) : (term673 P Q) = (term674 P Q).
Proof. exact (@lem5208105 real P Q). Qed.
Lemma lem5208107 (x : real) : (term675 x) = (term676 x).
Proof. exact (@lem5208106 (term677 x) (term678 x)). Qed.
Lemma lem5208108 (y : real) (x : real) : (term679 x y) = (term680 y x).
Proof. exact (eq_refl (term679 x y)). Qed.
Lemma lem5208109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208110 (y : real) (x : real) : (term681 x y) = (term682 y x).
Proof. exact (MK_COMB (@lem5208109) (@lem5208108 y x)). Qed.
Lemma lem5208111 (y : real) (x : real) : (term683 x y) = (term684 y x).
Proof. exact (eq_refl (term683 x y)). Qed.
Lemma lem5208112 (y : real) (x : real) : (term685 x y) = (term666 y x).
Proof. exact (MK_COMB (@lem5208110 y x) (@lem5208111 y x)). Qed.
Lemma lem5208113 (x : real) : (term686 x) = (term667 x).
Proof. exact (fun_ext (fun y : real => @lem5208112 y x)). Qed.
Lemma lem5208114 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208115 (x : real) : (term675 x) = (term668 x).
Proof. exact (MK_COMB (@lem5208114) (@lem5208113 x)). Qed.
Lemma lem5208116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5208117 (x : real) : (term687 x) = (term688 x).
Proof. exact (MK_COMB (@lem5208116) (@lem5208115 x)). Qed.
Lemma lem5208118 (y : real) (x : real) : (term679 x y) = (term680 y x).
Proof. exact (eq_refl (term679 x y)). Qed.
Lemma lem5208119 (x : real) : (term689 x) = (term677 x).
Proof. exact (fun_ext (fun y : real => @lem5208118 y x)). Qed.
Lemma lem5208120 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208121 (x : real) : (term690 x) = (term691 x).
Proof. exact (MK_COMB (@lem5208120) (@lem5208119 x)). Qed.
Lemma lem5208122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208123 (x : real) : (term692 x) = (term693 x).
Proof. exact (MK_COMB (@lem5208122) (@lem5208121 x)). Qed.
Lemma lem5208124 (y : real) (x : real) : (term683 x y) = (term684 y x).
Proof. exact (eq_refl (term683 x y)). Qed.
Lemma lem5208125 (x : real) : (term694 x) = (term678 x).
Proof. exact (fun_ext (fun y : real => @lem5208124 y x)). Qed.
Lemma lem5208126 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208127 (x : real) : (term695 x) = (term696 x).
Proof. exact (MK_COMB (@lem5208126) (@lem5208125 x)). Qed.
Lemma lem5208128 (x : real) : (term676 x) = (term697 x).
Proof. exact (MK_COMB (@lem5208123 x) (@lem5208127 x)). Qed.
Lemma lem5208129 (x : real) : ((term675 x) = (term676 x)) = ((term668 x) = (term697 x)).
Proof. exact (MK_COMB (@lem5208117 x) (@lem5208128 x)). Qed.
Lemma lem5208130 (x : real) : (term668 x) = (term697 x).
Proof. exact (EQ_MP (@lem5208129 x) (@lem5208107 x)). Qed.
Lemma lem5208227 : term669 = term698.
Proof. exact (fun_ext (fun x : real => @lem5208130 x)). Qed.
Lemma lem5208228 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208229 : term670 = term699.
Proof. exact (MK_COMB (@lem5208228) (@lem5208227)). Qed.
Lemma lem5208231 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term671 A P Q) = (term672 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5208232 (P : real -> Prop) (Q : real -> Prop) : (term673 P Q) = (term674 P Q).
Proof. exact (@lem5208231 real P Q). Qed.
Lemma lem5208233 : term700 = term701.
Proof. exact (@lem5208232 term702 term703). Qed.
Lemma lem5208234 (x : real) : (term704 x) = (term691 x).
Proof. exact (eq_refl (term704 x)). Qed.
Lemma lem5208235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208236 (x : real) : (term705 x) = (term693 x).
Proof. exact (MK_COMB (@lem5208235) (@lem5208234 x)). Qed.
Lemma lem5208237 (x : real) : (term706 x) = (term696 x).
Proof. exact (eq_refl (term706 x)). Qed.
Lemma lem5208238 (x : real) : (term707 x) = (term697 x).
Proof. exact (MK_COMB (@lem5208236 x) (@lem5208237 x)). Qed.
Lemma lem5208239 : term708 = term698.
Proof. exact (fun_ext (fun x : real => @lem5208238 x)). Qed.
Lemma lem5208240 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208241 : term700 = term699.
Proof. exact (MK_COMB (@lem5208240) (@lem5208239)). Qed.
Lemma lem5208242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5208243 : term709 = term710.
Proof. exact (MK_COMB (@lem5208242) (@lem5208241)). Qed.
Lemma lem5208244 (x : real) : (term704 x) = (term691 x).
Proof. exact (eq_refl (term704 x)). Qed.
Lemma lem5208245 : term711 = term702.
Proof. exact (fun_ext (fun x : real => @lem5208244 x)). Qed.
Lemma lem5208246 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208247 : term712 = term713.
Proof. exact (MK_COMB (@lem5208246) (@lem5208245)). Qed.
Lemma lem5208248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208249 : term714 = term715.
Proof. exact (MK_COMB (@lem5208248) (@lem5208247)). Qed.
Lemma lem5208250 (x : real) : (term706 x) = (term696 x).
Proof. exact (eq_refl (term706 x)). Qed.
Lemma lem5208251 : term716 = term703.
Proof. exact (fun_ext (fun x : real => @lem5208250 x)). Qed.
Lemma lem5208252 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208253 : term717 = term718.
Proof. exact (MK_COMB (@lem5208252) (@lem5208251)). Qed.
Lemma lem5208254 : term701 = term719.
Proof. exact (MK_COMB (@lem5208249) (@lem5208253)). Qed.
Lemma lem5208255 : (term700 = term701) = (term699 = term719).
Proof. exact (MK_COMB (@lem5208243) (@lem5208254)). Qed.
Lemma lem5208256 : term699 = term719.
Proof. exact (EQ_MP (@lem5208255) (@lem5208233)). Qed.
Lemma lem5208363 : term670 = term719.
Proof. exact (TRANS (@lem5208229) (@lem5208256)). Qed.
Lemma lem5208364 : term35 = term719.
Proof. exact (TRANS (@lem5208099) (@lem5208363)). Qed.
Lemma lem5208365 (h1 : term35) : term719.
Proof. exact (EQ_MP (@lem5208364) (@lem5206751 h1)). Qed.
Lemma lem5208367 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5208368 (P : real -> Prop) : (term236 P) = (term237 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5208369 (s : real -> Prop) : (term720 s) = (term721 s).
Proof. exact (@lem5208368 (term226 s)). Qed.
Lemma lem5208370 (x : real) (s : real -> Prop) : (term722 s x) = (@IN real x s).
Proof. exact (eq_refl (term722 s x)). Qed.
Lemma lem5208371 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5208373 (x : real) (s : real -> Prop) : (term723 s x) = (term724 x s).
Proof. exact (MK_COMB (@lem5208371) (@lem5208370 x s)). Qed.
Lemma lem5208374 (s : real -> Prop) : (term725 s) = (term726 s).
Proof. exact (fun_ext (fun x : real => @lem5208373 x s)). Qed.
Lemma lem5208375 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208376 (s : real -> Prop) : (term721 s) = (term727 s).
Proof. exact (MK_COMB (@lem5208375) (@lem5208374 s)). Qed.
Lemma lem5208377 (s : real -> Prop) : (term720 s) = (term727 s).
Proof. exact (TRANS (@lem5208369 s) (@lem5208376 s)). Qed.
Lemma lem5208378 (s : real -> Prop) : (term226 s) = (term226 s).
Proof. exact (fun_ext (fun x : real => @lem5208367 x s)). Qed.
Lemma lem5208379 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5208380 (s : real -> Prop) : (term154 s) = (term154 s).
Proof. exact (MK_COMB (@lem5208379) (@lem5208378 s)). Qed.
Lemma lem5208381 (s : real -> Prop) : (term43 s) = (term43 s).
Proof. exact (eq_refl (term43 s)). Qed.
Lemma lem5208384 (s : real -> Prop) : (term728 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5208385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208386 (s : real -> Prop) : (term729 s) = (term730 s).
Proof. exact (MK_COMB (@lem5208385) (@lem5208377 s)). Qed.
Lemma lem5208387 (s : real -> Prop) : (term731 s) = (term732 s).
Proof. exact (MK_COMB (@lem5208386 s) (@lem5208381 s)). Qed.
Lemma lem5208388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208389 (s : real -> Prop) : (term733 s) = (term733 s).
Proof. exact (MK_COMB (@lem5208388) (@lem5208380 s)). Qed.
Lemma lem5208390 (s : real -> Prop) : (term734 s) = (term735 s).
Proof. exact (MK_COMB (@lem5208389 s) (@lem5208384 s)). Qed.
Lemma lem5208391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208392 (s : real -> Prop) : (term736 s) = (term737 s).
Proof. exact (MK_COMB (@lem5208391) (@lem5208390 s)). Qed.
Lemma lem5208393 (s : real -> Prop) : (term738 s) = (term739 s).
Proof. exact (MK_COMB (@lem5208392 s) (@lem5208387 s)). Qed.
Lemma lem5208394 (s : real -> Prop) : ((term154 s) = (term43 s)) = (term738 s).
Proof. exact (@lem17784 (term154 s) (term43 s)). Qed.
Lemma lem5208395 (s : real -> Prop) : ((term154 s) = (term43 s)) = (term739 s).
Proof. exact (TRANS (@lem5208394 s) (@lem5208393 s)). Qed.
Lemma lem5208396 : term228 = term740.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5208395 s)). Qed.
Lemma lem5208397 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5208398 : term189 = term741.
Proof. exact (MK_COMB (@lem5208397) (@lem5208396)). Qed.
Lemma lem5208400 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term671 A P Q) = (term672 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5208401 (P : type1022) (Q : type1022) : (term742 P Q) = (term743 P Q).
Proof. exact (@lem5208400 (real -> Prop) P Q). Qed.
Lemma lem5208402 : term744 = term745.
Proof. exact (@lem5208401 term746 term747). Qed.
Lemma lem5208403 (s : real -> Prop) : (term748 s) = (term735 s).
Proof. exact (eq_refl (term748 s)). Qed.
Lemma lem5208404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208405 (s : real -> Prop) : (term749 s) = (term737 s).
Proof. exact (MK_COMB (@lem5208404) (@lem5208403 s)). Qed.
Lemma lem5208406 (s : real -> Prop) : (term750 s) = (term732 s).
Proof. exact (eq_refl (term750 s)). Qed.
Lemma lem5208407 (s : real -> Prop) : (term751 s) = (term739 s).
Proof. exact (MK_COMB (@lem5208405 s) (@lem5208406 s)). Qed.
Lemma lem5208408 : term752 = term740.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5208407 s)). Qed.
Lemma lem5208409 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5208410 : term744 = term741.
Proof. exact (MK_COMB (@lem5208409) (@lem5208408)). Qed.
Lemma lem5208411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5208412 : term753 = term754.
Proof. exact (MK_COMB (@lem5208411) (@lem5208410)). Qed.
Lemma lem5208413 (s : real -> Prop) : (term748 s) = (term735 s).
Proof. exact (eq_refl (term748 s)). Qed.
Lemma lem5208414 : term755 = term746.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5208413 s)). Qed.
Lemma lem5208415 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5208416 : term756 = term757.
Proof. exact (MK_COMB (@lem5208415) (@lem5208414)). Qed.
Lemma lem5208417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208418 : term758 = term759.
Proof. exact (MK_COMB (@lem5208417) (@lem5208416)). Qed.
Lemma lem5208419 (s : real -> Prop) : (term750 s) = (term732 s).
Proof. exact (eq_refl (term750 s)). Qed.
Lemma lem5208420 : term760 = term747.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5208419 s)). Qed.
Lemma lem5208421 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5208422 : term761 = term762.
Proof. exact (MK_COMB (@lem5208421) (@lem5208420)). Qed.
Lemma lem5208423 : term745 = term763.
Proof. exact (MK_COMB (@lem5208418) (@lem5208422)). Qed.
Lemma lem5208424 : (term744 = term745) = (term741 = term763).
Proof. exact (MK_COMB (@lem5208412) (@lem5208423)). Qed.
Lemma lem5208425 : term741 = term763.
Proof. exact (EQ_MP (@lem5208424) (@lem5208402)). Qed.
Lemma lem5208531 {A : Type'} (P : A -> Prop) (Q : Prop) : (term434 A P Q) = (term435 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5208532 (P : real -> Prop) (Q : Prop) : (term436 P Q) = (term437 P Q).
Proof. exact (@lem5208531 real P Q). Qed.
Lemma lem5208533 (s : real -> Prop) : (term764 s) = (term765 s).
Proof. exact (@lem5208532 (term226 s) (s = (@EMPTY real))). Qed.
Lemma lem5208534 (x : real) (s : real -> Prop) : (term722 s x) = (@IN real x s).
Proof. exact (eq_refl (term722 s x)). Qed.
Lemma lem5208535 (s : real -> Prop) : (term766 s) = (term226 s).
Proof. exact (fun_ext (fun x : real => @lem5208534 x s)). Qed.
Lemma lem5208536 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5208537 (s : real -> Prop) : (term767 s) = (term154 s).
Proof. exact (MK_COMB (@lem5208536) (@lem5208535 s)). Qed.
Lemma lem5208538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208539 (s : real -> Prop) : (term768 s) = (term733 s).
Proof. exact (MK_COMB (@lem5208538) (@lem5208537 s)). Qed.
Lemma lem5208540 (s : real -> Prop) : (s = (@EMPTY real)) = (s = (@EMPTY real)).
Proof. exact (eq_refl (s = (@EMPTY real))). Qed.
Lemma lem5208541 (s : real -> Prop) : (term764 s) = (term735 s).
Proof. exact (MK_COMB (@lem5208539 s) (@lem5208540 s)). Qed.
Lemma lem5208542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5208543 (s : real -> Prop) : (term769 s) = (term770 s).
Proof. exact (MK_COMB (@lem5208542) (@lem5208541 s)). Qed.
Lemma lem5208544 (x : real) (s : real -> Prop) : (term722 s x) = (@IN real x s).
Proof. exact (eq_refl (term722 s x)). Qed.
Lemma lem5208545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208546 (x : real) (s : real -> Prop) : (term771 s x) = (term772 x s).
Proof. exact (MK_COMB (@lem5208545) (@lem5208544 x s)). Qed.
Lemma lem5208547 (s : real -> Prop) : (s = (@EMPTY real)) = (s = (@EMPTY real)).
Proof. exact (eq_refl (s = (@EMPTY real))). Qed.
Lemma lem5208548 (x : real) (s : real -> Prop) : (term773 x s) = (term774 x s).
Proof. exact (MK_COMB (@lem5208546 x s) (@lem5208547 s)). Qed.
Lemma lem5208549 (s : real -> Prop) : (term775 s) = (term776 s).
Proof. exact (fun_ext (fun x : real => @lem5208548 x s)). Qed.
Lemma lem5208550 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5208551 (s : real -> Prop) : (term765 s) = (term777 s).
Proof. exact (MK_COMB (@lem5208550) (@lem5208549 s)). Qed.
Lemma lem5208552 (s : real -> Prop) : ((term764 s) = (term765 s)) = ((term735 s) = (term777 s)).
Proof. exact (MK_COMB (@lem5208543 s) (@lem5208551 s)). Qed.
Lemma lem5208553 (s : real -> Prop) : (term735 s) = (term777 s).
Proof. exact (EQ_MP (@lem5208552 s) (@lem5208533 s)). Qed.
Lemma lem5208554 : term746 = term778.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5208553 s)). Qed.
Lemma lem5208555 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5208556 : term757 = term779.
Proof. exact (MK_COMB (@lem5208555) (@lem5208554)). Qed.
Lemma lem5208558 {A B : Type'} (P : type1413 A B) : (term350 A B P) = (term351 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5208559 (P : type1020) : (term780 P) = (term781 P).
Proof. exact (@lem5208558 (real -> Prop) real P). Qed.
Lemma lem5208560 : term782 = term783.
Proof. exact (@lem5208559 term784). Qed.
Lemma lem5208561 (s : real -> Prop) : (term785 s) = (term776 s).
Proof. exact (eq_refl (term785 s)). Qed.
Lemma lem5208562 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5208563 (s : real -> Prop) (x : real) : (term786 s x) = (term787 s x).
Proof. exact (MK_COMB (@lem5208561 s) (@lem5208562 x)). Qed.
Lemma lem5208564 (x : real) (s : real -> Prop) : (term787 s x) = (term774 x s).
Proof. exact (eq_refl (term787 s x)). Qed.
Lemma lem5208565 (x : real) (s : real -> Prop) : (term786 s x) = (term774 x s).
Proof. exact (TRANS (@lem5208563 s x) (@lem5208564 x s)). Qed.
Lemma lem5208566 (s : real -> Prop) : (term788 s) = (term776 s).
Proof. exact (fun_ext (fun x : real => @lem5208565 x s)). Qed.
Lemma lem5208567 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5208568 (s : real -> Prop) : (term789 s) = (term777 s).
Proof. exact (MK_COMB (@lem5208567) (@lem5208566 s)). Qed.
Lemma lem5208569 : term790 = term778.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5208568 s)). Qed.
Lemma lem5208570 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5208571 : term782 = term779.
Proof. exact (MK_COMB (@lem5208570) (@lem5208569)). Qed.
Lemma lem5208572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5208573 : term791 = term792.
Proof. exact (MK_COMB (@lem5208572) (@lem5208571)). Qed.
Lemma lem5208574 (s : real -> Prop) : (term785 s) = (term776 s).
Proof. exact (eq_refl (term785 s)). Qed.
Lemma lem5208575 (x : type1023) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5208576 (x : type1023) (s : real -> Prop) : (term793 x s) = (term794 x s).
Proof. exact (MK_COMB (@lem5208574 s) (@lem5208575 x s)). Qed.
Lemma lem5208577 (x : type1023) (s : real -> Prop) : (term794 x s) = (term795 x s).
Proof. exact (eq_refl (term794 x s)). Qed.
Lemma lem5208578 (x : type1023) (s : real -> Prop) : (term793 x s) = (term795 x s).
Proof. exact (TRANS (@lem5208576 x s) (@lem5208577 x s)). Qed.
Lemma lem5208579 (x : type1023) : (term796 x) = (term797 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5208578 x s)). Qed.
Lemma lem5208580 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5208581 (x : type1023) : (term798 x) = (term799 x).
Proof. exact (MK_COMB (@lem5208580) (@lem5208579 x)). Qed.
Lemma lem5208582 : term800 = term801.
Proof. exact (fun_ext (fun x : type1023 => @lem5208581 x)). Qed.
Lemma lem5208583 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5208584 : term783 = term802.
Proof. exact (MK_COMB (@lem5208583) (@lem5208582)). Qed.
Lemma lem5208585 : (term782 = term783) = (term779 = term802).
Proof. exact (MK_COMB (@lem5208573) (@lem5208584)). Qed.
Lemma lem5208586 : term779 = term802.
Proof. exact (EQ_MP (@lem5208585) (@lem5208560)). Qed.
Lemma lem5208587 : term757 = term802.
Proof. exact (TRANS (@lem5208556) (@lem5208586)). Qed.
Lemma lem5208588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208589 : term759 = term803.
Proof. exact (MK_COMB (@lem5208588) (@lem5208587)). Qed.
Lemma lem5208590 : term762 = term762.
Proof. exact (eq_refl term762). Qed.
Lemma lem5208591 : term763 = term804.
Proof. exact (MK_COMB (@lem5208589) (@lem5208590)). Qed.
Lemma lem5208593 {A : Type'} (P : A -> Prop) (Q : Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5208594 (P : type257) (Q : Prop) : (term805 P Q) = (term806 P Q).
Proof. exact (@lem5208593 type1023 P Q). Qed.
Lemma lem5208595 : term807 = term808.
Proof. exact (@lem5208594 term801 term762). Qed.
Lemma lem5208596 (x : type1023) : (term809 x) = (term799 x).
Proof. exact (eq_refl (term809 x)). Qed.
Lemma lem5208597 : term810 = term801.
Proof. exact (fun_ext (fun x : type1023 => @lem5208596 x)). Qed.
Lemma lem5208598 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5208599 : term811 = term802.
Proof. exact (MK_COMB (@lem5208598) (@lem5208597)). Qed.
Lemma lem5208600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208601 : term812 = term803.
Proof. exact (MK_COMB (@lem5208600) (@lem5208599)). Qed.
Lemma lem5208602 : term762 = term762.
Proof. exact (eq_refl term762). Qed.
Lemma lem5208603 : term807 = term804.
Proof. exact (MK_COMB (@lem5208601) (@lem5208602)). Qed.
Lemma lem5208604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5208605 : term813 = term814.
Proof. exact (MK_COMB (@lem5208604) (@lem5208603)). Qed.
Lemma lem5208606 (x : type1023) : (term809 x) = (term799 x).
Proof. exact (eq_refl (term809 x)). Qed.
Lemma lem5208607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208608 (x : type1023) : (term815 x) = (term816 x).
Proof. exact (MK_COMB (@lem5208607) (@lem5208606 x)). Qed.
Lemma lem5208609 : term762 = term762.
Proof. exact (eq_refl term762). Qed.
Lemma lem5208610 (x : type1023) : (term817 x) = (term818 x).
Proof. exact (MK_COMB (@lem5208608 x) (@lem5208609)). Qed.
Lemma lem5208611 : term819 = term820.
Proof. exact (fun_ext (fun x : type1023 => @lem5208610 x)). Qed.
Lemma lem5208612 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5208613 : term808 = term821.
Proof. exact (MK_COMB (@lem5208612) (@lem5208611)). Qed.
Lemma lem5208614 : (term807 = term808) = (term804 = term821).
Proof. exact (MK_COMB (@lem5208605) (@lem5208613)). Qed.
Lemma lem5208615 : term804 = term821.
Proof. exact (EQ_MP (@lem5208614) (@lem5208595)). Qed.
Lemma lem5208616 : term763 = term821.
Proof. exact (TRANS (@lem5208591) (@lem5208615)). Qed.
Lemma lem5208617 : term741 = term821.
Proof. exact (TRANS (@lem5208425) (@lem5208616)). Qed.
Lemma lem5208618 : term189 = term821.
Proof. exact (TRANS (@lem5208398) (@lem5208617)). Qed.
Lemma lem5208619 (h1 : term189) : term821.
Proof. exact (EQ_MP (@lem5208618) (@lem5206752 h1)). Qed.
Lemma lem5208620 (x : real) : ((term25 x) = x) = ((term25 x) = x).
Proof. exact (eq_refl ((term25 x) = x)). Qed.
Lemma lem5208621 : term225 = term225.
Proof. exact (fun_ext (fun x : real => @lem5208620 x)). Qed.
Lemma lem5208622 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208631 : term196 = term196.
Proof. exact (MK_COMB (@lem5208622) (@lem5208621)). Qed.
Lemma lem5208632 (h1 : term196) : term196.
Proof. exact (EQ_MP (@lem5208631) (@lem5206753 h1)). Qed.
Lemma lem5208633 (x : type1023) (h1 : term818 x) : term818 x.
Proof. exact (h1). Qed.
Lemma lem5208634 (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term663 x' s a) : term663 x' s a.
Proof. exact (h1). Qed.
Lemma lem5208635 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term661 x'' x' s a) : term661 x'' x' s a.
Proof. exact (h1). Qed.
Lemma lem5208636 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term658 x'' x' s a b') : term658 x'' x' s a b'.
Proof. exact (h1). Qed.
Lemma lem5208644 (s : real -> Prop) (h1 : term43 s) : term43 s.
Proof. exact (h1). Qed.
Lemma lem5208659 (s : real -> Prop) (b : real) (x : real) : (term231 s b x) = (term231 s b x).
Proof. exact (eq_refl (term231 s b x)). Qed.
Lemma lem5208660 (s : real -> Prop) (b : real) : (term232 s b) = (term232 s b).
Proof. exact (fun_ext (fun x : real => @lem5208659 s b x)). Qed.
Lemma lem5208661 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208662 (s : real -> Prop) (b : real) : (term233 s b) = (term233 s b).
Proof. exact (MK_COMB (@lem5208661) (@lem5208660 s b)). Qed.
Lemma lem5208663 (s : real -> Prop) (b : real) (h1 : term44 s b) : term233 s b.
Proof. exact (EQ_MP (@lem5208662 s b) (@lem5206822 s b h1)). Qed.
Lemma lem5208675 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5208680 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem5208681 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5208682 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5208687 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208688 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208687 real real f x). Qed.
Lemma lem5208690 (x : real) : (real_neg x) = (@I (real -> real) real_neg x).
Proof. exact (@lem5208688 real_neg x). Qed.
Lemma lem5208695 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208696 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208695 real real f x). Qed.
Lemma lem5208698 (y : real) : (real_neg y) = (@I (real -> real) real_neg y).
Proof. exact (@lem5208696 real_neg y). Qed.
Lemma lem5208699 (x : real) : (term94 x) = (term822 x).
Proof. exact (MK_COMB (@lem5208682) (@lem5208690 x)). Qed.
Lemma lem5208700 (x : real) (y : real) : (term28 x y) = (term823 x y).
Proof. exact (MK_COMB (@lem5208699 x) (@lem5208698 y)). Qed.
Lemma lem5208701 (x : real) (y : real) : (term824 x y) = (term825 x y).
Proof. exact (MK_COMB (@lem5208681) (@lem5208700 x y)). Qed.
Lemma lem5208702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208703 (x : real) (y : real) : (term826 x y) = (term827 x y).
Proof. exact (MK_COMB (@lem5208702) (@lem5208701 x y)). Qed.
Lemma lem5208704 (y : real) (x : real) : (term684 y x) = (term828 y x).
Proof. exact (MK_COMB (@lem5208703 x y) (@lem5208680 y x)). Qed.
Lemma lem5208705 (x : real) : (term678 x) = (term829 x).
Proof. exact (fun_ext (fun y : real => @lem5208704 y x)). Qed.
Lemma lem5208706 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208707 (x : real) : (term696 x) = (term830 x).
Proof. exact (MK_COMB (@lem5208706) (@lem5208705 x)). Qed.
Lemma lem5208708 : term703 = term831.
Proof. exact (fun_ext (fun x : real => @lem5208707 x)). Qed.
Lemma lem5208709 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208710 : term718 = term832.
Proof. exact (MK_COMB (@lem5208709) (@lem5208708)). Qed.
Lemma lem5208717 (y : real) (x : real) : (term252 y x) = (term252 y x).
Proof. exact (eq_refl (term252 y x)). Qed.
Lemma lem5208718 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5208723 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208724 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208723 real real f x). Qed.
Lemma lem5208726 (x : real) : (real_neg x) = (@I (real -> real) real_neg x).
Proof. exact (@lem5208724 real_neg x). Qed.
Lemma lem5208731 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208732 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208731 real real f x). Qed.
Lemma lem5208734 (y : real) : (real_neg y) = (@I (real -> real) real_neg y).
Proof. exact (@lem5208732 real_neg y). Qed.
Lemma lem5208735 (x : real) : (term94 x) = (term822 x).
Proof. exact (MK_COMB (@lem5208718) (@lem5208726 x)). Qed.
Lemma lem5208736 (x : real) (y : real) : (term28 x y) = (term823 x y).
Proof. exact (MK_COMB (@lem5208735 x) (@lem5208734 y)). Qed.
Lemma lem5208737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208738 (x : real) (y : real) : (term833 x y) = (term834 x y).
Proof. exact (MK_COMB (@lem5208737) (@lem5208736 x y)). Qed.
Lemma lem5208739 (y : real) (x : real) : (term680 y x) = (term835 y x).
Proof. exact (MK_COMB (@lem5208738 x y) (@lem5208717 y x)). Qed.
Lemma lem5208740 (x : real) : (term677 x) = (term836 x).
Proof. exact (fun_ext (fun y : real => @lem5208739 y x)). Qed.
Lemma lem5208741 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208742 (x : real) : (term691 x) = (term837 x).
Proof. exact (MK_COMB (@lem5208741) (@lem5208740 x)). Qed.
Lemma lem5208743 : term702 = term838.
Proof. exact (fun_ext (fun x : real => @lem5208742 x)). Qed.
Lemma lem5208744 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208745 : term713 = term839.
Proof. exact (MK_COMB (@lem5208744) (@lem5208743)). Qed.
Lemma lem5208746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208747 : term715 = term840.
Proof. exact (MK_COMB (@lem5208746) (@lem5208745)). Qed.
Lemma lem5208748 : term719 = term841.
Proof. exact (MK_COMB (@lem5208747) (@lem5208710)). Qed.
Lemma lem5208749 (h1 : term35) : term841.
Proof. exact (EQ_MP (@lem5208748) (@lem5208365 h1)). Qed.
Lemma lem5208750 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5208751 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5208756 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208757 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208756 real real f x). Qed.
Lemma lem5208759 (x : real) : (real_neg x) = (@I (real -> real) real_neg x).
Proof. exact (@lem5208757 real_neg x). Qed.
Lemma lem5208760 (x : real) : (term25 x) = (term842 x).
Proof. exact (MK_COMB (@lem5208751) (@lem5208759 x)). Qed.
Lemma lem5208762 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208763 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208762 real real f x). Qed.
Lemma lem5208764 (x : real) : (term842 x) = (term843 x).
Proof. exact (@lem5208763 real_neg (@I (real -> real) real_neg x)). Qed.
Lemma lem5208765 (x : real) : (term25 x) = (term843 x).
Proof. exact (TRANS (@lem5208760 x) (@lem5208764 x)). Qed.
Lemma lem5208766 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5208767 (x : real) : (term844 x) = (term845 x).
Proof. exact (MK_COMB (@lem5208750) (@lem5208765 x)). Qed.
Lemma lem5208768 (x : real) : ((term25 x) = x) = ((term843 x) = x).
Proof. exact (MK_COMB (@lem5208767 x) (@lem5208766 x)). Qed.
Lemma lem5208769 : term225 = term846.
Proof. exact (fun_ext (fun x : real => @lem5208768 x)). Qed.
Lemma lem5208770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208771 : term196 = term847.
Proof. exact (MK_COMB (@lem5208770) (@lem5208769)). Qed.
Lemma lem5208772 (h1 : term196) : term847.
Proof. exact (EQ_MP (@lem5208771) (@lem5208632 h1)). Qed.
Lemma lem5208779 (s : real -> Prop) : (term43 s) = (term43 s).
Proof. exact (eq_refl (term43 s)). Qed.
Lemma lem5208786 (x : real) (s : real -> Prop) : (term724 x s) = (term724 x s).
Proof. exact (eq_refl (term724 x s)). Qed.
Lemma lem5208787 (s : real -> Prop) : (term726 s) = (term726 s).
Proof. exact (fun_ext (fun x : real => @lem5208786 x s)). Qed.
Lemma lem5208788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208789 (s : real -> Prop) : (term727 s) = (term727 s).
Proof. exact (MK_COMB (@lem5208788) (@lem5208787 s)). Qed.
Lemma lem5208790 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208791 (s : real -> Prop) : (term730 s) = (term730 s).
Proof. exact (MK_COMB (@lem5208790) (@lem5208789 s)). Qed.
Lemma lem5208792 (s : real -> Prop) : (term732 s) = (term732 s).
Proof. exact (MK_COMB (@lem5208791 s) (@lem5208779 s)). Qed.
Lemma lem5208793 : term747 = term747.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5208792 s)). Qed.
Lemma lem5208794 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5208795 : term762 = term762.
Proof. exact (MK_COMB (@lem5208794) (@lem5208793)). Qed.
Lemma lem5208810 (x : type1023) (s : real -> Prop) : (term795 x s) = (term795 x s).
Proof. exact (eq_refl (term795 x s)). Qed.
Lemma lem5208811 (x : type1023) : (term797 x) = (term797 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5208810 x s)). Qed.
Lemma lem5208812 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5208813 (x : type1023) : (term799 x) = (term799 x).
Proof. exact (MK_COMB (@lem5208812) (@lem5208811 x)). Qed.
Lemma lem5208814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208815 (x : type1023) : (term816 x) = (term816 x).
Proof. exact (MK_COMB (@lem5208814) (@lem5208813 x)). Qed.
Lemma lem5208816 (x : type1023) : (term818 x) = (term818 x).
Proof. exact (MK_COMB (@lem5208815 x) (@lem5208795)). Qed.
Lemma lem5208817 (x : type1023) (h1 : term818 x) : term818 x.
Proof. exact (EQ_MP (@lem5208816 x) (@lem5208633 x h1)). Qed.
Lemma lem5208818 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5208825 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208826 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208825 real real f x). Qed.
Lemma lem5208828 (b' : real) : (real_neg b') = (@I (real -> real) real_neg b').
Proof. exact (@lem5208826 real_neg b'). Qed.
Lemma lem5208829 (a : real) : (real_le a) = (real_le a).
Proof. exact (eq_refl (real_le a)). Qed.
Lemma lem5208830 (a : real) (b' : real) : (term148 a b') = (term848 a b').
Proof. exact (MK_COMB (@lem5208829 a) (@lem5208828 b')). Qed.
Lemma lem5208831 (a : real) (b' : real) : (term307 a b') = (term849 a b').
Proof. exact (MK_COMB (@lem5208818) (@lem5208830 a b')). Qed.
Lemma lem5208832 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5208837 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208838 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208837 real real f x). Qed.
Lemma lem5208840 (x : real) : (real_neg x) = (@I (real -> real) real_neg x).
Proof. exact (@lem5208838 real_neg x). Qed.
Lemma lem5208845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208846 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208845 real real f x). Qed.
Lemma lem5208848 (b' : real) : (real_neg b') = (@I (real -> real) real_neg b').
Proof. exact (@lem5208846 real_neg b'). Qed.
Lemma lem5208849 (x : real) : (term94 x) = (term822 x).
Proof. exact (MK_COMB (@lem5208832) (@lem5208840 x)). Qed.
Lemma lem5208850 (x : real) (b' : real) : (term28 x b') = (term823 x b').
Proof. exact (MK_COMB (@lem5208849 x) (@lem5208848 b')). Qed.
Lemma lem5208859 (x : real) (s : real -> Prop) : (term850 x s) = (term850 x s).
Proof. exact (eq_refl (term850 x s)). Qed.
Lemma lem5208860 (s : real -> Prop) (x : real) (b' : real) : (term304 s x b') = (term851 s x b').
Proof. exact (MK_COMB (@lem5208859 x s) (@lem5208850 x b')). Qed.
Lemma lem5208861 (s : real -> Prop) (b' : real) : (term305 s b') = (term852 s b').
Proof. exact (fun_ext (fun x : real => @lem5208860 s x b')). Qed.
Lemma lem5208862 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208863 (s : real -> Prop) (b' : real) : (term306 s b') = (term853 s b').
Proof. exact (MK_COMB (@lem5208862) (@lem5208861 s b')). Qed.
Lemma lem5208864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208865 (s : real -> Prop) (b' : real) : (term308 s b') = (term854 s b').
Proof. exact (MK_COMB (@lem5208864) (@lem5208863 s b')). Qed.
Lemma lem5208866 (s : real -> Prop) (a : real) (b' : real) : (term310 s a b') = (term855 s a b').
Proof. exact (MK_COMB (@lem5208865 s b') (@lem5208831 a b')). Qed.
Lemma lem5208867 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5208868 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5208873 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208874 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208873 real real f x). Qed.
Lemma lem5208876 (b' : real) : (real_neg b') = (@I (real -> real) real_neg b').
Proof. exact (@lem5208874 real_neg b'). Qed.
Lemma lem5208877 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5208878 (b' : real) : (term94 b') = (term822 b').
Proof. exact (MK_COMB (@lem5208868) (@lem5208876 b')). Qed.
Lemma lem5208879 (b' : real) (a : real) : (term143 b' a) = (term856 b' a).
Proof. exact (MK_COMB (@lem5208878 b') (@lem5208877 a)). Qed.
Lemma lem5208880 (b' : real) (a : real) : (term857 b' a) = (term858 b' a).
Proof. exact (MK_COMB (@lem5208867) (@lem5208879 b' a)). Qed.
Lemma lem5208887 (b' : real) (s : real -> Prop) : (term859 b' s) = (term859 b' s).
Proof. exact (eq_refl (term859 b' s)). Qed.
Lemma lem5208888 (s : real -> Prop) (b' : real) (a : real) : (term296 s b' a) = (term860 s b' a).
Proof. exact (MK_COMB (@lem5208887 b' s) (@lem5208880 b' a)). Qed.
Lemma lem5208889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208890 (s : real -> Prop) (b' : real) (a : real) : (term606 s b' a) = (term861 s b' a).
Proof. exact (MK_COMB (@lem5208889) (@lem5208888 s b' a)). Qed.
Lemma lem5208891 (s : real -> Prop) (a : real) (b' : real) : (term608 s a b') = (term862 s a b').
Proof. exact (MK_COMB (@lem5208890 s b' a) (@lem5208866 s a b')). Qed.
Lemma lem5208896 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5208905 (x' : real -> real) (b : real) : (term863 x' b) = (term863 x' b).
Proof. exact (eq_refl (term863 x' b)). Qed.
Lemma lem5208912 (x'' : real -> real) (b : real) (s : real -> Prop) : (term864 x'' b s) = (term864 x'' b s).
Proof. exact (eq_refl (term864 x'' b s)). Qed.
Lemma lem5208923 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208924 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208923 real real f x). Qed.
Lemma lem5208926 (x'' : real -> real) (b : real) : (term865 x'' b) = (term866 x'' b).
Proof. exact (@lem5208924 real_neg (x'' b)). Qed.
Lemma lem5208927 (x' : real -> real) (b : real) : (term867 x' b) = (term867 x' b).
Proof. exact (eq_refl (term867 x' b)). Qed.
Lemma lem5208928 (x' : real -> real) (x'' : real -> real) (b : real) : ((x' b) = (term865 x'' b)) = ((x' b) = (term866 x'' b)).
Proof. exact (MK_COMB (@lem5208927 x' b) (@lem5208926 x'' b)). Qed.
Lemma lem5208929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208930 (x' : real -> real) (x'' : real -> real) (b : real) : (term868 x' x'' b) = (term869 x' x'' b).
Proof. exact (MK_COMB (@lem5208929) (@lem5208928 x' x'' b)). Qed.
Lemma lem5208931 (x' : real -> real) (x'' : real -> real) (b : real) (s : real -> Prop) : (term870 x' x'' b s) = (term871 x' x'' b s).
Proof. exact (MK_COMB (@lem5208930 x' x'' b) (@lem5208912 x'' b s)). Qed.
Lemma lem5208932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208933 (x' : real -> real) (x'' : real -> real) (b : real) (s : real -> Prop) : (term872 x' x'' b s) = (term873 x' x'' b s).
Proof. exact (MK_COMB (@lem5208932) (@lem5208931 x' x'' b s)). Qed.
Lemma lem5208934 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (b : real) : (term390 x'' s x' b) = (term874 x'' s x' b).
Proof. exact (MK_COMB (@lem5208933 x' x'' b s) (@lem5208905 x' b)). Qed.
Lemma lem5208935 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208936 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (b : real) : (term875 x'' s x' b) = (term876 x'' s x' b).
Proof. exact (MK_COMB (@lem5208935) (@lem5208934 x'' s x' b)). Qed.
Lemma lem5208937 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (b : real) : (term507 x'' s x' a b) = (term877 x'' s x' a b).
Proof. exact (MK_COMB (@lem5208936 x'' s x' b) (@lem5208896 a b)). Qed.
Lemma lem5208938 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) : (term509 x'' s x' a) = (term878 x'' s x' a).
Proof. exact (fun_ext (fun b : real => @lem5208937 x'' s x' a b)). Qed.
Lemma lem5208939 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208940 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) : (term511 x'' s x' a) = (term879 x'' s x' a).
Proof. exact (MK_COMB (@lem5208939) (@lem5208938 x'' s x' a)). Qed.
Lemma lem5208945 (x : real) (a : real) : (real_le x a) = (real_le x a).
Proof. exact (eq_refl (real_le x a)). Qed.
Lemma lem5208952 (x' : real) (s : real -> Prop) : (term724 x' s) = (term724 x' s).
Proof. exact (eq_refl (term724 x' s)). Qed.
Lemma lem5208953 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5208960 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5208961 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5208960 real real f x). Qed.
Lemma lem5208963 (x' : real) : (real_neg x') = (@I (real -> real) real_neg x').
Proof. exact (@lem5208961 real_neg x'). Qed.
Lemma lem5208964 (x : real) : (@eq real x) = (@eq real x).
Proof. exact (eq_refl (@eq real x)). Qed.
Lemma lem5208965 (x : real) (x' : real) : (x = (real_neg x')) = (x = (@I (real -> real) real_neg x')).
Proof. exact (MK_COMB (@lem5208964 x) (@lem5208963 x')). Qed.
Lemma lem5208966 (x : real) (x' : real) : (term880 x x') = (term881 x x').
Proof. exact (MK_COMB (@lem5208953) (@lem5208965 x x')). Qed.
Lemma lem5208967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208968 (x : real) (x' : real) : (term882 x x') = (term883 x x').
Proof. exact (MK_COMB (@lem5208967) (@lem5208966 x x')). Qed.
Lemma lem5208969 (x : real) (x' : real) (s : real -> Prop) : (term235 x x' s) = (term884 x x' s).
Proof. exact (MK_COMB (@lem5208968 x x') (@lem5208952 x' s)). Qed.
Lemma lem5208970 (x : real) (s : real -> Prop) : (term243 x s) = (term885 x s).
Proof. exact (fun_ext (fun x' : real => @lem5208969 x x' s)). Qed.
Lemma lem5208971 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208972 (x : real) (s : real -> Prop) : (term244 x s) = (term886 x s).
Proof. exact (MK_COMB (@lem5208971) (@lem5208970 x s)). Qed.
Lemma lem5208973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5208974 (x : real) (s : real -> Prop) : (term278 x s) = (term887 x s).
Proof. exact (MK_COMB (@lem5208973) (@lem5208972 x s)). Qed.
Lemma lem5208975 (s : real -> Prop) (x : real) (a : real) : (term280 s x a) = (term888 s x a).
Proof. exact (MK_COMB (@lem5208974 x s) (@lem5208945 x a)). Qed.
Lemma lem5208976 (s : real -> Prop) (a : real) : (term281 s a) = (term889 s a).
Proof. exact (fun_ext (fun x : real => @lem5208975 s x a)). Qed.
Lemma lem5208977 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5208978 (s : real -> Prop) (a : real) : (term282 s a) = (term890 s a).
Proof. exact (MK_COMB (@lem5208977) (@lem5208976 s a)). Qed.
Lemma lem5208979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5208980 (s : real -> Prop) (a : real) : (term289 s a) = (term891 s a).
Proof. exact (MK_COMB (@lem5208979) (@lem5208978 s a)). Qed.
Lemma lem5208981 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) : (term542 x'' s x' a) = (term892 x'' s x' a).
Proof. exact (MK_COMB (@lem5208980 s a) (@lem5208940 x'' s x' a)). Qed.
Lemma lem5208990 (x' : real -> real) (b : real) : (term863 x' b) = (term863 x' b).
Proof. exact (eq_refl (term863 x' b)). Qed.
Lemma lem5208997 (x'' : real -> real) (b : real) (s : real -> Prop) : (term864 x'' b s) = (term864 x'' b s).
Proof. exact (eq_refl (term864 x'' b s)). Qed.
Lemma lem5209008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5209009 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5209008 real real f x). Qed.
Lemma lem5209011 (x'' : real -> real) (b : real) : (term865 x'' b) = (term866 x'' b).
Proof. exact (@lem5209009 real_neg (x'' b)). Qed.
Lemma lem5209012 (x' : real -> real) (b : real) : (term867 x' b) = (term867 x' b).
Proof. exact (eq_refl (term867 x' b)). Qed.
Lemma lem5209013 (x' : real -> real) (x'' : real -> real) (b : real) : ((x' b) = (term865 x'' b)) = ((x' b) = (term866 x'' b)).
Proof. exact (MK_COMB (@lem5209012 x' b) (@lem5209011 x'' b)). Qed.
Lemma lem5209014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5209015 (x' : real -> real) (x'' : real -> real) (b : real) : (term868 x' x'' b) = (term869 x' x'' b).
Proof. exact (MK_COMB (@lem5209014) (@lem5209013 x' x'' b)). Qed.
Lemma lem5209016 (x' : real -> real) (x'' : real -> real) (b : real) (s : real -> Prop) : (term870 x' x'' b s) = (term871 x' x'' b s).
Proof. exact (MK_COMB (@lem5209015 x' x'' b) (@lem5208997 x'' b s)). Qed.
Lemma lem5209017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5209018 (x' : real -> real) (x'' : real -> real) (b : real) (s : real -> Prop) : (term872 x' x'' b s) = (term873 x' x'' b s).
Proof. exact (MK_COMB (@lem5209017) (@lem5209016 x' x'' b s)). Qed.
Lemma lem5209019 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (b : real) : (term390 x'' s x' b) = (term874 x'' s x' b).
Proof. exact (MK_COMB (@lem5209018 x' x'' b s) (@lem5208990 x' b)). Qed.
Lemma lem5209020 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) : (term392 x'' s x') = (term893 x'' s x').
Proof. exact (fun_ext (fun b : real => @lem5209019 x'' s x' b)). Qed.
Lemma lem5209021 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209022 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) : (term394 x'' s x') = (term894 x'' s x').
Proof. exact (MK_COMB (@lem5209021) (@lem5209020 x'' s x')). Qed.
Lemma lem5209029 (x' : real) (s : real -> Prop) : (term724 x' s) = (term724 x' s).
Proof. exact (eq_refl (term724 x' s)). Qed.
Lemma lem5209030 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5209037 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5209038 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem5209037 real real f x). Qed.
Lemma lem5209040 (x' : real) : (real_neg x') = (@I (real -> real) real_neg x').
Proof. exact (@lem5209038 real_neg x'). Qed.
Lemma lem5209041 (x : real) : (@eq real x) = (@eq real x).
Proof. exact (eq_refl (@eq real x)). Qed.
Lemma lem5209042 (x : real) (x' : real) : (x = (real_neg x')) = (x = (@I (real -> real) real_neg x')).
Proof. exact (MK_COMB (@lem5209041 x) (@lem5209040 x')). Qed.
Lemma lem5209043 (x : real) (x' : real) : (term880 x x') = (term881 x x').
Proof. exact (MK_COMB (@lem5209030) (@lem5209042 x x')). Qed.
Lemma lem5209044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5209045 (x : real) (x' : real) : (term882 x x') = (term883 x x').
Proof. exact (MK_COMB (@lem5209044) (@lem5209043 x x')). Qed.
Lemma lem5209046 (x : real) (x' : real) (s : real -> Prop) : (term235 x x' s) = (term884 x x' s).
Proof. exact (MK_COMB (@lem5209045 x x') (@lem5209029 x' s)). Qed.
Lemma lem5209047 (x : real) (s : real -> Prop) : (term243 x s) = (term885 x s).
Proof. exact (fun_ext (fun x' : real => @lem5209046 x x' s)). Qed.
Lemma lem5209048 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209049 (x : real) (s : real -> Prop) : (term244 x s) = (term886 x s).
Proof. exact (MK_COMB (@lem5209048) (@lem5209047 x s)). Qed.
Lemma lem5209050 (s : real -> Prop) : (term250 s) = (term895 s).
Proof. exact (fun_ext (fun x : real => @lem5209049 x s)). Qed.
Lemma lem5209051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209052 (s : real -> Prop) : (term251 s) = (term896 s).
Proof. exact (MK_COMB (@lem5209051) (@lem5209050 s)). Qed.
Lemma lem5209053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5209054 (s : real -> Prop) : (term273 s) = (term897 s).
Proof. exact (MK_COMB (@lem5209053) (@lem5209052 s)). Qed.
Lemma lem5209055 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) : (term425 x'' s x') = (term898 x'' s x').
Proof. exact (MK_COMB (@lem5209054 s) (@lem5209022 x'' s x')). Qed.
Lemma lem5209056 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5209057 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) : (term583 x'' s x') = (term899 x'' s x').
Proof. exact (MK_COMB (@lem5209056) (@lem5209055 x'' s x')). Qed.
Lemma lem5209058 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) : (term585 x'' s x' a) = (term900 x'' s x' a).
Proof. exact (MK_COMB (@lem5209057 x'' s x') (@lem5208981 x'' s x' a)). Qed.
Lemma lem5209059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5209060 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) : (term642 x'' s x' a) = (term901 x'' s x' a).
Proof. exact (MK_COMB (@lem5209059) (@lem5209058 x'' s x' a)). Qed.
Lemma lem5209061 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) : (term658 x'' x' s a b') = (term902 x'' x' s a b').
Proof. exact (MK_COMB (@lem5209060 x'' s x' a) (@lem5208891 s a b')). Qed.
Lemma lem5209062 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term658 x'' x' s a b') : term902 x'' x' s a b'.
Proof. exact (EQ_MP (@lem5209061 x'' x' s a b') (@lem5208636 x'' x' s a b' h1)). Qed.
Lemma lem5209063 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term658 x'' x' s a b') : term862 s a b'.
Proof. exact (proj2 (@lem5209062 x'' x' s a b' h1)). Qed.
Lemma lem5209064 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term658 x'' x' s a b') : term900 x'' s x' a.
Proof. exact (proj1 (@lem5209062 x'' x' s a b' h1)). Qed.
Lemma lem5209066 (x : type1023) (h1 : term818 x) : term799 x.
Proof. exact (proj1 (@lem5208817 x h1)). Qed.
Lemma lem5209068 (h1 : term35) : term839.
Proof. exact (proj1 (@lem5208749 h1)). Qed.
Lemma lem5209069 (s : real -> Prop) (b' : real) (a : real) (h1 : term860 s b' a) : term860 s b' a.
Proof. exact (h1). Qed.
Lemma lem5209070 (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term855 s a b'.
Proof. exact (h1). Qed.
Lemma lem5209073 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term898 x'' s x') : term898 x'' s x'.
Proof. exact (h1). Qed.
Lemma lem5209074 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term892 x'' s x' a.
Proof. exact (h1). Qed.
Lemma lem5209075 (s : real -> Prop) (h1 : term896 s) : term896 s.
Proof. exact (h1). Qed.
Lemma lem5209076 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term894 x'' s x'.
Proof. exact (h1). Qed.
Lemma lem5209078 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term890 s a.
Proof. exact (proj1 (@lem5209074 x'' s x' a h1)). Qed.
Lemma lem5209080 (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term853 s b'.
Proof. exact (proj1 (@lem5209070 s a b' h1)). Qed.
Lemma lem5209081 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term898 x'' s x') : term898 x'' s x'.
Proof. exact (h1). Qed.
Lemma lem5209082 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term892 x'' s x' a.
Proof. exact (h1). Qed.
Lemma lem5209083 (s : real -> Prop) (h1 : term896 s) : term896 s.
Proof. exact (h1). Qed.
Lemma lem5209084 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term894 x'' s x'.
Proof. exact (h1). Qed.
Lemma lem5209085 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term879 x'' s x' a.
Proof. exact (proj2 (@lem5209082 x'' s x' a h1)). Qed.
Lemma lem5209109 (x : real) : ((term843 x) = x) = ((term843 x) = x).
Proof. exact (eq_refl ((term843 x) = x)). Qed.
Lemma lem5209110 : term846 = term846.
Proof. exact (fun_ext (fun x : real => @lem5209109 x)). Qed.
Lemma lem5209111 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209113 : term847 = term847.
Proof. exact (MK_COMB (@lem5209111) (@lem5209110)). Qed.
Lemma lem5209114 (h1 : term196) : term847.
Proof. exact (EQ_MP (@lem5209113) (@lem5208772 h1)). Qed.
Lemma lem5209217 (x : real) (x' : real) (s : real -> Prop) : (term884 x x' s) = (term884 x x' s).
Proof. exact (eq_refl (term884 x x' s)). Qed.
Lemma lem5209218 (x : real) (s : real -> Prop) : (term885 x s) = (term885 x s).
Proof. exact (fun_ext (fun x' : real => @lem5209217 x x' s)). Qed.
Lemma lem5209219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209220 (x : real) (s : real -> Prop) : (term886 x s) = (term886 x s).
Proof. exact (MK_COMB (@lem5209219) (@lem5209218 x s)). Qed.
Lemma lem5209221 (s : real -> Prop) : (term895 s) = (term895 s).
Proof. exact (fun_ext (fun x : real => @lem5209220 x s)). Qed.
Lemma lem5209222 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209224 (s : real -> Prop) : (term896 s) = (term896 s).
Proof. exact (MK_COMB (@lem5209222) (@lem5209221 s)). Qed.
Lemma lem5209225 (s : real -> Prop) (h1 : term896 s) : term896 s.
Proof. exact (EQ_MP (@lem5209224 s) (@lem5209075 s h1)). Qed.
Lemma lem5209237 (s : real -> Prop) (b : real) (x : real) : (term231 s b x) = (term231 s b x).
Proof. exact (eq_refl (term231 s b x)). Qed.
Lemma lem5209238 (s : real -> Prop) (b : real) : (term232 s b) = (term232 s b).
Proof. exact (fun_ext (fun x : real => @lem5209237 s b x)). Qed.
Lemma lem5209239 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209241 (s : real -> Prop) (b : real) : (term233 s b) = (term233 s b).
Proof. exact (MK_COMB (@lem5209239) (@lem5209238 s b)). Qed.
Lemma lem5209242 (s : real -> Prop) (b : real) (h1 : term44 s b) : term233 s b.
Proof. exact (EQ_MP (@lem5209241 s b) (@lem5208663 s b h1)). Qed.
Lemma lem5209316 (y : real) (x : real) : (term835 y x) = (term835 y x).
Proof. exact (eq_refl (term835 y x)). Qed.
Lemma lem5209317 (x : real) : (term836 x) = (term836 x).
Proof. exact (fun_ext (fun y : real => @lem5209316 y x)). Qed.
Lemma lem5209318 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209319 (x : real) : (term837 x) = (term837 x).
Proof. exact (MK_COMB (@lem5209318) (@lem5209317 x)). Qed.
Lemma lem5209320 : term838 = term838.
Proof. exact (fun_ext (fun x : real => @lem5209319 x)). Qed.
Lemma lem5209321 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209323 : term839 = term839.
Proof. exact (MK_COMB (@lem5209321) (@lem5209320)). Qed.
Lemma lem5209324 (h1 : term35) : term839.
Proof. exact (EQ_MP (@lem5209323) (@lem5209068 h1)). Qed.
Lemma lem5209358 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (b : real) : (term874 x'' s x' b) = (term874 x'' s x' b).
Proof. exact (eq_refl (term874 x'' s x' b)). Qed.
Lemma lem5209359 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) : (term893 x'' s x') = (term893 x'' s x').
Proof. exact (fun_ext (fun b : real => @lem5209358 x'' s x' b)). Qed.
Lemma lem5209360 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209362 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) : (term894 x'' s x') = (term894 x'' s x').
Proof. exact (MK_COMB (@lem5209360) (@lem5209359 x'' s x')). Qed.
Lemma lem5209363 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term894 x'' s x'.
Proof. exact (EQ_MP (@lem5209362 x'' s x') (@lem5209076 x'' s x' h1)). Qed.
Lemma lem5209384 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5209488 {A : Type'} (P : A -> Prop) (Q : Prop) : (term903 A P Q) = (term904 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5209489 (P : real -> Prop) (Q : Prop) : (term905 P Q) = (term906 P Q).
Proof. exact (@lem5209488 real P Q). Qed.
Lemma lem5209490 (s : real -> Prop) (x : real) (a : real) : (term907 s x a) = (term908 s x a).
Proof. exact (@lem5209489 (term885 x s) (real_le x a)). Qed.
Lemma lem5209491 (x : real) (x' : real) (s : real -> Prop) : (term909 x s x') = (term884 x x' s).
Proof. exact (eq_refl (term909 x s x')). Qed.
Lemma lem5209492 (x : real) (s : real -> Prop) : (term910 x s) = (term885 x s).
Proof. exact (fun_ext (fun x' : real => @lem5209491 x x' s)). Qed.
Lemma lem5209493 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209494 (x : real) (s : real -> Prop) : (term911 x s) = (term886 x s).
Proof. exact (MK_COMB (@lem5209493) (@lem5209492 x s)). Qed.
Lemma lem5209495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5209496 (x : real) (s : real -> Prop) : (term912 x s) = (term887 x s).
Proof. exact (MK_COMB (@lem5209495) (@lem5209494 x s)). Qed.
Lemma lem5209497 (x : real) (a : real) : (real_le x a) = (real_le x a).
Proof. exact (eq_refl (real_le x a)). Qed.
Lemma lem5209498 (s : real -> Prop) (x : real) (a : real) : (term907 s x a) = (term888 s x a).
Proof. exact (MK_COMB (@lem5209496 x s) (@lem5209497 x a)). Qed.
Lemma lem5209499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5209500 (s : real -> Prop) (x : real) (a : real) : (term913 s x a) = (term914 s x a).
Proof. exact (MK_COMB (@lem5209499) (@lem5209498 s x a)). Qed.
Lemma lem5209501 (x : real) (x' : real) (s : real -> Prop) : (term909 x s x') = (term884 x x' s).
Proof. exact (eq_refl (term909 x s x')). Qed.
Lemma lem5209502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5209503 (x : real) (x' : real) (s : real -> Prop) : (term915 x s x') = (term916 x x' s).
Proof. exact (MK_COMB (@lem5209502) (@lem5209501 x x' s)). Qed.
Lemma lem5209504 (x : real) (a : real) : (real_le x a) = (real_le x a).
Proof. exact (eq_refl (real_le x a)). Qed.
Lemma lem5209505 (x' : real) (s : real -> Prop) (x : real) (a : real) : (term917 s x' x a) = (term918 x' s x a).
Proof. exact (MK_COMB (@lem5209503 x x' s) (@lem5209504 x a)). Qed.
Lemma lem5209506 (s : real -> Prop) (x : real) (a : real) : (term919 s x a) = (term920 s x a).
Proof. exact (fun_ext (fun x' : real => @lem5209505 x' s x a)). Qed.
Lemma lem5209507 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209508 (s : real -> Prop) (x : real) (a : real) : (term908 s x a) = (term921 s x a).
Proof. exact (MK_COMB (@lem5209507) (@lem5209506 s x a)). Qed.
Lemma lem5209509 (s : real -> Prop) (x : real) (a : real) : ((term907 s x a) = (term908 s x a)) = ((term888 s x a) = (term921 s x a)).
Proof. exact (MK_COMB (@lem5209500 s x a) (@lem5209508 s x a)). Qed.
Lemma lem5209510 (s : real -> Prop) (x : real) (a : real) : (term888 s x a) = (term921 s x a).
Proof. exact (EQ_MP (@lem5209509 s x a) (@lem5209490 s x a)). Qed.
Lemma lem5209511 (s : real -> Prop) (a : real) : (term889 s a) = (term922 s a).
Proof. exact (fun_ext (fun x : real => @lem5209510 s x a)). Qed.
Lemma lem5209512 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209513 (s : real -> Prop) (a : real) : (term890 s a) = (term923 s a).
Proof. exact (MK_COMB (@lem5209512) (@lem5209511 s a)). Qed.
Lemma lem5209526 (x' : real) (s : real -> Prop) (x : real) (a : real) : (term918 x' s x a) = (term918 x' s x a).
Proof. exact (eq_refl (term918 x' s x a)). Qed.
Lemma lem5209527 (s : real -> Prop) (x : real) (a : real) : (term920 s x a) = (term920 s x a).
Proof. exact (fun_ext (fun x' : real => @lem5209526 x' s x a)). Qed.
Lemma lem5209528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209529 (s : real -> Prop) (x : real) (a : real) : (term921 s x a) = (term921 s x a).
Proof. exact (MK_COMB (@lem5209528) (@lem5209527 s x a)). Qed.
Lemma lem5209530 (s : real -> Prop) (a : real) : (term922 s a) = (term922 s a).
Proof. exact (fun_ext (fun x : real => @lem5209529 s x a)). Qed.
Lemma lem5209531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209532 (s : real -> Prop) (a : real) : (term923 s a) = (term923 s a).
Proof. exact (MK_COMB (@lem5209531) (@lem5209530 s a)). Qed.
Lemma lem5209533 (s : real -> Prop) (a : real) : (term890 s a) = (term923 s a).
Proof. exact (TRANS (@lem5209513 s a) (@lem5209532 s a)). Qed.
Lemma lem5209534 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term923 s a.
Proof. exact (EQ_MP (@lem5209533 s a) (@lem5209078 x'' s x' a h1)). Qed.
Lemma lem5209571 (s : real -> Prop) (h1 : term43 s) : term43 s.
Proof. exact (h1). Qed.
Lemma lem5209590 (x : real) : ((term843 x) = x) = ((term843 x) = x).
Proof. exact (eq_refl ((term843 x) = x)). Qed.
Lemma lem5209591 : term846 = term846.
Proof. exact (fun_ext (fun x : real => @lem5209590 x)). Qed.
Lemma lem5209592 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209594 : term847 = term847.
Proof. exact (MK_COMB (@lem5209592) (@lem5209591)). Qed.
Lemma lem5209595 (h1 : term196) : term847.
Proof. exact (EQ_MP (@lem5209594) (@lem5208772 h1)). Qed.
Lemma lem5209603 (x : type1023) (s : real -> Prop) : (term795 x s) = (term795 x s).
Proof. exact (eq_refl (term795 x s)). Qed.
Lemma lem5209604 (x : type1023) : (term797 x) = (term797 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5209603 x s)). Qed.
Lemma lem5209605 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5209607 (x : type1023) : (term799 x) = (term799 x).
Proof. exact (MK_COMB (@lem5209605) (@lem5209604 x)). Qed.
Lemma lem5209608 (x : type1023) (h1 : term818 x) : term799 x.
Proof. exact (EQ_MP (@lem5209607 x) (@lem5209066 x h1)). Qed.
Lemma lem5209707 (x : real) (x' : real) (s : real -> Prop) : (term884 x x' s) = (term884 x x' s).
Proof. exact (eq_refl (term884 x x' s)). Qed.
Lemma lem5209708 (x : real) (s : real -> Prop) : (term885 x s) = (term885 x s).
Proof. exact (fun_ext (fun x' : real => @lem5209707 x x' s)). Qed.
Lemma lem5209709 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209710 (x : real) (s : real -> Prop) : (term886 x s) = (term886 x s).
Proof. exact (MK_COMB (@lem5209709) (@lem5209708 x s)). Qed.
Lemma lem5209711 (s : real -> Prop) : (term895 s) = (term895 s).
Proof. exact (fun_ext (fun x : real => @lem5209710 x s)). Qed.
Lemma lem5209712 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209714 (s : real -> Prop) : (term896 s) = (term896 s).
Proof. exact (MK_COMB (@lem5209712) (@lem5209711 s)). Qed.
Lemma lem5209715 (s : real -> Prop) (h1 : term896 s) : term896 s.
Proof. exact (EQ_MP (@lem5209714 s) (@lem5209083 s h1)). Qed.
Lemma lem5209838 (s : real -> Prop) (x : real) (b' : real) : (term851 s x b') = (term851 s x b').
Proof. exact (eq_refl (term851 s x b')). Qed.
Lemma lem5209839 (s : real -> Prop) (b' : real) : (term852 s b') = (term852 s b').
Proof. exact (fun_ext (fun x : real => @lem5209838 s x b')). Qed.
Lemma lem5209840 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209842 (s : real -> Prop) (b' : real) : (term853 s b') = (term853 s b').
Proof. exact (MK_COMB (@lem5209840) (@lem5209839 s b')). Qed.
Lemma lem5209843 (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term853 s b'.
Proof. exact (EQ_MP (@lem5209842 s b') (@lem5209080 s a b' h1)). Qed.
Lemma lem5209857 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (b : real) : (term874 x'' s x' b) = (term874 x'' s x' b).
Proof. exact (eq_refl (term874 x'' s x' b)). Qed.
Lemma lem5209858 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) : (term893 x'' s x') = (term893 x'' s x').
Proof. exact (fun_ext (fun b : real => @lem5209857 x'' s x' b)). Qed.
Lemma lem5209859 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209861 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) : (term894 x'' s x') = (term894 x'' s x').
Proof. exact (MK_COMB (@lem5209859) (@lem5209858 x'' s x')). Qed.
Lemma lem5209862 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term894 x'' s x'.
Proof. exact (EQ_MP (@lem5209861 x'' s x') (@lem5209084 x'' s x' h1)). Qed.
Lemma lem5209883 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5209985 (s : real -> Prop) (x : real) (b' : real) : (term851 s x b') = (term851 s x b').
Proof. exact (eq_refl (term851 s x b')). Qed.
Lemma lem5209986 (s : real -> Prop) (b' : real) : (term852 s b') = (term852 s b').
Proof. exact (fun_ext (fun x : real => @lem5209985 s x b')). Qed.
Lemma lem5209987 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5209989 (s : real -> Prop) (b' : real) : (term853 s b') = (term853 s b').
Proof. exact (MK_COMB (@lem5209987) (@lem5209986 s b')). Qed.
Lemma lem5209990 (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term853 s b'.
Proof. exact (EQ_MP (@lem5209989 s b') (@lem5209080 s a b' h1)). Qed.
Lemma lem5210057 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (b : real) : (term877 x'' s x' a b) = (term924 x'' s x' a b).
Proof. exact (@lem19699 (term871 x' x'' b s) (term863 x' b) (real_le a b)). Qed.
Lemma lem5210058 (x' : real -> real) (a : real) (b : real) : (term925 x' a b) = (term925 x' a b).
Proof. exact (eq_refl (term925 x' a b)). Qed.
Lemma lem5210065 (x' : real -> real) (x'' : real -> real) (s : real -> Prop) (a : real) (b : real) : (term926 x' x'' s a b) = (term927 x' x'' s a b).
Proof. exact (@lem19699 ((x' b) = (term866 x'' b)) (term864 x'' b s) (real_le a b)). Qed.
Lemma lem5210066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5210067 (x' : real -> real) (x'' : real -> real) (s : real -> Prop) (a : real) (b : real) : (term928 x' x'' s a b) = (term929 x' x'' s a b).
Proof. exact (MK_COMB (@lem5210066) (@lem5210065 x' x'' s a b)). Qed.
Lemma lem5210068 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (b : real) : (term924 x'' s x' a b) = (term930 x'' s x' a b).
Proof. exact (MK_COMB (@lem5210067 x' x'' s a b) (@lem5210058 x' a b)). Qed.
Lemma lem5210070 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (b : real) : (term877 x'' s x' a b) = (term930 x'' s x' a b).
Proof. exact (TRANS (@lem5210057 x'' s x' a b) (@lem5210068 x'' s x' a b)). Qed.
Lemma lem5210071 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) : (term878 x'' s x' a) = (term931 x'' s x' a).
Proof. exact (fun_ext (fun b : real => @lem5210070 x'' s x' a b)). Qed.
Lemma lem5210072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5210074 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) : (term879 x'' s x' a) = (term932 x'' s x' a).
Proof. exact (MK_COMB (@lem5210072) (@lem5210071 x'' s x' a)). Qed.
Lemma lem5210075 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term932 x'' s x' a.
Proof. exact (EQ_MP (@lem5210074 x'' s x' a) (@lem5209085 x'' s x' a h1)). Qed.
Lemma lem5210079 (_67912 : real) (h1 : term196) : term933 _67912.
Proof. exact (@lem5209114 h1 _67912). Qed.
Lemma lem5210080 (_67912 : real) : (term933 _67912) = ((term843 _67912) = _67912).
Proof. exact (eq_refl (term933 _67912)). Qed.
Lemma lem5210103 (_67920 : real) (s : real -> Prop) (h1 : term896 s) : term934 s _67920.
Proof. exact (@lem5209225 s h1 _67920). Qed.
Lemma lem5210104 (_67920 : real) (s : real -> Prop) : (term934 s _67920) = (term886 _67920 s).
Proof. exact (eq_refl (term934 s _67920)). Qed.
Lemma lem5210105 (_67920 : real) (s : real -> Prop) (h1 : term896 s) : term886 _67920 s.
Proof. exact (EQ_MP (@lem5210104 _67920 s) (@lem5210103 _67920 s h1)). Qed.
Lemma lem5210106 (_67920 : real) (_67921 : real) (s : real -> Prop) (h1 : term896 s) : term909 _67920 s _67921.
Proof. exact (@lem5210105 _67920 s h1 _67921). Qed.
Lemma lem5210107 (_67920 : real) (_67921 : real) (s : real -> Prop) : (term909 _67920 s _67921) = (term884 _67920 _67921 s).
Proof. exact (eq_refl (term909 _67920 s _67921)). Qed.
Lemma lem5210109 (_67922 : real) (s : real -> Prop) (b : real) (h1 : term44 s b) : term935 s b _67922.
Proof. exact (@lem5209242 s b h1 _67922). Qed.
Lemma lem5210110 (s : real -> Prop) (b : real) (_67922 : real) : (term935 s b _67922) = (term231 s b _67922).
Proof. exact (eq_refl (term935 s b _67922)). Qed.
Lemma lem5210124 (_67927 : real) (h1 : term35) : term936 _67927.
Proof. exact (@lem5209324 h1 _67927). Qed.
Lemma lem5210125 (_67927 : real) : (term936 _67927) = (term837 _67927).
Proof. exact (eq_refl (term936 _67927)). Qed.
Lemma lem5210126 (_67927 : real) (h1 : term35) : term837 _67927.
Proof. exact (EQ_MP (@lem5210125 _67927) (@lem5210124 _67927 h1)). Qed.
Lemma lem5210127 (_67927 : real) (_67928 : real) (h1 : term35) : term937 _67927 _67928.
Proof. exact (@lem5210126 _67927 h1 _67928). Qed.
Lemma lem5210128 (_67928 : real) (_67927 : real) : (term937 _67927 _67928) = (term835 _67928 _67927).
Proof. exact (eq_refl (term937 _67927 _67928)). Qed.
Lemma lem5210136 (_67931 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term938 x'' s x' _67931.
Proof. exact (@lem5209363 x'' s x' h1 _67931). Qed.
Lemma lem5210137 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (_67931 : real) : (term938 x'' s x' _67931) = (term874 x'' s x' _67931).
Proof. exact (eq_refl (term938 x'' s x' _67931)). Qed.
Lemma lem5210138 (_67931 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term874 x'' s x' _67931.
Proof. exact (EQ_MP (@lem5210137 x'' s x' _67931) (@lem5210136 _67931 x'' s x' h1)). Qed.
Lemma lem5210166 (_67941 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term939 s a _67941.
Proof. exact (@lem5209534 x'' s x' a h1 _67941). Qed.
Lemma lem5210167 (s : real -> Prop) (_67941 : real) (a : real) : (term939 s a _67941) = (term921 s _67941 a).
Proof. exact (eq_refl (term939 s a _67941)). Qed.
Lemma lem5210168 (_67941 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term921 s _67941 a.
Proof. exact (EQ_MP (@lem5210167 s _67941 a) (@lem5210166 _67941 x'' s x' a h1)). Qed.
Lemma lem5210169 (_67941 : real) (_67942 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term940 s _67941 a _67942.
Proof. exact (@lem5210168 _67941 x'' s x' a h1 _67942). Qed.
Lemma lem5210170 (_67942 : real) (s : real -> Prop) (_67941 : real) (a : real) : (term940 s _67941 a _67942) = (term918 _67942 s _67941 a).
Proof. exact (eq_refl (term940 s _67941 a _67942)). Qed.
Lemma lem5210171 (_67942 : real) (_67941 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term918 _67942 s _67941 a.
Proof. exact (EQ_MP (@lem5210170 _67942 s _67941 a) (@lem5210169 _67941 _67942 x'' s x' a h1)). Qed.
Lemma lem5210178 (_67945 : real) (h1 : term196) : term933 _67945.
Proof. exact (@lem5209595 h1 _67945). Qed.
Lemma lem5210179 (_67945 : real) : (term933 _67945) = ((term843 _67945) = _67945).
Proof. exact (eq_refl (term933 _67945)). Qed.
Lemma lem5210181 (_67946 : real -> Prop) (x : type1023) (h1 : term818 x) : term941 x _67946.
Proof. exact (@lem5209608 x h1 _67946). Qed.
Lemma lem5210182 (x : type1023) (_67946 : real -> Prop) : (term941 x _67946) = (term795 x _67946).
Proof. exact (eq_refl (term941 x _67946)). Qed.
Lemma lem5210205 (_67954 : real) (s : real -> Prop) (h1 : term896 s) : term934 s _67954.
Proof. exact (@lem5209715 s h1 _67954). Qed.
Lemma lem5210206 (_67954 : real) (s : real -> Prop) : (term934 s _67954) = (term886 _67954 s).
Proof. exact (eq_refl (term934 s _67954)). Qed.
Lemma lem5210207 (_67954 : real) (s : real -> Prop) (h1 : term896 s) : term886 _67954 s.
Proof. exact (EQ_MP (@lem5210206 _67954 s) (@lem5210205 _67954 s h1)). Qed.
Lemma lem5210208 (_67954 : real) (_67955 : real) (s : real -> Prop) (h1 : term896 s) : term909 _67954 s _67955.
Proof. exact (@lem5210207 _67954 s h1 _67955). Qed.
Lemma lem5210209 (_67954 : real) (_67955 : real) (s : real -> Prop) : (term909 _67954 s _67955) = (term884 _67954 _67955 s).
Proof. exact (eq_refl (term909 _67954 s _67955)). Qed.
Lemma lem5210238 (_67965 : real) (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term942 s b' _67965.
Proof. exact (@lem5209843 s a b' h1 _67965). Qed.
Lemma lem5210239 (s : real -> Prop) (_67965 : real) (b' : real) : (term942 s b' _67965) = (term851 s _67965 b').
Proof. exact (eq_refl (term942 s b' _67965)). Qed.
Lemma lem5210241 (_67966 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term938 x'' s x' _67966.
Proof. exact (@lem5209862 x'' s x' h1 _67966). Qed.
Lemma lem5210242 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (_67966 : real) : (term938 x'' s x' _67966) = (term874 x'' s x' _67966).
Proof. exact (eq_refl (term938 x'' s x' _67966)). Qed.
Lemma lem5210243 (_67966 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term874 x'' s x' _67966.
Proof. exact (EQ_MP (@lem5210242 x'' s x' _67966) (@lem5210241 _67966 x'' s x' h1)). Qed.
Lemma lem5210271 (_67976 : real) (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term942 s b' _67976.
Proof. exact (@lem5209990 s a b' h1 _67976). Qed.
Lemma lem5210272 (s : real -> Prop) (_67976 : real) (b' : real) : (term942 s b' _67976) = (term851 s _67976 b').
Proof. exact (eq_refl (term942 s b' _67976)). Qed.
Lemma lem5210280 (_67979 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term943 x'' s x' a _67979.
Proof. exact (@lem5210075 x'' s x' a h1 _67979). Qed.
Lemma lem5210281 (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (_67979 : real) : (term943 x'' s x' a _67979) = (term930 x'' s x' a _67979).
Proof. exact (eq_refl (term943 x'' s x' a _67979)). Qed.
Lemma lem5210282 (_67979 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term930 x'' s x' a _67979.
Proof. exact (EQ_MP (@lem5210281 x'' s x' a _67979) (@lem5210280 _67979 x'' s x' a h1)). Qed.
Lemma lem5210284 (_67931 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term871 x' x'' _67931 s.
Proof. exact (proj1 (@lem5210138 _67931 x'' s x' h1)). Qed.
Lemma lem5210292 (_67966 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term871 x' x'' _67966 s.
Proof. exact (proj1 (@lem5210243 _67966 x'' s x' h1)). Qed.
Lemma lem5210296 (_67979 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term927 x' x'' s a _67979.
Proof. exact (proj1 (@lem5210282 _67979 x'' s x' a h1)). Qed.
Lemma lem5210400 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5210430 (s : real -> Prop) (b' : real) (a : real) (h1 : term860 s b' a) : term858 b' a.
Proof. exact (proj2 (@lem5209069 s b' a h1)). Qed.
Lemma lem5210441 (_67942 : real) (s : real -> Prop) (_67941 : real) (a : real) : (term918 _67942 s _67941 a) = (term944 _67942 s _67941 a).
Proof. exact (@lem5205418 (term881 _67941 _67942) (term724 _67942 s) (real_le _67941 a)). Qed.
Lemma lem5210442 (_67942 : real) (_67941 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term944 _67942 s _67941 a.
Proof. exact (EQ_MP (@lem5210441 _67942 s _67941 a) (@lem5210171 _67942 _67941 x'' s x' a h1)). Qed.
Lemma lem5210462 (s : real -> Prop) (h1 : term43 s) : term43 s.
Proof. exact (h1). Qed.
Lemma lem5210570 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term21 s) = a.
Proof. exact (h1). Qed.
Lemma lem5210604 (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term849 a b'.
Proof. exact (proj2 (@lem5209070 s a b' h1)). Qed.
Lemma lem5210622 (_67979 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term925 x' a _67979.
Proof. exact (proj2 (@lem5210282 _67979 x'' s x' a h1)). Qed.
Lemma lem5210628 (_67979 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term945 x' x'' a _67979.
Proof. exact (proj1 (@lem5210296 _67979 x'' s x' a h1)). Qed.
Lemma lem5210634 (_67979 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (a : real) (h1 : term892 x'' s x' a) : term946 x'' s a _67979.
Proof. exact (proj2 (@lem5210296 _67979 x'' s x' a h1)). Qed.
Lemma lem5210788 (_67920 : real) (_67921 : real) (s : real -> Prop) (h1 : term896 s) : term884 _67920 _67921 s.
Proof. exact (EQ_MP (@lem5210107 _67920 _67921 s) (@lem5210106 _67920 _67921 s h1)). Qed.
Lemma lem5210831 (_67922 : real) (s : real -> Prop) (b : real) (h1 : term44 s b) : term231 s b _67922.
Proof. exact (EQ_MP (@lem5210110 s b _67922) (@lem5210109 _67922 s b h1)). Qed.
Lemma lem5210887 (_67928 : real) (_67927 : real) (h1 : term35) : term835 _67928 _67927.
Proof. exact (EQ_MP (@lem5210128 _67928 _67927) (@lem5210127 _67927 _67928 h1)). Qed.
Lemma lem5210942 (_67931 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term863 x' _67931.
Proof. exact (proj2 (@lem5210138 _67931 x'' s x' h1)). Qed.
Lemma lem5210971 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : a = (term21 s).
Proof. exact (SYM (@lem5210400 s a h1)). Qed.
Lemma lem5211098 (b' : real) : (term947 b') = (term947 b').
Proof. exact (eq_refl (term947 b')). Qed.
Lemma lem5211099 (b' : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term948 b' a) = (term949 b' s).
Proof. exact (MK_COMB (@lem5211098 b') (@lem5210971 s a h1)). Qed.
Lemma lem5211100 (b' : real) (s : real -> Prop) : (term949 b' s) = (term950 b' s).
Proof. exact (eq_refl (term949 b' s)). Qed.
Lemma lem5211101 (b' : real) (a : real) : (term951 b' a) = (term951 b' a).
Proof. exact (eq_refl (term951 b' a)). Qed.
Lemma lem5211102 (a : real) (b' : real) (s : real -> Prop) : ((term948 b' a) = (term949 b' s)) = ((term948 b' a) = (term950 b' s)).
Proof. exact (MK_COMB (@lem5211101 b' a) (@lem5211100 b' s)). Qed.
Lemma lem5211103 (b' : real) (a : real) : (term948 b' a) = (term858 b' a).
Proof. exact (eq_refl (term948 b' a)). Qed.
Lemma lem5211104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5211105 (b' : real) (a : real) : (term951 b' a) = (term952 b' a).
Proof. exact (MK_COMB (@lem5211104) (@lem5211103 b' a)). Qed.
Lemma lem5211106 (b' : real) (s : real -> Prop) : (term950 b' s) = (term950 b' s).
Proof. exact (eq_refl (term950 b' s)). Qed.
Lemma lem5211107 (a : real) (b' : real) (s : real -> Prop) : ((term948 b' a) = (term950 b' s)) = ((term858 b' a) = (term950 b' s)).
Proof. exact (MK_COMB (@lem5211105 b' a) (@lem5211106 b' s)). Qed.
Lemma lem5211108 (a : real) (b' : real) (s : real -> Prop) : ((term948 b' a) = (term949 b' s)) = ((term858 b' a) = (term950 b' s)).
Proof. exact (TRANS (@lem5211102 a b' s) (@lem5211107 a b' s)). Qed.
Lemma lem5211109 (b' : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term858 b' a) = (term950 b' s).
Proof. exact (EQ_MP (@lem5211108 a b' s) (@lem5211099 b' s a h1)). Qed.
Lemma lem5211110 (b' : real) (s : real -> Prop) (a : real) (h1 : term860 s b' a) (h2 : (term21 s) = a) : term950 b' s.
Proof. exact (EQ_MP (@lem5211109 b' s a h2) (@lem5210430 s b' a h1)). Qed.
Lemma lem5211111 (_67942 : real) (s : real -> Prop) (_67941 : real) : (term953 _67942 s _67941) = (term953 _67942 s _67941).
Proof. exact (eq_refl (term953 _67942 s _67941)). Qed.
Lemma lem5211112 (_67942 : real) (_67941 : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term954 _67942 s _67941 a) = (term955 _67942 _67941 s).
Proof. exact (MK_COMB (@lem5211111 _67942 s _67941) (@lem5210971 s a h1)). Qed.
Lemma lem5211113 (_67942 : real) (_67941 : real) (s : real -> Prop) : (term955 _67942 _67941 s) = (term956 _67942 _67941 s).
Proof. exact (eq_refl (term955 _67942 _67941 s)). Qed.
Lemma lem5211114 (_67942 : real) (s : real -> Prop) (_67941 : real) (a : real) : (term957 _67942 s _67941 a) = (term957 _67942 s _67941 a).
Proof. exact (eq_refl (term957 _67942 s _67941 a)). Qed.
Lemma lem5211115 (a : real) (_67942 : real) (_67941 : real) (s : real -> Prop) : ((term954 _67942 s _67941 a) = (term955 _67942 _67941 s)) = ((term954 _67942 s _67941 a) = (term956 _67942 _67941 s)).
Proof. exact (MK_COMB (@lem5211114 _67942 s _67941 a) (@lem5211113 _67942 _67941 s)). Qed.
Lemma lem5211116 (_67942 : real) (s : real -> Prop) (_67941 : real) (a : real) : (term954 _67942 s _67941 a) = (term944 _67942 s _67941 a).
Proof. exact (eq_refl (term954 _67942 s _67941 a)). Qed.
Lemma lem5211117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5211118 (_67942 : real) (s : real -> Prop) (_67941 : real) (a : real) : (term957 _67942 s _67941 a) = (term958 _67942 s _67941 a).
Proof. exact (MK_COMB (@lem5211117) (@lem5211116 _67942 s _67941 a)). Qed.
Lemma lem5211119 (_67942 : real) (_67941 : real) (s : real -> Prop) : (term956 _67942 _67941 s) = (term956 _67942 _67941 s).
Proof. exact (eq_refl (term956 _67942 _67941 s)). Qed.
Lemma lem5211120 (a : real) (_67942 : real) (_67941 : real) (s : real -> Prop) : ((term954 _67942 s _67941 a) = (term956 _67942 _67941 s)) = ((term944 _67942 s _67941 a) = (term956 _67942 _67941 s)).
Proof. exact (MK_COMB (@lem5211118 _67942 s _67941 a) (@lem5211119 _67942 _67941 s)). Qed.
Lemma lem5211121 (a : real) (_67942 : real) (_67941 : real) (s : real -> Prop) : ((term954 _67942 s _67941 a) = (term955 _67942 _67941 s)) = ((term944 _67942 s _67941 a) = (term956 _67942 _67941 s)).
Proof. exact (TRANS (@lem5211115 a _67942 _67941 s) (@lem5211120 a _67942 _67941 s)). Qed.
Lemma lem5211122 (_67942 : real) (_67941 : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term944 _67942 s _67941 a) = (term956 _67942 _67941 s).
Proof. exact (EQ_MP (@lem5211121 a _67942 _67941 s) (@lem5211112 _67942 _67941 s a h1)). Qed.
Lemma lem5211123 (_67942 : real) (_67941 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term956 _67942 _67941 s.
Proof. exact (EQ_MP (@lem5211122 _67942 _67941 s a h2) (@lem5210442 _67942 _67941 x'' s x' a h1)). Qed.
Lemma lem5211191 (s : real -> Prop) (h1 : term43 s) : term43 s.
Proof. exact (h1). Qed.
Lemma lem5211233 (_67946 : real -> Prop) (x : type1023) (h1 : term818 x) : term795 x _67946.
Proof. exact (EQ_MP (@lem5210182 x _67946) (@lem5210181 _67946 x h1)). Qed.
Lemma lem5211316 (_67954 : real) (_67955 : real) (s : real -> Prop) (h1 : term896 s) : term884 _67954 _67955 s.
Proof. exact (EQ_MP (@lem5210209 _67954 _67955 s) (@lem5210208 _67954 _67955 s h1)). Qed.
Lemma lem5211443 (_67965 : real) (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term851 s _67965 b'.
Proof. exact (EQ_MP (@lem5210239 s _67965 b') (@lem5210238 _67965 s a b' h1)). Qed.
Lemma lem5211470 (_67966 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term863 x' _67966.
Proof. exact (proj2 (@lem5210243 _67966 x'' s x' h1)). Qed.
Lemma lem5211499 (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : a = (term21 s).
Proof. exact (SYM (@lem5210570 s a h1)). Qed.
Lemma lem5211625 (_67976 : real) (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term851 s _67976 b'.
Proof. exact (EQ_MP (@lem5210272 s _67976 b') (@lem5210271 _67976 s a b' h1)). Qed.
Lemma lem5211626 (b' : real) : (term959 b') = (term959 b').
Proof. exact (eq_refl (term959 b')). Qed.
Lemma lem5211627 (b' : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term960 b' a) = (term961 b' s).
Proof. exact (MK_COMB (@lem5211626 b') (@lem5211499 s a h1)). Qed.
Lemma lem5211628 (s : real -> Prop) (b' : real) : (term961 b' s) = (term962 s b').
Proof. exact (eq_refl (term961 b' s)). Qed.
Lemma lem5211629 (b' : real) (a : real) : (term963 b' a) = (term963 b' a).
Proof. exact (eq_refl (term963 b' a)). Qed.
Lemma lem5211630 (a : real) (s : real -> Prop) (b' : real) : ((term960 b' a) = (term961 b' s)) = ((term960 b' a) = (term962 s b')).
Proof. exact (MK_COMB (@lem5211629 b' a) (@lem5211628 s b')). Qed.
Lemma lem5211631 (a : real) (b' : real) : (term960 b' a) = (term849 a b').
Proof. exact (eq_refl (term960 b' a)). Qed.
Lemma lem5211632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5211633 (a : real) (b' : real) : (term963 b' a) = (term964 a b').
Proof. exact (MK_COMB (@lem5211632) (@lem5211631 a b')). Qed.
Lemma lem5211634 (s : real -> Prop) (b' : real) : (term962 s b') = (term962 s b').
Proof. exact (eq_refl (term962 s b')). Qed.
Lemma lem5211635 (a : real) (s : real -> Prop) (b' : real) : ((term960 b' a) = (term962 s b')) = ((term849 a b') = (term962 s b')).
Proof. exact (MK_COMB (@lem5211633 a b') (@lem5211634 s b')). Qed.
Lemma lem5211636 (a : real) (s : real -> Prop) (b' : real) : ((term960 b' a) = (term961 b' s)) = ((term849 a b') = (term962 s b')).
Proof. exact (TRANS (@lem5211630 a s b') (@lem5211635 a s b')). Qed.
Lemma lem5211637 (b' : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term849 a b') = (term962 s b').
Proof. exact (EQ_MP (@lem5211636 a s b') (@lem5211627 b' s a h1)). Qed.
Lemma lem5211638 (b' : real) (s : real -> Prop) (a : real) (h1 : term855 s a b') (h2 : (term21 s) = a) : term962 s b'.
Proof. exact (EQ_MP (@lem5211637 b' s a h2) (@lem5210604 s a b' h1)). Qed.
Lemma lem5211652 (x' : real -> real) (_67979 : real) : (term965 x' _67979) = (term965 x' _67979).
Proof. exact (eq_refl (term965 x' _67979)). Qed.
Lemma lem5211653 (x' : real -> real) (_67979 : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term966 x' _67979 a) = (term967 x' _67979 s).
Proof. exact (MK_COMB (@lem5211652 x' _67979) (@lem5211499 s a h1)). Qed.
Lemma lem5211654 (x' : real -> real) (s : real -> Prop) (_67979 : real) : (term967 x' _67979 s) = (term968 x' s _67979).
Proof. exact (eq_refl (term967 x' _67979 s)). Qed.
Lemma lem5211655 (x' : real -> real) (_67979 : real) (a : real) : (term969 x' _67979 a) = (term969 x' _67979 a).
Proof. exact (eq_refl (term969 x' _67979 a)). Qed.
Lemma lem5211656 (a : real) (x' : real -> real) (s : real -> Prop) (_67979 : real) : ((term966 x' _67979 a) = (term967 x' _67979 s)) = ((term966 x' _67979 a) = (term968 x' s _67979)).
Proof. exact (MK_COMB (@lem5211655 x' _67979 a) (@lem5211654 x' s _67979)). Qed.
Lemma lem5211657 (x' : real -> real) (a : real) (_67979 : real) : (term966 x' _67979 a) = (term925 x' a _67979).
Proof. exact (eq_refl (term966 x' _67979 a)). Qed.
Lemma lem5211658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5211659 (x' : real -> real) (a : real) (_67979 : real) : (term969 x' _67979 a) = (term970 x' a _67979).
Proof. exact (MK_COMB (@lem5211658) (@lem5211657 x' a _67979)). Qed.
Lemma lem5211660 (x' : real -> real) (s : real -> Prop) (_67979 : real) : (term968 x' s _67979) = (term968 x' s _67979).
Proof. exact (eq_refl (term968 x' s _67979)). Qed.
Lemma lem5211661 (a : real) (x' : real -> real) (s : real -> Prop) (_67979 : real) : ((term966 x' _67979 a) = (term968 x' s _67979)) = ((term925 x' a _67979) = (term968 x' s _67979)).
Proof. exact (MK_COMB (@lem5211659 x' a _67979) (@lem5211660 x' s _67979)). Qed.
Lemma lem5211662 (a : real) (x' : real -> real) (s : real -> Prop) (_67979 : real) : ((term966 x' _67979 a) = (term967 x' _67979 s)) = ((term925 x' a _67979) = (term968 x' s _67979)).
Proof. exact (TRANS (@lem5211656 a x' s _67979) (@lem5211661 a x' s _67979)). Qed.
Lemma lem5211663 (x' : real -> real) (_67979 : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term925 x' a _67979) = (term968 x' s _67979).
Proof. exact (EQ_MP (@lem5211662 a x' s _67979) (@lem5211653 x' _67979 s a h1)). Qed.
Lemma lem5211664 (_67979 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term968 x' s _67979.
Proof. exact (EQ_MP (@lem5211663 x' _67979 s a h2) (@lem5210622 _67979 x'' s x' a h1)). Qed.
Lemma lem5211665 (x' : real -> real) (x'' : real -> real) (_67979 : real) : (term971 x' x'' _67979) = (term971 x' x'' _67979).
Proof. exact (eq_refl (term971 x' x'' _67979)). Qed.
Lemma lem5211666 (x' : real -> real) (x'' : real -> real) (_67979 : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term972 x' x'' _67979 a) = (term973 x' x'' _67979 s).
Proof. exact (MK_COMB (@lem5211665 x' x'' _67979) (@lem5211499 s a h1)). Qed.
Lemma lem5211667 (x' : real -> real) (x'' : real -> real) (s : real -> Prop) (_67979 : real) : (term973 x' x'' _67979 s) = (term974 x' x'' s _67979).
Proof. exact (eq_refl (term973 x' x'' _67979 s)). Qed.
Lemma lem5211668 (x' : real -> real) (x'' : real -> real) (_67979 : real) (a : real) : (term975 x' x'' _67979 a) = (term975 x' x'' _67979 a).
Proof. exact (eq_refl (term975 x' x'' _67979 a)). Qed.
Lemma lem5211669 (a : real) (x' : real -> real) (x'' : real -> real) (s : real -> Prop) (_67979 : real) : ((term972 x' x'' _67979 a) = (term973 x' x'' _67979 s)) = ((term972 x' x'' _67979 a) = (term974 x' x'' s _67979)).
Proof. exact (MK_COMB (@lem5211668 x' x'' _67979 a) (@lem5211667 x' x'' s _67979)). Qed.
Lemma lem5211670 (x' : real -> real) (x'' : real -> real) (a : real) (_67979 : real) : (term972 x' x'' _67979 a) = (term945 x' x'' a _67979).
Proof. exact (eq_refl (term972 x' x'' _67979 a)). Qed.
Lemma lem5211671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5211672 (x' : real -> real) (x'' : real -> real) (a : real) (_67979 : real) : (term975 x' x'' _67979 a) = (term976 x' x'' a _67979).
Proof. exact (MK_COMB (@lem5211671) (@lem5211670 x' x'' a _67979)). Qed.
Lemma lem5211673 (x' : real -> real) (x'' : real -> real) (s : real -> Prop) (_67979 : real) : (term974 x' x'' s _67979) = (term974 x' x'' s _67979).
Proof. exact (eq_refl (term974 x' x'' s _67979)). Qed.
Lemma lem5211674 (a : real) (x' : real -> real) (x'' : real -> real) (s : real -> Prop) (_67979 : real) : ((term972 x' x'' _67979 a) = (term974 x' x'' s _67979)) = ((term945 x' x'' a _67979) = (term974 x' x'' s _67979)).
Proof. exact (MK_COMB (@lem5211672 x' x'' a _67979) (@lem5211673 x' x'' s _67979)). Qed.
Lemma lem5211675 (a : real) (x' : real -> real) (x'' : real -> real) (s : real -> Prop) (_67979 : real) : ((term972 x' x'' _67979 a) = (term973 x' x'' _67979 s)) = ((term945 x' x'' a _67979) = (term974 x' x'' s _67979)).
Proof. exact (TRANS (@lem5211669 a x' x'' s _67979) (@lem5211674 a x' x'' s _67979)). Qed.
Lemma lem5211676 (x' : real -> real) (x'' : real -> real) (_67979 : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term945 x' x'' a _67979) = (term974 x' x'' s _67979).
Proof. exact (EQ_MP (@lem5211675 a x' x'' s _67979) (@lem5211666 x' x'' _67979 s a h1)). Qed.
Lemma lem5211677 (_67979 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term974 x' x'' s _67979.
Proof. exact (EQ_MP (@lem5211676 x' x'' _67979 s a h2) (@lem5210628 _67979 x'' s x' a h1)). Qed.
Lemma lem5211678 (x'' : real -> real) (s : real -> Prop) (_67979 : real) : (term977 x'' s _67979) = (term977 x'' s _67979).
Proof. exact (eq_refl (term977 x'' s _67979)). Qed.
Lemma lem5211679 (x'' : real -> real) (_67979 : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term978 x'' s _67979 a) = (term979 x'' _67979 s).
Proof. exact (MK_COMB (@lem5211678 x'' s _67979) (@lem5211499 s a h1)). Qed.
Lemma lem5211680 (x'' : real -> real) (s : real -> Prop) (_67979 : real) : (term979 x'' _67979 s) = (term980 x'' s _67979).
Proof. exact (eq_refl (term979 x'' _67979 s)). Qed.
Lemma lem5211681 (x'' : real -> real) (s : real -> Prop) (_67979 : real) (a : real) : (term981 x'' s _67979 a) = (term981 x'' s _67979 a).
Proof. exact (eq_refl (term981 x'' s _67979 a)). Qed.
Lemma lem5211682 (a : real) (x'' : real -> real) (s : real -> Prop) (_67979 : real) : ((term978 x'' s _67979 a) = (term979 x'' _67979 s)) = ((term978 x'' s _67979 a) = (term980 x'' s _67979)).
Proof. exact (MK_COMB (@lem5211681 x'' s _67979 a) (@lem5211680 x'' s _67979)). Qed.
Lemma lem5211683 (x'' : real -> real) (s : real -> Prop) (a : real) (_67979 : real) : (term978 x'' s _67979 a) = (term946 x'' s a _67979).
Proof. exact (eq_refl (term978 x'' s _67979 a)). Qed.
Lemma lem5211684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5211685 (x'' : real -> real) (s : real -> Prop) (a : real) (_67979 : real) : (term981 x'' s _67979 a) = (term982 x'' s a _67979).
Proof. exact (MK_COMB (@lem5211684) (@lem5211683 x'' s a _67979)). Qed.
Lemma lem5211686 (x'' : real -> real) (s : real -> Prop) (_67979 : real) : (term980 x'' s _67979) = (term980 x'' s _67979).
Proof. exact (eq_refl (term980 x'' s _67979)). Qed.
Lemma lem5211687 (a : real) (x'' : real -> real) (s : real -> Prop) (_67979 : real) : ((term978 x'' s _67979 a) = (term980 x'' s _67979)) = ((term946 x'' s a _67979) = (term980 x'' s _67979)).
Proof. exact (MK_COMB (@lem5211685 x'' s a _67979) (@lem5211686 x'' s _67979)). Qed.
Lemma lem5211688 (a : real) (x'' : real -> real) (s : real -> Prop) (_67979 : real) : ((term978 x'' s _67979 a) = (term979 x'' _67979 s)) = ((term946 x'' s a _67979) = (term980 x'' s _67979)).
Proof. exact (TRANS (@lem5211682 a x'' s _67979) (@lem5211687 a x'' s _67979)). Qed.
Lemma lem5211689 (x'' : real -> real) (_67979 : real) (s : real -> Prop) (a : real) (h1 : (term21 s) = a) : (term946 x'' s a _67979) = (term980 x'' s _67979).
Proof. exact (EQ_MP (@lem5211688 a x'' s _67979) (@lem5211679 x'' _67979 s a h1)). Qed.
Lemma lem5211690 (_67979 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term980 x'' s _67979.
Proof. exact (EQ_MP (@lem5211689 x'' _67979 s a h2) (@lem5210634 _67979 x'' s x' a h1)). Qed.
Lemma lem5211782 (_67912 : real) (h1 : term196) : (term843 _67912) = _67912.
Proof. exact (EQ_MP (@lem5210080 _67912) (@lem5210079 _67912 h1)). Qed.
Lemma lem5211783 (b' : real) (h1 : term196) : (term983 b') = (@I (real -> real) real_neg b').
Proof. exact (@lem5211782 (@I (real -> real) real_neg b') h1). Qed.
Lemma lem5211784 (b' : real) (h1 : term196) : term984 b'.
Proof. exact (fun h0 : term985 b' => @lem5211783 b' h1). Qed.
Lemma lem5211786 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5211787 (b' : real) : (term984 b') = ((term983 b') = (@I (real -> real) real_neg b')).
Proof. exact (@lem5211786 ((term983 b') = (@I (real -> real) real_neg b'))). Qed.
Lemma lem5211788 (b' : real) (h1 : term196) : (term983 b') = (@I (real -> real) real_neg b').
Proof. exact (EQ_MP (@lem5211787 b') (@lem5211784 b' h1)). Qed.
Lemma lem5211790 (s : real -> Prop) (b' : real) (a : real) (h1 : term860 s b' a) : @IN real b' s.
Proof. exact (proj1 (@lem5209069 s b' a h1)). Qed.
Lemma lem5211791 (s : real -> Prop) (b' : real) (a : real) (h1 : term860 s b' a) : term987 b' s.
Proof. exact (fun h0 : term724 b' s => @lem5211790 s b' a h1). Qed.
Lemma lem5211793 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5211794 (b' : real) (s : real -> Prop) : (term987 b' s) = (@IN real b' s).
Proof. exact (@lem5211793 (@IN real b' s)). Qed.
Lemma lem5211795 (s : real -> Prop) (b' : real) (a : real) (h1 : term860 s b' a) : @IN real b' s.
Proof. exact (EQ_MP (@lem5211794 b' s) (@lem5211791 s b' a h1)). Qed.
Lemma lem5211797 (a : Prop) (b : Prop) : (term988 a b) = (term989 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5211798 (_67920 : real) (_67921 : real) (s : real -> Prop) : (term884 _67920 _67921 s) = (term990 _67920 _67921 s).
Proof. exact (@lem5211797 (_67920 = (@I (real -> real) real_neg _67921)) (@IN real _67921 s)). Qed.
Lemma lem5211800 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5211801 (_67920 : real) (_67921 : real) (s : real -> Prop) : (term990 _67920 _67921 s) = (term991 _67920 _67921 s).
Proof. exact (@lem5211800 (term992 _67920 _67921 s)). Qed.
Lemma lem5211802 (_67920 : real) (_67921 : real) (s : real -> Prop) : (term884 _67920 _67921 s) = (term991 _67920 _67921 s).
Proof. exact (TRANS (@lem5211798 _67920 _67921 s) (@lem5211801 _67920 _67921 s)). Qed.
Lemma lem5211804 (s : real -> Prop) (b' : real) (a : real) (h1 : term196) (h2 : term860 s b' a) : term993 b' s.
Proof. exact (conj (@lem5211788 b' h1) (@lem5211795 s b' a h2)). Qed.
Lemma lem5211806 (_67920 : real) (_67921 : real) (s : real -> Prop) (h1 : term896 s) : term991 _67920 _67921 s.
Proof. exact (EQ_MP (@lem5211802 _67920 _67921 s) (@lem5210788 _67920 _67921 s h1)). Qed.
Lemma lem5211807 (b' : real) (s : real -> Prop) (h1 : term896 s) : term994 b' s.
Proof. exact (@lem5211806 (term983 b') b' s h1). Qed.
Lemma lem5211810 (s : real -> Prop) (b' : real) (a : real) (h1 : term896 s) (h2 : term196) (h3 : term860 s b' a) : False.
Proof. exact (@lem5211807 b' s h1 (@lem5211804 s b' a h2 h3)). Qed.
Lemma lem5211811 (s : real -> Prop) (b' : real) (a : real) (h1 : term896 s) (h2 : term196) (h3 : term860 s b' a) : term995.
Proof. exact (fun h0 : ~ False => @lem5211810 s b' a h1 h2 h3). Qed.
Lemma lem5211813 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5211814 : term995 = False.
Proof. exact (@lem5211813 False). Qed.
Lemma lem5211835 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5211836 (_68156 : real) (_68158 : real) (h1 : _68156 = _68158) : _68156 = _68158.
Proof. exact (h1). Qed.
Lemma lem5211837 (_68157 : real) (_68159 : real) (h1 : _68157 = _68159) : _68157 = _68159.
Proof. exact (h1). Qed.
Lemma lem5211838 (_68156 : real) (_68158 : real) (h1 : _68156 = _68158) : (real_le _68156) = (real_le _68158).
Proof. exact (MK_COMB (@lem5211835) (@lem5211836 _68156 _68158 h1)). Qed.
Lemma lem5211839 (_68156 : real) (_68158 : real) (_68157 : real) (_68159 : real) (h1 : _68156 = _68158) (h2 : _68157 = _68159) : (real_le _68156 _68157) = (real_le _68158 _68159).
Proof. exact (MK_COMB (@lem5211838 _68156 _68158 h1) (@lem5211837 _68157 _68159 h2)). Qed.
Lemma lem5211841 (b : Prop) (a : Prop) : term996 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5211842 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : term997 _68158 _68159 _68156 _68157.
Proof. exact (@lem5211841 (real_le _68158 _68159) (real_le _68156 _68157)). Qed.
Lemma lem5211843 (_68156 : real) (_68158 : real) (_68157 : real) (_68159 : real) (h1 : _68156 = _68158) (h2 : _68157 = _68159) : term998 _68158 _68159 _68156 _68157.
Proof. exact (@lem5211842 _68158 _68159 _68156 _68157 (@lem5211839 _68156 _68158 _68157 _68159 h1 h2)). Qed.
Lemma lem5211844 (_68159 : real) (_68157 : real) (_68156 : real) (_68158 : real) (h1 : _68156 = _68158) : term999 _68158 _68159 _68156 _68157.
Proof. exact (fun h0 : _68157 = _68159 => @lem5211843 _68156 _68158 _68157 _68159 h1 h0). Qed.
Lemma lem5211846 (a : Prop) (b : Prop) : (a -> b) = (term1000 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5211847 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term999 _68158 _68159 _68156 _68157) = (term1001 _68158 _68159 _68156 _68157).
Proof. exact (@lem5211846 (_68157 = _68159) (term998 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5211848 (_68159 : real) (_68157 : real) (_68156 : real) (_68158 : real) (h1 : _68156 = _68158) : term1001 _68158 _68159 _68156 _68157.
Proof. exact (EQ_MP (@lem5211847 _68158 _68159 _68156 _68157) (@lem5211844 _68159 _68157 _68156 _68158 h1)). Qed.
Lemma lem5211849 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : term1002 _68158 _68159 _68156 _68157.
Proof. exact (fun h0 : _68156 = _68158 => @lem5211848 _68159 _68157 _68156 _68158 h0). Qed.
Lemma lem5211851 (a : Prop) (b : Prop) : (a -> b) = (term1000 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5211852 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1002 _68158 _68159 _68156 _68157) = (term1003 _68158 _68159 _68156 _68157).
Proof. exact (@lem5211851 (_68156 = _68158) (term1001 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5211853 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : term1003 _68158 _68159 _68156 _68157.
Proof. exact (EQ_MP (@lem5211852 _68158 _68159 _68156 _68157) (@lem5211849 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5211917 (x : real) (y : real) (z : real) : term1004 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem5211923 (_67931 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (x' _67931) = (term866 x'' _67931).
Proof. exact (proj1 (@lem5210284 _67931 x'' s x' h1)). Qed.
Lemma lem5211924 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (term1005 x' b) = (term1006 x'' b).
Proof. exact (@lem5211923 (@I (real -> real) real_neg b) x'' s x' h1). Qed.
Lemma lem5211925 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1007 x' x'' b.
Proof. exact (fun h0 : term1008 x' x'' b => @lem5211924 b x'' s x' h1). Qed.
Lemma lem5211927 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5211928 (x' : real -> real) (x'' : real -> real) (b : real) : (term1007 x' x'' b) = ((term1005 x' b) = (term1006 x'' b)).
Proof. exact (@lem5211927 ((term1005 x' b) = (term1006 x'' b))). Qed.
Lemma lem5211929 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (term1005 x' b) = (term1006 x'' b).
Proof. exact (EQ_MP (@lem5211928 x' x'' b) (@lem5211925 b x'' s x' h1)). Qed.
Lemma lem5211931 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5211932 (x' : real -> real) (b : real) : (term1005 x' b) = (term1005 x' b).
Proof. exact (@lem5211931 (term1005 x' b)). Qed.
Lemma lem5211933 (x' : real -> real) (b : real) : term1009 x' b.
Proof. exact (fun h0 : term1010 x' b => @lem5211932 x' b). Qed.
Lemma lem5211935 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5211936 (x' : real -> real) (b : real) : (term1009 x' b) = ((term1005 x' b) = (term1005 x' b)).
Proof. exact (@lem5211935 ((term1005 x' b) = (term1005 x' b))). Qed.
Lemma lem5211937 (x' : real -> real) (b : real) : (term1005 x' b) = (term1005 x' b).
Proof. exact (EQ_MP (@lem5211936 x' b) (@lem5211933 x' b)). Qed.
Lemma lem5211955 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5211956 (y : real) (x : real) (z : real) : (term1011 x y z) = (term1012 y x z).
Proof. exact (@lem5211955 (y = z) (term1013 x z)). Qed.
Lemma lem5211966 (x : real) (y : real) : (term1014 x y) = (term1014 x y).
Proof. exact (eq_refl (term1014 x y)). Qed.
Lemma lem5211967 (y : real) (x : real) (z : real) : (term1004 x y z) = (term1015 y x z).
Proof. exact (MK_COMB (@lem5211966 x y) (@lem5211956 y x z)). Qed.
Lemma lem5211971 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5211972 (y : real) (x : real) (z : real) : (term1015 y x z) = (term1016 y x z).
Proof. exact (@lem5211971 (y = z) (term1013 x y) (term1013 x z)). Qed.
Lemma lem5211994 (y : real) (x : real) (z : real) : (term1004 x y z) = (term1016 y x z).
Proof. exact (TRANS (@lem5211967 y x z) (@lem5211972 y x z)). Qed.
Lemma lem5211995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5211996 (y : real) (x : real) (z : real) : (term1017 x y z) = (term1018 y x z).
Proof. exact (MK_COMB (@lem5211995) (@lem5211994 y x z)). Qed.
Lemma lem5212018 (y : real) (x : real) (z : real) : (term1016 y x z) = (term1016 y x z).
Proof. exact (eq_refl (term1016 y x z)). Qed.
Lemma lem5212019 (y : real) (x : real) (z : real) : ((term1004 x y z) = (term1016 y x z)) = ((term1016 y x z) = (term1016 y x z)).
Proof. exact (MK_COMB (@lem5211996 y x z) (@lem5212018 y x z)). Qed.
Lemma lem5212021 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5212022 (x : Prop) : (x = x) = True.
Proof. exact (@lem5212021 Prop x). Qed.
Lemma lem5212023 (y : real) (x : real) (z : real) : ((term1016 y x z) = (term1016 y x z)) = True.
Proof. exact (@lem5212022 (term1016 y x z)). Qed.
Lemma lem5212024 (y : real) (x : real) (z : real) : ((term1004 x y z) = (term1016 y x z)) = True.
Proof. exact (TRANS (@lem5212019 y x z) (@lem5212023 y x z)). Qed.
Lemma lem5212025 (y : real) (x : real) (z : real) : True = ((term1004 x y z) = (term1016 y x z)).
Proof. exact (SYM (@lem5212024 y x z)). Qed.
Lemma lem5212026 (y : real) (x : real) (z : real) : (term1004 x y z) = (term1016 y x z).
Proof. exact (EQ_MP (@lem5212025 y x z) (@lem0)). Qed.
Lemma lem5212027 (y : real) (x : real) (z : real) : term1016 y x z.
Proof. exact (EQ_MP (@lem5212026 y x z) (@lem5211917 x y z)). Qed.
Lemma lem5212029 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5212030 (x : real) (y : real) (z : real) : (term1016 y x z) = (term1020 x y z).
Proof. exact (@lem5212029 (term1021 y x z) (y = z)). Qed.
Lemma lem5212032 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5212033 (y : real) (x : real) (z : real) : (term1024 y x z) = (term1025 y x z).
Proof. exact (@lem5212032 (term1013 x y) (term1013 x z)). Qed.
Lemma lem5212035 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212036 (x : real) (y : real) : (term1027 x y) = (x = y).
Proof. exact (@lem5212035 (x = y)). Qed.
Lemma lem5212037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5212038 (x : real) (y : real) : (term1028 x y) = (term1029 x y).
Proof. exact (MK_COMB (@lem5212037) (@lem5212036 x y)). Qed.
Lemma lem5212040 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212041 (x : real) (z : real) : (term1027 x z) = (x = z).
Proof. exact (@lem5212040 (x = z)). Qed.
Lemma lem5212042 (y : real) (x : real) (z : real) : (term1025 y x z) = (term1030 y x z).
Proof. exact (MK_COMB (@lem5212038 x y) (@lem5212041 x z)). Qed.
Lemma lem5212043 (y : real) (x : real) (z : real) : (term1024 y x z) = (term1030 y x z).
Proof. exact (TRANS (@lem5212033 y x z) (@lem5212042 y x z)). Qed.
Lemma lem5212044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5212045 (y : real) (x : real) (z : real) : (term1031 y x z) = (term1032 y x z).
Proof. exact (MK_COMB (@lem5212044) (@lem5212043 y x z)). Qed.
Lemma lem5212046 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5212047 (x : real) (y : real) (z : real) : (term1020 x y z) = (term1033 x y z).
Proof. exact (MK_COMB (@lem5212045 y x z) (@lem5212046 y z)). Qed.
Lemma lem5212048 (x : real) (y : real) (z : real) : (term1016 y x z) = (term1033 x y z).
Proof. exact (TRANS (@lem5212030 x y z) (@lem5212047 x y z)). Qed.
Lemma lem5212050 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1034 x'' x' b.
Proof. exact (conj (@lem5211929 b x'' s x' h1) (@lem5211937 x' b)). Qed.
Lemma lem5212052 (x : real) (y : real) (z : real) : term1033 x y z.
Proof. exact (EQ_MP (@lem5212048 x y z) (@lem5212027 y x z)). Qed.
Lemma lem5212053 (x'' : real -> real) (x' : real -> real) (b : real) : term1035 x'' x' b.
Proof. exact (@lem5212052 (term1005 x' b) (term1006 x'' b) (term1005 x' b)). Qed.
Lemma lem5212056 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (term1006 x'' b) = (term1005 x' b).
Proof. exact (@lem5212053 x'' x' b (@lem5212050 b x'' s x' h1)). Qed.
Lemma lem5212057 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1036 x'' x' b.
Proof. exact (fun h0 : term1037 x'' x' b => @lem5212056 b x'' s x' h1). Qed.
Lemma lem5212059 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212060 (x'' : real -> real) (x' : real -> real) (b : real) : (term1036 x'' x' b) = ((term1006 x'' b) = (term1005 x' b)).
Proof. exact (@lem5212059 ((term1006 x'' b) = (term1005 x' b))). Qed.
Lemma lem5212061 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (term1006 x'' b) = (term1005 x' b).
Proof. exact (EQ_MP (@lem5212060 x'' x' b) (@lem5212057 b x'' s x' h1)). Qed.
Lemma lem5212063 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5212064 (b : real) : (@I (real -> real) real_neg b) = (@I (real -> real) real_neg b).
Proof. exact (@lem5212063 (@I (real -> real) real_neg b)). Qed.
Lemma lem5212065 (b : real) : term1038 b.
Proof. exact (fun h0 : term1039 b => @lem5212064 b). Qed.
Lemma lem5212067 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212068 (b : real) : (term1038 b) = ((@I (real -> real) real_neg b) = (@I (real -> real) real_neg b)).
Proof. exact (@lem5212067 ((@I (real -> real) real_neg b) = (@I (real -> real) real_neg b))). Qed.
Lemma lem5212069 (b : real) : (@I (real -> real) real_neg b) = (@I (real -> real) real_neg b).
Proof. exact (EQ_MP (@lem5212068 b) (@lem5212065 b)). Qed.
Lemma lem5212071 (_67931 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term864 x'' _67931 s.
Proof. exact (proj2 (@lem5210284 _67931 x'' s x' h1)). Qed.
Lemma lem5212072 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1040 x'' b s.
Proof. exact (@lem5212071 (@I (real -> real) real_neg b) x'' s x' h1). Qed.
Lemma lem5212073 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1041 x'' b s.
Proof. exact (fun h0 : term1042 x'' b s => @lem5212072 b x'' s x' h1). Qed.
Lemma lem5212075 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212076 (x'' : real -> real) (b : real) (s : real -> Prop) : (term1041 x'' b s) = (term1040 x'' b s).
Proof. exact (@lem5212075 (term1040 x'' b s)). Qed.
Lemma lem5212077 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1040 x'' b s.
Proof. exact (EQ_MP (@lem5212076 x'' b s) (@lem5212073 b x'' s x' h1)). Qed.
Lemma lem5212083 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5212084 (b : real) (_67922 : real) (s : real -> Prop) : (term231 s b _67922) = (term1043 b _67922 s).
Proof. exact (@lem5212083 (real_le b _67922) (term724 _67922 s)). Qed.
Lemma lem5212090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5212091 (b : real) (_67922 : real) (s : real -> Prop) : (term1044 s b _67922) = (term1045 b _67922 s).
Proof. exact (MK_COMB (@lem5212090) (@lem5212084 b _67922 s)). Qed.
Lemma lem5212097 (b : real) (_67922 : real) (s : real -> Prop) : (term1043 b _67922 s) = (term1043 b _67922 s).
Proof. exact (eq_refl (term1043 b _67922 s)). Qed.
Lemma lem5212098 (b : real) (_67922 : real) (s : real -> Prop) : ((term231 s b _67922) = (term1043 b _67922 s)) = ((term1043 b _67922 s) = (term1043 b _67922 s)).
Proof. exact (MK_COMB (@lem5212091 b _67922 s) (@lem5212097 b _67922 s)). Qed.
Lemma lem5212100 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5212101 (x : Prop) : (x = x) = True.
Proof. exact (@lem5212100 Prop x). Qed.
Lemma lem5212102 (b : real) (_67922 : real) (s : real -> Prop) : ((term1043 b _67922 s) = (term1043 b _67922 s)) = True.
Proof. exact (@lem5212101 (term1043 b _67922 s)). Qed.
Lemma lem5212103 (b : real) (_67922 : real) (s : real -> Prop) : ((term231 s b _67922) = (term1043 b _67922 s)) = True.
Proof. exact (TRANS (@lem5212098 b _67922 s) (@lem5212102 b _67922 s)). Qed.
Lemma lem5212104 (b : real) (_67922 : real) (s : real -> Prop) : True = ((term231 s b _67922) = (term1043 b _67922 s)).
Proof. exact (SYM (@lem5212103 b _67922 s)). Qed.
Lemma lem5212105 (b : real) (_67922 : real) (s : real -> Prop) : (term231 s b _67922) = (term1043 b _67922 s).
Proof. exact (EQ_MP (@lem5212104 b _67922 s) (@lem0)). Qed.
Lemma lem5212106 (_67922 : real) (s : real -> Prop) (b : real) (h1 : term44 s b) : term1043 b _67922 s.
Proof. exact (EQ_MP (@lem5212105 b _67922 s) (@lem5210831 _67922 s b h1)). Qed.
Lemma lem5212108 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5212109 (s : real -> Prop) (b : real) (_67922 : real) : (term1043 b _67922 s) = (term1046 s b _67922).
Proof. exact (@lem5212108 (term724 _67922 s) (real_le b _67922)). Qed.
Lemma lem5212111 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212112 (_67922 : real) (s : real -> Prop) : (term1047 _67922 s) = (@IN real _67922 s).
Proof. exact (@lem5212111 (@IN real _67922 s)). Qed.
Lemma lem5212113 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5212114 (_67922 : real) (s : real -> Prop) : (term1048 _67922 s) = (term49 _67922 s).
Proof. exact (MK_COMB (@lem5212113) (@lem5212112 _67922 s)). Qed.
Lemma lem5212115 (b : real) (_67922 : real) : (real_le b _67922) = (real_le b _67922).
Proof. exact (eq_refl (real_le b _67922)). Qed.
Lemma lem5212116 (s : real -> Prop) (b : real) (_67922 : real) : (term1046 s b _67922) = (term75 s b _67922).
Proof. exact (MK_COMB (@lem5212114 _67922 s) (@lem5212115 b _67922)). Qed.
Lemma lem5212117 (s : real -> Prop) (b : real) (_67922 : real) : (term1043 b _67922 s) = (term75 s b _67922).
Proof. exact (TRANS (@lem5212109 s b _67922) (@lem5212116 s b _67922)). Qed.
Lemma lem5212120 (_67922 : real) (s : real -> Prop) (b : real) (h1 : term44 s b) : term75 s b _67922.
Proof. exact (EQ_MP (@lem5212117 s b _67922) (@lem5212106 _67922 s b h1)). Qed.
Lemma lem5212121 (x'' : real -> real) (s : real -> Prop) (b : real) (h1 : term44 s b) : term1049 s x'' b.
Proof. exact (@lem5212120 (term1005 x'' b) s b h1). Qed.
Lemma lem5212124 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term894 x'' s x') (h2 : term44 s b) : term1050 x'' b.
Proof. exact (@lem5212121 x'' s b h2 (@lem5212077 b x'' s x' h1)). Qed.
Lemma lem5212125 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term894 x'' s x') (h2 : term44 s b) : term1051 x'' b.
Proof. exact (fun h0 : term1052 x'' b => @lem5212124 x'' x' s b h1 h2). Qed.
Lemma lem5212127 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212128 (x'' : real -> real) (b : real) : (term1051 x'' b) = (term1050 x'' b).
Proof. exact (@lem5212127 (term1050 x'' b)). Qed.
Lemma lem5212129 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term894 x'' s x') (h2 : term44 s b) : term1050 x'' b.
Proof. exact (EQ_MP (@lem5212128 x'' b) (@lem5212125 x'' x' s b h1 h2)). Qed.
Lemma lem5212131 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5212132 (_67927 : real) (_67928 : real) : (term835 _67928 _67927) = (term1053 _67927 _67928).
Proof. exact (@lem5212131 (term252 _67928 _67927) (term823 _67927 _67928)). Qed.
Lemma lem5212134 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212135 (_67928 : real) (_67927 : real) : (term1054 _67928 _67927) = (real_le _67928 _67927).
Proof. exact (@lem5212134 (real_le _67928 _67927)). Qed.
Lemma lem5212136 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5212137 (_67928 : real) (_67927 : real) : (term1055 _67928 _67927) = (term1056 _67928 _67927).
Proof. exact (MK_COMB (@lem5212136) (@lem5212135 _67928 _67927)). Qed.
Lemma lem5212138 (_67927 : real) (_67928 : real) : (term823 _67927 _67928) = (term823 _67927 _67928).
Proof. exact (eq_refl (term823 _67927 _67928)). Qed.
Lemma lem5212139 (_67927 : real) (_67928 : real) : (term1053 _67927 _67928) = (term1057 _67927 _67928).
Proof. exact (MK_COMB (@lem5212137 _67928 _67927) (@lem5212138 _67927 _67928)). Qed.
Lemma lem5212140 (_67927 : real) (_67928 : real) : (term835 _67928 _67927) = (term1057 _67927 _67928).
Proof. exact (TRANS (@lem5212132 _67927 _67928) (@lem5212139 _67927 _67928)). Qed.
Lemma lem5212143 (_67927 : real) (_67928 : real) (h1 : term35) : term1057 _67927 _67928.
Proof. exact (EQ_MP (@lem5212140 _67927 _67928) (@lem5210887 _67928 _67927 h1)). Qed.
Lemma lem5212144 (x'' : real -> real) (b : real) (h1 : term35) : term1058 x'' b.
Proof. exact (@lem5212143 (term1005 x'' b) b h1). Qed.
Lemma lem5212147 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : term1059 x'' b.
Proof. exact (@lem5212144 x'' b h1 (@lem5212129 x'' x' s b h2 h3)). Qed.
Lemma lem5212148 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : term1060 x'' b.
Proof. exact (fun h0 : term1061 x'' b => @lem5212147 x'' x' s b h1 h2 h3). Qed.
Lemma lem5212150 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212151 (x'' : real -> real) (b : real) : (term1060 x'' b) = (term1059 x'' b).
Proof. exact (@lem5212150 (term1059 x'' b)). Qed.
Lemma lem5212152 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : term1059 x'' b.
Proof. exact (EQ_MP (@lem5212151 x'' b) (@lem5212148 x'' x' s b h1 h2 h3)). Qed.
Lemma lem5212170 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5212171 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1001 _68158 _68159 _68156 _68157) = (term1062 _68158 _68159 _68156 _68157).
Proof. exact (@lem5212170 (real_le _68158 _68159) (term1013 _68157 _68159) (term252 _68156 _68157)). Qed.
Lemma lem5212189 (_68156 : real) (_68158 : real) : (term1014 _68156 _68158) = (term1014 _68156 _68158).
Proof. exact (eq_refl (term1014 _68156 _68158)). Qed.
Lemma lem5212190 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1003 _68158 _68159 _68156 _68157) = (term1063 _68158 _68159 _68156 _68157).
Proof. exact (MK_COMB (@lem5212189 _68156 _68158) (@lem5212171 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212194 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5212195 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1063 _68158 _68159 _68156 _68157) = (term1064 _68158 _68159 _68156 _68157).
Proof. exact (@lem5212194 (real_le _68158 _68159) (term1013 _68156 _68158) (term1065 _68159 _68156 _68157)). Qed.
Lemma lem5212225 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1003 _68158 _68159 _68156 _68157) = (term1064 _68158 _68159 _68156 _68157).
Proof. exact (TRANS (@lem5212190 _68158 _68159 _68156 _68157) (@lem5212195 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5212227 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1066 _68158 _68159 _68156 _68157) = (term1067 _68158 _68159 _68156 _68157).
Proof. exact (MK_COMB (@lem5212226) (@lem5212225 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212257 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1064 _68158 _68159 _68156 _68157) = (term1064 _68158 _68159 _68156 _68157).
Proof. exact (eq_refl (term1064 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212258 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : ((term1003 _68158 _68159 _68156 _68157) = (term1064 _68158 _68159 _68156 _68157)) = ((term1064 _68158 _68159 _68156 _68157) = (term1064 _68158 _68159 _68156 _68157)).
Proof. exact (MK_COMB (@lem5212227 _68158 _68159 _68156 _68157) (@lem5212257 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212260 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5212261 (x : Prop) : (x = x) = True.
Proof. exact (@lem5212260 Prop x). Qed.
Lemma lem5212262 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : ((term1064 _68158 _68159 _68156 _68157) = (term1064 _68158 _68159 _68156 _68157)) = True.
Proof. exact (@lem5212261 (term1064 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212263 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : ((term1003 _68158 _68159 _68156 _68157) = (term1064 _68158 _68159 _68156 _68157)) = True.
Proof. exact (TRANS (@lem5212258 _68158 _68159 _68156 _68157) (@lem5212262 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212264 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : True = ((term1003 _68158 _68159 _68156 _68157) = (term1064 _68158 _68159 _68156 _68157)).
Proof. exact (SYM (@lem5212263 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212265 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1003 _68158 _68159 _68156 _68157) = (term1064 _68158 _68159 _68156 _68157).
Proof. exact (EQ_MP (@lem5212264 _68158 _68159 _68156 _68157) (@lem0)). Qed.
Lemma lem5212266 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : term1064 _68158 _68159 _68156 _68157.
Proof. exact (EQ_MP (@lem5212265 _68158 _68159 _68156 _68157) (@lem5211853 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212268 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5212269 (_68156 : real) (_68157 : real) (_68158 : real) (_68159 : real) : (term1064 _68158 _68159 _68156 _68157) = (term1068 _68156 _68157 _68158 _68159).
Proof. exact (@lem5212268 (term1069 _68158 _68159 _68156 _68157) (real_le _68158 _68159)). Qed.
Lemma lem5212271 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5212272 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1070 _68158 _68159 _68156 _68157) = (term1071 _68158 _68159 _68156 _68157).
Proof. exact (@lem5212271 (term1013 _68156 _68158) (term1065 _68159 _68156 _68157)). Qed.
Lemma lem5212274 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212275 (_68156 : real) (_68158 : real) : (term1027 _68156 _68158) = (_68156 = _68158).
Proof. exact (@lem5212274 (_68156 = _68158)). Qed.
Lemma lem5212276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5212277 (_68156 : real) (_68158 : real) : (term1028 _68156 _68158) = (term1029 _68156 _68158).
Proof. exact (MK_COMB (@lem5212276) (@lem5212275 _68156 _68158)). Qed.
Lemma lem5212279 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5212280 (_68159 : real) (_68156 : real) (_68157 : real) : (term1072 _68159 _68156 _68157) = (term1073 _68159 _68156 _68157).
Proof. exact (@lem5212279 (term1013 _68157 _68159) (term252 _68156 _68157)). Qed.
Lemma lem5212282 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212283 (_68157 : real) (_68159 : real) : (term1027 _68157 _68159) = (_68157 = _68159).
Proof. exact (@lem5212282 (_68157 = _68159)). Qed.
Lemma lem5212284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5212285 (_68157 : real) (_68159 : real) : (term1028 _68157 _68159) = (term1029 _68157 _68159).
Proof. exact (MK_COMB (@lem5212284) (@lem5212283 _68157 _68159)). Qed.
Lemma lem5212287 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212288 (_68156 : real) (_68157 : real) : (term1054 _68156 _68157) = (real_le _68156 _68157).
Proof. exact (@lem5212287 (real_le _68156 _68157)). Qed.
Lemma lem5212289 (_68159 : real) (_68156 : real) (_68157 : real) : (term1073 _68159 _68156 _68157) = (term1074 _68159 _68156 _68157).
Proof. exact (MK_COMB (@lem5212285 _68157 _68159) (@lem5212288 _68156 _68157)). Qed.
Lemma lem5212290 (_68159 : real) (_68156 : real) (_68157 : real) : (term1072 _68159 _68156 _68157) = (term1074 _68159 _68156 _68157).
Proof. exact (TRANS (@lem5212280 _68159 _68156 _68157) (@lem5212289 _68159 _68156 _68157)). Qed.
Lemma lem5212291 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1071 _68158 _68159 _68156 _68157) = (term1075 _68158 _68159 _68156 _68157).
Proof. exact (MK_COMB (@lem5212277 _68156 _68158) (@lem5212290 _68159 _68156 _68157)). Qed.
Lemma lem5212292 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1070 _68158 _68159 _68156 _68157) = (term1075 _68158 _68159 _68156 _68157).
Proof. exact (TRANS (@lem5212272 _68158 _68159 _68156 _68157) (@lem5212291 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212293 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5212294 (_68158 : real) (_68159 : real) (_68156 : real) (_68157 : real) : (term1076 _68158 _68159 _68156 _68157) = (term1077 _68158 _68159 _68156 _68157).
Proof. exact (MK_COMB (@lem5212293) (@lem5212292 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212295 (_68158 : real) (_68159 : real) : (real_le _68158 _68159) = (real_le _68158 _68159).
Proof. exact (eq_refl (real_le _68158 _68159)). Qed.
Lemma lem5212296 (_68156 : real) (_68157 : real) (_68158 : real) (_68159 : real) : (term1068 _68156 _68157 _68158 _68159) = (term1078 _68156 _68157 _68158 _68159).
Proof. exact (MK_COMB (@lem5212294 _68158 _68159 _68156 _68157) (@lem5212295 _68158 _68159)). Qed.
Lemma lem5212297 (_68156 : real) (_68157 : real) (_68158 : real) (_68159 : real) : (term1064 _68158 _68159 _68156 _68157) = (term1078 _68156 _68157 _68158 _68159).
Proof. exact (TRANS (@lem5212269 _68156 _68157 _68158 _68159) (@lem5212296 _68156 _68157 _68158 _68159)). Qed.
Lemma lem5212299 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : term1079 x'' b.
Proof. exact (conj (@lem5212069 b) (@lem5212152 x'' x' s b h1 h2 h3)). Qed.
Lemma lem5212300 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : term1080 x' x'' b.
Proof. exact (conj (@lem5212061 b x'' s x' h2) (@lem5212299 x'' x' s b h1 h2 h3)). Qed.
Lemma lem5212302 (_68156 : real) (_68157 : real) (_68158 : real) (_68159 : real) : term1078 _68156 _68157 _68158 _68159.
Proof. exact (EQ_MP (@lem5212297 _68156 _68157 _68158 _68159) (@lem5212266 _68158 _68159 _68156 _68157)). Qed.
Lemma lem5212303 (x'' : real -> real) (x' : real -> real) (b : real) : term1081 x'' x' b.
Proof. exact (@lem5212302 (term1006 x'' b) (@I (real -> real) real_neg b) (term1005 x' b) (@I (real -> real) real_neg b)). Qed.
Lemma lem5212306 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : term1082 x' b.
Proof. exact (@lem5212303 x'' x' b (@lem5212300 x'' x' s b h1 h2 h3)). Qed.
Lemma lem5212307 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : term1083 x' b.
Proof. exact (fun h0 : term1084 x' b => @lem5212306 x'' x' s b h1 h2 h3). Qed.
Lemma lem5212309 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212310 (x' : real -> real) (b : real) : (term1083 x' b) = (term1082 x' b).
Proof. exact (@lem5212309 (term1082 x' b)). Qed.
Lemma lem5212311 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : term1082 x' b.
Proof. exact (EQ_MP (@lem5212310 x' b) (@lem5212307 x'' x' s b h1 h2 h3)). Qed.
Lemma lem5212314 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5212316 (x' : real -> real) (_67931 : real) : (term863 x' _67931) = (term1085 x' _67931).
Proof. exact (@lem5212314 (term1086 x' _67931)). Qed.
Lemma lem5212319 (_67931 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1085 x' _67931.
Proof. exact (EQ_MP (@lem5212316 x' _67931) (@lem5210942 _67931 x'' s x' h1)). Qed.
Lemma lem5212320 (b : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1087 x' b.
Proof. exact (@lem5212319 (@I (real -> real) real_neg b) x'' s x' h1). Qed.
Lemma lem5212323 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : False.
Proof. exact (@lem5212320 b x'' s x' h2 (@lem5212311 x'' x' s b h1 h2 h3)). Qed.
Lemma lem5212324 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : term995.
Proof. exact (fun h0 : ~ False => @lem5212323 x'' x' s b h1 h2 h3). Qed.
Lemma lem5212326 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212327 : term995 = False.
Proof. exact (@lem5212326 False). Qed.
Lemma lem5212436 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5212437 (b' : real) : (@I (real -> real) real_neg b') = (@I (real -> real) real_neg b').
Proof. exact (@lem5212436 (@I (real -> real) real_neg b')). Qed.
Lemma lem5212438 (b' : real) : term1038 b'.
Proof. exact (fun h0 : term1039 b' => @lem5212437 b'). Qed.
Lemma lem5212440 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212441 (b' : real) : (term1038 b') = ((@I (real -> real) real_neg b') = (@I (real -> real) real_neg b')).
Proof. exact (@lem5212440 ((@I (real -> real) real_neg b') = (@I (real -> real) real_neg b'))). Qed.
Lemma lem5212442 (b' : real) : (@I (real -> real) real_neg b') = (@I (real -> real) real_neg b').
Proof. exact (EQ_MP (@lem5212441 b') (@lem5212438 b')). Qed.
Lemma lem5212444 (s : real -> Prop) (b' : real) (a : real) (h1 : term860 s b' a) : @IN real b' s.
Proof. exact (proj1 (@lem5209069 s b' a h1)). Qed.
Lemma lem5212445 (s : real -> Prop) (b' : real) (a : real) (h1 : term860 s b' a) : term987 b' s.
Proof. exact (fun h0 : term724 b' s => @lem5212444 s b' a h1). Qed.
Lemma lem5212447 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212448 (b' : real) (s : real -> Prop) : (term987 b' s) = (@IN real b' s).
Proof. exact (@lem5212447 (@IN real b' s)). Qed.
Lemma lem5212449 (s : real -> Prop) (b' : real) (a : real) (h1 : term860 s b' a) : @IN real b' s.
Proof. exact (EQ_MP (@lem5212448 b' s) (@lem5212445 s b' a h1)). Qed.
Lemma lem5212467 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5212468 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term1088 _67942 _67941 s) = (term1089 _67941 _67942 s).
Proof. exact (@lem5212467 (term120 _67941 s) (term724 _67942 s)). Qed.
Lemma lem5212474 (_67941 : real) (_67942 : real) : (term883 _67941 _67942) = (term883 _67941 _67942).
Proof. exact (eq_refl (term883 _67941 _67942)). Qed.
Lemma lem5212475 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term956 _67942 _67941 s) = (term1090 _67941 _67942 s).
Proof. exact (MK_COMB (@lem5212474 _67941 _67942) (@lem5212468 _67941 _67942 s)). Qed.
Lemma lem5212479 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5212480 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term1090 _67941 _67942 s) = (term1091 _67941 _67942 s).
Proof. exact (@lem5212479 (term120 _67941 s) (term881 _67941 _67942) (term724 _67942 s)). Qed.
Lemma lem5212498 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term956 _67942 _67941 s) = (term1091 _67941 _67942 s).
Proof. exact (TRANS (@lem5212475 _67941 _67942 s) (@lem5212480 _67941 _67942 s)). Qed.
Lemma lem5212499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5212500 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term1092 _67942 _67941 s) = (term1093 _67941 _67942 s).
Proof. exact (MK_COMB (@lem5212499) (@lem5212498 _67941 _67942 s)). Qed.
Lemma lem5212518 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term1091 _67941 _67942 s) = (term1091 _67941 _67942 s).
Proof. exact (eq_refl (term1091 _67941 _67942 s)). Qed.
Lemma lem5212519 (_67941 : real) (_67942 : real) (s : real -> Prop) : ((term956 _67942 _67941 s) = (term1091 _67941 _67942 s)) = ((term1091 _67941 _67942 s) = (term1091 _67941 _67942 s)).
Proof. exact (MK_COMB (@lem5212500 _67941 _67942 s) (@lem5212518 _67941 _67942 s)). Qed.
Lemma lem5212521 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5212522 (x : Prop) : (x = x) = True.
Proof. exact (@lem5212521 Prop x). Qed.
Lemma lem5212523 (_67941 : real) (_67942 : real) (s : real -> Prop) : ((term1091 _67941 _67942 s) = (term1091 _67941 _67942 s)) = True.
Proof. exact (@lem5212522 (term1091 _67941 _67942 s)). Qed.
Lemma lem5212524 (_67941 : real) (_67942 : real) (s : real -> Prop) : ((term956 _67942 _67941 s) = (term1091 _67941 _67942 s)) = True.
Proof. exact (TRANS (@lem5212519 _67941 _67942 s) (@lem5212523 _67941 _67942 s)). Qed.
Lemma lem5212525 (_67941 : real) (_67942 : real) (s : real -> Prop) : True = ((term956 _67942 _67941 s) = (term1091 _67941 _67942 s)).
Proof. exact (SYM (@lem5212524 _67941 _67942 s)). Qed.
Lemma lem5212526 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term956 _67942 _67941 s) = (term1091 _67941 _67942 s).
Proof. exact (EQ_MP (@lem5212525 _67941 _67942 s) (@lem0)). Qed.
Lemma lem5212527 (_67941 : real) (_67942 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1091 _67941 _67942 s.
Proof. exact (EQ_MP (@lem5212526 _67941 _67942 s) (@lem5211123 _67942 _67941 x'' x' s a h1 h2)). Qed.
Lemma lem5212529 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5212530 (_67942 : real) (_67941 : real) (s : real -> Prop) : (term1091 _67941 _67942 s) = (term1094 _67942 _67941 s).
Proof. exact (@lem5212529 (term884 _67941 _67942 s) (term120 _67941 s)). Qed.
Lemma lem5212532 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5212533 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term1095 _67941 _67942 s) = (term1096 _67941 _67942 s).
Proof. exact (@lem5212532 (term881 _67941 _67942) (term724 _67942 s)). Qed.
Lemma lem5212535 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212536 (_67941 : real) (_67942 : real) : (term1097 _67941 _67942) = (_67941 = (@I (real -> real) real_neg _67942)).
Proof. exact (@lem5212535 (_67941 = (@I (real -> real) real_neg _67942))). Qed.
Lemma lem5212537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5212538 (_67941 : real) (_67942 : real) : (term1098 _67941 _67942) = (term1099 _67941 _67942).
Proof. exact (MK_COMB (@lem5212537) (@lem5212536 _67941 _67942)). Qed.
Lemma lem5212540 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212541 (_67942 : real) (s : real -> Prop) : (term1047 _67942 s) = (@IN real _67942 s).
Proof. exact (@lem5212540 (@IN real _67942 s)). Qed.
Lemma lem5212542 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term1096 _67941 _67942 s) = (term992 _67941 _67942 s).
Proof. exact (MK_COMB (@lem5212538 _67941 _67942) (@lem5212541 _67942 s)). Qed.
Lemma lem5212543 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term1095 _67941 _67942 s) = (term992 _67941 _67942 s).
Proof. exact (TRANS (@lem5212533 _67941 _67942 s) (@lem5212542 _67941 _67942 s)). Qed.
Lemma lem5212544 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5212545 (_67941 : real) (_67942 : real) (s : real -> Prop) : (term1100 _67941 _67942 s) = (term1101 _67941 _67942 s).
Proof. exact (MK_COMB (@lem5212544) (@lem5212543 _67941 _67942 s)). Qed.
Lemma lem5212546 (_67941 : real) (s : real -> Prop) : (term120 _67941 s) = (term120 _67941 s).
Proof. exact (eq_refl (term120 _67941 s)). Qed.
Lemma lem5212547 (_67942 : real) (_67941 : real) (s : real -> Prop) : (term1094 _67942 _67941 s) = (term1102 _67942 _67941 s).
Proof. exact (MK_COMB (@lem5212545 _67941 _67942 s) (@lem5212546 _67941 s)). Qed.
Lemma lem5212548 (_67942 : real) (_67941 : real) (s : real -> Prop) : (term1091 _67941 _67942 s) = (term1102 _67942 _67941 s).
Proof. exact (TRANS (@lem5212530 _67942 _67941 s) (@lem5212547 _67942 _67941 s)). Qed.
Lemma lem5212550 (s : real -> Prop) (b' : real) (a : real) (h1 : term860 s b' a) : term1103 b' s.
Proof. exact (conj (@lem5212442 b') (@lem5212449 s b' a h1)). Qed.
Lemma lem5212552 (_67942 : real) (_67941 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1102 _67942 _67941 s.
Proof. exact (EQ_MP (@lem5212548 _67942 _67941 s) (@lem5212527 _67941 _67942 x'' x' s a h1 h2)). Qed.
Lemma lem5212553 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1104 b' s.
Proof. exact (@lem5212552 b' (@I (real -> real) real_neg b') x'' x' s a h1 h2). Qed.
Lemma lem5212556 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : term1105 b' s.
Proof. exact (@lem5212553 b' x'' x' s a h1 h3 (@lem5212550 s b' a h2)). Qed.
Lemma lem5212557 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : term1106 b' s.
Proof. exact (fun h0 : term950 b' s => @lem5212556 x'' x' b' s a h1 h2 h3). Qed.
Lemma lem5212559 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212560 (b' : real) (s : real -> Prop) : (term1106 b' s) = (term1105 b' s).
Proof. exact (@lem5212559 (term1105 b' s)). Qed.
Lemma lem5212561 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : term1105 b' s.
Proof. exact (EQ_MP (@lem5212560 b' s) (@lem5212557 x'' x' b' s a h1 h2 h3)). Qed.
Lemma lem5212564 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5212566 (b' : real) (s : real -> Prop) : (term950 b' s) = (term1107 b' s).
Proof. exact (@lem5212564 (term1105 b' s)). Qed.
Lemma lem5212569 (b' : real) (s : real -> Prop) (a : real) (h1 : term860 s b' a) (h2 : (term21 s) = a) : term1107 b' s.
Proof. exact (EQ_MP (@lem5212566 b' s) (@lem5211110 b' s a h1 h2)). Qed.
Lemma lem5212572 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : False.
Proof. exact (@lem5212569 b' s a h2 h3 (@lem5212561 x'' x' b' s a h1 h2 h3)). Qed.
Lemma lem5212573 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : term995.
Proof. exact (fun h0 : ~ False => @lem5212572 x'' x' b' s a h1 h2 h3). Qed.
Lemma lem5212575 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212576 : term995 = False.
Proof. exact (@lem5212575 False). Qed.
Lemma lem5212669 (_67945 : real) (h1 : term196) : (term843 _67945) = _67945.
Proof. exact (EQ_MP (@lem5210179 _67945) (@lem5210178 _67945 h1)). Qed.
Lemma lem5212670 (x : type1023) (s : real -> Prop) (h1 : term196) : (term1108 x s) = (term1109 x s).
Proof. exact (@lem5212669 (term1109 x s) h1). Qed.
Lemma lem5212671 (x : type1023) (s : real -> Prop) (h1 : term196) : term1110 x s.
Proof. exact (fun h0 : term1111 x s => @lem5212670 x s h1). Qed.
Lemma lem5212673 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212674 (x : type1023) (s : real -> Prop) : (term1110 x s) = ((term1108 x s) = (term1109 x s)).
Proof. exact (@lem5212673 ((term1108 x s) = (term1109 x s))). Qed.
Lemma lem5212675 (x : type1023) (s : real -> Prop) (h1 : term196) : (term1108 x s) = (term1109 x s).
Proof. exact (EQ_MP (@lem5212674 x s) (@lem5212671 x s h1)). Qed.
Lemma lem5212688 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5212689 (_67954 : real) (_67955 : real) (s : real -> Prop) : (term1112 s _67954 _67955) = (term884 _67954 _67955 s).
Proof. exact (@lem5212688 (term881 _67954 _67955) (term724 _67955 s)). Qed.
Lemma lem5212697 (_67954 : real) (_67955 : real) (s : real -> Prop) : (term1113 _67954 _67955 s) = (term1113 _67954 _67955 s).
Proof. exact (eq_refl (term1113 _67954 _67955 s)). Qed.
Lemma lem5212698 (_67954 : real) (_67955 : real) (s : real -> Prop) : ((term884 _67954 _67955 s) = (term1112 s _67954 _67955)) = ((term884 _67954 _67955 s) = (term884 _67954 _67955 s)).
Proof. exact (MK_COMB (@lem5212697 _67954 _67955 s) (@lem5212689 _67954 _67955 s)). Qed.
Lemma lem5212700 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5212701 (x : Prop) : (x = x) = True.
Proof. exact (@lem5212700 Prop x). Qed.
Lemma lem5212702 (_67954 : real) (_67955 : real) (s : real -> Prop) : ((term884 _67954 _67955 s) = (term884 _67954 _67955 s)) = True.
Proof. exact (@lem5212701 (term884 _67954 _67955 s)). Qed.
Lemma lem5212703 (s : real -> Prop) (_67954 : real) (_67955 : real) : ((term884 _67954 _67955 s) = (term1112 s _67954 _67955)) = True.
Proof. exact (TRANS (@lem5212698 _67954 _67955 s) (@lem5212702 _67954 _67955 s)). Qed.
Lemma lem5212704 (s : real -> Prop) (_67954 : real) (_67955 : real) : True = ((term884 _67954 _67955 s) = (term1112 s _67954 _67955)).
Proof. exact (SYM (@lem5212703 s _67954 _67955)). Qed.
Lemma lem5212705 (s : real -> Prop) (_67954 : real) (_67955 : real) : (term884 _67954 _67955 s) = (term1112 s _67954 _67955).
Proof. exact (EQ_MP (@lem5212704 s _67954 _67955) (@lem0)). Qed.
Lemma lem5212706 (_67954 : real) (_67955 : real) (s : real -> Prop) (h1 : term896 s) : term1112 s _67954 _67955.
Proof. exact (EQ_MP (@lem5212705 s _67954 _67955) (@lem5211316 _67954 _67955 s h1)). Qed.
Lemma lem5212708 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5212709 (_67954 : real) (_67955 : real) (s : real -> Prop) : (term1112 s _67954 _67955) = (term1114 _67954 _67955 s).
Proof. exact (@lem5212708 (term881 _67954 _67955) (term724 _67955 s)). Qed.
Lemma lem5212711 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5212712 (_67954 : real) (_67955 : real) : (term1097 _67954 _67955) = (_67954 = (@I (real -> real) real_neg _67955)).
Proof. exact (@lem5212711 (_67954 = (@I (real -> real) real_neg _67955))). Qed.
Lemma lem5212713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5212714 (_67954 : real) (_67955 : real) : (term1115 _67954 _67955) = (term1116 _67954 _67955).
Proof. exact (MK_COMB (@lem5212713) (@lem5212712 _67954 _67955)). Qed.
Lemma lem5212715 (_67955 : real) (s : real -> Prop) : (term724 _67955 s) = (term724 _67955 s).
Proof. exact (eq_refl (term724 _67955 s)). Qed.
Lemma lem5212716 (_67954 : real) (_67955 : real) (s : real -> Prop) : (term1114 _67954 _67955 s) = (term1117 _67954 _67955 s).
Proof. exact (MK_COMB (@lem5212714 _67954 _67955) (@lem5212715 _67955 s)). Qed.
Lemma lem5212717 (_67954 : real) (_67955 : real) (s : real -> Prop) : (term1112 s _67954 _67955) = (term1117 _67954 _67955 s).
Proof. exact (TRANS (@lem5212709 _67954 _67955 s) (@lem5212716 _67954 _67955 s)). Qed.
Lemma lem5212720 (_67954 : real) (_67955 : real) (s : real -> Prop) (h1 : term896 s) : term1117 _67954 _67955 s.
Proof. exact (EQ_MP (@lem5212717 _67954 _67955 s) (@lem5212706 _67954 _67955 s h1)). Qed.
Lemma lem5212721 (x : type1023) (s : real -> Prop) (h1 : term896 s) : term1118 x s.
Proof. exact (@lem5212720 (term1108 x s) (x s) s h1). Qed.
Lemma lem5212724 (x : type1023) (s : real -> Prop) (h1 : term896 s) (h2 : term196) : term1119 x s.
Proof. exact (@lem5212721 x s h1 (@lem5212675 x s h2)). Qed.
Lemma lem5212725 (x : type1023) (s : real -> Prop) (h1 : term896 s) (h2 : term196) : term1120 x s.
Proof. exact (fun h0 : term1121 x s => @lem5212724 x s h1 h2). Qed.
Lemma lem5212727 (p : Prop) : (term1122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5212728 (x : type1023) (s : real -> Prop) : (term1120 x s) = (term1119 x s).
Proof. exact (@lem5212727 (term1121 x s)). Qed.
Lemma lem5212729 (x : type1023) (s : real -> Prop) (h1 : term896 s) (h2 : term196) : term1119 x s.
Proof. exact (EQ_MP (@lem5212728 x s) (@lem5212725 x s h1 h2)). Qed.
Lemma lem5212735 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5212736 (x : type1023) (_67946 : real -> Prop) : (term795 x _67946) = (term1123 x _67946).
Proof. exact (@lem5212735 (_67946 = (@EMPTY real)) (term1121 x _67946)). Qed.
Lemma lem5212744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5212745 (x : type1023) (_67946 : real -> Prop) : (term1124 x _67946) = (term1125 x _67946).
Proof. exact (MK_COMB (@lem5212744) (@lem5212736 x _67946)). Qed.
Lemma lem5212753 (x : type1023) (_67946 : real -> Prop) : (term1123 x _67946) = (term1123 x _67946).
Proof. exact (eq_refl (term1123 x _67946)). Qed.
Lemma lem5212754 (x : type1023) (_67946 : real -> Prop) : ((term795 x _67946) = (term1123 x _67946)) = ((term1123 x _67946) = (term1123 x _67946)).
Proof. exact (MK_COMB (@lem5212745 x _67946) (@lem5212753 x _67946)). Qed.
Lemma lem5212756 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5212757 (x : Prop) : (x = x) = True.
Proof. exact (@lem5212756 Prop x). Qed.
Lemma lem5212758 (x : type1023) (_67946 : real -> Prop) : ((term1123 x _67946) = (term1123 x _67946)) = True.
Proof. exact (@lem5212757 (term1123 x _67946)). Qed.
Lemma lem5212759 (x : type1023) (_67946 : real -> Prop) : ((term795 x _67946) = (term1123 x _67946)) = True.
Proof. exact (TRANS (@lem5212754 x _67946) (@lem5212758 x _67946)). Qed.
Lemma lem5212760 (x : type1023) (_67946 : real -> Prop) : True = ((term795 x _67946) = (term1123 x _67946)).
Proof. exact (SYM (@lem5212759 x _67946)). Qed.
Lemma lem5212761 (x : type1023) (_67946 : real -> Prop) : (term795 x _67946) = (term1123 x _67946).
Proof. exact (EQ_MP (@lem5212760 x _67946) (@lem0)). Qed.
Lemma lem5212762 (_67946 : real -> Prop) (x : type1023) (h1 : term818 x) : term1123 x _67946.
Proof. exact (EQ_MP (@lem5212761 x _67946) (@lem5211233 _67946 x h1)). Qed.
Lemma lem5212764 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5212767 (x : type1023) (_67946 : real -> Prop) : (term1123 x _67946) = (term1126 x _67946).
Proof. exact (@lem5212764 (term1121 x _67946) (_67946 = (@EMPTY real))). Qed.
Lemma lem5212770 (_67946 : real -> Prop) (x : type1023) (h1 : term818 x) : term1126 x _67946.
Proof. exact (EQ_MP (@lem5212767 x _67946) (@lem5212762 _67946 x h1)). Qed.
Lemma lem5212771 (s : real -> Prop) (x : type1023) (h1 : term818 x) : term1126 x s.
Proof. exact (@lem5212770 s x h1). Qed.
Lemma lem5212774 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term818 x) : s = (@EMPTY real).
Proof. exact (@lem5212771 s x h3 (@lem5212729 x s h1 h2)). Qed.
Lemma lem5212775 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term818 x) : term1127 s.
Proof. exact (fun h0 : term43 s => @lem5212774 s x h1 h2 h3). Qed.
Lemma lem5212777 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212778 (s : real -> Prop) : (term1127 s) = (s = (@EMPTY real)).
Proof. exact (@lem5212777 (s = (@EMPTY real))). Qed.
Lemma lem5212779 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term818 x) : s = (@EMPTY real).
Proof. exact (EQ_MP (@lem5212778 s) (@lem5212775 s x h1 h2 h3)). Qed.
Lemma lem5212782 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5212784 (s : real -> Prop) : (term43 s) = (term1128 s).
Proof. exact (@lem5212782 (s = (@EMPTY real))). Qed.
Lemma lem5212787 (s : real -> Prop) (h1 : term43 s) : term1128 s.
Proof. exact (EQ_MP (@lem5212784 s) (@lem5211191 s h1)). Qed.
Lemma lem5212790 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : False.
Proof. exact (@lem5212787 s h3 (@lem5212779 s x h1 h2 h4)). Qed.
Lemma lem5212791 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : term995.
Proof. exact (fun h0 : ~ False => @lem5212790 s x h1 h2 h3 h4). Qed.
Lemma lem5212793 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212794 : term995 = False.
Proof. exact (@lem5212793 False). Qed.
Lemma lem5212795 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : False.
Proof. exact (EQ_MP (@lem5212794) (@lem5212791 s x h1 h2 h3 h4)). Qed.
Lemma lem5212815 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5212816 (_68224 : real) (_68226 : real) (h1 : _68224 = _68226) : _68224 = _68226.
Proof. exact (h1). Qed.
Lemma lem5212817 (_68225 : real) (_68227 : real) (h1 : _68225 = _68227) : _68225 = _68227.
Proof. exact (h1). Qed.
Lemma lem5212818 (_68224 : real) (_68226 : real) (h1 : _68224 = _68226) : (real_le _68224) = (real_le _68226).
Proof. exact (MK_COMB (@lem5212815) (@lem5212816 _68224 _68226 h1)). Qed.
Lemma lem5212819 (_68224 : real) (_68226 : real) (_68225 : real) (_68227 : real) (h1 : _68224 = _68226) (h2 : _68225 = _68227) : (real_le _68224 _68225) = (real_le _68226 _68227).
Proof. exact (MK_COMB (@lem5212818 _68224 _68226 h1) (@lem5212817 _68225 _68227 h2)). Qed.
Lemma lem5212821 (b : Prop) (a : Prop) : term996 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5212822 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : term997 _68226 _68227 _68224 _68225.
Proof. exact (@lem5212821 (real_le _68226 _68227) (real_le _68224 _68225)). Qed.
Lemma lem5212823 (_68224 : real) (_68226 : real) (_68225 : real) (_68227 : real) (h1 : _68224 = _68226) (h2 : _68225 = _68227) : term998 _68226 _68227 _68224 _68225.
Proof. exact (@lem5212822 _68226 _68227 _68224 _68225 (@lem5212819 _68224 _68226 _68225 _68227 h1 h2)). Qed.
Lemma lem5212824 (_68227 : real) (_68225 : real) (_68224 : real) (_68226 : real) (h1 : _68224 = _68226) : term999 _68226 _68227 _68224 _68225.
Proof. exact (fun h0 : _68225 = _68227 => @lem5212823 _68224 _68226 _68225 _68227 h1 h0). Qed.
Lemma lem5212826 (a : Prop) (b : Prop) : (a -> b) = (term1000 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5212827 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term999 _68226 _68227 _68224 _68225) = (term1001 _68226 _68227 _68224 _68225).
Proof. exact (@lem5212826 (_68225 = _68227) (term998 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5212828 (_68227 : real) (_68225 : real) (_68224 : real) (_68226 : real) (h1 : _68224 = _68226) : term1001 _68226 _68227 _68224 _68225.
Proof. exact (EQ_MP (@lem5212827 _68226 _68227 _68224 _68225) (@lem5212824 _68227 _68225 _68224 _68226 h1)). Qed.
Lemma lem5212829 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : term1002 _68226 _68227 _68224 _68225.
Proof. exact (fun h0 : _68224 = _68226 => @lem5212828 _68227 _68225 _68224 _68226 h0). Qed.
Lemma lem5212831 (a : Prop) (b : Prop) : (a -> b) = (term1000 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5212832 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1002 _68226 _68227 _68224 _68225) = (term1003 _68226 _68227 _68224 _68225).
Proof. exact (@lem5212831 (_68224 = _68226) (term1001 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5212833 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : term1003 _68226 _68227 _68224 _68225.
Proof. exact (EQ_MP (@lem5212832 _68226 _68227 _68224 _68225) (@lem5212829 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5212897 (x : real) (y : real) (z : real) : term1004 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem5212903 (_67966 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (x' _67966) = (term866 x'' _67966).
Proof. exact (proj1 (@lem5210292 _67966 x'' s x' h1)). Qed.
Lemma lem5212904 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (term1005 x' b') = (term1006 x'' b').
Proof. exact (@lem5212903 (@I (real -> real) real_neg b') x'' s x' h1). Qed.
Lemma lem5212905 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1007 x' x'' b'.
Proof. exact (fun h0 : term1008 x' x'' b' => @lem5212904 b' x'' s x' h1). Qed.
Lemma lem5212907 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212908 (x' : real -> real) (x'' : real -> real) (b' : real) : (term1007 x' x'' b') = ((term1005 x' b') = (term1006 x'' b')).
Proof. exact (@lem5212907 ((term1005 x' b') = (term1006 x'' b'))). Qed.
Lemma lem5212909 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (term1005 x' b') = (term1006 x'' b').
Proof. exact (EQ_MP (@lem5212908 x' x'' b') (@lem5212905 b' x'' s x' h1)). Qed.
Lemma lem5212911 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5212912 (x' : real -> real) (b' : real) : (term1005 x' b') = (term1005 x' b').
Proof. exact (@lem5212911 (term1005 x' b')). Qed.
Lemma lem5212913 (x' : real -> real) (b' : real) : term1009 x' b'.
Proof. exact (fun h0 : term1010 x' b' => @lem5212912 x' b'). Qed.
Lemma lem5212915 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5212916 (x' : real -> real) (b' : real) : (term1009 x' b') = ((term1005 x' b') = (term1005 x' b')).
Proof. exact (@lem5212915 ((term1005 x' b') = (term1005 x' b'))). Qed.
Lemma lem5212917 (x' : real -> real) (b' : real) : (term1005 x' b') = (term1005 x' b').
Proof. exact (EQ_MP (@lem5212916 x' b') (@lem5212913 x' b')). Qed.
Lemma lem5212935 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5212936 (y : real) (x : real) (z : real) : (term1011 x y z) = (term1012 y x z).
Proof. exact (@lem5212935 (y = z) (term1013 x z)). Qed.
Lemma lem5212946 (x : real) (y : real) : (term1014 x y) = (term1014 x y).
Proof. exact (eq_refl (term1014 x y)). Qed.
Lemma lem5212947 (y : real) (x : real) (z : real) : (term1004 x y z) = (term1015 y x z).
Proof. exact (MK_COMB (@lem5212946 x y) (@lem5212936 y x z)). Qed.
Lemma lem5212951 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5212952 (y : real) (x : real) (z : real) : (term1015 y x z) = (term1016 y x z).
Proof. exact (@lem5212951 (y = z) (term1013 x y) (term1013 x z)). Qed.
Lemma lem5212974 (y : real) (x : real) (z : real) : (term1004 x y z) = (term1016 y x z).
Proof. exact (TRANS (@lem5212947 y x z) (@lem5212952 y x z)). Qed.
Lemma lem5212975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5212976 (y : real) (x : real) (z : real) : (term1017 x y z) = (term1018 y x z).
Proof. exact (MK_COMB (@lem5212975) (@lem5212974 y x z)). Qed.
Lemma lem5212998 (y : real) (x : real) (z : real) : (term1016 y x z) = (term1016 y x z).
Proof. exact (eq_refl (term1016 y x z)). Qed.
Lemma lem5212999 (y : real) (x : real) (z : real) : ((term1004 x y z) = (term1016 y x z)) = ((term1016 y x z) = (term1016 y x z)).
Proof. exact (MK_COMB (@lem5212976 y x z) (@lem5212998 y x z)). Qed.
Lemma lem5213001 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5213002 (x : Prop) : (x = x) = True.
Proof. exact (@lem5213001 Prop x). Qed.
Lemma lem5213003 (y : real) (x : real) (z : real) : ((term1016 y x z) = (term1016 y x z)) = True.
Proof. exact (@lem5213002 (term1016 y x z)). Qed.
Lemma lem5213004 (y : real) (x : real) (z : real) : ((term1004 x y z) = (term1016 y x z)) = True.
Proof. exact (TRANS (@lem5212999 y x z) (@lem5213003 y x z)). Qed.
Lemma lem5213005 (y : real) (x : real) (z : real) : True = ((term1004 x y z) = (term1016 y x z)).
Proof. exact (SYM (@lem5213004 y x z)). Qed.
Lemma lem5213006 (y : real) (x : real) (z : real) : (term1004 x y z) = (term1016 y x z).
Proof. exact (EQ_MP (@lem5213005 y x z) (@lem0)). Qed.
Lemma lem5213007 (y : real) (x : real) (z : real) : term1016 y x z.
Proof. exact (EQ_MP (@lem5213006 y x z) (@lem5212897 x y z)). Qed.
Lemma lem5213009 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5213010 (x : real) (y : real) (z : real) : (term1016 y x z) = (term1020 x y z).
Proof. exact (@lem5213009 (term1021 y x z) (y = z)). Qed.
Lemma lem5213012 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5213013 (y : real) (x : real) (z : real) : (term1024 y x z) = (term1025 y x z).
Proof. exact (@lem5213012 (term1013 x y) (term1013 x z)). Qed.
Lemma lem5213015 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213016 (x : real) (y : real) : (term1027 x y) = (x = y).
Proof. exact (@lem5213015 (x = y)). Qed.
Lemma lem5213017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5213018 (x : real) (y : real) : (term1028 x y) = (term1029 x y).
Proof. exact (MK_COMB (@lem5213017) (@lem5213016 x y)). Qed.
Lemma lem5213020 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213021 (x : real) (z : real) : (term1027 x z) = (x = z).
Proof. exact (@lem5213020 (x = z)). Qed.
Lemma lem5213022 (y : real) (x : real) (z : real) : (term1025 y x z) = (term1030 y x z).
Proof. exact (MK_COMB (@lem5213018 x y) (@lem5213021 x z)). Qed.
Lemma lem5213023 (y : real) (x : real) (z : real) : (term1024 y x z) = (term1030 y x z).
Proof. exact (TRANS (@lem5213013 y x z) (@lem5213022 y x z)). Qed.
Lemma lem5213024 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5213025 (y : real) (x : real) (z : real) : (term1031 y x z) = (term1032 y x z).
Proof. exact (MK_COMB (@lem5213024) (@lem5213023 y x z)). Qed.
Lemma lem5213026 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5213027 (x : real) (y : real) (z : real) : (term1020 x y z) = (term1033 x y z).
Proof. exact (MK_COMB (@lem5213025 y x z) (@lem5213026 y z)). Qed.
Lemma lem5213028 (x : real) (y : real) (z : real) : (term1016 y x z) = (term1033 x y z).
Proof. exact (TRANS (@lem5213010 x y z) (@lem5213027 x y z)). Qed.
Lemma lem5213030 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1034 x'' x' b'.
Proof. exact (conj (@lem5212909 b' x'' s x' h1) (@lem5212917 x' b')). Qed.
Lemma lem5213032 (x : real) (y : real) (z : real) : term1033 x y z.
Proof. exact (EQ_MP (@lem5213028 x y z) (@lem5213007 y x z)). Qed.
Lemma lem5213033 (x'' : real -> real) (x' : real -> real) (b' : real) : term1035 x'' x' b'.
Proof. exact (@lem5213032 (term1005 x' b') (term1006 x'' b') (term1005 x' b')). Qed.
Lemma lem5213036 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (term1006 x'' b') = (term1005 x' b').
Proof. exact (@lem5213033 x'' x' b' (@lem5213030 b' x'' s x' h1)). Qed.
Lemma lem5213037 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1036 x'' x' b'.
Proof. exact (fun h0 : term1037 x'' x' b' => @lem5213036 b' x'' s x' h1). Qed.
Lemma lem5213039 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213040 (x'' : real -> real) (x' : real -> real) (b' : real) : (term1036 x'' x' b') = ((term1006 x'' b') = (term1005 x' b')).
Proof. exact (@lem5213039 ((term1006 x'' b') = (term1005 x' b'))). Qed.
Lemma lem5213041 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : (term1006 x'' b') = (term1005 x' b').
Proof. exact (EQ_MP (@lem5213040 x'' x' b') (@lem5213037 b' x'' s x' h1)). Qed.
Lemma lem5213043 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5213044 (b' : real) : (@I (real -> real) real_neg b') = (@I (real -> real) real_neg b').
Proof. exact (@lem5213043 (@I (real -> real) real_neg b')). Qed.
Lemma lem5213045 (b' : real) : term1038 b'.
Proof. exact (fun h0 : term1039 b' => @lem5213044 b'). Qed.
Lemma lem5213047 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213048 (b' : real) : (term1038 b') = ((@I (real -> real) real_neg b') = (@I (real -> real) real_neg b')).
Proof. exact (@lem5213047 ((@I (real -> real) real_neg b') = (@I (real -> real) real_neg b'))). Qed.
Lemma lem5213049 (b' : real) : (@I (real -> real) real_neg b') = (@I (real -> real) real_neg b').
Proof. exact (EQ_MP (@lem5213048 b') (@lem5213045 b')). Qed.
Lemma lem5213051 (_67966 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term864 x'' _67966 s.
Proof. exact (proj2 (@lem5210292 _67966 x'' s x' h1)). Qed.
Lemma lem5213052 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1040 x'' b' s.
Proof. exact (@lem5213051 (@I (real -> real) real_neg b') x'' s x' h1). Qed.
Lemma lem5213053 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1041 x'' b' s.
Proof. exact (fun h0 : term1042 x'' b' s => @lem5213052 b' x'' s x' h1). Qed.
Lemma lem5213055 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213056 (x'' : real -> real) (b' : real) (s : real -> Prop) : (term1041 x'' b' s) = (term1040 x'' b' s).
Proof. exact (@lem5213055 (term1040 x'' b' s)). Qed.
Lemma lem5213057 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1040 x'' b' s.
Proof. exact (EQ_MP (@lem5213056 x'' b' s) (@lem5213053 b' x'' s x' h1)). Qed.
Lemma lem5213063 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5213064 (b' : real) (_67965 : real) (s : real -> Prop) : (term851 s _67965 b') = (term1129 b' _67965 s).
Proof. exact (@lem5213063 (term823 _67965 b') (term724 _67965 s)). Qed.
Lemma lem5213070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5213071 (b' : real) (_67965 : real) (s : real -> Prop) : (term1130 s _67965 b') = (term1131 b' _67965 s).
Proof. exact (MK_COMB (@lem5213070) (@lem5213064 b' _67965 s)). Qed.
Lemma lem5213077 (b' : real) (_67965 : real) (s : real -> Prop) : (term1129 b' _67965 s) = (term1129 b' _67965 s).
Proof. exact (eq_refl (term1129 b' _67965 s)). Qed.
Lemma lem5213078 (b' : real) (_67965 : real) (s : real -> Prop) : ((term851 s _67965 b') = (term1129 b' _67965 s)) = ((term1129 b' _67965 s) = (term1129 b' _67965 s)).
Proof. exact (MK_COMB (@lem5213071 b' _67965 s) (@lem5213077 b' _67965 s)). Qed.
Lemma lem5213080 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5213081 (x : Prop) : (x = x) = True.
Proof. exact (@lem5213080 Prop x). Qed.
Lemma lem5213082 (b' : real) (_67965 : real) (s : real -> Prop) : ((term1129 b' _67965 s) = (term1129 b' _67965 s)) = True.
Proof. exact (@lem5213081 (term1129 b' _67965 s)). Qed.
Lemma lem5213083 (b' : real) (_67965 : real) (s : real -> Prop) : ((term851 s _67965 b') = (term1129 b' _67965 s)) = True.
Proof. exact (TRANS (@lem5213078 b' _67965 s) (@lem5213082 b' _67965 s)). Qed.
Lemma lem5213084 (b' : real) (_67965 : real) (s : real -> Prop) : True = ((term851 s _67965 b') = (term1129 b' _67965 s)).
Proof. exact (SYM (@lem5213083 b' _67965 s)). Qed.
Lemma lem5213085 (b' : real) (_67965 : real) (s : real -> Prop) : (term851 s _67965 b') = (term1129 b' _67965 s).
Proof. exact (EQ_MP (@lem5213084 b' _67965 s) (@lem0)). Qed.
Lemma lem5213086 (_67965 : real) (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term1129 b' _67965 s.
Proof. exact (EQ_MP (@lem5213085 b' _67965 s) (@lem5211443 _67965 s a b' h1)). Qed.
Lemma lem5213088 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5213089 (s : real -> Prop) (_67965 : real) (b' : real) : (term1129 b' _67965 s) = (term1132 s _67965 b').
Proof. exact (@lem5213088 (term724 _67965 s) (term823 _67965 b')). Qed.
Lemma lem5213091 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213092 (_67965 : real) (s : real -> Prop) : (term1047 _67965 s) = (@IN real _67965 s).
Proof. exact (@lem5213091 (@IN real _67965 s)). Qed.
Lemma lem5213093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5213094 (_67965 : real) (s : real -> Prop) : (term1048 _67965 s) = (term49 _67965 s).
Proof. exact (MK_COMB (@lem5213093) (@lem5213092 _67965 s)). Qed.
Lemma lem5213095 (_67965 : real) (b' : real) : (term823 _67965 b') = (term823 _67965 b').
Proof. exact (eq_refl (term823 _67965 b')). Qed.
Lemma lem5213096 (s : real -> Prop) (_67965 : real) (b' : real) : (term1132 s _67965 b') = (term1133 s _67965 b').
Proof. exact (MK_COMB (@lem5213094 _67965 s) (@lem5213095 _67965 b')). Qed.
Lemma lem5213097 (s : real -> Prop) (_67965 : real) (b' : real) : (term1129 b' _67965 s) = (term1133 s _67965 b').
Proof. exact (TRANS (@lem5213089 s _67965 b') (@lem5213096 s _67965 b')). Qed.
Lemma lem5213100 (_67965 : real) (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term1133 s _67965 b'.
Proof. exact (EQ_MP (@lem5213097 s _67965 b') (@lem5213086 _67965 s a b' h1)). Qed.
Lemma lem5213101 (x'' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term1134 s x'' b'.
Proof. exact (@lem5213100 (term1005 x'' b') s a b' h1). Qed.
Lemma lem5213104 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : term1059 x'' b'.
Proof. exact (@lem5213101 x'' s a b' h2 (@lem5213057 b' x'' s x' h1)). Qed.
Lemma lem5213105 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : term1060 x'' b'.
Proof. exact (fun h0 : term1061 x'' b' => @lem5213104 x'' x' s a b' h1 h2). Qed.
Lemma lem5213107 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213108 (x'' : real -> real) (b' : real) : (term1060 x'' b') = (term1059 x'' b').
Proof. exact (@lem5213107 (term1059 x'' b')). Qed.
Lemma lem5213109 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : term1059 x'' b'.
Proof. exact (EQ_MP (@lem5213108 x'' b') (@lem5213105 x'' x' s a b' h1 h2)). Qed.
Lemma lem5213127 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5213128 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1001 _68226 _68227 _68224 _68225) = (term1062 _68226 _68227 _68224 _68225).
Proof. exact (@lem5213127 (real_le _68226 _68227) (term1013 _68225 _68227) (term252 _68224 _68225)). Qed.
Lemma lem5213146 (_68224 : real) (_68226 : real) : (term1014 _68224 _68226) = (term1014 _68224 _68226).
Proof. exact (eq_refl (term1014 _68224 _68226)). Qed.
Lemma lem5213147 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1003 _68226 _68227 _68224 _68225) = (term1063 _68226 _68227 _68224 _68225).
Proof. exact (MK_COMB (@lem5213146 _68224 _68226) (@lem5213128 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213151 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5213152 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1063 _68226 _68227 _68224 _68225) = (term1064 _68226 _68227 _68224 _68225).
Proof. exact (@lem5213151 (real_le _68226 _68227) (term1013 _68224 _68226) (term1065 _68227 _68224 _68225)). Qed.
Lemma lem5213182 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1003 _68226 _68227 _68224 _68225) = (term1064 _68226 _68227 _68224 _68225).
Proof. exact (TRANS (@lem5213147 _68226 _68227 _68224 _68225) (@lem5213152 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5213184 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1066 _68226 _68227 _68224 _68225) = (term1067 _68226 _68227 _68224 _68225).
Proof. exact (MK_COMB (@lem5213183) (@lem5213182 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213214 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1064 _68226 _68227 _68224 _68225) = (term1064 _68226 _68227 _68224 _68225).
Proof. exact (eq_refl (term1064 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213215 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : ((term1003 _68226 _68227 _68224 _68225) = (term1064 _68226 _68227 _68224 _68225)) = ((term1064 _68226 _68227 _68224 _68225) = (term1064 _68226 _68227 _68224 _68225)).
Proof. exact (MK_COMB (@lem5213184 _68226 _68227 _68224 _68225) (@lem5213214 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213217 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5213218 (x : Prop) : (x = x) = True.
Proof. exact (@lem5213217 Prop x). Qed.
Lemma lem5213219 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : ((term1064 _68226 _68227 _68224 _68225) = (term1064 _68226 _68227 _68224 _68225)) = True.
Proof. exact (@lem5213218 (term1064 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213220 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : ((term1003 _68226 _68227 _68224 _68225) = (term1064 _68226 _68227 _68224 _68225)) = True.
Proof. exact (TRANS (@lem5213215 _68226 _68227 _68224 _68225) (@lem5213219 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213221 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : True = ((term1003 _68226 _68227 _68224 _68225) = (term1064 _68226 _68227 _68224 _68225)).
Proof. exact (SYM (@lem5213220 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213222 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1003 _68226 _68227 _68224 _68225) = (term1064 _68226 _68227 _68224 _68225).
Proof. exact (EQ_MP (@lem5213221 _68226 _68227 _68224 _68225) (@lem0)). Qed.
Lemma lem5213223 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : term1064 _68226 _68227 _68224 _68225.
Proof. exact (EQ_MP (@lem5213222 _68226 _68227 _68224 _68225) (@lem5212833 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213225 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5213226 (_68224 : real) (_68225 : real) (_68226 : real) (_68227 : real) : (term1064 _68226 _68227 _68224 _68225) = (term1068 _68224 _68225 _68226 _68227).
Proof. exact (@lem5213225 (term1069 _68226 _68227 _68224 _68225) (real_le _68226 _68227)). Qed.
Lemma lem5213228 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5213229 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1070 _68226 _68227 _68224 _68225) = (term1071 _68226 _68227 _68224 _68225).
Proof. exact (@lem5213228 (term1013 _68224 _68226) (term1065 _68227 _68224 _68225)). Qed.
Lemma lem5213231 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213232 (_68224 : real) (_68226 : real) : (term1027 _68224 _68226) = (_68224 = _68226).
Proof. exact (@lem5213231 (_68224 = _68226)). Qed.
Lemma lem5213233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5213234 (_68224 : real) (_68226 : real) : (term1028 _68224 _68226) = (term1029 _68224 _68226).
Proof. exact (MK_COMB (@lem5213233) (@lem5213232 _68224 _68226)). Qed.
Lemma lem5213236 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5213237 (_68227 : real) (_68224 : real) (_68225 : real) : (term1072 _68227 _68224 _68225) = (term1073 _68227 _68224 _68225).
Proof. exact (@lem5213236 (term1013 _68225 _68227) (term252 _68224 _68225)). Qed.
Lemma lem5213239 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213240 (_68225 : real) (_68227 : real) : (term1027 _68225 _68227) = (_68225 = _68227).
Proof. exact (@lem5213239 (_68225 = _68227)). Qed.
Lemma lem5213241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5213242 (_68225 : real) (_68227 : real) : (term1028 _68225 _68227) = (term1029 _68225 _68227).
Proof. exact (MK_COMB (@lem5213241) (@lem5213240 _68225 _68227)). Qed.
Lemma lem5213244 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213245 (_68224 : real) (_68225 : real) : (term1054 _68224 _68225) = (real_le _68224 _68225).
Proof. exact (@lem5213244 (real_le _68224 _68225)). Qed.
Lemma lem5213246 (_68227 : real) (_68224 : real) (_68225 : real) : (term1073 _68227 _68224 _68225) = (term1074 _68227 _68224 _68225).
Proof. exact (MK_COMB (@lem5213242 _68225 _68227) (@lem5213245 _68224 _68225)). Qed.
Lemma lem5213247 (_68227 : real) (_68224 : real) (_68225 : real) : (term1072 _68227 _68224 _68225) = (term1074 _68227 _68224 _68225).
Proof. exact (TRANS (@lem5213237 _68227 _68224 _68225) (@lem5213246 _68227 _68224 _68225)). Qed.
Lemma lem5213248 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1071 _68226 _68227 _68224 _68225) = (term1075 _68226 _68227 _68224 _68225).
Proof. exact (MK_COMB (@lem5213234 _68224 _68226) (@lem5213247 _68227 _68224 _68225)). Qed.
Lemma lem5213249 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1070 _68226 _68227 _68224 _68225) = (term1075 _68226 _68227 _68224 _68225).
Proof. exact (TRANS (@lem5213229 _68226 _68227 _68224 _68225) (@lem5213248 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5213251 (_68226 : real) (_68227 : real) (_68224 : real) (_68225 : real) : (term1076 _68226 _68227 _68224 _68225) = (term1077 _68226 _68227 _68224 _68225).
Proof. exact (MK_COMB (@lem5213250) (@lem5213249 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213252 (_68226 : real) (_68227 : real) : (real_le _68226 _68227) = (real_le _68226 _68227).
Proof. exact (eq_refl (real_le _68226 _68227)). Qed.
Lemma lem5213253 (_68224 : real) (_68225 : real) (_68226 : real) (_68227 : real) : (term1068 _68224 _68225 _68226 _68227) = (term1078 _68224 _68225 _68226 _68227).
Proof. exact (MK_COMB (@lem5213251 _68226 _68227 _68224 _68225) (@lem5213252 _68226 _68227)). Qed.
Lemma lem5213254 (_68224 : real) (_68225 : real) (_68226 : real) (_68227 : real) : (term1064 _68226 _68227 _68224 _68225) = (term1078 _68224 _68225 _68226 _68227).
Proof. exact (TRANS (@lem5213226 _68224 _68225 _68226 _68227) (@lem5213253 _68224 _68225 _68226 _68227)). Qed.
Lemma lem5213256 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : term1079 x'' b'.
Proof. exact (conj (@lem5213049 b') (@lem5213109 x'' x' s a b' h1 h2)). Qed.
Lemma lem5213257 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : term1080 x' x'' b'.
Proof. exact (conj (@lem5213041 b' x'' s x' h1) (@lem5213256 x'' x' s a b' h1 h2)). Qed.
Lemma lem5213259 (_68224 : real) (_68225 : real) (_68226 : real) (_68227 : real) : term1078 _68224 _68225 _68226 _68227.
Proof. exact (EQ_MP (@lem5213254 _68224 _68225 _68226 _68227) (@lem5213223 _68226 _68227 _68224 _68225)). Qed.
Lemma lem5213260 (x'' : real -> real) (x' : real -> real) (b' : real) : term1081 x'' x' b'.
Proof. exact (@lem5213259 (term1006 x'' b') (@I (real -> real) real_neg b') (term1005 x' b') (@I (real -> real) real_neg b')). Qed.
Lemma lem5213263 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : term1082 x' b'.
Proof. exact (@lem5213260 x'' x' b' (@lem5213257 x'' x' s a b' h1 h2)). Qed.
Lemma lem5213264 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : term1083 x' b'.
Proof. exact (fun h0 : term1084 x' b' => @lem5213263 x'' x' s a b' h1 h2). Qed.
Lemma lem5213266 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213267 (x' : real -> real) (b' : real) : (term1083 x' b') = (term1082 x' b').
Proof. exact (@lem5213266 (term1082 x' b')). Qed.
Lemma lem5213268 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : term1082 x' b'.
Proof. exact (EQ_MP (@lem5213267 x' b') (@lem5213264 x'' x' s a b' h1 h2)). Qed.
Lemma lem5213271 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5213273 (x' : real -> real) (_67966 : real) : (term863 x' _67966) = (term1085 x' _67966).
Proof. exact (@lem5213271 (term1086 x' _67966)). Qed.
Lemma lem5213276 (_67966 : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1085 x' _67966.
Proof. exact (EQ_MP (@lem5213273 x' _67966) (@lem5211470 _67966 x'' s x' h1)). Qed.
Lemma lem5213277 (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term894 x'' s x') : term1087 x' b'.
Proof. exact (@lem5213276 (@I (real -> real) real_neg b') x'' s x' h1). Qed.
Lemma lem5213280 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : False.
Proof. exact (@lem5213277 b' x'' s x' h1 (@lem5213268 x'' x' s a b' h1 h2)). Qed.
Lemma lem5213281 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : term995.
Proof. exact (fun h0 : ~ False => @lem5213280 x'' x' s a b' h1 h2). Qed.
Lemma lem5213283 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213284 : term995 = False.
Proof. exact (@lem5213283 False). Qed.
Lemma lem5213305 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5213306 (_68248 : real) (_68250 : real) (h1 : _68248 = _68250) : _68248 = _68250.
Proof. exact (h1). Qed.
Lemma lem5213307 (_68249 : real) (_68251 : real) (h1 : _68249 = _68251) : _68249 = _68251.
Proof. exact (h1). Qed.
Lemma lem5213308 (_68248 : real) (_68250 : real) (h1 : _68248 = _68250) : (real_le _68248) = (real_le _68250).
Proof. exact (MK_COMB (@lem5213305) (@lem5213306 _68248 _68250 h1)). Qed.
Lemma lem5213309 (_68248 : real) (_68250 : real) (_68249 : real) (_68251 : real) (h1 : _68248 = _68250) (h2 : _68249 = _68251) : (real_le _68248 _68249) = (real_le _68250 _68251).
Proof. exact (MK_COMB (@lem5213308 _68248 _68250 h1) (@lem5213307 _68249 _68251 h2)). Qed.
Lemma lem5213311 (b : Prop) (a : Prop) : term996 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5213312 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : term997 _68250 _68251 _68248 _68249.
Proof. exact (@lem5213311 (real_le _68250 _68251) (real_le _68248 _68249)). Qed.
Lemma lem5213313 (_68248 : real) (_68250 : real) (_68249 : real) (_68251 : real) (h1 : _68248 = _68250) (h2 : _68249 = _68251) : term998 _68250 _68251 _68248 _68249.
Proof. exact (@lem5213312 _68250 _68251 _68248 _68249 (@lem5213309 _68248 _68250 _68249 _68251 h1 h2)). Qed.
Lemma lem5213314 (_68251 : real) (_68249 : real) (_68248 : real) (_68250 : real) (h1 : _68248 = _68250) : term999 _68250 _68251 _68248 _68249.
Proof. exact (fun h0 : _68249 = _68251 => @lem5213313 _68248 _68250 _68249 _68251 h1 h0). Qed.
Lemma lem5213316 (a : Prop) (b : Prop) : (a -> b) = (term1000 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5213317 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term999 _68250 _68251 _68248 _68249) = (term1001 _68250 _68251 _68248 _68249).
Proof. exact (@lem5213316 (_68249 = _68251) (term998 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213318 (_68251 : real) (_68249 : real) (_68248 : real) (_68250 : real) (h1 : _68248 = _68250) : term1001 _68250 _68251 _68248 _68249.
Proof. exact (EQ_MP (@lem5213317 _68250 _68251 _68248 _68249) (@lem5213314 _68251 _68249 _68248 _68250 h1)). Qed.
Lemma lem5213319 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : term1002 _68250 _68251 _68248 _68249.
Proof. exact (fun h0 : _68248 = _68250 => @lem5213318 _68251 _68249 _68248 _68250 h0). Qed.
Lemma lem5213321 (a : Prop) (b : Prop) : (a -> b) = (term1000 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5213322 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1002 _68250 _68251 _68248 _68249) = (term1003 _68250 _68251 _68248 _68249).
Proof. exact (@lem5213321 (_68248 = _68250) (term1001 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213323 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : term1003 _68250 _68251 _68248 _68249.
Proof. exact (EQ_MP (@lem5213322 _68250 _68251 _68248 _68249) (@lem5213319 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213387 (x : real) (y : real) (z : real) : term1004 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem5213394 (s : real -> Prop) (b' : real) (h1 : term962 s b') : term962 s b'.
Proof. exact (h1). Qed.
Lemma lem5213395 (s : real -> Prop) (b' : real) (h1 : term962 s b') : term1135 s b'.
Proof. exact (fun h0 : term1136 s b' => @lem5213394 s b' h1). Qed.
Lemma lem5213397 (p : Prop) : (term1122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5213398 (s : real -> Prop) (b' : real) : (term1135 s b') = (term962 s b').
Proof. exact (@lem5213397 (term1136 s b')). Qed.
Lemma lem5213399 (s : real -> Prop) (b' : real) (h1 : term962 s b') : term962 s b'.
Proof. exact (EQ_MP (@lem5213398 s b') (@lem5213395 s b' h1)). Qed.
Lemma lem5213401 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5213404 (s : real -> Prop) (x' : real -> real) (x'' : real -> real) (_67979 : real) : (term974 x' x'' s _67979) = (term1137 s x' x'' _67979).
Proof. exact (@lem5213401 (term130 s _67979) ((x' _67979) = (term866 x'' _67979))). Qed.
Lemma lem5213407 (_67979 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1137 s x' x'' _67979.
Proof. exact (EQ_MP (@lem5213404 s x' x'' _67979) (@lem5211677 _67979 x'' x' s a h1 h2)). Qed.
Lemma lem5213408 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1138 s x' x'' b'.
Proof. exact (@lem5213407 (@I (real -> real) real_neg b') x'' x' s a h1 h2). Qed.
Lemma lem5213411 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : (term1005 x' b') = (term1006 x'' b').
Proof. exact (@lem5213408 b' x'' x' s a h2 h3 (@lem5213399 s b' h1)). Qed.
Lemma lem5213412 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1007 x' x'' b'.
Proof. exact (fun h0 : term1008 x' x'' b' => @lem5213411 b' x'' x' s a h1 h2 h3). Qed.
Lemma lem5213414 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213415 (x' : real -> real) (x'' : real -> real) (b' : real) : (term1007 x' x'' b') = ((term1005 x' b') = (term1006 x'' b')).
Proof. exact (@lem5213414 ((term1005 x' b') = (term1006 x'' b'))). Qed.
Lemma lem5213416 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : (term1005 x' b') = (term1006 x'' b').
Proof. exact (EQ_MP (@lem5213415 x' x'' b') (@lem5213412 b' x'' x' s a h1 h2 h3)). Qed.
Lemma lem5213418 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5213419 (x' : real -> real) (b' : real) : (term1005 x' b') = (term1005 x' b').
Proof. exact (@lem5213418 (term1005 x' b')). Qed.
Lemma lem5213420 (x' : real -> real) (b' : real) : term1009 x' b'.
Proof. exact (fun h0 : term1010 x' b' => @lem5213419 x' b'). Qed.
Lemma lem5213422 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213423 (x' : real -> real) (b' : real) : (term1009 x' b') = ((term1005 x' b') = (term1005 x' b')).
Proof. exact (@lem5213422 ((term1005 x' b') = (term1005 x' b'))). Qed.
Lemma lem5213424 (x' : real -> real) (b' : real) : (term1005 x' b') = (term1005 x' b').
Proof. exact (EQ_MP (@lem5213423 x' b') (@lem5213420 x' b')). Qed.
Lemma lem5213442 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5213443 (y : real) (x : real) (z : real) : (term1011 x y z) = (term1012 y x z).
Proof. exact (@lem5213442 (y = z) (term1013 x z)). Qed.
Lemma lem5213453 (x : real) (y : real) : (term1014 x y) = (term1014 x y).
Proof. exact (eq_refl (term1014 x y)). Qed.
Lemma lem5213454 (y : real) (x : real) (z : real) : (term1004 x y z) = (term1015 y x z).
Proof. exact (MK_COMB (@lem5213453 x y) (@lem5213443 y x z)). Qed.
Lemma lem5213458 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5213459 (y : real) (x : real) (z : real) : (term1015 y x z) = (term1016 y x z).
Proof. exact (@lem5213458 (y = z) (term1013 x y) (term1013 x z)). Qed.
Lemma lem5213481 (y : real) (x : real) (z : real) : (term1004 x y z) = (term1016 y x z).
Proof. exact (TRANS (@lem5213454 y x z) (@lem5213459 y x z)). Qed.
Lemma lem5213482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5213483 (y : real) (x : real) (z : real) : (term1017 x y z) = (term1018 y x z).
Proof. exact (MK_COMB (@lem5213482) (@lem5213481 y x z)). Qed.
Lemma lem5213505 (y : real) (x : real) (z : real) : (term1016 y x z) = (term1016 y x z).
Proof. exact (eq_refl (term1016 y x z)). Qed.
Lemma lem5213506 (y : real) (x : real) (z : real) : ((term1004 x y z) = (term1016 y x z)) = ((term1016 y x z) = (term1016 y x z)).
Proof. exact (MK_COMB (@lem5213483 y x z) (@lem5213505 y x z)). Qed.
Lemma lem5213508 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5213509 (x : Prop) : (x = x) = True.
Proof. exact (@lem5213508 Prop x). Qed.
Lemma lem5213510 (y : real) (x : real) (z : real) : ((term1016 y x z) = (term1016 y x z)) = True.
Proof. exact (@lem5213509 (term1016 y x z)). Qed.
Lemma lem5213511 (y : real) (x : real) (z : real) : ((term1004 x y z) = (term1016 y x z)) = True.
Proof. exact (TRANS (@lem5213506 y x z) (@lem5213510 y x z)). Qed.
Lemma lem5213512 (y : real) (x : real) (z : real) : True = ((term1004 x y z) = (term1016 y x z)).
Proof. exact (SYM (@lem5213511 y x z)). Qed.
Lemma lem5213513 (y : real) (x : real) (z : real) : (term1004 x y z) = (term1016 y x z).
Proof. exact (EQ_MP (@lem5213512 y x z) (@lem0)). Qed.
Lemma lem5213514 (y : real) (x : real) (z : real) : term1016 y x z.
Proof. exact (EQ_MP (@lem5213513 y x z) (@lem5213387 x y z)). Qed.
Lemma lem5213516 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5213517 (x : real) (y : real) (z : real) : (term1016 y x z) = (term1020 x y z).
Proof. exact (@lem5213516 (term1021 y x z) (y = z)). Qed.
Lemma lem5213519 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5213520 (y : real) (x : real) (z : real) : (term1024 y x z) = (term1025 y x z).
Proof. exact (@lem5213519 (term1013 x y) (term1013 x z)). Qed.
Lemma lem5213522 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213523 (x : real) (y : real) : (term1027 x y) = (x = y).
Proof. exact (@lem5213522 (x = y)). Qed.
Lemma lem5213524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5213525 (x : real) (y : real) : (term1028 x y) = (term1029 x y).
Proof. exact (MK_COMB (@lem5213524) (@lem5213523 x y)). Qed.
Lemma lem5213527 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213528 (x : real) (z : real) : (term1027 x z) = (x = z).
Proof. exact (@lem5213527 (x = z)). Qed.
Lemma lem5213529 (y : real) (x : real) (z : real) : (term1025 y x z) = (term1030 y x z).
Proof. exact (MK_COMB (@lem5213525 x y) (@lem5213528 x z)). Qed.
Lemma lem5213530 (y : real) (x : real) (z : real) : (term1024 y x z) = (term1030 y x z).
Proof. exact (TRANS (@lem5213520 y x z) (@lem5213529 y x z)). Qed.
Lemma lem5213531 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5213532 (y : real) (x : real) (z : real) : (term1031 y x z) = (term1032 y x z).
Proof. exact (MK_COMB (@lem5213531) (@lem5213530 y x z)). Qed.
Lemma lem5213533 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5213534 (x : real) (y : real) (z : real) : (term1020 x y z) = (term1033 x y z).
Proof. exact (MK_COMB (@lem5213532 y x z) (@lem5213533 y z)). Qed.
Lemma lem5213535 (x : real) (y : real) (z : real) : (term1016 y x z) = (term1033 x y z).
Proof. exact (TRANS (@lem5213517 x y z) (@lem5213534 x y z)). Qed.
Lemma lem5213537 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1034 x'' x' b'.
Proof. exact (conj (@lem5213416 b' x'' x' s a h1 h2 h3) (@lem5213424 x' b')). Qed.
Lemma lem5213539 (x : real) (y : real) (z : real) : term1033 x y z.
Proof. exact (EQ_MP (@lem5213535 x y z) (@lem5213514 y x z)). Qed.
Lemma lem5213540 (x'' : real -> real) (x' : real -> real) (b' : real) : term1035 x'' x' b'.
Proof. exact (@lem5213539 (term1005 x' b') (term1006 x'' b') (term1005 x' b')). Qed.
Lemma lem5213543 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : (term1006 x'' b') = (term1005 x' b').
Proof. exact (@lem5213540 x'' x' b' (@lem5213537 b' x'' x' s a h1 h2 h3)). Qed.
Lemma lem5213544 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1036 x'' x' b'.
Proof. exact (fun h0 : term1037 x'' x' b' => @lem5213543 b' x'' x' s a h1 h2 h3). Qed.
Lemma lem5213546 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213547 (x'' : real -> real) (x' : real -> real) (b' : real) : (term1036 x'' x' b') = ((term1006 x'' b') = (term1005 x' b')).
Proof. exact (@lem5213546 ((term1006 x'' b') = (term1005 x' b'))). Qed.
Lemma lem5213548 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : (term1006 x'' b') = (term1005 x' b').
Proof. exact (EQ_MP (@lem5213547 x'' x' b') (@lem5213544 b' x'' x' s a h1 h2 h3)). Qed.
Lemma lem5213550 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5213551 (b' : real) : (@I (real -> real) real_neg b') = (@I (real -> real) real_neg b').
Proof. exact (@lem5213550 (@I (real -> real) real_neg b')). Qed.
Lemma lem5213552 (b' : real) : term1038 b'.
Proof. exact (fun h0 : term1039 b' => @lem5213551 b'). Qed.
Lemma lem5213554 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213555 (b' : real) : (term1038 b') = ((@I (real -> real) real_neg b') = (@I (real -> real) real_neg b')).
Proof. exact (@lem5213554 ((@I (real -> real) real_neg b') = (@I (real -> real) real_neg b'))). Qed.
Lemma lem5213556 (b' : real) : (@I (real -> real) real_neg b') = (@I (real -> real) real_neg b').
Proof. exact (EQ_MP (@lem5213555 b') (@lem5213552 b')). Qed.
Lemma lem5213559 (s : real -> Prop) (b' : real) (h1 : term962 s b') : term962 s b'.
Proof. exact (h1). Qed.
Lemma lem5213560 (s : real -> Prop) (b' : real) (h1 : term962 s b') : term1135 s b'.
Proof. exact (fun h0 : term1136 s b' => @lem5213559 s b' h1). Qed.
Lemma lem5213562 (p : Prop) : (term1122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5213563 (s : real -> Prop) (b' : real) : (term1135 s b') = (term962 s b').
Proof. exact (@lem5213562 (term1136 s b')). Qed.
Lemma lem5213564 (s : real -> Prop) (b' : real) (h1 : term962 s b') : term962 s b'.
Proof. exact (EQ_MP (@lem5213563 s b') (@lem5213560 s b' h1)). Qed.
Lemma lem5213566 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5213569 (s : real -> Prop) (x' : real -> real) (_67979 : real) : (term968 x' s _67979) = (term1139 s x' _67979).
Proof. exact (@lem5213566 (term130 s _67979) (term863 x' _67979)). Qed.
Lemma lem5213572 (_67979 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1139 s x' _67979.
Proof. exact (EQ_MP (@lem5213569 s x' _67979) (@lem5211664 _67979 x'' x' s a h1 h2)). Qed.
Lemma lem5213573 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1140 s x' b'.
Proof. exact (@lem5213572 (@I (real -> real) real_neg b') x'' x' s a h1 h2). Qed.
Lemma lem5213576 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1084 x' b'.
Proof. exact (@lem5213573 b' x'' x' s a h2 h3 (@lem5213564 s b' h1)). Qed.
Lemma lem5213577 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1141 x' b'.
Proof. exact (fun h0 : term1082 x' b' => @lem5213576 b' x'' x' s a h1 h2 h3). Qed.
Lemma lem5213579 (p : Prop) : (term1122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5213580 (x' : real -> real) (b' : real) : (term1141 x' b') = (term1084 x' b').
Proof. exact (@lem5213579 (term1082 x' b')). Qed.
Lemma lem5213581 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1084 x' b'.
Proof. exact (EQ_MP (@lem5213580 x' b') (@lem5213577 b' x'' x' s a h1 h2 h3)). Qed.
Lemma lem5213599 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5213600 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1001 _68250 _68251 _68248 _68249) = (term1062 _68250 _68251 _68248 _68249).
Proof. exact (@lem5213599 (real_le _68250 _68251) (term1013 _68249 _68251) (term252 _68248 _68249)). Qed.
Lemma lem5213618 (_68248 : real) (_68250 : real) : (term1014 _68248 _68250) = (term1014 _68248 _68250).
Proof. exact (eq_refl (term1014 _68248 _68250)). Qed.
Lemma lem5213619 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1003 _68250 _68251 _68248 _68249) = (term1063 _68250 _68251 _68248 _68249).
Proof. exact (MK_COMB (@lem5213618 _68248 _68250) (@lem5213600 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213623 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5213624 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1063 _68250 _68251 _68248 _68249) = (term1064 _68250 _68251 _68248 _68249).
Proof. exact (@lem5213623 (real_le _68250 _68251) (term1013 _68248 _68250) (term1065 _68251 _68248 _68249)). Qed.
Lemma lem5213654 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1003 _68250 _68251 _68248 _68249) = (term1064 _68250 _68251 _68248 _68249).
Proof. exact (TRANS (@lem5213619 _68250 _68251 _68248 _68249) (@lem5213624 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5213656 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1066 _68250 _68251 _68248 _68249) = (term1067 _68250 _68251 _68248 _68249).
Proof. exact (MK_COMB (@lem5213655) (@lem5213654 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213660 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5213661 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : (term1142 _68248 _68249 _68250 _68251) = (term1143 _68248 _68249 _68250 _68251).
Proof. exact (@lem5213660 (term1013 _68248 _68250) (term252 _68248 _68249) (term1144 _68249 _68250 _68251)). Qed.
Lemma lem5213677 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5213678 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : (term1145 _68248 _68249 _68250 _68251) = (term1146 _68248 _68249 _68250 _68251).
Proof. exact (@lem5213677 (term1013 _68249 _68251) (term252 _68248 _68249) (real_le _68250 _68251)). Qed.
Lemma lem5213694 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5213695 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1147 _68248 _68249 _68250 _68251) = (term998 _68250 _68251 _68248 _68249).
Proof. exact (@lem5213694 (real_le _68250 _68251) (term252 _68248 _68249)). Qed.
Lemma lem5213701 (_68249 : real) (_68251 : real) : (term1014 _68249 _68251) = (term1014 _68249 _68251).
Proof. exact (eq_refl (term1014 _68249 _68251)). Qed.
Lemma lem5213702 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1146 _68248 _68249 _68250 _68251) = (term1001 _68250 _68251 _68248 _68249).
Proof. exact (MK_COMB (@lem5213701 _68249 _68251) (@lem5213695 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213706 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5213707 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1001 _68250 _68251 _68248 _68249) = (term1062 _68250 _68251 _68248 _68249).
Proof. exact (@lem5213706 (real_le _68250 _68251) (term1013 _68249 _68251) (term252 _68248 _68249)). Qed.
Lemma lem5213725 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1146 _68248 _68249 _68250 _68251) = (term1062 _68250 _68251 _68248 _68249).
Proof. exact (TRANS (@lem5213702 _68250 _68251 _68248 _68249) (@lem5213707 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213726 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1145 _68248 _68249 _68250 _68251) = (term1062 _68250 _68251 _68248 _68249).
Proof. exact (TRANS (@lem5213678 _68248 _68249 _68250 _68251) (@lem5213725 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213727 (_68248 : real) (_68250 : real) : (term1014 _68248 _68250) = (term1014 _68248 _68250).
Proof. exact (eq_refl (term1014 _68248 _68250)). Qed.
Lemma lem5213728 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1143 _68248 _68249 _68250 _68251) = (term1063 _68250 _68251 _68248 _68249).
Proof. exact (MK_COMB (@lem5213727 _68248 _68250) (@lem5213726 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213732 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5213733 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1063 _68250 _68251 _68248 _68249) = (term1064 _68250 _68251 _68248 _68249).
Proof. exact (@lem5213732 (real_le _68250 _68251) (term1013 _68248 _68250) (term1065 _68251 _68248 _68249)). Qed.
Lemma lem5213763 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1143 _68248 _68249 _68250 _68251) = (term1064 _68250 _68251 _68248 _68249).
Proof. exact (TRANS (@lem5213728 _68250 _68251 _68248 _68249) (@lem5213733 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213764 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1142 _68248 _68249 _68250 _68251) = (term1064 _68250 _68251 _68248 _68249).
Proof. exact (TRANS (@lem5213661 _68248 _68249 _68250 _68251) (@lem5213763 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213765 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : ((term1003 _68250 _68251 _68248 _68249) = (term1142 _68248 _68249 _68250 _68251)) = ((term1064 _68250 _68251 _68248 _68249) = (term1064 _68250 _68251 _68248 _68249)).
Proof. exact (MK_COMB (@lem5213656 _68250 _68251 _68248 _68249) (@lem5213764 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213767 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5213768 (x : Prop) : (x = x) = True.
Proof. exact (@lem5213767 Prop x). Qed.
Lemma lem5213769 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : ((term1064 _68250 _68251 _68248 _68249) = (term1064 _68250 _68251 _68248 _68249)) = True.
Proof. exact (@lem5213768 (term1064 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213770 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : ((term1003 _68250 _68251 _68248 _68249) = (term1142 _68248 _68249 _68250 _68251)) = True.
Proof. exact (TRANS (@lem5213765 _68250 _68251 _68248 _68249) (@lem5213769 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213771 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : True = ((term1003 _68250 _68251 _68248 _68249) = (term1142 _68248 _68249 _68250 _68251)).
Proof. exact (SYM (@lem5213770 _68248 _68249 _68250 _68251)). Qed.
Lemma lem5213772 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : (term1003 _68250 _68251 _68248 _68249) = (term1142 _68248 _68249 _68250 _68251).
Proof. exact (EQ_MP (@lem5213771 _68248 _68249 _68250 _68251) (@lem0)). Qed.
Lemma lem5213773 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : term1142 _68248 _68249 _68250 _68251.
Proof. exact (EQ_MP (@lem5213772 _68248 _68249 _68250 _68251) (@lem5213323 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213775 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5213776 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1142 _68248 _68249 _68250 _68251) = (term1148 _68250 _68251 _68248 _68249).
Proof. exact (@lem5213775 (term1149 _68248 _68249 _68250 _68251) (term252 _68248 _68249)). Qed.
Lemma lem5213778 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5213779 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : (term1150 _68248 _68249 _68250 _68251) = (term1151 _68248 _68249 _68250 _68251).
Proof. exact (@lem5213778 (term1013 _68248 _68250) (term1144 _68249 _68250 _68251)). Qed.
Lemma lem5213781 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213782 (_68248 : real) (_68250 : real) : (term1027 _68248 _68250) = (_68248 = _68250).
Proof. exact (@lem5213781 (_68248 = _68250)). Qed.
Lemma lem5213783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5213784 (_68248 : real) (_68250 : real) : (term1028 _68248 _68250) = (term1029 _68248 _68250).
Proof. exact (MK_COMB (@lem5213783) (@lem5213782 _68248 _68250)). Qed.
Lemma lem5213786 (a : Prop) (b : Prop) : (term1022 a b) = (term1023 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5213787 (_68249 : real) (_68250 : real) (_68251 : real) : (term1152 _68249 _68250 _68251) = (term1153 _68249 _68250 _68251).
Proof. exact (@lem5213786 (term1013 _68249 _68251) (real_le _68250 _68251)). Qed.
Lemma lem5213789 (a : Prop) : (term1026 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5213790 (_68249 : real) (_68251 : real) : (term1027 _68249 _68251) = (_68249 = _68251).
Proof. exact (@lem5213789 (_68249 = _68251)). Qed.
Lemma lem5213791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5213792 (_68249 : real) (_68251 : real) : (term1028 _68249 _68251) = (term1029 _68249 _68251).
Proof. exact (MK_COMB (@lem5213791) (@lem5213790 _68249 _68251)). Qed.
Lemma lem5213793 (_68250 : real) (_68251 : real) : (term252 _68250 _68251) = (term252 _68250 _68251).
Proof. exact (eq_refl (term252 _68250 _68251)). Qed.
Lemma lem5213794 (_68249 : real) (_68250 : real) (_68251 : real) : (term1153 _68249 _68250 _68251) = (term1154 _68249 _68250 _68251).
Proof. exact (MK_COMB (@lem5213792 _68249 _68251) (@lem5213793 _68250 _68251)). Qed.
Lemma lem5213795 (_68249 : real) (_68250 : real) (_68251 : real) : (term1152 _68249 _68250 _68251) = (term1154 _68249 _68250 _68251).
Proof. exact (TRANS (@lem5213787 _68249 _68250 _68251) (@lem5213794 _68249 _68250 _68251)). Qed.
Lemma lem5213796 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : (term1151 _68248 _68249 _68250 _68251) = (term1155 _68248 _68249 _68250 _68251).
Proof. exact (MK_COMB (@lem5213784 _68248 _68250) (@lem5213795 _68249 _68250 _68251)). Qed.
Lemma lem5213797 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : (term1150 _68248 _68249 _68250 _68251) = (term1155 _68248 _68249 _68250 _68251).
Proof. exact (TRANS (@lem5213779 _68248 _68249 _68250 _68251) (@lem5213796 _68248 _68249 _68250 _68251)). Qed.
Lemma lem5213798 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5213799 (_68248 : real) (_68249 : real) (_68250 : real) (_68251 : real) : (term1156 _68248 _68249 _68250 _68251) = (term1157 _68248 _68249 _68250 _68251).
Proof. exact (MK_COMB (@lem5213798) (@lem5213797 _68248 _68249 _68250 _68251)). Qed.
Lemma lem5213800 (_68248 : real) (_68249 : real) : (term252 _68248 _68249) = (term252 _68248 _68249).
Proof. exact (eq_refl (term252 _68248 _68249)). Qed.
Lemma lem5213801 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1148 _68250 _68251 _68248 _68249) = (term1158 _68250 _68251 _68248 _68249).
Proof. exact (MK_COMB (@lem5213799 _68248 _68249 _68250 _68251) (@lem5213800 _68248 _68249)). Qed.
Lemma lem5213802 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : (term1142 _68248 _68249 _68250 _68251) = (term1158 _68250 _68251 _68248 _68249).
Proof. exact (TRANS (@lem5213776 _68250 _68251 _68248 _68249) (@lem5213801 _68250 _68251 _68248 _68249)). Qed.
Lemma lem5213804 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1159 x' b'.
Proof. exact (conj (@lem5213556 b') (@lem5213581 b' x'' x' s a h1 h2 h3)). Qed.
Lemma lem5213805 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1160 x'' x' b'.
Proof. exact (conj (@lem5213548 b' x'' x' s a h1 h2 h3) (@lem5213804 b' x'' x' s a h1 h2 h3)). Qed.
Lemma lem5213807 (_68250 : real) (_68251 : real) (_68248 : real) (_68249 : real) : term1158 _68250 _68251 _68248 _68249.
Proof. exact (EQ_MP (@lem5213802 _68250 _68251 _68248 _68249) (@lem5213773 _68248 _68249 _68250 _68251)). Qed.
Lemma lem5213808 (x' : real -> real) (x'' : real -> real) (b' : real) : term1161 x' x'' b'.
Proof. exact (@lem5213807 (term1005 x' b') (@I (real -> real) real_neg b') (term1006 x'' b') (@I (real -> real) real_neg b')). Qed.
Lemma lem5213811 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1061 x'' b'.
Proof. exact (@lem5213808 x' x'' b' (@lem5213805 b' x'' x' s a h1 h2 h3)). Qed.
Lemma lem5213812 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1162 x'' b'.
Proof. exact (fun h0 : term1059 x'' b' => @lem5213811 b' x'' x' s a h1 h2 h3). Qed.
Lemma lem5213814 (p : Prop) : (term1122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5213815 (x'' : real -> real) (b' : real) : (term1162 x'' b') = (term1061 x'' b').
Proof. exact (@lem5213814 (term1059 x'' b')). Qed.
Lemma lem5213816 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : (term21 s) = a) : term1061 x'' b'.
Proof. exact (EQ_MP (@lem5213815 x'' b') (@lem5213812 b' x'' x' s a h1 h2 h3)). Qed.
Lemma lem5213818 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5213821 (b' : real) (_67976 : real) (s : real -> Prop) : (term851 s _67976 b') = (term1163 b' _67976 s).
Proof. exact (@lem5213818 (term823 _67976 b') (term724 _67976 s)). Qed.
Lemma lem5213824 (_67976 : real) (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term1163 b' _67976 s.
Proof. exact (EQ_MP (@lem5213821 b' _67976 s) (@lem5211625 _67976 s a b' h1)). Qed.
Lemma lem5213825 (x'' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term855 s a b') : term1164 x'' b' s.
Proof. exact (@lem5213824 (term1005 x'' b') s a b' h1). Qed.
Lemma lem5213828 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : term855 s a b') (h4 : (term21 s) = a) : term1042 x'' b' s.
Proof. exact (@lem5213825 x'' s a b' h3 (@lem5213816 b' x'' x' s a h1 h2 h4)). Qed.
Lemma lem5213829 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : term855 s a b') (h4 : (term21 s) = a) : term1165 x'' b' s.
Proof. exact (fun h0 : term1040 x'' b' s => @lem5213828 x'' x' b' s a h1 h2 h3 h4). Qed.
Lemma lem5213831 (p : Prop) : (term1122 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5213832 (x'' : real -> real) (b' : real) (s : real -> Prop) : (term1165 x'' b' s) = (term1042 x'' b' s).
Proof. exact (@lem5213831 (term1040 x'' b' s)). Qed.
Lemma lem5213833 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : term855 s a b') (h4 : (term21 s) = a) : term1042 x'' b' s.
Proof. exact (EQ_MP (@lem5213832 x'' b' s) (@lem5213829 x'' x' b' s a h1 h2 h3 h4)). Qed.
Lemma lem5213844 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5213845 (x'' : real -> real) (s : real -> Prop) (_67979 : real) : (term1166 x'' _67979 s) = (term980 x'' s _67979).
Proof. exact (@lem5213844 (term864 x'' _67979 s) (term130 s _67979)). Qed.
Lemma lem5213851 (x'' : real -> real) (s : real -> Prop) (_67979 : real) : (term1167 x'' s _67979) = (term1167 x'' s _67979).
Proof. exact (eq_refl (term1167 x'' s _67979)). Qed.
Lemma lem5213852 (x'' : real -> real) (s : real -> Prop) (_67979 : real) : ((term980 x'' s _67979) = (term1166 x'' _67979 s)) = ((term980 x'' s _67979) = (term980 x'' s _67979)).
Proof. exact (MK_COMB (@lem5213851 x'' s _67979) (@lem5213845 x'' s _67979)). Qed.
Lemma lem5213854 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5213855 (x : Prop) : (x = x) = True.
Proof. exact (@lem5213854 Prop x). Qed.
Lemma lem5213856 (x'' : real -> real) (s : real -> Prop) (_67979 : real) : ((term980 x'' s _67979) = (term980 x'' s _67979)) = True.
Proof. exact (@lem5213855 (term980 x'' s _67979)). Qed.
Lemma lem5213857 (x'' : real -> real) (_67979 : real) (s : real -> Prop) : ((term980 x'' s _67979) = (term1166 x'' _67979 s)) = True.
Proof. exact (TRANS (@lem5213852 x'' s _67979) (@lem5213856 x'' s _67979)). Qed.
Lemma lem5213858 (x'' : real -> real) (_67979 : real) (s : real -> Prop) : True = ((term980 x'' s _67979) = (term1166 x'' _67979 s)).
Proof. exact (SYM (@lem5213857 x'' _67979 s)). Qed.
Lemma lem5213859 (x'' : real -> real) (_67979 : real) (s : real -> Prop) : (term980 x'' s _67979) = (term1166 x'' _67979 s).
Proof. exact (EQ_MP (@lem5213858 x'' _67979 s) (@lem0)). Qed.
Lemma lem5213860 (_67979 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1166 x'' _67979 s.
Proof. exact (EQ_MP (@lem5213859 x'' _67979 s) (@lem5211690 _67979 x'' x' s a h1 h2)). Qed.
Lemma lem5213862 (b : Prop) (a : Prop) : (a \/ b) = (term1019 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5213865 (x'' : real -> real) (s : real -> Prop) (_67979 : real) : (term1166 x'' _67979 s) = (term1168 x'' s _67979).
Proof. exact (@lem5213862 (term864 x'' _67979 s) (term130 s _67979)). Qed.
Lemma lem5213868 (_67979 : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1168 x'' s _67979.
Proof. exact (EQ_MP (@lem5213865 x'' s _67979) (@lem5213860 _67979 x'' x' s a h1 h2)). Qed.
Lemma lem5213869 (b' : real) (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : (term21 s) = a) : term1169 x'' s b'.
Proof. exact (@lem5213868 (@I (real -> real) real_neg b') x'' x' s a h1 h2). Qed.
Lemma lem5213872 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term962 s b') (h2 : term892 x'' s x' a) (h3 : term855 s a b') (h4 : (term21 s) = a) : term1136 s b'.
Proof. exact (@lem5213869 b' x'' x' s a h2 h4 (@lem5213833 x'' x' b' s a h1 h2 h3 h4)). Qed.
Lemma lem5213873 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : term1170 s b'.
Proof. exact (fun h0 : term962 s b' => @lem5213872 x'' x' b' s a h0 h1 h2 h3). Qed.
Lemma lem5213875 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213876 (s : real -> Prop) (b' : real) : (term1170 s b') = (term1136 s b').
Proof. exact (@lem5213875 (term1136 s b')). Qed.
Lemma lem5213877 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : term1136 s b'.
Proof. exact (EQ_MP (@lem5213876 s b') (@lem5213873 x'' x' b' s a h1 h2 h3)). Qed.
Lemma lem5213880 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5213882 (s : real -> Prop) (b' : real) : (term962 s b') = (term1171 s b').
Proof. exact (@lem5213880 (term1136 s b')). Qed.
Lemma lem5213885 (b' : real) (s : real -> Prop) (a : real) (h1 : term855 s a b') (h2 : (term21 s) = a) : term1171 s b'.
Proof. exact (EQ_MP (@lem5213882 s b') (@lem5211638 b' s a h1 h2)). Qed.
Lemma lem5213888 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : False.
Proof. exact (@lem5213885 b' s a h2 h3 (@lem5213877 x'' x' b' s a h1 h2 h3)). Qed.
Lemma lem5213889 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : term995.
Proof. exact (fun h0 : ~ False => @lem5213888 x'' x' b' s a h1 h2 h3). Qed.
Lemma lem5213891 (p : Prop) : (term986 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5213892 : term995 = False.
Proof. exact (@lem5213891 False). Qed.
Lemma lem5213894 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213892) (@lem5213889 x'' x' b' s a h1 h2 h3)). Qed.
Lemma lem5213895 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : False.
Proof. exact (EQ_MP (@lem5213284) (@lem5213281 x'' x' s a b' h1 h2)). Qed.
Lemma lem5213896 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : (term43 s) = False.
Proof. exact (prop_ext (fun h5 : term43 s => @lem5212795 s x h1 h2 h3 h4) (fun h5 : False => @lem5211191 s h3)). Qed.
Lemma lem5213898 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : False.
Proof. exact (EQ_MP (@lem5213896 s x h1 h2 h3 h4) (@lem5211191 s h3)). Qed.
Lemma lem5213899 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5212576) (@lem5212573 x'' x' b' s a h1 h2 h3)). Qed.
Lemma lem5213900 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : False.
Proof. exact (EQ_MP (@lem5212327) (@lem5212324 x'' x' s b h1 h2 h3)). Qed.
Lemma lem5213901 (s : real -> Prop) (b' : real) (a : real) (h1 : term896 s) (h2 : term196) (h3 : term860 s b' a) : False.
Proof. exact (EQ_MP (@lem5211814) (@lem5211811 s b' a h1 h2 h3)). Qed.
Lemma lem5213902 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : ((term21 s) = a) = False.
Proof. exact (prop_ext (fun h4 : (term21 s) = a => @lem5213894 x'' x' b' s a h1 h2 h3) (fun h4 : False => @lem5210570 s a h3)). Qed.
Lemma lem5213903 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213902 x'' x' b' s a h1 h2 h3) (@lem5210570 s a h3)). Qed.
Lemma lem5213904 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : (term43 s) = False.
Proof. exact (prop_ext (fun h5 : term43 s => @lem5213898 s x h1 h2 h3 h4) (fun h5 : False => @lem5210462 s h3)). Qed.
Lemma lem5213905 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : False.
Proof. exact (EQ_MP (@lem5213904 s x h1 h2 h3 h4) (@lem5210462 s h3)). Qed.
Lemma lem5213906 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : ((term21 s) = a) = False.
Proof. exact (prop_ext (fun h4 : (term21 s) = a => @lem5213899 x'' x' b' s a h1 h2 h3) (fun h4 : False => @lem5210400 s a h3)). Qed.
Lemma lem5213907 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213906 x'' x' b' s a h1 h2 h3) (@lem5210400 s a h3)). Qed.
Lemma lem5213908 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : ((term21 s) = a) = False.
Proof. exact (prop_ext (fun h4 : (term21 s) = a => @lem5213903 x'' x' b' s a h1 h2 h3) (fun h4 : False => @lem5209883 s a h3)). Qed.
Lemma lem5213909 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213908 x'' x' b' s a h1 h2 h3) (@lem5209883 s a h3)). Qed.
Lemma lem5213910 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : (term43 s) = False.
Proof. exact (prop_ext (fun h5 : term43 s => @lem5213905 s x h1 h2 h3 h4) (fun h5 : False => @lem5209571 s h3)). Qed.
Lemma lem5213911 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : False.
Proof. exact (EQ_MP (@lem5213910 s x h1 h2 h3 h4) (@lem5209571 s h3)). Qed.
Lemma lem5213912 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : ((term21 s) = a) = False.
Proof. exact (prop_ext (fun h4 : (term21 s) = a => @lem5213907 x'' x' b' s a h1 h2 h3) (fun h4 : False => @lem5209384 s a h3)). Qed.
Lemma lem5213913 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213912 x'' x' b' s a h1 h2 h3) (@lem5209384 s a h3)). Qed.
Lemma lem5213914 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : ((term21 s) = a) = False.
Proof. exact (prop_ext (fun h4 : (term21 s) = a => @lem5213909 x'' x' b' s a h1 h2 h3) (fun h4 : False => @lem5209883 s a h3)). Qed.
Lemma lem5213915 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term855 s a b') (h3 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213914 x'' x' b' s a h1 h2 h3) (@lem5209883 s a h3)). Qed.
Lemma lem5213916 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : (term894 x'' s x') = False.
Proof. exact (prop_ext (fun h3 : term894 x'' s x' => @lem5213895 x'' x' s a b' h1 h2) (fun h3 : False => @lem5209862 x'' s x' h1)). Qed.
Lemma lem5213917 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (a : real) (b' : real) (h1 : term894 x'' s x') (h2 : term855 s a b') : False.
Proof. exact (EQ_MP (@lem5213916 x'' x' s a b' h1 h2) (@lem5209862 x'' s x' h1)). Qed.
Lemma lem5213918 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : (term896 s) = False.
Proof. exact (prop_ext (fun h5 : term896 s => @lem5213911 s x h1 h2 h3 h4) (fun h5 : False => @lem5209715 s h1)). Qed.
Lemma lem5213919 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : False.
Proof. exact (EQ_MP (@lem5213918 s x h1 h2 h3 h4) (@lem5209715 s h1)). Qed.
Lemma lem5213920 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : (term43 s) = False.
Proof. exact (prop_ext (fun h5 : term43 s => @lem5213919 s x h1 h2 h3 h4) (fun h5 : False => @lem5209571 s h3)). Qed.
Lemma lem5213921 (s : real -> Prop) (x : type1023) (h1 : term896 s) (h2 : term196) (h3 : term43 s) (h4 : term818 x) : False.
Proof. exact (EQ_MP (@lem5213920 s x h1 h2 h3 h4) (@lem5209571 s h3)). Qed.
Lemma lem5213922 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : ((term21 s) = a) = False.
Proof. exact (prop_ext (fun h4 : (term21 s) = a => @lem5213913 x'' x' b' s a h1 h2 h3) (fun h4 : False => @lem5209384 s a h3)). Qed.
Lemma lem5213923 (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term892 x'' s x' a) (h2 : term860 s b' a) (h3 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213922 x'' x' b' s a h1 h2 h3) (@lem5209384 s a h3)). Qed.
Lemma lem5213924 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : (term894 x'' s x') = False.
Proof. exact (prop_ext (fun h4 : term894 x'' s x' => @lem5213900 x'' x' s b h1 h2 h3) (fun h4 : False => @lem5209363 x'' s x' h2)). Qed.
Lemma lem5213925 (x'' : real -> real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term35) (h2 : term894 x'' s x') (h3 : term44 s b) : False.
Proof. exact (EQ_MP (@lem5213924 x'' x' s b h1 h2 h3) (@lem5209363 x'' s x' h2)). Qed.
Lemma lem5213926 (s : real -> Prop) (b' : real) (a : real) (h1 : term896 s) (h2 : term196) (h3 : term860 s b' a) : (term896 s) = False.
Proof. exact (prop_ext (fun h4 : term896 s => @lem5213901 s b' a h1 h2 h3) (fun h4 : False => @lem5209225 s h1)). Qed.
Lemma lem5213927 (s : real -> Prop) (b' : real) (a : real) (h1 : term896 s) (h2 : term196) (h3 : term860 s b' a) : False.
Proof. exact (EQ_MP (@lem5213926 s b' a h1 h2 h3) (@lem5209225 s h1)). Qed.
Lemma lem5213928 (x : type1023) (a : real) (b' : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term196) (h2 : term43 s) (h3 : term818 x) (h4 : term855 s a b') (h5 : term898 x'' s x') : False.
Proof. exact (or_elim (@lem5209081 x'' s x' h5) (fun h0 : term896 s => @lem5213921 s x h0 h1 h2 h3) (fun h0 : term894 x'' s x' => @lem5213917 x'' x' s a b' h0 h4)). Qed.
Lemma lem5213929 (x : type1023) (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term196) (h2 : term43 s) (h3 : term818 x) (h4 : term855 s a b') (h5 : term658 x'' x' s a b') (h6 : (term21 s) = a) : False.
Proof. exact (or_elim (@lem5209064 x'' x' s a b' h5) (fun h0 : term898 x'' s x' => @lem5213928 x a b' x'' s x' h1 h2 h3 h4 h0) (fun h0 : term892 x'' s x' a => @lem5213915 x'' x' b' s a h0 h4 h6)). Qed.
Lemma lem5213930 (b : real) (b' : real) (a : real) (x'' : real -> real) (s : real -> Prop) (x' : real -> real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term860 s b' a) (h5 : term898 x'' s x') : False.
Proof. exact (or_elim (@lem5209073 x'' s x' h5) (fun h0 : term896 s => @lem5213927 s b' a h0 h2 h4) (fun h0 : term894 x'' s x' => @lem5213925 x'' x' s b h1 h0 h3)). Qed.
Lemma lem5213931 (b : real) (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term860 s b' a) (h5 : term658 x'' x' s a b') (h6 : (term21 s) = a) : False.
Proof. exact (or_elim (@lem5209064 x'' x' s a b' h5) (fun h0 : term898 x'' s x' => @lem5213930 b b' a x'' s x' h1 h2 h3 h4 h0) (fun h0 : term892 x'' s x' a => @lem5213923 x'' x' b' s a h0 h4 h6)). Qed.
Lemma lem5213932 (b : real) (x : type1023) (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term43 s) (h5 : term818 x) (h6 : term658 x'' x' s a b') (h7 : (term21 s) = a) : False.
Proof. exact (or_elim (@lem5209063 x'' x' s a b' h6) (fun h0 : term860 s b' a => @lem5213931 b x'' x' b' s a h1 h2 h3 h0 h6 h7) (fun h0 : term855 s a b' => @lem5213929 x x'' x' b' s a h2 h4 h5 h0 h6 h7)). Qed.
Lemma lem5213933 (b : real) (x : type1023) (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term43 s) (h5 : term818 x) (h6 : term658 x'' x' s a b') (h7 : (term21 s) = a) : (term818 x) = False.
Proof. exact (prop_ext (fun h8 : term818 x => @lem5213932 b x x'' x' b' s a h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5208817 x h5)). Qed.
Lemma lem5213934 (b : real) (x : type1023) (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term43 s) (h5 : term818 x) (h6 : term658 x'' x' s a b') (h7 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213933 b x x'' x' b' s a h1 h2 h3 h4 h5 h6 h7) (@lem5208817 x h5)). Qed.
Lemma lem5213935 (b : real) (x : type1023) (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term43 s) (h5 : term818 x) (h6 : term658 x'' x' s a b') (h7 : (term21 s) = a) : ((term21 s) = a) = False.
Proof. exact (prop_ext (fun h8 : (term21 s) = a => @lem5213934 b x x'' x' b' s a h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5208675 s a h7)). Qed.
Lemma lem5213936 (b : real) (x : type1023) (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term43 s) (h5 : term818 x) (h6 : term658 x'' x' s a b') (h7 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213935 b x x'' x' b' s a h1 h2 h3 h4 h5 h6 h7) (@lem5208675 s a h7)). Qed.
Lemma lem5213937 (b : real) (x : type1023) (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term43 s) (h5 : term818 x) (h6 : term658 x'' x' s a b') (h7 : (term21 s) = a) : (term43 s) = False.
Proof. exact (prop_ext (fun h8 : term43 s => @lem5213936 b x x'' x' b' s a h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5208644 s h4)). Qed.
Lemma lem5213938 (b : real) (x : type1023) (x'' : real -> real) (x' : real -> real) (b' : real) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term43 s) (h5 : term818 x) (h6 : term658 x'' x' s a b') (h7 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213937 b x x'' x' b' s a h1 h2 h3 h4 h5 h6 h7) (@lem5208644 s h4)). Qed.
Lemma lem5213939 (b : real) (x'' : real -> real) (x' : real -> real) (x : type1023) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term661 x'' x' s a) (h5 : term43 s) (h6 : term818 x) (h7 : (term21 s) = a) : False.
Proof. exact (ex_elim (@lem5208635 x'' x' s a h4) (fun b' : real => fun h0 : term660 x'' x' s a b' => @lem5213938 b x x'' x' b' s a h1 h2 h3 h5 h6 h0 h7)). Qed.
Lemma lem5213940 (b : real) (x' : real -> real) (x : type1023) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term663 x' s a) (h5 : term43 s) (h6 : term818 x) (h7 : (term21 s) = a) : False.
Proof. exact (ex_elim (@lem5208634 x' s a h4) (fun x'' : real -> real => fun h0 : term662 x' s a x'' => @lem5213939 b x'' x' x s a h1 h2 h3 h0 h5 h6 h7)). Qed.
Lemma lem5213941 (b : real) (x : type1023) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term196) (h3 : term44 s b) (h4 : term43 s) (h5 : term188 s a) (h6 : term818 x) (h7 : (term21 s) = a) : False.
Proof. exact (ex_elim (@lem5208078 s a h5) (fun x' : real -> real => fun h0 : term664 s a x' => @lem5213940 b x' x s a h1 h2 h3 h0 h4 h6 h7)). Qed.
Lemma lem5213942 (b : real) (s : real -> Prop) (a : real) (h1 : term189) (h2 : term35) (h3 : term196) (h4 : term44 s b) (h5 : term43 s) (h6 : term188 s a) (h7 : (term21 s) = a) : False.
Proof. exact (ex_elim (@lem5208619 h1) (fun x : type1023 => fun h0 : term820 x => @lem5213941 b x s a h2 h3 h4 h5 h6 h0 h7)). Qed.
Lemma lem5213943 (b : real) (s : real -> Prop) (a : real) (h1 : term189) (h2 : term35) (h3 : term196) (h4 : term44 s b) (h5 : term43 s) (h6 : term188 s a) (h7 : (term21 s) = a) : term196 = False.
Proof. exact (prop_ext (fun h8 : term196 => @lem5213942 b s a h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5208632 h3)). Qed.
Lemma lem5213944 (b : real) (s : real -> Prop) (a : real) (h1 : term189) (h2 : term35) (h3 : term196) (h4 : term44 s b) (h5 : term43 s) (h6 : term188 s a) (h7 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213943 b s a h1 h2 h3 h4 h5 h6 h7) (@lem5208632 h3)). Qed.
Lemma lem5213945 (b : real) (s : real -> Prop) (a : real) (h1 : term189) (h2 : term35) (h3 : term196) (h4 : term44 s b) (h5 : term43 s) (h6 : term188 s a) (h7 : (term21 s) = a) : ((term21 s) = a) = False.
Proof. exact (prop_ext (fun h8 : (term21 s) = a => @lem5213944 b s a h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5206828 s a h7)). Qed.
Lemma lem5213946 (b : real) (s : real -> Prop) (a : real) (h1 : term189) (h2 : term35) (h3 : term196) (h4 : term44 s b) (h5 : term43 s) (h6 : term188 s a) (h7 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213945 b s a h1 h2 h3 h4 h5 h6 h7) (@lem5206828 s a h7)). Qed.
Lemma lem5213947 (b : real) (s : real -> Prop) (a : real) (h1 : term189) (h2 : term35) (h3 : term196) (h4 : term44 s b) (h5 : term43 s) (h6 : term188 s a) (h7 : (term21 s) = a) : (term43 s) = False.
Proof. exact (prop_ext (fun h8 : term43 s => @lem5213946 b s a h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5206759 s h5)). Qed.
Lemma lem5213948 (b : real) (s : real -> Prop) (a : real) (h1 : term189) (h2 : term35) (h3 : term196) (h4 : term44 s b) (h5 : term43 s) (h6 : term188 s a) (h7 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213947 b s a h1 h2 h3 h4 h5 h6 h7) (@lem5206759 s h5)). Qed.
Lemma lem5213949 (b : real) (s : real -> Prop) (a : real) (h1 : term189) (h2 : term35) (h3 : term44 s b) (h4 : term43 s) (h5 : term188 s a) (h6 : (term21 s) = a) : term194.
Proof. exact (fun h0 : term196 => @lem5213948 b s a h1 h2 h0 h3 h4 h5 h6). Qed.
Lemma lem5213950 : term194 = term195.
Proof. exact (@lem69 term196). Qed.
Lemma lem5213951 (b : real) (s : real -> Prop) (a : real) (h1 : term189) (h2 : term35) (h3 : term44 s b) (h4 : term43 s) (h5 : term188 s a) (h6 : (term21 s) = a) : term195.
Proof. exact (EQ_MP (@lem5213950) (@lem5213949 b s a h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5213952 (b : real) (s : real -> Prop) (a : real) (h1 : term35) (h2 : term44 s b) (h3 : term43 s) (h4 : term188 s a) (h5 : (term21 s) = a) : term199.
Proof. exact (fun h0 : term189 => @lem5213951 b s a h0 h1 h2 h3 h4 h5). Qed.
Lemma lem5213953 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : term188 s a) (h4 : (term21 s) = a) : term202.
Proof. exact (fun h0 : term35 => @lem5213952 b s a h0 h1 h2 h3 h4). Qed.
Lemma lem5213954 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : term205 s a.
Proof. exact (fun h0 : term188 s a => @lem5213953 b s a h1 h2 h0 h3). Qed.
Lemma lem5213955 (a : real) (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term208 s a.
Proof. exact (fun h0 : (term21 s) = a => @lem5213954 b s a h1 h2 h0). Qed.
Lemma lem5213956 (b : real) (a : real) (s : real -> Prop) (h1 : term43 s) : term210 b s a.
Proof. exact (fun h0 : term44 s b => @lem5213955 a b s h0 h1). Qed.
Lemma lem5213957 (b : real) (s : real -> Prop) (a : real) : term212 b s a.
Proof. exact (fun h0 : term43 s => @lem5213956 b a s h0). Qed.
Lemma lem5213962 (s : real -> Prop) (a : real) : term216 s a.
Proof. exact (fun b : real => @lem5213957 b s a). Qed.
Lemma lem5213967 (a : real) : term220 a.
Proof. exact (fun s : real -> Prop => @lem5213962 s a). Qed.
Lemma lem5213972 : term224.
Proof. exact (fun a : real => @lem5213967 a). Qed.
Lemma lem5213973 : term223.
Proof. exact (EQ_MP (@lem5206746) (@lem5213972)). Qed.
Lemma lem5213974 (a : real) : term1172 a.
Proof. exact (@lem5213973 a). Qed.
Lemma lem5213975 (a : real) : (term1172 a) = (term219 a).
Proof. exact (eq_refl (term1172 a)). Qed.
Lemma lem5213976 (a : real) : term219 a.
Proof. exact (EQ_MP (@lem5213975 a) (@lem5213974 a)). Qed.
Lemma lem5213977 (a : real) (s : real -> Prop) : term1173 a s.
Proof. exact (@lem5213976 a s). Qed.
Lemma lem5213978 (s : real -> Prop) (a : real) : (term1173 a s) = (term215 s a).
Proof. exact (eq_refl (term1173 a s)). Qed.
Lemma lem5213979 (s : real -> Prop) (a : real) : term215 s a.
Proof. exact (EQ_MP (@lem5213978 s a) (@lem5213977 a s)). Qed.
Lemma lem5213980 (s : real -> Prop) (a : real) (b : real) : term1174 s a b.
Proof. exact (@lem5213979 s a b). Qed.
Lemma lem5213981 (b : real) (s : real -> Prop) (a : real) : (term1174 s a b) = (term190 b s a).
Proof. exact (eq_refl (term1174 s a b)). Qed.
Lemma lem5213982 (b : real) (s : real -> Prop) (a : real) : term190 b s a.
Proof. exact (EQ_MP (@lem5213981 b s a) (@lem5213980 s a b)). Qed.
Lemma lem5213984 (b : real) (s : real -> Prop) (a : real) : term190 b s a.
Proof. exact (@lem5206027 b s a (@lem5213982 b s a)). Qed.
Lemma lem5213985 (b : real) (a : real) (s : real -> Prop) (h1 : term43 s) : term209 b s a.
Proof. exact (@lem5213984 b s a (@lem5205749 s h1)). Qed.
Lemma lem5213986 (a : real) (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term207 s a.
Proof. exact (@lem5213985 b a s h2 (@lem5205751 s b h1)). Qed.
Lemma lem5213987 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : term204 s a.
Proof. exact (@lem5213986 a b s h1 h2 (@lem5205747 s a h3)). Qed.
Lemma lem5213988 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : term188 s a) (h4 : (term21 s) = a) : term201.
Proof. exact (@lem5213987 b s a h1 h2 h4 (@lem5206009 s a h3)). Qed.
Lemma lem5213989 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : term188 s a) (h4 : (term21 s) = a) : term198.
Proof. exact (@lem5213988 b s a h1 h2 h3 h4 (@lem1362291)). Qed.
Lemma lem5213990 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : term188 s a) (h4 : (term21 s) = a) : term194.
Proof. exact (@lem5213989 b s a h1 h2 h3 h4 (@lem5206010)). Qed.
Lemma lem5213991 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : term188 s a) (h4 : (term21 s) = a) : False.
Proof. exact (@lem5213990 b s a h1 h2 h3 h4 (@lem1358662)). Qed.
Lemma lem5213992 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : term188 s a) (h4 : (term21 s) = a) : (term188 s a) = False.
Proof. exact (prop_ext (fun h5 : term188 s a => @lem5213991 b s a h1 h2 h3 h4) (fun h5 : False => @lem5206009 s a h3)). Qed.
Lemma lem5213993 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : term188 s a) (h4 : (term21 s) = a) : False.
Proof. exact (EQ_MP (@lem5213992 b s a h1 h2 h3 h4) (@lem5206009 s a h3)). Qed.
Lemma lem5213994 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : term187 s a.
Proof. exact (fun h0 : term188 s a => @lem5213993 b s a h1 h2 h0 h3). Qed.
Lemma lem5213995 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : term185 s a.
Proof. exact (EQ_MP (@lem5206008 s a) (@lem5213994 b s a h1 h2 h3)). Qed.
Lemma lem5213996 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : term153 s a.
Proof. exact (EQ_MP (@lem5206004 s a) (@lem5213995 b s a h1 h2 h3)). Qed.
Lemma lem5213997 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : ((term21 s) = a) = (term153 s a).
Proof. exact (prop_ext (fun h4 : (term21 s) = a => @lem5213996 b s a h1 h2 h3) (fun h4 : term153 s a => @lem5205747 s a h3)). Qed.
Lemma lem5213998 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : term153 s a.
Proof. exact (EQ_MP (@lem5213997 b s a h1 h2 h3) (@lem5205747 s a h3)). Qed.
Lemma lem5213999 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : term119 s.
Proof. exact (EQ_MP (@lem5205803 s a h3) (@lem5213998 b s a h1 h2 h3)). Qed.
Lemma lem5214000 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : (term44 s b) = (term119 s).
Proof. exact (prop_ext (fun h4 : term44 s b => @lem5213999 b s a h1 h2 h3) (fun h4 : term119 s => @lem5205751 s b h1)). Qed.
Lemma lem5214001 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : term119 s.
Proof. exact (EQ_MP (@lem5214000 b s a h1 h2 h3) (@lem5205751 s b h1)). Qed.
Lemma lem5214002 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : (term43 s) = (term119 s).
Proof. exact (prop_ext (fun h4 : term43 s => @lem5214001 b s a h1 h2 h3) (fun h4 : term119 s => @lem5205749 s h2)). Qed.
Lemma lem5214003 (b : real) (s : real -> Prop) (a : real) (h1 : term44 s b) (h2 : term43 s) (h3 : (term21 s) = a) : term119 s.
Proof. exact (EQ_MP (@lem5214002 b s a h1 h2 h3) (@lem5205749 s h2)). Qed.
Lemma lem5214004 (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term119 s.
Proof. exact (ex_elim (@lem5205448 s) (fun a : real => fun h0 : term23 s a => @lem5214003 b s a h1 h2 h0)). Qed.
Lemma lem5214005 (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term118 s.
Proof. exact (EQ_MP (@lem5205746 s) (@lem5214004 b s h1 h2)). Qed.
Lemma lem5214006 (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term115 s.
Proof. exact (@lem5214005 b s h1 h2 (@lem5205454 s)). Qed.
Lemma lem5214007 (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term92 s.
Proof. exact (ex_intro (term91 s) (term1175 s) (@lem5214006 b s h1 h2)). Qed.
Lemma lem5214008 (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term71 s.
Proof. exact (EQ_MP (@lem5205644 s) (@lem5214007 b s h1 h2)). Qed.
Lemma lem5214009 (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term68 s.
Proof. exact (EQ_MP (@lem5205588 s) (@lem5214008 b s h1 h2)). Qed.
Lemma lem5214010 (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term67 s.
Proof. exact (EQ_MP (@lem5205579 s) (@lem5214009 b s h1 h2)). Qed.
Lemma lem5214011 (s : real -> Prop) (h1 : term41 s) : term42 s.
Proof. exact (proj2 (@lem5205478 s h1)). Qed.
Lemma lem5214012 (s : real -> Prop) (h1 : term41 s) : term43 s.
Proof. exact (proj1 (@lem5205478 s h1)). Qed.
Lemma lem5214013 (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : (term44 s b) = (term67 s).
Proof. exact (prop_ext (fun h3 : term44 s b => @lem5214010 b s h1 h2) (fun h3 : term67 s => @lem5205481 s b h1)). Qed.
Lemma lem5214014 (b : real) (s : real -> Prop) (h1 : term44 s b) (h2 : term43 s) : term67 s.
Proof. exact (EQ_MP (@lem5214013 b s h1 h2) (@lem5205481 s b h1)). Qed.
Lemma lem5214015 (s : real -> Prop) (h1 : term42 s) (h2 : term43 s) : term67 s.
Proof. exact (ex_elim (@lem5205479 s h1) (fun b : real => fun h0 : term1176 s b => @lem5214014 b s h0 h2)). Qed.
Lemma lem5214016 (s : real -> Prop) (h1 : term42 s) (h2 : term43 s) : (term43 s) = (term67 s).
Proof. exact (prop_ext (fun h3 : term43 s => @lem5214015 s h1 h2) (fun h3 : term67 s => @lem5205480 s h2)). Qed.
Lemma lem5214017 (s : real -> Prop) (h1 : term42 s) (h2 : term43 s) : term67 s.
Proof. exact (EQ_MP (@lem5214016 s h1 h2) (@lem5205480 s h2)). Qed.
Lemma lem5214018 (s : real -> Prop) (h1 : term43 s) (h2 : term41 s) : (term42 s) = (term67 s).
Proof. exact (prop_ext (fun h3 : term42 s => @lem5214017 s h3 h1) (fun h3 : term67 s => @lem5214011 s h2)). Qed.
Lemma lem5214019 (s : real -> Prop) (h1 : term43 s) (h2 : term41 s) : term67 s.
Proof. exact (EQ_MP (@lem5214018 s h1 h2) (@lem5214011 s h2)). Qed.
Lemma lem5214020 (s : real -> Prop) (h1 : term41 s) : (term43 s) = (term67 s).
Proof. exact (prop_ext (fun h2 : term43 s => @lem5214019 s h2 h1) (fun h2 : term67 s => @lem5214012 s h1)). Qed.
Lemma lem5214021 (s : real -> Prop) (h1 : term41 s) : term67 s.
Proof. exact (EQ_MP (@lem5214020 s h1) (@lem5214012 s h1)). Qed.
Lemma lem5214022 (s : real -> Prop) : term1177 s.
Proof. exact (fun h0 : term41 s => @lem5214021 s h0). Qed.
Lemma lem5214027 : term1178.
Proof. exact (fun s : real -> Prop => @lem5214022 s). Qed.
