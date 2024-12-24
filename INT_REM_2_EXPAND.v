Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_2_EXPAND_term_abbrevs.
Require Import INT_REM_2_DIVIDES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem2725360 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2725361 : term1 = term2.
Proof. exact (@lem2725360 term1). Qed.
Lemma lem2725362 : term2 = term1.
Proof. exact (SYM (@lem2725361)). Qed.
Lemma lem2725363 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2725366 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2725367 : term5.
Proof. exact (fun h0 : term4 => @lem2725366 h0). Qed.
Lemma lem2725368 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2725369 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2725370 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2725368 h2 (@lem2725369 h1)). Qed.
Lemma lem2725371 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem2725370 h1 h0). Qed.
Lemma lem2725372 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2725373 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2725371 h1 (@lem2725372 h2)). Qed.
Lemma lem2725374 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem2725373 h0 h1). Qed.
Lemma lem2725375 : term7.
Proof. exact (fun h0 : term5 => @lem2725374 h0). Qed.
Lemma lem2725378 : term5.
Proof. exact (@lem2725375 (@lem2725367)). Qed.
Lemma lem2725386 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2725387 : term8 = term9.
Proof. exact (@lem2725386 term10). Qed.
Lemma lem2725398 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem2725405 : term4 = term12.
Proof. exact (MK_COMB (@lem2725398) (@lem2725387)). Qed.
Lemma lem2725412 (n : int) : (((term13 n) = term14) = (term15 n)) = (((term13 n) = term14) = (term15 n)).
Proof. exact (eq_refl (((term13 n) = term14) = (term15 n))). Qed.
Lemma lem2725413 : term16 = term16.
Proof. exact (fun_ext (fun n : int => @lem2725412 n)). Qed.
Lemma lem2725414 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725415 : term17 = term17.
Proof. exact (MK_COMB (@lem2725414) (@lem2725413)). Qed.
Lemma lem2725420 (n : int) : (((term13 n) = term18) = (term19 n)) = (((term13 n) = term18) = (term19 n)).
Proof. exact (eq_refl (((term13 n) = term18) = (term19 n))). Qed.
Lemma lem2725421 : term20 = term20.
Proof. exact (fun_ext (fun n : int => @lem2725420 n)). Qed.
Lemma lem2725422 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725423 : term21 = term21.
Proof. exact (MK_COMB (@lem2725422) (@lem2725421)). Qed.
Lemma lem2725424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725425 : term22 = term22.
Proof. exact (MK_COMB (@lem2725424) (@lem2725423)). Qed.
Lemma lem2725426 : term10 = term10.
Proof. exact (MK_COMB (@lem2725425) (@lem2725415)). Qed.
Lemma lem2725427 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2725428 : term9 = term9.
Proof. exact (MK_COMB (@lem2725427) (@lem2725426)). Qed.
Lemma lem2725432 (x : int) (h1 : (term19 x) = False) : (term19 x) = False.
Proof. exact (h1). Qed.
Lemma lem2725433 : (@COND int) = (@COND int).
Proof. exact (eq_refl (@COND int)). Qed.
Lemma lem2725434 (x : int) (h1 : (term19 x) = False) : (term23 x) = (@COND int False).
Proof. exact (MK_COMB (@lem2725433) (@lem2725432 x h1)). Qed.
Lemma lem2725435 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2725436 (x : int) (h1 : (term19 x) = False) : (term24 x) = term25.
Proof. exact (MK_COMB (@lem2725434 x h1) (@lem2725435)). Qed.
Lemma lem2725437 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2725438 (x : int) (h1 : (term19 x) = False) : (term26 x) = term27.
Proof. exact (MK_COMB (@lem2725436 x h1) (@lem2725437)). Qed.
Lemma lem2725440 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem2725441 (t1 : int) (t2 : int) : (@COND int False t1 t2) = t2.
Proof. exact (@lem2725440 int t1 t2). Qed.
Lemma lem2725442 : term27 = term14.
Proof. exact (@lem2725441 term18 term14). Qed.
Lemma lem2725443 (x : int) (h1 : (term19 x) = False) : (term26 x) = term14.
Proof. exact (TRANS (@lem2725438 x h1) (@lem2725442)). Qed.
Lemma lem2725444 (x : int) : (term28 x) = (term28 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2725445 (x : int) (h1 : (term19 x) = False) : ((term13 x) = (term26 x)) = ((term13 x) = term14).
Proof. exact (MK_COMB (@lem2725444 x) (@lem2725443 x h1)). Qed.
Lemma lem2725448 (x : int) : term29 x.
Proof. exact (fun h0 : (term19 x) = False => @lem2725445 x h0). Qed.
Lemma lem2725450 (x : int) (h1 : (term19 x) = True) : (term19 x) = True.
Proof. exact (h1). Qed.
Lemma lem2725451 : (@COND int) = (@COND int).
Proof. exact (eq_refl (@COND int)). Qed.
Lemma lem2725452 (x : int) (h1 : (term19 x) = True) : (term23 x) = (@COND int True).
Proof. exact (MK_COMB (@lem2725451) (@lem2725450 x h1)). Qed.
Lemma lem2725453 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2725454 (x : int) (h1 : (term19 x) = True) : (term24 x) = term30.
Proof. exact (MK_COMB (@lem2725452 x h1) (@lem2725453)). Qed.
Lemma lem2725455 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2725456 (x : int) (h1 : (term19 x) = True) : (term26 x) = term31.
Proof. exact (MK_COMB (@lem2725454 x h1) (@lem2725455)). Qed.
Lemma lem2725458 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem2725459 (t2 : int) (t1 : int) : (@COND int True t1 t2) = t1.
Proof. exact (@lem2725458 int t2 t1). Qed.
Lemma lem2725460 : term31 = term18.
Proof. exact (@lem2725459 term14 term18). Qed.
Lemma lem2725461 (x : int) (h1 : (term19 x) = True) : (term26 x) = term18.
Proof. exact (TRANS (@lem2725456 x h1) (@lem2725460)). Qed.
Lemma lem2725462 (x : int) : (term28 x) = (term28 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2725463 (x : int) (h1 : (term19 x) = True) : ((term13 x) = (term26 x)) = ((term13 x) = term18).
Proof. exact (MK_COMB (@lem2725462 x) (@lem2725461 x h1)). Qed.
Lemma lem2725466 (x : int) : term32 x.
Proof. exact (fun h0 : (term19 x) = True => @lem2725463 x h0). Qed.
Lemma lem2725467 (x : int) : term33 x.
Proof. exact (conj (@lem2725448 x) (@lem2725466 x)). Qed.
Lemma lem2725469 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term34 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem2725470 (x : int) : term35 x.
Proof. exact (@lem2725469 ((term13 x) = (term26 x)) ((term13 x) = term18) (term19 x) ((term13 x) = term14)). Qed.
Lemma lem2725503 (x : int) : ((term13 x) = (term26 x)) = (term36 x).
Proof. exact (@lem2725470 x (@lem2725467 x)). Qed.
Lemma lem2725504 : term37 = term38.
Proof. exact (fun_ext (fun x : int => @lem2725503 x)). Qed.
Lemma lem2725505 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725506 : term1 = term39.
Proof. exact (MK_COMB (@lem2725505) (@lem2725504)). Qed.
Lemma lem2725507 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2725508 : term3 = term40.
Proof. exact (MK_COMB (@lem2725507) (@lem2725506)). Qed.
Lemma lem2725509 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2725510 : term11 = term41.
Proof. exact (MK_COMB (@lem2725509) (@lem2725508)). Qed.
Lemma lem2725511 : term12 = term42.
Proof. exact (MK_COMB (@lem2725510) (@lem2725428)). Qed.
Lemma lem2725542 : term4 = term42.
Proof. exact (TRANS (@lem2725405) (@lem2725511)). Qed.
Lemma lem2725543 : term42 = term4.
Proof. exact (SYM (@lem2725542)). Qed.
Lemma lem2725544 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem2725545 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem2725548 (x : int) : (term43 x) = (term19 x).
Proof. exact (@lem16933 (term19 x)). Qed.
Lemma lem2725549 (x : int) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem2725550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725551 (x : int) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem2725550) (@lem2725548 x)). Qed.
Lemma lem2725552 (x : int) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem2725551 x) (@lem2725549 x)). Qed.
Lemma lem2725553 (x : int) : (term49 x) = (term47 x).
Proof. exact (@lem17160 (term15 x) ((term13 x) = term18)). Qed.
Lemma lem2725554 (x : int) : (term49 x) = (term48 x).
Proof. exact (TRANS (@lem2725553 x) (@lem2725552 x)). Qed.
Lemma lem2725561 (x : int) : (term50 x) = (term51 x).
Proof. exact (@lem17160 (term19 x) ((term13 x) = term14)). Qed.
Lemma lem2725562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2725563 (x : int) : (term52 x) = (term53 x).
Proof. exact (MK_COMB (@lem2725562) (@lem2725554 x)). Qed.
Lemma lem2725564 (x : int) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem2725563 x) (@lem2725561 x)). Qed.
Lemma lem2725565 (x : int) : (term56 x) = (term54 x).
Proof. exact (@lem17045 (term57 x) (term58 x)). Qed.
Lemma lem2725566 (x : int) : (term56 x) = (term55 x).
Proof. exact (TRANS (@lem2725565 x) (@lem2725564 x)). Qed.
Lemma lem2725567 (P : int -> Prop) : (term59 P) = (term60 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2725568 : term40 = term61.
Proof. exact (@lem2725567 term38). Qed.
Lemma lem2725569 (x : int) : (term62 x) = (term36 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem2725570 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2725571 (x : int) : (term63 x) = (term56 x).
Proof. exact (MK_COMB (@lem2725570) (@lem2725569 x)). Qed.
Lemma lem2725572 (x : int) : (term63 x) = (term55 x).
Proof. exact (TRANS (@lem2725571 x) (@lem2725566 x)). Qed.
Lemma lem2725573 : term64 = term65.
Proof. exact (fun_ext (fun x : int => @lem2725572 x)). Qed.
Lemma lem2725574 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2725575 : term61 = term66.
Proof. exact (MK_COMB (@lem2725574) (@lem2725573)). Qed.
Lemma lem2725576 : term40 = term66.
Proof. exact (TRANS (@lem2725568) (@lem2725575)). Qed.
Lemma lem2725578 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem2725579 (P : int -> Prop) (Q : int -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem2725578 int P Q). Qed.
Lemma lem2725580 : term71 = term72.
Proof. exact (@lem2725579 term73 term74). Qed.
Lemma lem2725581 (x : int) : (term75 x) = (term48 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem2725582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2725583 (x : int) : (term76 x) = (term53 x).
Proof. exact (MK_COMB (@lem2725582) (@lem2725581 x)). Qed.
Lemma lem2725584 (x : int) : (term77 x) = (term51 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem2725585 (x : int) : (term78 x) = (term55 x).
Proof. exact (MK_COMB (@lem2725583 x) (@lem2725584 x)). Qed.
Lemma lem2725586 : term79 = term65.
Proof. exact (fun_ext (fun x : int => @lem2725585 x)). Qed.
Lemma lem2725587 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2725588 : term71 = term66.
Proof. exact (MK_COMB (@lem2725587) (@lem2725586)). Qed.
Lemma lem2725589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2725590 : term80 = term81.
Proof. exact (MK_COMB (@lem2725589) (@lem2725588)). Qed.
Lemma lem2725591 (x : int) : (term75 x) = (term48 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem2725592 : term82 = term73.
Proof. exact (fun_ext (fun x : int => @lem2725591 x)). Qed.
Lemma lem2725593 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2725594 : term83 = term84.
Proof. exact (MK_COMB (@lem2725593) (@lem2725592)). Qed.
Lemma lem2725595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2725596 : term85 = term86.
Proof. exact (MK_COMB (@lem2725595) (@lem2725594)). Qed.
Lemma lem2725597 (x : int) : (term77 x) = (term51 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem2725598 : term87 = term74.
Proof. exact (fun_ext (fun x : int => @lem2725597 x)). Qed.
Lemma lem2725599 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2725600 : term88 = term89.
Proof. exact (MK_COMB (@lem2725599) (@lem2725598)). Qed.
Lemma lem2725601 : term72 = term90.
Proof. exact (MK_COMB (@lem2725596) (@lem2725600)). Qed.
Lemma lem2725602 : (term71 = term72) = (term66 = term90).
Proof. exact (MK_COMB (@lem2725590) (@lem2725601)). Qed.
Lemma lem2725603 : term66 = term90.
Proof. exact (EQ_MP (@lem2725602) (@lem2725580)). Qed.
Lemma lem2725701 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term68 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2725702 (P : int -> Prop) (Q : int -> Prop) : (term70 P Q) = (term69 P Q).
Proof. exact (@lem2725701 int P Q). Qed.
Lemma lem2725703 : term72 = term71.
Proof. exact (@lem2725702 term73 term74). Qed.
Lemma lem2725704 (x : int) : (term75 x) = (term48 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem2725705 : term82 = term73.
Proof. exact (fun_ext (fun x : int => @lem2725704 x)). Qed.
Lemma lem2725706 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2725707 : term83 = term84.
Proof. exact (MK_COMB (@lem2725706) (@lem2725705)). Qed.
Lemma lem2725708 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2725709 : term85 = term86.
Proof. exact (MK_COMB (@lem2725708) (@lem2725707)). Qed.
Lemma lem2725710 (x : int) : (term77 x) = (term51 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem2725711 : term87 = term74.
Proof. exact (fun_ext (fun x : int => @lem2725710 x)). Qed.
Lemma lem2725712 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2725713 : term88 = term89.
Proof. exact (MK_COMB (@lem2725712) (@lem2725711)). Qed.
Lemma lem2725714 : term72 = term90.
Proof. exact (MK_COMB (@lem2725709) (@lem2725713)). Qed.
Lemma lem2725715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2725716 : term91 = term92.
Proof. exact (MK_COMB (@lem2725715) (@lem2725714)). Qed.
Lemma lem2725717 (x : int) : (term75 x) = (term48 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem2725718 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2725719 (x : int) : (term76 x) = (term53 x).
Proof. exact (MK_COMB (@lem2725718) (@lem2725717 x)). Qed.
Lemma lem2725720 (x : int) : (term77 x) = (term51 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem2725721 (x : int) : (term78 x) = (term55 x).
Proof. exact (MK_COMB (@lem2725719 x) (@lem2725720 x)). Qed.
Lemma lem2725722 : term79 = term65.
Proof. exact (fun_ext (fun x : int => @lem2725721 x)). Qed.
Lemma lem2725723 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2725724 : term71 = term66.
Proof. exact (MK_COMB (@lem2725723) (@lem2725722)). Qed.
Lemma lem2725725 : (term72 = term71) = (term90 = term66).
Proof. exact (MK_COMB (@lem2725716) (@lem2725724)). Qed.
Lemma lem2725726 : term90 = term66.
Proof. exact (EQ_MP (@lem2725725) (@lem2725703)). Qed.
Lemma lem2725727 : term66 = term66.
Proof. exact (TRANS (@lem2725603) (@lem2725726)). Qed.
Lemma lem2725728 : term40 = term66.
Proof. exact (TRANS (@lem2725576) (@lem2725727)). Qed.
Lemma lem2725729 (h1 : term40) : term66.
Proof. exact (EQ_MP (@lem2725728) (@lem2725544 h1)). Qed.
Lemma lem2725744 (n : int) : (((term13 n) = term18) = (term19 n)) = (term93 n).
Proof. exact (@lem17784 ((term13 n) = term18) (term19 n)). Qed.
Lemma lem2725745 : term20 = term94.
Proof. exact (fun_ext (fun n : int => @lem2725744 n)). Qed.
Lemma lem2725746 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725747 : term21 = term95.
Proof. exact (MK_COMB (@lem2725746) (@lem2725745)). Qed.
Lemma lem2725753 (n : int) : (term43 n) = (term19 n).
Proof. exact (@lem16933 (term19 n)). Qed.
Lemma lem2725756 (n : int) : (term96 n) = (term96 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem2725758 (n : int) : (term97 n) = (term97 n).
Proof. exact (eq_refl (term97 n)). Qed.
Lemma lem2725759 (n : int) : (term98 n) = (term99 n).
Proof. exact (MK_COMB (@lem2725758 n) (@lem2725753 n)). Qed.
Lemma lem2725760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725761 (n : int) : (term100 n) = (term101 n).
Proof. exact (MK_COMB (@lem2725760) (@lem2725759 n)). Qed.
Lemma lem2725762 (n : int) : (term102 n) = (term103 n).
Proof. exact (MK_COMB (@lem2725761 n) (@lem2725756 n)). Qed.
Lemma lem2725763 (n : int) : (((term13 n) = term14) = (term15 n)) = (term102 n).
Proof. exact (@lem17784 ((term13 n) = term14) (term15 n)). Qed.
Lemma lem2725764 (n : int) : (((term13 n) = term14) = (term15 n)) = (term103 n).
Proof. exact (TRANS (@lem2725763 n) (@lem2725762 n)). Qed.
Lemma lem2725765 : term16 = term104.
Proof. exact (fun_ext (fun n : int => @lem2725764 n)). Qed.
Lemma lem2725766 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725767 : term17 = term105.
Proof. exact (MK_COMB (@lem2725766) (@lem2725765)). Qed.
Lemma lem2725768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725769 : term22 = term106.
Proof. exact (MK_COMB (@lem2725768) (@lem2725747)). Qed.
Lemma lem2725770 : term10 = term107.
Proof. exact (MK_COMB (@lem2725769) (@lem2725767)). Qed.
Lemma lem2725772 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2725773 (P : int -> Prop) (Q : int -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem2725772 int P Q). Qed.
Lemma lem2725774 : term112 = term113.
Proof. exact (@lem2725773 term114 term115). Qed.
Lemma lem2725775 (n : int) : (term116 n) = (term117 n).
Proof. exact (eq_refl (term116 n)). Qed.
Lemma lem2725776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725777 (n : int) : (term118 n) = (term119 n).
Proof. exact (MK_COMB (@lem2725776) (@lem2725775 n)). Qed.
Lemma lem2725778 (n : int) : (term120 n) = (term121 n).
Proof. exact (eq_refl (term120 n)). Qed.
Lemma lem2725779 (n : int) : (term122 n) = (term93 n).
Proof. exact (MK_COMB (@lem2725777 n) (@lem2725778 n)). Qed.
Lemma lem2725780 : term123 = term94.
Proof. exact (fun_ext (fun n : int => @lem2725779 n)). Qed.
Lemma lem2725781 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725782 : term112 = term95.
Proof. exact (MK_COMB (@lem2725781) (@lem2725780)). Qed.
Lemma lem2725783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2725784 : term124 = term125.
Proof. exact (MK_COMB (@lem2725783) (@lem2725782)). Qed.
Lemma lem2725785 (n : int) : (term116 n) = (term117 n).
Proof. exact (eq_refl (term116 n)). Qed.
Lemma lem2725786 : term126 = term114.
Proof. exact (fun_ext (fun n : int => @lem2725785 n)). Qed.
Lemma lem2725787 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725788 : term127 = term128.
Proof. exact (MK_COMB (@lem2725787) (@lem2725786)). Qed.
Lemma lem2725789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725790 : term129 = term130.
Proof. exact (MK_COMB (@lem2725789) (@lem2725788)). Qed.
Lemma lem2725791 (n : int) : (term120 n) = (term121 n).
Proof. exact (eq_refl (term120 n)). Qed.
Lemma lem2725792 : term131 = term115.
Proof. exact (fun_ext (fun n : int => @lem2725791 n)). Qed.
Lemma lem2725793 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725794 : term132 = term133.
Proof. exact (MK_COMB (@lem2725793) (@lem2725792)). Qed.
Lemma lem2725795 : term113 = term134.
Proof. exact (MK_COMB (@lem2725790) (@lem2725794)). Qed.
Lemma lem2725796 : (term112 = term113) = (term95 = term134).
Proof. exact (MK_COMB (@lem2725784) (@lem2725795)). Qed.
Lemma lem2725797 : term95 = term134.
Proof. exact (EQ_MP (@lem2725796) (@lem2725774)). Qed.
Lemma lem2725894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725895 : term106 = term135.
Proof. exact (MK_COMB (@lem2725894) (@lem2725797)). Qed.
Lemma lem2725897 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2725898 (P : int -> Prop) (Q : int -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem2725897 int P Q). Qed.
Lemma lem2725899 : term136 = term137.
Proof. exact (@lem2725898 term138 term139). Qed.
Lemma lem2725900 (n : int) : (term140 n) = (term99 n).
Proof. exact (eq_refl (term140 n)). Qed.
Lemma lem2725901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725902 (n : int) : (term141 n) = (term101 n).
Proof. exact (MK_COMB (@lem2725901) (@lem2725900 n)). Qed.
Lemma lem2725903 (n : int) : (term142 n) = (term96 n).
Proof. exact (eq_refl (term142 n)). Qed.
Lemma lem2725904 (n : int) : (term143 n) = (term103 n).
Proof. exact (MK_COMB (@lem2725902 n) (@lem2725903 n)). Qed.
Lemma lem2725905 : term144 = term104.
Proof. exact (fun_ext (fun n : int => @lem2725904 n)). Qed.
Lemma lem2725906 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725907 : term136 = term105.
Proof. exact (MK_COMB (@lem2725906) (@lem2725905)). Qed.
Lemma lem2725908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2725909 : term145 = term146.
Proof. exact (MK_COMB (@lem2725908) (@lem2725907)). Qed.
Lemma lem2725910 (n : int) : (term140 n) = (term99 n).
Proof. exact (eq_refl (term140 n)). Qed.
Lemma lem2725911 : term147 = term138.
Proof. exact (fun_ext (fun n : int => @lem2725910 n)). Qed.
Lemma lem2725912 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725913 : term148 = term149.
Proof. exact (MK_COMB (@lem2725912) (@lem2725911)). Qed.
Lemma lem2725914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725915 : term150 = term151.
Proof. exact (MK_COMB (@lem2725914) (@lem2725913)). Qed.
Lemma lem2725916 (n : int) : (term142 n) = (term96 n).
Proof. exact (eq_refl (term142 n)). Qed.
Lemma lem2725917 : term152 = term139.
Proof. exact (fun_ext (fun n : int => @lem2725916 n)). Qed.
Lemma lem2725918 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725919 : term153 = term154.
Proof. exact (MK_COMB (@lem2725918) (@lem2725917)). Qed.
Lemma lem2725920 : term137 = term155.
Proof. exact (MK_COMB (@lem2725915) (@lem2725919)). Qed.
Lemma lem2725921 : (term136 = term137) = (term105 = term155).
Proof. exact (MK_COMB (@lem2725909) (@lem2725920)). Qed.
Lemma lem2725922 : term105 = term155.
Proof. exact (EQ_MP (@lem2725921) (@lem2725899)). Qed.
Lemma lem2726021 : term107 = term156.
Proof. exact (MK_COMB (@lem2725895) (@lem2725922)). Qed.
Lemma lem2726022 : term10 = term156.
Proof. exact (TRANS (@lem2725770) (@lem2726021)). Qed.
Lemma lem2726023 (h1 : term10) : term156.
Proof. exact (EQ_MP (@lem2726022) (@lem2725545 h1)). Qed.
Lemma lem2726067 (n : int) : (term96 n) = (term96 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem2726068 : term139 = term139.
Proof. exact (fun_ext (fun n : int => @lem2726067 n)). Qed.
Lemma lem2726069 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2726070 : term154 = term154.
Proof. exact (MK_COMB (@lem2726069) (@lem2726068)). Qed.
Lemma lem2726109 (n : int) : (term99 n) = (term99 n).
Proof. exact (eq_refl (term99 n)). Qed.
Lemma lem2726110 : term138 = term138.
Proof. exact (fun_ext (fun n : int => @lem2726109 n)). Qed.
Lemma lem2726111 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2726112 : term149 = term149.
Proof. exact (MK_COMB (@lem2726111) (@lem2726110)). Qed.
Lemma lem2726113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2726114 : term151 = term151.
Proof. exact (MK_COMB (@lem2726113) (@lem2726112)). Qed.
Lemma lem2726115 : term155 = term155.
Proof. exact (MK_COMB (@lem2726114) (@lem2726070)). Qed.
Lemma lem2726154 (n : int) : (term121 n) = (term121 n).
Proof. exact (eq_refl (term121 n)). Qed.
Lemma lem2726155 : term115 = term115.
Proof. exact (fun_ext (fun n : int => @lem2726154 n)). Qed.
Lemma lem2726156 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2726157 : term133 = term133.
Proof. exact (MK_COMB (@lem2726156) (@lem2726155)). Qed.
Lemma lem2726196 (n : int) : (term117 n) = (term117 n).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem2726197 : term114 = term114.
Proof. exact (fun_ext (fun n : int => @lem2726196 n)). Qed.
Lemma lem2726198 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2726199 : term128 = term128.
Proof. exact (MK_COMB (@lem2726198) (@lem2726197)). Qed.
Lemma lem2726200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2726201 : term130 = term130.
Proof. exact (MK_COMB (@lem2726200) (@lem2726199)). Qed.
Lemma lem2726202 : term134 = term134.
Proof. exact (MK_COMB (@lem2726201) (@lem2726157)). Qed.
Lemma lem2726203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2726204 : term135 = term135.
Proof. exact (MK_COMB (@lem2726203) (@lem2726202)). Qed.
Lemma lem2726205 : term156 = term156.
Proof. exact (MK_COMB (@lem2726204) (@lem2726115)). Qed.
Lemma lem2726206 (h1 : term10) : term156.
Proof. exact (EQ_MP (@lem2726205) (@lem2726023 h1)). Qed.
Lemma lem2726292 (x : int) (h1 : term55 x) : term55 x.
Proof. exact (h1). Qed.
Lemma lem2726293 (h1 : term10) : term155.
Proof. exact (proj2 (@lem2726206 h1)). Qed.
Lemma lem2726294 (h1 : term10) : term134.
Proof. exact (proj1 (@lem2726206 h1)). Qed.
Lemma lem2726296 (h1 : term10) : term149.
Proof. exact (proj1 (@lem2726293 h1)). Qed.
Lemma lem2726298 (h1 : term10) : term128.
Proof. exact (proj1 (@lem2726294 h1)). Qed.
Lemma lem2726299 (x : int) (h1 : term48 x) : term48 x.
Proof. exact (h1). Qed.
Lemma lem2726300 (x : int) (h1 : term51 x) : term51 x.
Proof. exact (h1). Qed.
Lemma lem2726338 (n : int) : (term117 n) = (term117 n).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem2726339 : term114 = term114.
Proof. exact (fun_ext (fun n : int => @lem2726338 n)). Qed.
Lemma lem2726340 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2726342 : term128 = term128.
Proof. exact (MK_COMB (@lem2726340) (@lem2726339)). Qed.
Lemma lem2726343 (h1 : term10) : term128.
Proof. exact (EQ_MP (@lem2726342) (@lem2726298 h1)). Qed.
Lemma lem2726372 (n : int) : (term99 n) = (term99 n).
Proof. exact (eq_refl (term99 n)). Qed.
Lemma lem2726373 : term138 = term138.
Proof. exact (fun_ext (fun n : int => @lem2726372 n)). Qed.
Lemma lem2726374 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2726376 : term149 = term149.
Proof. exact (MK_COMB (@lem2726374) (@lem2726373)). Qed.
Lemma lem2726377 (h1 : term10) : term149.
Proof. exact (EQ_MP (@lem2726376) (@lem2726296 h1)). Qed.
Lemma lem2726431 (_30316 : int) (h1 : term10) : term116 _30316.
Proof. exact (@lem2726343 h1 _30316). Qed.
Lemma lem2726432 (_30316 : int) : (term116 _30316) = (term117 _30316).
Proof. exact (eq_refl (term116 _30316)). Qed.
Lemma lem2726437 (_30318 : int) (h1 : term10) : term140 _30318.
Proof. exact (@lem2726377 h1 _30318). Qed.
Lemma lem2726438 (_30318 : int) : (term140 _30318) = (term99 _30318).
Proof. exact (eq_refl (term140 _30318)). Qed.
Lemma lem2726466 (_30316 : int) (h1 : term10) : term117 _30316.
Proof. exact (EQ_MP (@lem2726432 _30316) (@lem2726431 _30316 h1)). Qed.
Lemma lem2726476 (x : int) (h1 : term48 x) : term44 x.
Proof. exact (proj2 (@lem2726299 x h1)). Qed.
Lemma lem2726482 (_30318 : int) (h1 : term10) : term99 _30318.
Proof. exact (EQ_MP (@lem2726438 _30318) (@lem2726437 _30318 h1)). Qed.
Lemma lem2726504 (x : int) (h1 : term51 x) : term157 x.
Proof. exact (proj2 (@lem2726300 x h1)). Qed.
Lemma lem2726576 (x : int) (h1 : term48 x) : term19 x.
Proof. exact (proj1 (@lem2726299 x h1)). Qed.
Lemma lem2726577 (x : int) (h1 : term48 x) : term158 x.
Proof. exact (fun h0 : term15 x => @lem2726576 x h1). Qed.
Lemma lem2726579 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2726580 (x : int) : (term158 x) = (term19 x).
Proof. exact (@lem2726579 (term19 x)). Qed.
Lemma lem2726581 (x : int) (h1 : term48 x) : term19 x.
Proof. exact (EQ_MP (@lem2726580 x) (@lem2726577 x h1)). Qed.
Lemma lem2726583 (b : Prop) (a : Prop) : (a \/ b) = (term160 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2726584 (_30316 : int) : (term117 _30316) = (term161 _30316).
Proof. exact (@lem2726583 (term15 _30316) ((term13 _30316) = term18)). Qed.
Lemma lem2726586 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2726587 (_30316 : int) : (term43 _30316) = (term19 _30316).
Proof. exact (@lem2726586 (term19 _30316)). Qed.
Lemma lem2726588 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2726589 (_30316 : int) : (term163 _30316) = (term164 _30316).
Proof. exact (MK_COMB (@lem2726588) (@lem2726587 _30316)). Qed.
Lemma lem2726590 (_30316 : int) : ((term13 _30316) = term18) = ((term13 _30316) = term18).
Proof. exact (eq_refl ((term13 _30316) = term18)). Qed.
Lemma lem2726591 (_30316 : int) : (term161 _30316) = (term165 _30316).
Proof. exact (MK_COMB (@lem2726589 _30316) (@lem2726590 _30316)). Qed.
Lemma lem2726592 (_30316 : int) : (term117 _30316) = (term165 _30316).
Proof. exact (TRANS (@lem2726584 _30316) (@lem2726591 _30316)). Qed.
Lemma lem2726595 (_30316 : int) (h1 : term10) : term165 _30316.
Proof. exact (EQ_MP (@lem2726592 _30316) (@lem2726466 _30316 h1)). Qed.
Lemma lem2726596 (x : int) (h1 : term10) : term165 x.
Proof. exact (@lem2726595 x h1). Qed.
Lemma lem2726599 (x : int) (h1 : term10) (h2 : term48 x) : (term13 x) = term18.
Proof. exact (@lem2726596 x h1 (@lem2726581 x h2)). Qed.
Lemma lem2726600 (x : int) (h1 : term10) (h2 : term48 x) : term166 x.
Proof. exact (fun h0 : term44 x => @lem2726599 x h1 h2). Qed.
Lemma lem2726602 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2726603 (x : int) : (term166 x) = ((term13 x) = term18).
Proof. exact (@lem2726602 ((term13 x) = term18)). Qed.
Lemma lem2726604 (x : int) (h1 : term10) (h2 : term48 x) : (term13 x) = term18.
Proof. exact (EQ_MP (@lem2726603 x) (@lem2726600 x h1 h2)). Qed.
Lemma lem2726607 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2726609 (x : int) : (term44 x) = (term167 x).
Proof. exact (@lem2726607 ((term13 x) = term18)). Qed.
Lemma lem2726612 (x : int) (h1 : term48 x) : term167 x.
Proof. exact (EQ_MP (@lem2726609 x) (@lem2726476 x h1)). Qed.
Lemma lem2726615 (x : int) (h1 : term10) (h2 : term48 x) : False.
Proof. exact (@lem2726612 x h2 (@lem2726604 x h1 h2)). Qed.
Lemma lem2726616 (x : int) (h1 : term10) (h2 : term48 x) : term168.
Proof. exact (fun h0 : ~ False => @lem2726615 x h1 h2). Qed.
Lemma lem2726618 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2726619 : term168 = False.
Proof. exact (@lem2726618 False). Qed.
Lemma lem2726620 (x : int) (h1 : term10) (h2 : term48 x) : False.
Proof. exact (EQ_MP (@lem2726619) (@lem2726616 x h1 h2)). Qed.
Lemma lem2726692 (x : int) (h1 : term51 x) : term15 x.
Proof. exact (proj1 (@lem2726300 x h1)). Qed.
Lemma lem2726693 (x : int) (h1 : term51 x) : term169 x.
Proof. exact (fun h0 : term19 x => @lem2726692 x h1). Qed.
Lemma lem2726695 (p : Prop) : (term170 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2726696 (x : int) : (term169 x) = (term15 x).
Proof. exact (@lem2726695 (term19 x)). Qed.
Lemma lem2726697 (x : int) (h1 : term51 x) : term15 x.
Proof. exact (EQ_MP (@lem2726696 x) (@lem2726693 x h1)). Qed.
Lemma lem2726699 (b : Prop) (a : Prop) : (a \/ b) = (term160 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2726702 (_30318 : int) : (term99 _30318) = (term171 _30318).
Proof. exact (@lem2726699 (term19 _30318) ((term13 _30318) = term14)). Qed.
Lemma lem2726705 (_30318 : int) (h1 : term10) : term171 _30318.
Proof. exact (EQ_MP (@lem2726702 _30318) (@lem2726482 _30318 h1)). Qed.
Lemma lem2726706 (x : int) (h1 : term10) : term171 x.
Proof. exact (@lem2726705 x h1). Qed.
Lemma lem2726709 (x : int) (h1 : term10) (h2 : term51 x) : (term13 x) = term14.
Proof. exact (@lem2726706 x h1 (@lem2726697 x h2)). Qed.
Lemma lem2726710 (x : int) (h1 : term10) (h2 : term51 x) : term172 x.
Proof. exact (fun h0 : term157 x => @lem2726709 x h1 h2). Qed.
Lemma lem2726712 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2726713 (x : int) : (term172 x) = ((term13 x) = term14).
Proof. exact (@lem2726712 ((term13 x) = term14)). Qed.
Lemma lem2726714 (x : int) (h1 : term10) (h2 : term51 x) : (term13 x) = term14.
Proof. exact (EQ_MP (@lem2726713 x) (@lem2726710 x h1 h2)). Qed.
Lemma lem2726717 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2726719 (x : int) : (term157 x) = (term173 x).
Proof. exact (@lem2726717 ((term13 x) = term14)). Qed.
Lemma lem2726722 (x : int) (h1 : term51 x) : term173 x.
Proof. exact (EQ_MP (@lem2726719 x) (@lem2726504 x h1)). Qed.
Lemma lem2726725 (x : int) (h1 : term10) (h2 : term51 x) : False.
Proof. exact (@lem2726722 x h2 (@lem2726714 x h1 h2)). Qed.
Lemma lem2726726 (x : int) (h1 : term10) (h2 : term51 x) : term168.
Proof. exact (fun h0 : ~ False => @lem2726725 x h1 h2). Qed.
Lemma lem2726728 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2726729 : term168 = False.
Proof. exact (@lem2726728 False). Qed.
Lemma lem2726730 (x : int) (h1 : term10) (h2 : term51 x) : False.
Proof. exact (EQ_MP (@lem2726729) (@lem2726726 x h1 h2)). Qed.
Lemma lem2726731 (x : int) (h1 : term10) (h2 : term55 x) : False.
Proof. exact (or_elim (@lem2726292 x h2) (fun h0 : term48 x => @lem2726620 x h1 h0) (fun h0 : term51 x => @lem2726730 x h1 h0)). Qed.
Lemma lem2726732 (x : int) (h1 : term10) (h2 : term55 x) : (term55 x) = False.
Proof. exact (prop_ext (fun h3 : term55 x => @lem2726731 x h1 h2) (fun h3 : False => @lem2726292 x h2)). Qed.
Lemma lem2726733 (x : int) (h1 : term10) (h2 : term55 x) : False.
Proof. exact (EQ_MP (@lem2726732 x h1 h2) (@lem2726292 x h2)). Qed.
Lemma lem2726734 (h1 : term40) (h2 : term10) : False.
Proof. exact (ex_elim (@lem2725729 h1) (fun x : int => fun h0 : term65 x => @lem2726733 x h2 h0)). Qed.
Lemma lem2726735 (h1 : term40) : term8.
Proof. exact (fun h0 : term10 => @lem2726734 h1 h0). Qed.
Lemma lem2726736 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem2726737 (h1 : term40) : term9.
Proof. exact (EQ_MP (@lem2726736) (@lem2726735 h1)). Qed.
Lemma lem2726738 : term42.
Proof. exact (fun h0 : term40 => @lem2726737 h0). Qed.
Lemma lem2726739 : term4.
Proof. exact (EQ_MP (@lem2725543) (@lem2726738)). Qed.
Lemma lem2726741 : term4.
Proof. exact (@lem2725378 (@lem2726739)). Qed.
Lemma lem2726742 (h1 : term3) : term8.
Proof. exact (@lem2726741 (@lem2725363 h1)). Qed.
Lemma lem2726743 (h1 : term3) : False.
Proof. exact (@lem2726742 h1 (@lem2725348)). Qed.
Lemma lem2726744 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem2726743 h1) (fun h2 : False => @lem2725363 h1)). Qed.
Lemma lem2726745 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem2726744 h1) (@lem2725363 h1)). Qed.
Lemma lem2726746 : term2.
Proof. exact (fun h0 : term3 => @lem2726745 h0). Qed.
Lemma lem2726747 : term1.
Proof. exact (EQ_MP (@lem2725362) (@lem2726746)). Qed.
