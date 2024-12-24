Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_TRANS_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Lemma lem1988352 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1988353 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1988354 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1988353 t1) (@lem1988352 t1)). Qed.
Lemma lem1988355 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1988354 t1 t2). Qed.
Lemma lem1988356 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1988357 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1988356 t1 t2) (@lem1988355 t1 t2)). Qed.
Lemma lem1988358 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1988357 t1 t2 t3). Qed.
Lemma lem1988359 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1988360 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1988359 t1 t2 t3) (@lem1988358 t1 t2 t3)). Qed.
Lemma lem1988361 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1988360 t1 t2 t3)). Qed.
Lemma lem1988363 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1988364 : term8 = term9.
Proof. exact (@lem1988363 term8). Qed.
Lemma lem1988365 : term9 = term8.
Proof. exact (SYM (@lem1988364)). Qed.
Lemma lem1988366 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1988369 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1988370 : term12.
Proof. exact (fun h0 : term11 => @lem1988369 h0). Qed.
Lemma lem1988371 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1988372 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1988373 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1988371 h2 (@lem1988372 h1)). Qed.
Lemma lem1988374 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1988373 h1 h0). Qed.
Lemma lem1988375 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1988376 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1988374 h1 (@lem1988375 h2)). Qed.
Lemma lem1988377 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1988376 h0 h1). Qed.
Lemma lem1988378 : term14.
Proof. exact (fun h0 : term12 => @lem1988377 h0). Qed.
Lemma lem1988381 : term12.
Proof. exact (@lem1988378 (@lem1988370)). Qed.
Lemma lem1988405 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1988406 : term15 = term16.
Proof. exact (@lem1988405 term17). Qed.
Lemma lem1988423 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1988424 : term19 = term20.
Proof. exact (MK_COMB (@lem1988423) (@lem1988406)). Qed.
Lemma lem1988427 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1988434 : term11 = term22.
Proof. exact (MK_COMB (@lem1988427) (@lem1988424)). Qed.
Lemma lem1988443 (y : real) (x : real) (z : real) : (term23 y x z) = (term23 y x z).
Proof. exact (eq_refl (term23 y x z)). Qed.
Lemma lem1988444 (y : real) (x : real) : (term24 y x) = (term24 y x).
Proof. exact (fun_ext (fun z : real => @lem1988443 y x z)). Qed.
Lemma lem1988445 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1988446 (y : real) (x : real) : (term25 y x) = (term25 y x).
Proof. exact (MK_COMB (@lem1988445) (@lem1988444 y x)). Qed.
Lemma lem1988447 (x : real) : (term26 x) = (term26 x).
Proof. exact (fun_ext (fun y : real => @lem1988446 y x)). Qed.
Lemma lem1988448 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1988449 (x : real) : (term27 x) = (term27 x).
Proof. exact (MK_COMB (@lem1988448) (@lem1988447 x)). Qed.
Lemma lem1988450 : term28 = term28.
Proof. exact (fun_ext (fun x : real => @lem1988449 x)). Qed.
Lemma lem1988451 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1988452 : term17 = term17.
Proof. exact (MK_COMB (@lem1988451) (@lem1988450)). Qed.
Lemma lem1988453 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1988454 : term16 = term16.
Proof. exact (MK_COMB (@lem1988453) (@lem1988452)). Qed.
Lemma lem1988455 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem1988456 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1988455 x)). Qed.
Lemma lem1988457 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1988458 : term30 = term30.
Proof. exact (MK_COMB (@lem1988457) (@lem1988456)). Qed.
Lemma lem1988459 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1988460 : term18 = term18.
Proof. exact (MK_COMB (@lem1988459) (@lem1988458)). Qed.
Lemma lem1988461 : term20 = term20.
Proof. exact (MK_COMB (@lem1988460) (@lem1988454)). Qed.
Lemma lem1988466 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem1988467 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem1988466 y x z)). Qed.
Lemma lem1988468 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1988469 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem1988468) (@lem1988467 y x)). Qed.
Lemma lem1988472 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1988473 (y : real) (x : real) : ((real_le x y) = (term33 y x)) = ((real_le x y) = (term33 y x)).
Proof. exact (MK_COMB (@lem1988472 x y) (@lem1988469 y x)). Qed.
Lemma lem1988474 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1988473 y x)). Qed.
Lemma lem1988475 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1988476 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1988475) (@lem1988474 x)). Qed.
Lemma lem1988477 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1988476 x)). Qed.
Lemma lem1988478 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1988479 : term8 = term8.
Proof. exact (MK_COMB (@lem1988478) (@lem1988477)). Qed.
Lemma lem1988480 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1988481 : term10 = term10.
Proof. exact (MK_COMB (@lem1988480) (@lem1988479)). Qed.
Lemma lem1988482 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1988483 : term21 = term21.
Proof. exact (MK_COMB (@lem1988482) (@lem1988481)). Qed.
Lemma lem1988484 : term22 = term22.
Proof. exact (MK_COMB (@lem1988483) (@lem1988461)). Qed.
Lemma lem1988539 : term11 = term22.
Proof. exact (TRANS (@lem1988434) (@lem1988484)). Qed.
Lemma lem1988540 : term22 = term11.
Proof. exact (SYM (@lem1988539)). Qed.
Lemma lem1988541 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1988542 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1988543 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1988554 (y : real) (x : real) (z : real) : (term38 y x z) = (term39 y x z).
Proof. exact (@lem17362 (real_le y z) (real_le x z)). Qed.
Lemma lem1988559 (y : real) (x : real) (z : real) : (term31 y x z) = (term40 y x z).
Proof. exact (@lem17265 (real_le y z) (real_le x z)). Qed.
Lemma lem1988560 (P : real -> Prop) : (term41 P) = (term42 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1988561 (y : real) (x : real) : (term43 y x) = (term44 y x).
Proof. exact (@lem1988560 (term32 y x)). Qed.
Lemma lem1988562 (y : real) (x : real) (z : real) : (term45 y x z) = (term31 y x z).
Proof. exact (eq_refl (term45 y x z)). Qed.
Lemma lem1988563 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1988564 (y : real) (x : real) (z : real) : (term46 y x z) = (term38 y x z).
Proof. exact (MK_COMB (@lem1988563) (@lem1988562 y x z)). Qed.
Lemma lem1988565 (y : real) (x : real) (z : real) : (term46 y x z) = (term39 y x z).
Proof. exact (TRANS (@lem1988564 y x z) (@lem1988554 y x z)). Qed.
Lemma lem1988566 (y : real) (x : real) : (term47 y x) = (term48 y x).
Proof. exact (fun_ext (fun z : real => @lem1988565 y x z)). Qed.
Lemma lem1988567 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988568 (y : real) (x : real) : (term44 y x) = (term49 y x).
Proof. exact (MK_COMB (@lem1988567) (@lem1988566 y x)). Qed.
Lemma lem1988569 (y : real) (x : real) : (term43 y x) = (term49 y x).
Proof. exact (TRANS (@lem1988561 y x) (@lem1988568 y x)). Qed.
Lemma lem1988570 (y : real) (x : real) : (term32 y x) = (term50 y x).
Proof. exact (fun_ext (fun z : real => @lem1988559 y x z)). Qed.
Lemma lem1988571 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1988572 (y : real) (x : real) : (term33 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1988571) (@lem1988570 y x)). Qed.
Lemma lem1988574 (x : real) (y : real) : (term52 x y) = (term52 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem1988575 (y : real) (x : real) : (term53 y x) = (term54 y x).
Proof. exact (MK_COMB (@lem1988574 x y) (@lem1988572 y x)). Qed.
Lemma lem1988577 (x : real) (y : real) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1988578 (y : real) (x : real) : (term56 y x) = (term57 y x).
Proof. exact (MK_COMB (@lem1988577 x y) (@lem1988569 y x)). Qed.
Lemma lem1988579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1988580 (y : real) (x : real) : (term58 y x) = (term59 y x).
Proof. exact (MK_COMB (@lem1988579) (@lem1988578 y x)). Qed.
Lemma lem1988581 (y : real) (x : real) : (term60 y x) = (term61 y x).
Proof. exact (MK_COMB (@lem1988580 y x) (@lem1988575 y x)). Qed.
Lemma lem1988582 (y : real) (x : real) : (term62 y x) = (term60 y x).
Proof. exact (@lem17646 (real_le x y) (term33 y x)). Qed.
Lemma lem1988583 (y : real) (x : real) : (term62 y x) = (term61 y x).
Proof. exact (TRANS (@lem1988582 y x) (@lem1988581 y x)). Qed.
Lemma lem1988584 (P : real -> Prop) : (term41 P) = (term42 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1988585 (x : real) : (term63 x) = (term64 x).
Proof. exact (@lem1988584 (term35 x)). Qed.
Lemma lem1988586 (y : real) (x : real) : (term65 x y) = ((real_le x y) = (term33 y x)).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1988587 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1988588 (y : real) (x : real) : (term66 x y) = (term62 y x).
Proof. exact (MK_COMB (@lem1988587) (@lem1988586 y x)). Qed.
Lemma lem1988589 (y : real) (x : real) : (term66 x y) = (term61 y x).
Proof. exact (TRANS (@lem1988588 y x) (@lem1988583 y x)). Qed.
Lemma lem1988590 (x : real) : (term67 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1988589 y x)). Qed.
Lemma lem1988591 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988592 (x : real) : (term64 x) = (term69 x).
Proof. exact (MK_COMB (@lem1988591) (@lem1988590 x)). Qed.
Lemma lem1988593 (x : real) : (term63 x) = (term69 x).
Proof. exact (TRANS (@lem1988585 x) (@lem1988592 x)). Qed.
Lemma lem1988594 (P : real -> Prop) : (term41 P) = (term42 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1988595 : term10 = term70.
Proof. exact (@lem1988594 term37). Qed.
Lemma lem1988596 (x : real) : (term71 x) = (term36 x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem1988597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1988598 (x : real) : (term72 x) = (term63 x).
Proof. exact (MK_COMB (@lem1988597) (@lem1988596 x)). Qed.
Lemma lem1988599 (x : real) : (term72 x) = (term69 x).
Proof. exact (TRANS (@lem1988598 x) (@lem1988593 x)). Qed.
Lemma lem1988600 : term73 = term74.
Proof. exact (fun_ext (fun x : real => @lem1988599 x)). Qed.
Lemma lem1988601 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988602 : term70 = term75.
Proof. exact (MK_COMB (@lem1988601) (@lem1988600)). Qed.
Lemma lem1988603 : term10 = term75.
Proof. exact (TRANS (@lem1988595) (@lem1988602)). Qed.
Lemma lem1988609 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1988610 (P : real -> Prop) (Q : real -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1988609 real P Q). Qed.
Lemma lem1988611 (x : real) : (term80 x) = (term81 x).
Proof. exact (@lem1988610 (term82 x) (term83 x)). Qed.
Lemma lem1988612 (y : real) (x : real) : (term84 x y) = (term57 y x).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1988613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1988614 (y : real) (x : real) : (term85 x y) = (term59 y x).
Proof. exact (MK_COMB (@lem1988613) (@lem1988612 y x)). Qed.
Lemma lem1988615 (y : real) (x : real) : (term86 x y) = (term54 y x).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1988616 (y : real) (x : real) : (term87 x y) = (term61 y x).
Proof. exact (MK_COMB (@lem1988614 y x) (@lem1988615 y x)). Qed.
Lemma lem1988617 (x : real) : (term88 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1988616 y x)). Qed.
Lemma lem1988618 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988619 (x : real) : (term80 x) = (term69 x).
Proof. exact (MK_COMB (@lem1988618) (@lem1988617 x)). Qed.
Lemma lem1988620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1988621 (x : real) : (term89 x) = (term90 x).
Proof. exact (MK_COMB (@lem1988620) (@lem1988619 x)). Qed.
Lemma lem1988622 (y : real) (x : real) : (term84 x y) = (term57 y x).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1988623 (x : real) : (term91 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1988622 y x)). Qed.
Lemma lem1988624 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988625 (x : real) : (term92 x) = (term93 x).
Proof. exact (MK_COMB (@lem1988624) (@lem1988623 x)). Qed.
Lemma lem1988626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1988627 (x : real) : (term94 x) = (term95 x).
Proof. exact (MK_COMB (@lem1988626) (@lem1988625 x)). Qed.
Lemma lem1988628 (y : real) (x : real) : (term86 x y) = (term54 y x).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1988629 (x : real) : (term96 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1988628 y x)). Qed.
Lemma lem1988630 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988631 (x : real) : (term97 x) = (term98 x).
Proof. exact (MK_COMB (@lem1988630) (@lem1988629 x)). Qed.
Lemma lem1988632 (x : real) : (term81 x) = (term99 x).
Proof. exact (MK_COMB (@lem1988627 x) (@lem1988631 x)). Qed.
Lemma lem1988633 (x : real) : ((term80 x) = (term81 x)) = ((term69 x) = (term99 x)).
Proof. exact (MK_COMB (@lem1988621 x) (@lem1988632 x)). Qed.
Lemma lem1988634 (x : real) : (term69 x) = (term99 x).
Proof. exact (EQ_MP (@lem1988633 x) (@lem1988611 x)). Qed.
Lemma lem1988827 : term74 = term100.
Proof. exact (fun_ext (fun x : real => @lem1988634 x)). Qed.
Lemma lem1988828 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988829 : term75 = term101.
Proof. exact (MK_COMB (@lem1988828) (@lem1988827)). Qed.
Lemma lem1988831 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1988832 (P : real -> Prop) (Q : real -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1988831 real P Q). Qed.
Lemma lem1988833 : term102 = term103.
Proof. exact (@lem1988832 term104 term105). Qed.
Lemma lem1988834 (x : real) : (term106 x) = (term93 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1988835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1988836 (x : real) : (term107 x) = (term95 x).
Proof. exact (MK_COMB (@lem1988835) (@lem1988834 x)). Qed.
Lemma lem1988837 (x : real) : (term108 x) = (term98 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1988838 (x : real) : (term109 x) = (term99 x).
Proof. exact (MK_COMB (@lem1988836 x) (@lem1988837 x)). Qed.
Lemma lem1988839 : term110 = term100.
Proof. exact (fun_ext (fun x : real => @lem1988838 x)). Qed.
Lemma lem1988840 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988841 : term102 = term101.
Proof. exact (MK_COMB (@lem1988840) (@lem1988839)). Qed.
Lemma lem1988842 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1988843 : term111 = term112.
Proof. exact (MK_COMB (@lem1988842) (@lem1988841)). Qed.
Lemma lem1988844 (x : real) : (term106 x) = (term93 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1988845 : term113 = term104.
Proof. exact (fun_ext (fun x : real => @lem1988844 x)). Qed.
Lemma lem1988846 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988847 : term114 = term115.
Proof. exact (MK_COMB (@lem1988846) (@lem1988845)). Qed.
Lemma lem1988848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1988849 : term116 = term117.
Proof. exact (MK_COMB (@lem1988848) (@lem1988847)). Qed.
Lemma lem1988850 (x : real) : (term108 x) = (term98 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1988851 : term118 = term105.
Proof. exact (fun_ext (fun x : real => @lem1988850 x)). Qed.
Lemma lem1988852 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1988853 : term119 = term120.
Proof. exact (MK_COMB (@lem1988852) (@lem1988851)). Qed.
Lemma lem1988854 : term103 = term121.
Proof. exact (MK_COMB (@lem1988849) (@lem1988853)). Qed.
Lemma lem1988855 : (term102 = term103) = (term101 = term121).
Proof. exact (MK_COMB (@lem1988843) (@lem1988854)). Qed.
Lemma lem1988856 : term101 = term121.
Proof. exact (EQ_MP (@lem1988855) (@lem1988833)). Qed.
Lemma lem1989057 : term75 = term121.
Proof. exact (TRANS (@lem1988829) (@lem1988856)). Qed.
Lemma lem1989059 {A : Type'} (P : Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1989060 (P : Prop) (Q : real -> Prop) : (term124 P Q) = (term125 P Q).
Proof. exact (@lem1989059 real P Q). Qed.
Lemma lem1989061 (y : real) (x : real) : (term126 y x) = (term127 y x).
Proof. exact (@lem1989060 (real_le x y) (term48 y x)). Qed.
Lemma lem1989062 (y : real) (x : real) (z : real) : (term128 y x z) = (term39 y x z).
Proof. exact (eq_refl (term128 y x z)). Qed.
Lemma lem1989063 (y : real) (x : real) : (term129 y x) = (term48 y x).
Proof. exact (fun_ext (fun z : real => @lem1989062 y x z)). Qed.
Lemma lem1989064 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989065 (y : real) (x : real) : (term130 y x) = (term49 y x).
Proof. exact (MK_COMB (@lem1989064) (@lem1989063 y x)). Qed.
Lemma lem1989066 (x : real) (y : real) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1989067 (y : real) (x : real) : (term126 y x) = (term57 y x).
Proof. exact (MK_COMB (@lem1989066 x y) (@lem1989065 y x)). Qed.
Lemma lem1989068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1989069 (y : real) (x : real) : (term131 y x) = (term132 y x).
Proof. exact (MK_COMB (@lem1989068) (@lem1989067 y x)). Qed.
Lemma lem1989070 (y : real) (x : real) (z : real) : (term128 y x z) = (term39 y x z).
Proof. exact (eq_refl (term128 y x z)). Qed.
Lemma lem1989071 (x : real) (y : real) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1989072 (y : real) (x : real) (z : real) : (term133 y x z) = (term134 y x z).
Proof. exact (MK_COMB (@lem1989071 x y) (@lem1989070 y x z)). Qed.
Lemma lem1989073 (y : real) (x : real) : (term135 y x) = (term136 y x).
Proof. exact (fun_ext (fun z : real => @lem1989072 y x z)). Qed.
Lemma lem1989074 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989075 (y : real) (x : real) : (term127 y x) = (term137 y x).
Proof. exact (MK_COMB (@lem1989074) (@lem1989073 y x)). Qed.
Lemma lem1989076 (y : real) (x : real) : ((term126 y x) = (term127 y x)) = ((term57 y x) = (term137 y x)).
Proof. exact (MK_COMB (@lem1989069 y x) (@lem1989075 y x)). Qed.
Lemma lem1989077 (y : real) (x : real) : (term57 y x) = (term137 y x).
Proof. exact (EQ_MP (@lem1989076 y x) (@lem1989061 y x)). Qed.
Lemma lem1989078 (x : real) : (term82 x) = (term138 x).
Proof. exact (fun_ext (fun y : real => @lem1989077 y x)). Qed.
Lemma lem1989079 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989080 (x : real) : (term93 x) = (term139 x).
Proof. exact (MK_COMB (@lem1989079) (@lem1989078 x)). Qed.
Lemma lem1989081 : term104 = term140.
Proof. exact (fun_ext (fun x : real => @lem1989080 x)). Qed.
Lemma lem1989082 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989083 : term115 = term141.
Proof. exact (MK_COMB (@lem1989082) (@lem1989081)). Qed.
Lemma lem1989084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1989085 : term117 = term142.
Proof. exact (MK_COMB (@lem1989084) (@lem1989083)). Qed.
Lemma lem1989086 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem1989087 : term121 = term143.
Proof. exact (MK_COMB (@lem1989085) (@lem1989086)). Qed.
Lemma lem1989089 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1989090 (P : real -> Prop) (Q : real -> Prop) : (term79 P Q) = (term78 P Q).
Proof. exact (@lem1989089 real P Q). Qed.
Lemma lem1989091 : term144 = term145.
Proof. exact (@lem1989090 term140 term105). Qed.
Lemma lem1989092 (x : real) : (term146 x) = (term139 x).
Proof. exact (eq_refl (term146 x)). Qed.
Lemma lem1989093 : term147 = term140.
Proof. exact (fun_ext (fun x : real => @lem1989092 x)). Qed.
Lemma lem1989094 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989095 : term148 = term141.
Proof. exact (MK_COMB (@lem1989094) (@lem1989093)). Qed.
Lemma lem1989096 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1989097 : term149 = term142.
Proof. exact (MK_COMB (@lem1989096) (@lem1989095)). Qed.
Lemma lem1989098 (x : real) : (term108 x) = (term98 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1989099 : term118 = term105.
Proof. exact (fun_ext (fun x : real => @lem1989098 x)). Qed.
Lemma lem1989100 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989101 : term119 = term120.
Proof. exact (MK_COMB (@lem1989100) (@lem1989099)). Qed.
Lemma lem1989102 : term144 = term143.
Proof. exact (MK_COMB (@lem1989097) (@lem1989101)). Qed.
Lemma lem1989103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1989104 : term150 = term151.
Proof. exact (MK_COMB (@lem1989103) (@lem1989102)). Qed.
Lemma lem1989105 (x : real) : (term146 x) = (term139 x).
Proof. exact (eq_refl (term146 x)). Qed.
Lemma lem1989106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1989107 (x : real) : (term152 x) = (term153 x).
Proof. exact (MK_COMB (@lem1989106) (@lem1989105 x)). Qed.
Lemma lem1989108 (x : real) : (term108 x) = (term98 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1989109 (x : real) : (term154 x) = (term155 x).
Proof. exact (MK_COMB (@lem1989107 x) (@lem1989108 x)). Qed.
Lemma lem1989110 : term156 = term157.
Proof. exact (fun_ext (fun x : real => @lem1989109 x)). Qed.
Lemma lem1989111 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989112 : term145 = term158.
Proof. exact (MK_COMB (@lem1989111) (@lem1989110)). Qed.
Lemma lem1989113 : (term144 = term145) = (term143 = term158).
Proof. exact (MK_COMB (@lem1989104) (@lem1989112)). Qed.
Lemma lem1989114 : term143 = term158.
Proof. exact (EQ_MP (@lem1989113) (@lem1989091)). Qed.
Lemma lem1989116 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1989117 (P : real -> Prop) (Q : real -> Prop) : (term79 P Q) = (term78 P Q).
Proof. exact (@lem1989116 real P Q). Qed.
Lemma lem1989118 (x : real) : (term159 x) = (term160 x).
Proof. exact (@lem1989117 (term138 x) (term83 x)). Qed.
Lemma lem1989119 (y : real) (x : real) : (term161 x y) = (term137 y x).
Proof. exact (eq_refl (term161 x y)). Qed.
Lemma lem1989120 (x : real) : (term162 x) = (term138 x).
Proof. exact (fun_ext (fun y : real => @lem1989119 y x)). Qed.
Lemma lem1989121 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989122 (x : real) : (term163 x) = (term139 x).
Proof. exact (MK_COMB (@lem1989121) (@lem1989120 x)). Qed.
Lemma lem1989123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1989124 (x : real) : (term164 x) = (term153 x).
Proof. exact (MK_COMB (@lem1989123) (@lem1989122 x)). Qed.
Lemma lem1989125 (y : real) (x : real) : (term86 x y) = (term54 y x).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1989126 (x : real) : (term96 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1989125 y x)). Qed.
Lemma lem1989127 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989128 (x : real) : (term97 x) = (term98 x).
Proof. exact (MK_COMB (@lem1989127) (@lem1989126 x)). Qed.
Lemma lem1989129 (x : real) : (term159 x) = (term155 x).
Proof. exact (MK_COMB (@lem1989124 x) (@lem1989128 x)). Qed.
Lemma lem1989130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1989131 (x : real) : (term165 x) = (term166 x).
Proof. exact (MK_COMB (@lem1989130) (@lem1989129 x)). Qed.
Lemma lem1989132 (y : real) (x : real) : (term161 x y) = (term137 y x).
Proof. exact (eq_refl (term161 x y)). Qed.
Lemma lem1989133 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1989134 (y : real) (x : real) : (term167 x y) = (term168 y x).
Proof. exact (MK_COMB (@lem1989133) (@lem1989132 y x)). Qed.
Lemma lem1989135 (y : real) (x : real) : (term86 x y) = (term54 y x).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1989136 (y : real) (x : real) : (term169 x y) = (term170 y x).
Proof. exact (MK_COMB (@lem1989134 y x) (@lem1989135 y x)). Qed.
Lemma lem1989137 (x : real) : (term171 x) = (term172 x).
Proof. exact (fun_ext (fun y : real => @lem1989136 y x)). Qed.
Lemma lem1989138 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989139 (x : real) : (term160 x) = (term173 x).
Proof. exact (MK_COMB (@lem1989138) (@lem1989137 x)). Qed.
Lemma lem1989140 (x : real) : ((term159 x) = (term160 x)) = ((term155 x) = (term173 x)).
Proof. exact (MK_COMB (@lem1989131 x) (@lem1989139 x)). Qed.
Lemma lem1989141 (x : real) : (term155 x) = (term173 x).
Proof. exact (EQ_MP (@lem1989140 x) (@lem1989118 x)). Qed.
Lemma lem1989143 {A : Type'} (P : A -> Prop) (Q : Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1989144 (P : real -> Prop) (Q : Prop) : (term176 P Q) = (term177 P Q).
Proof. exact (@lem1989143 real P Q). Qed.
Lemma lem1989145 (y : real) (x : real) : (term178 y x) = (term179 y x).
Proof. exact (@lem1989144 (term136 y x) (term54 y x)). Qed.
Lemma lem1989146 (y : real) (x : real) (z : real) : (term180 y x z) = (term134 y x z).
Proof. exact (eq_refl (term180 y x z)). Qed.
Lemma lem1989147 (y : real) (x : real) : (term181 y x) = (term136 y x).
Proof. exact (fun_ext (fun z : real => @lem1989146 y x z)). Qed.
Lemma lem1989148 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989149 (y : real) (x : real) : (term182 y x) = (term137 y x).
Proof. exact (MK_COMB (@lem1989148) (@lem1989147 y x)). Qed.
Lemma lem1989150 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1989151 (y : real) (x : real) : (term183 y x) = (term168 y x).
Proof. exact (MK_COMB (@lem1989150) (@lem1989149 y x)). Qed.
Lemma lem1989152 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (eq_refl (term54 y x)). Qed.
Lemma lem1989153 (y : real) (x : real) : (term178 y x) = (term170 y x).
Proof. exact (MK_COMB (@lem1989151 y x) (@lem1989152 y x)). Qed.
Lemma lem1989154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1989155 (y : real) (x : real) : (term184 y x) = (term185 y x).
Proof. exact (MK_COMB (@lem1989154) (@lem1989153 y x)). Qed.
Lemma lem1989156 (y : real) (x : real) (z : real) : (term180 y x z) = (term134 y x z).
Proof. exact (eq_refl (term180 y x z)). Qed.
Lemma lem1989157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1989158 (y : real) (x : real) (z : real) : (term186 y x z) = (term187 y x z).
Proof. exact (MK_COMB (@lem1989157) (@lem1989156 y x z)). Qed.
Lemma lem1989159 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (eq_refl (term54 y x)). Qed.
Lemma lem1989160 (z : real) (y : real) (x : real) : (term188 z y x) = (term189 z y x).
Proof. exact (MK_COMB (@lem1989158 y x z) (@lem1989159 y x)). Qed.
Lemma lem1989161 (y : real) (x : real) : (term190 y x) = (term191 y x).
Proof. exact (fun_ext (fun z : real => @lem1989160 z y x)). Qed.
Lemma lem1989162 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989163 (y : real) (x : real) : (term179 y x) = (term192 y x).
Proof. exact (MK_COMB (@lem1989162) (@lem1989161 y x)). Qed.
Lemma lem1989164 (y : real) (x : real) : ((term178 y x) = (term179 y x)) = ((term170 y x) = (term192 y x)).
Proof. exact (MK_COMB (@lem1989155 y x) (@lem1989163 y x)). Qed.
Lemma lem1989165 (y : real) (x : real) : (term170 y x) = (term192 y x).
Proof. exact (EQ_MP (@lem1989164 y x) (@lem1989145 y x)). Qed.
Lemma lem1989166 (x : real) : (term172 x) = (term193 x).
Proof. exact (fun_ext (fun y : real => @lem1989165 y x)). Qed.
Lemma lem1989167 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989168 (x : real) : (term173 x) = (term194 x).
Proof. exact (MK_COMB (@lem1989167) (@lem1989166 x)). Qed.
Lemma lem1989169 (x : real) : (term155 x) = (term194 x).
Proof. exact (TRANS (@lem1989141 x) (@lem1989168 x)). Qed.
Lemma lem1989170 : term157 = term195.
Proof. exact (fun_ext (fun x : real => @lem1989169 x)). Qed.
Lemma lem1989171 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1989172 : term158 = term196.
Proof. exact (MK_COMB (@lem1989171) (@lem1989170)). Qed.
Lemma lem1989173 : term143 = term196.
Proof. exact (TRANS (@lem1989114) (@lem1989172)). Qed.
Lemma lem1989174 : term121 = term196.
Proof. exact (TRANS (@lem1989087) (@lem1989173)). Qed.
Lemma lem1989175 : term75 = term196.
Proof. exact (TRANS (@lem1989057) (@lem1989174)). Qed.
Lemma lem1989176 : term10 = term196.
Proof. exact (TRANS (@lem1988603) (@lem1989175)). Qed.
Lemma lem1989177 (h1 : term10) : term196.
Proof. exact (EQ_MP (@lem1989176) (@lem1988541 h1)). Qed.
Lemma lem1989178 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem1989179 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1989178 x)). Qed.
Lemma lem1989180 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989189 : term30 = term30.
Proof. exact (MK_COMB (@lem1989180) (@lem1989179)). Qed.
Lemma lem1989190 (h1 : term30) : term30.
Proof. exact (EQ_MP (@lem1989189) (@lem1988542 h1)). Qed.
Lemma lem1989197 (x : real) (y : real) (z : real) : (term197 x y z) = (term198 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem1989198 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem1989199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1989200 (x : real) (y : real) (z : real) : (term199 x y z) = (term200 x y z).
Proof. exact (MK_COMB (@lem1989199) (@lem1989197 x y z)). Qed.
Lemma lem1989201 (y : real) (x : real) (z : real) : (term201 y x z) = (term202 y x z).
Proof. exact (MK_COMB (@lem1989200 x y z) (@lem1989198 x z)). Qed.
Lemma lem1989202 (y : real) (x : real) (z : real) : (term23 y x z) = (term201 y x z).
Proof. exact (@lem17265 (term203 x y z) (real_le x z)). Qed.
Lemma lem1989203 (y : real) (x : real) (z : real) : (term23 y x z) = (term202 y x z).
Proof. exact (TRANS (@lem1989202 y x z) (@lem1989201 y x z)). Qed.
Lemma lem1989204 (y : real) (x : real) : (term24 y x) = (term204 y x).
Proof. exact (fun_ext (fun z : real => @lem1989203 y x z)). Qed.
Lemma lem1989205 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989206 (y : real) (x : real) : (term25 y x) = (term205 y x).
Proof. exact (MK_COMB (@lem1989205) (@lem1989204 y x)). Qed.
Lemma lem1989207 (x : real) : (term26 x) = (term206 x).
Proof. exact (fun_ext (fun y : real => @lem1989206 y x)). Qed.
Lemma lem1989208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989209 (x : real) : (term27 x) = (term207 x).
Proof. exact (MK_COMB (@lem1989208) (@lem1989207 x)). Qed.
Lemma lem1989210 : term28 = term208.
Proof. exact (fun_ext (fun x : real => @lem1989209 x)). Qed.
Lemma lem1989211 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989272 : term17 = term209.
Proof. exact (MK_COMB (@lem1989211) (@lem1989210)). Qed.
Lemma lem1989273 (h1 : term17) : term209.
Proof. exact (EQ_MP (@lem1989272) (@lem1988543 h1)). Qed.
Lemma lem1989274 (x : real) (h1 : term194 x) : term194 x.
Proof. exact (h1). Qed.
Lemma lem1989275 (y : real) (x : real) (h1 : term192 y x) : term192 y x.
Proof. exact (h1). Qed.
Lemma lem1989276 (z : real) (y : real) (x : real) (h1 : term189 z y x) : term189 z y x.
Proof. exact (h1). Qed.
Lemma lem1989281 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem1989282 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1989281 x)). Qed.
Lemma lem1989283 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989284 : term30 = term30.
Proof. exact (MK_COMB (@lem1989283) (@lem1989282)). Qed.
Lemma lem1989285 (h1 : term30) : term30.
Proof. exact (EQ_MP (@lem1989284) (@lem1989190 h1)). Qed.
Lemma lem1989310 (y : real) (x : real) (z : real) : (term202 y x z) = (term202 y x z).
Proof. exact (eq_refl (term202 y x z)). Qed.
Lemma lem1989311 (y : real) (x : real) : (term204 y x) = (term204 y x).
Proof. exact (fun_ext (fun z : real => @lem1989310 y x z)). Qed.
Lemma lem1989312 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989313 (y : real) (x : real) : (term205 y x) = (term205 y x).
Proof. exact (MK_COMB (@lem1989312) (@lem1989311 y x)). Qed.
Lemma lem1989314 (x : real) : (term206 x) = (term206 x).
Proof. exact (fun_ext (fun y : real => @lem1989313 y x)). Qed.
Lemma lem1989315 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989316 (x : real) : (term207 x) = (term207 x).
Proof. exact (MK_COMB (@lem1989315) (@lem1989314 x)). Qed.
Lemma lem1989317 : term208 = term208.
Proof. exact (fun_ext (fun x : real => @lem1989316 x)). Qed.
Lemma lem1989318 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989319 : term209 = term209.
Proof. exact (MK_COMB (@lem1989318) (@lem1989317)). Qed.
Lemma lem1989320 (h1 : term17) : term209.
Proof. exact (EQ_MP (@lem1989319) (@lem1989273 h1)). Qed.
Lemma lem1989335 (y : real) (x : real) (z : real) : (term40 y x z) = (term40 y x z).
Proof. exact (eq_refl (term40 y x z)). Qed.
Lemma lem1989336 (y : real) (x : real) : (term50 y x) = (term50 y x).
Proof. exact (fun_ext (fun z : real => @lem1989335 y x z)). Qed.
Lemma lem1989337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989338 (y : real) (x : real) : (term51 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1989337) (@lem1989336 y x)). Qed.
Lemma lem1989347 (x : real) (y : real) : (term52 x y) = (term52 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem1989348 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (MK_COMB (@lem1989347 x y) (@lem1989338 y x)). Qed.
Lemma lem1989373 (y : real) (x : real) (z : real) : (term187 y x z) = (term187 y x z).
Proof. exact (eq_refl (term187 y x z)). Qed.
Lemma lem1989374 (z : real) (y : real) (x : real) : (term189 z y x) = (term189 z y x).
Proof. exact (MK_COMB (@lem1989373 y x z) (@lem1989348 y x)). Qed.
Lemma lem1989375 (z : real) (y : real) (x : real) (h1 : term189 z y x) : term189 z y x.
Proof. exact (EQ_MP (@lem1989374 z y x) (@lem1989276 z y x h1)). Qed.
Lemma lem1989376 (y : real) (x : real) (z : real) (h1 : term134 y x z) : term134 y x z.
Proof. exact (h1). Qed.
Lemma lem1989377 (y : real) (x : real) (h1 : term54 y x) : term54 y x.
Proof. exact (h1). Qed.
Lemma lem1989378 (y : real) (x : real) (z : real) (h1 : term134 y x z) : term39 y x z.
Proof. exact (proj2 (@lem1989376 y x z h1)). Qed.
Lemma lem1989382 (y : real) (x : real) (h1 : term54 y x) : term51 y x.
Proof. exact (proj2 (@lem1989377 y x h1)). Qed.
Lemma lem1989404 (y : real) (x : real) (z : real) : (term202 y x z) = (term202 y x z).
Proof. exact (eq_refl (term202 y x z)). Qed.
Lemma lem1989405 (y : real) (x : real) : (term204 y x) = (term204 y x).
Proof. exact (fun_ext (fun z : real => @lem1989404 y x z)). Qed.
Lemma lem1989406 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989407 (y : real) (x : real) : (term205 y x) = (term205 y x).
Proof. exact (MK_COMB (@lem1989406) (@lem1989405 y x)). Qed.
Lemma lem1989408 (x : real) : (term206 x) = (term206 x).
Proof. exact (fun_ext (fun y : real => @lem1989407 y x)). Qed.
Lemma lem1989409 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989410 (x : real) : (term207 x) = (term207 x).
Proof. exact (MK_COMB (@lem1989409) (@lem1989408 x)). Qed.
Lemma lem1989411 : term208 = term208.
Proof. exact (fun_ext (fun x : real => @lem1989410 x)). Qed.
Lemma lem1989412 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989414 : term209 = term209.
Proof. exact (MK_COMB (@lem1989412) (@lem1989411)). Qed.
Lemma lem1989415 (h1 : term17) : term209.
Proof. exact (EQ_MP (@lem1989414) (@lem1989320 h1)). Qed.
Lemma lem1989429 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem1989430 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1989429 x)). Qed.
Lemma lem1989431 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989433 : term30 = term30.
Proof. exact (MK_COMB (@lem1989431) (@lem1989430)). Qed.
Lemma lem1989434 (h1 : term30) : term30.
Proof. exact (EQ_MP (@lem1989433) (@lem1989285 h1)). Qed.
Lemma lem1989471 (y : real) (x : real) (z : real) : (term40 y x z) = (term40 y x z).
Proof. exact (eq_refl (term40 y x z)). Qed.
Lemma lem1989472 (y : real) (x : real) : (term50 y x) = (term50 y x).
Proof. exact (fun_ext (fun z : real => @lem1989471 y x z)). Qed.
Lemma lem1989473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1989475 (y : real) (x : real) : (term51 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1989473) (@lem1989472 y x)). Qed.
Lemma lem1989476 (y : real) (x : real) (h1 : term54 y x) : term51 y x.
Proof. exact (EQ_MP (@lem1989475 y x) (@lem1989382 y x h1)). Qed.
Lemma lem1989480 (_27781 : real) (h1 : term17) : term210 _27781.
Proof. exact (@lem1989415 h1 _27781). Qed.
Lemma lem1989481 (_27781 : real) : (term210 _27781) = (term207 _27781).
Proof. exact (eq_refl (term210 _27781)). Qed.
Lemma lem1989482 (_27781 : real) (h1 : term17) : term207 _27781.
Proof. exact (EQ_MP (@lem1989481 _27781) (@lem1989480 _27781 h1)). Qed.
Lemma lem1989483 (_27781 : real) (_27782 : real) (h1 : term17) : term211 _27781 _27782.
Proof. exact (@lem1989482 _27781 h1 _27782). Qed.
Lemma lem1989484 (_27782 : real) (_27781 : real) : (term211 _27781 _27782) = (term205 _27782 _27781).
Proof. exact (eq_refl (term211 _27781 _27782)). Qed.
Lemma lem1989485 (_27782 : real) (_27781 : real) (h1 : term17) : term205 _27782 _27781.
Proof. exact (EQ_MP (@lem1989484 _27782 _27781) (@lem1989483 _27781 _27782 h1)). Qed.
Lemma lem1989486 (_27782 : real) (_27781 : real) (_27783 : real) (h1 : term17) : term212 _27782 _27781 _27783.
Proof. exact (@lem1989485 _27782 _27781 h1 _27783). Qed.
Lemma lem1989487 (_27782 : real) (_27781 : real) (_27783 : real) : (term212 _27782 _27781 _27783) = (term202 _27782 _27781 _27783).
Proof. exact (eq_refl (term212 _27782 _27781 _27783)). Qed.
Lemma lem1989488 (_27782 : real) (_27781 : real) (_27783 : real) (h1 : term17) : term202 _27782 _27781 _27783.
Proof. exact (EQ_MP (@lem1989487 _27782 _27781 _27783) (@lem1989486 _27782 _27781 _27783 h1)). Qed.
Lemma lem1989489 (_27784 : real) (h1 : term30) : term213 _27784.
Proof. exact (@lem1989434 h1 _27784). Qed.
Lemma lem1989490 (_27784 : real) : (term213 _27784) = (real_le _27784 _27784).
Proof. exact (eq_refl (term213 _27784)). Qed.
Lemma lem1989501 (_27788 : real) (y : real) (x : real) (h1 : term54 y x) : term214 y x _27788.
Proof. exact (@lem1989476 y x h1 _27788). Qed.
Lemma lem1989502 (y : real) (x : real) (_27788 : real) : (term214 y x _27788) = (term40 y x _27788).
Proof. exact (eq_refl (term214 y x _27788)). Qed.
Lemma lem1989516 (_27782 : real) (_27781 : real) (_27783 : real) : (term202 _27782 _27781 _27783) = (term215 _27782 _27781 _27783).
Proof. exact (@lem1988361 (term216 _27781 _27782) (term216 _27782 _27783) (real_le _27781 _27783)). Qed.
Lemma lem1989517 (_27782 : real) (_27781 : real) (_27783 : real) (h1 : term17) : term215 _27782 _27781 _27783.
Proof. exact (EQ_MP (@lem1989516 _27782 _27781 _27783) (@lem1989488 _27782 _27781 _27783 h1)). Qed.
Lemma lem1989523 (y : real) (x : real) (z : real) (h1 : term134 y x z) : term216 x z.
Proof. exact (proj2 (@lem1989378 y x z h1)). Qed.
Lemma lem1989539 (y : real) (x : real) (h1 : term54 y x) : term216 x y.
Proof. exact (proj1 (@lem1989377 y x h1)). Qed.
Lemma lem1989545 (_27788 : real) (y : real) (x : real) (h1 : term54 y x) : term40 y x _27788.
Proof. exact (EQ_MP (@lem1989502 y x _27788) (@lem1989501 _27788 y x h1)). Qed.
Lemma lem1989547 (y : real) (x : real) (z : real) (h1 : term134 y x z) : real_le x y.
Proof. exact (proj1 (@lem1989376 y x z h1)). Qed.
Lemma lem1989548 (y : real) (x : real) (z : real) (h1 : term134 y x z) : term217 x y.
Proof. exact (fun h0 : term216 x y => @lem1989547 y x z h1). Qed.
Lemma lem1989550 (p : Prop) : (term218 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1989551 (x : real) (y : real) : (term217 x y) = (real_le x y).
Proof. exact (@lem1989550 (real_le x y)). Qed.
Lemma lem1989552 (y : real) (x : real) (z : real) (h1 : term134 y x z) : real_le x y.
Proof. exact (EQ_MP (@lem1989551 x y) (@lem1989548 y x z h1)). Qed.
Lemma lem1989554 (y : real) (x : real) (z : real) (h1 : term134 y x z) : real_le y z.
Proof. exact (proj1 (@lem1989378 y x z h1)). Qed.
Lemma lem1989555 (y : real) (x : real) (z : real) (h1 : term134 y x z) : term217 y z.
Proof. exact (fun h0 : term216 y z => @lem1989554 y x z h1). Qed.
Lemma lem1989557 (p : Prop) : (term218 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1989558 (y : real) (z : real) : (term217 y z) = (real_le y z).
Proof. exact (@lem1989557 (real_le y z)). Qed.
Lemma lem1989559 (y : real) (x : real) (z : real) (h1 : term134 y x z) : real_le y z.
Proof. exact (EQ_MP (@lem1989558 y z) (@lem1989555 y x z h1)). Qed.
Lemma lem1989575 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1989576 (_27781 : real) (_27782 : real) (_27783 : real) : (term40 _27782 _27781 _27783) = (term219 _27781 _27782 _27783).
Proof. exact (@lem1989575 (real_le _27781 _27783) (term216 _27782 _27783)). Qed.
Lemma lem1989582 (_27781 : real) (_27782 : real) : (term220 _27781 _27782) = (term220 _27781 _27782).
Proof. exact (eq_refl (term220 _27781 _27782)). Qed.
Lemma lem1989583 (_27781 : real) (_27782 : real) (_27783 : real) : (term215 _27782 _27781 _27783) = (term221 _27781 _27782 _27783).
Proof. exact (MK_COMB (@lem1989582 _27781 _27782) (@lem1989576 _27781 _27782 _27783)). Qed.
Lemma lem1989587 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1989588 (_27781 : real) (_27782 : real) (_27783 : real) : (term221 _27781 _27782 _27783) = (term222 _27781 _27782 _27783).
Proof. exact (@lem1989587 (real_le _27781 _27783) (term216 _27781 _27782) (term216 _27782 _27783)). Qed.
Lemma lem1989604 (_27781 : real) (_27782 : real) (_27783 : real) : (term215 _27782 _27781 _27783) = (term222 _27781 _27782 _27783).
Proof. exact (TRANS (@lem1989583 _27781 _27782 _27783) (@lem1989588 _27781 _27782 _27783)). Qed.
Lemma lem1989605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1989606 (_27781 : real) (_27782 : real) (_27783 : real) : (term223 _27782 _27781 _27783) = (term224 _27781 _27782 _27783).
Proof. exact (MK_COMB (@lem1989605) (@lem1989604 _27781 _27782 _27783)). Qed.
Lemma lem1989622 (_27781 : real) (_27782 : real) (_27783 : real) : (term222 _27781 _27782 _27783) = (term222 _27781 _27782 _27783).
Proof. exact (eq_refl (term222 _27781 _27782 _27783)). Qed.
Lemma lem1989623 (_27781 : real) (_27782 : real) (_27783 : real) : ((term215 _27782 _27781 _27783) = (term222 _27781 _27782 _27783)) = ((term222 _27781 _27782 _27783) = (term222 _27781 _27782 _27783)).
Proof. exact (MK_COMB (@lem1989606 _27781 _27782 _27783) (@lem1989622 _27781 _27782 _27783)). Qed.
Lemma lem1989625 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1989626 (x : Prop) : (x = x) = True.
Proof. exact (@lem1989625 Prop x). Qed.
Lemma lem1989627 (_27781 : real) (_27782 : real) (_27783 : real) : ((term222 _27781 _27782 _27783) = (term222 _27781 _27782 _27783)) = True.
Proof. exact (@lem1989626 (term222 _27781 _27782 _27783)). Qed.
Lemma lem1989628 (_27781 : real) (_27782 : real) (_27783 : real) : ((term215 _27782 _27781 _27783) = (term222 _27781 _27782 _27783)) = True.
Proof. exact (TRANS (@lem1989623 _27781 _27782 _27783) (@lem1989627 _27781 _27782 _27783)). Qed.
Lemma lem1989629 (_27781 : real) (_27782 : real) (_27783 : real) : True = ((term215 _27782 _27781 _27783) = (term222 _27781 _27782 _27783)).
Proof. exact (SYM (@lem1989628 _27781 _27782 _27783)). Qed.
Lemma lem1989630 (_27781 : real) (_27782 : real) (_27783 : real) : (term215 _27782 _27781 _27783) = (term222 _27781 _27782 _27783).
Proof. exact (EQ_MP (@lem1989629 _27781 _27782 _27783) (@lem0)). Qed.
Lemma lem1989631 (_27781 : real) (_27782 : real) (_27783 : real) (h1 : term17) : term222 _27781 _27782 _27783.
Proof. exact (EQ_MP (@lem1989630 _27781 _27782 _27783) (@lem1989517 _27782 _27781 _27783 h1)). Qed.
Lemma lem1989633 (b : Prop) (a : Prop) : (a \/ b) = (term225 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1989634 (_27782 : real) (_27781 : real) (_27783 : real) : (term222 _27781 _27782 _27783) = (term226 _27782 _27781 _27783).
Proof. exact (@lem1989633 (term198 _27781 _27782 _27783) (real_le _27781 _27783)). Qed.
Lemma lem1989636 (a : Prop) (b : Prop) : (term227 a b) = (term228 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1989637 (_27781 : real) (_27782 : real) (_27783 : real) : (term229 _27781 _27782 _27783) = (term230 _27781 _27782 _27783).
Proof. exact (@lem1989636 (term216 _27781 _27782) (term216 _27782 _27783)). Qed.
Lemma lem1989639 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1989640 (_27781 : real) (_27782 : real) : (term232 _27781 _27782) = (real_le _27781 _27782).
Proof. exact (@lem1989639 (real_le _27781 _27782)). Qed.
Lemma lem1989641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1989642 (_27781 : real) (_27782 : real) : (term233 _27781 _27782) = (term55 _27781 _27782).
Proof. exact (MK_COMB (@lem1989641) (@lem1989640 _27781 _27782)). Qed.
Lemma lem1989644 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1989645 (_27782 : real) (_27783 : real) : (term232 _27782 _27783) = (real_le _27782 _27783).
Proof. exact (@lem1989644 (real_le _27782 _27783)). Qed.
Lemma lem1989646 (_27781 : real) (_27782 : real) (_27783 : real) : (term230 _27781 _27782 _27783) = (term203 _27781 _27782 _27783).
Proof. exact (MK_COMB (@lem1989642 _27781 _27782) (@lem1989645 _27782 _27783)). Qed.
Lemma lem1989647 (_27781 : real) (_27782 : real) (_27783 : real) : (term229 _27781 _27782 _27783) = (term203 _27781 _27782 _27783).
Proof. exact (TRANS (@lem1989637 _27781 _27782 _27783) (@lem1989646 _27781 _27782 _27783)). Qed.
Lemma lem1989648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1989649 (_27781 : real) (_27782 : real) (_27783 : real) : (term234 _27781 _27782 _27783) = (term235 _27781 _27782 _27783).
Proof. exact (MK_COMB (@lem1989648) (@lem1989647 _27781 _27782 _27783)). Qed.
Lemma lem1989650 (_27781 : real) (_27783 : real) : (real_le _27781 _27783) = (real_le _27781 _27783).
Proof. exact (eq_refl (real_le _27781 _27783)). Qed.
Lemma lem1989651 (_27782 : real) (_27781 : real) (_27783 : real) : (term226 _27782 _27781 _27783) = (term23 _27782 _27781 _27783).
Proof. exact (MK_COMB (@lem1989649 _27781 _27782 _27783) (@lem1989650 _27781 _27783)). Qed.
Lemma lem1989652 (_27782 : real) (_27781 : real) (_27783 : real) : (term222 _27781 _27782 _27783) = (term23 _27782 _27781 _27783).
Proof. exact (TRANS (@lem1989634 _27782 _27781 _27783) (@lem1989651 _27782 _27781 _27783)). Qed.
Lemma lem1989654 (y : real) (x : real) (z : real) (h1 : term134 y x z) : term203 x y z.
Proof. exact (conj (@lem1989552 y x z h1) (@lem1989559 y x z h1)). Qed.
Lemma lem1989656 (_27782 : real) (_27781 : real) (_27783 : real) (h1 : term17) : term23 _27782 _27781 _27783.
Proof. exact (EQ_MP (@lem1989652 _27782 _27781 _27783) (@lem1989631 _27781 _27782 _27783 h1)). Qed.
Lemma lem1989657 (y : real) (x : real) (z : real) (h1 : term17) : term23 y x z.
Proof. exact (@lem1989656 y x z h1). Qed.
Lemma lem1989660 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term134 y x z) : real_le x z.
Proof. exact (@lem1989657 y x z h1 (@lem1989654 y x z h2)). Qed.
Lemma lem1989661 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term134 y x z) : term217 x z.
Proof. exact (fun h0 : term216 x z => @lem1989660 y x z h1 h2). Qed.
Lemma lem1989663 (p : Prop) : (term218 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1989664 (x : real) (z : real) : (term217 x z) = (real_le x z).
Proof. exact (@lem1989663 (real_le x z)). Qed.
Lemma lem1989665 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term134 y x z) : real_le x z.
Proof. exact (EQ_MP (@lem1989664 x z) (@lem1989661 y x z h1 h2)). Qed.
Lemma lem1989668 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1989670 (x : real) (z : real) : (term216 x z) = (term236 x z).
Proof. exact (@lem1989668 (real_le x z)). Qed.
Lemma lem1989673 (y : real) (x : real) (z : real) (h1 : term134 y x z) : term236 x z.
Proof. exact (EQ_MP (@lem1989670 x z) (@lem1989523 y x z h1)). Qed.
Lemma lem1989676 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term134 y x z) : False.
Proof. exact (@lem1989673 y x z h2 (@lem1989665 y x z h1 h2)). Qed.
Lemma lem1989677 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term134 y x z) : term237.
Proof. exact (fun h0 : ~ False => @lem1989676 y x z h1 h2). Qed.
Lemma lem1989679 (p : Prop) : (term218 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1989680 : term237 = False.
Proof. exact (@lem1989679 False). Qed.
Lemma lem1989681 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term134 y x z) : False.
Proof. exact (EQ_MP (@lem1989680) (@lem1989677 y x z h1 h2)). Qed.
Lemma lem1989683 (_27784 : real) (h1 : term30) : real_le _27784 _27784.
Proof. exact (EQ_MP (@lem1989490 _27784) (@lem1989489 _27784 h1)). Qed.
Lemma lem1989684 (y : real) (h1 : term30) : real_le y y.
Proof. exact (@lem1989683 y h1). Qed.
Lemma lem1989685 (y : real) (h1 : term30) : term238 y.
Proof. exact (fun h0 : term239 y => @lem1989684 y h1). Qed.
Lemma lem1989687 (p : Prop) : (term218 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1989688 (y : real) : (term238 y) = (real_le y y).
Proof. exact (@lem1989687 (real_le y y)). Qed.
Lemma lem1989689 (y : real) (h1 : term30) : real_le y y.
Proof. exact (EQ_MP (@lem1989688 y) (@lem1989685 y h1)). Qed.
Lemma lem1989695 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1989696 (x : real) (y : real) (_27788 : real) : (term40 y x _27788) = (term219 x y _27788).
Proof. exact (@lem1989695 (real_le x _27788) (term216 y _27788)). Qed.
Lemma lem1989702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1989703 (x : real) (y : real) (_27788 : real) : (term240 y x _27788) = (term241 x y _27788).
Proof. exact (MK_COMB (@lem1989702) (@lem1989696 x y _27788)). Qed.
Lemma lem1989709 (x : real) (y : real) (_27788 : real) : (term219 x y _27788) = (term219 x y _27788).
Proof. exact (eq_refl (term219 x y _27788)). Qed.
Lemma lem1989710 (x : real) (y : real) (_27788 : real) : ((term40 y x _27788) = (term219 x y _27788)) = ((term219 x y _27788) = (term219 x y _27788)).
Proof. exact (MK_COMB (@lem1989703 x y _27788) (@lem1989709 x y _27788)). Qed.
Lemma lem1989712 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1989713 (x : Prop) : (x = x) = True.
Proof. exact (@lem1989712 Prop x). Qed.
Lemma lem1989714 (x : real) (y : real) (_27788 : real) : ((term219 x y _27788) = (term219 x y _27788)) = True.
Proof. exact (@lem1989713 (term219 x y _27788)). Qed.
Lemma lem1989715 (x : real) (y : real) (_27788 : real) : ((term40 y x _27788) = (term219 x y _27788)) = True.
Proof. exact (TRANS (@lem1989710 x y _27788) (@lem1989714 x y _27788)). Qed.
Lemma lem1989716 (x : real) (y : real) (_27788 : real) : True = ((term40 y x _27788) = (term219 x y _27788)).
Proof. exact (SYM (@lem1989715 x y _27788)). Qed.
Lemma lem1989717 (x : real) (y : real) (_27788 : real) : (term40 y x _27788) = (term219 x y _27788).
Proof. exact (EQ_MP (@lem1989716 x y _27788) (@lem0)). Qed.
Lemma lem1989718 (_27788 : real) (y : real) (x : real) (h1 : term54 y x) : term219 x y _27788.
Proof. exact (EQ_MP (@lem1989717 x y _27788) (@lem1989545 _27788 y x h1)). Qed.
Lemma lem1989720 (b : Prop) (a : Prop) : (a \/ b) = (term225 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1989721 (y : real) (x : real) (_27788 : real) : (term219 x y _27788) = (term242 y x _27788).
Proof. exact (@lem1989720 (term216 y _27788) (real_le x _27788)). Qed.
Lemma lem1989723 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1989724 (y : real) (_27788 : real) : (term232 y _27788) = (real_le y _27788).
Proof. exact (@lem1989723 (real_le y _27788)). Qed.
Lemma lem1989725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1989726 (y : real) (_27788 : real) : (term243 y _27788) = (term244 y _27788).
Proof. exact (MK_COMB (@lem1989725) (@lem1989724 y _27788)). Qed.
Lemma lem1989727 (x : real) (_27788 : real) : (real_le x _27788) = (real_le x _27788).
Proof. exact (eq_refl (real_le x _27788)). Qed.
Lemma lem1989728 (y : real) (x : real) (_27788 : real) : (term242 y x _27788) = (term31 y x _27788).
Proof. exact (MK_COMB (@lem1989726 y _27788) (@lem1989727 x _27788)). Qed.
Lemma lem1989729 (y : real) (x : real) (_27788 : real) : (term219 x y _27788) = (term31 y x _27788).
Proof. exact (TRANS (@lem1989721 y x _27788) (@lem1989728 y x _27788)). Qed.
Lemma lem1989732 (_27788 : real) (y : real) (x : real) (h1 : term54 y x) : term31 y x _27788.
Proof. exact (EQ_MP (@lem1989729 y x _27788) (@lem1989718 _27788 y x h1)). Qed.
Lemma lem1989733 (y : real) (x : real) (h1 : term54 y x) : term245 x y.
Proof. exact (@lem1989732 y y x h1). Qed.
Lemma lem1989736 (y : real) (x : real) (h1 : term30) (h2 : term54 y x) : real_le x y.
Proof. exact (@lem1989733 y x h2 (@lem1989689 y h1)). Qed.
Lemma lem1989737 (y : real) (x : real) (h1 : term30) (h2 : term54 y x) : term217 x y.
Proof. exact (fun h0 : term216 x y => @lem1989736 y x h1 h2). Qed.
Lemma lem1989739 (p : Prop) : (term218 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1989740 (x : real) (y : real) : (term217 x y) = (real_le x y).
Proof. exact (@lem1989739 (real_le x y)). Qed.
Lemma lem1989741 (y : real) (x : real) (h1 : term30) (h2 : term54 y x) : real_le x y.
Proof. exact (EQ_MP (@lem1989740 x y) (@lem1989737 y x h1 h2)). Qed.
Lemma lem1989744 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1989746 (x : real) (y : real) : (term216 x y) = (term236 x y).
Proof. exact (@lem1989744 (real_le x y)). Qed.
Lemma lem1989749 (y : real) (x : real) (h1 : term54 y x) : term236 x y.
Proof. exact (EQ_MP (@lem1989746 x y) (@lem1989539 y x h1)). Qed.
Lemma lem1989752 (y : real) (x : real) (h1 : term30) (h2 : term54 y x) : False.
Proof. exact (@lem1989749 y x h2 (@lem1989741 y x h1 h2)). Qed.
Lemma lem1989753 (y : real) (x : real) (h1 : term30) (h2 : term54 y x) : term237.
Proof. exact (fun h0 : ~ False => @lem1989752 y x h1 h2). Qed.
Lemma lem1989755 (p : Prop) : (term218 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1989756 : term237 = False.
Proof. exact (@lem1989755 False). Qed.
Lemma lem1989757 (y : real) (x : real) (h1 : term30) (h2 : term54 y x) : False.
Proof. exact (EQ_MP (@lem1989756) (@lem1989753 y x h1 h2)). Qed.
Lemma lem1989758 (y : real) (x : real) (h1 : term30) (h2 : term54 y x) : term30 = False.
Proof. exact (prop_ext (fun h3 : term30 => @lem1989757 y x h1 h2) (fun h3 : False => @lem1989434 h1)). Qed.
Lemma lem1989759 (y : real) (x : real) (h1 : term30) (h2 : term54 y x) : False.
Proof. exact (EQ_MP (@lem1989758 y x h1 h2) (@lem1989434 h1)). Qed.
Lemma lem1989760 (z : real) (y : real) (x : real) (h1 : term17) (h2 : term30) (h3 : term189 z y x) : False.
Proof. exact (or_elim (@lem1989375 z y x h3) (fun h0 : term134 y x z => @lem1989681 y x z h1 h0) (fun h0 : term54 y x => @lem1989759 y x h2 h0)). Qed.
Lemma lem1989761 (z : real) (y : real) (x : real) (h1 : term17) (h2 : term30) (h3 : term189 z y x) : (term189 z y x) = False.
Proof. exact (prop_ext (fun h4 : term189 z y x => @lem1989760 z y x h1 h2 h3) (fun h4 : False => @lem1989375 z y x h3)). Qed.
Lemma lem1989762 (z : real) (y : real) (x : real) (h1 : term17) (h2 : term30) (h3 : term189 z y x) : False.
Proof. exact (EQ_MP (@lem1989761 z y x h1 h2 h3) (@lem1989375 z y x h3)). Qed.
Lemma lem1989763 (z : real) (y : real) (x : real) (h1 : term17) (h2 : term30) (h3 : term189 z y x) : term30 = False.
Proof. exact (prop_ext (fun h4 : term30 => @lem1989762 z y x h1 h2 h3) (fun h4 : False => @lem1989285 h2)). Qed.
Lemma lem1989764 (z : real) (y : real) (x : real) (h1 : term17) (h2 : term30) (h3 : term189 z y x) : False.
Proof. exact (EQ_MP (@lem1989763 z y x h1 h2 h3) (@lem1989285 h2)). Qed.
Lemma lem1989765 (y : real) (x : real) (h1 : term17) (h2 : term30) (h3 : term192 y x) : False.
Proof. exact (ex_elim (@lem1989275 y x h3) (fun z : real => fun h0 : term191 y x z => @lem1989764 z y x h1 h2 h0)). Qed.
Lemma lem1989766 (x : real) (h1 : term17) (h2 : term30) (h3 : term194 x) : False.
Proof. exact (ex_elim (@lem1989274 x h3) (fun y : real => fun h0 : term193 x y => @lem1989765 y x h1 h2 h0)). Qed.
Lemma lem1989767 (h1 : term17) (h2 : term30) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1989177 h3) (fun x : real => fun h0 : term195 x => @lem1989766 x h1 h2 h0)). Qed.
Lemma lem1989768 (h1 : term17) (h2 : term30) (h3 : term10) : term30 = False.
Proof. exact (prop_ext (fun h4 : term30 => @lem1989767 h1 h2 h3) (fun h4 : False => @lem1989190 h2)). Qed.
Lemma lem1989769 (h1 : term17) (h2 : term30) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem1989768 h1 h2 h3) (@lem1989190 h2)). Qed.
Lemma lem1989770 (h1 : term30) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1989769 h0 h1 h2). Qed.
Lemma lem1989771 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1989772 (h1 : term30) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1989771) (@lem1989770 h1 h2)). Qed.
Lemma lem1989773 (h1 : term10) : term20.
Proof. exact (fun h0 : term30 => @lem1989772 h0 h1). Qed.
Lemma lem1989774 : term22.
Proof. exact (fun h0 : term10 => @lem1989773 h0). Qed.
Lemma lem1989775 : term11.
Proof. exact (EQ_MP (@lem1988540) (@lem1989774)). Qed.
Lemma lem1989777 : term11.
Proof. exact (@lem1988381 (@lem1989775)). Qed.
Lemma lem1989778 (h1 : term10) : term19.
Proof. exact (@lem1989777 (@lem1988366 h1)). Qed.
Lemma lem1989779 (h1 : term10) : term15.
Proof. exact (@lem1989778 h1 (@lem1339240)). Qed.
Lemma lem1989780 (h1 : term10) : False.
Proof. exact (@lem1989779 h1 (@lem1339577)). Qed.
Lemma lem1989781 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1989780 h1) (fun h2 : False => @lem1988366 h1)). Qed.
Lemma lem1989782 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1989781 h1) (@lem1988366 h1)). Qed.
Lemma lem1989783 : term9.
Proof. exact (fun h0 : term10 => @lem1989782 h0). Qed.
Lemma lem1989784 : term8.
Proof. exact (EQ_MP (@lem1988365) (@lem1989783)). Qed.
