Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_EMPTY_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import IN_NUMSEG_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem5374367 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5374368 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5374369 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5374368 t1) (@lem5374367 t1)). Qed.
Lemma lem5374370 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5374369 t1 t2). Qed.
Lemma lem5374371 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5374372 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5374371 t1 t2) (@lem5374370 t1 t2)). Qed.
Lemma lem5374373 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5374372 t1 t2 t3). Qed.
Lemma lem5374374 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5374375 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5374374 t1 t2 t3) (@lem5374373 t1 t2 t3)). Qed.
Lemma lem5374376 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5374375 t1 t2 t3)). Qed.
Lemma lem5374377 (m : nat) : term7 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5374378 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem5374379 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem5374378 m) (@lem5374377 m)). Qed.
Lemma lem5374380 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem5374379 m n). Qed.
Lemma lem5374381 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem5374382 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem5374381 m n) (@lem5374380 m n)). Qed.
Lemma lem5374383 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem5374382 m n p). Qed.
Lemma lem5374384 (m : nat) (p : nat) (n : nat) : (term11 m n p) = ((term12 p m n) = (term13 m p n)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem5374386 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5374387 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem5374388 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem5374387 A x) (@lem5374386 A x)). Qed.
Lemma lem5374389 {A : Type'} (x : A) : term16 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5374391 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5374392 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem5374393 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem5374392 A s) (@lem5374391 A s)). Qed.
Lemma lem5374394 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem5374393 A s t). Qed.
Lemma lem5374395 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem5374412 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem5374395 A s t) (@lem5374394 A s t)). Qed.
Lemma lem5374413 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term21 s t).
Proof. exact (@lem5374412 nat s t). Qed.
Lemma lem5374414 (m : nat) (n : nat) : ((dotdot m n) = (@EMPTY nat)) = (term22 m n).
Proof. exact (@lem5374413 (dotdot m n) (@EMPTY nat)). Qed.
Lemma lem5374424 (m : nat) (p : nat) (n : nat) : (term12 p m n) = (term13 m p n).
Proof. exact (EQ_MP (@lem5374384 m p n) (@lem5374383 m n p)). Qed.
Lemma lem5374425 (m : nat) (x : nat) (n : nat) : (term12 x m n) = (term13 m x n).
Proof. exact (@lem5374424 m x n). Qed.
Lemma lem5374428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5374429 (m : nat) (x : nat) (n : nat) : (term23 x m n) = (term24 m x n).
Proof. exact (MK_COMB (@lem5374428) (@lem5374425 m x n)). Qed.
Lemma lem5374431 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5374389 A x (@lem5374388 A x)). Qed.
Lemma lem5374432 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem5374431 nat x). Qed.
Lemma lem5374433 (m : nat) (x : nat) (n : nat) : ((term12 x m n) = (@IN nat x (@EMPTY nat))) = ((term13 m x n) = False).
Proof. exact (MK_COMB (@lem5374429 m x n) (@lem5374432 x)). Qed.
Lemma lem5374435 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5374436 (m : nat) (x : nat) (n : nat) : ((term13 m x n) = False) = (term25 m x n).
Proof. exact (@lem5374435 (term13 m x n)). Qed.
Lemma lem5374439 (m : nat) (x : nat) (n : nat) : ((term12 x m n) = (@IN nat x (@EMPTY nat))) = (term25 m x n).
Proof. exact (TRANS (@lem5374433 m x n) (@lem5374436 m x n)). Qed.
Lemma lem5374440 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (fun_ext (fun x : nat => @lem5374439 m x n)). Qed.
Lemma lem5374441 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374442 (m : nat) (n : nat) : (term22 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem5374441) (@lem5374440 m n)). Qed.
Lemma lem5374447 (m : nat) (n : nat) : ((dotdot m n) = (@EMPTY nat)) = (term28 m n).
Proof. exact (TRANS (@lem5374414 m n) (@lem5374442 m n)). Qed.
Lemma lem5374448 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5374449 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem5374448) (@lem5374447 m n)). Qed.
Lemma lem5374450 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem5374451 (n : nat) (m : nat) : (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m)) = ((term28 m n) = (Peano.lt n m)).
Proof. exact (MK_COMB (@lem5374449 m n) (@lem5374450 n m)). Qed.
Lemma lem5374456 (m : nat) : (term31 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem5374451 n m)). Qed.
Lemma lem5374457 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374458 (m : nat) : (term33 m) = (term34 m).
Proof. exact (MK_COMB (@lem5374457) (@lem5374456 m)). Qed.
Lemma lem5374463 : term35 = term36.
Proof. exact (fun_ext (fun m : nat => @lem5374458 m)). Qed.
Lemma lem5374464 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374465 : term37 = term38.
Proof. exact (MK_COMB (@lem5374464) (@lem5374463)). Qed.
Lemma lem5374470 : term38 = term37.
Proof. exact (SYM (@lem5374465)). Qed.
Lemma lem5374472 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5374473 : term38 = term40.
Proof. exact (@lem5374472 term38). Qed.
Lemma lem5374474 : term40 = term38.
Proof. exact (SYM (@lem5374473)). Qed.
Lemma lem5374475 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem5374478 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem5374479 : term43.
Proof. exact (fun h0 : term42 => @lem5374478 h0). Qed.
Lemma lem5374480 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem5374481 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem5374482 (h1 : term42) (h2 : term43) : term42.
Proof. exact (@lem5374480 h2 (@lem5374481 h1)). Qed.
Lemma lem5374483 (h1 : term42) : term44.
Proof. exact (fun h0 : term43 => @lem5374482 h1 h0). Qed.
Lemma lem5374484 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem5374485 (h1 : term42) (h2 : term43) : term42.
Proof. exact (@lem5374483 h1 (@lem5374484 h2)). Qed.
Lemma lem5374486 (h1 : term43) : term43.
Proof. exact (fun h0 : term42 => @lem5374485 h0 h1). Qed.
Lemma lem5374487 : term45.
Proof. exact (fun h0 : term43 => @lem5374486 h0). Qed.
Lemma lem5374490 : term43.
Proof. exact (@lem5374487 (@lem5374479)). Qed.
Lemma lem5374532 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5374533 : term46 = term47.
Proof. exact (@lem5374532 term48). Qed.
Lemma lem5374542 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem5374543 : term50 = term51.
Proof. exact (MK_COMB (@lem5374542) (@lem5374533)). Qed.
Lemma lem5374546 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem5374547 : term53 = term54.
Proof. exact (MK_COMB (@lem5374546) (@lem5374543)). Qed.
Lemma lem5374550 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem5374557 : term42 = term56.
Proof. exact (MK_COMB (@lem5374550) (@lem5374547)). Qed.
Lemma lem5374564 (n : nat) (m : nat) : ((term57 m n) = (Peano.lt n m)) = ((term57 m n) = (Peano.lt n m)).
Proof. exact (eq_refl ((term57 m n) = (Peano.lt n m))). Qed.
Lemma lem5374565 (m : nat) : (term58 m) = (term58 m).
Proof. exact (fun_ext (fun n : nat => @lem5374564 n m)). Qed.
Lemma lem5374566 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374567 (m : nat) : (term59 m) = (term59 m).
Proof. exact (MK_COMB (@lem5374566) (@lem5374565 m)). Qed.
Lemma lem5374568 : term60 = term60.
Proof. exact (fun_ext (fun m : nat => @lem5374567 m)). Qed.
Lemma lem5374569 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374570 : term48 = term48.
Proof. exact (MK_COMB (@lem5374569) (@lem5374568)). Qed.
Lemma lem5374571 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5374572 : term47 = term47.
Proof. exact (MK_COMB (@lem5374571) (@lem5374570)). Qed.
Lemma lem5374581 (n : nat) (m : nat) (p : nat) : (term61 n m p) = (term61 n m p).
Proof. exact (eq_refl (term61 n m p)). Qed.
Lemma lem5374582 (n : nat) (m : nat) : (term62 n m) = (term62 n m).
Proof. exact (fun_ext (fun p : nat => @lem5374581 n m p)). Qed.
Lemma lem5374583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374584 (n : nat) (m : nat) : (term63 n m) = (term63 n m).
Proof. exact (MK_COMB (@lem5374583) (@lem5374582 n m)). Qed.
Lemma lem5374585 (m : nat) : (term64 m) = (term64 m).
Proof. exact (fun_ext (fun n : nat => @lem5374584 n m)). Qed.
Lemma lem5374586 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374587 (m : nat) : (term65 m) = (term65 m).
Proof. exact (MK_COMB (@lem5374586) (@lem5374585 m)). Qed.
Lemma lem5374588 : term66 = term66.
Proof. exact (fun_ext (fun m : nat => @lem5374587 m)). Qed.
Lemma lem5374589 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374590 : term67 = term67.
Proof. exact (MK_COMB (@lem5374589) (@lem5374588)). Qed.
Lemma lem5374591 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5374592 : term49 = term49.
Proof. exact (MK_COMB (@lem5374591) (@lem5374590)). Qed.
Lemma lem5374593 : term51 = term51.
Proof. exact (MK_COMB (@lem5374592) (@lem5374572)). Qed.
Lemma lem5374594 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5374595 : term68 = term68.
Proof. exact (fun_ext (fun n : nat => @lem5374594 n)). Qed.
Lemma lem5374596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374597 : term69 = term69.
Proof. exact (MK_COMB (@lem5374596) (@lem5374595)). Qed.
Lemma lem5374598 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5374599 : term52 = term52.
Proof. exact (MK_COMB (@lem5374598) (@lem5374597)). Qed.
Lemma lem5374600 : term54 = term54.
Proof. exact (MK_COMB (@lem5374599) (@lem5374593)). Qed.
Lemma lem5374601 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem5374608 (m : nat) (x : nat) (n : nat) : (term25 m x n) = (term25 m x n).
Proof. exact (eq_refl (term25 m x n)). Qed.
Lemma lem5374609 (m : nat) (n : nat) : (term27 m n) = (term27 m n).
Proof. exact (fun_ext (fun x : nat => @lem5374608 m x n)). Qed.
Lemma lem5374610 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374611 (m : nat) (n : nat) : (term28 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem5374610) (@lem5374609 m n)). Qed.
Lemma lem5374612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5374613 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem5374612) (@lem5374611 m n)). Qed.
Lemma lem5374614 (n : nat) (m : nat) : ((term28 m n) = (Peano.lt n m)) = ((term28 m n) = (Peano.lt n m)).
Proof. exact (MK_COMB (@lem5374613 m n) (@lem5374601 n m)). Qed.
Lemma lem5374615 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem5374614 n m)). Qed.
Lemma lem5374616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374617 (m : nat) : (term34 m) = (term34 m).
Proof. exact (MK_COMB (@lem5374616) (@lem5374615 m)). Qed.
Lemma lem5374618 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem5374617 m)). Qed.
Lemma lem5374619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374620 : term38 = term38.
Proof. exact (MK_COMB (@lem5374619) (@lem5374618)). Qed.
Lemma lem5374621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5374622 : term41 = term41.
Proof. exact (MK_COMB (@lem5374621) (@lem5374620)). Qed.
Lemma lem5374623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5374624 : term55 = term55.
Proof. exact (MK_COMB (@lem5374623) (@lem5374622)). Qed.
Lemma lem5374625 : term56 = term56.
Proof. exact (MK_COMB (@lem5374624) (@lem5374600)). Qed.
Lemma lem5374694 : term42 = term56.
Proof. exact (TRANS (@lem5374557) (@lem5374625)). Qed.
Lemma lem5374695 : term56 = term42.
Proof. exact (SYM (@lem5374694)). Qed.
Lemma lem5374696 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem5374697 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem5374698 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem5374699 (h1 : term48) : term48.
Proof. exact (h1). Qed.
Lemma lem5374708 (m : nat) (x : nat) (n : nat) : (term25 m x n) = (term70 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem5374713 (m : nat) (x : nat) (n : nat) : (term71 m x n) = (term13 m x n).
Proof. exact (@lem16933 (term13 m x n)). Qed.
Lemma lem5374714 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5374715 (m : nat) (n : nat) : (term74 m n) = (term75 m n).
Proof. exact (@lem5374714 (term27 m n)). Qed.
Lemma lem5374716 (m : nat) (x : nat) (n : nat) : (term76 m n x) = (term25 m x n).
Proof. exact (eq_refl (term76 m n x)). Qed.
Lemma lem5374717 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5374718 (m : nat) (x : nat) (n : nat) : (term77 m n x) = (term71 m x n).
Proof. exact (MK_COMB (@lem5374717) (@lem5374716 m x n)). Qed.
Lemma lem5374719 (m : nat) (x : nat) (n : nat) : (term77 m n x) = (term13 m x n).
Proof. exact (TRANS (@lem5374718 m x n) (@lem5374713 m x n)). Qed.
Lemma lem5374720 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (fun_ext (fun x : nat => @lem5374719 m x n)). Qed.
Lemma lem5374721 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5374722 (m : nat) (n : nat) : (term75 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem5374721) (@lem5374720 m n)). Qed.
Lemma lem5374723 (m : nat) (n : nat) : (term74 m n) = (term80 m n).
Proof. exact (TRANS (@lem5374715 m n) (@lem5374722 m n)). Qed.
Lemma lem5374724 (m : nat) (n : nat) : (term27 m n) = (term81 m n).
Proof. exact (fun_ext (fun x : nat => @lem5374708 m x n)). Qed.
Lemma lem5374725 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5374726 (m : nat) (n : nat) : (term28 m n) = (term82 m n).
Proof. exact (MK_COMB (@lem5374725) (@lem5374724 m n)). Qed.
Lemma lem5374727 (n : nat) (m : nat) : (term83 n m) = (term83 n m).
Proof. exact (eq_refl (term83 n m)). Qed.
Lemma lem5374728 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem5374729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5374730 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem5374729) (@lem5374723 m n)). Qed.
Lemma lem5374731 (n : nat) (m : nat) : (term86 n m) = (term87 n m).
Proof. exact (MK_COMB (@lem5374730 m n) (@lem5374728 n m)). Qed.
Lemma lem5374732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5374733 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem5374732) (@lem5374726 m n)). Qed.
Lemma lem5374734 (n : nat) (m : nat) : (term90 n m) = (term91 n m).
Proof. exact (MK_COMB (@lem5374733 m n) (@lem5374727 n m)). Qed.
Lemma lem5374735 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5374736 (n : nat) (m : nat) : (term92 n m) = (term93 n m).
Proof. exact (MK_COMB (@lem5374735) (@lem5374734 n m)). Qed.
Lemma lem5374737 (n : nat) (m : nat) : (term94 n m) = (term95 n m).
Proof. exact (MK_COMB (@lem5374736 n m) (@lem5374731 n m)). Qed.
Lemma lem5374738 (n : nat) (m : nat) : (term96 n m) = (term94 n m).
Proof. exact (@lem17646 (term28 m n) (Peano.lt n m)). Qed.
Lemma lem5374739 (n : nat) (m : nat) : (term96 n m) = (term95 n m).
Proof. exact (TRANS (@lem5374738 n m) (@lem5374737 n m)). Qed.
Lemma lem5374740 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5374741 (m : nat) : (term97 m) = (term98 m).
Proof. exact (@lem5374740 (term32 m)). Qed.
Lemma lem5374742 (n : nat) (m : nat) : (term99 m n) = ((term28 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term99 m n)). Qed.
Lemma lem5374743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5374744 (n : nat) (m : nat) : (term100 m n) = (term96 n m).
Proof. exact (MK_COMB (@lem5374743) (@lem5374742 n m)). Qed.
Lemma lem5374745 (n : nat) (m : nat) : (term100 m n) = (term95 n m).
Proof. exact (TRANS (@lem5374744 n m) (@lem5374739 n m)). Qed.
Lemma lem5374746 (m : nat) : (term101 m) = (term102 m).
Proof. exact (fun_ext (fun n : nat => @lem5374745 n m)). Qed.
Lemma lem5374747 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5374748 (m : nat) : (term98 m) = (term103 m).
Proof. exact (MK_COMB (@lem5374747) (@lem5374746 m)). Qed.
Lemma lem5374749 (m : nat) : (term97 m) = (term103 m).
Proof. exact (TRANS (@lem5374741 m) (@lem5374748 m)). Qed.
Lemma lem5374750 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5374751 : term41 = term104.
Proof. exact (@lem5374750 term36). Qed.
Lemma lem5374752 (m : nat) : (term105 m) = (term34 m).
Proof. exact (eq_refl (term105 m)). Qed.
Lemma lem5374753 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5374754 (m : nat) : (term106 m) = (term97 m).
Proof. exact (MK_COMB (@lem5374753) (@lem5374752 m)). Qed.
Lemma lem5374755 (m : nat) : (term106 m) = (term103 m).
Proof. exact (TRANS (@lem5374754 m) (@lem5374749 m)). Qed.
Lemma lem5374756 : term107 = term108.
Proof. exact (fun_ext (fun m : nat => @lem5374755 m)). Qed.
Lemma lem5374757 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5374758 : term104 = term109.
Proof. exact (MK_COMB (@lem5374757) (@lem5374756)). Qed.
Lemma lem5374759 : term41 = term109.
Proof. exact (TRANS (@lem5374751) (@lem5374758)). Qed.
Lemma lem5374765 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5374766 (P : nat -> Prop) (Q : nat -> Prop) : (term112 P Q) = (term113 P Q).
Proof. exact (@lem5374765 nat P Q). Qed.
Lemma lem5374767 (m : nat) : (term114 m) = (term115 m).
Proof. exact (@lem5374766 (term116 m) (term117 m)). Qed.
Lemma lem5374768 (n : nat) (m : nat) : (term118 m n) = (term91 n m).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem5374769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5374770 (n : nat) (m : nat) : (term119 m n) = (term93 n m).
Proof. exact (MK_COMB (@lem5374769) (@lem5374768 n m)). Qed.
Lemma lem5374771 (n : nat) (m : nat) : (term120 m n) = (term87 n m).
Proof. exact (eq_refl (term120 m n)). Qed.
Lemma lem5374772 (n : nat) (m : nat) : (term121 m n) = (term95 n m).
Proof. exact (MK_COMB (@lem5374770 n m) (@lem5374771 n m)). Qed.
Lemma lem5374773 (m : nat) : (term122 m) = (term102 m).
Proof. exact (fun_ext (fun n : nat => @lem5374772 n m)). Qed.
Lemma lem5374774 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5374775 (m : nat) : (term114 m) = (term103 m).
Proof. exact (MK_COMB (@lem5374774) (@lem5374773 m)). Qed.
Lemma lem5374776 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5374777 (m : nat) : (term123 m) = (term124 m).
Proof. exact (MK_COMB (@lem5374776) (@lem5374775 m)). Qed.
Lemma lem5374778 (n : nat) (m : nat) : (term118 m n) = (term91 n m).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem5374779 (m : nat) : (term125 m) = (term116 m).
Proof. exact (fun_ext (fun n : nat => @lem5374778 n m)). Qed.
Lemma lem5374780 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5374781 (m : nat) : (term126 m) = (term127 m).
Proof. exact (MK_COMB (@lem5374780) (@lem5374779 m)). Qed.
Lemma lem5374782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5374783 (m : nat) : (term128 m) = (term129 m).
Proof. exact (MK_COMB (@lem5374782) (@lem5374781 m)). Qed.
Lemma lem5374784 (n : nat) (m : nat) : (term120 m n) = (term87 n m).
Proof. exact (eq_refl (term120 m n)). Qed.
Lemma lem5374785 (m : nat) : (term130 m) = (term117 m).
Proof. exact (fun_ext (fun n : nat => @lem5374784 n m)). Qed.
Lemma lem5374786 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5374787 (m : nat) : (term131 m) = (term132 m).
Proof. exact (MK_COMB (@lem5374786) (@lem5374785 m)). Qed.
Lemma lem5374788 (m : nat) : (term115 m) = (term133 m).
Proof. exact (MK_COMB (@lem5374783 m) (@lem5374787 m)). Qed.
Lemma lem5374789 (m : nat) : ((term114 m) = (term115 m)) = ((term103 m) = (term133 m)).
Proof. exact (MK_COMB (@lem5374777 m) (@lem5374788 m)). Qed.
Lemma lem5374790 (m : nat) : (term103 m) = (term133 m).
Proof. exact (EQ_MP (@lem5374789 m) (@lem5374767 m)). Qed.
Lemma lem5374983 : term108 = term134.
Proof. exact (fun_ext (fun m : nat => @lem5374790 m)). Qed.
Lemma lem5374984 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5374985 : term109 = term135.
Proof. exact (MK_COMB (@lem5374984) (@lem5374983)). Qed.
Lemma lem5374987 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5374988 (P : nat -> Prop) (Q : nat -> Prop) : (term112 P Q) = (term113 P Q).
Proof. exact (@lem5374987 nat P Q). Qed.
Lemma lem5374989 : term136 = term137.
Proof. exact (@lem5374988 term138 term139). Qed.
Lemma lem5374990 (m : nat) : (term140 m) = (term127 m).
Proof. exact (eq_refl (term140 m)). Qed.
Lemma lem5374991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5374992 (m : nat) : (term141 m) = (term129 m).
Proof. exact (MK_COMB (@lem5374991) (@lem5374990 m)). Qed.
Lemma lem5374993 (m : nat) : (term142 m) = (term132 m).
Proof. exact (eq_refl (term142 m)). Qed.
Lemma lem5374994 (m : nat) : (term143 m) = (term133 m).
Proof. exact (MK_COMB (@lem5374992 m) (@lem5374993 m)). Qed.
Lemma lem5374995 : term144 = term134.
Proof. exact (fun_ext (fun m : nat => @lem5374994 m)). Qed.
Lemma lem5374996 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5374997 : term136 = term135.
Proof. exact (MK_COMB (@lem5374996) (@lem5374995)). Qed.
Lemma lem5374998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5374999 : term145 = term146.
Proof. exact (MK_COMB (@lem5374998) (@lem5374997)). Qed.
Lemma lem5375000 (m : nat) : (term140 m) = (term127 m).
Proof. exact (eq_refl (term140 m)). Qed.
Lemma lem5375001 : term147 = term138.
Proof. exact (fun_ext (fun m : nat => @lem5375000 m)). Qed.
Lemma lem5375002 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375003 : term148 = term149.
Proof. exact (MK_COMB (@lem5375002) (@lem5375001)). Qed.
Lemma lem5375004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5375005 : term150 = term151.
Proof. exact (MK_COMB (@lem5375004) (@lem5375003)). Qed.
Lemma lem5375006 (m : nat) : (term142 m) = (term132 m).
Proof. exact (eq_refl (term142 m)). Qed.
Lemma lem5375007 : term152 = term139.
Proof. exact (fun_ext (fun m : nat => @lem5375006 m)). Qed.
Lemma lem5375008 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375009 : term153 = term154.
Proof. exact (MK_COMB (@lem5375008) (@lem5375007)). Qed.
Lemma lem5375010 : term137 = term155.
Proof. exact (MK_COMB (@lem5375005) (@lem5375009)). Qed.
Lemma lem5375011 : (term136 = term137) = (term135 = term155).
Proof. exact (MK_COMB (@lem5374999) (@lem5375010)). Qed.
Lemma lem5375012 : term135 = term155.
Proof. exact (EQ_MP (@lem5375011) (@lem5374989)). Qed.
Lemma lem5375213 : term109 = term155.
Proof. exact (TRANS (@lem5374985) (@lem5375012)). Qed.
Lemma lem5375215 {A : Type'} (P : A -> Prop) (Q : Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5375216 (P : nat -> Prop) (Q : Prop) : (term158 P Q) = (term159 P Q).
Proof. exact (@lem5375215 nat P Q). Qed.
Lemma lem5375217 (n : nat) (m : nat) : (term160 n m) = (term161 n m).
Proof. exact (@lem5375216 (term79 m n) (Peano.lt n m)). Qed.
Lemma lem5375218 (m : nat) (x : nat) (n : nat) : (term162 m n x) = (term13 m x n).
Proof. exact (eq_refl (term162 m n x)). Qed.
Lemma lem5375219 (m : nat) (n : nat) : (term163 m n) = (term79 m n).
Proof. exact (fun_ext (fun x : nat => @lem5375218 m x n)). Qed.
Lemma lem5375220 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375221 (m : nat) (n : nat) : (term164 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem5375220) (@lem5375219 m n)). Qed.
Lemma lem5375222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5375223 (m : nat) (n : nat) : (term165 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem5375222) (@lem5375221 m n)). Qed.
Lemma lem5375224 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem5375225 (n : nat) (m : nat) : (term160 n m) = (term87 n m).
Proof. exact (MK_COMB (@lem5375223 m n) (@lem5375224 n m)). Qed.
Lemma lem5375226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5375227 (n : nat) (m : nat) : (term166 n m) = (term167 n m).
Proof. exact (MK_COMB (@lem5375226) (@lem5375225 n m)). Qed.
Lemma lem5375228 (m : nat) (x : nat) (n : nat) : (term162 m n x) = (term13 m x n).
Proof. exact (eq_refl (term162 m n x)). Qed.
Lemma lem5375229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5375230 (m : nat) (x : nat) (n : nat) : (term168 m n x) = (term169 m x n).
Proof. exact (MK_COMB (@lem5375229) (@lem5375228 m x n)). Qed.
Lemma lem5375231 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem5375232 (x : nat) (n : nat) (m : nat) : (term170 x n m) = (term171 x n m).
Proof. exact (MK_COMB (@lem5375230 m x n) (@lem5375231 n m)). Qed.
Lemma lem5375233 (n : nat) (m : nat) : (term172 n m) = (term173 n m).
Proof. exact (fun_ext (fun x : nat => @lem5375232 x n m)). Qed.
Lemma lem5375234 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375235 (n : nat) (m : nat) : (term161 n m) = (term174 n m).
Proof. exact (MK_COMB (@lem5375234) (@lem5375233 n m)). Qed.
Lemma lem5375236 (n : nat) (m : nat) : ((term160 n m) = (term161 n m)) = ((term87 n m) = (term174 n m)).
Proof. exact (MK_COMB (@lem5375227 n m) (@lem5375235 n m)). Qed.
Lemma lem5375237 (n : nat) (m : nat) : (term87 n m) = (term174 n m).
Proof. exact (EQ_MP (@lem5375236 n m) (@lem5375217 n m)). Qed.
Lemma lem5375238 (m : nat) : (term117 m) = (term175 m).
Proof. exact (fun_ext (fun n : nat => @lem5375237 n m)). Qed.
Lemma lem5375239 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375240 (m : nat) : (term132 m) = (term176 m).
Proof. exact (MK_COMB (@lem5375239) (@lem5375238 m)). Qed.
Lemma lem5375241 : term139 = term177.
Proof. exact (fun_ext (fun m : nat => @lem5375240 m)). Qed.
Lemma lem5375242 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375243 : term154 = term178.
Proof. exact (MK_COMB (@lem5375242) (@lem5375241)). Qed.
Lemma lem5375244 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem5375245 : term155 = term179.
Proof. exact (MK_COMB (@lem5375244) (@lem5375243)). Qed.
Lemma lem5375247 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term111 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5375248 (P : nat -> Prop) (Q : nat -> Prop) : (term113 P Q) = (term112 P Q).
Proof. exact (@lem5375247 nat P Q). Qed.
Lemma lem5375249 : term180 = term181.
Proof. exact (@lem5375248 term138 term177). Qed.
Lemma lem5375250 (m : nat) : (term140 m) = (term127 m).
Proof. exact (eq_refl (term140 m)). Qed.
Lemma lem5375251 : term147 = term138.
Proof. exact (fun_ext (fun m : nat => @lem5375250 m)). Qed.
Lemma lem5375252 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375253 : term148 = term149.
Proof. exact (MK_COMB (@lem5375252) (@lem5375251)). Qed.
Lemma lem5375254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5375255 : term150 = term151.
Proof. exact (MK_COMB (@lem5375254) (@lem5375253)). Qed.
Lemma lem5375256 (m : nat) : (term182 m) = (term176 m).
Proof. exact (eq_refl (term182 m)). Qed.
Lemma lem5375257 : term183 = term177.
Proof. exact (fun_ext (fun m : nat => @lem5375256 m)). Qed.
Lemma lem5375258 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375259 : term184 = term178.
Proof. exact (MK_COMB (@lem5375258) (@lem5375257)). Qed.
Lemma lem5375260 : term180 = term179.
Proof. exact (MK_COMB (@lem5375255) (@lem5375259)). Qed.
Lemma lem5375261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5375262 : term185 = term186.
Proof. exact (MK_COMB (@lem5375261) (@lem5375260)). Qed.
Lemma lem5375263 (m : nat) : (term140 m) = (term127 m).
Proof. exact (eq_refl (term140 m)). Qed.
Lemma lem5375264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5375265 (m : nat) : (term141 m) = (term129 m).
Proof. exact (MK_COMB (@lem5375264) (@lem5375263 m)). Qed.
Lemma lem5375266 (m : nat) : (term182 m) = (term176 m).
Proof. exact (eq_refl (term182 m)). Qed.
Lemma lem5375267 (m : nat) : (term187 m) = (term188 m).
Proof. exact (MK_COMB (@lem5375265 m) (@lem5375266 m)). Qed.
Lemma lem5375268 : term189 = term190.
Proof. exact (fun_ext (fun m : nat => @lem5375267 m)). Qed.
Lemma lem5375269 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375270 : term181 = term191.
Proof. exact (MK_COMB (@lem5375269) (@lem5375268)). Qed.
Lemma lem5375271 : (term180 = term181) = (term179 = term191).
Proof. exact (MK_COMB (@lem5375262) (@lem5375270)). Qed.
Lemma lem5375272 : term179 = term191.
Proof. exact (EQ_MP (@lem5375271) (@lem5375249)). Qed.
Lemma lem5375274 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term111 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5375275 (P : nat -> Prop) (Q : nat -> Prop) : (term113 P Q) = (term112 P Q).
Proof. exact (@lem5375274 nat P Q). Qed.
Lemma lem5375276 (m : nat) : (term192 m) = (term193 m).
Proof. exact (@lem5375275 (term116 m) (term175 m)). Qed.
Lemma lem5375277 (n : nat) (m : nat) : (term118 m n) = (term91 n m).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem5375278 (m : nat) : (term125 m) = (term116 m).
Proof. exact (fun_ext (fun n : nat => @lem5375277 n m)). Qed.
Lemma lem5375279 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375280 (m : nat) : (term126 m) = (term127 m).
Proof. exact (MK_COMB (@lem5375279) (@lem5375278 m)). Qed.
Lemma lem5375281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5375282 (m : nat) : (term128 m) = (term129 m).
Proof. exact (MK_COMB (@lem5375281) (@lem5375280 m)). Qed.
Lemma lem5375283 (n : nat) (m : nat) : (term194 m n) = (term174 n m).
Proof. exact (eq_refl (term194 m n)). Qed.
Lemma lem5375284 (m : nat) : (term195 m) = (term175 m).
Proof. exact (fun_ext (fun n : nat => @lem5375283 n m)). Qed.
Lemma lem5375285 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375286 (m : nat) : (term196 m) = (term176 m).
Proof. exact (MK_COMB (@lem5375285) (@lem5375284 m)). Qed.
Lemma lem5375287 (m : nat) : (term192 m) = (term188 m).
Proof. exact (MK_COMB (@lem5375282 m) (@lem5375286 m)). Qed.
Lemma lem5375288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5375289 (m : nat) : (term197 m) = (term198 m).
Proof. exact (MK_COMB (@lem5375288) (@lem5375287 m)). Qed.
Lemma lem5375290 (n : nat) (m : nat) : (term118 m n) = (term91 n m).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem5375291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5375292 (n : nat) (m : nat) : (term119 m n) = (term93 n m).
Proof. exact (MK_COMB (@lem5375291) (@lem5375290 n m)). Qed.
Lemma lem5375293 (n : nat) (m : nat) : (term194 m n) = (term174 n m).
Proof. exact (eq_refl (term194 m n)). Qed.
Lemma lem5375294 (n : nat) (m : nat) : (term199 m n) = (term200 n m).
Proof. exact (MK_COMB (@lem5375292 n m) (@lem5375293 n m)). Qed.
Lemma lem5375295 (m : nat) : (term201 m) = (term202 m).
Proof. exact (fun_ext (fun n : nat => @lem5375294 n m)). Qed.
Lemma lem5375296 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375297 (m : nat) : (term193 m) = (term203 m).
Proof. exact (MK_COMB (@lem5375296) (@lem5375295 m)). Qed.
Lemma lem5375298 (m : nat) : ((term192 m) = (term193 m)) = ((term188 m) = (term203 m)).
Proof. exact (MK_COMB (@lem5375289 m) (@lem5375297 m)). Qed.
Lemma lem5375299 (m : nat) : (term188 m) = (term203 m).
Proof. exact (EQ_MP (@lem5375298 m) (@lem5375276 m)). Qed.
Lemma lem5375301 {A : Type'} (P : Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5375302 (P : Prop) (Q : nat -> Prop) : (term206 P Q) = (term207 P Q).
Proof. exact (@lem5375301 nat P Q). Qed.
Lemma lem5375303 (n : nat) (m : nat) : (term208 n m) = (term209 n m).
Proof. exact (@lem5375302 (term91 n m) (term173 n m)). Qed.
Lemma lem5375304 (x : nat) (n : nat) (m : nat) : (term210 n m x) = (term171 x n m).
Proof. exact (eq_refl (term210 n m x)). Qed.
Lemma lem5375305 (n : nat) (m : nat) : (term211 n m) = (term173 n m).
Proof. exact (fun_ext (fun x : nat => @lem5375304 x n m)). Qed.
Lemma lem5375306 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375307 (n : nat) (m : nat) : (term212 n m) = (term174 n m).
Proof. exact (MK_COMB (@lem5375306) (@lem5375305 n m)). Qed.
Lemma lem5375308 (n : nat) (m : nat) : (term93 n m) = (term93 n m).
Proof. exact (eq_refl (term93 n m)). Qed.
Lemma lem5375309 (n : nat) (m : nat) : (term208 n m) = (term200 n m).
Proof. exact (MK_COMB (@lem5375308 n m) (@lem5375307 n m)). Qed.
Lemma lem5375310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5375311 (n : nat) (m : nat) : (term213 n m) = (term214 n m).
Proof. exact (MK_COMB (@lem5375310) (@lem5375309 n m)). Qed.
Lemma lem5375312 (x : nat) (n : nat) (m : nat) : (term210 n m x) = (term171 x n m).
Proof. exact (eq_refl (term210 n m x)). Qed.
Lemma lem5375313 (n : nat) (m : nat) : (term93 n m) = (term93 n m).
Proof. exact (eq_refl (term93 n m)). Qed.
Lemma lem5375314 (x : nat) (n : nat) (m : nat) : (term215 n m x) = (term216 x n m).
Proof. exact (MK_COMB (@lem5375313 n m) (@lem5375312 x n m)). Qed.
Lemma lem5375315 (n : nat) (m : nat) : (term217 n m) = (term218 n m).
Proof. exact (fun_ext (fun x : nat => @lem5375314 x n m)). Qed.
Lemma lem5375316 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375317 (n : nat) (m : nat) : (term209 n m) = (term219 n m).
Proof. exact (MK_COMB (@lem5375316) (@lem5375315 n m)). Qed.
Lemma lem5375318 (n : nat) (m : nat) : ((term208 n m) = (term209 n m)) = ((term200 n m) = (term219 n m)).
Proof. exact (MK_COMB (@lem5375311 n m) (@lem5375317 n m)). Qed.
Lemma lem5375319 (n : nat) (m : nat) : (term200 n m) = (term219 n m).
Proof. exact (EQ_MP (@lem5375318 n m) (@lem5375303 n m)). Qed.
Lemma lem5375320 (m : nat) : (term202 m) = (term220 m).
Proof. exact (fun_ext (fun n : nat => @lem5375319 n m)). Qed.
Lemma lem5375321 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375322 (m : nat) : (term203 m) = (term221 m).
Proof. exact (MK_COMB (@lem5375321) (@lem5375320 m)). Qed.
Lemma lem5375323 (m : nat) : (term188 m) = (term221 m).
Proof. exact (TRANS (@lem5375299 m) (@lem5375322 m)). Qed.
Lemma lem5375324 : term190 = term222.
Proof. exact (fun_ext (fun m : nat => @lem5375323 m)). Qed.
Lemma lem5375325 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5375326 : term191 = term223.
Proof. exact (MK_COMB (@lem5375325) (@lem5375324)). Qed.
Lemma lem5375327 : term179 = term223.
Proof. exact (TRANS (@lem5375272) (@lem5375326)). Qed.
Lemma lem5375328 : term155 = term223.
Proof. exact (TRANS (@lem5375245) (@lem5375327)). Qed.
Lemma lem5375329 : term109 = term223.
Proof. exact (TRANS (@lem5375213) (@lem5375328)). Qed.
Lemma lem5375330 : term41 = term223.
Proof. exact (TRANS (@lem5374759) (@lem5375329)). Qed.
Lemma lem5375331 (h1 : term41) : term223.
Proof. exact (EQ_MP (@lem5375330) (@lem5374696 h1)). Qed.
Lemma lem5375332 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5375333 : term68 = term68.
Proof. exact (fun_ext (fun n : nat => @lem5375332 n)). Qed.
Lemma lem5375334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375343 : term69 = term69.
Proof. exact (MK_COMB (@lem5375334) (@lem5375333)). Qed.
Lemma lem5375344 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem5375343) (@lem5374697 h1)). Qed.
Lemma lem5375351 (m : nat) (n : nat) (p : nat) : (term25 m n p) = (term70 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem5375352 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem5375353 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5375354 (m : nat) (n : nat) (p : nat) : (term224 m n p) = (term225 m n p).
Proof. exact (MK_COMB (@lem5375353) (@lem5375351 m n p)). Qed.
Lemma lem5375355 (n : nat) (m : nat) (p : nat) : (term226 n m p) = (term227 n m p).
Proof. exact (MK_COMB (@lem5375354 m n p) (@lem5375352 m p)). Qed.
Lemma lem5375356 (n : nat) (m : nat) (p : nat) : (term61 n m p) = (term226 n m p).
Proof. exact (@lem17265 (term13 m n p) (Peano.le m p)). Qed.
Lemma lem5375357 (n : nat) (m : nat) (p : nat) : (term61 n m p) = (term227 n m p).
Proof. exact (TRANS (@lem5375356 n m p) (@lem5375355 n m p)). Qed.
Lemma lem5375358 (n : nat) (m : nat) : (term62 n m) = (term228 n m).
Proof. exact (fun_ext (fun p : nat => @lem5375357 n m p)). Qed.
Lemma lem5375359 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375360 (n : nat) (m : nat) : (term63 n m) = (term229 n m).
Proof. exact (MK_COMB (@lem5375359) (@lem5375358 n m)). Qed.
Lemma lem5375361 (m : nat) : (term64 m) = (term230 m).
Proof. exact (fun_ext (fun n : nat => @lem5375360 n m)). Qed.
Lemma lem5375362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375363 (m : nat) : (term65 m) = (term231 m).
Proof. exact (MK_COMB (@lem5375362) (@lem5375361 m)). Qed.
Lemma lem5375364 : term66 = term232.
Proof. exact (fun_ext (fun m : nat => @lem5375363 m)). Qed.
Lemma lem5375365 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375426 : term67 = term233.
Proof. exact (MK_COMB (@lem5375365) (@lem5375364)). Qed.
Lemma lem5375427 (h1 : term67) : term233.
Proof. exact (EQ_MP (@lem5375426) (@lem5374698 h1)). Qed.
Lemma lem5375431 (m : nat) (n : nat) : (term234 m n) = (Peano.le m n).
Proof. exact (@lem16933 (Peano.le m n)). Qed.
Lemma lem5375433 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem5375434 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5375435 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (MK_COMB (@lem5375434) (@lem5375431 m n)). Qed.
Lemma lem5375436 (n : nat) (m : nat) : (term237 n m) = (term238 n m).
Proof. exact (MK_COMB (@lem5375435 m n) (@lem5375433 n m)). Qed.
Lemma lem5375441 (n : nat) (m : nat) : (term239 n m) = (term239 n m).
Proof. exact (eq_refl (term239 n m)). Qed.
Lemma lem5375442 (n : nat) (m : nat) : (term240 n m) = (term241 n m).
Proof. exact (MK_COMB (@lem5375441 n m) (@lem5375436 n m)). Qed.
Lemma lem5375443 (n : nat) (m : nat) : ((term57 m n) = (Peano.lt n m)) = (term240 n m).
Proof. exact (@lem17784 (term57 m n) (Peano.lt n m)). Qed.
Lemma lem5375444 (n : nat) (m : nat) : ((term57 m n) = (Peano.lt n m)) = (term241 n m).
Proof. exact (TRANS (@lem5375443 n m) (@lem5375442 n m)). Qed.
Lemma lem5375445 (m : nat) : (term58 m) = (term242 m).
Proof. exact (fun_ext (fun n : nat => @lem5375444 n m)). Qed.
Lemma lem5375446 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375447 (m : nat) : (term59 m) = (term243 m).
Proof. exact (MK_COMB (@lem5375446) (@lem5375445 m)). Qed.
Lemma lem5375448 : term60 = term244.
Proof. exact (fun_ext (fun m : nat => @lem5375447 m)). Qed.
Lemma lem5375449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375450 : term48 = term245.
Proof. exact (MK_COMB (@lem5375449) (@lem5375448)). Qed.
Lemma lem5375456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5375457 (P : nat -> Prop) (Q : nat -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5375456 nat P Q). Qed.
Lemma lem5375458 (m : nat) : (term250 m) = (term251 m).
Proof. exact (@lem5375457 (term252 m) (term253 m)). Qed.
Lemma lem5375459 (n : nat) (m : nat) : (term254 m n) = (term255 n m).
Proof. exact (eq_refl (term254 m n)). Qed.
Lemma lem5375460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5375461 (n : nat) (m : nat) : (term256 m n) = (term239 n m).
Proof. exact (MK_COMB (@lem5375460) (@lem5375459 n m)). Qed.
Lemma lem5375462 (n : nat) (m : nat) : (term257 m n) = (term238 n m).
Proof. exact (eq_refl (term257 m n)). Qed.
Lemma lem5375463 (n : nat) (m : nat) : (term258 m n) = (term241 n m).
Proof. exact (MK_COMB (@lem5375461 n m) (@lem5375462 n m)). Qed.
Lemma lem5375464 (m : nat) : (term259 m) = (term242 m).
Proof. exact (fun_ext (fun n : nat => @lem5375463 n m)). Qed.
Lemma lem5375465 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375466 (m : nat) : (term250 m) = (term243 m).
Proof. exact (MK_COMB (@lem5375465) (@lem5375464 m)). Qed.
Lemma lem5375467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5375468 (m : nat) : (term260 m) = (term261 m).
Proof. exact (MK_COMB (@lem5375467) (@lem5375466 m)). Qed.
Lemma lem5375469 (n : nat) (m : nat) : (term254 m n) = (term255 n m).
Proof. exact (eq_refl (term254 m n)). Qed.
Lemma lem5375470 (m : nat) : (term262 m) = (term252 m).
Proof. exact (fun_ext (fun n : nat => @lem5375469 n m)). Qed.
Lemma lem5375471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375472 (m : nat) : (term263 m) = (term264 m).
Proof. exact (MK_COMB (@lem5375471) (@lem5375470 m)). Qed.
Lemma lem5375473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5375474 (m : nat) : (term265 m) = (term266 m).
Proof. exact (MK_COMB (@lem5375473) (@lem5375472 m)). Qed.
Lemma lem5375475 (n : nat) (m : nat) : (term257 m n) = (term238 n m).
Proof. exact (eq_refl (term257 m n)). Qed.
Lemma lem5375476 (m : nat) : (term267 m) = (term253 m).
Proof. exact (fun_ext (fun n : nat => @lem5375475 n m)). Qed.
Lemma lem5375477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375478 (m : nat) : (term268 m) = (term269 m).
Proof. exact (MK_COMB (@lem5375477) (@lem5375476 m)). Qed.
Lemma lem5375479 (m : nat) : (term251 m) = (term270 m).
Proof. exact (MK_COMB (@lem5375474 m) (@lem5375478 m)). Qed.
Lemma lem5375480 (m : nat) : ((term250 m) = (term251 m)) = ((term243 m) = (term270 m)).
Proof. exact (MK_COMB (@lem5375468 m) (@lem5375479 m)). Qed.
Lemma lem5375481 (m : nat) : (term243 m) = (term270 m).
Proof. exact (EQ_MP (@lem5375480 m) (@lem5375458 m)). Qed.
Lemma lem5375578 : term244 = term271.
Proof. exact (fun_ext (fun m : nat => @lem5375481 m)). Qed.
Lemma lem5375579 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375580 : term245 = term272.
Proof. exact (MK_COMB (@lem5375579) (@lem5375578)). Qed.
Lemma lem5375582 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5375583 (P : nat -> Prop) (Q : nat -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5375582 nat P Q). Qed.
Lemma lem5375584 : term273 = term274.
Proof. exact (@lem5375583 term275 term276). Qed.
Lemma lem5375585 (m : nat) : (term277 m) = (term264 m).
Proof. exact (eq_refl (term277 m)). Qed.
Lemma lem5375586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5375587 (m : nat) : (term278 m) = (term266 m).
Proof. exact (MK_COMB (@lem5375586) (@lem5375585 m)). Qed.
Lemma lem5375588 (m : nat) : (term279 m) = (term269 m).
Proof. exact (eq_refl (term279 m)). Qed.
Lemma lem5375589 (m : nat) : (term280 m) = (term270 m).
Proof. exact (MK_COMB (@lem5375587 m) (@lem5375588 m)). Qed.
Lemma lem5375590 : term281 = term271.
Proof. exact (fun_ext (fun m : nat => @lem5375589 m)). Qed.
Lemma lem5375591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375592 : term273 = term272.
Proof. exact (MK_COMB (@lem5375591) (@lem5375590)). Qed.
Lemma lem5375593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5375594 : term282 = term283.
Proof. exact (MK_COMB (@lem5375593) (@lem5375592)). Qed.
Lemma lem5375595 (m : nat) : (term277 m) = (term264 m).
Proof. exact (eq_refl (term277 m)). Qed.
Lemma lem5375596 : term284 = term275.
Proof. exact (fun_ext (fun m : nat => @lem5375595 m)). Qed.
Lemma lem5375597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375598 : term285 = term286.
Proof. exact (MK_COMB (@lem5375597) (@lem5375596)). Qed.
Lemma lem5375599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5375600 : term287 = term288.
Proof. exact (MK_COMB (@lem5375599) (@lem5375598)). Qed.
Lemma lem5375601 (m : nat) : (term279 m) = (term269 m).
Proof. exact (eq_refl (term279 m)). Qed.
Lemma lem5375602 : term289 = term276.
Proof. exact (fun_ext (fun m : nat => @lem5375601 m)). Qed.
Lemma lem5375603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375604 : term290 = term291.
Proof. exact (MK_COMB (@lem5375603) (@lem5375602)). Qed.
Lemma lem5375605 : term274 = term292.
Proof. exact (MK_COMB (@lem5375600) (@lem5375604)). Qed.
Lemma lem5375606 : (term273 = term274) = (term272 = term292).
Proof. exact (MK_COMB (@lem5375594) (@lem5375605)). Qed.
Lemma lem5375607 : term272 = term292.
Proof. exact (EQ_MP (@lem5375606) (@lem5375584)). Qed.
Lemma lem5375714 : term245 = term292.
Proof. exact (TRANS (@lem5375580) (@lem5375607)). Qed.
Lemma lem5375715 : term48 = term292.
Proof. exact (TRANS (@lem5375450) (@lem5375714)). Qed.
Lemma lem5375716 (h1 : term48) : term292.
Proof. exact (EQ_MP (@lem5375715) (@lem5374699 h1)). Qed.
Lemma lem5375717 (m : nat) (h1 : term221 m) : term221 m.
Proof. exact (h1). Qed.
Lemma lem5375718 (n : nat) (m : nat) (h1 : term219 n m) : term219 n m.
Proof. exact (h1). Qed.
Lemma lem5375719 (x : nat) (n : nat) (m : nat) (h1 : term216 x n m) : term216 x n m.
Proof. exact (h1). Qed.
Lemma lem5375724 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5375725 : term68 = term68.
Proof. exact (fun_ext (fun n : nat => @lem5375724 n)). Qed.
Lemma lem5375726 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375727 : term69 = term69.
Proof. exact (MK_COMB (@lem5375726) (@lem5375725)). Qed.
Lemma lem5375728 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem5375727) (@lem5375344 h1)). Qed.
Lemma lem5375753 (n : nat) (m : nat) (p : nat) : (term227 n m p) = (term227 n m p).
Proof. exact (eq_refl (term227 n m p)). Qed.
Lemma lem5375754 (n : nat) (m : nat) : (term228 n m) = (term228 n m).
Proof. exact (fun_ext (fun p : nat => @lem5375753 n m p)). Qed.
Lemma lem5375755 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375756 (n : nat) (m : nat) : (term229 n m) = (term229 n m).
Proof. exact (MK_COMB (@lem5375755) (@lem5375754 n m)). Qed.
Lemma lem5375757 (m : nat) : (term230 m) = (term230 m).
Proof. exact (fun_ext (fun n : nat => @lem5375756 n m)). Qed.
Lemma lem5375758 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375759 (m : nat) : (term231 m) = (term231 m).
Proof. exact (MK_COMB (@lem5375758) (@lem5375757 m)). Qed.
Lemma lem5375760 : term232 = term232.
Proof. exact (fun_ext (fun m : nat => @lem5375759 m)). Qed.
Lemma lem5375761 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375762 : term233 = term233.
Proof. exact (MK_COMB (@lem5375761) (@lem5375760)). Qed.
Lemma lem5375763 (h1 : term67) : term233.
Proof. exact (EQ_MP (@lem5375762) (@lem5375427 h1)). Qed.
Lemma lem5375776 (n : nat) (m : nat) : (term238 n m) = (term238 n m).
Proof. exact (eq_refl (term238 n m)). Qed.
Lemma lem5375777 (m : nat) : (term253 m) = (term253 m).
Proof. exact (fun_ext (fun n : nat => @lem5375776 n m)). Qed.
Lemma lem5375778 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375779 (m : nat) : (term269 m) = (term269 m).
Proof. exact (MK_COMB (@lem5375778) (@lem5375777 m)). Qed.
Lemma lem5375780 : term276 = term276.
Proof. exact (fun_ext (fun m : nat => @lem5375779 m)). Qed.
Lemma lem5375781 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375782 : term291 = term291.
Proof. exact (MK_COMB (@lem5375781) (@lem5375780)). Qed.
Lemma lem5375799 (n : nat) (m : nat) : (term255 n m) = (term255 n m).
Proof. exact (eq_refl (term255 n m)). Qed.
Lemma lem5375800 (m : nat) : (term252 m) = (term252 m).
Proof. exact (fun_ext (fun n : nat => @lem5375799 n m)). Qed.
Lemma lem5375801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375802 (m : nat) : (term264 m) = (term264 m).
Proof. exact (MK_COMB (@lem5375801) (@lem5375800 m)). Qed.
Lemma lem5375803 : term275 = term275.
Proof. exact (fun_ext (fun m : nat => @lem5375802 m)). Qed.
Lemma lem5375804 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375805 : term286 = term286.
Proof. exact (MK_COMB (@lem5375804) (@lem5375803)). Qed.
Lemma lem5375806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5375807 : term288 = term288.
Proof. exact (MK_COMB (@lem5375806) (@lem5375805)). Qed.
Lemma lem5375808 : term292 = term292.
Proof. exact (MK_COMB (@lem5375807) (@lem5375782)). Qed.
Lemma lem5375809 (h1 : term48) : term292.
Proof. exact (EQ_MP (@lem5375808) (@lem5375716 h1)). Qed.
Lemma lem5375830 (x : nat) (n : nat) (m : nat) : (term171 x n m) = (term171 x n m).
Proof. exact (eq_refl (term171 x n m)). Qed.
Lemma lem5375837 (n : nat) (m : nat) : (term83 n m) = (term83 n m).
Proof. exact (eq_refl (term83 n m)). Qed.
Lemma lem5375854 (m : nat) (x : nat) (n : nat) : (term70 m x n) = (term70 m x n).
Proof. exact (eq_refl (term70 m x n)). Qed.
Lemma lem5375855 (m : nat) (n : nat) : (term81 m n) = (term81 m n).
Proof. exact (fun_ext (fun x : nat => @lem5375854 m x n)). Qed.
Lemma lem5375856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375857 (m : nat) (n : nat) : (term82 m n) = (term82 m n).
Proof. exact (MK_COMB (@lem5375856) (@lem5375855 m n)). Qed.
Lemma lem5375858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5375859 (m : nat) (n : nat) : (term89 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem5375858) (@lem5375857 m n)). Qed.
Lemma lem5375860 (n : nat) (m : nat) : (term91 n m) = (term91 n m).
Proof. exact (MK_COMB (@lem5375859 m n) (@lem5375837 n m)). Qed.
Lemma lem5375861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5375862 (n : nat) (m : nat) : (term93 n m) = (term93 n m).
Proof. exact (MK_COMB (@lem5375861) (@lem5375860 n m)). Qed.
Lemma lem5375863 (x : nat) (n : nat) (m : nat) : (term216 x n m) = (term216 x n m).
Proof. exact (MK_COMB (@lem5375862 n m) (@lem5375830 x n m)). Qed.
Lemma lem5375864 (x : nat) (n : nat) (m : nat) (h1 : term216 x n m) : term216 x n m.
Proof. exact (EQ_MP (@lem5375863 x n m) (@lem5375719 x n m h1)). Qed.
Lemma lem5375865 (h1 : term48) : term291.
Proof. exact (proj2 (@lem5375809 h1)). Qed.
Lemma lem5375866 (h1 : term48) : term286.
Proof. exact (proj1 (@lem5375809 h1)). Qed.
Lemma lem5375867 (n : nat) (m : nat) (h1 : term91 n m) : term91 n m.
Proof. exact (h1). Qed.
Lemma lem5375868 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : term171 x n m.
Proof. exact (h1). Qed.
Lemma lem5375870 (n : nat) (m : nat) (h1 : term91 n m) : term82 m n.
Proof. exact (proj1 (@lem5375867 n m h1)). Qed.
Lemma lem5375872 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : term13 m x n.
Proof. exact (proj1 (@lem5375868 x n m h1)). Qed.
Lemma lem5375876 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5375877 : term68 = term68.
Proof. exact (fun_ext (fun n : nat => @lem5375876 n)). Qed.
Lemma lem5375878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375880 : term69 = term69.
Proof. exact (MK_COMB (@lem5375878) (@lem5375877)). Qed.
Lemma lem5375881 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem5375880) (@lem5375728 h1)). Qed.
Lemma lem5375930 (n : nat) (m : nat) : (term238 n m) = (term238 n m).
Proof. exact (eq_refl (term238 n m)). Qed.
Lemma lem5375931 (m : nat) : (term253 m) = (term253 m).
Proof. exact (fun_ext (fun n : nat => @lem5375930 n m)). Qed.
Lemma lem5375932 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375933 (m : nat) : (term269 m) = (term269 m).
Proof. exact (MK_COMB (@lem5375932) (@lem5375931 m)). Qed.
Lemma lem5375934 : term276 = term276.
Proof. exact (fun_ext (fun m : nat => @lem5375933 m)). Qed.
Lemma lem5375935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375937 : term291 = term291.
Proof. exact (MK_COMB (@lem5375935) (@lem5375934)). Qed.
Lemma lem5375938 (h1 : term48) : term291.
Proof. exact (EQ_MP (@lem5375937) (@lem5375865 h1)). Qed.
Lemma lem5375946 (m : nat) (x : nat) (n : nat) : (term70 m x n) = (term70 m x n).
Proof. exact (eq_refl (term70 m x n)). Qed.
Lemma lem5375947 (m : nat) (n : nat) : (term81 m n) = (term81 m n).
Proof. exact (fun_ext (fun x : nat => @lem5375946 m x n)). Qed.
Lemma lem5375948 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375950 (m : nat) (n : nat) : (term82 m n) = (term82 m n).
Proof. exact (MK_COMB (@lem5375948) (@lem5375947 m n)). Qed.
Lemma lem5375951 (n : nat) (m : nat) (h1 : term91 n m) : term82 m n.
Proof. exact (EQ_MP (@lem5375950 m n) (@lem5375870 n m h1)). Qed.
Lemma lem5375976 (n : nat) (m : nat) (p : nat) : (term227 n m p) = (term227 n m p).
Proof. exact (eq_refl (term227 n m p)). Qed.
Lemma lem5375977 (n : nat) (m : nat) : (term228 n m) = (term228 n m).
Proof. exact (fun_ext (fun p : nat => @lem5375976 n m p)). Qed.
Lemma lem5375978 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375979 (n : nat) (m : nat) : (term229 n m) = (term229 n m).
Proof. exact (MK_COMB (@lem5375978) (@lem5375977 n m)). Qed.
Lemma lem5375980 (m : nat) : (term230 m) = (term230 m).
Proof. exact (fun_ext (fun n : nat => @lem5375979 n m)). Qed.
Lemma lem5375981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375982 (m : nat) : (term231 m) = (term231 m).
Proof. exact (MK_COMB (@lem5375981) (@lem5375980 m)). Qed.
Lemma lem5375983 : term232 = term232.
Proof. exact (fun_ext (fun m : nat => @lem5375982 m)). Qed.
Lemma lem5375984 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375986 : term233 = term233.
Proof. exact (MK_COMB (@lem5375984) (@lem5375983)). Qed.
Lemma lem5375987 (h1 : term67) : term233.
Proof. exact (EQ_MP (@lem5375986) (@lem5375763 h1)). Qed.
Lemma lem5375995 (n : nat) (m : nat) : (term255 n m) = (term255 n m).
Proof. exact (eq_refl (term255 n m)). Qed.
Lemma lem5375996 (m : nat) : (term252 m) = (term252 m).
Proof. exact (fun_ext (fun n : nat => @lem5375995 n m)). Qed.
Lemma lem5375997 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5375998 (m : nat) : (term264 m) = (term264 m).
Proof. exact (MK_COMB (@lem5375997) (@lem5375996 m)). Qed.
Lemma lem5375999 : term275 = term275.
Proof. exact (fun_ext (fun m : nat => @lem5375998 m)). Qed.
Lemma lem5376000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376002 : term286 = term286.
Proof. exact (MK_COMB (@lem5376000) (@lem5375999)). Qed.
Lemma lem5376003 (h1 : term48) : term286.
Proof. exact (EQ_MP (@lem5376002) (@lem5375866 h1)). Qed.
Lemma lem5376032 (_69744 : nat) (h1 : term69) : term293 _69744.
Proof. exact (@lem5375881 h1 _69744). Qed.
Lemma lem5376033 (_69744 : nat) : (term293 _69744) = (Peano.le _69744 _69744).
Proof. exact (eq_refl (term293 _69744)). Qed.
Lemma lem5376050 (_69750 : nat) (h1 : term48) : term279 _69750.
Proof. exact (@lem5375938 h1 _69750). Qed.
Lemma lem5376051 (_69750 : nat) : (term279 _69750) = (term269 _69750).
Proof. exact (eq_refl (term279 _69750)). Qed.
Lemma lem5376052 (_69750 : nat) (h1 : term48) : term269 _69750.
Proof. exact (EQ_MP (@lem5376051 _69750) (@lem5376050 _69750 h1)). Qed.
Lemma lem5376053 (_69750 : nat) (_69751 : nat) (h1 : term48) : term257 _69750 _69751.
Proof. exact (@lem5376052 _69750 h1 _69751). Qed.
Lemma lem5376054 (_69751 : nat) (_69750 : nat) : (term257 _69750 _69751) = (term238 _69751 _69750).
Proof. exact (eq_refl (term257 _69750 _69751)). Qed.
Lemma lem5376056 (_69752 : nat) (n : nat) (m : nat) (h1 : term91 n m) : term294 m n _69752.
Proof. exact (@lem5375951 n m h1 _69752). Qed.
Lemma lem5376057 (m : nat) (_69752 : nat) (n : nat) : (term294 m n _69752) = (term70 m _69752 n).
Proof. exact (eq_refl (term294 m n _69752)). Qed.
Lemma lem5376062 (_69754 : nat) (h1 : term67) : term295 _69754.
Proof. exact (@lem5375987 h1 _69754). Qed.
Lemma lem5376063 (_69754 : nat) : (term295 _69754) = (term231 _69754).
Proof. exact (eq_refl (term295 _69754)). Qed.
Lemma lem5376064 (_69754 : nat) (h1 : term67) : term231 _69754.
Proof. exact (EQ_MP (@lem5376063 _69754) (@lem5376062 _69754 h1)). Qed.
Lemma lem5376065 (_69754 : nat) (_69755 : nat) (h1 : term67) : term296 _69754 _69755.
Proof. exact (@lem5376064 _69754 h1 _69755). Qed.
Lemma lem5376066 (_69755 : nat) (_69754 : nat) : (term296 _69754 _69755) = (term229 _69755 _69754).
Proof. exact (eq_refl (term296 _69754 _69755)). Qed.
Lemma lem5376067 (_69755 : nat) (_69754 : nat) (h1 : term67) : term229 _69755 _69754.
Proof. exact (EQ_MP (@lem5376066 _69755 _69754) (@lem5376065 _69754 _69755 h1)). Qed.
Lemma lem5376068 (_69755 : nat) (_69754 : nat) (_69756 : nat) (h1 : term67) : term297 _69755 _69754 _69756.
Proof. exact (@lem5376067 _69755 _69754 h1 _69756). Qed.
Lemma lem5376069 (_69755 : nat) (_69754 : nat) (_69756 : nat) : (term297 _69755 _69754 _69756) = (term227 _69755 _69754 _69756).
Proof. exact (eq_refl (term297 _69755 _69754 _69756)). Qed.
Lemma lem5376070 (_69755 : nat) (_69754 : nat) (_69756 : nat) (h1 : term67) : term227 _69755 _69754 _69756.
Proof. exact (EQ_MP (@lem5376069 _69755 _69754 _69756) (@lem5376068 _69755 _69754 _69756 h1)). Qed.
Lemma lem5376071 (_69757 : nat) (h1 : term48) : term277 _69757.
Proof. exact (@lem5376003 h1 _69757). Qed.
Lemma lem5376072 (_69757 : nat) : (term277 _69757) = (term264 _69757).
Proof. exact (eq_refl (term277 _69757)). Qed.
Lemma lem5376073 (_69757 : nat) (h1 : term48) : term264 _69757.
Proof. exact (EQ_MP (@lem5376072 _69757) (@lem5376071 _69757 h1)). Qed.
Lemma lem5376074 (_69757 : nat) (_69758 : nat) (h1 : term48) : term254 _69757 _69758.
Proof. exact (@lem5376073 _69757 h1 _69758). Qed.
Lemma lem5376075 (_69758 : nat) (_69757 : nat) : (term254 _69757 _69758) = (term255 _69758 _69757).
Proof. exact (eq_refl (term254 _69757 _69758)). Qed.
Lemma lem5376108 (_69751 : nat) (_69750 : nat) (h1 : term48) : term238 _69751 _69750.
Proof. exact (EQ_MP (@lem5376054 _69751 _69750) (@lem5376053 _69750 _69751 h1)). Qed.
Lemma lem5376114 (_69752 : nat) (n : nat) (m : nat) (h1 : term91 n m) : term70 m _69752 n.
Proof. exact (EQ_MP (@lem5376057 m _69752 n) (@lem5376056 _69752 n m h1)). Qed.
Lemma lem5376116 (n : nat) (m : nat) (h1 : term91 n m) : term83 n m.
Proof. exact (proj2 (@lem5375867 n m h1)). Qed.
Lemma lem5376129 (_69755 : nat) (_69754 : nat) (_69756 : nat) : (term227 _69755 _69754 _69756) = (term298 _69755 _69754 _69756).
Proof. exact (@lem5374376 (term57 _69754 _69755) (term57 _69755 _69756) (Peano.le _69754 _69756)). Qed.
Lemma lem5376130 (_69755 : nat) (_69754 : nat) (_69756 : nat) (h1 : term67) : term298 _69755 _69754 _69756.
Proof. exact (EQ_MP (@lem5376129 _69755 _69754 _69756) (@lem5376070 _69755 _69754 _69756 h1)). Qed.
Lemma lem5376136 (_69758 : nat) (_69757 : nat) (h1 : term48) : term255 _69758 _69757.
Proof. exact (EQ_MP (@lem5376075 _69758 _69757) (@lem5376074 _69757 _69758 h1)). Qed.
Lemma lem5376150 (_69744 : nat) (h1 : term69) : Peano.le _69744 _69744.
Proof. exact (EQ_MP (@lem5376033 _69744) (@lem5376032 _69744 h1)). Qed.
Lemma lem5376151 (m : nat) (h1 : term69) : Peano.le m m.
Proof. exact (@lem5376150 m h1). Qed.
Lemma lem5376152 (m : nat) (h1 : term69) : term299 m.
Proof. exact (fun h0 : term300 m => @lem5376151 m h1). Qed.
Lemma lem5376154 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5376155 (m : nat) : (term299 m) = (Peano.le m m).
Proof. exact (@lem5376154 (Peano.le m m)). Qed.
Lemma lem5376156 (m : nat) (h1 : term69) : Peano.le m m.
Proof. exact (EQ_MP (@lem5376155 m) (@lem5376152 m h1)). Qed.
Lemma lem5376162 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5376163 (n : nat) (m : nat) (_69752 : nat) : (term70 m _69752 n) = (term302 n m _69752).
Proof. exact (@lem5376162 (term57 _69752 n) (term57 m _69752)). Qed.
Lemma lem5376169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5376170 (n : nat) (m : nat) (_69752 : nat) : (term303 m _69752 n) = (term304 n m _69752).
Proof. exact (MK_COMB (@lem5376169) (@lem5376163 n m _69752)). Qed.
Lemma lem5376176 (n : nat) (m : nat) (_69752 : nat) : (term302 n m _69752) = (term302 n m _69752).
Proof. exact (eq_refl (term302 n m _69752)). Qed.
Lemma lem5376177 (n : nat) (m : nat) (_69752 : nat) : ((term70 m _69752 n) = (term302 n m _69752)) = ((term302 n m _69752) = (term302 n m _69752)).
Proof. exact (MK_COMB (@lem5376170 n m _69752) (@lem5376176 n m _69752)). Qed.
Lemma lem5376179 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5376180 (x : Prop) : (x = x) = True.
Proof. exact (@lem5376179 Prop x). Qed.
Lemma lem5376181 (n : nat) (m : nat) (_69752 : nat) : ((term302 n m _69752) = (term302 n m _69752)) = True.
Proof. exact (@lem5376180 (term302 n m _69752)). Qed.
Lemma lem5376182 (n : nat) (m : nat) (_69752 : nat) : ((term70 m _69752 n) = (term302 n m _69752)) = True.
Proof. exact (TRANS (@lem5376177 n m _69752) (@lem5376181 n m _69752)). Qed.
Lemma lem5376183 (n : nat) (m : nat) (_69752 : nat) : True = ((term70 m _69752 n) = (term302 n m _69752)).
Proof. exact (SYM (@lem5376182 n m _69752)). Qed.
Lemma lem5376184 (n : nat) (m : nat) (_69752 : nat) : (term70 m _69752 n) = (term302 n m _69752).
Proof. exact (EQ_MP (@lem5376183 n m _69752) (@lem0)). Qed.
Lemma lem5376185 (_69752 : nat) (n : nat) (m : nat) (h1 : term91 n m) : term302 n m _69752.
Proof. exact (EQ_MP (@lem5376184 n m _69752) (@lem5376114 _69752 n m h1)). Qed.
Lemma lem5376187 (b : Prop) (a : Prop) : (a \/ b) = (term305 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5376188 (m : nat) (_69752 : nat) (n : nat) : (term302 n m _69752) = (term306 m _69752 n).
Proof. exact (@lem5376187 (term57 m _69752) (term57 _69752 n)). Qed.
Lemma lem5376190 (a : Prop) : (term307 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5376191 (m : nat) (_69752 : nat) : (term234 m _69752) = (Peano.le m _69752).
Proof. exact (@lem5376190 (Peano.le m _69752)). Qed.
Lemma lem5376192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5376193 (m : nat) (_69752 : nat) : (term308 m _69752) = (term309 m _69752).
Proof. exact (MK_COMB (@lem5376192) (@lem5376191 m _69752)). Qed.
Lemma lem5376194 (_69752 : nat) (n : nat) : (term57 _69752 n) = (term57 _69752 n).
Proof. exact (eq_refl (term57 _69752 n)). Qed.
Lemma lem5376195 (m : nat) (_69752 : nat) (n : nat) : (term306 m _69752 n) = (term310 m _69752 n).
Proof. exact (MK_COMB (@lem5376193 m _69752) (@lem5376194 _69752 n)). Qed.
Lemma lem5376196 (m : nat) (_69752 : nat) (n : nat) : (term302 n m _69752) = (term310 m _69752 n).
Proof. exact (TRANS (@lem5376188 m _69752 n) (@lem5376195 m _69752 n)). Qed.
Lemma lem5376199 (_69752 : nat) (n : nat) (m : nat) (h1 : term91 n m) : term310 m _69752 n.
Proof. exact (EQ_MP (@lem5376196 m _69752 n) (@lem5376185 _69752 n m h1)). Qed.
Lemma lem5376200 (n : nat) (m : nat) (h1 : term91 n m) : term311 m n.
Proof. exact (@lem5376199 m n m h1). Qed.
Lemma lem5376203 (n : nat) (m : nat) (h1 : term69) (h2 : term91 n m) : term57 m n.
Proof. exact (@lem5376200 n m h2 (@lem5376156 m h1)). Qed.
Lemma lem5376204 (n : nat) (m : nat) (h1 : term69) (h2 : term91 n m) : term312 m n.
Proof. exact (fun h0 : Peano.le m n => @lem5376203 n m h1 h2). Qed.
Lemma lem5376206 (p : Prop) : (term313 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5376207 (m : nat) (n : nat) : (term312 m n) = (term57 m n).
Proof. exact (@lem5376206 (Peano.le m n)). Qed.
Lemma lem5376208 (n : nat) (m : nat) (h1 : term69) (h2 : term91 n m) : term57 m n.
Proof. exact (EQ_MP (@lem5376207 m n) (@lem5376204 n m h1 h2)). Qed.
Lemma lem5376214 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5376215 (_69750 : nat) (_69751 : nat) : (term238 _69751 _69750) = (term314 _69750 _69751).
Proof. exact (@lem5376214 (Peano.lt _69751 _69750) (Peano.le _69750 _69751)). Qed.
Lemma lem5376221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5376222 (_69750 : nat) (_69751 : nat) : (term315 _69751 _69750) = (term316 _69750 _69751).
Proof. exact (MK_COMB (@lem5376221) (@lem5376215 _69750 _69751)). Qed.
Lemma lem5376228 (_69750 : nat) (_69751 : nat) : (term314 _69750 _69751) = (term314 _69750 _69751).
Proof. exact (eq_refl (term314 _69750 _69751)). Qed.
Lemma lem5376229 (_69750 : nat) (_69751 : nat) : ((term238 _69751 _69750) = (term314 _69750 _69751)) = ((term314 _69750 _69751) = (term314 _69750 _69751)).
Proof. exact (MK_COMB (@lem5376222 _69750 _69751) (@lem5376228 _69750 _69751)). Qed.
Lemma lem5376231 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5376232 (x : Prop) : (x = x) = True.
Proof. exact (@lem5376231 Prop x). Qed.
Lemma lem5376233 (_69750 : nat) (_69751 : nat) : ((term314 _69750 _69751) = (term314 _69750 _69751)) = True.
Proof. exact (@lem5376232 (term314 _69750 _69751)). Qed.
Lemma lem5376234 (_69750 : nat) (_69751 : nat) : ((term238 _69751 _69750) = (term314 _69750 _69751)) = True.
Proof. exact (TRANS (@lem5376229 _69750 _69751) (@lem5376233 _69750 _69751)). Qed.
Lemma lem5376235 (_69750 : nat) (_69751 : nat) : True = ((term238 _69751 _69750) = (term314 _69750 _69751)).
Proof. exact (SYM (@lem5376234 _69750 _69751)). Qed.
Lemma lem5376236 (_69750 : nat) (_69751 : nat) : (term238 _69751 _69750) = (term314 _69750 _69751).
Proof. exact (EQ_MP (@lem5376235 _69750 _69751) (@lem0)). Qed.
Lemma lem5376237 (_69750 : nat) (_69751 : nat) (h1 : term48) : term314 _69750 _69751.
Proof. exact (EQ_MP (@lem5376236 _69750 _69751) (@lem5376108 _69751 _69750 h1)). Qed.
Lemma lem5376239 (b : Prop) (a : Prop) : (a \/ b) = (term305 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5376242 (_69751 : nat) (_69750 : nat) : (term314 _69750 _69751) = (term317 _69751 _69750).
Proof. exact (@lem5376239 (Peano.le _69750 _69751) (Peano.lt _69751 _69750)). Qed.
Lemma lem5376245 (_69751 : nat) (_69750 : nat) (h1 : term48) : term317 _69751 _69750.
Proof. exact (EQ_MP (@lem5376242 _69751 _69750) (@lem5376237 _69750 _69751 h1)). Qed.
Lemma lem5376246 (n : nat) (m : nat) (h1 : term48) : term317 n m.
Proof. exact (@lem5376245 n m h1). Qed.
Lemma lem5376249 (n : nat) (m : nat) (h1 : term48) (h2 : term69) (h3 : term91 n m) : Peano.lt n m.
Proof. exact (@lem5376246 n m h1 (@lem5376208 n m h2 h3)). Qed.
Lemma lem5376250 (n : nat) (m : nat) (h1 : term48) (h2 : term69) (h3 : term91 n m) : term318 n m.
Proof. exact (fun h0 : term83 n m => @lem5376249 n m h1 h2 h3). Qed.
Lemma lem5376252 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5376253 (n : nat) (m : nat) : (term318 n m) = (Peano.lt n m).
Proof. exact (@lem5376252 (Peano.lt n m)). Qed.
Lemma lem5376254 (n : nat) (m : nat) (h1 : term48) (h2 : term69) (h3 : term91 n m) : Peano.lt n m.
Proof. exact (EQ_MP (@lem5376253 n m) (@lem5376250 n m h1 h2 h3)). Qed.
Lemma lem5376257 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5376259 (n : nat) (m : nat) : (term83 n m) = (term319 n m).
Proof. exact (@lem5376257 (Peano.lt n m)). Qed.
Lemma lem5376262 (n : nat) (m : nat) (h1 : term91 n m) : term319 n m.
Proof. exact (EQ_MP (@lem5376259 n m) (@lem5376116 n m h1)). Qed.
Lemma lem5376265 (n : nat) (m : nat) (h1 : term48) (h2 : term69) (h3 : term91 n m) : False.
Proof. exact (@lem5376262 n m h3 (@lem5376254 n m h1 h2 h3)). Qed.
Lemma lem5376266 (n : nat) (m : nat) (h1 : term48) (h2 : term69) (h3 : term91 n m) : term320.
Proof. exact (fun h0 : ~ False => @lem5376265 n m h1 h2 h3). Qed.
Lemma lem5376268 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5376269 : term320 = False.
Proof. exact (@lem5376268 False). Qed.
Lemma lem5376270 (n : nat) (m : nat) (h1 : term48) (h2 : term69) (h3 : term91 n m) : False.
Proof. exact (EQ_MP (@lem5376269) (@lem5376266 n m h1 h2 h3)). Qed.
Lemma lem5376272 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : Peano.le m x.
Proof. exact (proj1 (@lem5375872 x n m h1)). Qed.
Lemma lem5376273 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : term321 m x.
Proof. exact (fun h0 : term57 m x => @lem5376272 x n m h1). Qed.
Lemma lem5376275 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5376276 (m : nat) (x : nat) : (term321 m x) = (Peano.le m x).
Proof. exact (@lem5376275 (Peano.le m x)). Qed.
Lemma lem5376277 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : Peano.le m x.
Proof. exact (EQ_MP (@lem5376276 m x) (@lem5376273 x n m h1)). Qed.
Lemma lem5376279 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : Peano.le x n.
Proof. exact (proj2 (@lem5375872 x n m h1)). Qed.
Lemma lem5376280 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : term321 x n.
Proof. exact (fun h0 : term57 x n => @lem5376279 x n m h1). Qed.
Lemma lem5376282 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5376283 (x : nat) (n : nat) : (term321 x n) = (Peano.le x n).
Proof. exact (@lem5376282 (Peano.le x n)). Qed.
Lemma lem5376284 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : Peano.le x n.
Proof. exact (EQ_MP (@lem5376283 x n) (@lem5376280 x n m h1)). Qed.
Lemma lem5376300 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5376301 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term322 _69755 _69754 _69756) = (term323 _69754 _69755 _69756).
Proof. exact (@lem5376300 (Peano.le _69754 _69756) (term57 _69755 _69756)). Qed.
Lemma lem5376307 (_69754 : nat) (_69755 : nat) : (term324 _69754 _69755) = (term324 _69754 _69755).
Proof. exact (eq_refl (term324 _69754 _69755)). Qed.
Lemma lem5376308 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term298 _69755 _69754 _69756) = (term325 _69754 _69755 _69756).
Proof. exact (MK_COMB (@lem5376307 _69754 _69755) (@lem5376301 _69754 _69755 _69756)). Qed.
Lemma lem5376312 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5376313 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term325 _69754 _69755 _69756) = (term326 _69754 _69755 _69756).
Proof. exact (@lem5376312 (Peano.le _69754 _69756) (term57 _69754 _69755) (term57 _69755 _69756)). Qed.
Lemma lem5376329 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term298 _69755 _69754 _69756) = (term326 _69754 _69755 _69756).
Proof. exact (TRANS (@lem5376308 _69754 _69755 _69756) (@lem5376313 _69754 _69755 _69756)). Qed.
Lemma lem5376330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5376331 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term327 _69755 _69754 _69756) = (term328 _69754 _69755 _69756).
Proof. exact (MK_COMB (@lem5376330) (@lem5376329 _69754 _69755 _69756)). Qed.
Lemma lem5376347 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term326 _69754 _69755 _69756) = (term326 _69754 _69755 _69756).
Proof. exact (eq_refl (term326 _69754 _69755 _69756)). Qed.
Lemma lem5376348 (_69754 : nat) (_69755 : nat) (_69756 : nat) : ((term298 _69755 _69754 _69756) = (term326 _69754 _69755 _69756)) = ((term326 _69754 _69755 _69756) = (term326 _69754 _69755 _69756)).
Proof. exact (MK_COMB (@lem5376331 _69754 _69755 _69756) (@lem5376347 _69754 _69755 _69756)). Qed.
Lemma lem5376350 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5376351 (x : Prop) : (x = x) = True.
Proof. exact (@lem5376350 Prop x). Qed.
Lemma lem5376352 (_69754 : nat) (_69755 : nat) (_69756 : nat) : ((term326 _69754 _69755 _69756) = (term326 _69754 _69755 _69756)) = True.
Proof. exact (@lem5376351 (term326 _69754 _69755 _69756)). Qed.
Lemma lem5376353 (_69754 : nat) (_69755 : nat) (_69756 : nat) : ((term298 _69755 _69754 _69756) = (term326 _69754 _69755 _69756)) = True.
Proof. exact (TRANS (@lem5376348 _69754 _69755 _69756) (@lem5376352 _69754 _69755 _69756)). Qed.
Lemma lem5376354 (_69754 : nat) (_69755 : nat) (_69756 : nat) : True = ((term298 _69755 _69754 _69756) = (term326 _69754 _69755 _69756)).
Proof. exact (SYM (@lem5376353 _69754 _69755 _69756)). Qed.
Lemma lem5376355 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term298 _69755 _69754 _69756) = (term326 _69754 _69755 _69756).
Proof. exact (EQ_MP (@lem5376354 _69754 _69755 _69756) (@lem0)). Qed.
Lemma lem5376356 (_69754 : nat) (_69755 : nat) (_69756 : nat) (h1 : term67) : term326 _69754 _69755 _69756.
Proof. exact (EQ_MP (@lem5376355 _69754 _69755 _69756) (@lem5376130 _69755 _69754 _69756 h1)). Qed.
Lemma lem5376358 (b : Prop) (a : Prop) : (a \/ b) = (term305 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5376359 (_69755 : nat) (_69754 : nat) (_69756 : nat) : (term326 _69754 _69755 _69756) = (term329 _69755 _69754 _69756).
Proof. exact (@lem5376358 (term70 _69754 _69755 _69756) (Peano.le _69754 _69756)). Qed.
Lemma lem5376361 (a : Prop) (b : Prop) : (term330 a b) = (term331 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5376362 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term332 _69754 _69755 _69756) = (term333 _69754 _69755 _69756).
Proof. exact (@lem5376361 (term57 _69754 _69755) (term57 _69755 _69756)). Qed.
Lemma lem5376364 (a : Prop) : (term307 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5376365 (_69754 : nat) (_69755 : nat) : (term234 _69754 _69755) = (Peano.le _69754 _69755).
Proof. exact (@lem5376364 (Peano.le _69754 _69755)). Qed.
Lemma lem5376366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5376367 (_69754 : nat) (_69755 : nat) : (term334 _69754 _69755) = (term335 _69754 _69755).
Proof. exact (MK_COMB (@lem5376366) (@lem5376365 _69754 _69755)). Qed.
Lemma lem5376369 (a : Prop) : (term307 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5376370 (_69755 : nat) (_69756 : nat) : (term234 _69755 _69756) = (Peano.le _69755 _69756).
Proof. exact (@lem5376369 (Peano.le _69755 _69756)). Qed.
Lemma lem5376371 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term333 _69754 _69755 _69756) = (term13 _69754 _69755 _69756).
Proof. exact (MK_COMB (@lem5376367 _69754 _69755) (@lem5376370 _69755 _69756)). Qed.
Lemma lem5376372 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term332 _69754 _69755 _69756) = (term13 _69754 _69755 _69756).
Proof. exact (TRANS (@lem5376362 _69754 _69755 _69756) (@lem5376371 _69754 _69755 _69756)). Qed.
Lemma lem5376373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5376374 (_69754 : nat) (_69755 : nat) (_69756 : nat) : (term336 _69754 _69755 _69756) = (term337 _69754 _69755 _69756).
Proof. exact (MK_COMB (@lem5376373) (@lem5376372 _69754 _69755 _69756)). Qed.
Lemma lem5376375 (_69754 : nat) (_69756 : nat) : (Peano.le _69754 _69756) = (Peano.le _69754 _69756).
Proof. exact (eq_refl (Peano.le _69754 _69756)). Qed.
Lemma lem5376376 (_69755 : nat) (_69754 : nat) (_69756 : nat) : (term329 _69755 _69754 _69756) = (term61 _69755 _69754 _69756).
Proof. exact (MK_COMB (@lem5376374 _69754 _69755 _69756) (@lem5376375 _69754 _69756)). Qed.
Lemma lem5376377 (_69755 : nat) (_69754 : nat) (_69756 : nat) : (term326 _69754 _69755 _69756) = (term61 _69755 _69754 _69756).
Proof. exact (TRANS (@lem5376359 _69755 _69754 _69756) (@lem5376376 _69755 _69754 _69756)). Qed.
Lemma lem5376379 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : term13 m x n.
Proof. exact (conj (@lem5376277 x n m h1) (@lem5376284 x n m h1)). Qed.
Lemma lem5376381 (_69755 : nat) (_69754 : nat) (_69756 : nat) (h1 : term67) : term61 _69755 _69754 _69756.
Proof. exact (EQ_MP (@lem5376377 _69755 _69754 _69756) (@lem5376356 _69754 _69755 _69756 h1)). Qed.
Lemma lem5376382 (x : nat) (m : nat) (n : nat) (h1 : term67) : term61 x m n.
Proof. exact (@lem5376381 x m n h1). Qed.
Lemma lem5376385 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term171 x n m) : Peano.le m n.
Proof. exact (@lem5376382 x m n h1 (@lem5376379 x n m h2)). Qed.
Lemma lem5376386 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term171 x n m) : term321 m n.
Proof. exact (fun h0 : term57 m n => @lem5376385 x n m h1 h2). Qed.
Lemma lem5376388 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5376389 (m : nat) (n : nat) : (term321 m n) = (Peano.le m n).
Proof. exact (@lem5376388 (Peano.le m n)). Qed.
Lemma lem5376390 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term171 x n m) : Peano.le m n.
Proof. exact (EQ_MP (@lem5376389 m n) (@lem5376386 x n m h1 h2)). Qed.
Lemma lem5376392 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : Peano.lt n m.
Proof. exact (proj2 (@lem5375868 x n m h1)). Qed.
Lemma lem5376393 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : term318 n m.
Proof. exact (fun h0 : term83 n m => @lem5376392 x n m h1). Qed.
Lemma lem5376395 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5376396 (n : nat) (m : nat) : (term318 n m) = (Peano.lt n m).
Proof. exact (@lem5376395 (Peano.lt n m)). Qed.
Lemma lem5376397 (x : nat) (n : nat) (m : nat) (h1 : term171 x n m) : Peano.lt n m.
Proof. exact (EQ_MP (@lem5376396 n m) (@lem5376393 x n m h1)). Qed.
Lemma lem5376399 (a : Prop) (b : Prop) : (term338 a b) = (term339 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5376400 (_69758 : nat) (_69757 : nat) : (term255 _69758 _69757) = (term340 _69758 _69757).
Proof. exact (@lem5376399 (Peano.le _69757 _69758) (Peano.lt _69758 _69757)). Qed.
Lemma lem5376402 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5376403 (_69758 : nat) (_69757 : nat) : (term340 _69758 _69757) = (term341 _69758 _69757).
Proof. exact (@lem5376402 (term342 _69758 _69757)). Qed.
Lemma lem5376404 (_69758 : nat) (_69757 : nat) : (term255 _69758 _69757) = (term341 _69758 _69757).
Proof. exact (TRANS (@lem5376400 _69758 _69757) (@lem5376403 _69758 _69757)). Qed.
Lemma lem5376406 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term171 x n m) : term342 n m.
Proof. exact (conj (@lem5376390 x n m h1 h2) (@lem5376397 x n m h2)). Qed.
Lemma lem5376408 (_69758 : nat) (_69757 : nat) (h1 : term48) : term341 _69758 _69757.
Proof. exact (EQ_MP (@lem5376404 _69758 _69757) (@lem5376136 _69758 _69757 h1)). Qed.
Lemma lem5376409 (n : nat) (m : nat) (h1 : term48) : term341 n m.
Proof. exact (@lem5376408 n m h1). Qed.
Lemma lem5376412 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term48) (h3 : term171 x n m) : False.
Proof. exact (@lem5376409 n m h2 (@lem5376406 x n m h1 h3)). Qed.
Lemma lem5376413 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term48) (h3 : term171 x n m) : term320.
Proof. exact (fun h0 : ~ False => @lem5376412 x n m h1 h2 h3). Qed.
Lemma lem5376415 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5376416 : term320 = False.
Proof. exact (@lem5376415 False). Qed.
Lemma lem5376417 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term48) (h3 : term171 x n m) : False.
Proof. exact (EQ_MP (@lem5376416) (@lem5376413 x n m h1 h2 h3)). Qed.
Lemma lem5376418 (n : nat) (m : nat) (h1 : term48) (h2 : term69) (h3 : term91 n m) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem5376270 n m h1 h2 h3) (fun h4 : False => @lem5375881 h2)). Qed.
Lemma lem5376419 (n : nat) (m : nat) (h1 : term48) (h2 : term69) (h3 : term91 n m) : False.
Proof. exact (EQ_MP (@lem5376418 n m h1 h2 h3) (@lem5375881 h2)). Qed.
Lemma lem5376420 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term216 x n m) : False.
Proof. exact (or_elim (@lem5375864 x n m h4) (fun h0 : term91 n m => @lem5376419 n m h2 h3 h0) (fun h0 : term171 x n m => @lem5376417 x n m h1 h2 h0)). Qed.
Lemma lem5376421 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term216 x n m) : (term216 x n m) = False.
Proof. exact (prop_ext (fun h5 : term216 x n m => @lem5376420 x n m h1 h2 h3 h4) (fun h5 : False => @lem5375864 x n m h4)). Qed.
Lemma lem5376422 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term216 x n m) : False.
Proof. exact (EQ_MP (@lem5376421 x n m h1 h2 h3 h4) (@lem5375864 x n m h4)). Qed.
Lemma lem5376423 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term216 x n m) : term69 = False.
Proof. exact (prop_ext (fun h5 : term69 => @lem5376422 x n m h1 h2 h3 h4) (fun h5 : False => @lem5375728 h3)). Qed.
Lemma lem5376424 (x : nat) (n : nat) (m : nat) (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term216 x n m) : False.
Proof. exact (EQ_MP (@lem5376423 x n m h1 h2 h3 h4) (@lem5375728 h3)). Qed.
Lemma lem5376425 (n : nat) (m : nat) (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term219 n m) : False.
Proof. exact (ex_elim (@lem5375718 n m h4) (fun x : nat => fun h0 : term218 n m x => @lem5376424 x n m h1 h2 h3 h0)). Qed.
Lemma lem5376426 (m : nat) (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term221 m) : False.
Proof. exact (ex_elim (@lem5375717 m h4) (fun n : nat => fun h0 : term220 m n => @lem5376425 n m h1 h2 h3 h0)). Qed.
Lemma lem5376427 (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term41) : False.
Proof. exact (ex_elim (@lem5375331 h4) (fun m : nat => fun h0 : term222 m => @lem5376426 m h1 h2 h3 h0)). Qed.
Lemma lem5376428 (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term41) : term69 = False.
Proof. exact (prop_ext (fun h5 : term69 => @lem5376427 h1 h2 h3 h4) (fun h5 : False => @lem5375344 h3)). Qed.
Lemma lem5376429 (h1 : term67) (h2 : term48) (h3 : term69) (h4 : term41) : False.
Proof. exact (EQ_MP (@lem5376428 h1 h2 h3 h4) (@lem5375344 h3)). Qed.
Lemma lem5376430 (h1 : term67) (h2 : term69) (h3 : term41) : term46.
Proof. exact (fun h0 : term48 => @lem5376429 h1 h0 h2 h3). Qed.
Lemma lem5376431 : term46 = term47.
Proof. exact (@lem69 term48). Qed.
Lemma lem5376432 (h1 : term67) (h2 : term69) (h3 : term41) : term47.
Proof. exact (EQ_MP (@lem5376431) (@lem5376430 h1 h2 h3)). Qed.
Lemma lem5376433 (h1 : term69) (h2 : term41) : term51.
Proof. exact (fun h0 : term67 => @lem5376432 h0 h1 h2). Qed.
Lemma lem5376434 (h1 : term41) : term54.
Proof. exact (fun h0 : term69 => @lem5376433 h0 h1). Qed.
Lemma lem5376435 : term56.
Proof. exact (fun h0 : term41 => @lem5376434 h0). Qed.
Lemma lem5376436 : term42.
Proof. exact (EQ_MP (@lem5374695) (@lem5376435)). Qed.
Lemma lem5376438 : term42.
Proof. exact (@lem5374490 (@lem5376436)). Qed.
Lemma lem5376439 (h1 : term41) : term53.
Proof. exact (@lem5376438 (@lem5374475 h1)). Qed.
Lemma lem5376440 (h1 : term41) : term50.
Proof. exact (@lem5376439 h1 (@lem91603)). Qed.
Lemma lem5376441 (h1 : term41) : term46.
Proof. exact (@lem5376440 h1 (@lem93743)). Qed.
Lemma lem5376442 (h1 : term41) : False.
Proof. exact (@lem5376441 h1 (@lem97961)). Qed.
Lemma lem5376443 (h1 : term41) : term41 = False.
Proof. exact (prop_ext (fun h2 : term41 => @lem5376442 h1) (fun h2 : False => @lem5374475 h1)). Qed.
Lemma lem5376444 (h1 : term41) : False.
Proof. exact (EQ_MP (@lem5376443 h1) (@lem5374475 h1)). Qed.
Lemma lem5376445 : term40.
Proof. exact (fun h0 : term41 => @lem5376444 h0). Qed.
Lemma lem5376446 : term38.
Proof. exact (EQ_MP (@lem5374474) (@lem5376445)). Qed.
Lemma lem5376447 : term37.
Proof. exact (EQ_MP (@lem5374470) (@lem5376446)). Qed.
