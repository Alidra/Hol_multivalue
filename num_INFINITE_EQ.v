Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_INFINITE_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INFINITE_spec.
Require Import LE_SUC_LT_spec.
Require Import LT_IMP_LE_spec.
Require Import NOT_LE_spec.
Require Import num_FINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
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
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4626370 (s : nat -> Prop) : term0 s.
Proof. exact (@lem4624119 s). Qed.
Lemma lem4626371 (s : nat -> Prop) : (term0 s) = ((@FINITE nat s) = (term1 s)).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem4626373 {A : Type'} (s : A -> Prop) : term2 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem4626374 {A : Type'} (s : A -> Prop) : (term2 A s) = ((@INFINITE A s) = (term3 A s)).
Proof. exact (eq_refl (term2 A s)). Qed.
Lemma lem4626379 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term3 A s).
Proof. exact (EQ_MP (@lem4626374 A s) (@lem4626373 A s)). Qed.
Lemma lem4626380 (s : nat -> Prop) : (@INFINITE nat s) = (term4 s).
Proof. exact (@lem4626379 nat s). Qed.
Lemma lem4626382 (s : nat -> Prop) : (@FINITE nat s) = (term1 s).
Proof. exact (EQ_MP (@lem4626371 s) (@lem4626370 s)). Qed.
Lemma lem4626393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4626394 (s : nat -> Prop) : (term4 s) = (term5 s).
Proof. exact (MK_COMB (@lem4626393) (@lem4626382 s)). Qed.
Lemma lem4626395 (s : nat -> Prop) : (@INFINITE nat s) = (term5 s).
Proof. exact (TRANS (@lem4626380 s) (@lem4626394 s)). Qed.
Lemma lem4626396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4626397 (s : nat -> Prop) : (term6 s) = (term7 s).
Proof. exact (MK_COMB (@lem4626396) (@lem4626395 s)). Qed.
Lemma lem4626408 (s : nat -> Prop) : (term8 s) = (term8 s).
Proof. exact (eq_refl (term8 s)). Qed.
Lemma lem4626409 (s : nat -> Prop) : ((@INFINITE nat s) = (term8 s)) = ((term5 s) = (term8 s)).
Proof. exact (MK_COMB (@lem4626397 s) (@lem4626408 s)). Qed.
Lemma lem4626412 (s : nat -> Prop) : ((term5 s) = (term8 s)) = ((@INFINITE nat s) = (term8 s)).
Proof. exact (SYM (@lem4626409 s)). Qed.
Lemma lem4626414 (p : Prop) : p = (term9 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4626415 (s : nat -> Prop) : ((term5 s) = (term8 s)) = (term10 s).
Proof. exact (@lem4626414 ((term5 s) = (term8 s))). Qed.
Lemma lem4626416 (s : nat -> Prop) : (term10 s) = ((term5 s) = (term8 s)).
Proof. exact (SYM (@lem4626415 s)). Qed.
Lemma lem4626417 (s : nat -> Prop) (h1 : term11 s) : term11 s.
Proof. exact (h1). Qed.
Lemma lem4626420 (s : nat -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (h1). Qed.
Lemma lem4626421 (s : nat -> Prop) : term13 s.
Proof. exact (fun h0 : term12 s => @lem4626420 s h0). Qed.
Lemma lem4626422 (s : nat -> Prop) (h1 : term13 s) : term13 s.
Proof. exact (h1). Qed.
Lemma lem4626423 (s : nat -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (h1). Qed.
Lemma lem4626424 (s : nat -> Prop) (h1 : term12 s) (h2 : term13 s) : term12 s.
Proof. exact (@lem4626422 s h2 (@lem4626423 s h1)). Qed.
Lemma lem4626425 (s : nat -> Prop) (h1 : term12 s) : term14 s.
Proof. exact (fun h0 : term13 s => @lem4626424 s h1 h0). Qed.
Lemma lem4626426 (s : nat -> Prop) (h1 : term13 s) : term13 s.
Proof. exact (h1). Qed.
Lemma lem4626427 (s : nat -> Prop) (h1 : term12 s) (h2 : term13 s) : term12 s.
Proof. exact (@lem4626425 s h1 (@lem4626426 s h2)). Qed.
Lemma lem4626428 (s : nat -> Prop) (h1 : term13 s) : term13 s.
Proof. exact (fun h0 : term12 s => @lem4626427 s h0 h1). Qed.
Lemma lem4626429 (s : nat -> Prop) : term15 s.
Proof. exact (fun h0 : term13 s => @lem4626428 s h0). Qed.
Lemma lem4626432 (s : nat -> Prop) : term13 s.
Proof. exact (@lem4626429 s (@lem4626421 s)). Qed.
Lemma lem4626526 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4626527 : term16 = term17.
Proof. exact (@lem4626526 term18). Qed.
Lemma lem4626536 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem4626537 : term20 = term21.
Proof. exact (MK_COMB (@lem4626536) (@lem4626527)). Qed.
Lemma lem4626540 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem4626541 : term23 = term24.
Proof. exact (MK_COMB (@lem4626540) (@lem4626537)). Qed.
Lemma lem4626544 (s : nat -> Prop) : (term25 s) = (term25 s).
Proof. exact (eq_refl (term25 s)). Qed.
Lemma lem4626545 (s : nat -> Prop) : (term12 s) = (term26 s).
Proof. exact (MK_COMB (@lem4626544 s) (@lem4626541)). Qed.
Lemma lem4626548 : term27 = term28.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4626545 s)). Qed.
Lemma lem4626549 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4626558 : term29 = term30.
Proof. exact (MK_COMB (@lem4626549) (@lem4626548)). Qed.
Lemma lem4626565 (n : nat) (m : nat) : ((term31 m n) = (Peano.lt n m)) = ((term31 m n) = (Peano.lt n m)).
Proof. exact (eq_refl ((term31 m n) = (Peano.lt n m))). Qed.
Lemma lem4626566 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem4626565 n m)). Qed.
Lemma lem4626567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626568 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem4626567) (@lem4626566 m)). Qed.
Lemma lem4626569 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem4626568 m)). Qed.
Lemma lem4626570 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626571 : term18 = term18.
Proof. exact (MK_COMB (@lem4626570) (@lem4626569)). Qed.
Lemma lem4626572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4626573 : term17 = term17.
Proof. exact (MK_COMB (@lem4626572) (@lem4626571)). Qed.
Lemma lem4626578 (m : nat) (n : nat) : (term35 m n) = (term35 m n).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem4626579 (m : nat) : (term36 m) = (term36 m).
Proof. exact (fun_ext (fun n : nat => @lem4626578 m n)). Qed.
Lemma lem4626580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626581 (m : nat) : (term37 m) = (term37 m).
Proof. exact (MK_COMB (@lem4626580) (@lem4626579 m)). Qed.
Lemma lem4626582 : term38 = term38.
Proof. exact (fun_ext (fun m : nat => @lem4626581 m)). Qed.
Lemma lem4626583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626584 : term39 = term39.
Proof. exact (MK_COMB (@lem4626583) (@lem4626582)). Qed.
Lemma lem4626585 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4626586 : term19 = term19.
Proof. exact (MK_COMB (@lem4626585) (@lem4626584)). Qed.
Lemma lem4626587 : term21 = term21.
Proof. exact (MK_COMB (@lem4626586) (@lem4626573)). Qed.
Lemma lem4626592 (m : nat) (n : nat) : ((term40 m n) = (Peano.lt m n)) = ((term40 m n) = (Peano.lt m n)).
Proof. exact (eq_refl ((term40 m n) = (Peano.lt m n))). Qed.
Lemma lem4626593 (m : nat) : (term41 m) = (term41 m).
Proof. exact (fun_ext (fun n : nat => @lem4626592 m n)). Qed.
Lemma lem4626594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626595 (m : nat) : (term42 m) = (term42 m).
Proof. exact (MK_COMB (@lem4626594) (@lem4626593 m)). Qed.
Lemma lem4626596 : term43 = term43.
Proof. exact (fun_ext (fun m : nat => @lem4626595 m)). Qed.
Lemma lem4626597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626598 : term44 = term44.
Proof. exact (MK_COMB (@lem4626597) (@lem4626596)). Qed.
Lemma lem4626599 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4626600 : term22 = term22.
Proof. exact (MK_COMB (@lem4626599) (@lem4626598)). Qed.
Lemma lem4626601 : term24 = term24.
Proof. exact (MK_COMB (@lem4626600) (@lem4626587)). Qed.
Lemma lem4626606 (N : nat) (n : nat) (s : nat -> Prop) : (term45 N n s) = (term45 N n s).
Proof. exact (eq_refl (term45 N n s)). Qed.
Lemma lem4626607 (N : nat) (s : nat -> Prop) : (term46 N s) = (term46 N s).
Proof. exact (fun_ext (fun n : nat => @lem4626606 N n s)). Qed.
Lemma lem4626608 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4626609 (N : nat) (s : nat -> Prop) : (term47 N s) = (term47 N s).
Proof. exact (MK_COMB (@lem4626608) (@lem4626607 N s)). Qed.
Lemma lem4626610 (s : nat -> Prop) : (term48 s) = (term48 s).
Proof. exact (fun_ext (fun N : nat => @lem4626609 N s)). Qed.
Lemma lem4626611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626612 (s : nat -> Prop) : (term8 s) = (term8 s).
Proof. exact (MK_COMB (@lem4626611) (@lem4626610 s)). Qed.
Lemma lem4626617 (s : nat -> Prop) (x : nat) (a : nat) : (term49 s x a) = (term49 s x a).
Proof. exact (eq_refl (term49 s x a)). Qed.
Lemma lem4626618 (s : nat -> Prop) (a : nat) : (term50 s a) = (term50 s a).
Proof. exact (fun_ext (fun x : nat => @lem4626617 s x a)). Qed.
Lemma lem4626619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626620 (s : nat -> Prop) (a : nat) : (term51 s a) = (term51 s a).
Proof. exact (MK_COMB (@lem4626619) (@lem4626618 s a)). Qed.
Lemma lem4626621 (s : nat -> Prop) : (term52 s) = (term52 s).
Proof. exact (fun_ext (fun a : nat => @lem4626620 s a)). Qed.
Lemma lem4626622 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4626623 (s : nat -> Prop) : (term1 s) = (term1 s).
Proof. exact (MK_COMB (@lem4626622) (@lem4626621 s)). Qed.
Lemma lem4626624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4626625 (s : nat -> Prop) : (term5 s) = (term5 s).
Proof. exact (MK_COMB (@lem4626624) (@lem4626623 s)). Qed.
Lemma lem4626626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4626627 (s : nat -> Prop) : (term7 s) = (term7 s).
Proof. exact (MK_COMB (@lem4626626) (@lem4626625 s)). Qed.
Lemma lem4626628 (s : nat -> Prop) : ((term5 s) = (term8 s)) = ((term5 s) = (term8 s)).
Proof. exact (MK_COMB (@lem4626627 s) (@lem4626612 s)). Qed.
Lemma lem4626629 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4626630 (s : nat -> Prop) : (term11 s) = (term11 s).
Proof. exact (MK_COMB (@lem4626629) (@lem4626628 s)). Qed.
Lemma lem4626631 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4626632 (s : nat -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem4626631) (@lem4626630 s)). Qed.
Lemma lem4626633 (s : nat -> Prop) : (term26 s) = (term26 s).
Proof. exact (MK_COMB (@lem4626632 s) (@lem4626601)). Qed.
Lemma lem4626634 : term28 = term28.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4626633 s)). Qed.
Lemma lem4626635 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4626636 : term30 = term30.
Proof. exact (MK_COMB (@lem4626635) (@lem4626634)). Qed.
Lemma lem4626717 : term29 = term30.
Proof. exact (TRANS (@lem4626558) (@lem4626636)). Qed.
Lemma lem4626718 : term30 = term29.
Proof. exact (SYM (@lem4626717)). Qed.
Lemma lem4626719 (s : nat -> Prop) (h1 : term11 s) : term11 s.
Proof. exact (h1). Qed.
Lemma lem4626720 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem4626721 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem4626722 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem4626731 (s : nat -> Prop) (x : nat) (a : nat) : (term53 s x a) = (term54 s x a).
Proof. exact (@lem17362 (@IN nat x s) (Peano.le x a)). Qed.
Lemma lem4626736 (s : nat -> Prop) (x : nat) (a : nat) : (term49 s x a) = (term55 s x a).
Proof. exact (@lem17265 (@IN nat x s) (Peano.le x a)). Qed.
Lemma lem4626737 (P : nat -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4626738 (s : nat -> Prop) (a : nat) : (term58 s a) = (term59 s a).
Proof. exact (@lem4626737 (term50 s a)). Qed.
Lemma lem4626739 (s : nat -> Prop) (x : nat) (a : nat) : (term60 s a x) = (term49 s x a).
Proof. exact (eq_refl (term60 s a x)). Qed.
Lemma lem4626740 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4626741 (s : nat -> Prop) (x : nat) (a : nat) : (term61 s a x) = (term53 s x a).
Proof. exact (MK_COMB (@lem4626740) (@lem4626739 s x a)). Qed.
Lemma lem4626742 (s : nat -> Prop) (x : nat) (a : nat) : (term61 s a x) = (term54 s x a).
Proof. exact (TRANS (@lem4626741 s x a) (@lem4626731 s x a)). Qed.
Lemma lem4626743 (s : nat -> Prop) (a : nat) : (term62 s a) = (term63 s a).
Proof. exact (fun_ext (fun x : nat => @lem4626742 s x a)). Qed.
Lemma lem4626744 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4626745 (s : nat -> Prop) (a : nat) : (term59 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem4626744) (@lem4626743 s a)). Qed.
Lemma lem4626746 (s : nat -> Prop) (a : nat) : (term58 s a) = (term64 s a).
Proof. exact (TRANS (@lem4626738 s a) (@lem4626745 s a)). Qed.
Lemma lem4626747 (s : nat -> Prop) (a : nat) : (term50 s a) = (term65 s a).
Proof. exact (fun_ext (fun x : nat => @lem4626736 s x a)). Qed.
Lemma lem4626748 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626749 (s : nat -> Prop) (a : nat) : (term51 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem4626748) (@lem4626747 s a)). Qed.
Lemma lem4626750 (P : nat -> Prop) : (term67 P) = (term68 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem4626751 (s : nat -> Prop) : (term5 s) = (term69 s).
Proof. exact (@lem4626750 (term52 s)). Qed.
Lemma lem4626752 (s : nat -> Prop) (a : nat) : (term70 s a) = (term51 s a).
Proof. exact (eq_refl (term70 s a)). Qed.
Lemma lem4626753 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4626754 (s : nat -> Prop) (a : nat) : (term71 s a) = (term58 s a).
Proof. exact (MK_COMB (@lem4626753) (@lem4626752 s a)). Qed.
Lemma lem4626755 (s : nat -> Prop) (a : nat) : (term71 s a) = (term64 s a).
Proof. exact (TRANS (@lem4626754 s a) (@lem4626746 s a)). Qed.
Lemma lem4626756 (s : nat -> Prop) : (term72 s) = (term73 s).
Proof. exact (fun_ext (fun a : nat => @lem4626755 s a)). Qed.
Lemma lem4626757 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626758 (s : nat -> Prop) : (term69 s) = (term74 s).
Proof. exact (MK_COMB (@lem4626757) (@lem4626756 s)). Qed.
Lemma lem4626759 (s : nat -> Prop) : (term5 s) = (term74 s).
Proof. exact (TRANS (@lem4626751 s) (@lem4626758 s)). Qed.
Lemma lem4626760 (s : nat -> Prop) : (term52 s) = (term75 s).
Proof. exact (fun_ext (fun a : nat => @lem4626749 s a)). Qed.
Lemma lem4626761 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4626762 (s : nat -> Prop) : (term1 s) = (term76 s).
Proof. exact (MK_COMB (@lem4626761) (@lem4626760 s)). Qed.
Lemma lem4626763 (s : nat -> Prop) : (term77 s) = (term1 s).
Proof. exact (@lem16933 (term1 s)). Qed.
Lemma lem4626764 (s : nat -> Prop) : (term77 s) = (term76 s).
Proof. exact (TRANS (@lem4626763 s) (@lem4626762 s)). Qed.
Lemma lem4626773 (N : nat) (n : nat) (s : nat -> Prop) : (term78 N n s) = (term79 N n s).
Proof. exact (@lem17045 (Peano.le N n) (@IN nat n s)). Qed.
Lemma lem4626776 (N : nat) (n : nat) (s : nat -> Prop) : (term45 N n s) = (term45 N n s).
Proof. exact (eq_refl (term45 N n s)). Qed.
Lemma lem4626777 (P : nat -> Prop) : (term67 P) = (term68 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem4626778 (N : nat) (s : nat -> Prop) : (term80 N s) = (term81 N s).
Proof. exact (@lem4626777 (term46 N s)). Qed.
Lemma lem4626779 (N : nat) (n : nat) (s : nat -> Prop) : (term82 N s n) = (term45 N n s).
Proof. exact (eq_refl (term82 N s n)). Qed.
Lemma lem4626780 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4626781 (N : nat) (n : nat) (s : nat -> Prop) : (term83 N s n) = (term78 N n s).
Proof. exact (MK_COMB (@lem4626780) (@lem4626779 N n s)). Qed.
Lemma lem4626782 (N : nat) (n : nat) (s : nat -> Prop) : (term83 N s n) = (term79 N n s).
Proof. exact (TRANS (@lem4626781 N n s) (@lem4626773 N n s)). Qed.
Lemma lem4626783 (N : nat) (s : nat -> Prop) : (term84 N s) = (term85 N s).
Proof. exact (fun_ext (fun n : nat => @lem4626782 N n s)). Qed.
Lemma lem4626784 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626785 (N : nat) (s : nat -> Prop) : (term81 N s) = (term86 N s).
Proof. exact (MK_COMB (@lem4626784) (@lem4626783 N s)). Qed.
Lemma lem4626786 (N : nat) (s : nat -> Prop) : (term80 N s) = (term86 N s).
Proof. exact (TRANS (@lem4626778 N s) (@lem4626785 N s)). Qed.
Lemma lem4626787 (N : nat) (s : nat -> Prop) : (term46 N s) = (term46 N s).
Proof. exact (fun_ext (fun n : nat => @lem4626776 N n s)). Qed.
Lemma lem4626788 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4626789 (N : nat) (s : nat -> Prop) : (term47 N s) = (term47 N s).
Proof. exact (MK_COMB (@lem4626788) (@lem4626787 N s)). Qed.
Lemma lem4626790 (P : nat -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4626791 (s : nat -> Prop) : (term87 s) = (term88 s).
Proof. exact (@lem4626790 (term48 s)). Qed.
Lemma lem4626792 (N : nat) (s : nat -> Prop) : (term89 s N) = (term47 N s).
Proof. exact (eq_refl (term89 s N)). Qed.
Lemma lem4626793 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4626794 (N : nat) (s : nat -> Prop) : (term90 s N) = (term80 N s).
Proof. exact (MK_COMB (@lem4626793) (@lem4626792 N s)). Qed.
Lemma lem4626795 (N : nat) (s : nat -> Prop) : (term90 s N) = (term86 N s).
Proof. exact (TRANS (@lem4626794 N s) (@lem4626786 N s)). Qed.
Lemma lem4626796 (s : nat -> Prop) : (term91 s) = (term92 s).
Proof. exact (fun_ext (fun N : nat => @lem4626795 N s)). Qed.
Lemma lem4626797 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4626798 (s : nat -> Prop) : (term88 s) = (term93 s).
Proof. exact (MK_COMB (@lem4626797) (@lem4626796 s)). Qed.
Lemma lem4626799 (s : nat -> Prop) : (term87 s) = (term93 s).
Proof. exact (TRANS (@lem4626791 s) (@lem4626798 s)). Qed.
Lemma lem4626800 (s : nat -> Prop) : (term48 s) = (term48 s).
Proof. exact (fun_ext (fun N : nat => @lem4626789 N s)). Qed.
Lemma lem4626801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4626802 (s : nat -> Prop) : (term8 s) = (term8 s).
Proof. exact (MK_COMB (@lem4626801) (@lem4626800 s)). Qed.
Lemma lem4626803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4626804 (s : nat -> Prop) : (term94 s) = (term95 s).
Proof. exact (MK_COMB (@lem4626803) (@lem4626764 s)). Qed.
Lemma lem4626805 (s : nat -> Prop) : (term96 s) = (term97 s).
Proof. exact (MK_COMB (@lem4626804 s) (@lem4626802 s)). Qed.
Lemma lem4626806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4626807 (s : nat -> Prop) : (term98 s) = (term99 s).
Proof. exact (MK_COMB (@lem4626806) (@lem4626759 s)). Qed.
Lemma lem4626808 (s : nat -> Prop) : (term100 s) = (term101 s).
Proof. exact (MK_COMB (@lem4626807 s) (@lem4626799 s)). Qed.
Lemma lem4626809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4626810 (s : nat -> Prop) : (term102 s) = (term103 s).
Proof. exact (MK_COMB (@lem4626809) (@lem4626808 s)). Qed.
Lemma lem4626811 (s : nat -> Prop) : (term104 s) = (term105 s).
Proof. exact (MK_COMB (@lem4626810 s) (@lem4626805 s)). Qed.
Lemma lem4626812 (s : nat -> Prop) : (term11 s) = (term104 s).
Proof. exact (@lem17646 (term5 s) (term8 s)). Qed.
Lemma lem4626813 (s : nat -> Prop) : (term11 s) = (term105 s).
Proof. exact (TRANS (@lem4626812 s) (@lem4626811 s)). Qed.
Lemma lem4627024 {A B : Type'} (P : type1413 A B) : (term106 A B P) = (term107 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4627025 (P : type1605) : (term108 P) = (term109 P).
Proof. exact (@lem4627024 nat nat P). Qed.
Lemma lem4627026 (s : nat -> Prop) : (term110 s) = (term111 s).
Proof. exact (@lem4627025 (term112 s)). Qed.
Lemma lem4627027 (s : nat -> Prop) (a : nat) : (term113 s a) = (term63 s a).
Proof. exact (eq_refl (term113 s a)). Qed.
Lemma lem4627028 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4627029 (s : nat -> Prop) (a : nat) (x : nat) : (term114 s a x) = (term115 s a x).
Proof. exact (MK_COMB (@lem4627027 s a) (@lem4627028 x)). Qed.
Lemma lem4627030 (s : nat -> Prop) (x : nat) (a : nat) : (term115 s a x) = (term54 s x a).
Proof. exact (eq_refl (term115 s a x)). Qed.
Lemma lem4627031 (s : nat -> Prop) (x : nat) (a : nat) : (term114 s a x) = (term54 s x a).
Proof. exact (TRANS (@lem4627029 s a x) (@lem4627030 s x a)). Qed.
Lemma lem4627032 (s : nat -> Prop) (a : nat) : (term116 s a) = (term63 s a).
Proof. exact (fun_ext (fun x : nat => @lem4627031 s x a)). Qed.
Lemma lem4627033 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627034 (s : nat -> Prop) (a : nat) : (term117 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem4627033) (@lem4627032 s a)). Qed.
Lemma lem4627035 (s : nat -> Prop) : (term118 s) = (term73 s).
Proof. exact (fun_ext (fun a : nat => @lem4627034 s a)). Qed.
Lemma lem4627036 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627037 (s : nat -> Prop) : (term110 s) = (term74 s).
Proof. exact (MK_COMB (@lem4627036) (@lem4627035 s)). Qed.
Lemma lem4627038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627039 (s : nat -> Prop) : (term119 s) = (term120 s).
Proof. exact (MK_COMB (@lem4627038) (@lem4627037 s)). Qed.
Lemma lem4627040 (s : nat -> Prop) (a : nat) : (term113 s a) = (term63 s a).
Proof. exact (eq_refl (term113 s a)). Qed.
Lemma lem4627041 (x : nat -> nat) (a : nat) : (x a) = (x a).
Proof. exact (eq_refl (x a)). Qed.
Lemma lem4627042 (s : nat -> Prop) (x : nat -> nat) (a : nat) : (term121 s x a) = (term122 s x a).
Proof. exact (MK_COMB (@lem4627040 s a) (@lem4627041 x a)). Qed.
Lemma lem4627043 (s : nat -> Prop) (x : nat -> nat) (a : nat) : (term122 s x a) = (term123 s x a).
Proof. exact (eq_refl (term122 s x a)). Qed.
Lemma lem4627044 (s : nat -> Prop) (x : nat -> nat) (a : nat) : (term121 s x a) = (term123 s x a).
Proof. exact (TRANS (@lem4627042 s x a) (@lem4627043 s x a)). Qed.
Lemma lem4627045 (s : nat -> Prop) (x : nat -> nat) : (term124 s x) = (term125 s x).
Proof. exact (fun_ext (fun a : nat => @lem4627044 s x a)). Qed.
Lemma lem4627046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627047 (s : nat -> Prop) (x : nat -> nat) : (term126 s x) = (term127 s x).
Proof. exact (MK_COMB (@lem4627046) (@lem4627045 s x)). Qed.
Lemma lem4627048 (s : nat -> Prop) : (term128 s) = (term129 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4627047 s x)). Qed.
Lemma lem4627049 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627050 (s : nat -> Prop) : (term111 s) = (term130 s).
Proof. exact (MK_COMB (@lem4627049) (@lem4627048 s)). Qed.
Lemma lem4627051 (s : nat -> Prop) : ((term110 s) = (term111 s)) = ((term74 s) = (term130 s)).
Proof. exact (MK_COMB (@lem4627039 s) (@lem4627050 s)). Qed.
Lemma lem4627052 (s : nat -> Prop) : (term74 s) = (term130 s).
Proof. exact (EQ_MP (@lem4627051 s) (@lem4627026 s)). Qed.
Lemma lem4627053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627054 (s : nat -> Prop) : (term99 s) = (term131 s).
Proof. exact (MK_COMB (@lem4627053) (@lem4627052 s)). Qed.
Lemma lem4627055 (s : nat -> Prop) : (term93 s) = (term93 s).
Proof. exact (eq_refl (term93 s)). Qed.
Lemma lem4627056 (s : nat -> Prop) : (term101 s) = (term132 s).
Proof. exact (MK_COMB (@lem4627054 s) (@lem4627055 s)). Qed.
Lemma lem4627058 {A : Type'} (P : A -> Prop) (Q : Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4627059 (P : type1002) (Q : Prop) : (term135 P Q) = (term136 P Q).
Proof. exact (@lem4627058 (nat -> nat) P Q). Qed.
Lemma lem4627060 (s : nat -> Prop) : (term137 s) = (term138 s).
Proof. exact (@lem4627059 (term129 s) (term93 s)). Qed.
Lemma lem4627061 (s : nat -> Prop) (x : nat -> nat) : (term139 s x) = (term127 s x).
Proof. exact (eq_refl (term139 s x)). Qed.
Lemma lem4627062 (s : nat -> Prop) : (term140 s) = (term129 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4627061 s x)). Qed.
Lemma lem4627063 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627064 (s : nat -> Prop) : (term141 s) = (term130 s).
Proof. exact (MK_COMB (@lem4627063) (@lem4627062 s)). Qed.
Lemma lem4627065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627066 (s : nat -> Prop) : (term142 s) = (term131 s).
Proof. exact (MK_COMB (@lem4627065) (@lem4627064 s)). Qed.
Lemma lem4627067 (s : nat -> Prop) : (term93 s) = (term93 s).
Proof. exact (eq_refl (term93 s)). Qed.
Lemma lem4627068 (s : nat -> Prop) : (term137 s) = (term132 s).
Proof. exact (MK_COMB (@lem4627066 s) (@lem4627067 s)). Qed.
Lemma lem4627069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627070 (s : nat -> Prop) : (term143 s) = (term144 s).
Proof. exact (MK_COMB (@lem4627069) (@lem4627068 s)). Qed.
Lemma lem4627071 (s : nat -> Prop) (x : nat -> nat) : (term139 s x) = (term127 s x).
Proof. exact (eq_refl (term139 s x)). Qed.
Lemma lem4627072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627073 (s : nat -> Prop) (x : nat -> nat) : (term145 s x) = (term146 s x).
Proof. exact (MK_COMB (@lem4627072) (@lem4627071 s x)). Qed.
Lemma lem4627074 (s : nat -> Prop) : (term93 s) = (term93 s).
Proof. exact (eq_refl (term93 s)). Qed.
Lemma lem4627075 (x : nat -> nat) (s : nat -> Prop) : (term147 x s) = (term148 x s).
Proof. exact (MK_COMB (@lem4627073 s x) (@lem4627074 s)). Qed.
Lemma lem4627076 (s : nat -> Prop) : (term149 s) = (term150 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4627075 x s)). Qed.
Lemma lem4627077 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627078 (s : nat -> Prop) : (term138 s) = (term151 s).
Proof. exact (MK_COMB (@lem4627077) (@lem4627076 s)). Qed.
Lemma lem4627079 (s : nat -> Prop) : ((term137 s) = (term138 s)) = ((term132 s) = (term151 s)).
Proof. exact (MK_COMB (@lem4627070 s) (@lem4627078 s)). Qed.
Lemma lem4627080 (s : nat -> Prop) : (term132 s) = (term151 s).
Proof. exact (EQ_MP (@lem4627079 s) (@lem4627060 s)). Qed.
Lemma lem4627082 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4627083 (P : Prop) (Q : nat -> Prop) : (term154 P Q) = (term155 P Q).
Proof. exact (@lem4627082 nat P Q). Qed.
Lemma lem4627084 (x : nat -> nat) (s : nat -> Prop) : (term156 x s) = (term157 x s).
Proof. exact (@lem4627083 (term127 s x) (term92 s)). Qed.
Lemma lem4627085 (N : nat) (s : nat -> Prop) : (term158 s N) = (term86 N s).
Proof. exact (eq_refl (term158 s N)). Qed.
Lemma lem4627086 (s : nat -> Prop) : (term159 s) = (term92 s).
Proof. exact (fun_ext (fun N : nat => @lem4627085 N s)). Qed.
Lemma lem4627087 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627088 (s : nat -> Prop) : (term160 s) = (term93 s).
Proof. exact (MK_COMB (@lem4627087) (@lem4627086 s)). Qed.
Lemma lem4627089 (s : nat -> Prop) (x : nat -> nat) : (term146 s x) = (term146 s x).
Proof. exact (eq_refl (term146 s x)). Qed.
Lemma lem4627090 (x : nat -> nat) (s : nat -> Prop) : (term156 x s) = (term148 x s).
Proof. exact (MK_COMB (@lem4627089 s x) (@lem4627088 s)). Qed.
Lemma lem4627091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627092 (x : nat -> nat) (s : nat -> Prop) : (term161 x s) = (term162 x s).
Proof. exact (MK_COMB (@lem4627091) (@lem4627090 x s)). Qed.
Lemma lem4627093 (N : nat) (s : nat -> Prop) : (term158 s N) = (term86 N s).
Proof. exact (eq_refl (term158 s N)). Qed.
Lemma lem4627094 (s : nat -> Prop) (x : nat -> nat) : (term146 s x) = (term146 s x).
Proof. exact (eq_refl (term146 s x)). Qed.
Lemma lem4627095 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term163 x s N) = (term164 x N s).
Proof. exact (MK_COMB (@lem4627094 s x) (@lem4627093 N s)). Qed.
Lemma lem4627096 (x : nat -> nat) (s : nat -> Prop) : (term165 x s) = (term166 x s).
Proof. exact (fun_ext (fun N : nat => @lem4627095 x N s)). Qed.
Lemma lem4627097 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627098 (x : nat -> nat) (s : nat -> Prop) : (term157 x s) = (term167 x s).
Proof. exact (MK_COMB (@lem4627097) (@lem4627096 x s)). Qed.
Lemma lem4627099 (x : nat -> nat) (s : nat -> Prop) : ((term156 x s) = (term157 x s)) = ((term148 x s) = (term167 x s)).
Proof. exact (MK_COMB (@lem4627092 x s) (@lem4627098 x s)). Qed.
Lemma lem4627100 (x : nat -> nat) (s : nat -> Prop) : (term148 x s) = (term167 x s).
Proof. exact (EQ_MP (@lem4627099 x s) (@lem4627084 x s)). Qed.
Lemma lem4627101 (s : nat -> Prop) : (term150 s) = (term168 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4627100 x s)). Qed.
Lemma lem4627102 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627103 (s : nat -> Prop) : (term151 s) = (term169 s).
Proof. exact (MK_COMB (@lem4627102) (@lem4627101 s)). Qed.
Lemma lem4627104 (s : nat -> Prop) : (term132 s) = (term169 s).
Proof. exact (TRANS (@lem4627080 s) (@lem4627103 s)). Qed.
Lemma lem4627105 (s : nat -> Prop) : (term101 s) = (term169 s).
Proof. exact (TRANS (@lem4627056 s) (@lem4627104 s)). Qed.
Lemma lem4627106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4627107 (s : nat -> Prop) : (term103 s) = (term170 s).
Proof. exact (MK_COMB (@lem4627106) (@lem4627105 s)). Qed.
Lemma lem4627109 {A B : Type'} (P : type1413 A B) : (term106 A B P) = (term107 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4627110 (P : type1605) : (term108 P) = (term109 P).
Proof. exact (@lem4627109 nat nat P). Qed.
Lemma lem4627111 (s : nat -> Prop) : (term171 s) = (term172 s).
Proof. exact (@lem4627110 (term173 s)). Qed.
Lemma lem4627112 (N : nat) (s : nat -> Prop) : (term174 s N) = (term46 N s).
Proof. exact (eq_refl (term174 s N)). Qed.
Lemma lem4627113 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4627114 (N : nat) (s : nat -> Prop) (n : nat) : (term175 s N n) = (term82 N s n).
Proof. exact (MK_COMB (@lem4627112 N s) (@lem4627113 n)). Qed.
Lemma lem4627115 (N : nat) (n : nat) (s : nat -> Prop) : (term82 N s n) = (term45 N n s).
Proof. exact (eq_refl (term82 N s n)). Qed.
Lemma lem4627116 (N : nat) (n : nat) (s : nat -> Prop) : (term175 s N n) = (term45 N n s).
Proof. exact (TRANS (@lem4627114 N s n) (@lem4627115 N n s)). Qed.
Lemma lem4627117 (N : nat) (s : nat -> Prop) : (term176 s N) = (term46 N s).
Proof. exact (fun_ext (fun n : nat => @lem4627116 N n s)). Qed.
Lemma lem4627118 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627119 (N : nat) (s : nat -> Prop) : (term177 s N) = (term47 N s).
Proof. exact (MK_COMB (@lem4627118) (@lem4627117 N s)). Qed.
Lemma lem4627120 (s : nat -> Prop) : (term178 s) = (term48 s).
Proof. exact (fun_ext (fun N : nat => @lem4627119 N s)). Qed.
Lemma lem4627121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627122 (s : nat -> Prop) : (term171 s) = (term8 s).
Proof. exact (MK_COMB (@lem4627121) (@lem4627120 s)). Qed.
Lemma lem4627123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627124 (s : nat -> Prop) : (term179 s) = (term180 s).
Proof. exact (MK_COMB (@lem4627123) (@lem4627122 s)). Qed.
Lemma lem4627125 (N : nat) (s : nat -> Prop) : (term174 s N) = (term46 N s).
Proof. exact (eq_refl (term174 s N)). Qed.
Lemma lem4627126 (n : nat -> nat) (N : nat) : (n N) = (n N).
Proof. exact (eq_refl (n N)). Qed.
Lemma lem4627127 (s : nat -> Prop) (n : nat -> nat) (N : nat) : (term181 s n N) = (term182 s n N).
Proof. exact (MK_COMB (@lem4627125 N s) (@lem4627126 n N)). Qed.
Lemma lem4627128 (n : nat -> nat) (N : nat) (s : nat -> Prop) : (term182 s n N) = (term183 n N s).
Proof. exact (eq_refl (term182 s n N)). Qed.
Lemma lem4627129 (n : nat -> nat) (N : nat) (s : nat -> Prop) : (term181 s n N) = (term183 n N s).
Proof. exact (TRANS (@lem4627127 s n N) (@lem4627128 n N s)). Qed.
Lemma lem4627130 (n : nat -> nat) (s : nat -> Prop) : (term184 s n) = (term185 n s).
Proof. exact (fun_ext (fun N : nat => @lem4627129 n N s)). Qed.
Lemma lem4627131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627132 (n : nat -> nat) (s : nat -> Prop) : (term186 s n) = (term187 n s).
Proof. exact (MK_COMB (@lem4627131) (@lem4627130 n s)). Qed.
Lemma lem4627133 (s : nat -> Prop) : (term188 s) = (term189 s).
Proof. exact (fun_ext (fun n : nat -> nat => @lem4627132 n s)). Qed.
Lemma lem4627134 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627135 (s : nat -> Prop) : (term172 s) = (term190 s).
Proof. exact (MK_COMB (@lem4627134) (@lem4627133 s)). Qed.
Lemma lem4627136 (s : nat -> Prop) : ((term171 s) = (term172 s)) = ((term8 s) = (term190 s)).
Proof. exact (MK_COMB (@lem4627124 s) (@lem4627135 s)). Qed.
Lemma lem4627137 (s : nat -> Prop) : (term8 s) = (term190 s).
Proof. exact (EQ_MP (@lem4627136 s) (@lem4627111 s)). Qed.
Lemma lem4627138 (s : nat -> Prop) : (term95 s) = (term95 s).
Proof. exact (eq_refl (term95 s)). Qed.
Lemma lem4627139 (s : nat -> Prop) : (term97 s) = (term191 s).
Proof. exact (MK_COMB (@lem4627138 s) (@lem4627137 s)). Qed.
Lemma lem4627141 {A : Type'} (P : A -> Prop) (Q : Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4627142 (P : nat -> Prop) (Q : Prop) : (term192 P Q) = (term193 P Q).
Proof. exact (@lem4627141 nat P Q). Qed.
Lemma lem4627143 (s : nat -> Prop) : (term194 s) = (term195 s).
Proof. exact (@lem4627142 (term75 s) (term190 s)). Qed.
Lemma lem4627144 (s : nat -> Prop) (a : nat) : (term196 s a) = (term66 s a).
Proof. exact (eq_refl (term196 s a)). Qed.
Lemma lem4627145 (s : nat -> Prop) : (term197 s) = (term75 s).
Proof. exact (fun_ext (fun a : nat => @lem4627144 s a)). Qed.
Lemma lem4627146 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627147 (s : nat -> Prop) : (term198 s) = (term76 s).
Proof. exact (MK_COMB (@lem4627146) (@lem4627145 s)). Qed.
Lemma lem4627148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627149 (s : nat -> Prop) : (term199 s) = (term95 s).
Proof. exact (MK_COMB (@lem4627148) (@lem4627147 s)). Qed.
Lemma lem4627150 (s : nat -> Prop) : (term190 s) = (term190 s).
Proof. exact (eq_refl (term190 s)). Qed.
Lemma lem4627151 (s : nat -> Prop) : (term194 s) = (term191 s).
Proof. exact (MK_COMB (@lem4627149 s) (@lem4627150 s)). Qed.
Lemma lem4627152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627153 (s : nat -> Prop) : (term200 s) = (term201 s).
Proof. exact (MK_COMB (@lem4627152) (@lem4627151 s)). Qed.
Lemma lem4627154 (s : nat -> Prop) (a : nat) : (term196 s a) = (term66 s a).
Proof. exact (eq_refl (term196 s a)). Qed.
Lemma lem4627155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627156 (s : nat -> Prop) (a : nat) : (term202 s a) = (term203 s a).
Proof. exact (MK_COMB (@lem4627155) (@lem4627154 s a)). Qed.
Lemma lem4627157 (s : nat -> Prop) : (term190 s) = (term190 s).
Proof. exact (eq_refl (term190 s)). Qed.
Lemma lem4627158 (a : nat) (s : nat -> Prop) : (term204 a s) = (term205 a s).
Proof. exact (MK_COMB (@lem4627156 s a) (@lem4627157 s)). Qed.
Lemma lem4627159 (s : nat -> Prop) : (term206 s) = (term207 s).
Proof. exact (fun_ext (fun a : nat => @lem4627158 a s)). Qed.
Lemma lem4627160 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627161 (s : nat -> Prop) : (term195 s) = (term208 s).
Proof. exact (MK_COMB (@lem4627160) (@lem4627159 s)). Qed.
Lemma lem4627162 (s : nat -> Prop) : ((term194 s) = (term195 s)) = ((term191 s) = (term208 s)).
Proof. exact (MK_COMB (@lem4627153 s) (@lem4627161 s)). Qed.
Lemma lem4627163 (s : nat -> Prop) : (term191 s) = (term208 s).
Proof. exact (EQ_MP (@lem4627162 s) (@lem4627143 s)). Qed.
Lemma lem4627165 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4627166 (P : Prop) (Q : type1002) : (term209 P Q) = (term210 P Q).
Proof. exact (@lem4627165 (nat -> nat) P Q). Qed.
Lemma lem4627167 (a : nat) (s : nat -> Prop) : (term211 a s) = (term212 a s).
Proof. exact (@lem4627166 (term66 s a) (term189 s)). Qed.
Lemma lem4627168 (n : nat -> nat) (s : nat -> Prop) : (term213 s n) = (term187 n s).
Proof. exact (eq_refl (term213 s n)). Qed.
Lemma lem4627169 (s : nat -> Prop) : (term214 s) = (term189 s).
Proof. exact (fun_ext (fun n : nat -> nat => @lem4627168 n s)). Qed.
Lemma lem4627170 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627171 (s : nat -> Prop) : (term215 s) = (term190 s).
Proof. exact (MK_COMB (@lem4627170) (@lem4627169 s)). Qed.
Lemma lem4627172 (s : nat -> Prop) (a : nat) : (term203 s a) = (term203 s a).
Proof. exact (eq_refl (term203 s a)). Qed.
Lemma lem4627173 (a : nat) (s : nat -> Prop) : (term211 a s) = (term205 a s).
Proof. exact (MK_COMB (@lem4627172 s a) (@lem4627171 s)). Qed.
Lemma lem4627174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627175 (a : nat) (s : nat -> Prop) : (term216 a s) = (term217 a s).
Proof. exact (MK_COMB (@lem4627174) (@lem4627173 a s)). Qed.
Lemma lem4627176 (n : nat -> nat) (s : nat -> Prop) : (term213 s n) = (term187 n s).
Proof. exact (eq_refl (term213 s n)). Qed.
Lemma lem4627177 (s : nat -> Prop) (a : nat) : (term203 s a) = (term203 s a).
Proof. exact (eq_refl (term203 s a)). Qed.
Lemma lem4627178 (a : nat) (n : nat -> nat) (s : nat -> Prop) : (term218 a s n) = (term219 a n s).
Proof. exact (MK_COMB (@lem4627177 s a) (@lem4627176 n s)). Qed.
Lemma lem4627179 (a : nat) (s : nat -> Prop) : (term220 a s) = (term221 a s).
Proof. exact (fun_ext (fun n : nat -> nat => @lem4627178 a n s)). Qed.
Lemma lem4627180 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627181 (a : nat) (s : nat -> Prop) : (term212 a s) = (term222 a s).
Proof. exact (MK_COMB (@lem4627180) (@lem4627179 a s)). Qed.
Lemma lem4627182 (a : nat) (s : nat -> Prop) : ((term211 a s) = (term212 a s)) = ((term205 a s) = (term222 a s)).
Proof. exact (MK_COMB (@lem4627175 a s) (@lem4627181 a s)). Qed.
Lemma lem4627183 (a : nat) (s : nat -> Prop) : (term205 a s) = (term222 a s).
Proof. exact (EQ_MP (@lem4627182 a s) (@lem4627167 a s)). Qed.
Lemma lem4627184 (s : nat -> Prop) : (term207 s) = (term223 s).
Proof. exact (fun_ext (fun a : nat => @lem4627183 a s)). Qed.
Lemma lem4627185 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627186 (s : nat -> Prop) : (term208 s) = (term224 s).
Proof. exact (MK_COMB (@lem4627185) (@lem4627184 s)). Qed.
Lemma lem4627187 (s : nat -> Prop) : (term191 s) = (term224 s).
Proof. exact (TRANS (@lem4627163 s) (@lem4627186 s)). Qed.
Lemma lem4627188 (s : nat -> Prop) : (term97 s) = (term224 s).
Proof. exact (TRANS (@lem4627139 s) (@lem4627187 s)). Qed.
Lemma lem4627189 (s : nat -> Prop) : (term105 s) = (term225 s).
Proof. exact (MK_COMB (@lem4627107 s) (@lem4627188 s)). Qed.
Lemma lem4627193 {A : Type'} (P : A -> Prop) (Q : Prop) : (term226 A P Q) = (term227 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4627194 (P : type1002) (Q : Prop) : (term228 P Q) = (term229 P Q).
Proof. exact (@lem4627193 (nat -> nat) P Q). Qed.
Lemma lem4627195 (s : nat -> Prop) : (term230 s) = (term231 s).
Proof. exact (@lem4627194 (term168 s) (term224 s)). Qed.
Lemma lem4627196 (x : nat -> nat) (s : nat -> Prop) : (term232 s x) = (term167 x s).
Proof. exact (eq_refl (term232 s x)). Qed.
Lemma lem4627197 (s : nat -> Prop) : (term233 s) = (term168 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4627196 x s)). Qed.
Lemma lem4627198 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627199 (s : nat -> Prop) : (term234 s) = (term169 s).
Proof. exact (MK_COMB (@lem4627198) (@lem4627197 s)). Qed.
Lemma lem4627200 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4627201 (s : nat -> Prop) : (term235 s) = (term170 s).
Proof. exact (MK_COMB (@lem4627200) (@lem4627199 s)). Qed.
Lemma lem4627202 (s : nat -> Prop) : (term224 s) = (term224 s).
Proof. exact (eq_refl (term224 s)). Qed.
Lemma lem4627203 (s : nat -> Prop) : (term230 s) = (term225 s).
Proof. exact (MK_COMB (@lem4627201 s) (@lem4627202 s)). Qed.
Lemma lem4627204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627205 (s : nat -> Prop) : (term236 s) = (term237 s).
Proof. exact (MK_COMB (@lem4627204) (@lem4627203 s)). Qed.
Lemma lem4627206 (x : nat -> nat) (s : nat -> Prop) : (term232 s x) = (term167 x s).
Proof. exact (eq_refl (term232 s x)). Qed.
Lemma lem4627207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4627208 (x : nat -> nat) (s : nat -> Prop) : (term238 s x) = (term239 x s).
Proof. exact (MK_COMB (@lem4627207) (@lem4627206 x s)). Qed.
Lemma lem4627209 (s : nat -> Prop) : (term224 s) = (term224 s).
Proof. exact (eq_refl (term224 s)). Qed.
Lemma lem4627210 (x : nat -> nat) (s : nat -> Prop) : (term240 x s) = (term241 x s).
Proof. exact (MK_COMB (@lem4627208 x s) (@lem4627209 s)). Qed.
Lemma lem4627211 (s : nat -> Prop) : (term242 s) = (term243 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4627210 x s)). Qed.
Lemma lem4627212 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627213 (s : nat -> Prop) : (term231 s) = (term244 s).
Proof. exact (MK_COMB (@lem4627212) (@lem4627211 s)). Qed.
Lemma lem4627214 (s : nat -> Prop) : ((term230 s) = (term231 s)) = ((term225 s) = (term244 s)).
Proof. exact (MK_COMB (@lem4627205 s) (@lem4627213 s)). Qed.
Lemma lem4627215 (s : nat -> Prop) : (term225 s) = (term244 s).
Proof. exact (EQ_MP (@lem4627214 s) (@lem4627195 s)). Qed.
Lemma lem4627217 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4627218 (P : nat -> Prop) (Q : nat -> Prop) : (term247 P Q) = (term248 P Q).
Proof. exact (@lem4627217 nat P Q). Qed.
Lemma lem4627219 (x : nat -> nat) (s : nat -> Prop) : (term249 x s) = (term250 x s).
Proof. exact (@lem4627218 (term166 x s) (term223 s)). Qed.
Lemma lem4627220 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term251 x s N) = (term164 x N s).
Proof. exact (eq_refl (term251 x s N)). Qed.
Lemma lem4627221 (x : nat -> nat) (s : nat -> Prop) : (term252 x s) = (term166 x s).
Proof. exact (fun_ext (fun N : nat => @lem4627220 x N s)). Qed.
Lemma lem4627222 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627223 (x : nat -> nat) (s : nat -> Prop) : (term253 x s) = (term167 x s).
Proof. exact (MK_COMB (@lem4627222) (@lem4627221 x s)). Qed.
Lemma lem4627224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4627225 (x : nat -> nat) (s : nat -> Prop) : (term254 x s) = (term239 x s).
Proof. exact (MK_COMB (@lem4627224) (@lem4627223 x s)). Qed.
Lemma lem4627226 (N : nat) (s : nat -> Prop) : (term255 s N) = (term222 N s).
Proof. exact (eq_refl (term255 s N)). Qed.
Lemma lem4627227 (s : nat -> Prop) : (term256 s) = (term223 s).
Proof. exact (fun_ext (fun N : nat => @lem4627226 N s)). Qed.
Lemma lem4627228 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627229 (s : nat -> Prop) : (term257 s) = (term224 s).
Proof. exact (MK_COMB (@lem4627228) (@lem4627227 s)). Qed.
Lemma lem4627230 (x : nat -> nat) (s : nat -> Prop) : (term249 x s) = (term241 x s).
Proof. exact (MK_COMB (@lem4627225 x s) (@lem4627229 s)). Qed.
Lemma lem4627231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627232 (x : nat -> nat) (s : nat -> Prop) : (term258 x s) = (term259 x s).
Proof. exact (MK_COMB (@lem4627231) (@lem4627230 x s)). Qed.
Lemma lem4627233 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term251 x s N) = (term164 x N s).
Proof. exact (eq_refl (term251 x s N)). Qed.
Lemma lem4627234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4627235 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term260 x s N) = (term261 x N s).
Proof. exact (MK_COMB (@lem4627234) (@lem4627233 x N s)). Qed.
Lemma lem4627236 (N : nat) (s : nat -> Prop) : (term255 s N) = (term222 N s).
Proof. exact (eq_refl (term255 s N)). Qed.
Lemma lem4627237 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term262 x s N) = (term263 x N s).
Proof. exact (MK_COMB (@lem4627235 x N s) (@lem4627236 N s)). Qed.
Lemma lem4627238 (x : nat -> nat) (s : nat -> Prop) : (term264 x s) = (term265 x s).
Proof. exact (fun_ext (fun N : nat => @lem4627237 x N s)). Qed.
Lemma lem4627239 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627240 (x : nat -> nat) (s : nat -> Prop) : (term250 x s) = (term266 x s).
Proof. exact (MK_COMB (@lem4627239) (@lem4627238 x s)). Qed.
Lemma lem4627241 (x : nat -> nat) (s : nat -> Prop) : ((term249 x s) = (term250 x s)) = ((term241 x s) = (term266 x s)).
Proof. exact (MK_COMB (@lem4627232 x s) (@lem4627240 x s)). Qed.
Lemma lem4627242 (x : nat -> nat) (s : nat -> Prop) : (term241 x s) = (term266 x s).
Proof. exact (EQ_MP (@lem4627241 x s) (@lem4627219 x s)). Qed.
Lemma lem4627245 (x : nat -> nat) (s : nat -> Prop) : (term267 x s) = (term267 x s).
Proof. exact (eq_refl (term267 x s)). Qed.
Lemma lem4627246 (x : nat -> nat) (s : nat -> Prop) : (term267 x s) = ((term241 x s) = (term266 x s)).
Proof. exact (eq_refl (term267 x s)). Qed.
Lemma lem4627247 (x : nat -> nat) (s : nat -> Prop) : (term268 x s) = (term268 x s).
Proof. exact (eq_refl (term268 x s)). Qed.
Lemma lem4627248 (x : nat -> nat) (s : nat -> Prop) : ((term267 x s) = (term267 x s)) = ((term267 x s) = ((term241 x s) = (term266 x s))).
Proof. exact (MK_COMB (@lem4627247 x s) (@lem4627246 x s)). Qed.
Lemma lem4627249 (x : nat -> nat) (s : nat -> Prop) : (term267 x s) = ((term241 x s) = (term266 x s)).
Proof. exact (eq_refl (term267 x s)). Qed.
Lemma lem4627250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627251 (x : nat -> nat) (s : nat -> Prop) : (term268 x s) = (term269 x s).
Proof. exact (MK_COMB (@lem4627250) (@lem4627249 x s)). Qed.
Lemma lem4627252 (x : nat -> nat) (s : nat -> Prop) : ((term241 x s) = (term266 x s)) = ((term241 x s) = (term266 x s)).
Proof. exact (eq_refl ((term241 x s) = (term266 x s))). Qed.
Lemma lem4627253 (x : nat -> nat) (s : nat -> Prop) : ((term267 x s) = ((term241 x s) = (term266 x s))) = (((term241 x s) = (term266 x s)) = ((term241 x s) = (term266 x s))).
Proof. exact (MK_COMB (@lem4627251 x s) (@lem4627252 x s)). Qed.
Lemma lem4627254 (x : nat -> nat) (s : nat -> Prop) : ((term267 x s) = (term267 x s)) = (((term241 x s) = (term266 x s)) = ((term241 x s) = (term266 x s))).
Proof. exact (TRANS (@lem4627248 x s) (@lem4627253 x s)). Qed.
Lemma lem4627255 (x : nat -> nat) (s : nat -> Prop) : ((term241 x s) = (term266 x s)) = ((term241 x s) = (term266 x s)).
Proof. exact (EQ_MP (@lem4627254 x s) (@lem4627245 x s)). Qed.
Lemma lem4627256 (x : nat -> nat) (s : nat -> Prop) : (term241 x s) = (term266 x s).
Proof. exact (EQ_MP (@lem4627255 x s) (@lem4627242 x s)). Qed.
Lemma lem4627258 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4627259 (P : Prop) (Q : type1002) : (term272 P Q) = (term273 P Q).
Proof. exact (@lem4627258 (nat -> nat) P Q). Qed.
Lemma lem4627260 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term274 x N s) = (term275 x N s).
Proof. exact (@lem4627259 (term164 x N s) (term221 N s)). Qed.
Lemma lem4627261 (N : nat) (n : nat -> nat) (s : nat -> Prop) : (term276 N s n) = (term219 N n s).
Proof. exact (eq_refl (term276 N s n)). Qed.
Lemma lem4627262 (N : nat) (s : nat -> Prop) : (term277 N s) = (term221 N s).
Proof. exact (fun_ext (fun n : nat -> nat => @lem4627261 N n s)). Qed.
Lemma lem4627263 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627264 (N : nat) (s : nat -> Prop) : (term278 N s) = (term222 N s).
Proof. exact (MK_COMB (@lem4627263) (@lem4627262 N s)). Qed.
Lemma lem4627265 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term261 x N s) = (term261 x N s).
Proof. exact (eq_refl (term261 x N s)). Qed.
Lemma lem4627266 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term274 x N s) = (term263 x N s).
Proof. exact (MK_COMB (@lem4627265 x N s) (@lem4627264 N s)). Qed.
Lemma lem4627267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627268 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term279 x N s) = (term280 x N s).
Proof. exact (MK_COMB (@lem4627267) (@lem4627266 x N s)). Qed.
Lemma lem4627269 (N : nat) (n : nat -> nat) (s : nat -> Prop) : (term276 N s n) = (term219 N n s).
Proof. exact (eq_refl (term276 N s n)). Qed.
Lemma lem4627270 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term261 x N s) = (term261 x N s).
Proof. exact (eq_refl (term261 x N s)). Qed.
Lemma lem4627271 (x : nat -> nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) : (term281 x N s n) = (term282 x N n s).
Proof. exact (MK_COMB (@lem4627270 x N s) (@lem4627269 N n s)). Qed.
Lemma lem4627272 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term283 x N s) = (term284 x N s).
Proof. exact (fun_ext (fun n : nat -> nat => @lem4627271 x N n s)). Qed.
Lemma lem4627273 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627274 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term275 x N s) = (term285 x N s).
Proof. exact (MK_COMB (@lem4627273) (@lem4627272 x N s)). Qed.
Lemma lem4627275 (x : nat -> nat) (N : nat) (s : nat -> Prop) : ((term274 x N s) = (term275 x N s)) = ((term263 x N s) = (term285 x N s)).
Proof. exact (MK_COMB (@lem4627268 x N s) (@lem4627274 x N s)). Qed.
Lemma lem4627276 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term263 x N s) = (term285 x N s).
Proof. exact (EQ_MP (@lem4627275 x N s) (@lem4627260 x N s)). Qed.
Lemma lem4627277 (x : nat -> nat) (s : nat -> Prop) : (term265 x s) = (term286 x s).
Proof. exact (fun_ext (fun N : nat => @lem4627276 x N s)). Qed.
Lemma lem4627278 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4627279 (x : nat -> nat) (s : nat -> Prop) : (term266 x s) = (term287 x s).
Proof. exact (MK_COMB (@lem4627278) (@lem4627277 x s)). Qed.
Lemma lem4627280 (x : nat -> nat) (s : nat -> Prop) : (term241 x s) = (term287 x s).
Proof. exact (TRANS (@lem4627256 x s) (@lem4627279 x s)). Qed.
Lemma lem4627281 (s : nat -> Prop) : (term243 s) = (term288 s).
Proof. exact (fun_ext (fun x : nat -> nat => @lem4627280 x s)). Qed.
Lemma lem4627282 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4627283 (s : nat -> Prop) : (term244 s) = (term289 s).
Proof. exact (MK_COMB (@lem4627282) (@lem4627281 s)). Qed.
Lemma lem4627284 (s : nat -> Prop) : (term225 s) = (term289 s).
Proof. exact (TRANS (@lem4627215 s) (@lem4627283 s)). Qed.
Lemma lem4627286 (s : nat -> Prop) : (term105 s) = (term289 s).
Proof. exact (TRANS (@lem4627189 s) (@lem4627284 s)). Qed.
Lemma lem4627287 (s : nat -> Prop) : (term11 s) = (term289 s).
Proof. exact (TRANS (@lem4626813 s) (@lem4627286 s)). Qed.
Lemma lem4627288 (s : nat -> Prop) (h1 : term11 s) : term289 s.
Proof. exact (EQ_MP (@lem4627287 s) (@lem4626719 s h1)). Qed.
Lemma lem4627303 (m : nat) (n : nat) : ((term40 m n) = (Peano.lt m n)) = (term290 m n).
Proof. exact (@lem17784 (term40 m n) (Peano.lt m n)). Qed.
Lemma lem4627304 (m : nat) : (term41 m) = (term291 m).
Proof. exact (fun_ext (fun n : nat => @lem4627303 m n)). Qed.
Lemma lem4627305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627306 (m : nat) : (term42 m) = (term292 m).
Proof. exact (MK_COMB (@lem4627305) (@lem4627304 m)). Qed.
Lemma lem4627307 : term43 = term293.
Proof. exact (fun_ext (fun m : nat => @lem4627306 m)). Qed.
Lemma lem4627308 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627309 : term44 = term294.
Proof. exact (MK_COMB (@lem4627308) (@lem4627307)). Qed.
Lemma lem4627315 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term296 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4627316 (P : nat -> Prop) (Q : nat -> Prop) : (term297 P Q) = (term298 P Q).
Proof. exact (@lem4627315 nat P Q). Qed.
Lemma lem4627317 (m : nat) : (term299 m) = (term300 m).
Proof. exact (@lem4627316 (term301 m) (term302 m)). Qed.
Lemma lem4627318 (m : nat) (n : nat) : (term303 m n) = (term304 m n).
Proof. exact (eq_refl (term303 m n)). Qed.
Lemma lem4627319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627320 (m : nat) (n : nat) : (term305 m n) = (term306 m n).
Proof. exact (MK_COMB (@lem4627319) (@lem4627318 m n)). Qed.
Lemma lem4627321 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (eq_refl (term307 m n)). Qed.
Lemma lem4627322 (m : nat) (n : nat) : (term309 m n) = (term290 m n).
Proof. exact (MK_COMB (@lem4627320 m n) (@lem4627321 m n)). Qed.
Lemma lem4627323 (m : nat) : (term310 m) = (term291 m).
Proof. exact (fun_ext (fun n : nat => @lem4627322 m n)). Qed.
Lemma lem4627324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627325 (m : nat) : (term299 m) = (term292 m).
Proof. exact (MK_COMB (@lem4627324) (@lem4627323 m)). Qed.
Lemma lem4627326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627327 (m : nat) : (term311 m) = (term312 m).
Proof. exact (MK_COMB (@lem4627326) (@lem4627325 m)). Qed.
Lemma lem4627328 (m : nat) (n : nat) : (term303 m n) = (term304 m n).
Proof. exact (eq_refl (term303 m n)). Qed.
Lemma lem4627329 (m : nat) : (term313 m) = (term301 m).
Proof. exact (fun_ext (fun n : nat => @lem4627328 m n)). Qed.
Lemma lem4627330 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627331 (m : nat) : (term314 m) = (term315 m).
Proof. exact (MK_COMB (@lem4627330) (@lem4627329 m)). Qed.
Lemma lem4627332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627333 (m : nat) : (term316 m) = (term317 m).
Proof. exact (MK_COMB (@lem4627332) (@lem4627331 m)). Qed.
Lemma lem4627334 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (eq_refl (term307 m n)). Qed.
Lemma lem4627335 (m : nat) : (term318 m) = (term302 m).
Proof. exact (fun_ext (fun n : nat => @lem4627334 m n)). Qed.
Lemma lem4627336 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627337 (m : nat) : (term319 m) = (term320 m).
Proof. exact (MK_COMB (@lem4627336) (@lem4627335 m)). Qed.
Lemma lem4627338 (m : nat) : (term300 m) = (term321 m).
Proof. exact (MK_COMB (@lem4627333 m) (@lem4627337 m)). Qed.
Lemma lem4627339 (m : nat) : ((term299 m) = (term300 m)) = ((term292 m) = (term321 m)).
Proof. exact (MK_COMB (@lem4627327 m) (@lem4627338 m)). Qed.
Lemma lem4627340 (m : nat) : (term292 m) = (term321 m).
Proof. exact (EQ_MP (@lem4627339 m) (@lem4627317 m)). Qed.
Lemma lem4627437 : term293 = term322.
Proof. exact (fun_ext (fun m : nat => @lem4627340 m)). Qed.
Lemma lem4627438 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627439 : term294 = term323.
Proof. exact (MK_COMB (@lem4627438) (@lem4627437)). Qed.
Lemma lem4627441 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term296 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4627442 (P : nat -> Prop) (Q : nat -> Prop) : (term297 P Q) = (term298 P Q).
Proof. exact (@lem4627441 nat P Q). Qed.
Lemma lem4627443 : term324 = term325.
Proof. exact (@lem4627442 term326 term327). Qed.
Lemma lem4627444 (m : nat) : (term328 m) = (term315 m).
Proof. exact (eq_refl (term328 m)). Qed.
Lemma lem4627445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627446 (m : nat) : (term329 m) = (term317 m).
Proof. exact (MK_COMB (@lem4627445) (@lem4627444 m)). Qed.
Lemma lem4627447 (m : nat) : (term330 m) = (term320 m).
Proof. exact (eq_refl (term330 m)). Qed.
Lemma lem4627448 (m : nat) : (term331 m) = (term321 m).
Proof. exact (MK_COMB (@lem4627446 m) (@lem4627447 m)). Qed.
Lemma lem4627449 : term332 = term322.
Proof. exact (fun_ext (fun m : nat => @lem4627448 m)). Qed.
Lemma lem4627450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627451 : term324 = term323.
Proof. exact (MK_COMB (@lem4627450) (@lem4627449)). Qed.
Lemma lem4627452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627453 : term333 = term334.
Proof. exact (MK_COMB (@lem4627452) (@lem4627451)). Qed.
Lemma lem4627454 (m : nat) : (term328 m) = (term315 m).
Proof. exact (eq_refl (term328 m)). Qed.
Lemma lem4627455 : term335 = term326.
Proof. exact (fun_ext (fun m : nat => @lem4627454 m)). Qed.
Lemma lem4627456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627457 : term336 = term337.
Proof. exact (MK_COMB (@lem4627456) (@lem4627455)). Qed.
Lemma lem4627458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627459 : term338 = term339.
Proof. exact (MK_COMB (@lem4627458) (@lem4627457)). Qed.
Lemma lem4627460 (m : nat) : (term330 m) = (term320 m).
Proof. exact (eq_refl (term330 m)). Qed.
Lemma lem4627461 : term340 = term327.
Proof. exact (fun_ext (fun m : nat => @lem4627460 m)). Qed.
Lemma lem4627462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627463 : term341 = term342.
Proof. exact (MK_COMB (@lem4627462) (@lem4627461)). Qed.
Lemma lem4627464 : term325 = term343.
Proof. exact (MK_COMB (@lem4627459) (@lem4627463)). Qed.
Lemma lem4627465 : (term324 = term325) = (term323 = term343).
Proof. exact (MK_COMB (@lem4627453) (@lem4627464)). Qed.
Lemma lem4627466 : term323 = term343.
Proof. exact (EQ_MP (@lem4627465) (@lem4627443)). Qed.
Lemma lem4627573 : term294 = term343.
Proof. exact (TRANS (@lem4627439) (@lem4627466)). Qed.
Lemma lem4627574 : term44 = term343.
Proof. exact (TRANS (@lem4627309) (@lem4627573)). Qed.
Lemma lem4627575 (h1 : term44) : term343.
Proof. exact (EQ_MP (@lem4627574) (@lem4626720 h1)). Qed.
Lemma lem4627582 (m : nat) (n : nat) : (term35 m n) = (term344 m n).
Proof. exact (@lem17265 (Peano.lt m n) (Peano.le m n)). Qed.
Lemma lem4627583 (m : nat) : (term36 m) = (term345 m).
Proof. exact (fun_ext (fun n : nat => @lem4627582 m n)). Qed.
Lemma lem4627584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627585 (m : nat) : (term37 m) = (term346 m).
Proof. exact (MK_COMB (@lem4627584) (@lem4627583 m)). Qed.
Lemma lem4627586 : term38 = term347.
Proof. exact (fun_ext (fun m : nat => @lem4627585 m)). Qed.
Lemma lem4627587 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627644 : term39 = term348.
Proof. exact (MK_COMB (@lem4627587) (@lem4627586)). Qed.
Lemma lem4627645 (h1 : term39) : term348.
Proof. exact (EQ_MP (@lem4627644) (@lem4626721 h1)). Qed.
Lemma lem4627649 (m : nat) (n : nat) : (term349 m n) = (Peano.le m n).
Proof. exact (@lem16933 (Peano.le m n)). Qed.
Lemma lem4627651 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem4627652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4627653 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (MK_COMB (@lem4627652) (@lem4627649 m n)). Qed.
Lemma lem4627654 (n : nat) (m : nat) : (term352 n m) = (term353 n m).
Proof. exact (MK_COMB (@lem4627653 m n) (@lem4627651 n m)). Qed.
Lemma lem4627659 (n : nat) (m : nat) : (term354 n m) = (term354 n m).
Proof. exact (eq_refl (term354 n m)). Qed.
Lemma lem4627660 (n : nat) (m : nat) : (term355 n m) = (term356 n m).
Proof. exact (MK_COMB (@lem4627659 n m) (@lem4627654 n m)). Qed.
Lemma lem4627661 (n : nat) (m : nat) : ((term31 m n) = (Peano.lt n m)) = (term355 n m).
Proof. exact (@lem17784 (term31 m n) (Peano.lt n m)). Qed.
Lemma lem4627662 (n : nat) (m : nat) : ((term31 m n) = (Peano.lt n m)) = (term356 n m).
Proof. exact (TRANS (@lem4627661 n m) (@lem4627660 n m)). Qed.
Lemma lem4627663 (m : nat) : (term32 m) = (term357 m).
Proof. exact (fun_ext (fun n : nat => @lem4627662 n m)). Qed.
Lemma lem4627664 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627665 (m : nat) : (term33 m) = (term358 m).
Proof. exact (MK_COMB (@lem4627664) (@lem4627663 m)). Qed.
Lemma lem4627666 : term34 = term359.
Proof. exact (fun_ext (fun m : nat => @lem4627665 m)). Qed.
Lemma lem4627667 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627668 : term18 = term360.
Proof. exact (MK_COMB (@lem4627667) (@lem4627666)). Qed.
Lemma lem4627674 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term296 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4627675 (P : nat -> Prop) (Q : nat -> Prop) : (term297 P Q) = (term298 P Q).
Proof. exact (@lem4627674 nat P Q). Qed.
Lemma lem4627676 (m : nat) : (term361 m) = (term362 m).
Proof. exact (@lem4627675 (term363 m) (term364 m)). Qed.
Lemma lem4627677 (n : nat) (m : nat) : (term365 m n) = (term366 n m).
Proof. exact (eq_refl (term365 m n)). Qed.
Lemma lem4627678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627679 (n : nat) (m : nat) : (term367 m n) = (term354 n m).
Proof. exact (MK_COMB (@lem4627678) (@lem4627677 n m)). Qed.
Lemma lem4627680 (n : nat) (m : nat) : (term368 m n) = (term353 n m).
Proof. exact (eq_refl (term368 m n)). Qed.
Lemma lem4627681 (n : nat) (m : nat) : (term369 m n) = (term356 n m).
Proof. exact (MK_COMB (@lem4627679 n m) (@lem4627680 n m)). Qed.
Lemma lem4627682 (m : nat) : (term370 m) = (term357 m).
Proof. exact (fun_ext (fun n : nat => @lem4627681 n m)). Qed.
Lemma lem4627683 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627684 (m : nat) : (term361 m) = (term358 m).
Proof. exact (MK_COMB (@lem4627683) (@lem4627682 m)). Qed.
Lemma lem4627685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627686 (m : nat) : (term371 m) = (term372 m).
Proof. exact (MK_COMB (@lem4627685) (@lem4627684 m)). Qed.
Lemma lem4627687 (n : nat) (m : nat) : (term365 m n) = (term366 n m).
Proof. exact (eq_refl (term365 m n)). Qed.
Lemma lem4627688 (m : nat) : (term373 m) = (term363 m).
Proof. exact (fun_ext (fun n : nat => @lem4627687 n m)). Qed.
Lemma lem4627689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627690 (m : nat) : (term374 m) = (term375 m).
Proof. exact (MK_COMB (@lem4627689) (@lem4627688 m)). Qed.
Lemma lem4627691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627692 (m : nat) : (term376 m) = (term377 m).
Proof. exact (MK_COMB (@lem4627691) (@lem4627690 m)). Qed.
Lemma lem4627693 (n : nat) (m : nat) : (term368 m n) = (term353 n m).
Proof. exact (eq_refl (term368 m n)). Qed.
Lemma lem4627694 (m : nat) : (term378 m) = (term364 m).
Proof. exact (fun_ext (fun n : nat => @lem4627693 n m)). Qed.
Lemma lem4627695 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627696 (m : nat) : (term379 m) = (term380 m).
Proof. exact (MK_COMB (@lem4627695) (@lem4627694 m)). Qed.
Lemma lem4627697 (m : nat) : (term362 m) = (term381 m).
Proof. exact (MK_COMB (@lem4627692 m) (@lem4627696 m)). Qed.
Lemma lem4627698 (m : nat) : ((term361 m) = (term362 m)) = ((term358 m) = (term381 m)).
Proof. exact (MK_COMB (@lem4627686 m) (@lem4627697 m)). Qed.
Lemma lem4627699 (m : nat) : (term358 m) = (term381 m).
Proof. exact (EQ_MP (@lem4627698 m) (@lem4627676 m)). Qed.
Lemma lem4627796 : term359 = term382.
Proof. exact (fun_ext (fun m : nat => @lem4627699 m)). Qed.
Lemma lem4627797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627798 : term360 = term383.
Proof. exact (MK_COMB (@lem4627797) (@lem4627796)). Qed.
Lemma lem4627800 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term296 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4627801 (P : nat -> Prop) (Q : nat -> Prop) : (term297 P Q) = (term298 P Q).
Proof. exact (@lem4627800 nat P Q). Qed.
Lemma lem4627802 : term384 = term385.
Proof. exact (@lem4627801 term386 term387). Qed.
Lemma lem4627803 (m : nat) : (term388 m) = (term375 m).
Proof. exact (eq_refl (term388 m)). Qed.
Lemma lem4627804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627805 (m : nat) : (term389 m) = (term377 m).
Proof. exact (MK_COMB (@lem4627804) (@lem4627803 m)). Qed.
Lemma lem4627806 (m : nat) : (term390 m) = (term380 m).
Proof. exact (eq_refl (term390 m)). Qed.
Lemma lem4627807 (m : nat) : (term391 m) = (term381 m).
Proof. exact (MK_COMB (@lem4627805 m) (@lem4627806 m)). Qed.
Lemma lem4627808 : term392 = term382.
Proof. exact (fun_ext (fun m : nat => @lem4627807 m)). Qed.
Lemma lem4627809 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627810 : term384 = term383.
Proof. exact (MK_COMB (@lem4627809) (@lem4627808)). Qed.
Lemma lem4627811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4627812 : term393 = term394.
Proof. exact (MK_COMB (@lem4627811) (@lem4627810)). Qed.
Lemma lem4627813 (m : nat) : (term388 m) = (term375 m).
Proof. exact (eq_refl (term388 m)). Qed.
Lemma lem4627814 : term395 = term386.
Proof. exact (fun_ext (fun m : nat => @lem4627813 m)). Qed.
Lemma lem4627815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627816 : term396 = term397.
Proof. exact (MK_COMB (@lem4627815) (@lem4627814)). Qed.
Lemma lem4627817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627818 : term398 = term399.
Proof. exact (MK_COMB (@lem4627817) (@lem4627816)). Qed.
Lemma lem4627819 (m : nat) : (term390 m) = (term380 m).
Proof. exact (eq_refl (term390 m)). Qed.
Lemma lem4627820 : term400 = term387.
Proof. exact (fun_ext (fun m : nat => @lem4627819 m)). Qed.
Lemma lem4627821 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627822 : term401 = term402.
Proof. exact (MK_COMB (@lem4627821) (@lem4627820)). Qed.
Lemma lem4627823 : term385 = term403.
Proof. exact (MK_COMB (@lem4627818) (@lem4627822)). Qed.
Lemma lem4627824 : (term384 = term385) = (term383 = term403).
Proof. exact (MK_COMB (@lem4627812) (@lem4627823)). Qed.
Lemma lem4627825 : term383 = term403.
Proof. exact (EQ_MP (@lem4627824) (@lem4627802)). Qed.
Lemma lem4627932 : term360 = term403.
Proof. exact (TRANS (@lem4627798) (@lem4627825)). Qed.
Lemma lem4627933 : term18 = term403.
Proof. exact (TRANS (@lem4627668) (@lem4627932)). Qed.
Lemma lem4627934 (h1 : term18) : term403.
Proof. exact (EQ_MP (@lem4627933) (@lem4626722 h1)). Qed.
Lemma lem4627935 (x : nat -> nat) (s : nat -> Prop) (h1 : term287 x s) : term287 x s.
Proof. exact (h1). Qed.
Lemma lem4627936 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term285 x N s) : term285 x N s.
Proof. exact (h1). Qed.
Lemma lem4627937 (x : nat -> nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term282 x N n s) : term282 x N n s.
Proof. exact (h1). Qed.
Lemma lem4627954 (m : nat) (n : nat) : (term308 m n) = (term308 m n).
Proof. exact (eq_refl (term308 m n)). Qed.
Lemma lem4627955 (m : nat) : (term302 m) = (term302 m).
Proof. exact (fun_ext (fun n : nat => @lem4627954 m n)). Qed.
Lemma lem4627956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627957 (m : nat) : (term320 m) = (term320 m).
Proof. exact (MK_COMB (@lem4627956) (@lem4627955 m)). Qed.
Lemma lem4627958 : term327 = term327.
Proof. exact (fun_ext (fun m : nat => @lem4627957 m)). Qed.
Lemma lem4627959 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627960 : term342 = term342.
Proof. exact (MK_COMB (@lem4627959) (@lem4627958)). Qed.
Lemma lem4627977 (m : nat) (n : nat) : (term304 m n) = (term304 m n).
Proof. exact (eq_refl (term304 m n)). Qed.
Lemma lem4627978 (m : nat) : (term301 m) = (term301 m).
Proof. exact (fun_ext (fun n : nat => @lem4627977 m n)). Qed.
Lemma lem4627979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627980 (m : nat) : (term315 m) = (term315 m).
Proof. exact (MK_COMB (@lem4627979) (@lem4627978 m)). Qed.
Lemma lem4627981 : term326 = term326.
Proof. exact (fun_ext (fun m : nat => @lem4627980 m)). Qed.
Lemma lem4627982 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4627983 : term337 = term337.
Proof. exact (MK_COMB (@lem4627982) (@lem4627981)). Qed.
Lemma lem4627984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4627985 : term339 = term339.
Proof. exact (MK_COMB (@lem4627984) (@lem4627983)). Qed.
Lemma lem4627986 : term343 = term343.
Proof. exact (MK_COMB (@lem4627985) (@lem4627960)). Qed.
Lemma lem4627987 (h1 : term44) : term343.
Proof. exact (EQ_MP (@lem4627986) (@lem4627575 h1)). Qed.
Lemma lem4628002 (m : nat) (n : nat) : (term344 m n) = (term344 m n).
Proof. exact (eq_refl (term344 m n)). Qed.
Lemma lem4628003 (m : nat) : (term345 m) = (term345 m).
Proof. exact (fun_ext (fun n : nat => @lem4628002 m n)). Qed.
Lemma lem4628004 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628005 (m : nat) : (term346 m) = (term346 m).
Proof. exact (MK_COMB (@lem4628004) (@lem4628003 m)). Qed.
Lemma lem4628006 : term347 = term347.
Proof. exact (fun_ext (fun m : nat => @lem4628005 m)). Qed.
Lemma lem4628007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628008 : term348 = term348.
Proof. exact (MK_COMB (@lem4628007) (@lem4628006)). Qed.
Lemma lem4628009 (h1 : term39) : term348.
Proof. exact (EQ_MP (@lem4628008) (@lem4627645 h1)). Qed.
Lemma lem4628022 (n : nat) (m : nat) : (term353 n m) = (term353 n m).
Proof. exact (eq_refl (term353 n m)). Qed.
Lemma lem4628023 (m : nat) : (term364 m) = (term364 m).
Proof. exact (fun_ext (fun n : nat => @lem4628022 n m)). Qed.
Lemma lem4628024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628025 (m : nat) : (term380 m) = (term380 m).
Proof. exact (MK_COMB (@lem4628024) (@lem4628023 m)). Qed.
Lemma lem4628026 : term387 = term387.
Proof. exact (fun_ext (fun m : nat => @lem4628025 m)). Qed.
Lemma lem4628027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628028 : term402 = term402.
Proof. exact (MK_COMB (@lem4628027) (@lem4628026)). Qed.
Lemma lem4628045 (n : nat) (m : nat) : (term366 n m) = (term366 n m).
Proof. exact (eq_refl (term366 n m)). Qed.
Lemma lem4628046 (m : nat) : (term363 m) = (term363 m).
Proof. exact (fun_ext (fun n : nat => @lem4628045 n m)). Qed.
Lemma lem4628047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628048 (m : nat) : (term375 m) = (term375 m).
Proof. exact (MK_COMB (@lem4628047) (@lem4628046 m)). Qed.
Lemma lem4628049 : term386 = term386.
Proof. exact (fun_ext (fun m : nat => @lem4628048 m)). Qed.
Lemma lem4628050 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628051 : term397 = term397.
Proof. exact (MK_COMB (@lem4628050) (@lem4628049)). Qed.
Lemma lem4628052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4628053 : term399 = term399.
Proof. exact (MK_COMB (@lem4628052) (@lem4628051)). Qed.
Lemma lem4628054 : term403 = term403.
Proof. exact (MK_COMB (@lem4628053) (@lem4628028)). Qed.
Lemma lem4628055 (h1 : term18) : term403.
Proof. exact (EQ_MP (@lem4628054) (@lem4627934 h1)). Qed.
Lemma lem4628072 (n : nat -> nat) (N : nat) (s : nat -> Prop) : (term183 n N s) = (term183 n N s).
Proof. exact (eq_refl (term183 n N s)). Qed.
Lemma lem4628073 (n : nat -> nat) (s : nat -> Prop) : (term185 n s) = (term185 n s).
Proof. exact (fun_ext (fun N : nat => @lem4628072 n N s)). Qed.
Lemma lem4628074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628075 (n : nat -> nat) (s : nat -> Prop) : (term187 n s) = (term187 n s).
Proof. exact (MK_COMB (@lem4628074) (@lem4628073 n s)). Qed.
Lemma lem4628090 (s : nat -> Prop) (x : nat) (N : nat) : (term55 s x N) = (term55 s x N).
Proof. exact (eq_refl (term55 s x N)). Qed.
Lemma lem4628091 (s : nat -> Prop) (N : nat) : (term65 s N) = (term65 s N).
Proof. exact (fun_ext (fun x : nat => @lem4628090 s x N)). Qed.
Lemma lem4628092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628093 (s : nat -> Prop) (N : nat) : (term66 s N) = (term66 s N).
Proof. exact (MK_COMB (@lem4628092) (@lem4628091 s N)). Qed.
Lemma lem4628094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4628095 (s : nat -> Prop) (N : nat) : (term203 s N) = (term203 s N).
Proof. exact (MK_COMB (@lem4628094) (@lem4628093 s N)). Qed.
Lemma lem4628096 (N : nat) (n : nat -> nat) (s : nat -> Prop) : (term219 N n s) = (term219 N n s).
Proof. exact (MK_COMB (@lem4628095 s N) (@lem4628075 n s)). Qed.
Lemma lem4628113 (N : nat) (n : nat) (s : nat -> Prop) : (term79 N n s) = (term79 N n s).
Proof. exact (eq_refl (term79 N n s)). Qed.
Lemma lem4628114 (N : nat) (s : nat -> Prop) : (term85 N s) = (term85 N s).
Proof. exact (fun_ext (fun n : nat => @lem4628113 N n s)). Qed.
Lemma lem4628115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628116 (N : nat) (s : nat -> Prop) : (term86 N s) = (term86 N s).
Proof. exact (MK_COMB (@lem4628115) (@lem4628114 N s)). Qed.
Lemma lem4628135 (s : nat -> Prop) (x : nat -> nat) (a : nat) : (term123 s x a) = (term123 s x a).
Proof. exact (eq_refl (term123 s x a)). Qed.
Lemma lem4628136 (s : nat -> Prop) (x : nat -> nat) : (term125 s x) = (term125 s x).
Proof. exact (fun_ext (fun a : nat => @lem4628135 s x a)). Qed.
Lemma lem4628137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628138 (s : nat -> Prop) (x : nat -> nat) : (term127 s x) = (term127 s x).
Proof. exact (MK_COMB (@lem4628137) (@lem4628136 s x)). Qed.
Lemma lem4628139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4628140 (s : nat -> Prop) (x : nat -> nat) : (term146 s x) = (term146 s x).
Proof. exact (MK_COMB (@lem4628139) (@lem4628138 s x)). Qed.
Lemma lem4628141 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term164 x N s) = (term164 x N s).
Proof. exact (MK_COMB (@lem4628140 s x) (@lem4628116 N s)). Qed.
Lemma lem4628142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4628143 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term261 x N s) = (term261 x N s).
Proof. exact (MK_COMB (@lem4628142) (@lem4628141 x N s)). Qed.
Lemma lem4628144 (x : nat -> nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) : (term282 x N n s) = (term282 x N n s).
Proof. exact (MK_COMB (@lem4628143 x N s) (@lem4628096 N n s)). Qed.
Lemma lem4628145 (x : nat -> nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term282 x N n s) : term282 x N n s.
Proof. exact (EQ_MP (@lem4628144 x N n s) (@lem4627937 x N n s h1)). Qed.
Lemma lem4628146 (h1 : term18) : term402.
Proof. exact (proj2 (@lem4628055 h1)). Qed.
Lemma lem4628147 (h1 : term18) : term397.
Proof. exact (proj1 (@lem4628055 h1)). Qed.
Lemma lem4628148 (h1 : term44) : term342.
Proof. exact (proj2 (@lem4627987 h1)). Qed.
Lemma lem4628150 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term164 x N s.
Proof. exact (h1). Qed.
Lemma lem4628151 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term219 N n s.
Proof. exact (h1). Qed.
Lemma lem4628152 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term86 N s.
Proof. exact (proj2 (@lem4628150 x N s h1)). Qed.
Lemma lem4628153 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term127 s x.
Proof. exact (proj1 (@lem4628150 x N s h1)). Qed.
Lemma lem4628154 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term187 n s.
Proof. exact (proj2 (@lem4628151 N n s h1)). Qed.
Lemma lem4628155 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term66 s N.
Proof. exact (proj1 (@lem4628151 N n s h1)). Qed.
Lemma lem4628163 (m : nat) (n : nat) : (term344 m n) = (term344 m n).
Proof. exact (eq_refl (term344 m n)). Qed.
Lemma lem4628164 (m : nat) : (term345 m) = (term345 m).
Proof. exact (fun_ext (fun n : nat => @lem4628163 m n)). Qed.
Lemma lem4628165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628166 (m : nat) : (term346 m) = (term346 m).
Proof. exact (MK_COMB (@lem4628165) (@lem4628164 m)). Qed.
Lemma lem4628167 : term347 = term347.
Proof. exact (fun_ext (fun m : nat => @lem4628166 m)). Qed.
Lemma lem4628168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628170 : term348 = term348.
Proof. exact (MK_COMB (@lem4628168) (@lem4628167)). Qed.
Lemma lem4628171 (h1 : term39) : term348.
Proof. exact (EQ_MP (@lem4628170) (@lem4628009 h1)). Qed.
Lemma lem4628195 (n : nat) (m : nat) : (term353 n m) = (term353 n m).
Proof. exact (eq_refl (term353 n m)). Qed.
Lemma lem4628196 (m : nat) : (term364 m) = (term364 m).
Proof. exact (fun_ext (fun n : nat => @lem4628195 n m)). Qed.
Lemma lem4628197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628198 (m : nat) : (term380 m) = (term380 m).
Proof. exact (MK_COMB (@lem4628197) (@lem4628196 m)). Qed.
Lemma lem4628199 : term387 = term387.
Proof. exact (fun_ext (fun m : nat => @lem4628198 m)). Qed.
Lemma lem4628200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628202 : term402 = term402.
Proof. exact (MK_COMB (@lem4628200) (@lem4628199)). Qed.
Lemma lem4628203 (h1 : term18) : term402.
Proof. exact (EQ_MP (@lem4628202) (@lem4628146 h1)). Qed.
Lemma lem4628241 (s : nat -> Prop) (x : nat -> nat) (a : nat) : (term123 s x a) = (term123 s x a).
Proof. exact (eq_refl (term123 s x a)). Qed.
Lemma lem4628242 (s : nat -> Prop) (x : nat -> nat) : (term125 s x) = (term125 s x).
Proof. exact (fun_ext (fun a : nat => @lem4628241 s x a)). Qed.
Lemma lem4628243 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628245 (s : nat -> Prop) (x : nat -> nat) : (term127 s x) = (term127 s x).
Proof. exact (MK_COMB (@lem4628243) (@lem4628242 s x)). Qed.
Lemma lem4628246 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term127 s x.
Proof. exact (EQ_MP (@lem4628245 s x) (@lem4628153 x N s h1)). Qed.
Lemma lem4628254 (N : nat) (n : nat) (s : nat -> Prop) : (term79 N n s) = (term79 N n s).
Proof. exact (eq_refl (term79 N n s)). Qed.
Lemma lem4628255 (N : nat) (s : nat -> Prop) : (term85 N s) = (term85 N s).
Proof. exact (fun_ext (fun n : nat => @lem4628254 N n s)). Qed.
Lemma lem4628256 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628258 (N : nat) (s : nat -> Prop) : (term86 N s) = (term86 N s).
Proof. exact (MK_COMB (@lem4628256) (@lem4628255 N s)). Qed.
Lemma lem4628259 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term86 N s.
Proof. exact (EQ_MP (@lem4628258 N s) (@lem4628152 x N s h1)). Qed.
Lemma lem4628283 (n : nat) (m : nat) : (term366 n m) = (term366 n m).
Proof. exact (eq_refl (term366 n m)). Qed.
Lemma lem4628284 (m : nat) : (term363 m) = (term363 m).
Proof. exact (fun_ext (fun n : nat => @lem4628283 n m)). Qed.
Lemma lem4628285 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628286 (m : nat) : (term375 m) = (term375 m).
Proof. exact (MK_COMB (@lem4628285) (@lem4628284 m)). Qed.
Lemma lem4628287 : term386 = term386.
Proof. exact (fun_ext (fun m : nat => @lem4628286 m)). Qed.
Lemma lem4628288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628290 : term397 = term397.
Proof. exact (MK_COMB (@lem4628288) (@lem4628287)). Qed.
Lemma lem4628291 (h1 : term18) : term397.
Proof. exact (EQ_MP (@lem4628290) (@lem4628147 h1)). Qed.
Lemma lem4628331 (m : nat) (n : nat) : (term308 m n) = (term308 m n).
Proof. exact (eq_refl (term308 m n)). Qed.
Lemma lem4628332 (m : nat) : (term302 m) = (term302 m).
Proof. exact (fun_ext (fun n : nat => @lem4628331 m n)). Qed.
Lemma lem4628333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628334 (m : nat) : (term320 m) = (term320 m).
Proof. exact (MK_COMB (@lem4628333) (@lem4628332 m)). Qed.
Lemma lem4628335 : term327 = term327.
Proof. exact (fun_ext (fun m : nat => @lem4628334 m)). Qed.
Lemma lem4628336 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628338 : term342 = term342.
Proof. exact (MK_COMB (@lem4628336) (@lem4628335)). Qed.
Lemma lem4628339 (h1 : term44) : term342.
Proof. exact (EQ_MP (@lem4628338) (@lem4628148 h1)). Qed.
Lemma lem4628347 (s : nat -> Prop) (x : nat) (N : nat) : (term55 s x N) = (term55 s x N).
Proof. exact (eq_refl (term55 s x N)). Qed.
Lemma lem4628348 (s : nat -> Prop) (N : nat) : (term65 s N) = (term65 s N).
Proof. exact (fun_ext (fun x : nat => @lem4628347 s x N)). Qed.
Lemma lem4628349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628351 (s : nat -> Prop) (N : nat) : (term66 s N) = (term66 s N).
Proof. exact (MK_COMB (@lem4628349) (@lem4628348 s N)). Qed.
Lemma lem4628352 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term66 s N.
Proof. exact (EQ_MP (@lem4628351 s N) (@lem4628155 N n s h1)). Qed.
Lemma lem4628358 (n : nat -> nat) (N : nat) (s : nat -> Prop) : (term183 n N s) = (term183 n N s).
Proof. exact (eq_refl (term183 n N s)). Qed.
Lemma lem4628359 (n : nat -> nat) (s : nat -> Prop) : (term185 n s) = (term185 n s).
Proof. exact (fun_ext (fun N : nat => @lem4628358 n N s)). Qed.
Lemma lem4628360 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628362 (n : nat -> nat) (s : nat -> Prop) : (term187 n s) = (term187 n s).
Proof. exact (MK_COMB (@lem4628360) (@lem4628359 n s)). Qed.
Lemma lem4628363 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term187 n s.
Proof. exact (EQ_MP (@lem4628362 n s) (@lem4628154 N n s h1)). Qed.
Lemma lem4628364 (_55577 : nat) (h1 : term39) : term404 _55577.
Proof. exact (@lem4628171 h1 _55577). Qed.
Lemma lem4628365 (_55577 : nat) : (term404 _55577) = (term346 _55577).
Proof. exact (eq_refl (term404 _55577)). Qed.
Lemma lem4628366 (_55577 : nat) (h1 : term39) : term346 _55577.
Proof. exact (EQ_MP (@lem4628365 _55577) (@lem4628364 _55577 h1)). Qed.
Lemma lem4628367 (_55577 : nat) (_55578 : nat) (h1 : term39) : term405 _55577 _55578.
Proof. exact (@lem4628366 _55577 h1 _55578). Qed.
Lemma lem4628368 (_55577 : nat) (_55578 : nat) : (term405 _55577 _55578) = (term344 _55577 _55578).
Proof. exact (eq_refl (term405 _55577 _55578)). Qed.
Lemma lem4628376 (_55581 : nat) (h1 : term18) : term390 _55581.
Proof. exact (@lem4628203 h1 _55581). Qed.
Lemma lem4628377 (_55581 : nat) : (term390 _55581) = (term380 _55581).
Proof. exact (eq_refl (term390 _55581)). Qed.
Lemma lem4628378 (_55581 : nat) (h1 : term18) : term380 _55581.
Proof. exact (EQ_MP (@lem4628377 _55581) (@lem4628376 _55581 h1)). Qed.
Lemma lem4628379 (_55581 : nat) (_55582 : nat) (h1 : term18) : term368 _55581 _55582.
Proof. exact (@lem4628378 _55581 h1 _55582). Qed.
Lemma lem4628380 (_55582 : nat) (_55581 : nat) : (term368 _55581 _55582) = (term353 _55582 _55581).
Proof. exact (eq_refl (term368 _55581 _55582)). Qed.
Lemma lem4628394 (_55587 : nat) (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term406 s x _55587.
Proof. exact (@lem4628246 x N s h1 _55587). Qed.
Lemma lem4628395 (s : nat -> Prop) (x : nat -> nat) (_55587 : nat) : (term406 s x _55587) = (term123 s x _55587).
Proof. exact (eq_refl (term406 s x _55587)). Qed.
Lemma lem4628396 (_55587 : nat) (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term123 s x _55587.
Proof. exact (EQ_MP (@lem4628395 s x _55587) (@lem4628394 _55587 x N s h1)). Qed.
Lemma lem4628397 (_55588 : nat) (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term407 N s _55588.
Proof. exact (@lem4628259 x N s h1 _55588). Qed.
Lemma lem4628398 (N : nat) (_55588 : nat) (s : nat -> Prop) : (term407 N s _55588) = (term79 N _55588 s).
Proof. exact (eq_refl (term407 N s _55588)). Qed.
Lemma lem4628406 (_55591 : nat) (h1 : term18) : term388 _55591.
Proof. exact (@lem4628291 h1 _55591). Qed.
Lemma lem4628407 (_55591 : nat) : (term388 _55591) = (term375 _55591).
Proof. exact (eq_refl (term388 _55591)). Qed.
Lemma lem4628408 (_55591 : nat) (h1 : term18) : term375 _55591.
Proof. exact (EQ_MP (@lem4628407 _55591) (@lem4628406 _55591 h1)). Qed.
Lemma lem4628409 (_55591 : nat) (_55592 : nat) (h1 : term18) : term365 _55591 _55592.
Proof. exact (@lem4628408 _55591 h1 _55592). Qed.
Lemma lem4628410 (_55592 : nat) (_55591 : nat) : (term365 _55591 _55592) = (term366 _55592 _55591).
Proof. exact (eq_refl (term365 _55591 _55592)). Qed.
Lemma lem4628424 (_55597 : nat) (h1 : term44) : term330 _55597.
Proof. exact (@lem4628339 h1 _55597). Qed.
Lemma lem4628425 (_55597 : nat) : (term330 _55597) = (term320 _55597).
Proof. exact (eq_refl (term330 _55597)). Qed.
Lemma lem4628426 (_55597 : nat) (h1 : term44) : term320 _55597.
Proof. exact (EQ_MP (@lem4628425 _55597) (@lem4628424 _55597 h1)). Qed.
Lemma lem4628427 (_55597 : nat) (_55598 : nat) (h1 : term44) : term307 _55597 _55598.
Proof. exact (@lem4628426 _55597 h1 _55598). Qed.
Lemma lem4628428 (_55597 : nat) (_55598 : nat) : (term307 _55597 _55598) = (term308 _55597 _55598).
Proof. exact (eq_refl (term307 _55597 _55598)). Qed.
Lemma lem4628430 (_55599 : nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term408 s N _55599.
Proof. exact (@lem4628352 N n s h1 _55599). Qed.
Lemma lem4628431 (s : nat -> Prop) (_55599 : nat) (N : nat) : (term408 s N _55599) = (term55 s _55599 N).
Proof. exact (eq_refl (term408 s N _55599)). Qed.
Lemma lem4628433 (_55600 : nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term409 n s _55600.
Proof. exact (@lem4628363 N n s h1 _55600). Qed.
Lemma lem4628434 (n : nat -> nat) (_55600 : nat) (s : nat -> Prop) : (term409 n s _55600) = (term183 n _55600 s).
Proof. exact (eq_refl (term409 n s _55600)). Qed.
Lemma lem4628435 (_55600 : nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term183 n _55600 s.
Proof. exact (EQ_MP (@lem4628434 n _55600 s) (@lem4628433 _55600 N n s h1)). Qed.
Lemma lem4628445 (_55577 : nat) (_55578 : nat) (h1 : term39) : term344 _55577 _55578.
Proof. exact (EQ_MP (@lem4628368 _55577 _55578) (@lem4628367 _55577 _55578 h1)). Qed.
Lemma lem4628457 (_55582 : nat) (_55581 : nat) (h1 : term18) : term353 _55582 _55581.
Proof. exact (EQ_MP (@lem4628380 _55582 _55581) (@lem4628379 _55581 _55582 h1)). Qed.
Lemma lem4628475 (_55588 : nat) (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term79 N _55588 s.
Proof. exact (EQ_MP (@lem4628398 N _55588 s) (@lem4628397 _55588 x N s h1)). Qed.
Lemma lem4628479 (_55587 : nat) (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term410 x _55587.
Proof. exact (proj2 (@lem4628396 _55587 x N s h1)). Qed.
Lemma lem4628491 (_55592 : nat) (_55591 : nat) (h1 : term18) : term366 _55592 _55591.
Proof. exact (EQ_MP (@lem4628410 _55592 _55591) (@lem4628409 _55591 _55592 h1)). Qed.
Lemma lem4628509 (_55597 : nat) (_55598 : nat) (h1 : term44) : term308 _55597 _55598.
Proof. exact (EQ_MP (@lem4628428 _55597 _55598) (@lem4628427 _55597 _55598 h1)). Qed.
Lemma lem4628515 (_55599 : nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term55 s _55599 N.
Proof. exact (EQ_MP (@lem4628431 s _55599 N) (@lem4628430 _55599 N n s h1)). Qed.
Lemma lem4628521 (_55587 : nat) (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term411 x _55587 s.
Proof. exact (proj1 (@lem4628396 _55587 x N s h1)). Qed.
Lemma lem4628522 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term411 x N s.
Proof. exact (@lem4628521 N x N s h1). Qed.
Lemma lem4628523 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term412 x N s.
Proof. exact (fun h0 : term413 x N s => @lem4628522 x N s h1). Qed.
Lemma lem4628525 (p : Prop) : (term414 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4628526 (x : nat -> nat) (N : nat) (s : nat -> Prop) : (term412 x N s) = (term411 x N s).
Proof. exact (@lem4628525 (term411 x N s)). Qed.
Lemma lem4628527 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term411 x N s.
Proof. exact (EQ_MP (@lem4628526 x N s) (@lem4628523 x N s h1)). Qed.
Lemma lem4628529 (b : Prop) (a : Prop) : (a \/ b) = (term415 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4628530 (s : nat -> Prop) (N : nat) (_55588 : nat) : (term79 N _55588 s) = (term416 s N _55588).
Proof. exact (@lem4628529 (term417 _55588 s) (term31 N _55588)). Qed.
Lemma lem4628532 (a : Prop) : (term418 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4628533 (_55588 : nat) (s : nat -> Prop) : (term419 _55588 s) = (@IN nat _55588 s).
Proof. exact (@lem4628532 (@IN nat _55588 s)). Qed.
Lemma lem4628534 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4628535 (_55588 : nat) (s : nat -> Prop) : (term420 _55588 s) = (term421 _55588 s).
Proof. exact (MK_COMB (@lem4628534) (@lem4628533 _55588 s)). Qed.
Lemma lem4628536 (N : nat) (_55588 : nat) : (term31 N _55588) = (term31 N _55588).
Proof. exact (eq_refl (term31 N _55588)). Qed.
Lemma lem4628537 (s : nat -> Prop) (N : nat) (_55588 : nat) : (term416 s N _55588) = (term422 s N _55588).
Proof. exact (MK_COMB (@lem4628535 _55588 s) (@lem4628536 N _55588)). Qed.
Lemma lem4628538 (s : nat -> Prop) (N : nat) (_55588 : nat) : (term79 N _55588 s) = (term422 s N _55588).
Proof. exact (TRANS (@lem4628530 s N _55588) (@lem4628537 s N _55588)). Qed.
Lemma lem4628541 (_55588 : nat) (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term422 s N _55588.
Proof. exact (EQ_MP (@lem4628538 s N _55588) (@lem4628475 _55588 x N s h1)). Qed.
Lemma lem4628542 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term423 s x N.
Proof. exact (@lem4628541 (x N) x N s h1). Qed.
Lemma lem4628545 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term424 x N.
Proof. exact (@lem4628542 x N s h1 (@lem4628527 x N s h1)). Qed.
Lemma lem4628546 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term425 x N.
Proof. exact (fun h0 : term426 x N => @lem4628545 x N s h1). Qed.
Lemma lem4628548 (p : Prop) : (term427 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4628549 (x : nat -> nat) (N : nat) : (term425 x N) = (term424 x N).
Proof. exact (@lem4628548 (term426 x N)). Qed.
Lemma lem4628550 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term424 x N.
Proof. exact (EQ_MP (@lem4628549 x N) (@lem4628546 x N s h1)). Qed.
Lemma lem4628552 (b : Prop) (a : Prop) : (a \/ b) = (term415 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4628555 (_55577 : nat) (_55578 : nat) : (term344 _55577 _55578) = (term428 _55577 _55578).
Proof. exact (@lem4628552 (Peano.le _55577 _55578) (term429 _55577 _55578)). Qed.
Lemma lem4628558 (_55577 : nat) (_55578 : nat) (h1 : term39) : term428 _55577 _55578.
Proof. exact (EQ_MP (@lem4628555 _55577 _55578) (@lem4628445 _55577 _55578 h1)). Qed.
Lemma lem4628559 (x : nat -> nat) (N : nat) (h1 : term39) : term430 x N.
Proof. exact (@lem4628558 N (x N) h1). Qed.
Lemma lem4628562 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term39) (h2 : term164 x N s) : term431 x N.
Proof. exact (@lem4628559 x N h1 (@lem4628550 x N s h2)). Qed.
Lemma lem4628563 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term39) (h2 : term164 x N s) : term432 x N.
Proof. exact (fun h0 : term433 x N => @lem4628562 x N s h1 h2). Qed.
Lemma lem4628565 (p : Prop) : (term427 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4628566 (x : nat -> nat) (N : nat) : (term432 x N) = (term431 x N).
Proof. exact (@lem4628565 (term433 x N)). Qed.
Lemma lem4628567 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term39) (h2 : term164 x N s) : term431 x N.
Proof. exact (EQ_MP (@lem4628566 x N) (@lem4628563 x N s h1 h2)). Qed.
Lemma lem4628569 (b : Prop) (a : Prop) : (a \/ b) = (term415 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4628572 (_55581 : nat) (_55582 : nat) : (term353 _55582 _55581) = (term434 _55581 _55582).
Proof. exact (@lem4628569 (Peano.lt _55582 _55581) (Peano.le _55581 _55582)). Qed.
Lemma lem4628575 (_55581 : nat) (_55582 : nat) (h1 : term18) : term434 _55581 _55582.
Proof. exact (EQ_MP (@lem4628572 _55581 _55582) (@lem4628457 _55582 _55581 h1)). Qed.
Lemma lem4628576 (x : nat -> nat) (N : nat) (h1 : term18) : term435 x N.
Proof. exact (@lem4628575 (x N) N h1). Qed.
Lemma lem4628579 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term18) (h2 : term39) (h3 : term164 x N s) : term436 x N.
Proof. exact (@lem4628576 x N h1 (@lem4628567 x N s h2 h3)). Qed.
Lemma lem4628580 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term18) (h2 : term39) (h3 : term164 x N s) : term437 x N.
Proof. exact (fun h0 : term410 x N => @lem4628579 x N s h1 h2 h3). Qed.
Lemma lem4628582 (p : Prop) : (term414 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4628583 (x : nat -> nat) (N : nat) : (term437 x N) = (term436 x N).
Proof. exact (@lem4628582 (term436 x N)). Qed.
Lemma lem4628584 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term18) (h2 : term39) (h3 : term164 x N s) : term436 x N.
Proof. exact (EQ_MP (@lem4628583 x N) (@lem4628580 x N s h1 h2 h3)). Qed.
Lemma lem4628587 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4628589 (x : nat -> nat) (_55587 : nat) : (term410 x _55587) = (term438 x _55587).
Proof. exact (@lem4628587 (term436 x _55587)). Qed.
Lemma lem4628592 (_55587 : nat) (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term438 x _55587.
Proof. exact (EQ_MP (@lem4628589 x _55587) (@lem4628479 _55587 x N s h1)). Qed.
Lemma lem4628593 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term164 x N s) : term438 x N.
Proof. exact (@lem4628592 N x N s h1). Qed.
Lemma lem4628596 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term18) (h2 : term39) (h3 : term164 x N s) : False.
Proof. exact (@lem4628593 x N s h3 (@lem4628584 x N s h1 h2 h3)). Qed.
Lemma lem4628597 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term18) (h2 : term39) (h3 : term164 x N s) : term439.
Proof. exact (fun h0 : ~ False => @lem4628596 x N s h1 h2 h3). Qed.
Lemma lem4628599 (p : Prop) : (term414 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4628600 : term439 = False.
Proof. exact (@lem4628599 False). Qed.
Lemma lem4628601 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term18) (h2 : term39) (h3 : term164 x N s) : False.
Proof. exact (EQ_MP (@lem4628600) (@lem4628597 x N s h1 h2 h3)). Qed.
Lemma lem4628603 (_55600 : nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term411 n _55600 s.
Proof. exact (proj2 (@lem4628435 _55600 N n s h1)). Qed.
Lemma lem4628604 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term440 n N s.
Proof. exact (@lem4628603 (S N) N n s h1). Qed.
Lemma lem4628605 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term441 n N s.
Proof. exact (fun h0 : term442 n N s => @lem4628604 N n s h1). Qed.
Lemma lem4628607 (p : Prop) : (term414 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4628608 (n : nat -> nat) (N : nat) (s : nat -> Prop) : (term441 n N s) = (term440 n N s).
Proof. exact (@lem4628607 (term440 n N s)). Qed.
Lemma lem4628609 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term440 n N s.
Proof. exact (EQ_MP (@lem4628608 n N s) (@lem4628605 N n s h1)). Qed.
Lemma lem4628615 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4628616 (N : nat) (_55599 : nat) (s : nat -> Prop) : (term55 s _55599 N) = (term443 N _55599 s).
Proof. exact (@lem4628615 (Peano.le _55599 N) (term417 _55599 s)). Qed.
Lemma lem4628622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4628623 (N : nat) (_55599 : nat) (s : nat -> Prop) : (term444 s _55599 N) = (term445 N _55599 s).
Proof. exact (MK_COMB (@lem4628622) (@lem4628616 N _55599 s)). Qed.
Lemma lem4628629 (N : nat) (_55599 : nat) (s : nat -> Prop) : (term443 N _55599 s) = (term443 N _55599 s).
Proof. exact (eq_refl (term443 N _55599 s)). Qed.
Lemma lem4628630 (N : nat) (_55599 : nat) (s : nat -> Prop) : ((term55 s _55599 N) = (term443 N _55599 s)) = ((term443 N _55599 s) = (term443 N _55599 s)).
Proof. exact (MK_COMB (@lem4628623 N _55599 s) (@lem4628629 N _55599 s)). Qed.
Lemma lem4628632 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4628633 (x : Prop) : (x = x) = True.
Proof. exact (@lem4628632 Prop x). Qed.
Lemma lem4628634 (N : nat) (_55599 : nat) (s : nat -> Prop) : ((term443 N _55599 s) = (term443 N _55599 s)) = True.
Proof. exact (@lem4628633 (term443 N _55599 s)). Qed.
Lemma lem4628635 (N : nat) (_55599 : nat) (s : nat -> Prop) : ((term55 s _55599 N) = (term443 N _55599 s)) = True.
Proof. exact (TRANS (@lem4628630 N _55599 s) (@lem4628634 N _55599 s)). Qed.
Lemma lem4628636 (N : nat) (_55599 : nat) (s : nat -> Prop) : True = ((term55 s _55599 N) = (term443 N _55599 s)).
Proof. exact (SYM (@lem4628635 N _55599 s)). Qed.
Lemma lem4628637 (N : nat) (_55599 : nat) (s : nat -> Prop) : (term55 s _55599 N) = (term443 N _55599 s).
Proof. exact (EQ_MP (@lem4628636 N _55599 s) (@lem0)). Qed.
Lemma lem4628638 (_55599 : nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term443 N _55599 s.
Proof. exact (EQ_MP (@lem4628637 N _55599 s) (@lem4628515 _55599 N n s h1)). Qed.
Lemma lem4628640 (b : Prop) (a : Prop) : (a \/ b) = (term415 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4628641 (s : nat -> Prop) (_55599 : nat) (N : nat) : (term443 N _55599 s) = (term446 s _55599 N).
Proof. exact (@lem4628640 (term417 _55599 s) (Peano.le _55599 N)). Qed.
Lemma lem4628643 (a : Prop) : (term418 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4628644 (_55599 : nat) (s : nat -> Prop) : (term419 _55599 s) = (@IN nat _55599 s).
Proof. exact (@lem4628643 (@IN nat _55599 s)). Qed.
Lemma lem4628645 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4628646 (_55599 : nat) (s : nat -> Prop) : (term420 _55599 s) = (term421 _55599 s).
Proof. exact (MK_COMB (@lem4628645) (@lem4628644 _55599 s)). Qed.
Lemma lem4628647 (_55599 : nat) (N : nat) : (Peano.le _55599 N) = (Peano.le _55599 N).
Proof. exact (eq_refl (Peano.le _55599 N)). Qed.
Lemma lem4628648 (s : nat -> Prop) (_55599 : nat) (N : nat) : (term446 s _55599 N) = (term49 s _55599 N).
Proof. exact (MK_COMB (@lem4628646 _55599 s) (@lem4628647 _55599 N)). Qed.
Lemma lem4628649 (s : nat -> Prop) (_55599 : nat) (N : nat) : (term443 N _55599 s) = (term49 s _55599 N).
Proof. exact (TRANS (@lem4628641 s _55599 N) (@lem4628648 s _55599 N)). Qed.
Lemma lem4628652 (_55599 : nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term49 s _55599 N.
Proof. exact (EQ_MP (@lem4628649 s _55599 N) (@lem4628638 _55599 N n s h1)). Qed.
Lemma lem4628653 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term447 s n N.
Proof. exact (@lem4628652 (term448 n N) N n s h1). Qed.
Lemma lem4628656 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term449 n N.
Proof. exact (@lem4628653 N n s h1 (@lem4628609 N n s h1)). Qed.
Lemma lem4628657 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term450 n N.
Proof. exact (fun h0 : term451 n N => @lem4628656 N n s h1). Qed.
Lemma lem4628659 (p : Prop) : (term414 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4628660 (n : nat -> nat) (N : nat) : (term450 n N) = (term449 n N).
Proof. exact (@lem4628659 (term449 n N)). Qed.
Lemma lem4628661 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term449 n N.
Proof. exact (EQ_MP (@lem4628660 n N) (@lem4628657 N n s h1)). Qed.
Lemma lem4628663 (_55600 : nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term426 n _55600.
Proof. exact (proj1 (@lem4628435 _55600 N n s h1)). Qed.
Lemma lem4628664 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term452 n N.
Proof. exact (@lem4628663 (S N) N n s h1). Qed.
Lemma lem4628665 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term453 n N.
Proof. exact (fun h0 : term454 n N => @lem4628664 N n s h1). Qed.
Lemma lem4628667 (p : Prop) : (term414 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4628668 (n : nat -> nat) (N : nat) : (term453 n N) = (term452 n N).
Proof. exact (@lem4628667 (term452 n N)). Qed.
Lemma lem4628669 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term219 N n s) : term452 n N.
Proof. exact (EQ_MP (@lem4628668 n N) (@lem4628665 N n s h1)). Qed.
Lemma lem4628675 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4628676 (_55597 : nat) (_55598 : nat) : (term308 _55597 _55598) = (term455 _55597 _55598).
Proof. exact (@lem4628675 (Peano.lt _55597 _55598) (term456 _55597 _55598)). Qed.
Lemma lem4628682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4628683 (_55597 : nat) (_55598 : nat) : (term457 _55597 _55598) = (term458 _55597 _55598).
Proof. exact (MK_COMB (@lem4628682) (@lem4628676 _55597 _55598)). Qed.
Lemma lem4628689 (_55597 : nat) (_55598 : nat) : (term455 _55597 _55598) = (term455 _55597 _55598).
Proof. exact (eq_refl (term455 _55597 _55598)). Qed.
Lemma lem4628690 (_55597 : nat) (_55598 : nat) : ((term308 _55597 _55598) = (term455 _55597 _55598)) = ((term455 _55597 _55598) = (term455 _55597 _55598)).
Proof. exact (MK_COMB (@lem4628683 _55597 _55598) (@lem4628689 _55597 _55598)). Qed.
Lemma lem4628692 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4628693 (x : Prop) : (x = x) = True.
Proof. exact (@lem4628692 Prop x). Qed.
Lemma lem4628694 (_55597 : nat) (_55598 : nat) : ((term455 _55597 _55598) = (term455 _55597 _55598)) = True.
Proof. exact (@lem4628693 (term455 _55597 _55598)). Qed.
Lemma lem4628695 (_55597 : nat) (_55598 : nat) : ((term308 _55597 _55598) = (term455 _55597 _55598)) = True.
Proof. exact (TRANS (@lem4628690 _55597 _55598) (@lem4628694 _55597 _55598)). Qed.
Lemma lem4628696 (_55597 : nat) (_55598 : nat) : True = ((term308 _55597 _55598) = (term455 _55597 _55598)).
Proof. exact (SYM (@lem4628695 _55597 _55598)). Qed.
Lemma lem4628697 (_55597 : nat) (_55598 : nat) : (term308 _55597 _55598) = (term455 _55597 _55598).
Proof. exact (EQ_MP (@lem4628696 _55597 _55598) (@lem0)). Qed.
Lemma lem4628698 (_55597 : nat) (_55598 : nat) (h1 : term44) : term455 _55597 _55598.
Proof. exact (EQ_MP (@lem4628697 _55597 _55598) (@lem4628509 _55597 _55598 h1)). Qed.
Lemma lem4628700 (b : Prop) (a : Prop) : (a \/ b) = (term415 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4628701 (_55597 : nat) (_55598 : nat) : (term455 _55597 _55598) = (term459 _55597 _55598).
Proof. exact (@lem4628700 (term456 _55597 _55598) (Peano.lt _55597 _55598)). Qed.
Lemma lem4628703 (a : Prop) : (term418 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4628704 (_55597 : nat) (_55598 : nat) : (term460 _55597 _55598) = (term40 _55597 _55598).
Proof. exact (@lem4628703 (term40 _55597 _55598)). Qed.
Lemma lem4628705 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4628706 (_55597 : nat) (_55598 : nat) : (term461 _55597 _55598) = (term462 _55597 _55598).
Proof. exact (MK_COMB (@lem4628705) (@lem4628704 _55597 _55598)). Qed.
Lemma lem4628707 (_55597 : nat) (_55598 : nat) : (Peano.lt _55597 _55598) = (Peano.lt _55597 _55598).
Proof. exact (eq_refl (Peano.lt _55597 _55598)). Qed.
Lemma lem4628708 (_55597 : nat) (_55598 : nat) : (term459 _55597 _55598) = (term463 _55597 _55598).
Proof. exact (MK_COMB (@lem4628706 _55597 _55598) (@lem4628707 _55597 _55598)). Qed.
Lemma lem4628709 (_55597 : nat) (_55598 : nat) : (term455 _55597 _55598) = (term463 _55597 _55598).
Proof. exact (TRANS (@lem4628701 _55597 _55598) (@lem4628708 _55597 _55598)). Qed.
Lemma lem4628712 (_55597 : nat) (_55598 : nat) (h1 : term44) : term463 _55597 _55598.
Proof. exact (EQ_MP (@lem4628709 _55597 _55598) (@lem4628698 _55597 _55598 h1)). Qed.
Lemma lem4628713 (n : nat -> nat) (N : nat) (h1 : term44) : term464 n N.
Proof. exact (@lem4628712 N (term448 n N) h1). Qed.
Lemma lem4628716 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term44) (h2 : term219 N n s) : term465 n N.
Proof. exact (@lem4628713 n N h1 (@lem4628669 N n s h2)). Qed.
Lemma lem4628717 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term44) (h2 : term219 N n s) : term466 n N.
Proof. exact (fun h0 : term467 n N => @lem4628716 N n s h1 h2). Qed.
Lemma lem4628719 (p : Prop) : (term414 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4628720 (n : nat -> nat) (N : nat) : (term466 n N) = (term465 n N).
Proof. exact (@lem4628719 (term465 n N)). Qed.
Lemma lem4628721 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term44) (h2 : term219 N n s) : term465 n N.
Proof. exact (EQ_MP (@lem4628720 n N) (@lem4628717 N n s h1 h2)). Qed.
Lemma lem4628723 (a : Prop) (b : Prop) : (term468 a b) = (term469 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4628724 (_55592 : nat) (_55591 : nat) : (term366 _55592 _55591) = (term470 _55592 _55591).
Proof. exact (@lem4628723 (Peano.le _55591 _55592) (Peano.lt _55592 _55591)). Qed.
Lemma lem4628726 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4628727 (_55592 : nat) (_55591 : nat) : (term470 _55592 _55591) = (term471 _55592 _55591).
Proof. exact (@lem4628726 (term472 _55592 _55591)). Qed.
Lemma lem4628728 (_55592 : nat) (_55591 : nat) : (term366 _55592 _55591) = (term471 _55592 _55591).
Proof. exact (TRANS (@lem4628724 _55592 _55591) (@lem4628727 _55592 _55591)). Qed.
Lemma lem4628730 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term44) (h2 : term219 N n s) : term473 n N.
Proof. exact (conj (@lem4628661 N n s h2) (@lem4628721 N n s h1 h2)). Qed.
Lemma lem4628732 (_55592 : nat) (_55591 : nat) (h1 : term18) : term471 _55592 _55591.
Proof. exact (EQ_MP (@lem4628728 _55592 _55591) (@lem4628491 _55592 _55591 h1)). Qed.
Lemma lem4628733 (n : nat -> nat) (N : nat) (h1 : term18) : term474 n N.
Proof. exact (@lem4628732 N (term448 n N) h1). Qed.
Lemma lem4628736 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term18) (h2 : term44) (h3 : term219 N n s) : False.
Proof. exact (@lem4628733 n N h1 (@lem4628730 N n s h2 h3)). Qed.
Lemma lem4628737 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term18) (h2 : term44) (h3 : term219 N n s) : term439.
Proof. exact (fun h0 : ~ False => @lem4628736 N n s h1 h2 h3). Qed.
Lemma lem4628739 (p : Prop) : (term414 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4628740 : term439 = False.
Proof. exact (@lem4628739 False). Qed.
Lemma lem4628741 (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term18) (h2 : term44) (h3 : term219 N n s) : False.
Proof. exact (EQ_MP (@lem4628740) (@lem4628737 N n s h1 h2 h3)). Qed.
Lemma lem4628742 (x : nat -> nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term18) (h2 : term44) (h3 : term39) (h4 : term282 x N n s) : False.
Proof. exact (or_elim (@lem4628145 x N n s h4) (fun h0 : term164 x N s => @lem4628601 x N s h1 h3 h0) (fun h0 : term219 N n s => @lem4628741 N n s h1 h2 h0)). Qed.
Lemma lem4628743 (x : nat -> nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term18) (h2 : term44) (h3 : term39) (h4 : term282 x N n s) : (term282 x N n s) = False.
Proof. exact (prop_ext (fun h5 : term282 x N n s => @lem4628742 x N n s h1 h2 h3 h4) (fun h5 : False => @lem4628145 x N n s h4)). Qed.
Lemma lem4628744 (x : nat -> nat) (N : nat) (n : nat -> nat) (s : nat -> Prop) (h1 : term18) (h2 : term44) (h3 : term39) (h4 : term282 x N n s) : False.
Proof. exact (EQ_MP (@lem4628743 x N n s h1 h2 h3 h4) (@lem4628145 x N n s h4)). Qed.
Lemma lem4628745 (x : nat -> nat) (N : nat) (s : nat -> Prop) (h1 : term18) (h2 : term44) (h3 : term39) (h4 : term285 x N s) : False.
Proof. exact (ex_elim (@lem4627936 x N s h4) (fun n : nat -> nat => fun h0 : term284 x N s n => @lem4628744 x N n s h1 h2 h3 h0)). Qed.
Lemma lem4628746 (x : nat -> nat) (s : nat -> Prop) (h1 : term18) (h2 : term44) (h3 : term39) (h4 : term287 x s) : False.
Proof. exact (ex_elim (@lem4627935 x s h4) (fun N : nat => fun h0 : term286 x s N => @lem4628745 x N s h1 h2 h3 h0)). Qed.
Lemma lem4628747 (s : nat -> Prop) (h1 : term18) (h2 : term44) (h3 : term39) (h4 : term11 s) : False.
Proof. exact (ex_elim (@lem4627288 s h4) (fun x : nat -> nat => fun h0 : term288 s x => @lem4628746 x s h1 h2 h3 h0)). Qed.
Lemma lem4628748 (s : nat -> Prop) (h1 : term44) (h2 : term39) (h3 : term11 s) : term16.
Proof. exact (fun h0 : term18 => @lem4628747 s h0 h1 h2 h3). Qed.
Lemma lem4628749 : term16 = term17.
Proof. exact (@lem69 term18). Qed.
Lemma lem4628750 (s : nat -> Prop) (h1 : term44) (h2 : term39) (h3 : term11 s) : term17.
Proof. exact (EQ_MP (@lem4628749) (@lem4628748 s h1 h2 h3)). Qed.
Lemma lem4628751 (s : nat -> Prop) (h1 : term44) (h2 : term11 s) : term21.
Proof. exact (fun h0 : term39 => @lem4628750 s h1 h0 h2). Qed.
Lemma lem4628752 (s : nat -> Prop) (h1 : term11 s) : term24.
Proof. exact (fun h0 : term44 => @lem4628751 s h0 h1). Qed.
Lemma lem4628753 (s : nat -> Prop) : term26 s.
Proof. exact (fun h0 : term11 s => @lem4628752 s h0). Qed.
Lemma lem4628758 : term30.
Proof. exact (fun s : nat -> Prop => @lem4628753 s). Qed.
Lemma lem4628759 : term29.
Proof. exact (EQ_MP (@lem4626718) (@lem4628758)). Qed.
Lemma lem4628760 (s : nat -> Prop) : term475 s.
Proof. exact (@lem4628759 s). Qed.
Lemma lem4628761 (s : nat -> Prop) : (term475 s) = (term12 s).
Proof. exact (eq_refl (term475 s)). Qed.
Lemma lem4628762 (s : nat -> Prop) : term12 s.
Proof. exact (EQ_MP (@lem4628761 s) (@lem4628760 s)). Qed.
Lemma lem4628764 (s : nat -> Prop) : term12 s.
Proof. exact (@lem4626432 s (@lem4628762 s)). Qed.
Lemma lem4628765 (s : nat -> Prop) (h1 : term11 s) : term23.
Proof. exact (@lem4628764 s (@lem4626417 s h1)). Qed.
Lemma lem4628766 (s : nat -> Prop) (h1 : term11 s) : term20.
Proof. exact (@lem4628765 s h1 (@lem91144)). Qed.
Lemma lem4628767 (s : nat -> Prop) (h1 : term11 s) : term16.
Proof. exact (@lem4628766 s h1 (@lem98439)). Qed.
Lemma lem4628768 (s : nat -> Prop) (h1 : term11 s) : False.
Proof. exact (@lem4628767 s h1 (@lem97961)). Qed.
Lemma lem4628769 (s : nat -> Prop) (h1 : term11 s) : (term11 s) = False.
Proof. exact (prop_ext (fun h2 : term11 s => @lem4628768 s h1) (fun h2 : False => @lem4626417 s h1)). Qed.
Lemma lem4628770 (s : nat -> Prop) (h1 : term11 s) : False.
Proof. exact (EQ_MP (@lem4628769 s h1) (@lem4626417 s h1)). Qed.
Lemma lem4628771 (s : nat -> Prop) : term10 s.
Proof. exact (fun h0 : term11 s => @lem4628770 s h0). Qed.
Lemma lem4628772 (s : nat -> Prop) : (term5 s) = (term8 s).
Proof. exact (EQ_MP (@lem4626416 s) (@lem4628771 s)). Qed.
Lemma lem4628773 (s : nat -> Prop) : (@INFINITE nat s) = (term8 s).
Proof. exact (EQ_MP (@lem4626412 s) (@lem4628772 s)). Qed.
Lemma lem4628778 : term476.
Proof. exact (fun s : nat -> Prop => @lem4628773 s). Qed.
