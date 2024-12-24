Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_AC_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_SYM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem82369 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem82370 (n : nat) (m : nat) (p : nat) : (term1 n m p) = (term2 n m p).
Proof. exact (@lem82369 (term1 n m p)). Qed.
Lemma lem82371 (n : nat) (m : nat) (p : nat) : (term2 n m p) = (term1 n m p).
Proof. exact (SYM (@lem82370 n m p)). Qed.
Lemma lem82372 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term3 n m p.
Proof. exact (h1). Qed.
Lemma lem82375 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) : term4 n m p.
Proof. exact (h1). Qed.
Lemma lem82376 (n : nat) (m : nat) (p : nat) : term5 n m p.
Proof. exact (fun h0 : term4 n m p => @lem82375 n m p h0). Qed.
Lemma lem82377 (n : nat) (m : nat) (p : nat) (h1 : term5 n m p) : term5 n m p.
Proof. exact (h1). Qed.
Lemma lem82378 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) : term4 n m p.
Proof. exact (h1). Qed.
Lemma lem82379 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) (h2 : term5 n m p) : term4 n m p.
Proof. exact (@lem82377 n m p h2 (@lem82378 n m p h1)). Qed.
Lemma lem82380 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) : term6 n m p.
Proof. exact (fun h0 : term5 n m p => @lem82379 n m p h1 h0). Qed.
Lemma lem82381 (n : nat) (m : nat) (p : nat) (h1 : term5 n m p) : term5 n m p.
Proof. exact (h1). Qed.
Lemma lem82382 (n : nat) (m : nat) (p : nat) (h1 : term4 n m p) (h2 : term5 n m p) : term4 n m p.
Proof. exact (@lem82380 n m p h1 (@lem82381 n m p h2)). Qed.
Lemma lem82383 (n : nat) (m : nat) (p : nat) (h1 : term5 n m p) : term5 n m p.
Proof. exact (fun h0 : term4 n m p => @lem82382 n m p h0 h1). Qed.
Lemma lem82384 (n : nat) (m : nat) (p : nat) : term7 n m p.
Proof. exact (fun h0 : term5 n m p => @lem82383 n m p h0). Qed.
Lemma lem82387 (n : nat) (m : nat) (p : nat) : term5 n m p.
Proof. exact (@lem82384 n m p (@lem82376 n m p)). Qed.
Lemma lem82417 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem82418 : term8 = term9.
Proof. exact (@lem82417 term10). Qed.
Lemma lem82431 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem82432 : term12 = term13.
Proof. exact (MK_COMB (@lem82431) (@lem82418)). Qed.
Lemma lem82435 (n : nat) (m : nat) (p : nat) : (term14 n m p) = (term14 n m p).
Proof. exact (eq_refl (term14 n m p)). Qed.
Lemma lem82436 (n : nat) (m : nat) (p : nat) : (term4 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem82435 n m p) (@lem82432)). Qed.
Lemma lem82439 (m : nat) (p : nat) : (term16 m p) = (term17 m p).
Proof. exact (fun_ext (fun n : nat => @lem82436 n m p)). Qed.
Lemma lem82440 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82441 (m : nat) (p : nat) : (term18 m p) = (term19 m p).
Proof. exact (MK_COMB (@lem82440) (@lem82439 m p)). Qed.
Lemma lem82446 (p : nat) : (term20 p) = (term21 p).
Proof. exact (fun_ext (fun m : nat => @lem82441 m p)). Qed.
Lemma lem82447 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82448 (p : nat) : (term22 p) = (term23 p).
Proof. exact (MK_COMB (@lem82447) (@lem82446 p)). Qed.
Lemma lem82453 : term24 = term25.
Proof. exact (fun_ext (fun p : nat => @lem82448 p)). Qed.
Lemma lem82454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82463 : term26 = term27.
Proof. exact (MK_COMB (@lem82454) (@lem82453)). Qed.
Lemma lem82464 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem82465 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem82464 m n p)). Qed.
Lemma lem82466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82467 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem82466) (@lem82465 m n)). Qed.
Lemma lem82468 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem82467 m n)). Qed.
Lemma lem82469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82470 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem82469) (@lem82468 m)). Qed.
Lemma lem82471 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem82470 m)). Qed.
Lemma lem82472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82473 : term10 = term10.
Proof. exact (MK_COMB (@lem82472) (@lem82471)). Qed.
Lemma lem82474 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem82475 : term9 = term9.
Proof. exact (MK_COMB (@lem82474) (@lem82473)). Qed.
Lemma lem82476 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem82477 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem82476 n m)). Qed.
Lemma lem82478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82479 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem82478) (@lem82477 m)). Qed.
Lemma lem82480 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem82479 m)). Qed.
Lemma lem82481 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82482 : term38 = term38.
Proof. exact (MK_COMB (@lem82481) (@lem82480)). Qed.
Lemma lem82483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem82484 : term11 = term11.
Proof. exact (MK_COMB (@lem82483) (@lem82482)). Qed.
Lemma lem82485 : term13 = term13.
Proof. exact (MK_COMB (@lem82484) (@lem82475)). Qed.
Lemma lem82498 (n : nat) (m : nat) (p : nat) : (term14 n m p) = (term14 n m p).
Proof. exact (eq_refl (term14 n m p)). Qed.
Lemma lem82499 (n : nat) (m : nat) (p : nat) : (term15 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem82498 n m p) (@lem82485)). Qed.
Lemma lem82500 (m : nat) (p : nat) : (term17 m p) = (term17 m p).
Proof. exact (fun_ext (fun n : nat => @lem82499 n m p)). Qed.
Lemma lem82501 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82502 (m : nat) (p : nat) : (term19 m p) = (term19 m p).
Proof. exact (MK_COMB (@lem82501) (@lem82500 m p)). Qed.
Lemma lem82503 (p : nat) : (term21 p) = (term21 p).
Proof. exact (fun_ext (fun m : nat => @lem82502 m p)). Qed.
Lemma lem82504 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82505 (p : nat) : (term23 p) = (term23 p).
Proof. exact (MK_COMB (@lem82504) (@lem82503 p)). Qed.
Lemma lem82506 : term25 = term25.
Proof. exact (fun_ext (fun p : nat => @lem82505 p)). Qed.
Lemma lem82507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82508 : term27 = term27.
Proof. exact (MK_COMB (@lem82507) (@lem82506)). Qed.
Lemma lem82567 : term26 = term27.
Proof. exact (TRANS (@lem82463) (@lem82508)). Qed.
Lemma lem82568 : term27 = term26.
Proof. exact (SYM (@lem82567)). Qed.
Lemma lem82569 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term3 n m p.
Proof. exact (h1). Qed.
Lemma lem82570 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem82571 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem82579 (n : nat) (m : nat) (p : nat) : (term39 n m p) = (term40 n m p).
Proof. exact (@lem17045 ((term29 m n p) = (term28 m n p)) ((term28 m n p) = (term28 n m p))). Qed.
Lemma lem82581 (n : nat) (m : nat) : (term41 n m) = (term41 n m).
Proof. exact (eq_refl (term41 n m)). Qed.
Lemma lem82582 (n : nat) (m : nat) (p : nat) : (term42 n m p) = (term43 n m p).
Proof. exact (MK_COMB (@lem82581 n m) (@lem82579 n m p)). Qed.
Lemma lem82583 (n : nat) (m : nat) (p : nat) : (term3 n m p) = (term42 n m p).
Proof. exact (@lem17045 ((Nat.mul m n) = (Nat.mul n m)) (term44 n m p)). Qed.
Lemma lem82588 (n : nat) (m : nat) (p : nat) : (term3 n m p) = (term43 n m p).
Proof. exact (TRANS (@lem82583 n m p) (@lem82582 n m p)). Qed.
Lemma lem82590 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem82591 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem82590 n m)). Qed.
Lemma lem82592 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82593 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem82592) (@lem82591 m)). Qed.
Lemma lem82594 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem82593 m)). Qed.
Lemma lem82595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82608 : term38 = term38.
Proof. exact (MK_COMB (@lem82595) (@lem82594)). Qed.
Lemma lem82609 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem82608) (@lem82570 h1)). Qed.
Lemma lem82610 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem82611 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem82610 m n p)). Qed.
Lemma lem82612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82613 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem82612) (@lem82611 m n)). Qed.
Lemma lem82614 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem82613 m n)). Qed.
Lemma lem82615 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82616 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem82615) (@lem82614 m)). Qed.
Lemma lem82617 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem82616 m)). Qed.
Lemma lem82618 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82635 : term10 = term10.
Proof. exact (MK_COMB (@lem82618) (@lem82617)). Qed.
Lemma lem82636 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem82635) (@lem82571 h1)). Qed.
Lemma lem82704 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term43 n m p.
Proof. exact (EQ_MP (@lem82588 n m p) (@lem82569 n m p h1)). Qed.
Lemma lem82717 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem82718 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem82717 n m)). Qed.
Lemma lem82719 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82720 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem82719) (@lem82718 m)). Qed.
Lemma lem82721 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem82720 m)). Qed.
Lemma lem82722 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82723 : term38 = term38.
Proof. exact (MK_COMB (@lem82722) (@lem82721)). Qed.
Lemma lem82724 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem82723) (@lem82609 h1)). Qed.
Lemma lem82745 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem82746 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem82745 m n p)). Qed.
Lemma lem82747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82748 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem82747) (@lem82746 m n)). Qed.
Lemma lem82749 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem82748 m n)). Qed.
Lemma lem82750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82751 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem82750) (@lem82749 m)). Qed.
Lemma lem82752 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem82751 m)). Qed.
Lemma lem82753 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82754 : term10 = term10.
Proof. exact (MK_COMB (@lem82753) (@lem82752)). Qed.
Lemma lem82755 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem82754) (@lem82636 h1)). Qed.
Lemma lem82757 (n : nat) (m : nat) (p : nat) (h1 : term40 n m p) : term40 n m p.
Proof. exact (h1). Qed.
Lemma lem82761 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem82762 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem82761 n m)). Qed.
Lemma lem82763 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82764 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem82763) (@lem82762 m)). Qed.
Lemma lem82765 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem82764 m)). Qed.
Lemma lem82766 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82768 : term38 = term38.
Proof. exact (MK_COMB (@lem82766) (@lem82765)). Qed.
Lemma lem82769 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem82768) (@lem82724 h1)). Qed.
Lemma lem82786 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem82798 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem82799 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem82798 m n p)). Qed.
Lemma lem82800 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82801 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem82800) (@lem82799 m n)). Qed.
Lemma lem82802 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem82801 m n)). Qed.
Lemma lem82803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82804 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem82803) (@lem82802 m)). Qed.
Lemma lem82805 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem82804 m)). Qed.
Lemma lem82806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82808 : term10 = term10.
Proof. exact (MK_COMB (@lem82806) (@lem82805)). Qed.
Lemma lem82809 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem82808) (@lem82755 h1)). Qed.
Lemma lem82813 (m : nat) (n : nat) (p : nat) (h1 : term46 m n p) : term46 m n p.
Proof. exact (h1). Qed.
Lemma lem82815 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem82816 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem82815 n m)). Qed.
Lemma lem82817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82818 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem82817) (@lem82816 m)). Qed.
Lemma lem82819 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem82818 m)). Qed.
Lemma lem82820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82822 : term38 = term38.
Proof. exact (MK_COMB (@lem82820) (@lem82819)). Qed.
Lemma lem82823 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem82822) (@lem82724 h1)). Qed.
Lemma lem82825 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term28 m n p) = (term29 m n p)).
Proof. exact (eq_refl ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem82826 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem82825 m n p)). Qed.
Lemma lem82827 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82828 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem82827) (@lem82826 m n)). Qed.
Lemma lem82829 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem82828 m n)). Qed.
Lemma lem82830 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82831 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem82830) (@lem82829 m)). Qed.
Lemma lem82832 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem82831 m)). Qed.
Lemma lem82833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82835 : term10 = term10.
Proof. exact (MK_COMB (@lem82833) (@lem82832)). Qed.
Lemma lem82836 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem82835) (@lem82755 h1)). Qed.
Lemma lem82840 (n : nat) (m : nat) (p : nat) (h1 : term47 n m p) : term47 n m p.
Proof. exact (h1). Qed.
Lemma lem82841 (_2187 : nat) (h1 : term38) : term48 _2187.
Proof. exact (@lem82769 h1 _2187). Qed.
Lemma lem82842 (_2187 : nat) : (term48 _2187) = (term36 _2187).
Proof. exact (eq_refl (term48 _2187)). Qed.
Lemma lem82843 (_2187 : nat) (h1 : term38) : term36 _2187.
Proof. exact (EQ_MP (@lem82842 _2187) (@lem82841 _2187 h1)). Qed.
Lemma lem82844 (_2187 : nat) (_2188 : nat) (h1 : term38) : term49 _2187 _2188.
Proof. exact (@lem82843 _2187 h1 _2188). Qed.
Lemma lem82845 (_2188 : nat) (_2187 : nat) : (term49 _2187 _2188) = ((Nat.mul _2187 _2188) = (Nat.mul _2188 _2187)).
Proof. exact (eq_refl (term49 _2187 _2188)). Qed.
Lemma lem82862 (_2194 : nat) (h1 : term10) : term50 _2194.
Proof. exact (@lem82809 h1 _2194). Qed.
Lemma lem82863 (_2194 : nat) : (term50 _2194) = (term33 _2194).
Proof. exact (eq_refl (term50 _2194)). Qed.
Lemma lem82864 (_2194 : nat) (h1 : term10) : term33 _2194.
Proof. exact (EQ_MP (@lem82863 _2194) (@lem82862 _2194 h1)). Qed.
Lemma lem82865 (_2194 : nat) (_2195 : nat) (h1 : term10) : term51 _2194 _2195.
Proof. exact (@lem82864 _2194 h1 _2195). Qed.
Lemma lem82866 (_2194 : nat) (_2195 : nat) : (term51 _2194 _2195) = (term31 _2194 _2195).
Proof. exact (eq_refl (term51 _2194 _2195)). Qed.
Lemma lem82867 (_2194 : nat) (_2195 : nat) (h1 : term10) : term31 _2194 _2195.
Proof. exact (EQ_MP (@lem82866 _2194 _2195) (@lem82865 _2194 _2195 h1)). Qed.
Lemma lem82868 (_2194 : nat) (_2195 : nat) (_2196 : nat) (h1 : term10) : term52 _2194 _2195 _2196.
Proof. exact (@lem82867 _2194 _2195 h1 _2196). Qed.
Lemma lem82869 (_2194 : nat) (_2195 : nat) (_2196 : nat) : (term52 _2194 _2195 _2196) = ((term28 _2194 _2195 _2196) = (term29 _2194 _2195 _2196)).
Proof. exact (eq_refl (term52 _2194 _2195 _2196)). Qed.
Lemma lem82871 (_2197 : nat) (h1 : term38) : term48 _2197.
Proof. exact (@lem82823 h1 _2197). Qed.
Lemma lem82872 (_2197 : nat) : (term48 _2197) = (term36 _2197).
Proof. exact (eq_refl (term48 _2197)). Qed.
Lemma lem82873 (_2197 : nat) (h1 : term38) : term36 _2197.
Proof. exact (EQ_MP (@lem82872 _2197) (@lem82871 _2197 h1)). Qed.
Lemma lem82874 (_2197 : nat) (_2198 : nat) (h1 : term38) : term49 _2197 _2198.
Proof. exact (@lem82873 _2197 h1 _2198). Qed.
Lemma lem82875 (_2198 : nat) (_2197 : nat) : (term49 _2197 _2198) = ((Nat.mul _2197 _2198) = (Nat.mul _2198 _2197)).
Proof. exact (eq_refl (term49 _2197 _2198)). Qed.
Lemma lem82877 (_2199 : nat) (h1 : term10) : term50 _2199.
Proof. exact (@lem82836 h1 _2199). Qed.
Lemma lem82878 (_2199 : nat) : (term50 _2199) = (term33 _2199).
Proof. exact (eq_refl (term50 _2199)). Qed.
Lemma lem82879 (_2199 : nat) (h1 : term10) : term33 _2199.
Proof. exact (EQ_MP (@lem82878 _2199) (@lem82877 _2199 h1)). Qed.
Lemma lem82880 (_2199 : nat) (_2200 : nat) (h1 : term10) : term51 _2199 _2200.
Proof. exact (@lem82879 _2199 h1 _2200). Qed.
Lemma lem82881 (_2199 : nat) (_2200 : nat) : (term51 _2199 _2200) = (term31 _2199 _2200).
Proof. exact (eq_refl (term51 _2199 _2200)). Qed.
Lemma lem82882 (_2199 : nat) (_2200 : nat) (h1 : term10) : term31 _2199 _2200.
Proof. exact (EQ_MP (@lem82881 _2199 _2200) (@lem82880 _2199 _2200 h1)). Qed.
Lemma lem82883 (_2199 : nat) (_2200 : nat) (_2201 : nat) (h1 : term10) : term52 _2199 _2200 _2201.
Proof. exact (@lem82882 _2199 _2200 h1 _2201). Qed.
Lemma lem82884 (_2199 : nat) (_2200 : nat) (_2201 : nat) : (term52 _2199 _2200 _2201) = ((term28 _2199 _2200 _2201) = (term29 _2199 _2200 _2201)).
Proof. exact (eq_refl (term52 _2199 _2200 _2201)). Qed.
Lemma lem82891 (n : nat) (m : nat) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem82897 (m : nat) (n : nat) (p : nat) (h1 : term46 m n p) : term46 m n p.
Proof. exact (h1). Qed.
Lemma lem82903 (n : nat) (m : nat) (p : nat) (h1 : term47 n m p) : term47 n m p.
Proof. exact (h1). Qed.
Lemma lem82922 (_2188 : nat) (_2187 : nat) (h1 : term38) : (Nat.mul _2187 _2188) = (Nat.mul _2188 _2187).
Proof. exact (EQ_MP (@lem82845 _2188 _2187) (@lem82844 _2187 _2188 h1)). Qed.
Lemma lem82923 (n : nat) (m : nat) (h1 : term38) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (@lem82922 n m h1). Qed.
Lemma lem82924 (n : nat) (m : nat) (h1 : term38) : term53 n m.
Proof. exact (fun h0 : term45 n m => @lem82923 n m h1). Qed.
Lemma lem82926 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem82927 (n : nat) (m : nat) : (term53 n m) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (@lem82926 ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem82928 (n : nat) (m : nat) (h1 : term38) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem82927 n m) (@lem82924 n m h1)). Qed.
Lemma lem82931 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem82933 (n : nat) (m : nat) : (term45 n m) = (term55 n m).
Proof. exact (@lem82931 ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem82936 (n : nat) (m : nat) (h1 : term45 n m) : term55 n m.
Proof. exact (EQ_MP (@lem82933 n m) (@lem82891 n m h1)). Qed.
Lemma lem82939 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (@lem82936 n m h2 (@lem82928 n m h1)). Qed.
Lemma lem82940 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : term56.
Proof. exact (fun h0 : ~ False => @lem82939 n m h1 h2). Qed.
Lemma lem82942 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem82943 : term56 = False.
Proof. exact (@lem82942 False). Qed.
Lemma lem82944 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem82943) (@lem82940 n m h1 h2)). Qed.
Lemma lem82961 (x : nat) (y : nat) (z : nat) : term57 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem82963 (_2194 : nat) (_2195 : nat) (_2196 : nat) (h1 : term10) : (term28 _2194 _2195 _2196) = (term29 _2194 _2195 _2196).
Proof. exact (EQ_MP (@lem82869 _2194 _2195 _2196) (@lem82868 _2194 _2195 _2196 h1)). Qed.
Lemma lem82964 (m : nat) (n : nat) (p : nat) (h1 : term10) : (term28 m n p) = (term29 m n p).
Proof. exact (@lem82963 m n p h1). Qed.
Lemma lem82965 (m : nat) (n : nat) (p : nat) (h1 : term10) : term58 m n p.
Proof. exact (fun h0 : term59 m n p => @lem82964 m n p h1). Qed.
Lemma lem82967 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem82968 (m : nat) (n : nat) (p : nat) : (term58 m n p) = ((term28 m n p) = (term29 m n p)).
Proof. exact (@lem82967 ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem82969 (m : nat) (n : nat) (p : nat) (h1 : term10) : (term28 m n p) = (term29 m n p).
Proof. exact (EQ_MP (@lem82968 m n p) (@lem82965 m n p h1)). Qed.
Lemma lem82971 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem82972 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (term28 m n p).
Proof. exact (@lem82971 (term28 m n p)). Qed.
Lemma lem82973 (m : nat) (n : nat) (p : nat) : term60 m n p.
Proof. exact (fun h0 : term61 m n p => @lem82972 m n p). Qed.
Lemma lem82975 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem82976 (m : nat) (n : nat) (p : nat) : (term60 m n p) = ((term28 m n p) = (term28 m n p)).
Proof. exact (@lem82975 ((term28 m n p) = (term28 m n p))). Qed.
Lemma lem82977 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (term28 m n p).
Proof. exact (EQ_MP (@lem82976 m n p) (@lem82973 m n p)). Qed.
Lemma lem82995 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem82996 (y : nat) (x : nat) (z : nat) : (term62 x y z) = (term63 y x z).
Proof. exact (@lem82995 (y = z) (term64 x z)). Qed.
Lemma lem83006 (x : nat) (y : nat) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem83007 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term66 y x z).
Proof. exact (MK_COMB (@lem83006 x y) (@lem82996 y x z)). Qed.
Lemma lem83011 (q : Prop) (p : Prop) (r : Prop) : (term67 p q r) = (term67 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem83012 (y : nat) (x : nat) (z : nat) : (term66 y x z) = (term68 y x z).
Proof. exact (@lem83011 (y = z) (term64 x y) (term64 x z)). Qed.
Lemma lem83034 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term68 y x z).
Proof. exact (TRANS (@lem83007 y x z) (@lem83012 y x z)). Qed.
Lemma lem83035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem83036 (y : nat) (x : nat) (z : nat) : (term69 x y z) = (term70 y x z).
Proof. exact (MK_COMB (@lem83035) (@lem83034 y x z)). Qed.
Lemma lem83058 (y : nat) (x : nat) (z : nat) : (term68 y x z) = (term68 y x z).
Proof. exact (eq_refl (term68 y x z)). Qed.
Lemma lem83059 (y : nat) (x : nat) (z : nat) : ((term57 x y z) = (term68 y x z)) = ((term68 y x z) = (term68 y x z)).
Proof. exact (MK_COMB (@lem83036 y x z) (@lem83058 y x z)). Qed.
Lemma lem83061 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem83062 (x : Prop) : (x = x) = True.
Proof. exact (@lem83061 Prop x). Qed.
Lemma lem83063 (y : nat) (x : nat) (z : nat) : ((term68 y x z) = (term68 y x z)) = True.
Proof. exact (@lem83062 (term68 y x z)). Qed.
Lemma lem83064 (y : nat) (x : nat) (z : nat) : ((term57 x y z) = (term68 y x z)) = True.
Proof. exact (TRANS (@lem83059 y x z) (@lem83063 y x z)). Qed.
Lemma lem83065 (y : nat) (x : nat) (z : nat) : True = ((term57 x y z) = (term68 y x z)).
Proof. exact (SYM (@lem83064 y x z)). Qed.
Lemma lem83066 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term68 y x z).
Proof. exact (EQ_MP (@lem83065 y x z) (@lem0)). Qed.
Lemma lem83067 (y : nat) (x : nat) (z : nat) : term68 y x z.
Proof. exact (EQ_MP (@lem83066 y x z) (@lem82961 x y z)). Qed.
Lemma lem83069 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem83070 (x : nat) (y : nat) (z : nat) : (term68 y x z) = (term72 x y z).
Proof. exact (@lem83069 (term73 y x z) (y = z)). Qed.
Lemma lem83072 (a : Prop) (b : Prop) : (term74 a b) = (term75 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem83073 (y : nat) (x : nat) (z : nat) : (term76 y x z) = (term77 y x z).
Proof. exact (@lem83072 (term64 x y) (term64 x z)). Qed.
Lemma lem83075 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem83076 (x : nat) (y : nat) : (term79 x y) = (x = y).
Proof. exact (@lem83075 (x = y)). Qed.
Lemma lem83077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem83078 (x : nat) (y : nat) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem83077) (@lem83076 x y)). Qed.
Lemma lem83080 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem83081 (x : nat) (z : nat) : (term79 x z) = (x = z).
Proof. exact (@lem83080 (x = z)). Qed.
Lemma lem83082 (y : nat) (x : nat) (z : nat) : (term77 y x z) = (term82 y x z).
Proof. exact (MK_COMB (@lem83078 x y) (@lem83081 x z)). Qed.
Lemma lem83083 (y : nat) (x : nat) (z : nat) : (term76 y x z) = (term82 y x z).
Proof. exact (TRANS (@lem83073 y x z) (@lem83082 y x z)). Qed.
Lemma lem83084 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83085 (y : nat) (x : nat) (z : nat) : (term83 y x z) = (term84 y x z).
Proof. exact (MK_COMB (@lem83084) (@lem83083 y x z)). Qed.
Lemma lem83086 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem83087 (x : nat) (y : nat) (z : nat) : (term72 x y z) = (term85 x y z).
Proof. exact (MK_COMB (@lem83085 y x z) (@lem83086 y z)). Qed.
Lemma lem83088 (x : nat) (y : nat) (z : nat) : (term68 y x z) = (term85 x y z).
Proof. exact (TRANS (@lem83070 x y z) (@lem83087 x y z)). Qed.
Lemma lem83090 (m : nat) (n : nat) (p : nat) (h1 : term10) : term86 m n p.
Proof. exact (conj (@lem82969 m n p h1) (@lem82977 m n p)). Qed.
Lemma lem83092 (x : nat) (y : nat) (z : nat) : term85 x y z.
Proof. exact (EQ_MP (@lem83088 x y z) (@lem83067 y x z)). Qed.
Lemma lem83093 (m : nat) (n : nat) (p : nat) : term87 m n p.
Proof. exact (@lem83092 (term28 m n p) (term29 m n p) (term28 m n p)). Qed.
Lemma lem83096 (m : nat) (n : nat) (p : nat) (h1 : term10) : (term29 m n p) = (term28 m n p).
Proof. exact (@lem83093 m n p (@lem83090 m n p h1)). Qed.
Lemma lem83097 (m : nat) (n : nat) (p : nat) (h1 : term10) : term88 m n p.
Proof. exact (fun h0 : term46 m n p => @lem83096 m n p h1). Qed.
Lemma lem83099 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83100 (m : nat) (n : nat) (p : nat) : (term88 m n p) = ((term29 m n p) = (term28 m n p)).
Proof. exact (@lem83099 ((term29 m n p) = (term28 m n p))). Qed.
Lemma lem83101 (m : nat) (n : nat) (p : nat) (h1 : term10) : (term29 m n p) = (term28 m n p).
Proof. exact (EQ_MP (@lem83100 m n p) (@lem83097 m n p h1)). Qed.
Lemma lem83104 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem83106 (m : nat) (n : nat) (p : nat) : (term46 m n p) = (term89 m n p).
Proof. exact (@lem83104 ((term29 m n p) = (term28 m n p))). Qed.
Lemma lem83109 (m : nat) (n : nat) (p : nat) (h1 : term46 m n p) : term89 m n p.
Proof. exact (EQ_MP (@lem83106 m n p) (@lem82897 m n p h1)). Qed.
Lemma lem83112 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (@lem83109 m n p h2 (@lem83101 m n p h1)). Qed.
Lemma lem83113 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : term56.
Proof. exact (fun h0 : ~ False => @lem83112 m n p h1 h2). Qed.
Lemma lem83115 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83116 : term56 = False.
Proof. exact (@lem83115 False). Qed.
Lemma lem83117 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem83116) (@lem83113 m n p h1 h2)). Qed.
Lemma lem83118 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem83119 (_2210 : nat) (_2212 : nat) (h1 : _2210 = _2212) : _2210 = _2212.
Proof. exact (h1). Qed.
Lemma lem83120 (_2211 : nat) (_2213 : nat) (h1 : _2211 = _2213) : _2211 = _2213.
Proof. exact (h1). Qed.
Lemma lem83121 (_2210 : nat) (_2212 : nat) (h1 : _2210 = _2212) : (Nat.mul _2210) = (Nat.mul _2212).
Proof. exact (MK_COMB (@lem83118) (@lem83119 _2210 _2212 h1)). Qed.
Lemma lem83122 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) (h1 : _2210 = _2212) (h2 : _2211 = _2213) : (Nat.mul _2210 _2211) = (Nat.mul _2212 _2213).
Proof. exact (MK_COMB (@lem83121 _2210 _2212 h1) (@lem83120 _2211 _2213 h2)). Qed.
Lemma lem83123 (_2211 : nat) (_2213 : nat) (_2210 : nat) (_2212 : nat) (h1 : _2210 = _2212) : term90 _2210 _2211 _2212 _2213.
Proof. exact (fun h0 : _2211 = _2213 => @lem83122 _2210 _2212 _2211 _2213 h1 h0). Qed.
Lemma lem83125 (a : Prop) (b : Prop) : (a -> b) = (term91 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem83126 (_2210 : nat) (_2211 : nat) (_2212 : nat) (_2213 : nat) : (term90 _2210 _2211 _2212 _2213) = (term92 _2210 _2211 _2212 _2213).
Proof. exact (@lem83125 (_2211 = _2213) ((Nat.mul _2210 _2211) = (Nat.mul _2212 _2213))). Qed.
Lemma lem83127 (_2211 : nat) (_2213 : nat) (_2210 : nat) (_2212 : nat) (h1 : _2210 = _2212) : term92 _2210 _2211 _2212 _2213.
Proof. exact (EQ_MP (@lem83126 _2210 _2211 _2212 _2213) (@lem83123 _2211 _2213 _2210 _2212 h1)). Qed.
Lemma lem83128 (_2210 : nat) (_2211 : nat) (_2212 : nat) (_2213 : nat) : term93 _2210 _2211 _2212 _2213.
Proof. exact (fun h0 : _2210 = _2212 => @lem83127 _2211 _2213 _2210 _2212 h0). Qed.
Lemma lem83130 (a : Prop) (b : Prop) : (a -> b) = (term91 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem83131 (_2210 : nat) (_2211 : nat) (_2212 : nat) (_2213 : nat) : (term93 _2210 _2211 _2212 _2213) = (term94 _2210 _2211 _2212 _2213).
Proof. exact (@lem83130 (_2210 = _2212) (term92 _2210 _2211 _2212 _2213)). Qed.
Lemma lem83132 (_2210 : nat) (_2211 : nat) (_2212 : nat) (_2213 : nat) : term94 _2210 _2211 _2212 _2213.
Proof. exact (EQ_MP (@lem83131 _2210 _2211 _2212 _2213) (@lem83128 _2210 _2211 _2212 _2213)). Qed.
Lemma lem83134 (x : nat) (y : nat) (z : nat) : term57 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem83136 (_2198 : nat) (_2197 : nat) (h1 : term38) : (Nat.mul _2197 _2198) = (Nat.mul _2198 _2197).
Proof. exact (EQ_MP (@lem82875 _2198 _2197) (@lem82874 _2197 _2198 h1)). Qed.
Lemma lem83137 (m : nat) (n : nat) (p : nat) (h1 : term38) : (term29 n p m) = (term28 m n p).
Proof. exact (@lem83136 m (Nat.mul n p) h1). Qed.
Lemma lem83138 (m : nat) (n : nat) (p : nat) (h1 : term38) : term95 m n p.
Proof. exact (fun h0 : term96 m n p => @lem83137 m n p h1). Qed.
Lemma lem83140 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83141 (m : nat) (n : nat) (p : nat) : (term95 m n p) = ((term29 n p m) = (term28 m n p)).
Proof. exact (@lem83140 ((term29 n p m) = (term28 m n p))). Qed.
Lemma lem83142 (m : nat) (n : nat) (p : nat) (h1 : term38) : (term29 n p m) = (term28 m n p).
Proof. exact (EQ_MP (@lem83141 m n p) (@lem83138 m n p h1)). Qed.
Lemma lem83144 (_2199 : nat) (_2200 : nat) (_2201 : nat) (h1 : term10) : (term28 _2199 _2200 _2201) = (term29 _2199 _2200 _2201).
Proof. exact (EQ_MP (@lem82884 _2199 _2200 _2201) (@lem82883 _2199 _2200 _2201 h1)). Qed.
Lemma lem83145 (n : nat) (p : nat) (m : nat) (h1 : term10) : (term28 n p m) = (term29 n p m).
Proof. exact (@lem83144 n p m h1). Qed.
Lemma lem83146 (n : nat) (p : nat) (m : nat) (h1 : term10) : term58 n p m.
Proof. exact (fun h0 : term59 n p m => @lem83145 n p m h1). Qed.
Lemma lem83148 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83149 (n : nat) (p : nat) (m : nat) : (term58 n p m) = ((term28 n p m) = (term29 n p m)).
Proof. exact (@lem83148 ((term28 n p m) = (term29 n p m))). Qed.
Lemma lem83150 (n : nat) (p : nat) (m : nat) (h1 : term10) : (term28 n p m) = (term29 n p m).
Proof. exact (EQ_MP (@lem83149 n p m) (@lem83146 n p m h1)). Qed.
Lemma lem83152 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem83153 (n : nat) : n = n.
Proof. exact (@lem83152 n). Qed.
Lemma lem83154 (n : nat) : term97 n.
Proof. exact (fun h0 : term98 n => @lem83153 n). Qed.
Lemma lem83156 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83157 (n : nat) : (term97 n) = (n = n).
Proof. exact (@lem83156 (n = n)). Qed.
Lemma lem83158 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem83157 n) (@lem83154 n)). Qed.
Lemma lem83160 (_2198 : nat) (_2197 : nat) (h1 : term38) : (Nat.mul _2197 _2198) = (Nat.mul _2198 _2197).
Proof. exact (EQ_MP (@lem82875 _2198 _2197) (@lem82874 _2197 _2198 h1)). Qed.
Lemma lem83161 (m : nat) (p : nat) (h1 : term38) : (Nat.mul p m) = (Nat.mul m p).
Proof. exact (@lem83160 m p h1). Qed.
Lemma lem83162 (m : nat) (p : nat) (h1 : term38) : term53 m p.
Proof. exact (fun h0 : term45 m p => @lem83161 m p h1). Qed.
Lemma lem83164 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83165 (m : nat) (p : nat) : (term53 m p) = ((Nat.mul p m) = (Nat.mul m p)).
Proof. exact (@lem83164 ((Nat.mul p m) = (Nat.mul m p))). Qed.
Lemma lem83166 (m : nat) (p : nat) (h1 : term38) : (Nat.mul p m) = (Nat.mul m p).
Proof. exact (EQ_MP (@lem83165 m p) (@lem83162 m p h1)). Qed.
Lemma lem83184 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem83185 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term92 _2210 _2211 _2212 _2213) = (term99 _2210 _2212 _2211 _2213).
Proof. exact (@lem83184 ((Nat.mul _2210 _2211) = (Nat.mul _2212 _2213)) (term64 _2211 _2213)). Qed.
Lemma lem83195 (_2210 : nat) (_2212 : nat) : (term65 _2210 _2212) = (term65 _2210 _2212).
Proof. exact (eq_refl (term65 _2210 _2212)). Qed.
Lemma lem83196 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term94 _2210 _2211 _2212 _2213) = (term100 _2210 _2212 _2211 _2213).
Proof. exact (MK_COMB (@lem83195 _2210 _2212) (@lem83185 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83200 (q : Prop) (p : Prop) (r : Prop) : (term67 p q r) = (term67 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem83201 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term100 _2210 _2212 _2211 _2213) = (term101 _2210 _2212 _2211 _2213).
Proof. exact (@lem83200 ((Nat.mul _2210 _2211) = (Nat.mul _2212 _2213)) (term64 _2210 _2212) (term64 _2211 _2213)). Qed.
Lemma lem83223 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term94 _2210 _2211 _2212 _2213) = (term101 _2210 _2212 _2211 _2213).
Proof. exact (TRANS (@lem83196 _2210 _2212 _2211 _2213) (@lem83201 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem83225 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term102 _2210 _2211 _2212 _2213) = (term103 _2210 _2212 _2211 _2213).
Proof. exact (MK_COMB (@lem83224) (@lem83223 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83247 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term101 _2210 _2212 _2211 _2213) = (term101 _2210 _2212 _2211 _2213).
Proof. exact (eq_refl (term101 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83248 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : ((term94 _2210 _2211 _2212 _2213) = (term101 _2210 _2212 _2211 _2213)) = ((term101 _2210 _2212 _2211 _2213) = (term101 _2210 _2212 _2211 _2213)).
Proof. exact (MK_COMB (@lem83225 _2210 _2212 _2211 _2213) (@lem83247 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83250 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem83251 (x : Prop) : (x = x) = True.
Proof. exact (@lem83250 Prop x). Qed.
Lemma lem83252 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : ((term101 _2210 _2212 _2211 _2213) = (term101 _2210 _2212 _2211 _2213)) = True.
Proof. exact (@lem83251 (term101 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83253 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : ((term94 _2210 _2211 _2212 _2213) = (term101 _2210 _2212 _2211 _2213)) = True.
Proof. exact (TRANS (@lem83248 _2210 _2212 _2211 _2213) (@lem83252 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83254 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : True = ((term94 _2210 _2211 _2212 _2213) = (term101 _2210 _2212 _2211 _2213)).
Proof. exact (SYM (@lem83253 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83255 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term94 _2210 _2211 _2212 _2213) = (term101 _2210 _2212 _2211 _2213).
Proof. exact (EQ_MP (@lem83254 _2210 _2212 _2211 _2213) (@lem0)). Qed.
Lemma lem83256 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : term101 _2210 _2212 _2211 _2213.
Proof. exact (EQ_MP (@lem83255 _2210 _2212 _2211 _2213) (@lem83132 _2210 _2211 _2212 _2213)). Qed.
Lemma lem83258 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem83259 (_2210 : nat) (_2211 : nat) (_2212 : nat) (_2213 : nat) : (term101 _2210 _2212 _2211 _2213) = (term104 _2210 _2211 _2212 _2213).
Proof. exact (@lem83258 (term105 _2210 _2212 _2211 _2213) ((Nat.mul _2210 _2211) = (Nat.mul _2212 _2213))). Qed.
Lemma lem83261 (a : Prop) (b : Prop) : (term74 a b) = (term75 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem83262 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term106 _2210 _2212 _2211 _2213) = (term107 _2210 _2212 _2211 _2213).
Proof. exact (@lem83261 (term64 _2210 _2212) (term64 _2211 _2213)). Qed.
Lemma lem83264 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem83265 (_2210 : nat) (_2212 : nat) : (term79 _2210 _2212) = (_2210 = _2212).
Proof. exact (@lem83264 (_2210 = _2212)). Qed.
Lemma lem83266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem83267 (_2210 : nat) (_2212 : nat) : (term80 _2210 _2212) = (term81 _2210 _2212).
Proof. exact (MK_COMB (@lem83266) (@lem83265 _2210 _2212)). Qed.
Lemma lem83269 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem83270 (_2211 : nat) (_2213 : nat) : (term79 _2211 _2213) = (_2211 = _2213).
Proof. exact (@lem83269 (_2211 = _2213)). Qed.
Lemma lem83271 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term107 _2210 _2212 _2211 _2213) = (term108 _2210 _2212 _2211 _2213).
Proof. exact (MK_COMB (@lem83267 _2210 _2212) (@lem83270 _2211 _2213)). Qed.
Lemma lem83272 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term106 _2210 _2212 _2211 _2213) = (term108 _2210 _2212 _2211 _2213).
Proof. exact (TRANS (@lem83262 _2210 _2212 _2211 _2213) (@lem83271 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83274 (_2210 : nat) (_2212 : nat) (_2211 : nat) (_2213 : nat) : (term109 _2210 _2212 _2211 _2213) = (term110 _2210 _2212 _2211 _2213).
Proof. exact (MK_COMB (@lem83273) (@lem83272 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83275 (_2210 : nat) (_2211 : nat) (_2212 : nat) (_2213 : nat) : ((Nat.mul _2210 _2211) = (Nat.mul _2212 _2213)) = ((Nat.mul _2210 _2211) = (Nat.mul _2212 _2213)).
Proof. exact (eq_refl ((Nat.mul _2210 _2211) = (Nat.mul _2212 _2213))). Qed.
Lemma lem83276 (_2210 : nat) (_2211 : nat) (_2212 : nat) (_2213 : nat) : (term104 _2210 _2211 _2212 _2213) = (term111 _2210 _2211 _2212 _2213).
Proof. exact (MK_COMB (@lem83274 _2210 _2212 _2211 _2213) (@lem83275 _2210 _2211 _2212 _2213)). Qed.
Lemma lem83277 (_2210 : nat) (_2211 : nat) (_2212 : nat) (_2213 : nat) : (term101 _2210 _2212 _2211 _2213) = (term111 _2210 _2211 _2212 _2213).
Proof. exact (TRANS (@lem83259 _2210 _2211 _2212 _2213) (@lem83276 _2210 _2211 _2212 _2213)). Qed.
Lemma lem83279 (n : nat) (m : nat) (p : nat) (h1 : term38) : term112 n m p.
Proof. exact (conj (@lem83158 n) (@lem83166 m p h1)). Qed.
Lemma lem83281 (_2210 : nat) (_2211 : nat) (_2212 : nat) (_2213 : nat) : term111 _2210 _2211 _2212 _2213.
Proof. exact (EQ_MP (@lem83277 _2210 _2211 _2212 _2213) (@lem83256 _2210 _2212 _2211 _2213)). Qed.
Lemma lem83282 (n : nat) (m : nat) (p : nat) : term113 n m p.
Proof. exact (@lem83281 n (Nat.mul p m) n (Nat.mul m p)). Qed.
Lemma lem83285 (n : nat) (m : nat) (p : nat) (h1 : term38) : (term28 n p m) = (term28 n m p).
Proof. exact (@lem83282 n m p (@lem83279 n m p h1)). Qed.
Lemma lem83286 (n : nat) (m : nat) (p : nat) (h1 : term38) : term114 n m p.
Proof. exact (fun h0 : term115 n m p => @lem83285 n m p h1). Qed.
Lemma lem83288 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83289 (n : nat) (m : nat) (p : nat) : (term114 n m p) = ((term28 n p m) = (term28 n m p)).
Proof. exact (@lem83288 ((term28 n p m) = (term28 n m p))). Qed.
Lemma lem83290 (n : nat) (m : nat) (p : nat) (h1 : term38) : (term28 n p m) = (term28 n m p).
Proof. exact (EQ_MP (@lem83289 n m p) (@lem83286 n m p h1)). Qed.
Lemma lem83308 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem83309 (y : nat) (x : nat) (z : nat) : (term62 x y z) = (term63 y x z).
Proof. exact (@lem83308 (y = z) (term64 x z)). Qed.
Lemma lem83319 (x : nat) (y : nat) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem83320 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term66 y x z).
Proof. exact (MK_COMB (@lem83319 x y) (@lem83309 y x z)). Qed.
Lemma lem83324 (q : Prop) (p : Prop) (r : Prop) : (term67 p q r) = (term67 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem83325 (y : nat) (x : nat) (z : nat) : (term66 y x z) = (term68 y x z).
Proof. exact (@lem83324 (y = z) (term64 x y) (term64 x z)). Qed.
Lemma lem83347 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term68 y x z).
Proof. exact (TRANS (@lem83320 y x z) (@lem83325 y x z)). Qed.
Lemma lem83348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem83349 (y : nat) (x : nat) (z : nat) : (term69 x y z) = (term70 y x z).
Proof. exact (MK_COMB (@lem83348) (@lem83347 y x z)). Qed.
Lemma lem83371 (y : nat) (x : nat) (z : nat) : (term68 y x z) = (term68 y x z).
Proof. exact (eq_refl (term68 y x z)). Qed.
Lemma lem83372 (y : nat) (x : nat) (z : nat) : ((term57 x y z) = (term68 y x z)) = ((term68 y x z) = (term68 y x z)).
Proof. exact (MK_COMB (@lem83349 y x z) (@lem83371 y x z)). Qed.
Lemma lem83374 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem83375 (x : Prop) : (x = x) = True.
Proof. exact (@lem83374 Prop x). Qed.
Lemma lem83376 (y : nat) (x : nat) (z : nat) : ((term68 y x z) = (term68 y x z)) = True.
Proof. exact (@lem83375 (term68 y x z)). Qed.
Lemma lem83377 (y : nat) (x : nat) (z : nat) : ((term57 x y z) = (term68 y x z)) = True.
Proof. exact (TRANS (@lem83372 y x z) (@lem83376 y x z)). Qed.
Lemma lem83378 (y : nat) (x : nat) (z : nat) : True = ((term57 x y z) = (term68 y x z)).
Proof. exact (SYM (@lem83377 y x z)). Qed.
Lemma lem83379 (y : nat) (x : nat) (z : nat) : (term57 x y z) = (term68 y x z).
Proof. exact (EQ_MP (@lem83378 y x z) (@lem0)). Qed.
Lemma lem83380 (y : nat) (x : nat) (z : nat) : term68 y x z.
Proof. exact (EQ_MP (@lem83379 y x z) (@lem83134 x y z)). Qed.
Lemma lem83382 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem83383 (x : nat) (y : nat) (z : nat) : (term68 y x z) = (term72 x y z).
Proof. exact (@lem83382 (term73 y x z) (y = z)). Qed.
Lemma lem83385 (a : Prop) (b : Prop) : (term74 a b) = (term75 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem83386 (y : nat) (x : nat) (z : nat) : (term76 y x z) = (term77 y x z).
Proof. exact (@lem83385 (term64 x y) (term64 x z)). Qed.
Lemma lem83388 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem83389 (x : nat) (y : nat) : (term79 x y) = (x = y).
Proof. exact (@lem83388 (x = y)). Qed.
Lemma lem83390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem83391 (x : nat) (y : nat) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem83390) (@lem83389 x y)). Qed.
Lemma lem83393 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem83394 (x : nat) (z : nat) : (term79 x z) = (x = z).
Proof. exact (@lem83393 (x = z)). Qed.
Lemma lem83395 (y : nat) (x : nat) (z : nat) : (term77 y x z) = (term82 y x z).
Proof. exact (MK_COMB (@lem83391 x y) (@lem83394 x z)). Qed.
Lemma lem83396 (y : nat) (x : nat) (z : nat) : (term76 y x z) = (term82 y x z).
Proof. exact (TRANS (@lem83386 y x z) (@lem83395 y x z)). Qed.
Lemma lem83397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83398 (y : nat) (x : nat) (z : nat) : (term83 y x z) = (term84 y x z).
Proof. exact (MK_COMB (@lem83397) (@lem83396 y x z)). Qed.
Lemma lem83399 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem83400 (x : nat) (y : nat) (z : nat) : (term72 x y z) = (term85 x y z).
Proof. exact (MK_COMB (@lem83398 y x z) (@lem83399 y z)). Qed.
Lemma lem83401 (x : nat) (y : nat) (z : nat) : (term68 y x z) = (term85 x y z).
Proof. exact (TRANS (@lem83383 x y z) (@lem83400 x y z)). Qed.
Lemma lem83403 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : term116 n m p.
Proof. exact (conj (@lem83150 n p m h1) (@lem83290 n m p h2)). Qed.
Lemma lem83405 (x : nat) (y : nat) (z : nat) : term85 x y z.
Proof. exact (EQ_MP (@lem83401 x y z) (@lem83380 y x z)). Qed.
Lemma lem83406 (n : nat) (m : nat) (p : nat) : term117 n m p.
Proof. exact (@lem83405 (term28 n p m) (term29 n p m) (term28 n m p)). Qed.
Lemma lem83409 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : (term29 n p m) = (term28 n m p).
Proof. exact (@lem83406 n m p (@lem83403 n m p h1 h2)). Qed.
Lemma lem83410 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : term118 n m p.
Proof. exact (fun h0 : term119 n m p => @lem83409 n m p h1 h2). Qed.
Lemma lem83412 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83413 (n : nat) (m : nat) (p : nat) : (term118 n m p) = ((term29 n p m) = (term28 n m p)).
Proof. exact (@lem83412 ((term29 n p m) = (term28 n m p))). Qed.
Lemma lem83414 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : (term29 n p m) = (term28 n m p).
Proof. exact (EQ_MP (@lem83413 n m p) (@lem83410 n m p h1 h2)). Qed.
Lemma lem83415 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : term120 n m p.
Proof. exact (conj (@lem83142 m n p h2) (@lem83414 n m p h1 h2)). Qed.
Lemma lem83417 (x : nat) (y : nat) (z : nat) : term85 x y z.
Proof. exact (EQ_MP (@lem83401 x y z) (@lem83380 y x z)). Qed.
Lemma lem83418 (n : nat) (m : nat) (p : nat) : term121 n m p.
Proof. exact (@lem83417 (term29 n p m) (term28 m n p) (term28 n m p)). Qed.
Lemma lem83421 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : (term28 m n p) = (term28 n m p).
Proof. exact (@lem83418 n m p (@lem83415 n m p h1 h2)). Qed.
Lemma lem83422 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : term122 n m p.
Proof. exact (fun h0 : term47 n m p => @lem83421 n m p h1 h2). Qed.
Lemma lem83424 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83425 (n : nat) (m : nat) (p : nat) : (term122 n m p) = ((term28 m n p) = (term28 n m p)).
Proof. exact (@lem83424 ((term28 m n p) = (term28 n m p))). Qed.
Lemma lem83426 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) : (term28 m n p) = (term28 n m p).
Proof. exact (EQ_MP (@lem83425 n m p) (@lem83422 n m p h1 h2)). Qed.
Lemma lem83429 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem83431 (n : nat) (m : nat) (p : nat) : (term47 n m p) = (term123 n m p).
Proof. exact (@lem83429 ((term28 m n p) = (term28 n m p))). Qed.
Lemma lem83434 (n : nat) (m : nat) (p : nat) (h1 : term47 n m p) : term123 n m p.
Proof. exact (EQ_MP (@lem83431 n m p) (@lem82903 n m p h1)). Qed.
Lemma lem83437 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (@lem83434 n m p h3 (@lem83426 n m p h1 h2)). Qed.
Lemma lem83438 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : term56.
Proof. exact (fun h0 : ~ False => @lem83437 n m p h1 h2 h3). Qed.
Lemma lem83440 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem83441 : term56 = False.
Proof. exact (@lem83440 False). Qed.
Lemma lem83442 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem83441) (@lem83438 n m p h1 h2 h3)). Qed.
Lemma lem83443 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : (term47 n m p) = False.
Proof. exact (prop_ext (fun h4 : term47 n m p => @lem83442 n m p h1 h2 h3) (fun h4 : False => @lem82903 n m p h3)). Qed.
Lemma lem83444 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem83443 n m p h1 h2 h3) (@lem82903 n m p h3)). Qed.
Lemma lem83445 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : (term46 m n p) = False.
Proof. exact (prop_ext (fun h3 : term46 m n p => @lem83117 m n p h1 h2) (fun h3 : False => @lem82897 m n p h2)). Qed.
Lemma lem83446 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem83445 m n p h1 h2) (@lem82897 m n p h2)). Qed.
Lemma lem83447 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h3 : term45 n m => @lem82944 n m h1 h2) (fun h3 : False => @lem82891 n m h2)). Qed.
Lemma lem83448 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem83447 n m h1 h2) (@lem82891 n m h2)). Qed.
Lemma lem83449 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : (term47 n m p) = False.
Proof. exact (prop_ext (fun h4 : term47 n m p => @lem83444 n m p h1 h2 h3) (fun h4 : False => @lem82840 n m p h3)). Qed.
Lemma lem83450 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem83449 n m p h1 h2 h3) (@lem82840 n m p h3)). Qed.
Lemma lem83451 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : (term46 m n p) = False.
Proof. exact (prop_ext (fun h3 : term46 m n p => @lem83446 m n p h1 h2) (fun h3 : False => @lem82813 m n p h2)). Qed.
Lemma lem83452 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem83451 m n p h1 h2) (@lem82813 m n p h2)). Qed.
Lemma lem83453 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h3 : term45 n m => @lem83448 n m h1 h2) (fun h3 : False => @lem82786 n m h2)). Qed.
Lemma lem83454 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem83453 n m h1 h2) (@lem82786 n m h2)). Qed.
Lemma lem83455 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : (term47 n m p) = False.
Proof. exact (prop_ext (fun h4 : term47 n m p => @lem83450 n m p h1 h2 h3) (fun h4 : False => @lem82840 n m p h3)). Qed.
Lemma lem83456 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem83455 n m p h1 h2 h3) (@lem82840 n m p h3)). Qed.
Lemma lem83457 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem83456 n m p h1 h2 h3) (fun h4 : False => @lem82836 h1)). Qed.
Lemma lem83458 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem83457 n m p h1 h2 h3) (@lem82836 h1)). Qed.
Lemma lem83459 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : term38 = False.
Proof. exact (prop_ext (fun h4 : term38 => @lem83458 n m p h1 h2 h3) (fun h4 : False => @lem82823 h2)). Qed.
Lemma lem83460 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem83459 n m p h1 h2 h3) (@lem82823 h2)). Qed.
Lemma lem83461 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : (term46 m n p) = False.
Proof. exact (prop_ext (fun h3 : term46 m n p => @lem83452 m n p h1 h2) (fun h3 : False => @lem82813 m n p h2)). Qed.
Lemma lem83462 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem83461 m n p h1 h2) (@lem82813 m n p h2)). Qed.
Lemma lem83463 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem83462 m n p h1 h2) (fun h3 : False => @lem82809 h1)). Qed.
Lemma lem83464 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem83463 m n p h1 h2) (@lem82809 h1)). Qed.
Lemma lem83465 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h3 : term45 n m => @lem83454 n m h1 h2) (fun h3 : False => @lem82786 n m h2)). Qed.
Lemma lem83466 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem83465 n m h1 h2) (@lem82786 n m h2)). Qed.
Lemma lem83467 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : term38 = False.
Proof. exact (prop_ext (fun h3 : term38 => @lem83466 n m h1 h2) (fun h3 : False => @lem82769 h1)). Qed.
Lemma lem83468 (n : nat) (m : nat) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem83467 n m h1 h2) (@lem82769 h1)). Qed.
Lemma lem83469 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term40 n m p) : False.
Proof. exact (or_elim (@lem82757 n m p h3) (fun h0 : term46 m n p => @lem83464 m n p h1 h0) (fun h0 : term47 n m p => @lem83460 n m p h1 h2 h0)). Qed.
Lemma lem83470 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (or_elim (@lem82704 n m p h3) (fun h0 : term45 n m => @lem83468 n m h2 h0) (fun h0 : term40 n m p => @lem83469 n m p h1 h2 h0)). Qed.
Lemma lem83471 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem83470 n m p h1 h2 h3) (fun h4 : False => @lem82755 h1)). Qed.
Lemma lem83472 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem83471 n m p h1 h2 h3) (@lem82755 h1)). Qed.
Lemma lem83473 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term38 = False.
Proof. exact (prop_ext (fun h4 : term38 => @lem83472 n m p h1 h2 h3) (fun h4 : False => @lem82724 h2)). Qed.
Lemma lem83474 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem83473 n m p h1 h2 h3) (@lem82724 h2)). Qed.
Lemma lem83475 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem83474 n m p h1 h2 h3) (fun h4 : False => @lem82636 h1)). Qed.
Lemma lem83476 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem83475 n m p h1 h2 h3) (@lem82636 h1)). Qed.
Lemma lem83477 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term38 = False.
Proof. exact (prop_ext (fun h4 : term38 => @lem83476 n m p h1 h2 h3) (fun h4 : False => @lem82609 h2)). Qed.
Lemma lem83478 (n : nat) (m : nat) (p : nat) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem83477 n m p h1 h2 h3) (@lem82609 h2)). Qed.
Lemma lem83479 (n : nat) (m : nat) (p : nat) (h1 : term38) (h2 : term3 n m p) : term8.
Proof. exact (fun h0 : term10 => @lem83478 n m p h0 h1 h2). Qed.
Lemma lem83480 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem83481 (n : nat) (m : nat) (p : nat) (h1 : term38) (h2 : term3 n m p) : term9.
Proof. exact (EQ_MP (@lem83480) (@lem83479 n m p h1 h2)). Qed.
Lemma lem83482 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term13.
Proof. exact (fun h0 : term38 => @lem83481 n m p h0 h1). Qed.
Lemma lem83483 (n : nat) (m : nat) (p : nat) : term15 n m p.
Proof. exact (fun h0 : term3 n m p => @lem83482 n m p h0). Qed.
Lemma lem83488 (m : nat) (p : nat) : term19 m p.
Proof. exact (fun n : nat => @lem83483 n m p). Qed.
Lemma lem83493 (p : nat) : term23 p.
Proof. exact (fun m : nat => @lem83488 m p). Qed.
Lemma lem83498 : term27.
Proof. exact (fun p : nat => @lem83493 p). Qed.
Lemma lem83499 : term26.
Proof. exact (EQ_MP (@lem82568) (@lem83498)). Qed.
Lemma lem83500 (p : nat) : term124 p.
Proof. exact (@lem83499 p). Qed.
Lemma lem83501 (p : nat) : (term124 p) = (term22 p).
Proof. exact (eq_refl (term124 p)). Qed.
Lemma lem83502 (p : nat) : term22 p.
Proof. exact (EQ_MP (@lem83501 p) (@lem83500 p)). Qed.
Lemma lem83503 (p : nat) (m : nat) : term125 p m.
Proof. exact (@lem83502 p m). Qed.
Lemma lem83504 (m : nat) (p : nat) : (term125 p m) = (term18 m p).
Proof. exact (eq_refl (term125 p m)). Qed.
Lemma lem83505 (m : nat) (p : nat) : term18 m p.
Proof. exact (EQ_MP (@lem83504 m p) (@lem83503 p m)). Qed.
Lemma lem83506 (m : nat) (p : nat) (n : nat) : term126 m p n.
Proof. exact (@lem83505 m p n). Qed.
Lemma lem83507 (n : nat) (m : nat) (p : nat) : (term126 m p n) = (term4 n m p).
Proof. exact (eq_refl (term126 m p n)). Qed.
Lemma lem83508 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (EQ_MP (@lem83507 n m p) (@lem83506 m p n)). Qed.
Lemma lem83510 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem82387 n m p (@lem83508 n m p)). Qed.
Lemma lem83511 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term12.
Proof. exact (@lem83510 n m p (@lem82372 n m p h1)). Qed.
Lemma lem83512 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : term8.
Proof. exact (@lem83511 n m p h1 (@lem81820)). Qed.
Lemma lem83513 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : False.
Proof. exact (@lem83512 n m p h1 (@lem82357)). Qed.
Lemma lem83514 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : (term3 n m p) = False.
Proof. exact (prop_ext (fun h2 : term3 n m p => @lem83513 n m p h1) (fun h2 : False => @lem82372 n m p h1)). Qed.
Lemma lem83515 (n : nat) (m : nat) (p : nat) (h1 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem83514 n m p h1) (@lem82372 n m p h1)). Qed.
Lemma lem83516 (n : nat) (m : nat) (p : nat) : term2 n m p.
Proof. exact (fun h0 : term3 n m p => @lem83515 n m p h0). Qed.
Lemma lem83517 (n : nat) (m : nat) (p : nat) : term1 n m p.
Proof. exact (EQ_MP (@lem82371 n m p) (@lem83516 n m p)). Qed.
