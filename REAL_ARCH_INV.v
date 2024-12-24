Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ARCH_INV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import MONO_EXISTS_spec.
Require Import REAL_ARCH_LT_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_LT_ANTISYM_spec.
Require Import REAL_LT_INV2_spec.
Require Import REAL_LT_INV_EQ_spec.
Require Import REAL_LT_TRANS_spec.
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
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Lemma lem1700439 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1700440 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1700441 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1700440 t1) (@lem1700439 t1)). Qed.
Lemma lem1700442 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1700441 t1 t2). Qed.
Lemma lem1700443 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1700444 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1700443 t1 t2) (@lem1700442 t1 t2)). Qed.
Lemma lem1700445 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1700444 t1 t2 t3). Qed.
Lemma lem1700446 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1700447 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1700446 t1 t2 t3) (@lem1700445 t1 t2 t3)). Qed.
Lemma lem1700448 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1700447 t1 t2 t3)). Qed.
Lemma lem1700449 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (h1). Qed.
Lemma lem1700450 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term8 A P Q.
Proof. exact (h1). Qed.
Lemma lem1700451 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term7 A P Q) : term9 A P Q.
Proof. exact (@lem1700449 A P Q h2 (@lem1700450 A P Q h1)). Qed.
Lemma lem1700452 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term10 A P Q.
Proof. exact (fun h0 : term7 A P Q => @lem1700451 A P Q h1 h0). Qed.
Lemma lem1700453 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (h1). Qed.
Lemma lem1700454 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term7 A P Q) : term9 A P Q.
Proof. exact (@lem1700452 A P Q h1 (@lem1700453 A P Q h2)). Qed.
Lemma lem1700455 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (fun h0 : term8 A P Q => @lem1700454 A P Q h0 h1). Qed.
Lemma lem1700456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term11 A P Q.
Proof. exact (fun h0 : term7 A P Q => @lem1700455 A P Q h0). Qed.
Lemma lem1700458 (e : real) : term12 e.
Proof. exact (@lem1699575 (real_inv e)). Qed.
Lemma lem1700459 (e : real) : (term12 e) = (term13 e).
Proof. exact (eq_refl (term12 e)). Qed.
Lemma lem1700460 (e : real) : term13 e.
Proof. exact (EQ_MP (@lem1700459 e) (@lem1700458 e)). Qed.
Lemma lem1700461 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1700462 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1700463 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1700462 t1) (@lem1700461 t1)). Qed.
Lemma lem1700464 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1700463 t1 t2). Qed.
Lemma lem1700465 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1700466 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1700465 t1 t2) (@lem1700464 t1 t2)). Qed.
Lemma lem1700467 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1700466 t1 t2 t3). Qed.
Lemma lem1700468 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1700469 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1700468 t1 t2 t3) (@lem1700467 t1 t2 t3)). Qed.
Lemma lem1700470 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1700469 t1 t2 t3)). Qed.
Lemma lem1700472 (p : Prop) : p = (term14 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1700473 (e : real) : (term15 e) = (term16 e).
Proof. exact (@lem1700472 (term15 e)). Qed.
Lemma lem1700474 (e : real) : (term16 e) = (term15 e).
Proof. exact (SYM (@lem1700473 e)). Qed.
Lemma lem1700475 (e : real) (h1 : term17 e) : term17 e.
Proof. exact (h1). Qed.
Lemma lem1700478 (e : real) (h1 : term18 e) : term18 e.
Proof. exact (h1). Qed.
Lemma lem1700479 (e : real) : term19 e.
Proof. exact (fun h0 : term18 e => @lem1700478 e h0). Qed.
Lemma lem1700480 (e : real) (h1 : term19 e) : term19 e.
Proof. exact (h1). Qed.
Lemma lem1700481 (e : real) (h1 : term18 e) : term18 e.
Proof. exact (h1). Qed.
Lemma lem1700482 (e : real) (h1 : term18 e) (h2 : term19 e) : term18 e.
Proof. exact (@lem1700480 e h2 (@lem1700481 e h1)). Qed.
Lemma lem1700483 (e : real) (h1 : term18 e) : term20 e.
Proof. exact (fun h0 : term19 e => @lem1700482 e h1 h0). Qed.
Lemma lem1700484 (e : real) (h1 : term19 e) : term19 e.
Proof. exact (h1). Qed.
Lemma lem1700485 (e : real) (h1 : term18 e) (h2 : term19 e) : term18 e.
Proof. exact (@lem1700483 e h1 (@lem1700484 e h2)). Qed.
Lemma lem1700486 (e : real) (h1 : term19 e) : term19 e.
Proof. exact (fun h0 : term18 e => @lem1700485 e h0 h1). Qed.
Lemma lem1700487 (e : real) : term21 e.
Proof. exact (fun h0 : term19 e => @lem1700486 e h0). Qed.
Lemma lem1700490 (e : real) : term19 e.
Proof. exact (@lem1700487 e (@lem1700479 e)). Qed.
Lemma lem1700552 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1700553 : term22 = term23.
Proof. exact (@lem1700552 term24). Qed.
Lemma lem1700570 (e : real) : (term25 e) = (term25 e).
Proof. exact (eq_refl (term25 e)). Qed.
Lemma lem1700571 (e : real) : (term18 e) = (term26 e).
Proof. exact (MK_COMB (@lem1700570 e) (@lem1700553)). Qed.
Lemma lem1700574 : term27 = term28.
Proof. exact (fun_ext (fun e : real => @lem1700571 e)). Qed.
Lemma lem1700575 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700584 : term29 = term30.
Proof. exact (MK_COMB (@lem1700575) (@lem1700574)). Qed.
Lemma lem1700593 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem1700594 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem1700593 y x z)). Qed.
Lemma lem1700595 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700596 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem1700595) (@lem1700594 y x)). Qed.
Lemma lem1700597 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1700596 y x)). Qed.
Lemma lem1700598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700599 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1700598) (@lem1700597 x)). Qed.
Lemma lem1700600 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1700599 x)). Qed.
Lemma lem1700601 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700602 : term24 = term24.
Proof. exact (MK_COMB (@lem1700601) (@lem1700600)). Qed.
Lemma lem1700603 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1700604 : term23 = term23.
Proof. exact (MK_COMB (@lem1700603) (@lem1700602)). Qed.
Lemma lem1700605 (e : real) : (term37 e) = (term37 e).
Proof. exact (eq_refl (term37 e)). Qed.
Lemma lem1700616 (n : nat) (e : real) : (term38 n e) = (term38 n e).
Proof. exact (eq_refl (term38 n e)). Qed.
Lemma lem1700617 (e : real) : (term39 e) = (term39 e).
Proof. exact (fun_ext (fun n : nat => @lem1700616 n e)). Qed.
Lemma lem1700618 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1700619 (e : real) : (term40 e) = (term40 e).
Proof. exact (MK_COMB (@lem1700618) (@lem1700617 e)). Qed.
Lemma lem1700620 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1700621 (e : real) : (term41 e) = (term41 e).
Proof. exact (MK_COMB (@lem1700620) (@lem1700619 e)). Qed.
Lemma lem1700622 (e : real) : (term15 e) = (term15 e).
Proof. exact (MK_COMB (@lem1700621 e) (@lem1700605 e)). Qed.
Lemma lem1700623 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1700624 (e : real) : (term17 e) = (term17 e).
Proof. exact (MK_COMB (@lem1700623) (@lem1700622 e)). Qed.
Lemma lem1700625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1700626 (e : real) : (term25 e) = (term25 e).
Proof. exact (MK_COMB (@lem1700625) (@lem1700624 e)). Qed.
Lemma lem1700627 (e : real) : (term26 e) = (term26 e).
Proof. exact (MK_COMB (@lem1700626 e) (@lem1700604)). Qed.
Lemma lem1700628 : term28 = term28.
Proof. exact (fun_ext (fun e : real => @lem1700627 e)). Qed.
Lemma lem1700629 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700630 : term30 = term30.
Proof. exact (MK_COMB (@lem1700629) (@lem1700628)). Qed.
Lemma lem1700675 : term29 = term30.
Proof. exact (TRANS (@lem1700584) (@lem1700630)). Qed.
Lemma lem1700676 : term30 = term29.
Proof. exact (SYM (@lem1700675)). Qed.
Lemma lem1700677 (e : real) (h1 : term17 e) : term17 e.
Proof. exact (h1). Qed.
Lemma lem1700678 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1700687 (n : nat) (e : real) : (term38 n e) = (term38 n e).
Proof. exact (eq_refl (term38 n e)). Qed.
Lemma lem1700688 (e : real) : (term39 e) = (term39 e).
Proof. exact (fun_ext (fun n : nat => @lem1700687 n e)). Qed.
Lemma lem1700689 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1700690 (e : real) : (term40 e) = (term40 e).
Proof. exact (MK_COMB (@lem1700689) (@lem1700688 e)). Qed.
Lemma lem1700691 (e : real) : (term42 e) = (term42 e).
Proof. exact (eq_refl (term42 e)). Qed.
Lemma lem1700692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1700693 (e : real) : (term43 e) = (term43 e).
Proof. exact (MK_COMB (@lem1700692) (@lem1700690 e)). Qed.
Lemma lem1700694 (e : real) : (term44 e) = (term44 e).
Proof. exact (MK_COMB (@lem1700693 e) (@lem1700691 e)). Qed.
Lemma lem1700695 (e : real) : (term17 e) = (term44 e).
Proof. exact (@lem17362 (term40 e) (term37 e)). Qed.
Lemma lem1700696 (e : real) : (term17 e) = (term44 e).
Proof. exact (TRANS (@lem1700695 e) (@lem1700694 e)). Qed.
Lemma lem1700747 {A : Type'} (P : A -> Prop) (Q : Prop) : (term45 A P Q) = (term46 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1700748 (P : nat -> Prop) (Q : Prop) : (term47 P Q) = (term48 P Q).
Proof. exact (@lem1700747 nat P Q). Qed.
Lemma lem1700749 (e : real) : (term49 e) = (term50 e).
Proof. exact (@lem1700748 (term39 e) (term42 e)). Qed.
Lemma lem1700750 (n : nat) (e : real) : (term51 e n) = (term38 n e).
Proof. exact (eq_refl (term51 e n)). Qed.
Lemma lem1700751 (e : real) : (term52 e) = (term39 e).
Proof. exact (fun_ext (fun n : nat => @lem1700750 n e)). Qed.
Lemma lem1700752 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1700753 (e : real) : (term53 e) = (term40 e).
Proof. exact (MK_COMB (@lem1700752) (@lem1700751 e)). Qed.
Lemma lem1700754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1700755 (e : real) : (term54 e) = (term43 e).
Proof. exact (MK_COMB (@lem1700754) (@lem1700753 e)). Qed.
Lemma lem1700756 (e : real) : (term42 e) = (term42 e).
Proof. exact (eq_refl (term42 e)). Qed.
Lemma lem1700757 (e : real) : (term49 e) = (term44 e).
Proof. exact (MK_COMB (@lem1700755 e) (@lem1700756 e)). Qed.
Lemma lem1700758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1700759 (e : real) : (term55 e) = (term56 e).
Proof. exact (MK_COMB (@lem1700758) (@lem1700757 e)). Qed.
Lemma lem1700760 (n : nat) (e : real) : (term51 e n) = (term38 n e).
Proof. exact (eq_refl (term51 e n)). Qed.
Lemma lem1700761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1700762 (n : nat) (e : real) : (term57 e n) = (term58 n e).
Proof. exact (MK_COMB (@lem1700761) (@lem1700760 n e)). Qed.
Lemma lem1700763 (e : real) : (term42 e) = (term42 e).
Proof. exact (eq_refl (term42 e)). Qed.
Lemma lem1700764 (n : nat) (e : real) : (term59 n e) = (term60 n e).
Proof. exact (MK_COMB (@lem1700762 n e) (@lem1700763 e)). Qed.
Lemma lem1700765 (e : real) : (term61 e) = (term62 e).
Proof. exact (fun_ext (fun n : nat => @lem1700764 n e)). Qed.
Lemma lem1700766 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1700767 (e : real) : (term50 e) = (term63 e).
Proof. exact (MK_COMB (@lem1700766) (@lem1700765 e)). Qed.
Lemma lem1700768 (e : real) : ((term49 e) = (term50 e)) = ((term44 e) = (term63 e)).
Proof. exact (MK_COMB (@lem1700759 e) (@lem1700767 e)). Qed.
Lemma lem1700770 (e : real) : (term44 e) = (term63 e).
Proof. exact (EQ_MP (@lem1700768 e) (@lem1700749 e)). Qed.
Lemma lem1700771 (e : real) : (term17 e) = (term63 e).
Proof. exact (TRANS (@lem1700696 e) (@lem1700770 e)). Qed.
Lemma lem1700772 (e : real) (h1 : term17 e) : term63 e.
Proof. exact (EQ_MP (@lem1700771 e) (@lem1700677 e h1)). Qed.
Lemma lem1700779 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (@lem17045 (real_lt x y) (real_lt y z)). Qed.
Lemma lem1700780 (x : real) (z : real) : (real_lt x z) = (real_lt x z).
Proof. exact (eq_refl (real_lt x z)). Qed.
Lemma lem1700781 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1700782 (x : real) (y : real) (z : real) : (term66 x y z) = (term67 x y z).
Proof. exact (MK_COMB (@lem1700781) (@lem1700779 x y z)). Qed.
Lemma lem1700783 (y : real) (x : real) (z : real) : (term68 y x z) = (term69 y x z).
Proof. exact (MK_COMB (@lem1700782 x y z) (@lem1700780 x z)). Qed.
Lemma lem1700784 (y : real) (x : real) (z : real) : (term31 y x z) = (term68 y x z).
Proof. exact (@lem17265 (term70 x y z) (real_lt x z)). Qed.
Lemma lem1700785 (y : real) (x : real) (z : real) : (term31 y x z) = (term69 y x z).
Proof. exact (TRANS (@lem1700784 y x z) (@lem1700783 y x z)). Qed.
Lemma lem1700786 (y : real) (x : real) : (term32 y x) = (term71 y x).
Proof. exact (fun_ext (fun z : real => @lem1700785 y x z)). Qed.
Lemma lem1700787 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700788 (y : real) (x : real) : (term33 y x) = (term72 y x).
Proof. exact (MK_COMB (@lem1700787) (@lem1700786 y x)). Qed.
Lemma lem1700789 (x : real) : (term34 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1700788 y x)). Qed.
Lemma lem1700790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700791 (x : real) : (term35 x) = (term74 x).
Proof. exact (MK_COMB (@lem1700790) (@lem1700789 x)). Qed.
Lemma lem1700792 : term36 = term75.
Proof. exact (fun_ext (fun x : real => @lem1700791 x)). Qed.
Lemma lem1700793 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700854 : term24 = term76.
Proof. exact (MK_COMB (@lem1700793) (@lem1700792)). Qed.
Lemma lem1700855 (h1 : term24) : term76.
Proof. exact (EQ_MP (@lem1700854) (@lem1700678 h1)). Qed.
Lemma lem1700881 (y : real) (x : real) (z : real) : (term69 y x z) = (term69 y x z).
Proof. exact (eq_refl (term69 y x z)). Qed.
Lemma lem1700882 (y : real) (x : real) : (term71 y x) = (term71 y x).
Proof. exact (fun_ext (fun z : real => @lem1700881 y x z)). Qed.
Lemma lem1700883 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700884 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (MK_COMB (@lem1700883) (@lem1700882 y x)). Qed.
Lemma lem1700885 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1700884 y x)). Qed.
Lemma lem1700886 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700887 (x : real) : (term74 x) = (term74 x).
Proof. exact (MK_COMB (@lem1700886) (@lem1700885 x)). Qed.
Lemma lem1700888 : term75 = term75.
Proof. exact (fun_ext (fun x : real => @lem1700887 x)). Qed.
Lemma lem1700889 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700890 : term76 = term76.
Proof. exact (MK_COMB (@lem1700889) (@lem1700888)). Qed.
Lemma lem1700891 (h1 : term24) : term76.
Proof. exact (EQ_MP (@lem1700890) (@lem1700855 h1)). Qed.
Lemma lem1700943 (n : nat) (e : real) (h1 : term60 n e) : term60 n e.
Proof. exact (h1). Qed.
Lemma lem1700945 (n : nat) (e : real) (h1 : term60 n e) : term38 n e.
Proof. exact (proj1 (@lem1700943 n e h1)). Qed.
Lemma lem1700946 (n : nat) (e : real) (h1 : term60 n e) : term77 n e.
Proof. exact (proj2 (@lem1700945 n e h1)). Qed.
Lemma lem1700963 (y : real) (x : real) (z : real) : (term69 y x z) = (term69 y x z).
Proof. exact (eq_refl (term69 y x z)). Qed.
Lemma lem1700964 (y : real) (x : real) : (term71 y x) = (term71 y x).
Proof. exact (fun_ext (fun z : real => @lem1700963 y x z)). Qed.
Lemma lem1700965 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700966 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (MK_COMB (@lem1700965) (@lem1700964 y x)). Qed.
Lemma lem1700967 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1700966 y x)). Qed.
Lemma lem1700968 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700969 (x : real) : (term74 x) = (term74 x).
Proof. exact (MK_COMB (@lem1700968) (@lem1700967 x)). Qed.
Lemma lem1700970 : term75 = term75.
Proof. exact (fun_ext (fun x : real => @lem1700969 x)). Qed.
Lemma lem1700971 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700973 : term76 = term76.
Proof. exact (MK_COMB (@lem1700971) (@lem1700970)). Qed.
Lemma lem1700974 (h1 : term24) : term76.
Proof. exact (EQ_MP (@lem1700973) (@lem1700891 h1)). Qed.
Lemma lem1700991 (_26318 : real) (h1 : term24) : term78 _26318.
Proof. exact (@lem1700974 h1 _26318). Qed.
Lemma lem1700992 (_26318 : real) : (term78 _26318) = (term74 _26318).
Proof. exact (eq_refl (term78 _26318)). Qed.
Lemma lem1700993 (_26318 : real) (h1 : term24) : term74 _26318.
Proof. exact (EQ_MP (@lem1700992 _26318) (@lem1700991 _26318 h1)). Qed.
Lemma lem1700994 (_26318 : real) (_26319 : real) (h1 : term24) : term79 _26318 _26319.
Proof. exact (@lem1700993 _26318 h1 _26319). Qed.
Lemma lem1700995 (_26319 : real) (_26318 : real) : (term79 _26318 _26319) = (term72 _26319 _26318).
Proof. exact (eq_refl (term79 _26318 _26319)). Qed.
Lemma lem1700996 (_26319 : real) (_26318 : real) (h1 : term24) : term72 _26319 _26318.
Proof. exact (EQ_MP (@lem1700995 _26319 _26318) (@lem1700994 _26318 _26319 h1)). Qed.
Lemma lem1700997 (_26319 : real) (_26318 : real) (_26320 : real) (h1 : term24) : term80 _26319 _26318 _26320.
Proof. exact (@lem1700996 _26319 _26318 h1 _26320). Qed.
Lemma lem1700998 (_26319 : real) (_26318 : real) (_26320 : real) : (term80 _26319 _26318 _26320) = (term69 _26319 _26318 _26320).
Proof. exact (eq_refl (term80 _26319 _26318 _26320)). Qed.
Lemma lem1700999 (_26319 : real) (_26318 : real) (_26320 : real) (h1 : term24) : term69 _26319 _26318 _26320.
Proof. exact (EQ_MP (@lem1700998 _26319 _26318 _26320) (@lem1700997 _26319 _26318 _26320 h1)). Qed.
Lemma lem1701010 (_26319 : real) (_26318 : real) (_26320 : real) : (term69 _26319 _26318 _26320) = (term81 _26319 _26318 _26320).
Proof. exact (@lem1700470 (term82 _26318 _26319) (term82 _26319 _26320) (real_lt _26318 _26320)). Qed.
Lemma lem1701011 (_26319 : real) (_26318 : real) (_26320 : real) (h1 : term24) : term81 _26319 _26318 _26320.
Proof. exact (EQ_MP (@lem1701010 _26319 _26318 _26320) (@lem1700999 _26319 _26318 _26320 h1)). Qed.
Lemma lem1701013 (n : nat) (e : real) (h1 : term60 n e) : term42 e.
Proof. exact (proj2 (@lem1700943 n e h1)). Qed.
Lemma lem1701068 (n : nat) (e : real) (h1 : term60 n e) : term83 n.
Proof. exact (proj1 (@lem1700946 n e h1)). Qed.
Lemma lem1701069 (n : nat) (e : real) (h1 : term60 n e) : term84 n.
Proof. exact (fun h0 : term85 n => @lem1701068 n e h1). Qed.
Lemma lem1701071 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1701072 (n : nat) : (term84 n) = (term83 n).
Proof. exact (@lem1701071 (term83 n)). Qed.
Lemma lem1701073 (n : nat) (e : real) (h1 : term60 n e) : term83 n.
Proof. exact (EQ_MP (@lem1701072 n) (@lem1701069 n e h1)). Qed.
Lemma lem1701075 (n : nat) (e : real) (h1 : term60 n e) : term87 n e.
Proof. exact (proj2 (@lem1700946 n e h1)). Qed.
Lemma lem1701076 (n : nat) (e : real) (h1 : term60 n e) : term88 n e.
Proof. exact (fun h0 : term89 n e => @lem1701075 n e h1). Qed.
Lemma lem1701078 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1701079 (n : nat) (e : real) : (term88 n e) = (term87 n e).
Proof. exact (@lem1701078 (term87 n e)). Qed.
Lemma lem1701080 (n : nat) (e : real) (h1 : term60 n e) : term87 n e.
Proof. exact (EQ_MP (@lem1701079 n e) (@lem1701076 n e h1)). Qed.
Lemma lem1701096 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1701097 (_26318 : real) (_26319 : real) (_26320 : real) : (term90 _26319 _26318 _26320) = (term91 _26318 _26319 _26320).
Proof. exact (@lem1701096 (real_lt _26318 _26320) (term82 _26319 _26320)). Qed.
Lemma lem1701103 (_26318 : real) (_26319 : real) : (term92 _26318 _26319) = (term92 _26318 _26319).
Proof. exact (eq_refl (term92 _26318 _26319)). Qed.
Lemma lem1701104 (_26318 : real) (_26319 : real) (_26320 : real) : (term81 _26319 _26318 _26320) = (term93 _26318 _26319 _26320).
Proof. exact (MK_COMB (@lem1701103 _26318 _26319) (@lem1701097 _26318 _26319 _26320)). Qed.
Lemma lem1701108 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1701109 (_26318 : real) (_26319 : real) (_26320 : real) : (term93 _26318 _26319 _26320) = (term94 _26318 _26319 _26320).
Proof. exact (@lem1701108 (real_lt _26318 _26320) (term82 _26318 _26319) (term82 _26319 _26320)). Qed.
Lemma lem1701125 (_26318 : real) (_26319 : real) (_26320 : real) : (term81 _26319 _26318 _26320) = (term94 _26318 _26319 _26320).
Proof. exact (TRANS (@lem1701104 _26318 _26319 _26320) (@lem1701109 _26318 _26319 _26320)). Qed.
Lemma lem1701126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1701127 (_26318 : real) (_26319 : real) (_26320 : real) : (term95 _26319 _26318 _26320) = (term96 _26318 _26319 _26320).
Proof. exact (MK_COMB (@lem1701126) (@lem1701125 _26318 _26319 _26320)). Qed.
Lemma lem1701143 (_26318 : real) (_26319 : real) (_26320 : real) : (term94 _26318 _26319 _26320) = (term94 _26318 _26319 _26320).
Proof. exact (eq_refl (term94 _26318 _26319 _26320)). Qed.
Lemma lem1701144 (_26318 : real) (_26319 : real) (_26320 : real) : ((term81 _26319 _26318 _26320) = (term94 _26318 _26319 _26320)) = ((term94 _26318 _26319 _26320) = (term94 _26318 _26319 _26320)).
Proof. exact (MK_COMB (@lem1701127 _26318 _26319 _26320) (@lem1701143 _26318 _26319 _26320)). Qed.
Lemma lem1701146 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1701147 (x : Prop) : (x = x) = True.
Proof. exact (@lem1701146 Prop x). Qed.
Lemma lem1701148 (_26318 : real) (_26319 : real) (_26320 : real) : ((term94 _26318 _26319 _26320) = (term94 _26318 _26319 _26320)) = True.
Proof. exact (@lem1701147 (term94 _26318 _26319 _26320)). Qed.
Lemma lem1701149 (_26318 : real) (_26319 : real) (_26320 : real) : ((term81 _26319 _26318 _26320) = (term94 _26318 _26319 _26320)) = True.
Proof. exact (TRANS (@lem1701144 _26318 _26319 _26320) (@lem1701148 _26318 _26319 _26320)). Qed.
Lemma lem1701150 (_26318 : real) (_26319 : real) (_26320 : real) : True = ((term81 _26319 _26318 _26320) = (term94 _26318 _26319 _26320)).
Proof. exact (SYM (@lem1701149 _26318 _26319 _26320)). Qed.
Lemma lem1701151 (_26318 : real) (_26319 : real) (_26320 : real) : (term81 _26319 _26318 _26320) = (term94 _26318 _26319 _26320).
Proof. exact (EQ_MP (@lem1701150 _26318 _26319 _26320) (@lem0)). Qed.
Lemma lem1701152 (_26318 : real) (_26319 : real) (_26320 : real) (h1 : term24) : term94 _26318 _26319 _26320.
Proof. exact (EQ_MP (@lem1701151 _26318 _26319 _26320) (@lem1701011 _26319 _26318 _26320 h1)). Qed.
Lemma lem1701154 (b : Prop) (a : Prop) : (a \/ b) = (term97 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1701155 (_26319 : real) (_26318 : real) (_26320 : real) : (term94 _26318 _26319 _26320) = (term98 _26319 _26318 _26320).
Proof. exact (@lem1701154 (term65 _26318 _26319 _26320) (real_lt _26318 _26320)). Qed.
Lemma lem1701157 (a : Prop) (b : Prop) : (term99 a b) = (term100 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1701158 (_26318 : real) (_26319 : real) (_26320 : real) : (term101 _26318 _26319 _26320) = (term102 _26318 _26319 _26320).
Proof. exact (@lem1701157 (term82 _26318 _26319) (term82 _26319 _26320)). Qed.
Lemma lem1701160 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1701161 (_26318 : real) (_26319 : real) : (term104 _26318 _26319) = (real_lt _26318 _26319).
Proof. exact (@lem1701160 (real_lt _26318 _26319)). Qed.
Lemma lem1701162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1701163 (_26318 : real) (_26319 : real) : (term105 _26318 _26319) = (term106 _26318 _26319).
Proof. exact (MK_COMB (@lem1701162) (@lem1701161 _26318 _26319)). Qed.
Lemma lem1701165 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1701166 (_26319 : real) (_26320 : real) : (term104 _26319 _26320) = (real_lt _26319 _26320).
Proof. exact (@lem1701165 (real_lt _26319 _26320)). Qed.
Lemma lem1701167 (_26318 : real) (_26319 : real) (_26320 : real) : (term102 _26318 _26319 _26320) = (term70 _26318 _26319 _26320).
Proof. exact (MK_COMB (@lem1701163 _26318 _26319) (@lem1701166 _26319 _26320)). Qed.
Lemma lem1701168 (_26318 : real) (_26319 : real) (_26320 : real) : (term101 _26318 _26319 _26320) = (term70 _26318 _26319 _26320).
Proof. exact (TRANS (@lem1701158 _26318 _26319 _26320) (@lem1701167 _26318 _26319 _26320)). Qed.
Lemma lem1701169 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1701170 (_26318 : real) (_26319 : real) (_26320 : real) : (term107 _26318 _26319 _26320) = (term108 _26318 _26319 _26320).
Proof. exact (MK_COMB (@lem1701169) (@lem1701168 _26318 _26319 _26320)). Qed.
Lemma lem1701171 (_26318 : real) (_26320 : real) : (real_lt _26318 _26320) = (real_lt _26318 _26320).
Proof. exact (eq_refl (real_lt _26318 _26320)). Qed.
Lemma lem1701172 (_26319 : real) (_26318 : real) (_26320 : real) : (term98 _26319 _26318 _26320) = (term31 _26319 _26318 _26320).
Proof. exact (MK_COMB (@lem1701170 _26318 _26319 _26320) (@lem1701171 _26318 _26320)). Qed.
Lemma lem1701173 (_26319 : real) (_26318 : real) (_26320 : real) : (term94 _26318 _26319 _26320) = (term31 _26319 _26318 _26320).
Proof. exact (TRANS (@lem1701155 _26319 _26318 _26320) (@lem1701172 _26319 _26318 _26320)). Qed.
Lemma lem1701175 (n : nat) (e : real) (h1 : term60 n e) : term77 n e.
Proof. exact (conj (@lem1701073 n e h1) (@lem1701080 n e h1)). Qed.
Lemma lem1701177 (_26319 : real) (_26318 : real) (_26320 : real) (h1 : term24) : term31 _26319 _26318 _26320.
Proof. exact (EQ_MP (@lem1701173 _26319 _26318 _26320) (@lem1701152 _26318 _26319 _26320 h1)). Qed.
Lemma lem1701178 (n : nat) (e : real) (h1 : term24) : term109 n e.
Proof. exact (@lem1701177 (term110 n) term111 e h1). Qed.
Lemma lem1701181 (n : nat) (e : real) (h1 : term24) (h2 : term60 n e) : term37 e.
Proof. exact (@lem1701178 n e h1 (@lem1701175 n e h2)). Qed.
Lemma lem1701182 (n : nat) (e : real) (h1 : term24) (h2 : term60 n e) : term112 e.
Proof. exact (fun h0 : term42 e => @lem1701181 n e h1 h2). Qed.
Lemma lem1701184 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1701185 (e : real) : (term112 e) = (term37 e).
Proof. exact (@lem1701184 (term37 e)). Qed.
Lemma lem1701186 (n : nat) (e : real) (h1 : term24) (h2 : term60 n e) : term37 e.
Proof. exact (EQ_MP (@lem1701185 e) (@lem1701182 n e h1 h2)). Qed.
Lemma lem1701189 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1701191 (e : real) : (term42 e) = (term113 e).
Proof. exact (@lem1701189 (term37 e)). Qed.
Lemma lem1701194 (n : nat) (e : real) (h1 : term60 n e) : term113 e.
Proof. exact (EQ_MP (@lem1701191 e) (@lem1701013 n e h1)). Qed.
Lemma lem1701197 (n : nat) (e : real) (h1 : term24) (h2 : term60 n e) : False.
Proof. exact (@lem1701194 n e h2 (@lem1701186 n e h1 h2)). Qed.
Lemma lem1701198 (n : nat) (e : real) (h1 : term24) (h2 : term60 n e) : term114.
Proof. exact (fun h0 : ~ False => @lem1701197 n e h1 h2). Qed.
Lemma lem1701200 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1701201 : term114 = False.
Proof. exact (@lem1701200 False). Qed.
Lemma lem1701202 (n : nat) (e : real) (h1 : term24) (h2 : term60 n e) : False.
Proof. exact (EQ_MP (@lem1701201) (@lem1701198 n e h1 h2)). Qed.
Lemma lem1701203 (n : nat) (e : real) (h1 : term24) (h2 : term60 n e) : (term60 n e) = False.
Proof. exact (prop_ext (fun h3 : term60 n e => @lem1701202 n e h1 h2) (fun h3 : False => @lem1700943 n e h2)). Qed.
Lemma lem1701204 (n : nat) (e : real) (h1 : term24) (h2 : term60 n e) : False.
Proof. exact (EQ_MP (@lem1701203 n e h1 h2) (@lem1700943 n e h2)). Qed.
Lemma lem1701205 (e : real) (h1 : term24) (h2 : term17 e) : False.
Proof. exact (ex_elim (@lem1700772 e h2) (fun n : nat => fun h0 : term62 e n => @lem1701204 n e h1 h0)). Qed.
Lemma lem1701206 (e : real) (h1 : term17 e) : term22.
Proof. exact (fun h0 : term24 => @lem1701205 e h0 h1). Qed.
Lemma lem1701207 : term22 = term23.
Proof. exact (@lem69 term24). Qed.
Lemma lem1701208 (e : real) (h1 : term17 e) : term23.
Proof. exact (EQ_MP (@lem1701207) (@lem1701206 e h1)). Qed.
Lemma lem1701209 (e : real) : term26 e.
Proof. exact (fun h0 : term17 e => @lem1701208 e h0). Qed.
Lemma lem1701214 : term30.
Proof. exact (fun e : real => @lem1701209 e). Qed.
Lemma lem1701215 : term29.
Proof. exact (EQ_MP (@lem1700676) (@lem1701214)). Qed.
Lemma lem1701216 (e : real) : term115 e.
Proof. exact (@lem1701215 e). Qed.
Lemma lem1701217 (e : real) : (term115 e) = (term18 e).
Proof. exact (eq_refl (term115 e)). Qed.
Lemma lem1701218 (e : real) : term18 e.
Proof. exact (EQ_MP (@lem1701217 e) (@lem1701216 e)). Qed.
Lemma lem1701220 (e : real) : term18 e.
Proof. exact (@lem1700490 e (@lem1701218 e)). Qed.
Lemma lem1701221 (e : real) (h1 : term17 e) : term22.
Proof. exact (@lem1701220 e (@lem1700475 e h1)). Qed.
Lemma lem1701222 (e : real) (h1 : term17 e) : False.
Proof. exact (@lem1701221 e h1 (@lem1372268)). Qed.
Lemma lem1701223 (e : real) (h1 : term17 e) : (term17 e) = False.
Proof. exact (prop_ext (fun h2 : term17 e => @lem1701222 e h1) (fun h2 : False => @lem1700475 e h1)). Qed.
Lemma lem1701224 (e : real) (h1 : term17 e) : False.
Proof. exact (EQ_MP (@lem1701223 e h1) (@lem1700475 e h1)). Qed.
Lemma lem1701225 (e : real) : term16 e.
Proof. exact (fun h0 : term17 e => @lem1701224 e h0). Qed.
Lemma lem1701226 (e : real) : term15 e.
Proof. exact (EQ_MP (@lem1700474 e) (@lem1701225 e)). Qed.
Lemma lem1701227 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1701229 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (@lem1700456 A P Q (@lem7401 A P Q)). Qed.
Lemma lem1701230 (P : nat -> Prop) (Q : nat -> Prop) : term116 P Q.
Proof. exact (@lem1701229 nat P Q). Qed.
Lemma lem1701231 (e : real) : term117 e.
Proof. exact (@lem1701230 (term118 e) (term39 e)). Qed.
Lemma lem1701232 (e : real) (n : nat) : (term119 e n) = (term120 e n).
Proof. exact (eq_refl (term119 e n)). Qed.
Lemma lem1701233 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1701234 (e : real) (n : nat) : (term121 e n) = (term122 e n).
Proof. exact (MK_COMB (@lem1701233) (@lem1701232 e n)). Qed.
Lemma lem1701235 (n : nat) (e : real) : (term51 e n) = (term38 n e).
Proof. exact (eq_refl (term51 e n)). Qed.
Lemma lem1701236 (n : nat) (e : real) : (term123 e n) = (term124 n e).
Proof. exact (MK_COMB (@lem1701234 e n) (@lem1701235 n e)). Qed.
Lemma lem1701237 (e : real) : (term125 e) = (term126 e).
Proof. exact (fun_ext (fun n : nat => @lem1701236 n e)). Qed.
Lemma lem1701238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1701239 (e : real) : (term127 e) = (term128 e).
Proof. exact (MK_COMB (@lem1701238) (@lem1701237 e)). Qed.
Lemma lem1701240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1701241 (e : real) : (term129 e) = (term130 e).
Proof. exact (MK_COMB (@lem1701240) (@lem1701239 e)). Qed.
Lemma lem1701242 (e : real) (n : nat) : (term119 e n) = (term120 e n).
Proof. exact (eq_refl (term119 e n)). Qed.
Lemma lem1701243 (e : real) : (term131 e) = (term118 e).
Proof. exact (fun_ext (fun n : nat => @lem1701242 e n)). Qed.
Lemma lem1701244 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1701245 (e : real) : (term132 e) = (term13 e).
Proof. exact (MK_COMB (@lem1701244) (@lem1701243 e)). Qed.
Lemma lem1701246 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1701247 (e : real) : (term133 e) = (term134 e).
Proof. exact (MK_COMB (@lem1701246) (@lem1701245 e)). Qed.
Lemma lem1701248 (n : nat) (e : real) : (term51 e n) = (term38 n e).
Proof. exact (eq_refl (term51 e n)). Qed.
Lemma lem1701249 (e : real) : (term52 e) = (term39 e).
Proof. exact (fun_ext (fun n : nat => @lem1701248 n e)). Qed.
Lemma lem1701250 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1701251 (e : real) : (term53 e) = (term40 e).
Proof. exact (MK_COMB (@lem1701250) (@lem1701249 e)). Qed.
Lemma lem1701252 (e : real) : (term135 e) = (term136 e).
Proof. exact (MK_COMB (@lem1701247 e) (@lem1701251 e)). Qed.
Lemma lem1701253 (e : real) : (term117 e) = (term137 e).
Proof. exact (MK_COMB (@lem1701241 e) (@lem1701252 e)). Qed.
Lemma lem1701254 (e : real) : term137 e.
Proof. exact (EQ_MP (@lem1701253 e) (@lem1701231 e)). Qed.
Lemma lem1701256 (p : Prop) : p = (term14 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1701257 (e : real) : (term128 e) = (term138 e).
Proof. exact (@lem1701256 (term128 e)). Qed.
Lemma lem1701258 (e : real) : (term138 e) = (term128 e).
Proof. exact (SYM (@lem1701257 e)). Qed.
Lemma lem1701259 (e : real) (h1 : term139 e) : term139 e.
Proof. exact (h1). Qed.
Lemma lem1701262 (e : real) (h1 : term140 e) : term140 e.
Proof. exact (h1). Qed.
Lemma lem1701263 (e : real) : term141 e.
Proof. exact (fun h0 : term140 e => @lem1701262 e h0). Qed.
Lemma lem1701264 (e : real) (h1 : term141 e) : term141 e.
Proof. exact (h1). Qed.
Lemma lem1701265 (e : real) (h1 : term140 e) : term140 e.
Proof. exact (h1). Qed.
Lemma lem1701266 (e : real) (h1 : term141 e) (h2 : term140 e) : term140 e.
Proof. exact (@lem1701264 e h1 (@lem1701265 e h2)). Qed.
Lemma lem1701267 (e : real) (h1 : term140 e) : term142 e.
Proof. exact (fun h0 : term141 e => @lem1701266 e h0 h1). Qed.
Lemma lem1701268 (e : real) (h1 : term141 e) : term141 e.
Proof. exact (h1). Qed.
Lemma lem1701269 (e : real) (h1 : term141 e) (h2 : term140 e) : term140 e.
Proof. exact (@lem1701267 e h2 (@lem1701268 e h1)). Qed.
Lemma lem1701270 (e : real) (h1 : term141 e) : term141 e.
Proof. exact (fun h0 : term140 e => @lem1701269 e h1 h0). Qed.
Lemma lem1701271 (e : real) : term143 e.
Proof. exact (fun h0 : term141 e => @lem1701270 e h0). Qed.
Lemma lem1701274 (e : real) : term141 e.
Proof. exact (@lem1701271 e (@lem1701263 e)). Qed.
Lemma lem1701336 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1701337 : term144 = term145.
Proof. exact (@lem1701336 term146). Qed.
Lemma lem1701350 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1701351 : term148 = term149.
Proof. exact (MK_COMB (@lem1701350) (@lem1701337)). Qed.
Lemma lem1701354 : term150 = term150.
Proof. exact (eq_refl term150). Qed.
Lemma lem1701355 : term151 = term152.
Proof. exact (MK_COMB (@lem1701354) (@lem1701351)). Qed.
Lemma lem1701358 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem1701359 : term154 = term155.
Proof. exact (MK_COMB (@lem1701358) (@lem1701355)). Qed.
Lemma lem1701362 : term156 = term156.
Proof. exact (eq_refl term156). Qed.
Lemma lem1701363 : term157 = term158.
Proof. exact (MK_COMB (@lem1701362) (@lem1701359)). Qed.
Lemma lem1701366 (e : real) : (term159 e) = (term159 e).
Proof. exact (eq_refl (term159 e)). Qed.
Lemma lem1701367 (e : real) : (term160 e) = (term161 e).
Proof. exact (MK_COMB (@lem1701366 e) (@lem1701363)). Qed.
Lemma lem1701370 (e : real) : (term162 e) = (term162 e).
Proof. exact (eq_refl (term162 e)). Qed.
Lemma lem1701371 (e : real) : (term140 e) = (term163 e).
Proof. exact (MK_COMB (@lem1701370 e) (@lem1701367 e)). Qed.
Lemma lem1701374 : term164 = term165.
Proof. exact (fun_ext (fun e : real => @lem1701371 e)). Qed.
Lemma lem1701375 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701384 : term166 = term167.
Proof. exact (MK_COMB (@lem1701375) (@lem1701374)). Qed.
Lemma lem1701393 (y : real) (x : real) : (term168 y x) = (term168 y x).
Proof. exact (eq_refl (term168 y x)). Qed.
Lemma lem1701394 (x : real) : (term169 x) = (term169 x).
Proof. exact (fun_ext (fun y : real => @lem1701393 y x)). Qed.
Lemma lem1701395 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701396 (x : real) : (term170 x) = (term170 x).
Proof. exact (MK_COMB (@lem1701395) (@lem1701394 x)). Qed.
Lemma lem1701397 : term171 = term171.
Proof. exact (fun_ext (fun x : real => @lem1701396 x)). Qed.
Lemma lem1701398 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701399 : term146 = term146.
Proof. exact (MK_COMB (@lem1701398) (@lem1701397)). Qed.
Lemma lem1701400 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1701401 : term145 = term145.
Proof. exact (MK_COMB (@lem1701400) (@lem1701399)). Qed.
Lemma lem1701402 (x : real) : ((term172 x) = x) = ((term172 x) = x).
Proof. exact (eq_refl ((term172 x) = x)). Qed.
Lemma lem1701403 : term173 = term173.
Proof. exact (fun_ext (fun x : real => @lem1701402 x)). Qed.
Lemma lem1701404 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701405 : term174 = term174.
Proof. exact (MK_COMB (@lem1701404) (@lem1701403)). Qed.
Lemma lem1701406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1701407 : term147 = term147.
Proof. exact (MK_COMB (@lem1701406) (@lem1701405)). Qed.
Lemma lem1701408 : term149 = term149.
Proof. exact (MK_COMB (@lem1701407) (@lem1701401)). Qed.
Lemma lem1701413 (x : real) : ((term175 x) = (term37 x)) = ((term175 x) = (term37 x)).
Proof. exact (eq_refl ((term175 x) = (term37 x))). Qed.
Lemma lem1701414 : term176 = term176.
Proof. exact (fun_ext (fun x : real => @lem1701413 x)). Qed.
Lemma lem1701415 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701416 : term177 = term177.
Proof. exact (MK_COMB (@lem1701415) (@lem1701414)). Qed.
Lemma lem1701417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1701418 : term150 = term150.
Proof. exact (MK_COMB (@lem1701417) (@lem1701416)). Qed.
Lemma lem1701419 : term152 = term152.
Proof. exact (MK_COMB (@lem1701418) (@lem1701408)). Qed.
Lemma lem1701428 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem1701429 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem1701428 y x z)). Qed.
Lemma lem1701430 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701431 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem1701430) (@lem1701429 y x)). Qed.
Lemma lem1701432 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1701431 y x)). Qed.
Lemma lem1701433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701434 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1701433) (@lem1701432 x)). Qed.
Lemma lem1701435 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1701434 x)). Qed.
Lemma lem1701436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701437 : term24 = term24.
Proof. exact (MK_COMB (@lem1701436) (@lem1701435)). Qed.
Lemma lem1701438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1701439 : term153 = term153.
Proof. exact (MK_COMB (@lem1701438) (@lem1701437)). Qed.
Lemma lem1701440 : term155 = term155.
Proof. exact (MK_COMB (@lem1701439) (@lem1701419)). Qed.
Lemma lem1701447 (y : real) (x : real) : (term178 y x) = (term178 y x).
Proof. exact (eq_refl (term178 y x)). Qed.
Lemma lem1701448 (x : real) : (term179 x) = (term179 x).
Proof. exact (fun_ext (fun y : real => @lem1701447 y x)). Qed.
Lemma lem1701449 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701450 (x : real) : (term180 x) = (term180 x).
Proof. exact (MK_COMB (@lem1701449) (@lem1701448 x)). Qed.
Lemma lem1701451 : term181 = term181.
Proof. exact (fun_ext (fun x : real => @lem1701450 x)). Qed.
Lemma lem1701452 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701453 : term182 = term182.
Proof. exact (MK_COMB (@lem1701452) (@lem1701451)). Qed.
Lemma lem1701454 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1701455 : term156 = term156.
Proof. exact (MK_COMB (@lem1701454) (@lem1701453)). Qed.
Lemma lem1701456 : term158 = term158.
Proof. exact (MK_COMB (@lem1701455) (@lem1701440)). Qed.
Lemma lem1701471 (n : nat) (e : real) : (term124 n e) = (term124 n e).
Proof. exact (eq_refl (term124 n e)). Qed.
Lemma lem1701472 (e : real) : (term126 e) = (term126 e).
Proof. exact (fun_ext (fun n : nat => @lem1701471 n e)). Qed.
Lemma lem1701473 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1701474 (e : real) : (term128 e) = (term128 e).
Proof. exact (MK_COMB (@lem1701473) (@lem1701472 e)). Qed.
Lemma lem1701475 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1701476 (e : real) : (term139 e) = (term139 e).
Proof. exact (MK_COMB (@lem1701475) (@lem1701474 e)). Qed.
Lemma lem1701477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1701478 (e : real) : (term159 e) = (term159 e).
Proof. exact (MK_COMB (@lem1701477) (@lem1701476 e)). Qed.
Lemma lem1701479 (e : real) : (term161 e) = (term161 e).
Proof. exact (MK_COMB (@lem1701478 e) (@lem1701456)). Qed.
Lemma lem1701482 (e : real) : (term162 e) = (term162 e).
Proof. exact (eq_refl (term162 e)). Qed.
Lemma lem1701483 (e : real) : (term163 e) = (term163 e).
Proof. exact (MK_COMB (@lem1701482 e) (@lem1701479 e)). Qed.
Lemma lem1701484 : term165 = term165.
Proof. exact (fun_ext (fun e : real => @lem1701483 e)). Qed.
Lemma lem1701485 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701486 : term167 = term167.
Proof. exact (MK_COMB (@lem1701485) (@lem1701484)). Qed.
Lemma lem1701583 : term166 = term167.
Proof. exact (TRANS (@lem1701384) (@lem1701486)). Qed.
Lemma lem1701584 : term167 = term166.
Proof. exact (SYM (@lem1701583)). Qed.
Lemma lem1701586 (e : real) (h1 : term139 e) : term139 e.
Proof. exact (h1). Qed.
Lemma lem1701587 (h1 : term182) : term182.
Proof. exact (h1). Qed.
Lemma lem1701588 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1701589 (h1 : term177) : term177.
Proof. exact (h1). Qed.
Lemma lem1701590 (h1 : term174) : term174.
Proof. exact (h1). Qed.
Lemma lem1701591 (h1 : term146) : term146.
Proof. exact (h1). Qed.
Lemma lem1701597 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1701601 (n : nat) : (term183 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem1701608 (n : nat) (e : real) : (term184 n e) = (term185 n e).
Proof. exact (@lem17045 (term83 n) (term87 n e)). Qed.
Lemma lem1701609 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1701610 (n : nat) : (term186 n) = (term187 n).
Proof. exact (MK_COMB (@lem1701609) (@lem1701601 n)). Qed.
Lemma lem1701611 (n : nat) (e : real) : (term188 n e) = (term189 n e).
Proof. exact (MK_COMB (@lem1701610 n) (@lem1701608 n e)). Qed.
Lemma lem1701612 (n : nat) (e : real) : (term190 n e) = (term188 n e).
Proof. exact (@lem17045 (term191 n) (term77 n e)). Qed.
Lemma lem1701613 (n : nat) (e : real) : (term190 n e) = (term189 n e).
Proof. exact (TRANS (@lem1701612 n e) (@lem1701611 n e)). Qed.
Lemma lem1701615 (e : real) (n : nat) : (term192 e n) = (term192 e n).
Proof. exact (eq_refl (term192 e n)). Qed.
Lemma lem1701616 (n : nat) (e : real) : (term193 n e) = (term194 n e).
Proof. exact (MK_COMB (@lem1701615 e n) (@lem1701613 n e)). Qed.
Lemma lem1701617 (n : nat) (e : real) : (term195 n e) = (term193 n e).
Proof. exact (@lem17362 (term120 e n) (term38 n e)). Qed.
Lemma lem1701618 (n : nat) (e : real) : (term195 n e) = (term194 n e).
Proof. exact (TRANS (@lem1701617 n e) (@lem1701616 n e)). Qed.
Lemma lem1701619 (P : nat -> Prop) : (term196 P) = (term197 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1701620 (e : real) : (term139 e) = (term198 e).
Proof. exact (@lem1701619 (term126 e)). Qed.
Lemma lem1701621 (n : nat) (e : real) : (term199 e n) = (term124 n e).
Proof. exact (eq_refl (term199 e n)). Qed.
Lemma lem1701622 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1701623 (n : nat) (e : real) : (term200 e n) = (term195 n e).
Proof. exact (MK_COMB (@lem1701622) (@lem1701621 n e)). Qed.
Lemma lem1701624 (n : nat) (e : real) : (term200 e n) = (term194 n e).
Proof. exact (TRANS (@lem1701623 n e) (@lem1701618 n e)). Qed.
Lemma lem1701625 (e : real) : (term201 e) = (term202 e).
Proof. exact (fun_ext (fun n : nat => @lem1701624 n e)). Qed.
Lemma lem1701626 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1701627 (e : real) : (term198 e) = (term203 e).
Proof. exact (MK_COMB (@lem1701626) (@lem1701625 e)). Qed.
Lemma lem1701680 (e : real) : (term139 e) = (term203 e).
Proof. exact (TRANS (@lem1701620 e) (@lem1701627 e)). Qed.
Lemma lem1701681 (e : real) (h1 : term139 e) : term203 e.
Proof. exact (EQ_MP (@lem1701680 e) (@lem1701586 e h1)). Qed.
Lemma lem1701688 (y : real) (x : real) : (term178 y x) = (term204 y x).
Proof. exact (@lem17045 (real_lt x y) (real_lt y x)). Qed.
Lemma lem1701689 (x : real) : (term179 x) = (term205 x).
Proof. exact (fun_ext (fun y : real => @lem1701688 y x)). Qed.
Lemma lem1701690 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701691 (x : real) : (term180 x) = (term206 x).
Proof. exact (MK_COMB (@lem1701690) (@lem1701689 x)). Qed.
Lemma lem1701692 : term181 = term207.
Proof. exact (fun_ext (fun x : real => @lem1701691 x)). Qed.
Lemma lem1701693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701750 : term182 = term208.
Proof. exact (MK_COMB (@lem1701693) (@lem1701692)). Qed.
Lemma lem1701751 (h1 : term182) : term208.
Proof. exact (EQ_MP (@lem1701750) (@lem1701587 h1)). Qed.
Lemma lem1701758 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (@lem17045 (real_lt x y) (real_lt y z)). Qed.
Lemma lem1701759 (x : real) (z : real) : (real_lt x z) = (real_lt x z).
Proof. exact (eq_refl (real_lt x z)). Qed.
Lemma lem1701760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1701761 (x : real) (y : real) (z : real) : (term66 x y z) = (term67 x y z).
Proof. exact (MK_COMB (@lem1701760) (@lem1701758 x y z)). Qed.
Lemma lem1701762 (y : real) (x : real) (z : real) : (term68 y x z) = (term69 y x z).
Proof. exact (MK_COMB (@lem1701761 x y z) (@lem1701759 x z)). Qed.
Lemma lem1701763 (y : real) (x : real) (z : real) : (term31 y x z) = (term68 y x z).
Proof. exact (@lem17265 (term70 x y z) (real_lt x z)). Qed.
Lemma lem1701764 (y : real) (x : real) (z : real) : (term31 y x z) = (term69 y x z).
Proof. exact (TRANS (@lem1701763 y x z) (@lem1701762 y x z)). Qed.
Lemma lem1701765 (y : real) (x : real) : (term32 y x) = (term71 y x).
Proof. exact (fun_ext (fun z : real => @lem1701764 y x z)). Qed.
Lemma lem1701766 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701767 (y : real) (x : real) : (term33 y x) = (term72 y x).
Proof. exact (MK_COMB (@lem1701766) (@lem1701765 y x)). Qed.
Lemma lem1701768 (x : real) : (term34 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1701767 y x)). Qed.
Lemma lem1701769 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701770 (x : real) : (term35 x) = (term74 x).
Proof. exact (MK_COMB (@lem1701769) (@lem1701768 x)). Qed.
Lemma lem1701771 : term36 = term75.
Proof. exact (fun_ext (fun x : real => @lem1701770 x)). Qed.
Lemma lem1701772 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701833 : term24 = term76.
Proof. exact (MK_COMB (@lem1701772) (@lem1701771)). Qed.
Lemma lem1701834 (h1 : term24) : term76.
Proof. exact (EQ_MP (@lem1701833) (@lem1701588 h1)). Qed.
Lemma lem1701849 (x : real) : ((term175 x) = (term37 x)) = (term209 x).
Proof. exact (@lem17784 (term175 x) (term37 x)). Qed.
Lemma lem1701850 : term176 = term210.
Proof. exact (fun_ext (fun x : real => @lem1701849 x)). Qed.
Lemma lem1701851 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701852 : term177 = term211.
Proof. exact (MK_COMB (@lem1701851) (@lem1701850)). Qed.
Lemma lem1701854 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term212 A P Q) = (term213 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1701855 (P : real -> Prop) (Q : real -> Prop) : (term214 P Q) = (term215 P Q).
Proof. exact (@lem1701854 real P Q). Qed.
Lemma lem1701856 : term216 = term217.
Proof. exact (@lem1701855 term218 term219). Qed.
Lemma lem1701857 (x : real) : (term220 x) = (term221 x).
Proof. exact (eq_refl (term220 x)). Qed.
Lemma lem1701858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1701859 (x : real) : (term222 x) = (term223 x).
Proof. exact (MK_COMB (@lem1701858) (@lem1701857 x)). Qed.
Lemma lem1701860 (x : real) : (term224 x) = (term225 x).
Proof. exact (eq_refl (term224 x)). Qed.
Lemma lem1701861 (x : real) : (term226 x) = (term209 x).
Proof. exact (MK_COMB (@lem1701859 x) (@lem1701860 x)). Qed.
Lemma lem1701862 : term227 = term210.
Proof. exact (fun_ext (fun x : real => @lem1701861 x)). Qed.
Lemma lem1701863 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701864 : term216 = term211.
Proof. exact (MK_COMB (@lem1701863) (@lem1701862)). Qed.
Lemma lem1701865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1701866 : term228 = term229.
Proof. exact (MK_COMB (@lem1701865) (@lem1701864)). Qed.
Lemma lem1701867 (x : real) : (term220 x) = (term221 x).
Proof. exact (eq_refl (term220 x)). Qed.
Lemma lem1701868 : term230 = term218.
Proof. exact (fun_ext (fun x : real => @lem1701867 x)). Qed.
Lemma lem1701869 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701870 : term231 = term232.
Proof. exact (MK_COMB (@lem1701869) (@lem1701868)). Qed.
Lemma lem1701871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1701872 : term233 = term234.
Proof. exact (MK_COMB (@lem1701871) (@lem1701870)). Qed.
Lemma lem1701873 (x : real) : (term224 x) = (term225 x).
Proof. exact (eq_refl (term224 x)). Qed.
Lemma lem1701874 : term235 = term219.
Proof. exact (fun_ext (fun x : real => @lem1701873 x)). Qed.
Lemma lem1701875 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701876 : term236 = term237.
Proof. exact (MK_COMB (@lem1701875) (@lem1701874)). Qed.
Lemma lem1701877 : term217 = term238.
Proof. exact (MK_COMB (@lem1701872) (@lem1701876)). Qed.
Lemma lem1701878 : (term216 = term217) = (term211 = term238).
Proof. exact (MK_COMB (@lem1701866) (@lem1701877)). Qed.
Lemma lem1701977 : term211 = term238.
Proof. exact (EQ_MP (@lem1701878) (@lem1701856)). Qed.
Lemma lem1701978 : term177 = term238.
Proof. exact (TRANS (@lem1701852) (@lem1701977)). Qed.
Lemma lem1701979 (h1 : term177) : term238.
Proof. exact (EQ_MP (@lem1701978) (@lem1701589 h1)). Qed.
Lemma lem1701980 (x : real) : ((term172 x) = x) = ((term172 x) = x).
Proof. exact (eq_refl ((term172 x) = x)). Qed.
Lemma lem1701981 : term173 = term173.
Proof. exact (fun_ext (fun x : real => @lem1701980 x)). Qed.
Lemma lem1701982 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1701991 : term174 = term174.
Proof. exact (MK_COMB (@lem1701982) (@lem1701981)). Qed.
Lemma lem1701992 (h1 : term174) : term174.
Proof. exact (EQ_MP (@lem1701991) (@lem1701590 h1)). Qed.
Lemma lem1701999 (x : real) (y : real) : (term239 x y) = (term240 x y).
Proof. exact (@lem17045 (term37 x) (real_lt x y)). Qed.
Lemma lem1702000 (y : real) (x : real) : (term241 y x) = (term241 y x).
Proof. exact (eq_refl (term241 y x)). Qed.
Lemma lem1702001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1702002 (x : real) (y : real) : (term242 x y) = (term243 x y).
Proof. exact (MK_COMB (@lem1702001) (@lem1701999 x y)). Qed.
Lemma lem1702003 (y : real) (x : real) : (term244 y x) = (term245 y x).
Proof. exact (MK_COMB (@lem1702002 x y) (@lem1702000 y x)). Qed.
Lemma lem1702004 (y : real) (x : real) : (term168 y x) = (term244 y x).
Proof. exact (@lem17265 (term246 x y) (term241 y x)). Qed.
Lemma lem1702005 (y : real) (x : real) : (term168 y x) = (term245 y x).
Proof. exact (TRANS (@lem1702004 y x) (@lem1702003 y x)). Qed.
Lemma lem1702006 (x : real) : (term169 x) = (term247 x).
Proof. exact (fun_ext (fun y : real => @lem1702005 y x)). Qed.
Lemma lem1702007 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702008 (x : real) : (term170 x) = (term248 x).
Proof. exact (MK_COMB (@lem1702007) (@lem1702006 x)). Qed.
Lemma lem1702009 : term171 = term249.
Proof. exact (fun_ext (fun x : real => @lem1702008 x)). Qed.
Lemma lem1702010 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702067 : term146 = term250.
Proof. exact (MK_COMB (@lem1702010) (@lem1702009)). Qed.
Lemma lem1702068 (h1 : term146) : term250.
Proof. exact (EQ_MP (@lem1702067) (@lem1701591 h1)). Qed.
Lemma lem1702079 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1702096 (y : real) (x : real) : (term204 y x) = (term204 y x).
Proof. exact (eq_refl (term204 y x)). Qed.
Lemma lem1702097 (x : real) : (term205 x) = (term205 x).
Proof. exact (fun_ext (fun y : real => @lem1702096 y x)). Qed.
Lemma lem1702098 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702099 (x : real) : (term206 x) = (term206 x).
Proof. exact (MK_COMB (@lem1702098) (@lem1702097 x)). Qed.
Lemma lem1702100 : term207 = term207.
Proof. exact (fun_ext (fun x : real => @lem1702099 x)). Qed.
Lemma lem1702101 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702102 : term208 = term208.
Proof. exact (MK_COMB (@lem1702101) (@lem1702100)). Qed.
Lemma lem1702103 (h1 : term182) : term208.
Proof. exact (EQ_MP (@lem1702102) (@lem1701751 h1)). Qed.
Lemma lem1702128 (y : real) (x : real) (z : real) : (term69 y x z) = (term69 y x z).
Proof. exact (eq_refl (term69 y x z)). Qed.
Lemma lem1702129 (y : real) (x : real) : (term71 y x) = (term71 y x).
Proof. exact (fun_ext (fun z : real => @lem1702128 y x z)). Qed.
Lemma lem1702130 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702131 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (MK_COMB (@lem1702130) (@lem1702129 y x)). Qed.
Lemma lem1702132 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1702131 y x)). Qed.
Lemma lem1702133 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702134 (x : real) : (term74 x) = (term74 x).
Proof. exact (MK_COMB (@lem1702133) (@lem1702132 x)). Qed.
Lemma lem1702135 : term75 = term75.
Proof. exact (fun_ext (fun x : real => @lem1702134 x)). Qed.
Lemma lem1702136 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702137 : term76 = term76.
Proof. exact (MK_COMB (@lem1702136) (@lem1702135)). Qed.
Lemma lem1702138 (h1 : term24) : term76.
Proof. exact (EQ_MP (@lem1702137) (@lem1701834 h1)). Qed.
Lemma lem1702163 (x : real) : (term225 x) = (term225 x).
Proof. exact (eq_refl (term225 x)). Qed.
Lemma lem1702164 : term219 = term219.
Proof. exact (fun_ext (fun x : real => @lem1702163 x)). Qed.
Lemma lem1702165 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702166 : term237 = term237.
Proof. exact (MK_COMB (@lem1702165) (@lem1702164)). Qed.
Lemma lem1702191 (x : real) : (term221 x) = (term221 x).
Proof. exact (eq_refl (term221 x)). Qed.
Lemma lem1702192 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem1702191 x)). Qed.
Lemma lem1702193 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702194 : term232 = term232.
Proof. exact (MK_COMB (@lem1702193) (@lem1702192)). Qed.
Lemma lem1702195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1702196 : term234 = term234.
Proof. exact (MK_COMB (@lem1702195) (@lem1702194)). Qed.
Lemma lem1702197 : term238 = term238.
Proof. exact (MK_COMB (@lem1702196) (@lem1702166)). Qed.
Lemma lem1702198 (h1 : term177) : term238.
Proof. exact (EQ_MP (@lem1702197) (@lem1701979 h1)). Qed.
Lemma lem1702207 (x : real) : ((term172 x) = x) = ((term172 x) = x).
Proof. exact (eq_refl ((term172 x) = x)). Qed.
Lemma lem1702208 : term173 = term173.
Proof. exact (fun_ext (fun x : real => @lem1702207 x)). Qed.
Lemma lem1702209 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702210 : term174 = term174.
Proof. exact (MK_COMB (@lem1702209) (@lem1702208)). Qed.
Lemma lem1702211 (h1 : term174) : term174.
Proof. exact (EQ_MP (@lem1702210) (@lem1701992 h1)). Qed.
Lemma lem1702244 (y : real) (x : real) : (term245 y x) = (term245 y x).
Proof. exact (eq_refl (term245 y x)). Qed.
Lemma lem1702245 (x : real) : (term247 x) = (term247 x).
Proof. exact (fun_ext (fun y : real => @lem1702244 y x)). Qed.
Lemma lem1702246 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702247 (x : real) : (term248 x) = (term248 x).
Proof. exact (MK_COMB (@lem1702246) (@lem1702245 x)). Qed.
Lemma lem1702248 : term249 = term249.
Proof. exact (fun_ext (fun x : real => @lem1702247 x)). Qed.
Lemma lem1702249 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702250 : term250 = term250.
Proof. exact (MK_COMB (@lem1702249) (@lem1702248)). Qed.
Lemma lem1702251 (h1 : term146) : term250.
Proof. exact (EQ_MP (@lem1702250) (@lem1702068 h1)). Qed.
Lemma lem1702303 (n : nat) (e : real) (h1 : term194 n e) : term194 n e.
Proof. exact (h1). Qed.
Lemma lem1702304 (n : nat) (e : real) (h1 : term194 n e) : term189 n e.
Proof. exact (proj2 (@lem1702303 n e h1)). Qed.
Lemma lem1702307 (h1 : term177) : term232.
Proof. exact (proj1 (@lem1702198 h1)). Qed.
Lemma lem1702309 (n : nat) (e : real) (h1 : term185 n e) : term185 n e.
Proof. exact (h1). Qed.
Lemma lem1702315 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1702323 (y : real) (x : real) : (term204 y x) = (term204 y x).
Proof. exact (eq_refl (term204 y x)). Qed.
Lemma lem1702324 (x : real) : (term205 x) = (term205 x).
Proof. exact (fun_ext (fun y : real => @lem1702323 y x)). Qed.
Lemma lem1702325 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702326 (x : real) : (term206 x) = (term206 x).
Proof. exact (MK_COMB (@lem1702325) (@lem1702324 x)). Qed.
Lemma lem1702327 : term207 = term207.
Proof. exact (fun_ext (fun x : real => @lem1702326 x)). Qed.
Lemma lem1702328 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702330 : term208 = term208.
Proof. exact (MK_COMB (@lem1702328) (@lem1702327)). Qed.
Lemma lem1702331 (h1 : term182) : term208.
Proof. exact (EQ_MP (@lem1702330) (@lem1702103 h1)). Qed.
Lemma lem1702397 (x : real) : (term221 x) = (term221 x).
Proof. exact (eq_refl (term221 x)). Qed.
Lemma lem1702398 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem1702397 x)). Qed.
Lemma lem1702399 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702401 : term232 = term232.
Proof. exact (MK_COMB (@lem1702399) (@lem1702398)). Qed.
Lemma lem1702402 (h1 : term177) : term232.
Proof. exact (EQ_MP (@lem1702401) (@lem1702307 h1)). Qed.
Lemma lem1702419 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1702423 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1702453 (y : real) (x : real) (z : real) : (term69 y x z) = (term69 y x z).
Proof. exact (eq_refl (term69 y x z)). Qed.
Lemma lem1702454 (y : real) (x : real) : (term71 y x) = (term71 y x).
Proof. exact (fun_ext (fun z : real => @lem1702453 y x z)). Qed.
Lemma lem1702455 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702456 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (MK_COMB (@lem1702455) (@lem1702454 y x)). Qed.
Lemma lem1702457 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1702456 y x)). Qed.
Lemma lem1702458 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702459 (x : real) : (term74 x) = (term74 x).
Proof. exact (MK_COMB (@lem1702458) (@lem1702457 x)). Qed.
Lemma lem1702460 : term75 = term75.
Proof. exact (fun_ext (fun x : real => @lem1702459 x)). Qed.
Lemma lem1702461 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702463 : term76 = term76.
Proof. exact (MK_COMB (@lem1702461) (@lem1702460)). Qed.
Lemma lem1702464 (h1 : term24) : term76.
Proof. exact (EQ_MP (@lem1702463) (@lem1702138 h1)). Qed.
Lemma lem1702505 (x : real) : (term221 x) = (term221 x).
Proof. exact (eq_refl (term221 x)). Qed.
Lemma lem1702506 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem1702505 x)). Qed.
Lemma lem1702507 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702509 : term232 = term232.
Proof. exact (MK_COMB (@lem1702507) (@lem1702506)). Qed.
Lemma lem1702510 (h1 : term177) : term232.
Proof. exact (EQ_MP (@lem1702509) (@lem1702307 h1)). Qed.
Lemma lem1702527 (n : nat) (h1 : term85 n) : term85 n.
Proof. exact (h1). Qed.
Lemma lem1702531 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1702574 (x : real) : ((term172 x) = x) = ((term172 x) = x).
Proof. exact (eq_refl ((term172 x) = x)). Qed.
Lemma lem1702575 : term173 = term173.
Proof. exact (fun_ext (fun x : real => @lem1702574 x)). Qed.
Lemma lem1702576 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702578 : term174 = term174.
Proof. exact (MK_COMB (@lem1702576) (@lem1702575)). Qed.
Lemma lem1702579 (h1 : term174) : term174.
Proof. exact (EQ_MP (@lem1702578) (@lem1702211 h1)). Qed.
Lemma lem1702593 (y : real) (x : real) : (term245 y x) = (term245 y x).
Proof. exact (eq_refl (term245 y x)). Qed.
Lemma lem1702594 (x : real) : (term247 x) = (term247 x).
Proof. exact (fun_ext (fun y : real => @lem1702593 y x)). Qed.
Lemma lem1702595 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702596 (x : real) : (term248 x) = (term248 x).
Proof. exact (MK_COMB (@lem1702595) (@lem1702594 x)). Qed.
Lemma lem1702597 : term249 = term249.
Proof. exact (fun_ext (fun x : real => @lem1702596 x)). Qed.
Lemma lem1702598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702600 : term250 = term250.
Proof. exact (MK_COMB (@lem1702598) (@lem1702597)). Qed.
Lemma lem1702601 (h1 : term146) : term250.
Proof. exact (EQ_MP (@lem1702600) (@lem1702251 h1)). Qed.
Lemma lem1702613 (x : real) : (term221 x) = (term221 x).
Proof. exact (eq_refl (term221 x)). Qed.
Lemma lem1702614 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem1702613 x)). Qed.
Lemma lem1702615 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1702617 : term232 = term232.
Proof. exact (MK_COMB (@lem1702615) (@lem1702614)). Qed.
Lemma lem1702618 (h1 : term177) : term232.
Proof. exact (EQ_MP (@lem1702617) (@lem1702307 h1)). Qed.
Lemma lem1702635 (n : nat) (e : real) (h1 : term89 n e) : term89 n e.
Proof. exact (h1). Qed.
Lemma lem1702636 (_26331 : real) (h1 : term182) : term251 _26331.
Proof. exact (@lem1702331 h1 _26331). Qed.
Lemma lem1702637 (_26331 : real) : (term251 _26331) = (term206 _26331).
Proof. exact (eq_refl (term251 _26331)). Qed.
Lemma lem1702638 (_26331 : real) (h1 : term182) : term206 _26331.
Proof. exact (EQ_MP (@lem1702637 _26331) (@lem1702636 _26331 h1)). Qed.
Lemma lem1702639 (_26331 : real) (_26332 : real) (h1 : term182) : term252 _26331 _26332.
Proof. exact (@lem1702638 _26331 h1 _26332). Qed.
Lemma lem1702640 (_26332 : real) (_26331 : real) : (term252 _26331 _26332) = (term204 _26332 _26331).
Proof. exact (eq_refl (term252 _26331 _26332)). Qed.
Lemma lem1702660 (_26339 : real) (h1 : term177) : term220 _26339.
Proof. exact (@lem1702402 h1 _26339). Qed.
Lemma lem1702661 (_26339 : real) : (term220 _26339) = (term221 _26339).
Proof. exact (eq_refl (term220 _26339)). Qed.
Lemma lem1702672 (_26343 : real) (h1 : term24) : term78 _26343.
Proof. exact (@lem1702464 h1 _26343). Qed.
Lemma lem1702673 (_26343 : real) : (term78 _26343) = (term74 _26343).
Proof. exact (eq_refl (term78 _26343)). Qed.
Lemma lem1702674 (_26343 : real) (h1 : term24) : term74 _26343.
Proof. exact (EQ_MP (@lem1702673 _26343) (@lem1702672 _26343 h1)). Qed.
Lemma lem1702675 (_26343 : real) (_26344 : real) (h1 : term24) : term79 _26343 _26344.
Proof. exact (@lem1702674 _26343 h1 _26344). Qed.
Lemma lem1702676 (_26344 : real) (_26343 : real) : (term79 _26343 _26344) = (term72 _26344 _26343).
Proof. exact (eq_refl (term79 _26343 _26344)). Qed.
Lemma lem1702677 (_26344 : real) (_26343 : real) (h1 : term24) : term72 _26344 _26343.
Proof. exact (EQ_MP (@lem1702676 _26344 _26343) (@lem1702675 _26343 _26344 h1)). Qed.
Lemma lem1702678 (_26344 : real) (_26343 : real) (_26345 : real) (h1 : term24) : term80 _26344 _26343 _26345.
Proof. exact (@lem1702677 _26344 _26343 h1 _26345). Qed.
Lemma lem1702679 (_26344 : real) (_26343 : real) (_26345 : real) : (term80 _26344 _26343 _26345) = (term69 _26344 _26343 _26345).
Proof. exact (eq_refl (term80 _26344 _26343 _26345)). Qed.
Lemma lem1702680 (_26344 : real) (_26343 : real) (_26345 : real) (h1 : term24) : term69 _26344 _26343 _26345.
Proof. exact (EQ_MP (@lem1702679 _26344 _26343 _26345) (@lem1702678 _26344 _26343 _26345 h1)). Qed.
Lemma lem1702690 (_26349 : real) (h1 : term177) : term220 _26349.
Proof. exact (@lem1702510 h1 _26349). Qed.
Lemma lem1702691 (_26349 : real) : (term220 _26349) = (term221 _26349).
Proof. exact (eq_refl (term220 _26349)). Qed.
Lemma lem1702711 (_26356 : real) (h1 : term174) : term253 _26356.
Proof. exact (@lem1702579 h1 _26356). Qed.
Lemma lem1702712 (_26356 : real) : (term253 _26356) = ((term172 _26356) = _26356).
Proof. exact (eq_refl (term253 _26356)). Qed.
Lemma lem1702714 (_26357 : real) (h1 : term146) : term254 _26357.
Proof. exact (@lem1702601 h1 _26357). Qed.
Lemma lem1702715 (_26357 : real) : (term254 _26357) = (term248 _26357).
Proof. exact (eq_refl (term254 _26357)). Qed.
Lemma lem1702716 (_26357 : real) (h1 : term146) : term248 _26357.
Proof. exact (EQ_MP (@lem1702715 _26357) (@lem1702714 _26357 h1)). Qed.
Lemma lem1702717 (_26357 : real) (_26358 : real) (h1 : term146) : term255 _26357 _26358.
Proof. exact (@lem1702716 _26357 h1 _26358). Qed.
Lemma lem1702718 (_26358 : real) (_26357 : real) : (term255 _26357 _26358) = (term245 _26358 _26357).
Proof. exact (eq_refl (term255 _26357 _26358)). Qed.
Lemma lem1702719 (_26358 : real) (_26357 : real) (h1 : term146) : term245 _26358 _26357.
Proof. exact (EQ_MP (@lem1702718 _26358 _26357) (@lem1702717 _26357 _26358 h1)). Qed.
Lemma lem1702720 (_26359 : real) (h1 : term177) : term220 _26359.
Proof. exact (@lem1702618 h1 _26359). Qed.
Lemma lem1702721 (_26359 : real) : (term220 _26359) = (term221 _26359).
Proof. exact (eq_refl (term220 _26359)). Qed.
Lemma lem1702727 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1702761 (n : nat) (e : real) (h1 : term194 n e) : term120 e n.
Proof. exact (proj1 (@lem1702303 n e h1)). Qed.
Lemma lem1702775 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1702777 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1702794 (_26344 : real) (_26343 : real) (_26345 : real) : (term69 _26344 _26343 _26345) = (term81 _26344 _26343 _26345).
Proof. exact (@lem1700448 (term82 _26343 _26344) (term82 _26344 _26345) (real_lt _26343 _26345)). Qed.
Lemma lem1702795 (_26344 : real) (_26343 : real) (_26345 : real) (h1 : term24) : term81 _26344 _26343 _26345.
Proof. exact (EQ_MP (@lem1702794 _26344 _26343 _26345) (@lem1702680 _26344 _26343 _26345 h1)). Qed.
Lemma lem1702817 (_26349 : real) (h1 : term177) : term221 _26349.
Proof. exact (EQ_MP (@lem1702691 _26349) (@lem1702690 _26349 h1)). Qed.
Lemma lem1702825 (n : nat) (h1 : term85 n) : term85 n.
Proof. exact (h1). Qed.
Lemma lem1702827 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1702858 (_26358 : real) (_26357 : real) : (term245 _26358 _26357) = (term256 _26358 _26357).
Proof. exact (@lem1700448 (term42 _26357) (term82 _26357 _26358) (term241 _26358 _26357)). Qed.
Lemma lem1702859 (_26358 : real) (_26357 : real) (h1 : term146) : term256 _26358 _26357.
Proof. exact (EQ_MP (@lem1702858 _26358 _26357) (@lem1702719 _26358 _26357 h1)). Qed.
Lemma lem1702867 (_26359 : real) (h1 : term177) : term221 _26359.
Proof. exact (EQ_MP (@lem1702721 _26359) (@lem1702720 _26359 h1)). Qed.
Lemma lem1702875 (n : nat) (e : real) (h1 : term89 n e) : term89 n e.
Proof. exact (h1). Qed.
Lemma lem1702903 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1702917 (_26332 : real) (_26331 : real) (h1 : term182) : term204 _26332 _26331.
Proof. exact (EQ_MP (@lem1702640 _26332 _26331) (@lem1702639 _26331 _26332 h1)). Qed.
Lemma lem1702960 (e : real) : (term118 e) = (term118 e).
Proof. exact (eq_refl (term118 e)). Qed.
Lemma lem1702961 (e : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term119 e n) = (term257 e).
Proof. exact (MK_COMB (@lem1702960 e) (@lem1702775 n h1)). Qed.
Lemma lem1702962 (e : real) : (term257 e) = (term258 e).
Proof. exact (eq_refl (term257 e)). Qed.
Lemma lem1702963 (e : real) (n : nat) : (term259 e n) = (term259 e n).
Proof. exact (eq_refl (term259 e n)). Qed.
Lemma lem1702964 (n : nat) (e : real) : ((term119 e n) = (term257 e)) = ((term119 e n) = (term258 e)).
Proof. exact (MK_COMB (@lem1702963 e n) (@lem1702962 e)). Qed.
Lemma lem1702965 (e : real) (n : nat) : (term119 e n) = (term120 e n).
Proof. exact (eq_refl (term119 e n)). Qed.
Lemma lem1702966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1702967 (e : real) (n : nat) : (term259 e n) = (term260 e n).
Proof. exact (MK_COMB (@lem1702966) (@lem1702965 e n)). Qed.
Lemma lem1702968 (e : real) : (term258 e) = (term258 e).
Proof. exact (eq_refl (term258 e)). Qed.
Lemma lem1702969 (n : nat) (e : real) : ((term119 e n) = (term258 e)) = ((term120 e n) = (term258 e)).
Proof. exact (MK_COMB (@lem1702967 e n) (@lem1702968 e)). Qed.
Lemma lem1702970 (n : nat) (e : real) : ((term119 e n) = (term257 e)) = ((term120 e n) = (term258 e)).
Proof. exact (TRANS (@lem1702964 n e) (@lem1702969 n e)). Qed.
Lemma lem1702971 (e : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term120 e n) = (term258 e).
Proof. exact (EQ_MP (@lem1702970 n e) (@lem1702961 e n h1)). Qed.
Lemma lem1702986 (_26339 : real) (h1 : term177) : term221 _26339.
Proof. exact (EQ_MP (@lem1702661 _26339) (@lem1702660 _26339 h1)). Qed.
Lemma lem1703049 (e : real) (n : nat) (h1 : term194 n e) (h2 : n = (NUMERAL 0)) : term258 e.
Proof. exact (EQ_MP (@lem1702971 e n h2) (@lem1702761 n e h1)). Qed.
Lemma lem1703050 (e : real) (n : nat) (h1 : term194 n e) (h2 : n = (NUMERAL 0)) : term261 e.
Proof. exact (fun h0 : term262 e => @lem1703049 e n h1 h2). Qed.
Lemma lem1703052 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703053 (e : real) : (term261 e) = (term258 e).
Proof. exact (@lem1703052 (term258 e)). Qed.
Lemma lem1703054 (e : real) (n : nat) (h1 : term194 n e) (h2 : n = (NUMERAL 0)) : term258 e.
Proof. exact (EQ_MP (@lem1703053 e) (@lem1703050 e n h1 h2)). Qed.
Lemma lem1703056 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1703057 (e : real) (h1 : term37 e) : term112 e.
Proof. exact (fun h0 : term42 e => @lem1703056 e h1). Qed.
Lemma lem1703059 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703060 (e : real) : (term112 e) = (term37 e).
Proof. exact (@lem1703059 (term37 e)). Qed.
Lemma lem1703061 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (EQ_MP (@lem1703060 e) (@lem1703057 e h1)). Qed.
Lemma lem1703063 (b : Prop) (a : Prop) : (a \/ b) = (term97 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1703064 (_26339 : real) : (term221 _26339) = (term263 _26339).
Proof. exact (@lem1703063 (term42 _26339) (term175 _26339)). Qed.
Lemma lem1703066 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703067 (_26339 : real) : (term264 _26339) = (term37 _26339).
Proof. exact (@lem1703066 (term37 _26339)). Qed.
Lemma lem1703068 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1703069 (_26339 : real) : (term265 _26339) = (term162 _26339).
Proof. exact (MK_COMB (@lem1703068) (@lem1703067 _26339)). Qed.
Lemma lem1703070 (_26339 : real) : (term175 _26339) = (term175 _26339).
Proof. exact (eq_refl (term175 _26339)). Qed.
Lemma lem1703071 (_26339 : real) : (term263 _26339) = (term266 _26339).
Proof. exact (MK_COMB (@lem1703069 _26339) (@lem1703070 _26339)). Qed.
Lemma lem1703072 (_26339 : real) : (term221 _26339) = (term266 _26339).
Proof. exact (TRANS (@lem1703064 _26339) (@lem1703071 _26339)). Qed.
Lemma lem1703075 (_26339 : real) (h1 : term177) : term266 _26339.
Proof. exact (EQ_MP (@lem1703072 _26339) (@lem1702986 _26339 h1)). Qed.
Lemma lem1703076 (e : real) (h1 : term177) : term266 e.
Proof. exact (@lem1703075 e h1). Qed.
Lemma lem1703079 (e : real) (h1 : term177) (h2 : term37 e) : term175 e.
Proof. exact (@lem1703076 e h1 (@lem1703061 e h2)). Qed.
Lemma lem1703080 (e : real) (h1 : term177) (h2 : term37 e) : term267 e.
Proof. exact (fun h0 : term268 e => @lem1703079 e h1 h2). Qed.
Lemma lem1703082 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703083 (e : real) : (term267 e) = (term175 e).
Proof. exact (@lem1703082 (term175 e)). Qed.
Lemma lem1703084 (e : real) (h1 : term177) (h2 : term37 e) : term175 e.
Proof. exact (EQ_MP (@lem1703083 e) (@lem1703080 e h1 h2)). Qed.
Lemma lem1703086 (a : Prop) (b : Prop) : (term269 a b) = (term270 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1703087 (_26332 : real) (_26331 : real) : (term204 _26332 _26331) = (term178 _26332 _26331).
Proof. exact (@lem1703086 (real_lt _26331 _26332) (real_lt _26332 _26331)). Qed.
Lemma lem1703089 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1703090 (_26332 : real) (_26331 : real) : (term178 _26332 _26331) = (term271 _26332 _26331).
Proof. exact (@lem1703089 (term272 _26332 _26331)). Qed.
Lemma lem1703091 (_26332 : real) (_26331 : real) : (term204 _26332 _26331) = (term271 _26332 _26331).
Proof. exact (TRANS (@lem1703087 _26332 _26331) (@lem1703090 _26332 _26331)). Qed.
Lemma lem1703093 (n : nat) (e : real) (h1 : term177) (h2 : term194 n e) (h3 : n = (NUMERAL 0)) (h4 : term37 e) : term273 e.
Proof. exact (conj (@lem1703054 e n h2 h3) (@lem1703084 e h1 h4)). Qed.
Lemma lem1703095 (_26332 : real) (_26331 : real) (h1 : term182) : term271 _26332 _26331.
Proof. exact (EQ_MP (@lem1703091 _26332 _26331) (@lem1702917 _26332 _26331 h1)). Qed.
Lemma lem1703096 (e : real) (h1 : term182) : term274 e.
Proof. exact (@lem1703095 term111 (real_inv e) h1). Qed.
Lemma lem1703099 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : False.
Proof. exact (@lem1703096 e h1 (@lem1703093 n e h2 h3 h4 h5)). Qed.
Lemma lem1703100 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : term114.
Proof. exact (fun h0 : ~ False => @lem1703099 n e h1 h2 h3 h4 h5). Qed.
Lemma lem1703102 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703103 : term114 = False.
Proof. exact (@lem1703102 False). Qed.
Lemma lem1703104 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703103) (@lem1703100 n e h1 h2 h3 h4 h5)). Qed.
Lemma lem1703153 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1703154 (e : real) (h1 : term37 e) : term112 e.
Proof. exact (fun h0 : term42 e => @lem1703153 e h1). Qed.
Lemma lem1703156 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703157 (e : real) : (term112 e) = (term37 e).
Proof. exact (@lem1703156 (term37 e)). Qed.
Lemma lem1703158 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (EQ_MP (@lem1703157 e) (@lem1703154 e h1)). Qed.
Lemma lem1703160 (b : Prop) (a : Prop) : (a \/ b) = (term97 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1703161 (_26349 : real) : (term221 _26349) = (term263 _26349).
Proof. exact (@lem1703160 (term42 _26349) (term175 _26349)). Qed.
Lemma lem1703163 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703164 (_26349 : real) : (term264 _26349) = (term37 _26349).
Proof. exact (@lem1703163 (term37 _26349)). Qed.
Lemma lem1703165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1703166 (_26349 : real) : (term265 _26349) = (term162 _26349).
Proof. exact (MK_COMB (@lem1703165) (@lem1703164 _26349)). Qed.
Lemma lem1703167 (_26349 : real) : (term175 _26349) = (term175 _26349).
Proof. exact (eq_refl (term175 _26349)). Qed.
Lemma lem1703168 (_26349 : real) : (term263 _26349) = (term266 _26349).
Proof. exact (MK_COMB (@lem1703166 _26349) (@lem1703167 _26349)). Qed.
Lemma lem1703169 (_26349 : real) : (term221 _26349) = (term266 _26349).
Proof. exact (TRANS (@lem1703161 _26349) (@lem1703168 _26349)). Qed.
Lemma lem1703172 (_26349 : real) (h1 : term177) : term266 _26349.
Proof. exact (EQ_MP (@lem1703169 _26349) (@lem1702817 _26349 h1)). Qed.
Lemma lem1703173 (e : real) (h1 : term177) : term266 e.
Proof. exact (@lem1703172 e h1). Qed.
Lemma lem1703176 (e : real) (h1 : term177) (h2 : term37 e) : term175 e.
Proof. exact (@lem1703173 e h1 (@lem1703158 e h2)). Qed.
Lemma lem1703177 (e : real) (h1 : term177) (h2 : term37 e) : term267 e.
Proof. exact (fun h0 : term268 e => @lem1703176 e h1 h2). Qed.
Lemma lem1703179 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703180 (e : real) : (term267 e) = (term175 e).
Proof. exact (@lem1703179 (term175 e)). Qed.
Lemma lem1703181 (e : real) (h1 : term177) (h2 : term37 e) : term175 e.
Proof. exact (EQ_MP (@lem1703180 e) (@lem1703177 e h1 h2)). Qed.
Lemma lem1703183 (n : nat) (e : real) (h1 : term194 n e) : term120 e n.
Proof. exact (proj1 (@lem1702303 n e h1)). Qed.
Lemma lem1703184 (n : nat) (e : real) (h1 : term194 n e) : term275 e n.
Proof. exact (fun h0 : term276 e n => @lem1703183 n e h1). Qed.
Lemma lem1703186 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703187 (e : real) (n : nat) : (term275 e n) = (term120 e n).
Proof. exact (@lem1703186 (term120 e n)). Qed.
Lemma lem1703188 (n : nat) (e : real) (h1 : term194 n e) : term120 e n.
Proof. exact (EQ_MP (@lem1703187 e n) (@lem1703184 n e h1)). Qed.
Lemma lem1703204 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1703205 (_26343 : real) (_26344 : real) (_26345 : real) : (term90 _26344 _26343 _26345) = (term91 _26343 _26344 _26345).
Proof. exact (@lem1703204 (real_lt _26343 _26345) (term82 _26344 _26345)). Qed.
Lemma lem1703211 (_26343 : real) (_26344 : real) : (term92 _26343 _26344) = (term92 _26343 _26344).
Proof. exact (eq_refl (term92 _26343 _26344)). Qed.
Lemma lem1703212 (_26343 : real) (_26344 : real) (_26345 : real) : (term81 _26344 _26343 _26345) = (term93 _26343 _26344 _26345).
Proof. exact (MK_COMB (@lem1703211 _26343 _26344) (@lem1703205 _26343 _26344 _26345)). Qed.
Lemma lem1703216 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1703217 (_26343 : real) (_26344 : real) (_26345 : real) : (term93 _26343 _26344 _26345) = (term94 _26343 _26344 _26345).
Proof. exact (@lem1703216 (real_lt _26343 _26345) (term82 _26343 _26344) (term82 _26344 _26345)). Qed.
Lemma lem1703233 (_26343 : real) (_26344 : real) (_26345 : real) : (term81 _26344 _26343 _26345) = (term94 _26343 _26344 _26345).
Proof. exact (TRANS (@lem1703212 _26343 _26344 _26345) (@lem1703217 _26343 _26344 _26345)). Qed.
Lemma lem1703234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1703235 (_26343 : real) (_26344 : real) (_26345 : real) : (term95 _26344 _26343 _26345) = (term96 _26343 _26344 _26345).
Proof. exact (MK_COMB (@lem1703234) (@lem1703233 _26343 _26344 _26345)). Qed.
Lemma lem1703251 (_26343 : real) (_26344 : real) (_26345 : real) : (term94 _26343 _26344 _26345) = (term94 _26343 _26344 _26345).
Proof. exact (eq_refl (term94 _26343 _26344 _26345)). Qed.
Lemma lem1703252 (_26343 : real) (_26344 : real) (_26345 : real) : ((term81 _26344 _26343 _26345) = (term94 _26343 _26344 _26345)) = ((term94 _26343 _26344 _26345) = (term94 _26343 _26344 _26345)).
Proof. exact (MK_COMB (@lem1703235 _26343 _26344 _26345) (@lem1703251 _26343 _26344 _26345)). Qed.
Lemma lem1703254 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1703255 (x : Prop) : (x = x) = True.
Proof. exact (@lem1703254 Prop x). Qed.
Lemma lem1703256 (_26343 : real) (_26344 : real) (_26345 : real) : ((term94 _26343 _26344 _26345) = (term94 _26343 _26344 _26345)) = True.
Proof. exact (@lem1703255 (term94 _26343 _26344 _26345)). Qed.
Lemma lem1703257 (_26343 : real) (_26344 : real) (_26345 : real) : ((term81 _26344 _26343 _26345) = (term94 _26343 _26344 _26345)) = True.
Proof. exact (TRANS (@lem1703252 _26343 _26344 _26345) (@lem1703256 _26343 _26344 _26345)). Qed.
Lemma lem1703258 (_26343 : real) (_26344 : real) (_26345 : real) : True = ((term81 _26344 _26343 _26345) = (term94 _26343 _26344 _26345)).
Proof. exact (SYM (@lem1703257 _26343 _26344 _26345)). Qed.
Lemma lem1703259 (_26343 : real) (_26344 : real) (_26345 : real) : (term81 _26344 _26343 _26345) = (term94 _26343 _26344 _26345).
Proof. exact (EQ_MP (@lem1703258 _26343 _26344 _26345) (@lem0)). Qed.
Lemma lem1703260 (_26343 : real) (_26344 : real) (_26345 : real) (h1 : term24) : term94 _26343 _26344 _26345.
Proof. exact (EQ_MP (@lem1703259 _26343 _26344 _26345) (@lem1702795 _26344 _26343 _26345 h1)). Qed.
Lemma lem1703262 (b : Prop) (a : Prop) : (a \/ b) = (term97 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1703263 (_26344 : real) (_26343 : real) (_26345 : real) : (term94 _26343 _26344 _26345) = (term98 _26344 _26343 _26345).
Proof. exact (@lem1703262 (term65 _26343 _26344 _26345) (real_lt _26343 _26345)). Qed.
Lemma lem1703265 (a : Prop) (b : Prop) : (term99 a b) = (term100 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1703266 (_26343 : real) (_26344 : real) (_26345 : real) : (term101 _26343 _26344 _26345) = (term102 _26343 _26344 _26345).
Proof. exact (@lem1703265 (term82 _26343 _26344) (term82 _26344 _26345)). Qed.
Lemma lem1703268 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703269 (_26343 : real) (_26344 : real) : (term104 _26343 _26344) = (real_lt _26343 _26344).
Proof. exact (@lem1703268 (real_lt _26343 _26344)). Qed.
Lemma lem1703270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1703271 (_26343 : real) (_26344 : real) : (term105 _26343 _26344) = (term106 _26343 _26344).
Proof. exact (MK_COMB (@lem1703270) (@lem1703269 _26343 _26344)). Qed.
Lemma lem1703273 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703274 (_26344 : real) (_26345 : real) : (term104 _26344 _26345) = (real_lt _26344 _26345).
Proof. exact (@lem1703273 (real_lt _26344 _26345)). Qed.
Lemma lem1703275 (_26343 : real) (_26344 : real) (_26345 : real) : (term102 _26343 _26344 _26345) = (term70 _26343 _26344 _26345).
Proof. exact (MK_COMB (@lem1703271 _26343 _26344) (@lem1703274 _26344 _26345)). Qed.
Lemma lem1703276 (_26343 : real) (_26344 : real) (_26345 : real) : (term101 _26343 _26344 _26345) = (term70 _26343 _26344 _26345).
Proof. exact (TRANS (@lem1703266 _26343 _26344 _26345) (@lem1703275 _26343 _26344 _26345)). Qed.
Lemma lem1703277 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1703278 (_26343 : real) (_26344 : real) (_26345 : real) : (term107 _26343 _26344 _26345) = (term108 _26343 _26344 _26345).
Proof. exact (MK_COMB (@lem1703277) (@lem1703276 _26343 _26344 _26345)). Qed.
Lemma lem1703279 (_26343 : real) (_26345 : real) : (real_lt _26343 _26345) = (real_lt _26343 _26345).
Proof. exact (eq_refl (real_lt _26343 _26345)). Qed.
Lemma lem1703280 (_26344 : real) (_26343 : real) (_26345 : real) : (term98 _26344 _26343 _26345) = (term31 _26344 _26343 _26345).
Proof. exact (MK_COMB (@lem1703278 _26343 _26344 _26345) (@lem1703279 _26343 _26345)). Qed.
Lemma lem1703281 (_26344 : real) (_26343 : real) (_26345 : real) : (term94 _26343 _26344 _26345) = (term31 _26344 _26343 _26345).
Proof. exact (TRANS (@lem1703263 _26344 _26343 _26345) (@lem1703280 _26344 _26343 _26345)). Qed.
Lemma lem1703283 (n : nat) (e : real) (h1 : term177) (h2 : term194 n e) (h3 : term37 e) : term277 e n.
Proof. exact (conj (@lem1703181 e h1 h3) (@lem1703188 n e h2)). Qed.
Lemma lem1703285 (_26344 : real) (_26343 : real) (_26345 : real) (h1 : term24) : term31 _26344 _26343 _26345.
Proof. exact (EQ_MP (@lem1703281 _26344 _26343 _26345) (@lem1703260 _26343 _26344 _26345 h1)). Qed.
Lemma lem1703286 (e : real) (n : nat) (h1 : term24) : term278 e n.
Proof. exact (@lem1703285 (real_inv e) term111 (real_of_num n) h1). Qed.
Lemma lem1703289 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term194 n e) (h4 : term37 e) : term279 n.
Proof. exact (@lem1703286 e n h1 (@lem1703283 n e h2 h3 h4)). Qed.
Lemma lem1703290 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term194 n e) (h4 : term37 e) : term280 n.
Proof. exact (fun h0 : term281 n => @lem1703289 n e h1 h2 h3 h4). Qed.
Lemma lem1703292 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703293 (n : nat) : (term280 n) = (term279 n).
Proof. exact (@lem1703292 (term279 n)). Qed.
Lemma lem1703294 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term194 n e) (h4 : term37 e) : term279 n.
Proof. exact (EQ_MP (@lem1703293 n) (@lem1703290 n e h1 h2 h3 h4)). Qed.
Lemma lem1703296 (_26349 : real) (h1 : term177) : term266 _26349.
Proof. exact (EQ_MP (@lem1703169 _26349) (@lem1702817 _26349 h1)). Qed.
Lemma lem1703297 (n : nat) (h1 : term177) : term282 n.
Proof. exact (@lem1703296 (real_of_num n) h1). Qed.
Lemma lem1703300 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term194 n e) (h4 : term37 e) : term83 n.
Proof. exact (@lem1703297 n h2 (@lem1703294 n e h1 h2 h3 h4)). Qed.
Lemma lem1703301 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term194 n e) (h4 : term37 e) : term84 n.
Proof. exact (fun h0 : term85 n => @lem1703300 n e h1 h2 h3 h4). Qed.
Lemma lem1703303 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703304 (n : nat) : (term84 n) = (term83 n).
Proof. exact (@lem1703303 (term83 n)). Qed.
Lemma lem1703305 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term194 n e) (h4 : term37 e) : term83 n.
Proof. exact (EQ_MP (@lem1703304 n) (@lem1703301 n e h1 h2 h3 h4)). Qed.
Lemma lem1703308 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1703310 (n : nat) : (term85 n) = (term283 n).
Proof. exact (@lem1703308 (term83 n)). Qed.
Lemma lem1703313 (n : nat) (h1 : term85 n) : term283 n.
Proof. exact (EQ_MP (@lem1703310 n) (@lem1702825 n h1)). Qed.
Lemma lem1703316 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : False.
Proof. exact (@lem1703313 n h3 (@lem1703305 n e h1 h2 h4 h5)). Qed.
Lemma lem1703317 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : term114.
Proof. exact (fun h0 : ~ False => @lem1703316 n e h1 h2 h3 h4 h5). Qed.
Lemma lem1703319 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703320 : term114 = False.
Proof. exact (@lem1703319 False). Qed.
Lemma lem1703321 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703320) (@lem1703317 n e h1 h2 h3 h4 h5)). Qed.
Lemma lem1703322 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1703323 (_26399 : real) (_26401 : real) (h1 : _26399 = _26401) : _26399 = _26401.
Proof. exact (h1). Qed.
Lemma lem1703324 (_26400 : real) (_26402 : real) (h1 : _26400 = _26402) : _26400 = _26402.
Proof. exact (h1). Qed.
Lemma lem1703325 (_26399 : real) (_26401 : real) (h1 : _26399 = _26401) : (real_lt _26399) = (real_lt _26401).
Proof. exact (MK_COMB (@lem1703322) (@lem1703323 _26399 _26401 h1)). Qed.
Lemma lem1703326 (_26399 : real) (_26401 : real) (_26400 : real) (_26402 : real) (h1 : _26399 = _26401) (h2 : _26400 = _26402) : (real_lt _26399 _26400) = (real_lt _26401 _26402).
Proof. exact (MK_COMB (@lem1703325 _26399 _26401 h1) (@lem1703324 _26400 _26402 h2)). Qed.
Lemma lem1703328 (b : Prop) (a : Prop) : term284 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1703329 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : term285 _26401 _26402 _26399 _26400.
Proof. exact (@lem1703328 (real_lt _26401 _26402) (real_lt _26399 _26400)). Qed.
Lemma lem1703330 (_26399 : real) (_26401 : real) (_26400 : real) (_26402 : real) (h1 : _26399 = _26401) (h2 : _26400 = _26402) : term286 _26401 _26402 _26399 _26400.
Proof. exact (@lem1703329 _26401 _26402 _26399 _26400 (@lem1703326 _26399 _26401 _26400 _26402 h1 h2)). Qed.
Lemma lem1703331 (_26402 : real) (_26400 : real) (_26399 : real) (_26401 : real) (h1 : _26399 = _26401) : term287 _26401 _26402 _26399 _26400.
Proof. exact (fun h0 : _26400 = _26402 => @lem1703330 _26399 _26401 _26400 _26402 h1 h0). Qed.
Lemma lem1703333 (a : Prop) (b : Prop) : (a -> b) = (term288 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1703334 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term287 _26401 _26402 _26399 _26400) = (term289 _26401 _26402 _26399 _26400).
Proof. exact (@lem1703333 (_26400 = _26402) (term286 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703335 (_26402 : real) (_26400 : real) (_26399 : real) (_26401 : real) (h1 : _26399 = _26401) : term289 _26401 _26402 _26399 _26400.
Proof. exact (EQ_MP (@lem1703334 _26401 _26402 _26399 _26400) (@lem1703331 _26402 _26400 _26399 _26401 h1)). Qed.
Lemma lem1703336 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : term290 _26401 _26402 _26399 _26400.
Proof. exact (fun h0 : _26399 = _26401 => @lem1703335 _26402 _26400 _26399 _26401 h0). Qed.
Lemma lem1703338 (a : Prop) (b : Prop) : (a -> b) = (term288 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1703339 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term290 _26401 _26402 _26399 _26400) = (term291 _26401 _26402 _26399 _26400).
Proof. exact (@lem1703338 (_26399 = _26401) (term289 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703340 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : term291 _26401 _26402 _26399 _26400.
Proof. exact (EQ_MP (@lem1703339 _26401 _26402 _26399 _26400) (@lem1703336 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703370 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1703371 (n : nat) : (term110 n) = (term110 n).
Proof. exact (@lem1703370 (term110 n)). Qed.
Lemma lem1703372 (n : nat) : term292 n.
Proof. exact (fun h0 : term293 n => @lem1703371 n). Qed.
Lemma lem1703374 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703375 (n : nat) : (term292 n) = ((term110 n) = (term110 n)).
Proof. exact (@lem1703374 ((term110 n) = (term110 n))). Qed.
Lemma lem1703376 (n : nat) : (term110 n) = (term110 n).
Proof. exact (EQ_MP (@lem1703375 n) (@lem1703372 n)). Qed.
Lemma lem1703378 (_26356 : real) (h1 : term174) : (term172 _26356) = _26356.
Proof. exact (EQ_MP (@lem1702712 _26356) (@lem1702711 _26356 h1)). Qed.
Lemma lem1703379 (e : real) (h1 : term174) : (term172 e) = e.
Proof. exact (@lem1703378 e h1). Qed.
Lemma lem1703380 (e : real) (h1 : term174) : term294 e.
Proof. exact (fun h0 : term295 e => @lem1703379 e h1). Qed.
Lemma lem1703382 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703383 (e : real) : (term294 e) = ((term172 e) = e).
Proof. exact (@lem1703382 ((term172 e) = e)). Qed.
Lemma lem1703384 (e : real) (h1 : term174) : (term172 e) = e.
Proof. exact (EQ_MP (@lem1703383 e) (@lem1703380 e h1)). Qed.
Lemma lem1703386 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (h1). Qed.
Lemma lem1703387 (e : real) (h1 : term37 e) : term112 e.
Proof. exact (fun h0 : term42 e => @lem1703386 e h1). Qed.
Lemma lem1703389 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703390 (e : real) : (term112 e) = (term37 e).
Proof. exact (@lem1703389 (term37 e)). Qed.
Lemma lem1703391 (e : real) (h1 : term37 e) : term37 e.
Proof. exact (EQ_MP (@lem1703390 e) (@lem1703387 e h1)). Qed.
Lemma lem1703393 (b : Prop) (a : Prop) : (a \/ b) = (term97 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1703394 (_26359 : real) : (term221 _26359) = (term263 _26359).
Proof. exact (@lem1703393 (term42 _26359) (term175 _26359)). Qed.
Lemma lem1703396 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703397 (_26359 : real) : (term264 _26359) = (term37 _26359).
Proof. exact (@lem1703396 (term37 _26359)). Qed.
Lemma lem1703398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1703399 (_26359 : real) : (term265 _26359) = (term162 _26359).
Proof. exact (MK_COMB (@lem1703398) (@lem1703397 _26359)). Qed.
Lemma lem1703400 (_26359 : real) : (term175 _26359) = (term175 _26359).
Proof. exact (eq_refl (term175 _26359)). Qed.
Lemma lem1703401 (_26359 : real) : (term263 _26359) = (term266 _26359).
Proof. exact (MK_COMB (@lem1703399 _26359) (@lem1703400 _26359)). Qed.
Lemma lem1703402 (_26359 : real) : (term221 _26359) = (term266 _26359).
Proof. exact (TRANS (@lem1703394 _26359) (@lem1703401 _26359)). Qed.
Lemma lem1703405 (_26359 : real) (h1 : term177) : term266 _26359.
Proof. exact (EQ_MP (@lem1703402 _26359) (@lem1702867 _26359 h1)). Qed.
Lemma lem1703406 (e : real) (h1 : term177) : term266 e.
Proof. exact (@lem1703405 e h1). Qed.
Lemma lem1703409 (e : real) (h1 : term177) (h2 : term37 e) : term175 e.
Proof. exact (@lem1703406 e h1 (@lem1703391 e h2)). Qed.
Lemma lem1703410 (e : real) (h1 : term177) (h2 : term37 e) : term267 e.
Proof. exact (fun h0 : term268 e => @lem1703409 e h1 h2). Qed.
Lemma lem1703412 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703413 (e : real) : (term267 e) = (term175 e).
Proof. exact (@lem1703412 (term175 e)). Qed.
Lemma lem1703414 (e : real) (h1 : term177) (h2 : term37 e) : term175 e.
Proof. exact (EQ_MP (@lem1703413 e) (@lem1703410 e h1 h2)). Qed.
Lemma lem1703416 (n : nat) (e : real) (h1 : term194 n e) : term120 e n.
Proof. exact (proj1 (@lem1702303 n e h1)). Qed.
Lemma lem1703417 (n : nat) (e : real) (h1 : term194 n e) : term275 e n.
Proof. exact (fun h0 : term276 e n => @lem1703416 n e h1). Qed.
Lemma lem1703419 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703420 (e : real) (n : nat) : (term275 e n) = (term120 e n).
Proof. exact (@lem1703419 (term120 e n)). Qed.
Lemma lem1703421 (n : nat) (e : real) (h1 : term194 n e) : term120 e n.
Proof. exact (EQ_MP (@lem1703420 e n) (@lem1703417 n e h1)). Qed.
Lemma lem1703427 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1703428 (_26358 : real) (_26357 : real) : (term256 _26358 _26357) = (term296 _26358 _26357).
Proof. exact (@lem1703427 (term82 _26357 _26358) (term42 _26357) (term241 _26358 _26357)). Qed.
Lemma lem1703442 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1703443 (_26358 : real) (_26357 : real) : (term297 _26358 _26357) = (term298 _26358 _26357).
Proof. exact (@lem1703442 (term241 _26358 _26357) (term42 _26357)). Qed.
Lemma lem1703449 (_26357 : real) (_26358 : real) : (term92 _26357 _26358) = (term92 _26357 _26358).
Proof. exact (eq_refl (term92 _26357 _26358)). Qed.
Lemma lem1703450 (_26358 : real) (_26357 : real) : (term296 _26358 _26357) = (term299 _26358 _26357).
Proof. exact (MK_COMB (@lem1703449 _26357 _26358) (@lem1703443 _26358 _26357)). Qed.
Lemma lem1703454 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1703455 (_26358 : real) (_26357 : real) : (term299 _26358 _26357) = (term300 _26358 _26357).
Proof. exact (@lem1703454 (term241 _26358 _26357) (term82 _26357 _26358) (term42 _26357)). Qed.
Lemma lem1703471 (_26358 : real) (_26357 : real) : (term296 _26358 _26357) = (term300 _26358 _26357).
Proof. exact (TRANS (@lem1703450 _26358 _26357) (@lem1703455 _26358 _26357)). Qed.
Lemma lem1703472 (_26358 : real) (_26357 : real) : (term256 _26358 _26357) = (term300 _26358 _26357).
Proof. exact (TRANS (@lem1703428 _26358 _26357) (@lem1703471 _26358 _26357)). Qed.
Lemma lem1703473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1703474 (_26358 : real) (_26357 : real) : (term301 _26358 _26357) = (term302 _26358 _26357).
Proof. exact (MK_COMB (@lem1703473) (@lem1703472 _26358 _26357)). Qed.
Lemma lem1703488 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1703489 (_26358 : real) (_26357 : real) : (term240 _26357 _26358) = (term303 _26358 _26357).
Proof. exact (@lem1703488 (term82 _26357 _26358) (term42 _26357)). Qed.
Lemma lem1703495 (_26358 : real) (_26357 : real) : (term304 _26358 _26357) = (term304 _26358 _26357).
Proof. exact (eq_refl (term304 _26358 _26357)). Qed.
Lemma lem1703496 (_26358 : real) (_26357 : real) : (term305 _26357 _26358) = (term300 _26358 _26357).
Proof. exact (MK_COMB (@lem1703495 _26358 _26357) (@lem1703489 _26358 _26357)). Qed.
Lemma lem1703507 (_26358 : real) (_26357 : real) : ((term256 _26358 _26357) = (term305 _26357 _26358)) = ((term300 _26358 _26357) = (term300 _26358 _26357)).
Proof. exact (MK_COMB (@lem1703474 _26358 _26357) (@lem1703496 _26358 _26357)). Qed.
Lemma lem1703509 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1703510 (x : Prop) : (x = x) = True.
Proof. exact (@lem1703509 Prop x). Qed.
Lemma lem1703511 (_26358 : real) (_26357 : real) : ((term300 _26358 _26357) = (term300 _26358 _26357)) = True.
Proof. exact (@lem1703510 (term300 _26358 _26357)). Qed.
Lemma lem1703512 (_26357 : real) (_26358 : real) : ((term256 _26358 _26357) = (term305 _26357 _26358)) = True.
Proof. exact (TRANS (@lem1703507 _26358 _26357) (@lem1703511 _26358 _26357)). Qed.
Lemma lem1703513 (_26357 : real) (_26358 : real) : True = ((term256 _26358 _26357) = (term305 _26357 _26358)).
Proof. exact (SYM (@lem1703512 _26357 _26358)). Qed.
Lemma lem1703514 (_26357 : real) (_26358 : real) : (term256 _26358 _26357) = (term305 _26357 _26358).
Proof. exact (EQ_MP (@lem1703513 _26357 _26358) (@lem0)). Qed.
Lemma lem1703515 (_26357 : real) (_26358 : real) (h1 : term146) : term305 _26357 _26358.
Proof. exact (EQ_MP (@lem1703514 _26357 _26358) (@lem1702859 _26358 _26357 h1)). Qed.
Lemma lem1703517 (b : Prop) (a : Prop) : (a \/ b) = (term97 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1703518 (_26358 : real) (_26357 : real) : (term305 _26357 _26358) = (term306 _26358 _26357).
Proof. exact (@lem1703517 (term240 _26357 _26358) (term241 _26358 _26357)). Qed.
Lemma lem1703520 (a : Prop) (b : Prop) : (term99 a b) = (term100 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1703521 (_26357 : real) (_26358 : real) : (term307 _26357 _26358) = (term308 _26357 _26358).
Proof. exact (@lem1703520 (term42 _26357) (term82 _26357 _26358)). Qed.
Lemma lem1703523 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703524 (_26357 : real) : (term264 _26357) = (term37 _26357).
Proof. exact (@lem1703523 (term37 _26357)). Qed.
Lemma lem1703525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1703526 (_26357 : real) : (term309 _26357) = (term310 _26357).
Proof. exact (MK_COMB (@lem1703525) (@lem1703524 _26357)). Qed.
Lemma lem1703528 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703529 (_26357 : real) (_26358 : real) : (term104 _26357 _26358) = (real_lt _26357 _26358).
Proof. exact (@lem1703528 (real_lt _26357 _26358)). Qed.
Lemma lem1703530 (_26357 : real) (_26358 : real) : (term308 _26357 _26358) = (term246 _26357 _26358).
Proof. exact (MK_COMB (@lem1703526 _26357) (@lem1703529 _26357 _26358)). Qed.
Lemma lem1703531 (_26357 : real) (_26358 : real) : (term307 _26357 _26358) = (term246 _26357 _26358).
Proof. exact (TRANS (@lem1703521 _26357 _26358) (@lem1703530 _26357 _26358)). Qed.
Lemma lem1703532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1703533 (_26357 : real) (_26358 : real) : (term311 _26357 _26358) = (term312 _26357 _26358).
Proof. exact (MK_COMB (@lem1703532) (@lem1703531 _26357 _26358)). Qed.
Lemma lem1703534 (_26358 : real) (_26357 : real) : (term241 _26358 _26357) = (term241 _26358 _26357).
Proof. exact (eq_refl (term241 _26358 _26357)). Qed.
Lemma lem1703535 (_26358 : real) (_26357 : real) : (term306 _26358 _26357) = (term168 _26358 _26357).
Proof. exact (MK_COMB (@lem1703533 _26357 _26358) (@lem1703534 _26358 _26357)). Qed.
Lemma lem1703536 (_26358 : real) (_26357 : real) : (term305 _26357 _26358) = (term168 _26358 _26357).
Proof. exact (TRANS (@lem1703518 _26358 _26357) (@lem1703535 _26358 _26357)). Qed.
Lemma lem1703538 (n : nat) (e : real) (h1 : term177) (h2 : term194 n e) (h3 : term37 e) : term277 e n.
Proof. exact (conj (@lem1703414 e h1 h3) (@lem1703421 n e h2)). Qed.
Lemma lem1703540 (_26358 : real) (_26357 : real) (h1 : term146) : term168 _26358 _26357.
Proof. exact (EQ_MP (@lem1703536 _26358 _26357) (@lem1703515 _26357 _26358 h1)). Qed.
Lemma lem1703541 (n : nat) (e : real) (h1 : term146) : term313 n e.
Proof. exact (@lem1703540 (real_of_num n) (real_inv e) h1). Qed.
Lemma lem1703544 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term194 n e) (h4 : term37 e) : term314 n e.
Proof. exact (@lem1703541 n e h1 (@lem1703538 n e h2 h3 h4)). Qed.
Lemma lem1703545 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term194 n e) (h4 : term37 e) : term315 n e.
Proof. exact (fun h0 : term316 n e => @lem1703544 n e h1 h2 h3 h4). Qed.
Lemma lem1703547 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703548 (n : nat) (e : real) : (term315 n e) = (term314 n e).
Proof. exact (@lem1703547 (term314 n e)). Qed.
Lemma lem1703549 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term194 n e) (h4 : term37 e) : term314 n e.
Proof. exact (EQ_MP (@lem1703548 n e) (@lem1703545 n e h1 h2 h3 h4)). Qed.
Lemma lem1703567 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1703568 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term289 _26401 _26402 _26399 _26400) = (term317 _26401 _26402 _26399 _26400).
Proof. exact (@lem1703567 (real_lt _26401 _26402) (term318 _26400 _26402) (term82 _26399 _26400)). Qed.
Lemma lem1703586 (_26399 : real) (_26401 : real) : (term319 _26399 _26401) = (term319 _26399 _26401).
Proof. exact (eq_refl (term319 _26399 _26401)). Qed.
Lemma lem1703587 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term291 _26401 _26402 _26399 _26400) = (term320 _26401 _26402 _26399 _26400).
Proof. exact (MK_COMB (@lem1703586 _26399 _26401) (@lem1703568 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703591 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1703592 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term320 _26401 _26402 _26399 _26400) = (term321 _26401 _26402 _26399 _26400).
Proof. exact (@lem1703591 (real_lt _26401 _26402) (term318 _26399 _26401) (term322 _26402 _26399 _26400)). Qed.
Lemma lem1703622 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term291 _26401 _26402 _26399 _26400) = (term321 _26401 _26402 _26399 _26400).
Proof. exact (TRANS (@lem1703587 _26401 _26402 _26399 _26400) (@lem1703592 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1703624 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term323 _26401 _26402 _26399 _26400) = (term324 _26401 _26402 _26399 _26400).
Proof. exact (MK_COMB (@lem1703623) (@lem1703622 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703654 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term321 _26401 _26402 _26399 _26400) = (term321 _26401 _26402 _26399 _26400).
Proof. exact (eq_refl (term321 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703655 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : ((term291 _26401 _26402 _26399 _26400) = (term321 _26401 _26402 _26399 _26400)) = ((term321 _26401 _26402 _26399 _26400) = (term321 _26401 _26402 _26399 _26400)).
Proof. exact (MK_COMB (@lem1703624 _26401 _26402 _26399 _26400) (@lem1703654 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1703658 (x : Prop) : (x = x) = True.
Proof. exact (@lem1703657 Prop x). Qed.
Lemma lem1703659 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : ((term321 _26401 _26402 _26399 _26400) = (term321 _26401 _26402 _26399 _26400)) = True.
Proof. exact (@lem1703658 (term321 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703660 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : ((term291 _26401 _26402 _26399 _26400) = (term321 _26401 _26402 _26399 _26400)) = True.
Proof. exact (TRANS (@lem1703655 _26401 _26402 _26399 _26400) (@lem1703659 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703661 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : True = ((term291 _26401 _26402 _26399 _26400) = (term321 _26401 _26402 _26399 _26400)).
Proof. exact (SYM (@lem1703660 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703662 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term291 _26401 _26402 _26399 _26400) = (term321 _26401 _26402 _26399 _26400).
Proof. exact (EQ_MP (@lem1703661 _26401 _26402 _26399 _26400) (@lem0)). Qed.
Lemma lem1703663 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : term321 _26401 _26402 _26399 _26400.
Proof. exact (EQ_MP (@lem1703662 _26401 _26402 _26399 _26400) (@lem1703340 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703665 (b : Prop) (a : Prop) : (a \/ b) = (term97 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1703666 (_26399 : real) (_26400 : real) (_26401 : real) (_26402 : real) : (term321 _26401 _26402 _26399 _26400) = (term325 _26399 _26400 _26401 _26402).
Proof. exact (@lem1703665 (term326 _26401 _26402 _26399 _26400) (real_lt _26401 _26402)). Qed.
Lemma lem1703668 (a : Prop) (b : Prop) : (term99 a b) = (term100 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1703669 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term327 _26401 _26402 _26399 _26400) = (term328 _26401 _26402 _26399 _26400).
Proof. exact (@lem1703668 (term318 _26399 _26401) (term322 _26402 _26399 _26400)). Qed.
Lemma lem1703671 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703672 (_26399 : real) (_26401 : real) : (term329 _26399 _26401) = (_26399 = _26401).
Proof. exact (@lem1703671 (_26399 = _26401)). Qed.
Lemma lem1703673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1703674 (_26399 : real) (_26401 : real) : (term330 _26399 _26401) = (term331 _26399 _26401).
Proof. exact (MK_COMB (@lem1703673) (@lem1703672 _26399 _26401)). Qed.
Lemma lem1703676 (a : Prop) (b : Prop) : (term99 a b) = (term100 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1703677 (_26402 : real) (_26399 : real) (_26400 : real) : (term332 _26402 _26399 _26400) = (term333 _26402 _26399 _26400).
Proof. exact (@lem1703676 (term318 _26400 _26402) (term82 _26399 _26400)). Qed.
Lemma lem1703679 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703680 (_26400 : real) (_26402 : real) : (term329 _26400 _26402) = (_26400 = _26402).
Proof. exact (@lem1703679 (_26400 = _26402)). Qed.
Lemma lem1703681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1703682 (_26400 : real) (_26402 : real) : (term330 _26400 _26402) = (term331 _26400 _26402).
Proof. exact (MK_COMB (@lem1703681) (@lem1703680 _26400 _26402)). Qed.
Lemma lem1703684 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1703685 (_26399 : real) (_26400 : real) : (term104 _26399 _26400) = (real_lt _26399 _26400).
Proof. exact (@lem1703684 (real_lt _26399 _26400)). Qed.
Lemma lem1703686 (_26402 : real) (_26399 : real) (_26400 : real) : (term333 _26402 _26399 _26400) = (term334 _26402 _26399 _26400).
Proof. exact (MK_COMB (@lem1703682 _26400 _26402) (@lem1703685 _26399 _26400)). Qed.
Lemma lem1703687 (_26402 : real) (_26399 : real) (_26400 : real) : (term332 _26402 _26399 _26400) = (term334 _26402 _26399 _26400).
Proof. exact (TRANS (@lem1703677 _26402 _26399 _26400) (@lem1703686 _26402 _26399 _26400)). Qed.
Lemma lem1703688 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term328 _26401 _26402 _26399 _26400) = (term335 _26401 _26402 _26399 _26400).
Proof. exact (MK_COMB (@lem1703674 _26399 _26401) (@lem1703687 _26402 _26399 _26400)). Qed.
Lemma lem1703689 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term327 _26401 _26402 _26399 _26400) = (term335 _26401 _26402 _26399 _26400).
Proof. exact (TRANS (@lem1703669 _26401 _26402 _26399 _26400) (@lem1703688 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703690 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1703691 (_26401 : real) (_26402 : real) (_26399 : real) (_26400 : real) : (term336 _26401 _26402 _26399 _26400) = (term337 _26401 _26402 _26399 _26400).
Proof. exact (MK_COMB (@lem1703690) (@lem1703689 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703692 (_26401 : real) (_26402 : real) : (real_lt _26401 _26402) = (real_lt _26401 _26402).
Proof. exact (eq_refl (real_lt _26401 _26402)). Qed.
Lemma lem1703693 (_26399 : real) (_26400 : real) (_26401 : real) (_26402 : real) : (term325 _26399 _26400 _26401 _26402) = (term338 _26399 _26400 _26401 _26402).
Proof. exact (MK_COMB (@lem1703691 _26401 _26402 _26399 _26400) (@lem1703692 _26401 _26402)). Qed.
Lemma lem1703694 (_26399 : real) (_26400 : real) (_26401 : real) (_26402 : real) : (term321 _26401 _26402 _26399 _26400) = (term338 _26399 _26400 _26401 _26402).
Proof. exact (TRANS (@lem1703666 _26399 _26400 _26401 _26402) (@lem1703693 _26399 _26400 _26401 _26402)). Qed.
Lemma lem1703696 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term194 n e) (h5 : term37 e) : term339 n e.
Proof. exact (conj (@lem1703384 e h3) (@lem1703549 n e h1 h2 h4 h5)). Qed.
Lemma lem1703697 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term194 n e) (h5 : term37 e) : term340 n e.
Proof. exact (conj (@lem1703376 n) (@lem1703696 n e h1 h2 h3 h4 h5)). Qed.
Lemma lem1703699 (_26399 : real) (_26400 : real) (_26401 : real) (_26402 : real) : term338 _26399 _26400 _26401 _26402.
Proof. exact (EQ_MP (@lem1703694 _26399 _26400 _26401 _26402) (@lem1703663 _26401 _26402 _26399 _26400)). Qed.
Lemma lem1703700 (n : nat) (e : real) : term341 n e.
Proof. exact (@lem1703699 (term110 n) (term172 e) (term110 n) e). Qed.
Lemma lem1703703 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term194 n e) (h5 : term37 e) : term87 n e.
Proof. exact (@lem1703700 n e (@lem1703697 n e h1 h2 h3 h4 h5)). Qed.
Lemma lem1703704 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term194 n e) (h5 : term37 e) : term88 n e.
Proof. exact (fun h0 : term89 n e => @lem1703703 n e h1 h2 h3 h4 h5). Qed.
Lemma lem1703706 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703707 (n : nat) (e : real) : (term88 n e) = (term87 n e).
Proof. exact (@lem1703706 (term87 n e)). Qed.
Lemma lem1703708 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term194 n e) (h5 : term37 e) : term87 n e.
Proof. exact (EQ_MP (@lem1703707 n e) (@lem1703704 n e h1 h2 h3 h4 h5)). Qed.
Lemma lem1703711 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1703713 (n : nat) (e : real) : (term89 n e) = (term342 n e).
Proof. exact (@lem1703711 (term87 n e)). Qed.
Lemma lem1703716 (n : nat) (e : real) (h1 : term89 n e) : term342 n e.
Proof. exact (EQ_MP (@lem1703713 n e) (@lem1702875 n e h1)). Qed.
Lemma lem1703719 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : False.
Proof. exact (@lem1703716 n e h4 (@lem1703708 n e h1 h2 h3 h5 h6)). Qed.
Lemma lem1703720 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : term114.
Proof. exact (fun h0 : ~ False => @lem1703719 n e h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1703722 (p : Prop) : (term86 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1703723 : term114 = False.
Proof. exact (@lem1703722 False). Qed.
Lemma lem1703724 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703723) (@lem1703720 n e h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1703725 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h6 : term37 e => @lem1703104 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702903 e h5)). Qed.
Lemma lem1703727 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703725 n e h1 h2 h3 h4 h5) (@lem1702903 e h5)). Qed.
Lemma lem1703728 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : (term89 n e) = False.
Proof. exact (prop_ext (fun h7 : term89 n e => @lem1703724 n e h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1702875 n e h4)). Qed.
Lemma lem1703729 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703728 n e h1 h2 h3 h4 h5 h6) (@lem1702875 n e h4)). Qed.
Lemma lem1703730 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h7 : term37 e => @lem1703729 n e h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1702827 e h6)). Qed.
Lemma lem1703731 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703730 n e h1 h2 h3 h4 h5 h6) (@lem1702827 e h6)). Qed.
Lemma lem1703732 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : (term85 n) = False.
Proof. exact (prop_ext (fun h6 : term85 n => @lem1703321 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702825 n h3)). Qed.
Lemma lem1703733 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703732 n e h1 h2 h3 h4 h5) (@lem1702825 n h3)). Qed.
Lemma lem1703734 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h6 : term37 e => @lem1703733 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702777 e h5)). Qed.
Lemma lem1703735 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703734 n e h1 h2 h3 h4 h5) (@lem1702777 e h5)). Qed.
Lemma lem1703736 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : n = (NUMERAL 0) => @lem1703727 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702775 n h4)). Qed.
Lemma lem1703737 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703736 n e h1 h2 h3 h4 h5) (@lem1702775 n h4)). Qed.
Lemma lem1703738 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h6 : term37 e => @lem1703737 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702727 e h5)). Qed.
Lemma lem1703739 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703738 n e h1 h2 h3 h4 h5) (@lem1702727 e h5)). Qed.
Lemma lem1703740 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : (term89 n e) = False.
Proof. exact (prop_ext (fun h7 : term89 n e => @lem1703731 n e h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1702635 n e h4)). Qed.
Lemma lem1703741 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703740 n e h1 h2 h3 h4 h5 h6) (@lem1702635 n e h4)). Qed.
Lemma lem1703742 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h7 : term37 e => @lem1703741 n e h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1702531 e h6)). Qed.
Lemma lem1703743 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703742 n e h1 h2 h3 h4 h5 h6) (@lem1702531 e h6)). Qed.
Lemma lem1703744 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : (term85 n) = False.
Proof. exact (prop_ext (fun h6 : term85 n => @lem1703735 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702527 n h3)). Qed.
Lemma lem1703745 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703744 n e h1 h2 h3 h4 h5) (@lem1702527 n h3)). Qed.
Lemma lem1703746 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h6 : term37 e => @lem1703745 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702423 e h5)). Qed.
Lemma lem1703747 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703746 n e h1 h2 h3 h4 h5) (@lem1702423 e h5)). Qed.
Lemma lem1703748 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : n = (NUMERAL 0) => @lem1703739 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702419 n h4)). Qed.
Lemma lem1703749 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703748 n e h1 h2 h3 h4 h5) (@lem1702419 n h4)). Qed.
Lemma lem1703750 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h6 : term37 e => @lem1703749 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702315 e h5)). Qed.
Lemma lem1703751 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703750 n e h1 h2 h3 h4 h5) (@lem1702315 e h5)). Qed.
Lemma lem1703752 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : (term89 n e) = False.
Proof. exact (prop_ext (fun h7 : term89 n e => @lem1703743 n e h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1702635 n e h4)). Qed.
Lemma lem1703753 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703752 n e h1 h2 h3 h4 h5 h6) (@lem1702635 n e h4)). Qed.
Lemma lem1703754 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : term174 = False.
Proof. exact (prop_ext (fun h7 : term174 => @lem1703753 n e h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1702579 h3)). Qed.
Lemma lem1703755 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703754 n e h1 h2 h3 h4 h5 h6) (@lem1702579 h3)). Qed.
Lemma lem1703756 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h7 : term37 e => @lem1703755 n e h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1702531 e h6)). Qed.
Lemma lem1703757 (n : nat) (e : real) (h1 : term146) (h2 : term177) (h3 : term174) (h4 : term89 n e) (h5 : term194 n e) (h6 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703756 n e h1 h2 h3 h4 h5 h6) (@lem1702531 e h6)). Qed.
Lemma lem1703758 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : (term85 n) = False.
Proof. exact (prop_ext (fun h6 : term85 n => @lem1703747 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702527 n h3)). Qed.
Lemma lem1703759 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703758 n e h1 h2 h3 h4 h5) (@lem1702527 n h3)). Qed.
Lemma lem1703760 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h6 : term37 e => @lem1703759 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702423 e h5)). Qed.
Lemma lem1703761 (n : nat) (e : real) (h1 : term24) (h2 : term177) (h3 : term85 n) (h4 : term194 n e) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703760 n e h1 h2 h3 h4 h5) (@lem1702423 e h5)). Qed.
Lemma lem1703762 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : n = (NUMERAL 0) => @lem1703751 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702419 n h4)). Qed.
Lemma lem1703763 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703762 n e h1 h2 h3 h4 h5) (@lem1702419 n h4)). Qed.
Lemma lem1703764 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h6 : term37 e => @lem1703763 n e h1 h2 h3 h4 h5) (fun h6 : False => @lem1702315 e h5)). Qed.
Lemma lem1703765 (n : nat) (e : real) (h1 : term182) (h2 : term177) (h3 : term194 n e) (h4 : n = (NUMERAL 0)) (h5 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703764 n e h1 h2 h3 h4 h5) (@lem1702315 e h5)). Qed.
Lemma lem1703766 (n : nat) (e : real) (h1 : term24) (h2 : term146) (h3 : term177) (h4 : term174) (h5 : term194 n e) (h6 : term185 n e) (h7 : term37 e) : False.
Proof. exact (or_elim (@lem1702309 n e h6) (fun h0 : term85 n => @lem1703761 n e h1 h3 h0 h5 h7) (fun h0 : term89 n e => @lem1703757 n e h2 h3 h4 h0 h5 h7)). Qed.
Lemma lem1703767 (n : nat) (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term194 n e) (h7 : term37 e) : False.
Proof. exact (or_elim (@lem1702304 n e h6) (fun h0 : n = (NUMERAL 0) => @lem1703765 n e h2 h4 h6 h0 h7) (fun h0 : term185 n e => @lem1703766 n e h1 h3 h4 h5 h6 h0 h7)). Qed.
Lemma lem1703768 (n : nat) (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term194 n e) (h7 : term37 e) : (term194 n e) = False.
Proof. exact (prop_ext (fun h8 : term194 n e => @lem1703767 n e h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1702303 n e h6)). Qed.
Lemma lem1703769 (n : nat) (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term194 n e) (h7 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703768 n e h1 h2 h3 h4 h5 h6 h7) (@lem1702303 n e h6)). Qed.
Lemma lem1703770 (n : nat) (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term194 n e) (h7 : term37 e) : term174 = False.
Proof. exact (prop_ext (fun h8 : term174 => @lem1703769 n e h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1702211 h5)). Qed.
Lemma lem1703771 (n : nat) (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term194 n e) (h7 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703770 n e h1 h2 h3 h4 h5 h6 h7) (@lem1702211 h5)). Qed.
Lemma lem1703772 (n : nat) (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term194 n e) (h7 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h8 : term37 e => @lem1703771 n e h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1702079 e h7)). Qed.
Lemma lem1703773 (n : nat) (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term194 n e) (h7 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703772 n e h1 h2 h3 h4 h5 h6 h7) (@lem1702079 e h7)). Qed.
Lemma lem1703774 (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term139 e) (h7 : term37 e) : False.
Proof. exact (ex_elim (@lem1701681 e h6) (fun n : nat => fun h0 : term202 e n => @lem1703773 n e h1 h2 h3 h4 h5 h0 h7)). Qed.
Lemma lem1703775 (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term139 e) (h7 : term37 e) : term174 = False.
Proof. exact (prop_ext (fun h8 : term174 => @lem1703774 e h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1701992 h5)). Qed.
Lemma lem1703776 (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term139 e) (h7 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703775 e h1 h2 h3 h4 h5 h6 h7) (@lem1701992 h5)). Qed.
Lemma lem1703777 (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term139 e) (h7 : term37 e) : (term37 e) = False.
Proof. exact (prop_ext (fun h8 : term37 e => @lem1703776 e h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1701597 e h7)). Qed.
Lemma lem1703778 (e : real) (h1 : term24) (h2 : term182) (h3 : term146) (h4 : term177) (h5 : term174) (h6 : term139 e) (h7 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703777 e h1 h2 h3 h4 h5 h6 h7) (@lem1701597 e h7)). Qed.
Lemma lem1703779 (e : real) (h1 : term24) (h2 : term182) (h3 : term177) (h4 : term174) (h5 : term139 e) (h6 : term37 e) : term144.
Proof. exact (fun h0 : term146 => @lem1703778 e h1 h2 h0 h3 h4 h5 h6). Qed.
Lemma lem1703780 : term144 = term145.
Proof. exact (@lem69 term146). Qed.
Lemma lem1703781 (e : real) (h1 : term24) (h2 : term182) (h3 : term177) (h4 : term174) (h5 : term139 e) (h6 : term37 e) : term145.
Proof. exact (EQ_MP (@lem1703780) (@lem1703779 e h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1703782 (e : real) (h1 : term24) (h2 : term182) (h3 : term177) (h4 : term139 e) (h5 : term37 e) : term149.
Proof. exact (fun h0 : term174 => @lem1703781 e h1 h2 h3 h0 h4 h5). Qed.
Lemma lem1703783 (e : real) (h1 : term24) (h2 : term182) (h3 : term139 e) (h4 : term37 e) : term152.
Proof. exact (fun h0 : term177 => @lem1703782 e h1 h2 h0 h3 h4). Qed.
Lemma lem1703784 (e : real) (h1 : term182) (h2 : term139 e) (h3 : term37 e) : term155.
Proof. exact (fun h0 : term24 => @lem1703783 e h0 h1 h2 h3). Qed.
Lemma lem1703785 (e : real) (h1 : term139 e) (h2 : term37 e) : term158.
Proof. exact (fun h0 : term182 => @lem1703784 e h0 h1 h2). Qed.
Lemma lem1703786 (e : real) (h1 : term37 e) : term161 e.
Proof. exact (fun h0 : term139 e => @lem1703785 e h0 h1). Qed.
Lemma lem1703787 (e : real) : term163 e.
Proof. exact (fun h0 : term37 e => @lem1703786 e h0). Qed.
Lemma lem1703792 : term167.
Proof. exact (fun e : real => @lem1703787 e). Qed.
Lemma lem1703793 : term166.
Proof. exact (EQ_MP (@lem1701584) (@lem1703792)). Qed.
Lemma lem1703794 (e : real) : term343 e.
Proof. exact (@lem1703793 e). Qed.
Lemma lem1703795 (e : real) : (term343 e) = (term140 e).
Proof. exact (eq_refl (term343 e)). Qed.
Lemma lem1703796 (e : real) : term140 e.
Proof. exact (EQ_MP (@lem1703795 e) (@lem1703794 e)). Qed.
Lemma lem1703798 (e : real) : term140 e.
Proof. exact (@lem1701274 e (@lem1703796 e)). Qed.
Lemma lem1703799 (e : real) (h1 : term37 e) : term160 e.
Proof. exact (@lem1703798 e (@lem1701227 e h1)). Qed.
Lemma lem1703800 (e : real) (h1 : term139 e) (h2 : term37 e) : term157.
Proof. exact (@lem1703799 e h2 (@lem1701259 e h1)). Qed.
Lemma lem1703801 (e : real) (h1 : term139 e) (h2 : term37 e) : term154.
Proof. exact (@lem1703800 e h1 h2 (@lem1493879)). Qed.
Lemma lem1703802 (e : real) (h1 : term139 e) (h2 : term37 e) : term151.
Proof. exact (@lem1703801 e h1 h2 (@lem1372268)). Qed.
Lemma lem1703803 (e : real) (h1 : term139 e) (h2 : term37 e) : term148.
Proof. exact (@lem1703802 e h1 h2 (@lem1590037)). Qed.
Lemma lem1703804 (e : real) (h1 : term139 e) (h2 : term37 e) : term144.
Proof. exact (@lem1703803 e h1 h2 (@lem1587920)). Qed.
Lemma lem1703805 (e : real) (h1 : term139 e) (h2 : term37 e) : False.
Proof. exact (@lem1703804 e h1 h2 (@lem1632194)). Qed.
Lemma lem1703806 (e : real) (h1 : term139 e) (h2 : term37 e) : (term139 e) = False.
Proof. exact (prop_ext (fun h3 : term139 e => @lem1703805 e h1 h2) (fun h3 : False => @lem1701259 e h1)). Qed.
Lemma lem1703807 (e : real) (h1 : term139 e) (h2 : term37 e) : False.
Proof. exact (EQ_MP (@lem1703806 e h1 h2) (@lem1701259 e h1)). Qed.
Lemma lem1703808 (e : real) (h1 : term37 e) : term138 e.
Proof. exact (fun h0 : term139 e => @lem1703807 e h0 h1). Qed.
Lemma lem1703809 (e : real) (h1 : term37 e) : term128 e.
Proof. exact (EQ_MP (@lem1701258 e) (@lem1703808 e h1)). Qed.
Lemma lem1703810 (e : real) (h1 : term37 e) : term136 e.
Proof. exact (@lem1701254 e (@lem1703809 e h1)). Qed.
Lemma lem1703811 (e : real) (h1 : term37 e) : term40 e.
Proof. exact (@lem1703810 e h1 (@lem1700460 e)). Qed.
Lemma lem1703812 (e : real) : term344 e.
Proof. exact (fun h0 : term37 e => @lem1703811 e h0). Qed.
Lemma lem1703813 (e : real) : term345 e.
Proof. exact (conj (@lem1703812 e) (@lem1701226 e)). Qed.
Lemma lem1703814 (e : real) : (term345 e) = ((term37 e) = (term40 e)).
Proof. exact (@lem32 (term37 e) (term40 e)). Qed.
Lemma lem1703815 (e : real) : (term37 e) = (term40 e).
Proof. exact (EQ_MP (@lem1703814 e) (@lem1703813 e)). Qed.
Lemma lem1703820 : term346.
Proof. exact (fun e : real => @lem1703815 e). Qed.
