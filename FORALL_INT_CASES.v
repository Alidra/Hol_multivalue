Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_INT_CASES_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
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
Lemma lem2295412 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2295413 : term1 = term2.
Proof. exact (@lem2295412 term1). Qed.
Lemma lem2295414 : term2 = term1.
Proof. exact (SYM (@lem2295413)). Qed.
Lemma lem2295415 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2295418 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2295419 : term5.
Proof. exact (fun h0 : term4 => @lem2295418 h0). Qed.
Lemma lem2295420 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2295421 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2295422 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2295420 h2 (@lem2295421 h1)). Qed.
Lemma lem2295423 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem2295422 h1 h0). Qed.
Lemma lem2295424 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2295425 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2295423 h1 (@lem2295424 h2)). Qed.
Lemma lem2295426 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem2295425 h0 h1). Qed.
Lemma lem2295427 : term7.
Proof. exact (fun h0 : term5 => @lem2295426 h0). Qed.
Lemma lem2295430 : term5.
Proof. exact (@lem2295427 (@lem2295419)). Qed.
Lemma lem2295452 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2295453 : term8 = term9.
Proof. exact (@lem2295452 term10). Qed.
Lemma lem2295512 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem2295519 : term4 = term12.
Proof. exact (MK_COMB (@lem2295512) (@lem2295453)). Qed.
Lemma lem2295520 (x : int) (n : nat) : (x = (term13 n)) = (x = (term13 n)).
Proof. exact (eq_refl (x = (term13 n))). Qed.
Lemma lem2295521 (x : int) : (term14 x) = (term14 x).
Proof. exact (fun_ext (fun n : nat => @lem2295520 x n)). Qed.
Lemma lem2295522 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295523 (x : int) : (term15 x) = (term15 x).
Proof. exact (MK_COMB (@lem2295522) (@lem2295521 x)). Qed.
Lemma lem2295524 (x : int) (n : nat) : (x = (int_of_num n)) = (x = (int_of_num n)).
Proof. exact (eq_refl (x = (int_of_num n))). Qed.
Lemma lem2295525 (x : int) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun n : nat => @lem2295524 x n)). Qed.
Lemma lem2295526 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295527 (x : int) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem2295526) (@lem2295525 x)). Qed.
Lemma lem2295528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295529 (x : int) : (term18 x) = (term18 x).
Proof. exact (MK_COMB (@lem2295528) (@lem2295527 x)). Qed.
Lemma lem2295530 (x : int) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem2295529 x) (@lem2295523 x)). Qed.
Lemma lem2295531 : term20 = term20.
Proof. exact (fun_ext (fun x : int => @lem2295530 x)). Qed.
Lemma lem2295532 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2295533 : term10 = term10.
Proof. exact (MK_COMB (@lem2295532) (@lem2295531)). Qed.
Lemma lem2295534 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2295535 : term9 = term9.
Proof. exact (MK_COMB (@lem2295534) (@lem2295533)). Qed.
Lemma lem2295536 (P : int -> Prop) (n : nat) : (term21 P n) = (term21 P n).
Proof. exact (eq_refl (term21 P n)). Qed.
Lemma lem2295537 (P : int -> Prop) : (term22 P) = (term22 P).
Proof. exact (fun_ext (fun n : nat => @lem2295536 P n)). Qed.
Lemma lem2295538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2295539 (P : int -> Prop) : (term23 P) = (term23 P).
Proof. exact (MK_COMB (@lem2295538) (@lem2295537 P)). Qed.
Lemma lem2295540 (P : int -> Prop) (n : nat) : (term24 P n) = (term24 P n).
Proof. exact (eq_refl (term24 P n)). Qed.
Lemma lem2295541 (P : int -> Prop) : (term25 P) = (term25 P).
Proof. exact (fun_ext (fun n : nat => @lem2295540 P n)). Qed.
Lemma lem2295542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2295543 (P : int -> Prop) : (term26 P) = (term26 P).
Proof. exact (MK_COMB (@lem2295542) (@lem2295541 P)). Qed.
Lemma lem2295544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2295545 (P : int -> Prop) : (term27 P) = (term27 P).
Proof. exact (MK_COMB (@lem2295544) (@lem2295543 P)). Qed.
Lemma lem2295546 (P : int -> Prop) : (term28 P) = (term28 P).
Proof. exact (MK_COMB (@lem2295545 P) (@lem2295539 P)). Qed.
Lemma lem2295547 (P : int -> Prop) (x : int) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2295548 (P : int -> Prop) : (term29 P) = (term29 P).
Proof. exact (fun_ext (fun x : int => @lem2295547 P x)). Qed.
Lemma lem2295549 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2295550 (P : int -> Prop) : (term30 P) = (term30 P).
Proof. exact (MK_COMB (@lem2295549) (@lem2295548 P)). Qed.
Lemma lem2295551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295552 (P : int -> Prop) : (term31 P) = (term31 P).
Proof. exact (MK_COMB (@lem2295551) (@lem2295550 P)). Qed.
Lemma lem2295553 (P : int -> Prop) : ((term30 P) = (term28 P)) = ((term30 P) = (term28 P)).
Proof. exact (MK_COMB (@lem2295552 P) (@lem2295546 P)). Qed.
Lemma lem2295554 : term32 = term32.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295553 P)). Qed.
Lemma lem2295555 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2295556 : term1 = term1.
Proof. exact (MK_COMB (@lem2295555) (@lem2295554)). Qed.
Lemma lem2295557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2295558 : term3 = term3.
Proof. exact (MK_COMB (@lem2295557) (@lem2295556)). Qed.
Lemma lem2295559 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2295560 : term11 = term11.
Proof. exact (MK_COMB (@lem2295559) (@lem2295558)). Qed.
Lemma lem2295561 : term12 = term12.
Proof. exact (MK_COMB (@lem2295560) (@lem2295535)). Qed.
Lemma lem2295612 : term4 = term12.
Proof. exact (TRANS (@lem2295519) (@lem2295561)). Qed.
Lemma lem2295613 : term12 = term4.
Proof. exact (SYM (@lem2295612)). Qed.
Lemma lem2295614 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2295615 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem2295617 (P : int -> Prop) (x : int) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2295618 (P : int -> Prop) : (term33 P) = (term34 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2295619 (P : int -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem2295618 (term29 P)). Qed.
Lemma lem2295620 (P : int -> Prop) (x : int) : (term37 P x) = (P x).
Proof. exact (eq_refl (term37 P x)). Qed.
Lemma lem2295621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2295623 (P : int -> Prop) (x : int) : (term38 P x) = (term39 P x).
Proof. exact (MK_COMB (@lem2295621) (@lem2295620 P x)). Qed.
Lemma lem2295624 (P : int -> Prop) : (term40 P) = (term41 P).
Proof. exact (fun_ext (fun x : int => @lem2295623 P x)). Qed.
Lemma lem2295625 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2295626 (P : int -> Prop) : (term36 P) = (term34 P).
Proof. exact (MK_COMB (@lem2295625) (@lem2295624 P)). Qed.
Lemma lem2295627 (P : int -> Prop) : (term35 P) = (term34 P).
Proof. exact (TRANS (@lem2295619 P) (@lem2295626 P)). Qed.
Lemma lem2295628 (P : int -> Prop) : (term29 P) = (term29 P).
Proof. exact (fun_ext (fun x : int => @lem2295617 P x)). Qed.
Lemma lem2295629 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2295630 (P : int -> Prop) : (term30 P) = (term30 P).
Proof. exact (MK_COMB (@lem2295629) (@lem2295628 P)). Qed.
Lemma lem2295632 (P : int -> Prop) (n : nat) : (term24 P n) = (term24 P n).
Proof. exact (eq_refl (term24 P n)). Qed.
Lemma lem2295633 (P : nat -> Prop) : (term42 P) = (term43 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem2295634 (P : int -> Prop) : (term44 P) = (term45 P).
Proof. exact (@lem2295633 (term25 P)). Qed.
Lemma lem2295635 (P : int -> Prop) (n : nat) : (term46 P n) = (term24 P n).
Proof. exact (eq_refl (term46 P n)). Qed.
Lemma lem2295636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2295638 (P : int -> Prop) (n : nat) : (term47 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem2295636) (@lem2295635 P n)). Qed.
Lemma lem2295639 (P : int -> Prop) : (term49 P) = (term50 P).
Proof. exact (fun_ext (fun n : nat => @lem2295638 P n)). Qed.
Lemma lem2295640 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295641 (P : int -> Prop) : (term45 P) = (term51 P).
Proof. exact (MK_COMB (@lem2295640) (@lem2295639 P)). Qed.
Lemma lem2295642 (P : int -> Prop) : (term44 P) = (term51 P).
Proof. exact (TRANS (@lem2295634 P) (@lem2295641 P)). Qed.
Lemma lem2295643 (P : int -> Prop) : (term25 P) = (term25 P).
Proof. exact (fun_ext (fun n : nat => @lem2295632 P n)). Qed.
Lemma lem2295644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2295645 (P : int -> Prop) : (term26 P) = (term26 P).
Proof. exact (MK_COMB (@lem2295644) (@lem2295643 P)). Qed.
Lemma lem2295647 (P : int -> Prop) (n : nat) : (term21 P n) = (term21 P n).
Proof. exact (eq_refl (term21 P n)). Qed.
Lemma lem2295648 (P : nat -> Prop) : (term42 P) = (term43 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem2295649 (P : int -> Prop) : (term52 P) = (term53 P).
Proof. exact (@lem2295648 (term22 P)). Qed.
Lemma lem2295650 (P : int -> Prop) (n : nat) : (term54 P n) = (term21 P n).
Proof. exact (eq_refl (term54 P n)). Qed.
Lemma lem2295651 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2295653 (P : int -> Prop) (n : nat) : (term55 P n) = (term56 P n).
Proof. exact (MK_COMB (@lem2295651) (@lem2295650 P n)). Qed.
Lemma lem2295654 (P : int -> Prop) : (term57 P) = (term58 P).
Proof. exact (fun_ext (fun n : nat => @lem2295653 P n)). Qed.
Lemma lem2295655 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295656 (P : int -> Prop) : (term53 P) = (term59 P).
Proof. exact (MK_COMB (@lem2295655) (@lem2295654 P)). Qed.
Lemma lem2295657 (P : int -> Prop) : (term52 P) = (term59 P).
Proof. exact (TRANS (@lem2295649 P) (@lem2295656 P)). Qed.
Lemma lem2295658 (P : int -> Prop) : (term22 P) = (term22 P).
Proof. exact (fun_ext (fun n : nat => @lem2295647 P n)). Qed.
Lemma lem2295659 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2295660 (P : int -> Prop) : (term23 P) = (term23 P).
Proof. exact (MK_COMB (@lem2295659) (@lem2295658 P)). Qed.
Lemma lem2295661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295662 (P : int -> Prop) : (term60 P) = (term61 P).
Proof. exact (MK_COMB (@lem2295661) (@lem2295642 P)). Qed.
Lemma lem2295663 (P : int -> Prop) : (term62 P) = (term63 P).
Proof. exact (MK_COMB (@lem2295662 P) (@lem2295657 P)). Qed.
Lemma lem2295664 (P : int -> Prop) : (term64 P) = (term62 P).
Proof. exact (@lem17045 (term26 P) (term23 P)). Qed.
Lemma lem2295665 (P : int -> Prop) : (term64 P) = (term63 P).
Proof. exact (TRANS (@lem2295664 P) (@lem2295663 P)). Qed.
Lemma lem2295666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2295667 (P : int -> Prop) : (term27 P) = (term27 P).
Proof. exact (MK_COMB (@lem2295666) (@lem2295645 P)). Qed.
Lemma lem2295668 (P : int -> Prop) : (term28 P) = (term28 P).
Proof. exact (MK_COMB (@lem2295667 P) (@lem2295660 P)). Qed.
Lemma lem2295669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2295670 (P : int -> Prop) : (term65 P) = (term66 P).
Proof. exact (MK_COMB (@lem2295669) (@lem2295627 P)). Qed.
Lemma lem2295671 (P : int -> Prop) : (term67 P) = (term68 P).
Proof. exact (MK_COMB (@lem2295670 P) (@lem2295668 P)). Qed.
Lemma lem2295672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2295673 (P : int -> Prop) : (term69 P) = (term69 P).
Proof. exact (MK_COMB (@lem2295672) (@lem2295630 P)). Qed.
Lemma lem2295674 (P : int -> Prop) : (term70 P) = (term71 P).
Proof. exact (MK_COMB (@lem2295673 P) (@lem2295665 P)). Qed.
Lemma lem2295675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295676 (P : int -> Prop) : (term72 P) = (term73 P).
Proof. exact (MK_COMB (@lem2295675) (@lem2295674 P)). Qed.
Lemma lem2295677 (P : int -> Prop) : (term74 P) = (term75 P).
Proof. exact (MK_COMB (@lem2295676 P) (@lem2295671 P)). Qed.
Lemma lem2295678 (P : int -> Prop) : (term76 P) = (term74 P).
Proof. exact (@lem17646 (term30 P) (term28 P)). Qed.
Lemma lem2295679 (P : int -> Prop) : (term76 P) = (term75 P).
Proof. exact (TRANS (@lem2295678 P) (@lem2295677 P)). Qed.
Lemma lem2295680 (P : type925) : (term77 P) = (term78 P).
Proof. exact (@lem18392 (int -> Prop) P). Qed.
Lemma lem2295681 : term3 = term79.
Proof. exact (@lem2295680 term32). Qed.
Lemma lem2295682 (P : int -> Prop) : (term80 P) = ((term30 P) = (term28 P)).
Proof. exact (eq_refl (term80 P)). Qed.
Lemma lem2295683 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2295684 (P : int -> Prop) : (term81 P) = (term76 P).
Proof. exact (MK_COMB (@lem2295683) (@lem2295682 P)). Qed.
Lemma lem2295685 (P : int -> Prop) : (term81 P) = (term75 P).
Proof. exact (TRANS (@lem2295684 P) (@lem2295679 P)). Qed.
Lemma lem2295686 : term82 = term83.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295685 P)). Qed.
Lemma lem2295687 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295688 : term79 = term84.
Proof. exact (MK_COMB (@lem2295687) (@lem2295686)). Qed.
Lemma lem2295689 : term3 = term84.
Proof. exact (TRANS (@lem2295681) (@lem2295688)). Qed.
Lemma lem2295691 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem2295692 (P : type925) (Q : type925) : (term87 P Q) = (term88 P Q).
Proof. exact (@lem2295691 (int -> Prop) P Q). Qed.
Lemma lem2295693 : term89 = term90.
Proof. exact (@lem2295692 term91 term92). Qed.
Lemma lem2295694 (P : int -> Prop) : (term93 P) = (term71 P).
Proof. exact (eq_refl (term93 P)). Qed.
Lemma lem2295695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295696 (P : int -> Prop) : (term94 P) = (term73 P).
Proof. exact (MK_COMB (@lem2295695) (@lem2295694 P)). Qed.
Lemma lem2295697 (P : int -> Prop) : (term95 P) = (term68 P).
Proof. exact (eq_refl (term95 P)). Qed.
Lemma lem2295698 (P : int -> Prop) : (term96 P) = (term75 P).
Proof. exact (MK_COMB (@lem2295696 P) (@lem2295697 P)). Qed.
Lemma lem2295699 : term97 = term83.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295698 P)). Qed.
Lemma lem2295700 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295701 : term89 = term84.
Proof. exact (MK_COMB (@lem2295700) (@lem2295699)). Qed.
Lemma lem2295702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295703 : term98 = term99.
Proof. exact (MK_COMB (@lem2295702) (@lem2295701)). Qed.
Lemma lem2295704 (P : int -> Prop) : (term93 P) = (term71 P).
Proof. exact (eq_refl (term93 P)). Qed.
Lemma lem2295705 : term100 = term91.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295704 P)). Qed.
Lemma lem2295706 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295707 : term101 = term102.
Proof. exact (MK_COMB (@lem2295706) (@lem2295705)). Qed.
Lemma lem2295708 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295709 : term103 = term104.
Proof. exact (MK_COMB (@lem2295708) (@lem2295707)). Qed.
Lemma lem2295710 (P : int -> Prop) : (term95 P) = (term68 P).
Proof. exact (eq_refl (term95 P)). Qed.
Lemma lem2295711 : term105 = term92.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295710 P)). Qed.
Lemma lem2295712 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295713 : term106 = term107.
Proof. exact (MK_COMB (@lem2295712) (@lem2295711)). Qed.
Lemma lem2295714 : term90 = term108.
Proof. exact (MK_COMB (@lem2295709) (@lem2295713)). Qed.
Lemma lem2295715 : (term89 = term90) = (term84 = term108).
Proof. exact (MK_COMB (@lem2295703) (@lem2295714)). Qed.
Lemma lem2295716 : term84 = term108.
Proof. exact (EQ_MP (@lem2295715) (@lem2295693)). Qed.
Lemma lem2295838 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term86 A P Q) = (term85 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2295839 (P : nat -> Prop) (Q : nat -> Prop) : (term109 P Q) = (term110 P Q).
Proof. exact (@lem2295838 nat P Q). Qed.
Lemma lem2295840 (P : int -> Prop) : (term111 P) = (term112 P).
Proof. exact (@lem2295839 (term50 P) (term58 P)). Qed.
Lemma lem2295841 (P : int -> Prop) (n : nat) : (term113 P n) = (term48 P n).
Proof. exact (eq_refl (term113 P n)). Qed.
Lemma lem2295842 (P : int -> Prop) : (term114 P) = (term50 P).
Proof. exact (fun_ext (fun n : nat => @lem2295841 P n)). Qed.
Lemma lem2295843 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295844 (P : int -> Prop) : (term115 P) = (term51 P).
Proof. exact (MK_COMB (@lem2295843) (@lem2295842 P)). Qed.
Lemma lem2295845 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295846 (P : int -> Prop) : (term116 P) = (term61 P).
Proof. exact (MK_COMB (@lem2295845) (@lem2295844 P)). Qed.
Lemma lem2295847 (P : int -> Prop) (n : nat) : (term117 P n) = (term56 P n).
Proof. exact (eq_refl (term117 P n)). Qed.
Lemma lem2295848 (P : int -> Prop) : (term118 P) = (term58 P).
Proof. exact (fun_ext (fun n : nat => @lem2295847 P n)). Qed.
Lemma lem2295849 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295850 (P : int -> Prop) : (term119 P) = (term59 P).
Proof. exact (MK_COMB (@lem2295849) (@lem2295848 P)). Qed.
Lemma lem2295851 (P : int -> Prop) : (term111 P) = (term63 P).
Proof. exact (MK_COMB (@lem2295846 P) (@lem2295850 P)). Qed.
Lemma lem2295852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295853 (P : int -> Prop) : (term120 P) = (term121 P).
Proof. exact (MK_COMB (@lem2295852) (@lem2295851 P)). Qed.
Lemma lem2295854 (P : int -> Prop) (n : nat) : (term113 P n) = (term48 P n).
Proof. exact (eq_refl (term113 P n)). Qed.
Lemma lem2295855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295856 (P : int -> Prop) (n : nat) : (term122 P n) = (term123 P n).
Proof. exact (MK_COMB (@lem2295855) (@lem2295854 P n)). Qed.
Lemma lem2295857 (P : int -> Prop) (n : nat) : (term117 P n) = (term56 P n).
Proof. exact (eq_refl (term117 P n)). Qed.
Lemma lem2295858 (P : int -> Prop) (n : nat) : (term124 P n) = (term125 P n).
Proof. exact (MK_COMB (@lem2295856 P n) (@lem2295857 P n)). Qed.
Lemma lem2295859 (P : int -> Prop) : (term126 P) = (term127 P).
Proof. exact (fun_ext (fun n : nat => @lem2295858 P n)). Qed.
Lemma lem2295860 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295861 (P : int -> Prop) : (term112 P) = (term128 P).
Proof. exact (MK_COMB (@lem2295860) (@lem2295859 P)). Qed.
Lemma lem2295862 (P : int -> Prop) : ((term111 P) = (term112 P)) = ((term63 P) = (term128 P)).
Proof. exact (MK_COMB (@lem2295853 P) (@lem2295861 P)). Qed.
Lemma lem2295863 (P : int -> Prop) : (term63 P) = (term128 P).
Proof. exact (EQ_MP (@lem2295862 P) (@lem2295840 P)). Qed.
Lemma lem2295864 (P : int -> Prop) : (term69 P) = (term69 P).
Proof. exact (eq_refl (term69 P)). Qed.
Lemma lem2295865 (P : int -> Prop) : (term71 P) = (term129 P).
Proof. exact (MK_COMB (@lem2295864 P) (@lem2295863 P)). Qed.
Lemma lem2295867 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2295868 (P : Prop) (Q : nat -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem2295867 nat P Q). Qed.
Lemma lem2295869 (P : int -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem2295868 (term30 P) (term127 P)). Qed.
Lemma lem2295870 (P : int -> Prop) (n : nat) : (term136 P n) = (term125 P n).
Proof. exact (eq_refl (term136 P n)). Qed.
Lemma lem2295871 (P : int -> Prop) : (term137 P) = (term127 P).
Proof. exact (fun_ext (fun n : nat => @lem2295870 P n)). Qed.
Lemma lem2295872 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295873 (P : int -> Prop) : (term138 P) = (term128 P).
Proof. exact (MK_COMB (@lem2295872) (@lem2295871 P)). Qed.
Lemma lem2295874 (P : int -> Prop) : (term69 P) = (term69 P).
Proof. exact (eq_refl (term69 P)). Qed.
Lemma lem2295875 (P : int -> Prop) : (term134 P) = (term129 P).
Proof. exact (MK_COMB (@lem2295874 P) (@lem2295873 P)). Qed.
Lemma lem2295876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295877 (P : int -> Prop) : (term139 P) = (term140 P).
Proof. exact (MK_COMB (@lem2295876) (@lem2295875 P)). Qed.
Lemma lem2295878 (P : int -> Prop) (n : nat) : (term136 P n) = (term125 P n).
Proof. exact (eq_refl (term136 P n)). Qed.
Lemma lem2295879 (P : int -> Prop) : (term69 P) = (term69 P).
Proof. exact (eq_refl (term69 P)). Qed.
Lemma lem2295880 (P : int -> Prop) (n : nat) : (term141 P n) = (term142 P n).
Proof. exact (MK_COMB (@lem2295879 P) (@lem2295878 P n)). Qed.
Lemma lem2295881 (P : int -> Prop) : (term143 P) = (term144 P).
Proof. exact (fun_ext (fun n : nat => @lem2295880 P n)). Qed.
Lemma lem2295882 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295883 (P : int -> Prop) : (term135 P) = (term145 P).
Proof. exact (MK_COMB (@lem2295882) (@lem2295881 P)). Qed.
Lemma lem2295884 (P : int -> Prop) : ((term134 P) = (term135 P)) = ((term129 P) = (term145 P)).
Proof. exact (MK_COMB (@lem2295877 P) (@lem2295883 P)). Qed.
Lemma lem2295885 (P : int -> Prop) : (term129 P) = (term145 P).
Proof. exact (EQ_MP (@lem2295884 P) (@lem2295869 P)). Qed.
Lemma lem2295886 (P : int -> Prop) : (term71 P) = (term145 P).
Proof. exact (TRANS (@lem2295865 P) (@lem2295885 P)). Qed.
Lemma lem2295887 : term91 = term146.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295886 P)). Qed.
Lemma lem2295888 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295889 : term102 = term147.
Proof. exact (MK_COMB (@lem2295888) (@lem2295887)). Qed.
Lemma lem2295890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295891 : term104 = term148.
Proof. exact (MK_COMB (@lem2295890) (@lem2295889)). Qed.
Lemma lem2295893 {A : Type'} (P : A -> Prop) (Q : Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem2295894 (P : int -> Prop) (Q : Prop) : (term151 P Q) = (term152 P Q).
Proof. exact (@lem2295893 int P Q). Qed.
Lemma lem2295895 (P : int -> Prop) : (term153 P) = (term154 P).
Proof. exact (@lem2295894 (term41 P) (term28 P)). Qed.
Lemma lem2295896 (P : int -> Prop) (x : int) : (term155 P x) = (term39 P x).
Proof. exact (eq_refl (term155 P x)). Qed.
Lemma lem2295897 (P : int -> Prop) : (term156 P) = (term41 P).
Proof. exact (fun_ext (fun x : int => @lem2295896 P x)). Qed.
Lemma lem2295898 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2295899 (P : int -> Prop) : (term157 P) = (term34 P).
Proof. exact (MK_COMB (@lem2295898) (@lem2295897 P)). Qed.
Lemma lem2295900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2295901 (P : int -> Prop) : (term158 P) = (term66 P).
Proof. exact (MK_COMB (@lem2295900) (@lem2295899 P)). Qed.
Lemma lem2295902 (P : int -> Prop) : (term28 P) = (term28 P).
Proof. exact (eq_refl (term28 P)). Qed.
Lemma lem2295903 (P : int -> Prop) : (term153 P) = (term68 P).
Proof. exact (MK_COMB (@lem2295901 P) (@lem2295902 P)). Qed.
Lemma lem2295904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295905 (P : int -> Prop) : (term159 P) = (term160 P).
Proof. exact (MK_COMB (@lem2295904) (@lem2295903 P)). Qed.
Lemma lem2295906 (P : int -> Prop) (x : int) : (term155 P x) = (term39 P x).
Proof. exact (eq_refl (term155 P x)). Qed.
Lemma lem2295907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2295908 (P : int -> Prop) (x : int) : (term161 P x) = (term162 P x).
Proof. exact (MK_COMB (@lem2295907) (@lem2295906 P x)). Qed.
Lemma lem2295909 (P : int -> Prop) : (term28 P) = (term28 P).
Proof. exact (eq_refl (term28 P)). Qed.
Lemma lem2295910 (x : int) (P : int -> Prop) : (term163 x P) = (term164 x P).
Proof. exact (MK_COMB (@lem2295908 P x) (@lem2295909 P)). Qed.
Lemma lem2295911 (P : int -> Prop) : (term165 P) = (term166 P).
Proof. exact (fun_ext (fun x : int => @lem2295910 x P)). Qed.
Lemma lem2295912 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2295913 (P : int -> Prop) : (term154 P) = (term167 P).
Proof. exact (MK_COMB (@lem2295912) (@lem2295911 P)). Qed.
Lemma lem2295914 (P : int -> Prop) : ((term153 P) = (term154 P)) = ((term68 P) = (term167 P)).
Proof. exact (MK_COMB (@lem2295905 P) (@lem2295913 P)). Qed.
Lemma lem2295915 (P : int -> Prop) : (term68 P) = (term167 P).
Proof. exact (EQ_MP (@lem2295914 P) (@lem2295895 P)). Qed.
Lemma lem2295916 : term92 = term168.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295915 P)). Qed.
Lemma lem2295917 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295918 : term107 = term169.
Proof. exact (MK_COMB (@lem2295917) (@lem2295916)). Qed.
Lemma lem2295919 : term108 = term170.
Proof. exact (MK_COMB (@lem2295891) (@lem2295918)). Qed.
Lemma lem2295921 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term86 A P Q) = (term85 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2295922 (P : type925) (Q : type925) : (term88 P Q) = (term87 P Q).
Proof. exact (@lem2295921 (int -> Prop) P Q). Qed.
Lemma lem2295923 : term171 = term172.
Proof. exact (@lem2295922 term146 term168). Qed.
Lemma lem2295924 (P : int -> Prop) : (term173 P) = (term145 P).
Proof. exact (eq_refl (term173 P)). Qed.
Lemma lem2295925 : term174 = term146.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295924 P)). Qed.
Lemma lem2295926 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295927 : term175 = term147.
Proof. exact (MK_COMB (@lem2295926) (@lem2295925)). Qed.
Lemma lem2295928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295929 : term176 = term148.
Proof. exact (MK_COMB (@lem2295928) (@lem2295927)). Qed.
Lemma lem2295930 (P : int -> Prop) : (term177 P) = (term167 P).
Proof. exact (eq_refl (term177 P)). Qed.
Lemma lem2295931 : term178 = term168.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295930 P)). Qed.
Lemma lem2295932 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295933 : term179 = term169.
Proof. exact (MK_COMB (@lem2295932) (@lem2295931)). Qed.
Lemma lem2295934 : term171 = term170.
Proof. exact (MK_COMB (@lem2295929) (@lem2295933)). Qed.
Lemma lem2295935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295936 : term180 = term181.
Proof. exact (MK_COMB (@lem2295935) (@lem2295934)). Qed.
Lemma lem2295937 (P : int -> Prop) : (term173 P) = (term145 P).
Proof. exact (eq_refl (term173 P)). Qed.
Lemma lem2295938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295939 (P : int -> Prop) : (term182 P) = (term183 P).
Proof. exact (MK_COMB (@lem2295938) (@lem2295937 P)). Qed.
Lemma lem2295940 (P : int -> Prop) : (term177 P) = (term167 P).
Proof. exact (eq_refl (term177 P)). Qed.
Lemma lem2295941 (P : int -> Prop) : (term184 P) = (term185 P).
Proof. exact (MK_COMB (@lem2295939 P) (@lem2295940 P)). Qed.
Lemma lem2295942 : term186 = term187.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295941 P)). Qed.
Lemma lem2295943 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295944 : term172 = term188.
Proof. exact (MK_COMB (@lem2295943) (@lem2295942)). Qed.
Lemma lem2295945 : (term171 = term172) = (term170 = term188).
Proof. exact (MK_COMB (@lem2295936) (@lem2295944)). Qed.
Lemma lem2295946 : term170 = term188.
Proof. exact (EQ_MP (@lem2295945) (@lem2295923)). Qed.
Lemma lem2295950 {A : Type'} (P : A -> Prop) (Q : Prop) : (term189 A P Q) = (term190 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem2295951 (P : nat -> Prop) (Q : Prop) : (term191 P Q) = (term192 P Q).
Proof. exact (@lem2295950 nat P Q). Qed.
Lemma lem2295952 (P : int -> Prop) : (term193 P) = (term194 P).
Proof. exact (@lem2295951 (term144 P) (term167 P)). Qed.
Lemma lem2295953 (P : int -> Prop) (n : nat) : (term195 P n) = (term142 P n).
Proof. exact (eq_refl (term195 P n)). Qed.
Lemma lem2295954 (P : int -> Prop) : (term196 P) = (term144 P).
Proof. exact (fun_ext (fun n : nat => @lem2295953 P n)). Qed.
Lemma lem2295955 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295956 (P : int -> Prop) : (term197 P) = (term145 P).
Proof. exact (MK_COMB (@lem2295955) (@lem2295954 P)). Qed.
Lemma lem2295957 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295958 (P : int -> Prop) : (term198 P) = (term183 P).
Proof. exact (MK_COMB (@lem2295957) (@lem2295956 P)). Qed.
Lemma lem2295959 (P : int -> Prop) : (term167 P) = (term167 P).
Proof. exact (eq_refl (term167 P)). Qed.
Lemma lem2295960 (P : int -> Prop) : (term193 P) = (term185 P).
Proof. exact (MK_COMB (@lem2295958 P) (@lem2295959 P)). Qed.
Lemma lem2295961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295962 (P : int -> Prop) : (term199 P) = (term200 P).
Proof. exact (MK_COMB (@lem2295961) (@lem2295960 P)). Qed.
Lemma lem2295963 (P : int -> Prop) (n : nat) : (term195 P n) = (term142 P n).
Proof. exact (eq_refl (term195 P n)). Qed.
Lemma lem2295964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295965 (P : int -> Prop) (n : nat) : (term201 P n) = (term202 P n).
Proof. exact (MK_COMB (@lem2295964) (@lem2295963 P n)). Qed.
Lemma lem2295966 (P : int -> Prop) : (term167 P) = (term167 P).
Proof. exact (eq_refl (term167 P)). Qed.
Lemma lem2295967 (n : nat) (P : int -> Prop) : (term203 n P) = (term204 n P).
Proof. exact (MK_COMB (@lem2295965 P n) (@lem2295966 P)). Qed.
Lemma lem2295968 (P : int -> Prop) : (term205 P) = (term206 P).
Proof. exact (fun_ext (fun n : nat => @lem2295967 n P)). Qed.
Lemma lem2295969 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295970 (P : int -> Prop) : (term194 P) = (term207 P).
Proof. exact (MK_COMB (@lem2295969) (@lem2295968 P)). Qed.
Lemma lem2295971 (P : int -> Prop) : ((term193 P) = (term194 P)) = ((term185 P) = (term207 P)).
Proof. exact (MK_COMB (@lem2295962 P) (@lem2295970 P)). Qed.
Lemma lem2295972 (P : int -> Prop) : (term185 P) = (term207 P).
Proof. exact (EQ_MP (@lem2295971 P) (@lem2295952 P)). Qed.
Lemma lem2295974 {A : Type'} (P : Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2295975 (P : Prop) (Q : int -> Prop) : (term210 P Q) = (term211 P Q).
Proof. exact (@lem2295974 int P Q). Qed.
Lemma lem2295976 (n : nat) (P : int -> Prop) : (term212 n P) = (term213 n P).
Proof. exact (@lem2295975 (term142 P n) (term166 P)). Qed.
Lemma lem2295977 (x : int) (P : int -> Prop) : (term214 P x) = (term164 x P).
Proof. exact (eq_refl (term214 P x)). Qed.
Lemma lem2295978 (P : int -> Prop) : (term215 P) = (term166 P).
Proof. exact (fun_ext (fun x : int => @lem2295977 x P)). Qed.
Lemma lem2295979 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2295980 (P : int -> Prop) : (term216 P) = (term167 P).
Proof. exact (MK_COMB (@lem2295979) (@lem2295978 P)). Qed.
Lemma lem2295981 (P : int -> Prop) (n : nat) : (term202 P n) = (term202 P n).
Proof. exact (eq_refl (term202 P n)). Qed.
Lemma lem2295982 (n : nat) (P : int -> Prop) : (term212 n P) = (term204 n P).
Proof. exact (MK_COMB (@lem2295981 P n) (@lem2295980 P)). Qed.
Lemma lem2295983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295984 (n : nat) (P : int -> Prop) : (term217 n P) = (term218 n P).
Proof. exact (MK_COMB (@lem2295983) (@lem2295982 n P)). Qed.
Lemma lem2295985 (x : int) (P : int -> Prop) : (term214 P x) = (term164 x P).
Proof. exact (eq_refl (term214 P x)). Qed.
Lemma lem2295986 (P : int -> Prop) (n : nat) : (term202 P n) = (term202 P n).
Proof. exact (eq_refl (term202 P n)). Qed.
Lemma lem2295987 (n : nat) (x : int) (P : int -> Prop) : (term219 n P x) = (term220 n x P).
Proof. exact (MK_COMB (@lem2295986 P n) (@lem2295985 x P)). Qed.
Lemma lem2295988 (n : nat) (P : int -> Prop) : (term221 n P) = (term222 n P).
Proof. exact (fun_ext (fun x : int => @lem2295987 n x P)). Qed.
Lemma lem2295989 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2295990 (n : nat) (P : int -> Prop) : (term213 n P) = (term223 n P).
Proof. exact (MK_COMB (@lem2295989) (@lem2295988 n P)). Qed.
Lemma lem2295991 (n : nat) (P : int -> Prop) : ((term212 n P) = (term213 n P)) = ((term204 n P) = (term223 n P)).
Proof. exact (MK_COMB (@lem2295984 n P) (@lem2295990 n P)). Qed.
Lemma lem2295992 (n : nat) (P : int -> Prop) : (term204 n P) = (term223 n P).
Proof. exact (EQ_MP (@lem2295991 n P) (@lem2295976 n P)). Qed.
Lemma lem2295993 (P : int -> Prop) : (term206 P) = (term224 P).
Proof. exact (fun_ext (fun n : nat => @lem2295992 n P)). Qed.
Lemma lem2295994 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295995 (P : int -> Prop) : (term207 P) = (term225 P).
Proof. exact (MK_COMB (@lem2295994) (@lem2295993 P)). Qed.
Lemma lem2295996 (P : int -> Prop) : (term185 P) = (term225 P).
Proof. exact (TRANS (@lem2295972 P) (@lem2295995 P)). Qed.
Lemma lem2295997 : term187 = term226.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2295996 P)). Qed.
Lemma lem2295998 : (@ex (int -> Prop)) = (@ex (int -> Prop)).
Proof. exact (eq_refl (@ex (int -> Prop))). Qed.
Lemma lem2295999 : term188 = term227.
Proof. exact (MK_COMB (@lem2295998) (@lem2295997)). Qed.
Lemma lem2296000 : term170 = term227.
Proof. exact (TRANS (@lem2295946) (@lem2295999)). Qed.
Lemma lem2296001 : term108 = term227.
Proof. exact (TRANS (@lem2295919) (@lem2296000)). Qed.
Lemma lem2296002 : term84 = term227.
Proof. exact (TRANS (@lem2295716) (@lem2296001)). Qed.
Lemma lem2296003 : term3 = term227.
Proof. exact (TRANS (@lem2295689) (@lem2296002)). Qed.
Lemma lem2296004 (h1 : term3) : term227.
Proof. exact (EQ_MP (@lem2296003) (@lem2295614 h1)). Qed.
Lemma lem2296005 (x : int) (n : nat) : (x = (int_of_num n)) = (x = (int_of_num n)).
Proof. exact (eq_refl (x = (int_of_num n))). Qed.
Lemma lem2296006 (x : int) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun n : nat => @lem2296005 x n)). Qed.
Lemma lem2296007 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2296008 (x : int) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem2296007) (@lem2296006 x)). Qed.
Lemma lem2296009 (x : int) (n : nat) : (x = (term13 n)) = (x = (term13 n)).
Proof. exact (eq_refl (x = (term13 n))). Qed.
Lemma lem2296010 (x : int) : (term14 x) = (term14 x).
Proof. exact (fun_ext (fun n : nat => @lem2296009 x n)). Qed.
Lemma lem2296011 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2296012 (x : int) : (term15 x) = (term15 x).
Proof. exact (MK_COMB (@lem2296011) (@lem2296010 x)). Qed.
Lemma lem2296013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2296014 (x : int) : (term18 x) = (term18 x).
Proof. exact (MK_COMB (@lem2296013) (@lem2296008 x)). Qed.
Lemma lem2296015 (x : int) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem2296014 x) (@lem2296012 x)). Qed.
Lemma lem2296016 : term20 = term20.
Proof. exact (fun_ext (fun x : int => @lem2296015 x)). Qed.
Lemma lem2296017 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2296018 : term10 = term10.
Proof. exact (MK_COMB (@lem2296017) (@lem2296016)). Qed.
Lemma lem2296077 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term86 A P Q) = (term85 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2296078 (P : nat -> Prop) (Q : nat -> Prop) : (term109 P Q) = (term110 P Q).
Proof. exact (@lem2296077 nat P Q). Qed.
Lemma lem2296079 (x : int) : (term228 x) = (term229 x).
Proof. exact (@lem2296078 (term16 x) (term14 x)). Qed.
Lemma lem2296080 (x : int) (n : nat) : (term230 x n) = (x = (int_of_num n)).
Proof. exact (eq_refl (term230 x n)). Qed.
Lemma lem2296081 (x : int) : (term231 x) = (term16 x).
Proof. exact (fun_ext (fun n : nat => @lem2296080 x n)). Qed.
Lemma lem2296082 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2296083 (x : int) : (term232 x) = (term17 x).
Proof. exact (MK_COMB (@lem2296082) (@lem2296081 x)). Qed.
Lemma lem2296084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2296085 (x : int) : (term233 x) = (term18 x).
Proof. exact (MK_COMB (@lem2296084) (@lem2296083 x)). Qed.
Lemma lem2296086 (x : int) (n : nat) : (term234 x n) = (x = (term13 n)).
Proof. exact (eq_refl (term234 x n)). Qed.
Lemma lem2296087 (x : int) : (term235 x) = (term14 x).
Proof. exact (fun_ext (fun n : nat => @lem2296086 x n)). Qed.
Lemma lem2296088 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2296089 (x : int) : (term236 x) = (term15 x).
Proof. exact (MK_COMB (@lem2296088) (@lem2296087 x)). Qed.
Lemma lem2296090 (x : int) : (term228 x) = (term19 x).
Proof. exact (MK_COMB (@lem2296085 x) (@lem2296089 x)). Qed.
Lemma lem2296091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2296092 (x : int) : (term237 x) = (term238 x).
Proof. exact (MK_COMB (@lem2296091) (@lem2296090 x)). Qed.
Lemma lem2296093 (x : int) (n : nat) : (term230 x n) = (x = (int_of_num n)).
Proof. exact (eq_refl (term230 x n)). Qed.
Lemma lem2296094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2296095 (x : int) (n : nat) : (term239 x n) = (term240 x n).
Proof. exact (MK_COMB (@lem2296094) (@lem2296093 x n)). Qed.
Lemma lem2296096 (x : int) (n : nat) : (term234 x n) = (x = (term13 n)).
Proof. exact (eq_refl (term234 x n)). Qed.
Lemma lem2296097 (x : int) (n : nat) : (term241 x n) = (term242 x n).
Proof. exact (MK_COMB (@lem2296095 x n) (@lem2296096 x n)). Qed.
Lemma lem2296098 (x : int) : (term243 x) = (term244 x).
Proof. exact (fun_ext (fun n : nat => @lem2296097 x n)). Qed.
Lemma lem2296099 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2296100 (x : int) : (term229 x) = (term245 x).
Proof. exact (MK_COMB (@lem2296099) (@lem2296098 x)). Qed.
Lemma lem2296101 (x : int) : ((term228 x) = (term229 x)) = ((term19 x) = (term245 x)).
Proof. exact (MK_COMB (@lem2296092 x) (@lem2296100 x)). Qed.
Lemma lem2296102 (x : int) : (term19 x) = (term245 x).
Proof. exact (EQ_MP (@lem2296101 x) (@lem2296079 x)). Qed.
Lemma lem2296103 : term20 = term246.
Proof. exact (fun_ext (fun x : int => @lem2296102 x)). Qed.
Lemma lem2296104 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2296105 : term10 = term247.
Proof. exact (MK_COMB (@lem2296104) (@lem2296103)). Qed.
Lemma lem2296107 {A B : Type'} (P : type1413 A B) : (term248 A B P) = (term249 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem2296108 (P : type1552) : (term250 P) = (term251 P).
Proof. exact (@lem2296107 int nat P). Qed.
Lemma lem2296109 : term252 = term253.
Proof. exact (@lem2296108 term254). Qed.
Lemma lem2296110 (x : int) : (term255 x) = (term244 x).
Proof. exact (eq_refl (term255 x)). Qed.
Lemma lem2296111 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2296112 (x : int) (n : nat) : (term256 x n) = (term257 x n).
Proof. exact (MK_COMB (@lem2296110 x) (@lem2296111 n)). Qed.
Lemma lem2296113 (x : int) (n : nat) : (term257 x n) = (term242 x n).
Proof. exact (eq_refl (term257 x n)). Qed.
Lemma lem2296114 (x : int) (n : nat) : (term256 x n) = (term242 x n).
Proof. exact (TRANS (@lem2296112 x n) (@lem2296113 x n)). Qed.
Lemma lem2296115 (x : int) : (term258 x) = (term244 x).
Proof. exact (fun_ext (fun n : nat => @lem2296114 x n)). Qed.
Lemma lem2296116 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2296117 (x : int) : (term259 x) = (term245 x).
Proof. exact (MK_COMB (@lem2296116) (@lem2296115 x)). Qed.
Lemma lem2296118 : term260 = term246.
Proof. exact (fun_ext (fun x : int => @lem2296117 x)). Qed.
Lemma lem2296119 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2296120 : term252 = term247.
Proof. exact (MK_COMB (@lem2296119) (@lem2296118)). Qed.
Lemma lem2296121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2296122 : term261 = term262.
Proof. exact (MK_COMB (@lem2296121) (@lem2296120)). Qed.
Lemma lem2296123 (x : int) : (term255 x) = (term244 x).
Proof. exact (eq_refl (term255 x)). Qed.
Lemma lem2296124 (n : int -> nat) (x : int) : (n x) = (n x).
Proof. exact (eq_refl (n x)). Qed.
Lemma lem2296125 (n : int -> nat) (x : int) : (term263 n x) = (term264 n x).
Proof. exact (MK_COMB (@lem2296123 x) (@lem2296124 n x)). Qed.
Lemma lem2296126 (n : int -> nat) (x : int) : (term264 n x) = (term265 n x).
Proof. exact (eq_refl (term264 n x)). Qed.
Lemma lem2296127 (n : int -> nat) (x : int) : (term263 n x) = (term265 n x).
Proof. exact (TRANS (@lem2296125 n x) (@lem2296126 n x)). Qed.
Lemma lem2296128 (n : int -> nat) : (term266 n) = (term267 n).
Proof. exact (fun_ext (fun x : int => @lem2296127 n x)). Qed.
Lemma lem2296129 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2296130 (n : int -> nat) : (term268 n) = (term269 n).
Proof. exact (MK_COMB (@lem2296129) (@lem2296128 n)). Qed.
Lemma lem2296131 : term270 = term271.
Proof. exact (fun_ext (fun n : int -> nat => @lem2296130 n)). Qed.
Lemma lem2296132 : (@ex (int -> nat)) = (@ex (int -> nat)).
Proof. exact (eq_refl (@ex (int -> nat))). Qed.
Lemma lem2296133 : term253 = term272.
Proof. exact (MK_COMB (@lem2296132) (@lem2296131)). Qed.
Lemma lem2296134 : (term252 = term253) = (term247 = term272).
Proof. exact (MK_COMB (@lem2296122) (@lem2296133)). Qed.
Lemma lem2296135 : term247 = term272.
Proof. exact (EQ_MP (@lem2296134) (@lem2296109)). Qed.
Lemma lem2296137 : term10 = term272.
Proof. exact (TRANS (@lem2296105) (@lem2296135)). Qed.
Lemma lem2296138 : term10 = term272.
Proof. exact (TRANS (@lem2296018) (@lem2296137)). Qed.
Lemma lem2296139 (h1 : term10) : term272.
Proof. exact (EQ_MP (@lem2296138) (@lem2295615 h1)). Qed.
Lemma lem2296140 (n : int -> nat) (h1 : term269 n) : term269 n.
Proof. exact (h1). Qed.
Lemma lem2296141 (P : int -> Prop) (h1 : term225 P) : term225 P.
Proof. exact (h1). Qed.
Lemma lem2296142 (n' : nat) (P : int -> Prop) (h1 : term223 n' P) : term223 n' P.
Proof. exact (h1). Qed.
Lemma lem2296143 (n' : nat) (x : int) (P : int -> Prop) (h1 : term220 n' x P) : term220 n' x P.
Proof. exact (h1). Qed.
Lemma lem2296166 (n : int -> nat) (x : int) : (term265 n x) = (term265 n x).
Proof. exact (eq_refl (term265 n x)). Qed.
Lemma lem2296167 (n : int -> nat) : (term267 n) = (term267 n).
Proof. exact (fun_ext (fun x : int => @lem2296166 n x)). Qed.
Lemma lem2296168 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2296169 (n : int -> nat) : (term269 n) = (term269 n).
Proof. exact (MK_COMB (@lem2296168) (@lem2296167 n)). Qed.
Lemma lem2296170 (n : int -> nat) (h1 : term269 n) : term269 n.
Proof. exact (EQ_MP (@lem2296169 n) (@lem2296140 n h1)). Qed.
Lemma lem2296177 (P : int -> Prop) (n : nat) : (term21 P n) = (term21 P n).
Proof. exact (eq_refl (term21 P n)). Qed.
Lemma lem2296178 (P : int -> Prop) : (term22 P) = (term22 P).
Proof. exact (fun_ext (fun n : nat => @lem2296177 P n)). Qed.
Lemma lem2296179 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2296180 (P : int -> Prop) : (term23 P) = (term23 P).
Proof. exact (MK_COMB (@lem2296179) (@lem2296178 P)). Qed.
Lemma lem2296185 (P : int -> Prop) (n : nat) : (term24 P n) = (term24 P n).
Proof. exact (eq_refl (term24 P n)). Qed.
Lemma lem2296186 (P : int -> Prop) : (term25 P) = (term25 P).
Proof. exact (fun_ext (fun n : nat => @lem2296185 P n)). Qed.
Lemma lem2296187 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2296188 (P : int -> Prop) : (term26 P) = (term26 P).
Proof. exact (MK_COMB (@lem2296187) (@lem2296186 P)). Qed.
Lemma lem2296189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2296190 (P : int -> Prop) : (term27 P) = (term27 P).
Proof. exact (MK_COMB (@lem2296189) (@lem2296188 P)). Qed.
Lemma lem2296191 (P : int -> Prop) : (term28 P) = (term28 P).
Proof. exact (MK_COMB (@lem2296190 P) (@lem2296180 P)). Qed.
Lemma lem2296198 (P : int -> Prop) (x : int) : (term162 P x) = (term162 P x).
Proof. exact (eq_refl (term162 P x)). Qed.
Lemma lem2296199 (x : int) (P : int -> Prop) : (term164 x P) = (term164 x P).
Proof. exact (MK_COMB (@lem2296198 P x) (@lem2296191 P)). Qed.
Lemma lem2296218 (P : int -> Prop) (n' : nat) : (term125 P n') = (term125 P n').
Proof. exact (eq_refl (term125 P n')). Qed.
Lemma lem2296221 (P : int -> Prop) (x : int) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2296222 (P : int -> Prop) : (term29 P) = (term29 P).
Proof. exact (fun_ext (fun x : int => @lem2296221 P x)). Qed.
Lemma lem2296223 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2296224 (P : int -> Prop) : (term30 P) = (term30 P).
Proof. exact (MK_COMB (@lem2296223) (@lem2296222 P)). Qed.
Lemma lem2296225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2296226 (P : int -> Prop) : (term69 P) = (term69 P).
Proof. exact (MK_COMB (@lem2296225) (@lem2296224 P)). Qed.
Lemma lem2296227 (P : int -> Prop) (n' : nat) : (term142 P n') = (term142 P n').
Proof. exact (MK_COMB (@lem2296226 P) (@lem2296218 P n')). Qed.
Lemma lem2296228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2296229 (P : int -> Prop) (n' : nat) : (term202 P n') = (term202 P n').
Proof. exact (MK_COMB (@lem2296228) (@lem2296227 P n')). Qed.
Lemma lem2296230 (n' : nat) (x : int) (P : int -> Prop) : (term220 n' x P) = (term220 n' x P).
Proof. exact (MK_COMB (@lem2296229 P n') (@lem2296199 x P)). Qed.
Lemma lem2296231 (n' : nat) (x : int) (P : int -> Prop) (h1 : term220 n' x P) : term220 n' x P.
Proof. exact (EQ_MP (@lem2296230 n' x P) (@lem2296143 n' x P h1)). Qed.
Lemma lem2296232 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term142 P n'.
Proof. exact (h1). Qed.
Lemma lem2296233 (x : int) (P : int -> Prop) (h1 : term164 x P) : term164 x P.
Proof. exact (h1). Qed.
Lemma lem2296234 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term125 P n'.
Proof. exact (proj2 (@lem2296232 P n' h1)). Qed.
Lemma lem2296235 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term30 P.
Proof. exact (proj1 (@lem2296232 P n' h1)). Qed.
Lemma lem2296238 (x : int) (P : int -> Prop) (h1 : term164 x P) : term28 P.
Proof. exact (proj2 (@lem2296233 x P h1)). Qed.
Lemma lem2296240 (x : int) (P : int -> Prop) (h1 : term164 x P) : term23 P.
Proof. exact (proj2 (@lem2296238 x P h1)). Qed.
Lemma lem2296241 (x : int) (P : int -> Prop) (h1 : term164 x P) : term26 P.
Proof. exact (proj1 (@lem2296238 x P h1)). Qed.
Lemma lem2296256 (P : int -> Prop) (x : int) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2296257 (P : int -> Prop) : (term29 P) = (term29 P).
Proof. exact (fun_ext (fun x : int => @lem2296256 P x)). Qed.
Lemma lem2296258 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2296260 (P : int -> Prop) : (term30 P) = (term30 P).
Proof. exact (MK_COMB (@lem2296258) (@lem2296257 P)). Qed.
Lemma lem2296261 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term30 P.
Proof. exact (EQ_MP (@lem2296260 P) (@lem2296235 P n' h1)). Qed.
Lemma lem2296265 (P : int -> Prop) (n' : nat) (h1 : term48 P n') : term48 P n'.
Proof. exact (h1). Qed.
Lemma lem2296280 (P : int -> Prop) (x : int) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2296281 (P : int -> Prop) : (term29 P) = (term29 P).
Proof. exact (fun_ext (fun x : int => @lem2296280 P x)). Qed.
Lemma lem2296282 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2296284 (P : int -> Prop) : (term30 P) = (term30 P).
Proof. exact (MK_COMB (@lem2296282) (@lem2296281 P)). Qed.
Lemma lem2296285 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term30 P.
Proof. exact (EQ_MP (@lem2296284 P) (@lem2296235 P n' h1)). Qed.
Lemma lem2296289 (P : int -> Prop) (n' : nat) (h1 : term56 P n') : term56 P n'.
Proof. exact (h1). Qed.
Lemma lem2296297 (n : int -> nat) (x : int) : (term265 n x) = (term265 n x).
Proof. exact (eq_refl (term265 n x)). Qed.
Lemma lem2296298 (n : int -> nat) : (term267 n) = (term267 n).
Proof. exact (fun_ext (fun x : int => @lem2296297 n x)). Qed.
Lemma lem2296299 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2296301 (n : int -> nat) : (term269 n) = (term269 n).
Proof. exact (MK_COMB (@lem2296299) (@lem2296298 n)). Qed.
Lemma lem2296302 (n : int -> nat) (h1 : term269 n) : term269 n.
Proof. exact (EQ_MP (@lem2296301 n) (@lem2296170 n h1)). Qed.
Lemma lem2296308 (P : int -> Prop) (n : nat) : (term24 P n) = (term24 P n).
Proof. exact (eq_refl (term24 P n)). Qed.
Lemma lem2296309 (P : int -> Prop) : (term25 P) = (term25 P).
Proof. exact (fun_ext (fun n : nat => @lem2296308 P n)). Qed.
Lemma lem2296310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2296312 (P : int -> Prop) : (term26 P) = (term26 P).
Proof. exact (MK_COMB (@lem2296310) (@lem2296309 P)). Qed.
Lemma lem2296313 (x : int) (P : int -> Prop) (h1 : term164 x P) : term26 P.
Proof. exact (EQ_MP (@lem2296312 P) (@lem2296241 x P h1)). Qed.
Lemma lem2296315 (P : int -> Prop) (n : nat) : (term21 P n) = (term21 P n).
Proof. exact (eq_refl (term21 P n)). Qed.
Lemma lem2296316 (P : int -> Prop) : (term22 P) = (term22 P).
Proof. exact (fun_ext (fun n : nat => @lem2296315 P n)). Qed.
Lemma lem2296317 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2296319 (P : int -> Prop) : (term23 P) = (term23 P).
Proof. exact (MK_COMB (@lem2296317) (@lem2296316 P)). Qed.
Lemma lem2296320 (x : int) (P : int -> Prop) (h1 : term164 x P) : term23 P.
Proof. exact (EQ_MP (@lem2296319 P) (@lem2296240 x P h1)). Qed.
Lemma lem2296324 (_28866 : int) (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term37 P _28866.
Proof. exact (@lem2296261 P n' h1 _28866). Qed.
Lemma lem2296325 (P : int -> Prop) (_28866 : int) : (term37 P _28866) = (P _28866).
Proof. exact (eq_refl (term37 P _28866)). Qed.
Lemma lem2296330 (_28868 : int) (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term37 P _28868.
Proof. exact (@lem2296285 P n' h1 _28868). Qed.
Lemma lem2296331 (P : int -> Prop) (_28868 : int) : (term37 P _28868) = (P _28868).
Proof. exact (eq_refl (term37 P _28868)). Qed.
Lemma lem2296333 (_28869 : int) (n : int -> nat) (h1 : term269 n) : term273 n _28869.
Proof. exact (@lem2296302 n h1 _28869). Qed.
Lemma lem2296334 (n : int -> nat) (_28869 : int) : (term273 n _28869) = (term265 n _28869).
Proof. exact (eq_refl (term273 n _28869)). Qed.
Lemma lem2296336 (_28870 : nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term46 P _28870.
Proof. exact (@lem2296313 x P h1 _28870). Qed.
Lemma lem2296337 (P : int -> Prop) (_28870 : nat) : (term46 P _28870) = (term24 P _28870).
Proof. exact (eq_refl (term46 P _28870)). Qed.
Lemma lem2296339 (_28871 : nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term54 P _28871.
Proof. exact (@lem2296320 x P h1 _28871). Qed.
Lemma lem2296340 (P : int -> Prop) (_28871 : nat) : (term54 P _28871) = (term21 P _28871).
Proof. exact (eq_refl (term54 P _28871)). Qed.
Lemma lem2296351 (P : int -> Prop) (n' : nat) (h1 : term48 P n') : term48 P n'.
Proof. exact (h1). Qed.
Lemma lem2296361 (P : int -> Prop) (n' : nat) (h1 : term56 P n') : term56 P n'.
Proof. exact (h1). Qed.
Lemma lem2296367 (_28869 : int) (n : int -> nat) (h1 : term269 n) : term265 n _28869.
Proof. exact (EQ_MP (@lem2296334 n _28869) (@lem2296333 _28869 n h1)). Qed.
Lemma lem2296369 (x : int) (P : int -> Prop) (h1 : term164 x P) : term39 P x.
Proof. exact (proj1 (@lem2296233 x P h1)). Qed.
Lemma lem2296415 (_28866 : int) (P : int -> Prop) (n' : nat) (h1 : term142 P n') : P _28866.
Proof. exact (EQ_MP (@lem2296325 P _28866) (@lem2296324 _28866 P n' h1)). Qed.
Lemma lem2296416 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term24 P n'.
Proof. exact (@lem2296415 (int_of_num n') P n' h1). Qed.
Lemma lem2296417 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term274 P n'.
Proof. exact (fun h0 : term48 P n' => @lem2296416 P n' h1). Qed.
Lemma lem2296419 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296420 (P : int -> Prop) (n' : nat) : (term274 P n') = (term24 P n').
Proof. exact (@lem2296419 (term24 P n')). Qed.
Lemma lem2296421 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term24 P n'.
Proof. exact (EQ_MP (@lem2296420 P n') (@lem2296417 P n' h1)). Qed.
Lemma lem2296424 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2296426 (P : int -> Prop) (n' : nat) : (term48 P n') = (term276 P n').
Proof. exact (@lem2296424 (term24 P n')). Qed.
Lemma lem2296429 (P : int -> Prop) (n' : nat) (h1 : term48 P n') : term276 P n'.
Proof. exact (EQ_MP (@lem2296426 P n') (@lem2296351 P n' h1)). Qed.
Lemma lem2296432 (P : int -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term142 P n') : False.
Proof. exact (@lem2296429 P n' h1 (@lem2296421 P n' h2)). Qed.
Lemma lem2296433 (P : int -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term142 P n') : term277.
Proof. exact (fun h0 : ~ False => @lem2296432 P n' h1 h2). Qed.
Lemma lem2296435 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296436 : term277 = False.
Proof. exact (@lem2296435 False). Qed.
Lemma lem2296437 (P : int -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term142 P n') : False.
Proof. exact (EQ_MP (@lem2296436) (@lem2296433 P n' h1 h2)). Qed.
Lemma lem2296479 (_28868 : int) (P : int -> Prop) (n' : nat) (h1 : term142 P n') : P _28868.
Proof. exact (EQ_MP (@lem2296331 P _28868) (@lem2296330 _28868 P n' h1)). Qed.
Lemma lem2296480 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term21 P n'.
Proof. exact (@lem2296479 (term13 n') P n' h1). Qed.
Lemma lem2296481 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term278 P n'.
Proof. exact (fun h0 : term56 P n' => @lem2296480 P n' h1). Qed.
Lemma lem2296483 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296484 (P : int -> Prop) (n' : nat) : (term278 P n') = (term21 P n').
Proof. exact (@lem2296483 (term21 P n')). Qed.
Lemma lem2296485 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : term21 P n'.
Proof. exact (EQ_MP (@lem2296484 P n') (@lem2296481 P n' h1)). Qed.
Lemma lem2296488 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2296490 (P : int -> Prop) (n' : nat) : (term56 P n') = (term279 P n').
Proof. exact (@lem2296488 (term21 P n')). Qed.
Lemma lem2296493 (P : int -> Prop) (n' : nat) (h1 : term56 P n') : term279 P n'.
Proof. exact (EQ_MP (@lem2296490 P n') (@lem2296361 P n' h1)). Qed.
Lemma lem2296496 (P : int -> Prop) (n' : nat) (h1 : term56 P n') (h2 : term142 P n') : False.
Proof. exact (@lem2296493 P n' h1 (@lem2296485 P n' h2)). Qed.
Lemma lem2296497 (P : int -> Prop) (n' : nat) (h1 : term56 P n') (h2 : term142 P n') : term277.
Proof. exact (fun h0 : ~ False => @lem2296496 P n' h1 h2). Qed.
Lemma lem2296499 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296500 : term277 = False.
Proof. exact (@lem2296499 False). Qed.
Lemma lem2296501 (P : int -> Prop) (n' : nat) (h1 : term56 P n') (h2 : term142 P n') : False.
Proof. exact (EQ_MP (@lem2296500) (@lem2296497 P n' h1 h2)). Qed.
Lemma lem2296502 (P : int -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem2296503 (_28888 : int) (_28889 : int) (h1 : _28888 = _28889) : _28888 = _28889.
Proof. exact (h1). Qed.
Lemma lem2296504 (P : int -> Prop) (_28888 : int) (_28889 : int) (h1 : _28888 = _28889) : (P _28888) = (P _28889).
Proof. exact (MK_COMB (@lem2296502 P) (@lem2296503 _28888 _28889 h1)). Qed.
Lemma lem2296506 (b : Prop) (a : Prop) : term280 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem2296507 (_28889 : int) (P : int -> Prop) (_28888 : int) : term281 _28889 P _28888.
Proof. exact (@lem2296506 (P _28889) (P _28888)). Qed.
Lemma lem2296508 (P : int -> Prop) (_28888 : int) (_28889 : int) (h1 : _28888 = _28889) : term282 _28889 P _28888.
Proof. exact (@lem2296507 _28889 P _28888 (@lem2296504 P _28888 _28889 h1)). Qed.
Lemma lem2296509 (_28889 : int) (P : int -> Prop) (_28888 : int) : term283 _28889 P _28888.
Proof. exact (fun h0 : _28888 = _28889 => @lem2296508 P _28888 _28889 h0). Qed.
Lemma lem2296511 (a : Prop) (b : Prop) : (a -> b) = (term284 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem2296512 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term283 _28889 P _28888) = (term285 _28889 P _28888).
Proof. exact (@lem2296511 (_28888 = _28889) (term282 _28889 P _28888)). Qed.
Lemma lem2296513 (_28889 : int) (P : int -> Prop) (_28888 : int) : term285 _28889 P _28888.
Proof. exact (EQ_MP (@lem2296512 _28889 P _28888) (@lem2296509 _28889 P _28888)). Qed.
Lemma lem2296539 (x : int) (y : int) (z : int) : term286 x y z.
Proof. exact (@lem21385 int x y z). Qed.
Lemma lem2296543 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2296544 (x : int) : term287 x.
Proof. exact (fun h0 : term288 x => @lem2296543 x). Qed.
Lemma lem2296546 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296547 (x : int) : (term287 x) = (x = x).
Proof. exact (@lem2296546 (x = x)). Qed.
Lemma lem2296548 (x : int) : x = x.
Proof. exact (EQ_MP (@lem2296547 x) (@lem2296544 x)). Qed.
Lemma lem2296551 (P : int -> Prop) (x : int) (h1 : term39 P x) : term39 P x.
Proof. exact (h1). Qed.
Lemma lem2296552 (P : int -> Prop) (x : int) (h1 : term39 P x) : term289 P x.
Proof. exact (fun h0 : P x => @lem2296551 P x h1). Qed.
Lemma lem2296554 (p : Prop) : (term290 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2296555 (P : int -> Prop) (x : int) : (term289 P x) = (term39 P x).
Proof. exact (@lem2296554 (P x)). Qed.
Lemma lem2296556 (P : int -> Prop) (x : int) (h1 : term39 P x) : term39 P x.
Proof. exact (EQ_MP (@lem2296555 P x) (@lem2296552 P x h1)). Qed.
Lemma lem2296558 (_28870 : nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term24 P _28870.
Proof. exact (EQ_MP (@lem2296337 P _28870) (@lem2296336 _28870 x P h1)). Qed.
Lemma lem2296559 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term291 P n x.
Proof. exact (@lem2296558 (n x) x P h1). Qed.
Lemma lem2296560 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term292 P n x.
Proof. exact (fun h0 : term293 P n x => @lem2296559 n x P h1). Qed.
Lemma lem2296562 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296563 (P : int -> Prop) (n : int -> nat) (x : int) : (term292 P n x) = (term291 P n x).
Proof. exact (@lem2296562 (term291 P n x)). Qed.
Lemma lem2296564 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term291 P n x.
Proof. exact (EQ_MP (@lem2296563 P n x) (@lem2296560 n x P h1)). Qed.
Lemma lem2296566 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2296567 (P : int -> Prop) (_28888 : int) (_28889 : int) : (term285 _28889 P _28888) = (term295 P _28888 _28889).
Proof. exact (@lem2296566 (term282 _28889 P _28888) (term296 _28888 _28889)). Qed.
Lemma lem2296569 (a : Prop) (b : Prop) : (term297 a b) = (term298 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2296570 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term299 _28889 P _28888) = (term300 _28889 P _28888).
Proof. exact (@lem2296569 (P _28889) (term39 P _28888)). Qed.
Lemma lem2296572 (a : Prop) : (term301 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2296573 (P : int -> Prop) (_28888 : int) : (term302 P _28888) = (P _28888).
Proof. exact (@lem2296572 (P _28888)). Qed.
Lemma lem2296574 (P : int -> Prop) (_28889 : int) : (term162 P _28889) = (term162 P _28889).
Proof. exact (eq_refl (term162 P _28889)). Qed.
Lemma lem2296575 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term300 _28889 P _28888) = (term303 _28889 P _28888).
Proof. exact (MK_COMB (@lem2296574 P _28889) (@lem2296573 P _28888)). Qed.
Lemma lem2296576 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term299 _28889 P _28888) = (term303 _28889 P _28888).
Proof. exact (TRANS (@lem2296570 _28889 P _28888) (@lem2296575 _28889 P _28888)). Qed.
Lemma lem2296577 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2296578 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term304 _28889 P _28888) = (term305 _28889 P _28888).
Proof. exact (MK_COMB (@lem2296577) (@lem2296576 _28889 P _28888)). Qed.
Lemma lem2296579 (_28888 : int) (_28889 : int) : (term296 _28888 _28889) = (term296 _28888 _28889).
Proof. exact (eq_refl (term296 _28888 _28889)). Qed.
Lemma lem2296580 (P : int -> Prop) (_28888 : int) (_28889 : int) : (term295 P _28888 _28889) = (term306 P _28888 _28889).
Proof. exact (MK_COMB (@lem2296578 _28889 P _28888) (@lem2296579 _28888 _28889)). Qed.
Lemma lem2296581 (P : int -> Prop) (_28888 : int) (_28889 : int) : (term285 _28889 P _28888) = (term306 P _28888 _28889).
Proof. exact (TRANS (@lem2296567 P _28888 _28889) (@lem2296580 P _28888 _28889)). Qed.
Lemma lem2296583 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term39 P x) (h2 : term164 x P) : term307 P n x.
Proof. exact (conj (@lem2296556 P x h1) (@lem2296564 n x P h2)). Qed.
Lemma lem2296585 (P : int -> Prop) (_28888 : int) (_28889 : int) : term306 P _28888 _28889.
Proof. exact (EQ_MP (@lem2296581 P _28888 _28889) (@lem2296513 _28889 P _28888)). Qed.
Lemma lem2296586 (P : int -> Prop) (n : int -> nat) (x : int) : term308 P n x.
Proof. exact (@lem2296585 P (term309 n x) x). Qed.
Lemma lem2296589 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term39 P x) (h2 : term164 x P) : term310 n x.
Proof. exact (@lem2296586 P n x (@lem2296583 n x P h1 h2)). Qed.
Lemma lem2296590 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term39 P x) (h2 : term164 x P) : term311 n x.
Proof. exact (fun h0 : (term309 n x) = x => @lem2296589 n x P h1 h2). Qed.
Lemma lem2296592 (p : Prop) : (term290 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2296593 (n : int -> nat) (x : int) : (term311 n x) = (term310 n x).
Proof. exact (@lem2296592 ((term309 n x) = x)). Qed.
Lemma lem2296594 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term39 P x) (h2 : term164 x P) : term310 n x.
Proof. exact (EQ_MP (@lem2296593 n x) (@lem2296590 n x P h1 h2)). Qed.
Lemma lem2296596 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2296597 (z : int) (x : int) (y : int) : (term286 x y z) = (term312 z x y).
Proof. exact (@lem2296596 (term313 x y z) (term296 x y)). Qed.
Lemma lem2296599 (a : Prop) (b : Prop) : (term297 a b) = (term298 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2296600 (x : int) (y : int) (z : int) : (term314 x y z) = (term315 x y z).
Proof. exact (@lem2296599 (term296 x z) (y = z)). Qed.
Lemma lem2296602 (a : Prop) : (term301 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2296603 (x : int) (z : int) : (term316 x z) = (x = z).
Proof. exact (@lem2296602 (x = z)). Qed.
Lemma lem2296604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2296605 (x : int) (z : int) : (term317 x z) = (term318 x z).
Proof. exact (MK_COMB (@lem2296604) (@lem2296603 x z)). Qed.
Lemma lem2296606 (y : int) (z : int) : (term296 y z) = (term296 y z).
Proof. exact (eq_refl (term296 y z)). Qed.
Lemma lem2296607 (x : int) (y : int) (z : int) : (term315 x y z) = (term319 x y z).
Proof. exact (MK_COMB (@lem2296605 x z) (@lem2296606 y z)). Qed.
Lemma lem2296608 (x : int) (y : int) (z : int) : (term314 x y z) = (term319 x y z).
Proof. exact (TRANS (@lem2296600 x y z) (@lem2296607 x y z)). Qed.
Lemma lem2296609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2296610 (x : int) (y : int) (z : int) : (term320 x y z) = (term321 x y z).
Proof. exact (MK_COMB (@lem2296609) (@lem2296608 x y z)). Qed.
Lemma lem2296611 (x : int) (y : int) : (term296 x y) = (term296 x y).
Proof. exact (eq_refl (term296 x y)). Qed.
Lemma lem2296612 (z : int) (x : int) (y : int) : (term312 z x y) = (term322 z x y).
Proof. exact (MK_COMB (@lem2296610 x y z) (@lem2296611 x y)). Qed.
Lemma lem2296613 (z : int) (x : int) (y : int) : (term286 x y z) = (term322 z x y).
Proof. exact (TRANS (@lem2296597 z x y) (@lem2296612 z x y)). Qed.
Lemma lem2296615 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term39 P x) (h2 : term164 x P) : term323 n x.
Proof. exact (conj (@lem2296548 x) (@lem2296594 n x P h1 h2)). Qed.
Lemma lem2296617 (z : int) (x : int) (y : int) : term322 z x y.
Proof. exact (EQ_MP (@lem2296613 z x y) (@lem2296539 x y z)). Qed.
Lemma lem2296618 (n : int -> nat) (x : int) : term324 n x.
Proof. exact (@lem2296617 x x (term309 n x)). Qed.
Lemma lem2296621 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term39 P x) (h2 : term164 x P) : term325 n x.
Proof. exact (@lem2296618 n x (@lem2296615 n x P h1 h2)). Qed.
Lemma lem2296622 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term39 P x) (h2 : term164 x P) : term326 n x.
Proof. exact (fun h0 : x = (term309 n x) => @lem2296621 n x P h1 h2). Qed.
Lemma lem2296624 (p : Prop) : (term290 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2296625 (n : int -> nat) (x : int) : (term326 n x) = (term325 n x).
Proof. exact (@lem2296624 (x = (term309 n x))). Qed.
Lemma lem2296626 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term39 P x) (h2 : term164 x P) : term325 n x.
Proof. exact (EQ_MP (@lem2296625 n x) (@lem2296622 n x P h1 h2)). Qed.
Lemma lem2296632 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2296633 (n : int -> nat) (_28869 : int) : (term265 n _28869) = (term327 n _28869).
Proof. exact (@lem2296632 (_28869 = (term328 n _28869)) (_28869 = (term309 n _28869))). Qed.
Lemma lem2296643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2296644 (n : int -> nat) (_28869 : int) : (term329 n _28869) = (term330 n _28869).
Proof. exact (MK_COMB (@lem2296643) (@lem2296633 n _28869)). Qed.
Lemma lem2296654 (n : int -> nat) (_28869 : int) : (term327 n _28869) = (term327 n _28869).
Proof. exact (eq_refl (term327 n _28869)). Qed.
Lemma lem2296655 (n : int -> nat) (_28869 : int) : ((term265 n _28869) = (term327 n _28869)) = ((term327 n _28869) = (term327 n _28869)).
Proof. exact (MK_COMB (@lem2296644 n _28869) (@lem2296654 n _28869)). Qed.
Lemma lem2296657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2296658 (x : Prop) : (x = x) = True.
Proof. exact (@lem2296657 Prop x). Qed.
Lemma lem2296659 (n : int -> nat) (_28869 : int) : ((term327 n _28869) = (term327 n _28869)) = True.
Proof. exact (@lem2296658 (term327 n _28869)). Qed.
Lemma lem2296660 (n : int -> nat) (_28869 : int) : ((term265 n _28869) = (term327 n _28869)) = True.
Proof. exact (TRANS (@lem2296655 n _28869) (@lem2296659 n _28869)). Qed.
Lemma lem2296661 (n : int -> nat) (_28869 : int) : True = ((term265 n _28869) = (term327 n _28869)).
Proof. exact (SYM (@lem2296660 n _28869)). Qed.
Lemma lem2296662 (n : int -> nat) (_28869 : int) : (term265 n _28869) = (term327 n _28869).
Proof. exact (EQ_MP (@lem2296661 n _28869) (@lem0)). Qed.
Lemma lem2296663 (_28869 : int) (n : int -> nat) (h1 : term269 n) : term327 n _28869.
Proof. exact (EQ_MP (@lem2296662 n _28869) (@lem2296367 _28869 n h1)). Qed.
Lemma lem2296665 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2296668 (n : int -> nat) (_28869 : int) : (term327 n _28869) = (term331 n _28869).
Proof. exact (@lem2296665 (_28869 = (term309 n _28869)) (_28869 = (term328 n _28869))). Qed.
Lemma lem2296671 (_28869 : int) (n : int -> nat) (h1 : term269 n) : term331 n _28869.
Proof. exact (EQ_MP (@lem2296668 n _28869) (@lem2296663 _28869 n h1)). Qed.
Lemma lem2296672 (x : int) (n : int -> nat) (h1 : term269 n) : term331 n x.
Proof. exact (@lem2296671 x n h1). Qed.
Lemma lem2296675 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term39 P x) (h3 : term164 x P) : x = (term328 n x).
Proof. exact (@lem2296672 x n h1 (@lem2296626 n x P h2 h3)). Qed.
Lemma lem2296676 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term39 P x) (h3 : term164 x P) : term332 n x.
Proof. exact (fun h0 : term333 n x => @lem2296675 n x P h1 h2 h3). Qed.
Lemma lem2296678 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296679 (n : int -> nat) (x : int) : (term332 n x) = (x = (term328 n x)).
Proof. exact (@lem2296678 (x = (term328 n x))). Qed.
Lemma lem2296680 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term39 P x) (h3 : term164 x P) : x = (term328 n x).
Proof. exact (EQ_MP (@lem2296679 n x) (@lem2296676 n x P h1 h2 h3)). Qed.
Lemma lem2296682 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2296683 (x : int) : term287 x.
Proof. exact (fun h0 : term288 x => @lem2296682 x). Qed.
Lemma lem2296685 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296686 (x : int) : (term287 x) = (x = x).
Proof. exact (@lem2296685 (x = x)). Qed.
Lemma lem2296687 (x : int) : x = x.
Proof. exact (EQ_MP (@lem2296686 x) (@lem2296683 x)). Qed.
Lemma lem2296705 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2296706 (y : int) (x : int) (z : int) : (term313 x y z) = (term334 y x z).
Proof. exact (@lem2296705 (y = z) (term296 x z)). Qed.
Lemma lem2296716 (x : int) (y : int) : (term335 x y) = (term335 x y).
Proof. exact (eq_refl (term335 x y)). Qed.
Lemma lem2296717 (y : int) (x : int) (z : int) : (term286 x y z) = (term336 y x z).
Proof. exact (MK_COMB (@lem2296716 x y) (@lem2296706 y x z)). Qed.
Lemma lem2296721 (q : Prop) (p : Prop) (r : Prop) : (term337 p q r) = (term337 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2296722 (y : int) (x : int) (z : int) : (term336 y x z) = (term338 y x z).
Proof. exact (@lem2296721 (y = z) (term296 x y) (term296 x z)). Qed.
Lemma lem2296744 (y : int) (x : int) (z : int) : (term286 x y z) = (term338 y x z).
Proof. exact (TRANS (@lem2296717 y x z) (@lem2296722 y x z)). Qed.
Lemma lem2296745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2296746 (y : int) (x : int) (z : int) : (term339 x y z) = (term340 y x z).
Proof. exact (MK_COMB (@lem2296745) (@lem2296744 y x z)). Qed.
Lemma lem2296768 (y : int) (x : int) (z : int) : (term338 y x z) = (term338 y x z).
Proof. exact (eq_refl (term338 y x z)). Qed.
Lemma lem2296769 (y : int) (x : int) (z : int) : ((term286 x y z) = (term338 y x z)) = ((term338 y x z) = (term338 y x z)).
Proof. exact (MK_COMB (@lem2296746 y x z) (@lem2296768 y x z)). Qed.
Lemma lem2296771 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2296772 (x : Prop) : (x = x) = True.
Proof. exact (@lem2296771 Prop x). Qed.
Lemma lem2296773 (y : int) (x : int) (z : int) : ((term338 y x z) = (term338 y x z)) = True.
Proof. exact (@lem2296772 (term338 y x z)). Qed.
Lemma lem2296774 (y : int) (x : int) (z : int) : ((term286 x y z) = (term338 y x z)) = True.
Proof. exact (TRANS (@lem2296769 y x z) (@lem2296773 y x z)). Qed.
Lemma lem2296775 (y : int) (x : int) (z : int) : True = ((term286 x y z) = (term338 y x z)).
Proof. exact (SYM (@lem2296774 y x z)). Qed.
Lemma lem2296776 (y : int) (x : int) (z : int) : (term286 x y z) = (term338 y x z).
Proof. exact (EQ_MP (@lem2296775 y x z) (@lem0)). Qed.
Lemma lem2296777 (y : int) (x : int) (z : int) : term338 y x z.
Proof. exact (EQ_MP (@lem2296776 y x z) (@lem2296539 x y z)). Qed.
Lemma lem2296779 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2296780 (x : int) (y : int) (z : int) : (term338 y x z) = (term341 x y z).
Proof. exact (@lem2296779 (term342 y x z) (y = z)). Qed.
Lemma lem2296782 (a : Prop) (b : Prop) : (term297 a b) = (term298 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2296783 (y : int) (x : int) (z : int) : (term343 y x z) = (term344 y x z).
Proof. exact (@lem2296782 (term296 x y) (term296 x z)). Qed.
Lemma lem2296785 (a : Prop) : (term301 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2296786 (x : int) (y : int) : (term316 x y) = (x = y).
Proof. exact (@lem2296785 (x = y)). Qed.
Lemma lem2296787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2296788 (x : int) (y : int) : (term317 x y) = (term318 x y).
Proof. exact (MK_COMB (@lem2296787) (@lem2296786 x y)). Qed.
Lemma lem2296790 (a : Prop) : (term301 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2296791 (x : int) (z : int) : (term316 x z) = (x = z).
Proof. exact (@lem2296790 (x = z)). Qed.
Lemma lem2296792 (y : int) (x : int) (z : int) : (term344 y x z) = (term345 y x z).
Proof. exact (MK_COMB (@lem2296788 x y) (@lem2296791 x z)). Qed.
Lemma lem2296793 (y : int) (x : int) (z : int) : (term343 y x z) = (term345 y x z).
Proof. exact (TRANS (@lem2296783 y x z) (@lem2296792 y x z)). Qed.
Lemma lem2296794 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2296795 (y : int) (x : int) (z : int) : (term346 y x z) = (term347 y x z).
Proof. exact (MK_COMB (@lem2296794) (@lem2296793 y x z)). Qed.
Lemma lem2296796 (y : int) (z : int) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem2296797 (x : int) (y : int) (z : int) : (term341 x y z) = (term348 x y z).
Proof. exact (MK_COMB (@lem2296795 y x z) (@lem2296796 y z)). Qed.
Lemma lem2296798 (x : int) (y : int) (z : int) : (term338 y x z) = (term348 x y z).
Proof. exact (TRANS (@lem2296780 x y z) (@lem2296797 x y z)). Qed.
Lemma lem2296800 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term39 P x) (h3 : term164 x P) : term349 n x.
Proof. exact (conj (@lem2296680 n x P h1 h2 h3) (@lem2296687 x)). Qed.
Lemma lem2296802 (x : int) (y : int) (z : int) : term348 x y z.
Proof. exact (EQ_MP (@lem2296798 x y z) (@lem2296777 y x z)). Qed.
Lemma lem2296803 (n : int -> nat) (x : int) : term350 n x.
Proof. exact (@lem2296802 x (term328 n x) x). Qed.
Lemma lem2296806 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term39 P x) (h3 : term164 x P) : (term328 n x) = x.
Proof. exact (@lem2296803 n x (@lem2296800 n x P h1 h2 h3)). Qed.
Lemma lem2296807 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term39 P x) (h3 : term164 x P) : term351 n x.
Proof. exact (fun h0 : term352 n x => @lem2296806 n x P h1 h2 h3). Qed.
Lemma lem2296809 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296810 (n : int -> nat) (x : int) : (term351 n x) = ((term328 n x) = x).
Proof. exact (@lem2296809 ((term328 n x) = x)). Qed.
Lemma lem2296811 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term39 P x) (h3 : term164 x P) : (term328 n x) = x.
Proof. exact (EQ_MP (@lem2296810 n x) (@lem2296807 n x P h1 h2 h3)). Qed.
Lemma lem2296813 (_28871 : nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term21 P _28871.
Proof. exact (EQ_MP (@lem2296340 P _28871) (@lem2296339 _28871 x P h1)). Qed.
Lemma lem2296814 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term353 P n x.
Proof. exact (@lem2296813 (n x) x P h1). Qed.
Lemma lem2296815 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term354 P n x.
Proof. exact (fun h0 : term355 P n x => @lem2296814 n x P h1). Qed.
Lemma lem2296817 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296818 (P : int -> Prop) (n : int -> nat) (x : int) : (term354 P n x) = (term353 P n x).
Proof. exact (@lem2296817 (term353 P n x)). Qed.
Lemma lem2296819 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term164 x P) : term353 P n x.
Proof. exact (EQ_MP (@lem2296818 P n x) (@lem2296815 n x P h1)). Qed.
Lemma lem2296825 (q : Prop) (p : Prop) (r : Prop) : (term337 p q r) = (term337 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2296826 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term285 _28889 P _28888) = (term356 _28889 P _28888).
Proof. exact (@lem2296825 (P _28889) (term296 _28888 _28889) (term39 P _28888)). Qed.
Lemma lem2296840 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2296841 (P : int -> Prop) (_28888 : int) (_28889 : int) : (term357 _28889 P _28888) = (term358 P _28888 _28889).
Proof. exact (@lem2296840 (term39 P _28888) (term296 _28888 _28889)). Qed.
Lemma lem2296849 (P : int -> Prop) (_28889 : int) : (term359 P _28889) = (term359 P _28889).
Proof. exact (eq_refl (term359 P _28889)). Qed.
Lemma lem2296850 (P : int -> Prop) (_28888 : int) (_28889 : int) : (term356 _28889 P _28888) = (term360 P _28888 _28889).
Proof. exact (MK_COMB (@lem2296849 P _28889) (@lem2296841 P _28888 _28889)). Qed.
Lemma lem2296861 (P : int -> Prop) (_28888 : int) (_28889 : int) : (term285 _28889 P _28888) = (term360 P _28888 _28889).
Proof. exact (TRANS (@lem2296826 _28889 P _28888) (@lem2296850 P _28888 _28889)). Qed.
Lemma lem2296862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2296863 (P : int -> Prop) (_28888 : int) (_28889 : int) : (term361 _28889 P _28888) = (term362 P _28888 _28889).
Proof. exact (MK_COMB (@lem2296862) (@lem2296861 P _28888 _28889)). Qed.
Lemma lem2296877 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2296878 (P : int -> Prop) (_28888 : int) (_28889 : int) : (term357 _28889 P _28888) = (term358 P _28888 _28889).
Proof. exact (@lem2296877 (term39 P _28888) (term296 _28888 _28889)). Qed.
Lemma lem2296886 (P : int -> Prop) (_28889 : int) : (term359 P _28889) = (term359 P _28889).
Proof. exact (eq_refl (term359 P _28889)). Qed.
Lemma lem2296887 (P : int -> Prop) (_28888 : int) (_28889 : int) : (term356 _28889 P _28888) = (term360 P _28888 _28889).
Proof. exact (MK_COMB (@lem2296886 P _28889) (@lem2296878 P _28888 _28889)). Qed.
Lemma lem2296898 (P : int -> Prop) (_28888 : int) (_28889 : int) : ((term285 _28889 P _28888) = (term356 _28889 P _28888)) = ((term360 P _28888 _28889) = (term360 P _28888 _28889)).
Proof. exact (MK_COMB (@lem2296863 P _28888 _28889) (@lem2296887 P _28888 _28889)). Qed.
Lemma lem2296900 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2296901 (x : Prop) : (x = x) = True.
Proof. exact (@lem2296900 Prop x). Qed.
Lemma lem2296902 (P : int -> Prop) (_28888 : int) (_28889 : int) : ((term360 P _28888 _28889) = (term360 P _28888 _28889)) = True.
Proof. exact (@lem2296901 (term360 P _28888 _28889)). Qed.
Lemma lem2296903 (_28889 : int) (P : int -> Prop) (_28888 : int) : ((term285 _28889 P _28888) = (term356 _28889 P _28888)) = True.
Proof. exact (TRANS (@lem2296898 P _28888 _28889) (@lem2296902 P _28888 _28889)). Qed.
Lemma lem2296904 (_28889 : int) (P : int -> Prop) (_28888 : int) : True = ((term285 _28889 P _28888) = (term356 _28889 P _28888)).
Proof. exact (SYM (@lem2296903 _28889 P _28888)). Qed.
Lemma lem2296905 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term285 _28889 P _28888) = (term356 _28889 P _28888).
Proof. exact (EQ_MP (@lem2296904 _28889 P _28888) (@lem0)). Qed.
Lemma lem2296906 (_28889 : int) (P : int -> Prop) (_28888 : int) : term356 _28889 P _28888.
Proof. exact (EQ_MP (@lem2296905 _28889 P _28888) (@lem2296513 _28889 P _28888)). Qed.
Lemma lem2296908 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2296909 (_28888 : int) (P : int -> Prop) (_28889 : int) : (term356 _28889 P _28888) = (term363 _28888 P _28889).
Proof. exact (@lem2296908 (term357 _28889 P _28888) (P _28889)). Qed.
Lemma lem2296911 (a : Prop) (b : Prop) : (term297 a b) = (term298 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2296912 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term364 _28889 P _28888) = (term365 _28889 P _28888).
Proof. exact (@lem2296911 (term296 _28888 _28889) (term39 P _28888)). Qed.
Lemma lem2296914 (a : Prop) : (term301 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2296915 (_28888 : int) (_28889 : int) : (term316 _28888 _28889) = (_28888 = _28889).
Proof. exact (@lem2296914 (_28888 = _28889)). Qed.
Lemma lem2296916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2296917 (_28888 : int) (_28889 : int) : (term317 _28888 _28889) = (term318 _28888 _28889).
Proof. exact (MK_COMB (@lem2296916) (@lem2296915 _28888 _28889)). Qed.
Lemma lem2296919 (a : Prop) : (term301 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2296920 (P : int -> Prop) (_28888 : int) : (term302 P _28888) = (P _28888).
Proof. exact (@lem2296919 (P _28888)). Qed.
Lemma lem2296921 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term365 _28889 P _28888) = (term366 _28889 P _28888).
Proof. exact (MK_COMB (@lem2296917 _28888 _28889) (@lem2296920 P _28888)). Qed.
Lemma lem2296922 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term364 _28889 P _28888) = (term366 _28889 P _28888).
Proof. exact (TRANS (@lem2296912 _28889 P _28888) (@lem2296921 _28889 P _28888)). Qed.
Lemma lem2296923 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2296924 (_28889 : int) (P : int -> Prop) (_28888 : int) : (term367 _28889 P _28888) = (term368 _28889 P _28888).
Proof. exact (MK_COMB (@lem2296923) (@lem2296922 _28889 P _28888)). Qed.
Lemma lem2296925 (P : int -> Prop) (_28889 : int) : (P _28889) = (P _28889).
Proof. exact (eq_refl (P _28889)). Qed.
Lemma lem2296926 (_28888 : int) (P : int -> Prop) (_28889 : int) : (term363 _28888 P _28889) = (term369 _28888 P _28889).
Proof. exact (MK_COMB (@lem2296924 _28889 P _28888) (@lem2296925 P _28889)). Qed.
Lemma lem2296927 (_28888 : int) (P : int -> Prop) (_28889 : int) : (term356 _28889 P _28888) = (term369 _28888 P _28889).
Proof. exact (TRANS (@lem2296909 _28888 P _28889) (@lem2296926 _28888 P _28889)). Qed.
Lemma lem2296929 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term39 P x) (h3 : term164 x P) : term370 P n x.
Proof. exact (conj (@lem2296811 n x P h1 h2 h3) (@lem2296819 n x P h3)). Qed.
Lemma lem2296931 (_28888 : int) (P : int -> Prop) (_28889 : int) : term369 _28888 P _28889.
Proof. exact (EQ_MP (@lem2296927 _28888 P _28889) (@lem2296906 _28889 P _28888)). Qed.
Lemma lem2296932 (n : int -> nat) (P : int -> Prop) (x : int) : term371 n P x.
Proof. exact (@lem2296931 (term328 n x) P x). Qed.
Lemma lem2296935 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term39 P x) (h3 : term164 x P) : P x.
Proof. exact (@lem2296932 n P x (@lem2296929 n x P h1 h2 h3)). Qed.
Lemma lem2296936 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term164 x P) : term372 P x.
Proof. exact (fun h0 : term39 P x => @lem2296935 n x P h1 h0 h2). Qed.
Lemma lem2296938 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296939 (P : int -> Prop) (x : int) : (term372 P x) = (P x).
Proof. exact (@lem2296938 (P x)). Qed.
Lemma lem2296940 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term164 x P) : P x.
Proof. exact (EQ_MP (@lem2296939 P x) (@lem2296936 n x P h1 h2)). Qed.
Lemma lem2296943 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2296945 (P : int -> Prop) (x : int) : (term39 P x) = (term373 P x).
Proof. exact (@lem2296943 (P x)). Qed.
Lemma lem2296948 (x : int) (P : int -> Prop) (h1 : term164 x P) : term373 P x.
Proof. exact (EQ_MP (@lem2296945 P x) (@lem2296369 x P h1)). Qed.
Lemma lem2296951 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term164 x P) : False.
Proof. exact (@lem2296948 x P h2 (@lem2296940 n x P h1 h2)). Qed.
Lemma lem2296952 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term164 x P) : term277.
Proof. exact (fun h0 : ~ False => @lem2296951 n x P h1 h2). Qed.
Lemma lem2296954 (p : Prop) : (term275 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2296955 : term277 = False.
Proof. exact (@lem2296954 False). Qed.
Lemma lem2296956 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term164 x P) : False.
Proof. exact (EQ_MP (@lem2296955) (@lem2296952 n x P h1 h2)). Qed.
Lemma lem2296957 (P : int -> Prop) (n' : nat) (h1 : term56 P n') (h2 : term142 P n') : (term56 P n') = False.
Proof. exact (prop_ext (fun h3 : term56 P n' => @lem2296501 P n' h1 h2) (fun h3 : False => @lem2296361 P n' h1)). Qed.
Lemma lem2296958 (P : int -> Prop) (n' : nat) (h1 : term56 P n') (h2 : term142 P n') : False.
Proof. exact (EQ_MP (@lem2296957 P n' h1 h2) (@lem2296361 P n' h1)). Qed.
Lemma lem2296959 (P : int -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term142 P n') : (term48 P n') = False.
Proof. exact (prop_ext (fun h3 : term48 P n' => @lem2296437 P n' h1 h2) (fun h3 : False => @lem2296351 P n' h1)). Qed.
Lemma lem2296960 (P : int -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term142 P n') : False.
Proof. exact (EQ_MP (@lem2296959 P n' h1 h2) (@lem2296351 P n' h1)). Qed.
Lemma lem2296961 (P : int -> Prop) (n' : nat) (h1 : term56 P n') (h2 : term142 P n') : (term56 P n') = False.
Proof. exact (prop_ext (fun h3 : term56 P n' => @lem2296958 P n' h1 h2) (fun h3 : False => @lem2296289 P n' h1)). Qed.
Lemma lem2296962 (P : int -> Prop) (n' : nat) (h1 : term56 P n') (h2 : term142 P n') : False.
Proof. exact (EQ_MP (@lem2296961 P n' h1 h2) (@lem2296289 P n' h1)). Qed.
Lemma lem2296963 (P : int -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term142 P n') : (term48 P n') = False.
Proof. exact (prop_ext (fun h3 : term48 P n' => @lem2296960 P n' h1 h2) (fun h3 : False => @lem2296265 P n' h1)). Qed.
Lemma lem2296964 (P : int -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term142 P n') : False.
Proof. exact (EQ_MP (@lem2296963 P n' h1 h2) (@lem2296265 P n' h1)). Qed.
Lemma lem2296965 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term164 x P) : (term269 n) = False.
Proof. exact (prop_ext (fun h3 : term269 n => @lem2296956 n x P h1 h2) (fun h3 : False => @lem2296302 n h1)). Qed.
Lemma lem2296966 (n : int -> nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term164 x P) : False.
Proof. exact (EQ_MP (@lem2296965 n x P h1 h2) (@lem2296302 n h1)). Qed.
Lemma lem2296967 (P : int -> Prop) (n' : nat) (h1 : term56 P n') (h2 : term142 P n') : (term56 P n') = False.
Proof. exact (prop_ext (fun h3 : term56 P n' => @lem2296962 P n' h1 h2) (fun h3 : False => @lem2296289 P n' h1)). Qed.
Lemma lem2296968 (P : int -> Prop) (n' : nat) (h1 : term56 P n') (h2 : term142 P n') : False.
Proof. exact (EQ_MP (@lem2296967 P n' h1 h2) (@lem2296289 P n' h1)). Qed.
Lemma lem2296969 (P : int -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term142 P n') : (term48 P n') = False.
Proof. exact (prop_ext (fun h3 : term48 P n' => @lem2296964 P n' h1 h2) (fun h3 : False => @lem2296265 P n' h1)). Qed.
Lemma lem2296970 (P : int -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term142 P n') : False.
Proof. exact (EQ_MP (@lem2296969 P n' h1 h2) (@lem2296265 P n' h1)). Qed.
Lemma lem2296971 (P : int -> Prop) (n' : nat) (h1 : term142 P n') : False.
Proof. exact (or_elim (@lem2296234 P n' h1) (fun h0 : term48 P n' => @lem2296970 P n' h0 h1) (fun h0 : term56 P n' => @lem2296968 P n' h0 h1)). Qed.
Lemma lem2296972 (n : int -> nat) (n' : nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term220 n' x P) : False.
Proof. exact (or_elim (@lem2296231 n' x P h2) (fun h0 : term142 P n' => @lem2296971 P n' h0) (fun h0 : term164 x P => @lem2296966 n x P h1 h0)). Qed.
Lemma lem2296973 (n : int -> nat) (n' : nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term220 n' x P) : (term220 n' x P) = False.
Proof. exact (prop_ext (fun h3 : term220 n' x P => @lem2296972 n n' x P h1 h2) (fun h3 : False => @lem2296231 n' x P h2)). Qed.
Lemma lem2296974 (n : int -> nat) (n' : nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term220 n' x P) : False.
Proof. exact (EQ_MP (@lem2296973 n n' x P h1 h2) (@lem2296231 n' x P h2)). Qed.
Lemma lem2296975 (n : int -> nat) (n' : nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term220 n' x P) : (term269 n) = False.
Proof. exact (prop_ext (fun h3 : term269 n => @lem2296974 n n' x P h1 h2) (fun h3 : False => @lem2296170 n h1)). Qed.
Lemma lem2296976 (n : int -> nat) (n' : nat) (x : int) (P : int -> Prop) (h1 : term269 n) (h2 : term220 n' x P) : False.
Proof. exact (EQ_MP (@lem2296975 n n' x P h1 h2) (@lem2296170 n h1)). Qed.
Lemma lem2296977 (n : int -> nat) (n' : nat) (P : int -> Prop) (h1 : term269 n) (h2 : term223 n' P) : False.
Proof. exact (ex_elim (@lem2296142 n' P h2) (fun x : int => fun h0 : term222 n' P x => @lem2296976 n n' x P h1 h0)). Qed.
Lemma lem2296978 (n : int -> nat) (P : int -> Prop) (h1 : term269 n) (h2 : term225 P) : False.
Proof. exact (ex_elim (@lem2296141 P h2) (fun n' : nat => fun h0 : term224 P n' => @lem2296977 n n' P h1 h0)). Qed.
Lemma lem2296979 (n : int -> nat) (h1 : term269 n) (h2 : term3) : False.
Proof. exact (ex_elim (@lem2296004 h2) (fun P : int -> Prop => fun h0 : term226 P => @lem2296978 n P h1 h0)). Qed.
Lemma lem2296980 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem2296139 h1) (fun n : int -> nat => fun h0 : term271 n => @lem2296979 n h0 h2)). Qed.
Lemma lem2296981 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem2296980 h0 h1). Qed.
Lemma lem2296982 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem2296983 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem2296982) (@lem2296981 h1)). Qed.
Lemma lem2296984 : term12.
Proof. exact (fun h0 : term3 => @lem2296983 h0). Qed.
Lemma lem2296985 : term4.
Proof. exact (EQ_MP (@lem2295613) (@lem2296984)). Qed.
Lemma lem2296987 : term4.
Proof. exact (@lem2295430 (@lem2296985)). Qed.
Lemma lem2296988 (h1 : term3) : term8.
Proof. exact (@lem2296987 (@lem2295415 h1)). Qed.
Lemma lem2296989 (h1 : term3) : False.
Proof. exact (@lem2296988 h1 (@lem2295400)). Qed.
Lemma lem2296990 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem2296989 h1) (fun h2 : False => @lem2295415 h1)). Qed.
Lemma lem2296991 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem2296990 h1) (@lem2295415 h1)). Qed.
Lemma lem2296992 : term2.
Proof. exact (fun h0 : term3 => @lem2296991 h0). Qed.
Lemma lem2296993 : term1.
Proof. exact (EQ_MP (@lem2295414) (@lem2296992)). Qed.
