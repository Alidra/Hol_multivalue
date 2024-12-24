Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ARCH_ZERO_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NADD_ADD_LID_spec.
Require Import NADD_ADD_WELLDEF_spec.
Require Import NADD_ARCH_spec.
Require Import NADD_ARCH_MULT_spec.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_SYM_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import NADD_LE_0_spec.
Require Import NADD_LE_ANTISYM_spec.
Require Import NADD_LE_RADD_spec.
Require Import NADD_LE_TRANS_spec.
Require Import NADD_LE_WELLDEF_spec.
Require Import NADD_MUL_LID_spec.
Require Import NADD_MUL_SYM_spec.
Require Import NADD_MUL_WELLDEF_spec.
Require Import NADD_OF_NUM_ADD_spec.
Require Import NADD_RDISTRIB_spec.
Require Import NOT_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10568_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1823_spec.
Require Import thm1843_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
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
Require Import thm37_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1286558 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1286559 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1286560 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1286559 t1) (@lem1286558 t1)). Qed.
Lemma lem1286561 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1286560 t1 t2). Qed.
Lemma lem1286562 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1286563 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1286562 t1 t2) (@lem1286561 t1 t2)). Qed.
Lemma lem1286564 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1286563 t1 t2 t3). Qed.
Lemma lem1286565 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1286566 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1286565 t1 t2 t3) (@lem1286564 t1 t2 t3)). Qed.
Lemma lem1286567 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1286566 t1 t2 t3)). Qed.
Lemma lem1286568 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1286569 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1286570 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1286569 t1) (@lem1286568 t1)). Qed.
Lemma lem1286571 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1286570 t1 t2). Qed.
Lemma lem1286572 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1286573 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1286572 t1 t2) (@lem1286571 t1 t2)). Qed.
Lemma lem1286574 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1286573 t1 t2 t3). Qed.
Lemma lem1286575 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1286576 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1286575 t1 t2 t3) (@lem1286574 t1 t2 t3)). Qed.
Lemma lem1286577 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1286576 t1 t2 t3)). Qed.
Lemma lem1286578 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1286579 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1286580 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1286579 t1) (@lem1286578 t1)). Qed.
Lemma lem1286581 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1286580 t1 t2). Qed.
Lemma lem1286582 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1286583 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1286582 t1 t2) (@lem1286581 t1 t2)). Qed.
Lemma lem1286584 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1286583 t1 t2 t3). Qed.
Lemma lem1286585 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1286586 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1286585 t1 t2 t3) (@lem1286584 t1 t2 t3)). Qed.
Lemma lem1286587 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1286586 t1 t2 t3)). Qed.
Lemma lem1286598 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1286599 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1286600 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1286599 t1) (@lem1286598 t1)). Qed.
Lemma lem1286601 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1286600 t1 t2). Qed.
Lemma lem1286602 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1286603 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1286602 t1 t2) (@lem1286601 t1 t2)). Qed.
Lemma lem1286604 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1286603 t1 t2 t3). Qed.
Lemma lem1286605 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1286606 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1286605 t1 t2 t3) (@lem1286604 t1 t2 t3)). Qed.
Lemma lem1286607 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1286606 t1 t2 t3)). Qed.
Lemma lem1286608 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1286609 (x : nadd) (h1 : term7) : term8 x.
Proof. exact (@lem1286608 h1 x). Qed.
Lemma lem1286610 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1286611 (x : nadd) (h1 : term7) : term9 x.
Proof. exact (EQ_MP (@lem1286610 x) (@lem1286609 x h1)). Qed.
Lemma lem1286612 (x : nadd) (y : nadd) (h1 : term7) : term10 x y.
Proof. exact (@lem1286611 x h1 y). Qed.
Lemma lem1286613 (y : nadd) (x : nadd) : (term10 x y) = (term11 y x).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1286614 (y : nadd) (x : nadd) (h1 : term7) : term11 y x.
Proof. exact (EQ_MP (@lem1286613 y x) (@lem1286612 x y h1)). Qed.
Lemma lem1286615 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term12 y x z.
Proof. exact (@lem1286614 y x h1 z). Qed.
Lemma lem1286616 (y : nadd) (x : nadd) (z : nadd) : (term12 y x z) = (term13 y x z).
Proof. exact (eq_refl (term12 y x z)). Qed.
Lemma lem1286617 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term13 y x z.
Proof. exact (EQ_MP (@lem1286616 y x z) (@lem1286615 y x z h1)). Qed.
Lemma lem1286618 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term14 x y z.
Proof. exact (h1). Qed.
Lemma lem1286619 (x : nadd) (y : nadd) (z : nadd) (h1 : term7) (h2 : term14 x y z) : nadd_eq x z.
Proof. exact (@lem1286617 y x z h1 (@lem1286618 x y z h2)). Qed.
Lemma lem1286620 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term15 x z.
Proof. exact (fun h0 : term7 => @lem1286619 x y z h0 h1). Qed.
Lemma lem1286621 (x : nadd) (z : nadd) (h1 : term16 x z) : term16 x z.
Proof. exact (h1). Qed.
Lemma lem1286622 (x : nadd) (z : nadd) (h1 : term16 x z) : term15 x z.
Proof. exact (ex_elim (@lem1286621 x z h1) (fun y : nadd => fun h0 : term17 x z y => @lem1286620 x y z h0)). Qed.
Lemma lem1286623 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1286624 (x : nadd) (z : nadd) (h1 : term7) (h2 : term16 x z) : nadd_eq x z.
Proof. exact (@lem1286622 x z h2 (@lem1286623 h1)). Qed.
Lemma lem1286625 (x : nadd) (z : nadd) (h1 : term7) : term18 x z.
Proof. exact (fun h0 : term16 x z => @lem1286624 x z h1 h0). Qed.
Lemma lem1286626 (x : nadd) (h1 : term7) : term19 x.
Proof. exact (fun z : nadd => @lem1286625 x z h1). Qed.
Lemma lem1286627 (h1 : term7) : term20.
Proof. exact (fun x : nadd => @lem1286626 x h1). Qed.
Lemma lem1286628 : term21.
Proof. exact (fun h0 : term7 => @lem1286627 h0). Qed.
Lemma lem1286629 : term20.
Proof. exact (@lem1286628 (@lem1268295)). Qed.
Lemma lem1286630 (x : nadd) : term22 x.
Proof. exact (@lem1286629 x). Qed.
Lemma lem1286631 (x : nadd) : (term22 x) = (term19 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1286632 (x : nadd) : term19 x.
Proof. exact (EQ_MP (@lem1286631 x) (@lem1286630 x)). Qed.
Lemma lem1286633 (x : nadd) (z : nadd) : term23 x z.
Proof. exact (@lem1286632 x z). Qed.
Lemma lem1286634 (x : nadd) (z : nadd) : (term23 x z) = (term18 x z).
Proof. exact (eq_refl (term23 x z)). Qed.
Lemma lem1286636 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1286637 (x : nadd) (h1 : term7) : term8 x.
Proof. exact (@lem1286636 h1 x). Qed.
Lemma lem1286638 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1286639 (x : nadd) (h1 : term7) : term9 x.
Proof. exact (EQ_MP (@lem1286638 x) (@lem1286637 x h1)). Qed.
Lemma lem1286640 (x : nadd) (y : nadd) (h1 : term7) : term10 x y.
Proof. exact (@lem1286639 x h1 y). Qed.
Lemma lem1286641 (y : nadd) (x : nadd) : (term10 x y) = (term11 y x).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1286642 (y : nadd) (x : nadd) (h1 : term7) : term11 y x.
Proof. exact (EQ_MP (@lem1286641 y x) (@lem1286640 x y h1)). Qed.
Lemma lem1286643 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term12 y x z.
Proof. exact (@lem1286642 y x h1 z). Qed.
Lemma lem1286644 (y : nadd) (x : nadd) (z : nadd) : (term12 y x z) = (term13 y x z).
Proof. exact (eq_refl (term12 y x z)). Qed.
Lemma lem1286645 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term13 y x z.
Proof. exact (EQ_MP (@lem1286644 y x z) (@lem1286643 y x z h1)). Qed.
Lemma lem1286646 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term14 x y z.
Proof. exact (h1). Qed.
Lemma lem1286647 (x : nadd) (y : nadd) (z : nadd) (h1 : term7) (h2 : term14 x y z) : nadd_eq x z.
Proof. exact (@lem1286645 y x z h1 (@lem1286646 x y z h2)). Qed.
Lemma lem1286648 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term15 x z.
Proof. exact (fun h0 : term7 => @lem1286647 x y z h0 h1). Qed.
Lemma lem1286649 (x : nadd) (z : nadd) (h1 : term16 x z) : term16 x z.
Proof. exact (h1). Qed.
Lemma lem1286650 (x : nadd) (z : nadd) (h1 : term16 x z) : term15 x z.
Proof. exact (ex_elim (@lem1286649 x z h1) (fun y : nadd => fun h0 : term17 x z y => @lem1286648 x y z h0)). Qed.
Lemma lem1286651 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1286652 (x : nadd) (z : nadd) (h1 : term7) (h2 : term16 x z) : nadd_eq x z.
Proof. exact (@lem1286650 x z h2 (@lem1286651 h1)). Qed.
Lemma lem1286653 (x : nadd) (z : nadd) (h1 : term7) : term18 x z.
Proof. exact (fun h0 : term16 x z => @lem1286652 x z h1 h0). Qed.
Lemma lem1286654 (x : nadd) (h1 : term7) : term19 x.
Proof. exact (fun z : nadd => @lem1286653 x z h1). Qed.
Lemma lem1286655 (h1 : term7) : term20.
Proof. exact (fun x : nadd => @lem1286654 x h1). Qed.
Lemma lem1286656 : term21.
Proof. exact (fun h0 : term7 => @lem1286655 h0). Qed.
Lemma lem1286657 : term20.
Proof. exact (@lem1286656 (@lem1268295)). Qed.
Lemma lem1286658 (x : nadd) : term22 x.
Proof. exact (@lem1286657 x). Qed.
Lemma lem1286659 (x : nadd) : (term22 x) = (term19 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1286660 (x : nadd) : term19 x.
Proof. exact (EQ_MP (@lem1286659 x) (@lem1286658 x)). Qed.
Lemma lem1286661 (x : nadd) (z : nadd) : term23 x z.
Proof. exact (@lem1286660 x z). Qed.
Lemma lem1286662 (x : nadd) (z : nadd) : (term23 x z) = (term18 x z).
Proof. exact (eq_refl (term23 x z)). Qed.
Lemma lem1286664 (m : nat) : term24 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1286665 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1286666 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1286665 m) (@lem1286664 m)). Qed.
Lemma lem1286667 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1286666 m n). Qed.
Lemma lem1286668 (n : nat) (m : nat) : (term26 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1286670 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1286671 (x : nadd) (h1 : term27) : term28 x.
Proof. exact (@lem1286670 h1 x). Qed.
Lemma lem1286672 (x : nadd) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1286673 (x : nadd) (h1 : term27) : term29 x.
Proof. exact (EQ_MP (@lem1286672 x) (@lem1286671 x h1)). Qed.
Lemma lem1286674 (x : nadd) (y : nadd) (h1 : term27) : term30 x y.
Proof. exact (@lem1286673 x h1 y). Qed.
Lemma lem1286675 (y : nadd) (x : nadd) : (term30 x y) = (term31 y x).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem1286676 (y : nadd) (x : nadd) (h1 : term27) : term31 y x.
Proof. exact (EQ_MP (@lem1286675 y x) (@lem1286674 x y h1)). Qed.
Lemma lem1286677 (y : nadd) (x : nadd) (z : nadd) (h1 : term27) : term32 y x z.
Proof. exact (@lem1286676 y x h1 z). Qed.
Lemma lem1286678 (y : nadd) (x : nadd) (z : nadd) : (term32 y x z) = (term33 y x z).
Proof. exact (eq_refl (term32 y x z)). Qed.
Lemma lem1286679 (y : nadd) (x : nadd) (z : nadd) (h1 : term27) : term33 y x z.
Proof. exact (EQ_MP (@lem1286678 y x z) (@lem1286677 y x z h1)). Qed.
Lemma lem1286680 (x : nadd) (y : nadd) (z : nadd) (h1 : term34 x y z) : term34 x y z.
Proof. exact (h1). Qed.
Lemma lem1286681 (x : nadd) (y : nadd) (z : nadd) (h1 : term27) (h2 : term34 x y z) : nadd_le x z.
Proof. exact (@lem1286679 y x z h1 (@lem1286680 x y z h2)). Qed.
Lemma lem1286682 (x : nadd) (y : nadd) (z : nadd) (h1 : term34 x y z) : term35 x z.
Proof. exact (fun h0 : term27 => @lem1286681 x y z h0 h1). Qed.
Lemma lem1286683 (x : nadd) (z : nadd) (h1 : term36 x z) : term36 x z.
Proof. exact (h1). Qed.
Lemma lem1286684 (x : nadd) (z : nadd) (h1 : term36 x z) : term35 x z.
Proof. exact (ex_elim (@lem1286683 x z h1) (fun y : nadd => fun h0 : term37 x z y => @lem1286682 x y z h0)). Qed.
Lemma lem1286685 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1286686 (x : nadd) (z : nadd) (h1 : term27) (h2 : term36 x z) : nadd_le x z.
Proof. exact (@lem1286684 x z h2 (@lem1286685 h1)). Qed.
Lemma lem1286687 (x : nadd) (z : nadd) (h1 : term27) : term38 x z.
Proof. exact (fun h0 : term36 x z => @lem1286686 x z h1 h0). Qed.
Lemma lem1286688 (x : nadd) (h1 : term27) : term39 x.
Proof. exact (fun z : nadd => @lem1286687 x z h1). Qed.
Lemma lem1286689 (h1 : term27) : term40.
Proof. exact (fun x : nadd => @lem1286688 x h1). Qed.
Lemma lem1286690 : term41.
Proof. exact (fun h0 : term27 => @lem1286689 h0). Qed.
Lemma lem1286691 : term40.
Proof. exact (@lem1286690 (@lem1270880)). Qed.
Lemma lem1286692 (x : nadd) : term42 x.
Proof. exact (@lem1286691 x). Qed.
Lemma lem1286693 (x : nadd) : (term42 x) = (term39 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1286694 (x : nadd) : term39 x.
Proof. exact (EQ_MP (@lem1286693 x) (@lem1286692 x)). Qed.
Lemma lem1286695 (x : nadd) (z : nadd) : term43 x z.
Proof. exact (@lem1286694 x z). Qed.
Lemma lem1286696 (x : nadd) (z : nadd) : (term43 x z) = (term38 x z).
Proof. exact (eq_refl (term43 x z)). Qed.
Lemma lem1286698 (x : nadd) : term44 x.
Proof. exact (@lem1281482 x). Qed.
Lemma lem1286699 (x : nadd) : (term44 x) = (term45 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1286700 (x : nadd) : term45 x.
Proof. exact (EQ_MP (@lem1286699 x) (@lem1286698 x)). Qed.
Lemma lem1286701 (x : nadd) (y : nadd) : term46 x y.
Proof. exact (@lem1286700 x y). Qed.
Lemma lem1286702 (x : nadd) (y : nadd) : (term46 x y) = (term47 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1286703 (x : nadd) (y : nadd) : term47 x y.
Proof. exact (EQ_MP (@lem1286702 x y) (@lem1286701 x y)). Qed.
Lemma lem1286704 (x : nadd) (y : nadd) (z : nadd) : term48 x y z.
Proof. exact (@lem1286703 x y z). Qed.
Lemma lem1286705 (z : nadd) (x : nadd) (y : nadd) : (term48 x y z) = ((term49 x y z) = (nadd_le x y)).
Proof. exact (eq_refl (term48 x y z)). Qed.
Lemma lem1286706 (z : nadd) (x : nadd) (y : nadd) : (term49 x y z) = (nadd_le x y).
Proof. exact (EQ_MP (@lem1286705 z x y) (@lem1286704 x y z)). Qed.
Lemma lem1286709 (z : nadd) (x : nadd) (y : nadd) : term50 z x y.
Proof. exact (@lem37 (term49 x y z) (nadd_le x y)). Qed.
Lemma lem1286710 (z : nadd) (x : nadd) (y : nadd) : term51 z x y.
Proof. exact (@lem1286709 z x y (@lem1286706 z x y)). Qed.
Lemma lem1286711 (z : nadd) (x : nadd) : term52 z x.
Proof. exact (fun y : nadd => @lem1286710 z x y). Qed.
Lemma lem1286712 (z : nadd) : term53 z.
Proof. exact (fun x : nadd => @lem1286711 z x). Qed.
Lemma lem1286713 : term54.
Proof. exact (fun z : nadd => @lem1286712 z). Qed.
Lemma lem1286714 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem1286715 (z : nadd) (h1 : term54) : term55 z.
Proof. exact (@lem1286714 h1 z). Qed.
Lemma lem1286716 (z : nadd) : (term55 z) = (term53 z).
Proof. exact (eq_refl (term55 z)). Qed.
Lemma lem1286717 (z : nadd) (h1 : term54) : term53 z.
Proof. exact (EQ_MP (@lem1286716 z) (@lem1286715 z h1)). Qed.
Lemma lem1286718 (z : nadd) (x : nadd) (h1 : term54) : term56 z x.
Proof. exact (@lem1286717 z h1 x). Qed.
Lemma lem1286719 (z : nadd) (x : nadd) : (term56 z x) = (term52 z x).
Proof. exact (eq_refl (term56 z x)). Qed.
Lemma lem1286720 (z : nadd) (x : nadd) (h1 : term54) : term52 z x.
Proof. exact (EQ_MP (@lem1286719 z x) (@lem1286718 z x h1)). Qed.
Lemma lem1286721 (z : nadd) (x : nadd) (y : nadd) (h1 : term54) : term57 z x y.
Proof. exact (@lem1286720 z x h1 y). Qed.
Lemma lem1286722 (z : nadd) (x : nadd) (y : nadd) : (term57 z x y) = (term51 z x y).
Proof. exact (eq_refl (term57 z x y)). Qed.
Lemma lem1286723 (z : nadd) (x : nadd) (y : nadd) (h1 : term54) : term51 z x y.
Proof. exact (EQ_MP (@lem1286722 z x y) (@lem1286721 z x y h1)). Qed.
Lemma lem1286724 (x : nadd) (y : nadd) (z : nadd) (h1 : term49 x y z) : term49 x y z.
Proof. exact (h1). Qed.
Lemma lem1286725 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term49 x y z) : nadd_le x y.
Proof. exact (@lem1286723 z x y h1 (@lem1286724 x y z h2)). Qed.
Lemma lem1286726 (x : nadd) (y : nadd) (z : nadd) (h1 : term49 x y z) : term58 x y.
Proof. exact (fun h0 : term54 => @lem1286725 x y z h0 h1). Qed.
Lemma lem1286727 (x : nadd) (y : nadd) (h1 : term59 x y) : term59 x y.
Proof. exact (h1). Qed.
Lemma lem1286728 (x : nadd) (y : nadd) (h1 : term59 x y) : term58 x y.
Proof. exact (ex_elim (@lem1286727 x y h1) (fun z : nadd => fun h0 : term60 x y z => @lem1286726 x y z h0)). Qed.
Lemma lem1286729 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem1286730 (x : nadd) (y : nadd) (h1 : term54) (h2 : term59 x y) : nadd_le x y.
Proof. exact (@lem1286728 x y h2 (@lem1286729 h1)). Qed.
Lemma lem1286731 (x : nadd) (y : nadd) (h1 : term54) : term61 x y.
Proof. exact (fun h0 : term59 x y => @lem1286730 x y h1 h0). Qed.
Lemma lem1286732 (x : nadd) (h1 : term54) : term62 x.
Proof. exact (fun y : nadd => @lem1286731 x y h1). Qed.
Lemma lem1286733 (h1 : term54) : term63.
Proof. exact (fun x : nadd => @lem1286732 x h1). Qed.
Lemma lem1286734 : term64.
Proof. exact (fun h0 : term54 => @lem1286733 h0). Qed.
Lemma lem1286735 : term63.
Proof. exact (@lem1286734 (@lem1286713)). Qed.
Lemma lem1286736 (x : nadd) : term65 x.
Proof. exact (@lem1286735 x). Qed.
Lemma lem1286737 (x : nadd) : (term65 x) = (term62 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1286738 (x : nadd) : term62 x.
Proof. exact (EQ_MP (@lem1286737 x) (@lem1286736 x)). Qed.
Lemma lem1286739 (x : nadd) (y : nadd) : term66 x y.
Proof. exact (@lem1286738 x y). Qed.
Lemma lem1286740 (x : nadd) (y : nadd) : (term66 x y) = (term61 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1286744 (x : nadd) (y : nadd) (h1 : (term67 y x) = (nadd_eq x y)) : (term67 y x) = (nadd_eq x y).
Proof. exact (h1). Qed.
Lemma lem1286745 (x : nadd) (y : nadd) (h1 : (term67 y x) = (nadd_eq x y)) : (nadd_eq x y) = (term67 y x).
Proof. exact (SYM (@lem1286744 x y h1)). Qed.
Lemma lem1286746 (y : nadd) (x : nadd) (h1 : (nadd_eq x y) = (term67 y x)) : (nadd_eq x y) = (term67 y x).
Proof. exact (h1). Qed.
Lemma lem1286747 (y : nadd) (x : nadd) (h1 : (nadd_eq x y) = (term67 y x)) : (term67 y x) = (nadd_eq x y).
Proof. exact (SYM (@lem1286746 y x h1)). Qed.
Lemma lem1286748 (y : nadd) (x : nadd) : ((term67 y x) = (nadd_eq x y)) = ((nadd_eq x y) = (term67 y x)).
Proof. exact (prop_ext (fun h1 : (term67 y x) = (nadd_eq x y) => @lem1286745 x y h1) (fun h1 : (nadd_eq x y) = (term67 y x) => @lem1286747 y x h1)). Qed.
Lemma lem1286749 (x : nadd) : (term68 x) = (term69 x).
Proof. exact (fun_ext (fun y : nadd => @lem1286748 y x)). Qed.
Lemma lem1286750 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1286751 (x : nadd) : (term70 x) = (term71 x).
Proof. exact (MK_COMB (@lem1286750) (@lem1286749 x)). Qed.
Lemma lem1286752 : term72 = term73.
Proof. exact (fun_ext (fun x : nadd => @lem1286751 x)). Qed.
Lemma lem1286753 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1286754 : term74 = term75.
Proof. exact (MK_COMB (@lem1286753) (@lem1286752)). Qed.
Lemma lem1286755 : term75.
Proof. exact (EQ_MP (@lem1286754) (@lem1271366)). Qed.
Lemma lem1286756 (x : nadd) : term76 x.
Proof. exact (@lem1279653 x). Qed.
Lemma lem1286757 (x : nadd) : (term76 x) = (term77 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1286758 (x : nadd) : term77 x.
Proof. exact (EQ_MP (@lem1286757 x) (@lem1286756 x)). Qed.
Lemma lem1286759 (x : nadd) : (term77 x) = ((term77 x) = True).
Proof. exact (@lem7 (term77 x)). Qed.
Lemma lem1286761 (x : nadd) : term78 x.
Proof. exact (@lem1286755 x). Qed.
Lemma lem1286762 (x : nadd) : (term78 x) = (term71 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1286763 (x : nadd) : term71 x.
Proof. exact (EQ_MP (@lem1286762 x) (@lem1286761 x)). Qed.
Lemma lem1286764 (x : nadd) (y : nadd) : term79 x y.
Proof. exact (@lem1286763 x y). Qed.
Lemma lem1286765 (y : nadd) (x : nadd) : (term79 x y) = ((nadd_eq x y) = (term67 y x)).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1286767 (h1 : term80) : term80.
Proof. exact (h1). Qed.
Lemma lem1286768 (x : nadd) (h1 : term80) : term81 x.
Proof. exact (@lem1286767 h1 x). Qed.
Lemma lem1286769 (x : nadd) : (term81 x) = (term82 x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem1286770 (x : nadd) (h1 : term80) : term82 x.
Proof. exact (EQ_MP (@lem1286769 x) (@lem1286768 x h1)). Qed.
Lemma lem1286771 (x : nadd) (k : nat) (h1 : term80) : term83 x k.
Proof. exact (@lem1286770 x h1 k). Qed.
Lemma lem1286772 (k : nat) (x : nadd) : (term83 x k) = (term84 k x).
Proof. exact (eq_refl (term83 x k)). Qed.
Lemma lem1286773 (k : nat) (x : nadd) (h1 : term80) : term84 k x.
Proof. exact (EQ_MP (@lem1286772 k x) (@lem1286771 x k h1)). Qed.
Lemma lem1286774 (x : nadd) (h1 : term85 x) : term85 x.
Proof. exact (h1). Qed.
Lemma lem1286775 (k : nat) (x : nadd) (h1 : term80) (h2 : term85 x) : term86 k x.
Proof. exact (@lem1286773 k x h1 (@lem1286774 x h2)). Qed.
Lemma lem1286776 (x : nadd) (h1 : term80) (h2 : term85 x) : term87 x.
Proof. exact (fun k : nat => @lem1286775 k x h1 h2). Qed.
Lemma lem1286777 (x : nadd) (h1 : term80) : term88 x.
Proof. exact (fun h0 : term85 x => @lem1286776 x h1 h0). Qed.
Lemma lem1286778 (h1 : term80) : term89.
Proof. exact (fun x : nadd => @lem1286777 x h1). Qed.
Lemma lem1286779 : term90.
Proof. exact (fun h0 : term80 => @lem1286778 h0). Qed.
Lemma lem1286780 : term89.
Proof. exact (@lem1286779 (@lem1286557)). Qed.
Lemma lem1286781 (x : nadd) : term91 x.
Proof. exact (@lem1286780 x). Qed.
Lemma lem1286782 (x : nadd) : (term91 x) = (term88 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1286784 (k : nadd) : term92 k.
Proof. exact (@lem1273144 k). Qed.
Lemma lem1286785 (k : nadd) : (term92 k) = (term93 k).
Proof. exact (eq_refl (term92 k)). Qed.
Lemma lem1286786 (k : nadd) : term93 k.
Proof. exact (EQ_MP (@lem1286785 k) (@lem1286784 k)). Qed.
Lemma lem1286787 (k : nadd) (p : nat) (h1 : term94 k p) : term94 k p.
Proof. exact (h1). Qed.
Lemma lem1286788 {A : Type'} (P : A -> Prop) : term95 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem1286789 {A : Type'} (P : A -> Prop) : (term95 A P) = ((term96 A P) = (term97 A P)).
Proof. exact (eq_refl (term95 A P)). Qed.
Lemma lem1286791 (x : nadd) (k : nadd) : (term98 k x) = (term99 x k).
Proof. exact (@lem10568 (term100 x) (term101 x k)). Qed.
Lemma lem1286792 (k : nadd) (x : nadd) : (term99 x k) = (term98 k x).
Proof. exact (SYM (@lem1286791 x k)). Qed.
Lemma lem1286793 (x : nadd) (h1 : term85 x) : term85 x.
Proof. exact (h1). Qed.
Lemma lem1286795 {A : Type'} (P : A -> Prop) : (term96 A P) = (term97 A P).
Proof. exact (EQ_MP (@lem1286789 A P) (@lem1286788 A P)). Qed.
Lemma lem1286796 (P : nat -> Prop) : (term102 P) = (term103 P).
Proof. exact (@lem1286795 nat P). Qed.
Lemma lem1286797 (x : nadd) (k : nadd) : (term104 x k) = (term105 x k).
Proof. exact (@lem1286796 (term106 x k)). Qed.
Lemma lem1286798 (n : nat) (x : nadd) (k : nadd) : (term107 x k n) = (term108 n x k).
Proof. exact (eq_refl (term107 x k n)). Qed.
Lemma lem1286799 (x : nadd) (k : nadd) : (term109 x k) = (term106 x k).
Proof. exact (fun_ext (fun n : nat => @lem1286798 n x k)). Qed.
Lemma lem1286800 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1286801 (x : nadd) (k : nadd) : (term110 x k) = (term101 x k).
Proof. exact (MK_COMB (@lem1286800) (@lem1286799 x k)). Qed.
Lemma lem1286802 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1286803 (x : nadd) (k : nadd) : (term104 x k) = (term111 x k).
Proof. exact (MK_COMB (@lem1286802) (@lem1286801 x k)). Qed.
Lemma lem1286804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1286805 (x : nadd) (k : nadd) : (term112 x k) = (term113 x k).
Proof. exact (MK_COMB (@lem1286804) (@lem1286803 x k)). Qed.
Lemma lem1286806 (n : nat) (x : nadd) (k : nadd) : (term107 x k n) = (term108 n x k).
Proof. exact (eq_refl (term107 x k n)). Qed.
Lemma lem1286807 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1286808 (n : nat) (x : nadd) (k : nadd) : (term114 x k n) = (term115 n x k).
Proof. exact (MK_COMB (@lem1286807) (@lem1286806 n x k)). Qed.
Lemma lem1286809 (x : nadd) (k : nadd) : (term116 x k) = (term117 x k).
Proof. exact (fun_ext (fun n : nat => @lem1286808 n x k)). Qed.
Lemma lem1286810 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1286811 (x : nadd) (k : nadd) : (term105 x k) = (term118 x k).
Proof. exact (MK_COMB (@lem1286810) (@lem1286809 x k)). Qed.
Lemma lem1286812 (x : nadd) (k : nadd) : ((term104 x k) = (term105 x k)) = ((term111 x k) = (term118 x k)).
Proof. exact (MK_COMB (@lem1286805 x k) (@lem1286811 x k)). Qed.
Lemma lem1286813 (x : nadd) (k : nadd) : (term111 x k) = (term118 x k).
Proof. exact (EQ_MP (@lem1286812 x k) (@lem1286797 x k)). Qed.
Lemma lem1286818 (x : nadd) (k : nadd) : (term118 x k) = (term111 x k).
Proof. exact (SYM (@lem1286813 x k)). Qed.
Lemma lem1286822 (x : nadd) : term88 x.
Proof. exact (EQ_MP (@lem1286782 x) (@lem1286781 x)). Qed.
Lemma lem1286823 (x : nadd) (h1 : term85 x) : term87 x.
Proof. exact (@lem1286822 x (@lem1286793 x h1)). Qed.
Lemma lem1286824 (x : nadd) (h1 : term87 x) : term87 x.
Proof. exact (h1). Qed.
Lemma lem1286825 (p : nat) (x : nadd) (h1 : term87 x) : term119 x p.
Proof. exact (@lem1286824 x h1 p). Qed.
Lemma lem1286826 (p : nat) (x : nadd) : (term119 x p) = (term86 p x).
Proof. exact (eq_refl (term119 x p)). Qed.
Lemma lem1286827 (p : nat) (x : nadd) (h1 : term87 x) : term86 p x.
Proof. exact (EQ_MP (@lem1286826 p x) (@lem1286825 p x h1)). Qed.
Lemma lem1286828 (p : nat) (N : nat) (x : nadd) (h1 : term120 p N x) : term120 p N x.
Proof. exact (h1). Qed.
Lemma lem1286829 (N : nat) (x : nadd) (k : nadd) (h1 : term121 N x k) : term121 N x k.
Proof. exact (h1). Qed.
Lemma lem1286831 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1286832 (x : nadd) : (term122 x) = (term123 x).
Proof. exact (@lem1286831 (term85 x)). Qed.
Lemma lem1286834 (t : Prop) : (term124 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1286835 (x : nadd) : (term123 x) = (term100 x).
Proof. exact (@lem1286834 (term100 x)). Qed.
Lemma lem1286837 (y : nadd) (x : nadd) : (nadd_eq x y) = (term67 y x).
Proof. exact (EQ_MP (@lem1286765 y x) (@lem1286764 x y)). Qed.
Lemma lem1286838 (x : nadd) : (term100 x) = (term125 x).
Proof. exact (@lem1286837 term126 x). Qed.
Lemma lem1286841 (x : nadd) : (term123 x) = (term125 x).
Proof. exact (TRANS (@lem1286835 x) (@lem1286838 x)). Qed.
Lemma lem1286842 (x : nadd) : (term122 x) = (term125 x).
Proof. exact (TRANS (@lem1286832 x) (@lem1286841 x)). Qed.
Lemma lem1286844 (x : nadd) : (term77 x) = True.
Proof. exact (EQ_MP (@lem1286759 x) (@lem1286758 x)). Qed.
Lemma lem1286845 (x : nadd) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1286846 (x : nadd) : (term125 x) = (term128 x).
Proof. exact (MK_COMB (@lem1286845 x) (@lem1286844 x)). Qed.
Lemma lem1286848 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1286849 (x : nadd) : (term128 x) = (term129 x).
Proof. exact (@lem1286848 (term129 x)). Qed.
Lemma lem1286850 (x : nadd) : (term125 x) = (term129 x).
Proof. exact (TRANS (@lem1286846 x) (@lem1286849 x)). Qed.
Lemma lem1286851 (x : nadd) : (term122 x) = (term129 x).
Proof. exact (TRANS (@lem1286842 x) (@lem1286850 x)). Qed.
Lemma lem1286852 (x : nadd) : (term129 x) = (term122 x).
Proof. exact (SYM (@lem1286851 x)). Qed.
Lemma lem1286854 (x : nadd) (y : nadd) : term61 x y.
Proof. exact (EQ_MP (@lem1286740 x y) (@lem1286739 x y)). Qed.
Lemma lem1286855 (x : nadd) : term130 x.
Proof. exact (@lem1286854 x term126). Qed.
Lemma lem1286857 (x : nadd) (z : nadd) : term38 x z.
Proof. exact (EQ_MP (@lem1286696 x z) (@lem1286695 x z)). Qed.
Lemma lem1286858 (N : nat) (x : nadd) : term131 N x.
Proof. exact (@lem1286857 (term132 N x) (term133 N x)). Qed.
Lemma lem1286859 (N : nat) (x : nadd) (h1 : term134 N x) : term134 N x.
Proof. exact (h1). Qed.
Lemma lem1286861 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1286668 n m) (@lem1286667 m n)). Qed.
Lemma lem1286862 (N : nat) : (term135 N) = (term136 N).
Proof. exact (@lem1286861 term137 N). Qed.
Lemma lem1286863 : nadd_of_num = nadd_of_num.
Proof. exact (eq_refl nadd_of_num). Qed.
Lemma lem1286864 (N : nat) : (term138 N) = (term139 N).
Proof. exact (MK_COMB (@lem1286863) (@lem1286862 N)). Qed.
Lemma lem1286865 : nadd_mul = nadd_mul.
Proof. exact (eq_refl nadd_mul). Qed.
Lemma lem1286866 (N : nat) : (term140 N) = (term141 N).
Proof. exact (MK_COMB (@lem1286865) (@lem1286864 N)). Qed.
Lemma lem1286867 (x : nadd) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1286868 (N : nat) (x : nadd) : (term142 N x) = (term143 N x).
Proof. exact (MK_COMB (@lem1286866 N) (@lem1286867 x)). Qed.
Lemma lem1286869 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1286870 (N : nat) (x : nadd) : (term144 N x) = (term145 N x).
Proof. exact (MK_COMB (@lem1286869) (@lem1286868 N x)). Qed.
Lemma lem1286871 (N : nat) (x : nadd) : (term132 N x) = (term132 N x).
Proof. exact (eq_refl (term132 N x)). Qed.
Lemma lem1286872 (N : nat) (x : nadd) : (term134 N x) = (term146 N x).
Proof. exact (MK_COMB (@lem1286870 N x) (@lem1286871 N x)). Qed.
Lemma lem1286873 (N : nat) (x : nadd) : (term146 N x) = (term134 N x).
Proof. exact (SYM (@lem1286872 N x)). Qed.
Lemma lem1286875 (x : nadd) (z : nadd) : term18 x z.
Proof. exact (EQ_MP (@lem1286662 x z) (@lem1286661 x z)). Qed.
Lemma lem1286876 (N : nat) (x : nadd) : term147 N x.
Proof. exact (@lem1286875 (term143 N x) (term132 N x)). Qed.
Lemma lem1286878 (x : nadd) (z : nadd) : term18 x z.
Proof. exact (EQ_MP (@lem1286634 x z) (@lem1286633 x z)). Qed.
Lemma lem1286879 (N : nat) (x : nadd) : term148 N x.
Proof. exact (@lem1286878 (term143 N x) (term149 N x)). Qed.
Lemma lem1286881 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1286882 (N : nat) (x : nadd) : (term151 N x) = (term152 N x).
Proof. exact (@lem1286881 (term151 N x)). Qed.
Lemma lem1286883 (N : nat) (x : nadd) : (term152 N x) = (term151 N x).
Proof. exact (SYM (@lem1286882 N x)). Qed.
Lemma lem1286884 (N : nat) (x : nadd) (h1 : term153 N x) : term153 N x.
Proof. exact (h1). Qed.
Lemma lem1286887 (N : nat) (x : nadd) (h1 : term154 N x) : term154 N x.
Proof. exact (h1). Qed.
Lemma lem1286888 (N : nat) (x : nadd) : term155 N x.
Proof. exact (fun h0 : term154 N x => @lem1286887 N x h0). Qed.
Lemma lem1286889 (N : nat) (x : nadd) (h1 : term155 N x) : term155 N x.
Proof. exact (h1). Qed.
Lemma lem1286890 (N : nat) (x : nadd) (h1 : term154 N x) : term154 N x.
Proof. exact (h1). Qed.
Lemma lem1286891 (N : nat) (x : nadd) (h1 : term154 N x) (h2 : term155 N x) : term154 N x.
Proof. exact (@lem1286889 N x h2 (@lem1286890 N x h1)). Qed.
Lemma lem1286892 (N : nat) (x : nadd) (h1 : term154 N x) : term156 N x.
Proof. exact (fun h0 : term155 N x => @lem1286891 N x h1 h0). Qed.
Lemma lem1286893 (N : nat) (x : nadd) (h1 : term155 N x) : term155 N x.
Proof. exact (h1). Qed.
Lemma lem1286894 (N : nat) (x : nadd) (h1 : term154 N x) (h2 : term155 N x) : term154 N x.
Proof. exact (@lem1286892 N x h1 (@lem1286893 N x h2)). Qed.
Lemma lem1286895 (N : nat) (x : nadd) (h1 : term155 N x) : term155 N x.
Proof. exact (fun h0 : term154 N x => @lem1286894 N x h0 h1). Qed.
Lemma lem1286896 (N : nat) (x : nadd) : term157 N x.
Proof. exact (fun h0 : term155 N x => @lem1286895 N x h0). Qed.
Lemma lem1286899 (N : nat) (x : nadd) : term155 N x.
Proof. exact (@lem1286896 N x (@lem1286888 N x)). Qed.
Lemma lem1286949 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1286950 : term158 = term159.
Proof. exact (@lem1286949 term160). Qed.
Lemma lem1286959 : term161 = term161.
Proof. exact (eq_refl term161). Qed.
Lemma lem1286960 : term162 = term163.
Proof. exact (MK_COMB (@lem1286959) (@lem1286950)). Qed.
Lemma lem1286963 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem1286964 : term165 = term166.
Proof. exact (MK_COMB (@lem1286963) (@lem1286960)). Qed.
Lemma lem1286967 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem1286968 : term168 = term169.
Proof. exact (MK_COMB (@lem1286967) (@lem1286964)). Qed.
Lemma lem1286971 (N : nat) (x : nadd) : (term170 N x) = (term170 N x).
Proof. exact (eq_refl (term170 N x)). Qed.
Lemma lem1286972 (N : nat) (x : nadd) : (term154 N x) = (term171 N x).
Proof. exact (MK_COMB (@lem1286971 N x) (@lem1286968)). Qed.
Lemma lem1286975 (x : nadd) : (term172 x) = (term173 x).
Proof. exact (fun_ext (fun N : nat => @lem1286972 N x)). Qed.
Lemma lem1286976 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1286977 (x : nadd) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1286976) (@lem1286975 x)). Qed.
Lemma lem1286982 : term176 = term177.
Proof. exact (fun_ext (fun x : nadd => @lem1286977 x)). Qed.
Lemma lem1286983 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1286992 : term178 = term179.
Proof. exact (MK_COMB (@lem1286983) (@lem1286982)). Qed.
Lemma lem1286993 (m : nat) (n : nat) : (term180 m n) = (term180 m n).
Proof. exact (eq_refl (term180 m n)). Qed.
Lemma lem1286994 (m : nat) : (term181 m) = (term181 m).
Proof. exact (fun_ext (fun n : nat => @lem1286993 m n)). Qed.
Lemma lem1286995 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1286996 (m : nat) : (term182 m) = (term182 m).
Proof. exact (MK_COMB (@lem1286995) (@lem1286994 m)). Qed.
Lemma lem1286997 : term183 = term183.
Proof. exact (fun_ext (fun m : nat => @lem1286996 m)). Qed.
Lemma lem1286998 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1286999 : term160 = term160.
Proof. exact (MK_COMB (@lem1286998) (@lem1286997)). Qed.
Lemma lem1287000 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1287001 : term159 = term159.
Proof. exact (MK_COMB (@lem1287000) (@lem1286999)). Qed.
Lemma lem1287010 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term184 x y x' y') = (term184 x y x' y').
Proof. exact (eq_refl (term184 x y x' y')). Qed.
Lemma lem1287011 (x : nadd) (y : nadd) (x' : nadd) : (term185 x y x') = (term185 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1287010 x y x' y')). Qed.
Lemma lem1287012 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287013 (x : nadd) (y : nadd) (x' : nadd) : (term186 x y x') = (term186 x y x').
Proof. exact (MK_COMB (@lem1287012) (@lem1287011 x y x')). Qed.
Lemma lem1287014 (x : nadd) (x' : nadd) : (term187 x x') = (term187 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1287013 x y x')). Qed.
Lemma lem1287015 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287016 (x : nadd) (x' : nadd) : (term188 x x') = (term188 x x').
Proof. exact (MK_COMB (@lem1287015) (@lem1287014 x x')). Qed.
Lemma lem1287017 (x : nadd) : (term189 x) = (term189 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1287016 x x')). Qed.
Lemma lem1287018 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287019 (x : nadd) : (term190 x) = (term190 x).
Proof. exact (MK_COMB (@lem1287018) (@lem1287017 x)). Qed.
Lemma lem1287020 : term191 = term191.
Proof. exact (fun_ext (fun x : nadd => @lem1287019 x)). Qed.
Lemma lem1287021 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287022 : term192 = term192.
Proof. exact (MK_COMB (@lem1287021) (@lem1287020)). Qed.
Lemma lem1287023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1287024 : term161 = term161.
Proof. exact (MK_COMB (@lem1287023) (@lem1287022)). Qed.
Lemma lem1287025 : term163 = term163.
Proof. exact (MK_COMB (@lem1287024) (@lem1287001)). Qed.
Lemma lem1287026 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1287027 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1287026 x)). Qed.
Lemma lem1287028 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287029 : term194 = term194.
Proof. exact (MK_COMB (@lem1287028) (@lem1287027)). Qed.
Lemma lem1287030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1287031 : term164 = term164.
Proof. exact (MK_COMB (@lem1287030) (@lem1287029)). Qed.
Lemma lem1287032 : term166 = term166.
Proof. exact (MK_COMB (@lem1287031) (@lem1287025)). Qed.
Lemma lem1287037 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl ((nadd_eq x y) = (nadd_eq y x))). Qed.
Lemma lem1287038 (x : nadd) : (term195 x) = (term195 x).
Proof. exact (fun_ext (fun y : nadd => @lem1287037 y x)). Qed.
Lemma lem1287039 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287040 (x : nadd) : (term196 x) = (term196 x).
Proof. exact (MK_COMB (@lem1287039) (@lem1287038 x)). Qed.
Lemma lem1287041 : term197 = term197.
Proof. exact (fun_ext (fun x : nadd => @lem1287040 x)). Qed.
Lemma lem1287042 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287043 : term198 = term198.
Proof. exact (MK_COMB (@lem1287042) (@lem1287041)). Qed.
Lemma lem1287044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1287045 : term167 = term167.
Proof. exact (MK_COMB (@lem1287044) (@lem1287043)). Qed.
Lemma lem1287046 : term169 = term169.
Proof. exact (MK_COMB (@lem1287045) (@lem1287032)). Qed.
Lemma lem1287051 (N : nat) (x : nadd) : (term170 N x) = (term170 N x).
Proof. exact (eq_refl (term170 N x)). Qed.
Lemma lem1287052 (N : nat) (x : nadd) : (term171 N x) = (term171 N x).
Proof. exact (MK_COMB (@lem1287051 N x) (@lem1287046)). Qed.
Lemma lem1287053 (x : nadd) : (term173 x) = (term173 x).
Proof. exact (fun_ext (fun N : nat => @lem1287052 N x)). Qed.
Lemma lem1287054 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1287055 (x : nadd) : (term175 x) = (term175 x).
Proof. exact (MK_COMB (@lem1287054) (@lem1287053 x)). Qed.
Lemma lem1287056 : term177 = term177.
Proof. exact (fun_ext (fun x : nadd => @lem1287055 x)). Qed.
Lemma lem1287057 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287058 : term179 = term179.
Proof. exact (MK_COMB (@lem1287057) (@lem1287056)). Qed.
Lemma lem1287139 : term178 = term179.
Proof. exact (TRANS (@lem1286992) (@lem1287058)). Qed.
Lemma lem1287140 : term179 = term178.
Proof. exact (SYM (@lem1287139)). Qed.
Lemma lem1287142 (h1 : term198) : term198.
Proof. exact (h1). Qed.
Lemma lem1287143 (h1 : term194) : term194.
Proof. exact (h1). Qed.
Lemma lem1287144 (h1 : term192) : term192.
Proof. exact (h1). Qed.
Lemma lem1287145 (h1 : term160) : term160.
Proof. exact (h1). Qed.
Lemma lem1287151 (N : nat) (x : nadd) (h1 : term153 N x) : term153 N x.
Proof. exact (h1). Qed.
Lemma lem1287166 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = (term199 y x).
Proof. exact (@lem17784 (nadd_eq x y) (nadd_eq y x)). Qed.
Lemma lem1287167 (x : nadd) : (term195 x) = (term200 x).
Proof. exact (fun_ext (fun y : nadd => @lem1287166 y x)). Qed.
Lemma lem1287168 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287169 (x : nadd) : (term196 x) = (term201 x).
Proof. exact (MK_COMB (@lem1287168) (@lem1287167 x)). Qed.
Lemma lem1287170 : term197 = term202.
Proof. exact (fun_ext (fun x : nadd => @lem1287169 x)). Qed.
Lemma lem1287171 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287172 : term198 = term203.
Proof. exact (MK_COMB (@lem1287171) (@lem1287170)). Qed.
Lemma lem1287178 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1287179 (P : nadd -> Prop) (Q : nadd -> Prop) : (term206 P Q) = (term207 P Q).
Proof. exact (@lem1287178 nadd P Q). Qed.
Lemma lem1287180 (x : nadd) : (term208 x) = (term209 x).
Proof. exact (@lem1287179 (term210 x) (term211 x)). Qed.
Lemma lem1287181 (y : nadd) (x : nadd) : (term212 x y) = (term213 y x).
Proof. exact (eq_refl (term212 x y)). Qed.
Lemma lem1287182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1287183 (y : nadd) (x : nadd) : (term214 x y) = (term215 y x).
Proof. exact (MK_COMB (@lem1287182) (@lem1287181 y x)). Qed.
Lemma lem1287184 (y : nadd) (x : nadd) : (term216 x y) = (term217 y x).
Proof. exact (eq_refl (term216 x y)). Qed.
Lemma lem1287185 (y : nadd) (x : nadd) : (term218 x y) = (term199 y x).
Proof. exact (MK_COMB (@lem1287183 y x) (@lem1287184 y x)). Qed.
Lemma lem1287186 (x : nadd) : (term219 x) = (term200 x).
Proof. exact (fun_ext (fun y : nadd => @lem1287185 y x)). Qed.
Lemma lem1287187 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287188 (x : nadd) : (term208 x) = (term201 x).
Proof. exact (MK_COMB (@lem1287187) (@lem1287186 x)). Qed.
Lemma lem1287189 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1287190 (x : nadd) : (term220 x) = (term221 x).
Proof. exact (MK_COMB (@lem1287189) (@lem1287188 x)). Qed.
Lemma lem1287191 (y : nadd) (x : nadd) : (term212 x y) = (term213 y x).
Proof. exact (eq_refl (term212 x y)). Qed.
Lemma lem1287192 (x : nadd) : (term222 x) = (term210 x).
Proof. exact (fun_ext (fun y : nadd => @lem1287191 y x)). Qed.
Lemma lem1287193 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287194 (x : nadd) : (term223 x) = (term224 x).
Proof. exact (MK_COMB (@lem1287193) (@lem1287192 x)). Qed.
Lemma lem1287195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1287196 (x : nadd) : (term225 x) = (term226 x).
Proof. exact (MK_COMB (@lem1287195) (@lem1287194 x)). Qed.
Lemma lem1287197 (y : nadd) (x : nadd) : (term216 x y) = (term217 y x).
Proof. exact (eq_refl (term216 x y)). Qed.
Lemma lem1287198 (x : nadd) : (term227 x) = (term211 x).
Proof. exact (fun_ext (fun y : nadd => @lem1287197 y x)). Qed.
Lemma lem1287199 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287200 (x : nadd) : (term228 x) = (term229 x).
Proof. exact (MK_COMB (@lem1287199) (@lem1287198 x)). Qed.
Lemma lem1287201 (x : nadd) : (term209 x) = (term230 x).
Proof. exact (MK_COMB (@lem1287196 x) (@lem1287200 x)). Qed.
Lemma lem1287202 (x : nadd) : ((term208 x) = (term209 x)) = ((term201 x) = (term230 x)).
Proof. exact (MK_COMB (@lem1287190 x) (@lem1287201 x)). Qed.
Lemma lem1287203 (x : nadd) : (term201 x) = (term230 x).
Proof. exact (EQ_MP (@lem1287202 x) (@lem1287180 x)). Qed.
Lemma lem1287300 : term202 = term231.
Proof. exact (fun_ext (fun x : nadd => @lem1287203 x)). Qed.
Lemma lem1287301 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287302 : term203 = term232.
Proof. exact (MK_COMB (@lem1287301) (@lem1287300)). Qed.
Lemma lem1287304 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1287305 (P : nadd -> Prop) (Q : nadd -> Prop) : (term206 P Q) = (term207 P Q).
Proof. exact (@lem1287304 nadd P Q). Qed.
Lemma lem1287306 : term233 = term234.
Proof. exact (@lem1287305 term235 term236). Qed.
Lemma lem1287307 (x : nadd) : (term237 x) = (term224 x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem1287308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1287309 (x : nadd) : (term238 x) = (term226 x).
Proof. exact (MK_COMB (@lem1287308) (@lem1287307 x)). Qed.
Lemma lem1287310 (x : nadd) : (term239 x) = (term229 x).
Proof. exact (eq_refl (term239 x)). Qed.
Lemma lem1287311 (x : nadd) : (term240 x) = (term230 x).
Proof. exact (MK_COMB (@lem1287309 x) (@lem1287310 x)). Qed.
Lemma lem1287312 : term241 = term231.
Proof. exact (fun_ext (fun x : nadd => @lem1287311 x)). Qed.
Lemma lem1287313 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287314 : term233 = term232.
Proof. exact (MK_COMB (@lem1287313) (@lem1287312)). Qed.
Lemma lem1287315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1287316 : term242 = term243.
Proof. exact (MK_COMB (@lem1287315) (@lem1287314)). Qed.
Lemma lem1287317 (x : nadd) : (term237 x) = (term224 x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem1287318 : term244 = term235.
Proof. exact (fun_ext (fun x : nadd => @lem1287317 x)). Qed.
Lemma lem1287319 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287320 : term245 = term246.
Proof. exact (MK_COMB (@lem1287319) (@lem1287318)). Qed.
Lemma lem1287321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1287322 : term247 = term248.
Proof. exact (MK_COMB (@lem1287321) (@lem1287320)). Qed.
Lemma lem1287323 (x : nadd) : (term239 x) = (term229 x).
Proof. exact (eq_refl (term239 x)). Qed.
Lemma lem1287324 : term249 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1287323 x)). Qed.
Lemma lem1287325 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287326 : term250 = term251.
Proof. exact (MK_COMB (@lem1287325) (@lem1287324)). Qed.
Lemma lem1287327 : term234 = term252.
Proof. exact (MK_COMB (@lem1287322) (@lem1287326)). Qed.
Lemma lem1287328 : (term233 = term234) = (term232 = term252).
Proof. exact (MK_COMB (@lem1287316) (@lem1287327)). Qed.
Lemma lem1287329 : term232 = term252.
Proof. exact (EQ_MP (@lem1287328) (@lem1287306)). Qed.
Lemma lem1287436 : term203 = term252.
Proof. exact (TRANS (@lem1287302) (@lem1287329)). Qed.
Lemma lem1287437 : term198 = term252.
Proof. exact (TRANS (@lem1287172) (@lem1287436)). Qed.
Lemma lem1287438 (h1 : term198) : term252.
Proof. exact (EQ_MP (@lem1287437) (@lem1287142 h1)). Qed.
Lemma lem1287439 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1287440 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1287439 x)). Qed.
Lemma lem1287441 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287450 : term194 = term194.
Proof. exact (MK_COMB (@lem1287441) (@lem1287440)). Qed.
Lemma lem1287451 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1287450) (@lem1287143 h1)). Qed.
Lemma lem1287458 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term253 x x' y y') = (term254 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1287459 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term255 x y x' y') = (term255 x y x' y').
Proof. exact (eq_refl (term255 x y x' y')). Qed.
Lemma lem1287460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1287461 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term256 x x' y y') = (term257 x x' y y').
Proof. exact (MK_COMB (@lem1287460) (@lem1287458 x x' y y')). Qed.
Lemma lem1287462 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term258 x y x' y') = (term259 x y x' y').
Proof. exact (MK_COMB (@lem1287461 x x' y y') (@lem1287459 x y x' y')). Qed.
Lemma lem1287463 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term184 x y x' y') = (term258 x y x' y').
Proof. exact (@lem17265 (term260 x x' y y') (term255 x y x' y')). Qed.
Lemma lem1287464 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term184 x y x' y') = (term259 x y x' y').
Proof. exact (TRANS (@lem1287463 x y x' y') (@lem1287462 x y x' y')). Qed.
Lemma lem1287465 (x : nadd) (y : nadd) (x' : nadd) : (term185 x y x') = (term261 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1287464 x y x' y')). Qed.
Lemma lem1287466 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287467 (x : nadd) (y : nadd) (x' : nadd) : (term186 x y x') = (term262 x y x').
Proof. exact (MK_COMB (@lem1287466) (@lem1287465 x y x')). Qed.
Lemma lem1287468 (x : nadd) (x' : nadd) : (term187 x x') = (term263 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1287467 x y x')). Qed.
Lemma lem1287469 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287470 (x : nadd) (x' : nadd) : (term188 x x') = (term264 x x').
Proof. exact (MK_COMB (@lem1287469) (@lem1287468 x x')). Qed.
Lemma lem1287471 (x : nadd) : (term189 x) = (term265 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1287470 x x')). Qed.
Lemma lem1287472 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287473 (x : nadd) : (term190 x) = (term266 x).
Proof. exact (MK_COMB (@lem1287472) (@lem1287471 x)). Qed.
Lemma lem1287474 : term191 = term267.
Proof. exact (fun_ext (fun x : nadd => @lem1287473 x)). Qed.
Lemma lem1287475 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287540 : term192 = term268.
Proof. exact (MK_COMB (@lem1287475) (@lem1287474)). Qed.
Lemma lem1287541 (h1 : term192) : term268.
Proof. exact (EQ_MP (@lem1287540) (@lem1287144 h1)). Qed.
Lemma lem1287542 (m : nat) (n : nat) : (term180 m n) = (term180 m n).
Proof. exact (eq_refl (term180 m n)). Qed.
Lemma lem1287543 (m : nat) : (term181 m) = (term181 m).
Proof. exact (fun_ext (fun n : nat => @lem1287542 m n)). Qed.
Lemma lem1287544 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1287545 (m : nat) : (term182 m) = (term182 m).
Proof. exact (MK_COMB (@lem1287544) (@lem1287543 m)). Qed.
Lemma lem1287546 : term183 = term183.
Proof. exact (fun_ext (fun m : nat => @lem1287545 m)). Qed.
Lemma lem1287547 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1287560 : term160 = term160.
Proof. exact (MK_COMB (@lem1287547) (@lem1287546)). Qed.
Lemma lem1287561 (h1 : term160) : term160.
Proof. exact (EQ_MP (@lem1287560) (@lem1287145 h1)). Qed.
Lemma lem1287599 (N : nat) (x : nadd) (h1 : term153 N x) : term153 N x.
Proof. exact (h1). Qed.
Lemma lem1287614 (y : nadd) (x : nadd) : (term217 y x) = (term217 y x).
Proof. exact (eq_refl (term217 y x)). Qed.
Lemma lem1287615 (x : nadd) : (term211 x) = (term211 x).
Proof. exact (fun_ext (fun y : nadd => @lem1287614 y x)). Qed.
Lemma lem1287616 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287617 (x : nadd) : (term229 x) = (term229 x).
Proof. exact (MK_COMB (@lem1287616) (@lem1287615 x)). Qed.
Lemma lem1287618 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1287617 x)). Qed.
Lemma lem1287619 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287620 : term251 = term251.
Proof. exact (MK_COMB (@lem1287619) (@lem1287618)). Qed.
Lemma lem1287635 (y : nadd) (x : nadd) : (term213 y x) = (term213 y x).
Proof. exact (eq_refl (term213 y x)). Qed.
Lemma lem1287636 (x : nadd) : (term210 x) = (term210 x).
Proof. exact (fun_ext (fun y : nadd => @lem1287635 y x)). Qed.
Lemma lem1287637 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287638 (x : nadd) : (term224 x) = (term224 x).
Proof. exact (MK_COMB (@lem1287637) (@lem1287636 x)). Qed.
Lemma lem1287639 : term235 = term235.
Proof. exact (fun_ext (fun x : nadd => @lem1287638 x)). Qed.
Lemma lem1287640 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287641 : term246 = term246.
Proof. exact (MK_COMB (@lem1287640) (@lem1287639)). Qed.
Lemma lem1287642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1287643 : term248 = term248.
Proof. exact (MK_COMB (@lem1287642) (@lem1287641)). Qed.
Lemma lem1287644 : term252 = term252.
Proof. exact (MK_COMB (@lem1287643) (@lem1287620)). Qed.
Lemma lem1287645 (h1 : term198) : term252.
Proof. exact (EQ_MP (@lem1287644) (@lem1287438 h1)). Qed.
Lemma lem1287650 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1287651 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1287650 x)). Qed.
Lemma lem1287652 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287653 : term194 = term194.
Proof. exact (MK_COMB (@lem1287652) (@lem1287651)). Qed.
Lemma lem1287654 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1287653) (@lem1287451 h1)). Qed.
Lemma lem1287687 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term259 x y x' y') = (term259 x y x' y').
Proof. exact (eq_refl (term259 x y x' y')). Qed.
Lemma lem1287688 (x : nadd) (y : nadd) (x' : nadd) : (term261 x y x') = (term261 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1287687 x y x' y')). Qed.
Lemma lem1287689 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287690 (x : nadd) (y : nadd) (x' : nadd) : (term262 x y x') = (term262 x y x').
Proof. exact (MK_COMB (@lem1287689) (@lem1287688 x y x')). Qed.
Lemma lem1287691 (x : nadd) (x' : nadd) : (term263 x x') = (term263 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1287690 x y x')). Qed.
Lemma lem1287692 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287693 (x : nadd) (x' : nadd) : (term264 x x') = (term264 x x').
Proof. exact (MK_COMB (@lem1287692) (@lem1287691 x x')). Qed.
Lemma lem1287694 (x : nadd) : (term265 x) = (term265 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1287693 x x')). Qed.
Lemma lem1287695 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287696 (x : nadd) : (term266 x) = (term266 x).
Proof. exact (MK_COMB (@lem1287695) (@lem1287694 x)). Qed.
Lemma lem1287697 : term267 = term267.
Proof. exact (fun_ext (fun x : nadd => @lem1287696 x)). Qed.
Lemma lem1287698 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287699 : term268 = term268.
Proof. exact (MK_COMB (@lem1287698) (@lem1287697)). Qed.
Lemma lem1287700 (h1 : term192) : term268.
Proof. exact (EQ_MP (@lem1287699) (@lem1287541 h1)). Qed.
Lemma lem1287719 (m : nat) (n : nat) : (term180 m n) = (term180 m n).
Proof. exact (eq_refl (term180 m n)). Qed.
Lemma lem1287720 (m : nat) : (term181 m) = (term181 m).
Proof. exact (fun_ext (fun n : nat => @lem1287719 m n)). Qed.
Lemma lem1287721 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1287722 (m : nat) : (term182 m) = (term182 m).
Proof. exact (MK_COMB (@lem1287721) (@lem1287720 m)). Qed.
Lemma lem1287723 : term183 = term183.
Proof. exact (fun_ext (fun m : nat => @lem1287722 m)). Qed.
Lemma lem1287724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1287725 : term160 = term160.
Proof. exact (MK_COMB (@lem1287724) (@lem1287723)). Qed.
Lemma lem1287726 (h1 : term160) : term160.
Proof. exact (EQ_MP (@lem1287725) (@lem1287561 h1)). Qed.
Lemma lem1287727 (h1 : term198) : term251.
Proof. exact (proj2 (@lem1287645 h1)). Qed.
Lemma lem1287732 (N : nat) (x : nadd) (h1 : term153 N x) : term153 N x.
Proof. exact (h1). Qed.
Lemma lem1287734 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1287735 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1287734 x)). Qed.
Lemma lem1287736 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287738 : term194 = term194.
Proof. exact (MK_COMB (@lem1287736) (@lem1287735)). Qed.
Lemma lem1287739 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1287738) (@lem1287654 h1)). Qed.
Lemma lem1287753 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term259 x y x' y') = (term259 x y x' y').
Proof. exact (eq_refl (term259 x y x' y')). Qed.
Lemma lem1287754 (x : nadd) (y : nadd) (x' : nadd) : (term261 x y x') = (term261 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1287753 x y x' y')). Qed.
Lemma lem1287755 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287756 (x : nadd) (y : nadd) (x' : nadd) : (term262 x y x') = (term262 x y x').
Proof. exact (MK_COMB (@lem1287755) (@lem1287754 x y x')). Qed.
Lemma lem1287757 (x : nadd) (x' : nadd) : (term263 x x') = (term263 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1287756 x y x')). Qed.
Lemma lem1287758 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287759 (x : nadd) (x' : nadd) : (term264 x x') = (term264 x x').
Proof. exact (MK_COMB (@lem1287758) (@lem1287757 x x')). Qed.
Lemma lem1287760 (x : nadd) : (term265 x) = (term265 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1287759 x x')). Qed.
Lemma lem1287761 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287762 (x : nadd) : (term266 x) = (term266 x).
Proof. exact (MK_COMB (@lem1287761) (@lem1287760 x)). Qed.
Lemma lem1287763 : term267 = term267.
Proof. exact (fun_ext (fun x : nadd => @lem1287762 x)). Qed.
Lemma lem1287764 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287766 : term268 = term268.
Proof. exact (MK_COMB (@lem1287764) (@lem1287763)). Qed.
Lemma lem1287767 (h1 : term192) : term268.
Proof. exact (EQ_MP (@lem1287766) (@lem1287700 h1)). Qed.
Lemma lem1287769 (m : nat) (n : nat) : (term180 m n) = (term180 m n).
Proof. exact (eq_refl (term180 m n)). Qed.
Lemma lem1287770 (m : nat) : (term181 m) = (term181 m).
Proof. exact (fun_ext (fun n : nat => @lem1287769 m n)). Qed.
Lemma lem1287771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1287772 (m : nat) : (term182 m) = (term182 m).
Proof. exact (MK_COMB (@lem1287771) (@lem1287770 m)). Qed.
Lemma lem1287773 : term183 = term183.
Proof. exact (fun_ext (fun m : nat => @lem1287772 m)). Qed.
Lemma lem1287774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1287776 : term160 = term160.
Proof. exact (MK_COMB (@lem1287774) (@lem1287773)). Qed.
Lemma lem1287777 (h1 : term160) : term160.
Proof. exact (EQ_MP (@lem1287776) (@lem1287726 h1)). Qed.
Lemma lem1287801 (y : nadd) (x : nadd) : (term217 y x) = (term217 y x).
Proof. exact (eq_refl (term217 y x)). Qed.
Lemma lem1287802 (x : nadd) : (term211 x) = (term211 x).
Proof. exact (fun_ext (fun y : nadd => @lem1287801 y x)). Qed.
Lemma lem1287803 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287804 (x : nadd) : (term229 x) = (term229 x).
Proof. exact (MK_COMB (@lem1287803) (@lem1287802 x)). Qed.
Lemma lem1287805 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1287804 x)). Qed.
Lemma lem1287806 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1287808 : term251 = term251.
Proof. exact (MK_COMB (@lem1287806) (@lem1287805)). Qed.
Lemma lem1287809 (h1 : term198) : term251.
Proof. exact (EQ_MP (@lem1287808) (@lem1287727 h1)). Qed.
Lemma lem1287810 (_23260 : nadd) (h1 : term194) : term269 _23260.
Proof. exact (@lem1287739 h1 _23260). Qed.
Lemma lem1287811 (_23260 : nadd) : (term269 _23260) = (nadd_eq _23260 _23260).
Proof. exact (eq_refl (term269 _23260)). Qed.
Lemma lem1287813 (_23261 : nadd) (h1 : term192) : term270 _23261.
Proof. exact (@lem1287767 h1 _23261). Qed.
Lemma lem1287814 (_23261 : nadd) : (term270 _23261) = (term266 _23261).
Proof. exact (eq_refl (term270 _23261)). Qed.
Lemma lem1287815 (_23261 : nadd) (h1 : term192) : term266 _23261.
Proof. exact (EQ_MP (@lem1287814 _23261) (@lem1287813 _23261 h1)). Qed.
Lemma lem1287816 (_23261 : nadd) (_23262 : nadd) (h1 : term192) : term271 _23261 _23262.
Proof. exact (@lem1287815 _23261 h1 _23262). Qed.
Lemma lem1287817 (_23261 : nadd) (_23262 : nadd) : (term271 _23261 _23262) = (term264 _23261 _23262).
Proof. exact (eq_refl (term271 _23261 _23262)). Qed.
Lemma lem1287818 (_23261 : nadd) (_23262 : nadd) (h1 : term192) : term264 _23261 _23262.
Proof. exact (EQ_MP (@lem1287817 _23261 _23262) (@lem1287816 _23261 _23262 h1)). Qed.
Lemma lem1287819 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (h1 : term192) : term272 _23261 _23262 _23263.
Proof. exact (@lem1287818 _23261 _23262 h1 _23263). Qed.
Lemma lem1287820 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) : (term272 _23261 _23262 _23263) = (term262 _23261 _23263 _23262).
Proof. exact (eq_refl (term272 _23261 _23262 _23263)). Qed.
Lemma lem1287821 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (h1 : term192) : term262 _23261 _23263 _23262.
Proof. exact (EQ_MP (@lem1287820 _23261 _23263 _23262) (@lem1287819 _23261 _23262 _23263 h1)). Qed.
Lemma lem1287822 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) (h1 : term192) : term273 _23261 _23263 _23262 _23264.
Proof. exact (@lem1287821 _23261 _23263 _23262 h1 _23264). Qed.
Lemma lem1287823 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) : (term273 _23261 _23263 _23262 _23264) = (term259 _23261 _23263 _23262 _23264).
Proof. exact (eq_refl (term273 _23261 _23263 _23262 _23264)). Qed.
Lemma lem1287824 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) (h1 : term192) : term259 _23261 _23263 _23262 _23264.
Proof. exact (EQ_MP (@lem1287823 _23261 _23263 _23262 _23264) (@lem1287822 _23261 _23263 _23262 _23264 h1)). Qed.
Lemma lem1287825 (_23265 : nat) (h1 : term160) : term274 _23265.
Proof. exact (@lem1287777 h1 _23265). Qed.
Lemma lem1287826 (_23265 : nat) : (term274 _23265) = (term182 _23265).
Proof. exact (eq_refl (term274 _23265)). Qed.
Lemma lem1287827 (_23265 : nat) (h1 : term160) : term182 _23265.
Proof. exact (EQ_MP (@lem1287826 _23265) (@lem1287825 _23265 h1)). Qed.
Lemma lem1287828 (_23265 : nat) (_23266 : nat) (h1 : term160) : term275 _23265 _23266.
Proof. exact (@lem1287827 _23265 h1 _23266). Qed.
Lemma lem1287829 (_23265 : nat) (_23266 : nat) : (term275 _23265 _23266) = (term180 _23265 _23266).
Proof. exact (eq_refl (term275 _23265 _23266)). Qed.
Lemma lem1287837 (_23269 : nadd) (h1 : term198) : term239 _23269.
Proof. exact (@lem1287809 h1 _23269). Qed.
Lemma lem1287838 (_23269 : nadd) : (term239 _23269) = (term229 _23269).
Proof. exact (eq_refl (term239 _23269)). Qed.
Lemma lem1287839 (_23269 : nadd) (h1 : term198) : term229 _23269.
Proof. exact (EQ_MP (@lem1287838 _23269) (@lem1287837 _23269 h1)). Qed.
Lemma lem1287840 (_23269 : nadd) (_23270 : nadd) (h1 : term198) : term216 _23269 _23270.
Proof. exact (@lem1287839 _23269 h1 _23270). Qed.
Lemma lem1287841 (_23270 : nadd) (_23269 : nadd) : (term216 _23269 _23270) = (term217 _23270 _23269).
Proof. exact (eq_refl (term216 _23269 _23270)). Qed.
Lemma lem1287844 (N : nat) (x : nadd) (h1 : term153 N x) : term153 N x.
Proof. exact (h1). Qed.
Lemma lem1287857 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) : (term259 _23261 _23263 _23262 _23264) = (term276 _23261 _23263 _23262 _23264).
Proof. exact (@lem1286607 (term277 _23261 _23262) (term277 _23263 _23264) (term255 _23261 _23263 _23262 _23264)). Qed.
Lemma lem1287858 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) (h1 : term192) : term276 _23261 _23263 _23262 _23264.
Proof. exact (EQ_MP (@lem1287857 _23261 _23263 _23262 _23264) (@lem1287824 _23261 _23263 _23262 _23264 h1)). Qed.
Lemma lem1287872 (_23270 : nadd) (_23269 : nadd) (h1 : term198) : term217 _23270 _23269.
Proof. exact (EQ_MP (@lem1287841 _23270 _23269) (@lem1287840 _23269 _23270 h1)). Qed.
Lemma lem1287874 (_23265 : nat) (_23266 : nat) (h1 : term160) : term180 _23265 _23266.
Proof. exact (EQ_MP (@lem1287829 _23265 _23266) (@lem1287828 _23265 _23266 h1)). Qed.
Lemma lem1287875 (N : nat) (h1 : term160) : term278 N.
Proof. exact (@lem1287874 term137 N h1). Qed.
Lemma lem1287876 (N : nat) (h1 : term160) : term279 N.
Proof. exact (fun h0 : term280 N => @lem1287875 N h1). Qed.
Lemma lem1287878 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1287879 (N : nat) : (term279 N) = (term278 N).
Proof. exact (@lem1287878 (term278 N)). Qed.
Lemma lem1287880 (N : nat) (h1 : term160) : term278 N.
Proof. exact (EQ_MP (@lem1287879 N) (@lem1287876 N h1)). Qed.
Lemma lem1287882 (_23260 : nadd) (h1 : term194) : nadd_eq _23260 _23260.
Proof. exact (EQ_MP (@lem1287811 _23260) (@lem1287810 _23260 h1)). Qed.
Lemma lem1287883 (x : nadd) (h1 : term194) : nadd_eq x x.
Proof. exact (@lem1287882 x h1). Qed.
Lemma lem1287884 (x : nadd) (h1 : term194) : term282 x.
Proof. exact (fun h0 : term283 x => @lem1287883 x h1). Qed.
Lemma lem1287886 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1287887 (x : nadd) : (term282 x) = (nadd_eq x x).
Proof. exact (@lem1287886 (nadd_eq x x)). Qed.
Lemma lem1287888 (x : nadd) (h1 : term194) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1287887 x) (@lem1287884 x h1)). Qed.
Lemma lem1287904 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1287905 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term284 _23261 _23263 _23262 _23264) = (term285 _23261 _23262 _23263 _23264).
Proof. exact (@lem1287904 (term255 _23261 _23263 _23262 _23264) (term277 _23263 _23264)). Qed.
Lemma lem1287911 (_23261 : nadd) (_23262 : nadd) : (term286 _23261 _23262) = (term286 _23261 _23262).
Proof. exact (eq_refl (term286 _23261 _23262)). Qed.
Lemma lem1287912 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term276 _23261 _23263 _23262 _23264) = (term287 _23261 _23262 _23263 _23264).
Proof. exact (MK_COMB (@lem1287911 _23261 _23262) (@lem1287905 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287916 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1287917 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term287 _23261 _23262 _23263 _23264) = (term288 _23261 _23262 _23263 _23264).
Proof. exact (@lem1287916 (term255 _23261 _23263 _23262 _23264) (term277 _23261 _23262) (term277 _23263 _23264)). Qed.
Lemma lem1287933 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term276 _23261 _23263 _23262 _23264) = (term288 _23261 _23262 _23263 _23264).
Proof. exact (TRANS (@lem1287912 _23261 _23262 _23263 _23264) (@lem1287917 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1287935 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term289 _23261 _23263 _23262 _23264) = (term290 _23261 _23262 _23263 _23264).
Proof. exact (MK_COMB (@lem1287934) (@lem1287933 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287951 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term288 _23261 _23262 _23263 _23264) = (term288 _23261 _23262 _23263 _23264).
Proof. exact (eq_refl (term288 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287952 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : ((term276 _23261 _23263 _23262 _23264) = (term288 _23261 _23262 _23263 _23264)) = ((term288 _23261 _23262 _23263 _23264) = (term288 _23261 _23262 _23263 _23264)).
Proof. exact (MK_COMB (@lem1287935 _23261 _23262 _23263 _23264) (@lem1287951 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287954 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1287955 (x : Prop) : (x = x) = True.
Proof. exact (@lem1287954 Prop x). Qed.
Lemma lem1287956 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : ((term288 _23261 _23262 _23263 _23264) = (term288 _23261 _23262 _23263 _23264)) = True.
Proof. exact (@lem1287955 (term288 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287957 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : ((term276 _23261 _23263 _23262 _23264) = (term288 _23261 _23262 _23263 _23264)) = True.
Proof. exact (TRANS (@lem1287952 _23261 _23262 _23263 _23264) (@lem1287956 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287958 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : True = ((term276 _23261 _23263 _23262 _23264) = (term288 _23261 _23262 _23263 _23264)).
Proof. exact (SYM (@lem1287957 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287959 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term276 _23261 _23263 _23262 _23264) = (term288 _23261 _23262 _23263 _23264).
Proof. exact (EQ_MP (@lem1287958 _23261 _23262 _23263 _23264) (@lem0)). Qed.
Lemma lem1287960 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) (h1 : term192) : term288 _23261 _23262 _23263 _23264.
Proof. exact (EQ_MP (@lem1287959 _23261 _23262 _23263 _23264) (@lem1287858 _23261 _23263 _23262 _23264 h1)). Qed.
Lemma lem1287962 (b : Prop) (a : Prop) : (a \/ b) = (term291 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1287963 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) : (term288 _23261 _23262 _23263 _23264) = (term292 _23261 _23263 _23262 _23264).
Proof. exact (@lem1287962 (term254 _23261 _23262 _23263 _23264) (term255 _23261 _23263 _23262 _23264)). Qed.
Lemma lem1287965 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1287966 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term295 _23261 _23262 _23263 _23264) = (term296 _23261 _23262 _23263 _23264).
Proof. exact (@lem1287965 (term277 _23261 _23262) (term277 _23263 _23264)). Qed.
Lemma lem1287968 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1287969 (_23261 : nadd) (_23262 : nadd) : (term297 _23261 _23262) = (nadd_eq _23261 _23262).
Proof. exact (@lem1287968 (nadd_eq _23261 _23262)). Qed.
Lemma lem1287970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1287971 (_23261 : nadd) (_23262 : nadd) : (term298 _23261 _23262) = (term299 _23261 _23262).
Proof. exact (MK_COMB (@lem1287970) (@lem1287969 _23261 _23262)). Qed.
Lemma lem1287973 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1287974 (_23263 : nadd) (_23264 : nadd) : (term297 _23263 _23264) = (nadd_eq _23263 _23264).
Proof. exact (@lem1287973 (nadd_eq _23263 _23264)). Qed.
Lemma lem1287975 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term296 _23261 _23262 _23263 _23264) = (term260 _23261 _23262 _23263 _23264).
Proof. exact (MK_COMB (@lem1287971 _23261 _23262) (@lem1287974 _23263 _23264)). Qed.
Lemma lem1287976 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term295 _23261 _23262 _23263 _23264) = (term260 _23261 _23262 _23263 _23264).
Proof. exact (TRANS (@lem1287966 _23261 _23262 _23263 _23264) (@lem1287975 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1287978 (_23261 : nadd) (_23262 : nadd) (_23263 : nadd) (_23264 : nadd) : (term300 _23261 _23262 _23263 _23264) = (term301 _23261 _23262 _23263 _23264).
Proof. exact (MK_COMB (@lem1287977) (@lem1287976 _23261 _23262 _23263 _23264)). Qed.
Lemma lem1287979 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) : (term255 _23261 _23263 _23262 _23264) = (term255 _23261 _23263 _23262 _23264).
Proof. exact (eq_refl (term255 _23261 _23263 _23262 _23264)). Qed.
Lemma lem1287980 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) : (term292 _23261 _23263 _23262 _23264) = (term184 _23261 _23263 _23262 _23264).
Proof. exact (MK_COMB (@lem1287978 _23261 _23262 _23263 _23264) (@lem1287979 _23261 _23263 _23262 _23264)). Qed.
Lemma lem1287981 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) : (term288 _23261 _23262 _23263 _23264) = (term184 _23261 _23263 _23262 _23264).
Proof. exact (TRANS (@lem1287963 _23261 _23263 _23262 _23264) (@lem1287980 _23261 _23263 _23262 _23264)). Qed.
Lemma lem1287983 (N : nat) (x : nadd) (h1 : term194) (h2 : term160) : term302 N x.
Proof. exact (conj (@lem1287880 N h2) (@lem1287888 x h1)). Qed.
Lemma lem1287985 (_23261 : nadd) (_23263 : nadd) (_23262 : nadd) (_23264 : nadd) (h1 : term192) : term184 _23261 _23263 _23262 _23264.
Proof. exact (EQ_MP (@lem1287981 _23261 _23263 _23262 _23264) (@lem1287960 _23261 _23262 _23263 _23264 h1)). Qed.
Lemma lem1287986 (N : nat) (x : nadd) (h1 : term192) : term303 N x.
Proof. exact (@lem1287985 (term304 N) x (term139 N) x h1). Qed.
Lemma lem1287989 (N : nat) (x : nadd) (h1 : term192) (h2 : term194) (h3 : term160) : term305 N x.
Proof. exact (@lem1287986 N x h1 (@lem1287983 N x h2 h3)). Qed.
Lemma lem1287990 (N : nat) (x : nadd) (h1 : term192) (h2 : term194) (h3 : term160) : term306 N x.
Proof. exact (fun h0 : term307 N x => @lem1287989 N x h1 h2 h3). Qed.
Lemma lem1287992 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1287993 (N : nat) (x : nadd) : (term306 N x) = (term305 N x).
Proof. exact (@lem1287992 (term305 N x)). Qed.
Lemma lem1287994 (N : nat) (x : nadd) (h1 : term192) (h2 : term194) (h3 : term160) : term305 N x.
Proof. exact (EQ_MP (@lem1287993 N x) (@lem1287990 N x h1 h2 h3)). Qed.
Lemma lem1288000 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1288001 (_23269 : nadd) (_23270 : nadd) : (term217 _23270 _23269) = (term213 _23269 _23270).
Proof. exact (@lem1288000 (nadd_eq _23270 _23269) (term277 _23269 _23270)). Qed.
Lemma lem1288007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1288008 (_23269 : nadd) (_23270 : nadd) : (term308 _23270 _23269) = (term309 _23269 _23270).
Proof. exact (MK_COMB (@lem1288007) (@lem1288001 _23269 _23270)). Qed.
Lemma lem1288014 (_23269 : nadd) (_23270 : nadd) : (term213 _23269 _23270) = (term213 _23269 _23270).
Proof. exact (eq_refl (term213 _23269 _23270)). Qed.
Lemma lem1288015 (_23269 : nadd) (_23270 : nadd) : ((term217 _23270 _23269) = (term213 _23269 _23270)) = ((term213 _23269 _23270) = (term213 _23269 _23270)).
Proof. exact (MK_COMB (@lem1288008 _23269 _23270) (@lem1288014 _23269 _23270)). Qed.
Lemma lem1288017 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1288018 (x : Prop) : (x = x) = True.
Proof. exact (@lem1288017 Prop x). Qed.
Lemma lem1288019 (_23269 : nadd) (_23270 : nadd) : ((term213 _23269 _23270) = (term213 _23269 _23270)) = True.
Proof. exact (@lem1288018 (term213 _23269 _23270)). Qed.
Lemma lem1288020 (_23269 : nadd) (_23270 : nadd) : ((term217 _23270 _23269) = (term213 _23269 _23270)) = True.
Proof. exact (TRANS (@lem1288015 _23269 _23270) (@lem1288019 _23269 _23270)). Qed.
Lemma lem1288021 (_23269 : nadd) (_23270 : nadd) : True = ((term217 _23270 _23269) = (term213 _23269 _23270)).
Proof. exact (SYM (@lem1288020 _23269 _23270)). Qed.
Lemma lem1288022 (_23269 : nadd) (_23270 : nadd) : (term217 _23270 _23269) = (term213 _23269 _23270).
Proof. exact (EQ_MP (@lem1288021 _23269 _23270) (@lem0)). Qed.
Lemma lem1288023 (_23269 : nadd) (_23270 : nadd) (h1 : term198) : term213 _23269 _23270.
Proof. exact (EQ_MP (@lem1288022 _23269 _23270) (@lem1287872 _23270 _23269 h1)). Qed.
Lemma lem1288025 (b : Prop) (a : Prop) : (a \/ b) = (term291 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1288026 (_23270 : nadd) (_23269 : nadd) : (term213 _23269 _23270) = (term310 _23270 _23269).
Proof. exact (@lem1288025 (term277 _23269 _23270) (nadd_eq _23270 _23269)). Qed.
Lemma lem1288028 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1288029 (_23269 : nadd) (_23270 : nadd) : (term297 _23269 _23270) = (nadd_eq _23269 _23270).
Proof. exact (@lem1288028 (nadd_eq _23269 _23270)). Qed.
Lemma lem1288030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1288031 (_23269 : nadd) (_23270 : nadd) : (term311 _23269 _23270) = (term312 _23269 _23270).
Proof. exact (MK_COMB (@lem1288030) (@lem1288029 _23269 _23270)). Qed.
Lemma lem1288032 (_23270 : nadd) (_23269 : nadd) : (nadd_eq _23270 _23269) = (nadd_eq _23270 _23269).
Proof. exact (eq_refl (nadd_eq _23270 _23269)). Qed.
Lemma lem1288033 (_23270 : nadd) (_23269 : nadd) : (term310 _23270 _23269) = (term313 _23270 _23269).
Proof. exact (MK_COMB (@lem1288031 _23269 _23270) (@lem1288032 _23270 _23269)). Qed.
Lemma lem1288034 (_23270 : nadd) (_23269 : nadd) : (term213 _23269 _23270) = (term313 _23270 _23269).
Proof. exact (TRANS (@lem1288026 _23270 _23269) (@lem1288033 _23270 _23269)). Qed.
Lemma lem1288037 (_23270 : nadd) (_23269 : nadd) (h1 : term198) : term313 _23270 _23269.
Proof. exact (EQ_MP (@lem1288034 _23270 _23269) (@lem1288023 _23269 _23270 h1)). Qed.
Lemma lem1288038 (N : nat) (x : nadd) (h1 : term198) : term314 N x.
Proof. exact (@lem1288037 (term143 N x) (term315 N x) h1). Qed.
Lemma lem1288041 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) : term151 N x.
Proof. exact (@lem1288038 N x h2 (@lem1287994 N x h1 h3 h4)). Qed.
Lemma lem1288042 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) : term316 N x.
Proof. exact (fun h0 : term153 N x => @lem1288041 N x h1 h2 h3 h4). Qed.
Lemma lem1288044 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1288045 (N : nat) (x : nadd) : (term316 N x) = (term151 N x).
Proof. exact (@lem1288044 (term151 N x)). Qed.
Lemma lem1288046 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) : term151 N x.
Proof. exact (EQ_MP (@lem1288045 N x) (@lem1288042 N x h1 h2 h3 h4)). Qed.
Lemma lem1288049 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1288051 (N : nat) (x : nadd) : (term153 N x) = (term317 N x).
Proof. exact (@lem1288049 (term151 N x)). Qed.
Lemma lem1288054 (N : nat) (x : nadd) (h1 : term153 N x) : term317 N x.
Proof. exact (EQ_MP (@lem1288051 N x) (@lem1287844 N x h1)). Qed.
Lemma lem1288057 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (@lem1288054 N x h5 (@lem1288046 N x h1 h2 h3 h4)). Qed.
Lemma lem1288058 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : term318.
Proof. exact (fun h0 : ~ False => @lem1288057 N x h1 h2 h3 h4 h5). Qed.
Lemma lem1288060 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1288061 : term318 = False.
Proof. exact (@lem1288060 False). Qed.
Lemma lem1288062 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288061) (@lem1288058 N x h1 h2 h3 h4 h5)). Qed.
Lemma lem1288063 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : (term153 N x) = False.
Proof. exact (prop_ext (fun h6 : term153 N x => @lem1288062 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287844 N x h5)). Qed.
Lemma lem1288064 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288063 N x h1 h2 h3 h4 h5) (@lem1287844 N x h5)). Qed.
Lemma lem1288065 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : (term153 N x) = False.
Proof. exact (prop_ext (fun h6 : term153 N x => @lem1288064 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287732 N x h5)). Qed.
Lemma lem1288066 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288065 N x h1 h2 h3 h4 h5) (@lem1287732 N x h5)). Qed.
Lemma lem1288067 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : term160 = False.
Proof. exact (prop_ext (fun h6 : term160 => @lem1288066 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287777 h4)). Qed.
Lemma lem1288068 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288067 N x h1 h2 h3 h4 h5) (@lem1287777 h4)). Qed.
Lemma lem1288069 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : term194 = False.
Proof. exact (prop_ext (fun h6 : term194 => @lem1288068 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287739 h3)). Qed.
Lemma lem1288070 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288069 N x h1 h2 h3 h4 h5) (@lem1287739 h3)). Qed.
Lemma lem1288071 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : (term153 N x) = False.
Proof. exact (prop_ext (fun h6 : term153 N x => @lem1288070 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287732 N x h5)). Qed.
Lemma lem1288072 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288071 N x h1 h2 h3 h4 h5) (@lem1287732 N x h5)). Qed.
Lemma lem1288073 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : term160 = False.
Proof. exact (prop_ext (fun h6 : term160 => @lem1288072 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287726 h4)). Qed.
Lemma lem1288074 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288073 N x h1 h2 h3 h4 h5) (@lem1287726 h4)). Qed.
Lemma lem1288075 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : term194 = False.
Proof. exact (prop_ext (fun h6 : term194 => @lem1288074 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287654 h3)). Qed.
Lemma lem1288076 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288075 N x h1 h2 h3 h4 h5) (@lem1287654 h3)). Qed.
Lemma lem1288077 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : (term153 N x) = False.
Proof. exact (prop_ext (fun h6 : term153 N x => @lem1288076 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287599 N x h5)). Qed.
Lemma lem1288078 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288077 N x h1 h2 h3 h4 h5) (@lem1287599 N x h5)). Qed.
Lemma lem1288079 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : term160 = False.
Proof. exact (prop_ext (fun h6 : term160 => @lem1288078 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287561 h4)). Qed.
Lemma lem1288080 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288079 N x h1 h2 h3 h4 h5) (@lem1287561 h4)). Qed.
Lemma lem1288081 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : term194 = False.
Proof. exact (prop_ext (fun h6 : term194 => @lem1288080 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287451 h3)). Qed.
Lemma lem1288082 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288081 N x h1 h2 h3 h4 h5) (@lem1287451 h3)). Qed.
Lemma lem1288083 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : (term153 N x) = False.
Proof. exact (prop_ext (fun h6 : term153 N x => @lem1288082 N x h1 h2 h3 h4 h5) (fun h6 : False => @lem1287151 N x h5)). Qed.
Lemma lem1288084 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term160) (h5 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288083 N x h1 h2 h3 h4 h5) (@lem1287151 N x h5)). Qed.
Lemma lem1288085 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term153 N x) : term158.
Proof. exact (fun h0 : term160 => @lem1288084 N x h1 h2 h3 h0 h4). Qed.
Lemma lem1288086 : term158 = term159.
Proof. exact (@lem69 term160). Qed.
Lemma lem1288087 (N : nat) (x : nadd) (h1 : term192) (h2 : term198) (h3 : term194) (h4 : term153 N x) : term159.
Proof. exact (EQ_MP (@lem1288086) (@lem1288085 N x h1 h2 h3 h4)). Qed.
Lemma lem1288088 (N : nat) (x : nadd) (h1 : term198) (h2 : term194) (h3 : term153 N x) : term163.
Proof. exact (fun h0 : term192 => @lem1288087 N x h0 h1 h2 h3). Qed.
Lemma lem1288089 (N : nat) (x : nadd) (h1 : term198) (h2 : term153 N x) : term166.
Proof. exact (fun h0 : term194 => @lem1288088 N x h1 h0 h2). Qed.
Lemma lem1288090 (N : nat) (x : nadd) (h1 : term153 N x) : term169.
Proof. exact (fun h0 : term198 => @lem1288089 N x h0 h1). Qed.
Lemma lem1288091 (N : nat) (x : nadd) : term171 N x.
Proof. exact (fun h0 : term153 N x => @lem1288090 N x h0). Qed.
Lemma lem1288096 (x : nadd) : term175 x.
Proof. exact (fun N : nat => @lem1288091 N x). Qed.
Lemma lem1288101 : term179.
Proof. exact (fun x : nadd => @lem1288096 x). Qed.
Lemma lem1288102 : term178.
Proof. exact (EQ_MP (@lem1287140) (@lem1288101)). Qed.
Lemma lem1288103 (x : nadd) : term319 x.
Proof. exact (@lem1288102 x). Qed.
Lemma lem1288104 (x : nadd) : (term319 x) = (term174 x).
Proof. exact (eq_refl (term319 x)). Qed.
Lemma lem1288105 (x : nadd) : term174 x.
Proof. exact (EQ_MP (@lem1288104 x) (@lem1288103 x)). Qed.
Lemma lem1288106 (x : nadd) (N : nat) : term320 x N.
Proof. exact (@lem1288105 x N). Qed.
Lemma lem1288107 (N : nat) (x : nadd) : (term320 x N) = (term154 N x).
Proof. exact (eq_refl (term320 x N)). Qed.
Lemma lem1288108 (N : nat) (x : nadd) : term154 N x.
Proof. exact (EQ_MP (@lem1288107 N x) (@lem1288106 x N)). Qed.
Lemma lem1288110 (N : nat) (x : nadd) : term154 N x.
Proof. exact (@lem1286899 N x (@lem1288108 N x)). Qed.
Lemma lem1288111 (N : nat) (x : nadd) (h1 : term153 N x) : term168.
Proof. exact (@lem1288110 N x (@lem1286884 N x h1)). Qed.
Lemma lem1288112 (N : nat) (x : nadd) (h1 : term153 N x) : term165.
Proof. exact (@lem1288111 N x h1 (@lem1268060)). Qed.
Lemma lem1288113 (N : nat) (x : nadd) (h1 : term153 N x) : term162.
Proof. exact (@lem1288112 N x h1 (@lem1267990)). Qed.
Lemma lem1288114 (N : nat) (x : nadd) (h1 : term153 N x) : term158.
Proof. exact (@lem1288113 N x h1 (@lem1279298)). Qed.
Lemma lem1288115 (N : nat) (x : nadd) (h1 : term153 N x) : False.
Proof. exact (@lem1288114 N x h1 (@lem1276280)). Qed.
Lemma lem1288116 (N : nat) (x : nadd) (h1 : term153 N x) : (term153 N x) = False.
Proof. exact (prop_ext (fun h2 : term153 N x => @lem1288115 N x h1) (fun h2 : False => @lem1286884 N x h1)). Qed.
Lemma lem1288117 (N : nat) (x : nadd) (h1 : term153 N x) : False.
Proof. exact (EQ_MP (@lem1288116 N x h1) (@lem1286884 N x h1)). Qed.
Lemma lem1288118 (N : nat) (x : nadd) : term152 N x.
Proof. exact (fun h0 : term153 N x => @lem1288117 N x h0). Qed.
Lemma lem1288119 (N : nat) (x : nadd) : term151 N x.
Proof. exact (EQ_MP (@lem1286883 N x) (@lem1288118 N x)). Qed.
Lemma lem1288121 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1288122 (N : nat) (x : nadd) : (term321 N x) = (term322 N x).
Proof. exact (@lem1288121 (term321 N x)). Qed.
Lemma lem1288123 (N : nat) (x : nadd) : (term322 N x) = (term321 N x).
Proof. exact (SYM (@lem1288122 N x)). Qed.
Lemma lem1288124 (N : nat) (x : nadd) (h1 : term323 N x) : term323 N x.
Proof. exact (h1). Qed.
Lemma lem1288127 (N : nat) (x : nadd) (h1 : term324 N x) : term324 N x.
Proof. exact (h1). Qed.
Lemma lem1288128 (N : nat) (x : nadd) : term325 N x.
Proof. exact (fun h0 : term324 N x => @lem1288127 N x h0). Qed.
Lemma lem1288129 (N : nat) (x : nadd) (h1 : term325 N x) : term325 N x.
Proof. exact (h1). Qed.
Lemma lem1288130 (N : nat) (x : nadd) (h1 : term324 N x) : term324 N x.
Proof. exact (h1). Qed.
Lemma lem1288131 (N : nat) (x : nadd) (h1 : term324 N x) (h2 : term325 N x) : term324 N x.
Proof. exact (@lem1288129 N x h2 (@lem1288130 N x h1)). Qed.
Lemma lem1288132 (N : nat) (x : nadd) (h1 : term324 N x) : term326 N x.
Proof. exact (fun h0 : term325 N x => @lem1288131 N x h1 h0). Qed.
Lemma lem1288133 (N : nat) (x : nadd) (h1 : term325 N x) : term325 N x.
Proof. exact (h1). Qed.
Lemma lem1288134 (N : nat) (x : nadd) (h1 : term324 N x) (h2 : term325 N x) : term324 N x.
Proof. exact (@lem1288132 N x h1 (@lem1288133 N x h2)). Qed.
Lemma lem1288135 (N : nat) (x : nadd) (h1 : term325 N x) : term325 N x.
Proof. exact (fun h0 : term324 N x => @lem1288134 N x h0 h1). Qed.
Lemma lem1288136 (N : nat) (x : nadd) : term327 N x.
Proof. exact (fun h0 : term325 N x => @lem1288135 N x h0). Qed.
Lemma lem1288139 (N : nat) (x : nadd) : term325 N x.
Proof. exact (@lem1288136 N x (@lem1288128 N x)). Qed.
Lemma lem1288189 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1288190 : term328 = term329.
Proof. exact (@lem1288189 term330). Qed.
Lemma lem1288203 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem1288204 : term332 = term333.
Proof. exact (MK_COMB (@lem1288203) (@lem1288190)). Qed.
Lemma lem1288207 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem1288208 : term334 = term335.
Proof. exact (MK_COMB (@lem1288207) (@lem1288204)). Qed.
Lemma lem1288211 : term336 = term336.
Proof. exact (eq_refl term336). Qed.
Lemma lem1288212 : term337 = term338.
Proof. exact (MK_COMB (@lem1288211) (@lem1288208)). Qed.
Lemma lem1288215 (N : nat) (x : nadd) : (term339 N x) = (term339 N x).
Proof. exact (eq_refl (term339 N x)). Qed.
Lemma lem1288216 (N : nat) (x : nadd) : (term324 N x) = (term340 N x).
Proof. exact (MK_COMB (@lem1288215 N x) (@lem1288212)). Qed.
Lemma lem1288219 (x : nadd) : (term341 x) = (term342 x).
Proof. exact (fun_ext (fun N : nat => @lem1288216 N x)). Qed.
Lemma lem1288220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1288221 (x : nadd) : (term343 x) = (term344 x).
Proof. exact (MK_COMB (@lem1288220) (@lem1288219 x)). Qed.
Lemma lem1288226 : term345 = term346.
Proof. exact (fun_ext (fun x : nadd => @lem1288221 x)). Qed.
Lemma lem1288227 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288236 : term347 = term348.
Proof. exact (MK_COMB (@lem1288227) (@lem1288226)). Qed.
Lemma lem1288237 (x : nadd) (y : nadd) (z : nadd) : (term349 x y z) = (term349 x y z).
Proof. exact (eq_refl (term349 x y z)). Qed.
Lemma lem1288238 (x : nadd) (y : nadd) : (term350 x y) = (term350 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1288237 x y z)). Qed.
Lemma lem1288239 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288240 (x : nadd) (y : nadd) : (term351 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem1288239) (@lem1288238 x y)). Qed.
Lemma lem1288241 (x : nadd) : (term352 x) = (term352 x).
Proof. exact (fun_ext (fun y : nadd => @lem1288240 x y)). Qed.
Lemma lem1288242 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288243 (x : nadd) : (term353 x) = (term353 x).
Proof. exact (MK_COMB (@lem1288242) (@lem1288241 x)). Qed.
Lemma lem1288244 : term354 = term354.
Proof. exact (fun_ext (fun x : nadd => @lem1288243 x)). Qed.
Lemma lem1288245 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288246 : term330 = term330.
Proof. exact (MK_COMB (@lem1288245) (@lem1288244)). Qed.
Lemma lem1288247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1288248 : term329 = term329.
Proof. exact (MK_COMB (@lem1288247) (@lem1288246)). Qed.
Lemma lem1288249 (y : nadd) (x : nadd) : (term355 y x) = (term355 y x).
Proof. exact (eq_refl (term355 y x)). Qed.
Lemma lem1288250 (x : nadd) : (term356 x) = (term356 x).
Proof. exact (fun_ext (fun y : nadd => @lem1288249 y x)). Qed.
Lemma lem1288251 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288252 (x : nadd) : (term357 x) = (term357 x).
Proof. exact (MK_COMB (@lem1288251) (@lem1288250 x)). Qed.
Lemma lem1288253 : term358 = term358.
Proof. exact (fun_ext (fun x : nadd => @lem1288252 x)). Qed.
Lemma lem1288254 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288255 : term359 = term359.
Proof. exact (MK_COMB (@lem1288254) (@lem1288253)). Qed.
Lemma lem1288256 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1288257 : term331 = term331.
Proof. exact (MK_COMB (@lem1288256) (@lem1288255)). Qed.
Lemma lem1288258 : term333 = term333.
Proof. exact (MK_COMB (@lem1288257) (@lem1288248)). Qed.
Lemma lem1288263 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl ((nadd_eq x y) = (nadd_eq y x))). Qed.
Lemma lem1288264 (x : nadd) : (term195 x) = (term195 x).
Proof. exact (fun_ext (fun y : nadd => @lem1288263 y x)). Qed.
Lemma lem1288265 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288266 (x : nadd) : (term196 x) = (term196 x).
Proof. exact (MK_COMB (@lem1288265) (@lem1288264 x)). Qed.
Lemma lem1288267 : term197 = term197.
Proof. exact (fun_ext (fun x : nadd => @lem1288266 x)). Qed.
Lemma lem1288268 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288269 : term198 = term198.
Proof. exact (MK_COMB (@lem1288268) (@lem1288267)). Qed.
Lemma lem1288270 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1288271 : term167 = term167.
Proof. exact (MK_COMB (@lem1288270) (@lem1288269)). Qed.
Lemma lem1288272 : term335 = term335.
Proof. exact (MK_COMB (@lem1288271) (@lem1288258)). Qed.
Lemma lem1288281 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term13 y x z).
Proof. exact (eq_refl (term13 y x z)). Qed.
Lemma lem1288282 (y : nadd) (x : nadd) : (term360 y x) = (term360 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1288281 y x z)). Qed.
Lemma lem1288283 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288284 (y : nadd) (x : nadd) : (term11 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1288283) (@lem1288282 y x)). Qed.
Lemma lem1288285 (x : nadd) : (term361 x) = (term361 x).
Proof. exact (fun_ext (fun y : nadd => @lem1288284 y x)). Qed.
Lemma lem1288286 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288287 (x : nadd) : (term9 x) = (term9 x).
Proof. exact (MK_COMB (@lem1288286) (@lem1288285 x)). Qed.
Lemma lem1288288 : term362 = term362.
Proof. exact (fun_ext (fun x : nadd => @lem1288287 x)). Qed.
Lemma lem1288289 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288290 : term7 = term7.
Proof. exact (MK_COMB (@lem1288289) (@lem1288288)). Qed.
Lemma lem1288291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1288292 : term336 = term336.
Proof. exact (MK_COMB (@lem1288291) (@lem1288290)). Qed.
Lemma lem1288293 : term338 = term338.
Proof. exact (MK_COMB (@lem1288292) (@lem1288272)). Qed.
Lemma lem1288298 (N : nat) (x : nadd) : (term339 N x) = (term339 N x).
Proof. exact (eq_refl (term339 N x)). Qed.
Lemma lem1288299 (N : nat) (x : nadd) : (term340 N x) = (term340 N x).
Proof. exact (MK_COMB (@lem1288298 N x) (@lem1288293)). Qed.
Lemma lem1288300 (x : nadd) : (term342 x) = (term342 x).
Proof. exact (fun_ext (fun N : nat => @lem1288299 N x)). Qed.
Lemma lem1288301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1288302 (x : nadd) : (term344 x) = (term344 x).
Proof. exact (MK_COMB (@lem1288301) (@lem1288300 x)). Qed.
Lemma lem1288303 : term346 = term346.
Proof. exact (fun_ext (fun x : nadd => @lem1288302 x)). Qed.
Lemma lem1288304 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288305 : term348 = term348.
Proof. exact (MK_COMB (@lem1288304) (@lem1288303)). Qed.
Lemma lem1288392 : term347 = term348.
Proof. exact (TRANS (@lem1288236) (@lem1288305)). Qed.
Lemma lem1288393 : term348 = term347.
Proof. exact (SYM (@lem1288392)). Qed.
Lemma lem1288398 (h1 : term330) : term330.
Proof. exact (h1). Qed.
Lemma lem1288404 (N : nat) (x : nadd) (h1 : term323 N x) : term323 N x.
Proof. exact (h1). Qed.
Lemma lem1288795 (x : nadd) (y : nadd) (z : nadd) : (term349 x y z) = (term349 x y z).
Proof. exact (eq_refl (term349 x y z)). Qed.
Lemma lem1288796 (x : nadd) (y : nadd) : (term350 x y) = (term350 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1288795 x y z)). Qed.
Lemma lem1288797 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288798 (x : nadd) (y : nadd) : (term351 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem1288797) (@lem1288796 x y)). Qed.
Lemma lem1288799 (x : nadd) : (term352 x) = (term352 x).
Proof. exact (fun_ext (fun y : nadd => @lem1288798 x y)). Qed.
Lemma lem1288800 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288801 (x : nadd) : (term353 x) = (term353 x).
Proof. exact (MK_COMB (@lem1288800) (@lem1288799 x)). Qed.
Lemma lem1288802 : term354 = term354.
Proof. exact (fun_ext (fun x : nadd => @lem1288801 x)). Qed.
Lemma lem1288803 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288820 : term330 = term330.
Proof. exact (MK_COMB (@lem1288803) (@lem1288802)). Qed.
Lemma lem1288821 (h1 : term330) : term330.
Proof. exact (EQ_MP (@lem1288820) (@lem1288398 h1)). Qed.
Lemma lem1288865 (N : nat) (x : nadd) (h1 : term323 N x) : term323 N x.
Proof. exact (h1). Qed.
Lemma lem1288991 (x : nadd) (y : nadd) (z : nadd) : (term349 x y z) = (term349 x y z).
Proof. exact (eq_refl (term349 x y z)). Qed.
Lemma lem1288992 (x : nadd) (y : nadd) : (term350 x y) = (term350 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1288991 x y z)). Qed.
Lemma lem1288993 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288994 (x : nadd) (y : nadd) : (term351 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem1288993) (@lem1288992 x y)). Qed.
Lemma lem1288995 (x : nadd) : (term352 x) = (term352 x).
Proof. exact (fun_ext (fun y : nadd => @lem1288994 x y)). Qed.
Lemma lem1288996 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1288997 (x : nadd) : (term353 x) = (term353 x).
Proof. exact (MK_COMB (@lem1288996) (@lem1288995 x)). Qed.
Lemma lem1288998 : term354 = term354.
Proof. exact (fun_ext (fun x : nadd => @lem1288997 x)). Qed.
Lemma lem1288999 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289000 : term330 = term330.
Proof. exact (MK_COMB (@lem1288999) (@lem1288998)). Qed.
Lemma lem1289001 (h1 : term330) : term330.
Proof. exact (EQ_MP (@lem1289000) (@lem1288821 h1)). Qed.
Lemma lem1289007 (N : nat) (x : nadd) (h1 : term323 N x) : term323 N x.
Proof. exact (h1). Qed.
Lemma lem1289044 (x : nadd) (y : nadd) (z : nadd) : (term349 x y z) = (term349 x y z).
Proof. exact (eq_refl (term349 x y z)). Qed.
Lemma lem1289045 (x : nadd) (y : nadd) : (term350 x y) = (term350 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1289044 x y z)). Qed.
Lemma lem1289046 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289047 (x : nadd) (y : nadd) : (term351 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem1289046) (@lem1289045 x y)). Qed.
Lemma lem1289048 (x : nadd) : (term352 x) = (term352 x).
Proof. exact (fun_ext (fun y : nadd => @lem1289047 x y)). Qed.
Lemma lem1289049 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289050 (x : nadd) : (term353 x) = (term353 x).
Proof. exact (MK_COMB (@lem1289049) (@lem1289048 x)). Qed.
Lemma lem1289051 : term354 = term354.
Proof. exact (fun_ext (fun x : nadd => @lem1289050 x)). Qed.
Lemma lem1289052 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289054 : term330 = term330.
Proof. exact (MK_COMB (@lem1289052) (@lem1289051)). Qed.
Lemma lem1289055 (h1 : term330) : term330.
Proof. exact (EQ_MP (@lem1289054) (@lem1289001 h1)). Qed.
Lemma lem1289103 (_23276 : nadd) (h1 : term330) : term363 _23276.
Proof. exact (@lem1289055 h1 _23276). Qed.
Lemma lem1289104 (_23276 : nadd) : (term363 _23276) = (term353 _23276).
Proof. exact (eq_refl (term363 _23276)). Qed.
Lemma lem1289105 (_23276 : nadd) (h1 : term330) : term353 _23276.
Proof. exact (EQ_MP (@lem1289104 _23276) (@lem1289103 _23276 h1)). Qed.
Lemma lem1289106 (_23276 : nadd) (_23277 : nadd) (h1 : term330) : term364 _23276 _23277.
Proof. exact (@lem1289105 _23276 h1 _23277). Qed.
Lemma lem1289107 (_23276 : nadd) (_23277 : nadd) : (term364 _23276 _23277) = (term351 _23276 _23277).
Proof. exact (eq_refl (term364 _23276 _23277)). Qed.
Lemma lem1289108 (_23276 : nadd) (_23277 : nadd) (h1 : term330) : term351 _23276 _23277.
Proof. exact (EQ_MP (@lem1289107 _23276 _23277) (@lem1289106 _23276 _23277 h1)). Qed.
Lemma lem1289109 (_23276 : nadd) (_23277 : nadd) (_23278 : nadd) (h1 : term330) : term365 _23276 _23277 _23278.
Proof. exact (@lem1289108 _23276 _23277 h1 _23278). Qed.
Lemma lem1289110 (_23276 : nadd) (_23277 : nadd) (_23278 : nadd) : (term365 _23276 _23277 _23278) = (term349 _23276 _23277 _23278).
Proof. exact (eq_refl (term365 _23276 _23277 _23278)). Qed.
Lemma lem1289125 (N : nat) (x : nadd) (h1 : term323 N x) : term323 N x.
Proof. exact (h1). Qed.
Lemma lem1289155 (_23276 : nadd) (_23277 : nadd) (_23278 : nadd) (h1 : term330) : term349 _23276 _23277 _23278.
Proof. exact (EQ_MP (@lem1289110 _23276 _23277 _23278) (@lem1289109 _23276 _23277 _23278 h1)). Qed.
Lemma lem1289156 (N : nat) (x : nadd) (h1 : term330) : term321 N x.
Proof. exact (@lem1289155 term366 (nadd_of_num N) x h1). Qed.
Lemma lem1289157 (N : nat) (x : nadd) (h1 : term330) : term367 N x.
Proof. exact (fun h0 : term323 N x => @lem1289156 N x h1). Qed.
Lemma lem1289159 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1289160 (N : nat) (x : nadd) : (term367 N x) = (term321 N x).
Proof. exact (@lem1289159 (term321 N x)). Qed.
Lemma lem1289161 (N : nat) (x : nadd) (h1 : term330) : term321 N x.
Proof. exact (EQ_MP (@lem1289160 N x) (@lem1289157 N x h1)). Qed.
Lemma lem1289164 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1289166 (N : nat) (x : nadd) : (term323 N x) = (term368 N x).
Proof. exact (@lem1289164 (term321 N x)). Qed.
Lemma lem1289169 (N : nat) (x : nadd) (h1 : term323 N x) : term368 N x.
Proof. exact (EQ_MP (@lem1289166 N x) (@lem1289125 N x h1)). Qed.
Lemma lem1289172 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (@lem1289169 N x h2 (@lem1289161 N x h1)). Qed.
Lemma lem1289173 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : term318.
Proof. exact (fun h0 : ~ False => @lem1289172 N x h1 h2). Qed.
Lemma lem1289175 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1289176 : term318 = False.
Proof. exact (@lem1289175 False). Qed.
Lemma lem1289177 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289176) (@lem1289173 N x h1 h2)). Qed.
Lemma lem1289178 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : (term323 N x) = False.
Proof. exact (prop_ext (fun h3 : term323 N x => @lem1289177 N x h1 h2) (fun h3 : False => @lem1289125 N x h2)). Qed.
Lemma lem1289179 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289178 N x h1 h2) (@lem1289125 N x h2)). Qed.
Lemma lem1289180 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : (term323 N x) = False.
Proof. exact (prop_ext (fun h3 : term323 N x => @lem1289179 N x h1 h2) (fun h3 : False => @lem1289007 N x h2)). Qed.
Lemma lem1289181 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289180 N x h1 h2) (@lem1289007 N x h2)). Qed.
Lemma lem1289182 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : term330 = False.
Proof. exact (prop_ext (fun h3 : term330 => @lem1289181 N x h1 h2) (fun h3 : False => @lem1289055 h1)). Qed.
Lemma lem1289183 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289182 N x h1 h2) (@lem1289055 h1)). Qed.
Lemma lem1289184 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : (term323 N x) = False.
Proof. exact (prop_ext (fun h3 : term323 N x => @lem1289183 N x h1 h2) (fun h3 : False => @lem1289007 N x h2)). Qed.
Lemma lem1289185 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289184 N x h1 h2) (@lem1289007 N x h2)). Qed.
Lemma lem1289186 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : term330 = False.
Proof. exact (prop_ext (fun h3 : term330 => @lem1289185 N x h1 h2) (fun h3 : False => @lem1289001 h1)). Qed.
Lemma lem1289187 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289186 N x h1 h2) (@lem1289001 h1)). Qed.
Lemma lem1289188 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : (term323 N x) = False.
Proof. exact (prop_ext (fun h3 : term323 N x => @lem1289187 N x h1 h2) (fun h3 : False => @lem1288865 N x h2)). Qed.
Lemma lem1289189 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289188 N x h1 h2) (@lem1288865 N x h2)). Qed.
Lemma lem1289190 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : term330 = False.
Proof. exact (prop_ext (fun h3 : term330 => @lem1289189 N x h1 h2) (fun h3 : False => @lem1288821 h1)). Qed.
Lemma lem1289191 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289190 N x h1 h2) (@lem1288821 h1)). Qed.
Lemma lem1289192 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : (term323 N x) = False.
Proof. exact (prop_ext (fun h3 : term323 N x => @lem1289191 N x h1 h2) (fun h3 : False => @lem1288404 N x h2)). Qed.
Lemma lem1289193 (N : nat) (x : nadd) (h1 : term330) (h2 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289192 N x h1 h2) (@lem1288404 N x h2)). Qed.
Lemma lem1289194 (N : nat) (x : nadd) (h1 : term323 N x) : term328.
Proof. exact (fun h0 : term330 => @lem1289193 N x h0 h1). Qed.
Lemma lem1289195 : term328 = term329.
Proof. exact (@lem69 term330). Qed.
Lemma lem1289196 (N : nat) (x : nadd) (h1 : term323 N x) : term329.
Proof. exact (EQ_MP (@lem1289195) (@lem1289194 N x h1)). Qed.
Lemma lem1289197 (N : nat) (x : nadd) (h1 : term323 N x) : term333.
Proof. exact (fun h0 : term359 => @lem1289196 N x h1). Qed.
Lemma lem1289198 (N : nat) (x : nadd) (h1 : term323 N x) : term335.
Proof. exact (fun h0 : term198 => @lem1289197 N x h1). Qed.
Lemma lem1289199 (N : nat) (x : nadd) (h1 : term323 N x) : term338.
Proof. exact (fun h0 : term7 => @lem1289198 N x h1). Qed.
Lemma lem1289200 (N : nat) (x : nadd) : term340 N x.
Proof. exact (fun h0 : term323 N x => @lem1289199 N x h0). Qed.
Lemma lem1289205 (x : nadd) : term344 x.
Proof. exact (fun N : nat => @lem1289200 N x). Qed.
Lemma lem1289210 : term348.
Proof. exact (fun x : nadd => @lem1289205 x). Qed.
Lemma lem1289211 : term347.
Proof. exact (EQ_MP (@lem1288393) (@lem1289210)). Qed.
Lemma lem1289212 (x : nadd) : term369 x.
Proof. exact (@lem1289211 x). Qed.
Lemma lem1289213 (x : nadd) : (term369 x) = (term343 x).
Proof. exact (eq_refl (term369 x)). Qed.
Lemma lem1289214 (x : nadd) : term343 x.
Proof. exact (EQ_MP (@lem1289213 x) (@lem1289212 x)). Qed.
Lemma lem1289215 (x : nadd) (N : nat) : term370 x N.
Proof. exact (@lem1289214 x N). Qed.
Lemma lem1289216 (N : nat) (x : nadd) : (term370 x N) = (term324 N x).
Proof. exact (eq_refl (term370 x N)). Qed.
Lemma lem1289217 (N : nat) (x : nadd) : term324 N x.
Proof. exact (EQ_MP (@lem1289216 N x) (@lem1289215 x N)). Qed.
Lemma lem1289219 (N : nat) (x : nadd) : term324 N x.
Proof. exact (@lem1288139 N x (@lem1289217 N x)). Qed.
Lemma lem1289220 (N : nat) (x : nadd) (h1 : term323 N x) : term337.
Proof. exact (@lem1289219 N x (@lem1288124 N x h1)). Qed.
Lemma lem1289221 (N : nat) (x : nadd) (h1 : term323 N x) : term334.
Proof. exact (@lem1289220 N x h1 (@lem1268295)). Qed.
Lemma lem1289222 (N : nat) (x : nadd) (h1 : term323 N x) : term332.
Proof. exact (@lem1289221 N x h1 (@lem1268060)). Qed.
Lemma lem1289223 (N : nat) (x : nadd) (h1 : term323 N x) : term328.
Proof. exact (@lem1289222 N x h1 (@lem1278399)). Qed.
Lemma lem1289224 (N : nat) (x : nadd) (h1 : term323 N x) : False.
Proof. exact (@lem1289223 N x h1 (@lem1285826)). Qed.
Lemma lem1289225 (N : nat) (x : nadd) (h1 : term323 N x) : (term323 N x) = False.
Proof. exact (prop_ext (fun h2 : term323 N x => @lem1289224 N x h1) (fun h2 : False => @lem1288124 N x h1)). Qed.
Lemma lem1289226 (N : nat) (x : nadd) (h1 : term323 N x) : False.
Proof. exact (EQ_MP (@lem1289225 N x h1) (@lem1288124 N x h1)). Qed.
Lemma lem1289227 (N : nat) (x : nadd) : term322 N x.
Proof. exact (fun h0 : term323 N x => @lem1289226 N x h0). Qed.
Lemma lem1289228 (N : nat) (x : nadd) : term321 N x.
Proof. exact (EQ_MP (@lem1288123 N x) (@lem1289227 N x)). Qed.
Lemma lem1289229 (N : nat) (x : nadd) : term371 N x.
Proof. exact (conj (@lem1288119 N x) (@lem1289228 N x)). Qed.
Lemma lem1289230 (N : nat) (x : nadd) : term372 N x.
Proof. exact (ex_intro (term373 N x) (term315 N x) (@lem1289229 N x)). Qed.
Lemma lem1289231 (N : nat) (x : nadd) : term374 N x.
Proof. exact (@lem1286879 N x (@lem1289230 N x)). Qed.
Lemma lem1289233 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1289234 (N : nat) (x : nadd) : (term375 N x) = (term376 N x).
Proof. exact (@lem1289233 (term375 N x)). Qed.
Lemma lem1289235 (N : nat) (x : nadd) : (term376 N x) = (term375 N x).
Proof. exact (SYM (@lem1289234 N x)). Qed.
Lemma lem1289236 (N : nat) (x : nadd) (h1 : term377 N x) : term377 N x.
Proof. exact (h1). Qed.
Lemma lem1289239 (N : nat) (x : nadd) (h1 : term378 N x) : term378 N x.
Proof. exact (h1). Qed.
Lemma lem1289240 (N : nat) (x : nadd) : term379 N x.
Proof. exact (fun h0 : term378 N x => @lem1289239 N x h0). Qed.
Lemma lem1289241 (N : nat) (x : nadd) (h1 : term379 N x) : term379 N x.
Proof. exact (h1). Qed.
Lemma lem1289242 (N : nat) (x : nadd) (h1 : term378 N x) : term378 N x.
Proof. exact (h1). Qed.
Lemma lem1289243 (N : nat) (x : nadd) (h1 : term378 N x) (h2 : term379 N x) : term378 N x.
Proof. exact (@lem1289241 N x h2 (@lem1289242 N x h1)). Qed.
Lemma lem1289244 (N : nat) (x : nadd) (h1 : term378 N x) : term380 N x.
Proof. exact (fun h0 : term379 N x => @lem1289243 N x h1 h0). Qed.
Lemma lem1289245 (N : nat) (x : nadd) (h1 : term379 N x) : term379 N x.
Proof. exact (h1). Qed.
Lemma lem1289246 (N : nat) (x : nadd) (h1 : term378 N x) (h2 : term379 N x) : term378 N x.
Proof. exact (@lem1289244 N x h1 (@lem1289245 N x h2)). Qed.
Lemma lem1289247 (N : nat) (x : nadd) (h1 : term379 N x) : term379 N x.
Proof. exact (fun h0 : term378 N x => @lem1289246 N x h0 h1). Qed.
Lemma lem1289248 (N : nat) (x : nadd) : term381 N x.
Proof. exact (fun h0 : term379 N x => @lem1289247 N x h0). Qed.
Lemma lem1289251 (N : nat) (x : nadd) : term379 N x.
Proof. exact (@lem1289248 N x (@lem1289240 N x)). Qed.
Lemma lem1289275 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1289276 : term382 = term383.
Proof. exact (@lem1289275 term384). Qed.
Lemma lem1289297 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem1289298 : term385 = term386.
Proof. exact (MK_COMB (@lem1289297) (@lem1289276)). Qed.
Lemma lem1289301 : term387 = term387.
Proof. exact (eq_refl term387). Qed.
Lemma lem1289302 : term388 = term389.
Proof. exact (MK_COMB (@lem1289301) (@lem1289298)). Qed.
Lemma lem1289305 (N : nat) (x : nadd) : (term390 N x) = (term390 N x).
Proof. exact (eq_refl (term390 N x)). Qed.
Lemma lem1289306 (N : nat) (x : nadd) : (term378 N x) = (term391 N x).
Proof. exact (MK_COMB (@lem1289305 N x) (@lem1289302)). Qed.
Lemma lem1289309 (x : nadd) : (term392 x) = (term393 x).
Proof. exact (fun_ext (fun N : nat => @lem1289306 N x)). Qed.
Lemma lem1289310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1289311 (x : nadd) : (term394 x) = (term395 x).
Proof. exact (MK_COMB (@lem1289310) (@lem1289309 x)). Qed.
Lemma lem1289316 : term396 = term397.
Proof. exact (fun_ext (fun x : nadd => @lem1289311 x)). Qed.
Lemma lem1289317 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289326 : term398 = term399.
Proof. exact (MK_COMB (@lem1289317) (@lem1289316)). Qed.
Lemma lem1289335 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term400 x y x' y') = (term400 x y x' y').
Proof. exact (eq_refl (term400 x y x' y')). Qed.
Lemma lem1289336 (x : nadd) (y : nadd) (x' : nadd) : (term401 x y x') = (term401 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1289335 x y x' y')). Qed.
Lemma lem1289337 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289338 (x : nadd) (y : nadd) (x' : nadd) : (term402 x y x') = (term402 x y x').
Proof. exact (MK_COMB (@lem1289337) (@lem1289336 x y x')). Qed.
Lemma lem1289339 (x : nadd) (x' : nadd) : (term403 x x') = (term403 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1289338 x y x')). Qed.
Lemma lem1289340 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289341 (x : nadd) (x' : nadd) : (term404 x x') = (term404 x x').
Proof. exact (MK_COMB (@lem1289340) (@lem1289339 x x')). Qed.
Lemma lem1289342 (x : nadd) : (term405 x) = (term405 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1289341 x x')). Qed.
Lemma lem1289343 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289344 (x : nadd) : (term406 x) = (term406 x).
Proof. exact (MK_COMB (@lem1289343) (@lem1289342 x)). Qed.
Lemma lem1289345 : term407 = term407.
Proof. exact (fun_ext (fun x : nadd => @lem1289344 x)). Qed.
Lemma lem1289346 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289347 : term384 = term384.
Proof. exact (MK_COMB (@lem1289346) (@lem1289345)). Qed.
Lemma lem1289348 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1289349 : term383 = term383.
Proof. exact (MK_COMB (@lem1289348) (@lem1289347)). Qed.
Lemma lem1289350 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1289351 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1289350 x)). Qed.
Lemma lem1289352 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289353 : term194 = term194.
Proof. exact (MK_COMB (@lem1289352) (@lem1289351)). Qed.
Lemma lem1289354 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1289355 : term164 = term164.
Proof. exact (MK_COMB (@lem1289354) (@lem1289353)). Qed.
Lemma lem1289356 : term386 = term386.
Proof. exact (MK_COMB (@lem1289355) (@lem1289349)). Qed.
Lemma lem1289357 (x : nadd) : (term408 x) = (term408 x).
Proof. exact (eq_refl (term408 x)). Qed.
Lemma lem1289358 : term409 = term409.
Proof. exact (fun_ext (fun x : nadd => @lem1289357 x)). Qed.
Lemma lem1289359 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289360 : term410 = term410.
Proof. exact (MK_COMB (@lem1289359) (@lem1289358)). Qed.
Lemma lem1289361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1289362 : term387 = term387.
Proof. exact (MK_COMB (@lem1289361) (@lem1289360)). Qed.
Lemma lem1289363 : term389 = term389.
Proof. exact (MK_COMB (@lem1289362) (@lem1289356)). Qed.
Lemma lem1289368 (N : nat) (x : nadd) : (term390 N x) = (term390 N x).
Proof. exact (eq_refl (term390 N x)). Qed.
Lemma lem1289369 (N : nat) (x : nadd) : (term391 N x) = (term391 N x).
Proof. exact (MK_COMB (@lem1289368 N x) (@lem1289363)). Qed.
Lemma lem1289370 (x : nadd) : (term393 x) = (term393 x).
Proof. exact (fun_ext (fun N : nat => @lem1289369 N x)). Qed.
Lemma lem1289371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1289372 (x : nadd) : (term395 x) = (term395 x).
Proof. exact (MK_COMB (@lem1289371) (@lem1289370 x)). Qed.
Lemma lem1289373 : term397 = term397.
Proof. exact (fun_ext (fun x : nadd => @lem1289372 x)). Qed.
Lemma lem1289374 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289375 : term399 = term399.
Proof. exact (MK_COMB (@lem1289374) (@lem1289373)). Qed.
Lemma lem1289436 : term398 = term399.
Proof. exact (TRANS (@lem1289326) (@lem1289375)). Qed.
Lemma lem1289437 : term399 = term398.
Proof. exact (SYM (@lem1289436)). Qed.
Lemma lem1289439 (h1 : term410) : term410.
Proof. exact (h1). Qed.
Lemma lem1289440 (h1 : term194) : term194.
Proof. exact (h1). Qed.
Lemma lem1289441 (h1 : term384) : term384.
Proof. exact (h1). Qed.
Lemma lem1289447 (N : nat) (x : nadd) (h1 : term377 N x) : term377 N x.
Proof. exact (h1). Qed.
Lemma lem1289448 (x : nadd) : (term408 x) = (term408 x).
Proof. exact (eq_refl (term408 x)). Qed.
Lemma lem1289449 : term409 = term409.
Proof. exact (fun_ext (fun x : nadd => @lem1289448 x)). Qed.
Lemma lem1289450 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289459 : term410 = term410.
Proof. exact (MK_COMB (@lem1289450) (@lem1289449)). Qed.
Lemma lem1289460 (h1 : term410) : term410.
Proof. exact (EQ_MP (@lem1289459) (@lem1289439 h1)). Qed.
Lemma lem1289461 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1289462 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1289461 x)). Qed.
Lemma lem1289463 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289472 : term194 = term194.
Proof. exact (MK_COMB (@lem1289463) (@lem1289462)). Qed.
Lemma lem1289473 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1289472) (@lem1289440 h1)). Qed.
Lemma lem1289480 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term253 x x' y y') = (term254 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1289481 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term411 x y x' y') = (term411 x y x' y').
Proof. exact (eq_refl (term411 x y x' y')). Qed.
Lemma lem1289482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1289483 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term256 x x' y y') = (term257 x x' y y').
Proof. exact (MK_COMB (@lem1289482) (@lem1289480 x x' y y')). Qed.
Lemma lem1289484 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term412 x y x' y') = (term413 x y x' y').
Proof. exact (MK_COMB (@lem1289483 x x' y y') (@lem1289481 x y x' y')). Qed.
Lemma lem1289485 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term400 x y x' y') = (term412 x y x' y').
Proof. exact (@lem17265 (term260 x x' y y') (term411 x y x' y')). Qed.
Lemma lem1289486 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term400 x y x' y') = (term413 x y x' y').
Proof. exact (TRANS (@lem1289485 x y x' y') (@lem1289484 x y x' y')). Qed.
Lemma lem1289487 (x : nadd) (y : nadd) (x' : nadd) : (term401 x y x') = (term414 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1289486 x y x' y')). Qed.
Lemma lem1289488 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289489 (x : nadd) (y : nadd) (x' : nadd) : (term402 x y x') = (term415 x y x').
Proof. exact (MK_COMB (@lem1289488) (@lem1289487 x y x')). Qed.
Lemma lem1289490 (x : nadd) (x' : nadd) : (term403 x x') = (term416 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1289489 x y x')). Qed.
Lemma lem1289491 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289492 (x : nadd) (x' : nadd) : (term404 x x') = (term417 x x').
Proof. exact (MK_COMB (@lem1289491) (@lem1289490 x x')). Qed.
Lemma lem1289493 (x : nadd) : (term405 x) = (term418 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1289492 x x')). Qed.
Lemma lem1289494 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289495 (x : nadd) : (term406 x) = (term419 x).
Proof. exact (MK_COMB (@lem1289494) (@lem1289493 x)). Qed.
Lemma lem1289496 : term407 = term420.
Proof. exact (fun_ext (fun x : nadd => @lem1289495 x)). Qed.
Lemma lem1289497 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289562 : term384 = term421.
Proof. exact (MK_COMB (@lem1289497) (@lem1289496)). Qed.
Lemma lem1289563 (h1 : term384) : term421.
Proof. exact (EQ_MP (@lem1289562) (@lem1289441 h1)). Qed.
Lemma lem1289601 (N : nat) (x : nadd) (h1 : term377 N x) : term377 N x.
Proof. exact (h1). Qed.
Lemma lem1289616 (x : nadd) : (term408 x) = (term408 x).
Proof. exact (eq_refl (term408 x)). Qed.
Lemma lem1289617 : term409 = term409.
Proof. exact (fun_ext (fun x : nadd => @lem1289616 x)). Qed.
Lemma lem1289618 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289619 : term410 = term410.
Proof. exact (MK_COMB (@lem1289618) (@lem1289617)). Qed.
Lemma lem1289620 (h1 : term410) : term410.
Proof. exact (EQ_MP (@lem1289619) (@lem1289460 h1)). Qed.
Lemma lem1289625 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1289626 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1289625 x)). Qed.
Lemma lem1289627 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289628 : term194 = term194.
Proof. exact (MK_COMB (@lem1289627) (@lem1289626)). Qed.
Lemma lem1289629 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1289628) (@lem1289473 h1)). Qed.
Lemma lem1289662 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term413 x y x' y') = (term413 x y x' y').
Proof. exact (eq_refl (term413 x y x' y')). Qed.
Lemma lem1289663 (x : nadd) (y : nadd) (x' : nadd) : (term414 x y x') = (term414 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1289662 x y x' y')). Qed.
Lemma lem1289664 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289665 (x : nadd) (y : nadd) (x' : nadd) : (term415 x y x') = (term415 x y x').
Proof. exact (MK_COMB (@lem1289664) (@lem1289663 x y x')). Qed.
Lemma lem1289666 (x : nadd) (x' : nadd) : (term416 x x') = (term416 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1289665 x y x')). Qed.
Lemma lem1289667 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289668 (x : nadd) (x' : nadd) : (term417 x x') = (term417 x x').
Proof. exact (MK_COMB (@lem1289667) (@lem1289666 x x')). Qed.
Lemma lem1289669 (x : nadd) : (term418 x) = (term418 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1289668 x x')). Qed.
Lemma lem1289670 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289671 (x : nadd) : (term419 x) = (term419 x).
Proof. exact (MK_COMB (@lem1289670) (@lem1289669 x)). Qed.
Lemma lem1289672 : term420 = term420.
Proof. exact (fun_ext (fun x : nadd => @lem1289671 x)). Qed.
Lemma lem1289673 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289674 : term421 = term421.
Proof. exact (MK_COMB (@lem1289673) (@lem1289672)). Qed.
Lemma lem1289675 (h1 : term384) : term421.
Proof. exact (EQ_MP (@lem1289674) (@lem1289563 h1)). Qed.
Lemma lem1289679 (N : nat) (x : nadd) (h1 : term377 N x) : term377 N x.
Proof. exact (h1). Qed.
Lemma lem1289681 (x : nadd) : (term408 x) = (term408 x).
Proof. exact (eq_refl (term408 x)). Qed.
Lemma lem1289682 : term409 = term409.
Proof. exact (fun_ext (fun x : nadd => @lem1289681 x)). Qed.
Lemma lem1289683 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289685 : term410 = term410.
Proof. exact (MK_COMB (@lem1289683) (@lem1289682)). Qed.
Lemma lem1289686 (h1 : term410) : term410.
Proof. exact (EQ_MP (@lem1289685) (@lem1289620 h1)). Qed.
Lemma lem1289688 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1289689 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1289688 x)). Qed.
Lemma lem1289690 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289692 : term194 = term194.
Proof. exact (MK_COMB (@lem1289690) (@lem1289689)). Qed.
Lemma lem1289693 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1289692) (@lem1289629 h1)). Qed.
Lemma lem1289707 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term413 x y x' y') = (term413 x y x' y').
Proof. exact (eq_refl (term413 x y x' y')). Qed.
Lemma lem1289708 (x : nadd) (y : nadd) (x' : nadd) : (term414 x y x') = (term414 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1289707 x y x' y')). Qed.
Lemma lem1289709 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289710 (x : nadd) (y : nadd) (x' : nadd) : (term415 x y x') = (term415 x y x').
Proof. exact (MK_COMB (@lem1289709) (@lem1289708 x y x')). Qed.
Lemma lem1289711 (x : nadd) (x' : nadd) : (term416 x x') = (term416 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1289710 x y x')). Qed.
Lemma lem1289712 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289713 (x : nadd) (x' : nadd) : (term417 x x') = (term417 x x').
Proof. exact (MK_COMB (@lem1289712) (@lem1289711 x x')). Qed.
Lemma lem1289714 (x : nadd) : (term418 x) = (term418 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1289713 x x')). Qed.
Lemma lem1289715 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289716 (x : nadd) : (term419 x) = (term419 x).
Proof. exact (MK_COMB (@lem1289715) (@lem1289714 x)). Qed.
Lemma lem1289717 : term420 = term420.
Proof. exact (fun_ext (fun x : nadd => @lem1289716 x)). Qed.
Lemma lem1289718 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1289720 : term421 = term421.
Proof. exact (MK_COMB (@lem1289718) (@lem1289717)). Qed.
Lemma lem1289721 (h1 : term384) : term421.
Proof. exact (EQ_MP (@lem1289720) (@lem1289675 h1)). Qed.
Lemma lem1289722 (_23283 : nadd) (h1 : term410) : term422 _23283.
Proof. exact (@lem1289686 h1 _23283). Qed.
Lemma lem1289723 (_23283 : nadd) : (term422 _23283) = (term408 _23283).
Proof. exact (eq_refl (term422 _23283)). Qed.
Lemma lem1289725 (_23284 : nadd) (h1 : term194) : term269 _23284.
Proof. exact (@lem1289693 h1 _23284). Qed.
Lemma lem1289726 (_23284 : nadd) : (term269 _23284) = (nadd_eq _23284 _23284).
Proof. exact (eq_refl (term269 _23284)). Qed.
Lemma lem1289728 (_23285 : nadd) (h1 : term384) : term423 _23285.
Proof. exact (@lem1289721 h1 _23285). Qed.
Lemma lem1289729 (_23285 : nadd) : (term423 _23285) = (term419 _23285).
Proof. exact (eq_refl (term423 _23285)). Qed.
Lemma lem1289730 (_23285 : nadd) (h1 : term384) : term419 _23285.
Proof. exact (EQ_MP (@lem1289729 _23285) (@lem1289728 _23285 h1)). Qed.
Lemma lem1289731 (_23285 : nadd) (_23286 : nadd) (h1 : term384) : term424 _23285 _23286.
Proof. exact (@lem1289730 _23285 h1 _23286). Qed.
Lemma lem1289732 (_23285 : nadd) (_23286 : nadd) : (term424 _23285 _23286) = (term417 _23285 _23286).
Proof. exact (eq_refl (term424 _23285 _23286)). Qed.
Lemma lem1289733 (_23285 : nadd) (_23286 : nadd) (h1 : term384) : term417 _23285 _23286.
Proof. exact (EQ_MP (@lem1289732 _23285 _23286) (@lem1289731 _23285 _23286 h1)). Qed.
Lemma lem1289734 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (h1 : term384) : term425 _23285 _23286 _23287.
Proof. exact (@lem1289733 _23285 _23286 h1 _23287). Qed.
Lemma lem1289735 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) : (term425 _23285 _23286 _23287) = (term415 _23285 _23287 _23286).
Proof. exact (eq_refl (term425 _23285 _23286 _23287)). Qed.
Lemma lem1289736 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (h1 : term384) : term415 _23285 _23287 _23286.
Proof. exact (EQ_MP (@lem1289735 _23285 _23287 _23286) (@lem1289734 _23285 _23286 _23287 h1)). Qed.
Lemma lem1289737 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) (h1 : term384) : term426 _23285 _23287 _23286 _23288.
Proof. exact (@lem1289736 _23285 _23287 _23286 h1 _23288). Qed.
Lemma lem1289738 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) : (term426 _23285 _23287 _23286 _23288) = (term413 _23285 _23287 _23286 _23288).
Proof. exact (eq_refl (term426 _23285 _23287 _23286 _23288)). Qed.
Lemma lem1289739 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) (h1 : term384) : term413 _23285 _23287 _23286 _23288.
Proof. exact (EQ_MP (@lem1289738 _23285 _23287 _23286 _23288) (@lem1289737 _23285 _23287 _23286 _23288 h1)). Qed.
Lemma lem1289741 (N : nat) (x : nadd) (h1 : term377 N x) : term377 N x.
Proof. exact (h1). Qed.
Lemma lem1289756 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) : (term413 _23285 _23287 _23286 _23288) = (term427 _23285 _23287 _23286 _23288).
Proof. exact (@lem1286587 (term277 _23285 _23286) (term277 _23287 _23288) (term411 _23285 _23287 _23286 _23288)). Qed.
Lemma lem1289757 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) (h1 : term384) : term427 _23285 _23287 _23286 _23288.
Proof. exact (EQ_MP (@lem1289756 _23285 _23287 _23286 _23288) (@lem1289739 _23285 _23287 _23286 _23288 h1)). Qed.
Lemma lem1289759 (_23283 : nadd) (h1 : term410) : term408 _23283.
Proof. exact (EQ_MP (@lem1289723 _23283) (@lem1289722 _23283 h1)). Qed.
Lemma lem1289760 (x : nadd) (h1 : term410) : term408 x.
Proof. exact (@lem1289759 x h1). Qed.
Lemma lem1289761 (x : nadd) (h1 : term410) : term428 x.
Proof. exact (fun h0 : term429 x => @lem1289760 x h1). Qed.
Lemma lem1289763 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1289764 (x : nadd) : (term428 x) = (term408 x).
Proof. exact (@lem1289763 (term408 x)). Qed.
Lemma lem1289765 (x : nadd) (h1 : term410) : term408 x.
Proof. exact (EQ_MP (@lem1289764 x) (@lem1289761 x h1)). Qed.
Lemma lem1289767 (_23284 : nadd) (h1 : term194) : nadd_eq _23284 _23284.
Proof. exact (EQ_MP (@lem1289726 _23284) (@lem1289725 _23284 h1)). Qed.
Lemma lem1289768 (N : nat) (x : nadd) (h1 : term194) : term430 N x.
Proof. exact (@lem1289767 (term431 N x) h1). Qed.
Lemma lem1289769 (N : nat) (x : nadd) (h1 : term194) : term432 N x.
Proof. exact (fun h0 : term433 N x => @lem1289768 N x h1). Qed.
Lemma lem1289771 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1289772 (N : nat) (x : nadd) : (term432 N x) = (term430 N x).
Proof. exact (@lem1289771 (term430 N x)). Qed.
Lemma lem1289773 (N : nat) (x : nadd) (h1 : term194) : term430 N x.
Proof. exact (EQ_MP (@lem1289772 N x) (@lem1289769 N x h1)). Qed.
Lemma lem1289789 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1289790 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term434 _23285 _23287 _23286 _23288) = (term435 _23285 _23286 _23287 _23288).
Proof. exact (@lem1289789 (term411 _23285 _23287 _23286 _23288) (term277 _23287 _23288)). Qed.
Lemma lem1289796 (_23285 : nadd) (_23286 : nadd) : (term286 _23285 _23286) = (term286 _23285 _23286).
Proof. exact (eq_refl (term286 _23285 _23286)). Qed.
Lemma lem1289797 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term427 _23285 _23287 _23286 _23288) = (term436 _23285 _23286 _23287 _23288).
Proof. exact (MK_COMB (@lem1289796 _23285 _23286) (@lem1289790 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289801 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1289802 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term436 _23285 _23286 _23287 _23288) = (term437 _23285 _23286 _23287 _23288).
Proof. exact (@lem1289801 (term411 _23285 _23287 _23286 _23288) (term277 _23285 _23286) (term277 _23287 _23288)). Qed.
Lemma lem1289818 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term427 _23285 _23287 _23286 _23288) = (term437 _23285 _23286 _23287 _23288).
Proof. exact (TRANS (@lem1289797 _23285 _23286 _23287 _23288) (@lem1289802 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1289820 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term438 _23285 _23287 _23286 _23288) = (term439 _23285 _23286 _23287 _23288).
Proof. exact (MK_COMB (@lem1289819) (@lem1289818 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289836 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term437 _23285 _23286 _23287 _23288) = (term437 _23285 _23286 _23287 _23288).
Proof. exact (eq_refl (term437 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289837 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : ((term427 _23285 _23287 _23286 _23288) = (term437 _23285 _23286 _23287 _23288)) = ((term437 _23285 _23286 _23287 _23288) = (term437 _23285 _23286 _23287 _23288)).
Proof. exact (MK_COMB (@lem1289820 _23285 _23286 _23287 _23288) (@lem1289836 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289839 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1289840 (x : Prop) : (x = x) = True.
Proof. exact (@lem1289839 Prop x). Qed.
Lemma lem1289841 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : ((term437 _23285 _23286 _23287 _23288) = (term437 _23285 _23286 _23287 _23288)) = True.
Proof. exact (@lem1289840 (term437 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289842 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : ((term427 _23285 _23287 _23286 _23288) = (term437 _23285 _23286 _23287 _23288)) = True.
Proof. exact (TRANS (@lem1289837 _23285 _23286 _23287 _23288) (@lem1289841 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289843 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : True = ((term427 _23285 _23287 _23286 _23288) = (term437 _23285 _23286 _23287 _23288)).
Proof. exact (SYM (@lem1289842 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289844 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term427 _23285 _23287 _23286 _23288) = (term437 _23285 _23286 _23287 _23288).
Proof. exact (EQ_MP (@lem1289843 _23285 _23286 _23287 _23288) (@lem0)). Qed.
Lemma lem1289845 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) (h1 : term384) : term437 _23285 _23286 _23287 _23288.
Proof. exact (EQ_MP (@lem1289844 _23285 _23286 _23287 _23288) (@lem1289757 _23285 _23287 _23286 _23288 h1)). Qed.
Lemma lem1289847 (b : Prop) (a : Prop) : (a \/ b) = (term291 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1289848 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) : (term437 _23285 _23286 _23287 _23288) = (term440 _23285 _23287 _23286 _23288).
Proof. exact (@lem1289847 (term254 _23285 _23286 _23287 _23288) (term411 _23285 _23287 _23286 _23288)). Qed.
Lemma lem1289850 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1289851 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term295 _23285 _23286 _23287 _23288) = (term296 _23285 _23286 _23287 _23288).
Proof. exact (@lem1289850 (term277 _23285 _23286) (term277 _23287 _23288)). Qed.
Lemma lem1289853 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1289854 (_23285 : nadd) (_23286 : nadd) : (term297 _23285 _23286) = (nadd_eq _23285 _23286).
Proof. exact (@lem1289853 (nadd_eq _23285 _23286)). Qed.
Lemma lem1289855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1289856 (_23285 : nadd) (_23286 : nadd) : (term298 _23285 _23286) = (term299 _23285 _23286).
Proof. exact (MK_COMB (@lem1289855) (@lem1289854 _23285 _23286)). Qed.
Lemma lem1289858 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1289859 (_23287 : nadd) (_23288 : nadd) : (term297 _23287 _23288) = (nadd_eq _23287 _23288).
Proof. exact (@lem1289858 (nadd_eq _23287 _23288)). Qed.
Lemma lem1289860 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term296 _23285 _23286 _23287 _23288) = (term260 _23285 _23286 _23287 _23288).
Proof. exact (MK_COMB (@lem1289856 _23285 _23286) (@lem1289859 _23287 _23288)). Qed.
Lemma lem1289861 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term295 _23285 _23286 _23287 _23288) = (term260 _23285 _23286 _23287 _23288).
Proof. exact (TRANS (@lem1289851 _23285 _23286 _23287 _23288) (@lem1289860 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1289863 (_23285 : nadd) (_23286 : nadd) (_23287 : nadd) (_23288 : nadd) : (term300 _23285 _23286 _23287 _23288) = (term301 _23285 _23286 _23287 _23288).
Proof. exact (MK_COMB (@lem1289862) (@lem1289861 _23285 _23286 _23287 _23288)). Qed.
Lemma lem1289864 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) : (term411 _23285 _23287 _23286 _23288) = (term411 _23285 _23287 _23286 _23288).
Proof. exact (eq_refl (term411 _23285 _23287 _23286 _23288)). Qed.
Lemma lem1289865 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) : (term440 _23285 _23287 _23286 _23288) = (term400 _23285 _23287 _23286 _23288).
Proof. exact (MK_COMB (@lem1289863 _23285 _23286 _23287 _23288) (@lem1289864 _23285 _23287 _23286 _23288)). Qed.
Lemma lem1289866 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) : (term437 _23285 _23286 _23287 _23288) = (term400 _23285 _23287 _23286 _23288).
Proof. exact (TRANS (@lem1289848 _23285 _23287 _23286 _23288) (@lem1289865 _23285 _23287 _23286 _23288)). Qed.
Lemma lem1289868 (N : nat) (x : nadd) (h1 : term194) (h2 : term410) : term441 N x.
Proof. exact (conj (@lem1289765 x h2) (@lem1289773 N x h1)). Qed.
Lemma lem1289870 (_23285 : nadd) (_23287 : nadd) (_23286 : nadd) (_23288 : nadd) (h1 : term384) : term400 _23285 _23287 _23286 _23288.
Proof. exact (EQ_MP (@lem1289866 _23285 _23287 _23286 _23288) (@lem1289845 _23285 _23286 _23287 _23288 h1)). Qed.
Lemma lem1289871 (N : nat) (x : nadd) (h1 : term384) : term442 N x.
Proof. exact (@lem1289870 (term443 x) (term431 N x) x (term431 N x) h1). Qed.
Lemma lem1289874 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) : term375 N x.
Proof. exact (@lem1289871 N x h1 (@lem1289868 N x h2 h3)). Qed.
Lemma lem1289875 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) : term444 N x.
Proof. exact (fun h0 : term377 N x => @lem1289874 N x h1 h2 h3). Qed.
Lemma lem1289877 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1289878 (N : nat) (x : nadd) : (term444 N x) = (term375 N x).
Proof. exact (@lem1289877 (term375 N x)). Qed.
Lemma lem1289879 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) : term375 N x.
Proof. exact (EQ_MP (@lem1289878 N x) (@lem1289875 N x h1 h2 h3)). Qed.
Lemma lem1289882 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1289884 (N : nat) (x : nadd) : (term377 N x) = (term445 N x).
Proof. exact (@lem1289882 (term375 N x)). Qed.
Lemma lem1289887 (N : nat) (x : nadd) (h1 : term377 N x) : term445 N x.
Proof. exact (EQ_MP (@lem1289884 N x) (@lem1289741 N x h1)). Qed.
Lemma lem1289890 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (@lem1289887 N x h4 (@lem1289879 N x h1 h2 h3)). Qed.
Lemma lem1289891 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : term318.
Proof. exact (fun h0 : ~ False => @lem1289890 N x h1 h2 h3 h4). Qed.
Lemma lem1289893 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1289894 : term318 = False.
Proof. exact (@lem1289893 False). Qed.
Lemma lem1289895 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289894) (@lem1289891 N x h1 h2 h3 h4)). Qed.
Lemma lem1289896 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : (term377 N x) = False.
Proof. exact (prop_ext (fun h5 : term377 N x => @lem1289895 N x h1 h2 h3 h4) (fun h5 : False => @lem1289741 N x h4)). Qed.
Lemma lem1289897 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289896 N x h1 h2 h3 h4) (@lem1289741 N x h4)). Qed.
Lemma lem1289898 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : (term377 N x) = False.
Proof. exact (prop_ext (fun h5 : term377 N x => @lem1289897 N x h1 h2 h3 h4) (fun h5 : False => @lem1289679 N x h4)). Qed.
Lemma lem1289899 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289898 N x h1 h2 h3 h4) (@lem1289679 N x h4)). Qed.
Lemma lem1289900 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : term194 = False.
Proof. exact (prop_ext (fun h5 : term194 => @lem1289899 N x h1 h2 h3 h4) (fun h5 : False => @lem1289693 h2)). Qed.
Lemma lem1289901 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289900 N x h1 h2 h3 h4) (@lem1289693 h2)). Qed.
Lemma lem1289902 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : term410 = False.
Proof. exact (prop_ext (fun h5 : term410 => @lem1289901 N x h1 h2 h3 h4) (fun h5 : False => @lem1289686 h3)). Qed.
Lemma lem1289903 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289902 N x h1 h2 h3 h4) (@lem1289686 h3)). Qed.
Lemma lem1289904 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : (term377 N x) = False.
Proof. exact (prop_ext (fun h5 : term377 N x => @lem1289903 N x h1 h2 h3 h4) (fun h5 : False => @lem1289679 N x h4)). Qed.
Lemma lem1289905 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289904 N x h1 h2 h3 h4) (@lem1289679 N x h4)). Qed.
Lemma lem1289906 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : term194 = False.
Proof. exact (prop_ext (fun h5 : term194 => @lem1289905 N x h1 h2 h3 h4) (fun h5 : False => @lem1289629 h2)). Qed.
Lemma lem1289907 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289906 N x h1 h2 h3 h4) (@lem1289629 h2)). Qed.
Lemma lem1289908 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : term410 = False.
Proof. exact (prop_ext (fun h5 : term410 => @lem1289907 N x h1 h2 h3 h4) (fun h5 : False => @lem1289620 h3)). Qed.
Lemma lem1289909 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289908 N x h1 h2 h3 h4) (@lem1289620 h3)). Qed.
Lemma lem1289910 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : (term377 N x) = False.
Proof. exact (prop_ext (fun h5 : term377 N x => @lem1289909 N x h1 h2 h3 h4) (fun h5 : False => @lem1289601 N x h4)). Qed.
Lemma lem1289911 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289910 N x h1 h2 h3 h4) (@lem1289601 N x h4)). Qed.
Lemma lem1289912 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : term194 = False.
Proof. exact (prop_ext (fun h5 : term194 => @lem1289911 N x h1 h2 h3 h4) (fun h5 : False => @lem1289473 h2)). Qed.
Lemma lem1289913 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289912 N x h1 h2 h3 h4) (@lem1289473 h2)). Qed.
Lemma lem1289914 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : term410 = False.
Proof. exact (prop_ext (fun h5 : term410 => @lem1289913 N x h1 h2 h3 h4) (fun h5 : False => @lem1289460 h3)). Qed.
Lemma lem1289915 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289914 N x h1 h2 h3 h4) (@lem1289460 h3)). Qed.
Lemma lem1289916 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : (term377 N x) = False.
Proof. exact (prop_ext (fun h5 : term377 N x => @lem1289915 N x h1 h2 h3 h4) (fun h5 : False => @lem1289447 N x h4)). Qed.
Lemma lem1289917 (N : nat) (x : nadd) (h1 : term384) (h2 : term194) (h3 : term410) (h4 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289916 N x h1 h2 h3 h4) (@lem1289447 N x h4)). Qed.
Lemma lem1289918 (N : nat) (x : nadd) (h1 : term194) (h2 : term410) (h3 : term377 N x) : term382.
Proof. exact (fun h0 : term384 => @lem1289917 N x h0 h1 h2 h3). Qed.
Lemma lem1289919 : term382 = term383.
Proof. exact (@lem69 term384). Qed.
Lemma lem1289920 (N : nat) (x : nadd) (h1 : term194) (h2 : term410) (h3 : term377 N x) : term383.
Proof. exact (EQ_MP (@lem1289919) (@lem1289918 N x h1 h2 h3)). Qed.
Lemma lem1289921 (N : nat) (x : nadd) (h1 : term410) (h2 : term377 N x) : term386.
Proof. exact (fun h0 : term194 => @lem1289920 N x h0 h1 h2). Qed.
Lemma lem1289922 (N : nat) (x : nadd) (h1 : term377 N x) : term389.
Proof. exact (fun h0 : term410 => @lem1289921 N x h0 h1). Qed.
Lemma lem1289923 (N : nat) (x : nadd) : term391 N x.
Proof. exact (fun h0 : term377 N x => @lem1289922 N x h0). Qed.
Lemma lem1289928 (x : nadd) : term395 x.
Proof. exact (fun N : nat => @lem1289923 N x). Qed.
Lemma lem1289933 : term399.
Proof. exact (fun x : nadd => @lem1289928 x). Qed.
Lemma lem1289934 : term398.
Proof. exact (EQ_MP (@lem1289437) (@lem1289933)). Qed.
Lemma lem1289935 (x : nadd) : term446 x.
Proof. exact (@lem1289934 x). Qed.
Lemma lem1289936 (x : nadd) : (term446 x) = (term394 x).
Proof. exact (eq_refl (term446 x)). Qed.
Lemma lem1289937 (x : nadd) : term394 x.
Proof. exact (EQ_MP (@lem1289936 x) (@lem1289935 x)). Qed.
Lemma lem1289938 (x : nadd) (N : nat) : term447 x N.
Proof. exact (@lem1289937 x N). Qed.
Lemma lem1289939 (N : nat) (x : nadd) : (term447 x N) = (term378 N x).
Proof. exact (eq_refl (term447 x N)). Qed.
Lemma lem1289940 (N : nat) (x : nadd) : term378 N x.
Proof. exact (EQ_MP (@lem1289939 N x) (@lem1289938 x N)). Qed.
Lemma lem1289942 (N : nat) (x : nadd) : term378 N x.
Proof. exact (@lem1289251 N x (@lem1289940 N x)). Qed.
Lemma lem1289943 (N : nat) (x : nadd) (h1 : term377 N x) : term388.
Proof. exact (@lem1289942 N x (@lem1289236 N x h1)). Qed.
Lemma lem1289944 (N : nat) (x : nadd) (h1 : term377 N x) : term385.
Proof. exact (@lem1289943 N x h1 (@lem1278627)). Qed.
Lemma lem1289945 (N : nat) (x : nadd) (h1 : term377 N x) : term382.
Proof. exact (@lem1289944 N x h1 (@lem1267990)). Qed.
Lemma lem1289946 (N : nat) (x : nadd) (h1 : term377 N x) : False.
Proof. exact (@lem1289945 N x h1 (@lem1274424)). Qed.
Lemma lem1289947 (N : nat) (x : nadd) (h1 : term377 N x) : (term377 N x) = False.
Proof. exact (prop_ext (fun h2 : term377 N x => @lem1289946 N x h1) (fun h2 : False => @lem1289236 N x h1)). Qed.
Lemma lem1289948 (N : nat) (x : nadd) (h1 : term377 N x) : False.
Proof. exact (EQ_MP (@lem1289947 N x h1) (@lem1289236 N x h1)). Qed.
Lemma lem1289949 (N : nat) (x : nadd) : term376 N x.
Proof. exact (fun h0 : term377 N x => @lem1289948 N x h0). Qed.
Lemma lem1289950 (N : nat) (x : nadd) : term375 N x.
Proof. exact (EQ_MP (@lem1289235 N x) (@lem1289949 N x)). Qed.
Lemma lem1289951 (N : nat) (x : nadd) : term448 N x.
Proof. exact (conj (@lem1289231 N x) (@lem1289950 N x)). Qed.
Lemma lem1289952 (N : nat) (x : nadd) : term449 N x.
Proof. exact (ex_intro (term450 N x) (term149 N x) (@lem1289951 N x)). Qed.
Lemma lem1289953 (N : nat) (x : nadd) : term146 N x.
Proof. exact (@lem1286876 N x (@lem1289952 N x)). Qed.
Lemma lem1289954 (N : nat) (x : nadd) : term134 N x.
Proof. exact (EQ_MP (@lem1286873 N x) (@lem1289953 N x)). Qed.
Lemma lem1289956 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1289957 (N : nat) (x : nadd) (k : nadd) : (term451 N x k) = (term452 N x k).
Proof. exact (@lem1289956 (term451 N x k)). Qed.
Lemma lem1289958 (N : nat) (x : nadd) (k : nadd) : (term452 N x k) = (term451 N x k).
Proof. exact (SYM (@lem1289957 N x k)). Qed.
Lemma lem1289959 (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) : term453 N x k.
Proof. exact (h1). Qed.
Lemma lem1289962 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term454 p N x k) : term454 p N x k.
Proof. exact (h1). Qed.
Lemma lem1289963 (p : nat) (N : nat) (x : nadd) (k : nadd) : term455 p N x k.
Proof. exact (fun h0 : term454 p N x k => @lem1289962 p N x k h0). Qed.
Lemma lem1289964 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term455 p N x k) : term455 p N x k.
Proof. exact (h1). Qed.
Lemma lem1289965 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term454 p N x k) : term454 p N x k.
Proof. exact (h1). Qed.
Lemma lem1289966 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term455 p N x k) (h2 : term454 p N x k) : term454 p N x k.
Proof. exact (@lem1289964 p N x k h1 (@lem1289965 p N x k h2)). Qed.
Lemma lem1289967 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term454 p N x k) : term456 p N x k.
Proof. exact (fun h0 : term455 p N x k => @lem1289966 p N x k h0 h1). Qed.
Lemma lem1289968 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term455 p N x k) : term455 p N x k.
Proof. exact (h1). Qed.
Lemma lem1289969 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term455 p N x k) (h2 : term454 p N x k) : term454 p N x k.
Proof. exact (@lem1289967 p N x k h2 (@lem1289968 p N x k h1)). Qed.
Lemma lem1289970 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term455 p N x k) : term455 p N x k.
Proof. exact (fun h0 : term454 p N x k => @lem1289969 p N x k h1 h0). Qed.
Lemma lem1289971 (p : nat) (N : nat) (x : nadd) (k : nadd) : term457 p N x k.
Proof. exact (fun h0 : term455 p N x k => @lem1289970 p N x k h0). Qed.
Lemma lem1289974 (p : nat) (N : nat) (x : nadd) (k : nadd) : term455 p N x k.
Proof. exact (@lem1289971 p N x k (@lem1289963 p N x k)). Qed.
Lemma lem1290008 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1290009 : term458 = term459.
Proof. exact (@lem1290008 term460). Qed.
Lemma lem1290030 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem1290031 : term461 = term462.
Proof. exact (MK_COMB (@lem1290030) (@lem1290009)). Qed.
Lemma lem1290034 (N : nat) (x : nadd) (k : nadd) : (term463 N x k) = (term463 N x k).
Proof. exact (eq_refl (term463 N x k)). Qed.
Lemma lem1290035 (N : nat) (x : nadd) (k : nadd) : (term464 N x k) = (term465 N x k).
Proof. exact (MK_COMB (@lem1290034 N x k) (@lem1290031)). Qed.
Lemma lem1290038 (N : nat) (x : nadd) (k : nadd) : (term466 N x k) = (term466 N x k).
Proof. exact (eq_refl (term466 N x k)). Qed.
Lemma lem1290039 (N : nat) (x : nadd) (k : nadd) : (term467 N x k) = (term468 N x k).
Proof. exact (MK_COMB (@lem1290038 N x k) (@lem1290035 N x k)). Qed.
Lemma lem1290042 (p : nat) (N : nat) (x : nadd) : (term469 p N x) = (term469 p N x).
Proof. exact (eq_refl (term469 p N x)). Qed.
Lemma lem1290043 (p : nat) (N : nat) (x : nadd) (k : nadd) : (term470 p N x k) = (term471 p N x k).
Proof. exact (MK_COMB (@lem1290042 p N x) (@lem1290039 N x k)). Qed.
Lemma lem1290046 (k : nadd) (p : nat) : (term472 k p) = (term472 k p).
Proof. exact (eq_refl (term472 k p)). Qed.
Lemma lem1290047 (p : nat) (N : nat) (x : nadd) (k : nadd) : (term454 p N x k) = (term473 p N x k).
Proof. exact (MK_COMB (@lem1290046 k p) (@lem1290043 p N x k)). Qed.
Lemma lem1290050 (N : nat) (x : nadd) (k : nadd) : (term474 N x k) = (term475 N x k).
Proof. exact (fun_ext (fun p : nat => @lem1290047 p N x k)). Qed.
Lemma lem1290051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1290052 (N : nat) (x : nadd) (k : nadd) : (term476 N x k) = (term477 N x k).
Proof. exact (MK_COMB (@lem1290051) (@lem1290050 N x k)). Qed.
Lemma lem1290057 (x : nadd) (k : nadd) : (term478 x k) = (term479 x k).
Proof. exact (fun_ext (fun N : nat => @lem1290052 N x k)). Qed.
Lemma lem1290058 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1290059 (x : nadd) (k : nadd) : (term480 x k) = (term481 x k).
Proof. exact (MK_COMB (@lem1290058) (@lem1290057 x k)). Qed.
Lemma lem1290064 (k : nadd) : (term482 k) = (term483 k).
Proof. exact (fun_ext (fun x : nadd => @lem1290059 x k)). Qed.
Lemma lem1290065 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290066 (k : nadd) : (term484 k) = (term485 k).
Proof. exact (MK_COMB (@lem1290065) (@lem1290064 k)). Qed.
Lemma lem1290071 : term486 = term487.
Proof. exact (fun_ext (fun k : nadd => @lem1290066 k)). Qed.
Lemma lem1290072 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290081 : term488 = term489.
Proof. exact (MK_COMB (@lem1290072) (@lem1290071)). Qed.
Lemma lem1290094 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term490 x y x' y') = (term490 x y x' y').
Proof. exact (eq_refl (term490 x y x' y')). Qed.
Lemma lem1290095 (x : nadd) (y : nadd) (x' : nadd) : (term491 x y x') = (term491 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1290094 x y x' y')). Qed.
Lemma lem1290096 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290097 (x : nadd) (y : nadd) (x' : nadd) : (term492 x y x') = (term492 x y x').
Proof. exact (MK_COMB (@lem1290096) (@lem1290095 x y x')). Qed.
Lemma lem1290098 (x : nadd) (x' : nadd) : (term493 x x') = (term493 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1290097 x y x')). Qed.
Lemma lem1290099 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290100 (x : nadd) (x' : nadd) : (term494 x x') = (term494 x x').
Proof. exact (MK_COMB (@lem1290099) (@lem1290098 x x')). Qed.
Lemma lem1290101 (x : nadd) : (term495 x) = (term495 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1290100 x x')). Qed.
Lemma lem1290102 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290103 (x : nadd) : (term496 x) = (term496 x).
Proof. exact (MK_COMB (@lem1290102) (@lem1290101 x)). Qed.
Lemma lem1290104 : term497 = term497.
Proof. exact (fun_ext (fun x : nadd => @lem1290103 x)). Qed.
Lemma lem1290105 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290106 : term460 = term460.
Proof. exact (MK_COMB (@lem1290105) (@lem1290104)). Qed.
Lemma lem1290107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1290108 : term459 = term459.
Proof. exact (MK_COMB (@lem1290107) (@lem1290106)). Qed.
Lemma lem1290109 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1290110 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1290109 x)). Qed.
Lemma lem1290111 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290112 : term194 = term194.
Proof. exact (MK_COMB (@lem1290111) (@lem1290110)). Qed.
Lemma lem1290113 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1290114 : term164 = term164.
Proof. exact (MK_COMB (@lem1290113) (@lem1290112)). Qed.
Lemma lem1290115 : term462 = term462.
Proof. exact (MK_COMB (@lem1290114) (@lem1290108)). Qed.
Lemma lem1290124 (N : nat) (x : nadd) (k : nadd) : (term463 N x k) = (term463 N x k).
Proof. exact (eq_refl (term463 N x k)). Qed.
Lemma lem1290125 (N : nat) (x : nadd) (k : nadd) : (term465 N x k) = (term465 N x k).
Proof. exact (MK_COMB (@lem1290124 N x k) (@lem1290115)). Qed.
Lemma lem1290128 (N : nat) (x : nadd) (k : nadd) : (term466 N x k) = (term466 N x k).
Proof. exact (eq_refl (term466 N x k)). Qed.
Lemma lem1290129 (N : nat) (x : nadd) (k : nadd) : (term468 N x k) = (term468 N x k).
Proof. exact (MK_COMB (@lem1290128 N x k) (@lem1290125 N x k)). Qed.
Lemma lem1290132 (p : nat) (N : nat) (x : nadd) : (term469 p N x) = (term469 p N x).
Proof. exact (eq_refl (term469 p N x)). Qed.
Lemma lem1290133 (p : nat) (N : nat) (x : nadd) (k : nadd) : (term471 p N x k) = (term471 p N x k).
Proof. exact (MK_COMB (@lem1290132 p N x) (@lem1290129 N x k)). Qed.
Lemma lem1290136 (k : nadd) (p : nat) : (term472 k p) = (term472 k p).
Proof. exact (eq_refl (term472 k p)). Qed.
Lemma lem1290137 (p : nat) (N : nat) (x : nadd) (k : nadd) : (term473 p N x k) = (term473 p N x k).
Proof. exact (MK_COMB (@lem1290136 k p) (@lem1290133 p N x k)). Qed.
Lemma lem1290138 (N : nat) (x : nadd) (k : nadd) : (term475 N x k) = (term475 N x k).
Proof. exact (fun_ext (fun p : nat => @lem1290137 p N x k)). Qed.
Lemma lem1290139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1290140 (N : nat) (x : nadd) (k : nadd) : (term477 N x k) = (term477 N x k).
Proof. exact (MK_COMB (@lem1290139) (@lem1290138 N x k)). Qed.
Lemma lem1290141 (x : nadd) (k : nadd) : (term479 x k) = (term479 x k).
Proof. exact (fun_ext (fun N : nat => @lem1290140 N x k)). Qed.
Lemma lem1290142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1290143 (x : nadd) (k : nadd) : (term481 x k) = (term481 x k).
Proof. exact (MK_COMB (@lem1290142) (@lem1290141 x k)). Qed.
Lemma lem1290144 (k : nadd) : (term483 k) = (term483 k).
Proof. exact (fun_ext (fun x : nadd => @lem1290143 x k)). Qed.
Lemma lem1290145 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290146 (k : nadd) : (term485 k) = (term485 k).
Proof. exact (MK_COMB (@lem1290145) (@lem1290144 k)). Qed.
Lemma lem1290147 : term487 = term487.
Proof. exact (fun_ext (fun k : nadd => @lem1290146 k)). Qed.
Lemma lem1290148 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290149 : term489 = term489.
Proof. exact (MK_COMB (@lem1290148) (@lem1290147)). Qed.
Lemma lem1290222 : term488 = term489.
Proof. exact (TRANS (@lem1290081) (@lem1290149)). Qed.
Lemma lem1290223 : term489 = term488.
Proof. exact (SYM (@lem1290222)). Qed.
Lemma lem1290227 (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) : term453 N x k.
Proof. exact (h1). Qed.
Lemma lem1290228 (h1 : term194) : term194.
Proof. exact (h1). Qed.
Lemma lem1290229 (h1 : term460) : term460.
Proof. exact (h1). Qed.
Lemma lem1290247 (N : nat) (x : nadd) (k : nadd) (h1 : term121 N x k) : term121 N x k.
Proof. exact (h1). Qed.
Lemma lem1290258 (N : nat) (x : nadd) (k : nadd) : (term453 N x k) = (term498 N x k).
Proof. exact (@lem17362 (term134 N x) (term499 N x k)). Qed.
Lemma lem1290260 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1290261 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1290260 x)). Qed.
Lemma lem1290262 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290271 : term194 = term194.
Proof. exact (MK_COMB (@lem1290262) (@lem1290261)). Qed.
Lemma lem1290272 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1290271) (@lem1290228 h1)). Qed.
Lemma lem1290279 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term253 x x' y y') = (term254 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1290294 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : ((nadd_le x y) = (nadd_le x' y')) = (term500 x y x' y').
Proof. exact (@lem17784 (nadd_le x y) (nadd_le x' y')). Qed.
Lemma lem1290295 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1290296 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term256 x x' y y') = (term257 x x' y y').
Proof. exact (MK_COMB (@lem1290295) (@lem1290279 x x' y y')). Qed.
Lemma lem1290297 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term501 x y x' y') = (term502 x y x' y').
Proof. exact (MK_COMB (@lem1290296 x x' y y') (@lem1290294 x y x' y')). Qed.
Lemma lem1290298 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term490 x y x' y') = (term501 x y x' y').
Proof. exact (@lem17265 (term260 x x' y y') ((nadd_le x y) = (nadd_le x' y'))). Qed.
Lemma lem1290299 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term490 x y x' y') = (term502 x y x' y').
Proof. exact (TRANS (@lem1290298 x y x' y') (@lem1290297 x y x' y')). Qed.
Lemma lem1290300 (x : nadd) (y : nadd) (x' : nadd) : (term491 x y x') = (term503 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1290299 x y x' y')). Qed.
Lemma lem1290301 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290302 (x : nadd) (y : nadd) (x' : nadd) : (term492 x y x') = (term504 x y x').
Proof. exact (MK_COMB (@lem1290301) (@lem1290300 x y x')). Qed.
Lemma lem1290303 (x : nadd) (x' : nadd) : (term493 x x') = (term505 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1290302 x y x')). Qed.
Lemma lem1290304 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290305 (x : nadd) (x' : nadd) : (term494 x x') = (term506 x x').
Proof. exact (MK_COMB (@lem1290304) (@lem1290303 x x')). Qed.
Lemma lem1290306 (x : nadd) : (term495 x) = (term507 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1290305 x x')). Qed.
Lemma lem1290307 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290308 (x : nadd) : (term496 x) = (term508 x).
Proof. exact (MK_COMB (@lem1290307) (@lem1290306 x)). Qed.
Lemma lem1290309 : term497 = term509.
Proof. exact (fun_ext (fun x : nadd => @lem1290308 x)). Qed.
Lemma lem1290310 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290375 : term460 = term510.
Proof. exact (MK_COMB (@lem1290310) (@lem1290309)). Qed.
Lemma lem1290376 (h1 : term460) : term510.
Proof. exact (EQ_MP (@lem1290375) (@lem1290229 h1)). Qed.
Lemma lem1290418 (N : nat) (x : nadd) (k : nadd) (h1 : term121 N x k) : term121 N x k.
Proof. exact (h1). Qed.
Lemma lem1290468 (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) : term498 N x k.
Proof. exact (EQ_MP (@lem1290258 N x k) (@lem1290227 N x k h1)). Qed.
Lemma lem1290473 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1290474 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1290473 x)). Qed.
Lemma lem1290475 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290476 : term194 = term194.
Proof. exact (MK_COMB (@lem1290475) (@lem1290474)). Qed.
Lemma lem1290477 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1290476) (@lem1290272 h1)). Qed.
Lemma lem1290530 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term502 x y x' y') = (term502 x y x' y').
Proof. exact (eq_refl (term502 x y x' y')). Qed.
Lemma lem1290531 (x : nadd) (y : nadd) (x' : nadd) : (term503 x y x') = (term503 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1290530 x y x' y')). Qed.
Lemma lem1290532 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290533 (x : nadd) (y : nadd) (x' : nadd) : (term504 x y x') = (term504 x y x').
Proof. exact (MK_COMB (@lem1290532) (@lem1290531 x y x')). Qed.
Lemma lem1290534 (x : nadd) (x' : nadd) : (term505 x x') = (term505 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1290533 x y x')). Qed.
Lemma lem1290535 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290536 (x : nadd) (x' : nadd) : (term506 x x') = (term506 x x').
Proof. exact (MK_COMB (@lem1290535) (@lem1290534 x x')). Qed.
Lemma lem1290537 (x : nadd) : (term507 x) = (term507 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1290536 x x')). Qed.
Lemma lem1290538 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290539 (x : nadd) : (term508 x) = (term508 x).
Proof. exact (MK_COMB (@lem1290538) (@lem1290537 x)). Qed.
Lemma lem1290540 : term509 = term509.
Proof. exact (fun_ext (fun x : nadd => @lem1290539 x)). Qed.
Lemma lem1290541 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290542 : term510 = term510.
Proof. exact (MK_COMB (@lem1290541) (@lem1290540)). Qed.
Lemma lem1290543 (h1 : term460) : term510.
Proof. exact (EQ_MP (@lem1290542) (@lem1290376 h1)). Qed.
Lemma lem1290557 (N : nat) (x : nadd) (k : nadd) (h1 : term121 N x k) : term121 N x k.
Proof. exact (h1). Qed.
Lemma lem1290559 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1290560 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1290559 x)). Qed.
Lemma lem1290561 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290563 : term194 = term194.
Proof. exact (MK_COMB (@lem1290561) (@lem1290560)). Qed.
Lemma lem1290564 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1290563) (@lem1290477 h1)). Qed.
Lemma lem1290600 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term502 x y x' y') = (term511 x y x' y').
Proof. exact (@lem19490 (term512 x y x' y') (term254 x x' y y') (term513 x y x' y')). Qed.
Lemma lem1290601 (x : nadd) (y : nadd) (x' : nadd) : (term503 x y x') = (term514 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1290600 x y x' y')). Qed.
Lemma lem1290602 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290603 (x : nadd) (y : nadd) (x' : nadd) : (term504 x y x') = (term515 x y x').
Proof. exact (MK_COMB (@lem1290602) (@lem1290601 x y x')). Qed.
Lemma lem1290604 (x : nadd) (x' : nadd) : (term505 x x') = (term516 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1290603 x y x')). Qed.
Lemma lem1290605 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290606 (x : nadd) (x' : nadd) : (term506 x x') = (term517 x x').
Proof. exact (MK_COMB (@lem1290605) (@lem1290604 x x')). Qed.
Lemma lem1290607 (x : nadd) : (term507 x) = (term518 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1290606 x x')). Qed.
Lemma lem1290608 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290609 (x : nadd) : (term508 x) = (term519 x).
Proof. exact (MK_COMB (@lem1290608) (@lem1290607 x)). Qed.
Lemma lem1290610 : term509 = term520.
Proof. exact (fun_ext (fun x : nadd => @lem1290609 x)). Qed.
Lemma lem1290611 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1290613 : term510 = term521.
Proof. exact (MK_COMB (@lem1290611) (@lem1290610)). Qed.
Lemma lem1290614 (h1 : term460) : term521.
Proof. exact (EQ_MP (@lem1290613) (@lem1290543 h1)). Qed.
Lemma lem1290623 (_23289 : nadd) (h1 : term194) : term269 _23289.
Proof. exact (@lem1290564 h1 _23289). Qed.
Lemma lem1290624 (_23289 : nadd) : (term269 _23289) = (nadd_eq _23289 _23289).
Proof. exact (eq_refl (term269 _23289)). Qed.
Lemma lem1290626 (_23290 : nadd) (h1 : term460) : term522 _23290.
Proof. exact (@lem1290614 h1 _23290). Qed.
Lemma lem1290627 (_23290 : nadd) : (term522 _23290) = (term519 _23290).
Proof. exact (eq_refl (term522 _23290)). Qed.
Lemma lem1290628 (_23290 : nadd) (h1 : term460) : term519 _23290.
Proof. exact (EQ_MP (@lem1290627 _23290) (@lem1290626 _23290 h1)). Qed.
Lemma lem1290629 (_23290 : nadd) (_23291 : nadd) (h1 : term460) : term523 _23290 _23291.
Proof. exact (@lem1290628 _23290 h1 _23291). Qed.
Lemma lem1290630 (_23290 : nadd) (_23291 : nadd) : (term523 _23290 _23291) = (term517 _23290 _23291).
Proof. exact (eq_refl (term523 _23290 _23291)). Qed.
Lemma lem1290631 (_23290 : nadd) (_23291 : nadd) (h1 : term460) : term517 _23290 _23291.
Proof. exact (EQ_MP (@lem1290630 _23290 _23291) (@lem1290629 _23290 _23291 h1)). Qed.
Lemma lem1290632 (_23290 : nadd) (_23291 : nadd) (_23292 : nadd) (h1 : term460) : term524 _23290 _23291 _23292.
Proof. exact (@lem1290631 _23290 _23291 h1 _23292). Qed.
Lemma lem1290633 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) : (term524 _23290 _23291 _23292) = (term515 _23290 _23292 _23291).
Proof. exact (eq_refl (term524 _23290 _23291 _23292)). Qed.
Lemma lem1290634 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (h1 : term460) : term515 _23290 _23292 _23291.
Proof. exact (EQ_MP (@lem1290633 _23290 _23292 _23291) (@lem1290632 _23290 _23291 _23292 h1)). Qed.
Lemma lem1290635 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) (h1 : term460) : term525 _23290 _23292 _23291 _23293.
Proof. exact (@lem1290634 _23290 _23292 _23291 h1 _23293). Qed.
Lemma lem1290636 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) : (term525 _23290 _23292 _23291 _23293) = (term511 _23290 _23292 _23291 _23293).
Proof. exact (eq_refl (term525 _23290 _23292 _23291 _23293)). Qed.
Lemma lem1290637 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) (h1 : term460) : term511 _23290 _23292 _23291 _23293.
Proof. exact (EQ_MP (@lem1290636 _23290 _23292 _23291 _23293) (@lem1290635 _23290 _23292 _23291 _23293 h1)). Qed.
Lemma lem1290638 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) (h1 : term460) : term526 _23290 _23292 _23291 _23293.
Proof. exact (proj2 (@lem1290637 _23290 _23292 _23291 _23293 h1)). Qed.
Lemma lem1290645 (N : nat) (x : nadd) (k : nadd) (h1 : term121 N x k) : term121 N x k.
Proof. exact (h1). Qed.
Lemma lem1290651 (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) : term527 N x k.
Proof. exact (proj2 (@lem1290468 N x k h1)). Qed.
Lemma lem1290682 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) : (term526 _23290 _23292 _23291 _23293) = (term528 _23290 _23292 _23291 _23293).
Proof. exact (@lem1286577 (term277 _23290 _23291) (term277 _23292 _23293) (term513 _23290 _23292 _23291 _23293)). Qed.
Lemma lem1290683 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) (h1 : term460) : term528 _23290 _23292 _23291 _23293.
Proof. exact (EQ_MP (@lem1290682 _23290 _23292 _23291 _23293) (@lem1290638 _23290 _23292 _23291 _23293 h1)). Qed.
Lemma lem1290685 (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) : term134 N x.
Proof. exact (proj1 (@lem1290468 N x k h1)). Qed.
Lemma lem1290686 (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) : term529 N x.
Proof. exact (fun h0 : term530 N x => @lem1290685 N x k h1). Qed.
Lemma lem1290688 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1290689 (N : nat) (x : nadd) : (term529 N x) = (term134 N x).
Proof. exact (@lem1290688 (term134 N x)). Qed.
Lemma lem1290690 (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) : term134 N x.
Proof. exact (EQ_MP (@lem1290689 N x) (@lem1290686 N x k h1)). Qed.
Lemma lem1290692 (_23289 : nadd) (h1 : term194) : nadd_eq _23289 _23289.
Proof. exact (EQ_MP (@lem1290624 _23289) (@lem1290623 _23289 h1)). Qed.
Lemma lem1290693 (k : nadd) (h1 : term194) : nadd_eq k k.
Proof. exact (@lem1290692 k h1). Qed.
Lemma lem1290694 (k : nadd) (h1 : term194) : term282 k.
Proof. exact (fun h0 : term283 k => @lem1290693 k h1). Qed.
Lemma lem1290696 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1290697 (k : nadd) : (term282 k) = (nadd_eq k k).
Proof. exact (@lem1290696 (nadd_eq k k)). Qed.
Lemma lem1290698 (k : nadd) (h1 : term194) : nadd_eq k k.
Proof. exact (EQ_MP (@lem1290697 k) (@lem1290694 k h1)). Qed.
Lemma lem1290700 (N : nat) (x : nadd) (k : nadd) (h1 : term121 N x k) : term121 N x k.
Proof. exact (h1). Qed.
Lemma lem1290701 (N : nat) (x : nadd) (k : nadd) (h1 : term121 N x k) : term531 N x k.
Proof. exact (fun h0 : term532 N x k => @lem1290700 N x k h1). Qed.
Lemma lem1290703 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1290704 (N : nat) (x : nadd) (k : nadd) : (term531 N x k) = (term121 N x k).
Proof. exact (@lem1290703 (term121 N x k)). Qed.
Lemma lem1290705 (N : nat) (x : nadd) (k : nadd) (h1 : term121 N x k) : term121 N x k.
Proof. exact (EQ_MP (@lem1290704 N x k) (@lem1290701 N x k h1)). Qed.
Lemma lem1290731 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1290732 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term513 _23290 _23292 _23291 _23293) = (term512 _23291 _23293 _23290 _23292).
Proof. exact (@lem1290731 (nadd_le _23291 _23293) (term533 _23290 _23292)). Qed.
Lemma lem1290738 (_23292 : nadd) (_23293 : nadd) : (term286 _23292 _23293) = (term286 _23292 _23293).
Proof. exact (eq_refl (term286 _23292 _23293)). Qed.
Lemma lem1290739 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term534 _23290 _23292 _23291 _23293) = (term535 _23291 _23293 _23290 _23292).
Proof. exact (MK_COMB (@lem1290738 _23292 _23293) (@lem1290732 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290743 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1290744 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term535 _23291 _23293 _23290 _23292) = (term536 _23291 _23293 _23290 _23292).
Proof. exact (@lem1290743 (nadd_le _23291 _23293) (term277 _23292 _23293) (term533 _23290 _23292)). Qed.
Lemma lem1290760 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term534 _23290 _23292 _23291 _23293) = (term536 _23291 _23293 _23290 _23292).
Proof. exact (TRANS (@lem1290739 _23291 _23293 _23290 _23292) (@lem1290744 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290761 (_23290 : nadd) (_23291 : nadd) : (term286 _23290 _23291) = (term286 _23290 _23291).
Proof. exact (eq_refl (term286 _23290 _23291)). Qed.
Lemma lem1290762 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term528 _23290 _23292 _23291 _23293) = (term537 _23291 _23293 _23290 _23292).
Proof. exact (MK_COMB (@lem1290761 _23290 _23291) (@lem1290760 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290766 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1290767 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term537 _23291 _23293 _23290 _23292) = (term538 _23291 _23293 _23290 _23292).
Proof. exact (@lem1290766 (nadd_le _23291 _23293) (term277 _23290 _23291) (term539 _23293 _23290 _23292)). Qed.
Lemma lem1290793 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term528 _23290 _23292 _23291 _23293) = (term538 _23291 _23293 _23290 _23292).
Proof. exact (TRANS (@lem1290762 _23291 _23293 _23290 _23292) (@lem1290767 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1290795 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term540 _23290 _23292 _23291 _23293) = (term541 _23291 _23293 _23290 _23292).
Proof. exact (MK_COMB (@lem1290794) (@lem1290793 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290821 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term538 _23291 _23293 _23290 _23292) = (term538 _23291 _23293 _23290 _23292).
Proof. exact (eq_refl (term538 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290822 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : ((term528 _23290 _23292 _23291 _23293) = (term538 _23291 _23293 _23290 _23292)) = ((term538 _23291 _23293 _23290 _23292) = (term538 _23291 _23293 _23290 _23292)).
Proof. exact (MK_COMB (@lem1290795 _23291 _23293 _23290 _23292) (@lem1290821 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290824 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1290825 (x : Prop) : (x = x) = True.
Proof. exact (@lem1290824 Prop x). Qed.
Lemma lem1290826 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : ((term538 _23291 _23293 _23290 _23292) = (term538 _23291 _23293 _23290 _23292)) = True.
Proof. exact (@lem1290825 (term538 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290827 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : ((term528 _23290 _23292 _23291 _23293) = (term538 _23291 _23293 _23290 _23292)) = True.
Proof. exact (TRANS (@lem1290822 _23291 _23293 _23290 _23292) (@lem1290826 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290828 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : True = ((term528 _23290 _23292 _23291 _23293) = (term538 _23291 _23293 _23290 _23292)).
Proof. exact (SYM (@lem1290827 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290829 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term528 _23290 _23292 _23291 _23293) = (term538 _23291 _23293 _23290 _23292).
Proof. exact (EQ_MP (@lem1290828 _23291 _23293 _23290 _23292) (@lem0)). Qed.
Lemma lem1290830 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) (h1 : term460) : term538 _23291 _23293 _23290 _23292.
Proof. exact (EQ_MP (@lem1290829 _23291 _23293 _23290 _23292) (@lem1290683 _23290 _23292 _23291 _23293 h1)). Qed.
Lemma lem1290832 (b : Prop) (a : Prop) : (a \/ b) = (term291 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1290833 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) : (term538 _23291 _23293 _23290 _23292) = (term542 _23290 _23292 _23291 _23293).
Proof. exact (@lem1290832 (term543 _23291 _23293 _23290 _23292) (nadd_le _23291 _23293)). Qed.
Lemma lem1290835 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1290836 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term544 _23291 _23293 _23290 _23292) = (term545 _23291 _23293 _23290 _23292).
Proof. exact (@lem1290835 (term277 _23290 _23291) (term539 _23293 _23290 _23292)). Qed.
Lemma lem1290838 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1290839 (_23290 : nadd) (_23291 : nadd) : (term297 _23290 _23291) = (nadd_eq _23290 _23291).
Proof. exact (@lem1290838 (nadd_eq _23290 _23291)). Qed.
Lemma lem1290840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1290841 (_23290 : nadd) (_23291 : nadd) : (term298 _23290 _23291) = (term299 _23290 _23291).
Proof. exact (MK_COMB (@lem1290840) (@lem1290839 _23290 _23291)). Qed.
Lemma lem1290843 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1290844 (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term546 _23293 _23290 _23292) = (term547 _23293 _23290 _23292).
Proof. exact (@lem1290843 (term277 _23292 _23293) (term533 _23290 _23292)). Qed.
Lemma lem1290846 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1290847 (_23292 : nadd) (_23293 : nadd) : (term297 _23292 _23293) = (nadd_eq _23292 _23293).
Proof. exact (@lem1290846 (nadd_eq _23292 _23293)). Qed.
Lemma lem1290848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1290849 (_23292 : nadd) (_23293 : nadd) : (term298 _23292 _23293) = (term299 _23292 _23293).
Proof. exact (MK_COMB (@lem1290848) (@lem1290847 _23292 _23293)). Qed.
Lemma lem1290851 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1290852 (_23290 : nadd) (_23292 : nadd) : (term548 _23290 _23292) = (nadd_le _23290 _23292).
Proof. exact (@lem1290851 (nadd_le _23290 _23292)). Qed.
Lemma lem1290853 (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term547 _23293 _23290 _23292) = (term549 _23293 _23290 _23292).
Proof. exact (MK_COMB (@lem1290849 _23292 _23293) (@lem1290852 _23290 _23292)). Qed.
Lemma lem1290854 (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term546 _23293 _23290 _23292) = (term549 _23293 _23290 _23292).
Proof. exact (TRANS (@lem1290844 _23293 _23290 _23292) (@lem1290853 _23293 _23290 _23292)). Qed.
Lemma lem1290855 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term545 _23291 _23293 _23290 _23292) = (term550 _23291 _23293 _23290 _23292).
Proof. exact (MK_COMB (@lem1290841 _23290 _23291) (@lem1290854 _23293 _23290 _23292)). Qed.
Lemma lem1290856 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term544 _23291 _23293 _23290 _23292) = (term550 _23291 _23293 _23290 _23292).
Proof. exact (TRANS (@lem1290836 _23291 _23293 _23290 _23292) (@lem1290855 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290857 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1290858 (_23291 : nadd) (_23293 : nadd) (_23290 : nadd) (_23292 : nadd) : (term551 _23291 _23293 _23290 _23292) = (term552 _23291 _23293 _23290 _23292).
Proof. exact (MK_COMB (@lem1290857) (@lem1290856 _23291 _23293 _23290 _23292)). Qed.
Lemma lem1290859 (_23291 : nadd) (_23293 : nadd) : (nadd_le _23291 _23293) = (nadd_le _23291 _23293).
Proof. exact (eq_refl (nadd_le _23291 _23293)). Qed.
Lemma lem1290860 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) : (term542 _23290 _23292 _23291 _23293) = (term553 _23290 _23292 _23291 _23293).
Proof. exact (MK_COMB (@lem1290858 _23291 _23293 _23290 _23292) (@lem1290859 _23291 _23293)). Qed.
Lemma lem1290861 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) : (term538 _23291 _23293 _23290 _23292) = (term553 _23290 _23292 _23291 _23293).
Proof. exact (TRANS (@lem1290833 _23290 _23292 _23291 _23293) (@lem1290860 _23290 _23292 _23291 _23293)). Qed.
Lemma lem1290863 (N : nat) (x : nadd) (k : nadd) (h1 : term194) (h2 : term121 N x k) : term554 N x k.
Proof. exact (conj (@lem1290698 k h1) (@lem1290705 N x k h2)). Qed.
Lemma lem1290864 (N : nat) (x : nadd) (k : nadd) (h1 : term194) (h2 : term453 N x k) (h3 : term121 N x k) : term555 N x k.
Proof. exact (conj (@lem1290690 N x k h2) (@lem1290863 N x k h1 h3)). Qed.
Lemma lem1290866 (_23290 : nadd) (_23292 : nadd) (_23291 : nadd) (_23293 : nadd) (h1 : term460) : term553 _23290 _23292 _23291 _23293.
Proof. exact (EQ_MP (@lem1290861 _23290 _23292 _23291 _23293) (@lem1290830 _23291 _23293 _23290 _23292 h1)). Qed.
Lemma lem1290867 (N : nat) (x : nadd) (k : nadd) (h1 : term460) : term556 N x k.
Proof. exact (@lem1290866 (term142 N x) k (term132 N x) k h1). Qed.
Lemma lem1290870 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : term499 N x k.
Proof. exact (@lem1290867 N x k h1 (@lem1290864 N x k h2 h3 h4)). Qed.
Lemma lem1290871 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : term557 N x k.
Proof. exact (fun h0 : term527 N x k => @lem1290870 N x k h1 h2 h3 h4). Qed.
Lemma lem1290873 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1290874 (N : nat) (x : nadd) (k : nadd) : (term557 N x k) = (term499 N x k).
Proof. exact (@lem1290873 (term499 N x k)). Qed.
Lemma lem1290875 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : term499 N x k.
Proof. exact (EQ_MP (@lem1290874 N x k) (@lem1290871 N x k h1 h2 h3 h4)). Qed.
Lemma lem1290878 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1290880 (N : nat) (x : nadd) (k : nadd) : (term527 N x k) = (term558 N x k).
Proof. exact (@lem1290878 (term499 N x k)). Qed.
Lemma lem1290883 (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) : term558 N x k.
Proof. exact (EQ_MP (@lem1290880 N x k) (@lem1290651 N x k h1)). Qed.
Lemma lem1290886 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (@lem1290883 N x k h3 (@lem1290875 N x k h1 h2 h3 h4)). Qed.
Lemma lem1290887 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : term318.
Proof. exact (fun h0 : ~ False => @lem1290886 N x k h1 h2 h3 h4). Qed.
Lemma lem1290889 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1290890 : term318 = False.
Proof. exact (@lem1290889 False). Qed.
Lemma lem1290891 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290890) (@lem1290887 N x k h1 h2 h3 h4)). Qed.
Lemma lem1290892 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : (term121 N x k) = False.
Proof. exact (prop_ext (fun h5 : term121 N x k => @lem1290891 N x k h1 h2 h3 h4) (fun h5 : False => @lem1290645 N x k h4)). Qed.
Lemma lem1290893 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290892 N x k h1 h2 h3 h4) (@lem1290645 N x k h4)). Qed.
Lemma lem1290894 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : (term121 N x k) = False.
Proof. exact (prop_ext (fun h5 : term121 N x k => @lem1290893 N x k h1 h2 h3 h4) (fun h5 : False => @lem1290557 N x k h4)). Qed.
Lemma lem1290895 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290894 N x k h1 h2 h3 h4) (@lem1290557 N x k h4)). Qed.
Lemma lem1290896 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : term194 = False.
Proof. exact (prop_ext (fun h5 : term194 => @lem1290895 N x k h1 h2 h3 h4) (fun h5 : False => @lem1290564 h2)). Qed.
Lemma lem1290897 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290896 N x k h1 h2 h3 h4) (@lem1290564 h2)). Qed.
Lemma lem1290898 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : (term121 N x k) = False.
Proof. exact (prop_ext (fun h5 : term121 N x k => @lem1290897 N x k h1 h2 h3 h4) (fun h5 : False => @lem1290557 N x k h4)). Qed.
Lemma lem1290899 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290898 N x k h1 h2 h3 h4) (@lem1290557 N x k h4)). Qed.
Lemma lem1290900 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : term194 = False.
Proof. exact (prop_ext (fun h5 : term194 => @lem1290899 N x k h1 h2 h3 h4) (fun h5 : False => @lem1290477 h2)). Qed.
Lemma lem1290901 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290900 N x k h1 h2 h3 h4) (@lem1290477 h2)). Qed.
Lemma lem1290902 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : (term121 N x k) = False.
Proof. exact (prop_ext (fun h5 : term121 N x k => @lem1290901 N x k h1 h2 h3 h4) (fun h5 : False => @lem1290418 N x k h4)). Qed.
Lemma lem1290903 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290902 N x k h1 h2 h3 h4) (@lem1290418 N x k h4)). Qed.
Lemma lem1290904 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : term194 = False.
Proof. exact (prop_ext (fun h5 : term194 => @lem1290903 N x k h1 h2 h3 h4) (fun h5 : False => @lem1290272 h2)). Qed.
Lemma lem1290905 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290904 N x k h1 h2 h3 h4) (@lem1290272 h2)). Qed.
Lemma lem1290906 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : (term121 N x k) = False.
Proof. exact (prop_ext (fun h5 : term121 N x k => @lem1290905 N x k h1 h2 h3 h4) (fun h5 : False => @lem1290247 N x k h4)). Qed.
Lemma lem1290907 (N : nat) (x : nadd) (k : nadd) (h1 : term460) (h2 : term194) (h3 : term453 N x k) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290906 N x k h1 h2 h3 h4) (@lem1290247 N x k h4)). Qed.
Lemma lem1290908 (N : nat) (x : nadd) (k : nadd) (h1 : term194) (h2 : term453 N x k) (h3 : term121 N x k) : term458.
Proof. exact (fun h0 : term460 => @lem1290907 N x k h0 h1 h2 h3). Qed.
Lemma lem1290909 : term458 = term459.
Proof. exact (@lem69 term460). Qed.
Lemma lem1290910 (N : nat) (x : nadd) (k : nadd) (h1 : term194) (h2 : term453 N x k) (h3 : term121 N x k) : term459.
Proof. exact (EQ_MP (@lem1290909) (@lem1290908 N x k h1 h2 h3)). Qed.
Lemma lem1290911 (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) (h2 : term121 N x k) : term462.
Proof. exact (fun h0 : term194 => @lem1290910 N x k h0 h1 h2). Qed.
Lemma lem1290912 (N : nat) (x : nadd) (k : nadd) (h1 : term121 N x k) : term465 N x k.
Proof. exact (fun h0 : term453 N x k => @lem1290911 N x k h0 h1). Qed.
Lemma lem1290913 (N : nat) (x : nadd) (k : nadd) : term468 N x k.
Proof. exact (fun h0 : term121 N x k => @lem1290912 N x k h0). Qed.
Lemma lem1290914 (p : nat) (N : nat) (x : nadd) (k : nadd) : term471 p N x k.
Proof. exact (fun h0 : term120 p N x => @lem1290913 N x k). Qed.
Lemma lem1290915 (p : nat) (N : nat) (x : nadd) (k : nadd) : term473 p N x k.
Proof. exact (fun h0 : term94 k p => @lem1290914 p N x k). Qed.
Lemma lem1290920 (N : nat) (x : nadd) (k : nadd) : term477 N x k.
Proof. exact (fun p : nat => @lem1290915 p N x k). Qed.
Lemma lem1290925 (x : nadd) (k : nadd) : term481 x k.
Proof. exact (fun N : nat => @lem1290920 N x k). Qed.
Lemma lem1290930 (k : nadd) : term485 k.
Proof. exact (fun x : nadd => @lem1290925 x k). Qed.
Lemma lem1290935 : term489.
Proof. exact (fun k : nadd => @lem1290930 k). Qed.
Lemma lem1290936 : term488.
Proof. exact (EQ_MP (@lem1290223) (@lem1290935)). Qed.
Lemma lem1290937 (k : nadd) : term559 k.
Proof. exact (@lem1290936 k). Qed.
Lemma lem1290938 (k : nadd) : (term559 k) = (term484 k).
Proof. exact (eq_refl (term559 k)). Qed.
Lemma lem1290939 (k : nadd) : term484 k.
Proof. exact (EQ_MP (@lem1290938 k) (@lem1290937 k)). Qed.
Lemma lem1290940 (k : nadd) (x : nadd) : term560 k x.
Proof. exact (@lem1290939 k x). Qed.
Lemma lem1290941 (x : nadd) (k : nadd) : (term560 k x) = (term480 x k).
Proof. exact (eq_refl (term560 k x)). Qed.
Lemma lem1290942 (x : nadd) (k : nadd) : term480 x k.
Proof. exact (EQ_MP (@lem1290941 x k) (@lem1290940 k x)). Qed.
Lemma lem1290943 (x : nadd) (k : nadd) (N : nat) : term561 x k N.
Proof. exact (@lem1290942 x k N). Qed.
Lemma lem1290944 (N : nat) (x : nadd) (k : nadd) : (term561 x k N) = (term476 N x k).
Proof. exact (eq_refl (term561 x k N)). Qed.
Lemma lem1290945 (N : nat) (x : nadd) (k : nadd) : term476 N x k.
Proof. exact (EQ_MP (@lem1290944 N x k) (@lem1290943 x k N)). Qed.
Lemma lem1290946 (N : nat) (x : nadd) (k : nadd) (p : nat) : term562 N x k p.
Proof. exact (@lem1290945 N x k p). Qed.
Lemma lem1290947 (p : nat) (N : nat) (x : nadd) (k : nadd) : (term562 N x k p) = (term454 p N x k).
Proof. exact (eq_refl (term562 N x k p)). Qed.
Lemma lem1290948 (p : nat) (N : nat) (x : nadd) (k : nadd) : term454 p N x k.
Proof. exact (EQ_MP (@lem1290947 p N x k) (@lem1290946 N x k p)). Qed.
Lemma lem1290950 (p : nat) (N : nat) (x : nadd) (k : nadd) : term454 p N x k.
Proof. exact (@lem1289974 p N x k (@lem1290948 p N x k)). Qed.
Lemma lem1290951 (N : nat) (x : nadd) (k : nadd) (p : nat) (h1 : term94 k p) : term470 p N x k.
Proof. exact (@lem1290950 p N x k (@lem1286787 k p h1)). Qed.
Lemma lem1290952 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term94 k p) (h2 : term120 p N x) : term467 N x k.
Proof. exact (@lem1290951 N x k p h1 (@lem1286828 p N x h2)). Qed.
Lemma lem1290953 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term464 N x k.
Proof. exact (@lem1290952 k p N x h1 h2 (@lem1286829 N x k h3)). Qed.
Lemma lem1290954 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : term461.
Proof. exact (@lem1290953 p N x k h2 h3 h4 (@lem1289959 N x k h1)). Qed.
Lemma lem1290955 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : term458.
Proof. exact (@lem1290954 p N x k h1 h2 h3 h4 (@lem1267990)). Qed.
Lemma lem1290956 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : False.
Proof. exact (@lem1290955 p N x k h1 h2 h3 h4 (@lem1270569)). Qed.
Lemma lem1290957 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : (term453 N x k) = False.
Proof. exact (prop_ext (fun h5 : term453 N x k => @lem1290956 p N x k h1 h2 h3 h4) (fun h5 : False => @lem1289959 N x k h1)). Qed.
Lemma lem1290958 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term453 N x k) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1290957 p N x k h1 h2 h3 h4) (@lem1289959 N x k h1)). Qed.
Lemma lem1290959 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term452 N x k.
Proof. exact (fun h0 : term453 N x k => @lem1290958 p N x k h0 h1 h2 h3). Qed.
Lemma lem1290960 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term451 N x k.
Proof. exact (EQ_MP (@lem1289958 N x k) (@lem1290959 p N x k h1 h2 h3)). Qed.
Lemma lem1290961 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term134 N x) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : term499 N x k.
Proof. exact (@lem1290960 p N x k h2 h3 h4 (@lem1286859 N x h1)). Qed.
Lemma lem1290962 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : (term134 N x) = (term499 N x k).
Proof. exact (prop_ext (fun h4 : term134 N x => @lem1290961 p N x k h4 h1 h2 h3) (fun h4 : term499 N x k => @lem1289954 N x)). Qed.
Lemma lem1290963 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term499 N x k.
Proof. exact (EQ_MP (@lem1290962 p N x k h1 h2 h3) (@lem1289954 N x)). Qed.
Lemma lem1290965 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1290966 (k : nadd) (N : nat) (x : nadd) : (term563 k N x) = (term564 k N x).
Proof. exact (@lem1290965 (term563 k N x)). Qed.
Lemma lem1290967 (k : nadd) (N : nat) (x : nadd) : (term564 k N x) = (term563 k N x).
Proof. exact (SYM (@lem1290966 k N x)). Qed.
Lemma lem1290968 (k : nadd) (N : nat) (x : nadd) (h1 : term565 k N x) : term565 k N x.
Proof. exact (h1). Qed.
Lemma lem1290971 (p : nat) (k : nadd) (N : nat) (x : nadd) (h1 : term566 p k N x) : term566 p k N x.
Proof. exact (h1). Qed.
Lemma lem1290972 (p : nat) (k : nadd) (N : nat) (x : nadd) : term567 p k N x.
Proof. exact (fun h0 : term566 p k N x => @lem1290971 p k N x h0). Qed.
Lemma lem1290973 (p : nat) (k : nadd) (N : nat) (x : nadd) (h1 : term567 p k N x) : term567 p k N x.
Proof. exact (h1). Qed.
Lemma lem1290974 (p : nat) (k : nadd) (N : nat) (x : nadd) (h1 : term566 p k N x) : term566 p k N x.
Proof. exact (h1). Qed.
Lemma lem1290975 (p : nat) (k : nadd) (N : nat) (x : nadd) (h1 : term567 p k N x) (h2 : term566 p k N x) : term566 p k N x.
Proof. exact (@lem1290973 p k N x h1 (@lem1290974 p k N x h2)). Qed.
Lemma lem1290976 (p : nat) (k : nadd) (N : nat) (x : nadd) (h1 : term566 p k N x) : term568 p k N x.
Proof. exact (fun h0 : term567 p k N x => @lem1290975 p k N x h0 h1). Qed.
Lemma lem1290977 (p : nat) (k : nadd) (N : nat) (x : nadd) (h1 : term567 p k N x) : term567 p k N x.
Proof. exact (h1). Qed.
Lemma lem1290978 (p : nat) (k : nadd) (N : nat) (x : nadd) (h1 : term567 p k N x) (h2 : term566 p k N x) : term566 p k N x.
Proof. exact (@lem1290976 p k N x h2 (@lem1290977 p k N x h1)). Qed.
Lemma lem1290979 (p : nat) (k : nadd) (N : nat) (x : nadd) (h1 : term567 p k N x) : term567 p k N x.
Proof. exact (fun h0 : term566 p k N x => @lem1290978 p k N x h1 h0). Qed.
Lemma lem1290980 (p : nat) (k : nadd) (N : nat) (x : nadd) : term569 p k N x.
Proof. exact (fun h0 : term567 p k N x => @lem1290979 p k N x h0). Qed.
Lemma lem1290983 (p : nat) (k : nadd) (N : nat) (x : nadd) : term567 p k N x.
Proof. exact (@lem1290980 p k N x (@lem1290972 p k N x)). Qed.
Lemma lem1291043 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1291044 : term570 = term571.
Proof. exact (@lem1291043 term27). Qed.
Lemma lem1291061 : term572 = term572.
Proof. exact (eq_refl term572). Qed.
Lemma lem1291062 : term573 = term574.
Proof. exact (MK_COMB (@lem1291061) (@lem1291044)). Qed.
Lemma lem1291065 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem1291066 : term575 = term576.
Proof. exact (MK_COMB (@lem1291065) (@lem1291062)). Qed.
Lemma lem1291069 : term577 = term577.
Proof. exact (eq_refl term577). Qed.
Lemma lem1291070 : term578 = term579.
Proof. exact (MK_COMB (@lem1291069) (@lem1291066)). Qed.
Lemma lem1291073 (k : nadd) (N : nat) (x : nadd) : (term580 k N x) = (term580 k N x).
Proof. exact (eq_refl (term580 k N x)). Qed.
Lemma lem1291074 (k : nadd) (N : nat) (x : nadd) : (term581 k N x) = (term582 k N x).
Proof. exact (MK_COMB (@lem1291073 k N x) (@lem1291070)). Qed.
Lemma lem1291077 (N : nat) (x : nadd) (k : nadd) : (term466 N x k) = (term466 N x k).
Proof. exact (eq_refl (term466 N x k)). Qed.
Lemma lem1291078 (k : nadd) (N : nat) (x : nadd) : (term583 k N x) = (term584 k N x).
Proof. exact (MK_COMB (@lem1291077 N x k) (@lem1291074 k N x)). Qed.
Lemma lem1291081 (p : nat) (N : nat) (x : nadd) : (term469 p N x) = (term469 p N x).
Proof. exact (eq_refl (term469 p N x)). Qed.
Lemma lem1291082 (p : nat) (k : nadd) (N : nat) (x : nadd) : (term585 p k N x) = (term586 p k N x).
Proof. exact (MK_COMB (@lem1291081 p N x) (@lem1291078 k N x)). Qed.
Lemma lem1291085 (k : nadd) (p : nat) : (term472 k p) = (term472 k p).
Proof. exact (eq_refl (term472 k p)). Qed.
Lemma lem1291086 (p : nat) (k : nadd) (N : nat) (x : nadd) : (term566 p k N x) = (term587 p k N x).
Proof. exact (MK_COMB (@lem1291085 k p) (@lem1291082 p k N x)). Qed.
Lemma lem1291089 (k : nadd) (N : nat) (x : nadd) : (term588 k N x) = (term589 k N x).
Proof. exact (fun_ext (fun p : nat => @lem1291086 p k N x)). Qed.
Lemma lem1291090 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1291091 (k : nadd) (N : nat) (x : nadd) : (term590 k N x) = (term591 k N x).
Proof. exact (MK_COMB (@lem1291090) (@lem1291089 k N x)). Qed.
Lemma lem1291096 (N : nat) (x : nadd) : (term592 N x) = (term593 N x).
Proof. exact (fun_ext (fun k : nadd => @lem1291091 k N x)). Qed.
Lemma lem1291097 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291098 (N : nat) (x : nadd) : (term594 N x) = (term595 N x).
Proof. exact (MK_COMB (@lem1291097) (@lem1291096 N x)). Qed.
Lemma lem1291103 (x : nadd) : (term596 x) = (term597 x).
Proof. exact (fun_ext (fun N : nat => @lem1291098 N x)). Qed.
Lemma lem1291104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1291105 (x : nadd) : (term598 x) = (term599 x).
Proof. exact (MK_COMB (@lem1291104) (@lem1291103 x)). Qed.
Lemma lem1291110 : term600 = term601.
Proof. exact (fun_ext (fun x : nadd => @lem1291105 x)). Qed.
Lemma lem1291111 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291120 : term602 = term603.
Proof. exact (MK_COMB (@lem1291111) (@lem1291110)). Qed.
Lemma lem1291129 (y : nadd) (x : nadd) (z : nadd) : (term33 y x z) = (term33 y x z).
Proof. exact (eq_refl (term33 y x z)). Qed.
Lemma lem1291130 (y : nadd) (x : nadd) : (term604 y x) = (term604 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1291129 y x z)). Qed.
Lemma lem1291131 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291132 (y : nadd) (x : nadd) : (term31 y x) = (term31 y x).
Proof. exact (MK_COMB (@lem1291131) (@lem1291130 y x)). Qed.
Lemma lem1291133 (x : nadd) : (term605 x) = (term605 x).
Proof. exact (fun_ext (fun y : nadd => @lem1291132 y x)). Qed.
Lemma lem1291134 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291135 (x : nadd) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1291134) (@lem1291133 x)). Qed.
Lemma lem1291136 : term606 = term606.
Proof. exact (fun_ext (fun x : nadd => @lem1291135 x)). Qed.
Lemma lem1291137 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291138 : term27 = term27.
Proof. exact (MK_COMB (@lem1291137) (@lem1291136)). Qed.
Lemma lem1291139 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1291140 : term571 = term571.
Proof. exact (MK_COMB (@lem1291139) (@lem1291138)). Qed.
Lemma lem1291153 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term490 x y x' y') = (term490 x y x' y').
Proof. exact (eq_refl (term490 x y x' y')). Qed.
Lemma lem1291154 (x : nadd) (y : nadd) (x' : nadd) : (term491 x y x') = (term491 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1291153 x y x' y')). Qed.
Lemma lem1291155 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291156 (x : nadd) (y : nadd) (x' : nadd) : (term492 x y x') = (term492 x y x').
Proof. exact (MK_COMB (@lem1291155) (@lem1291154 x y x')). Qed.
Lemma lem1291157 (x : nadd) (x' : nadd) : (term493 x x') = (term493 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1291156 x y x')). Qed.
Lemma lem1291158 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291159 (x : nadd) (x' : nadd) : (term494 x x') = (term494 x x').
Proof. exact (MK_COMB (@lem1291158) (@lem1291157 x x')). Qed.
Lemma lem1291160 (x : nadd) : (term495 x) = (term495 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1291159 x x')). Qed.
Lemma lem1291161 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291162 (x : nadd) : (term496 x) = (term496 x).
Proof. exact (MK_COMB (@lem1291161) (@lem1291160 x)). Qed.
Lemma lem1291163 : term497 = term497.
Proof. exact (fun_ext (fun x : nadd => @lem1291162 x)). Qed.
Lemma lem1291164 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291165 : term460 = term460.
Proof. exact (MK_COMB (@lem1291164) (@lem1291163)). Qed.
Lemma lem1291166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1291167 : term572 = term572.
Proof. exact (MK_COMB (@lem1291166) (@lem1291165)). Qed.
Lemma lem1291168 : term574 = term574.
Proof. exact (MK_COMB (@lem1291167) (@lem1291140)). Qed.
Lemma lem1291169 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1291170 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1291169 x)). Qed.
Lemma lem1291171 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291172 : term194 = term194.
Proof. exact (MK_COMB (@lem1291171) (@lem1291170)). Qed.
Lemma lem1291173 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1291174 : term164 = term164.
Proof. exact (MK_COMB (@lem1291173) (@lem1291172)). Qed.
Lemma lem1291175 : term576 = term576.
Proof. exact (MK_COMB (@lem1291174) (@lem1291168)). Qed.
Lemma lem1291176 (x : nadd) : (term607 x) = (term607 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1291177 : term608 = term608.
Proof. exact (fun_ext (fun x : nadd => @lem1291176 x)). Qed.
Lemma lem1291178 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291179 : term609 = term609.
Proof. exact (MK_COMB (@lem1291178) (@lem1291177)). Qed.
Lemma lem1291180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1291181 : term577 = term577.
Proof. exact (MK_COMB (@lem1291180) (@lem1291179)). Qed.
Lemma lem1291182 : term579 = term579.
Proof. exact (MK_COMB (@lem1291181) (@lem1291175)). Qed.
Lemma lem1291187 (k : nadd) (N : nat) (x : nadd) : (term580 k N x) = (term580 k N x).
Proof. exact (eq_refl (term580 k N x)). Qed.
Lemma lem1291188 (k : nadd) (N : nat) (x : nadd) : (term582 k N x) = (term582 k N x).
Proof. exact (MK_COMB (@lem1291187 k N x) (@lem1291182)). Qed.
Lemma lem1291191 (N : nat) (x : nadd) (k : nadd) : (term466 N x k) = (term466 N x k).
Proof. exact (eq_refl (term466 N x k)). Qed.
Lemma lem1291192 (k : nadd) (N : nat) (x : nadd) : (term584 k N x) = (term584 k N x).
Proof. exact (MK_COMB (@lem1291191 N x k) (@lem1291188 k N x)). Qed.
Lemma lem1291195 (p : nat) (N : nat) (x : nadd) : (term469 p N x) = (term469 p N x).
Proof. exact (eq_refl (term469 p N x)). Qed.
Lemma lem1291196 (p : nat) (k : nadd) (N : nat) (x : nadd) : (term586 p k N x) = (term586 p k N x).
Proof. exact (MK_COMB (@lem1291195 p N x) (@lem1291192 k N x)). Qed.
Lemma lem1291199 (k : nadd) (p : nat) : (term472 k p) = (term472 k p).
Proof. exact (eq_refl (term472 k p)). Qed.
Lemma lem1291200 (p : nat) (k : nadd) (N : nat) (x : nadd) : (term587 p k N x) = (term587 p k N x).
Proof. exact (MK_COMB (@lem1291199 k p) (@lem1291196 p k N x)). Qed.
Lemma lem1291201 (k : nadd) (N : nat) (x : nadd) : (term589 k N x) = (term589 k N x).
Proof. exact (fun_ext (fun p : nat => @lem1291200 p k N x)). Qed.
Lemma lem1291202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1291203 (k : nadd) (N : nat) (x : nadd) : (term591 k N x) = (term591 k N x).
Proof. exact (MK_COMB (@lem1291202) (@lem1291201 k N x)). Qed.
Lemma lem1291204 (N : nat) (x : nadd) : (term593 N x) = (term593 N x).
Proof. exact (fun_ext (fun k : nadd => @lem1291203 k N x)). Qed.
Lemma lem1291205 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291206 (N : nat) (x : nadd) : (term595 N x) = (term595 N x).
Proof. exact (MK_COMB (@lem1291205) (@lem1291204 N x)). Qed.
Lemma lem1291207 (x : nadd) : (term597 x) = (term597 x).
Proof. exact (fun_ext (fun N : nat => @lem1291206 N x)). Qed.
Lemma lem1291208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1291209 (x : nadd) : (term599 x) = (term599 x).
Proof. exact (MK_COMB (@lem1291208) (@lem1291207 x)). Qed.
Lemma lem1291210 : term601 = term601.
Proof. exact (fun_ext (fun x : nadd => @lem1291209 x)). Qed.
Lemma lem1291211 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291212 : term603 = term603.
Proof. exact (MK_COMB (@lem1291211) (@lem1291210)). Qed.
Lemma lem1291315 : term602 = term603.
Proof. exact (TRANS (@lem1291120) (@lem1291212)). Qed.
Lemma lem1291316 : term603 = term602.
Proof. exact (SYM (@lem1291315)). Qed.
Lemma lem1291321 (h1 : term609) : term609.
Proof. exact (h1). Qed.
Lemma lem1291322 (h1 : term194) : term194.
Proof. exact (h1). Qed.
Lemma lem1291323 (h1 : term460) : term460.
Proof. exact (h1). Qed.
Lemma lem1291324 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1291330 (k : nadd) (p : nat) (h1 : term94 k p) : term94 k p.
Proof. exact (h1). Qed.
Lemma lem1291336 (p : nat) (N : nat) (x : nadd) (h1 : term120 p N x) : term120 p N x.
Proof. exact (h1). Qed.
Lemma lem1291348 (k : nadd) (N : nat) (x : nadd) (h1 : term565 k N x) : term565 k N x.
Proof. exact (h1). Qed.
Lemma lem1291349 (x : nadd) : (term607 x) = (term607 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1291350 : term608 = term608.
Proof. exact (fun_ext (fun x : nadd => @lem1291349 x)). Qed.
Lemma lem1291351 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291360 : term609 = term609.
Proof. exact (MK_COMB (@lem1291351) (@lem1291350)). Qed.
Lemma lem1291361 (h1 : term609) : term609.
Proof. exact (EQ_MP (@lem1291360) (@lem1291321 h1)). Qed.
Lemma lem1291362 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1291363 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1291362 x)). Qed.
Lemma lem1291364 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291373 : term194 = term194.
Proof. exact (MK_COMB (@lem1291364) (@lem1291363)). Qed.
Lemma lem1291374 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1291373) (@lem1291322 h1)). Qed.
Lemma lem1291381 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term253 x x' y y') = (term254 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1291396 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : ((nadd_le x y) = (nadd_le x' y')) = (term500 x y x' y').
Proof. exact (@lem17784 (nadd_le x y) (nadd_le x' y')). Qed.
Lemma lem1291397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1291398 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term256 x x' y y') = (term257 x x' y y').
Proof. exact (MK_COMB (@lem1291397) (@lem1291381 x x' y y')). Qed.
Lemma lem1291399 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term501 x y x' y') = (term502 x y x' y').
Proof. exact (MK_COMB (@lem1291398 x x' y y') (@lem1291396 x y x' y')). Qed.
Lemma lem1291400 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term490 x y x' y') = (term501 x y x' y').
Proof. exact (@lem17265 (term260 x x' y y') ((nadd_le x y) = (nadd_le x' y'))). Qed.
Lemma lem1291401 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term490 x y x' y') = (term502 x y x' y').
Proof. exact (TRANS (@lem1291400 x y x' y') (@lem1291399 x y x' y')). Qed.
Lemma lem1291402 (x : nadd) (y : nadd) (x' : nadd) : (term491 x y x') = (term503 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1291401 x y x' y')). Qed.
Lemma lem1291403 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291404 (x : nadd) (y : nadd) (x' : nadd) : (term492 x y x') = (term504 x y x').
Proof. exact (MK_COMB (@lem1291403) (@lem1291402 x y x')). Qed.
Lemma lem1291405 (x : nadd) (x' : nadd) : (term493 x x') = (term505 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1291404 x y x')). Qed.
Lemma lem1291406 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291407 (x : nadd) (x' : nadd) : (term494 x x') = (term506 x x').
Proof. exact (MK_COMB (@lem1291406) (@lem1291405 x x')). Qed.
Lemma lem1291408 (x : nadd) : (term495 x) = (term507 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1291407 x x')). Qed.
Lemma lem1291409 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291410 (x : nadd) : (term496 x) = (term508 x).
Proof. exact (MK_COMB (@lem1291409) (@lem1291408 x)). Qed.
Lemma lem1291411 : term497 = term509.
Proof. exact (fun_ext (fun x : nadd => @lem1291410 x)). Qed.
Lemma lem1291412 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291477 : term460 = term510.
Proof. exact (MK_COMB (@lem1291412) (@lem1291411)). Qed.
Lemma lem1291478 (h1 : term460) : term510.
Proof. exact (EQ_MP (@lem1291477) (@lem1291323 h1)). Qed.
Lemma lem1291485 (x : nadd) (y : nadd) (z : nadd) : (term610 x y z) = (term611 x y z).
Proof. exact (@lem17045 (nadd_le x y) (nadd_le y z)). Qed.
Lemma lem1291486 (x : nadd) (z : nadd) : (nadd_le x z) = (nadd_le x z).
Proof. exact (eq_refl (nadd_le x z)). Qed.
Lemma lem1291487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1291488 (x : nadd) (y : nadd) (z : nadd) : (term612 x y z) = (term613 x y z).
Proof. exact (MK_COMB (@lem1291487) (@lem1291485 x y z)). Qed.
Lemma lem1291489 (y : nadd) (x : nadd) (z : nadd) : (term614 y x z) = (term615 y x z).
Proof. exact (MK_COMB (@lem1291488 x y z) (@lem1291486 x z)). Qed.
Lemma lem1291490 (y : nadd) (x : nadd) (z : nadd) : (term33 y x z) = (term614 y x z).
Proof. exact (@lem17265 (term34 x y z) (nadd_le x z)). Qed.
Lemma lem1291491 (y : nadd) (x : nadd) (z : nadd) : (term33 y x z) = (term615 y x z).
Proof. exact (TRANS (@lem1291490 y x z) (@lem1291489 y x z)). Qed.
Lemma lem1291492 (y : nadd) (x : nadd) : (term604 y x) = (term616 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1291491 y x z)). Qed.
Lemma lem1291493 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291494 (y : nadd) (x : nadd) : (term31 y x) = (term617 y x).
Proof. exact (MK_COMB (@lem1291493) (@lem1291492 y x)). Qed.
Lemma lem1291495 (x : nadd) : (term605 x) = (term618 x).
Proof. exact (fun_ext (fun y : nadd => @lem1291494 y x)). Qed.
Lemma lem1291496 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291497 (x : nadd) : (term29 x) = (term619 x).
Proof. exact (MK_COMB (@lem1291496) (@lem1291495 x)). Qed.
Lemma lem1291498 : term606 = term620.
Proof. exact (fun_ext (fun x : nadd => @lem1291497 x)). Qed.
Lemma lem1291499 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291560 : term27 = term621.
Proof. exact (MK_COMB (@lem1291499) (@lem1291498)). Qed.
Lemma lem1291561 (h1 : term27) : term621.
Proof. exact (EQ_MP (@lem1291560) (@lem1291324 h1)). Qed.
Lemma lem1291569 (k : nadd) (p : nat) (h1 : term94 k p) : term94 k p.
Proof. exact (h1). Qed.
Lemma lem1291583 (p : nat) (N : nat) (x : nadd) (h1 : term120 p N x) : term120 p N x.
Proof. exact (h1). Qed.
Lemma lem1291625 (k : nadd) (N : nat) (x : nadd) (h1 : term565 k N x) : term565 k N x.
Proof. exact (h1). Qed.
Lemma lem1291638 (x : nadd) : (term607 x) = (term607 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1291639 : term608 = term608.
Proof. exact (fun_ext (fun x : nadd => @lem1291638 x)). Qed.
Lemma lem1291640 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291641 : term609 = term609.
Proof. exact (MK_COMB (@lem1291640) (@lem1291639)). Qed.
Lemma lem1291642 (h1 : term609) : term609.
Proof. exact (EQ_MP (@lem1291641) (@lem1291361 h1)). Qed.
Lemma lem1291647 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1291648 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1291647 x)). Qed.
Lemma lem1291649 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291650 : term194 = term194.
Proof. exact (MK_COMB (@lem1291649) (@lem1291648)). Qed.
Lemma lem1291651 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1291650) (@lem1291374 h1)). Qed.
Lemma lem1291704 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term502 x y x' y') = (term502 x y x' y').
Proof. exact (eq_refl (term502 x y x' y')). Qed.
Lemma lem1291705 (x : nadd) (y : nadd) (x' : nadd) : (term503 x y x') = (term503 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1291704 x y x' y')). Qed.
Lemma lem1291706 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291707 (x : nadd) (y : nadd) (x' : nadd) : (term504 x y x') = (term504 x y x').
Proof. exact (MK_COMB (@lem1291706) (@lem1291705 x y x')). Qed.
Lemma lem1291708 (x : nadd) (x' : nadd) : (term505 x x') = (term505 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1291707 x y x')). Qed.
Lemma lem1291709 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291710 (x : nadd) (x' : nadd) : (term506 x x') = (term506 x x').
Proof. exact (MK_COMB (@lem1291709) (@lem1291708 x x')). Qed.
Lemma lem1291711 (x : nadd) : (term507 x) = (term507 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1291710 x x')). Qed.
Lemma lem1291712 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291713 (x : nadd) : (term508 x) = (term508 x).
Proof. exact (MK_COMB (@lem1291712) (@lem1291711 x)). Qed.
Lemma lem1291714 : term509 = term509.
Proof. exact (fun_ext (fun x : nadd => @lem1291713 x)). Qed.
Lemma lem1291715 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291716 : term510 = term510.
Proof. exact (MK_COMB (@lem1291715) (@lem1291714)). Qed.
Lemma lem1291717 (h1 : term460) : term510.
Proof. exact (EQ_MP (@lem1291716) (@lem1291478 h1)). Qed.
Lemma lem1291742 (y : nadd) (x : nadd) (z : nadd) : (term615 y x z) = (term615 y x z).
Proof. exact (eq_refl (term615 y x z)). Qed.
Lemma lem1291743 (y : nadd) (x : nadd) : (term616 y x) = (term616 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1291742 y x z)). Qed.
Lemma lem1291744 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291745 (y : nadd) (x : nadd) : (term617 y x) = (term617 y x).
Proof. exact (MK_COMB (@lem1291744) (@lem1291743 y x)). Qed.
Lemma lem1291746 (x : nadd) : (term618 x) = (term618 x).
Proof. exact (fun_ext (fun y : nadd => @lem1291745 y x)). Qed.
Lemma lem1291747 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291748 (x : nadd) : (term619 x) = (term619 x).
Proof. exact (MK_COMB (@lem1291747) (@lem1291746 x)). Qed.
Lemma lem1291749 : term620 = term620.
Proof. exact (fun_ext (fun x : nadd => @lem1291748 x)). Qed.
Lemma lem1291750 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291751 : term621 = term621.
Proof. exact (MK_COMB (@lem1291750) (@lem1291749)). Qed.
Lemma lem1291752 (h1 : term27) : term621.
Proof. exact (EQ_MP (@lem1291751) (@lem1291561 h1)). Qed.
Lemma lem1291756 (k : nadd) (p : nat) (h1 : term94 k p) : term94 k p.
Proof. exact (h1). Qed.
Lemma lem1291760 (p : nat) (N : nat) (x : nadd) (h1 : term120 p N x) : term120 p N x.
Proof. exact (h1). Qed.
Lemma lem1291768 (k : nadd) (N : nat) (x : nadd) (h1 : term565 k N x) : term565 k N x.
Proof. exact (h1). Qed.
Lemma lem1291770 (x : nadd) : (term607 x) = (term607 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1291771 : term608 = term608.
Proof. exact (fun_ext (fun x : nadd => @lem1291770 x)). Qed.
Lemma lem1291772 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291774 : term609 = term609.
Proof. exact (MK_COMB (@lem1291772) (@lem1291771)). Qed.
Lemma lem1291775 (h1 : term609) : term609.
Proof. exact (EQ_MP (@lem1291774) (@lem1291642 h1)). Qed.
Lemma lem1291777 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1291778 : term193 = term193.
Proof. exact (fun_ext (fun x : nadd => @lem1291777 x)). Qed.
Lemma lem1291779 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291781 : term194 = term194.
Proof. exact (MK_COMB (@lem1291779) (@lem1291778)). Qed.
Lemma lem1291782 (h1 : term194) : term194.
Proof. exact (EQ_MP (@lem1291781) (@lem1291651 h1)). Qed.
Lemma lem1291818 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term502 x y x' y') = (term511 x y x' y').
Proof. exact (@lem19490 (term512 x y x' y') (term254 x x' y y') (term513 x y x' y')). Qed.
Lemma lem1291819 (x : nadd) (y : nadd) (x' : nadd) : (term503 x y x') = (term514 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1291818 x y x' y')). Qed.
Lemma lem1291820 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291821 (x : nadd) (y : nadd) (x' : nadd) : (term504 x y x') = (term515 x y x').
Proof. exact (MK_COMB (@lem1291820) (@lem1291819 x y x')). Qed.
Lemma lem1291822 (x : nadd) (x' : nadd) : (term505 x x') = (term516 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1291821 x y x')). Qed.
Lemma lem1291823 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291824 (x : nadd) (x' : nadd) : (term506 x x') = (term517 x x').
Proof. exact (MK_COMB (@lem1291823) (@lem1291822 x x')). Qed.
Lemma lem1291825 (x : nadd) : (term507 x) = (term518 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1291824 x x')). Qed.
Lemma lem1291826 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291827 (x : nadd) : (term508 x) = (term519 x).
Proof. exact (MK_COMB (@lem1291826) (@lem1291825 x)). Qed.
Lemma lem1291828 : term509 = term520.
Proof. exact (fun_ext (fun x : nadd => @lem1291827 x)). Qed.
Lemma lem1291829 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291831 : term510 = term521.
Proof. exact (MK_COMB (@lem1291829) (@lem1291828)). Qed.
Lemma lem1291832 (h1 : term460) : term521.
Proof. exact (EQ_MP (@lem1291831) (@lem1291717 h1)). Qed.
Lemma lem1291846 (y : nadd) (x : nadd) (z : nadd) : (term615 y x z) = (term615 y x z).
Proof. exact (eq_refl (term615 y x z)). Qed.
Lemma lem1291847 (y : nadd) (x : nadd) : (term616 y x) = (term616 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1291846 y x z)). Qed.
Lemma lem1291848 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291849 (y : nadd) (x : nadd) : (term617 y x) = (term617 y x).
Proof. exact (MK_COMB (@lem1291848) (@lem1291847 y x)). Qed.
Lemma lem1291850 (x : nadd) : (term618 x) = (term618 x).
Proof. exact (fun_ext (fun y : nadd => @lem1291849 y x)). Qed.
Lemma lem1291851 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291852 (x : nadd) : (term619 x) = (term619 x).
Proof. exact (MK_COMB (@lem1291851) (@lem1291850 x)). Qed.
Lemma lem1291853 : term620 = term620.
Proof. exact (fun_ext (fun x : nadd => @lem1291852 x)). Qed.
Lemma lem1291854 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1291856 : term621 = term621.
Proof. exact (MK_COMB (@lem1291854) (@lem1291853)). Qed.
Lemma lem1291857 (h1 : term27) : term621.
Proof. exact (EQ_MP (@lem1291856) (@lem1291752 h1)). Qed.
Lemma lem1291858 (_23294 : nadd) (h1 : term609) : term622 _23294.
Proof. exact (@lem1291775 h1 _23294). Qed.
Lemma lem1291859 (_23294 : nadd) : (term622 _23294) = (term607 _23294).
Proof. exact (eq_refl (term622 _23294)). Qed.
Lemma lem1291861 (_23295 : nadd) (h1 : term194) : term269 _23295.
Proof. exact (@lem1291782 h1 _23295). Qed.
Lemma lem1291862 (_23295 : nadd) : (term269 _23295) = (nadd_eq _23295 _23295).
Proof. exact (eq_refl (term269 _23295)). Qed.
Lemma lem1291864 (_23296 : nadd) (h1 : term460) : term522 _23296.
Proof. exact (@lem1291832 h1 _23296). Qed.
Lemma lem1291865 (_23296 : nadd) : (term522 _23296) = (term519 _23296).
Proof. exact (eq_refl (term522 _23296)). Qed.
Lemma lem1291866 (_23296 : nadd) (h1 : term460) : term519 _23296.
Proof. exact (EQ_MP (@lem1291865 _23296) (@lem1291864 _23296 h1)). Qed.
Lemma lem1291867 (_23296 : nadd) (_23297 : nadd) (h1 : term460) : term523 _23296 _23297.
Proof. exact (@lem1291866 _23296 h1 _23297). Qed.
Lemma lem1291868 (_23296 : nadd) (_23297 : nadd) : (term523 _23296 _23297) = (term517 _23296 _23297).
Proof. exact (eq_refl (term523 _23296 _23297)). Qed.
Lemma lem1291869 (_23296 : nadd) (_23297 : nadd) (h1 : term460) : term517 _23296 _23297.
Proof. exact (EQ_MP (@lem1291868 _23296 _23297) (@lem1291867 _23296 _23297 h1)). Qed.
Lemma lem1291870 (_23296 : nadd) (_23297 : nadd) (_23298 : nadd) (h1 : term460) : term524 _23296 _23297 _23298.
Proof. exact (@lem1291869 _23296 _23297 h1 _23298). Qed.
Lemma lem1291871 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) : (term524 _23296 _23297 _23298) = (term515 _23296 _23298 _23297).
Proof. exact (eq_refl (term524 _23296 _23297 _23298)). Qed.
Lemma lem1291872 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (h1 : term460) : term515 _23296 _23298 _23297.
Proof. exact (EQ_MP (@lem1291871 _23296 _23298 _23297) (@lem1291870 _23296 _23297 _23298 h1)). Qed.
Lemma lem1291873 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) (h1 : term460) : term525 _23296 _23298 _23297 _23299.
Proof. exact (@lem1291872 _23296 _23298 _23297 h1 _23299). Qed.
Lemma lem1291874 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term525 _23296 _23298 _23297 _23299) = (term511 _23296 _23298 _23297 _23299).
Proof. exact (eq_refl (term525 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1291875 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) (h1 : term460) : term511 _23296 _23298 _23297 _23299.
Proof. exact (EQ_MP (@lem1291874 _23296 _23298 _23297 _23299) (@lem1291873 _23296 _23298 _23297 _23299 h1)). Qed.
Lemma lem1291876 (_23300 : nadd) (h1 : term27) : term623 _23300.
Proof. exact (@lem1291857 h1 _23300). Qed.
Lemma lem1291877 (_23300 : nadd) : (term623 _23300) = (term619 _23300).
Proof. exact (eq_refl (term623 _23300)). Qed.
Lemma lem1291878 (_23300 : nadd) (h1 : term27) : term619 _23300.
Proof. exact (EQ_MP (@lem1291877 _23300) (@lem1291876 _23300 h1)). Qed.
Lemma lem1291879 (_23300 : nadd) (_23301 : nadd) (h1 : term27) : term624 _23300 _23301.
Proof. exact (@lem1291878 _23300 h1 _23301). Qed.
Lemma lem1291880 (_23301 : nadd) (_23300 : nadd) : (term624 _23300 _23301) = (term617 _23301 _23300).
Proof. exact (eq_refl (term624 _23300 _23301)). Qed.
Lemma lem1291881 (_23301 : nadd) (_23300 : nadd) (h1 : term27) : term617 _23301 _23300.
Proof. exact (EQ_MP (@lem1291880 _23301 _23300) (@lem1291879 _23300 _23301 h1)). Qed.
Lemma lem1291882 (_23301 : nadd) (_23300 : nadd) (_23302 : nadd) (h1 : term27) : term625 _23301 _23300 _23302.
Proof. exact (@lem1291881 _23301 _23300 h1 _23302). Qed.
Lemma lem1291883 (_23301 : nadd) (_23300 : nadd) (_23302 : nadd) : (term625 _23301 _23300 _23302) = (term615 _23301 _23300 _23302).
Proof. exact (eq_refl (term625 _23301 _23300 _23302)). Qed.
Lemma lem1291884 (_23301 : nadd) (_23300 : nadd) (_23302 : nadd) (h1 : term27) : term615 _23301 _23300 _23302.
Proof. exact (EQ_MP (@lem1291883 _23301 _23300 _23302) (@lem1291882 _23301 _23300 _23302 h1)). Qed.
Lemma lem1291886 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) (h1 : term460) : term626 _23296 _23298 _23297 _23299.
Proof. exact (proj1 (@lem1291875 _23296 _23298 _23297 _23299 h1)). Qed.
Lemma lem1291888 (k : nadd) (p : nat) (h1 : term94 k p) : term94 k p.
Proof. exact (h1). Qed.
Lemma lem1291890 (p : nat) (N : nat) (x : nadd) (h1 : term120 p N x) : term120 p N x.
Proof. exact (h1). Qed.
Lemma lem1291894 (k : nadd) (N : nat) (x : nadd) (h1 : term565 k N x) : term565 k N x.
Proof. exact (h1). Qed.
Lemma lem1291909 (_23301 : nadd) (_23300 : nadd) (_23302 : nadd) : (term615 _23301 _23300 _23302) = (term627 _23301 _23300 _23302).
Proof. exact (@lem1286567 (term533 _23300 _23301) (term533 _23301 _23302) (nadd_le _23300 _23302)). Qed.
Lemma lem1291910 (_23301 : nadd) (_23300 : nadd) (_23302 : nadd) (h1 : term27) : term627 _23301 _23300 _23302.
Proof. exact (EQ_MP (@lem1291909 _23301 _23300 _23302) (@lem1291884 _23301 _23300 _23302 h1)). Qed.
Lemma lem1291925 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term626 _23296 _23298 _23297 _23299) = (term628 _23296 _23298 _23297 _23299).
Proof. exact (@lem1286567 (term277 _23296 _23297) (term277 _23298 _23299) (term512 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1291926 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) (h1 : term460) : term628 _23296 _23298 _23297 _23299.
Proof. exact (EQ_MP (@lem1291925 _23296 _23298 _23297 _23299) (@lem1291886 _23296 _23298 _23297 _23299 h1)). Qed.
Lemma lem1291944 (k : nadd) (p : nat) (h1 : term94 k p) : term94 k p.
Proof. exact (h1). Qed.
Lemma lem1291945 (k : nadd) (p : nat) (h1 : term94 k p) : term629 k p.
Proof. exact (fun h0 : term630 k p => @lem1291944 k p h1). Qed.
Lemma lem1291947 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1291948 (k : nadd) (p : nat) : (term629 k p) = (term94 k p).
Proof. exact (@lem1291947 (term94 k p)). Qed.
Lemma lem1291949 (k : nadd) (p : nat) (h1 : term94 k p) : term94 k p.
Proof. exact (EQ_MP (@lem1291948 k p) (@lem1291945 k p h1)). Qed.
Lemma lem1291951 (_23295 : nadd) (h1 : term194) : nadd_eq _23295 _23295.
Proof. exact (EQ_MP (@lem1291862 _23295) (@lem1291861 _23295 h1)). Qed.
Lemma lem1291952 (p : nat) (h1 : term194) : term631 p.
Proof. exact (@lem1291951 (nadd_of_num p) h1). Qed.
Lemma lem1291953 (p : nat) (h1 : term194) : term632 p.
Proof. exact (fun h0 : term633 p => @lem1291952 p h1). Qed.
Lemma lem1291955 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1291956 (p : nat) : (term632 p) = (term631 p).
Proof. exact (@lem1291955 (term631 p)). Qed.
Lemma lem1291957 (p : nat) (h1 : term194) : term631 p.
Proof. exact (EQ_MP (@lem1291956 p) (@lem1291953 p h1)). Qed.
Lemma lem1291959 (_23294 : nadd) (h1 : term609) : term607 _23294.
Proof. exact (EQ_MP (@lem1291859 _23294) (@lem1291858 _23294 h1)). Qed.
Lemma lem1291960 (N : nat) (x : nadd) (h1 : term609) : term634 N x.
Proof. exact (@lem1291959 (term431 N x) h1). Qed.
Lemma lem1291961 (N : nat) (x : nadd) (h1 : term609) : term635 N x.
Proof. exact (fun h0 : term636 N x => @lem1291960 N x h1). Qed.
Lemma lem1291963 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1291964 (N : nat) (x : nadd) : (term635 N x) = (term634 N x).
Proof. exact (@lem1291963 (term634 N x)). Qed.
Lemma lem1291965 (N : nat) (x : nadd) (h1 : term609) : term634 N x.
Proof. exact (EQ_MP (@lem1291964 N x) (@lem1291961 N x h1)). Qed.
Lemma lem1291967 (p : nat) (N : nat) (x : nadd) (h1 : term120 p N x) : term120 p N x.
Proof. exact (h1). Qed.
Lemma lem1291968 (p : nat) (N : nat) (x : nadd) (h1 : term120 p N x) : term637 p N x.
Proof. exact (fun h0 : term638 p N x => @lem1291967 p N x h1). Qed.
Lemma lem1291970 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1291971 (p : nat) (N : nat) (x : nadd) : (term637 p N x) = (term120 p N x).
Proof. exact (@lem1291970 (term120 p N x)). Qed.
Lemma lem1291972 (p : nat) (N : nat) (x : nadd) (h1 : term120 p N x) : term120 p N x.
Proof. exact (EQ_MP (@lem1291971 p N x) (@lem1291968 p N x h1)). Qed.
Lemma lem1291988 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1291989 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term639 _23296 _23298 _23297 _23299) = (term640 _23296 _23298 _23297 _23299).
Proof. exact (@lem1291988 (nadd_le _23296 _23298) (term277 _23298 _23299) (term533 _23297 _23299)). Qed.
Lemma lem1292005 (_23296 : nadd) (_23297 : nadd) : (term286 _23296 _23297) = (term286 _23296 _23297).
Proof. exact (eq_refl (term286 _23296 _23297)). Qed.
Lemma lem1292006 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term628 _23296 _23298 _23297 _23299) = (term641 _23296 _23298 _23297 _23299).
Proof. exact (MK_COMB (@lem1292005 _23296 _23297) (@lem1291989 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292010 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1292011 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term641 _23296 _23298 _23297 _23299) = (term642 _23296 _23298 _23297 _23299).
Proof. exact (@lem1292010 (nadd_le _23296 _23298) (term277 _23296 _23297) (term643 _23298 _23297 _23299)). Qed.
Lemma lem1292037 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term628 _23296 _23298 _23297 _23299) = (term642 _23296 _23298 _23297 _23299).
Proof. exact (TRANS (@lem1292006 _23296 _23298 _23297 _23299) (@lem1292011 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1292039 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term644 _23296 _23298 _23297 _23299) = (term645 _23296 _23298 _23297 _23299).
Proof. exact (MK_COMB (@lem1292038) (@lem1292037 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292065 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term642 _23296 _23298 _23297 _23299) = (term642 _23296 _23298 _23297 _23299).
Proof. exact (eq_refl (term642 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292066 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : ((term628 _23296 _23298 _23297 _23299) = (term642 _23296 _23298 _23297 _23299)) = ((term642 _23296 _23298 _23297 _23299) = (term642 _23296 _23298 _23297 _23299)).
Proof. exact (MK_COMB (@lem1292039 _23296 _23298 _23297 _23299) (@lem1292065 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292068 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1292069 (x : Prop) : (x = x) = True.
Proof. exact (@lem1292068 Prop x). Qed.
Lemma lem1292070 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : ((term642 _23296 _23298 _23297 _23299) = (term642 _23296 _23298 _23297 _23299)) = True.
Proof. exact (@lem1292069 (term642 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292071 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : ((term628 _23296 _23298 _23297 _23299) = (term642 _23296 _23298 _23297 _23299)) = True.
Proof. exact (TRANS (@lem1292066 _23296 _23298 _23297 _23299) (@lem1292070 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292072 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : True = ((term628 _23296 _23298 _23297 _23299) = (term642 _23296 _23298 _23297 _23299)).
Proof. exact (SYM (@lem1292071 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292073 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term628 _23296 _23298 _23297 _23299) = (term642 _23296 _23298 _23297 _23299).
Proof. exact (EQ_MP (@lem1292072 _23296 _23298 _23297 _23299) (@lem0)). Qed.
Lemma lem1292074 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) (h1 : term460) : term642 _23296 _23298 _23297 _23299.
Proof. exact (EQ_MP (@lem1292073 _23296 _23298 _23297 _23299) (@lem1291926 _23296 _23298 _23297 _23299 h1)). Qed.
Lemma lem1292076 (b : Prop) (a : Prop) : (a \/ b) = (term291 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1292077 (_23297 : nadd) (_23299 : nadd) (_23296 : nadd) (_23298 : nadd) : (term642 _23296 _23298 _23297 _23299) = (term646 _23297 _23299 _23296 _23298).
Proof. exact (@lem1292076 (term647 _23296 _23298 _23297 _23299) (nadd_le _23296 _23298)). Qed.
Lemma lem1292079 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1292080 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term648 _23296 _23298 _23297 _23299) = (term649 _23296 _23298 _23297 _23299).
Proof. exact (@lem1292079 (term277 _23296 _23297) (term643 _23298 _23297 _23299)). Qed.
Lemma lem1292082 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1292083 (_23296 : nadd) (_23297 : nadd) : (term297 _23296 _23297) = (nadd_eq _23296 _23297).
Proof. exact (@lem1292082 (nadd_eq _23296 _23297)). Qed.
Lemma lem1292084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1292085 (_23296 : nadd) (_23297 : nadd) : (term298 _23296 _23297) = (term299 _23296 _23297).
Proof. exact (MK_COMB (@lem1292084) (@lem1292083 _23296 _23297)). Qed.
Lemma lem1292087 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1292088 (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term650 _23298 _23297 _23299) = (term651 _23298 _23297 _23299).
Proof. exact (@lem1292087 (term277 _23298 _23299) (term533 _23297 _23299)). Qed.
Lemma lem1292090 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1292091 (_23298 : nadd) (_23299 : nadd) : (term297 _23298 _23299) = (nadd_eq _23298 _23299).
Proof. exact (@lem1292090 (nadd_eq _23298 _23299)). Qed.
Lemma lem1292092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1292093 (_23298 : nadd) (_23299 : nadd) : (term298 _23298 _23299) = (term299 _23298 _23299).
Proof. exact (MK_COMB (@lem1292092) (@lem1292091 _23298 _23299)). Qed.
Lemma lem1292095 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1292096 (_23297 : nadd) (_23299 : nadd) : (term548 _23297 _23299) = (nadd_le _23297 _23299).
Proof. exact (@lem1292095 (nadd_le _23297 _23299)). Qed.
Lemma lem1292097 (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term651 _23298 _23297 _23299) = (term652 _23298 _23297 _23299).
Proof. exact (MK_COMB (@lem1292093 _23298 _23299) (@lem1292096 _23297 _23299)). Qed.
Lemma lem1292098 (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term650 _23298 _23297 _23299) = (term652 _23298 _23297 _23299).
Proof. exact (TRANS (@lem1292088 _23298 _23297 _23299) (@lem1292097 _23298 _23297 _23299)). Qed.
Lemma lem1292099 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term649 _23296 _23298 _23297 _23299) = (term653 _23296 _23298 _23297 _23299).
Proof. exact (MK_COMB (@lem1292085 _23296 _23297) (@lem1292098 _23298 _23297 _23299)). Qed.
Lemma lem1292100 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term648 _23296 _23298 _23297 _23299) = (term653 _23296 _23298 _23297 _23299).
Proof. exact (TRANS (@lem1292080 _23296 _23298 _23297 _23299) (@lem1292099 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292101 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1292102 (_23296 : nadd) (_23298 : nadd) (_23297 : nadd) (_23299 : nadd) : (term654 _23296 _23298 _23297 _23299) = (term655 _23296 _23298 _23297 _23299).
Proof. exact (MK_COMB (@lem1292101) (@lem1292100 _23296 _23298 _23297 _23299)). Qed.
Lemma lem1292103 (_23296 : nadd) (_23298 : nadd) : (nadd_le _23296 _23298) = (nadd_le _23296 _23298).
Proof. exact (eq_refl (nadd_le _23296 _23298)). Qed.
Lemma lem1292104 (_23297 : nadd) (_23299 : nadd) (_23296 : nadd) (_23298 : nadd) : (term646 _23297 _23299 _23296 _23298) = (term656 _23297 _23299 _23296 _23298).
Proof. exact (MK_COMB (@lem1292102 _23296 _23298 _23297 _23299) (@lem1292103 _23296 _23298)). Qed.
Lemma lem1292105 (_23297 : nadd) (_23299 : nadd) (_23296 : nadd) (_23298 : nadd) : (term642 _23296 _23298 _23297 _23299) = (term656 _23297 _23299 _23296 _23298).
Proof. exact (TRANS (@lem1292077 _23297 _23299 _23296 _23298) (@lem1292104 _23297 _23299 _23296 _23298)). Qed.
Lemma lem1292107 (p : nat) (N : nat) (x : nadd) (h1 : term609) (h2 : term120 p N x) : term657 p N x.
Proof. exact (conj (@lem1291965 N x h1) (@lem1291972 p N x h2)). Qed.
Lemma lem1292108 (p : nat) (N : nat) (x : nadd) (h1 : term194) (h2 : term609) (h3 : term120 p N x) : term658 p N x.
Proof. exact (conj (@lem1291957 p h1) (@lem1292107 p N x h2 h3)). Qed.
Lemma lem1292110 (_23297 : nadd) (_23299 : nadd) (_23296 : nadd) (_23298 : nadd) (h1 : term460) : term656 _23297 _23299 _23296 _23298.
Proof. exact (EQ_MP (@lem1292105 _23297 _23299 _23296 _23298) (@lem1292074 _23296 _23298 _23297 _23299 h1)). Qed.
Lemma lem1292111 (p : nat) (N : nat) (x : nadd) (h1 : term460) : term659 p N x.
Proof. exact (@lem1292110 (nadd_of_num p) (term431 N x) (nadd_of_num p) (term133 N x) h1). Qed.
Lemma lem1292114 (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term194) (h3 : term609) (h4 : term120 p N x) : term660 p N x.
Proof. exact (@lem1292111 p N x h1 (@lem1292108 p N x h2 h3 h4)). Qed.
Lemma lem1292115 (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term194) (h3 : term609) (h4 : term120 p N x) : term661 p N x.
Proof. exact (fun h0 : term662 p N x => @lem1292114 p N x h1 h2 h3 h4). Qed.
Lemma lem1292117 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1292118 (p : nat) (N : nat) (x : nadd) : (term661 p N x) = (term660 p N x).
Proof. exact (@lem1292117 (term660 p N x)). Qed.
Lemma lem1292119 (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term194) (h3 : term609) (h4 : term120 p N x) : term660 p N x.
Proof. exact (EQ_MP (@lem1292118 p N x) (@lem1292115 p N x h1 h2 h3 h4)). Qed.
Lemma lem1292135 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1292136 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term663 _23301 _23300 _23302) = (term664 _23300 _23301 _23302).
Proof. exact (@lem1292135 (nadd_le _23300 _23302) (term533 _23301 _23302)). Qed.
Lemma lem1292142 (_23300 : nadd) (_23301 : nadd) : (term665 _23300 _23301) = (term665 _23300 _23301).
Proof. exact (eq_refl (term665 _23300 _23301)). Qed.
Lemma lem1292143 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term627 _23301 _23300 _23302) = (term666 _23300 _23301 _23302).
Proof. exact (MK_COMB (@lem1292142 _23300 _23301) (@lem1292136 _23300 _23301 _23302)). Qed.
Lemma lem1292147 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1292148 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term666 _23300 _23301 _23302) = (term667 _23300 _23301 _23302).
Proof. exact (@lem1292147 (nadd_le _23300 _23302) (term533 _23300 _23301) (term533 _23301 _23302)). Qed.
Lemma lem1292164 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term627 _23301 _23300 _23302) = (term667 _23300 _23301 _23302).
Proof. exact (TRANS (@lem1292143 _23300 _23301 _23302) (@lem1292148 _23300 _23301 _23302)). Qed.
Lemma lem1292165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1292166 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term668 _23301 _23300 _23302) = (term669 _23300 _23301 _23302).
Proof. exact (MK_COMB (@lem1292165) (@lem1292164 _23300 _23301 _23302)). Qed.
Lemma lem1292182 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term667 _23300 _23301 _23302) = (term667 _23300 _23301 _23302).
Proof. exact (eq_refl (term667 _23300 _23301 _23302)). Qed.
Lemma lem1292183 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : ((term627 _23301 _23300 _23302) = (term667 _23300 _23301 _23302)) = ((term667 _23300 _23301 _23302) = (term667 _23300 _23301 _23302)).
Proof. exact (MK_COMB (@lem1292166 _23300 _23301 _23302) (@lem1292182 _23300 _23301 _23302)). Qed.
Lemma lem1292185 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1292186 (x : Prop) : (x = x) = True.
Proof. exact (@lem1292185 Prop x). Qed.
Lemma lem1292187 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : ((term667 _23300 _23301 _23302) = (term667 _23300 _23301 _23302)) = True.
Proof. exact (@lem1292186 (term667 _23300 _23301 _23302)). Qed.
Lemma lem1292188 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : ((term627 _23301 _23300 _23302) = (term667 _23300 _23301 _23302)) = True.
Proof. exact (TRANS (@lem1292183 _23300 _23301 _23302) (@lem1292187 _23300 _23301 _23302)). Qed.
Lemma lem1292189 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : True = ((term627 _23301 _23300 _23302) = (term667 _23300 _23301 _23302)).
Proof. exact (SYM (@lem1292188 _23300 _23301 _23302)). Qed.
Lemma lem1292190 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term627 _23301 _23300 _23302) = (term667 _23300 _23301 _23302).
Proof. exact (EQ_MP (@lem1292189 _23300 _23301 _23302) (@lem0)). Qed.
Lemma lem1292191 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) (h1 : term27) : term667 _23300 _23301 _23302.
Proof. exact (EQ_MP (@lem1292190 _23300 _23301 _23302) (@lem1291910 _23301 _23300 _23302 h1)). Qed.
Lemma lem1292193 (b : Prop) (a : Prop) : (a \/ b) = (term291 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1292194 (_23301 : nadd) (_23300 : nadd) (_23302 : nadd) : (term667 _23300 _23301 _23302) = (term670 _23301 _23300 _23302).
Proof. exact (@lem1292193 (term611 _23300 _23301 _23302) (nadd_le _23300 _23302)). Qed.
Lemma lem1292196 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1292197 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term671 _23300 _23301 _23302) = (term672 _23300 _23301 _23302).
Proof. exact (@lem1292196 (term533 _23300 _23301) (term533 _23301 _23302)). Qed.
Lemma lem1292199 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1292200 (_23300 : nadd) (_23301 : nadd) : (term548 _23300 _23301) = (nadd_le _23300 _23301).
Proof. exact (@lem1292199 (nadd_le _23300 _23301)). Qed.
Lemma lem1292201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1292202 (_23300 : nadd) (_23301 : nadd) : (term673 _23300 _23301) = (term674 _23300 _23301).
Proof. exact (MK_COMB (@lem1292201) (@lem1292200 _23300 _23301)). Qed.
Lemma lem1292204 (a : Prop) : (term124 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1292205 (_23301 : nadd) (_23302 : nadd) : (term548 _23301 _23302) = (nadd_le _23301 _23302).
Proof. exact (@lem1292204 (nadd_le _23301 _23302)). Qed.
Lemma lem1292206 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term672 _23300 _23301 _23302) = (term34 _23300 _23301 _23302).
Proof. exact (MK_COMB (@lem1292202 _23300 _23301) (@lem1292205 _23301 _23302)). Qed.
Lemma lem1292207 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term671 _23300 _23301 _23302) = (term34 _23300 _23301 _23302).
Proof. exact (TRANS (@lem1292197 _23300 _23301 _23302) (@lem1292206 _23300 _23301 _23302)). Qed.
Lemma lem1292208 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1292209 (_23300 : nadd) (_23301 : nadd) (_23302 : nadd) : (term675 _23300 _23301 _23302) = (term676 _23300 _23301 _23302).
Proof. exact (MK_COMB (@lem1292208) (@lem1292207 _23300 _23301 _23302)). Qed.
Lemma lem1292210 (_23300 : nadd) (_23302 : nadd) : (nadd_le _23300 _23302) = (nadd_le _23300 _23302).
Proof. exact (eq_refl (nadd_le _23300 _23302)). Qed.
Lemma lem1292211 (_23301 : nadd) (_23300 : nadd) (_23302 : nadd) : (term670 _23301 _23300 _23302) = (term33 _23301 _23300 _23302).
Proof. exact (MK_COMB (@lem1292209 _23300 _23301 _23302) (@lem1292210 _23300 _23302)). Qed.
Lemma lem1292212 (_23301 : nadd) (_23300 : nadd) (_23302 : nadd) : (term667 _23300 _23301 _23302) = (term33 _23301 _23300 _23302).
Proof. exact (TRANS (@lem1292194 _23301 _23300 _23302) (@lem1292211 _23301 _23300 _23302)). Qed.
Lemma lem1292214 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term194) (h3 : term609) (h4 : term94 k p) (h5 : term120 p N x) : term677 k p N x.
Proof. exact (conj (@lem1291949 k p h4) (@lem1292119 p N x h1 h2 h3 h5)). Qed.
Lemma lem1292216 (_23301 : nadd) (_23300 : nadd) (_23302 : nadd) (h1 : term27) : term33 _23301 _23300 _23302.
Proof. exact (EQ_MP (@lem1292212 _23301 _23300 _23302) (@lem1292191 _23300 _23301 _23302 h1)). Qed.
Lemma lem1292217 (p : nat) (k : nadd) (N : nat) (x : nadd) (h1 : term27) : term678 p k N x.
Proof. exact (@lem1292216 (nadd_of_num p) k (term133 N x) h1). Qed.
Lemma lem1292220 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term94 k p) (h6 : term120 p N x) : term563 k N x.
Proof. exact (@lem1292217 p k N x h2 (@lem1292214 k p N x h1 h3 h4 h5 h6)). Qed.
Lemma lem1292221 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term94 k p) (h6 : term120 p N x) : term679 k N x.
Proof. exact (fun h0 : term565 k N x => @lem1292220 k p N x h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1292223 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1292224 (k : nadd) (N : nat) (x : nadd) : (term679 k N x) = (term563 k N x).
Proof. exact (@lem1292223 (term563 k N x)). Qed.
Lemma lem1292225 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term94 k p) (h6 : term120 p N x) : term563 k N x.
Proof. exact (EQ_MP (@lem1292224 k N x) (@lem1292221 k p N x h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1292228 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1292230 (k : nadd) (N : nat) (x : nadd) : (term565 k N x) = (term680 k N x).
Proof. exact (@lem1292228 (term563 k N x)). Qed.
Lemma lem1292233 (k : nadd) (N : nat) (x : nadd) (h1 : term565 k N x) : term680 k N x.
Proof. exact (EQ_MP (@lem1292230 k N x) (@lem1291894 k N x h1)). Qed.
Lemma lem1292236 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (@lem1292233 k N x h5 (@lem1292225 k p N x h1 h2 h3 h4 h6 h7)). Qed.
Lemma lem1292237 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : term318.
Proof. exact (fun h0 : ~ False => @lem1292236 k p N x h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem1292239 (p : Prop) : (term281 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1292240 : term318 = False.
Proof. exact (@lem1292239 False). Qed.
Lemma lem1292241 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292240) (@lem1292237 k p N x h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1292242 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term565 k N x) = False.
Proof. exact (prop_ext (fun h8 : term565 k N x => @lem1292241 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291894 k N x h5)). Qed.
Lemma lem1292243 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292242 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291894 k N x h5)). Qed.
Lemma lem1292244 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term120 p N x) = False.
Proof. exact (prop_ext (fun h8 : term120 p N x => @lem1292243 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291890 p N x h7)). Qed.
Lemma lem1292245 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292244 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291890 p N x h7)). Qed.
Lemma lem1292246 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term94 k p) = False.
Proof. exact (prop_ext (fun h8 : term94 k p => @lem1292245 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291888 k p h6)). Qed.
Lemma lem1292247 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292246 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291888 k p h6)). Qed.
Lemma lem1292248 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term565 k N x) = False.
Proof. exact (prop_ext (fun h8 : term565 k N x => @lem1292247 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291768 k N x h5)). Qed.
Lemma lem1292249 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292248 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291768 k N x h5)). Qed.
Lemma lem1292250 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term120 p N x) = False.
Proof. exact (prop_ext (fun h8 : term120 p N x => @lem1292249 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291760 p N x h7)). Qed.
Lemma lem1292251 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292250 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291760 p N x h7)). Qed.
Lemma lem1292252 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term94 k p) = False.
Proof. exact (prop_ext (fun h8 : term94 k p => @lem1292251 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291756 k p h6)). Qed.
Lemma lem1292253 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292252 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291756 k p h6)). Qed.
Lemma lem1292254 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : term194 = False.
Proof. exact (prop_ext (fun h8 : term194 => @lem1292253 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291782 h3)). Qed.
Lemma lem1292255 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292254 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291782 h3)). Qed.
Lemma lem1292256 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : term609 = False.
Proof. exact (prop_ext (fun h8 : term609 => @lem1292255 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291775 h4)). Qed.
Lemma lem1292257 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292256 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291775 h4)). Qed.
Lemma lem1292258 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term565 k N x) = False.
Proof. exact (prop_ext (fun h8 : term565 k N x => @lem1292257 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291768 k N x h5)). Qed.
Lemma lem1292259 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292258 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291768 k N x h5)). Qed.
Lemma lem1292260 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term120 p N x) = False.
Proof. exact (prop_ext (fun h8 : term120 p N x => @lem1292259 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291760 p N x h7)). Qed.
Lemma lem1292261 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292260 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291760 p N x h7)). Qed.
Lemma lem1292262 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term94 k p) = False.
Proof. exact (prop_ext (fun h8 : term94 k p => @lem1292261 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291756 k p h6)). Qed.
Lemma lem1292263 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292262 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291756 k p h6)). Qed.
Lemma lem1292264 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : term194 = False.
Proof. exact (prop_ext (fun h8 : term194 => @lem1292263 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291651 h3)). Qed.
Lemma lem1292265 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292264 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291651 h3)). Qed.
Lemma lem1292266 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : term609 = False.
Proof. exact (prop_ext (fun h8 : term609 => @lem1292265 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291642 h4)). Qed.
Lemma lem1292267 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292266 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291642 h4)). Qed.
Lemma lem1292268 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term565 k N x) = False.
Proof. exact (prop_ext (fun h8 : term565 k N x => @lem1292267 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291625 k N x h5)). Qed.
Lemma lem1292269 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292268 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291625 k N x h5)). Qed.
Lemma lem1292270 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term120 p N x) = False.
Proof. exact (prop_ext (fun h8 : term120 p N x => @lem1292269 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291583 p N x h7)). Qed.
Lemma lem1292271 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292270 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291583 p N x h7)). Qed.
Lemma lem1292272 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term94 k p) = False.
Proof. exact (prop_ext (fun h8 : term94 k p => @lem1292271 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291569 k p h6)). Qed.
Lemma lem1292273 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292272 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291569 k p h6)). Qed.
Lemma lem1292274 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : term194 = False.
Proof. exact (prop_ext (fun h8 : term194 => @lem1292273 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291374 h3)). Qed.
Lemma lem1292275 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292274 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291374 h3)). Qed.
Lemma lem1292276 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : term609 = False.
Proof. exact (prop_ext (fun h8 : term609 => @lem1292275 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291361 h4)). Qed.
Lemma lem1292277 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292276 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291361 h4)). Qed.
Lemma lem1292278 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term565 k N x) = False.
Proof. exact (prop_ext (fun h8 : term565 k N x => @lem1292277 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291348 k N x h5)). Qed.
Lemma lem1292279 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292278 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291348 k N x h5)). Qed.
Lemma lem1292280 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term120 p N x) = False.
Proof. exact (prop_ext (fun h8 : term120 p N x => @lem1292279 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291336 p N x h7)). Qed.
Lemma lem1292281 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292280 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291336 p N x h7)). Qed.
Lemma lem1292282 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : (term94 k p) = False.
Proof. exact (prop_ext (fun h8 : term94 k p => @lem1292281 k p N x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem1291330 k p h6)). Qed.
Lemma lem1292283 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term27) (h3 : term194) (h4 : term609) (h5 : term565 k N x) (h6 : term94 k p) (h7 : term120 p N x) : False.
Proof. exact (EQ_MP (@lem1292282 k p N x h1 h2 h3 h4 h5 h6 h7) (@lem1291330 k p h6)). Qed.
Lemma lem1292284 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term194) (h3 : term609) (h4 : term565 k N x) (h5 : term94 k p) (h6 : term120 p N x) : term570.
Proof. exact (fun h0 : term27 => @lem1292283 k p N x h1 h0 h2 h3 h4 h5 h6). Qed.
Lemma lem1292285 : term570 = term571.
Proof. exact (@lem69 term27). Qed.
Lemma lem1292286 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term460) (h2 : term194) (h3 : term609) (h4 : term565 k N x) (h5 : term94 k p) (h6 : term120 p N x) : term571.
Proof. exact (EQ_MP (@lem1292285) (@lem1292284 k p N x h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1292287 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term194) (h2 : term609) (h3 : term565 k N x) (h4 : term94 k p) (h5 : term120 p N x) : term574.
Proof. exact (fun h0 : term460 => @lem1292286 k p N x h0 h1 h2 h3 h4 h5). Qed.
Lemma lem1292288 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term609) (h2 : term565 k N x) (h3 : term94 k p) (h4 : term120 p N x) : term576.
Proof. exact (fun h0 : term194 => @lem1292287 k p N x h0 h1 h2 h3 h4). Qed.
Lemma lem1292289 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term565 k N x) (h2 : term94 k p) (h3 : term120 p N x) : term579.
Proof. exact (fun h0 : term609 => @lem1292288 k p N x h0 h1 h2 h3). Qed.
Lemma lem1292290 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term94 k p) (h2 : term120 p N x) : term582 k N x.
Proof. exact (fun h0 : term565 k N x => @lem1292289 k p N x h0 h1 h2). Qed.
Lemma lem1292291 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term94 k p) (h2 : term120 p N x) : term584 k N x.
Proof. exact (fun h0 : term121 N x k => @lem1292290 k p N x h1 h2). Qed.
Lemma lem1292292 (N : nat) (x : nadd) (k : nadd) (p : nat) (h1 : term94 k p) : term586 p k N x.
Proof. exact (fun h0 : term120 p N x => @lem1292291 k p N x h1 h0). Qed.
Lemma lem1292293 (p : nat) (k : nadd) (N : nat) (x : nadd) : term587 p k N x.
Proof. exact (fun h0 : term94 k p => @lem1292292 N x k p h0). Qed.
Lemma lem1292298 (k : nadd) (N : nat) (x : nadd) : term591 k N x.
Proof. exact (fun p : nat => @lem1292293 p k N x). Qed.
Lemma lem1292303 (N : nat) (x : nadd) : term595 N x.
Proof. exact (fun k : nadd => @lem1292298 k N x). Qed.
Lemma lem1292308 (x : nadd) : term599 x.
Proof. exact (fun N : nat => @lem1292303 N x). Qed.
Lemma lem1292313 : term603.
Proof. exact (fun x : nadd => @lem1292308 x). Qed.
Lemma lem1292314 : term602.
Proof. exact (EQ_MP (@lem1291316) (@lem1292313)). Qed.
Lemma lem1292315 (x : nadd) : term681 x.
Proof. exact (@lem1292314 x). Qed.
Lemma lem1292316 (x : nadd) : (term681 x) = (term598 x).
Proof. exact (eq_refl (term681 x)). Qed.
Lemma lem1292317 (x : nadd) : term598 x.
Proof. exact (EQ_MP (@lem1292316 x) (@lem1292315 x)). Qed.
Lemma lem1292318 (x : nadd) (N : nat) : term682 x N.
Proof. exact (@lem1292317 x N). Qed.
Lemma lem1292319 (N : nat) (x : nadd) : (term682 x N) = (term594 N x).
Proof. exact (eq_refl (term682 x N)). Qed.
Lemma lem1292320 (N : nat) (x : nadd) : term594 N x.
Proof. exact (EQ_MP (@lem1292319 N x) (@lem1292318 x N)). Qed.
Lemma lem1292321 (N : nat) (x : nadd) (k : nadd) : term683 N x k.
Proof. exact (@lem1292320 N x k). Qed.
Lemma lem1292322 (k : nadd) (N : nat) (x : nadd) : (term683 N x k) = (term590 k N x).
Proof. exact (eq_refl (term683 N x k)). Qed.
Lemma lem1292323 (k : nadd) (N : nat) (x : nadd) : term590 k N x.
Proof. exact (EQ_MP (@lem1292322 k N x) (@lem1292321 N x k)). Qed.
Lemma lem1292324 (k : nadd) (N : nat) (x : nadd) (p : nat) : term684 k N x p.
Proof. exact (@lem1292323 k N x p). Qed.
Lemma lem1292325 (p : nat) (k : nadd) (N : nat) (x : nadd) : (term684 k N x p) = (term566 p k N x).
Proof. exact (eq_refl (term684 k N x p)). Qed.
Lemma lem1292326 (p : nat) (k : nadd) (N : nat) (x : nadd) : term566 p k N x.
Proof. exact (EQ_MP (@lem1292325 p k N x) (@lem1292324 k N x p)). Qed.
Lemma lem1292328 (p : nat) (k : nadd) (N : nat) (x : nadd) : term566 p k N x.
Proof. exact (@lem1290983 p k N x (@lem1292326 p k N x)). Qed.
Lemma lem1292329 (N : nat) (x : nadd) (k : nadd) (p : nat) (h1 : term94 k p) : term585 p k N x.
Proof. exact (@lem1292328 p k N x (@lem1286787 k p h1)). Qed.
Lemma lem1292330 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term94 k p) (h2 : term120 p N x) : term583 k N x.
Proof. exact (@lem1292329 N x k p h1 (@lem1286828 p N x h2)). Qed.
Lemma lem1292331 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term581 k N x.
Proof. exact (@lem1292330 k p N x h1 h2 (@lem1286829 N x k h3)). Qed.
Lemma lem1292332 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term565 k N x) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : term578.
Proof. exact (@lem1292331 p N x k h2 h3 h4 (@lem1290968 k N x h1)). Qed.
Lemma lem1292333 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term565 k N x) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : term575.
Proof. exact (@lem1292332 p N x k h1 h2 h3 h4 (@lem1274816)). Qed.
Lemma lem1292334 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term565 k N x) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : term573.
Proof. exact (@lem1292333 p N x k h1 h2 h3 h4 (@lem1267990)). Qed.
Lemma lem1292335 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term565 k N x) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : term570.
Proof. exact (@lem1292334 p N x k h1 h2 h3 h4 (@lem1270569)). Qed.
Lemma lem1292336 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term565 k N x) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : False.
Proof. exact (@lem1292335 p N x k h1 h2 h3 h4 (@lem1270880)). Qed.
Lemma lem1292337 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term565 k N x) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : (term565 k N x) = False.
Proof. exact (prop_ext (fun h5 : term565 k N x => @lem1292336 p N x k h1 h2 h3 h4) (fun h5 : False => @lem1290968 k N x h1)). Qed.
Lemma lem1292338 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term565 k N x) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : False.
Proof. exact (EQ_MP (@lem1292337 p N x k h1 h2 h3 h4) (@lem1290968 k N x h1)). Qed.
Lemma lem1292339 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term564 k N x.
Proof. exact (fun h0 : term565 k N x => @lem1292338 p N x k h0 h1 h2 h3). Qed.
Lemma lem1292340 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term563 k N x.
Proof. exact (EQ_MP (@lem1290967 k N x) (@lem1292339 p N x k h1 h2 h3)). Qed.
Lemma lem1292341 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term685 k N x.
Proof. exact (conj (@lem1290963 p N x k h1 h2 h3) (@lem1292340 p N x k h1 h2 h3)). Qed.
Lemma lem1292342 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term686 N x.
Proof. exact (ex_intro (term687 N x) k (@lem1292341 p N x k h1 h2 h3)). Qed.
Lemma lem1292343 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term688 N x.
Proof. exact (@lem1286858 N x (@lem1292342 p N x k h1 h2 h3)). Qed.
Lemma lem1292344 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term689 x.
Proof. exact (ex_intro (term690 x) (term431 N x) (@lem1292343 p N x k h1 h2 h3)). Qed.
Lemma lem1292345 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term129 x.
Proof. exact (@lem1286855 x (@lem1292344 p N x k h1 h2 h3)). Qed.
Lemma lem1292346 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term94 k p) (h2 : term120 p N x) (h3 : term121 N x k) : term122 x.
Proof. exact (EQ_MP (@lem1286852 x) (@lem1292345 p N x k h1 h2 h3)). Qed.
Lemma lem1292347 (p : nat) (N : nat) (x : nadd) (k : nadd) (h1 : term85 x) (h2 : term94 k p) (h3 : term120 p N x) (h4 : term121 N x k) : False.
Proof. exact (@lem1292346 p N x k h2 h3 h4 (@lem1286793 x h1)). Qed.
Lemma lem1292348 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term85 x) (h2 : term94 k p) (h3 : term120 p N x) : term691 N x k.
Proof. exact (fun h0 : term121 N x k => @lem1292347 p N x k h1 h2 h3 h0). Qed.
Lemma lem1292349 (N : nat) (x : nadd) (k : nadd) : (term691 N x k) = (term532 N x k).
Proof. exact (@lem69 (term121 N x k)). Qed.
Lemma lem1292350 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term85 x) (h2 : term94 k p) (h3 : term120 p N x) : term532 N x k.
Proof. exact (EQ_MP (@lem1292349 N x k) (@lem1292348 k p N x h1 h2 h3)). Qed.
Lemma lem1292351 (k : nadd) (p : nat) (N : nat) (x : nadd) (h1 : term85 x) (h2 : term94 k p) (h3 : term120 p N x) : term118 x k.
Proof. exact (ex_intro (term117 x k) (term135 N) (@lem1292350 k p N x h1 h2 h3)). Qed.
Lemma lem1292352 (x : nadd) (k : nadd) (p : nat) (h1 : term87 x) (h2 : term85 x) (h3 : term94 k p) : term118 x k.
Proof. exact (ex_elim (@lem1286827 p x h1) (fun N : nat => fun h0 : term692 p x N => @lem1292351 k p N x h2 h3 h0)). Qed.
Lemma lem1292353 (x : nadd) (k : nadd) (p : nat) (h1 : term85 x) (h2 : term94 k p) : term693 x k.
Proof. exact (fun h0 : term87 x => @lem1292352 x k p h0 h1 h2). Qed.
Lemma lem1292354 (x : nadd) (k : nadd) (p : nat) (h1 : term85 x) (h2 : term94 k p) : term118 x k.
Proof. exact (@lem1292353 x k p h1 h2 (@lem1286823 x h1)). Qed.
Lemma lem1292355 (k : nadd) (x : nadd) (h1 : term85 x) : term118 x k.
Proof. exact (ex_elim (@lem1286786 k) (fun p : nat => fun h0 : term694 k p => @lem1292354 x k p h1 h0)). Qed.
Lemma lem1292356 (k : nadd) (x : nadd) (h1 : term85 x) : term111 x k.
Proof. exact (EQ_MP (@lem1286818 x k) (@lem1292355 k x h1)). Qed.
Lemma lem1292357 (x : nadd) (k : nadd) : term99 x k.
Proof. exact (fun h0 : term85 x => @lem1292356 k x h0). Qed.
Lemma lem1292358 (k : nadd) (x : nadd) : term98 k x.
Proof. exact (EQ_MP (@lem1286792 k x) (@lem1292357 x k)). Qed.
Lemma lem1292363 (x : nadd) : term695 x.
Proof. exact (fun k : nadd => @lem1292358 k x). Qed.
Lemma lem1292368 : term696.
Proof. exact (fun x : nadd => @lem1292363 x). Qed.
