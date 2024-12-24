Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_TRIANGLE_LE_term_abbrevs.
Require Import LE_TRANS_spec.
Require Import thm0_spec.
Require Import thm1259719_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1259722 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1259723 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1259722 h1 m). Qed.
Lemma lem1259724 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1259725 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1259724 m) (@lem1259723 m h1)). Qed.
Lemma lem1259726 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1259725 m h1 n). Qed.
Lemma lem1259727 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1259728 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1259727 n m) (@lem1259726 m n h1)). Qed.
Lemma lem1259729 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem1259728 n m h1 p). Qed.
Lemma lem1259730 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem1259731 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem1259730 n m p) (@lem1259729 n m p h1)). Qed.
Lemma lem1259732 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem1259733 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.le m p.
Proof. exact (@lem1259731 n m p h1 (@lem1259732 m n p h2)). Qed.
Lemma lem1259734 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem1259733 m n p h0 h1). Qed.
Lemma lem1259735 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem1259736 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem1259735 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem1259734 m n p h0)). Qed.
Lemma lem1259737 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1259738 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.le m p.
Proof. exact (@lem1259736 m p h2 (@lem1259737 h1)). Qed.
Lemma lem1259739 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem1259738 m p h1 h0). Qed.
Lemma lem1259740 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem1259739 m p h1). Qed.
Lemma lem1259741 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem1259740 m h1). Qed.
Lemma lem1259742 : term14.
Proof. exact (fun h0 : term0 => @lem1259741 h0). Qed.
Lemma lem1259743 : term13.
Proof. exact (@lem1259742 (@lem93743)). Qed.
Lemma lem1259744 (m : nat) : term15 m.
Proof. exact (@lem1259743 m). Qed.
Lemma lem1259745 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1259746 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1259745 m) (@lem1259744 m)). Qed.
Lemma lem1259747 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem1259746 m p). Qed.
Lemma lem1259748 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem1259750 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : term17 m n p q.
Proof. exact (h1). Qed.
Lemma lem1259752 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1259748 m p) (@lem1259747 m p)). Qed.
Lemma lem1259753 (m : nat) (p : nat) (q : nat) : term18 m p q.
Proof. exact (@lem1259752 (term19 m p) q). Qed.
Lemma lem1259754 (m : nat) : term20 m.
Proof. exact (@lem1259719 m). Qed.
Lemma lem1259755 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1259756 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem1259755 m) (@lem1259754 m)). Qed.
Lemma lem1259757 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem1259756 m n). Qed.
Lemma lem1259758 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem1259759 (m : nat) (n : nat) : term23 m n.
Proof. exact (EQ_MP (@lem1259758 m n) (@lem1259757 m n)). Qed.
Lemma lem1259760 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (@lem1259759 m n p). Qed.
Lemma lem1259761 (m : nat) (n : nat) (p : nat) : (term24 m n p) = (term25 m n p).
Proof. exact (eq_refl (term24 m n p)). Qed.
Lemma lem1259762 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (EQ_MP (@lem1259761 m n p) (@lem1259760 m n p)). Qed.
Lemma lem1259763 (m : nat) (n : nat) (p : nat) : (term25 m n p) = ((term25 m n p) = True).
Proof. exact (@lem7 (term25 m n p)). Qed.
Lemma lem1259765 (m : nat) (n : nat) (p : nat) (q : nat) : (term17 m n p q) = ((term17 m n p q) = True).
Proof. exact (@lem7 (term17 m n p q)). Qed.
Lemma lem1259770 (m : nat) (n : nat) (p : nat) : (term25 m n p) = True.
Proof. exact (EQ_MP (@lem1259763 m n p) (@lem1259762 m n p)). Qed.
Lemma lem1259771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1259772 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (and True).
Proof. exact (MK_COMB (@lem1259771) (@lem1259770 m n p)). Qed.
Lemma lem1259774 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : (term17 m n p q) = True.
Proof. exact (EQ_MP (@lem1259765 m n p q) (@lem1259750 m n p q h1)). Qed.
Lemma lem1259775 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : (term27 m n p q) = (True /\ True).
Proof. exact (MK_COMB (@lem1259772 m n p) (@lem1259774 m n p q h1)). Qed.
Lemma lem1259777 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1259778 : (True /\ True) = True.
Proof. exact (@lem1259777 True). Qed.
Lemma lem1259779 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : (term27 m n p q) = True.
Proof. exact (TRANS (@lem1259775 m n p q h1) (@lem1259778)). Qed.
Lemma lem1259780 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : True = (term27 m n p q).
Proof. exact (SYM (@lem1259779 m n p q h1)). Qed.
Lemma lem1259781 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : term27 m n p q.
Proof. exact (EQ_MP (@lem1259780 m n p q h1) (@lem0)). Qed.
Lemma lem1259782 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : term28 m p q.
Proof. exact (ex_intro (term29 m p q) (term30 m n p) (@lem1259781 m n p q h1)). Qed.
Lemma lem1259783 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : term31 m p q.
Proof. exact (@lem1259753 m p q (@lem1259782 m n p q h1)). Qed.
Lemma lem1259784 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : (term17 m n p q) = (term31 m p q).
Proof. exact (prop_ext (fun h2 : term17 m n p q => @lem1259783 m n p q h1) (fun h2 : term31 m p q => @lem1259750 m n p q h1)). Qed.
Lemma lem1259785 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17 m n p q) : term31 m p q.
Proof. exact (EQ_MP (@lem1259784 m n p q h1) (@lem1259750 m n p q h1)). Qed.
Lemma lem1259786 (n : nat) (m : nat) (p : nat) (q : nat) : term32 n m p q.
Proof. exact (fun h0 : term17 m n p q => @lem1259785 m n p q h0). Qed.
Lemma lem1259791 (n : nat) (m : nat) (p : nat) : term33 n m p.
Proof. exact (fun q : nat => @lem1259786 n m p q). Qed.
Lemma lem1259796 (n : nat) (m : nat) : term34 n m.
Proof. exact (fun p : nat => @lem1259791 n m p). Qed.
Lemma lem1259801 (m : nat) : term35 m.
Proof. exact (fun n : nat => @lem1259796 n m). Qed.
Lemma lem1259806 : term36.
Proof. exact (fun m : nat => @lem1259801 m). Qed.
