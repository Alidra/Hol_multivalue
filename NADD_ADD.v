Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ADD_term_abbrevs.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD2_spec.
Require Import NADD_CAUCHY_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import is_nadd_spec.
Require Import nadd_add_spec.
Require Import thm0_spec.
Require Import thm1259721_spec.
Require Import thm1262760_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1273760 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1273761 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1273760 h1 m). Qed.
Lemma lem1273762 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1273763 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1273762 m) (@lem1273761 m h1)). Qed.
Lemma lem1273764 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1273763 m h1 n). Qed.
Lemma lem1273765 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1273766 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem1273765 m n) (@lem1273764 m n h1)). Qed.
Lemma lem1273767 (m : nat) (n : nat) (p : nat) (h1 : term0) : term5 m n p.
Proof. exact (@lem1273766 m n h1 p). Qed.
Lemma lem1273768 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1273769 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (EQ_MP (@lem1273768 m n p) (@lem1273767 m n p h1)). Qed.
Lemma lem1273770 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term7 m n p q.
Proof. exact (@lem1273769 m n p h1 q). Qed.
Lemma lem1273771 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1273772 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (EQ_MP (@lem1273771 m n p q) (@lem1273770 m n p q h1)). Qed.
Lemma lem1273773 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term9 m p n q.
Proof. exact (h1). Qed.
Lemma lem1273774 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1273772 m n p q h1 (@lem1273773 m p n q h2)). Qed.
Lemma lem1273775 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term11 m n p q.
Proof. exact (fun h0 : term0 => @lem1273774 m p n q h0 h1). Qed.
Lemma lem1273776 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1273777 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1273775 m p n q h2 (@lem1273776 h1)). Qed.
Lemma lem1273778 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (fun h0 : term9 m p n q => @lem1273777 m p n q h1 h0). Qed.
Lemma lem1273779 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (fun q : nat => @lem1273778 m n p q h1). Qed.
Lemma lem1273780 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (fun p : nat => @lem1273779 m n p h1). Qed.
Lemma lem1273781 (m : nat) (h1 : term0) : term2 m.
Proof. exact (fun n : nat => @lem1273780 m n h1). Qed.
Lemma lem1273782 (h1 : term0) : term0.
Proof. exact (fun m : nat => @lem1273781 m h1). Qed.
Lemma lem1273783 : term12.
Proof. exact (fun h0 : term0 => @lem1273782 h0). Qed.
Lemma lem1273784 : term0.
Proof. exact (@lem1273783 (@lem101399)). Qed.
Lemma lem1273785 (m : nat) : term1 m.
Proof. exact (@lem1273784 m). Qed.
Lemma lem1273786 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1273787 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1273786 m) (@lem1273785 m)). Qed.
Lemma lem1273788 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1273787 m n). Qed.
Lemma lem1273789 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1273790 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem1273789 m n) (@lem1273788 m n)). Qed.
Lemma lem1273791 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem1273790 m n p). Qed.
Lemma lem1273792 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1273793 (m : nat) (n : nat) (p : nat) : term6 m n p.
Proof. exact (EQ_MP (@lem1273792 m n p) (@lem1273791 m n p)). Qed.
Lemma lem1273794 (m : nat) (n : nat) (p : nat) (q : nat) : term7 m n p q.
Proof. exact (@lem1273793 m n p q). Qed.
Lemma lem1273795 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1273797 (m : nat) : term13 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1273798 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1273799 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1273798 m) (@lem1273797 m)). Qed.
Lemma lem1273800 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1273799 m n). Qed.
Lemma lem1273801 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1273802 (m : nat) (n : nat) : term16 m n.
Proof. exact (EQ_MP (@lem1273801 m n) (@lem1273800 m n)). Qed.
Lemma lem1273803 (m : nat) (n : nat) (p : nat) : term17 m n p.
Proof. exact (@lem1273802 m n p). Qed.
Lemma lem1273804 (m : nat) (n : nat) (p : nat) : (term17 m n p) = ((term18 m n p) = (term19 m n p)).
Proof. exact (eq_refl (term17 m n p)). Qed.
Lemma lem1273806 (m : nat) : term20 m.
Proof. exact (@lem1259721 m). Qed.
Lemma lem1273807 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1273808 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem1273807 m) (@lem1273806 m)). Qed.
Lemma lem1273809 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem1273808 m n). Qed.
Lemma lem1273810 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem1273811 (m : nat) (n : nat) : term23 m n.
Proof. exact (EQ_MP (@lem1273810 m n) (@lem1273809 m n)). Qed.
Lemma lem1273812 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (@lem1273811 m n p). Qed.
Lemma lem1273813 (m : nat) (p : nat) (n : nat) : (term24 m n p) = (term25 m p n).
Proof. exact (eq_refl (term24 m n p)). Qed.
Lemma lem1273814 (m : nat) (p : nat) (n : nat) : term25 m p n.
Proof. exact (EQ_MP (@lem1273813 m p n) (@lem1273812 m n p)). Qed.
Lemma lem1273815 (m : nat) (p : nat) (n : nat) (q : nat) : term26 m p n q.
Proof. exact (@lem1273814 m p n q). Qed.
Lemma lem1273816 (m : nat) (p : nat) (n : nat) (q : nat) : (term26 m p n q) = (term27 m p n q).
Proof. exact (eq_refl (term26 m p n q)). Qed.
Lemma lem1273817 (m : nat) (p : nat) (n : nat) (q : nat) : term27 m p n q.
Proof. exact (EQ_MP (@lem1273816 m p n q) (@lem1273815 m p n q)). Qed.
Lemma lem1273818 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem1273819 (m : nat) (h1 : term28) : term29 m.
Proof. exact (@lem1273818 h1 m). Qed.
Lemma lem1273820 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem1273821 (m : nat) (h1 : term28) : term30 m.
Proof. exact (EQ_MP (@lem1273820 m) (@lem1273819 m h1)). Qed.
Lemma lem1273822 (m : nat) (n : nat) (h1 : term28) : term31 m n.
Proof. exact (@lem1273821 m h1 n). Qed.
Lemma lem1273823 (n : nat) (m : nat) : (term31 m n) = (term32 n m).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem1273824 (n : nat) (m : nat) (h1 : term28) : term32 n m.
Proof. exact (EQ_MP (@lem1273823 n m) (@lem1273822 m n h1)). Qed.
Lemma lem1273825 (n : nat) (m : nat) (p : nat) (h1 : term28) : term33 n m p.
Proof. exact (@lem1273824 n m h1 p). Qed.
Lemma lem1273826 (n : nat) (m : nat) (p : nat) : (term33 n m p) = (term34 n m p).
Proof. exact (eq_refl (term33 n m p)). Qed.
Lemma lem1273827 (n : nat) (m : nat) (p : nat) (h1 : term28) : term34 n m p.
Proof. exact (EQ_MP (@lem1273826 n m p) (@lem1273825 n m p h1)). Qed.
Lemma lem1273828 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1273829 (p : nat) (m : nat) (n : nat) (h1 : term28) (h2 : Peano.le m n) : term35 n m p.
Proof. exact (@lem1273827 n m p h1 (@lem1273828 m n h2)). Qed.
Lemma lem1273830 (m : nat) (n : nat) (h1 : term28) (h2 : Peano.le m n) : term36 n m.
Proof. exact (fun p : nat => @lem1273829 p m n h1 h2). Qed.
Lemma lem1273831 (n : nat) (m : nat) (h1 : term28) : term37 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1273830 m n h1 h0). Qed.
Lemma lem1273832 (m : nat) (h1 : term28) : term38 m.
Proof. exact (fun n : nat => @lem1273831 n m h1). Qed.
Lemma lem1273833 (h1 : term28) : term39.
Proof. exact (fun m : nat => @lem1273832 m h1). Qed.
Lemma lem1273834 : term40.
Proof. exact (fun h0 : term28 => @lem1273833 h0). Qed.
Lemma lem1273835 : term39.
Proof. exact (@lem1273834 (@lem272809)). Qed.
Lemma lem1273836 (m : nat) : term41 m.
Proof. exact (@lem1273835 m). Qed.
Lemma lem1273837 (m : nat) : (term41 m) = (term38 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem1273838 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem1273837 m) (@lem1273836 m)). Qed.
Lemma lem1273839 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem1273838 m n). Qed.
Lemma lem1273840 (n : nat) (m : nat) : (term42 m n) = (term37 n m).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem1273843 (n : nat) (m : nat) : term37 n m.
Proof. exact (EQ_MP (@lem1273840 n m) (@lem1273839 m n)). Qed.
Lemma lem1273844 (m : nat) (n : nat) (p : nat) (q : nat) : term43 m n p q.
Proof. exact (@lem1273843 (term44 m p n q) (term45 m n p q)). Qed.
Lemma lem1273845 (m : nat) (n : nat) (p : nat) (q : nat) : term46 m n p q.
Proof. exact (@lem1273844 m n p q (@lem1273817 m p n q)). Qed.
Lemma lem1273846 (m : nat) (n : nat) (p : nat) : term47 m n p.
Proof. exact (fun q : nat => @lem1273845 m n p q). Qed.
Lemma lem1273847 (m : nat) (n : nat) : term48 m n.
Proof. exact (fun p : nat => @lem1273846 m n p). Qed.
Lemma lem1273848 (m : nat) : term49 m.
Proof. exact (fun n : nat => @lem1273847 m n). Qed.
Lemma lem1273849 : term50.
Proof. exact (fun m : nat => @lem1273848 m). Qed.
Lemma lem1273850 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem1273851 (m : nat) (h1 : term50) : term51 m.
Proof. exact (@lem1273850 h1 m). Qed.
Lemma lem1273852 (m : nat) : (term51 m) = (term49 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem1273853 (m : nat) (h1 : term50) : term49 m.
Proof. exact (EQ_MP (@lem1273852 m) (@lem1273851 m h1)). Qed.
Lemma lem1273854 (m : nat) (n : nat) (h1 : term50) : term52 m n.
Proof. exact (@lem1273853 m h1 n). Qed.
Lemma lem1273855 (m : nat) (n : nat) : (term52 m n) = (term48 m n).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem1273856 (m : nat) (n : nat) (h1 : term50) : term48 m n.
Proof. exact (EQ_MP (@lem1273855 m n) (@lem1273854 m n h1)). Qed.
Lemma lem1273857 (m : nat) (n : nat) (p : nat) (h1 : term50) : term53 m n p.
Proof. exact (@lem1273856 m n h1 p). Qed.
Lemma lem1273858 (m : nat) (n : nat) (p : nat) : (term53 m n p) = (term47 m n p).
Proof. exact (eq_refl (term53 m n p)). Qed.
Lemma lem1273859 (m : nat) (n : nat) (p : nat) (h1 : term50) : term47 m n p.
Proof. exact (EQ_MP (@lem1273858 m n p) (@lem1273857 m n p h1)). Qed.
Lemma lem1273860 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term50) : term54 m n p q.
Proof. exact (@lem1273859 m n p h1 q). Qed.
Lemma lem1273861 (m : nat) (n : nat) (p : nat) (q : nat) : (term54 m n p q) = (term46 m n p q).
Proof. exact (eq_refl (term54 m n p q)). Qed.
Lemma lem1273862 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term50) : term46 m n p q.
Proof. exact (EQ_MP (@lem1273861 m n p q) (@lem1273860 m n p q h1)). Qed.
Lemma lem1273863 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term50) : term55 m n p q p'.
Proof. exact (@lem1273862 m n p q h1 p'). Qed.
Lemma lem1273864 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : (term55 m n p q p') = (term56 m n p q p').
Proof. exact (eq_refl (term55 m n p q p')). Qed.
Lemma lem1273865 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term50) : term56 m n p q p'.
Proof. exact (EQ_MP (@lem1273864 m n p q p') (@lem1273863 m n p q p' h1)). Qed.
Lemma lem1273866 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term57 m p n q p') : term57 m p n q p'.
Proof. exact (h1). Qed.
Lemma lem1273867 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term50) (h2 : term57 m p n q p') : term58 m n p q p'.
Proof. exact (@lem1273865 m n p q p' h1 (@lem1273866 m p n q p' h2)). Qed.
Lemma lem1273868 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term57 m p n q p') : term59 m n p q p'.
Proof. exact (fun h0 : term50 => @lem1273867 m p n q p' h0 h1). Qed.
Lemma lem1273869 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem1273870 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term50) (h2 : term57 m p n q p') : term58 m n p q p'.
Proof. exact (@lem1273868 m p n q p' h2 (@lem1273869 h1)). Qed.
Lemma lem1273871 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term50) : term56 m n p q p'.
Proof. exact (fun h0 : term57 m p n q p' => @lem1273870 m p n q p' h1 h0). Qed.
Lemma lem1273872 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term50) : term46 m n p q.
Proof. exact (fun p' : nat => @lem1273871 m n p q p' h1). Qed.
Lemma lem1273873 (m : nat) (n : nat) (p : nat) (h1 : term50) : term47 m n p.
Proof. exact (fun q : nat => @lem1273872 m n p q h1). Qed.
Lemma lem1273874 (m : nat) (n : nat) (h1 : term50) : term48 m n.
Proof. exact (fun p : nat => @lem1273873 m n p h1). Qed.
Lemma lem1273875 (m : nat) (h1 : term50) : term49 m.
Proof. exact (fun n : nat => @lem1273874 m n h1). Qed.
Lemma lem1273876 (h1 : term50) : term50.
Proof. exact (fun m : nat => @lem1273875 m h1). Qed.
Lemma lem1273877 : term60.
Proof. exact (fun h0 : term50 => @lem1273876 h0). Qed.
Lemma lem1273878 : term50.
Proof. exact (@lem1273877 (@lem1273849)). Qed.
Lemma lem1273879 (m : nat) : term51 m.
Proof. exact (@lem1273878 m). Qed.
Lemma lem1273880 (m : nat) : (term51 m) = (term49 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem1273881 (m : nat) : term49 m.
Proof. exact (EQ_MP (@lem1273880 m) (@lem1273879 m)). Qed.
Lemma lem1273882 (m : nat) (n : nat) : term52 m n.
Proof. exact (@lem1273881 m n). Qed.
Lemma lem1273883 (m : nat) (n : nat) : (term52 m n) = (term48 m n).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem1273884 (m : nat) (n : nat) : term48 m n.
Proof. exact (EQ_MP (@lem1273883 m n) (@lem1273882 m n)). Qed.
Lemma lem1273885 (m : nat) (n : nat) (p : nat) : term53 m n p.
Proof. exact (@lem1273884 m n p). Qed.
Lemma lem1273886 (m : nat) (n : nat) (p : nat) : (term53 m n p) = (term47 m n p).
Proof. exact (eq_refl (term53 m n p)). Qed.
Lemma lem1273887 (m : nat) (n : nat) (p : nat) : term47 m n p.
Proof. exact (EQ_MP (@lem1273886 m n p) (@lem1273885 m n p)). Qed.
Lemma lem1273888 (m : nat) (n : nat) (p : nat) (q : nat) : term54 m n p q.
Proof. exact (@lem1273887 m n p q). Qed.
Lemma lem1273889 (m : nat) (n : nat) (p : nat) (q : nat) : (term54 m n p q) = (term46 m n p q).
Proof. exact (eq_refl (term54 m n p q)). Qed.
Lemma lem1273890 (m : nat) (n : nat) (p : nat) (q : nat) : term46 m n p q.
Proof. exact (EQ_MP (@lem1273889 m n p q) (@lem1273888 m n p q)). Qed.
Lemma lem1273891 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : term55 m n p q p'.
Proof. exact (@lem1273890 m n p q p'). Qed.
Lemma lem1273892 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : (term55 m n p q p') = (term56 m n p q p').
Proof. exact (eq_refl (term55 m n p q p')). Qed.
Lemma lem1273894 (m : nat) : term61 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1273895 (m : nat) : (term61 m) = (term62 m).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem1273896 (m : nat) : term62 m.
Proof. exact (EQ_MP (@lem1273895 m) (@lem1273894 m)). Qed.
Lemma lem1273897 (m : nat) (n : nat) : term63 m n.
Proof. exact (@lem1273896 m n). Qed.
Lemma lem1273898 (n : nat) (m : nat) : (term63 m n) = (term64 n m).
Proof. exact (eq_refl (term63 m n)). Qed.
Lemma lem1273899 (n : nat) (m : nat) : term64 n m.
Proof. exact (EQ_MP (@lem1273898 n m) (@lem1273897 m n)). Qed.
Lemma lem1273900 (n : nat) (m : nat) (p : nat) : term65 n m p.
Proof. exact (@lem1273899 n m p). Qed.
Lemma lem1273901 (n : nat) (m : nat) (p : nat) : (term65 n m p) = ((term66 m n p) = (term67 n m p)).
Proof. exact (eq_refl (term65 n m p)). Qed.
Lemma lem1273903 (y : nadd) : term68 y.
Proof. exact (@lem1262851 y). Qed.
Lemma lem1273904 (y : nadd) : (term68 y) = (term69 y).
Proof. exact (eq_refl (term68 y)). Qed.
Lemma lem1273905 (y : nadd) : term69 y.
Proof. exact (EQ_MP (@lem1273904 y) (@lem1273903 y)). Qed.
Lemma lem1273906 (y : nadd) (B2 : nat) (h1 : term70 y B2) : term70 y B2.
Proof. exact (h1). Qed.
Lemma lem1273907 (x : nadd) : term68 x.
Proof. exact (@lem1262851 x). Qed.
Lemma lem1273908 (x : nadd) : (term68 x) = (term69 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1273909 (x : nadd) : term69 x.
Proof. exact (EQ_MP (@lem1273908 x) (@lem1273907 x)). Qed.
Lemma lem1273910 (x : nadd) (B1 : nat) (h1 : term70 x B1) : term70 x B1.
Proof. exact (h1). Qed.
Lemma lem1273911 (r : nat -> nat) (h1 : (is_nadd r) = ((term71 r) = r)) : (is_nadd r) = ((term71 r) = r).
Proof. exact (h1). Qed.
Lemma lem1273912 (r : nat -> nat) (h1 : (is_nadd r) = ((term71 r) = r)) : ((term71 r) = r) = (is_nadd r).
Proof. exact (SYM (@lem1273911 r h1)). Qed.
Lemma lem1273913 (r : nat -> nat) (h1 : ((term71 r) = r) = (is_nadd r)) : ((term71 r) = r) = (is_nadd r).
Proof. exact (h1). Qed.
Lemma lem1273914 (r : nat -> nat) (h1 : ((term71 r) = r) = (is_nadd r)) : (is_nadd r) = ((term71 r) = r).
Proof. exact (SYM (@lem1273913 r h1)). Qed.
Lemma lem1273915 (r : nat -> nat) : ((is_nadd r) = ((term71 r) = r)) = (((term71 r) = r) = (is_nadd r)).
Proof. exact (prop_ext (fun h1 : (is_nadd r) = ((term71 r) = r) => @lem1273912 r h1) (fun h1 : ((term71 r) = r) = (is_nadd r) => @lem1273914 r h1)). Qed.
Lemma lem1273917 (x : nat -> nat) : term72 x.
Proof. exact (@lem1262615 x). Qed.
Lemma lem1273918 (x : nat -> nat) : (term72 x) = ((is_nadd x) = (term73 x)).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1273920 (x : nadd) : term74 x.
Proof. exact (@lem1273759 x). Qed.
Lemma lem1273921 (x : nadd) : (term74 x) = (term75 x).
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem1273922 (x : nadd) : term75 x.
Proof. exact (EQ_MP (@lem1273921 x) (@lem1273920 x)). Qed.
Lemma lem1273923 (x : nadd) (y : nadd) : term76 x y.
Proof. exact (@lem1273922 x y). Qed.
Lemma lem1273924 (x : nadd) (y : nadd) : (term76 x y) = ((nadd_add x y) = (term77 x y)).
Proof. exact (eq_refl (term76 x y)). Qed.
Lemma lem1273929 (x : nadd) (y : nadd) : (nadd_add x y) = (term77 x y).
Proof. exact (EQ_MP (@lem1273924 x y) (@lem1273923 x y)). Qed.
Lemma lem1273930 : dest_nadd = dest_nadd.
Proof. exact (eq_refl dest_nadd). Qed.
Lemma lem1273931 (x : nadd) (y : nadd) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1273930) (@lem1273929 x y)). Qed.
Lemma lem1273932 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem1273933 (x : nadd) (y : nadd) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1273932) (@lem1273931 x y)). Qed.
Lemma lem1273934 (x : nadd) (y : nadd) : (term82 x y) = (term82 x y).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem1273935 (x : nadd) (y : nadd) : ((term78 x y) = (term82 x y)) = ((term79 x y) = (term82 x y)).
Proof. exact (MK_COMB (@lem1273933 x y) (@lem1273934 x y)). Qed.
Lemma lem1273937 (r : nat -> nat) : ((term71 r) = r) = (is_nadd r).
Proof. exact (EQ_MP (@lem1273915 r) (@lem1262760 r)). Qed.
Lemma lem1273938 (x : nadd) (y : nadd) : ((term79 x y) = (term82 x y)) = (term83 x y).
Proof. exact (@lem1273937 (term82 x y)). Qed.
Lemma lem1273940 (x : nat -> nat) : (is_nadd x) = (term73 x).
Proof. exact (EQ_MP (@lem1273918 x) (@lem1273917 x)). Qed.
Lemma lem1273941 (x : nadd) (y : nadd) : (term83 x y) = (term84 x y).
Proof. exact (@lem1273940 (term82 x y)). Qed.
Lemma lem1273955 {A B : Type'} (f : A -> B) (y : A) : (term85 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1273956 (f : nat -> nat) (y : nat) : (term86 f y) = (f y).
Proof. exact (@lem1273955 nat nat f y). Qed.
Lemma lem1273957 (x : nadd) (y : nadd) (n : nat) : (term87 x y n) = (term88 x y n).
Proof. exact (@lem1273956 (term82 x y) n). Qed.
Lemma lem1273958 (x : nadd) (y : nadd) (n : nat) : (term88 x y n) = (term89 x y n).
Proof. exact (eq_refl (term88 x y n)). Qed.
Lemma lem1273959 (x : nadd) (y : nadd) : (term90 x y) = (term82 x y).
Proof. exact (fun_ext (fun n : nat => @lem1273958 x y n)). Qed.
Lemma lem1273960 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1273961 (x : nadd) (y : nadd) (n : nat) : (term87 x y n) = (term88 x y n).
Proof. exact (MK_COMB (@lem1273959 x y) (@lem1273960 n)). Qed.
Lemma lem1273962 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1273963 (x : nadd) (y : nadd) (n : nat) : (term91 x y n) = (term92 x y n).
Proof. exact (MK_COMB (@lem1273962) (@lem1273961 x y n)). Qed.
Lemma lem1273964 (x : nadd) (y : nadd) (n : nat) : (term88 x y n) = (term89 x y n).
Proof. exact (eq_refl (term88 x y n)). Qed.
Lemma lem1273965 (x : nadd) (y : nadd) (n : nat) : ((term87 x y n) = (term88 x y n)) = ((term88 x y n) = (term89 x y n)).
Proof. exact (MK_COMB (@lem1273963 x y n) (@lem1273964 x y n)). Qed.
Lemma lem1273966 (x : nadd) (y : nadd) (n : nat) : (term88 x y n) = (term89 x y n).
Proof. exact (EQ_MP (@lem1273965 x y n) (@lem1273957 x y n)). Qed.
Lemma lem1273967 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1273968 (m : nat) (x : nadd) (y : nadd) (n : nat) : (term93 m x y n) = (term94 m x y n).
Proof. exact (MK_COMB (@lem1273967 m) (@lem1273966 x y n)). Qed.
Lemma lem1273969 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1273970 (m : nat) (x : nadd) (y : nadd) (n : nat) : (term95 m x y n) = (term96 m x y n).
Proof. exact (MK_COMB (@lem1273969) (@lem1273968 m x y n)). Qed.
Lemma lem1273972 {A B : Type'} (f : A -> B) (y : A) : (term85 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1273973 (f : nat -> nat) (y : nat) : (term86 f y) = (f y).
Proof. exact (@lem1273972 nat nat f y). Qed.
Lemma lem1273974 (x : nadd) (y : nadd) (m : nat) : (term87 x y m) = (term88 x y m).
Proof. exact (@lem1273973 (term82 x y) m). Qed.
Lemma lem1273975 (x : nadd) (y : nadd) (n : nat) : (term88 x y n) = (term89 x y n).
Proof. exact (eq_refl (term88 x y n)). Qed.
Lemma lem1273976 (x : nadd) (y : nadd) : (term90 x y) = (term82 x y).
Proof. exact (fun_ext (fun n : nat => @lem1273975 x y n)). Qed.
Lemma lem1273977 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1273978 (x : nadd) (y : nadd) (m : nat) : (term87 x y m) = (term88 x y m).
Proof. exact (MK_COMB (@lem1273976 x y) (@lem1273977 m)). Qed.
Lemma lem1273979 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1273980 (x : nadd) (y : nadd) (m : nat) : (term91 x y m) = (term92 x y m).
Proof. exact (MK_COMB (@lem1273979) (@lem1273978 x y m)). Qed.
Lemma lem1273981 (x : nadd) (y : nadd) (m : nat) : (term88 x y m) = (term89 x y m).
Proof. exact (eq_refl (term88 x y m)). Qed.
Lemma lem1273982 (x : nadd) (y : nadd) (m : nat) : ((term87 x y m) = (term88 x y m)) = ((term88 x y m) = (term89 x y m)).
Proof. exact (MK_COMB (@lem1273980 x y m) (@lem1273981 x y m)). Qed.
Lemma lem1273983 (x : nadd) (y : nadd) (m : nat) : (term88 x y m) = (term89 x y m).
Proof. exact (EQ_MP (@lem1273982 x y m) (@lem1273974 x y m)). Qed.
Lemma lem1273984 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1273985 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term93 n x y m) = (term94 n x y m).
Proof. exact (MK_COMB (@lem1273984 n) (@lem1273983 x y m)). Qed.
Lemma lem1273986 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term97 n x y m) = (term98 n x y m).
Proof. exact (MK_COMB (@lem1273970 m x y n) (@lem1273985 n x y m)). Qed.
Lemma lem1273987 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1273988 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term99 n x y m) = (term100 n x y m).
Proof. exact (MK_COMB (@lem1273987) (@lem1273986 n x y m)). Qed.
Lemma lem1273989 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1273990 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term101 n x y m) = (term102 n x y m).
Proof. exact (MK_COMB (@lem1273989) (@lem1273988 n x y m)). Qed.
Lemma lem1273991 (B : nat) (m : nat) (n : nat) : (term66 B m n) = (term66 B m n).
Proof. exact (eq_refl (term66 B m n)). Qed.
Lemma lem1273992 (x : nadd) (y : nadd) (B : nat) (m : nat) (n : nat) : (term103 x y B m n) = (term104 x y B m n).
Proof. exact (MK_COMB (@lem1273990 n x y m) (@lem1273991 B m n)). Qed.
Lemma lem1273993 (x : nadd) (y : nadd) (B : nat) (m : nat) : (term105 x y B m) = (term106 x y B m).
Proof. exact (fun_ext (fun n : nat => @lem1273992 x y B m n)). Qed.
Lemma lem1273994 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1273995 (x : nadd) (y : nadd) (B : nat) (m : nat) : (term107 x y B m) = (term108 x y B m).
Proof. exact (MK_COMB (@lem1273994) (@lem1273993 x y B m)). Qed.
Lemma lem1274000 (x : nadd) (y : nadd) (B : nat) : (term109 x y B) = (term110 x y B).
Proof. exact (fun_ext (fun m : nat => @lem1273995 x y B m)). Qed.
Lemma lem1274001 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1274002 (x : nadd) (y : nadd) (B : nat) : (term111 x y B) = (term112 x y B).
Proof. exact (MK_COMB (@lem1274001) (@lem1274000 x y B)). Qed.
Lemma lem1274007 (x : nadd) (y : nadd) : (term113 x y) = (term114 x y).
Proof. exact (fun_ext (fun B : nat => @lem1274002 x y B)). Qed.
Lemma lem1274008 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1274009 (x : nadd) (y : nadd) : (term84 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1274008) (@lem1274007 x y)). Qed.
Lemma lem1274014 (x : nadd) (y : nadd) : (term83 x y) = (term115 x y).
Proof. exact (TRANS (@lem1273941 x y) (@lem1274009 x y)). Qed.
Lemma lem1274015 (x : nadd) (y : nadd) : ((term79 x y) = (term82 x y)) = (term115 x y).
Proof. exact (TRANS (@lem1273938 x y) (@lem1274014 x y)). Qed.
Lemma lem1274016 (x : nadd) (y : nadd) : ((term78 x y) = (term82 x y)) = (term115 x y).
Proof. exact (TRANS (@lem1273935 x y) (@lem1274015 x y)). Qed.
Lemma lem1274017 (x : nadd) (y : nadd) : (term115 x y) = ((term78 x y) = (term82 x y)).
Proof. exact (SYM (@lem1274016 x y)). Qed.
Lemma lem1274019 (n : nat) (m : nat) (p : nat) : (term66 m n p) = (term67 n m p).
Proof. exact (EQ_MP (@lem1273901 n m p) (@lem1273900 n m p)). Qed.
Lemma lem1274020 (x : nadd) (m : nat) (y : nadd) (n : nat) : (term94 m x y n) = (term116 x m y n).
Proof. exact (@lem1274019 (dest_nadd x n) m (dest_nadd y n)). Qed.
Lemma lem1274021 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1274022 (x : nadd) (m : nat) (y : nadd) (n : nat) : (term96 m x y n) = (term117 x m y n).
Proof. exact (MK_COMB (@lem1274021) (@lem1274020 x m y n)). Qed.
Lemma lem1274024 (n : nat) (m : nat) (p : nat) : (term66 m n p) = (term67 n m p).
Proof. exact (EQ_MP (@lem1273901 n m p) (@lem1273900 n m p)). Qed.
Lemma lem1274025 (x : nadd) (n : nat) (y : nadd) (m : nat) : (term94 n x y m) = (term116 x n y m).
Proof. exact (@lem1274024 (dest_nadd x m) n (dest_nadd y m)). Qed.
Lemma lem1274026 (x : nadd) (n : nat) (y : nadd) (m : nat) : (term98 n x y m) = (term118 x n y m).
Proof. exact (MK_COMB (@lem1274022 x m y n) (@lem1274025 x n y m)). Qed.
Lemma lem1274027 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1274028 (x : nadd) (n : nat) (y : nadd) (m : nat) : (term100 n x y m) = (term119 x n y m).
Proof. exact (MK_COMB (@lem1274027) (@lem1274026 x n y m)). Qed.
Lemma lem1274029 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1274030 (x : nadd) (n : nat) (y : nadd) (m : nat) : (term102 n x y m) = (term120 x n y m).
Proof. exact (MK_COMB (@lem1274029) (@lem1274028 x n y m)). Qed.
Lemma lem1274031 (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term121 B1 B2 m n) = (term121 B1 B2 m n).
Proof. exact (eq_refl (term121 B1 B2 m n)). Qed.
Lemma lem1274032 (x : nadd) (y : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term122 x y B1 B2 m n) = (term123 x y B1 B2 m n).
Proof. exact (MK_COMB (@lem1274030 x n y m) (@lem1274031 B1 B2 m n)). Qed.
Lemma lem1274033 (x : nadd) (y : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term123 x y B1 B2 m n) = (term122 x y B1 B2 m n).
Proof. exact (SYM (@lem1274032 x y B1 B2 m n)). Qed.
Lemma lem1274035 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : term56 m n p q p'.
Proof. exact (EQ_MP (@lem1273892 m n p q p') (@lem1273891 m n p q p')). Qed.
Lemma lem1274036 (x : nadd) (y : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : term124 x y B1 B2 m n.
Proof. exact (@lem1274035 (term125 m x n) (term125 m y n) (term125 n x m) (term125 n y m) (term121 B1 B2 m n)). Qed.
Lemma lem1274038 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (term19 m n p).
Proof. exact (EQ_MP (@lem1273804 m n p) (@lem1273803 m n p)). Qed.
Lemma lem1274039 (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term121 B1 B2 m n) = (term126 B1 B2 m n).
Proof. exact (@lem1274038 B1 B2 (Nat.add m n)). Qed.
Lemma lem1274040 (x : nadd) (n : nat) (y : nadd) (m : nat) : (term127 x n y m) = (term127 x n y m).
Proof. exact (eq_refl (term127 x n y m)). Qed.
Lemma lem1274041 (x : nadd) (y : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term128 x y B1 B2 m n) = (term129 x y B1 B2 m n).
Proof. exact (MK_COMB (@lem1274040 x n y m) (@lem1274039 B1 B2 m n)). Qed.
Lemma lem1274042 (x : nadd) (y : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term129 x y B1 B2 m n) = (term128 x y B1 B2 m n).
Proof. exact (SYM (@lem1274041 x y B1 B2 m n)). Qed.
Lemma lem1274044 (m : nat) (n : nat) (p : nat) (q : nat) : term8 m n p q.
Proof. exact (EQ_MP (@lem1273795 m n p q) (@lem1273794 m n p q)). Qed.
Lemma lem1274045 (x : nadd) (y : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : term130 x y B1 B2 m n.
Proof. exact (@lem1274044 (term131 n x m) (term131 n y m) (term66 B1 m n) (term66 B2 m n)). Qed.
Lemma lem1274046 (m : nat) (x : nadd) (B1 : nat) (h1 : term70 x B1) : term132 x B1 m.
Proof. exact (@lem1273910 x B1 h1 m). Qed.
Lemma lem1274047 (x : nadd) (B1 : nat) (m : nat) : (term132 x B1 m) = (term133 x B1 m).
Proof. exact (eq_refl (term132 x B1 m)). Qed.
Lemma lem1274048 (m : nat) (x : nadd) (B1 : nat) (h1 : term70 x B1) : term133 x B1 m.
Proof. exact (EQ_MP (@lem1274047 x B1 m) (@lem1274046 m x B1 h1)). Qed.
Lemma lem1274049 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term70 x B1) : term134 x B1 m n.
Proof. exact (@lem1274048 m x B1 h1 n). Qed.
Lemma lem1274050 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term134 x B1 m n) = (term135 x B1 m n).
Proof. exact (eq_refl (term134 x B1 m n)). Qed.
Lemma lem1274051 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term70 x B1) : term135 x B1 m n.
Proof. exact (EQ_MP (@lem1274050 x B1 m n) (@lem1274049 m n x B1 h1)). Qed.
Lemma lem1274052 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term135 x B1 m n) = ((term135 x B1 m n) = True).
Proof. exact (@lem7 (term135 x B1 m n)). Qed.
Lemma lem1274054 (m : nat) (y : nadd) (B2 : nat) (h1 : term70 y B2) : term132 y B2 m.
Proof. exact (@lem1273906 y B2 h1 m). Qed.
Lemma lem1274055 (y : nadd) (B2 : nat) (m : nat) : (term132 y B2 m) = (term133 y B2 m).
Proof. exact (eq_refl (term132 y B2 m)). Qed.
Lemma lem1274056 (m : nat) (y : nadd) (B2 : nat) (h1 : term70 y B2) : term133 y B2 m.
Proof. exact (EQ_MP (@lem1274055 y B2 m) (@lem1274054 m y B2 h1)). Qed.
Lemma lem1274057 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term70 y B2) : term134 y B2 m n.
Proof. exact (@lem1274056 m y B2 h1 n). Qed.
Lemma lem1274058 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term134 y B2 m n) = (term135 y B2 m n).
Proof. exact (eq_refl (term134 y B2 m n)). Qed.
Lemma lem1274059 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term70 y B2) : term135 y B2 m n.
Proof. exact (EQ_MP (@lem1274058 y B2 m n) (@lem1274057 m n y B2 h1)). Qed.
Lemma lem1274060 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term135 y B2 m n) = ((term135 y B2 m n) = True).
Proof. exact (@lem7 (term135 y B2 m n)). Qed.
Lemma lem1274065 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term70 x B1) : (term135 x B1 m n) = True.
Proof. exact (EQ_MP (@lem1274052 x B1 m n) (@lem1274051 m n x B1 h1)). Qed.
Lemma lem1274066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1274067 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term70 x B1) : (term136 x B1 m n) = (and True).
Proof. exact (MK_COMB (@lem1274066) (@lem1274065 m n x B1 h1)). Qed.
Lemma lem1274069 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term70 y B2) : (term135 y B2 m n) = True.
Proof. exact (EQ_MP (@lem1274060 y B2 m n) (@lem1274059 m n y B2 h1)). Qed.
Lemma lem1274070 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : (term137 x B1 y B2 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem1274067 m n x B1 h1) (@lem1274069 m n y B2 h2)). Qed.
Lemma lem1274072 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1274073 : (True /\ True) = True.
Proof. exact (@lem1274072 True). Qed.
Lemma lem1274074 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : (term137 x B1 y B2 m n) = True.
Proof. exact (TRANS (@lem1274070 m n x B1 y B2 h1 h2) (@lem1274073)). Qed.
Lemma lem1274075 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : True = (term137 x B1 y B2 m n).
Proof. exact (SYM (@lem1274074 m n x B1 y B2 h1 h2)). Qed.
Lemma lem1274076 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : term137 x B1 y B2 m n.
Proof. exact (EQ_MP (@lem1274075 m n x B1 y B2 h1 h2) (@lem0)). Qed.
Lemma lem1274077 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : term129 x y B1 B2 m n.
Proof. exact (@lem1274045 x y B1 B2 m n (@lem1274076 m n x B1 y B2 h1 h2)). Qed.
Lemma lem1274078 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : term128 x y B1 B2 m n.
Proof. exact (EQ_MP (@lem1274042 x y B1 B2 m n) (@lem1274077 m n x B1 y B2 h1 h2)). Qed.
Lemma lem1274079 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : term123 x y B1 B2 m n.
Proof. exact (@lem1274036 x y B1 B2 m n (@lem1274078 m n x B1 y B2 h1 h2)). Qed.
Lemma lem1274080 (m : nat) (n : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : term122 x y B1 B2 m n.
Proof. exact (EQ_MP (@lem1274033 x y B1 B2 m n) (@lem1274079 m n x B1 y B2 h1 h2)). Qed.
Lemma lem1274085 (m : nat) (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : term138 x y B1 B2 m.
Proof. exact (fun n : nat => @lem1274080 m n x B1 y B2 h1 h2). Qed.
Lemma lem1274090 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : term139 x y B1 B2.
Proof. exact (fun m : nat => @lem1274085 m x B1 y B2 h1 h2). Qed.
Lemma lem1274091 (x : nadd) (B1 : nat) (y : nadd) (B2 : nat) (h1 : term70 x B1) (h2 : term70 y B2) : term115 x y.
Proof. exact (ex_intro (term114 x y) (Nat.add B1 B2) (@lem1274090 x B1 y B2 h1 h2)). Qed.
Lemma lem1274092 (y : nadd) (x : nadd) (B1 : nat) (h1 : term70 x B1) : term115 x y.
Proof. exact (ex_elim (@lem1273905 y) (fun B2 : nat => fun h0 : term140 y B2 => @lem1274091 x B1 y B2 h1 h0)). Qed.
Lemma lem1274093 (x : nadd) (y : nadd) : term115 x y.
Proof. exact (ex_elim (@lem1273909 x) (fun B1 : nat => fun h0 : term140 x B1 => @lem1274092 y x B1 h0)). Qed.
Lemma lem1274094 (x : nadd) (y : nadd) : (term78 x y) = (term82 x y).
Proof. exact (EQ_MP (@lem1274017 x y) (@lem1274093 x y)). Qed.
Lemma lem1274099 (x : nadd) : term141 x.
Proof. exact (fun y : nadd => @lem1274094 x y). Qed.
Lemma lem1274104 : term142.
Proof. exact (fun x : nadd => @lem1274099 x). Qed.
