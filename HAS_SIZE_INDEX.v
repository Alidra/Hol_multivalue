Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_INDEX_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXTENSION_spec.
Require Import HAS_SIZE_0_spec.
Require Import HAS_SIZE_SUC_spec.
Require Import IN_DELETE_spec.
Require Import LT_REFL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16471_spec.
Require Import thm16474_spec.
Require Import thm16483_spec.
Require Import thm16485_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm18393_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18897_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem4713724 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4713725 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4713726 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4713725 t1) (@lem4713724 t1)). Qed.
Lemma lem4713727 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4713726 t1 t2). Qed.
Lemma lem4713728 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4713729 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4713728 t1 t2) (@lem4713727 t1 t2)). Qed.
Lemma lem4713730 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4713729 t1 t2 t3). Qed.
Lemma lem4713731 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4713732 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4713731 t1 t2 t3) (@lem4713730 t1 t2 t3)). Qed.
Lemma lem4713733 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4713732 t1 t2 t3)). Qed.
Lemma lem4713734 {A : Type'} (a : A) (x : A) : term7 A a x.
Proof. exact (@lem9784 (a = x)). Qed.
Lemma lem4713735 {A : Type'} (a : A) (x : A) : (term7 A a x) = (term8 A a x).
Proof. exact (eq_refl (term7 A a x)). Qed.
Lemma lem4713736 {A : Type'} (a : A) (x : A) : term8 A a x.
Proof. exact (EQ_MP (@lem4713735 A a x) (@lem4713734 A a x)). Qed.
Lemma lem4713737 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4713738 {A : Type'} (a : A) (x : A) (h1 : term9 A a x) : term9 A a x.
Proof. exact (h1). Qed.
Lemma lem4713749 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem4713750 {A : Type'} (P : A -> Prop) : (term10 A P) = ((term11 A P) = (term12 A P)).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem4713752 {A : Type'} (x : A) : term13 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4713753 {A : Type'} (x : A) : (term13 A x) = (term14 A x).
Proof. exact (eq_refl (term13 A x)). Qed.
Lemma lem4713754 {A : Type'} (x : A) : term14 A x.
Proof. exact (EQ_MP (@lem4713753 A x) (@lem4713752 A x)). Qed.
Lemma lem4713755 {A : Type'} (x : A) : term15 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4713757 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4713758 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem4713759 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem4713758 A s) (@lem4713757 A s)). Qed.
Lemma lem4713760 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem4713759 A s t). Qed.
Lemma lem4713761 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem4713763 {A : Type'} (x : A) : term13 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4713764 {A : Type'} (x : A) : (term13 A x) = (term14 A x).
Proof. exact (eq_refl (term13 A x)). Qed.
Lemma lem4713765 {A : Type'} (x : A) : term14 A x.
Proof. exact (EQ_MP (@lem4713764 A x) (@lem4713763 A x)). Qed.
Lemma lem4713766 {A : Type'} (x : A) : term15 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4713768 : term20.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem4713769 (m : nat) : term21 m.
Proof. exact (@lem4713768 m). Qed.
Lemma lem4713770 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem4713771 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem4713770 m) (@lem4713769 m)). Qed.
Lemma lem4713772 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem4713771 m n). Qed.
Lemma lem4713773 (m : nat) (n : nat) : (term23 m n) = ((term24 m n) = (term25 m n)).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem4713775 : term26.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem4713776 (m : nat) : term27 m.
Proof. exact (@lem4713775 m). Qed.
Lemma lem4713777 (m : nat) : (term27 m) = ((term28 m) = False).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem4713779 {A : Type'} (s : A -> Prop) : term29 A s.
Proof. exact (@lem3867912 A s). Qed.
Lemma lem4713780 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (eq_refl (term29 A s)). Qed.
Lemma lem4713781 {A : Type'} (s : A -> Prop) : term30 A s.
Proof. exact (EQ_MP (@lem4713780 A s) (@lem4713779 A s)). Qed.
Lemma lem4713782 {A : Type'} (s : A -> Prop) (n : nat) : term31 A s n.
Proof. exact (@lem4713781 A s n). Qed.
Lemma lem4713783 {A : Type'} (s : A -> Prop) (n : nat) : (term31 A s n) = ((term32 A s n) = (term33 A s n)).
Proof. exact (eq_refl (term31 A s n)). Qed.
Lemma lem4713785 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (@lem3864294 A s). Qed.
Lemma lem4713786 {A : Type'} (s : A -> Prop) : (term34 A s) = ((term35 A s) = (s = (@EMPTY A))).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem4713788 {A B : Type'} (P : type1413 A B) : term36 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem4713789 {A B : Type'} (P : type1413 A B) : (term36 A B P) = ((term37 A B P) = (term38 A B P)).
Proof. exact (eq_refl (term36 A B P)). Qed.
Lemma lem4713792 {A B : Type'} (P : type1413 A B) : (term37 A B P) = (term38 A B P).
Proof. exact (EQ_MP (@lem4713789 A B P) (@lem4713788 A B P)). Qed.
Lemma lem4713793 {A : Type'} (P : type682 A) : (term39 A P) = (term40 A P).
Proof. exact (@lem4713792 (A -> Prop) nat P). Qed.
Lemma lem4713794 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (@lem4713793 A (term43 A)). Qed.
Lemma lem4713795 {A : Type'} (s : A -> Prop) : (term44 A s) = (term45 A s).
Proof. exact (eq_refl (term44 A s)). Qed.
Lemma lem4713796 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4713797 {A : Type'} (s : A -> Prop) (n : nat) : (term46 A s n) = (term47 A s n).
Proof. exact (MK_COMB (@lem4713795 A s) (@lem4713796 n)). Qed.
Lemma lem4713798 {A : Type'} (s : A -> Prop) (n : nat) : (term47 A s n) = (term48 A s n).
Proof. exact (eq_refl (term47 A s n)). Qed.
Lemma lem4713799 {A : Type'} (s : A -> Prop) (n : nat) : (term46 A s n) = (term48 A s n).
Proof. exact (TRANS (@lem4713797 A s n) (@lem4713798 A s n)). Qed.
Lemma lem4713800 {A : Type'} (s : A -> Prop) : (term49 A s) = (term45 A s).
Proof. exact (fun_ext (fun n : nat => @lem4713799 A s n)). Qed.
Lemma lem4713801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4713802 {A : Type'} (s : A -> Prop) : (term50 A s) = (term51 A s).
Proof. exact (MK_COMB (@lem4713801) (@lem4713800 A s)). Qed.
Lemma lem4713803 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4713802 A s)). Qed.
Lemma lem4713804 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4713805 {A : Type'} : (term41 A) = (term54 A).
Proof. exact (MK_COMB (@lem4713804 A) (@lem4713803 A)). Qed.
Lemma lem4713806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4713807 {A : Type'} : (term55 A) = (term56 A).
Proof. exact (MK_COMB (@lem4713806) (@lem4713805 A)). Qed.
Lemma lem4713808 {A : Type'} (s : A -> Prop) : (term44 A s) = (term45 A s).
Proof. exact (eq_refl (term44 A s)). Qed.
Lemma lem4713809 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4713810 {A : Type'} (s : A -> Prop) (n : nat) : (term46 A s n) = (term47 A s n).
Proof. exact (MK_COMB (@lem4713808 A s) (@lem4713809 n)). Qed.
Lemma lem4713811 {A : Type'} (s : A -> Prop) (n : nat) : (term47 A s n) = (term48 A s n).
Proof. exact (eq_refl (term47 A s n)). Qed.
Lemma lem4713812 {A : Type'} (s : A -> Prop) (n : nat) : (term46 A s n) = (term48 A s n).
Proof. exact (TRANS (@lem4713810 A s n) (@lem4713811 A s n)). Qed.
Lemma lem4713813 {A : Type'} (n : nat) : (term57 A n) = (term58 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4713812 A s n)). Qed.
Lemma lem4713814 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4713815 {A : Type'} (n : nat) : (term59 A n) = (term60 A n).
Proof. exact (MK_COMB (@lem4713814 A) (@lem4713813 A n)). Qed.
Lemma lem4713816 {A : Type'} : (term61 A) = (term62 A).
Proof. exact (fun_ext (fun n : nat => @lem4713815 A n)). Qed.
Lemma lem4713817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4713818 {A : Type'} : (term42 A) = (term63 A).
Proof. exact (MK_COMB (@lem4713817) (@lem4713816 A)). Qed.
Lemma lem4713819 {A : Type'} : ((term41 A) = (term42 A)) = ((term54 A) = (term63 A)).
Proof. exact (MK_COMB (@lem4713807 A) (@lem4713818 A)). Qed.
Lemma lem4713820 {A : Type'} : (term54 A) = (term63 A).
Proof. exact (EQ_MP (@lem4713819 A) (@lem4713794 A)). Qed.
Lemma lem4713821 {A : Type'} : (term63 A) = (term54 A).
Proof. exact (SYM (@lem4713820 A)). Qed.
Lemma lem4713823 (P : nat -> Prop) : term64 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem4713824 {A : Type'} : term65 A.
Proof. exact (@lem4713823 (term62 A)). Qed.
Lemma lem4713825 {A : Type'} : (term66 A) = (term67 A).
Proof. exact (eq_refl (term66 A)). Qed.
Lemma lem4713826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4713827 {A : Type'} : (term68 A) = (term69 A).
Proof. exact (MK_COMB (@lem4713826) (@lem4713825 A)). Qed.
Lemma lem4713828 {A : Type'} (n : nat) : (term70 A n) = (term60 A n).
Proof. exact (eq_refl (term70 A n)). Qed.
Lemma lem4713829 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4713830 {A : Type'} (n : nat) : (term71 A n) = (term72 A n).
Proof. exact (MK_COMB (@lem4713829) (@lem4713828 A n)). Qed.
Lemma lem4713831 {A : Type'} (n : nat) : (term73 A n) = (term74 A n).
Proof. exact (eq_refl (term73 A n)). Qed.
Lemma lem4713832 {A : Type'} (n : nat) : (term75 A n) = (term76 A n).
Proof. exact (MK_COMB (@lem4713830 A n) (@lem4713831 A n)). Qed.
Lemma lem4713833 {A : Type'} : (term77 A) = (term78 A).
Proof. exact (fun_ext (fun n : nat => @lem4713832 A n)). Qed.
Lemma lem4713834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4713835 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (MK_COMB (@lem4713834) (@lem4713833 A)). Qed.
Lemma lem4713836 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (MK_COMB (@lem4713827 A) (@lem4713835 A)). Qed.
Lemma lem4713837 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4713838 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (MK_COMB (@lem4713837) (@lem4713836 A)). Qed.
Lemma lem4713839 {A : Type'} (n : nat) : (term70 A n) = (term60 A n).
Proof. exact (eq_refl (term70 A n)). Qed.
Lemma lem4713840 {A : Type'} : (term85 A) = (term62 A).
Proof. exact (fun_ext (fun n : nat => @lem4713839 A n)). Qed.
Lemma lem4713841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4713842 {A : Type'} : (term86 A) = (term63 A).
Proof. exact (MK_COMB (@lem4713841) (@lem4713840 A)). Qed.
Lemma lem4713843 {A : Type'} : (term65 A) = (term87 A).
Proof. exact (MK_COMB (@lem4713838 A) (@lem4713842 A)). Qed.
Lemma lem4713844 {A : Type'} : term87 A.
Proof. exact (EQ_MP (@lem4713843 A) (@lem4713824 A)). Qed.
Lemma lem4713845 {A : Type'} (n : nat) (h1 : term60 A n) : term60 A n.
Proof. exact (h1). Qed.
Lemma lem4713853 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4713854 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4713853 p q p' q'). Qed.
Lemma lem4713855 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4713854 p q p'). Qed.
Lemma lem4713856 {A : Type'} (s : A -> Prop) : term91 A s.
Proof. exact (@lem4713855 (term35 A s) (term92 A s)). Qed.
Lemma lem4713857 {A : Type'} (s : A -> Prop) (p' : Prop) : term93 A s p'.
Proof. exact (@lem4713856 A s p'). Qed.
Lemma lem4713858 {A : Type'} (s : A -> Prop) (p' : Prop) : (term93 A s p') = (term94 A s p').
Proof. exact (eq_refl (term93 A s p')). Qed.
Lemma lem4713859 {A : Type'} (s : A -> Prop) (p' : Prop) : term94 A s p'.
Proof. exact (EQ_MP (@lem4713858 A s p') (@lem4713857 A s p')). Qed.
Lemma lem4713860 {A : Type'} (s : A -> Prop) (p' : Prop) (q' : Prop) : term95 A s p' q'.
Proof. exact (@lem4713859 A s p' q'). Qed.
Lemma lem4713861 {A : Type'} (s : A -> Prop) (p' : Prop) (q' : Prop) : (term95 A s p' q') = (term96 A s p' q').
Proof. exact (eq_refl (term95 A s p' q')). Qed.
Lemma lem4713862 {A : Type'} (s : A -> Prop) (p' : Prop) (q' : Prop) : term96 A s p' q'.
Proof. exact (EQ_MP (@lem4713861 A s p' q') (@lem4713860 A s p' q')). Qed.
Lemma lem4713864 {A : Type'} (s : A -> Prop) : (term35 A s) = (s = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4713786 A s) (@lem4713785 A s)). Qed.
Lemma lem4713865 {A : Type'} (s : A -> Prop) : (term35 A s) = (s = (@EMPTY A)).
Proof. exact (@lem4713864 A s). Qed.
Lemma lem4713868 {A : Type'} (s : A -> Prop) (q' : Prop) : term97 A s q'.
Proof. exact (@lem4713862 A s (s = (@EMPTY A)) q'). Qed.
Lemma lem4713869 {A : Type'} (s : A -> Prop) (q' : Prop) : term98 A s q'.
Proof. exact (@lem4713868 A s q' (@lem4713865 A s)). Qed.
Lemma lem4713884 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4713885 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4713884 p q p' q'). Qed.
Lemma lem4713886 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4713885 p q p'). Qed.
Lemma lem4713887 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : term99 A f m s.
Proof. exact (@lem4713886 (term28 m) (term100 A f m s)). Qed.
Lemma lem4713888 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) : term101 A f m s p'.
Proof. exact (@lem4713887 A f m s p'). Qed.
Lemma lem4713889 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) : (term101 A f m s p') = (term102 A f m s p').
Proof. exact (eq_refl (term101 A f m s p')). Qed.
Lemma lem4713890 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) : term102 A f m s p'.
Proof. exact (EQ_MP (@lem4713889 A f m s p') (@lem4713888 A f m s p')). Qed.
Lemma lem4713891 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) (q' : Prop) : term103 A f m s p' q'.
Proof. exact (@lem4713890 A f m s p' q'). Qed.
Lemma lem4713892 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term103 A f m s p' q') = (term104 A f m s p' q').
Proof. exact (eq_refl (term103 A f m s p' q')). Qed.
Lemma lem4713893 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) (q' : Prop) : term104 A f m s p' q'.
Proof. exact (EQ_MP (@lem4713892 A f m s p' q') (@lem4713891 A f m s p' q')). Qed.
Lemma lem4713895 (m : nat) : (term28 m) = False.
Proof. exact (EQ_MP (@lem4713777 m) (@lem4713776 m)). Qed.
Lemma lem4713896 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (q' : Prop) : term105 A f m s q'.
Proof. exact (@lem4713893 A f m s False q'). Qed.
Lemma lem4713897 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (q' : Prop) : term106 A f m s q'.
Proof. exact (@lem4713896 A f m s q' (@lem4713895 m)). Qed.
Lemma lem4713898 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem4713899 : False = (False = True).
Proof. exact (@lem7 False). Qed.
Lemma lem4713902 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4713903 {A : Type'} (f : nat -> A) (m : nat) : (term107 A f m) = (term107 A f m).
Proof. exact (eq_refl (term107 A f m)). Qed.
Lemma lem4713904 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term100 A f m s) = (term108 A f m).
Proof. exact (MK_COMB (@lem4713903 A f m) (@lem4713902 A s h1)). Qed.
Lemma lem4713906 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4713766 A x (@lem4713765 A x)). Qed.
Lemma lem4713907 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4713906 A x). Qed.
Lemma lem4713908 {A : Type'} (f : nat -> A) (m : nat) : (term108 A f m) = False.
Proof. exact (@lem4713907 A (f m)). Qed.
Lemma lem4713910 (h1 : False) : False = True.
Proof. exact (EQ_MP (@lem4713899) (@lem4713898 h1)). Qed.
Lemma lem4713911 {A : Type'} (f : nat -> A) (m : nat) (h1 : False) : (term108 A f m) = True.
Proof. exact (TRANS (@lem4713908 A f m) (@lem4713910 h1)). Qed.
Lemma lem4713912 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : False) (h2 : s = (@EMPTY A)) : (term100 A f m s) = True.
Proof. exact (TRANS (@lem4713904 A f m s h2) (@lem4713911 A f m h1)). Qed.
Lemma lem4713913 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : term109 A f m s.
Proof. exact (fun h0 : False => @lem4713912 A f m s h0 h1). Qed.
Lemma lem4713914 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : term110 A f m s.
Proof. exact (@lem4713897 A f m s True). Qed.
Lemma lem4713915 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term111 A f m s) = (False -> True).
Proof. exact (@lem4713914 A f m s (@lem4713913 A f m s h1)). Qed.
Lemma lem4713917 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4713918 : (False -> True) = True.
Proof. exact (@lem4713917 True). Qed.
Lemma lem4713919 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term111 A f m s) = True.
Proof. exact (TRANS (@lem4713915 A f m s h1) (@lem4713918)). Qed.
Lemma lem4713920 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term112 A f s) = term113.
Proof. exact (fun_ext (fun m : nat => @lem4713919 A f m s h1)). Qed.
Lemma lem4713921 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4713922 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term114 A f s) = term115.
Proof. exact (MK_COMB (@lem4713921) (@lem4713920 A f s h1)). Qed.
Lemma lem4713924 {A : Type'} (t : Prop) : (term116 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4713925 (t : Prop) : (term117 t) = t.
Proof. exact (@lem4713924 nat t). Qed.
Lemma lem4713926 : term115 = True.
Proof. exact (@lem4713925 True). Qed.
Lemma lem4713927 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term114 A f s) = True.
Proof. exact (TRANS (@lem4713922 A f s h1) (@lem4713926)). Qed.
Lemma lem4713928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4713929 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term118 A f s) = (and True).
Proof. exact (MK_COMB (@lem4713928) (@lem4713927 A f s h1)). Qed.
Lemma lem4713937 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4713938 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4713937 p q p' q'). Qed.
Lemma lem4713939 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4713938 p q p'). Qed.
Lemma lem4713940 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : A) : term119 A s f x.
Proof. exact (@lem4713939 (@IN A x s) (term120 A f x)). Qed.
Lemma lem4713941 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : A) (p' : Prop) : term121 A s f x p'.
Proof. exact (@lem4713940 A s f x p'). Qed.
Lemma lem4713942 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : A) (p' : Prop) : (term121 A s f x p') = (term122 A s f x p').
Proof. exact (eq_refl (term121 A s f x p')). Qed.
Lemma lem4713943 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : A) (p' : Prop) : term122 A s f x p'.
Proof. exact (EQ_MP (@lem4713942 A s f x p') (@lem4713941 A s f x p')). Qed.
Lemma lem4713944 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : term123 A s f x p' q'.
Proof. exact (@lem4713943 A s f x p' q'). Qed.
Lemma lem4713945 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : (term123 A s f x p' q') = (term124 A s f x p' q').
Proof. exact (eq_refl (term123 A s f x p' q')). Qed.
Lemma lem4713946 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : term124 A s f x p' q'.
Proof. exact (EQ_MP (@lem4713945 A s f x p' q') (@lem4713944 A s f x p' q')). Qed.
Lemma lem4713948 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4713949 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4713950 {A : Type'} (x : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@IN A x s) = (@IN A x (@EMPTY A)).
Proof. exact (MK_COMB (@lem4713949 A x) (@lem4713948 A s h1)). Qed.
Lemma lem4713952 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4713766 A x (@lem4713765 A x)). Qed.
Lemma lem4713953 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4713952 A x). Qed.
Lemma lem4713954 {A : Type'} (x : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@IN A x s) = False.
Proof. exact (TRANS (@lem4713950 A x s h1) (@lem4713953 A x)). Qed.
Lemma lem4713955 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : A) (q' : Prop) : term125 A s f x q'.
Proof. exact (@lem4713946 A s f x False q'). Qed.
Lemma lem4713956 {A : Type'} (f : nat -> A) (x : A) (q' : Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : term126 A s f x q'.
Proof. exact (@lem4713955 A s f x q' (@lem4713954 A x s h1)). Qed.
Lemma lem4713957 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem4713958 : False = (False = True).
Proof. exact (@lem7 False). Qed.
Lemma lem4713963 (m : nat) : (term28 m) = False.
Proof. exact (EQ_MP (@lem4713777 m) (@lem4713776 m)). Qed.
Lemma lem4713965 (h1 : False) : False = True.
Proof. exact (EQ_MP (@lem4713958) (@lem4713957 h1)). Qed.
Lemma lem4713966 (m : nat) (h1 : False) : (term28 m) = True.
Proof. exact (TRANS (@lem4713963 m) (@lem4713965 h1)). Qed.
Lemma lem4713967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4713968 (m : nat) (h1 : False) : (term127 m) = (and True).
Proof. exact (MK_COMB (@lem4713967) (@lem4713966 m h1)). Qed.
Lemma lem4713971 {A : Type'} (f : nat -> A) (m : nat) (x : A) : ((f m) = x) = ((f m) = x).
Proof. exact (eq_refl ((f m) = x)). Qed.
Lemma lem4713972 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : False) : (term128 A f m x) = (term129 A f m x).
Proof. exact (MK_COMB (@lem4713968 m h1) (@lem4713971 A f m x)). Qed.
Lemma lem4713974 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4713975 {A : Type'} (f : nat -> A) (m : nat) (x : A) : (term129 A f m x) = ((f m) = x).
Proof. exact (@lem4713974 ((f m) = x)). Qed.
Lemma lem4713978 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : False) : (term128 A f m x) = ((f m) = x).
Proof. exact (TRANS (@lem4713972 A f m x h1) (@lem4713975 A f m x)). Qed.
Lemma lem4713979 {A : Type'} (f : nat -> A) (x : A) (h1 : False) : (term130 A f x) = (term131 A f x).
Proof. exact (fun_ext (fun m : nat => @lem4713978 A f m x h1)). Qed.
Lemma lem4713982 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4713983 {A : Type'} (f : nat -> A) (x : A) (h1 : False) : (term120 A f x) = (term132 A f x).
Proof. exact (MK_COMB (@lem4713982) (@lem4713979 A f x h1)). Qed.
Lemma lem4713986 {A : Type'} (f : nat -> A) (x : A) : term133 A f x.
Proof. exact (fun h0 : False => @lem4713983 A f x h0). Qed.
Lemma lem4713987 {A : Type'} (f : nat -> A) (x : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : term134 A s f x.
Proof. exact (@lem4713956 A f x (term132 A f x) s h1). Qed.
Lemma lem4713988 {A : Type'} (f : nat -> A) (x : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term135 A s f x) = (term136 A f x).
Proof. exact (@lem4713987 A f x s h1 (@lem4713986 A f x)). Qed.
Lemma lem4713990 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4713991 {A : Type'} (f : nat -> A) (x : A) : (term136 A f x) = True.
Proof. exact (@lem4713990 (term132 A f x)). Qed.
Lemma lem4713992 {A : Type'} (f : nat -> A) (x : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term135 A s f x) = True.
Proof. exact (TRANS (@lem4713988 A f x s h1) (@lem4713991 A f x)). Qed.
Lemma lem4713993 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term137 A s f) = (term138 A).
Proof. exact (fun_ext (fun x : A => @lem4713992 A f x s h1)). Qed.
Lemma lem4713994 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4713995 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term139 A s f) = (term140 A).
Proof. exact (MK_COMB (@lem4713994 A) (@lem4713993 A f s h1)). Qed.
Lemma lem4713997 {A : Type'} (t : Prop) : (term116 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4713998 {A : Type'} (t : Prop) : (term116 A t) = t.
Proof. exact (@lem4713997 A t). Qed.
Lemma lem4713999 {A : Type'} : (term140 A) = True.
Proof. exact (@lem4713998 A True). Qed.
Lemma lem4714000 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term139 A s f) = True.
Proof. exact (TRANS (@lem4713995 A f s h1) (@lem4713999 A)). Qed.
Lemma lem4714001 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term141 A s f) = (True /\ True).
Proof. exact (MK_COMB (@lem4713929 A f s h1) (@lem4714000 A f s h1)). Qed.
Lemma lem4714003 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4714004 : (True /\ True) = True.
Proof. exact (@lem4714003 True). Qed.
Lemma lem4714005 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term141 A s f) = True.
Proof. exact (TRANS (@lem4714001 A f s h1) (@lem4714004)). Qed.
Lemma lem4714006 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term142 A s) = (term143 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4714005 A f s h1)). Qed.
Lemma lem4714007 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem4714008 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term92 A s) = (term144 A).
Proof. exact (MK_COMB (@lem4714007 A) (@lem4714006 A s h1)). Qed.
Lemma lem4714010 {A : Type'} (t : Prop) : (term145 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem4714011 {A : Type'} (t : Prop) : (term146 A t) = t.
Proof. exact (@lem4714010 (nat -> A) t). Qed.
Lemma lem4714012 {A : Type'} : (term144 A) = True.
Proof. exact (@lem4714011 A True). Qed.
Lemma lem4714013 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term92 A s) = True.
Proof. exact (TRANS (@lem4714008 A s h1) (@lem4714012 A)). Qed.
Lemma lem4714014 {A : Type'} (s : A -> Prop) : term147 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem4714013 A s h0). Qed.
Lemma lem4714015 {A : Type'} (s : A -> Prop) : term148 A s.
Proof. exact (@lem4713869 A s True). Qed.
Lemma lem4714016 {A : Type'} (s : A -> Prop) : (term149 A s) = (term150 A s).
Proof. exact (@lem4714015 A s (@lem4714014 A s)). Qed.
Lemma lem4714020 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4714021 {A : Type'} (s : A -> Prop) : (term150 A s) = True.
Proof. exact (@lem4714020 (s = (@EMPTY A))). Qed.
Lemma lem4714022 {A : Type'} (s : A -> Prop) : (term149 A s) = True.
Proof. exact (TRANS (@lem4714016 A s) (@lem4714021 A s)). Qed.
Lemma lem4714023 {A : Type'} : (term151 A) = (term152 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4714022 A s)). Qed.
Lemma lem4714024 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4714025 {A : Type'} : (term67 A) = (term153 A).
Proof. exact (MK_COMB (@lem4714024 A) (@lem4714023 A)). Qed.
Lemma lem4714027 {A : Type'} (t : Prop) : (term116 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4714028 {A : Type'} (t : Prop) : (term154 A t) = t.
Proof. exact (@lem4714027 (A -> Prop) t). Qed.
Lemma lem4714029 {A : Type'} : (term153 A) = True.
Proof. exact (@lem4714028 A True). Qed.
Lemma lem4714030 {A : Type'} : (term67 A) = True.
Proof. exact (TRANS (@lem4714025 A) (@lem4714029 A)). Qed.
Lemma lem4714031 {A : Type'} : True = (term67 A).
Proof. exact (SYM (@lem4714030 A)). Qed.
Lemma lem4714032 {A : Type'} : term67 A.
Proof. exact (EQ_MP (@lem4714031 A) (@lem0)). Qed.
Lemma lem4714040 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4714041 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4714040 p q p' q'). Qed.
Lemma lem4714042 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4714041 p q p'). Qed.
Lemma lem4714043 {A : Type'} (s : A -> Prop) (n : nat) : term155 A s n.
Proof. exact (@lem4714042 (term32 A s n) (term156 A s n)). Qed.
Lemma lem4714044 {A : Type'} (s : A -> Prop) (n : nat) (p' : Prop) : term157 A s n p'.
Proof. exact (@lem4714043 A s n p'). Qed.
Lemma lem4714045 {A : Type'} (s : A -> Prop) (n : nat) (p' : Prop) : (term157 A s n p') = (term158 A s n p').
Proof. exact (eq_refl (term157 A s n p')). Qed.
Lemma lem4714046 {A : Type'} (s : A -> Prop) (n : nat) (p' : Prop) : term158 A s n p'.
Proof. exact (EQ_MP (@lem4714045 A s n p') (@lem4714044 A s n p')). Qed.
Lemma lem4714047 {A : Type'} (s : A -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term159 A s n p' q'.
Proof. exact (@lem4714046 A s n p' q'). Qed.
Lemma lem4714048 {A : Type'} (s : A -> Prop) (n : nat) (p' : Prop) (q' : Prop) : (term159 A s n p' q') = (term160 A s n p' q').
Proof. exact (eq_refl (term159 A s n p' q')). Qed.
Lemma lem4714049 {A : Type'} (s : A -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term160 A s n p' q'.
Proof. exact (EQ_MP (@lem4714048 A s n p' q') (@lem4714047 A s n p' q')). Qed.
Lemma lem4714051 {A : Type'} (s : A -> Prop) (n : nat) : (term32 A s n) = (term33 A s n).
Proof. exact (EQ_MP (@lem4713783 A s n) (@lem4713782 A s n)). Qed.
Lemma lem4714052 {A : Type'} (s : A -> Prop) (n : nat) : (term32 A s n) = (term33 A s n).
Proof. exact (@lem4714051 A s n). Qed.
Lemma lem4714084 {A : Type'} (s : A -> Prop) (n : nat) (q' : Prop) : term161 A s n q'.
Proof. exact (@lem4714049 A s n (term33 A s n) q'). Qed.
Lemma lem4714085 {A : Type'} (s : A -> Prop) (n : nat) (q' : Prop) : term162 A s n q'.
Proof. exact (@lem4714084 A s n q' (@lem4714052 A s n)). Qed.
Lemma lem4714127 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4714128 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4714127 p q p' q'). Qed.
Lemma lem4714129 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4714128 p q p'). Qed.
Lemma lem4714130 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term163 A n f m s.
Proof. exact (@lem4714129 (term24 m n) (term100 A f m s)). Qed.
Lemma lem4714131 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) : term164 A n f m s p'.
Proof. exact (@lem4714130 A n f m s p'). Qed.
Lemma lem4714132 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) : (term164 A n f m s p') = (term165 A n f m s p').
Proof. exact (eq_refl (term164 A n f m s p')). Qed.
Lemma lem4714133 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) : term165 A n f m s p'.
Proof. exact (EQ_MP (@lem4714132 A n f m s p') (@lem4714131 A n f m s p')). Qed.
Lemma lem4714134 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) (q' : Prop) : term166 A n f m s p' q'.
Proof. exact (@lem4714133 A n f m s p' q'). Qed.
Lemma lem4714135 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term166 A n f m s p' q') = (term167 A n f m s p' q').
Proof. exact (eq_refl (term166 A n f m s p' q')). Qed.
Lemma lem4714136 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (p' : Prop) (q' : Prop) : term167 A n f m s p' q'.
Proof. exact (EQ_MP (@lem4714135 A n f m s p' q') (@lem4714134 A n f m s p' q')). Qed.
Lemma lem4714138 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem4713773 m n) (@lem4713772 m n)). Qed.
Lemma lem4714143 {A : Type'} (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (q' : Prop) : term168 A f s m n q'.
Proof. exact (@lem4714136 A n f m s (term25 m n) q'). Qed.
Lemma lem4714144 {A : Type'} (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (q' : Prop) : term169 A f s m n q'.
Proof. exact (@lem4714143 A f s m n q' (@lem4714138 m n)). Qed.
Lemma lem4714148 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term100 A f m s) = (term100 A f m s).
Proof. exact (eq_refl (term100 A f m s)). Qed.
Lemma lem4714149 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term170 A n f m s.
Proof. exact (fun h0 : term25 m n => @lem4714148 A f m s). Qed.
Lemma lem4714150 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term171 A n f m s.
Proof. exact (@lem4714144 A f s m n (term100 A f m s)). Qed.
Lemma lem4714151 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term172 A n f m s) = (term173 A n f m s).
Proof. exact (@lem4714150 A n f m s (@lem4714149 A n f m s)). Qed.
Lemma lem4714183 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) : (term174 A n f s) = (term175 A n f s).
Proof. exact (fun_ext (fun m : nat => @lem4714151 A n f m s)). Qed.
Lemma lem4714215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4714216 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) : (term176 A n f s) = (term177 A n f s).
Proof. exact (MK_COMB (@lem4714215) (@lem4714183 A n f s)). Qed.
Lemma lem4714252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4714253 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) : (term178 A n f s) = (term179 A n f s).
Proof. exact (MK_COMB (@lem4714252) (@lem4714216 A n f s)). Qed.
Lemma lem4714296 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4714297 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4714296 p q p' q'). Qed.
Lemma lem4714298 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4714297 p q p'). Qed.
Lemma lem4714299 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) : term180 A s n f x.
Proof. exact (@lem4714298 (@IN A x s) (term181 A n f x)). Qed.
Lemma lem4714300 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) (p' : Prop) : term182 A s n f x p'.
Proof. exact (@lem4714299 A s n f x p'). Qed.
Lemma lem4714301 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) (p' : Prop) : (term182 A s n f x p') = (term183 A s n f x p').
Proof. exact (eq_refl (term182 A s n f x p')). Qed.
Lemma lem4714302 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) (p' : Prop) : term183 A s n f x p'.
Proof. exact (EQ_MP (@lem4714301 A s n f x p') (@lem4714300 A s n f x p')). Qed.
Lemma lem4714303 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : term184 A s n f x p' q'.
Proof. exact (@lem4714302 A s n f x p' q'). Qed.
Lemma lem4714304 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : (term184 A s n f x p' q') = (term185 A s n f x p' q').
Proof. exact (eq_refl (term184 A s n f x p' q')). Qed.
Lemma lem4714305 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : term185 A s n f x p' q'.
Proof. exact (EQ_MP (@lem4714304 A s n f x p' q') (@lem4714303 A s n f x p' q')). Qed.
Lemma lem4714306 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4714307 {A : Type'} (n : nat) (f : nat -> A) (x : A) (s : A -> Prop) (q' : Prop) : term186 A n f x s q'.
Proof. exact (@lem4714305 A s n f x (@IN A x s) q'). Qed.
Lemma lem4714308 {A : Type'} (n : nat) (f : nat -> A) (x : A) (s : A -> Prop) (q' : Prop) : term187 A n f x s q'.
Proof. exact (@lem4714307 A n f x s q' (@lem4714306 A x s)). Qed.
Lemma lem4714315 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem4713773 m n) (@lem4713772 m n)). Qed.
Lemma lem4714320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4714321 (m : nat) (n : nat) : (term188 m n) = (term189 m n).
Proof. exact (MK_COMB (@lem4714320) (@lem4714315 m n)). Qed.
Lemma lem4714328 {A : Type'} (f : nat -> A) (m : nat) (x : A) : ((f m) = x) = ((f m) = x).
Proof. exact (eq_refl ((f m) = x)). Qed.
Lemma lem4714329 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term190 A n f m x) = (term191 A n f m x).
Proof. exact (MK_COMB (@lem4714321 m n) (@lem4714328 A f m x)). Qed.
Lemma lem4714338 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term192 A n f x) = (term193 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4714329 A n f m x)). Qed.
Lemma lem4714347 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4714348 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term181 A n f x) = (term194 A n f x).
Proof. exact (MK_COMB (@lem4714347) (@lem4714338 A n f x)). Qed.
Lemma lem4714357 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) : term195 A s n f x.
Proof. exact (fun h0 : @IN A x s => @lem4714348 A n f x). Qed.
Lemma lem4714358 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) : term196 A s n f x.
Proof. exact (@lem4714308 A n f x s (term194 A n f x)). Qed.
Lemma lem4714359 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (x : A) : (term197 A s n f x) = (term198 A s n f x).
Proof. exact (@lem4714358 A s n f x (@lem4714357 A s n f x)). Qed.
Lemma lem4714399 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term199 A s n f) = (term200 A s n f).
Proof. exact (fun_ext (fun x : A => @lem4714359 A s n f x)). Qed.
Lemma lem4714439 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4714440 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term201 A s n f) = (term202 A s n f).
Proof. exact (MK_COMB (@lem4714439 A) (@lem4714399 A s n f)). Qed.
Lemma lem4714484 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term203 A s n f) = (term204 A s n f).
Proof. exact (MK_COMB (@lem4714253 A n f s) (@lem4714440 A s n f)). Qed.
Lemma lem4714565 {A : Type'} (s : A -> Prop) (n : nat) : (term205 A s n) = (term206 A s n).
Proof. exact (fun_ext (fun f : nat -> A => @lem4714484 A s n f)). Qed.
Lemma lem4714646 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem4714647 {A : Type'} (s : A -> Prop) (n : nat) : (term156 A s n) = (term207 A s n).
Proof. exact (MK_COMB (@lem4714646 A) (@lem4714565 A s n)). Qed.
Lemma lem4714732 {A : Type'} (s : A -> Prop) (n : nat) : term208 A s n.
Proof. exact (fun h0 : term33 A s n => @lem4714647 A s n). Qed.
Lemma lem4714733 {A : Type'} (s : A -> Prop) (n : nat) : term209 A s n.
Proof. exact (@lem4714085 A s n (term207 A s n)). Qed.
Lemma lem4714734 {A : Type'} (s : A -> Prop) (n : nat) : (term210 A s n) = (term211 A s n).
Proof. exact (@lem4714733 A s n (@lem4714732 A s n)). Qed.
Lemma lem4715013 {A : Type'} (n : nat) : (term212 A n) = (term213 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4714734 A s n)). Qed.
Lemma lem4715292 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4715293 {A : Type'} (n : nat) : (term74 A n) = (term214 A n).
Proof. exact (MK_COMB (@lem4715292 A) (@lem4715013 A n)). Qed.
Lemma lem4715576 {A : Type'} (n : nat) : (term214 A n) = (term74 A n).
Proof. exact (SYM (@lem4715293 A n)). Qed.
Lemma lem4715584 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem4713761 A s t) (@lem4713760 A s t)). Qed.
Lemma lem4715585 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (@lem4715584 A s t). Qed.
Lemma lem4715586 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term215 A s).
Proof. exact (@lem4715585 A s (@EMPTY A)). Qed.
Lemma lem4715596 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4713755 A x (@lem4713754 A x)). Qed.
Lemma lem4715597 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4715596 A x). Qed.
Lemma lem4715598 {A : Type'} (x : A) (s : A -> Prop) : (term216 A x s) = (term216 A x s).
Proof. exact (eq_refl (term216 A x s)). Qed.
Lemma lem4715599 {A : Type'} (x : A) (s : A -> Prop) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((@IN A x s) = False).
Proof. exact (MK_COMB (@lem4715598 A x s) (@lem4715597 A x)). Qed.
Lemma lem4715601 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4715602 {A : Type'} (x : A) (s : A -> Prop) : ((@IN A x s) = False) = (term217 A x s).
Proof. exact (@lem4715601 (@IN A x s)). Qed.
Lemma lem4715603 {A : Type'} (x : A) (s : A -> Prop) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term217 A x s).
Proof. exact (TRANS (@lem4715599 A x s) (@lem4715602 A x s)). Qed.
Lemma lem4715604 {A : Type'} (s : A -> Prop) : (term218 A s) = (term219 A s).
Proof. exact (fun_ext (fun x : A => @lem4715603 A x s)). Qed.
Lemma lem4715605 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4715606 {A : Type'} (s : A -> Prop) : (term215 A s) = (term220 A s).
Proof. exact (MK_COMB (@lem4715605 A) (@lem4715604 A s)). Qed.
Lemma lem4715611 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term220 A s).
Proof. exact (TRANS (@lem4715586 A s) (@lem4715606 A s)). Qed.
Lemma lem4715612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4715613 {A : Type'} (s : A -> Prop) : (term221 A s) = (term222 A s).
Proof. exact (MK_COMB (@lem4715612) (@lem4715611 A s)). Qed.
Lemma lem4715614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4715615 {A : Type'} (s : A -> Prop) : (term223 A s) = (term224 A s).
Proof. exact (MK_COMB (@lem4715614) (@lem4715613 A s)). Qed.
Lemma lem4715622 {A : Type'} (s : A -> Prop) (n : nat) : (term225 A s n) = (term225 A s n).
Proof. exact (eq_refl (term225 A s n)). Qed.
Lemma lem4715623 {A : Type'} (s : A -> Prop) (n : nat) : (term33 A s n) = (term226 A s n).
Proof. exact (MK_COMB (@lem4715615 A s) (@lem4715622 A s n)). Qed.
Lemma lem4715626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4715627 {A : Type'} (s : A -> Prop) (n : nat) : (term227 A s n) = (term228 A s n).
Proof. exact (MK_COMB (@lem4715626) (@lem4715623 A s n)). Qed.
Lemma lem4715664 {A : Type'} (s : A -> Prop) (n : nat) : (term207 A s n) = (term207 A s n).
Proof. exact (eq_refl (term207 A s n)). Qed.
Lemma lem4715665 {A : Type'} (s : A -> Prop) (n : nat) : (term211 A s n) = (term229 A s n).
Proof. exact (MK_COMB (@lem4715627 A s n) (@lem4715664 A s n)). Qed.
Lemma lem4715668 {A : Type'} (s : A -> Prop) (n : nat) : (term229 A s n) = (term211 A s n).
Proof. exact (SYM (@lem4715665 A s n)). Qed.
Lemma lem4715674 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem4713750 A P) (@lem4713749 A P)). Qed.
Lemma lem4715675 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (@lem4715674 A P). Qed.
Lemma lem4715676 {A : Type'} (s : A -> Prop) : (term230 A s) = (term231 A s).
Proof. exact (@lem4715675 A (term219 A s)). Qed.
Lemma lem4715677 {A : Type'} (x : A) (s : A -> Prop) : (term232 A s x) = (term217 A x s).
Proof. exact (eq_refl (term232 A s x)). Qed.
Lemma lem4715678 {A : Type'} (s : A -> Prop) : (term233 A s) = (term219 A s).
Proof. exact (fun_ext (fun x : A => @lem4715677 A x s)). Qed.
Lemma lem4715679 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4715680 {A : Type'} (s : A -> Prop) : (term234 A s) = (term220 A s).
Proof. exact (MK_COMB (@lem4715679 A) (@lem4715678 A s)). Qed.
Lemma lem4715681 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4715682 {A : Type'} (s : A -> Prop) : (term230 A s) = (term222 A s).
Proof. exact (MK_COMB (@lem4715681) (@lem4715680 A s)). Qed.
Lemma lem4715683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4715684 {A : Type'} (s : A -> Prop) : (term235 A s) = (term236 A s).
Proof. exact (MK_COMB (@lem4715683) (@lem4715682 A s)). Qed.
Lemma lem4715685 {A : Type'} (x : A) (s : A -> Prop) : (term232 A s x) = (term217 A x s).
Proof. exact (eq_refl (term232 A s x)). Qed.
Lemma lem4715686 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4715687 {A : Type'} (x : A) (s : A -> Prop) : (term237 A s x) = (term238 A x s).
Proof. exact (MK_COMB (@lem4715686) (@lem4715685 A x s)). Qed.
Lemma lem4715688 {A : Type'} (s : A -> Prop) : (term239 A s) = (term240 A s).
Proof. exact (fun_ext (fun x : A => @lem4715687 A x s)). Qed.
Lemma lem4715689 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4715690 {A : Type'} (s : A -> Prop) : (term231 A s) = (term241 A s).
Proof. exact (MK_COMB (@lem4715689 A) (@lem4715688 A s)). Qed.
Lemma lem4715691 {A : Type'} (s : A -> Prop) : ((term230 A s) = (term231 A s)) = ((term222 A s) = (term241 A s)).
Proof. exact (MK_COMB (@lem4715684 A s) (@lem4715690 A s)). Qed.
Lemma lem4715692 {A : Type'} (s : A -> Prop) : (term222 A s) = (term241 A s).
Proof. exact (EQ_MP (@lem4715691 A s) (@lem4715676 A s)). Qed.
Lemma lem4715698 (t : Prop) : (term242 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem4715699 {A : Type'} (x : A) (s : A -> Prop) : (term238 A x s) = (@IN A x s).
Proof. exact (@lem4715698 (@IN A x s)). Qed.
Lemma lem4715700 {A : Type'} (s : A -> Prop) : (term240 A s) = (term243 A s).
Proof. exact (fun_ext (fun x : A => @lem4715699 A x s)). Qed.
Lemma lem4715701 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4715702 {A : Type'} (s : A -> Prop) : (term241 A s) = (term244 A s).
Proof. exact (MK_COMB (@lem4715701 A) (@lem4715700 A s)). Qed.
Lemma lem4715707 {A : Type'} (s : A -> Prop) : (term222 A s) = (term244 A s).
Proof. exact (TRANS (@lem4715692 A s) (@lem4715702 A s)). Qed.
Lemma lem4715708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4715709 {A : Type'} (s : A -> Prop) : (term224 A s) = (term245 A s).
Proof. exact (MK_COMB (@lem4715708) (@lem4715707 A s)). Qed.
Lemma lem4715716 {A : Type'} (s : A -> Prop) (n : nat) : (term225 A s n) = (term225 A s n).
Proof. exact (eq_refl (term225 A s n)). Qed.
Lemma lem4715717 {A : Type'} (s : A -> Prop) (n : nat) : (term226 A s n) = (term246 A s n).
Proof. exact (MK_COMB (@lem4715709 A s) (@lem4715716 A s n)). Qed.
Lemma lem4715720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4715721 {A : Type'} (s : A -> Prop) (n : nat) : (term228 A s n) = (term247 A s n).
Proof. exact (MK_COMB (@lem4715720) (@lem4715717 A s n)). Qed.
Lemma lem4715752 {A : Type'} (s : A -> Prop) (n : nat) : (term207 A s n) = (term207 A s n).
Proof. exact (eq_refl (term207 A s n)). Qed.
Lemma lem4715753 {A : Type'} (s : A -> Prop) (n : nat) : (term229 A s n) = (term248 A s n).
Proof. exact (MK_COMB (@lem4715721 A s n) (@lem4715752 A s n)). Qed.
Lemma lem4715756 {A : Type'} (s : A -> Prop) (n : nat) : (term248 A s n) = (term229 A s n).
Proof. exact (SYM (@lem4715753 A s n)). Qed.
Lemma lem4715757 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term246 A s n) : term246 A s n.
Proof. exact (h1). Qed.
Lemma lem4715758 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term225 A s n) : term225 A s n.
Proof. exact (h1). Qed.
Lemma lem4715759 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term225 A s n) : term249 A s n a.
Proof. exact (@lem4715758 A s n h1 a). Qed.
Lemma lem4715760 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term249 A s n a) = (term250 A s a n).
Proof. exact (eq_refl (term249 A s n a)). Qed.
Lemma lem4715761 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term225 A s n) : term250 A s a n.
Proof. exact (EQ_MP (@lem4715760 A s a n) (@lem4715759 A a s n h1)). Qed.
Lemma lem4715762 {A : Type'} (s : A -> Prop) (h1 : term244 A s) : term244 A s.
Proof. exact (h1). Qed.
Lemma lem4715763 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem4715769 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = ((@IN A a s) = True).
Proof. exact (@lem7 (@IN A a s)). Qed.
Lemma lem4715776 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (@IN A a s) = True.
Proof. exact (EQ_MP (@lem4715769 A a s) (@lem4715763 A a s h1)). Qed.
Lemma lem4715777 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4715778 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term251 A a s) = (imp True).
Proof. exact (MK_COMB (@lem4715777) (@lem4715776 A a s h1)). Qed.
Lemma lem4715779 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term252 A s a n) = (term252 A s a n).
Proof. exact (eq_refl (term252 A s a n)). Qed.
Lemma lem4715780 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term250 A s a n) = (term253 A s a n).
Proof. exact (MK_COMB (@lem4715778 A a s h1) (@lem4715779 A s a n)). Qed.
Lemma lem4715782 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4715783 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term253 A s a n) = (term252 A s a n).
Proof. exact (@lem4715782 (term252 A s a n)). Qed.
Lemma lem4715784 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term250 A s a n) = (term252 A s a n).
Proof. exact (TRANS (@lem4715780 A n a s h1) (@lem4715783 A s a n)). Qed.
Lemma lem4715785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4715786 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term254 A s a n) = (term255 A s a n).
Proof. exact (MK_COMB (@lem4715785) (@lem4715784 A n a s h1)). Qed.
Lemma lem4715817 {A : Type'} (s : A -> Prop) (n : nat) : (term207 A s n) = (term207 A s n).
Proof. exact (eq_refl (term207 A s n)). Qed.
Lemma lem4715818 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term256 A a s n) = (term257 A a s n).
Proof. exact (MK_COMB (@lem4715786 A n a s h1) (@lem4715817 A s n)). Qed.
Lemma lem4715821 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term257 A a s n) = (term256 A a s n).
Proof. exact (SYM (@lem4715818 A n a s h1)). Qed.
Lemma lem4715822 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term252 A s a n) : term252 A s a n.
Proof. exact (h1). Qed.
Lemma lem4715823 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term60 A n) : term258 A n s a.
Proof. exact (@lem4713845 A n h1 (@DELETE A s a)). Qed.
Lemma lem4715824 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term258 A n s a) = (term259 A s a n).
Proof. exact (eq_refl (term258 A n s a)). Qed.
Lemma lem4715825 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term60 A n) : term259 A s a n.
Proof. exact (EQ_MP (@lem4715824 A s a n) (@lem4715823 A s a n h1)). Qed.
Lemma lem4715828 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term252 A s a n) = ((term252 A s a n) = True).
Proof. exact (@lem7 (term252 A s a n)). Qed.
Lemma lem4715835 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term252 A s a n) : (term252 A s a n) = True.
Proof. exact (EQ_MP (@lem4715828 A s a n) (@lem4715822 A s a n h1)). Qed.
Lemma lem4715836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4715837 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term252 A s a n) : (term255 A s a n) = (imp True).
Proof. exact (MK_COMB (@lem4715836) (@lem4715835 A s a n h1)). Qed.
Lemma lem4715860 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term260 A s a n) = (term260 A s a n).
Proof. exact (eq_refl (term260 A s a n)). Qed.
Lemma lem4715861 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term252 A s a n) : (term259 A s a n) = (term261 A s a n).
Proof. exact (MK_COMB (@lem4715837 A s a n h1) (@lem4715860 A s a n)). Qed.
Lemma lem4715863 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4715864 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term261 A s a n) = (term260 A s a n).
Proof. exact (@lem4715863 (term260 A s a n)). Qed.
Lemma lem4715887 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term252 A s a n) : (term259 A s a n) = (term260 A s a n).
Proof. exact (TRANS (@lem4715861 A s a n h1) (@lem4715864 A s a n)). Qed.
Lemma lem4715888 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4715889 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term252 A s a n) : (term262 A s a n) = (term263 A s a n).
Proof. exact (MK_COMB (@lem4715888) (@lem4715887 A s a n h1)). Qed.
Lemma lem4715920 {A : Type'} (s : A -> Prop) (n : nat) : (term207 A s n) = (term207 A s n).
Proof. exact (eq_refl (term207 A s n)). Qed.
Lemma lem4715921 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term252 A s a n) : (term264 A a s n) = (term265 A a s n).
Proof. exact (MK_COMB (@lem4715889 A s a n h1) (@lem4715920 A s n)). Qed.
Lemma lem4715924 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term252 A s a n) : (term265 A a s n) = (term264 A a s n).
Proof. exact (SYM (@lem4715921 A s a n h1)). Qed.
Lemma lem4715925 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term260 A s a n) : term260 A s a n.
Proof. exact (h1). Qed.
Lemma lem4715926 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term266 A s a n f) : term266 A s a n f.
Proof. exact (h1). Qed.
Lemma lem4715927 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term267 A s a n f) : term267 A s a n f.
Proof. exact (h1). Qed.
Lemma lem4715928 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term268 A n f s a.
Proof. exact (h1). Qed.
Lemma lem4715936 {A B : Type'} (f : A -> B) (y : A) : (term269 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4715937 {A : Type'} (f : nat -> A) (y : nat) : (term270 A f y) = (f y).
Proof. exact (@lem4715936 nat A f y). Qed.
Lemma lem4715938 {A : Type'} (n : nat) (f : nat -> A) (a : A) (m : nat) : (term271 A n f a m) = (term272 A n f a m).
Proof. exact (@lem4715937 A (term273 A n f a) m). Qed.
Lemma lem4715939 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : (term272 A n f a m) = (term274 A n f m a).
Proof. exact (eq_refl (term272 A n f a m)). Qed.
Lemma lem4715940 {A : Type'} (n : nat) (f : nat -> A) (a : A) : (term275 A n f a) = (term273 A n f a).
Proof. exact (fun_ext (fun m : nat => @lem4715939 A n f m a)). Qed.
Lemma lem4715941 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4715942 {A : Type'} (n : nat) (f : nat -> A) (a : A) (m : nat) : (term271 A n f a m) = (term272 A n f a m).
Proof. exact (MK_COMB (@lem4715940 A n f a) (@lem4715941 m)). Qed.
Lemma lem4715943 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4715944 {A : Type'} (n : nat) (f : nat -> A) (a : A) (m : nat) : (term276 A n f a m) = (term277 A n f a m).
Proof. exact (MK_COMB (@lem4715943 A) (@lem4715942 A n f a m)). Qed.
Lemma lem4715945 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : (term272 A n f a m) = (term274 A n f m a).
Proof. exact (eq_refl (term272 A n f a m)). Qed.
Lemma lem4715946 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : ((term271 A n f a m) = (term272 A n f a m)) = ((term272 A n f a m) = (term274 A n f m a)).
Proof. exact (MK_COMB (@lem4715944 A n f a m) (@lem4715945 A n f m a)). Qed.
Lemma lem4715947 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : (term272 A n f a m) = (term274 A n f m a).
Proof. exact (EQ_MP (@lem4715946 A n f m a) (@lem4715938 A n f a m)). Qed.
Lemma lem4715948 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4715949 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : (term278 A n f a m) = (term279 A n f m a).
Proof. exact (MK_COMB (@lem4715948 A) (@lem4715947 A n f m a)). Qed.
Lemma lem4715950 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4715951 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (s : A -> Prop) : (term280 A n f a m s) = (term281 A n f m a s).
Proof. exact (MK_COMB (@lem4715949 A n f m a) (@lem4715950 A s)). Qed.
Lemma lem4715952 (m : nat) (n : nat) : (term282 m n) = (term282 m n).
Proof. exact (eq_refl (term282 m n)). Qed.
Lemma lem4715953 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (s : A -> Prop) : (term283 A n f a m s) = (term284 A n f m a s).
Proof. exact (MK_COMB (@lem4715952 m n) (@lem4715951 A n f m a s)). Qed.
Lemma lem4715956 {A : Type'} (n : nat) (f : nat -> A) (a : A) (m : nat) (s : A -> Prop) : (term284 A n f m a s) = (term283 A n f a m s).
Proof. exact (SYM (@lem4715953 A n f m a s)). Qed.
Lemma lem4715957 {A : Type'} (_474 : A) (_475 : Prop) (_476 : A -> Prop) (_477 : A) : (term285 A _476 _475 _474 _477) = (term286 A _474 _475 _476 _477).
Proof. exact (@lem13473 A _474 _475 _476 _477). Qed.
Lemma lem4715958 {A : Type'} (_474 : A) (_475 : Prop) (m : nat) (n : nat) (s : A -> Prop) (_477 : A) : (term287 A m n s _475 _474 _477) = (term288 A _474 _475 m n s _477).
Proof. exact (@lem4715957 A _474 _475 (term289 A m n s) _477). Qed.
Lemma lem4715959 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (s : A -> Prop) (a : A) : (term290 A s n f m a) = (term291 A f m n s a).
Proof. exact (@lem4715958 A (f m) (Peano.lt m n) m n s a). Qed.
Lemma lem4715960 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term292 A m n s a) = (term293 A m n a s).
Proof. exact (eq_refl (term292 A m n s a)). Qed.
Lemma lem4715961 (m : nat) (n : nat) : (term294 m n) = (term294 m n).
Proof. exact (eq_refl (term294 m n)). Qed.
Lemma lem4715962 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term295 A m n s a) = (term296 A m n a s).
Proof. exact (MK_COMB (@lem4715961 m n) (@lem4715960 A m n a s)). Qed.
Lemma lem4715963 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term297 A n s f m) = (term173 A n f m s).
Proof. exact (eq_refl (term297 A n s f m)). Qed.
Lemma lem4715964 (m : nat) (n : nat) : (term298 m n) = (term298 m n).
Proof. exact (eq_refl (term298 m n)). Qed.
Lemma lem4715965 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term299 A n s f m) = (term300 A n f m s).
Proof. exact (MK_COMB (@lem4715964 m n) (@lem4715963 A n f m s)). Qed.
Lemma lem4715966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4715967 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term301 A n s f m) = (term302 A n f m s).
Proof. exact (MK_COMB (@lem4715966) (@lem4715965 A n f m s)). Qed.
Lemma lem4715968 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term291 A f m n s a) = (term303 A f m n a s).
Proof. exact (MK_COMB (@lem4715967 A n f m s) (@lem4715962 A m n a s)). Qed.
Lemma lem4715969 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (s : A -> Prop) : (term290 A s n f m a) = (term284 A n f m a s).
Proof. exact (eq_refl (term290 A s n f m a)). Qed.
Lemma lem4715970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4715971 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (s : A -> Prop) : (term304 A s n f m a) = (term305 A n f m a s).
Proof. exact (MK_COMB (@lem4715970) (@lem4715969 A n f m a s)). Qed.
Lemma lem4715972 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : ((term290 A s n f m a) = (term291 A f m n s a)) = ((term284 A n f m a s) = (term303 A f m n a s)).
Proof. exact (MK_COMB (@lem4715971 A n f m a s) (@lem4715968 A f m n a s)). Qed.
Lemma lem4715973 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term284 A n f m a s) = (term303 A f m n a s).
Proof. exact (EQ_MP (@lem4715972 A f m n a s) (@lem4715959 A f m n s a)). Qed.
Lemma lem4715974 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (s : A -> Prop) : (term303 A f m n a s) = (term284 A n f m a s).
Proof. exact (SYM (@lem4715973 A f m n a s)). Qed.
Lemma lem4715975 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4715976 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem4715977 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem4715976 m n) (@lem4715975 m n h1)). Qed.
Lemma lem4715978 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term306 A n f m s) = (term306 A n f m s).
Proof. exact (eq_refl (term306 A n f m s)). Qed.
Lemma lem4715979 {A : Type'} (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term307 A f s m n) = (term308 A n f m s).
Proof. exact (MK_COMB (@lem4715978 A n f m s) (@lem4715977 m n h1)). Qed.
Lemma lem4715980 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term308 A n f m s) = (term309 A n f m s).
Proof. exact (eq_refl (term308 A n f m s)). Qed.
Lemma lem4715981 {A : Type'} (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) : (term310 A f s m n) = (term310 A f s m n).
Proof. exact (eq_refl (term310 A f s m n)). Qed.
Lemma lem4715982 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : ((term307 A f s m n) = (term308 A n f m s)) = ((term307 A f s m n) = (term309 A n f m s)).
Proof. exact (MK_COMB (@lem4715981 A f s m n) (@lem4715980 A n f m s)). Qed.
Lemma lem4715983 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term307 A f s m n) = (term173 A n f m s).
Proof. exact (eq_refl (term307 A f s m n)). Qed.
Lemma lem4715984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4715985 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term310 A f s m n) = (term311 A n f m s).
Proof. exact (MK_COMB (@lem4715984) (@lem4715983 A n f m s)). Qed.
Lemma lem4715986 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term309 A n f m s) = (term309 A n f m s).
Proof. exact (eq_refl (term309 A n f m s)). Qed.
Lemma lem4715987 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : ((term307 A f s m n) = (term309 A n f m s)) = ((term173 A n f m s) = (term309 A n f m s)).
Proof. exact (MK_COMB (@lem4715985 A n f m s) (@lem4715986 A n f m s)). Qed.
Lemma lem4715988 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : ((term307 A f s m n) = (term308 A n f m s)) = ((term173 A n f m s) = (term309 A n f m s)).
Proof. exact (TRANS (@lem4715982 A n f m s) (@lem4715987 A n f m s)). Qed.
Lemma lem4715989 {A : Type'} (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term173 A n f m s) = (term309 A n f m s).
Proof. exact (EQ_MP (@lem4715988 A n f m s) (@lem4715979 A f s m n h1)). Qed.
Lemma lem4715990 {A : Type'} (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term309 A n f m s) = (term173 A n f m s).
Proof. exact (SYM (@lem4715989 A f s m n h1)). Qed.
Lemma lem4715991 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4715992 (m : nat) (n : nat) : term313 m n.
Proof. exact (@lem82 (Peano.lt m n)). Qed.
Lemma lem4715993 (m : nat) (n : nat) (h1 : term312 m n) : (Peano.lt m n) = False.
Proof. exact (@lem4715992 m n (@lem4715991 m n h1)). Qed.
Lemma lem4715994 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term314 A m n a s) = (term314 A m n a s).
Proof. exact (eq_refl (term314 A m n a s)). Qed.
Lemma lem4715995 {A : Type'} (a : A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term312 m n) : (term315 A a s m n) = (term316 A m n a s).
Proof. exact (MK_COMB (@lem4715994 A m n a s) (@lem4715993 m n h1)). Qed.
Lemma lem4715996 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term316 A m n a s) = (term317 A m n a s).
Proof. exact (eq_refl (term316 A m n a s)). Qed.
Lemma lem4715997 {A : Type'} (a : A) (s : A -> Prop) (m : nat) (n : nat) : (term318 A a s m n) = (term318 A a s m n).
Proof. exact (eq_refl (term318 A a s m n)). Qed.
Lemma lem4715998 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : ((term315 A a s m n) = (term316 A m n a s)) = ((term315 A a s m n) = (term317 A m n a s)).
Proof. exact (MK_COMB (@lem4715997 A a s m n) (@lem4715996 A m n a s)). Qed.
Lemma lem4715999 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term315 A a s m n) = (term293 A m n a s).
Proof. exact (eq_refl (term315 A a s m n)). Qed.
Lemma lem4716000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4716001 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term318 A a s m n) = (term319 A m n a s).
Proof. exact (MK_COMB (@lem4716000) (@lem4715999 A m n a s)). Qed.
Lemma lem4716002 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term317 A m n a s) = (term317 A m n a s).
Proof. exact (eq_refl (term317 A m n a s)). Qed.
Lemma lem4716003 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : ((term315 A a s m n) = (term317 A m n a s)) = ((term293 A m n a s) = (term317 A m n a s)).
Proof. exact (MK_COMB (@lem4716001 A m n a s) (@lem4716002 A m n a s)). Qed.
Lemma lem4716004 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : ((term315 A a s m n) = (term316 A m n a s)) = ((term293 A m n a s) = (term317 A m n a s)).
Proof. exact (TRANS (@lem4715998 A m n a s) (@lem4716003 A m n a s)). Qed.
Lemma lem4716005 {A : Type'} (a : A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term312 m n) : (term293 A m n a s) = (term317 A m n a s).
Proof. exact (EQ_MP (@lem4716004 A m n a s) (@lem4715995 A a s m n h1)). Qed.
Lemma lem4716006 {A : Type'} (a : A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term312 m n) : (term317 A m n a s) = (term293 A m n a s).
Proof. exact (SYM (@lem4716005 A a s m n h1)). Qed.
Lemma lem4716008 (p : Prop) : p = (term320 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4716009 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term309 A n f m s) = (term321 A n f m s).
Proof. exact (@lem4716008 (term309 A n f m s)). Qed.
Lemma lem4716010 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term321 A n f m s) = (term309 A n f m s).
Proof. exact (SYM (@lem4716009 A n f m s)). Qed.
Lemma lem4716011 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term322 A n f m s) : term322 A n f m s.
Proof. exact (h1). Qed.
Lemma lem4716012 {A : Type'} : term323 A.
Proof. exact (@lem3205803 A). Qed.
Lemma lem4716015 : term324.
Proof. exact (@lem3205803 nat). Qed.
Lemma lem4716018 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term325 A a n f m s) : term325 A a n f m s.
Proof. exact (h1). Qed.
Lemma lem4716019 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term326 A a n f m s.
Proof. exact (fun h0 : term325 A a n f m s => @lem4716018 A a n f m s h0). Qed.
Lemma lem4716020 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term326 A a n f m s) : term326 A a n f m s.
Proof. exact (h1). Qed.
Lemma lem4716021 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term325 A a n f m s) : term325 A a n f m s.
Proof. exact (h1). Qed.
Lemma lem4716022 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term326 A a n f m s) (h2 : term325 A a n f m s) : term325 A a n f m s.
Proof. exact (@lem4716020 A a n f m s h1 (@lem4716021 A a n f m s h2)). Qed.
Lemma lem4716023 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term325 A a n f m s) : term327 A a n f m s.
Proof. exact (fun h0 : term326 A a n f m s => @lem4716022 A a n f m s h0 h1). Qed.
Lemma lem4716024 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term326 A a n f m s) : term326 A a n f m s.
Proof. exact (h1). Qed.
Lemma lem4716025 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term326 A a n f m s) (h2 : term325 A a n f m s) : term325 A a n f m s.
Proof. exact (@lem4716023 A a n f m s h2 (@lem4716024 A a n f m s h1)). Qed.
Lemma lem4716026 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term326 A a n f m s) : term326 A a n f m s.
Proof. exact (fun h0 : term325 A a n f m s => @lem4716025 A a n f m s h1 h0). Qed.
Lemma lem4716027 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term328 A a n f m s.
Proof. exact (fun h0 : term326 A a n f m s => @lem4716026 A a n f m s h0). Qed.
Lemma lem4716030 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term326 A a n f m s.
Proof. exact (@lem4716027 A a n f m s (@lem4716019 A a n f m s)). Qed.
Lemma lem4716031 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term326 A a n f m s.
Proof. exact (@lem4716030 A a n f m s). Qed.
Lemma lem4716081 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem16483 t)). Qed.
Lemma lem4716082 (m : nat) (n : nat) : (term329 m n) = True.
Proof. exact (@lem4716081 (m = n)). Qed.
Lemma lem4716083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4716084 (m : nat) (n : nat) : (term330 m n) = (imp True).
Proof. exact (MK_COMB (@lem4716083) (@lem4716082 m n)). Qed.
Lemma lem4716085 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term100 A f m s) = (term100 A f m s).
Proof. exact (eq_refl (term100 A f m s)). Qed.
Lemma lem4716086 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term309 A n f m s) = (term331 A f m s).
Proof. exact (MK_COMB (@lem4716084 m n) (@lem4716085 A f m s)). Qed.
Lemma lem4716088 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem16471 t)). Qed.
Lemma lem4716089 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term331 A f m s) = (term100 A f m s).
Proof. exact (@lem4716088 (term100 A f m s)). Qed.
Lemma lem4716090 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term309 A n f m s) = (term100 A f m s).
Proof. exact (TRANS (@lem4716086 A n f m s) (@lem4716089 A f m s)). Qed.
Lemma lem4716091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4716092 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term322 A n f m s) = (term332 A f m s).
Proof. exact (MK_COMB (@lem4716091) (@lem4716090 A n f m s)). Qed.
Lemma lem4716093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4716094 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term333 A n f m s) = (term334 A f m s).
Proof. exact (MK_COMB (@lem4716093) (@lem4716092 A n f m s)). Qed.
Lemma lem4716112 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4716113 : term335 = term336.
Proof. exact (@lem4716112 term324). Qed.
Lemma lem4716128 {A : Type'} : (term337 A) = (term337 A).
Proof. exact (eq_refl (term337 A)). Qed.
Lemma lem4716129 {A : Type'} : (term338 A) = (term339 A).
Proof. exact (MK_COMB (@lem4716128 A) (@lem4716113)). Qed.
Lemma lem4716132 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term340 A n f m s) = (term341 A f m s).
Proof. exact (MK_COMB (@lem4716094 A n f m s) (@lem4716129 A)). Qed.
Lemma lem4716135 (m : nat) (n : nat) : (term298 m n) = (term298 m n).
Proof. exact (eq_refl (term298 m n)). Qed.
Lemma lem4716136 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term342 A n f m s) = (term343 A n f m s).
Proof. exact (MK_COMB (@lem4716135 m n) (@lem4716132 A n f m s)). Qed.
Lemma lem4716139 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term344 A s a n f) = (term344 A s a n f).
Proof. exact (eq_refl (term344 A s a n f)). Qed.
Lemma lem4716140 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term345 A a n f m s) = (term346 A a n f m s).
Proof. exact (MK_COMB (@lem4716139 A s a n f) (@lem4716136 A n f m s)). Qed.
Lemma lem4716143 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term347 A n f s a) = (term347 A n f s a).
Proof. exact (eq_refl (term347 A n f s a)). Qed.
Lemma lem4716144 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term348 A a n f m s) = (term349 A a n f m s).
Proof. exact (MK_COMB (@lem4716143 A n f s a) (@lem4716140 A a n f m s)). Qed.
Lemma lem4716147 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term255 A s a n) = (term255 A s a n).
Proof. exact (eq_refl (term255 A s a n)). Qed.
Lemma lem4716148 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term350 A a n f m s) = (term351 A a n f m s).
Proof. exact (MK_COMB (@lem4716147 A s a n) (@lem4716144 A a n f m s)). Qed.
Lemma lem4716151 {A : Type'} (a : A) (s : A -> Prop) : (term251 A a s) = (term251 A a s).
Proof. exact (eq_refl (term251 A a s)). Qed.
Lemma lem4716152 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term325 A a n f m s) = (term352 A a n f m s).
Proof. exact (MK_COMB (@lem4716151 A a s) (@lem4716148 A a n f m s)). Qed.
Lemma lem4716155 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term353 A n f m s) = (term354 A n f m s).
Proof. exact (fun_ext (fun a : A => @lem4716152 A a n f m s)). Qed.
Lemma lem4716156 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716157 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term355 A n f m s) = (term356 A n f m s).
Proof. exact (MK_COMB (@lem4716156 A) (@lem4716155 A n f m s)). Qed.
Lemma lem4716162 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term357 A f m s) = (term358 A f m s).
Proof. exact (fun_ext (fun n : nat => @lem4716157 A n f m s)). Qed.
Lemma lem4716163 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716164 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term359 A f m s) = (term360 A f m s).
Proof. exact (MK_COMB (@lem4716163) (@lem4716162 A f m s)). Qed.
Lemma lem4716169 {A : Type'} (m : nat) (s : A -> Prop) : (term361 A m s) = (term362 A m s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4716164 A f m s)). Qed.
Lemma lem4716170 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4716171 {A : Type'} (m : nat) (s : A -> Prop) : (term363 A m s) = (term364 A m s).
Proof. exact (MK_COMB (@lem4716170 A) (@lem4716169 A m s)). Qed.
Lemma lem4716176 {A : Type'} (s : A -> Prop) : (term365 A s) = (term366 A s).
Proof. exact (fun_ext (fun m : nat => @lem4716171 A m s)). Qed.
Lemma lem4716177 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716178 {A : Type'} (s : A -> Prop) : (term367 A s) = (term368 A s).
Proof. exact (MK_COMB (@lem4716177) (@lem4716176 A s)). Qed.
Lemma lem4716183 {A : Type'} : (term369 A) = (term370 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4716178 A s)). Qed.
Lemma lem4716184 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4716193 {A : Type'} : (term371 A) = (term372 A).
Proof. exact (MK_COMB (@lem4716184 A) (@lem4716183 A)). Qed.
Lemma lem4716204 (s : nat -> Prop) (x : nat) (y : nat) : ((term373 x s y) = (term374 s x y)) = ((term373 x s y) = (term374 s x y)).
Proof. exact (eq_refl ((term373 x s y) = (term374 s x y))). Qed.
Lemma lem4716205 (s : nat -> Prop) (x : nat) : (term375 s x) = (term375 s x).
Proof. exact (fun_ext (fun y : nat => @lem4716204 s x y)). Qed.
Lemma lem4716206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716207 (s : nat -> Prop) (x : nat) : (term376 s x) = (term376 s x).
Proof. exact (MK_COMB (@lem4716206) (@lem4716205 s x)). Qed.
Lemma lem4716208 (s : nat -> Prop) : (term377 s) = (term377 s).
Proof. exact (fun_ext (fun x : nat => @lem4716207 s x)). Qed.
Lemma lem4716209 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716210 (s : nat -> Prop) : (term378 s) = (term378 s).
Proof. exact (MK_COMB (@lem4716209) (@lem4716208 s)). Qed.
Lemma lem4716211 : term379 = term379.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4716210 s)). Qed.
Lemma lem4716212 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4716213 : term324 = term324.
Proof. exact (MK_COMB (@lem4716212) (@lem4716211)). Qed.
Lemma lem4716214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4716215 : term336 = term336.
Proof. exact (MK_COMB (@lem4716214) (@lem4716213)). Qed.
Lemma lem4716226 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term380 A x s y) = (term381 A s x y)) = ((term380 A x s y) = (term381 A s x y)).
Proof. exact (eq_refl ((term380 A x s y) = (term381 A s x y))). Qed.
Lemma lem4716227 {A : Type'} (s : A -> Prop) (x : A) : (term382 A s x) = (term382 A s x).
Proof. exact (fun_ext (fun y : A => @lem4716226 A s x y)). Qed.
Lemma lem4716228 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716229 {A : Type'} (s : A -> Prop) (x : A) : (term383 A s x) = (term383 A s x).
Proof. exact (MK_COMB (@lem4716228 A) (@lem4716227 A s x)). Qed.
Lemma lem4716230 {A : Type'} (s : A -> Prop) : (term384 A s) = (term384 A s).
Proof. exact (fun_ext (fun x : A => @lem4716229 A s x)). Qed.
Lemma lem4716231 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716232 {A : Type'} (s : A -> Prop) : (term385 A s) = (term385 A s).
Proof. exact (MK_COMB (@lem4716231 A) (@lem4716230 A s)). Qed.
Lemma lem4716233 {A : Type'} : (term386 A) = (term386 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4716232 A s)). Qed.
Lemma lem4716234 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4716235 {A : Type'} : (term323 A) = (term323 A).
Proof. exact (MK_COMB (@lem4716234 A) (@lem4716233 A)). Qed.
Lemma lem4716236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4716237 {A : Type'} : (term337 A) = (term337 A).
Proof. exact (MK_COMB (@lem4716236) (@lem4716235 A)). Qed.
Lemma lem4716238 {A : Type'} : (term339 A) = (term339 A).
Proof. exact (MK_COMB (@lem4716237 A) (@lem4716215)). Qed.
Lemma lem4716243 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term334 A f m s) = (term334 A f m s).
Proof. exact (eq_refl (term334 A f m s)). Qed.
Lemma lem4716244 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term341 A f m s) = (term341 A f m s).
Proof. exact (MK_COMB (@lem4716243 A f m s) (@lem4716238 A)). Qed.
Lemma lem4716247 (m : nat) (n : nat) : (term298 m n) = (term298 m n).
Proof. exact (eq_refl (term298 m n)). Qed.
Lemma lem4716248 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term343 A n f m s) = (term343 A n f m s).
Proof. exact (MK_COMB (@lem4716247 m n) (@lem4716244 A f m s)). Qed.
Lemma lem4716253 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term387 A n f m x) = (term387 A n f m x).
Proof. exact (eq_refl (term387 A n f m x)). Qed.
Lemma lem4716254 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term388 A n f x) = (term388 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4716253 A n f m x)). Qed.
Lemma lem4716255 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4716256 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term389 A n f x).
Proof. exact (MK_COMB (@lem4716255) (@lem4716254 A n f x)). Qed.
Lemma lem4716259 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term390 A x s a) = (term390 A x s a).
Proof. exact (eq_refl (term390 A x s a)). Qed.
Lemma lem4716260 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term391 A s a n f x) = (term391 A s a n f x).
Proof. exact (MK_COMB (@lem4716259 A x s a) (@lem4716256 A n f x)). Qed.
Lemma lem4716261 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term392 A s a n f) = (term392 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4716260 A s a n f x)). Qed.
Lemma lem4716262 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716263 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term267 A s a n f) = (term267 A s a n f).
Proof. exact (MK_COMB (@lem4716262 A) (@lem4716261 A s a n f)). Qed.
Lemma lem4716264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4716265 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term344 A s a n f) = (term344 A s a n f).
Proof. exact (MK_COMB (@lem4716264) (@lem4716263 A s a n f)). Qed.
Lemma lem4716266 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term346 A a n f m s) = (term346 A a n f m s).
Proof. exact (MK_COMB (@lem4716265 A s a n f) (@lem4716248 A n f m s)). Qed.
Lemma lem4716271 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term393 A n f m s a) = (term393 A n f m s a).
Proof. exact (eq_refl (term393 A n f m s a)). Qed.
Lemma lem4716272 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term394 A n f s a) = (term394 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4716271 A n f m s a)). Qed.
Lemma lem4716273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716274 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term268 A n f s a) = (term268 A n f s a).
Proof. exact (MK_COMB (@lem4716273) (@lem4716272 A n f s a)). Qed.
Lemma lem4716275 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4716276 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term347 A n f s a) = (term347 A n f s a).
Proof. exact (MK_COMB (@lem4716275) (@lem4716274 A n f s a)). Qed.
Lemma lem4716277 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term349 A a n f m s) = (term349 A a n f m s).
Proof. exact (MK_COMB (@lem4716276 A n f s a) (@lem4716266 A a n f m s)). Qed.
Lemma lem4716280 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term255 A s a n) = (term255 A s a n).
Proof. exact (eq_refl (term255 A s a n)). Qed.
Lemma lem4716281 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term351 A a n f m s) = (term351 A a n f m s).
Proof. exact (MK_COMB (@lem4716280 A s a n) (@lem4716277 A a n f m s)). Qed.
Lemma lem4716284 {A : Type'} (a : A) (s : A -> Prop) : (term251 A a s) = (term251 A a s).
Proof. exact (eq_refl (term251 A a s)). Qed.
Lemma lem4716285 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term352 A a n f m s) = (term352 A a n f m s).
Proof. exact (MK_COMB (@lem4716284 A a s) (@lem4716281 A a n f m s)). Qed.
Lemma lem4716286 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term354 A n f m s) = (term354 A n f m s).
Proof. exact (fun_ext (fun a : A => @lem4716285 A a n f m s)). Qed.
Lemma lem4716287 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716288 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term356 A n f m s) = (term356 A n f m s).
Proof. exact (MK_COMB (@lem4716287 A) (@lem4716286 A n f m s)). Qed.
Lemma lem4716289 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term358 A f m s) = (term358 A f m s).
Proof. exact (fun_ext (fun n : nat => @lem4716288 A n f m s)). Qed.
Lemma lem4716290 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716291 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term360 A f m s) = (term360 A f m s).
Proof. exact (MK_COMB (@lem4716290) (@lem4716289 A f m s)). Qed.
Lemma lem4716292 {A : Type'} (m : nat) (s : A -> Prop) : (term362 A m s) = (term362 A m s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4716291 A f m s)). Qed.
Lemma lem4716293 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4716294 {A : Type'} (m : nat) (s : A -> Prop) : (term364 A m s) = (term364 A m s).
Proof. exact (MK_COMB (@lem4716293 A) (@lem4716292 A m s)). Qed.
Lemma lem4716295 {A : Type'} (s : A -> Prop) : (term366 A s) = (term366 A s).
Proof. exact (fun_ext (fun m : nat => @lem4716294 A m s)). Qed.
Lemma lem4716296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716297 {A : Type'} (s : A -> Prop) : (term368 A s) = (term368 A s).
Proof. exact (MK_COMB (@lem4716296) (@lem4716295 A s)). Qed.
Lemma lem4716298 {A : Type'} : (term370 A) = (term370 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4716297 A s)). Qed.
Lemma lem4716299 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4716300 {A : Type'} : (term372 A) = (term372 A).
Proof. exact (MK_COMB (@lem4716299 A) (@lem4716298 A)). Qed.
Lemma lem4716405 {A : Type'} : (term371 A) = (term372 A).
Proof. exact (TRANS (@lem4716193 A) (@lem4716300 A)). Qed.
Lemma lem4716406 {A : Type'} : (term372 A) = (term371 A).
Proof. exact (SYM (@lem4716405 A)). Qed.
Lemma lem4716409 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term268 A n f s a.
Proof. exact (h1). Qed.
Lemma lem4716410 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term267 A s a n f) : term267 A s a n f.
Proof. exact (h1). Qed.
Lemma lem4716413 {A : Type'} (h1 : term323 A) : term323 A.
Proof. exact (h1). Qed.
Lemma lem4716433 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term393 A n f m s a) = (term395 A n f m s a).
Proof. exact (@lem17265 (Peano.lt m n) (term396 A f m s a)). Qed.
Lemma lem4716434 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term394 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4716433 A n f m s a)). Qed.
Lemma lem4716435 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716488 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term268 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4716435) (@lem4716434 A n f s a)). Qed.
Lemma lem4716489 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4716488 A n f s a) (@lem4716409 A n f s a h1)). Qed.
Lemma lem4716499 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term399 A n f m x) = (term400 A n f m x).
Proof. exact (@lem17045 (Peano.lt m n) ((f m) = x)). Qed.
Lemma lem4716504 (m' : nat) (m : nat) : (m' = m) = (m' = m).
Proof. exact (eq_refl (m' = m)). Qed.
Lemma lem4716505 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4716506 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term401 A n f x m') = (term387 A n f m' x).
Proof. exact (eq_refl (term401 A n f x m')). Qed.
Lemma lem4716507 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term399 A n f m' x) = (term400 A n f m' x).
Proof. exact (@lem4716499 A n f m' x). Qed.
Lemma lem4716508 (P : nat -> Prop) : (@ex1 nat P) = (term402 P).
Proof. exact (@lem18897 nat P). Qed.
Lemma lem4716509 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term403 A n f x).
Proof. exact (@lem4716508 (term388 A n f x)). Qed.
Lemma lem4716510 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4716511 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term404 A n f x m') = (term399 A n f m' x).
Proof. exact (MK_COMB (@lem4716510) (@lem4716506 A n f m' x)). Qed.
Lemma lem4716512 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term404 A n f x m') = (term400 A n f m' x).
Proof. exact (TRANS (@lem4716511 A n f m' x) (@lem4716507 A n f m' x)). Qed.
Lemma lem4716513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4716514 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term405 A n f x m') = (term406 A n f m' x).
Proof. exact (MK_COMB (@lem4716513) (@lem4716512 A n f m' x)). Qed.
Lemma lem4716515 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term407 A n f x m' m) = (term408 A n f x m' m).
Proof. exact (MK_COMB (@lem4716514 A n f m' x) (@lem4716504 m' m)). Qed.
Lemma lem4716516 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4716517 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term404 A n f x m) = (term399 A n f m x).
Proof. exact (MK_COMB (@lem4716516) (@lem4716505 A n f m x)). Qed.
Lemma lem4716518 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term404 A n f x m) = (term400 A n f m x).
Proof. exact (TRANS (@lem4716517 A n f m x) (@lem4716499 A n f m x)). Qed.
Lemma lem4716519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4716520 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term405 A n f x m) = (term406 A n f m x).
Proof. exact (MK_COMB (@lem4716519) (@lem4716518 A n f m x)). Qed.
Lemma lem4716521 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term409 A n f x m' m) = (term410 A n f x m' m).
Proof. exact (MK_COMB (@lem4716520 A n f m x) (@lem4716515 A n f x m' m)). Qed.
Lemma lem4716522 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term411 A n f x m) = (term412 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4716521 A n f x m' m)). Qed.
Lemma lem4716523 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716524 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term413 A n f x m) = (term414 A n f x m).
Proof. exact (MK_COMB (@lem4716523) (@lem4716522 A n f x m)). Qed.
Lemma lem4716525 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term415 A n f x) = (term416 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4716524 A n f x m)). Qed.
Lemma lem4716526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716527 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term417 A n f x) = (term418 A n f x).
Proof. exact (MK_COMB (@lem4716526) (@lem4716525 A n f x)). Qed.
Lemma lem4716528 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4716529 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term419 A n f x) = (term388 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4716528 A n f m x)). Qed.
Lemma lem4716530 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4716531 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term420 A n f x) = (term421 A n f x).
Proof. exact (MK_COMB (@lem4716530) (@lem4716529 A n f x)). Qed.
Lemma lem4716532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4716533 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term422 A n f x) = (term423 A n f x).
Proof. exact (MK_COMB (@lem4716532) (@lem4716531 A n f x)). Qed.
Lemma lem4716534 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term403 A n f x) = (term424 A n f x).
Proof. exact (MK_COMB (@lem4716533 A n f x) (@lem4716527 A n f x)). Qed.
Lemma lem4716535 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term424 A n f x).
Proof. exact (TRANS (@lem4716509 A n f x) (@lem4716534 A n f x)). Qed.
Lemma lem4716537 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4716538 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term426 A s a n f x) = (term427 A s a n f x).
Proof. exact (MK_COMB (@lem4716537 A x s a) (@lem4716535 A n f x)). Qed.
Lemma lem4716539 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term391 A s a n f x) = (term426 A s a n f x).
Proof. exact (@lem17265 (term380 A x s a) (term389 A n f x)). Qed.
Lemma lem4716540 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term391 A s a n f x) = (term427 A s a n f x).
Proof. exact (TRANS (@lem4716539 A s a n f x) (@lem4716538 A s a n f x)). Qed.
Lemma lem4716541 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term392 A s a n f) = (term428 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4716540 A s a n f x)). Qed.
Lemma lem4716542 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716543 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term267 A s a n f) = (term429 A s a n f).
Proof. exact (MK_COMB (@lem4716542 A) (@lem4716541 A s a n f)). Qed.
Lemma lem4716645 {A : Type'} (P : Prop) (Q : A -> Prop) : (term430 A P Q) = (term431 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem4716646 (P : Prop) (Q : nat -> Prop) : (term432 P Q) = (term433 P Q).
Proof. exact (@lem4716645 nat P Q). Qed.
Lemma lem4716647 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term434 A n f x m) = (term435 A n f x m).
Proof. exact (@lem4716646 (term400 A n f m x) (term436 A n f x m)). Qed.
Lemma lem4716648 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term437 A n f x m m') = (term408 A n f x m' m).
Proof. exact (eq_refl (term437 A n f x m m')). Qed.
Lemma lem4716649 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term406 A n f m x) = (term406 A n f m x).
Proof. exact (eq_refl (term406 A n f m x)). Qed.
Lemma lem4716650 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term438 A n f x m m') = (term410 A n f x m' m).
Proof. exact (MK_COMB (@lem4716649 A n f m x) (@lem4716648 A n f x m' m)). Qed.
Lemma lem4716651 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term439 A n f x m) = (term412 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4716650 A n f x m' m)). Qed.
Lemma lem4716652 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716653 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term434 A n f x m) = (term414 A n f x m).
Proof. exact (MK_COMB (@lem4716652) (@lem4716651 A n f x m)). Qed.
Lemma lem4716654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4716655 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term440 A n f x m) = (term441 A n f x m).
Proof. exact (MK_COMB (@lem4716654) (@lem4716653 A n f x m)). Qed.
Lemma lem4716656 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term437 A n f x m m') = (term408 A n f x m' m).
Proof. exact (eq_refl (term437 A n f x m m')). Qed.
Lemma lem4716657 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term442 A n f x m) = (term436 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4716656 A n f x m' m)). Qed.
Lemma lem4716658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716659 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term443 A n f x m) = (term444 A n f x m).
Proof. exact (MK_COMB (@lem4716658) (@lem4716657 A n f x m)). Qed.
Lemma lem4716660 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term406 A n f m x) = (term406 A n f m x).
Proof. exact (eq_refl (term406 A n f m x)). Qed.
Lemma lem4716661 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term435 A n f x m) = (term445 A n f x m).
Proof. exact (MK_COMB (@lem4716660 A n f m x) (@lem4716659 A n f x m)). Qed.
Lemma lem4716662 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : ((term434 A n f x m) = (term435 A n f x m)) = ((term414 A n f x m) = (term445 A n f x m)).
Proof. exact (MK_COMB (@lem4716655 A n f x m) (@lem4716661 A n f x m)). Qed.
Lemma lem4716663 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term414 A n f x m) = (term445 A n f x m).
Proof. exact (EQ_MP (@lem4716662 A n f x m) (@lem4716647 A n f x m)). Qed.
Lemma lem4716712 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term416 A n f x) = (term446 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4716663 A n f x m)). Qed.
Lemma lem4716713 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4716714 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term418 A n f x) = (term447 A n f x).
Proof. exact (MK_COMB (@lem4716713) (@lem4716712 A n f x)). Qed.
Lemma lem4716763 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term423 A n f x) = (term423 A n f x).
Proof. exact (eq_refl (term423 A n f x)). Qed.
Lemma lem4716764 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term424 A n f x) = (term448 A n f x).
Proof. exact (MK_COMB (@lem4716763 A n f x) (@lem4716714 A n f x)). Qed.
Lemma lem4716765 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4716766 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term427 A s a n f x) = (term449 A s a n f x).
Proof. exact (MK_COMB (@lem4716765 A x s a) (@lem4716764 A n f x)). Qed.
Lemma lem4716767 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term428 A s a n f) = (term450 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4716766 A s a n f x)). Qed.
Lemma lem4716768 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716769 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term429 A s a n f) = (term451 A s a n f).
Proof. exact (MK_COMB (@lem4716768 A) (@lem4716767 A s a n f)). Qed.
Lemma lem4716819 {A : Type'} (P : A -> Prop) (Q : Prop) : (term452 A P Q) = (term453 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4716820 (P : nat -> Prop) (Q : Prop) : (term454 P Q) = (term455 P Q).
Proof. exact (@lem4716819 nat P Q). Qed.
Lemma lem4716821 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term456 A n f x) = (term457 A n f x).
Proof. exact (@lem4716820 (term388 A n f x) (term447 A n f x)). Qed.
Lemma lem4716822 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4716823 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term419 A n f x) = (term388 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4716822 A n f m x)). Qed.
Lemma lem4716824 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4716825 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term420 A n f x) = (term421 A n f x).
Proof. exact (MK_COMB (@lem4716824) (@lem4716823 A n f x)). Qed.
Lemma lem4716826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4716827 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term422 A n f x) = (term423 A n f x).
Proof. exact (MK_COMB (@lem4716826) (@lem4716825 A n f x)). Qed.
Lemma lem4716828 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term447 A n f x) = (term447 A n f x).
Proof. exact (eq_refl (term447 A n f x)). Qed.
Lemma lem4716829 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term456 A n f x) = (term448 A n f x).
Proof. exact (MK_COMB (@lem4716827 A n f x) (@lem4716828 A n f x)). Qed.
Lemma lem4716830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4716831 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term458 A n f x) = (term459 A n f x).
Proof. exact (MK_COMB (@lem4716830) (@lem4716829 A n f x)). Qed.
Lemma lem4716832 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4716833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4716834 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term460 A n f x m) = (term461 A n f m x).
Proof. exact (MK_COMB (@lem4716833) (@lem4716832 A n f m x)). Qed.
Lemma lem4716835 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term447 A n f x) = (term447 A n f x).
Proof. exact (eq_refl (term447 A n f x)). Qed.
Lemma lem4716836 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term462 A m n f x) = (term463 A m n f x).
Proof. exact (MK_COMB (@lem4716834 A n f m x) (@lem4716835 A n f x)). Qed.
Lemma lem4716837 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term464 A n f x) = (term465 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4716836 A m n f x)). Qed.
Lemma lem4716838 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4716839 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term457 A n f x) = (term466 A n f x).
Proof. exact (MK_COMB (@lem4716838) (@lem4716837 A n f x)). Qed.
Lemma lem4716840 {A : Type'} (n : nat) (f : nat -> A) (x : A) : ((term456 A n f x) = (term457 A n f x)) = ((term448 A n f x) = (term466 A n f x)).
Proof. exact (MK_COMB (@lem4716831 A n f x) (@lem4716839 A n f x)). Qed.
Lemma lem4716841 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term448 A n f x) = (term466 A n f x).
Proof. exact (EQ_MP (@lem4716840 A n f x) (@lem4716821 A n f x)). Qed.
Lemma lem4716842 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4716843 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term449 A s a n f x) = (term467 A s a n f x).
Proof. exact (MK_COMB (@lem4716842 A x s a) (@lem4716841 A n f x)). Qed.
Lemma lem4716845 {A : Type'} (P : Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4716846 (P : Prop) (Q : nat -> Prop) : (term470 P Q) = (term471 P Q).
Proof. exact (@lem4716845 nat P Q). Qed.
Lemma lem4716847 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term472 A s a n f x) = (term473 A s a n f x).
Proof. exact (@lem4716846 (term474 A x s a) (term465 A n f x)). Qed.
Lemma lem4716848 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term475 A n f x m) = (term463 A m n f x).
Proof. exact (eq_refl (term475 A n f x m)). Qed.
Lemma lem4716849 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term476 A n f x) = (term465 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4716848 A m n f x)). Qed.
Lemma lem4716850 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4716851 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term477 A n f x) = (term466 A n f x).
Proof. exact (MK_COMB (@lem4716850) (@lem4716849 A n f x)). Qed.
Lemma lem4716852 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4716853 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term472 A s a n f x) = (term467 A s a n f x).
Proof. exact (MK_COMB (@lem4716852 A x s a) (@lem4716851 A n f x)). Qed.
Lemma lem4716854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4716855 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term478 A s a n f x) = (term479 A s a n f x).
Proof. exact (MK_COMB (@lem4716854) (@lem4716853 A s a n f x)). Qed.
Lemma lem4716856 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term475 A n f x m) = (term463 A m n f x).
Proof. exact (eq_refl (term475 A n f x m)). Qed.
Lemma lem4716857 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4716858 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (n : nat) (f : nat -> A) (x : A) : (term480 A s a n f x m) = (term481 A s a m n f x).
Proof. exact (MK_COMB (@lem4716857 A x s a) (@lem4716856 A m n f x)). Qed.
Lemma lem4716859 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term482 A s a n f x) = (term483 A s a n f x).
Proof. exact (fun_ext (fun m : nat => @lem4716858 A s a m n f x)). Qed.
Lemma lem4716860 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4716861 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term473 A s a n f x) = (term484 A s a n f x).
Proof. exact (MK_COMB (@lem4716860) (@lem4716859 A s a n f x)). Qed.
Lemma lem4716862 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : ((term472 A s a n f x) = (term473 A s a n f x)) = ((term467 A s a n f x) = (term484 A s a n f x)).
Proof. exact (MK_COMB (@lem4716855 A s a n f x) (@lem4716861 A s a n f x)). Qed.
Lemma lem4716863 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term467 A s a n f x) = (term484 A s a n f x).
Proof. exact (EQ_MP (@lem4716862 A s a n f x) (@lem4716847 A s a n f x)). Qed.
Lemma lem4716864 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term449 A s a n f x) = (term484 A s a n f x).
Proof. exact (TRANS (@lem4716843 A s a n f x) (@lem4716863 A s a n f x)). Qed.
Lemma lem4716865 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term450 A s a n f) = (term485 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4716864 A s a n f x)). Qed.
Lemma lem4716866 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716867 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term451 A s a n f) = (term486 A s a n f).
Proof. exact (MK_COMB (@lem4716866 A) (@lem4716865 A s a n f)). Qed.
Lemma lem4716869 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4716870 {A : Type'} (P : type1424 A) : (term489 A P) = (term490 A P).
Proof. exact (@lem4716869 A nat P). Qed.
Lemma lem4716871 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term491 A s a n f) = (term492 A s a n f).
Proof. exact (@lem4716870 A (term493 A s a n f)). Qed.
Lemma lem4716872 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term494 A s a n f x) = (term483 A s a n f x).
Proof. exact (eq_refl (term494 A s a n f x)). Qed.
Lemma lem4716873 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4716874 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) (m : nat) : (term495 A s a n f x m) = (term496 A s a n f x m).
Proof. exact (MK_COMB (@lem4716872 A s a n f x) (@lem4716873 m)). Qed.
Lemma lem4716875 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (n : nat) (f : nat -> A) (x : A) : (term496 A s a n f x m) = (term481 A s a m n f x).
Proof. exact (eq_refl (term496 A s a n f x m)). Qed.
Lemma lem4716876 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (n : nat) (f : nat -> A) (x : A) : (term495 A s a n f x m) = (term481 A s a m n f x).
Proof. exact (TRANS (@lem4716874 A s a n f x m) (@lem4716875 A s a m n f x)). Qed.
Lemma lem4716877 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term497 A s a n f x) = (term483 A s a n f x).
Proof. exact (fun_ext (fun m : nat => @lem4716876 A s a m n f x)). Qed.
Lemma lem4716878 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4716879 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term498 A s a n f x) = (term484 A s a n f x).
Proof. exact (MK_COMB (@lem4716878) (@lem4716877 A s a n f x)). Qed.
Lemma lem4716880 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term499 A s a n f) = (term485 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4716879 A s a n f x)). Qed.
Lemma lem4716881 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716882 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term491 A s a n f) = (term486 A s a n f).
Proof. exact (MK_COMB (@lem4716881 A) (@lem4716880 A s a n f)). Qed.
Lemma lem4716883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4716884 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term500 A s a n f) = (term501 A s a n f).
Proof. exact (MK_COMB (@lem4716883) (@lem4716882 A s a n f)). Qed.
Lemma lem4716885 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term494 A s a n f x) = (term483 A s a n f x).
Proof. exact (eq_refl (term494 A s a n f x)). Qed.
Lemma lem4716886 {A : Type'} (m : A -> nat) (x : A) : (m x) = (m x).
Proof. exact (eq_refl (m x)). Qed.
Lemma lem4716887 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (m : A -> nat) (x : A) : (term502 A s a n f m x) = (term503 A s a n f m x).
Proof. exact (MK_COMB (@lem4716885 A s a n f x) (@lem4716886 A m x)). Qed.
Lemma lem4716888 {A : Type'} (s : A -> Prop) (a : A) (m : A -> nat) (n : nat) (f : nat -> A) (x : A) : (term503 A s a n f m x) = (term504 A s a m n f x).
Proof. exact (eq_refl (term503 A s a n f m x)). Qed.
Lemma lem4716889 {A : Type'} (s : A -> Prop) (a : A) (m : A -> nat) (n : nat) (f : nat -> A) (x : A) : (term502 A s a n f m x) = (term504 A s a m n f x).
Proof. exact (TRANS (@lem4716887 A s a n f m x) (@lem4716888 A s a m n f x)). Qed.
Lemma lem4716890 {A : Type'} (s : A -> Prop) (a : A) (m : A -> nat) (n : nat) (f : nat -> A) : (term505 A s a n f m) = (term506 A s a m n f).
Proof. exact (fun_ext (fun x : A => @lem4716889 A s a m n f x)). Qed.
Lemma lem4716891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716892 {A : Type'} (s : A -> Prop) (a : A) (m : A -> nat) (n : nat) (f : nat -> A) : (term507 A s a n f m) = (term508 A s a m n f).
Proof. exact (MK_COMB (@lem4716891 A) (@lem4716890 A s a m n f)). Qed.
Lemma lem4716893 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term509 A s a n f) = (term510 A s a n f).
Proof. exact (fun_ext (fun m : A -> nat => @lem4716892 A s a m n f)). Qed.
Lemma lem4716894 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem4716895 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term492 A s a n f) = (term511 A s a n f).
Proof. exact (MK_COMB (@lem4716894 A) (@lem4716893 A s a n f)). Qed.
Lemma lem4716896 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : ((term491 A s a n f) = (term492 A s a n f)) = ((term486 A s a n f) = (term511 A s a n f)).
Proof. exact (MK_COMB (@lem4716884 A s a n f) (@lem4716895 A s a n f)). Qed.
Lemma lem4716897 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term486 A s a n f) = (term511 A s a n f).
Proof. exact (EQ_MP (@lem4716896 A s a n f) (@lem4716871 A s a n f)). Qed.
Lemma lem4716898 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term451 A s a n f) = (term511 A s a n f).
Proof. exact (TRANS (@lem4716867 A s a n f) (@lem4716897 A s a n f)). Qed.
Lemma lem4716899 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term429 A s a n f) = (term511 A s a n f).
Proof. exact (TRANS (@lem4716769 A s a n f) (@lem4716898 A s a n f)). Qed.
Lemma lem4716900 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term267 A s a n f) = (term511 A s a n f).
Proof. exact (TRANS (@lem4716543 A s a n f) (@lem4716899 A s a n f)). Qed.
Lemma lem4716901 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term267 A s a n f) : term511 A s a n f.
Proof. exact (EQ_MP (@lem4716900 A s a n f) (@lem4716410 A s a n f h1)). Qed.
Lemma lem4716907 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4716913 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term332 A f m s) : term332 A f m s.
Proof. exact (h1). Qed.
Lemma lem4716921 {A : Type'} (x : A) (y : A) : (term512 A x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4716923 {A : Type'} (x : A) (s : A -> Prop) : (term513 A x s) = (term513 A x s).
Proof. exact (eq_refl (term513 A x s)). Qed.
Lemma lem4716924 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term514 A s x y) = (term515 A s x y).
Proof. exact (MK_COMB (@lem4716923 A x s) (@lem4716921 A x y)). Qed.
Lemma lem4716925 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term516 A s x y) = (term514 A s x y).
Proof. exact (@lem17045 (@IN A x s) (term9 A x y)). Qed.
Lemma lem4716926 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term516 A s x y) = (term515 A s x y).
Proof. exact (TRANS (@lem4716925 A s x y) (@lem4716924 A s x y)). Qed.
Lemma lem4716932 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term517 A s x y).
Proof. exact (eq_refl (term517 A s x y)). Qed.
Lemma lem4716934 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term518 A x s y) = (term518 A x s y).
Proof. exact (eq_refl (term518 A x s y)). Qed.
Lemma lem4716935 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term519 A s x y) = (term520 A s x y).
Proof. exact (MK_COMB (@lem4716934 A x s y) (@lem4716926 A s x y)). Qed.
Lemma lem4716936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4716937 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term521 A s x y) = (term522 A s x y).
Proof. exact (MK_COMB (@lem4716936) (@lem4716935 A s x y)). Qed.
Lemma lem4716938 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term523 A s x y) = (term524 A s x y).
Proof. exact (MK_COMB (@lem4716937 A s x y) (@lem4716932 A s x y)). Qed.
Lemma lem4716939 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term380 A x s y) = (term381 A s x y)) = (term523 A s x y).
Proof. exact (@lem17784 (term380 A x s y) (term381 A s x y)). Qed.
Lemma lem4716940 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term380 A x s y) = (term381 A s x y)) = (term524 A s x y).
Proof. exact (TRANS (@lem4716939 A s x y) (@lem4716938 A s x y)). Qed.
Lemma lem4716941 {A : Type'} (s : A -> Prop) (x : A) : (term382 A s x) = (term525 A s x).
Proof. exact (fun_ext (fun y : A => @lem4716940 A s x y)). Qed.
Lemma lem4716942 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716943 {A : Type'} (s : A -> Prop) (x : A) : (term383 A s x) = (term526 A s x).
Proof. exact (MK_COMB (@lem4716942 A) (@lem4716941 A s x)). Qed.
Lemma lem4716944 {A : Type'} (s : A -> Prop) : (term384 A s) = (term527 A s).
Proof. exact (fun_ext (fun x : A => @lem4716943 A s x)). Qed.
Lemma lem4716945 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716946 {A : Type'} (s : A -> Prop) : (term385 A s) = (term528 A s).
Proof. exact (MK_COMB (@lem4716945 A) (@lem4716944 A s)). Qed.
Lemma lem4716947 {A : Type'} : (term386 A) = (term529 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4716946 A s)). Qed.
Lemma lem4716948 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4716949 {A : Type'} : (term323 A) = (term530 A).
Proof. exact (MK_COMB (@lem4716948 A) (@lem4716947 A)). Qed.
Lemma lem4716959 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4716960 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (@lem4716959 A P Q). Qed.
Lemma lem4716961 {A : Type'} (s : A -> Prop) (x : A) : (term533 A s x) = (term534 A s x).
Proof. exact (@lem4716960 A (term535 A s x) (term536 A s x)). Qed.
Lemma lem4716962 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term537 A s x y) = (term520 A s x y).
Proof. exact (eq_refl (term537 A s x y)). Qed.
Lemma lem4716963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4716964 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term538 A s x y) = (term522 A s x y).
Proof. exact (MK_COMB (@lem4716963) (@lem4716962 A s x y)). Qed.
Lemma lem4716965 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term539 A s x y) = (term517 A s x y).
Proof. exact (eq_refl (term539 A s x y)). Qed.
Lemma lem4716966 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term540 A s x y) = (term524 A s x y).
Proof. exact (MK_COMB (@lem4716964 A s x y) (@lem4716965 A s x y)). Qed.
Lemma lem4716967 {A : Type'} (s : A -> Prop) (x : A) : (term541 A s x) = (term525 A s x).
Proof. exact (fun_ext (fun y : A => @lem4716966 A s x y)). Qed.
Lemma lem4716968 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716969 {A : Type'} (s : A -> Prop) (x : A) : (term533 A s x) = (term526 A s x).
Proof. exact (MK_COMB (@lem4716968 A) (@lem4716967 A s x)). Qed.
Lemma lem4716970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4716971 {A : Type'} (s : A -> Prop) (x : A) : (term542 A s x) = (term543 A s x).
Proof. exact (MK_COMB (@lem4716970) (@lem4716969 A s x)). Qed.
Lemma lem4716972 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term537 A s x y) = (term520 A s x y).
Proof. exact (eq_refl (term537 A s x y)). Qed.
Lemma lem4716973 {A : Type'} (s : A -> Prop) (x : A) : (term544 A s x) = (term535 A s x).
Proof. exact (fun_ext (fun y : A => @lem4716972 A s x y)). Qed.
Lemma lem4716974 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716975 {A : Type'} (s : A -> Prop) (x : A) : (term545 A s x) = (term546 A s x).
Proof. exact (MK_COMB (@lem4716974 A) (@lem4716973 A s x)). Qed.
Lemma lem4716976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4716977 {A : Type'} (s : A -> Prop) (x : A) : (term547 A s x) = (term548 A s x).
Proof. exact (MK_COMB (@lem4716976) (@lem4716975 A s x)). Qed.
Lemma lem4716978 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term539 A s x y) = (term517 A s x y).
Proof. exact (eq_refl (term539 A s x y)). Qed.
Lemma lem4716979 {A : Type'} (s : A -> Prop) (x : A) : (term549 A s x) = (term536 A s x).
Proof. exact (fun_ext (fun y : A => @lem4716978 A s x y)). Qed.
Lemma lem4716980 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4716981 {A : Type'} (s : A -> Prop) (x : A) : (term550 A s x) = (term551 A s x).
Proof. exact (MK_COMB (@lem4716980 A) (@lem4716979 A s x)). Qed.
Lemma lem4716982 {A : Type'} (s : A -> Prop) (x : A) : (term534 A s x) = (term552 A s x).
Proof. exact (MK_COMB (@lem4716977 A s x) (@lem4716981 A s x)). Qed.
Lemma lem4716983 {A : Type'} (s : A -> Prop) (x : A) : ((term533 A s x) = (term534 A s x)) = ((term526 A s x) = (term552 A s x)).
Proof. exact (MK_COMB (@lem4716971 A s x) (@lem4716982 A s x)). Qed.
Lemma lem4716984 {A : Type'} (s : A -> Prop) (x : A) : (term526 A s x) = (term552 A s x).
Proof. exact (EQ_MP (@lem4716983 A s x) (@lem4716961 A s x)). Qed.
Lemma lem4717081 {A : Type'} (s : A -> Prop) : (term527 A s) = (term553 A s).
Proof. exact (fun_ext (fun x : A => @lem4716984 A s x)). Qed.
Lemma lem4717082 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4717083 {A : Type'} (s : A -> Prop) : (term528 A s) = (term554 A s).
Proof. exact (MK_COMB (@lem4717082 A) (@lem4717081 A s)). Qed.
Lemma lem4717085 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4717086 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (@lem4717085 A P Q). Qed.
Lemma lem4717087 {A : Type'} (s : A -> Prop) : (term555 A s) = (term556 A s).
Proof. exact (@lem4717086 A (term557 A s) (term558 A s)). Qed.
Lemma lem4717088 {A : Type'} (s : A -> Prop) (x : A) : (term559 A s x) = (term546 A s x).
Proof. exact (eq_refl (term559 A s x)). Qed.
Lemma lem4717089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4717090 {A : Type'} (s : A -> Prop) (x : A) : (term560 A s x) = (term548 A s x).
Proof. exact (MK_COMB (@lem4717089) (@lem4717088 A s x)). Qed.
Lemma lem4717091 {A : Type'} (s : A -> Prop) (x : A) : (term561 A s x) = (term551 A s x).
Proof. exact (eq_refl (term561 A s x)). Qed.
Lemma lem4717092 {A : Type'} (s : A -> Prop) (x : A) : (term562 A s x) = (term552 A s x).
Proof. exact (MK_COMB (@lem4717090 A s x) (@lem4717091 A s x)). Qed.
Lemma lem4717093 {A : Type'} (s : A -> Prop) : (term563 A s) = (term553 A s).
Proof. exact (fun_ext (fun x : A => @lem4717092 A s x)). Qed.
Lemma lem4717094 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4717095 {A : Type'} (s : A -> Prop) : (term555 A s) = (term554 A s).
Proof. exact (MK_COMB (@lem4717094 A) (@lem4717093 A s)). Qed.
Lemma lem4717096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4717097 {A : Type'} (s : A -> Prop) : (term564 A s) = (term565 A s).
Proof. exact (MK_COMB (@lem4717096) (@lem4717095 A s)). Qed.
Lemma lem4717098 {A : Type'} (s : A -> Prop) (x : A) : (term559 A s x) = (term546 A s x).
Proof. exact (eq_refl (term559 A s x)). Qed.
Lemma lem4717099 {A : Type'} (s : A -> Prop) : (term566 A s) = (term557 A s).
Proof. exact (fun_ext (fun x : A => @lem4717098 A s x)). Qed.
Lemma lem4717100 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4717101 {A : Type'} (s : A -> Prop) : (term567 A s) = (term568 A s).
Proof. exact (MK_COMB (@lem4717100 A) (@lem4717099 A s)). Qed.
Lemma lem4717102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4717103 {A : Type'} (s : A -> Prop) : (term569 A s) = (term570 A s).
Proof. exact (MK_COMB (@lem4717102) (@lem4717101 A s)). Qed.
Lemma lem4717104 {A : Type'} (s : A -> Prop) (x : A) : (term561 A s x) = (term551 A s x).
Proof. exact (eq_refl (term561 A s x)). Qed.
Lemma lem4717105 {A : Type'} (s : A -> Prop) : (term571 A s) = (term558 A s).
Proof. exact (fun_ext (fun x : A => @lem4717104 A s x)). Qed.
Lemma lem4717106 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4717107 {A : Type'} (s : A -> Prop) : (term572 A s) = (term573 A s).
Proof. exact (MK_COMB (@lem4717106 A) (@lem4717105 A s)). Qed.
Lemma lem4717108 {A : Type'} (s : A -> Prop) : (term556 A s) = (term574 A s).
Proof. exact (MK_COMB (@lem4717103 A s) (@lem4717107 A s)). Qed.
Lemma lem4717109 {A : Type'} (s : A -> Prop) : ((term555 A s) = (term556 A s)) = ((term554 A s) = (term574 A s)).
Proof. exact (MK_COMB (@lem4717097 A s) (@lem4717108 A s)). Qed.
Lemma lem4717110 {A : Type'} (s : A -> Prop) : (term554 A s) = (term574 A s).
Proof. exact (EQ_MP (@lem4717109 A s) (@lem4717087 A s)). Qed.
Lemma lem4717215 {A : Type'} (s : A -> Prop) : (term528 A s) = (term574 A s).
Proof. exact (TRANS (@lem4717083 A s) (@lem4717110 A s)). Qed.
Lemma lem4717216 {A : Type'} : (term529 A) = (term575 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4717215 A s)). Qed.
Lemma lem4717217 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4717218 {A : Type'} : (term530 A) = (term576 A).
Proof. exact (MK_COMB (@lem4717217 A) (@lem4717216 A)). Qed.
Lemma lem4717220 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4717221 {A : Type'} (P : type686 A) (Q : type686 A) : (term577 A P Q) = (term578 A P Q).
Proof. exact (@lem4717220 (A -> Prop) P Q). Qed.
Lemma lem4717222 {A : Type'} : (term579 A) = (term580 A).
Proof. exact (@lem4717221 A (term581 A) (term582 A)). Qed.
Lemma lem4717223 {A : Type'} (s : A -> Prop) : (term583 A s) = (term568 A s).
Proof. exact (eq_refl (term583 A s)). Qed.
Lemma lem4717224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4717225 {A : Type'} (s : A -> Prop) : (term584 A s) = (term570 A s).
Proof. exact (MK_COMB (@lem4717224) (@lem4717223 A s)). Qed.
Lemma lem4717226 {A : Type'} (s : A -> Prop) : (term585 A s) = (term573 A s).
Proof. exact (eq_refl (term585 A s)). Qed.
Lemma lem4717227 {A : Type'} (s : A -> Prop) : (term586 A s) = (term574 A s).
Proof. exact (MK_COMB (@lem4717225 A s) (@lem4717226 A s)). Qed.
Lemma lem4717228 {A : Type'} : (term587 A) = (term575 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4717227 A s)). Qed.
Lemma lem4717229 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4717230 {A : Type'} : (term579 A) = (term576 A).
Proof. exact (MK_COMB (@lem4717229 A) (@lem4717228 A)). Qed.
Lemma lem4717231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4717232 {A : Type'} : (term588 A) = (term589 A).
Proof. exact (MK_COMB (@lem4717231) (@lem4717230 A)). Qed.
Lemma lem4717233 {A : Type'} (s : A -> Prop) : (term583 A s) = (term568 A s).
Proof. exact (eq_refl (term583 A s)). Qed.
Lemma lem4717234 {A : Type'} : (term590 A) = (term581 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4717233 A s)). Qed.
Lemma lem4717235 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4717236 {A : Type'} : (term591 A) = (term592 A).
Proof. exact (MK_COMB (@lem4717235 A) (@lem4717234 A)). Qed.
Lemma lem4717237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4717238 {A : Type'} : (term593 A) = (term594 A).
Proof. exact (MK_COMB (@lem4717237) (@lem4717236 A)). Qed.
Lemma lem4717239 {A : Type'} (s : A -> Prop) : (term585 A s) = (term573 A s).
Proof. exact (eq_refl (term585 A s)). Qed.
Lemma lem4717240 {A : Type'} : (term595 A) = (term582 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4717239 A s)). Qed.
Lemma lem4717241 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4717242 {A : Type'} : (term596 A) = (term597 A).
Proof. exact (MK_COMB (@lem4717241 A) (@lem4717240 A)). Qed.
Lemma lem4717243 {A : Type'} : (term580 A) = (term598 A).
Proof. exact (MK_COMB (@lem4717238 A) (@lem4717242 A)). Qed.
Lemma lem4717244 {A : Type'} : ((term579 A) = (term580 A)) = ((term576 A) = (term598 A)).
Proof. exact (MK_COMB (@lem4717232 A) (@lem4717243 A)). Qed.
Lemma lem4717245 {A : Type'} : (term576 A) = (term598 A).
Proof. exact (EQ_MP (@lem4717244 A) (@lem4717222 A)). Qed.
Lemma lem4717360 {A : Type'} : (term530 A) = (term598 A).
Proof. exact (TRANS (@lem4717218 A) (@lem4717245 A)). Qed.
Lemma lem4717361 {A : Type'} : (term323 A) = (term598 A).
Proof. exact (TRANS (@lem4716949 A) (@lem4717360 A)). Qed.
Lemma lem4717362 {A : Type'} (h1 : term323 A) : term598 A.
Proof. exact (EQ_MP (@lem4717361 A) (@lem4716413 A h1)). Qed.
Lemma lem4717849 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term395 A n f m s a) = (term395 A n f m s a).
Proof. exact (eq_refl (term395 A n f m s a)). Qed.
Lemma lem4717850 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term397 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4717849 A n f m s a)). Qed.
Lemma lem4717851 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4717852 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term398 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4717851) (@lem4717850 A n f s a)). Qed.
Lemma lem4717853 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4717852 A n f s a) (@lem4716489 A n f s a h1)). Qed.
Lemma lem4717859 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4717869 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term332 A f m s) : term332 A f m s.
Proof. exact (h1). Qed.
Lemma lem4717898 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term517 A s x y).
Proof. exact (eq_refl (term517 A s x y)). Qed.
Lemma lem4717899 {A : Type'} (s : A -> Prop) (x : A) : (term536 A s x) = (term536 A s x).
Proof. exact (fun_ext (fun y : A => @lem4717898 A s x y)). Qed.
Lemma lem4717900 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4717901 {A : Type'} (s : A -> Prop) (x : A) : (term551 A s x) = (term551 A s x).
Proof. exact (MK_COMB (@lem4717900 A) (@lem4717899 A s x)). Qed.
Lemma lem4717902 {A : Type'} (s : A -> Prop) : (term558 A s) = (term558 A s).
Proof. exact (fun_ext (fun x : A => @lem4717901 A s x)). Qed.
Lemma lem4717903 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4717904 {A : Type'} (s : A -> Prop) : (term573 A s) = (term573 A s).
Proof. exact (MK_COMB (@lem4717903 A) (@lem4717902 A s)). Qed.
Lemma lem4717905 {A : Type'} : (term582 A) = (term582 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4717904 A s)). Qed.
Lemma lem4717906 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4717907 {A : Type'} : (term597 A) = (term597 A).
Proof. exact (MK_COMB (@lem4717906 A) (@lem4717905 A)). Qed.
Lemma lem4717934 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term520 A s x y) = (term520 A s x y).
Proof. exact (eq_refl (term520 A s x y)). Qed.
Lemma lem4717935 {A : Type'} (s : A -> Prop) (x : A) : (term535 A s x) = (term535 A s x).
Proof. exact (fun_ext (fun y : A => @lem4717934 A s x y)). Qed.
Lemma lem4717936 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4717937 {A : Type'} (s : A -> Prop) (x : A) : (term546 A s x) = (term546 A s x).
Proof. exact (MK_COMB (@lem4717936 A) (@lem4717935 A s x)). Qed.
Lemma lem4717938 {A : Type'} (s : A -> Prop) : (term557 A s) = (term557 A s).
Proof. exact (fun_ext (fun x : A => @lem4717937 A s x)). Qed.
Lemma lem4717939 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4717940 {A : Type'} (s : A -> Prop) : (term568 A s) = (term568 A s).
Proof. exact (MK_COMB (@lem4717939 A) (@lem4717938 A s)). Qed.
Lemma lem4717941 {A : Type'} : (term581 A) = (term581 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4717940 A s)). Qed.
Lemma lem4717942 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4717943 {A : Type'} : (term592 A) = (term592 A).
Proof. exact (MK_COMB (@lem4717942 A) (@lem4717941 A)). Qed.
Lemma lem4717944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4717945 {A : Type'} : (term594 A) = (term594 A).
Proof. exact (MK_COMB (@lem4717944) (@lem4717943 A)). Qed.
Lemma lem4717946 {A : Type'} : (term598 A) = (term598 A).
Proof. exact (MK_COMB (@lem4717945 A) (@lem4717907 A)). Qed.
Lemma lem4717947 {A : Type'} (h1 : term323 A) : term598 A.
Proof. exact (EQ_MP (@lem4717946 A) (@lem4717362 A h1)). Qed.
Lemma lem4718123 {A : Type'} (h1 : term323 A) : term597 A.
Proof. exact (proj2 (@lem4717947 A h1)). Qed.
Lemma lem4718140 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term395 A n f m s a) = (term395 A n f m s a).
Proof. exact (eq_refl (term395 A n f m s a)). Qed.
Lemma lem4718141 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term397 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4718140 A n f m s a)). Qed.
Lemma lem4718142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4718144 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term398 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4718142) (@lem4718141 A n f s a)). Qed.
Lemma lem4718145 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4718144 A n f s a) (@lem4717853 A n f s a h1)). Qed.
Lemma lem4718149 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4718153 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term332 A f m s) : term332 A f m s.
Proof. exact (h1). Qed.
Lemma lem4718432 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term599 A s x y).
Proof. exact (@lem19490 (@IN A x s) (term474 A x s y) (term9 A x y)). Qed.
Lemma lem4718433 {A : Type'} (s : A -> Prop) (x : A) : (term536 A s x) = (term600 A s x).
Proof. exact (fun_ext (fun y : A => @lem4718432 A s x y)). Qed.
Lemma lem4718434 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4718435 {A : Type'} (s : A -> Prop) (x : A) : (term551 A s x) = (term601 A s x).
Proof. exact (MK_COMB (@lem4718434 A) (@lem4718433 A s x)). Qed.
Lemma lem4718436 {A : Type'} (s : A -> Prop) : (term558 A s) = (term602 A s).
Proof. exact (fun_ext (fun x : A => @lem4718435 A s x)). Qed.
Lemma lem4718437 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4718438 {A : Type'} (s : A -> Prop) : (term573 A s) = (term603 A s).
Proof. exact (MK_COMB (@lem4718437 A) (@lem4718436 A s)). Qed.
Lemma lem4718439 {A : Type'} : (term582 A) = (term604 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4718438 A s)). Qed.
Lemma lem4718440 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4718442 {A : Type'} : (term597 A) = (term605 A).
Proof. exact (MK_COMB (@lem4718440 A) (@lem4718439 A)). Qed.
Lemma lem4718443 {A : Type'} (h1 : term323 A) : term605 A.
Proof. exact (EQ_MP (@lem4718442 A) (@lem4718123 A h1)). Qed.
Lemma lem4718444 {A : Type'} (_55627 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term606 A n f s a _55627.
Proof. exact (@lem4718145 A n f s a h1 _55627). Qed.
Lemma lem4718445 {A : Type'} (n : nat) (f : nat -> A) (_55627 : nat) (s : A -> Prop) (a : A) : (term606 A n f s a _55627) = (term395 A n f _55627 s a).
Proof. exact (eq_refl (term606 A n f s a _55627)). Qed.
Lemma lem4718483 {A : Type'} (_55640 : A -> Prop) (h1 : term323 A) : term607 A _55640.
Proof. exact (@lem4718443 A h1 _55640). Qed.
Lemma lem4718484 {A : Type'} (_55640 : A -> Prop) : (term607 A _55640) = (term603 A _55640).
Proof. exact (eq_refl (term607 A _55640)). Qed.
Lemma lem4718485 {A : Type'} (_55640 : A -> Prop) (h1 : term323 A) : term603 A _55640.
Proof. exact (EQ_MP (@lem4718484 A _55640) (@lem4718483 A _55640 h1)). Qed.
Lemma lem4718486 {A : Type'} (_55640 : A -> Prop) (_55641 : A) (h1 : term323 A) : term608 A _55640 _55641.
Proof. exact (@lem4718485 A _55640 h1 _55641). Qed.
Lemma lem4718487 {A : Type'} (_55640 : A -> Prop) (_55641 : A) : (term608 A _55640 _55641) = (term601 A _55640 _55641).
Proof. exact (eq_refl (term608 A _55640 _55641)). Qed.
Lemma lem4718488 {A : Type'} (_55640 : A -> Prop) (_55641 : A) (h1 : term323 A) : term601 A _55640 _55641.
Proof. exact (EQ_MP (@lem4718487 A _55640 _55641) (@lem4718486 A _55640 _55641 h1)). Qed.
Lemma lem4718489 {A : Type'} (_55640 : A -> Prop) (_55641 : A) (_55642 : A) (h1 : term323 A) : term609 A _55640 _55641 _55642.
Proof. exact (@lem4718488 A _55640 _55641 h1 _55642). Qed.
Lemma lem4718490 {A : Type'} (_55640 : A -> Prop) (_55641 : A) (_55642 : A) : (term609 A _55640 _55641 _55642) = (term599 A _55640 _55641 _55642).
Proof. exact (eq_refl (term609 A _55640 _55641 _55642)). Qed.
Lemma lem4718491 {A : Type'} (_55640 : A -> Prop) (_55641 : A) (_55642 : A) (h1 : term323 A) : term599 A _55640 _55641 _55642.
Proof. exact (EQ_MP (@lem4718490 A _55640 _55641 _55642) (@lem4718489 A _55640 _55641 _55642 h1)). Qed.
Lemma lem4718509 {A : Type'} (_55627 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term395 A n f _55627 s a.
Proof. exact (EQ_MP (@lem4718445 A n f _55627 s a) (@lem4718444 A _55627 n f s a h1)). Qed.
Lemma lem4718511 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4718513 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term332 A f m s) : term332 A f m s.
Proof. exact (h1). Qed.
Lemma lem4718539 {A : Type'} (_55642 : A) (_55641 : A) (_55640 : A -> Prop) (h1 : term323 A) : term610 A _55642 _55641 _55640.
Proof. exact (proj1 (@lem4718491 A _55640 _55641 _55642 h1)). Qed.
Lemma lem4718727 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4718728 (m : nat) (n : nat) (h1 : Peano.lt m n) : term611 m n.
Proof. exact (fun h0 : term312 m n => @lem4718727 m n h1). Qed.
Lemma lem4718730 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4718731 (m : nat) (n : nat) : (term611 m n) = (Peano.lt m n).
Proof. exact (@lem4718730 (Peano.lt m n)). Qed.
Lemma lem4718732 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem4718731 m n) (@lem4718728 m n h1)). Qed.
Lemma lem4718738 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4718739 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (_55627 : nat) (n : nat) : (term395 A n f _55627 s a) = (term613 A f s a _55627 n).
Proof. exact (@lem4718738 (term396 A f _55627 s a) (term312 _55627 n)). Qed.
Lemma lem4718745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4718746 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (_55627 : nat) (n : nat) : (term614 A n f _55627 s a) = (term615 A f s a _55627 n).
Proof. exact (MK_COMB (@lem4718745) (@lem4718739 A f s a _55627 n)). Qed.
Lemma lem4718752 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (_55627 : nat) (n : nat) : (term613 A f s a _55627 n) = (term613 A f s a _55627 n).
Proof. exact (eq_refl (term613 A f s a _55627 n)). Qed.
Lemma lem4718753 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (_55627 : nat) (n : nat) : ((term395 A n f _55627 s a) = (term613 A f s a _55627 n)) = ((term613 A f s a _55627 n) = (term613 A f s a _55627 n)).
Proof. exact (MK_COMB (@lem4718746 A f s a _55627 n) (@lem4718752 A f s a _55627 n)). Qed.
Lemma lem4718755 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4718756 (x : Prop) : (x = x) = True.
Proof. exact (@lem4718755 Prop x). Qed.
Lemma lem4718757 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (_55627 : nat) (n : nat) : ((term613 A f s a _55627 n) = (term613 A f s a _55627 n)) = True.
Proof. exact (@lem4718756 (term613 A f s a _55627 n)). Qed.
Lemma lem4718758 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (_55627 : nat) (n : nat) : ((term395 A n f _55627 s a) = (term613 A f s a _55627 n)) = True.
Proof. exact (TRANS (@lem4718753 A f s a _55627 n) (@lem4718757 A f s a _55627 n)). Qed.
Lemma lem4718759 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (_55627 : nat) (n : nat) : True = ((term395 A n f _55627 s a) = (term613 A f s a _55627 n)).
Proof. exact (SYM (@lem4718758 A f s a _55627 n)). Qed.
Lemma lem4718760 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (_55627 : nat) (n : nat) : (term395 A n f _55627 s a) = (term613 A f s a _55627 n).
Proof. exact (EQ_MP (@lem4718759 A f s a _55627 n) (@lem0)). Qed.
Lemma lem4718761 {A : Type'} (_55627 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term613 A f s a _55627 n.
Proof. exact (EQ_MP (@lem4718760 A f s a _55627 n) (@lem4718509 A _55627 n f s a h1)). Qed.
Lemma lem4718763 (b : Prop) (a : Prop) : (a \/ b) = (term616 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4718764 {A : Type'} (n : nat) (f : nat -> A) (_55627 : nat) (s : A -> Prop) (a : A) : (term613 A f s a _55627 n) = (term617 A n f _55627 s a).
Proof. exact (@lem4718763 (term312 _55627 n) (term396 A f _55627 s a)). Qed.
Lemma lem4718766 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4718767 (_55627 : nat) (n : nat) : (term618 _55627 n) = (Peano.lt _55627 n).
Proof. exact (@lem4718766 (Peano.lt _55627 n)). Qed.
Lemma lem4718768 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4718769 (_55627 : nat) (n : nat) : (term619 _55627 n) = (term298 _55627 n).
Proof. exact (MK_COMB (@lem4718768) (@lem4718767 _55627 n)). Qed.
Lemma lem4718770 {A : Type'} (f : nat -> A) (_55627 : nat) (s : A -> Prop) (a : A) : (term396 A f _55627 s a) = (term396 A f _55627 s a).
Proof. exact (eq_refl (term396 A f _55627 s a)). Qed.
Lemma lem4718771 {A : Type'} (n : nat) (f : nat -> A) (_55627 : nat) (s : A -> Prop) (a : A) : (term617 A n f _55627 s a) = (term393 A n f _55627 s a).
Proof. exact (MK_COMB (@lem4718769 _55627 n) (@lem4718770 A f _55627 s a)). Qed.
Lemma lem4718772 {A : Type'} (n : nat) (f : nat -> A) (_55627 : nat) (s : A -> Prop) (a : A) : (term613 A f s a _55627 n) = (term393 A n f _55627 s a).
Proof. exact (TRANS (@lem4718764 A n f _55627 s a) (@lem4718771 A n f _55627 s a)). Qed.
Lemma lem4718775 {A : Type'} (_55627 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term393 A n f _55627 s a.
Proof. exact (EQ_MP (@lem4718772 A n f _55627 s a) (@lem4718761 A _55627 n f s a h1)). Qed.
Lemma lem4718776 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term393 A n f m s a.
Proof. exact (@lem4718775 A m n f s a h1). Qed.
Lemma lem4718779 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (m : nat) (n : nat) (h1 : term268 A n f s a) (h2 : Peano.lt m n) : term396 A f m s a.
Proof. exact (@lem4718776 A m n f s a h1 (@lem4718732 m n h2)). Qed.
Lemma lem4718780 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (m : nat) (n : nat) (h1 : term268 A n f s a) (h2 : Peano.lt m n) : term620 A f m s a.
Proof. exact (fun h0 : term621 A f m s a => @lem4718779 A f s a m n h1 h2). Qed.
Lemma lem4718782 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4718783 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term620 A f m s a) = (term396 A f m s a).
Proof. exact (@lem4718782 (term396 A f m s a)). Qed.
Lemma lem4718784 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (m : nat) (n : nat) (h1 : term268 A n f s a) (h2 : Peano.lt m n) : term396 A f m s a.
Proof. exact (EQ_MP (@lem4718783 A f m s a) (@lem4718780 A f s a m n h1 h2)). Qed.
Lemma lem4718790 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4718791 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : (term610 A _55642 _55641 _55640) = (term622 A _55641 _55640 _55642).
Proof. exact (@lem4718790 (@IN A _55641 _55640) (term474 A _55641 _55640 _55642)). Qed.
Lemma lem4718797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4718798 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : (term623 A _55642 _55641 _55640) = (term624 A _55641 _55640 _55642).
Proof. exact (MK_COMB (@lem4718797) (@lem4718791 A _55641 _55640 _55642)). Qed.
Lemma lem4718804 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : (term622 A _55641 _55640 _55642) = (term622 A _55641 _55640 _55642).
Proof. exact (eq_refl (term622 A _55641 _55640 _55642)). Qed.
Lemma lem4718805 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : ((term610 A _55642 _55641 _55640) = (term622 A _55641 _55640 _55642)) = ((term622 A _55641 _55640 _55642) = (term622 A _55641 _55640 _55642)).
Proof. exact (MK_COMB (@lem4718798 A _55641 _55640 _55642) (@lem4718804 A _55641 _55640 _55642)). Qed.
Lemma lem4718807 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4718808 (x : Prop) : (x = x) = True.
Proof. exact (@lem4718807 Prop x). Qed.
Lemma lem4718809 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : ((term622 A _55641 _55640 _55642) = (term622 A _55641 _55640 _55642)) = True.
Proof. exact (@lem4718808 (term622 A _55641 _55640 _55642)). Qed.
Lemma lem4718810 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : ((term610 A _55642 _55641 _55640) = (term622 A _55641 _55640 _55642)) = True.
Proof. exact (TRANS (@lem4718805 A _55641 _55640 _55642) (@lem4718809 A _55641 _55640 _55642)). Qed.
Lemma lem4718811 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : True = ((term610 A _55642 _55641 _55640) = (term622 A _55641 _55640 _55642)).
Proof. exact (SYM (@lem4718810 A _55641 _55640 _55642)). Qed.
Lemma lem4718812 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : (term610 A _55642 _55641 _55640) = (term622 A _55641 _55640 _55642).
Proof. exact (EQ_MP (@lem4718811 A _55641 _55640 _55642) (@lem0)). Qed.
Lemma lem4718813 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) (h1 : term323 A) : term622 A _55641 _55640 _55642.
Proof. exact (EQ_MP (@lem4718812 A _55641 _55640 _55642) (@lem4718539 A _55642 _55641 _55640 h1)). Qed.
Lemma lem4718815 (b : Prop) (a : Prop) : (a \/ b) = (term616 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4718816 {A : Type'} (_55642 : A) (_55641 : A) (_55640 : A -> Prop) : (term622 A _55641 _55640 _55642) = (term625 A _55642 _55641 _55640).
Proof. exact (@lem4718815 (term474 A _55641 _55640 _55642) (@IN A _55641 _55640)). Qed.
Lemma lem4718818 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4718819 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : (term626 A _55641 _55640 _55642) = (term380 A _55641 _55640 _55642).
Proof. exact (@lem4718818 (term380 A _55641 _55640 _55642)). Qed.
Lemma lem4718820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4718821 {A : Type'} (_55641 : A) (_55640 : A -> Prop) (_55642 : A) : (term627 A _55641 _55640 _55642) = (term390 A _55641 _55640 _55642).
Proof. exact (MK_COMB (@lem4718820) (@lem4718819 A _55641 _55640 _55642)). Qed.
Lemma lem4718822 {A : Type'} (_55641 : A) (_55640 : A -> Prop) : (@IN A _55641 _55640) = (@IN A _55641 _55640).
Proof. exact (eq_refl (@IN A _55641 _55640)). Qed.
Lemma lem4718823 {A : Type'} (_55642 : A) (_55641 : A) (_55640 : A -> Prop) : (term625 A _55642 _55641 _55640) = (term628 A _55642 _55641 _55640).
Proof. exact (MK_COMB (@lem4718821 A _55641 _55640 _55642) (@lem4718822 A _55641 _55640)). Qed.
Lemma lem4718824 {A : Type'} (_55642 : A) (_55641 : A) (_55640 : A -> Prop) : (term622 A _55641 _55640 _55642) = (term628 A _55642 _55641 _55640).
Proof. exact (TRANS (@lem4718816 A _55642 _55641 _55640) (@lem4718823 A _55642 _55641 _55640)). Qed.
Lemma lem4718827 {A : Type'} (_55642 : A) (_55641 : A) (_55640 : A -> Prop) (h1 : term323 A) : term628 A _55642 _55641 _55640.
Proof. exact (EQ_MP (@lem4718824 A _55642 _55641 _55640) (@lem4718813 A _55641 _55640 _55642 h1)). Qed.
Lemma lem4718828 {A : Type'} (_55642 : A) (_55641 : A) (_55640 : A -> Prop) (h1 : term323 A) : term628 A _55642 _55641 _55640.
Proof. exact (@lem4718827 A _55642 _55641 _55640 h1). Qed.
Lemma lem4718829 {A : Type'} (a : A) (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term323 A) : term629 A a f m s.
Proof. exact (@lem4718828 A a (f m) s h1). Qed.
Lemma lem4718832 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) : term100 A f m s.
Proof. exact (@lem4718829 A a f m s h1 (@lem4718784 A f s a m n h2 h3)). Qed.
Lemma lem4718833 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) : term630 A f m s.
Proof. exact (fun h0 : term332 A f m s => @lem4718832 A f s a m n h1 h2 h3). Qed.
Lemma lem4718835 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4718836 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term630 A f m s) = (term100 A f m s).
Proof. exact (@lem4718835 (term100 A f m s)). Qed.
Lemma lem4718837 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) : term100 A f m s.
Proof. exact (EQ_MP (@lem4718836 A f m s) (@lem4718833 A f s a m n h1 h2 h3)). Qed.
Lemma lem4718840 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4718842 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term332 A f m s) = (term631 A f m s).
Proof. exact (@lem4718840 (term100 A f m s)). Qed.
Lemma lem4718845 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (h1 : term332 A f m s) : term631 A f m s.
Proof. exact (EQ_MP (@lem4718842 A f m s) (@lem4718513 A f m s h1)). Qed.
Lemma lem4718848 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (@lem4718845 A f m s h3 (@lem4718837 A f s a m n h1 h2 h4)). Qed.
Lemma lem4718849 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : term632.
Proof. exact (fun h0 : ~ False => @lem4718848 A a f s m n h1 h2 h3 h4). Qed.
Lemma lem4718851 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4718852 : term632 = False.
Proof. exact (@lem4718851 False). Qed.
Lemma lem4718853 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718852) (@lem4718849 A a f s m n h1 h2 h3 h4)). Qed.
Lemma lem4718854 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : (term332 A f m s) = False.
Proof. exact (prop_ext (fun h5 : term332 A f m s => @lem4718853 A a f s m n h1 h2 h3 h4) (fun h5 : False => @lem4718513 A f m s h3)). Qed.
Lemma lem4718855 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718854 A a f s m n h1 h2 h3 h4) (@lem4718513 A f m s h3)). Qed.
Lemma lem4718856 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt m n => @lem4718855 A a f s m n h1 h2 h3 h4) (fun h5 : False => @lem4718511 m n h4)). Qed.
Lemma lem4718857 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718856 A a f s m n h1 h2 h3 h4) (@lem4718511 m n h4)). Qed.
Lemma lem4718858 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : (term332 A f m s) = False.
Proof. exact (prop_ext (fun h5 : term332 A f m s => @lem4718857 A a f s m n h1 h2 h3 h4) (fun h5 : False => @lem4718153 A f m s h3)). Qed.
Lemma lem4718859 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718858 A a f s m n h1 h2 h3 h4) (@lem4718153 A f m s h3)). Qed.
Lemma lem4718860 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt m n => @lem4718859 A a f s m n h1 h2 h3 h4) (fun h5 : False => @lem4718149 m n h4)). Qed.
Lemma lem4718861 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718860 A a f s m n h1 h2 h3 h4) (@lem4718149 m n h4)). Qed.
Lemma lem4718862 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : (term332 A f m s) = False.
Proof. exact (prop_ext (fun h5 : term332 A f m s => @lem4718861 A a f s m n h1 h2 h3 h4) (fun h5 : False => @lem4718153 A f m s h3)). Qed.
Lemma lem4718863 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718862 A a f s m n h1 h2 h3 h4) (@lem4718153 A f m s h3)). Qed.
Lemma lem4718864 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt m n => @lem4718863 A a f s m n h1 h2 h3 h4) (fun h5 : False => @lem4718149 m n h4)). Qed.
Lemma lem4718865 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718864 A a f s m n h1 h2 h3 h4) (@lem4718149 m n h4)). Qed.
Lemma lem4718866 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : (term332 A f m s) = False.
Proof. exact (prop_ext (fun h5 : term332 A f m s => @lem4718865 A a f s m n h1 h2 h3 h4) (fun h5 : False => @lem4717869 A f m s h3)). Qed.
Lemma lem4718867 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718866 A a f s m n h1 h2 h3 h4) (@lem4717869 A f m s h3)). Qed.
Lemma lem4718868 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt m n => @lem4718867 A a f s m n h1 h2 h3 h4) (fun h5 : False => @lem4717859 m n h4)). Qed.
Lemma lem4718869 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718868 A a f s m n h1 h2 h3 h4) (@lem4717859 m n h4)). Qed.
Lemma lem4718870 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term267 A s a n f) (h2 : term323 A) (h3 : term268 A n f s a) (h4 : term332 A f m s) (h5 : Peano.lt m n) : False.
Proof. exact (ex_elim (@lem4716901 A s a n f h1) (fun m' : A -> nat => fun h0 : term510 A s a n f m' => @lem4718869 A a f s m n h2 h3 h4 h5)). Qed.
Lemma lem4718871 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term267 A s a n f) (h2 : term323 A) (h3 : term268 A n f s a) (h4 : term332 A f m s) (h5 : Peano.lt m n) : (term332 A f m s) = False.
Proof. exact (prop_ext (fun h6 : term332 A f m s => @lem4718870 A a f s m n h1 h2 h3 h4 h5) (fun h6 : False => @lem4716913 A f m s h4)). Qed.
Lemma lem4718872 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term267 A s a n f) (h2 : term323 A) (h3 : term268 A n f s a) (h4 : term332 A f m s) (h5 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718871 A a f s m n h1 h2 h3 h4 h5) (@lem4716913 A f m s h4)). Qed.
Lemma lem4718873 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term267 A s a n f) (h2 : term323 A) (h3 : term268 A n f s a) (h4 : term332 A f m s) (h5 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m n => @lem4718872 A a f s m n h1 h2 h3 h4 h5) (fun h6 : False => @lem4716907 m n h5)). Qed.
Lemma lem4718874 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term267 A s a n f) (h2 : term323 A) (h3 : term268 A n f s a) (h4 : term332 A f m s) (h5 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4718873 A a f s m n h1 h2 h3 h4 h5) (@lem4716907 m n h5)). Qed.
Lemma lem4718875 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term267 A s a n f) (h2 : term323 A) (h3 : term268 A n f s a) (h4 : term332 A f m s) (h5 : Peano.lt m n) : term335.
Proof. exact (fun h0 : term324 => @lem4718874 A a f s m n h1 h2 h3 h4 h5). Qed.
Lemma lem4718876 : term335 = term336.
Proof. exact (@lem69 term324). Qed.
Lemma lem4718877 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term267 A s a n f) (h2 : term323 A) (h3 : term268 A n f s a) (h4 : term332 A f m s) (h5 : Peano.lt m n) : term336.
Proof. exact (EQ_MP (@lem4718876) (@lem4718875 A a f s m n h1 h2 h3 h4 h5)). Qed.
Lemma lem4718878 {A : Type'} (a : A) (f : nat -> A) (s : A -> Prop) (m : nat) (n : nat) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term332 A f m s) (h4 : Peano.lt m n) : term339 A.
Proof. exact (fun h0 : term323 A => @lem4718877 A a f s m n h1 h0 h2 h3 h4). Qed.
Lemma lem4718879 {A : Type'} (f : nat -> A) (s : A -> Prop) (a : A) (m : nat) (n : nat) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : Peano.lt m n) : term341 A f m s.
Proof. exact (fun h0 : term332 A f m s => @lem4718878 A a f s m n h1 h2 h0 h3). Qed.
Lemma lem4718880 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term267 A s a n f) (h2 : term268 A n f s a) : term343 A n f m s.
Proof. exact (fun h0 : Peano.lt m n => @lem4718879 A f s a m n h1 h2 h0). Qed.
Lemma lem4718881 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term346 A a n f m s.
Proof. exact (fun h0 : term267 A s a n f => @lem4718880 A m n f s a h0 h1). Qed.
Lemma lem4718882 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term349 A a n f m s.
Proof. exact (fun h0 : term268 A n f s a => @lem4718881 A m n f s a h0). Qed.
Lemma lem4718883 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term351 A a n f m s.
Proof. exact (fun h0 : term252 A s a n => @lem4718882 A a n f m s). Qed.
Lemma lem4718884 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term352 A a n f m s.
Proof. exact (fun h0 : @IN A a s => @lem4718883 A a n f m s). Qed.
Lemma lem4718889 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term356 A n f m s.
Proof. exact (fun a : A => @lem4718884 A a n f m s). Qed.
Lemma lem4718894 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : term360 A f m s.
Proof. exact (fun n : nat => @lem4718889 A n f m s). Qed.
Lemma lem4718899 {A : Type'} (m : nat) (s : A -> Prop) : term364 A m s.
Proof. exact (fun f : nat -> A => @lem4718894 A f m s). Qed.
Lemma lem4718904 {A : Type'} (s : A -> Prop) : term368 A s.
Proof. exact (fun m : nat => @lem4718899 A m s). Qed.
Lemma lem4718909 {A : Type'} : term372 A.
Proof. exact (fun s : A -> Prop => @lem4718904 A s). Qed.
Lemma lem4718910 {A : Type'} : term371 A.
Proof. exact (EQ_MP (@lem4716406 A) (@lem4718909 A)). Qed.
Lemma lem4718911 {A : Type'} (s : A -> Prop) : term633 A s.
Proof. exact (@lem4718910 A s). Qed.
Lemma lem4718912 {A : Type'} (s : A -> Prop) : (term633 A s) = (term367 A s).
Proof. exact (eq_refl (term633 A s)). Qed.
Lemma lem4718913 {A : Type'} (s : A -> Prop) : term367 A s.
Proof. exact (EQ_MP (@lem4718912 A s) (@lem4718911 A s)). Qed.
Lemma lem4718914 {A : Type'} (s : A -> Prop) (m : nat) : term634 A s m.
Proof. exact (@lem4718913 A s m). Qed.
Lemma lem4718915 {A : Type'} (m : nat) (s : A -> Prop) : (term634 A s m) = (term363 A m s).
Proof. exact (eq_refl (term634 A s m)). Qed.
Lemma lem4718916 {A : Type'} (m : nat) (s : A -> Prop) : term363 A m s.
Proof. exact (EQ_MP (@lem4718915 A m s) (@lem4718914 A s m)). Qed.
Lemma lem4718917 {A : Type'} (m : nat) (s : A -> Prop) (f : nat -> A) : term635 A m s f.
Proof. exact (@lem4718916 A m s f). Qed.
Lemma lem4718918 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : (term635 A m s f) = (term359 A f m s).
Proof. exact (eq_refl (term635 A m s f)). Qed.
Lemma lem4718919 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) : term359 A f m s.
Proof. exact (EQ_MP (@lem4718918 A f m s) (@lem4718917 A m s f)). Qed.
Lemma lem4718920 {A : Type'} (f : nat -> A) (m : nat) (s : A -> Prop) (n : nat) : term636 A f m s n.
Proof. exact (@lem4718919 A f m s n). Qed.
Lemma lem4718921 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term636 A f m s n) = (term355 A n f m s).
Proof. exact (eq_refl (term636 A f m s n)). Qed.
Lemma lem4718922 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term355 A n f m s.
Proof. exact (EQ_MP (@lem4718921 A n f m s) (@lem4718920 A f m s n)). Qed.
Lemma lem4718923 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : term637 A n f m s a.
Proof. exact (@lem4718922 A n f m s a). Qed.
Lemma lem4718924 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : (term637 A n f m s a) = (term325 A a n f m s).
Proof. exact (eq_refl (term637 A n f m s a)). Qed.
Lemma lem4718925 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term325 A a n f m s.
Proof. exact (EQ_MP (@lem4718924 A a n f m s) (@lem4718923 A n f m s a)). Qed.
Lemma lem4718927 {A : Type'} (a : A) (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) : term325 A a n f m s.
Proof. exact (@lem4716031 A a n f m s (@lem4718925 A a n f m s)). Qed.
Lemma lem4718928 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term350 A a n f m s.
Proof. exact (@lem4718927 A a n f m s (@lem4715763 A a s h1)). Qed.
Lemma lem4718929 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term252 A s a n) (h2 : @IN A a s) : term348 A a n f m s.
Proof. exact (@lem4718928 A n f m a s h2 (@lem4715822 A s a n h1)). Qed.
Lemma lem4718930 {A : Type'} (m : nat) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term252 A s a n) (h3 : @IN A a s) : term345 A a n f m s.
Proof. exact (@lem4718929 A f m n a s h2 h3 (@lem4715928 A n f s a h1)). Qed.
Lemma lem4718931 {A : Type'} (m : nat) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term342 A n f m s.
Proof. exact (@lem4718930 A m f n a s h2 h3 h4 (@lem4715927 A s a n f h1)). Qed.
Lemma lem4718932 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term340 A n f m s.
Proof. exact (@lem4718931 A m f n a s h1 h2 h4 h5 (@lem4715975 m n h3)). Qed.
Lemma lem4718933 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term322 A n f m s) (h4 : Peano.lt m n) (h5 : term252 A s a n) (h6 : @IN A a s) : term338 A.
Proof. exact (@lem4718932 A f m n a s h1 h2 h4 h5 h6 (@lem4716011 A n f m s h3)). Qed.
Lemma lem4718934 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term322 A n f m s) (h4 : Peano.lt m n) (h5 : term252 A s a n) (h6 : @IN A a s) : term335.
Proof. exact (@lem4718933 A f m n a s h1 h2 h3 h4 h5 h6 (@lem4716012 A)). Qed.
Lemma lem4718935 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term322 A n f m s) (h4 : Peano.lt m n) (h5 : term252 A s a n) (h6 : @IN A a s) : False.
Proof. exact (@lem4718934 A f m n a s h1 h2 h3 h4 h5 h6 (@lem4716015)). Qed.
Lemma lem4718936 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term322 A n f m s) (h4 : Peano.lt m n) (h5 : term252 A s a n) (h6 : @IN A a s) : (term322 A n f m s) = False.
Proof. exact (prop_ext (fun h7 : term322 A n f m s => @lem4718935 A f m n a s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4716011 A n f m s h3)). Qed.
Lemma lem4718937 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term322 A n f m s) (h4 : Peano.lt m n) (h5 : term252 A s a n) (h6 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem4718936 A f m n a s h1 h2 h3 h4 h5 h6) (@lem4716011 A n f m s h3)). Qed.
Lemma lem4718938 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term321 A n f m s.
Proof. exact (fun h0 : term322 A n f m s => @lem4718937 A f m n a s h1 h2 h0 h3 h4 h5). Qed.
Lemma lem4718939 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term309 A n f m s.
Proof. exact (EQ_MP (@lem4716010 A n f m s) (@lem4718938 A f m n a s h1 h2 h3 h4 h5)). Qed.
Lemma lem4718941 (p : Prop) : p = (term320 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4718942 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term317 A m n a s) = (term638 A m n a s).
Proof. exact (@lem4718941 (term317 A m n a s)). Qed.
Lemma lem4718943 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term638 A m n a s) = (term317 A m n a s).
Proof. exact (SYM (@lem4718942 A m n a s)). Qed.
Lemma lem4718944 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term639 A m n a s) : term639 A m n a s.
Proof. exact (h1). Qed.
Lemma lem4718945 {A : Type'} : term323 A.
Proof. exact (@lem3205803 A). Qed.
Lemma lem4718948 : term324.
Proof. exact (@lem3205803 nat). Qed.
Lemma lem4718951 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term640 A f m n a s) : term640 A f m n a s.
Proof. exact (h1). Qed.
Lemma lem4718952 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : term641 A f m n a s.
Proof. exact (fun h0 : term640 A f m n a s => @lem4718951 A f m n a s h0). Qed.
Lemma lem4718953 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term641 A f m n a s) : term641 A f m n a s.
Proof. exact (h1). Qed.
Lemma lem4718954 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term640 A f m n a s) : term640 A f m n a s.
Proof. exact (h1). Qed.
Lemma lem4718955 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term641 A f m n a s) (h2 : term640 A f m n a s) : term640 A f m n a s.
Proof. exact (@lem4718953 A f m n a s h1 (@lem4718954 A f m n a s h2)). Qed.
Lemma lem4718956 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term640 A f m n a s) : term642 A f m n a s.
Proof. exact (fun h0 : term641 A f m n a s => @lem4718955 A f m n a s h0 h1). Qed.
Lemma lem4718957 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term641 A f m n a s) : term641 A f m n a s.
Proof. exact (h1). Qed.
Lemma lem4718958 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term641 A f m n a s) (h2 : term640 A f m n a s) : term640 A f m n a s.
Proof. exact (@lem4718956 A f m n a s h2 (@lem4718957 A f m n a s h1)). Qed.
Lemma lem4718959 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term641 A f m n a s) : term641 A f m n a s.
Proof. exact (fun h0 : term640 A f m n a s => @lem4718958 A f m n a s h1 h0). Qed.
Lemma lem4718960 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : term643 A f m n a s.
Proof. exact (fun h0 : term641 A f m n a s => @lem4718959 A f m n a s h0). Qed.
Lemma lem4718963 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : term641 A f m n a s.
Proof. exact (@lem4718960 A f m n a s (@lem4718952 A f m n a s)). Qed.
Lemma lem4718964 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : term641 A f m n a s.
Proof. exact (@lem4718963 A f m n a s). Qed.
Lemma lem4719014 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem16485 t)). Qed.
Lemma lem4719015 (m : nat) (n : nat) : (term644 m n) = (m = n).
Proof. exact (@lem4719014 (m = n)). Qed.
Lemma lem4719016 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4719017 (m : nat) (n : nat) : (term645 m n) = (term646 m n).
Proof. exact (MK_COMB (@lem4719016) (@lem4719015 m n)). Qed.
Lemma lem4719018 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = (@IN A a s).
Proof. exact (eq_refl (@IN A a s)). Qed.
Lemma lem4719019 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term317 A m n a s) = (term647 A m n a s).
Proof. exact (MK_COMB (@lem4719017 m n) (@lem4719018 A a s)). Qed.
Lemma lem4719022 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4719023 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term639 A m n a s) = (term648 A m n a s).
Proof. exact (MK_COMB (@lem4719022) (@lem4719019 A m n a s)). Qed.
Lemma lem4719024 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4719025 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term649 A m n a s) = (term650 A m n a s).
Proof. exact (MK_COMB (@lem4719024) (@lem4719023 A m n a s)). Qed.
Lemma lem4719043 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4719044 : term335 = term336.
Proof. exact (@lem4719043 term324). Qed.
Lemma lem4719059 {A : Type'} : (term337 A) = (term337 A).
Proof. exact (eq_refl (term337 A)). Qed.
Lemma lem4719060 {A : Type'} : (term338 A) = (term339 A).
Proof. exact (MK_COMB (@lem4719059 A) (@lem4719044)). Qed.
Lemma lem4719063 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term651 A m n a s) = (term652 A m n a s).
Proof. exact (MK_COMB (@lem4719025 A m n a s) (@lem4719060 A)). Qed.
Lemma lem4719066 (m : nat) (n : nat) : (term294 m n) = (term294 m n).
Proof. exact (eq_refl (term294 m n)). Qed.
Lemma lem4719067 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term653 A m n a s) = (term654 A m n a s).
Proof. exact (MK_COMB (@lem4719066 m n) (@lem4719063 A m n a s)). Qed.
Lemma lem4719070 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term344 A s a n f) = (term344 A s a n f).
Proof. exact (eq_refl (term344 A s a n f)). Qed.
Lemma lem4719071 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term655 A f m n a s) = (term656 A f m n a s).
Proof. exact (MK_COMB (@lem4719070 A s a n f) (@lem4719067 A m n a s)). Qed.
Lemma lem4719074 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term347 A n f s a) = (term347 A n f s a).
Proof. exact (eq_refl (term347 A n f s a)). Qed.
Lemma lem4719075 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term657 A f m n a s) = (term658 A f m n a s).
Proof. exact (MK_COMB (@lem4719074 A n f s a) (@lem4719071 A f m n a s)). Qed.
Lemma lem4719078 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term255 A s a n) = (term255 A s a n).
Proof. exact (eq_refl (term255 A s a n)). Qed.
Lemma lem4719079 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term659 A f m n a s) = (term660 A f m n a s).
Proof. exact (MK_COMB (@lem4719078 A s a n) (@lem4719075 A f m n a s)). Qed.
Lemma lem4719082 {A : Type'} (a : A) (s : A -> Prop) : (term251 A a s) = (term251 A a s).
Proof. exact (eq_refl (term251 A a s)). Qed.
Lemma lem4719083 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term640 A f m n a s) = (term661 A f m n a s).
Proof. exact (MK_COMB (@lem4719082 A a s) (@lem4719079 A f m n a s)). Qed.
Lemma lem4719086 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term662 A m n a s) = (term663 A m n a s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4719083 A f m n a s)). Qed.
Lemma lem4719087 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4719088 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term664 A m n a s) = (term665 A m n a s).
Proof. exact (MK_COMB (@lem4719087 A) (@lem4719086 A m n a s)). Qed.
Lemma lem4719093 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : (term666 A n a s) = (term667 A n a s).
Proof. exact (fun_ext (fun m : nat => @lem4719088 A m n a s)). Qed.
Lemma lem4719094 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719095 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : (term668 A n a s) = (term669 A n a s).
Proof. exact (MK_COMB (@lem4719094) (@lem4719093 A n a s)). Qed.
Lemma lem4719100 {A : Type'} (a : A) (s : A -> Prop) : (term670 A a s) = (term671 A a s).
Proof. exact (fun_ext (fun n : nat => @lem4719095 A n a s)). Qed.
Lemma lem4719101 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719102 {A : Type'} (a : A) (s : A -> Prop) : (term672 A a s) = (term673 A a s).
Proof. exact (MK_COMB (@lem4719101) (@lem4719100 A a s)). Qed.
Lemma lem4719107 {A : Type'} (s : A -> Prop) : (term674 A s) = (term675 A s).
Proof. exact (fun_ext (fun a : A => @lem4719102 A a s)). Qed.
Lemma lem4719108 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719109 {A : Type'} (s : A -> Prop) : (term676 A s) = (term677 A s).
Proof. exact (MK_COMB (@lem4719108 A) (@lem4719107 A s)). Qed.
Lemma lem4719114 {A : Type'} : (term678 A) = (term679 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4719109 A s)). Qed.
Lemma lem4719115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4719124 {A : Type'} : (term680 A) = (term681 A).
Proof. exact (MK_COMB (@lem4719115 A) (@lem4719114 A)). Qed.
Lemma lem4719135 (s : nat -> Prop) (x : nat) (y : nat) : ((term373 x s y) = (term374 s x y)) = ((term373 x s y) = (term374 s x y)).
Proof. exact (eq_refl ((term373 x s y) = (term374 s x y))). Qed.
Lemma lem4719136 (s : nat -> Prop) (x : nat) : (term375 s x) = (term375 s x).
Proof. exact (fun_ext (fun y : nat => @lem4719135 s x y)). Qed.
Lemma lem4719137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719138 (s : nat -> Prop) (x : nat) : (term376 s x) = (term376 s x).
Proof. exact (MK_COMB (@lem4719137) (@lem4719136 s x)). Qed.
Lemma lem4719139 (s : nat -> Prop) : (term377 s) = (term377 s).
Proof. exact (fun_ext (fun x : nat => @lem4719138 s x)). Qed.
Lemma lem4719140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719141 (s : nat -> Prop) : (term378 s) = (term378 s).
Proof. exact (MK_COMB (@lem4719140) (@lem4719139 s)). Qed.
Lemma lem4719142 : term379 = term379.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4719141 s)). Qed.
Lemma lem4719143 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4719144 : term324 = term324.
Proof. exact (MK_COMB (@lem4719143) (@lem4719142)). Qed.
Lemma lem4719145 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4719146 : term336 = term336.
Proof. exact (MK_COMB (@lem4719145) (@lem4719144)). Qed.
Lemma lem4719157 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term380 A x s y) = (term381 A s x y)) = ((term380 A x s y) = (term381 A s x y)).
Proof. exact (eq_refl ((term380 A x s y) = (term381 A s x y))). Qed.
Lemma lem4719158 {A : Type'} (s : A -> Prop) (x : A) : (term382 A s x) = (term382 A s x).
Proof. exact (fun_ext (fun y : A => @lem4719157 A s x y)). Qed.
Lemma lem4719159 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719160 {A : Type'} (s : A -> Prop) (x : A) : (term383 A s x) = (term383 A s x).
Proof. exact (MK_COMB (@lem4719159 A) (@lem4719158 A s x)). Qed.
Lemma lem4719161 {A : Type'} (s : A -> Prop) : (term384 A s) = (term384 A s).
Proof. exact (fun_ext (fun x : A => @lem4719160 A s x)). Qed.
Lemma lem4719162 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719163 {A : Type'} (s : A -> Prop) : (term385 A s) = (term385 A s).
Proof. exact (MK_COMB (@lem4719162 A) (@lem4719161 A s)). Qed.
Lemma lem4719164 {A : Type'} : (term386 A) = (term386 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4719163 A s)). Qed.
Lemma lem4719165 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4719166 {A : Type'} : (term323 A) = (term323 A).
Proof. exact (MK_COMB (@lem4719165 A) (@lem4719164 A)). Qed.
Lemma lem4719167 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4719168 {A : Type'} : (term337 A) = (term337 A).
Proof. exact (MK_COMB (@lem4719167) (@lem4719166 A)). Qed.
Lemma lem4719169 {A : Type'} : (term339 A) = (term339 A).
Proof. exact (MK_COMB (@lem4719168 A) (@lem4719146)). Qed.
Lemma lem4719178 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term650 A m n a s) = (term650 A m n a s).
Proof. exact (eq_refl (term650 A m n a s)). Qed.
Lemma lem4719179 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term652 A m n a s) = (term652 A m n a s).
Proof. exact (MK_COMB (@lem4719178 A m n a s) (@lem4719169 A)). Qed.
Lemma lem4719184 (m : nat) (n : nat) : (term294 m n) = (term294 m n).
Proof. exact (eq_refl (term294 m n)). Qed.
Lemma lem4719185 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term654 A m n a s) = (term654 A m n a s).
Proof. exact (MK_COMB (@lem4719184 m n) (@lem4719179 A m n a s)). Qed.
Lemma lem4719190 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term387 A n f m x) = (term387 A n f m x).
Proof. exact (eq_refl (term387 A n f m x)). Qed.
Lemma lem4719191 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term388 A n f x) = (term388 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4719190 A n f m x)). Qed.
Lemma lem4719192 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4719193 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term389 A n f x).
Proof. exact (MK_COMB (@lem4719192) (@lem4719191 A n f x)). Qed.
Lemma lem4719196 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term390 A x s a) = (term390 A x s a).
Proof. exact (eq_refl (term390 A x s a)). Qed.
Lemma lem4719197 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term391 A s a n f x) = (term391 A s a n f x).
Proof. exact (MK_COMB (@lem4719196 A x s a) (@lem4719193 A n f x)). Qed.
Lemma lem4719198 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term392 A s a n f) = (term392 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4719197 A s a n f x)). Qed.
Lemma lem4719199 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719200 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term267 A s a n f) = (term267 A s a n f).
Proof. exact (MK_COMB (@lem4719199 A) (@lem4719198 A s a n f)). Qed.
Lemma lem4719201 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4719202 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term344 A s a n f) = (term344 A s a n f).
Proof. exact (MK_COMB (@lem4719201) (@lem4719200 A s a n f)). Qed.
Lemma lem4719203 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term656 A f m n a s) = (term656 A f m n a s).
Proof. exact (MK_COMB (@lem4719202 A s a n f) (@lem4719185 A m n a s)). Qed.
Lemma lem4719208 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term393 A n f m s a) = (term393 A n f m s a).
Proof. exact (eq_refl (term393 A n f m s a)). Qed.
Lemma lem4719209 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term394 A n f s a) = (term394 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4719208 A n f m s a)). Qed.
Lemma lem4719210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719211 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term268 A n f s a) = (term268 A n f s a).
Proof. exact (MK_COMB (@lem4719210) (@lem4719209 A n f s a)). Qed.
Lemma lem4719212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4719213 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term347 A n f s a) = (term347 A n f s a).
Proof. exact (MK_COMB (@lem4719212) (@lem4719211 A n f s a)). Qed.
Lemma lem4719214 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term658 A f m n a s) = (term658 A f m n a s).
Proof. exact (MK_COMB (@lem4719213 A n f s a) (@lem4719203 A f m n a s)). Qed.
Lemma lem4719217 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term255 A s a n) = (term255 A s a n).
Proof. exact (eq_refl (term255 A s a n)). Qed.
Lemma lem4719218 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term660 A f m n a s) = (term660 A f m n a s).
Proof. exact (MK_COMB (@lem4719217 A s a n) (@lem4719214 A f m n a s)). Qed.
Lemma lem4719221 {A : Type'} (a : A) (s : A -> Prop) : (term251 A a s) = (term251 A a s).
Proof. exact (eq_refl (term251 A a s)). Qed.
Lemma lem4719222 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term661 A f m n a s) = (term661 A f m n a s).
Proof. exact (MK_COMB (@lem4719221 A a s) (@lem4719218 A f m n a s)). Qed.
Lemma lem4719223 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term663 A m n a s) = (term663 A m n a s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4719222 A f m n a s)). Qed.
Lemma lem4719224 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4719225 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term665 A m n a s) = (term665 A m n a s).
Proof. exact (MK_COMB (@lem4719224 A) (@lem4719223 A m n a s)). Qed.
Lemma lem4719226 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : (term667 A n a s) = (term667 A n a s).
Proof. exact (fun_ext (fun m : nat => @lem4719225 A m n a s)). Qed.
Lemma lem4719227 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719228 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : (term669 A n a s) = (term669 A n a s).
Proof. exact (MK_COMB (@lem4719227) (@lem4719226 A n a s)). Qed.
Lemma lem4719229 {A : Type'} (a : A) (s : A -> Prop) : (term671 A a s) = (term671 A a s).
Proof. exact (fun_ext (fun n : nat => @lem4719228 A n a s)). Qed.
Lemma lem4719230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719231 {A : Type'} (a : A) (s : A -> Prop) : (term673 A a s) = (term673 A a s).
Proof. exact (MK_COMB (@lem4719230) (@lem4719229 A a s)). Qed.
Lemma lem4719232 {A : Type'} (s : A -> Prop) : (term675 A s) = (term675 A s).
Proof. exact (fun_ext (fun a : A => @lem4719231 A a s)). Qed.
Lemma lem4719233 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719234 {A : Type'} (s : A -> Prop) : (term677 A s) = (term677 A s).
Proof. exact (MK_COMB (@lem4719233 A) (@lem4719232 A s)). Qed.
Lemma lem4719235 {A : Type'} : (term679 A) = (term679 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4719234 A s)). Qed.
Lemma lem4719236 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4719237 {A : Type'} : (term681 A) = (term681 A).
Proof. exact (MK_COMB (@lem4719236 A) (@lem4719235 A)). Qed.
Lemma lem4719344 {A : Type'} : (term680 A) = (term681 A).
Proof. exact (TRANS (@lem4719124 A) (@lem4719237 A)). Qed.
Lemma lem4719345 {A : Type'} : (term681 A) = (term680 A).
Proof. exact (SYM (@lem4719344 A)). Qed.
Lemma lem4719349 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term267 A s a n f) : term267 A s a n f.
Proof. exact (h1). Qed.
Lemma lem4719351 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) : term648 A m n a s.
Proof. exact (h1). Qed.
Lemma lem4719359 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem4719438 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term399 A n f m x) = (term400 A n f m x).
Proof. exact (@lem17045 (Peano.lt m n) ((f m) = x)). Qed.
Lemma lem4719443 (m' : nat) (m : nat) : (m' = m) = (m' = m).
Proof. exact (eq_refl (m' = m)). Qed.
Lemma lem4719444 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4719445 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term401 A n f x m') = (term387 A n f m' x).
Proof. exact (eq_refl (term401 A n f x m')). Qed.
Lemma lem4719446 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term399 A n f m' x) = (term400 A n f m' x).
Proof. exact (@lem4719438 A n f m' x). Qed.
Lemma lem4719447 (P : nat -> Prop) : (@ex1 nat P) = (term402 P).
Proof. exact (@lem18897 nat P). Qed.
Lemma lem4719448 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term403 A n f x).
Proof. exact (@lem4719447 (term388 A n f x)). Qed.
Lemma lem4719449 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4719450 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term404 A n f x m') = (term399 A n f m' x).
Proof. exact (MK_COMB (@lem4719449) (@lem4719445 A n f m' x)). Qed.
Lemma lem4719451 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term404 A n f x m') = (term400 A n f m' x).
Proof. exact (TRANS (@lem4719450 A n f m' x) (@lem4719446 A n f m' x)). Qed.
Lemma lem4719452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4719453 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term405 A n f x m') = (term406 A n f m' x).
Proof. exact (MK_COMB (@lem4719452) (@lem4719451 A n f m' x)). Qed.
Lemma lem4719454 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term407 A n f x m' m) = (term408 A n f x m' m).
Proof. exact (MK_COMB (@lem4719453 A n f m' x) (@lem4719443 m' m)). Qed.
Lemma lem4719455 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4719456 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term404 A n f x m) = (term399 A n f m x).
Proof. exact (MK_COMB (@lem4719455) (@lem4719444 A n f m x)). Qed.
Lemma lem4719457 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term404 A n f x m) = (term400 A n f m x).
Proof. exact (TRANS (@lem4719456 A n f m x) (@lem4719438 A n f m x)). Qed.
Lemma lem4719458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4719459 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term405 A n f x m) = (term406 A n f m x).
Proof. exact (MK_COMB (@lem4719458) (@lem4719457 A n f m x)). Qed.
Lemma lem4719460 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term409 A n f x m' m) = (term410 A n f x m' m).
Proof. exact (MK_COMB (@lem4719459 A n f m x) (@lem4719454 A n f x m' m)). Qed.
Lemma lem4719461 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term411 A n f x m) = (term412 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4719460 A n f x m' m)). Qed.
Lemma lem4719462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719463 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term413 A n f x m) = (term414 A n f x m).
Proof. exact (MK_COMB (@lem4719462) (@lem4719461 A n f x m)). Qed.
Lemma lem4719464 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term415 A n f x) = (term416 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4719463 A n f x m)). Qed.
Lemma lem4719465 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719466 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term417 A n f x) = (term418 A n f x).
Proof. exact (MK_COMB (@lem4719465) (@lem4719464 A n f x)). Qed.
Lemma lem4719467 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4719468 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term419 A n f x) = (term388 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4719467 A n f m x)). Qed.
Lemma lem4719469 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4719470 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term420 A n f x) = (term421 A n f x).
Proof. exact (MK_COMB (@lem4719469) (@lem4719468 A n f x)). Qed.
Lemma lem4719471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4719472 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term422 A n f x) = (term423 A n f x).
Proof. exact (MK_COMB (@lem4719471) (@lem4719470 A n f x)). Qed.
Lemma lem4719473 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term403 A n f x) = (term424 A n f x).
Proof. exact (MK_COMB (@lem4719472 A n f x) (@lem4719466 A n f x)). Qed.
Lemma lem4719474 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term424 A n f x).
Proof. exact (TRANS (@lem4719448 A n f x) (@lem4719473 A n f x)). Qed.
Lemma lem4719476 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4719477 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term426 A s a n f x) = (term427 A s a n f x).
Proof. exact (MK_COMB (@lem4719476 A x s a) (@lem4719474 A n f x)). Qed.
Lemma lem4719478 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term391 A s a n f x) = (term426 A s a n f x).
Proof. exact (@lem17265 (term380 A x s a) (term389 A n f x)). Qed.
Lemma lem4719479 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term391 A s a n f x) = (term427 A s a n f x).
Proof. exact (TRANS (@lem4719478 A s a n f x) (@lem4719477 A s a n f x)). Qed.
Lemma lem4719480 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term392 A s a n f) = (term428 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4719479 A s a n f x)). Qed.
Lemma lem4719481 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719482 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term267 A s a n f) = (term429 A s a n f).
Proof. exact (MK_COMB (@lem4719481 A) (@lem4719480 A s a n f)). Qed.
Lemma lem4719584 {A : Type'} (P : Prop) (Q : A -> Prop) : (term430 A P Q) = (term431 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem4719585 (P : Prop) (Q : nat -> Prop) : (term432 P Q) = (term433 P Q).
Proof. exact (@lem4719584 nat P Q). Qed.
Lemma lem4719586 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term434 A n f x m) = (term435 A n f x m).
Proof. exact (@lem4719585 (term400 A n f m x) (term436 A n f x m)). Qed.
Lemma lem4719587 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term437 A n f x m m') = (term408 A n f x m' m).
Proof. exact (eq_refl (term437 A n f x m m')). Qed.
Lemma lem4719588 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term406 A n f m x) = (term406 A n f m x).
Proof. exact (eq_refl (term406 A n f m x)). Qed.
Lemma lem4719589 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term438 A n f x m m') = (term410 A n f x m' m).
Proof. exact (MK_COMB (@lem4719588 A n f m x) (@lem4719587 A n f x m' m)). Qed.
Lemma lem4719590 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term439 A n f x m) = (term412 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4719589 A n f x m' m)). Qed.
Lemma lem4719591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719592 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term434 A n f x m) = (term414 A n f x m).
Proof. exact (MK_COMB (@lem4719591) (@lem4719590 A n f x m)). Qed.
Lemma lem4719593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4719594 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term440 A n f x m) = (term441 A n f x m).
Proof. exact (MK_COMB (@lem4719593) (@lem4719592 A n f x m)). Qed.
Lemma lem4719595 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term437 A n f x m m') = (term408 A n f x m' m).
Proof. exact (eq_refl (term437 A n f x m m')). Qed.
Lemma lem4719596 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term442 A n f x m) = (term436 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4719595 A n f x m' m)). Qed.
Lemma lem4719597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719598 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term443 A n f x m) = (term444 A n f x m).
Proof. exact (MK_COMB (@lem4719597) (@lem4719596 A n f x m)). Qed.
Lemma lem4719599 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term406 A n f m x) = (term406 A n f m x).
Proof. exact (eq_refl (term406 A n f m x)). Qed.
Lemma lem4719600 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term435 A n f x m) = (term445 A n f x m).
Proof. exact (MK_COMB (@lem4719599 A n f m x) (@lem4719598 A n f x m)). Qed.
Lemma lem4719601 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : ((term434 A n f x m) = (term435 A n f x m)) = ((term414 A n f x m) = (term445 A n f x m)).
Proof. exact (MK_COMB (@lem4719594 A n f x m) (@lem4719600 A n f x m)). Qed.
Lemma lem4719602 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term414 A n f x m) = (term445 A n f x m).
Proof. exact (EQ_MP (@lem4719601 A n f x m) (@lem4719586 A n f x m)). Qed.
Lemma lem4719651 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term416 A n f x) = (term446 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4719602 A n f x m)). Qed.
Lemma lem4719652 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4719653 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term418 A n f x) = (term447 A n f x).
Proof. exact (MK_COMB (@lem4719652) (@lem4719651 A n f x)). Qed.
Lemma lem4719702 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term423 A n f x) = (term423 A n f x).
Proof. exact (eq_refl (term423 A n f x)). Qed.
Lemma lem4719703 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term424 A n f x) = (term448 A n f x).
Proof. exact (MK_COMB (@lem4719702 A n f x) (@lem4719653 A n f x)). Qed.
Lemma lem4719704 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4719705 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term427 A s a n f x) = (term449 A s a n f x).
Proof. exact (MK_COMB (@lem4719704 A x s a) (@lem4719703 A n f x)). Qed.
Lemma lem4719706 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term428 A s a n f) = (term450 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4719705 A s a n f x)). Qed.
Lemma lem4719707 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719708 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term429 A s a n f) = (term451 A s a n f).
Proof. exact (MK_COMB (@lem4719707 A) (@lem4719706 A s a n f)). Qed.
Lemma lem4719758 {A : Type'} (P : A -> Prop) (Q : Prop) : (term452 A P Q) = (term453 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4719759 (P : nat -> Prop) (Q : Prop) : (term454 P Q) = (term455 P Q).
Proof. exact (@lem4719758 nat P Q). Qed.
Lemma lem4719760 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term456 A n f x) = (term457 A n f x).
Proof. exact (@lem4719759 (term388 A n f x) (term447 A n f x)). Qed.
Lemma lem4719761 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4719762 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term419 A n f x) = (term388 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4719761 A n f m x)). Qed.
Lemma lem4719763 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4719764 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term420 A n f x) = (term421 A n f x).
Proof. exact (MK_COMB (@lem4719763) (@lem4719762 A n f x)). Qed.
Lemma lem4719765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4719766 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term422 A n f x) = (term423 A n f x).
Proof. exact (MK_COMB (@lem4719765) (@lem4719764 A n f x)). Qed.
Lemma lem4719767 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term447 A n f x) = (term447 A n f x).
Proof. exact (eq_refl (term447 A n f x)). Qed.
Lemma lem4719768 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term456 A n f x) = (term448 A n f x).
Proof. exact (MK_COMB (@lem4719766 A n f x) (@lem4719767 A n f x)). Qed.
Lemma lem4719769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4719770 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term458 A n f x) = (term459 A n f x).
Proof. exact (MK_COMB (@lem4719769) (@lem4719768 A n f x)). Qed.
Lemma lem4719771 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4719772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4719773 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term460 A n f x m) = (term461 A n f m x).
Proof. exact (MK_COMB (@lem4719772) (@lem4719771 A n f m x)). Qed.
Lemma lem4719774 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term447 A n f x) = (term447 A n f x).
Proof. exact (eq_refl (term447 A n f x)). Qed.
Lemma lem4719775 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term462 A m n f x) = (term463 A m n f x).
Proof. exact (MK_COMB (@lem4719773 A n f m x) (@lem4719774 A n f x)). Qed.
Lemma lem4719776 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term464 A n f x) = (term465 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4719775 A m n f x)). Qed.
Lemma lem4719777 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4719778 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term457 A n f x) = (term466 A n f x).
Proof. exact (MK_COMB (@lem4719777) (@lem4719776 A n f x)). Qed.
Lemma lem4719779 {A : Type'} (n : nat) (f : nat -> A) (x : A) : ((term456 A n f x) = (term457 A n f x)) = ((term448 A n f x) = (term466 A n f x)).
Proof. exact (MK_COMB (@lem4719770 A n f x) (@lem4719778 A n f x)). Qed.
Lemma lem4719780 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term448 A n f x) = (term466 A n f x).
Proof. exact (EQ_MP (@lem4719779 A n f x) (@lem4719760 A n f x)). Qed.
Lemma lem4719781 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4719782 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term449 A s a n f x) = (term467 A s a n f x).
Proof. exact (MK_COMB (@lem4719781 A x s a) (@lem4719780 A n f x)). Qed.
Lemma lem4719784 {A : Type'} (P : Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4719785 (P : Prop) (Q : nat -> Prop) : (term470 P Q) = (term471 P Q).
Proof. exact (@lem4719784 nat P Q). Qed.
Lemma lem4719786 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term472 A s a n f x) = (term473 A s a n f x).
Proof. exact (@lem4719785 (term474 A x s a) (term465 A n f x)). Qed.
Lemma lem4719787 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term475 A n f x m) = (term463 A m n f x).
Proof. exact (eq_refl (term475 A n f x m)). Qed.
Lemma lem4719788 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term476 A n f x) = (term465 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4719787 A m n f x)). Qed.
Lemma lem4719789 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4719790 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term477 A n f x) = (term466 A n f x).
Proof. exact (MK_COMB (@lem4719789) (@lem4719788 A n f x)). Qed.
Lemma lem4719791 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4719792 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term472 A s a n f x) = (term467 A s a n f x).
Proof. exact (MK_COMB (@lem4719791 A x s a) (@lem4719790 A n f x)). Qed.
Lemma lem4719793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4719794 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term478 A s a n f x) = (term479 A s a n f x).
Proof. exact (MK_COMB (@lem4719793) (@lem4719792 A s a n f x)). Qed.
Lemma lem4719795 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term475 A n f x m) = (term463 A m n f x).
Proof. exact (eq_refl (term475 A n f x m)). Qed.
Lemma lem4719796 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term425 A x s a) = (term425 A x s a).
Proof. exact (eq_refl (term425 A x s a)). Qed.
Lemma lem4719797 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (n : nat) (f : nat -> A) (x : A) : (term480 A s a n f x m) = (term481 A s a m n f x).
Proof. exact (MK_COMB (@lem4719796 A x s a) (@lem4719795 A m n f x)). Qed.
Lemma lem4719798 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term482 A s a n f x) = (term483 A s a n f x).
Proof. exact (fun_ext (fun m : nat => @lem4719797 A s a m n f x)). Qed.
Lemma lem4719799 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4719800 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term473 A s a n f x) = (term484 A s a n f x).
Proof. exact (MK_COMB (@lem4719799) (@lem4719798 A s a n f x)). Qed.
Lemma lem4719801 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : ((term472 A s a n f x) = (term473 A s a n f x)) = ((term467 A s a n f x) = (term484 A s a n f x)).
Proof. exact (MK_COMB (@lem4719794 A s a n f x) (@lem4719800 A s a n f x)). Qed.
Lemma lem4719802 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term467 A s a n f x) = (term484 A s a n f x).
Proof. exact (EQ_MP (@lem4719801 A s a n f x) (@lem4719786 A s a n f x)). Qed.
Lemma lem4719803 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term449 A s a n f x) = (term484 A s a n f x).
Proof. exact (TRANS (@lem4719782 A s a n f x) (@lem4719802 A s a n f x)). Qed.
Lemma lem4719804 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term450 A s a n f) = (term485 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4719803 A s a n f x)). Qed.
Lemma lem4719805 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719806 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term451 A s a n f) = (term486 A s a n f).
Proof. exact (MK_COMB (@lem4719805 A) (@lem4719804 A s a n f)). Qed.
Lemma lem4719808 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4719809 {A : Type'} (P : type1424 A) : (term489 A P) = (term490 A P).
Proof. exact (@lem4719808 A nat P). Qed.
Lemma lem4719810 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term491 A s a n f) = (term492 A s a n f).
Proof. exact (@lem4719809 A (term493 A s a n f)). Qed.
Lemma lem4719811 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term494 A s a n f x) = (term483 A s a n f x).
Proof. exact (eq_refl (term494 A s a n f x)). Qed.
Lemma lem4719812 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4719813 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) (m : nat) : (term495 A s a n f x m) = (term496 A s a n f x m).
Proof. exact (MK_COMB (@lem4719811 A s a n f x) (@lem4719812 m)). Qed.
Lemma lem4719814 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (n : nat) (f : nat -> A) (x : A) : (term496 A s a n f x m) = (term481 A s a m n f x).
Proof. exact (eq_refl (term496 A s a n f x m)). Qed.
Lemma lem4719815 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (n : nat) (f : nat -> A) (x : A) : (term495 A s a n f x m) = (term481 A s a m n f x).
Proof. exact (TRANS (@lem4719813 A s a n f x m) (@lem4719814 A s a m n f x)). Qed.
Lemma lem4719816 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term497 A s a n f x) = (term483 A s a n f x).
Proof. exact (fun_ext (fun m : nat => @lem4719815 A s a m n f x)). Qed.
Lemma lem4719817 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4719818 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term498 A s a n f x) = (term484 A s a n f x).
Proof. exact (MK_COMB (@lem4719817) (@lem4719816 A s a n f x)). Qed.
Lemma lem4719819 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term499 A s a n f) = (term485 A s a n f).
Proof. exact (fun_ext (fun x : A => @lem4719818 A s a n f x)). Qed.
Lemma lem4719820 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719821 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term491 A s a n f) = (term486 A s a n f).
Proof. exact (MK_COMB (@lem4719820 A) (@lem4719819 A s a n f)). Qed.
Lemma lem4719822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4719823 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term500 A s a n f) = (term501 A s a n f).
Proof. exact (MK_COMB (@lem4719822) (@lem4719821 A s a n f)). Qed.
Lemma lem4719824 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term494 A s a n f x) = (term483 A s a n f x).
Proof. exact (eq_refl (term494 A s a n f x)). Qed.
Lemma lem4719825 {A : Type'} (m : A -> nat) (x : A) : (m x) = (m x).
Proof. exact (eq_refl (m x)). Qed.
Lemma lem4719826 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (m : A -> nat) (x : A) : (term502 A s a n f m x) = (term503 A s a n f m x).
Proof. exact (MK_COMB (@lem4719824 A s a n f x) (@lem4719825 A m x)). Qed.
Lemma lem4719827 {A : Type'} (s : A -> Prop) (a : A) (m : A -> nat) (n : nat) (f : nat -> A) (x : A) : (term503 A s a n f m x) = (term504 A s a m n f x).
Proof. exact (eq_refl (term503 A s a n f m x)). Qed.
Lemma lem4719828 {A : Type'} (s : A -> Prop) (a : A) (m : A -> nat) (n : nat) (f : nat -> A) (x : A) : (term502 A s a n f m x) = (term504 A s a m n f x).
Proof. exact (TRANS (@lem4719826 A s a n f m x) (@lem4719827 A s a m n f x)). Qed.
Lemma lem4719829 {A : Type'} (s : A -> Prop) (a : A) (m : A -> nat) (n : nat) (f : nat -> A) : (term505 A s a n f m) = (term506 A s a m n f).
Proof. exact (fun_ext (fun x : A => @lem4719828 A s a m n f x)). Qed.
Lemma lem4719830 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4719831 {A : Type'} (s : A -> Prop) (a : A) (m : A -> nat) (n : nat) (f : nat -> A) : (term507 A s a n f m) = (term508 A s a m n f).
Proof. exact (MK_COMB (@lem4719830 A) (@lem4719829 A s a m n f)). Qed.
Lemma lem4719832 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term509 A s a n f) = (term510 A s a n f).
Proof. exact (fun_ext (fun m : A -> nat => @lem4719831 A s a m n f)). Qed.
Lemma lem4719833 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem4719834 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term492 A s a n f) = (term511 A s a n f).
Proof. exact (MK_COMB (@lem4719833 A) (@lem4719832 A s a n f)). Qed.
Lemma lem4719835 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : ((term491 A s a n f) = (term492 A s a n f)) = ((term486 A s a n f) = (term511 A s a n f)).
Proof. exact (MK_COMB (@lem4719823 A s a n f) (@lem4719834 A s a n f)). Qed.
Lemma lem4719836 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term486 A s a n f) = (term511 A s a n f).
Proof. exact (EQ_MP (@lem4719835 A s a n f) (@lem4719810 A s a n f)). Qed.
Lemma lem4719837 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term451 A s a n f) = (term511 A s a n f).
Proof. exact (TRANS (@lem4719806 A s a n f) (@lem4719836 A s a n f)). Qed.
Lemma lem4719838 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term429 A s a n f) = (term511 A s a n f).
Proof. exact (TRANS (@lem4719708 A s a n f) (@lem4719837 A s a n f)). Qed.
Lemma lem4719839 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) : (term267 A s a n f) = (term511 A s a n f).
Proof. exact (TRANS (@lem4719482 A s a n f) (@lem4719838 A s a n f)). Qed.
Lemma lem4719840 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term267 A s a n f) : term511 A s a n f.
Proof. exact (EQ_MP (@lem4719839 A s a n f) (@lem4719349 A s a n f h1)). Qed.
Lemma lem4719857 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term648 A m n a s) = (term682 A m n a s).
Proof. exact (@lem17362 (m = n) (@IN A a s)). Qed.
Lemma lem4720763 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem4720822 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) : term682 A m n a s.
Proof. exact (EQ_MP (@lem4719857 A m n a s) (@lem4719351 A m n a s h1)). Qed.
Lemma lem4721083 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem4721460 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem4721584 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem4721667 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) : term217 A a s.
Proof. exact (proj2 (@lem4720822 A m n a s h1)). Qed.
Lemma lem4721897 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem4721898 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : term683 A a s.
Proof. exact (fun h0 : term217 A a s => @lem4721897 A a s h1). Qed.
Lemma lem4721900 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4721901 {A : Type'} (a : A) (s : A -> Prop) : (term683 A a s) = (@IN A a s).
Proof. exact (@lem4721900 (@IN A a s)). Qed.
Lemma lem4721902 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (EQ_MP (@lem4721901 A a s) (@lem4721898 A a s h1)). Qed.
Lemma lem4721905 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4721907 {A : Type'} (a : A) (s : A -> Prop) : (term217 A a s) = (term684 A a s).
Proof. exact (@lem4721905 (@IN A a s)). Qed.
Lemma lem4721910 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) : term684 A a s.
Proof. exact (EQ_MP (@lem4721907 A a s) (@lem4721667 A m n a s h1)). Qed.
Lemma lem4721913 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : False.
Proof. exact (@lem4721910 A m n a s h1 (@lem4721902 A a s h2)). Qed.
Lemma lem4721914 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : term632.
Proof. exact (fun h0 : ~ False => @lem4721913 A m n a s h1 h2). Qed.
Lemma lem4721916 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4721917 : term632 = False.
Proof. exact (@lem4721916 False). Qed.
Lemma lem4721918 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem4721917) (@lem4721914 A m n a s h1 h2)). Qed.
Lemma lem4721919 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h3 : @IN A a s => @lem4721918 A m n a s h1 h2) (fun h3 : False => @lem4721584 A a s h2)). Qed.
Lemma lem4721921 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem4721919 A m n a s h1 h2) (@lem4721584 A a s h2)). Qed.
Lemma lem4721922 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h3 : @IN A a s => @lem4721921 A m n a s h1 h2) (fun h3 : False => @lem4721460 A a s h2)). Qed.
Lemma lem4721923 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem4721922 A m n a s h1 h2) (@lem4721460 A a s h2)). Qed.
Lemma lem4721924 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h3 : @IN A a s => @lem4721923 A m n a s h1 h2) (fun h3 : False => @lem4721083 A a s h2)). Qed.
Lemma lem4721925 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem4721924 A m n a s h1 h2) (@lem4721083 A a s h2)). Qed.
Lemma lem4721926 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h3 : @IN A a s => @lem4721925 A m n a s h1 h2) (fun h3 : False => @lem4721083 A a s h2)). Qed.
Lemma lem4721927 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem4721926 A m n a s h1 h2) (@lem4721083 A a s h2)). Qed.
Lemma lem4721928 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h3 : @IN A a s => @lem4721927 A m n a s h1 h2) (fun h3 : False => @lem4720763 A a s h2)). Qed.
Lemma lem4721929 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term648 A m n a s) (h2 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem4721928 A m n a s h1 h2) (@lem4720763 A a s h2)). Qed.
Lemma lem4721930 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term648 A m n a s) (h3 : @IN A a s) : False.
Proof. exact (ex_elim (@lem4719840 A s a n f h1) (fun m' : A -> nat => fun h0 : term510 A s a n f m' => @lem4721929 A m n a s h2 h3)). Qed.
Lemma lem4721931 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term648 A m n a s) (h3 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h4 : @IN A a s => @lem4721930 A f m n a s h1 h2 h3) (fun h4 : False => @lem4719359 A a s h3)). Qed.
Lemma lem4721932 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term648 A m n a s) (h3 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem4721931 A f m n a s h1 h2 h3) (@lem4719359 A a s h3)). Qed.
Lemma lem4721933 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term648 A m n a s) (h3 : @IN A a s) : term335.
Proof. exact (fun h0 : term324 => @lem4721932 A f m n a s h1 h2 h3). Qed.
Lemma lem4721934 : term335 = term336.
Proof. exact (@lem69 term324). Qed.
Lemma lem4721935 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term648 A m n a s) (h3 : @IN A a s) : term336.
Proof. exact (EQ_MP (@lem4721934) (@lem4721933 A f m n a s h1 h2 h3)). Qed.
Lemma lem4721936 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term648 A m n a s) (h3 : @IN A a s) : term339 A.
Proof. exact (fun h0 : term323 A => @lem4721935 A f m n a s h1 h2 h3). Qed.
Lemma lem4721937 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : @IN A a s) : term652 A m n a s.
Proof. exact (fun h0 : term648 A m n a s => @lem4721936 A f m n a s h1 h0 h2). Qed.
Lemma lem4721938 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : @IN A a s) : term654 A m n a s.
Proof. exact (fun h0 : term312 m n => @lem4721937 A m n f a s h1 h2). Qed.
Lemma lem4721939 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term656 A f m n a s.
Proof. exact (fun h0 : term267 A s a n f => @lem4721938 A m n f a s h0 h1). Qed.
Lemma lem4721940 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term658 A f m n a s.
Proof. exact (fun h0 : term268 A n f s a => @lem4721939 A f m n a s h1). Qed.
Lemma lem4721941 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term660 A f m n a s.
Proof. exact (fun h0 : term252 A s a n => @lem4721940 A f m n a s h1). Qed.
Lemma lem4721942 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : term661 A f m n a s.
Proof. exact (fun h0 : @IN A a s => @lem4721941 A f m n a s h0). Qed.
Lemma lem4721947 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : term665 A m n a s.
Proof. exact (fun f : nat -> A => @lem4721942 A f m n a s). Qed.
Lemma lem4721952 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : term669 A n a s.
Proof. exact (fun m : nat => @lem4721947 A m n a s). Qed.
Lemma lem4721957 {A : Type'} (a : A) (s : A -> Prop) : term673 A a s.
Proof. exact (fun n : nat => @lem4721952 A n a s). Qed.
Lemma lem4721962 {A : Type'} (s : A -> Prop) : term677 A s.
Proof. exact (fun a : A => @lem4721957 A a s). Qed.
Lemma lem4721967 {A : Type'} : term681 A.
Proof. exact (fun s : A -> Prop => @lem4721962 A s). Qed.
Lemma lem4721968 {A : Type'} : term680 A.
Proof. exact (EQ_MP (@lem4719345 A) (@lem4721967 A)). Qed.
Lemma lem4721969 {A : Type'} (s : A -> Prop) : term685 A s.
Proof. exact (@lem4721968 A s). Qed.
Lemma lem4721970 {A : Type'} (s : A -> Prop) : (term685 A s) = (term676 A s).
Proof. exact (eq_refl (term685 A s)). Qed.
Lemma lem4721971 {A : Type'} (s : A -> Prop) : term676 A s.
Proof. exact (EQ_MP (@lem4721970 A s) (@lem4721969 A s)). Qed.
Lemma lem4721972 {A : Type'} (s : A -> Prop) (a : A) : term686 A s a.
Proof. exact (@lem4721971 A s a). Qed.
Lemma lem4721973 {A : Type'} (a : A) (s : A -> Prop) : (term686 A s a) = (term672 A a s).
Proof. exact (eq_refl (term686 A s a)). Qed.
Lemma lem4721974 {A : Type'} (a : A) (s : A -> Prop) : term672 A a s.
Proof. exact (EQ_MP (@lem4721973 A a s) (@lem4721972 A s a)). Qed.
Lemma lem4721975 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term687 A a s n.
Proof. exact (@lem4721974 A a s n). Qed.
Lemma lem4721976 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : (term687 A a s n) = (term668 A n a s).
Proof. exact (eq_refl (term687 A a s n)). Qed.
Lemma lem4721977 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : term668 A n a s.
Proof. exact (EQ_MP (@lem4721976 A n a s) (@lem4721975 A a s n)). Qed.
Lemma lem4721978 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (m : nat) : term688 A n a s m.
Proof. exact (@lem4721977 A n a s m). Qed.
Lemma lem4721979 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term688 A n a s m) = (term664 A m n a s).
Proof. exact (eq_refl (term688 A n a s m)). Qed.
Lemma lem4721980 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) : term664 A m n a s.
Proof. exact (EQ_MP (@lem4721979 A m n a s) (@lem4721978 A n a s m)). Qed.
Lemma lem4721981 {A : Type'} (m : nat) (n : nat) (a : A) (s : A -> Prop) (f : nat -> A) : term689 A m n a s f.
Proof. exact (@lem4721980 A m n a s f). Qed.
Lemma lem4721982 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : (term689 A m n a s f) = (term640 A f m n a s).
Proof. exact (eq_refl (term689 A m n a s f)). Qed.
Lemma lem4721983 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : term640 A f m n a s.
Proof. exact (EQ_MP (@lem4721982 A f m n a s) (@lem4721981 A m n a s f)). Qed.
Lemma lem4721985 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) : term640 A f m n a s.
Proof. exact (@lem4718964 A f m n a s (@lem4721983 A f m n a s)). Qed.
Lemma lem4721986 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term659 A f m n a s.
Proof. exact (@lem4721985 A f m n a s (@lem4715763 A a s h1)). Qed.
Lemma lem4721987 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term252 A s a n) (h2 : @IN A a s) : term657 A f m n a s.
Proof. exact (@lem4721986 A f m n a s h2 (@lem4715822 A s a n h1)). Qed.
Lemma lem4721988 {A : Type'} (m : nat) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term252 A s a n) (h3 : @IN A a s) : term655 A f m n a s.
Proof. exact (@lem4721987 A f m n a s h2 h3 (@lem4715928 A n f s a h1)). Qed.
Lemma lem4721989 {A : Type'} (m : nat) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term653 A m n a s.
Proof. exact (@lem4721988 A m f n a s h2 h3 h4 (@lem4715927 A s a n f h1)). Qed.
Lemma lem4721990 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term651 A m n a s.
Proof. exact (@lem4721989 A m f n a s h1 h2 h4 h5 (@lem4715991 m n h3)). Qed.
Lemma lem4721991 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term639 A m n a s) (h5 : term252 A s a n) (h6 : @IN A a s) : term338 A.
Proof. exact (@lem4721990 A f m n a s h1 h2 h3 h5 h6 (@lem4718944 A m n a s h4)). Qed.
Lemma lem4721992 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term639 A m n a s) (h5 : term252 A s a n) (h6 : @IN A a s) : term335.
Proof. exact (@lem4721991 A f m n a s h1 h2 h3 h4 h5 h6 (@lem4718945 A)). Qed.
Lemma lem4721993 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term639 A m n a s) (h5 : term252 A s a n) (h6 : @IN A a s) : False.
Proof. exact (@lem4721992 A f m n a s h1 h2 h3 h4 h5 h6 (@lem4718948)). Qed.
Lemma lem4721994 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term639 A m n a s) (h5 : term252 A s a n) (h6 : @IN A a s) : (term639 A m n a s) = False.
Proof. exact (prop_ext (fun h7 : term639 A m n a s => @lem4721993 A f m n a s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4718944 A m n a s h4)). Qed.
Lemma lem4721995 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term639 A m n a s) (h5 : term252 A s a n) (h6 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem4721994 A f m n a s h1 h2 h3 h4 h5 h6) (@lem4718944 A m n a s h4)). Qed.
Lemma lem4721996 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term638 A m n a s.
Proof. exact (fun h0 : term639 A m n a s => @lem4721995 A f m n a s h1 h2 h3 h0 h4 h5). Qed.
Lemma lem4721997 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term317 A m n a s.
Proof. exact (EQ_MP (@lem4718943 A m n a s) (@lem4721996 A f m n a s h1 h2 h3 h4 h5)). Qed.
Lemma lem4721998 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term293 A m n a s.
Proof. exact (EQ_MP (@lem4716006 A a s m n h3) (@lem4721997 A f m n a s h1 h2 h3 h4 h5)). Qed.
Lemma lem4721999 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term252 A s a n) (h5 : @IN A a s) : (term312 m n) = (term293 A m n a s).
Proof. exact (prop_ext (fun h6 : term312 m n => @lem4721998 A f m n a s h1 h2 h3 h4 h5) (fun h6 : term293 A m n a s => @lem4715991 m n h3)). Qed.
Lemma lem4722000 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term312 m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term293 A m n a s.
Proof. exact (EQ_MP (@lem4721999 A f m n a s h1 h2 h3 h4 h5) (@lem4715991 m n h3)). Qed.
Lemma lem4722001 {A : Type'} (m : nat) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term296 A m n a s.
Proof. exact (fun h0 : term312 m n => @lem4722000 A f m n a s h1 h2 h0 h3 h4). Qed.
Lemma lem4722002 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term173 A n f m s.
Proof. exact (EQ_MP (@lem4715990 A f s m n h3) (@lem4718939 A f m n a s h1 h2 h3 h4 h5)). Qed.
Lemma lem4722003 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : term252 A s a n) (h5 : @IN A a s) : (Peano.lt m n) = (term173 A n f m s).
Proof. exact (prop_ext (fun h6 : Peano.lt m n => @lem4722002 A f m n a s h1 h2 h3 h4 h5) (fun h6 : term173 A n f m s => @lem4715975 m n h3)). Qed.
Lemma lem4722004 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : term252 A s a n) (h5 : @IN A a s) : term173 A n f m s.
Proof. exact (EQ_MP (@lem4722003 A f m n a s h1 h2 h3 h4 h5) (@lem4715975 m n h3)). Qed.
Lemma lem4722005 {A : Type'} (m : nat) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term300 A n f m s.
Proof. exact (fun h0 : Peano.lt m n => @lem4722004 A f m n a s h1 h2 h0 h3 h4). Qed.
Lemma lem4722006 {A : Type'} (m : nat) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term303 A f m n a s.
Proof. exact (conj (@lem4722005 A m f n a s h1 h2 h3 h4) (@lem4722001 A m f n a s h1 h2 h3 h4)). Qed.
Lemma lem4722007 {A : Type'} (m : nat) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term284 A n f m a s.
Proof. exact (EQ_MP (@lem4715974 A n f m a s) (@lem4722006 A m f n a s h1 h2 h3 h4)). Qed.
Lemma lem4722008 {A : Type'} (m : nat) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term283 A n f a m s.
Proof. exact (EQ_MP (@lem4715956 A n f a m s) (@lem4722007 A m f n a s h1 h2 h3 h4)). Qed.
Lemma lem4722013 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term690 A n f a s.
Proof. exact (fun m : nat => @lem4722008 A m f n a s h1 h2 h3 h4). Qed.
Lemma lem4722014 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4722040 {A B : Type'} (f : A -> B) (y : A) : (term269 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4722041 {A : Type'} (f : nat -> A) (y : nat) : (term270 A f y) = (f y).
Proof. exact (@lem4722040 nat A f y). Qed.
Lemma lem4722042 {A : Type'} (n : nat) (f : nat -> A) (a : A) (m : nat) : (term271 A n f a m) = (term272 A n f a m).
Proof. exact (@lem4722041 A (term273 A n f a) m). Qed.
Lemma lem4722043 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : (term272 A n f a m) = (term274 A n f m a).
Proof. exact (eq_refl (term272 A n f a m)). Qed.
Lemma lem4722044 {A : Type'} (n : nat) (f : nat -> A) (a : A) : (term275 A n f a) = (term273 A n f a).
Proof. exact (fun_ext (fun m : nat => @lem4722043 A n f m a)). Qed.
Lemma lem4722045 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4722046 {A : Type'} (n : nat) (f : nat -> A) (a : A) (m : nat) : (term271 A n f a m) = (term272 A n f a m).
Proof. exact (MK_COMB (@lem4722044 A n f a) (@lem4722045 m)). Qed.
Lemma lem4722047 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4722048 {A : Type'} (n : nat) (f : nat -> A) (a : A) (m : nat) : (term276 A n f a m) = (term277 A n f a m).
Proof. exact (MK_COMB (@lem4722047 A) (@lem4722046 A n f a m)). Qed.
Lemma lem4722049 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : (term272 A n f a m) = (term274 A n f m a).
Proof. exact (eq_refl (term272 A n f a m)). Qed.
Lemma lem4722050 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : ((term271 A n f a m) = (term272 A n f a m)) = ((term272 A n f a m) = (term274 A n f m a)).
Proof. exact (MK_COMB (@lem4722048 A n f a m) (@lem4722049 A n f m a)). Qed.
Lemma lem4722051 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : (term272 A n f a m) = (term274 A n f m a).
Proof. exact (EQ_MP (@lem4722050 A n f m a) (@lem4722042 A n f a m)). Qed.
Lemma lem4722052 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4722053 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) : (term277 A n f a m) = (term691 A n f m a).
Proof. exact (MK_COMB (@lem4722052 A) (@lem4722051 A n f m a)). Qed.
Lemma lem4722054 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4722055 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (x : A) : ((term272 A n f a m) = x) = ((term274 A n f m a) = x).
Proof. exact (MK_COMB (@lem4722053 A n f m a) (@lem4722054 A x)). Qed.
Lemma lem4722058 (m : nat) (n : nat) : (term189 m n) = (term189 m n).
Proof. exact (eq_refl (term189 m n)). Qed.
Lemma lem4722059 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (x : A) : (term692 A n f a m x) = (term693 A n f m a x).
Proof. exact (MK_COMB (@lem4722058 m n) (@lem4722055 A n f m a x)). Qed.
Lemma lem4722062 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) : (term694 A n f a x) = (term695 A n f a x).
Proof. exact (fun_ext (fun m : nat => @lem4722059 A n f m a x)). Qed.
Lemma lem4722063 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4722064 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) : (term696 A n f a x) = (term697 A n f a x).
Proof. exact (MK_COMB (@lem4722063) (@lem4722062 A n f a x)). Qed.
Lemma lem4722065 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) : (term697 A n f a x) = (term696 A n f a x).
Proof. exact (SYM (@lem4722064 A n f a x)). Qed.
Lemma lem4722066 {A : Type'} (x : A) (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term267 A s a n f) : term698 A s a n f x.
Proof. exact (@lem4715927 A s a n f h1 x). Qed.
Lemma lem4722067 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (x : A) : (term698 A s a n f x) = (term391 A s a n f x).
Proof. exact (eq_refl (term698 A s a n f x)). Qed.
Lemma lem4722068 {A : Type'} (x : A) (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term267 A s a n f) : term391 A s a n f x.
Proof. exact (EQ_MP (@lem4722067 A s a n f x) (@lem4722066 A x s a n f h1)). Qed.
Lemma lem4722069 {A : Type'} (s : A -> Prop) : term699 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem4722070 {A : Type'} (s : A -> Prop) : (term699 A s) = (term385 A s).
Proof. exact (eq_refl (term699 A s)). Qed.
Lemma lem4722071 {A : Type'} (s : A -> Prop) : term385 A s.
Proof. exact (EQ_MP (@lem4722070 A s) (@lem4722069 A s)). Qed.
Lemma lem4722072 {A : Type'} (s : A -> Prop) (x : A) : term700 A s x.
Proof. exact (@lem4722071 A s x). Qed.
Lemma lem4722073 {A : Type'} (s : A -> Prop) (x : A) : (term700 A s x) = (term383 A s x).
Proof. exact (eq_refl (term700 A s x)). Qed.
Lemma lem4722074 {A : Type'} (s : A -> Prop) (x : A) : term383 A s x.
Proof. exact (EQ_MP (@lem4722073 A s x) (@lem4722072 A s x)). Qed.
Lemma lem4722075 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term701 A s x y.
Proof. exact (@lem4722074 A s x y). Qed.
Lemma lem4722076 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term701 A s x y) = ((term380 A x s y) = (term381 A s x y)).
Proof. exact (eq_refl (term701 A s x y)). Qed.
Lemma lem4722087 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4722094 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term380 A x s y) = (term381 A s x y).
Proof. exact (EQ_MP (@lem4722076 A s x y) (@lem4722075 A s x y)). Qed.
Lemma lem4722095 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term380 A x s y) = (term381 A s x y).
Proof. exact (@lem4722094 A s x y). Qed.
Lemma lem4722096 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term380 A x s a) = (term381 A s x a).
Proof. exact (@lem4722095 A s x a). Qed.
Lemma lem4722100 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4722087 A x s) (@lem4722014 A x s h1)). Qed.
Lemma lem4722101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4722102 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term702 A x s) = (and True).
Proof. exact (MK_COMB (@lem4722101) (@lem4722100 A x s h1)). Qed.
Lemma lem4722105 {A : Type'} (x : A) (a : A) : (term9 A x a) = (term9 A x a).
Proof. exact (eq_refl (term9 A x a)). Qed.
Lemma lem4722106 {A : Type'} (a : A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term381 A s x a) = (term703 A x a).
Proof. exact (MK_COMB (@lem4722102 A x s h1) (@lem4722105 A x a)). Qed.
Lemma lem4722108 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4722109 {A : Type'} (x : A) (a : A) : (term703 A x a) = (term9 A x a).
Proof. exact (@lem4722108 (term9 A x a)). Qed.
Lemma lem4722112 {A : Type'} (a : A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term381 A s x a) = (term9 A x a).
Proof. exact (TRANS (@lem4722106 A a x s h1) (@lem4722109 A x a)). Qed.
Lemma lem4722113 {A : Type'} (a : A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term380 A x s a) = (term9 A x a).
Proof. exact (TRANS (@lem4722096 A s x a) (@lem4722112 A a x s h1)). Qed.
Lemma lem4722114 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4722115 {A : Type'} (a : A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term390 A x s a) = (term704 A x a).
Proof. exact (MK_COMB (@lem4722114) (@lem4722113 A a x s h1)). Qed.
Lemma lem4722120 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term389 A n f x).
Proof. exact (eq_refl (term389 A n f x)). Qed.
Lemma lem4722121 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term391 A s a n f x) = (term705 A a n f x).
Proof. exact (MK_COMB (@lem4722115 A a x s h1) (@lem4722120 A n f x)). Qed.
Lemma lem4722124 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4722125 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term706 A s a n f x) = (term707 A a n f x).
Proof. exact (MK_COMB (@lem4722124) (@lem4722121 A a n f x s h1)). Qed.
Lemma lem4722134 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) : (term697 A n f a x) = (term697 A n f a x).
Proof. exact (eq_refl (term697 A n f a x)). Qed.
Lemma lem4722135 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term708 A s n f a x) = (term709 A n f a x).
Proof. exact (MK_COMB (@lem4722125 A a n f x s h1) (@lem4722134 A n f a x)). Qed.
Lemma lem4722138 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term709 A n f a x) = (term708 A s n f a x).
Proof. exact (SYM (@lem4722135 A n f a x s h1)). Qed.
Lemma lem4722139 {A : Type'} (_474 : A) (_475 : Prop) (_476 : A -> Prop) (_477 : A) : (term285 A _476 _475 _474 _477) = (term286 A _474 _475 _476 _477).
Proof. exact (@lem13473 A _474 _475 _476 _477). Qed.
Lemma lem4722140 {A : Type'} (_474 : A) (_475 : Prop) (m : nat) (n : nat) (x : A) (_477 : A) : (term710 A m n x _475 _474 _477) = (term711 A _474 _475 m n x _477).
Proof. exact (@lem4722139 A _474 _475 (term712 A m n x) _477). Qed.
Lemma lem4722141 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (x : A) (a : A) : (term713 A x n f m a) = (term714 A f m n x a).
Proof. exact (@lem4722140 A (f m) (Peano.lt m n) m n x a). Qed.
Lemma lem4722142 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) : (term715 A m n x a) = (term716 A m n a x).
Proof. exact (eq_refl (term715 A m n x a)). Qed.
Lemma lem4722143 (m : nat) (n : nat) : (term294 m n) = (term294 m n).
Proof. exact (eq_refl (term294 m n)). Qed.
Lemma lem4722144 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) : (term717 A m n x a) = (term718 A m n a x).
Proof. exact (MK_COMB (@lem4722143 m n) (@lem4722142 A m n a x)). Qed.
Lemma lem4722145 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term719 A n x f m) = (term191 A n f m x).
Proof. exact (eq_refl (term719 A n x f m)). Qed.
Lemma lem4722146 (m : nat) (n : nat) : (term298 m n) = (term298 m n).
Proof. exact (eq_refl (term298 m n)). Qed.
Lemma lem4722147 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term720 A n x f m) = (term721 A n f m x).
Proof. exact (MK_COMB (@lem4722146 m n) (@lem4722145 A n f m x)). Qed.
Lemma lem4722148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4722149 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term722 A n x f m) = (term723 A n f m x).
Proof. exact (MK_COMB (@lem4722148) (@lem4722147 A n f m x)). Qed.
Lemma lem4722150 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (x : A) : (term714 A f m n x a) = (term724 A f m n a x).
Proof. exact (MK_COMB (@lem4722149 A n f m x) (@lem4722144 A m n a x)). Qed.
Lemma lem4722151 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (x : A) : (term713 A x n f m a) = (term693 A n f m a x).
Proof. exact (eq_refl (term713 A x n f m a)). Qed.
Lemma lem4722152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4722153 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (a : A) (x : A) : (term725 A x n f m a) = (term726 A n f m a x).
Proof. exact (MK_COMB (@lem4722152) (@lem4722151 A n f m a x)). Qed.
Lemma lem4722154 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (x : A) : ((term713 A x n f m a) = (term714 A f m n x a)) = ((term693 A n f m a x) = (term724 A f m n a x)).
Proof. exact (MK_COMB (@lem4722153 A n f m a x) (@lem4722150 A f m n a x)). Qed.
Lemma lem4722155 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (x : A) : (term693 A n f m a x) = (term724 A f m n a x).
Proof. exact (EQ_MP (@lem4722154 A f m n a x) (@lem4722141 A f m n x a)). Qed.
Lemma lem4722156 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) : (term695 A n f a x) = (term727 A f n a x).
Proof. exact (fun_ext (fun m : nat => @lem4722155 A f m n a x)). Qed.
Lemma lem4722157 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4722158 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) : (term697 A n f a x) = (term728 A f n a x).
Proof. exact (MK_COMB (@lem4722157) (@lem4722156 A f n a x)). Qed.
Lemma lem4722159 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) : (term707 A a n f x) = (term707 A a n f x).
Proof. exact (eq_refl (term707 A a n f x)). Qed.
Lemma lem4722160 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) : (term709 A n f a x) = (term729 A f n a x).
Proof. exact (MK_COMB (@lem4722159 A a n f x) (@lem4722158 A f n a x)). Qed.
Lemma lem4722161 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) : (term729 A f n a x) = (term709 A n f a x).
Proof. exact (SYM (@lem4722160 A f n a x)). Qed.
Lemma lem4722183 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4722184 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4722183 p q p' q'). Qed.
Lemma lem4722185 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4722184 p q p'). Qed.
Lemma lem4722186 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) : term730 A f n a x.
Proof. exact (@lem4722185 (term705 A a n f x) (term728 A f n a x)). Qed.
Lemma lem4722187 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) : term731 A f n a x p'.
Proof. exact (@lem4722186 A f n a x p'). Qed.
Lemma lem4722188 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) : (term731 A f n a x p') = (term732 A f n a x p').
Proof. exact (eq_refl (term731 A f n a x p')). Qed.
Lemma lem4722189 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) : term732 A f n a x p'.
Proof. exact (EQ_MP (@lem4722188 A f n a x p') (@lem4722187 A f n a x p')). Qed.
Lemma lem4722190 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : term733 A f n a x p' q'.
Proof. exact (@lem4722189 A f n a x p' q'). Qed.
Lemma lem4722191 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : (term733 A f n a x p' q') = (term734 A f n a x p' q').
Proof. exact (eq_refl (term733 A f n a x p' q')). Qed.
Lemma lem4722192 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : term734 A f n a x p' q'.
Proof. exact (EQ_MP (@lem4722191 A f n a x p' q') (@lem4722190 A f n a x p' q')). Qed.
Lemma lem4722196 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4722197 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4722196 p q p' q'). Qed.
Lemma lem4722198 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4722197 p q p'). Qed.
Lemma lem4722199 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) : term735 A a n f x.
Proof. exact (@lem4722198 (term9 A x a) (term389 A n f x)). Qed.
Lemma lem4722200 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) : term736 A a n f x p'.
Proof. exact (@lem4722199 A a n f x p'). Qed.
Lemma lem4722201 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) : (term736 A a n f x p') = (term737 A a n f x p').
Proof. exact (eq_refl (term736 A a n f x p')). Qed.
Lemma lem4722202 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) : term737 A a n f x p'.
Proof. exact (EQ_MP (@lem4722201 A a n f x p') (@lem4722200 A a n f x p')). Qed.
Lemma lem4722203 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : term738 A a n f x p' q'.
Proof. exact (@lem4722202 A a n f x p' q'). Qed.
Lemma lem4722204 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : (term738 A a n f x p' q') = (term739 A a n f x p' q').
Proof. exact (eq_refl (term738 A a n f x p' q')). Qed.
Lemma lem4722205 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : term739 A a n f x p' q'.
Proof. exact (EQ_MP (@lem4722204 A a n f x p' q') (@lem4722203 A a n f x p' q')). Qed.
Lemma lem4722209 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4722210 {A : Type'} (x : A) : (@eq A x) = (@eq A x).
Proof. exact (eq_refl (@eq A x)). Qed.
Lemma lem4722211 {A : Type'} (a : A) (x : A) (h1 : a = x) : (x = a) = (x = x).
Proof. exact (MK_COMB (@lem4722210 A x) (@lem4722209 A a x h1)). Qed.
Lemma lem4722213 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4722214 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4722213 A x). Qed.
Lemma lem4722215 {A : Type'} (a : A) (x : A) (h1 : a = x) : (x = a) = True.
Proof. exact (TRANS (@lem4722211 A a x h1) (@lem4722214 A x)). Qed.
Lemma lem4722216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4722217 {A : Type'} (a : A) (x : A) (h1 : a = x) : (term9 A x a) = (~ True).
Proof. exact (MK_COMB (@lem4722216) (@lem4722215 A a x h1)). Qed.
Lemma lem4722219 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4722220 {A : Type'} (a : A) (x : A) (h1 : a = x) : (term9 A x a) = False.
Proof. exact (TRANS (@lem4722217 A a x h1) (@lem4722219)). Qed.
Lemma lem4722221 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (q' : Prop) : term740 A a n f x q'.
Proof. exact (@lem4722205 A a n f x False q'). Qed.
Lemma lem4722222 {A : Type'} (n : nat) (f : nat -> A) (q' : Prop) (a : A) (x : A) (h1 : a = x) : term741 A a n f x q'.
Proof. exact (@lem4722221 A a n f x q' (@lem4722220 A a x h1)). Qed.
Lemma lem4722230 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term389 A n f x).
Proof. exact (eq_refl (term389 A n f x)). Qed.
Lemma lem4722231 {A : Type'} (n : nat) (f : nat -> A) (x : A) : term742 A n f x.
Proof. exact (fun h0 : False => @lem4722230 A n f x). Qed.
Lemma lem4722232 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) (h1 : a = x) : term743 A a n f x.
Proof. exact (@lem4722222 A n f (term389 A n f x) a x h1). Qed.
Lemma lem4722233 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) (h1 : a = x) : (term705 A a n f x) = (term744 A n f x).
Proof. exact (@lem4722232 A n f a x h1 (@lem4722231 A n f x)). Qed.
Lemma lem4722235 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4722236 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term744 A n f x) = True.
Proof. exact (@lem4722235 (term389 A n f x)). Qed.
Lemma lem4722237 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) (h1 : a = x) : (term705 A a n f x) = True.
Proof. exact (TRANS (@lem4722233 A n f a x h1) (@lem4722236 A n f x)). Qed.
Lemma lem4722238 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (q' : Prop) : term745 A f n a x q'.
Proof. exact (@lem4722192 A f n a x True q'). Qed.
Lemma lem4722239 {A : Type'} (f : nat -> A) (n : nat) (q' : Prop) (a : A) (x : A) (h1 : a = x) : term746 A f n a x q'.
Proof. exact (@lem4722238 A f n a x q' (@lem4722237 A n f a x h1)). Qed.
Lemma lem4722250 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4722251 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4722250 p q p' q'). Qed.
Lemma lem4722252 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4722251 p q p'). Qed.
Lemma lem4722253 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : term747 A n f m x.
Proof. exact (@lem4722252 (Peano.lt m n) (term191 A n f m x)). Qed.
Lemma lem4722254 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) : term748 A n f m x p'.
Proof. exact (@lem4722253 A n f m x p'). Qed.
Lemma lem4722255 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) : (term748 A n f m x p') = (term749 A n f m x p').
Proof. exact (eq_refl (term748 A n f m x p')). Qed.
Lemma lem4722256 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) : term749 A n f m x p'.
Proof. exact (EQ_MP (@lem4722255 A n f m x p') (@lem4722254 A n f m x p')). Qed.
Lemma lem4722257 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) (q' : Prop) : term750 A n f m x p' q'.
Proof. exact (@lem4722256 A n f m x p' q'). Qed.
Lemma lem4722258 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) (q' : Prop) : (term750 A n f m x p' q') = (term751 A n f m x p' q').
Proof. exact (eq_refl (term750 A n f m x p' q')). Qed.
Lemma lem4722259 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) (q' : Prop) : term751 A n f m x p' q'.
Proof. exact (EQ_MP (@lem4722258 A n f m x p' q') (@lem4722257 A n f m x p' q')). Qed.
Lemma lem4722260 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem4722261 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) (q' : Prop) : term752 A f x m n q'.
Proof. exact (@lem4722259 A n f m x (Peano.lt m n) q'). Qed.
Lemma lem4722262 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) (q' : Prop) : term753 A f x m n q'.
Proof. exact (@lem4722261 A f x m n q' (@lem4722260 m n)). Qed.
Lemma lem4722263 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4722264 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem4722273 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem4722264 m n) (@lem4722263 m n h1)). Qed.
Lemma lem4722276 (m : nat) (n : nat) : (term754 m n) = (term754 m n).
Proof. exact (eq_refl (term754 m n)). Qed.
Lemma lem4722277 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term25 m n) = (term329 m n).
Proof. exact (MK_COMB (@lem4722276 m n) (@lem4722273 m n h1)). Qed.
Lemma lem4722279 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4722280 (m : nat) (n : nat) : (term329 m n) = True.
Proof. exact (@lem4722279 (m = n)). Qed.
Lemma lem4722283 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term25 m n) = True.
Proof. exact (TRANS (@lem4722277 m n h1) (@lem4722280 m n)). Qed.
Lemma lem4722284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4722285 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term189 m n) = (and True).
Proof. exact (MK_COMB (@lem4722284) (@lem4722283 m n h1)). Qed.
Lemma lem4722290 {A : Type'} (f : nat -> A) (m : nat) (x : A) : ((f m) = x) = ((f m) = x).
Proof. exact (eq_refl ((f m) = x)). Qed.
Lemma lem4722291 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term191 A n f m x) = (term129 A f m x).
Proof. exact (MK_COMB (@lem4722285 m n h1) (@lem4722290 A f m x)). Qed.
Lemma lem4722293 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4722294 {A : Type'} (f : nat -> A) (m : nat) (x : A) : (term129 A f m x) = ((f m) = x).
Proof. exact (@lem4722293 ((f m) = x)). Qed.
Lemma lem4722297 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term191 A n f m x) = ((f m) = x).
Proof. exact (TRANS (@lem4722291 A f x m n h1) (@lem4722294 A f m x)). Qed.
Lemma lem4722298 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : term755 A n f m x.
Proof. exact (fun h0 : Peano.lt m n => @lem4722297 A f x m n h0). Qed.
Lemma lem4722299 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : term756 A n f m x.
Proof. exact (@lem4722262 A f x m n ((f m) = x)). Qed.
Lemma lem4722300 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term721 A n f m x) = (term757 A n f m x).
Proof. exact (@lem4722299 A n f m x (@lem4722298 A n f m x)). Qed.
Lemma lem4722328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4722329 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term723 A n f m x) = (term758 A n f m x).
Proof. exact (MK_COMB (@lem4722328) (@lem4722300 A n f m x)). Qed.
Lemma lem4722360 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4722361 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4722360 p q p' q'). Qed.
Lemma lem4722362 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4722361 p q p'). Qed.
Lemma lem4722363 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) : term759 A m n a x.
Proof. exact (@lem4722362 (term312 m n) (term716 A m n a x)). Qed.
Lemma lem4722364 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) : term760 A m n a x p'.
Proof. exact (@lem4722363 A m n a x p'). Qed.
Lemma lem4722365 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) : (term760 A m n a x p') = (term761 A m n a x p').
Proof. exact (eq_refl (term760 A m n a x p')). Qed.
Lemma lem4722366 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) : term761 A m n a x p'.
Proof. exact (EQ_MP (@lem4722365 A m n a x p') (@lem4722364 A m n a x p')). Qed.
Lemma lem4722367 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : term762 A m n a x p' q'.
Proof. exact (@lem4722366 A m n a x p' q'). Qed.
Lemma lem4722368 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : (term762 A m n a x p' q') = (term763 A m n a x p' q').
Proof. exact (eq_refl (term762 A m n a x p' q')). Qed.
Lemma lem4722369 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : term763 A m n a x p' q'.
Proof. exact (EQ_MP (@lem4722368 A m n a x p' q') (@lem4722367 A m n a x p' q')). Qed.
Lemma lem4722370 (m : nat) (n : nat) : (term312 m n) = (term312 m n).
Proof. exact (eq_refl (term312 m n)). Qed.
Lemma lem4722371 {A : Type'} (a : A) (x : A) (m : nat) (n : nat) (q' : Prop) : term764 A a x m n q'.
Proof. exact (@lem4722369 A m n a x (term312 m n) q'). Qed.
Lemma lem4722372 {A : Type'} (a : A) (x : A) (m : nat) (n : nat) (q' : Prop) : term765 A a x m n q'.
Proof. exact (@lem4722371 A a x m n q' (@lem4722370 m n)). Qed.
Lemma lem4722373 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4722374 (m : nat) (n : nat) : term313 m n.
Proof. exact (@lem82 (Peano.lt m n)). Qed.
Lemma lem4722383 (m : nat) (n : nat) (h1 : term312 m n) : (Peano.lt m n) = False.
Proof. exact (@lem4722374 m n (@lem4722373 m n h1)). Qed.
Lemma lem4722384 (m : nat) (n : nat) : (term754 m n) = (term754 m n).
Proof. exact (eq_refl (term754 m n)). Qed.
Lemma lem4722385 (m : nat) (n : nat) (h1 : term312 m n) : (term25 m n) = (term644 m n).
Proof. exact (MK_COMB (@lem4722384 m n) (@lem4722383 m n h1)). Qed.
Lemma lem4722387 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4722388 (m : nat) (n : nat) : (term644 m n) = (m = n).
Proof. exact (@lem4722387 (m = n)). Qed.
Lemma lem4722391 (m : nat) (n : nat) (h1 : term312 m n) : (term25 m n) = (m = n).
Proof. exact (TRANS (@lem4722385 m n h1) (@lem4722388 m n)). Qed.
Lemma lem4722392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4722393 (m : nat) (n : nat) (h1 : term312 m n) : (term189 m n) = (term766 m n).
Proof. exact (MK_COMB (@lem4722392) (@lem4722391 m n h1)). Qed.
Lemma lem4722399 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4722400 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4722401 {A : Type'} (a : A) (x : A) (h1 : a = x) : (@eq A a) = (@eq A x).
Proof. exact (MK_COMB (@lem4722400 A) (@lem4722399 A a x h1)). Qed.
Lemma lem4722402 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4722403 {A : Type'} (a : A) (x : A) (h1 : a = x) : (a = x) = (x = x).
Proof. exact (MK_COMB (@lem4722401 A a x h1) (@lem4722402 A x)). Qed.
Lemma lem4722405 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4722406 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4722405 A x). Qed.
Lemma lem4722409 {A : Type'} (a : A) (x : A) (h1 : a = x) : (a = x) = True.
Proof. exact (TRANS (@lem4722403 A a x h1) (@lem4722406 A x)). Qed.
Lemma lem4722410 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (h1 : term312 m n) (h2 : a = x) : (term716 A m n a x) = (term767 m n).
Proof. exact (MK_COMB (@lem4722393 m n h1) (@lem4722409 A a x h2)). Qed.
Lemma lem4722412 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4722413 (m : nat) (n : nat) : (term767 m n) = (m = n).
Proof. exact (@lem4722412 (m = n)). Qed.
Lemma lem4722416 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (h1 : term312 m n) (h2 : a = x) : (term716 A m n a x) = (m = n).
Proof. exact (TRANS (@lem4722410 A m n a x h1 h2) (@lem4722413 m n)). Qed.
Lemma lem4722417 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (h1 : a = x) : term768 A a x m n.
Proof. exact (fun h0 : term312 m n => @lem4722416 A m n a x h0 h1). Qed.
Lemma lem4722418 {A : Type'} (a : A) (x : A) (m : nat) (n : nat) : term769 A a x m n.
Proof. exact (@lem4722372 A a x m n (m = n)). Qed.
Lemma lem4722419 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (h1 : a = x) : (term718 A m n a x) = (term770 m n).
Proof. exact (@lem4722418 A a x m n (@lem4722417 A m n a x h1)). Qed.
Lemma lem4722447 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (x : A) (h1 : a = x) : (term724 A f m n a x) = (term771 A f x m n).
Proof. exact (MK_COMB (@lem4722329 A n f m x) (@lem4722419 A m n a x h1)). Qed.
Lemma lem4722504 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : a = x) : (term727 A f n a x) = (term772 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4722447 A f m n a x h1)). Qed.
Lemma lem4722561 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4722562 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : a = x) : (term728 A f n a x) = (term773 A f x n).
Proof. exact (MK_COMB (@lem4722561) (@lem4722504 A f n a x h1)). Qed.
Lemma lem4722619 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : a = x) : term774 A a f x n.
Proof. exact (fun h0 : True => @lem4722562 A f n a x h1). Qed.
Lemma lem4722620 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : a = x) : term775 A a f x n.
Proof. exact (@lem4722239 A f n (term773 A f x n) a x h1). Qed.
Lemma lem4722621 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : a = x) : (term729 A f n a x) = (term776 A f x n).
Proof. exact (@lem4722620 A f n a x h1 (@lem4722619 A f n a x h1)). Qed.
Lemma lem4722623 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4722624 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term776 A f x n) = (term773 A f x n).
Proof. exact (@lem4722623 (term773 A f x n)). Qed.
Lemma lem4722681 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : a = x) : (term729 A f n a x) = (term773 A f x n).
Proof. exact (TRANS (@lem4722621 A f n a x h1) (@lem4722624 A f x n)). Qed.
Lemma lem4722682 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : a = x) : (term773 A f x n) = (term729 A f n a x).
Proof. exact (SYM (@lem4722681 A f n a x h1)). Qed.
Lemma lem4722701 {A : Type'} (a : A) (x : A) : term777 A a x.
Proof. exact (@lem82 (a = x)). Qed.
Lemma lem4722704 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4722705 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem4722704 A a x h1)). Qed.
Lemma lem4722706 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4722707 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem4722706 A x a h1)). Qed.
Lemma lem4722708 {A : Type'} (x : A) (a : A) : (a = x) = (x = a).
Proof. exact (prop_ext (fun h1 : a = x => @lem4722705 A a x h1) (fun h1 : x = a => @lem4722707 A x a h1)). Qed.
Lemma lem4722709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4722710 {A : Type'} (x : A) (a : A) : (term9 A a x) = (term9 A x a).
Proof. exact (MK_COMB (@lem4722709) (@lem4722708 A x a)). Qed.
Lemma lem4722711 {A : Type'} (a : A) (x : A) (h1 : term9 A a x) : term9 A x a.
Proof. exact (EQ_MP (@lem4722710 A x a) (@lem4713738 A a x h1)). Qed.
Lemma lem4722712 {A : Type'} (x : A) (a : A) : term777 A x a.
Proof. exact (@lem82 (x = a)). Qed.
Lemma lem4722717 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4722718 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4722717 p q p' q'). Qed.
Lemma lem4722719 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4722718 p q p'). Qed.
Lemma lem4722720 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) : term730 A f n a x.
Proof. exact (@lem4722719 (term705 A a n f x) (term728 A f n a x)). Qed.
Lemma lem4722721 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) : term731 A f n a x p'.
Proof. exact (@lem4722720 A f n a x p'). Qed.
Lemma lem4722722 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) : (term731 A f n a x p') = (term732 A f n a x p').
Proof. exact (eq_refl (term731 A f n a x p')). Qed.
Lemma lem4722723 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) : term732 A f n a x p'.
Proof. exact (EQ_MP (@lem4722722 A f n a x p') (@lem4722721 A f n a x p')). Qed.
Lemma lem4722724 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : term733 A f n a x p' q'.
Proof. exact (@lem4722723 A f n a x p' q'). Qed.
Lemma lem4722725 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : (term733 A f n a x p' q') = (term734 A f n a x p' q').
Proof. exact (eq_refl (term733 A f n a x p' q')). Qed.
Lemma lem4722726 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : term734 A f n a x p' q'.
Proof. exact (EQ_MP (@lem4722725 A f n a x p' q') (@lem4722724 A f n a x p' q')). Qed.
Lemma lem4722730 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4722731 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4722730 p q p' q'). Qed.
Lemma lem4722732 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4722731 p q p'). Qed.
Lemma lem4722733 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) : term735 A a n f x.
Proof. exact (@lem4722732 (term9 A x a) (term389 A n f x)). Qed.
Lemma lem4722734 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) : term736 A a n f x p'.
Proof. exact (@lem4722733 A a n f x p'). Qed.
Lemma lem4722735 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) : (term736 A a n f x p') = (term737 A a n f x p').
Proof. exact (eq_refl (term736 A a n f x p')). Qed.
Lemma lem4722736 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) : term737 A a n f x p'.
Proof. exact (EQ_MP (@lem4722735 A a n f x p') (@lem4722734 A a n f x p')). Qed.
Lemma lem4722737 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : term738 A a n f x p' q'.
Proof. exact (@lem4722736 A a n f x p' q'). Qed.
Lemma lem4722738 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : (term738 A a n f x p' q') = (term739 A a n f x p' q').
Proof. exact (eq_refl (term738 A a n f x p' q')). Qed.
Lemma lem4722739 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (p' : Prop) (q' : Prop) : term739 A a n f x p' q'.
Proof. exact (EQ_MP (@lem4722738 A a n f x p' q') (@lem4722737 A a n f x p' q')). Qed.
Lemma lem4722741 {A : Type'} (a : A) (x : A) (h1 : term9 A a x) : (x = a) = False.
Proof. exact (@lem4722712 A x a (@lem4722711 A a x h1)). Qed.
Lemma lem4722742 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4722743 {A : Type'} (a : A) (x : A) (h1 : term9 A a x) : (term9 A x a) = (~ False).
Proof. exact (MK_COMB (@lem4722742) (@lem4722741 A a x h1)). Qed.
Lemma lem4722745 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4722746 {A : Type'} (a : A) (x : A) (h1 : term9 A a x) : (term9 A x a) = True.
Proof. exact (TRANS (@lem4722743 A a x h1) (@lem4722745)). Qed.
Lemma lem4722747 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (q' : Prop) : term778 A a n f x q'.
Proof. exact (@lem4722739 A a n f x True q'). Qed.
Lemma lem4722748 {A : Type'} (n : nat) (f : nat -> A) (q' : Prop) (a : A) (x : A) (h1 : term9 A a x) : term779 A a n f x q'.
Proof. exact (@lem4722747 A a n f x q' (@lem4722746 A a x h1)). Qed.
Lemma lem4722758 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term389 A n f x).
Proof. exact (eq_refl (term389 A n f x)). Qed.
Lemma lem4722759 {A : Type'} (n : nat) (f : nat -> A) (x : A) : term780 A n f x.
Proof. exact (fun h0 : True => @lem4722758 A n f x). Qed.
Lemma lem4722760 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) (h1 : term9 A a x) : term781 A a n f x.
Proof. exact (@lem4722748 A n f (term389 A n f x) a x h1). Qed.
Lemma lem4722761 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) (h1 : term9 A a x) : (term705 A a n f x) = (term782 A n f x).
Proof. exact (@lem4722760 A n f a x h1 (@lem4722759 A n f x)). Qed.
Lemma lem4722763 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4722764 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term782 A n f x) = (term389 A n f x).
Proof. exact (@lem4722763 (term389 A n f x)). Qed.
Lemma lem4722769 {A : Type'} (n : nat) (f : nat -> A) (a : A) (x : A) (h1 : term9 A a x) : (term705 A a n f x) = (term389 A n f x).
Proof. exact (TRANS (@lem4722761 A n f a x h1) (@lem4722764 A n f x)). Qed.
Lemma lem4722770 {A : Type'} (a : A) (n : nat) (f : nat -> A) (x : A) (q' : Prop) : term783 A a n f x q'.
Proof. exact (@lem4722726 A f n a x (term389 A n f x) q'). Qed.
Lemma lem4722771 {A : Type'} (n : nat) (f : nat -> A) (q' : Prop) (a : A) (x : A) (h1 : term9 A a x) : term784 A a n f x q'.
Proof. exact (@lem4722770 A a n f x q' (@lem4722769 A n f a x h1)). Qed.
Lemma lem4722780 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4722781 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4722780 p q p' q'). Qed.
Lemma lem4722782 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4722781 p q p'). Qed.
Lemma lem4722783 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : term747 A n f m x.
Proof. exact (@lem4722782 (Peano.lt m n) (term191 A n f m x)). Qed.
Lemma lem4722784 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) : term748 A n f m x p'.
Proof. exact (@lem4722783 A n f m x p'). Qed.
Lemma lem4722785 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) : (term748 A n f m x p') = (term749 A n f m x p').
Proof. exact (eq_refl (term748 A n f m x p')). Qed.
Lemma lem4722786 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) : term749 A n f m x p'.
Proof. exact (EQ_MP (@lem4722785 A n f m x p') (@lem4722784 A n f m x p')). Qed.
Lemma lem4722787 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) (q' : Prop) : term750 A n f m x p' q'.
Proof. exact (@lem4722786 A n f m x p' q'). Qed.
Lemma lem4722788 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) (q' : Prop) : (term750 A n f m x p' q') = (term751 A n f m x p' q').
Proof. exact (eq_refl (term750 A n f m x p' q')). Qed.
Lemma lem4722789 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) (p' : Prop) (q' : Prop) : term751 A n f m x p' q'.
Proof. exact (EQ_MP (@lem4722788 A n f m x p' q') (@lem4722787 A n f m x p' q')). Qed.
Lemma lem4722790 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem4722791 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) (q' : Prop) : term752 A f x m n q'.
Proof. exact (@lem4722789 A n f m x (Peano.lt m n) q'). Qed.
Lemma lem4722792 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) (q' : Prop) : term753 A f x m n q'.
Proof. exact (@lem4722791 A f x m n q' (@lem4722790 m n)). Qed.
Lemma lem4722793 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4722794 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem4722803 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem4722794 m n) (@lem4722793 m n h1)). Qed.
Lemma lem4722804 (m : nat) (n : nat) : (term754 m n) = (term754 m n).
Proof. exact (eq_refl (term754 m n)). Qed.
Lemma lem4722805 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term25 m n) = (term329 m n).
Proof. exact (MK_COMB (@lem4722804 m n) (@lem4722803 m n h1)). Qed.
Lemma lem4722807 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4722808 (m : nat) (n : nat) : (term329 m n) = True.
Proof. exact (@lem4722807 (m = n)). Qed.
Lemma lem4722809 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term25 m n) = True.
Proof. exact (TRANS (@lem4722805 m n h1) (@lem4722808 m n)). Qed.
Lemma lem4722810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4722811 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term189 m n) = (and True).
Proof. exact (MK_COMB (@lem4722810) (@lem4722809 m n h1)). Qed.
Lemma lem4722814 {A : Type'} (f : nat -> A) (m : nat) (x : A) : ((f m) = x) = ((f m) = x).
Proof. exact (eq_refl ((f m) = x)). Qed.
Lemma lem4722815 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term191 A n f m x) = (term129 A f m x).
Proof. exact (MK_COMB (@lem4722811 m n h1) (@lem4722814 A f m x)). Qed.
Lemma lem4722817 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4722818 {A : Type'} (f : nat -> A) (m : nat) (x : A) : (term129 A f m x) = ((f m) = x).
Proof. exact (@lem4722817 ((f m) = x)). Qed.
Lemma lem4722821 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) (h1 : Peano.lt m n) : (term191 A n f m x) = ((f m) = x).
Proof. exact (TRANS (@lem4722815 A f x m n h1) (@lem4722818 A f m x)). Qed.
Lemma lem4722822 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : term755 A n f m x.
Proof. exact (fun h0 : Peano.lt m n => @lem4722821 A f x m n h0). Qed.
Lemma lem4722823 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : term756 A n f m x.
Proof. exact (@lem4722792 A f x m n ((f m) = x)). Qed.
Lemma lem4722824 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term721 A n f m x) = (term757 A n f m x).
Proof. exact (@lem4722823 A n f m x (@lem4722822 A n f m x)). Qed.
Lemma lem4722852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4722853 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term723 A n f m x) = (term758 A n f m x).
Proof. exact (MK_COMB (@lem4722852) (@lem4722824 A n f m x)). Qed.
Lemma lem4722884 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term88 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4722885 (p : Prop) (q : Prop) (p' : Prop) : term89 p q p'.
Proof. exact (fun q' : Prop => @lem4722884 p q p' q'). Qed.
Lemma lem4722886 (p : Prop) (q : Prop) : term90 p q.
Proof. exact (fun p' : Prop => @lem4722885 p q p'). Qed.
Lemma lem4722887 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) : term759 A m n a x.
Proof. exact (@lem4722886 (term312 m n) (term716 A m n a x)). Qed.
Lemma lem4722888 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) : term760 A m n a x p'.
Proof. exact (@lem4722887 A m n a x p'). Qed.
Lemma lem4722889 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) : (term760 A m n a x p') = (term761 A m n a x p').
Proof. exact (eq_refl (term760 A m n a x p')). Qed.
Lemma lem4722890 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) : term761 A m n a x p'.
Proof. exact (EQ_MP (@lem4722889 A m n a x p') (@lem4722888 A m n a x p')). Qed.
Lemma lem4722891 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : term762 A m n a x p' q'.
Proof. exact (@lem4722890 A m n a x p' q'). Qed.
Lemma lem4722892 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : (term762 A m n a x p' q') = (term763 A m n a x p' q').
Proof. exact (eq_refl (term762 A m n a x p' q')). Qed.
Lemma lem4722893 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (p' : Prop) (q' : Prop) : term763 A m n a x p' q'.
Proof. exact (EQ_MP (@lem4722892 A m n a x p' q') (@lem4722891 A m n a x p' q')). Qed.
Lemma lem4722894 (m : nat) (n : nat) : (term312 m n) = (term312 m n).
Proof. exact (eq_refl (term312 m n)). Qed.
Lemma lem4722895 {A : Type'} (a : A) (x : A) (m : nat) (n : nat) (q' : Prop) : term764 A a x m n q'.
Proof. exact (@lem4722893 A m n a x (term312 m n) q'). Qed.
Lemma lem4722896 {A : Type'} (a : A) (x : A) (m : nat) (n : nat) (q' : Prop) : term765 A a x m n q'.
Proof. exact (@lem4722895 A a x m n q' (@lem4722894 m n)). Qed.
Lemma lem4722897 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4722898 (m : nat) (n : nat) : term313 m n.
Proof. exact (@lem82 (Peano.lt m n)). Qed.
Lemma lem4722907 (m : nat) (n : nat) (h1 : term312 m n) : (Peano.lt m n) = False.
Proof. exact (@lem4722898 m n (@lem4722897 m n h1)). Qed.
Lemma lem4722908 (m : nat) (n : nat) : (term754 m n) = (term754 m n).
Proof. exact (eq_refl (term754 m n)). Qed.
Lemma lem4722909 (m : nat) (n : nat) (h1 : term312 m n) : (term25 m n) = (term644 m n).
Proof. exact (MK_COMB (@lem4722908 m n) (@lem4722907 m n h1)). Qed.
Lemma lem4722911 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4722912 (m : nat) (n : nat) : (term644 m n) = (m = n).
Proof. exact (@lem4722911 (m = n)). Qed.
Lemma lem4722915 (m : nat) (n : nat) (h1 : term312 m n) : (term25 m n) = (m = n).
Proof. exact (TRANS (@lem4722909 m n h1) (@lem4722912 m n)). Qed.
Lemma lem4722916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4722917 (m : nat) (n : nat) (h1 : term312 m n) : (term189 m n) = (term766 m n).
Proof. exact (MK_COMB (@lem4722916) (@lem4722915 m n h1)). Qed.
Lemma lem4722921 {A : Type'} (a : A) (x : A) (h1 : term9 A a x) : (a = x) = False.
Proof. exact (@lem4722701 A a x (@lem4713738 A a x h1)). Qed.
Lemma lem4722922 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (h1 : term312 m n) (h2 : term9 A a x) : (term716 A m n a x) = (term785 m n).
Proof. exact (MK_COMB (@lem4722917 m n h1) (@lem4722921 A a x h2)). Qed.
Lemma lem4722924 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4722925 (m : nat) (n : nat) : (term785 m n) = False.
Proof. exact (@lem4722924 (m = n)). Qed.
Lemma lem4722926 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (h1 : term312 m n) (h2 : term9 A a x) : (term716 A m n a x) = False.
Proof. exact (TRANS (@lem4722922 A m n a x h1 h2) (@lem4722925 m n)). Qed.
Lemma lem4722927 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : term786 A m n a x.
Proof. exact (fun h0 : term312 m n => @lem4722926 A m n a x h0 h1). Qed.
Lemma lem4722928 {A : Type'} (a : A) (x : A) (m : nat) (n : nat) : term787 A a x m n.
Proof. exact (@lem4722896 A a x m n False). Qed.
Lemma lem4722929 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : (term718 A m n a x) = (term788 m n).
Proof. exact (@lem4722928 A a x m n (@lem4722927 A m n a x h1)). Qed.
Lemma lem4722931 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4722932 (m : nat) (n : nat) : (term788 m n) = (term618 m n).
Proof. exact (@lem4722931 (term312 m n)). Qed.
Lemma lem4722934 (t : Prop) : (term242 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem4722935 (m : nat) (n : nat) : (term618 m n) = (Peano.lt m n).
Proof. exact (@lem4722934 (Peano.lt m n)). Qed.
Lemma lem4722936 (m : nat) (n : nat) : (term788 m n) = (Peano.lt m n).
Proof. exact (TRANS (@lem4722932 m n) (@lem4722935 m n)). Qed.
Lemma lem4722937 {A : Type'} (m : nat) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : (term718 A m n a x) = (Peano.lt m n).
Proof. exact (TRANS (@lem4722929 A m n a x h1) (@lem4722936 m n)). Qed.
Lemma lem4722938 {A : Type'} (f : nat -> A) (m : nat) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : (term724 A f m n a x) = (term789 A f x m n).
Proof. exact (MK_COMB (@lem4722853 A n f m x) (@lem4722937 A m n a x h1)). Qed.
Lemma lem4722968 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : (term727 A f n a x) = (term790 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4722938 A f m n a x h1)). Qed.
Lemma lem4722998 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4722999 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : (term728 A f n a x) = (term791 A f x n).
Proof. exact (MK_COMB (@lem4722998) (@lem4722968 A f n a x h1)). Qed.
Lemma lem4723029 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : term792 A a f x n.
Proof. exact (fun h0 : term389 A n f x => @lem4722999 A f n a x h1). Qed.
Lemma lem4723030 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : term793 A a f x n.
Proof. exact (@lem4722771 A n f (term791 A f x n) a x h1). Qed.
Lemma lem4723031 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : (term729 A f n a x) = (term794 A f x n).
Proof. exact (@lem4723030 A f n a x h1 (@lem4723029 A f n a x h1)). Qed.
Lemma lem4723121 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term9 A a x) : (term794 A f x n) = (term729 A f n a x).
Proof. exact (SYM (@lem4723031 A f n a x h1)). Qed.
Lemma lem4723123 (p : Prop) : p = (term320 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4723124 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term773 A f x n) = (term795 A f x n).
Proof. exact (@lem4723123 (term773 A f x n)). Qed.
Lemma lem4723125 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term795 A f x n) = (term773 A f x n).
Proof. exact (SYM (@lem4723124 A f x n)). Qed.
Lemma lem4723126 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term796 A f x n) : term796 A f x n.
Proof. exact (h1). Qed.
Lemma lem4723127 {A : Type'} : term323 A.
Proof. exact (@lem3205803 A). Qed.
Lemma lem4723130 : term324.
Proof. exact (@lem3205803 nat). Qed.
Lemma lem4723133 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term797 A s a f x n) : term797 A s a f x n.
Proof. exact (h1). Qed.
Lemma lem4723134 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term798 A s a f x n.
Proof. exact (fun h0 : term797 A s a f x n => @lem4723133 A s a f x n h0). Qed.
Lemma lem4723135 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term798 A s a f x n) : term798 A s a f x n.
Proof. exact (h1). Qed.
Lemma lem4723136 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term797 A s a f x n) : term797 A s a f x n.
Proof. exact (h1). Qed.
Lemma lem4723137 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term798 A s a f x n) (h2 : term797 A s a f x n) : term797 A s a f x n.
Proof. exact (@lem4723135 A s a f x n h1 (@lem4723136 A s a f x n h2)). Qed.
Lemma lem4723138 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term797 A s a f x n) : term799 A s a f x n.
Proof. exact (fun h0 : term798 A s a f x n => @lem4723137 A s a f x n h0 h1). Qed.
Lemma lem4723139 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term798 A s a f x n) : term798 A s a f x n.
Proof. exact (h1). Qed.
Lemma lem4723140 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term798 A s a f x n) (h2 : term797 A s a f x n) : term797 A s a f x n.
Proof. exact (@lem4723138 A s a f x n h2 (@lem4723139 A s a f x n h1)). Qed.
Lemma lem4723141 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term798 A s a f x n) : term798 A s a f x n.
Proof. exact (fun h0 : term797 A s a f x n => @lem4723140 A s a f x n h1 h0). Qed.
Lemma lem4723142 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term800 A s a f x n.
Proof. exact (fun h0 : term798 A s a f x n => @lem4723141 A s a f x n h0). Qed.
Lemma lem4723145 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term798 A s a f x n.
Proof. exact (@lem4723142 A s a f x n (@lem4723134 A s a f x n)). Qed.
Lemma lem4723146 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term798 A s a f x n.
Proof. exact (@lem4723145 A s a f x n). Qed.
Lemma lem4723224 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4723225 : term801 = term802.
Proof. exact (@lem4723224 term803). Qed.
Lemma lem4723230 : term804 = term804.
Proof. exact (eq_refl term804). Qed.
Lemma lem4723231 : term805 = term806.
Proof. exact (MK_COMB (@lem4723230) (@lem4723225)). Qed.
Lemma lem4723234 {A : Type'} : (term337 A) = (term337 A).
Proof. exact (eq_refl (term337 A)). Qed.
Lemma lem4723235 {A : Type'} : (term807 A) = (term808 A).
Proof. exact (MK_COMB (@lem4723234 A) (@lem4723231)). Qed.
Lemma lem4723238 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term809 A f x n) = (term809 A f x n).
Proof. exact (eq_refl (term809 A f x n)). Qed.
Lemma lem4723239 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term810 A f x n) = (term811 A f x n).
Proof. exact (MK_COMB (@lem4723238 A f x n) (@lem4723235 A)). Qed.
Lemma lem4723242 {A : Type'} (a : A) (x : A) : (term812 A a x) = (term812 A a x).
Proof. exact (eq_refl (term812 A a x)). Qed.
Lemma lem4723243 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term813 A a f x n) = (term814 A a f x n).
Proof. exact (MK_COMB (@lem4723242 A a x) (@lem4723239 A f x n)). Qed.
Lemma lem4723246 {A : Type'} (x : A) (s : A -> Prop) : (term251 A x s) = (term251 A x s).
Proof. exact (eq_refl (term251 A x s)). Qed.
Lemma lem4723247 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term815 A s a f x n) = (term816 A s a f x n).
Proof. exact (MK_COMB (@lem4723246 A x s) (@lem4723243 A a f x n)). Qed.
Lemma lem4723250 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term347 A n f s a) = (term347 A n f s a).
Proof. exact (eq_refl (term347 A n f s a)). Qed.
Lemma lem4723251 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term817 A s a f x n) = (term818 A s a f x n).
Proof. exact (MK_COMB (@lem4723250 A n f s a) (@lem4723247 A s a f x n)). Qed.
Lemma lem4723254 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term255 A s a n) = (term255 A s a n).
Proof. exact (eq_refl (term255 A s a n)). Qed.
Lemma lem4723255 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term819 A s a f x n) = (term820 A s a f x n).
Proof. exact (MK_COMB (@lem4723254 A s a n) (@lem4723251 A s a f x n)). Qed.
Lemma lem4723258 {A : Type'} (a : A) (s : A -> Prop) : (term251 A a s) = (term251 A a s).
Proof. exact (eq_refl (term251 A a s)). Qed.
Lemma lem4723259 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term797 A s a f x n) = (term821 A s a f x n).
Proof. exact (MK_COMB (@lem4723258 A a s) (@lem4723255 A s a f x n)). Qed.
Lemma lem4723262 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term822 A a f x n) = (term823 A a f x n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4723259 A s a f x n)). Qed.
Lemma lem4723263 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4723264 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term824 A a f x n) = (term825 A a f x n).
Proof. exact (MK_COMB (@lem4723263 A) (@lem4723262 A a f x n)). Qed.
Lemma lem4723269 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term826 A f x n) = (term827 A f x n).
Proof. exact (fun_ext (fun a : A => @lem4723264 A a f x n)). Qed.
Lemma lem4723270 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4723271 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term828 A f x n) = (term829 A f x n).
Proof. exact (MK_COMB (@lem4723270 A) (@lem4723269 A f x n)). Qed.
Lemma lem4723276 {A : Type'} (x : A) (n : nat) : (term830 A x n) = (term831 A x n).
Proof. exact (fun_ext (fun f : nat -> A => @lem4723271 A f x n)). Qed.
Lemma lem4723277 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4723278 {A : Type'} (x : A) (n : nat) : (term832 A x n) = (term833 A x n).
Proof. exact (MK_COMB (@lem4723277 A) (@lem4723276 A x n)). Qed.
Lemma lem4723283 {A : Type'} (n : nat) : (term834 A n) = (term835 A n).
Proof. exact (fun_ext (fun x : A => @lem4723278 A x n)). Qed.
Lemma lem4723284 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4723285 {A : Type'} (n : nat) : (term836 A n) = (term837 A n).
Proof. exact (MK_COMB (@lem4723284 A) (@lem4723283 A n)). Qed.
Lemma lem4723290 {A : Type'} : (term838 A) = (term839 A).
Proof. exact (fun_ext (fun n : nat => @lem4723285 A n)). Qed.
Lemma lem4723291 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4723300 {A : Type'} : (term840 A) = (term841 A).
Proof. exact (MK_COMB (@lem4723291) (@lem4723290 A)). Qed.
Lemma lem4723303 (n : nat) : (term842 n) = (term842 n).
Proof. exact (eq_refl (term842 n)). Qed.
Lemma lem4723304 : term843 = term843.
Proof. exact (fun_ext (fun n : nat => @lem4723303 n)). Qed.
Lemma lem4723305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4723306 : term803 = term803.
Proof. exact (MK_COMB (@lem4723305) (@lem4723304)). Qed.
Lemma lem4723307 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4723308 : term802 = term802.
Proof. exact (MK_COMB (@lem4723307) (@lem4723306)). Qed.
Lemma lem4723319 (s : nat -> Prop) (x : nat) (y : nat) : ((term373 x s y) = (term374 s x y)) = ((term373 x s y) = (term374 s x y)).
Proof. exact (eq_refl ((term373 x s y) = (term374 s x y))). Qed.
Lemma lem4723320 (s : nat -> Prop) (x : nat) : (term375 s x) = (term375 s x).
Proof. exact (fun_ext (fun y : nat => @lem4723319 s x y)). Qed.
Lemma lem4723321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4723322 (s : nat -> Prop) (x : nat) : (term376 s x) = (term376 s x).
Proof. exact (MK_COMB (@lem4723321) (@lem4723320 s x)). Qed.
Lemma lem4723323 (s : nat -> Prop) : (term377 s) = (term377 s).
Proof. exact (fun_ext (fun x : nat => @lem4723322 s x)). Qed.
Lemma lem4723324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4723325 (s : nat -> Prop) : (term378 s) = (term378 s).
Proof. exact (MK_COMB (@lem4723324) (@lem4723323 s)). Qed.
Lemma lem4723326 : term379 = term379.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4723325 s)). Qed.
Lemma lem4723327 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4723328 : term324 = term324.
Proof. exact (MK_COMB (@lem4723327) (@lem4723326)). Qed.
Lemma lem4723329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4723330 : term804 = term804.
Proof. exact (MK_COMB (@lem4723329) (@lem4723328)). Qed.
Lemma lem4723331 : term806 = term806.
Proof. exact (MK_COMB (@lem4723330) (@lem4723308)). Qed.
Lemma lem4723342 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term380 A x s y) = (term381 A s x y)) = ((term380 A x s y) = (term381 A s x y)).
Proof. exact (eq_refl ((term380 A x s y) = (term381 A s x y))). Qed.
Lemma lem4723343 {A : Type'} (s : A -> Prop) (x : A) : (term382 A s x) = (term382 A s x).
Proof. exact (fun_ext (fun y : A => @lem4723342 A s x y)). Qed.
Lemma lem4723344 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4723345 {A : Type'} (s : A -> Prop) (x : A) : (term383 A s x) = (term383 A s x).
Proof. exact (MK_COMB (@lem4723344 A) (@lem4723343 A s x)). Qed.
Lemma lem4723346 {A : Type'} (s : A -> Prop) : (term384 A s) = (term384 A s).
Proof. exact (fun_ext (fun x : A => @lem4723345 A s x)). Qed.
Lemma lem4723347 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4723348 {A : Type'} (s : A -> Prop) : (term385 A s) = (term385 A s).
Proof. exact (MK_COMB (@lem4723347 A) (@lem4723346 A s)). Qed.
Lemma lem4723349 {A : Type'} : (term386 A) = (term386 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4723348 A s)). Qed.
Lemma lem4723350 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4723351 {A : Type'} : (term323 A) = (term323 A).
Proof. exact (MK_COMB (@lem4723350 A) (@lem4723349 A)). Qed.
Lemma lem4723352 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4723353 {A : Type'} : (term337 A) = (term337 A).
Proof. exact (MK_COMB (@lem4723352) (@lem4723351 A)). Qed.
Lemma lem4723354 {A : Type'} : (term808 A) = (term808 A).
Proof. exact (MK_COMB (@lem4723353 A) (@lem4723331)). Qed.
Lemma lem4723369 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term771 A f x m n) = (term771 A f x m n).
Proof. exact (eq_refl (term771 A f x m n)). Qed.
Lemma lem4723370 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term772 A f x n) = (term772 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4723369 A f x m n)). Qed.
Lemma lem4723371 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4723372 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term773 A f x n) = (term773 A f x n).
Proof. exact (MK_COMB (@lem4723371) (@lem4723370 A f x n)). Qed.
Lemma lem4723373 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4723374 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term796 A f x n) = (term796 A f x n).
Proof. exact (MK_COMB (@lem4723373) (@lem4723372 A f x n)). Qed.
Lemma lem4723375 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4723376 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term809 A f x n) = (term809 A f x n).
Proof. exact (MK_COMB (@lem4723375) (@lem4723374 A f x n)). Qed.
Lemma lem4723377 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term811 A f x n) = (term811 A f x n).
Proof. exact (MK_COMB (@lem4723376 A f x n) (@lem4723354 A)). Qed.
Lemma lem4723380 {A : Type'} (a : A) (x : A) : (term812 A a x) = (term812 A a x).
Proof. exact (eq_refl (term812 A a x)). Qed.
Lemma lem4723381 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term814 A a f x n) = (term814 A a f x n).
Proof. exact (MK_COMB (@lem4723380 A a x) (@lem4723377 A f x n)). Qed.
Lemma lem4723384 {A : Type'} (x : A) (s : A -> Prop) : (term251 A x s) = (term251 A x s).
Proof. exact (eq_refl (term251 A x s)). Qed.
Lemma lem4723385 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term816 A s a f x n) = (term816 A s a f x n).
Proof. exact (MK_COMB (@lem4723384 A x s) (@lem4723381 A a f x n)). Qed.
Lemma lem4723390 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term393 A n f m s a) = (term393 A n f m s a).
Proof. exact (eq_refl (term393 A n f m s a)). Qed.
Lemma lem4723391 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term394 A n f s a) = (term394 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4723390 A n f m s a)). Qed.
Lemma lem4723392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4723393 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term268 A n f s a) = (term268 A n f s a).
Proof. exact (MK_COMB (@lem4723392) (@lem4723391 A n f s a)). Qed.
Lemma lem4723394 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4723395 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term347 A n f s a) = (term347 A n f s a).
Proof. exact (MK_COMB (@lem4723394) (@lem4723393 A n f s a)). Qed.
Lemma lem4723396 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term818 A s a f x n) = (term818 A s a f x n).
Proof. exact (MK_COMB (@lem4723395 A n f s a) (@lem4723385 A s a f x n)). Qed.
Lemma lem4723399 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term255 A s a n) = (term255 A s a n).
Proof. exact (eq_refl (term255 A s a n)). Qed.
Lemma lem4723400 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term820 A s a f x n) = (term820 A s a f x n).
Proof. exact (MK_COMB (@lem4723399 A s a n) (@lem4723396 A s a f x n)). Qed.
Lemma lem4723403 {A : Type'} (a : A) (s : A -> Prop) : (term251 A a s) = (term251 A a s).
Proof. exact (eq_refl (term251 A a s)). Qed.
Lemma lem4723404 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term821 A s a f x n) = (term821 A s a f x n).
Proof. exact (MK_COMB (@lem4723403 A a s) (@lem4723400 A s a f x n)). Qed.
Lemma lem4723405 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term823 A a f x n) = (term823 A a f x n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4723404 A s a f x n)). Qed.
Lemma lem4723406 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4723407 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term825 A a f x n) = (term825 A a f x n).
Proof. exact (MK_COMB (@lem4723406 A) (@lem4723405 A a f x n)). Qed.
Lemma lem4723408 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term827 A f x n) = (term827 A f x n).
Proof. exact (fun_ext (fun a : A => @lem4723407 A a f x n)). Qed.
Lemma lem4723409 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4723410 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term829 A f x n) = (term829 A f x n).
Proof. exact (MK_COMB (@lem4723409 A) (@lem4723408 A f x n)). Qed.
Lemma lem4723411 {A : Type'} (x : A) (n : nat) : (term831 A x n) = (term831 A x n).
Proof. exact (fun_ext (fun f : nat -> A => @lem4723410 A f x n)). Qed.
Lemma lem4723412 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4723413 {A : Type'} (x : A) (n : nat) : (term833 A x n) = (term833 A x n).
Proof. exact (MK_COMB (@lem4723412 A) (@lem4723411 A x n)). Qed.
Lemma lem4723414 {A : Type'} (n : nat) : (term835 A n) = (term835 A n).
Proof. exact (fun_ext (fun x : A => @lem4723413 A x n)). Qed.
Lemma lem4723415 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4723416 {A : Type'} (n : nat) : (term837 A n) = (term837 A n).
Proof. exact (MK_COMB (@lem4723415 A) (@lem4723414 A n)). Qed.
Lemma lem4723417 {A : Type'} : (term839 A) = (term839 A).
Proof. exact (fun_ext (fun n : nat => @lem4723416 A n)). Qed.
Lemma lem4723418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4723419 {A : Type'} : (term841 A) = (term841 A).
Proof. exact (MK_COMB (@lem4723418) (@lem4723417 A)). Qed.
Lemma lem4723528 {A : Type'} : (term840 A) = (term841 A).
Proof. exact (TRANS (@lem4723300 A) (@lem4723419 A)). Qed.
Lemma lem4723529 {A : Type'} : (term841 A) = (term840 A).
Proof. exact (SYM (@lem4723528 A)). Qed.
Lemma lem4723532 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term268 A n f s a.
Proof. exact (h1). Qed.
Lemma lem4723535 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term796 A f x n) : term796 A f x n.
Proof. exact (h1). Qed.
Lemma lem4723536 {A : Type'} (h1 : term323 A) : term323 A.
Proof. exact (h1). Qed.
Lemma lem4723538 (h1 : term803) : term803.
Proof. exact (h1). Qed.
Lemma lem4723557 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term393 A n f m s a) = (term395 A n f m s a).
Proof. exact (@lem17265 (Peano.lt m n) (term396 A f m s a)). Qed.
Lemma lem4723558 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term394 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4723557 A n f m s a)). Qed.
Lemma lem4723559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4723612 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term268 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4723559) (@lem4723558 A n f s a)). Qed.
Lemma lem4723613 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4723612 A n f s a) (@lem4723532 A n f s a h1)). Qed.
Lemma lem4723625 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4723634 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term844 A n f m x) = (term845 A n f m x).
Proof. exact (@lem17362 (Peano.lt m n) ((f m) = x)). Qed.
Lemma lem4723639 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term757 A n f m x) = (term846 A n f m x).
Proof. exact (@lem17265 (Peano.lt m n) ((f m) = x)). Qed.
Lemma lem4723643 (m : nat) (n : nat) : (term618 m n) = (Peano.lt m n).
Proof. exact (@lem16933 (Peano.lt m n)). Qed.
Lemma lem4723645 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem4723650 (m : nat) (n : nat) : (term847 m n) = (term848 m n).
Proof. exact (@lem17362 (term312 m n) (m = n)). Qed.
Lemma lem4723651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4723652 (m : nat) (n : nat) : (term849 m n) = (term850 m n).
Proof. exact (MK_COMB (@lem4723651) (@lem4723643 m n)). Qed.
Lemma lem4723653 (m : nat) (n : nat) : (term851 m n) = (term852 m n).
Proof. exact (MK_COMB (@lem4723652 m n) (@lem4723645 m n)). Qed.
Lemma lem4723654 (m : nat) (n : nat) : (term770 m n) = (term851 m n).
Proof. exact (@lem17265 (term312 m n) (m = n)). Qed.
Lemma lem4723655 (m : nat) (n : nat) : (term770 m n) = (term852 m n).
Proof. exact (TRANS (@lem4723654 m n) (@lem4723653 m n)). Qed.
Lemma lem4723656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4723657 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term853 A n f m x) = (term854 A n f m x).
Proof. exact (MK_COMB (@lem4723656) (@lem4723634 A n f m x)). Qed.
Lemma lem4723658 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term855 A f x m n) = (term856 A f x m n).
Proof. exact (MK_COMB (@lem4723657 A n f m x) (@lem4723650 m n)). Qed.
Lemma lem4723659 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term857 A f x m n) = (term855 A f x m n).
Proof. exact (@lem17045 (term757 A n f m x) (term770 m n)). Qed.
Lemma lem4723660 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term857 A f x m n) = (term856 A f x m n).
Proof. exact (TRANS (@lem4723659 A f x m n) (@lem4723658 A f x m n)). Qed.
Lemma lem4723661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4723662 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term758 A n f m x) = (term858 A n f m x).
Proof. exact (MK_COMB (@lem4723661) (@lem4723639 A n f m x)). Qed.
Lemma lem4723663 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term771 A f x m n) = (term859 A f x m n).
Proof. exact (MK_COMB (@lem4723662 A n f m x) (@lem4723655 m n)). Qed.
Lemma lem4723664 (m' : nat) (m : nat) : (term860 m' m) = (term860 m' m).
Proof. exact (eq_refl (term860 m' m)). Qed.
Lemma lem4723666 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term861 A f x n m) = (term771 A f x m n).
Proof. exact (eq_refl (term861 A f x n m)). Qed.
Lemma lem4723667 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (n : nat) : (term861 A f x n m') = (term771 A f x m' n).
Proof. exact (eq_refl (term861 A f x n m')). Qed.
Lemma lem4723668 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (n : nat) : (term771 A f x m' n) = (term859 A f x m' n).
Proof. exact (@lem4723663 A f x m' n). Qed.
Lemma lem4723669 (P : nat -> Prop) : (term862 P) = (term863 P).
Proof. exact (@lem18393 nat P). Qed.
Lemma lem4723670 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term796 A f x n) = (term864 A f x n).
Proof. exact (@lem4723669 (term772 A f x n)). Qed.
Lemma lem4723671 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (n : nat) : (term861 A f x n m') = (term859 A f x m' n).
Proof. exact (TRANS (@lem4723667 A f x m' n) (@lem4723668 A f x m' n)). Qed.
Lemma lem4723672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4723673 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (n : nat) : (term865 A f x n m') = (term866 A f x m' n).
Proof. exact (MK_COMB (@lem4723672) (@lem4723671 A f x m' n)). Qed.
Lemma lem4723674 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term867 A f x n m' m) = (term868 A f x n m' m).
Proof. exact (MK_COMB (@lem4723673 A f x m' n) (@lem4723664 m' m)). Qed.
Lemma lem4723675 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term861 A f x n m) = (term859 A f x m n).
Proof. exact (TRANS (@lem4723666 A f x m n) (@lem4723663 A f x m n)). Qed.
Lemma lem4723676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4723677 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term865 A f x n m) = (term866 A f x m n).
Proof. exact (MK_COMB (@lem4723676) (@lem4723675 A f x m n)). Qed.
Lemma lem4723678 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term869 A f x n m' m) = (term870 A f x n m' m).
Proof. exact (MK_COMB (@lem4723677 A f x m n) (@lem4723674 A f x n m' m)). Qed.
Lemma lem4723679 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term871 A f x n m) = (term872 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4723678 A f x n m' m)). Qed.
Lemma lem4723680 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723681 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term873 A f x n m) = (term874 A f x n m).
Proof. exact (MK_COMB (@lem4723680) (@lem4723679 A f x n m)). Qed.
Lemma lem4723682 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term875 A f x n) = (term876 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4723681 A f x n m)). Qed.
Lemma lem4723683 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723684 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term877 A f x n) = (term878 A f x n).
Proof. exact (MK_COMB (@lem4723683) (@lem4723682 A f x n)). Qed.
Lemma lem4723685 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4723686 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term879 A f x n m) = (term857 A f x m n).
Proof. exact (MK_COMB (@lem4723685) (@lem4723666 A f x m n)). Qed.
Lemma lem4723687 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term879 A f x n m) = (term856 A f x m n).
Proof. exact (TRANS (@lem4723686 A f x m n) (@lem4723660 A f x m n)). Qed.
Lemma lem4723688 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term880 A f x n) = (term881 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4723687 A f x m n)). Qed.
Lemma lem4723689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4723690 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term882 A f x n) = (term883 A f x n).
Proof. exact (MK_COMB (@lem4723689) (@lem4723688 A f x n)). Qed.
Lemma lem4723691 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4723692 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term884 A f x n) = (term885 A f x n).
Proof. exact (MK_COMB (@lem4723691) (@lem4723690 A f x n)). Qed.
Lemma lem4723693 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term864 A f x n) = (term886 A f x n).
Proof. exact (MK_COMB (@lem4723692 A f x n) (@lem4723684 A f x n)). Qed.
Lemma lem4723694 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term796 A f x n) = (term886 A f x n).
Proof. exact (TRANS (@lem4723670 A f x n) (@lem4723693 A f x n)). Qed.
Lemma lem4723748 {A : Type'} (P : Prop) (Q : A -> Prop) : (term887 A P Q) = (term888 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem4723749 (P : Prop) (Q : nat -> Prop) : (term889 P Q) = (term890 P Q).
Proof. exact (@lem4723748 nat P Q). Qed.
Lemma lem4723750 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term891 A f x n m) = (term892 A f x n m).
Proof. exact (@lem4723749 (term859 A f x m n) (term893 A f x n m)). Qed.
Lemma lem4723751 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term894 A f x n m m') = (term868 A f x n m' m).
Proof. exact (eq_refl (term894 A f x n m m')). Qed.
Lemma lem4723752 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term866 A f x m n) = (term866 A f x m n).
Proof. exact (eq_refl (term866 A f x m n)). Qed.
Lemma lem4723753 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term895 A f x n m m') = (term870 A f x n m' m).
Proof. exact (MK_COMB (@lem4723752 A f x m n) (@lem4723751 A f x n m' m)). Qed.
Lemma lem4723754 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term896 A f x n m) = (term872 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4723753 A f x n m' m)). Qed.
Lemma lem4723755 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723756 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term891 A f x n m) = (term874 A f x n m).
Proof. exact (MK_COMB (@lem4723755) (@lem4723754 A f x n m)). Qed.
Lemma lem4723757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4723758 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term897 A f x n m) = (term898 A f x n m).
Proof. exact (MK_COMB (@lem4723757) (@lem4723756 A f x n m)). Qed.
Lemma lem4723759 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term894 A f x n m m') = (term868 A f x n m' m).
Proof. exact (eq_refl (term894 A f x n m m')). Qed.
Lemma lem4723760 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term899 A f x n m) = (term893 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4723759 A f x n m' m)). Qed.
Lemma lem4723761 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723762 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term900 A f x n m) = (term901 A f x n m).
Proof. exact (MK_COMB (@lem4723761) (@lem4723760 A f x n m)). Qed.
Lemma lem4723763 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term866 A f x m n) = (term866 A f x m n).
Proof. exact (eq_refl (term866 A f x m n)). Qed.
Lemma lem4723764 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term892 A f x n m) = (term902 A f x n m).
Proof. exact (MK_COMB (@lem4723763 A f x m n) (@lem4723762 A f x n m)). Qed.
Lemma lem4723765 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : ((term891 A f x n m) = (term892 A f x n m)) = ((term874 A f x n m) = (term902 A f x n m)).
Proof. exact (MK_COMB (@lem4723758 A f x n m) (@lem4723764 A f x n m)). Qed.
Lemma lem4723766 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term874 A f x n m) = (term902 A f x n m).
Proof. exact (EQ_MP (@lem4723765 A f x n m) (@lem4723750 A f x n m)). Qed.
Lemma lem4723815 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term876 A f x n) = (term903 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4723766 A f x n m)). Qed.
Lemma lem4723816 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723817 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term878 A f x n) = (term904 A f x n).
Proof. exact (MK_COMB (@lem4723816) (@lem4723815 A f x n)). Qed.
Lemma lem4723866 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term885 A f x n) = (term885 A f x n).
Proof. exact (eq_refl (term885 A f x n)). Qed.
Lemma lem4723867 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term886 A f x n) = (term905 A f x n).
Proof. exact (MK_COMB (@lem4723866 A f x n) (@lem4723817 A f x n)). Qed.
Lemma lem4723869 {A : Type'} (P : Prop) (Q : A -> Prop) : (term888 A P Q) = (term887 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4723870 (P : Prop) (Q : nat -> Prop) : (term890 P Q) = (term889 P Q).
Proof. exact (@lem4723869 nat P Q). Qed.
Lemma lem4723871 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term892 A f x n m) = (term891 A f x n m).
Proof. exact (@lem4723870 (term859 A f x m n) (term893 A f x n m)). Qed.
Lemma lem4723872 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term894 A f x n m m') = (term868 A f x n m' m).
Proof. exact (eq_refl (term894 A f x n m m')). Qed.
Lemma lem4723873 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term899 A f x n m) = (term893 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4723872 A f x n m' m)). Qed.
Lemma lem4723874 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723875 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term900 A f x n m) = (term901 A f x n m).
Proof. exact (MK_COMB (@lem4723874) (@lem4723873 A f x n m)). Qed.
Lemma lem4723876 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term866 A f x m n) = (term866 A f x m n).
Proof. exact (eq_refl (term866 A f x m n)). Qed.
Lemma lem4723877 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term892 A f x n m) = (term902 A f x n m).
Proof. exact (MK_COMB (@lem4723876 A f x m n) (@lem4723875 A f x n m)). Qed.
Lemma lem4723878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4723879 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term906 A f x n m) = (term907 A f x n m).
Proof. exact (MK_COMB (@lem4723878) (@lem4723877 A f x n m)). Qed.
Lemma lem4723880 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term894 A f x n m m') = (term868 A f x n m' m).
Proof. exact (eq_refl (term894 A f x n m m')). Qed.
Lemma lem4723881 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term866 A f x m n) = (term866 A f x m n).
Proof. exact (eq_refl (term866 A f x m n)). Qed.
Lemma lem4723882 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term895 A f x n m m') = (term870 A f x n m' m).
Proof. exact (MK_COMB (@lem4723881 A f x m n) (@lem4723880 A f x n m' m)). Qed.
Lemma lem4723883 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term896 A f x n m) = (term872 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4723882 A f x n m' m)). Qed.
Lemma lem4723884 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723885 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term891 A f x n m) = (term874 A f x n m).
Proof. exact (MK_COMB (@lem4723884) (@lem4723883 A f x n m)). Qed.
Lemma lem4723886 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : ((term892 A f x n m) = (term891 A f x n m)) = ((term902 A f x n m) = (term874 A f x n m)).
Proof. exact (MK_COMB (@lem4723879 A f x n m) (@lem4723885 A f x n m)). Qed.
Lemma lem4723887 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term902 A f x n m) = (term874 A f x n m).
Proof. exact (EQ_MP (@lem4723886 A f x n m) (@lem4723871 A f x n m)). Qed.
Lemma lem4723888 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term903 A f x n) = (term876 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4723887 A f x n m)). Qed.
Lemma lem4723889 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723890 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term904 A f x n) = (term878 A f x n).
Proof. exact (MK_COMB (@lem4723889) (@lem4723888 A f x n)). Qed.
Lemma lem4723891 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term885 A f x n) = (term885 A f x n).
Proof. exact (eq_refl (term885 A f x n)). Qed.
Lemma lem4723892 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term905 A f x n) = (term886 A f x n).
Proof. exact (MK_COMB (@lem4723891 A f x n) (@lem4723890 A f x n)). Qed.
Lemma lem4723894 {A : Type'} (P : Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4723895 (P : Prop) (Q : nat -> Prop) : (term470 P Q) = (term471 P Q).
Proof. exact (@lem4723894 nat P Q). Qed.
Lemma lem4723896 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term908 A f x n) = (term909 A f x n).
Proof. exact (@lem4723895 (term883 A f x n) (term876 A f x n)). Qed.
Lemma lem4723897 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term910 A f x n m) = (term874 A f x n m).
Proof. exact (eq_refl (term910 A f x n m)). Qed.
Lemma lem4723898 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term911 A f x n) = (term876 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4723897 A f x n m)). Qed.
Lemma lem4723899 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723900 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term912 A f x n) = (term878 A f x n).
Proof. exact (MK_COMB (@lem4723899) (@lem4723898 A f x n)). Qed.
Lemma lem4723901 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term885 A f x n) = (term885 A f x n).
Proof. exact (eq_refl (term885 A f x n)). Qed.
Lemma lem4723902 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term908 A f x n) = (term886 A f x n).
Proof. exact (MK_COMB (@lem4723901 A f x n) (@lem4723900 A f x n)). Qed.
Lemma lem4723903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4723904 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term913 A f x n) = (term914 A f x n).
Proof. exact (MK_COMB (@lem4723903) (@lem4723902 A f x n)). Qed.
Lemma lem4723905 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term910 A f x n m) = (term874 A f x n m).
Proof. exact (eq_refl (term910 A f x n m)). Qed.
Lemma lem4723906 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term885 A f x n) = (term885 A f x n).
Proof. exact (eq_refl (term885 A f x n)). Qed.
Lemma lem4723907 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term915 A f x n m) = (term916 A f x n m).
Proof. exact (MK_COMB (@lem4723906 A f x n) (@lem4723905 A f x n m)). Qed.
Lemma lem4723908 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term917 A f x n) = (term918 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4723907 A f x n m)). Qed.
Lemma lem4723909 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723910 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term909 A f x n) = (term919 A f x n).
Proof. exact (MK_COMB (@lem4723909) (@lem4723908 A f x n)). Qed.
Lemma lem4723911 {A : Type'} (f : nat -> A) (x : A) (n : nat) : ((term908 A f x n) = (term909 A f x n)) = ((term886 A f x n) = (term919 A f x n)).
Proof. exact (MK_COMB (@lem4723904 A f x n) (@lem4723910 A f x n)). Qed.
Lemma lem4723912 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term886 A f x n) = (term919 A f x n).
Proof. exact (EQ_MP (@lem4723911 A f x n) (@lem4723896 A f x n)). Qed.
Lemma lem4723914 {A : Type'} (P : Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4723915 (P : Prop) (Q : nat -> Prop) : (term470 P Q) = (term471 P Q).
Proof. exact (@lem4723914 nat P Q). Qed.
Lemma lem4723916 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term920 A f x n m) = (term921 A f x n m).
Proof. exact (@lem4723915 (term883 A f x n) (term872 A f x n m)). Qed.
Lemma lem4723917 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term922 A f x n m m') = (term870 A f x n m' m).
Proof. exact (eq_refl (term922 A f x n m m')). Qed.
Lemma lem4723918 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term923 A f x n m) = (term872 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4723917 A f x n m' m)). Qed.
Lemma lem4723919 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723920 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term924 A f x n m) = (term874 A f x n m).
Proof. exact (MK_COMB (@lem4723919) (@lem4723918 A f x n m)). Qed.
Lemma lem4723921 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term885 A f x n) = (term885 A f x n).
Proof. exact (eq_refl (term885 A f x n)). Qed.
Lemma lem4723922 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term920 A f x n m) = (term916 A f x n m).
Proof. exact (MK_COMB (@lem4723921 A f x n) (@lem4723920 A f x n m)). Qed.
Lemma lem4723923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4723924 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term925 A f x n m) = (term926 A f x n m).
Proof. exact (MK_COMB (@lem4723923) (@lem4723922 A f x n m)). Qed.
Lemma lem4723925 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term922 A f x n m m') = (term870 A f x n m' m).
Proof. exact (eq_refl (term922 A f x n m m')). Qed.
Lemma lem4723926 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term885 A f x n) = (term885 A f x n).
Proof. exact (eq_refl (term885 A f x n)). Qed.
Lemma lem4723927 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term927 A f x n m m') = (term928 A f x n m' m).
Proof. exact (MK_COMB (@lem4723926 A f x n) (@lem4723925 A f x n m' m)). Qed.
Lemma lem4723928 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term929 A f x n m) = (term930 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4723927 A f x n m' m)). Qed.
Lemma lem4723929 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723930 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term921 A f x n m) = (term931 A f x n m).
Proof. exact (MK_COMB (@lem4723929) (@lem4723928 A f x n m)). Qed.
Lemma lem4723931 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : ((term920 A f x n m) = (term921 A f x n m)) = ((term916 A f x n m) = (term931 A f x n m)).
Proof. exact (MK_COMB (@lem4723924 A f x n m) (@lem4723930 A f x n m)). Qed.
Lemma lem4723932 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term916 A f x n m) = (term931 A f x n m).
Proof. exact (EQ_MP (@lem4723931 A f x n m) (@lem4723916 A f x n m)). Qed.
Lemma lem4723933 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term918 A f x n) = (term932 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4723932 A f x n m)). Qed.
Lemma lem4723934 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4723935 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term919 A f x n) = (term933 A f x n).
Proof. exact (MK_COMB (@lem4723934) (@lem4723933 A f x n)). Qed.
Lemma lem4723936 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term886 A f x n) = (term933 A f x n).
Proof. exact (TRANS (@lem4723912 A f x n) (@lem4723935 A f x n)). Qed.
Lemma lem4723937 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term905 A f x n) = (term933 A f x n).
Proof. exact (TRANS (@lem4723892 A f x n) (@lem4723936 A f x n)). Qed.
Lemma lem4723938 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term886 A f x n) = (term933 A f x n).
Proof. exact (TRANS (@lem4723867 A f x n) (@lem4723937 A f x n)). Qed.
Lemma lem4723939 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term796 A f x n) = (term933 A f x n).
Proof. exact (TRANS (@lem4723694 A f x n) (@lem4723938 A f x n)). Qed.
Lemma lem4723940 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term796 A f x n) : term933 A f x n.
Proof. exact (EQ_MP (@lem4723939 A f x n) (@lem4723535 A f x n h1)). Qed.
Lemma lem4723948 {A : Type'} (x : A) (y : A) : (term512 A x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4723950 {A : Type'} (x : A) (s : A -> Prop) : (term513 A x s) = (term513 A x s).
Proof. exact (eq_refl (term513 A x s)). Qed.
Lemma lem4723951 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term514 A s x y) = (term515 A s x y).
Proof. exact (MK_COMB (@lem4723950 A x s) (@lem4723948 A x y)). Qed.
Lemma lem4723952 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term516 A s x y) = (term514 A s x y).
Proof. exact (@lem17045 (@IN A x s) (term9 A x y)). Qed.
Lemma lem4723953 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term516 A s x y) = (term515 A s x y).
Proof. exact (TRANS (@lem4723952 A s x y) (@lem4723951 A s x y)). Qed.
Lemma lem4723959 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term517 A s x y).
Proof. exact (eq_refl (term517 A s x y)). Qed.
Lemma lem4723961 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term518 A x s y) = (term518 A x s y).
Proof. exact (eq_refl (term518 A x s y)). Qed.
Lemma lem4723962 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term519 A s x y) = (term520 A s x y).
Proof. exact (MK_COMB (@lem4723961 A x s y) (@lem4723953 A s x y)). Qed.
Lemma lem4723963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4723964 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term521 A s x y) = (term522 A s x y).
Proof. exact (MK_COMB (@lem4723963) (@lem4723962 A s x y)). Qed.
Lemma lem4723965 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term523 A s x y) = (term524 A s x y).
Proof. exact (MK_COMB (@lem4723964 A s x y) (@lem4723959 A s x y)). Qed.
Lemma lem4723966 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term380 A x s y) = (term381 A s x y)) = (term523 A s x y).
Proof. exact (@lem17784 (term380 A x s y) (term381 A s x y)). Qed.
Lemma lem4723967 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term380 A x s y) = (term381 A s x y)) = (term524 A s x y).
Proof. exact (TRANS (@lem4723966 A s x y) (@lem4723965 A s x y)). Qed.
Lemma lem4723968 {A : Type'} (s : A -> Prop) (x : A) : (term382 A s x) = (term525 A s x).
Proof. exact (fun_ext (fun y : A => @lem4723967 A s x y)). Qed.
Lemma lem4723969 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4723970 {A : Type'} (s : A -> Prop) (x : A) : (term383 A s x) = (term526 A s x).
Proof. exact (MK_COMB (@lem4723969 A) (@lem4723968 A s x)). Qed.
Lemma lem4723971 {A : Type'} (s : A -> Prop) : (term384 A s) = (term527 A s).
Proof. exact (fun_ext (fun x : A => @lem4723970 A s x)). Qed.
Lemma lem4723972 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4723973 {A : Type'} (s : A -> Prop) : (term385 A s) = (term528 A s).
Proof. exact (MK_COMB (@lem4723972 A) (@lem4723971 A s)). Qed.
Lemma lem4723974 {A : Type'} : (term386 A) = (term529 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4723973 A s)). Qed.
Lemma lem4723975 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4723976 {A : Type'} : (term323 A) = (term530 A).
Proof. exact (MK_COMB (@lem4723975 A) (@lem4723974 A)). Qed.
Lemma lem4723986 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4723987 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (@lem4723986 A P Q). Qed.
Lemma lem4723988 {A : Type'} (s : A -> Prop) (x : A) : (term533 A s x) = (term534 A s x).
Proof. exact (@lem4723987 A (term535 A s x) (term536 A s x)). Qed.
Lemma lem4723989 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term537 A s x y) = (term520 A s x y).
Proof. exact (eq_refl (term537 A s x y)). Qed.
Lemma lem4723990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4723991 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term538 A s x y) = (term522 A s x y).
Proof. exact (MK_COMB (@lem4723990) (@lem4723989 A s x y)). Qed.
Lemma lem4723992 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term539 A s x y) = (term517 A s x y).
Proof. exact (eq_refl (term539 A s x y)). Qed.
Lemma lem4723993 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term540 A s x y) = (term524 A s x y).
Proof. exact (MK_COMB (@lem4723991 A s x y) (@lem4723992 A s x y)). Qed.
Lemma lem4723994 {A : Type'} (s : A -> Prop) (x : A) : (term541 A s x) = (term525 A s x).
Proof. exact (fun_ext (fun y : A => @lem4723993 A s x y)). Qed.
Lemma lem4723995 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4723996 {A : Type'} (s : A -> Prop) (x : A) : (term533 A s x) = (term526 A s x).
Proof. exact (MK_COMB (@lem4723995 A) (@lem4723994 A s x)). Qed.
Lemma lem4723997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4723998 {A : Type'} (s : A -> Prop) (x : A) : (term542 A s x) = (term543 A s x).
Proof. exact (MK_COMB (@lem4723997) (@lem4723996 A s x)). Qed.
Lemma lem4723999 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term537 A s x y) = (term520 A s x y).
Proof. exact (eq_refl (term537 A s x y)). Qed.
Lemma lem4724000 {A : Type'} (s : A -> Prop) (x : A) : (term544 A s x) = (term535 A s x).
Proof. exact (fun_ext (fun y : A => @lem4723999 A s x y)). Qed.
Lemma lem4724001 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724002 {A : Type'} (s : A -> Prop) (x : A) : (term545 A s x) = (term546 A s x).
Proof. exact (MK_COMB (@lem4724001 A) (@lem4724000 A s x)). Qed.
Lemma lem4724003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4724004 {A : Type'} (s : A -> Prop) (x : A) : (term547 A s x) = (term548 A s x).
Proof. exact (MK_COMB (@lem4724003) (@lem4724002 A s x)). Qed.
Lemma lem4724005 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term539 A s x y) = (term517 A s x y).
Proof. exact (eq_refl (term539 A s x y)). Qed.
Lemma lem4724006 {A : Type'} (s : A -> Prop) (x : A) : (term549 A s x) = (term536 A s x).
Proof. exact (fun_ext (fun y : A => @lem4724005 A s x y)). Qed.
Lemma lem4724007 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724008 {A : Type'} (s : A -> Prop) (x : A) : (term550 A s x) = (term551 A s x).
Proof. exact (MK_COMB (@lem4724007 A) (@lem4724006 A s x)). Qed.
Lemma lem4724009 {A : Type'} (s : A -> Prop) (x : A) : (term534 A s x) = (term552 A s x).
Proof. exact (MK_COMB (@lem4724004 A s x) (@lem4724008 A s x)). Qed.
Lemma lem4724010 {A : Type'} (s : A -> Prop) (x : A) : ((term533 A s x) = (term534 A s x)) = ((term526 A s x) = (term552 A s x)).
Proof. exact (MK_COMB (@lem4723998 A s x) (@lem4724009 A s x)). Qed.
Lemma lem4724011 {A : Type'} (s : A -> Prop) (x : A) : (term526 A s x) = (term552 A s x).
Proof. exact (EQ_MP (@lem4724010 A s x) (@lem4723988 A s x)). Qed.
Lemma lem4724108 {A : Type'} (s : A -> Prop) : (term527 A s) = (term553 A s).
Proof. exact (fun_ext (fun x : A => @lem4724011 A s x)). Qed.
Lemma lem4724109 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724110 {A : Type'} (s : A -> Prop) : (term528 A s) = (term554 A s).
Proof. exact (MK_COMB (@lem4724109 A) (@lem4724108 A s)). Qed.
Lemma lem4724112 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4724113 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (@lem4724112 A P Q). Qed.
Lemma lem4724114 {A : Type'} (s : A -> Prop) : (term555 A s) = (term556 A s).
Proof. exact (@lem4724113 A (term557 A s) (term558 A s)). Qed.
Lemma lem4724115 {A : Type'} (s : A -> Prop) (x : A) : (term559 A s x) = (term546 A s x).
Proof. exact (eq_refl (term559 A s x)). Qed.
Lemma lem4724116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4724117 {A : Type'} (s : A -> Prop) (x : A) : (term560 A s x) = (term548 A s x).
Proof. exact (MK_COMB (@lem4724116) (@lem4724115 A s x)). Qed.
Lemma lem4724118 {A : Type'} (s : A -> Prop) (x : A) : (term561 A s x) = (term551 A s x).
Proof. exact (eq_refl (term561 A s x)). Qed.
Lemma lem4724119 {A : Type'} (s : A -> Prop) (x : A) : (term562 A s x) = (term552 A s x).
Proof. exact (MK_COMB (@lem4724117 A s x) (@lem4724118 A s x)). Qed.
Lemma lem4724120 {A : Type'} (s : A -> Prop) : (term563 A s) = (term553 A s).
Proof. exact (fun_ext (fun x : A => @lem4724119 A s x)). Qed.
Lemma lem4724121 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724122 {A : Type'} (s : A -> Prop) : (term555 A s) = (term554 A s).
Proof. exact (MK_COMB (@lem4724121 A) (@lem4724120 A s)). Qed.
Lemma lem4724123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4724124 {A : Type'} (s : A -> Prop) : (term564 A s) = (term565 A s).
Proof. exact (MK_COMB (@lem4724123) (@lem4724122 A s)). Qed.
Lemma lem4724125 {A : Type'} (s : A -> Prop) (x : A) : (term559 A s x) = (term546 A s x).
Proof. exact (eq_refl (term559 A s x)). Qed.
Lemma lem4724126 {A : Type'} (s : A -> Prop) : (term566 A s) = (term557 A s).
Proof. exact (fun_ext (fun x : A => @lem4724125 A s x)). Qed.
Lemma lem4724127 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724128 {A : Type'} (s : A -> Prop) : (term567 A s) = (term568 A s).
Proof. exact (MK_COMB (@lem4724127 A) (@lem4724126 A s)). Qed.
Lemma lem4724129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4724130 {A : Type'} (s : A -> Prop) : (term569 A s) = (term570 A s).
Proof. exact (MK_COMB (@lem4724129) (@lem4724128 A s)). Qed.
Lemma lem4724131 {A : Type'} (s : A -> Prop) (x : A) : (term561 A s x) = (term551 A s x).
Proof. exact (eq_refl (term561 A s x)). Qed.
Lemma lem4724132 {A : Type'} (s : A -> Prop) : (term571 A s) = (term558 A s).
Proof. exact (fun_ext (fun x : A => @lem4724131 A s x)). Qed.
Lemma lem4724133 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724134 {A : Type'} (s : A -> Prop) : (term572 A s) = (term573 A s).
Proof. exact (MK_COMB (@lem4724133 A) (@lem4724132 A s)). Qed.
Lemma lem4724135 {A : Type'} (s : A -> Prop) : (term556 A s) = (term574 A s).
Proof. exact (MK_COMB (@lem4724130 A s) (@lem4724134 A s)). Qed.
Lemma lem4724136 {A : Type'} (s : A -> Prop) : ((term555 A s) = (term556 A s)) = ((term554 A s) = (term574 A s)).
Proof. exact (MK_COMB (@lem4724124 A s) (@lem4724135 A s)). Qed.
Lemma lem4724137 {A : Type'} (s : A -> Prop) : (term554 A s) = (term574 A s).
Proof. exact (EQ_MP (@lem4724136 A s) (@lem4724114 A s)). Qed.
Lemma lem4724242 {A : Type'} (s : A -> Prop) : (term528 A s) = (term574 A s).
Proof. exact (TRANS (@lem4724110 A s) (@lem4724137 A s)). Qed.
Lemma lem4724243 {A : Type'} : (term529 A) = (term575 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4724242 A s)). Qed.
Lemma lem4724244 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4724245 {A : Type'} : (term530 A) = (term576 A).
Proof. exact (MK_COMB (@lem4724244 A) (@lem4724243 A)). Qed.
Lemma lem4724247 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term531 A P Q) = (term532 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4724248 {A : Type'} (P : type686 A) (Q : type686 A) : (term577 A P Q) = (term578 A P Q).
Proof. exact (@lem4724247 (A -> Prop) P Q). Qed.
Lemma lem4724249 {A : Type'} : (term579 A) = (term580 A).
Proof. exact (@lem4724248 A (term581 A) (term582 A)). Qed.
Lemma lem4724250 {A : Type'} (s : A -> Prop) : (term583 A s) = (term568 A s).
Proof. exact (eq_refl (term583 A s)). Qed.
Lemma lem4724251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4724252 {A : Type'} (s : A -> Prop) : (term584 A s) = (term570 A s).
Proof. exact (MK_COMB (@lem4724251) (@lem4724250 A s)). Qed.
Lemma lem4724253 {A : Type'} (s : A -> Prop) : (term585 A s) = (term573 A s).
Proof. exact (eq_refl (term585 A s)). Qed.
Lemma lem4724254 {A : Type'} (s : A -> Prop) : (term586 A s) = (term574 A s).
Proof. exact (MK_COMB (@lem4724252 A s) (@lem4724253 A s)). Qed.
Lemma lem4724255 {A : Type'} : (term587 A) = (term575 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4724254 A s)). Qed.
Lemma lem4724256 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4724257 {A : Type'} : (term579 A) = (term576 A).
Proof. exact (MK_COMB (@lem4724256 A) (@lem4724255 A)). Qed.
Lemma lem4724258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4724259 {A : Type'} : (term588 A) = (term589 A).
Proof. exact (MK_COMB (@lem4724258) (@lem4724257 A)). Qed.
Lemma lem4724260 {A : Type'} (s : A -> Prop) : (term583 A s) = (term568 A s).
Proof. exact (eq_refl (term583 A s)). Qed.
Lemma lem4724261 {A : Type'} : (term590 A) = (term581 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4724260 A s)). Qed.
Lemma lem4724262 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4724263 {A : Type'} : (term591 A) = (term592 A).
Proof. exact (MK_COMB (@lem4724262 A) (@lem4724261 A)). Qed.
Lemma lem4724264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4724265 {A : Type'} : (term593 A) = (term594 A).
Proof. exact (MK_COMB (@lem4724264) (@lem4724263 A)). Qed.
Lemma lem4724266 {A : Type'} (s : A -> Prop) : (term585 A s) = (term573 A s).
Proof. exact (eq_refl (term585 A s)). Qed.
Lemma lem4724267 {A : Type'} : (term595 A) = (term582 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4724266 A s)). Qed.
Lemma lem4724268 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4724269 {A : Type'} : (term596 A) = (term597 A).
Proof. exact (MK_COMB (@lem4724268 A) (@lem4724267 A)). Qed.
Lemma lem4724270 {A : Type'} : (term580 A) = (term598 A).
Proof. exact (MK_COMB (@lem4724265 A) (@lem4724269 A)). Qed.
Lemma lem4724271 {A : Type'} : ((term579 A) = (term580 A)) = ((term576 A) = (term598 A)).
Proof. exact (MK_COMB (@lem4724259 A) (@lem4724270 A)). Qed.
Lemma lem4724272 {A : Type'} : (term576 A) = (term598 A).
Proof. exact (EQ_MP (@lem4724271 A) (@lem4724249 A)). Qed.
Lemma lem4724387 {A : Type'} : (term530 A) = (term598 A).
Proof. exact (TRANS (@lem4724245 A) (@lem4724272 A)). Qed.
Lemma lem4724388 {A : Type'} : (term323 A) = (term598 A).
Proof. exact (TRANS (@lem4723976 A) (@lem4724387 A)). Qed.
Lemma lem4724389 {A : Type'} (h1 : term323 A) : term598 A.
Proof. exact (EQ_MP (@lem4724388 A) (@lem4723536 A h1)). Qed.
Lemma lem4724839 (n : nat) : (term842 n) = (term842 n).
Proof. exact (eq_refl (term842 n)). Qed.
Lemma lem4724840 : term843 = term843.
Proof. exact (fun_ext (fun n : nat => @lem4724839 n)). Qed.
Lemma lem4724841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4724850 : term803 = term803.
Proof. exact (MK_COMB (@lem4724841) (@lem4724840)). Qed.
Lemma lem4724851 (h1 : term803) : term803.
Proof. exact (EQ_MP (@lem4724850) (@lem4723538 h1)). Qed.
Lemma lem4724852 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) (h1 : term931 A f x n m) : term931 A f x n m.
Proof. exact (h1). Qed.
Lemma lem4724853 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term928 A f x n m' m) : term928 A f x n m' m.
Proof. exact (h1). Qed.
Lemma lem4724890 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term395 A n f m s a) = (term395 A n f m s a).
Proof. exact (eq_refl (term395 A n f m s a)). Qed.
Lemma lem4724891 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term397 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4724890 A n f m s a)). Qed.
Lemma lem4724892 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4724893 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term398 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4724892) (@lem4724891 A n f s a)). Qed.
Lemma lem4724894 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4724893 A n f s a) (@lem4723613 A n f s a h1)). Qed.
Lemma lem4724906 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4724935 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term517 A s x y).
Proof. exact (eq_refl (term517 A s x y)). Qed.
Lemma lem4724936 {A : Type'} (s : A -> Prop) (x : A) : (term536 A s x) = (term536 A s x).
Proof. exact (fun_ext (fun y : A => @lem4724935 A s x y)). Qed.
Lemma lem4724937 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724938 {A : Type'} (s : A -> Prop) (x : A) : (term551 A s x) = (term551 A s x).
Proof. exact (MK_COMB (@lem4724937 A) (@lem4724936 A s x)). Qed.
Lemma lem4724939 {A : Type'} (s : A -> Prop) : (term558 A s) = (term558 A s).
Proof. exact (fun_ext (fun x : A => @lem4724938 A s x)). Qed.
Lemma lem4724940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724941 {A : Type'} (s : A -> Prop) : (term573 A s) = (term573 A s).
Proof. exact (MK_COMB (@lem4724940 A) (@lem4724939 A s)). Qed.
Lemma lem4724942 {A : Type'} : (term582 A) = (term582 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4724941 A s)). Qed.
Lemma lem4724943 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4724944 {A : Type'} : (term597 A) = (term597 A).
Proof. exact (MK_COMB (@lem4724943 A) (@lem4724942 A)). Qed.
Lemma lem4724971 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term520 A s x y) = (term520 A s x y).
Proof. exact (eq_refl (term520 A s x y)). Qed.
Lemma lem4724972 {A : Type'} (s : A -> Prop) (x : A) : (term535 A s x) = (term535 A s x).
Proof. exact (fun_ext (fun y : A => @lem4724971 A s x y)). Qed.
Lemma lem4724973 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724974 {A : Type'} (s : A -> Prop) (x : A) : (term546 A s x) = (term546 A s x).
Proof. exact (MK_COMB (@lem4724973 A) (@lem4724972 A s x)). Qed.
Lemma lem4724975 {A : Type'} (s : A -> Prop) : (term557 A s) = (term557 A s).
Proof. exact (fun_ext (fun x : A => @lem4724974 A s x)). Qed.
Lemma lem4724976 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4724977 {A : Type'} (s : A -> Prop) : (term568 A s) = (term568 A s).
Proof. exact (MK_COMB (@lem4724976 A) (@lem4724975 A s)). Qed.
Lemma lem4724978 {A : Type'} : (term581 A) = (term581 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4724977 A s)). Qed.
Lemma lem4724979 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4724980 {A : Type'} : (term592 A) = (term592 A).
Proof. exact (MK_COMB (@lem4724979 A) (@lem4724978 A)). Qed.
Lemma lem4724981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4724982 {A : Type'} : (term594 A) = (term594 A).
Proof. exact (MK_COMB (@lem4724981) (@lem4724980 A)). Qed.
Lemma lem4724983 {A : Type'} : (term598 A) = (term598 A).
Proof. exact (MK_COMB (@lem4724982 A) (@lem4724944 A)). Qed.
Lemma lem4724984 {A : Type'} (h1 : term323 A) : term598 A.
Proof. exact (EQ_MP (@lem4724983 A) (@lem4724389 A h1)). Qed.
Lemma lem4725069 (n : nat) : (term842 n) = (term842 n).
Proof. exact (eq_refl (term842 n)). Qed.
Lemma lem4725070 : term843 = term843.
Proof. exact (fun_ext (fun n : nat => @lem4725069 n)). Qed.
Lemma lem4725071 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4725072 : term803 = term803.
Proof. exact (MK_COMB (@lem4725071) (@lem4725070)). Qed.
Lemma lem4725073 (h1 : term803) : term803.
Proof. exact (EQ_MP (@lem4725072) (@lem4724851 h1)). Qed.
Lemma lem4725152 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term870 A f x n m' m) = (term870 A f x n m' m).
Proof. exact (eq_refl (term870 A f x n m' m)). Qed.
Lemma lem4725189 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term856 A f x m n) = (term856 A f x m n).
Proof. exact (eq_refl (term856 A f x m n)). Qed.
Lemma lem4725190 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term881 A f x n) = (term881 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4725189 A f x m n)). Qed.
Lemma lem4725191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4725192 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term883 A f x n) = (term883 A f x n).
Proof. exact (MK_COMB (@lem4725191) (@lem4725190 A f x n)). Qed.
Lemma lem4725193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4725194 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term885 A f x n) = (term885 A f x n).
Proof. exact (MK_COMB (@lem4725193) (@lem4725192 A f x n)). Qed.
Lemma lem4725195 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term928 A f x n m' m) = (term928 A f x n m' m).
Proof. exact (MK_COMB (@lem4725194 A f x n) (@lem4725152 A f x n m' m)). Qed.
Lemma lem4725196 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term928 A f x n m' m) : term928 A f x n m' m.
Proof. exact (EQ_MP (@lem4725195 A f x n m' m) (@lem4724853 A f x n m' m h1)). Qed.
Lemma lem4725199 {A : Type'} (h1 : term323 A) : term597 A.
Proof. exact (proj2 (@lem4724984 A h1)). Qed.
Lemma lem4725201 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : term883 A f x n.
Proof. exact (h1). Qed.
Lemma lem4725202 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term870 A f x n m' m.
Proof. exact (h1). Qed.
Lemma lem4725203 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term868 A f x n m' m.
Proof. exact (proj2 (@lem4725202 A f x n m' m h1)). Qed.
Lemma lem4725204 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term859 A f x m n.
Proof. exact (proj1 (@lem4725202 A f x n m' m h1)). Qed.
Lemma lem4725206 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term859 A f x m' n.
Proof. exact (proj1 (@lem4725203 A f x n m' m h1)). Qed.
Lemma lem4725207 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term852 m' n.
Proof. exact (proj2 (@lem4725206 A f x n m' m h1)). Qed.
Lemma lem4725208 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term846 A n f m' x.
Proof. exact (proj1 (@lem4725206 A f x n m' m h1)). Qed.
Lemma lem4725209 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term852 m n.
Proof. exact (proj2 (@lem4725204 A f x n m' m h1)). Qed.
Lemma lem4725210 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term846 A n f m x.
Proof. exact (proj1 (@lem4725204 A f x n m' m h1)). Qed.
Lemma lem4725271 (n : nat) : (term842 n) = (term842 n).
Proof. exact (eq_refl (term842 n)). Qed.
Lemma lem4725272 : term843 = term843.
Proof. exact (fun_ext (fun n : nat => @lem4725271 n)). Qed.
Lemma lem4725273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4725275 : term803 = term803.
Proof. exact (MK_COMB (@lem4725273) (@lem4725272)). Qed.
Lemma lem4725276 (h1 : term803) : term803.
Proof. exact (EQ_MP (@lem4725275) (@lem4725073 h1)). Qed.
Lemma lem4725399 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term856 A f x m n) = (term934 A f x m n).
Proof. exact (@lem19490 (term312 m n) (term845 A n f m x) (term860 m n)). Qed.
Lemma lem4725406 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term935 A f x m n) = (term936 A f x m n).
Proof. exact (@lem19699 (Peano.lt m n) (term937 A f m x) (term860 m n)). Qed.
Lemma lem4725413 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term938 A f x m n) = (term939 A f x m n).
Proof. exact (@lem19699 (Peano.lt m n) (term937 A f m x) (term312 m n)). Qed.
Lemma lem4725414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4725415 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term940 A f x m n) = (term941 A f x m n).
Proof. exact (MK_COMB (@lem4725414) (@lem4725413 A f x m n)). Qed.
Lemma lem4725416 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term934 A f x m n) = (term942 A f x m n).
Proof. exact (MK_COMB (@lem4725415 A f x m n) (@lem4725406 A f x m n)). Qed.
Lemma lem4725418 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term856 A f x m n) = (term942 A f x m n).
Proof. exact (TRANS (@lem4725399 A f x m n) (@lem4725416 A f x m n)). Qed.
Lemma lem4725419 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term881 A f x n) = (term943 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4725418 A f x m n)). Qed.
Lemma lem4725420 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4725422 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term883 A f x n) = (term944 A f x n).
Proof. exact (MK_COMB (@lem4725420) (@lem4725419 A f x n)). Qed.
Lemma lem4725423 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : term944 A f x n.
Proof. exact (EQ_MP (@lem4725422 A f x n) (@lem4725201 A f x n h1)). Qed.
Lemma lem4725583 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4725587 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4725739 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4725743 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4725903 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4725907 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4726067 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4726071 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4726239 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4726243 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4726259 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term395 A n f m s a) = (term395 A n f m s a).
Proof. exact (eq_refl (term395 A n f m s a)). Qed.
Lemma lem4726260 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term397 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4726259 A n f m s a)). Qed.
Lemma lem4726261 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4726263 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term398 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4726261) (@lem4726260 A n f s a)). Qed.
Lemma lem4726264 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4726263 A n f s a) (@lem4724894 A n f s a h1)). Qed.
Lemma lem4726272 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4726376 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term599 A s x y).
Proof. exact (@lem19490 (@IN A x s) (term474 A x s y) (term9 A x y)). Qed.
Lemma lem4726377 {A : Type'} (s : A -> Prop) (x : A) : (term536 A s x) = (term600 A s x).
Proof. exact (fun_ext (fun y : A => @lem4726376 A s x y)). Qed.
Lemma lem4726378 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4726379 {A : Type'} (s : A -> Prop) (x : A) : (term551 A s x) = (term601 A s x).
Proof. exact (MK_COMB (@lem4726378 A) (@lem4726377 A s x)). Qed.
Lemma lem4726380 {A : Type'} (s : A -> Prop) : (term558 A s) = (term602 A s).
Proof. exact (fun_ext (fun x : A => @lem4726379 A s x)). Qed.
Lemma lem4726381 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4726382 {A : Type'} (s : A -> Prop) : (term573 A s) = (term603 A s).
Proof. exact (MK_COMB (@lem4726381 A) (@lem4726380 A s)). Qed.
Lemma lem4726383 {A : Type'} : (term582 A) = (term604 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4726382 A s)). Qed.
Lemma lem4726384 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4726386 {A : Type'} : (term597 A) = (term605 A).
Proof. exact (MK_COMB (@lem4726384 A) (@lem4726383 A)). Qed.
Lemma lem4726387 {A : Type'} (h1 : term323 A) : term605 A.
Proof. exact (EQ_MP (@lem4726386 A) (@lem4725199 A h1)). Qed.
Lemma lem4726395 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4726399 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : (f m) = x.
Proof. exact (h1). Qed.
Lemma lem4726407 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4726423 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term395 A n f m s a) = (term395 A n f m s a).
Proof. exact (eq_refl (term395 A n f m s a)). Qed.
Lemma lem4726424 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term397 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4726423 A n f m s a)). Qed.
Lemma lem4726425 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4726427 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term398 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4726425) (@lem4726424 A n f s a)). Qed.
Lemma lem4726428 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4726427 A n f s a) (@lem4724894 A n f s a h1)). Qed.
Lemma lem4726436 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4726540 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term599 A s x y).
Proof. exact (@lem19490 (@IN A x s) (term474 A x s y) (term9 A x y)). Qed.
Lemma lem4726541 {A : Type'} (s : A -> Prop) (x : A) : (term536 A s x) = (term600 A s x).
Proof. exact (fun_ext (fun y : A => @lem4726540 A s x y)). Qed.
Lemma lem4726542 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4726543 {A : Type'} (s : A -> Prop) (x : A) : (term551 A s x) = (term601 A s x).
Proof. exact (MK_COMB (@lem4726542 A) (@lem4726541 A s x)). Qed.
Lemma lem4726544 {A : Type'} (s : A -> Prop) : (term558 A s) = (term602 A s).
Proof. exact (fun_ext (fun x : A => @lem4726543 A s x)). Qed.
Lemma lem4726545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4726546 {A : Type'} (s : A -> Prop) : (term573 A s) = (term603 A s).
Proof. exact (MK_COMB (@lem4726545 A) (@lem4726544 A s)). Qed.
Lemma lem4726547 {A : Type'} : (term582 A) = (term604 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4726546 A s)). Qed.
Lemma lem4726548 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4726550 {A : Type'} : (term597 A) = (term605 A).
Proof. exact (MK_COMB (@lem4726548 A) (@lem4726547 A)). Qed.
Lemma lem4726551 {A : Type'} (h1 : term323 A) : term605 A.
Proof. exact (EQ_MP (@lem4726550 A) (@lem4725199 A h1)). Qed.
Lemma lem4726559 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4726563 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : (f m) = x.
Proof. exact (h1). Qed.
Lemma lem4726587 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term395 A n f m s a) = (term395 A n f m s a).
Proof. exact (eq_refl (term395 A n f m s a)). Qed.
Lemma lem4726588 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term397 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4726587 A n f m s a)). Qed.
Lemma lem4726589 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4726591 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term398 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4726589) (@lem4726588 A n f s a)). Qed.
Lemma lem4726592 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4726591 A n f s a) (@lem4724894 A n f s a h1)). Qed.
Lemma lem4726600 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4726704 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term599 A s x y).
Proof. exact (@lem19490 (@IN A x s) (term474 A x s y) (term9 A x y)). Qed.
Lemma lem4726705 {A : Type'} (s : A -> Prop) (x : A) : (term536 A s x) = (term600 A s x).
Proof. exact (fun_ext (fun y : A => @lem4726704 A s x y)). Qed.
Lemma lem4726706 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4726707 {A : Type'} (s : A -> Prop) (x : A) : (term551 A s x) = (term601 A s x).
Proof. exact (MK_COMB (@lem4726706 A) (@lem4726705 A s x)). Qed.
Lemma lem4726708 {A : Type'} (s : A -> Prop) : (term558 A s) = (term602 A s).
Proof. exact (fun_ext (fun x : A => @lem4726707 A s x)). Qed.
Lemma lem4726709 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4726710 {A : Type'} (s : A -> Prop) : (term573 A s) = (term603 A s).
Proof. exact (MK_COMB (@lem4726709 A) (@lem4726708 A s)). Qed.
Lemma lem4726711 {A : Type'} : (term582 A) = (term604 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4726710 A s)). Qed.
Lemma lem4726712 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4726714 {A : Type'} : (term597 A) = (term605 A).
Proof. exact (MK_COMB (@lem4726712 A) (@lem4726711 A)). Qed.
Lemma lem4726715 {A : Type'} (h1 : term323 A) : term605 A.
Proof. exact (EQ_MP (@lem4726714 A) (@lem4725199 A h1)). Qed.
Lemma lem4726723 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4726727 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : (f m) = x.
Proof. exact (h1). Qed.
Lemma lem4726731 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4726735 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4726895 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4726899 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4726915 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term395 A n f m s a) = (term395 A n f m s a).
Proof. exact (eq_refl (term395 A n f m s a)). Qed.
Lemma lem4726916 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term397 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4726915 A n f m s a)). Qed.
Lemma lem4726917 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4726919 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term398 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4726917) (@lem4726916 A n f s a)). Qed.
Lemma lem4726920 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4726919 A n f s a) (@lem4724894 A n f s a h1)). Qed.
Lemma lem4726928 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4727032 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term599 A s x y).
Proof. exact (@lem19490 (@IN A x s) (term474 A x s y) (term9 A x y)). Qed.
Lemma lem4727033 {A : Type'} (s : A -> Prop) (x : A) : (term536 A s x) = (term600 A s x).
Proof. exact (fun_ext (fun y : A => @lem4727032 A s x y)). Qed.
Lemma lem4727034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4727035 {A : Type'} (s : A -> Prop) (x : A) : (term551 A s x) = (term601 A s x).
Proof. exact (MK_COMB (@lem4727034 A) (@lem4727033 A s x)). Qed.
Lemma lem4727036 {A : Type'} (s : A -> Prop) : (term558 A s) = (term602 A s).
Proof. exact (fun_ext (fun x : A => @lem4727035 A s x)). Qed.
Lemma lem4727037 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4727038 {A : Type'} (s : A -> Prop) : (term573 A s) = (term603 A s).
Proof. exact (MK_COMB (@lem4727037 A) (@lem4727036 A s)). Qed.
Lemma lem4727039 {A : Type'} : (term582 A) = (term604 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4727038 A s)). Qed.
Lemma lem4727040 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4727042 {A : Type'} : (term597 A) = (term605 A).
Proof. exact (MK_COMB (@lem4727040 A) (@lem4727039 A)). Qed.
Lemma lem4727043 {A : Type'} (h1 : term323 A) : term605 A.
Proof. exact (EQ_MP (@lem4727042 A) (@lem4725199 A h1)). Qed.
Lemma lem4727059 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4727063 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4727215 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4727223 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4727379 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4727387 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4727551 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4727555 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4727571 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term395 A n f m s a) = (term395 A n f m s a).
Proof. exact (eq_refl (term395 A n f m s a)). Qed.
Lemma lem4727572 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term397 A n f s a) = (term397 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4727571 A n f m s a)). Qed.
Lemma lem4727573 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4727575 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term398 A n f s a) = (term398 A n f s a).
Proof. exact (MK_COMB (@lem4727573) (@lem4727572 A n f s a)). Qed.
Lemma lem4727576 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term398 A n f s a.
Proof. exact (EQ_MP (@lem4727575 A n f s a) (@lem4724894 A n f s a h1)). Qed.
Lemma lem4727584 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4727688 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term517 A s x y) = (term599 A s x y).
Proof. exact (@lem19490 (@IN A x s) (term474 A x s y) (term9 A x y)). Qed.
Lemma lem4727689 {A : Type'} (s : A -> Prop) (x : A) : (term536 A s x) = (term600 A s x).
Proof. exact (fun_ext (fun y : A => @lem4727688 A s x y)). Qed.
Lemma lem4727690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4727691 {A : Type'} (s : A -> Prop) (x : A) : (term551 A s x) = (term601 A s x).
Proof. exact (MK_COMB (@lem4727690 A) (@lem4727689 A s x)). Qed.
Lemma lem4727692 {A : Type'} (s : A -> Prop) : (term558 A s) = (term602 A s).
Proof. exact (fun_ext (fun x : A => @lem4727691 A s x)). Qed.
Lemma lem4727693 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4727694 {A : Type'} (s : A -> Prop) : (term573 A s) = (term603 A s).
Proof. exact (MK_COMB (@lem4727693 A) (@lem4727692 A s)). Qed.
Lemma lem4727695 {A : Type'} : (term582 A) = (term604 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4727694 A s)). Qed.
Lemma lem4727696 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4727698 {A : Type'} : (term597 A) = (term605 A).
Proof. exact (MK_COMB (@lem4727696 A) (@lem4727695 A)). Qed.
Lemma lem4727699 {A : Type'} (h1 : term323 A) : term605 A.
Proof. exact (EQ_MP (@lem4727698 A) (@lem4725199 A h1)). Qed.
Lemma lem4727715 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4727719 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4727871 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4727879 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4728035 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4728043 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4728051 (_55748 : nat) (h1 : term803) : term945 _55748.
Proof. exact (@lem4725276 h1 _55748). Qed.
Lemma lem4728052 (_55748 : nat) : (term945 _55748) = (term842 _55748).
Proof. exact (eq_refl (term945 _55748)). Qed.
Lemma lem4728090 {A : Type'} (_55761 : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : term946 A f x n _55761.
Proof. exact (@lem4725423 A f x n h1 _55761). Qed.
Lemma lem4728091 {A : Type'} (f : nat -> A) (x : A) (_55761 : nat) (n : nat) : (term946 A f x n _55761) = (term942 A f x _55761 n).
Proof. exact (eq_refl (term946 A f x n _55761)). Qed.
Lemma lem4728092 {A : Type'} (_55761 : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : term942 A f x _55761 n.
Proof. exact (EQ_MP (@lem4728091 A f x _55761 n) (@lem4728090 A _55761 f x n h1)). Qed.
Lemma lem4728303 {A : Type'} (_55832 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term606 A n f s a _55832.
Proof. exact (@lem4726264 A n f s a h1 _55832). Qed.
Lemma lem4728304 {A : Type'} (n : nat) (f : nat -> A) (_55832 : nat) (s : A -> Prop) (a : A) : (term606 A n f s a _55832) = (term395 A n f _55832 s a).
Proof. exact (eq_refl (term606 A n f s a _55832)). Qed.
Lemma lem4728336 {A : Type'} (_55843 : A -> Prop) (h1 : term323 A) : term607 A _55843.
Proof. exact (@lem4726387 A h1 _55843). Qed.
Lemma lem4728337 {A : Type'} (_55843 : A -> Prop) : (term607 A _55843) = (term603 A _55843).
Proof. exact (eq_refl (term607 A _55843)). Qed.
Lemma lem4728338 {A : Type'} (_55843 : A -> Prop) (h1 : term323 A) : term603 A _55843.
Proof. exact (EQ_MP (@lem4728337 A _55843) (@lem4728336 A _55843 h1)). Qed.
Lemma lem4728339 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (h1 : term323 A) : term608 A _55843 _55844.
Proof. exact (@lem4728338 A _55843 h1 _55844). Qed.
Lemma lem4728340 {A : Type'} (_55843 : A -> Prop) (_55844 : A) : (term608 A _55843 _55844) = (term601 A _55843 _55844).
Proof. exact (eq_refl (term608 A _55843 _55844)). Qed.
Lemma lem4728341 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (h1 : term323 A) : term601 A _55843 _55844.
Proof. exact (EQ_MP (@lem4728340 A _55843 _55844) (@lem4728339 A _55843 _55844 h1)). Qed.
Lemma lem4728342 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (_55845 : A) (h1 : term323 A) : term609 A _55843 _55844 _55845.
Proof. exact (@lem4728341 A _55843 _55844 h1 _55845). Qed.
Lemma lem4728343 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (_55845 : A) : (term609 A _55843 _55844 _55845) = (term599 A _55843 _55844 _55845).
Proof. exact (eq_refl (term609 A _55843 _55844 _55845)). Qed.
Lemma lem4728344 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (_55845 : A) (h1 : term323 A) : term599 A _55843 _55844 _55845.
Proof. exact (EQ_MP (@lem4728343 A _55843 _55844 _55845) (@lem4728342 A _55843 _55844 _55845 h1)). Qed.
Lemma lem4728345 {A : Type'} (_55846 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term606 A n f s a _55846.
Proof. exact (@lem4726428 A n f s a h1 _55846). Qed.
Lemma lem4728346 {A : Type'} (n : nat) (f : nat -> A) (_55846 : nat) (s : A -> Prop) (a : A) : (term606 A n f s a _55846) = (term395 A n f _55846 s a).
Proof. exact (eq_refl (term606 A n f s a _55846)). Qed.
Lemma lem4728378 {A : Type'} (_55857 : A -> Prop) (h1 : term323 A) : term607 A _55857.
Proof. exact (@lem4726551 A h1 _55857). Qed.
Lemma lem4728379 {A : Type'} (_55857 : A -> Prop) : (term607 A _55857) = (term603 A _55857).
Proof. exact (eq_refl (term607 A _55857)). Qed.
Lemma lem4728380 {A : Type'} (_55857 : A -> Prop) (h1 : term323 A) : term603 A _55857.
Proof. exact (EQ_MP (@lem4728379 A _55857) (@lem4728378 A _55857 h1)). Qed.
Lemma lem4728381 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (h1 : term323 A) : term608 A _55857 _55858.
Proof. exact (@lem4728380 A _55857 h1 _55858). Qed.
Lemma lem4728382 {A : Type'} (_55857 : A -> Prop) (_55858 : A) : (term608 A _55857 _55858) = (term601 A _55857 _55858).
Proof. exact (eq_refl (term608 A _55857 _55858)). Qed.
Lemma lem4728383 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (h1 : term323 A) : term601 A _55857 _55858.
Proof. exact (EQ_MP (@lem4728382 A _55857 _55858) (@lem4728381 A _55857 _55858 h1)). Qed.
Lemma lem4728384 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (_55859 : A) (h1 : term323 A) : term609 A _55857 _55858 _55859.
Proof. exact (@lem4728383 A _55857 _55858 h1 _55859). Qed.
Lemma lem4728385 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (_55859 : A) : (term609 A _55857 _55858 _55859) = (term599 A _55857 _55858 _55859).
Proof. exact (eq_refl (term609 A _55857 _55858 _55859)). Qed.
Lemma lem4728386 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (_55859 : A) (h1 : term323 A) : term599 A _55857 _55858 _55859.
Proof. exact (EQ_MP (@lem4728385 A _55857 _55858 _55859) (@lem4728384 A _55857 _55858 _55859 h1)). Qed.
Lemma lem4728387 {A : Type'} (_55860 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term606 A n f s a _55860.
Proof. exact (@lem4726592 A n f s a h1 _55860). Qed.
Lemma lem4728388 {A : Type'} (n : nat) (f : nat -> A) (_55860 : nat) (s : A -> Prop) (a : A) : (term606 A n f s a _55860) = (term395 A n f _55860 s a).
Proof. exact (eq_refl (term606 A n f s a _55860)). Qed.
Lemma lem4728420 {A : Type'} (_55871 : A -> Prop) (h1 : term323 A) : term607 A _55871.
Proof. exact (@lem4726715 A h1 _55871). Qed.
Lemma lem4728421 {A : Type'} (_55871 : A -> Prop) : (term607 A _55871) = (term603 A _55871).
Proof. exact (eq_refl (term607 A _55871)). Qed.
Lemma lem4728422 {A : Type'} (_55871 : A -> Prop) (h1 : term323 A) : term603 A _55871.
Proof. exact (EQ_MP (@lem4728421 A _55871) (@lem4728420 A _55871 h1)). Qed.
Lemma lem4728423 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (h1 : term323 A) : term608 A _55871 _55872.
Proof. exact (@lem4728422 A _55871 h1 _55872). Qed.
Lemma lem4728424 {A : Type'} (_55871 : A -> Prop) (_55872 : A) : (term608 A _55871 _55872) = (term601 A _55871 _55872).
Proof. exact (eq_refl (term608 A _55871 _55872)). Qed.
Lemma lem4728425 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (h1 : term323 A) : term601 A _55871 _55872.
Proof. exact (EQ_MP (@lem4728424 A _55871 _55872) (@lem4728423 A _55871 _55872 h1)). Qed.
Lemma lem4728426 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (_55873 : A) (h1 : term323 A) : term609 A _55871 _55872 _55873.
Proof. exact (@lem4728425 A _55871 _55872 h1 _55873). Qed.
Lemma lem4728427 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (_55873 : A) : (term609 A _55871 _55872 _55873) = (term599 A _55871 _55872 _55873).
Proof. exact (eq_refl (term609 A _55871 _55872 _55873)). Qed.
Lemma lem4728428 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (_55873 : A) (h1 : term323 A) : term599 A _55871 _55872 _55873.
Proof. exact (EQ_MP (@lem4728427 A _55871 _55872 _55873) (@lem4728426 A _55871 _55872 _55873 h1)). Qed.
Lemma lem4728471 {A : Type'} (_55888 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term606 A n f s a _55888.
Proof. exact (@lem4726920 A n f s a h1 _55888). Qed.
Lemma lem4728472 {A : Type'} (n : nat) (f : nat -> A) (_55888 : nat) (s : A -> Prop) (a : A) : (term606 A n f s a _55888) = (term395 A n f _55888 s a).
Proof. exact (eq_refl (term606 A n f s a _55888)). Qed.
Lemma lem4728504 {A : Type'} (_55899 : A -> Prop) (h1 : term323 A) : term607 A _55899.
Proof. exact (@lem4727043 A h1 _55899). Qed.
Lemma lem4728505 {A : Type'} (_55899 : A -> Prop) : (term607 A _55899) = (term603 A _55899).
Proof. exact (eq_refl (term607 A _55899)). Qed.
Lemma lem4728506 {A : Type'} (_55899 : A -> Prop) (h1 : term323 A) : term603 A _55899.
Proof. exact (EQ_MP (@lem4728505 A _55899) (@lem4728504 A _55899 h1)). Qed.
Lemma lem4728507 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (h1 : term323 A) : term608 A _55899 _55900.
Proof. exact (@lem4728506 A _55899 h1 _55900). Qed.
Lemma lem4728508 {A : Type'} (_55899 : A -> Prop) (_55900 : A) : (term608 A _55899 _55900) = (term601 A _55899 _55900).
Proof. exact (eq_refl (term608 A _55899 _55900)). Qed.
Lemma lem4728509 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (h1 : term323 A) : term601 A _55899 _55900.
Proof. exact (EQ_MP (@lem4728508 A _55899 _55900) (@lem4728507 A _55899 _55900 h1)). Qed.
Lemma lem4728510 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (_55901 : A) (h1 : term323 A) : term609 A _55899 _55900 _55901.
Proof. exact (@lem4728509 A _55899 _55900 h1 _55901). Qed.
Lemma lem4728511 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (_55901 : A) : (term609 A _55899 _55900 _55901) = (term599 A _55899 _55900 _55901).
Proof. exact (eq_refl (term609 A _55899 _55900 _55901)). Qed.
Lemma lem4728512 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (_55901 : A) (h1 : term323 A) : term599 A _55899 _55900 _55901.
Proof. exact (EQ_MP (@lem4728511 A _55899 _55900 _55901) (@lem4728510 A _55899 _55900 _55901 h1)). Qed.
Lemma lem4728639 {A : Type'} (_55944 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term606 A n f s a _55944.
Proof. exact (@lem4727576 A n f s a h1 _55944). Qed.
Lemma lem4728640 {A : Type'} (n : nat) (f : nat -> A) (_55944 : nat) (s : A -> Prop) (a : A) : (term606 A n f s a _55944) = (term395 A n f _55944 s a).
Proof. exact (eq_refl (term606 A n f s a _55944)). Qed.
Lemma lem4728672 {A : Type'} (_55955 : A -> Prop) (h1 : term323 A) : term607 A _55955.
Proof. exact (@lem4727699 A h1 _55955). Qed.
Lemma lem4728673 {A : Type'} (_55955 : A -> Prop) : (term607 A _55955) = (term603 A _55955).
Proof. exact (eq_refl (term607 A _55955)). Qed.
Lemma lem4728674 {A : Type'} (_55955 : A -> Prop) (h1 : term323 A) : term603 A _55955.
Proof. exact (EQ_MP (@lem4728673 A _55955) (@lem4728672 A _55955 h1)). Qed.
Lemma lem4728675 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (h1 : term323 A) : term608 A _55955 _55956.
Proof. exact (@lem4728674 A _55955 h1 _55956). Qed.
Lemma lem4728676 {A : Type'} (_55955 : A -> Prop) (_55956 : A) : (term608 A _55955 _55956) = (term601 A _55955 _55956).
Proof. exact (eq_refl (term608 A _55955 _55956)). Qed.
Lemma lem4728677 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (h1 : term323 A) : term601 A _55955 _55956.
Proof. exact (EQ_MP (@lem4728676 A _55955 _55956) (@lem4728675 A _55955 _55956 h1)). Qed.
Lemma lem4728678 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (_55957 : A) (h1 : term323 A) : term609 A _55955 _55956 _55957.
Proof. exact (@lem4728677 A _55955 _55956 h1 _55957). Qed.
Lemma lem4728679 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (_55957 : A) : (term609 A _55955 _55956 _55957) = (term599 A _55955 _55956 _55957).
Proof. exact (eq_refl (term609 A _55955 _55956 _55957)). Qed.
Lemma lem4728680 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (_55957 : A) (h1 : term323 A) : term599 A _55955 _55956 _55957.
Proof. exact (EQ_MP (@lem4728679 A _55955 _55956 _55957) (@lem4728678 A _55955 _55956 _55957 h1)). Qed.
Lemma lem4728765 {A : Type'} (_55761 : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : term936 A f x _55761 n.
Proof. exact (proj2 (@lem4728092 A _55761 f x n h1)). Qed.
Lemma lem4728966 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4728968 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4729032 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4729034 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4729102 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4729104 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4729172 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4729174 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4729246 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4729248 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4729286 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4729312 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4729314 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : (f m) = x.
Proof. exact (h1). Qed.
Lemma lem4729318 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4729356 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4729382 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4729384 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : (f m) = x.
Proof. exact (h1). Qed.
Lemma lem4729426 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4729452 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4729454 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : (f m) = x.
Proof. exact (h1). Qed.
Lemma lem4729456 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4729458 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4729526 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4729528 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4729566 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4729596 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4729598 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4729660 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term860 m' m.
Proof. exact (proj2 (@lem4725203 A f x n m' m h1)). Qed.
Lemma lem4729662 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4729666 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4729732 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4729736 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4729806 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4729808 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4729846 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4729876 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4729878 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4729940 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term860 m' m.
Proof. exact (proj2 (@lem4725203 A f x n m' m h1)). Qed.
Lemma lem4729942 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4729946 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4730012 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4730016 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4730123 (_55748 : nat) (h1 : term803) : term842 _55748.
Proof. exact (EQ_MP (@lem4728052 _55748) (@lem4728051 _55748 h1)). Qed.
Lemma lem4730165 {A : Type'} (_55761 : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : term947 _55761 n.
Proof. exact (proj1 (@lem4728765 A _55761 f x n h1)). Qed.
Lemma lem4730428 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4730442 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4730651 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4730665 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4730872 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4730886 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4731109 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4731123 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4731329 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4731343 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4731566 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4731580 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4731801 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4731815 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4732008 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4732022 (m : nat) (n : nat) (h1 : term312 m n) : term312 m n.
Proof. exact (h1). Qed.
Lemma lem4732245 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4732259 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4732466 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4732480 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4732537 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : x = (f m').
Proof. exact (SYM (@lem4729318 A f m' x h1)). Qed.
Lemma lem4732593 {A : Type'} (_55832 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term395 A n f _55832 s a.
Proof. exact (EQ_MP (@lem4728304 A n f _55832 s a) (@lem4728303 A _55832 n f s a h1)). Qed.
Lemma lem4732607 {A : Type'} (a : A) : (term948 A a) = (term948 A a).
Proof. exact (eq_refl (term948 A a)). Qed.
Lemma lem4732608 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (term949 A a x) = (term950 A a f m').
Proof. exact (MK_COMB (@lem4732607 A a) (@lem4732537 A f m' x h1)). Qed.
Lemma lem4732609 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (term950 A a f m') = (a = (f m')).
Proof. exact (eq_refl (term950 A a f m')). Qed.
Lemma lem4732610 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term951 A a x).
Proof. exact (eq_refl (term951 A a x)). Qed.
Lemma lem4732611 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (term950 A a f m')) = ((term949 A a x) = (a = (f m'))).
Proof. exact (MK_COMB (@lem4732610 A a x) (@lem4732609 A a f m')). Qed.
Lemma lem4732612 {A : Type'} (a : A) (x : A) : (term949 A a x) = (a = x).
Proof. exact (eq_refl (term949 A a x)). Qed.
Lemma lem4732613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4732614 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term952 A a x).
Proof. exact (MK_COMB (@lem4732613) (@lem4732612 A a x)). Qed.
Lemma lem4732615 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (a = (f m')) = (a = (f m')).
Proof. exact (eq_refl (a = (f m'))). Qed.
Lemma lem4732616 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (a = (f m'))) = ((a = x) = (a = (f m'))).
Proof. exact (MK_COMB (@lem4732614 A a x) (@lem4732615 A a f m')). Qed.
Lemma lem4732617 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (term950 A a f m')) = ((a = x) = (a = (f m'))).
Proof. exact (TRANS (@lem4732611 A x a f m') (@lem4732616 A x a f m')). Qed.
Lemma lem4732618 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (a = x) = (a = (f m')).
Proof. exact (EQ_MP (@lem4732617 A x a f m') (@lem4732608 A a f m' x h1)). Qed.
Lemma lem4732619 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : a = (f m').
Proof. exact (EQ_MP (@lem4732618 A a f m' x h2) (@lem4729286 A a x h1)). Qed.
Lemma lem4732689 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4732690 {A : Type'} (f : nat -> A) (m : nat) : (term953 A f m) = (term953 A f m).
Proof. exact (eq_refl (term953 A f m)). Qed.
Lemma lem4732691 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (term954 A f m x) = (term955 A m f m').
Proof. exact (MK_COMB (@lem4732690 A f m) (@lem4732537 A f m' x h1)). Qed.
Lemma lem4732692 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) : (term955 A m f m') = ((f m) = (f m')).
Proof. exact (eq_refl (term955 A m f m')). Qed.
Lemma lem4732693 {A : Type'} (f : nat -> A) (m : nat) (x : A) : (term956 A f m x) = (term956 A f m x).
Proof. exact (eq_refl (term956 A f m x)). Qed.
Lemma lem4732694 {A : Type'} (x : A) (m : nat) (f : nat -> A) (m' : nat) : ((term954 A f m x) = (term955 A m f m')) = ((term954 A f m x) = ((f m) = (f m'))).
Proof. exact (MK_COMB (@lem4732693 A f m x) (@lem4732692 A m f m')). Qed.
Lemma lem4732695 {A : Type'} (f : nat -> A) (m : nat) (x : A) : (term954 A f m x) = ((f m) = x).
Proof. exact (eq_refl (term954 A f m x)). Qed.
Lemma lem4732696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4732697 {A : Type'} (f : nat -> A) (m : nat) (x : A) : (term956 A f m x) = (term957 A f m x).
Proof. exact (MK_COMB (@lem4732696) (@lem4732695 A f m x)). Qed.
Lemma lem4732698 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) : ((f m) = (f m')) = ((f m) = (f m')).
Proof. exact (eq_refl ((f m) = (f m'))). Qed.
Lemma lem4732699 {A : Type'} (x : A) (m : nat) (f : nat -> A) (m' : nat) : ((term954 A f m x) = ((f m) = (f m'))) = (((f m) = x) = ((f m) = (f m'))).
Proof. exact (MK_COMB (@lem4732697 A f m x) (@lem4732698 A m f m')). Qed.
Lemma lem4732700 {A : Type'} (x : A) (m : nat) (f : nat -> A) (m' : nat) : ((term954 A f m x) = (term955 A m f m')) = (((f m) = x) = ((f m) = (f m'))).
Proof. exact (TRANS (@lem4732694 A x m f m') (@lem4732699 A x m f m')). Qed.
Lemma lem4732701 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : ((f m) = x) = ((f m) = (f m')).
Proof. exact (EQ_MP (@lem4732700 A x m f m') (@lem4732691 A m f m' x h1)). Qed.
Lemma lem4732813 {A : Type'} (n : nat) (f : nat -> A) (_55832 : nat) (s : A -> Prop) : (term958 A n f _55832 s) = (term958 A n f _55832 s).
Proof. exact (eq_refl (term958 A n f _55832 s)). Qed.
Lemma lem4732814 {A : Type'} (n : nat) (_55832 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : (term959 A n f _55832 s a) = (term960 A n _55832 s f m').
Proof. exact (MK_COMB (@lem4732813 A n f _55832 s) (@lem4732619 A a f m' x h1 h2)). Qed.
Lemma lem4732815 {A : Type'} (n : nat) (_55832 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term960 A n _55832 s f m') = (term961 A n _55832 s f m').
Proof. exact (eq_refl (term960 A n _55832 s f m')). Qed.
Lemma lem4732816 {A : Type'} (n : nat) (f : nat -> A) (_55832 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55832 s a) = (term962 A n f _55832 s a).
Proof. exact (eq_refl (term962 A n f _55832 s a)). Qed.
Lemma lem4732817 {A : Type'} (a : A) (n : nat) (_55832 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : ((term959 A n f _55832 s a) = (term960 A n _55832 s f m')) = ((term959 A n f _55832 s a) = (term961 A n _55832 s f m')).
Proof. exact (MK_COMB (@lem4732816 A n f _55832 s a) (@lem4732815 A n _55832 s f m')). Qed.
Lemma lem4732818 {A : Type'} (n : nat) (f : nat -> A) (_55832 : nat) (s : A -> Prop) (a : A) : (term959 A n f _55832 s a) = (term395 A n f _55832 s a).
Proof. exact (eq_refl (term959 A n f _55832 s a)). Qed.
Lemma lem4732819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4732820 {A : Type'} (n : nat) (f : nat -> A) (_55832 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55832 s a) = (term614 A n f _55832 s a).
Proof. exact (MK_COMB (@lem4732819) (@lem4732818 A n f _55832 s a)). Qed.
Lemma lem4732821 {A : Type'} (n : nat) (_55832 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term961 A n _55832 s f m') = (term961 A n _55832 s f m').
Proof. exact (eq_refl (term961 A n _55832 s f m')). Qed.
Lemma lem4732822 {A : Type'} (a : A) (n : nat) (_55832 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : ((term959 A n f _55832 s a) = (term961 A n _55832 s f m')) = ((term395 A n f _55832 s a) = (term961 A n _55832 s f m')).
Proof. exact (MK_COMB (@lem4732820 A n f _55832 s a) (@lem4732821 A n _55832 s f m')). Qed.
Lemma lem4732823 {A : Type'} (a : A) (n : nat) (_55832 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : ((term959 A n f _55832 s a) = (term960 A n _55832 s f m')) = ((term395 A n f _55832 s a) = (term961 A n _55832 s f m')).
Proof. exact (TRANS (@lem4732817 A a n _55832 s f m') (@lem4732822 A a n _55832 s f m')). Qed.
Lemma lem4732824 {A : Type'} (n : nat) (_55832 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : (term395 A n f _55832 s a) = (term961 A n _55832 s f m').
Proof. exact (EQ_MP (@lem4732823 A a n _55832 s f m') (@lem4732814 A n _55832 s a f m' x h1 h2)). Qed.
Lemma lem4732825 {A : Type'} (_55832 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term961 A n _55832 s f m'.
Proof. exact (EQ_MP (@lem4732824 A n _55832 s a f m' x h2 h3) (@lem4732593 A _55832 n f s a h1)). Qed.
Lemma lem4732909 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4732965 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (_55845 : A) (h1 : term323 A) : term963 A _55843 _55844 _55845.
Proof. exact (proj2 (@lem4728344 A _55843 _55844 _55845 h1)). Qed.
Lemma lem4733077 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4733146 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4733160 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : (f m) = x.
Proof. exact (h1). Qed.
Lemma lem4733230 {A : Type'} (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : x = (f m).
Proof. exact (SYM (@lem4733160 A f m x h1)). Qed.
Lemma lem4733286 {A : Type'} (_55846 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term395 A n f _55846 s a.
Proof. exact (EQ_MP (@lem4728346 A n f _55846 s a) (@lem4728345 A _55846 n f s a h1)). Qed.
Lemma lem4733300 {A : Type'} (a : A) : (term948 A a) = (term948 A a).
Proof. exact (eq_refl (term948 A a)). Qed.
Lemma lem4733301 {A : Type'} (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : (term949 A a x) = (term950 A a f m).
Proof. exact (MK_COMB (@lem4733300 A a) (@lem4733230 A f m x h1)). Qed.
Lemma lem4733302 {A : Type'} (a : A) (f : nat -> A) (m : nat) : (term950 A a f m) = (a = (f m)).
Proof. exact (eq_refl (term950 A a f m)). Qed.
Lemma lem4733303 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term951 A a x).
Proof. exact (eq_refl (term951 A a x)). Qed.
Lemma lem4733304 {A : Type'} (x : A) (a : A) (f : nat -> A) (m : nat) : ((term949 A a x) = (term950 A a f m)) = ((term949 A a x) = (a = (f m))).
Proof. exact (MK_COMB (@lem4733303 A a x) (@lem4733302 A a f m)). Qed.
Lemma lem4733305 {A : Type'} (a : A) (x : A) : (term949 A a x) = (a = x).
Proof. exact (eq_refl (term949 A a x)). Qed.
Lemma lem4733306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4733307 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term952 A a x).
Proof. exact (MK_COMB (@lem4733306) (@lem4733305 A a x)). Qed.
Lemma lem4733308 {A : Type'} (a : A) (f : nat -> A) (m : nat) : (a = (f m)) = (a = (f m)).
Proof. exact (eq_refl (a = (f m))). Qed.
Lemma lem4733309 {A : Type'} (x : A) (a : A) (f : nat -> A) (m : nat) : ((term949 A a x) = (a = (f m))) = ((a = x) = (a = (f m))).
Proof. exact (MK_COMB (@lem4733307 A a x) (@lem4733308 A a f m)). Qed.
Lemma lem4733310 {A : Type'} (x : A) (a : A) (f : nat -> A) (m : nat) : ((term949 A a x) = (term950 A a f m)) = ((a = x) = (a = (f m))).
Proof. exact (TRANS (@lem4733304 A x a f m) (@lem4733309 A x a f m)). Qed.
Lemma lem4733311 {A : Type'} (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : (f m) = x) : (a = x) = (a = (f m)).
Proof. exact (EQ_MP (@lem4733310 A x a f m) (@lem4733301 A a f m x h1)). Qed.
Lemma lem4733312 {A : Type'} (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : a = x) (h2 : (f m) = x) : a = (f m).
Proof. exact (EQ_MP (@lem4733311 A a f m x h2) (@lem4733077 A a x h1)). Qed.
Lemma lem4733382 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4733493 {A : Type'} (n : nat) (f : nat -> A) (_55846 : nat) (s : A -> Prop) : (term958 A n f _55846 s) = (term958 A n f _55846 s).
Proof. exact (eq_refl (term958 A n f _55846 s)). Qed.
Lemma lem4733494 {A : Type'} (n : nat) (_55846 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : a = x) (h2 : (f m) = x) : (term959 A n f _55846 s a) = (term960 A n _55846 s f m).
Proof. exact (MK_COMB (@lem4733493 A n f _55846 s) (@lem4733312 A a f m x h1 h2)). Qed.
Lemma lem4733495 {A : Type'} (n : nat) (_55846 : nat) (s : A -> Prop) (f : nat -> A) (m : nat) : (term960 A n _55846 s f m) = (term961 A n _55846 s f m).
Proof. exact (eq_refl (term960 A n _55846 s f m)). Qed.
Lemma lem4733496 {A : Type'} (n : nat) (f : nat -> A) (_55846 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55846 s a) = (term962 A n f _55846 s a).
Proof. exact (eq_refl (term962 A n f _55846 s a)). Qed.
Lemma lem4733497 {A : Type'} (a : A) (n : nat) (_55846 : nat) (s : A -> Prop) (f : nat -> A) (m : nat) : ((term959 A n f _55846 s a) = (term960 A n _55846 s f m)) = ((term959 A n f _55846 s a) = (term961 A n _55846 s f m)).
Proof. exact (MK_COMB (@lem4733496 A n f _55846 s a) (@lem4733495 A n _55846 s f m)). Qed.
Lemma lem4733498 {A : Type'} (n : nat) (f : nat -> A) (_55846 : nat) (s : A -> Prop) (a : A) : (term959 A n f _55846 s a) = (term395 A n f _55846 s a).
Proof. exact (eq_refl (term959 A n f _55846 s a)). Qed.
Lemma lem4733499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4733500 {A : Type'} (n : nat) (f : nat -> A) (_55846 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55846 s a) = (term614 A n f _55846 s a).
Proof. exact (MK_COMB (@lem4733499) (@lem4733498 A n f _55846 s a)). Qed.
Lemma lem4733501 {A : Type'} (n : nat) (_55846 : nat) (s : A -> Prop) (f : nat -> A) (m : nat) : (term961 A n _55846 s f m) = (term961 A n _55846 s f m).
Proof. exact (eq_refl (term961 A n _55846 s f m)). Qed.
Lemma lem4733502 {A : Type'} (a : A) (n : nat) (_55846 : nat) (s : A -> Prop) (f : nat -> A) (m : nat) : ((term959 A n f _55846 s a) = (term961 A n _55846 s f m)) = ((term395 A n f _55846 s a) = (term961 A n _55846 s f m)).
Proof. exact (MK_COMB (@lem4733500 A n f _55846 s a) (@lem4733501 A n _55846 s f m)). Qed.
Lemma lem4733503 {A : Type'} (a : A) (n : nat) (_55846 : nat) (s : A -> Prop) (f : nat -> A) (m : nat) : ((term959 A n f _55846 s a) = (term960 A n _55846 s f m)) = ((term395 A n f _55846 s a) = (term961 A n _55846 s f m)).
Proof. exact (TRANS (@lem4733497 A a n _55846 s f m) (@lem4733502 A a n _55846 s f m)). Qed.
Lemma lem4733504 {A : Type'} (n : nat) (_55846 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : a = x) (h2 : (f m) = x) : (term395 A n f _55846 s a) = (term961 A n _55846 s f m).
Proof. exact (EQ_MP (@lem4733503 A a n _55846 s f m) (@lem4733494 A n _55846 s a f m x h1 h2)). Qed.
Lemma lem4733505 {A : Type'} (_55846 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m) = x) : term961 A n _55846 s f m.
Proof. exact (EQ_MP (@lem4733504 A n _55846 s a f m x h2 h3) (@lem4733286 A _55846 n f s a h1)). Qed.
Lemma lem4733589 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4733631 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (_55859 : A) (h1 : term323 A) : term963 A _55857 _55858 _55859.
Proof. exact (proj2 (@lem4728386 A _55857 _55858 _55859 h1)). Qed.
Lemma lem4733660 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : x = (f m').
Proof. exact (SYM (@lem4729458 A f m' x h1)). Qed.
Lemma lem4733730 {A : Type'} (a : A) : (term948 A a) = (term948 A a).
Proof. exact (eq_refl (term948 A a)). Qed.
Lemma lem4733731 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (term949 A a x) = (term950 A a f m').
Proof. exact (MK_COMB (@lem4733730 A a) (@lem4733660 A f m' x h1)). Qed.
Lemma lem4733732 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (term950 A a f m') = (a = (f m')).
Proof. exact (eq_refl (term950 A a f m')). Qed.
Lemma lem4733733 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term951 A a x).
Proof. exact (eq_refl (term951 A a x)). Qed.
Lemma lem4733734 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (term950 A a f m')) = ((term949 A a x) = (a = (f m'))).
Proof. exact (MK_COMB (@lem4733733 A a x) (@lem4733732 A a f m')). Qed.
Lemma lem4733735 {A : Type'} (a : A) (x : A) : (term949 A a x) = (a = x).
Proof. exact (eq_refl (term949 A a x)). Qed.
Lemma lem4733736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4733737 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term952 A a x).
Proof. exact (MK_COMB (@lem4733736) (@lem4733735 A a x)). Qed.
Lemma lem4733738 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (a = (f m')) = (a = (f m')).
Proof. exact (eq_refl (a = (f m'))). Qed.
Lemma lem4733739 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (a = (f m'))) = ((a = x) = (a = (f m'))).
Proof. exact (MK_COMB (@lem4733737 A a x) (@lem4733738 A a f m')). Qed.
Lemma lem4733740 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (term950 A a f m')) = ((a = x) = (a = (f m'))).
Proof. exact (TRANS (@lem4733734 A x a f m') (@lem4733739 A x a f m')). Qed.
Lemma lem4733741 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (a = x) = (a = (f m')).
Proof. exact (EQ_MP (@lem4733740 A x a f m') (@lem4733731 A a f m' x h1)). Qed.
Lemma lem4733742 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : a = (f m').
Proof. exact (EQ_MP (@lem4733741 A a f m' x h2) (@lem4729426 A a x h1)). Qed.
Lemma lem4733812 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4733813 {A : Type'} (f : nat -> A) (m : nat) : (term953 A f m) = (term953 A f m).
Proof. exact (eq_refl (term953 A f m)). Qed.
Lemma lem4733814 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (term954 A f m x) = (term955 A m f m').
Proof. exact (MK_COMB (@lem4733813 A f m) (@lem4733660 A f m' x h1)). Qed.
Lemma lem4733815 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) : (term955 A m f m') = ((f m) = (f m')).
Proof. exact (eq_refl (term955 A m f m')). Qed.
Lemma lem4733816 {A : Type'} (f : nat -> A) (m : nat) (x : A) : (term956 A f m x) = (term956 A f m x).
Proof. exact (eq_refl (term956 A f m x)). Qed.
Lemma lem4733817 {A : Type'} (x : A) (m : nat) (f : nat -> A) (m' : nat) : ((term954 A f m x) = (term955 A m f m')) = ((term954 A f m x) = ((f m) = (f m'))).
Proof. exact (MK_COMB (@lem4733816 A f m x) (@lem4733815 A m f m')). Qed.
Lemma lem4733818 {A : Type'} (f : nat -> A) (m : nat) (x : A) : (term954 A f m x) = ((f m) = x).
Proof. exact (eq_refl (term954 A f m x)). Qed.
Lemma lem4733819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4733820 {A : Type'} (f : nat -> A) (m : nat) (x : A) : (term956 A f m x) = (term957 A f m x).
Proof. exact (MK_COMB (@lem4733819) (@lem4733818 A f m x)). Qed.
Lemma lem4733821 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) : ((f m) = (f m')) = ((f m) = (f m')).
Proof. exact (eq_refl ((f m) = (f m'))). Qed.
Lemma lem4733822 {A : Type'} (x : A) (m : nat) (f : nat -> A) (m' : nat) : ((term954 A f m x) = ((f m) = (f m'))) = (((f m) = x) = ((f m) = (f m'))).
Proof. exact (MK_COMB (@lem4733820 A f m x) (@lem4733821 A m f m')). Qed.
Lemma lem4733823 {A : Type'} (x : A) (m : nat) (f : nat -> A) (m' : nat) : ((term954 A f m x) = (term955 A m f m')) = (((f m) = x) = ((f m) = (f m'))).
Proof. exact (TRANS (@lem4733817 A x m f m') (@lem4733822 A x m f m')). Qed.
Lemma lem4733824 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : ((f m) = x) = ((f m) = (f m')).
Proof. exact (EQ_MP (@lem4733823 A x m f m') (@lem4733814 A m f m' x h1)). Qed.
Lemma lem4733825 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m) = x) (h2 : (f m') = x) : (f m) = (f m').
Proof. exact (EQ_MP (@lem4733824 A m f m' x h2) (@lem4729454 A f m x h1)). Qed.
Lemma lem4733839 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4733951 {A : Type'} (_55860 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term395 A n f _55860 s a.
Proof. exact (EQ_MP (@lem4728388 A n f _55860 s a) (@lem4728387 A _55860 n f s a h1)). Qed.
Lemma lem4733965 {A : Type'} (a : A) (f : nat -> A) : (term964 A a f) = (term964 A a f).
Proof. exact (eq_refl (term964 A a f)). Qed.
Lemma lem4733966 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (n : nat) (h1 : m' = n) : (term965 A a f m') = (term965 A a f n).
Proof. exact (MK_COMB (@lem4733965 A a f) (@lem4733839 m' n h1)). Qed.
Lemma lem4733967 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term965 A a f n) = (a = (f n)).
Proof. exact (eq_refl (term965 A a f n)). Qed.
Lemma lem4733968 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (term966 A a f m') = (term966 A a f m').
Proof. exact (eq_refl (term966 A a f m')). Qed.
Lemma lem4733969 {A : Type'} (m' : nat) (a : A) (f : nat -> A) (n : nat) : ((term965 A a f m') = (term965 A a f n)) = ((term965 A a f m') = (a = (f n))).
Proof. exact (MK_COMB (@lem4733968 A a f m') (@lem4733967 A a f n)). Qed.
Lemma lem4733970 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (term965 A a f m') = (a = (f m')).
Proof. exact (eq_refl (term965 A a f m')). Qed.
Lemma lem4733971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4733972 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (term966 A a f m') = (term967 A a f m').
Proof. exact (MK_COMB (@lem4733971) (@lem4733970 A a f m')). Qed.
Lemma lem4733973 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (a = (f n)) = (a = (f n)).
Proof. exact (eq_refl (a = (f n))). Qed.
Lemma lem4733974 {A : Type'} (m' : nat) (a : A) (f : nat -> A) (n : nat) : ((term965 A a f m') = (a = (f n))) = ((a = (f m')) = (a = (f n))).
Proof. exact (MK_COMB (@lem4733972 A a f m') (@lem4733973 A a f n)). Qed.
Lemma lem4733975 {A : Type'} (m' : nat) (a : A) (f : nat -> A) (n : nat) : ((term965 A a f m') = (term965 A a f n)) = ((a = (f m')) = (a = (f n))).
Proof. exact (TRANS (@lem4733969 A m' a f n) (@lem4733974 A m' a f n)). Qed.
Lemma lem4733976 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (n : nat) (h1 : m' = n) : (a = (f m')) = (a = (f n)).
Proof. exact (EQ_MP (@lem4733975 A m' a f n) (@lem4733966 A a f m' n h1)). Qed.
Lemma lem4733977 {A : Type'} (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : a = x) (h2 : (f m') = x) (h3 : m' = n) : a = (f n).
Proof. exact (EQ_MP (@lem4733976 A a f m' n h3) (@lem4733742 A a f m' x h1 h2)). Qed.
Lemma lem4734046 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4734047 {A : Type'} (m : nat) (f : nat -> A) : (term968 A m f) = (term968 A m f).
Proof. exact (eq_refl (term968 A m f)). Qed.
Lemma lem4734048 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (n : nat) (h1 : m' = n) : (term969 A m f m') = (term969 A m f n).
Proof. exact (MK_COMB (@lem4734047 A m f) (@lem4733839 m' n h1)). Qed.
Lemma lem4734049 {A : Type'} (m : nat) (f : nat -> A) (n : nat) : (term969 A m f n) = ((f m) = (f n)).
Proof. exact (eq_refl (term969 A m f n)). Qed.
Lemma lem4734050 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) : (term970 A m f m') = (term970 A m f m').
Proof. exact (eq_refl (term970 A m f m')). Qed.
Lemma lem4734051 {A : Type'} (m' : nat) (m : nat) (f : nat -> A) (n : nat) : ((term969 A m f m') = (term969 A m f n)) = ((term969 A m f m') = ((f m) = (f n))).
Proof. exact (MK_COMB (@lem4734050 A m f m') (@lem4734049 A m f n)). Qed.
Lemma lem4734052 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) : (term969 A m f m') = ((f m) = (f m')).
Proof. exact (eq_refl (term969 A m f m')). Qed.
Lemma lem4734053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4734054 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) : (term970 A m f m') = (term971 A m f m').
Proof. exact (MK_COMB (@lem4734053) (@lem4734052 A m f m')). Qed.
Lemma lem4734055 {A : Type'} (m : nat) (f : nat -> A) (n : nat) : ((f m) = (f n)) = ((f m) = (f n)).
Proof. exact (eq_refl ((f m) = (f n))). Qed.
Lemma lem4734056 {A : Type'} (m' : nat) (m : nat) (f : nat -> A) (n : nat) : ((term969 A m f m') = ((f m) = (f n))) = (((f m) = (f m')) = ((f m) = (f n))).
Proof. exact (MK_COMB (@lem4734054 A m f m') (@lem4734055 A m f n)). Qed.
Lemma lem4734057 {A : Type'} (m' : nat) (m : nat) (f : nat -> A) (n : nat) : ((term969 A m f m') = (term969 A m f n)) = (((f m) = (f m')) = ((f m) = (f n))).
Proof. exact (TRANS (@lem4734051 A m' m f n) (@lem4734056 A m' m f n)). Qed.
Lemma lem4734058 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (n : nat) (h1 : m' = n) : ((f m) = (f m')) = ((f m) = (f n)).
Proof. exact (EQ_MP (@lem4734057 A m' m f n) (@lem4734048 A m f m' n h1)). Qed.
Lemma lem4734156 {A : Type'} (n : nat) (f : nat -> A) (_55860 : nat) (s : A -> Prop) : (term958 A n f _55860 s) = (term958 A n f _55860 s).
Proof. exact (eq_refl (term958 A n f _55860 s)). Qed.
Lemma lem4734157 {A : Type'} (_55860 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : a = x) (h2 : (f m') = x) (h3 : m' = n) : (term959 A n f _55860 s a) = (term972 A _55860 s f n).
Proof. exact (MK_COMB (@lem4734156 A n f _55860 s) (@lem4733977 A a f x m' n h1 h2 h3)). Qed.
Lemma lem4734158 {A : Type'} (_55860 : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : (term972 A _55860 s f n) = (term973 A _55860 s f n).
Proof. exact (eq_refl (term972 A _55860 s f n)). Qed.
Lemma lem4734159 {A : Type'} (n : nat) (f : nat -> A) (_55860 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55860 s a) = (term962 A n f _55860 s a).
Proof. exact (eq_refl (term962 A n f _55860 s a)). Qed.
Lemma lem4734160 {A : Type'} (a : A) (_55860 : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : ((term959 A n f _55860 s a) = (term972 A _55860 s f n)) = ((term959 A n f _55860 s a) = (term973 A _55860 s f n)).
Proof. exact (MK_COMB (@lem4734159 A n f _55860 s a) (@lem4734158 A _55860 s f n)). Qed.
Lemma lem4734161 {A : Type'} (n : nat) (f : nat -> A) (_55860 : nat) (s : A -> Prop) (a : A) : (term959 A n f _55860 s a) = (term395 A n f _55860 s a).
Proof. exact (eq_refl (term959 A n f _55860 s a)). Qed.
Lemma lem4734162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4734163 {A : Type'} (n : nat) (f : nat -> A) (_55860 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55860 s a) = (term614 A n f _55860 s a).
Proof. exact (MK_COMB (@lem4734162) (@lem4734161 A n f _55860 s a)). Qed.
Lemma lem4734164 {A : Type'} (_55860 : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : (term973 A _55860 s f n) = (term973 A _55860 s f n).
Proof. exact (eq_refl (term973 A _55860 s f n)). Qed.
Lemma lem4734165 {A : Type'} (a : A) (_55860 : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : ((term959 A n f _55860 s a) = (term973 A _55860 s f n)) = ((term395 A n f _55860 s a) = (term973 A _55860 s f n)).
Proof. exact (MK_COMB (@lem4734163 A n f _55860 s a) (@lem4734164 A _55860 s f n)). Qed.
Lemma lem4734166 {A : Type'} (a : A) (_55860 : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : ((term959 A n f _55860 s a) = (term972 A _55860 s f n)) = ((term395 A n f _55860 s a) = (term973 A _55860 s f n)).
Proof. exact (TRANS (@lem4734160 A a _55860 s f n) (@lem4734165 A a _55860 s f n)). Qed.
Lemma lem4734167 {A : Type'} (_55860 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : a = x) (h2 : (f m') = x) (h3 : m' = n) : (term395 A n f _55860 s a) = (term973 A _55860 s f n).
Proof. exact (EQ_MP (@lem4734166 A a _55860 s f n) (@lem4734157 A _55860 s a f x m' n h1 h2 h3)). Qed.
Lemma lem4734168 {A : Type'} (_55860 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) (h4 : m' = n) : term973 A _55860 s f n.
Proof. exact (EQ_MP (@lem4734167 A _55860 s a f x m' n h2 h3 h4) (@lem4733951 A _55860 n f s a h1)). Qed.
Lemma lem4734252 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4734294 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (_55873 : A) (h1 : term323 A) : term963 A _55871 _55872 _55873.
Proof. exact (proj2 (@lem4728428 A _55871 _55872 _55873 h1)). Qed.
Lemma lem4734488 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4734502 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4734709 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4734723 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4734780 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : x = (f m').
Proof. exact (SYM (@lem4729598 A f m' x h1)). Qed.
Lemma lem4734850 {A : Type'} (a : A) : (term948 A a) = (term948 A a).
Proof. exact (eq_refl (term948 A a)). Qed.
Lemma lem4734851 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (term949 A a x) = (term950 A a f m').
Proof. exact (MK_COMB (@lem4734850 A a) (@lem4734780 A f m' x h1)). Qed.
Lemma lem4734852 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (term950 A a f m') = (a = (f m')).
Proof. exact (eq_refl (term950 A a f m')). Qed.
Lemma lem4734853 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term951 A a x).
Proof. exact (eq_refl (term951 A a x)). Qed.
Lemma lem4734854 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (term950 A a f m')) = ((term949 A a x) = (a = (f m'))).
Proof. exact (MK_COMB (@lem4734853 A a x) (@lem4734852 A a f m')). Qed.
Lemma lem4734855 {A : Type'} (a : A) (x : A) : (term949 A a x) = (a = x).
Proof. exact (eq_refl (term949 A a x)). Qed.
Lemma lem4734856 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4734857 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term952 A a x).
Proof. exact (MK_COMB (@lem4734856) (@lem4734855 A a x)). Qed.
Lemma lem4734858 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (a = (f m')) = (a = (f m')).
Proof. exact (eq_refl (a = (f m'))). Qed.
Lemma lem4734859 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (a = (f m'))) = ((a = x) = (a = (f m'))).
Proof. exact (MK_COMB (@lem4734857 A a x) (@lem4734858 A a f m')). Qed.
Lemma lem4734860 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (term950 A a f m')) = ((a = x) = (a = (f m'))).
Proof. exact (TRANS (@lem4734854 A x a f m') (@lem4734859 A x a f m')). Qed.
Lemma lem4734861 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (a = x) = (a = (f m')).
Proof. exact (EQ_MP (@lem4734860 A x a f m') (@lem4734851 A a f m' x h1)). Qed.
Lemma lem4734960 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4735072 {A : Type'} (_55888 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term395 A n f _55888 s a.
Proof. exact (EQ_MP (@lem4728472 A n f _55888 s a) (@lem4728471 A _55888 n f s a h1)). Qed.
Lemma lem4735100 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : a = (f m').
Proof. exact (EQ_MP (@lem4734861 A a f m' x h2) (@lem4729566 A a x h1)). Qed.
Lemma lem4735182 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4735279 {A : Type'} (n : nat) (f : nat -> A) (_55888 : nat) (s : A -> Prop) : (term958 A n f _55888 s) = (term958 A n f _55888 s).
Proof. exact (eq_refl (term958 A n f _55888 s)). Qed.
Lemma lem4735280 {A : Type'} (n : nat) (_55888 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : (term959 A n f _55888 s a) = (term960 A n _55888 s f m').
Proof. exact (MK_COMB (@lem4735279 A n f _55888 s) (@lem4735100 A a f m' x h1 h2)). Qed.
Lemma lem4735281 {A : Type'} (n : nat) (_55888 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term960 A n _55888 s f m') = (term961 A n _55888 s f m').
Proof. exact (eq_refl (term960 A n _55888 s f m')). Qed.
Lemma lem4735282 {A : Type'} (n : nat) (f : nat -> A) (_55888 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55888 s a) = (term962 A n f _55888 s a).
Proof. exact (eq_refl (term962 A n f _55888 s a)). Qed.
Lemma lem4735283 {A : Type'} (a : A) (n : nat) (_55888 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : ((term959 A n f _55888 s a) = (term960 A n _55888 s f m')) = ((term959 A n f _55888 s a) = (term961 A n _55888 s f m')).
Proof. exact (MK_COMB (@lem4735282 A n f _55888 s a) (@lem4735281 A n _55888 s f m')). Qed.
Lemma lem4735284 {A : Type'} (n : nat) (f : nat -> A) (_55888 : nat) (s : A -> Prop) (a : A) : (term959 A n f _55888 s a) = (term395 A n f _55888 s a).
Proof. exact (eq_refl (term959 A n f _55888 s a)). Qed.
Lemma lem4735285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4735286 {A : Type'} (n : nat) (f : nat -> A) (_55888 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55888 s a) = (term614 A n f _55888 s a).
Proof. exact (MK_COMB (@lem4735285) (@lem4735284 A n f _55888 s a)). Qed.
Lemma lem4735287 {A : Type'} (n : nat) (_55888 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term961 A n _55888 s f m') = (term961 A n _55888 s f m').
Proof. exact (eq_refl (term961 A n _55888 s f m')). Qed.
Lemma lem4735288 {A : Type'} (a : A) (n : nat) (_55888 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : ((term959 A n f _55888 s a) = (term961 A n _55888 s f m')) = ((term395 A n f _55888 s a) = (term961 A n _55888 s f m')).
Proof. exact (MK_COMB (@lem4735286 A n f _55888 s a) (@lem4735287 A n _55888 s f m')). Qed.
Lemma lem4735289 {A : Type'} (a : A) (n : nat) (_55888 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : ((term959 A n f _55888 s a) = (term960 A n _55888 s f m')) = ((term395 A n f _55888 s a) = (term961 A n _55888 s f m')).
Proof. exact (TRANS (@lem4735283 A a n _55888 s f m') (@lem4735288 A a n _55888 s f m')). Qed.
Lemma lem4735290 {A : Type'} (n : nat) (_55888 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : (term395 A n f _55888 s a) = (term961 A n _55888 s f m').
Proof. exact (EQ_MP (@lem4735289 A a n _55888 s f m') (@lem4735280 A n _55888 s a f m' x h1 h2)). Qed.
Lemma lem4735291 {A : Type'} (_55888 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term961 A n _55888 s f m'.
Proof. exact (EQ_MP (@lem4735290 A n _55888 s a f m' x h2 h3) (@lem4735072 A _55888 n f s a h1)). Qed.
Lemma lem4735389 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4735417 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (_55901 : A) (h1 : term323 A) : term963 A _55899 _55900 _55901.
Proof. exact (proj2 (@lem4728512 A _55899 _55900 _55901 h1)). Qed.
Lemma lem4735572 (m : nat) : (term974 m) = (term974 m).
Proof. exact (eq_refl (term974 m)). Qed.
Lemma lem4735573 (m : nat) (m' : nat) (n : nat) (h1 : m' = n) : (term975 m m') = (term975 m n).
Proof. exact (MK_COMB (@lem4735572 m) (@lem4729666 m' n h1)). Qed.
Lemma lem4735574 (n : nat) (m : nat) : (term975 m n) = (term860 n m).
Proof. exact (eq_refl (term975 m n)). Qed.
Lemma lem4735575 (m : nat) (m' : nat) : (term976 m m') = (term976 m m').
Proof. exact (eq_refl (term976 m m')). Qed.
Lemma lem4735576 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term975 m n)) = ((term975 m m') = (term860 n m)).
Proof. exact (MK_COMB (@lem4735575 m m') (@lem4735574 n m)). Qed.
Lemma lem4735577 (m' : nat) (m : nat) : (term975 m m') = (term860 m' m).
Proof. exact (eq_refl (term975 m m')). Qed.
Lemma lem4735578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4735579 (m' : nat) (m : nat) : (term976 m m') = (term977 m' m).
Proof. exact (MK_COMB (@lem4735578) (@lem4735577 m' m)). Qed.
Lemma lem4735580 (n : nat) (m : nat) : (term860 n m) = (term860 n m).
Proof. exact (eq_refl (term860 n m)). Qed.
Lemma lem4735581 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term860 n m)) = ((term860 m' m) = (term860 n m)).
Proof. exact (MK_COMB (@lem4735579 m' m) (@lem4735580 n m)). Qed.
Lemma lem4735582 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term975 m n)) = ((term860 m' m) = (term860 n m)).
Proof. exact (TRANS (@lem4735576 m' n m) (@lem4735581 m' n m)). Qed.
Lemma lem4735583 (m : nat) (m' : nat) (n : nat) (h1 : m' = n) : (term860 m' m) = (term860 n m).
Proof. exact (EQ_MP (@lem4735582 m' n m) (@lem4735573 m m' n h1)). Qed.
Lemma lem4735584 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m' = n) : term860 n m.
Proof. exact (EQ_MP (@lem4735583 m m' n h2) (@lem4729660 A f x n m' m h1)). Qed.
Lemma lem4735598 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4735808 (n : nat) : (term978 n) = (term978 n).
Proof. exact (eq_refl (term978 n)). Qed.
Lemma lem4735809 (m : nat) (n : nat) (h1 : m = n) : (term979 n m) = (term980 n).
Proof. exact (MK_COMB (@lem4735808 n) (@lem4735598 m n h1)). Qed.
Lemma lem4735810 (n : nat) : (term980 n) = (term981 n).
Proof. exact (eq_refl (term980 n)). Qed.
Lemma lem4735811 (n : nat) (m : nat) : (term982 n m) = (term982 n m).
Proof. exact (eq_refl (term982 n m)). Qed.
Lemma lem4735812 (m : nat) (n : nat) : ((term979 n m) = (term980 n)) = ((term979 n m) = (term981 n)).
Proof. exact (MK_COMB (@lem4735811 n m) (@lem4735810 n)). Qed.
Lemma lem4735813 (n : nat) (m : nat) : (term979 n m) = (term860 n m).
Proof. exact (eq_refl (term979 n m)). Qed.
Lemma lem4735814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4735815 (n : nat) (m : nat) : (term982 n m) = (term977 n m).
Proof. exact (MK_COMB (@lem4735814) (@lem4735813 n m)). Qed.
Lemma lem4735816 (n : nat) : (term981 n) = (term981 n).
Proof. exact (eq_refl (term981 n)). Qed.
Lemma lem4735817 (m : nat) (n : nat) : ((term979 n m) = (term981 n)) = ((term860 n m) = (term981 n)).
Proof. exact (MK_COMB (@lem4735815 n m) (@lem4735816 n)). Qed.
Lemma lem4735818 (m : nat) (n : nat) : ((term979 n m) = (term980 n)) = ((term860 n m) = (term981 n)).
Proof. exact (TRANS (@lem4735812 m n) (@lem4735817 m n)). Qed.
Lemma lem4735819 (m : nat) (n : nat) (h1 : m = n) : (term860 n m) = (term981 n).
Proof. exact (EQ_MP (@lem4735818 m n) (@lem4735809 m n h1)). Qed.
Lemma lem4736026 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term981 n.
Proof. exact (EQ_MP (@lem4735819 m n h2) (@lem4735584 A f x m m' n h1 h3)). Qed.
Lemma lem4736249 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term860 m' m.
Proof. exact (proj2 (@lem4725203 A f x n m' m h1)). Qed.
Lemma lem4736263 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4736291 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4736472 (m : nat) : (term974 m) = (term974 m).
Proof. exact (eq_refl (term974 m)). Qed.
Lemma lem4736473 (m : nat) (m' : nat) (n : nat) (h1 : m' = n) : (term975 m m') = (term975 m n).
Proof. exact (MK_COMB (@lem4736472 m) (@lem4736291 m' n h1)). Qed.
Lemma lem4736474 (n : nat) (m : nat) : (term975 m n) = (term860 n m).
Proof. exact (eq_refl (term975 m n)). Qed.
Lemma lem4736475 (m : nat) (m' : nat) : (term976 m m') = (term976 m m').
Proof. exact (eq_refl (term976 m m')). Qed.
Lemma lem4736476 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term975 m n)) = ((term975 m m') = (term860 n m)).
Proof. exact (MK_COMB (@lem4736475 m m') (@lem4736474 n m)). Qed.
Lemma lem4736477 (m' : nat) (m : nat) : (term975 m m') = (term860 m' m).
Proof. exact (eq_refl (term975 m m')). Qed.
Lemma lem4736478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4736479 (m' : nat) (m : nat) : (term976 m m') = (term977 m' m).
Proof. exact (MK_COMB (@lem4736478) (@lem4736477 m' m)). Qed.
Lemma lem4736480 (n : nat) (m : nat) : (term860 n m) = (term860 n m).
Proof. exact (eq_refl (term860 n m)). Qed.
Lemma lem4736481 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term860 n m)) = ((term860 m' m) = (term860 n m)).
Proof. exact (MK_COMB (@lem4736479 m' m) (@lem4736480 n m)). Qed.
Lemma lem4736482 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term975 m n)) = ((term860 m' m) = (term860 n m)).
Proof. exact (TRANS (@lem4736476 m' n m) (@lem4736481 m' n m)). Qed.
Lemma lem4736483 (m : nat) (m' : nat) (n : nat) (h1 : m' = n) : (term860 m' m) = (term860 n m).
Proof. exact (EQ_MP (@lem4736482 m' n m) (@lem4736473 m m' n h1)). Qed.
Lemma lem4736484 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m' = n) : term860 n m.
Proof. exact (EQ_MP (@lem4736483 m m' n h2) (@lem4736249 A f x n m' m h1)). Qed.
Lemma lem4736498 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4736695 (n : nat) : (term978 n) = (term978 n).
Proof. exact (eq_refl (term978 n)). Qed.
Lemma lem4736696 (m : nat) (n : nat) (h1 : m = n) : (term979 n m) = (term980 n).
Proof. exact (MK_COMB (@lem4736695 n) (@lem4736498 m n h1)). Qed.
Lemma lem4736697 (n : nat) : (term980 n) = (term981 n).
Proof. exact (eq_refl (term980 n)). Qed.
Lemma lem4736698 (n : nat) (m : nat) : (term982 n m) = (term982 n m).
Proof. exact (eq_refl (term982 n m)). Qed.
Lemma lem4736699 (m : nat) (n : nat) : ((term979 n m) = (term980 n)) = ((term979 n m) = (term981 n)).
Proof. exact (MK_COMB (@lem4736698 n m) (@lem4736697 n)). Qed.
Lemma lem4736700 (n : nat) (m : nat) : (term979 n m) = (term860 n m).
Proof. exact (eq_refl (term979 n m)). Qed.
Lemma lem4736701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4736702 (n : nat) (m : nat) : (term982 n m) = (term977 n m).
Proof. exact (MK_COMB (@lem4736701) (@lem4736700 n m)). Qed.
Lemma lem4736703 (n : nat) : (term981 n) = (term981 n).
Proof. exact (eq_refl (term981 n)). Qed.
Lemma lem4736704 (m : nat) (n : nat) : ((term979 n m) = (term981 n)) = ((term860 n m) = (term981 n)).
Proof. exact (MK_COMB (@lem4736702 n m) (@lem4736703 n)). Qed.
Lemma lem4736705 (m : nat) (n : nat) : ((term979 n m) = (term980 n)) = ((term860 n m) = (term981 n)).
Proof. exact (TRANS (@lem4736699 m n) (@lem4736704 m n)). Qed.
Lemma lem4736706 (m : nat) (n : nat) (h1 : m = n) : (term860 n m) = (term981 n).
Proof. exact (EQ_MP (@lem4736705 m n) (@lem4736696 m n h1)). Qed.
Lemma lem4736899 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term981 n.
Proof. exact (EQ_MP (@lem4736706 m n h2) (@lem4736484 A f x m m' n h1 h3)). Qed.
Lemma lem4737136 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4737150 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4737357 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4737371 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4737564 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4737578 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4737635 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : x = (f m').
Proof. exact (SYM (@lem4729878 A f m' x h1)). Qed.
Lemma lem4737705 {A : Type'} (a : A) : (term948 A a) = (term948 A a).
Proof. exact (eq_refl (term948 A a)). Qed.
Lemma lem4737706 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (term949 A a x) = (term950 A a f m').
Proof. exact (MK_COMB (@lem4737705 A a) (@lem4737635 A f m' x h1)). Qed.
Lemma lem4737707 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (term950 A a f m') = (a = (f m')).
Proof. exact (eq_refl (term950 A a f m')). Qed.
Lemma lem4737708 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term951 A a x).
Proof. exact (eq_refl (term951 A a x)). Qed.
Lemma lem4737709 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (term950 A a f m')) = ((term949 A a x) = (a = (f m'))).
Proof. exact (MK_COMB (@lem4737708 A a x) (@lem4737707 A a f m')). Qed.
Lemma lem4737710 {A : Type'} (a : A) (x : A) : (term949 A a x) = (a = x).
Proof. exact (eq_refl (term949 A a x)). Qed.
Lemma lem4737711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4737712 {A : Type'} (a : A) (x : A) : (term951 A a x) = (term952 A a x).
Proof. exact (MK_COMB (@lem4737711) (@lem4737710 A a x)). Qed.
Lemma lem4737713 {A : Type'} (a : A) (f : nat -> A) (m' : nat) : (a = (f m')) = (a = (f m')).
Proof. exact (eq_refl (a = (f m'))). Qed.
Lemma lem4737714 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (a = (f m'))) = ((a = x) = (a = (f m'))).
Proof. exact (MK_COMB (@lem4737712 A a x) (@lem4737713 A a f m')). Qed.
Lemma lem4737715 {A : Type'} (x : A) (a : A) (f : nat -> A) (m' : nat) : ((term949 A a x) = (term950 A a f m')) = ((a = x) = (a = (f m'))).
Proof. exact (TRANS (@lem4737709 A x a f m') (@lem4737714 A x a f m')). Qed.
Lemma lem4737716 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (a = x) = (a = (f m')).
Proof. exact (EQ_MP (@lem4737715 A x a f m') (@lem4737706 A a f m' x h1)). Qed.
Lemma lem4737814 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4737926 {A : Type'} (_55944 : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term395 A n f _55944 s a.
Proof. exact (EQ_MP (@lem4728640 A n f _55944 s a) (@lem4728639 A _55944 n f s a h1)). Qed.
Lemma lem4737954 {A : Type'} (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : a = (f m').
Proof. exact (EQ_MP (@lem4737716 A a f m' x h2) (@lem4729846 A a x h1)). Qed.
Lemma lem4738036 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4738133 {A : Type'} (n : nat) (f : nat -> A) (_55944 : nat) (s : A -> Prop) : (term958 A n f _55944 s) = (term958 A n f _55944 s).
Proof. exact (eq_refl (term958 A n f _55944 s)). Qed.
Lemma lem4738134 {A : Type'} (n : nat) (_55944 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : (term959 A n f _55944 s a) = (term960 A n _55944 s f m').
Proof. exact (MK_COMB (@lem4738133 A n f _55944 s) (@lem4737954 A a f m' x h1 h2)). Qed.
Lemma lem4738135 {A : Type'} (n : nat) (_55944 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term960 A n _55944 s f m') = (term961 A n _55944 s f m').
Proof. exact (eq_refl (term960 A n _55944 s f m')). Qed.
Lemma lem4738136 {A : Type'} (n : nat) (f : nat -> A) (_55944 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55944 s a) = (term962 A n f _55944 s a).
Proof. exact (eq_refl (term962 A n f _55944 s a)). Qed.
Lemma lem4738137 {A : Type'} (a : A) (n : nat) (_55944 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : ((term959 A n f _55944 s a) = (term960 A n _55944 s f m')) = ((term959 A n f _55944 s a) = (term961 A n _55944 s f m')).
Proof. exact (MK_COMB (@lem4738136 A n f _55944 s a) (@lem4738135 A n _55944 s f m')). Qed.
Lemma lem4738138 {A : Type'} (n : nat) (f : nat -> A) (_55944 : nat) (s : A -> Prop) (a : A) : (term959 A n f _55944 s a) = (term395 A n f _55944 s a).
Proof. exact (eq_refl (term959 A n f _55944 s a)). Qed.
Lemma lem4738139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4738140 {A : Type'} (n : nat) (f : nat -> A) (_55944 : nat) (s : A -> Prop) (a : A) : (term962 A n f _55944 s a) = (term614 A n f _55944 s a).
Proof. exact (MK_COMB (@lem4738139) (@lem4738138 A n f _55944 s a)). Qed.
Lemma lem4738141 {A : Type'} (n : nat) (_55944 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term961 A n _55944 s f m') = (term961 A n _55944 s f m').
Proof. exact (eq_refl (term961 A n _55944 s f m')). Qed.
Lemma lem4738142 {A : Type'} (a : A) (n : nat) (_55944 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : ((term959 A n f _55944 s a) = (term961 A n _55944 s f m')) = ((term395 A n f _55944 s a) = (term961 A n _55944 s f m')).
Proof. exact (MK_COMB (@lem4738140 A n f _55944 s a) (@lem4738141 A n _55944 s f m')). Qed.
Lemma lem4738143 {A : Type'} (a : A) (n : nat) (_55944 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : ((term959 A n f _55944 s a) = (term960 A n _55944 s f m')) = ((term395 A n f _55944 s a) = (term961 A n _55944 s f m')).
Proof. exact (TRANS (@lem4738137 A a n _55944 s f m') (@lem4738142 A a n _55944 s f m')). Qed.
Lemma lem4738144 {A : Type'} (n : nat) (_55944 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : a = x) (h2 : (f m') = x) : (term395 A n f _55944 s a) = (term961 A n _55944 s f m').
Proof. exact (EQ_MP (@lem4738143 A a n _55944 s f m') (@lem4738134 A n _55944 s a f m' x h1 h2)). Qed.
Lemma lem4738145 {A : Type'} (_55944 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term961 A n _55944 s f m'.
Proof. exact (EQ_MP (@lem4738144 A n _55944 s a f m' x h2 h3) (@lem4737926 A _55944 n f s a h1)). Qed.
Lemma lem4738243 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4738271 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (_55957 : A) (h1 : term323 A) : term963 A _55955 _55956 _55957.
Proof. exact (proj2 (@lem4728680 A _55955 _55956 _55957 h1)). Qed.
Lemma lem4738426 (m : nat) : (term974 m) = (term974 m).
Proof. exact (eq_refl (term974 m)). Qed.
Lemma lem4738427 (m : nat) (m' : nat) (n : nat) (h1 : m' = n) : (term975 m m') = (term975 m n).
Proof. exact (MK_COMB (@lem4738426 m) (@lem4729946 m' n h1)). Qed.
Lemma lem4738428 (n : nat) (m : nat) : (term975 m n) = (term860 n m).
Proof. exact (eq_refl (term975 m n)). Qed.
Lemma lem4738429 (m : nat) (m' : nat) : (term976 m m') = (term976 m m').
Proof. exact (eq_refl (term976 m m')). Qed.
Lemma lem4738430 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term975 m n)) = ((term975 m m') = (term860 n m)).
Proof. exact (MK_COMB (@lem4738429 m m') (@lem4738428 n m)). Qed.
Lemma lem4738431 (m' : nat) (m : nat) : (term975 m m') = (term860 m' m).
Proof. exact (eq_refl (term975 m m')). Qed.
Lemma lem4738432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4738433 (m' : nat) (m : nat) : (term976 m m') = (term977 m' m).
Proof. exact (MK_COMB (@lem4738432) (@lem4738431 m' m)). Qed.
Lemma lem4738434 (n : nat) (m : nat) : (term860 n m) = (term860 n m).
Proof. exact (eq_refl (term860 n m)). Qed.
Lemma lem4738435 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term860 n m)) = ((term860 m' m) = (term860 n m)).
Proof. exact (MK_COMB (@lem4738433 m' m) (@lem4738434 n m)). Qed.
Lemma lem4738436 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term975 m n)) = ((term860 m' m) = (term860 n m)).
Proof. exact (TRANS (@lem4738430 m' n m) (@lem4738435 m' n m)). Qed.
Lemma lem4738437 (m : nat) (m' : nat) (n : nat) (h1 : m' = n) : (term860 m' m) = (term860 n m).
Proof. exact (EQ_MP (@lem4738436 m' n m) (@lem4738427 m m' n h1)). Qed.
Lemma lem4738452 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4738674 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m' = n) : term860 n m.
Proof. exact (EQ_MP (@lem4738437 m m' n h2) (@lem4729940 A f x n m' m h1)). Qed.
Lemma lem4738688 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4738883 (n : nat) : (term978 n) = (term978 n).
Proof. exact (eq_refl (term978 n)). Qed.
Lemma lem4738884 (m : nat) (n : nat) (h1 : m = n) : (term979 n m) = (term980 n).
Proof. exact (MK_COMB (@lem4738883 n) (@lem4738688 m n h1)). Qed.
Lemma lem4738885 (n : nat) : (term980 n) = (term981 n).
Proof. exact (eq_refl (term980 n)). Qed.
Lemma lem4738886 (n : nat) (m : nat) : (term982 n m) = (term982 n m).
Proof. exact (eq_refl (term982 n m)). Qed.
Lemma lem4738887 (m : nat) (n : nat) : ((term979 n m) = (term980 n)) = ((term979 n m) = (term981 n)).
Proof. exact (MK_COMB (@lem4738886 n m) (@lem4738885 n)). Qed.
Lemma lem4738888 (n : nat) (m : nat) : (term979 n m) = (term860 n m).
Proof. exact (eq_refl (term979 n m)). Qed.
Lemma lem4738889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4738890 (n : nat) (m : nat) : (term982 n m) = (term977 n m).
Proof. exact (MK_COMB (@lem4738889) (@lem4738888 n m)). Qed.
Lemma lem4738891 (n : nat) : (term981 n) = (term981 n).
Proof. exact (eq_refl (term981 n)). Qed.
Lemma lem4738892 (m : nat) (n : nat) : ((term979 n m) = (term981 n)) = ((term860 n m) = (term981 n)).
Proof. exact (MK_COMB (@lem4738890 n m) (@lem4738891 n)). Qed.
Lemma lem4738893 (m : nat) (n : nat) : ((term979 n m) = (term980 n)) = ((term860 n m) = (term981 n)).
Proof. exact (TRANS (@lem4738887 m n) (@lem4738892 m n)). Qed.
Lemma lem4738894 (m : nat) (n : nat) (h1 : m = n) : (term860 n m) = (term981 n).
Proof. exact (EQ_MP (@lem4738893 m n) (@lem4738884 m n h1)). Qed.
Lemma lem4739088 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term981 n.
Proof. exact (EQ_MP (@lem4738894 m n h2) (@lem4738674 A f x m m' n h1 h3)). Qed.
Lemma lem4739297 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term870 A f x n m' m) : term860 m' m.
Proof. exact (proj2 (@lem4725203 A f x n m' m h1)). Qed.
Lemma lem4739311 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4739338 (m' : nat) (n : nat) (h1 : m' = n) : m' = n.
Proof. exact (h1). Qed.
Lemma lem4739519 (m : nat) : (term974 m) = (term974 m).
Proof. exact (eq_refl (term974 m)). Qed.
Lemma lem4739520 (m : nat) (m' : nat) (n : nat) (h1 : m' = n) : (term975 m m') = (term975 m n).
Proof. exact (MK_COMB (@lem4739519 m) (@lem4739338 m' n h1)). Qed.
Lemma lem4739521 (n : nat) (m : nat) : (term975 m n) = (term860 n m).
Proof. exact (eq_refl (term975 m n)). Qed.
Lemma lem4739522 (m : nat) (m' : nat) : (term976 m m') = (term976 m m').
Proof. exact (eq_refl (term976 m m')). Qed.
Lemma lem4739523 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term975 m n)) = ((term975 m m') = (term860 n m)).
Proof. exact (MK_COMB (@lem4739522 m m') (@lem4739521 n m)). Qed.
Lemma lem4739524 (m' : nat) (m : nat) : (term975 m m') = (term860 m' m).
Proof. exact (eq_refl (term975 m m')). Qed.
Lemma lem4739525 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4739526 (m' : nat) (m : nat) : (term976 m m') = (term977 m' m).
Proof. exact (MK_COMB (@lem4739525) (@lem4739524 m' m)). Qed.
Lemma lem4739527 (n : nat) (m : nat) : (term860 n m) = (term860 n m).
Proof. exact (eq_refl (term860 n m)). Qed.
Lemma lem4739528 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term860 n m)) = ((term860 m' m) = (term860 n m)).
Proof. exact (MK_COMB (@lem4739526 m' m) (@lem4739527 n m)). Qed.
Lemma lem4739529 (m' : nat) (n : nat) (m : nat) : ((term975 m m') = (term975 m n)) = ((term860 m' m) = (term860 n m)).
Proof. exact (TRANS (@lem4739523 m' n m) (@lem4739528 m' n m)). Qed.
Lemma lem4739530 (m : nat) (m' : nat) (n : nat) (h1 : m' = n) : (term860 m' m) = (term860 n m).
Proof. exact (EQ_MP (@lem4739529 m' n m) (@lem4739520 m m' n h1)). Qed.
Lemma lem4739531 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m' = n) : term860 n m.
Proof. exact (EQ_MP (@lem4739530 m m' n h2) (@lem4739297 A f x n m' m h1)). Qed.
Lemma lem4739545 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem4739741 (n : nat) : (term978 n) = (term978 n).
Proof. exact (eq_refl (term978 n)). Qed.
Lemma lem4739742 (m : nat) (n : nat) (h1 : m = n) : (term979 n m) = (term980 n).
Proof. exact (MK_COMB (@lem4739741 n) (@lem4739545 m n h1)). Qed.
Lemma lem4739743 (n : nat) : (term980 n) = (term981 n).
Proof. exact (eq_refl (term980 n)). Qed.
Lemma lem4739744 (n : nat) (m : nat) : (term982 n m) = (term982 n m).
Proof. exact (eq_refl (term982 n m)). Qed.
Lemma lem4739745 (m : nat) (n : nat) : ((term979 n m) = (term980 n)) = ((term979 n m) = (term981 n)).
Proof. exact (MK_COMB (@lem4739744 n m) (@lem4739743 n)). Qed.
Lemma lem4739746 (n : nat) (m : nat) : (term979 n m) = (term860 n m).
Proof. exact (eq_refl (term979 n m)). Qed.
Lemma lem4739747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4739748 (n : nat) (m : nat) : (term982 n m) = (term977 n m).
Proof. exact (MK_COMB (@lem4739747) (@lem4739746 n m)). Qed.
Lemma lem4739749 (n : nat) : (term981 n) = (term981 n).
Proof. exact (eq_refl (term981 n)). Qed.
Lemma lem4739750 (m : nat) (n : nat) : ((term979 n m) = (term981 n)) = ((term860 n m) = (term981 n)).
Proof. exact (MK_COMB (@lem4739748 n m) (@lem4739749 n)). Qed.
Lemma lem4739751 (m : nat) (n : nat) : ((term979 n m) = (term980 n)) = ((term860 n m) = (term981 n)).
Proof. exact (TRANS (@lem4739745 m n) (@lem4739750 m n)). Qed.
Lemma lem4739752 (m : nat) (n : nat) (h1 : m = n) : (term860 n m) = (term981 n).
Proof. exact (EQ_MP (@lem4739751 m n) (@lem4739742 m n h1)). Qed.
Lemma lem4739945 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term981 n.
Proof. exact (EQ_MP (@lem4739752 m n h2) (@lem4739531 A f x m m' n h1 h3)). Qed.
Lemma lem4740125 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4740126 (n : nat) : n = n.
Proof. exact (@lem4740125 n). Qed.
Lemma lem4740127 (n : nat) : term983 n.
Proof. exact (fun h0 : term981 n => @lem4740126 n). Qed.
Lemma lem4740129 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740130 (n : nat) : (term983 n) = (n = n).
Proof. exact (@lem4740129 (n = n)). Qed.
Lemma lem4740131 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem4740130 n) (@lem4740127 n)). Qed.
Lemma lem4740133 (b : Prop) (a : Prop) : (a \/ b) = (term616 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4740134 (_55761 : nat) (n : nat) : (term947 _55761 n) = (term984 _55761 n).
Proof. exact (@lem4740133 (term860 _55761 n) (Peano.lt _55761 n)). Qed.
Lemma lem4740136 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4740137 (_55761 : nat) (n : nat) : (term985 _55761 n) = (_55761 = n).
Proof. exact (@lem4740136 (_55761 = n)). Qed.
Lemma lem4740138 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4740139 (_55761 : nat) (n : nat) : (term986 _55761 n) = (term646 _55761 n).
Proof. exact (MK_COMB (@lem4740138) (@lem4740137 _55761 n)). Qed.
Lemma lem4740140 (_55761 : nat) (n : nat) : (Peano.lt _55761 n) = (Peano.lt _55761 n).
Proof. exact (eq_refl (Peano.lt _55761 n)). Qed.
Lemma lem4740141 (_55761 : nat) (n : nat) : (term984 _55761 n) = (term987 _55761 n).
Proof. exact (MK_COMB (@lem4740139 _55761 n) (@lem4740140 _55761 n)). Qed.
Lemma lem4740142 (_55761 : nat) (n : nat) : (term947 _55761 n) = (term987 _55761 n).
Proof. exact (TRANS (@lem4740134 _55761 n) (@lem4740141 _55761 n)). Qed.
Lemma lem4740145 {A : Type'} (_55761 : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : term987 _55761 n.
Proof. exact (EQ_MP (@lem4740142 _55761 n) (@lem4730165 A _55761 f x n h1)). Qed.
Lemma lem4740146 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : term988 n.
Proof. exact (@lem4740145 A n f x n h1). Qed.
Lemma lem4740149 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : Peano.lt n n.
Proof. exact (@lem4740146 A f x n h1 (@lem4740131 n)). Qed.
Lemma lem4740150 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : term989 n.
Proof. exact (fun h0 : term842 n => @lem4740149 A f x n h1). Qed.
Lemma lem4740152 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740153 (n : nat) : (term989 n) = (Peano.lt n n).
Proof. exact (@lem4740152 (Peano.lt n n)). Qed.
Lemma lem4740154 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term883 A f x n) : Peano.lt n n.
Proof. exact (EQ_MP (@lem4740153 n) (@lem4740150 A f x n h1)). Qed.
Lemma lem4740157 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4740159 (_55748 : nat) : (term842 _55748) = (term990 _55748).
Proof. exact (@lem4740157 (Peano.lt _55748 _55748)). Qed.
Lemma lem4740162 (_55748 : nat) (h1 : term803) : term990 _55748.
Proof. exact (EQ_MP (@lem4740159 _55748) (@lem4730123 _55748 h1)). Qed.
Lemma lem4740163 (n : nat) (h1 : term803) : term990 n.
Proof. exact (@lem4740162 n h1). Qed.
Lemma lem4740166 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term803) (h2 : term883 A f x n) : False.
Proof. exact (@lem4740163 n h1 (@lem4740154 A f x n h2)). Qed.
Lemma lem4740167 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term803) (h2 : term883 A f x n) : term632.
Proof. exact (fun h0 : ~ False => @lem4740166 A f x n h1 h2). Qed.
Lemma lem4740169 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740170 : term632 = False.
Proof. exact (@lem4740169 False). Qed.
Lemma lem4740295 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4740296 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : term611 m' n.
Proof. exact (fun h0 : term312 m' n => @lem4740295 m' n h1). Qed.
Lemma lem4740298 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740299 (m' : nat) (n : nat) : (term611 m' n) = (Peano.lt m' n).
Proof. exact (@lem4740298 (Peano.lt m' n)). Qed.
Lemma lem4740300 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (EQ_MP (@lem4740299 m' n) (@lem4740296 m' n h1)). Qed.
Lemma lem4740303 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4740305 (m' : nat) (n : nat) : (term312 m' n) = (term991 m' n).
Proof. exact (@lem4740303 (Peano.lt m' n)). Qed.
Lemma lem4740308 (m' : nat) (n : nat) (h1 : term312 m' n) : term991 m' n.
Proof. exact (EQ_MP (@lem4740305 m' n) (@lem4730442 m' n h1)). Qed.
Lemma lem4740311 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (@lem4740308 m' n h1 (@lem4740300 m' n h2)). Qed.
Lemma lem4740312 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : term632.
Proof. exact (fun h0 : ~ False => @lem4740311 m' n h1 h2). Qed.
Lemma lem4740314 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740315 : term632 = False.
Proof. exact (@lem4740314 False). Qed.
Lemma lem4740316 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4740315) (@lem4740312 m' n h1 h2)). Qed.
Lemma lem4740440 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4740441 (m : nat) (n : nat) (h1 : Peano.lt m n) : term611 m n.
Proof. exact (fun h0 : term312 m n => @lem4740440 m n h1). Qed.
Lemma lem4740443 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740444 (m : nat) (n : nat) : (term611 m n) = (Peano.lt m n).
Proof. exact (@lem4740443 (Peano.lt m n)). Qed.
Lemma lem4740445 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem4740444 m n) (@lem4740441 m n h1)). Qed.
Lemma lem4740448 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4740450 (m : nat) (n : nat) : (term312 m n) = (term991 m n).
Proof. exact (@lem4740448 (Peano.lt m n)). Qed.
Lemma lem4740453 (m : nat) (n : nat) (h1 : term312 m n) : term991 m n.
Proof. exact (EQ_MP (@lem4740450 m n) (@lem4730886 m n h1)). Qed.
Lemma lem4740456 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (@lem4740453 m n h1 (@lem4740445 m n h2)). Qed.
Lemma lem4740457 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : term632.
Proof. exact (fun h0 : ~ False => @lem4740456 m n h1 h2). Qed.
Lemma lem4740459 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740460 : term632 = False.
Proof. exact (@lem4740459 False). Qed.
Lemma lem4740461 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4740460) (@lem4740457 m n h1 h2)). Qed.
Lemma lem4740585 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4740586 (m : nat) (n : nat) (h1 : Peano.lt m n) : term611 m n.
Proof. exact (fun h0 : term312 m n => @lem4740585 m n h1). Qed.
Lemma lem4740588 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740589 (m : nat) (n : nat) : (term611 m n) = (Peano.lt m n).
Proof. exact (@lem4740588 (Peano.lt m n)). Qed.
Lemma lem4740590 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem4740589 m n) (@lem4740586 m n h1)). Qed.
Lemma lem4740593 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4740595 (m : nat) (n : nat) : (term312 m n) = (term991 m n).
Proof. exact (@lem4740593 (Peano.lt m n)). Qed.
Lemma lem4740598 (m : nat) (n : nat) (h1 : term312 m n) : term991 m n.
Proof. exact (EQ_MP (@lem4740595 m n) (@lem4731343 m n h1)). Qed.
Lemma lem4740601 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (@lem4740598 m n h1 (@lem4740590 m n h2)). Qed.
Lemma lem4740602 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : term632.
Proof. exact (fun h0 : ~ False => @lem4740601 m n h1 h2). Qed.
Lemma lem4740604 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740605 : term632 = False.
Proof. exact (@lem4740604 False). Qed.
Lemma lem4740606 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4740605) (@lem4740602 m n h1 h2)). Qed.
Lemma lem4740730 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4740731 (m : nat) (n : nat) (h1 : Peano.lt m n) : term611 m n.
Proof. exact (fun h0 : term312 m n => @lem4740730 m n h1). Qed.
Lemma lem4740733 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740734 (m : nat) (n : nat) : (term611 m n) = (Peano.lt m n).
Proof. exact (@lem4740733 (Peano.lt m n)). Qed.
Lemma lem4740735 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem4740734 m n) (@lem4740731 m n h1)). Qed.
Lemma lem4740738 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4740740 (m : nat) (n : nat) : (term312 m n) = (term991 m n).
Proof. exact (@lem4740738 (Peano.lt m n)). Qed.
Lemma lem4740743 (m : nat) (n : nat) (h1 : term312 m n) : term991 m n.
Proof. exact (EQ_MP (@lem4740740 m n) (@lem4732022 m n h1)). Qed.
Lemma lem4740746 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (@lem4740743 m n h1 (@lem4740735 m n h2)). Qed.
Lemma lem4740747 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : term632.
Proof. exact (fun h0 : ~ False => @lem4740746 m n h1 h2). Qed.
Lemma lem4740749 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740750 : term632 = False.
Proof. exact (@lem4740749 False). Qed.
Lemma lem4740751 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4740750) (@lem4740747 m n h1 h2)). Qed.
Lemma lem4740875 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4740876 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : term611 m' n.
Proof. exact (fun h0 : term312 m' n => @lem4740875 m' n h1). Qed.
Lemma lem4740878 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740879 (m' : nat) (n : nat) : (term611 m' n) = (Peano.lt m' n).
Proof. exact (@lem4740878 (Peano.lt m' n)). Qed.
Lemma lem4740880 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (EQ_MP (@lem4740879 m' n) (@lem4740876 m' n h1)). Qed.
Lemma lem4740883 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4740885 (m' : nat) (n : nat) : (term312 m' n) = (term991 m' n).
Proof. exact (@lem4740883 (Peano.lt m' n)). Qed.
Lemma lem4740888 (m' : nat) (n : nat) (h1 : term312 m' n) : term991 m' n.
Proof. exact (EQ_MP (@lem4740885 m' n) (@lem4732480 m' n h1)). Qed.
Lemma lem4740891 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (@lem4740888 m' n h1 (@lem4740880 m' n h2)). Qed.
Lemma lem4740892 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : term632.
Proof. exact (fun h0 : ~ False => @lem4740891 m' n h1 h2). Qed.
Lemma lem4740894 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4740895 : term632 = False.
Proof. exact (@lem4740894 False). Qed.
Lemma lem4740896 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4740895) (@lem4740892 m' n h1 h2)). Qed.
Lemma lem4741020 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4741021 (m : nat) (n : nat) (h1 : Peano.lt m n) : term611 m n.
Proof. exact (fun h0 : term312 m n => @lem4741020 m n h1). Qed.
Lemma lem4741023 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741024 (m : nat) (n : nat) : (term611 m n) = (Peano.lt m n).
Proof. exact (@lem4741023 (Peano.lt m n)). Qed.
Lemma lem4741025 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem4741024 m n) (@lem4741021 m n h1)). Qed.
Lemma lem4741031 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4741032 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55832 : nat) (n : nat) : (term961 A n _55832 s f m') = (term992 A s f m' _55832 n).
Proof. exact (@lem4741031 (term993 A _55832 s f m') (term312 _55832 n)). Qed.
Lemma lem4741038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4741039 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55832 : nat) (n : nat) : (term994 A n _55832 s f m') = (term995 A s f m' _55832 n).
Proof. exact (MK_COMB (@lem4741038) (@lem4741032 A s f m' _55832 n)). Qed.
Lemma lem4741045 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55832 : nat) (n : nat) : (term992 A s f m' _55832 n) = (term992 A s f m' _55832 n).
Proof. exact (eq_refl (term992 A s f m' _55832 n)). Qed.
Lemma lem4741046 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55832 : nat) (n : nat) : ((term961 A n _55832 s f m') = (term992 A s f m' _55832 n)) = ((term992 A s f m' _55832 n) = (term992 A s f m' _55832 n)).
Proof. exact (MK_COMB (@lem4741039 A s f m' _55832 n) (@lem4741045 A s f m' _55832 n)). Qed.
Lemma lem4741048 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4741049 (x : Prop) : (x = x) = True.
Proof. exact (@lem4741048 Prop x). Qed.
Lemma lem4741050 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55832 : nat) (n : nat) : ((term992 A s f m' _55832 n) = (term992 A s f m' _55832 n)) = True.
Proof. exact (@lem4741049 (term992 A s f m' _55832 n)). Qed.
Lemma lem4741051 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55832 : nat) (n : nat) : ((term961 A n _55832 s f m') = (term992 A s f m' _55832 n)) = True.
Proof. exact (TRANS (@lem4741046 A s f m' _55832 n) (@lem4741050 A s f m' _55832 n)). Qed.
Lemma lem4741052 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55832 : nat) (n : nat) : True = ((term961 A n _55832 s f m') = (term992 A s f m' _55832 n)).
Proof. exact (SYM (@lem4741051 A s f m' _55832 n)). Qed.
Lemma lem4741053 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55832 : nat) (n : nat) : (term961 A n _55832 s f m') = (term992 A s f m' _55832 n).
Proof. exact (EQ_MP (@lem4741052 A s f m' _55832 n) (@lem0)). Qed.
Lemma lem4741054 {A : Type'} (_55832 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term992 A s f m' _55832 n.
Proof. exact (EQ_MP (@lem4741053 A s f m' _55832 n) (@lem4732825 A _55832 n s a f m' x h1 h2 h3)). Qed.
Lemma lem4741056 (b : Prop) (a : Prop) : (a \/ b) = (term616 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4741057 {A : Type'} (n : nat) (_55832 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term992 A s f m' _55832 n) = (term996 A n _55832 s f m').
Proof. exact (@lem4741056 (term312 _55832 n) (term993 A _55832 s f m')). Qed.
Lemma lem4741059 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4741060 (_55832 : nat) (n : nat) : (term618 _55832 n) = (Peano.lt _55832 n).
Proof. exact (@lem4741059 (Peano.lt _55832 n)). Qed.
Lemma lem4741061 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4741062 (_55832 : nat) (n : nat) : (term619 _55832 n) = (term298 _55832 n).
Proof. exact (MK_COMB (@lem4741061) (@lem4741060 _55832 n)). Qed.
Lemma lem4741063 {A : Type'} (_55832 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term993 A _55832 s f m') = (term993 A _55832 s f m').
Proof. exact (eq_refl (term993 A _55832 s f m')). Qed.
Lemma lem4741064 {A : Type'} (n : nat) (_55832 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term996 A n _55832 s f m') = (term997 A n _55832 s f m').
Proof. exact (MK_COMB (@lem4741062 _55832 n) (@lem4741063 A _55832 s f m')). Qed.
Lemma lem4741065 {A : Type'} (n : nat) (_55832 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term992 A s f m' _55832 n) = (term997 A n _55832 s f m').
Proof. exact (TRANS (@lem4741057 A n _55832 s f m') (@lem4741064 A n _55832 s f m')). Qed.
Lemma lem4741068 {A : Type'} (_55832 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term997 A n _55832 s f m'.
Proof. exact (EQ_MP (@lem4741065 A n _55832 s f m') (@lem4741054 A _55832 n s a f m' x h1 h2 h3)). Qed.
Lemma lem4741069 {A : Type'} (m : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term997 A n m s f m'.
Proof. exact (@lem4741068 A m n s a f m' x h1 h2 h3). Qed.
Lemma lem4741072 {A : Type'} (s : A -> Prop) (m : nat) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m') = x) : term993 A m s f m'.
Proof. exact (@lem4741069 A m n s a f m' x h1 h3 h4 (@lem4741025 m n h2)). Qed.
Lemma lem4741073 {A : Type'} (s : A -> Prop) (m : nat) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m') = x) : term998 A m s f m'.
Proof. exact (fun h0 : term999 A m s f m' => @lem4741072 A s m n a f m' x h1 h2 h3 h4). Qed.
Lemma lem4741075 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741076 {A : Type'} (m : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term998 A m s f m') = (term993 A m s f m').
Proof. exact (@lem4741075 (term993 A m s f m')). Qed.
Lemma lem4741077 {A : Type'} (s : A -> Prop) (m : nat) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m') = x) : term993 A m s f m'.
Proof. exact (EQ_MP (@lem4741076 A m s f m') (@lem4741073 A s m n a f m' x h1 h2 h3 h4)). Qed.
Lemma lem4741079 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m) = x) (h2 : (f m') = x) : (f m) = (f m').
Proof. exact (EQ_MP (@lem4732701 A m f m' x h2) (@lem4729314 A f m x h1)). Qed.
Lemma lem4741080 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m) = x) (h2 : (f m') = x) : term1000 A m f m'.
Proof. exact (fun h0 : term1001 A m f m' => @lem4741079 A m f m' x h1 h2). Qed.
Lemma lem4741082 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741083 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) : (term1000 A m f m') = ((f m) = (f m')).
Proof. exact (@lem4741082 ((f m) = (f m'))). Qed.
Lemma lem4741084 {A : Type'} (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : (f m) = x) (h2 : (f m') = x) : (f m) = (f m').
Proof. exact (EQ_MP (@lem4741083 A m f m') (@lem4741080 A m f m' x h1 h2)). Qed.
Lemma lem4741086 (a : Prop) (b : Prop) : (term1002 a b) = (term1003 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4741087 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (_55845 : A) : (term963 A _55843 _55844 _55845) = (term1004 A _55843 _55844 _55845).
Proof. exact (@lem4741086 (term380 A _55844 _55843 _55845) (_55844 = _55845)). Qed.
Lemma lem4741089 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4741090 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (_55845 : A) : (term1004 A _55843 _55844 _55845) = (term1005 A _55843 _55844 _55845).
Proof. exact (@lem4741089 (term1006 A _55843 _55844 _55845)). Qed.
Lemma lem4741091 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (_55845 : A) : (term963 A _55843 _55844 _55845) = (term1005 A _55843 _55844 _55845).
Proof. exact (TRANS (@lem4741087 A _55843 _55844 _55845) (@lem4741090 A _55843 _55844 _55845)). Qed.
Lemma lem4741093 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m) = x) (h5 : (f m') = x) : term1007 A s m f m'.
Proof. exact (conj (@lem4741077 A s m n a f m' x h1 h2 h3 h5) (@lem4741084 A m f m' x h4 h5)). Qed.
Lemma lem4741095 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (_55845 : A) (h1 : term323 A) : term1005 A _55843 _55844 _55845.
Proof. exact (EQ_MP (@lem4741091 A _55843 _55844 _55845) (@lem4732965 A _55843 _55844 _55845 h1)). Qed.
Lemma lem4741096 {A : Type'} (_55843 : A -> Prop) (_55844 : A) (_55845 : A) (h1 : term323 A) : term1005 A _55843 _55844 _55845.
Proof. exact (@lem4741095 A _55843 _55844 _55845 h1). Qed.
Lemma lem4741097 {A : Type'} (s : A -> Prop) (m : nat) (f : nat -> A) (m' : nat) (h1 : term323 A) : term1008 A s m f m'.
Proof. exact (@lem4741096 A s (f m) (f m') h1). Qed.
Lemma lem4741100 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (@lem4741097 A s m f m' h1 (@lem4741093 A s n a m f m' x h2 h3 h4 h5 h6)). Qed.
Lemma lem4741101 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : term632.
Proof. exact (fun h0 : ~ False => @lem4741100 A s n a m f m' x h1 h2 h3 h4 h5 h6). Qed.
Lemma lem4741103 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741104 : term632 = False.
Proof. exact (@lem4741103 False). Qed.
Lemma lem4741105 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4741104) (@lem4741101 A s n a m f m' x h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4741229 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4741230 (m : nat) (n : nat) (h1 : Peano.lt m n) : term611 m n.
Proof. exact (fun h0 : term312 m n => @lem4741229 m n h1). Qed.
Lemma lem4741232 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741233 (m : nat) (n : nat) : (term611 m n) = (Peano.lt m n).
Proof. exact (@lem4741232 (Peano.lt m n)). Qed.
Lemma lem4741234 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem4741233 m n) (@lem4741230 m n h1)). Qed.
Lemma lem4741240 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4741241 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (_55846 : nat) (n : nat) : (term961 A n _55846 s f m) = (term992 A s f m _55846 n).
Proof. exact (@lem4741240 (term993 A _55846 s f m) (term312 _55846 n)). Qed.
Lemma lem4741247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4741248 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (_55846 : nat) (n : nat) : (term994 A n _55846 s f m) = (term995 A s f m _55846 n).
Proof. exact (MK_COMB (@lem4741247) (@lem4741241 A s f m _55846 n)). Qed.
Lemma lem4741254 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (_55846 : nat) (n : nat) : (term992 A s f m _55846 n) = (term992 A s f m _55846 n).
Proof. exact (eq_refl (term992 A s f m _55846 n)). Qed.
Lemma lem4741255 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (_55846 : nat) (n : nat) : ((term961 A n _55846 s f m) = (term992 A s f m _55846 n)) = ((term992 A s f m _55846 n) = (term992 A s f m _55846 n)).
Proof. exact (MK_COMB (@lem4741248 A s f m _55846 n) (@lem4741254 A s f m _55846 n)). Qed.
Lemma lem4741257 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4741258 (x : Prop) : (x = x) = True.
Proof. exact (@lem4741257 Prop x). Qed.
Lemma lem4741259 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (_55846 : nat) (n : nat) : ((term992 A s f m _55846 n) = (term992 A s f m _55846 n)) = True.
Proof. exact (@lem4741258 (term992 A s f m _55846 n)). Qed.
Lemma lem4741260 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (_55846 : nat) (n : nat) : ((term961 A n _55846 s f m) = (term992 A s f m _55846 n)) = True.
Proof. exact (TRANS (@lem4741255 A s f m _55846 n) (@lem4741259 A s f m _55846 n)). Qed.
Lemma lem4741261 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (_55846 : nat) (n : nat) : True = ((term961 A n _55846 s f m) = (term992 A s f m _55846 n)).
Proof. exact (SYM (@lem4741260 A s f m _55846 n)). Qed.
Lemma lem4741262 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (_55846 : nat) (n : nat) : (term961 A n _55846 s f m) = (term992 A s f m _55846 n).
Proof. exact (EQ_MP (@lem4741261 A s f m _55846 n) (@lem0)). Qed.
Lemma lem4741263 {A : Type'} (_55846 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m) = x) : term992 A s f m _55846 n.
Proof. exact (EQ_MP (@lem4741262 A s f m _55846 n) (@lem4733505 A _55846 n s a f m x h1 h2 h3)). Qed.
Lemma lem4741265 (b : Prop) (a : Prop) : (a \/ b) = (term616 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4741266 {A : Type'} (n : nat) (_55846 : nat) (s : A -> Prop) (f : nat -> A) (m : nat) : (term992 A s f m _55846 n) = (term996 A n _55846 s f m).
Proof. exact (@lem4741265 (term312 _55846 n) (term993 A _55846 s f m)). Qed.
Lemma lem4741268 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4741269 (_55846 : nat) (n : nat) : (term618 _55846 n) = (Peano.lt _55846 n).
Proof. exact (@lem4741268 (Peano.lt _55846 n)). Qed.
Lemma lem4741270 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4741271 (_55846 : nat) (n : nat) : (term619 _55846 n) = (term298 _55846 n).
Proof. exact (MK_COMB (@lem4741270) (@lem4741269 _55846 n)). Qed.
Lemma lem4741272 {A : Type'} (_55846 : nat) (s : A -> Prop) (f : nat -> A) (m : nat) : (term993 A _55846 s f m) = (term993 A _55846 s f m).
Proof. exact (eq_refl (term993 A _55846 s f m)). Qed.
Lemma lem4741273 {A : Type'} (n : nat) (_55846 : nat) (s : A -> Prop) (f : nat -> A) (m : nat) : (term996 A n _55846 s f m) = (term997 A n _55846 s f m).
Proof. exact (MK_COMB (@lem4741271 _55846 n) (@lem4741272 A _55846 s f m)). Qed.
Lemma lem4741274 {A : Type'} (n : nat) (_55846 : nat) (s : A -> Prop) (f : nat -> A) (m : nat) : (term992 A s f m _55846 n) = (term997 A n _55846 s f m).
Proof. exact (TRANS (@lem4741266 A n _55846 s f m) (@lem4741273 A n _55846 s f m)). Qed.
Lemma lem4741277 {A : Type'} (_55846 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m) = x) : term997 A n _55846 s f m.
Proof. exact (EQ_MP (@lem4741274 A n _55846 s f m) (@lem4741263 A _55846 n s a f m x h1 h2 h3)). Qed.
Lemma lem4741278 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m) = x) : term1009 A n s f m.
Proof. exact (@lem4741277 A m n s a f m x h1 h2 h3). Qed.
Lemma lem4741281 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m) = x) : term1010 A s f m.
Proof. exact (@lem4741278 A n s a f m x h1 h3 h4 (@lem4741234 m n h2)). Qed.
Lemma lem4741282 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m) = x) : term1011 A s f m.
Proof. exact (fun h0 : term1012 A s f m => @lem4741281 A s n a f m x h1 h2 h3 h4). Qed.
Lemma lem4741284 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741285 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) : (term1011 A s f m) = (term1010 A s f m).
Proof. exact (@lem4741284 (term1010 A s f m)). Qed.
Lemma lem4741286 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m) = x) : term1010 A s f m.
Proof. exact (EQ_MP (@lem4741285 A s f m) (@lem4741282 A s n a f m x h1 h2 h3 h4)). Qed.
Lemma lem4741288 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4741289 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4741288 A x). Qed.
Lemma lem4741290 {A : Type'} (f : nat -> A) (m : nat) : (f m) = (f m).
Proof. exact (@lem4741289 A (f m)). Qed.
Lemma lem4741291 {A : Type'} (f : nat -> A) (m : nat) : term1013 A f m.
Proof. exact (fun h0 : term1014 A f m => @lem4741290 A f m). Qed.
Lemma lem4741293 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741294 {A : Type'} (f : nat -> A) (m : nat) : (term1013 A f m) = ((f m) = (f m)).
Proof. exact (@lem4741293 ((f m) = (f m))). Qed.
Lemma lem4741295 {A : Type'} (f : nat -> A) (m : nat) : (f m) = (f m).
Proof. exact (EQ_MP (@lem4741294 A f m) (@lem4741291 A f m)). Qed.
Lemma lem4741297 (a : Prop) (b : Prop) : (term1002 a b) = (term1003 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4741298 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (_55859 : A) : (term963 A _55857 _55858 _55859) = (term1004 A _55857 _55858 _55859).
Proof. exact (@lem4741297 (term380 A _55858 _55857 _55859) (_55858 = _55859)). Qed.
Lemma lem4741300 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4741301 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (_55859 : A) : (term1004 A _55857 _55858 _55859) = (term1005 A _55857 _55858 _55859).
Proof. exact (@lem4741300 (term1006 A _55857 _55858 _55859)). Qed.
Lemma lem4741302 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (_55859 : A) : (term963 A _55857 _55858 _55859) = (term1005 A _55857 _55858 _55859).
Proof. exact (TRANS (@lem4741298 A _55857 _55858 _55859) (@lem4741301 A _55857 _55858 _55859)). Qed.
Lemma lem4741304 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m) = x) : term1015 A s f m.
Proof. exact (conj (@lem4741286 A s n a f m x h1 h2 h3 h4) (@lem4741295 A f m)). Qed.
Lemma lem4741306 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (_55859 : A) (h1 : term323 A) : term1005 A _55857 _55858 _55859.
Proof. exact (EQ_MP (@lem4741302 A _55857 _55858 _55859) (@lem4733631 A _55857 _55858 _55859 h1)). Qed.
Lemma lem4741307 {A : Type'} (_55857 : A -> Prop) (_55858 : A) (_55859 : A) (h1 : term323 A) : term1005 A _55857 _55858 _55859.
Proof. exact (@lem4741306 A _55857 _55858 _55859 h1). Qed.
Lemma lem4741308 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (h1 : term323 A) : term1016 A s f m.
Proof. exact (@lem4741307 A s (f m) (f m) h1). Qed.
Lemma lem4741311 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (@lem4741308 A s f m h1 (@lem4741304 A s n a f m x h2 h3 h4 h5)). Qed.
Lemma lem4741312 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : term632.
Proof. exact (fun h0 : ~ False => @lem4741311 A s n a f m x h1 h2 h3 h4 h5). Qed.
Lemma lem4741314 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741315 : term632 = False.
Proof. exact (@lem4741314 False). Qed.
Lemma lem4741316 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4741315) (@lem4741312 A s n a f m x h1 h2 h3 h4 h5)). Qed.
Lemma lem4741440 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4741441 (m : nat) (n : nat) (h1 : Peano.lt m n) : term611 m n.
Proof. exact (fun h0 : term312 m n => @lem4741440 m n h1). Qed.
Lemma lem4741443 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741444 (m : nat) (n : nat) : (term611 m n) = (Peano.lt m n).
Proof. exact (@lem4741443 (Peano.lt m n)). Qed.
Lemma lem4741445 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem4741444 m n) (@lem4741441 m n h1)). Qed.
Lemma lem4741451 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4741452 {A : Type'} (s : A -> Prop) (f : nat -> A) (_55860 : nat) (n : nat) : (term973 A _55860 s f n) = (term1017 A s f _55860 n).
Proof. exact (@lem4741451 (term993 A _55860 s f n) (term312 _55860 n)). Qed.
Lemma lem4741458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4741459 {A : Type'} (s : A -> Prop) (f : nat -> A) (_55860 : nat) (n : nat) : (term1018 A _55860 s f n) = (term1019 A s f _55860 n).
Proof. exact (MK_COMB (@lem4741458) (@lem4741452 A s f _55860 n)). Qed.
Lemma lem4741465 {A : Type'} (s : A -> Prop) (f : nat -> A) (_55860 : nat) (n : nat) : (term1017 A s f _55860 n) = (term1017 A s f _55860 n).
Proof. exact (eq_refl (term1017 A s f _55860 n)). Qed.
Lemma lem4741466 {A : Type'} (s : A -> Prop) (f : nat -> A) (_55860 : nat) (n : nat) : ((term973 A _55860 s f n) = (term1017 A s f _55860 n)) = ((term1017 A s f _55860 n) = (term1017 A s f _55860 n)).
Proof. exact (MK_COMB (@lem4741459 A s f _55860 n) (@lem4741465 A s f _55860 n)). Qed.
Lemma lem4741468 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4741469 (x : Prop) : (x = x) = True.
Proof. exact (@lem4741468 Prop x). Qed.
Lemma lem4741470 {A : Type'} (s : A -> Prop) (f : nat -> A) (_55860 : nat) (n : nat) : ((term1017 A s f _55860 n) = (term1017 A s f _55860 n)) = True.
Proof. exact (@lem4741469 (term1017 A s f _55860 n)). Qed.
Lemma lem4741471 {A : Type'} (s : A -> Prop) (f : nat -> A) (_55860 : nat) (n : nat) : ((term973 A _55860 s f n) = (term1017 A s f _55860 n)) = True.
Proof. exact (TRANS (@lem4741466 A s f _55860 n) (@lem4741470 A s f _55860 n)). Qed.
Lemma lem4741472 {A : Type'} (s : A -> Prop) (f : nat -> A) (_55860 : nat) (n : nat) : True = ((term973 A _55860 s f n) = (term1017 A s f _55860 n)).
Proof. exact (SYM (@lem4741471 A s f _55860 n)). Qed.
Lemma lem4741473 {A : Type'} (s : A -> Prop) (f : nat -> A) (_55860 : nat) (n : nat) : (term973 A _55860 s f n) = (term1017 A s f _55860 n).
Proof. exact (EQ_MP (@lem4741472 A s f _55860 n) (@lem0)). Qed.
Lemma lem4741474 {A : Type'} (_55860 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) (h4 : m' = n) : term1017 A s f _55860 n.
Proof. exact (EQ_MP (@lem4741473 A s f _55860 n) (@lem4734168 A _55860 s a f x m' n h1 h2 h3 h4)). Qed.
Lemma lem4741476 (b : Prop) (a : Prop) : (a \/ b) = (term616 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4741477 {A : Type'} (_55860 : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : (term1017 A s f _55860 n) = (term1020 A _55860 s f n).
Proof. exact (@lem4741476 (term312 _55860 n) (term993 A _55860 s f n)). Qed.
Lemma lem4741479 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4741480 (_55860 : nat) (n : nat) : (term618 _55860 n) = (Peano.lt _55860 n).
Proof. exact (@lem4741479 (Peano.lt _55860 n)). Qed.
Lemma lem4741481 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4741482 (_55860 : nat) (n : nat) : (term619 _55860 n) = (term298 _55860 n).
Proof. exact (MK_COMB (@lem4741481) (@lem4741480 _55860 n)). Qed.
Lemma lem4741483 {A : Type'} (_55860 : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : (term993 A _55860 s f n) = (term993 A _55860 s f n).
Proof. exact (eq_refl (term993 A _55860 s f n)). Qed.
Lemma lem4741484 {A : Type'} (_55860 : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : (term1020 A _55860 s f n) = (term1021 A _55860 s f n).
Proof. exact (MK_COMB (@lem4741482 _55860 n) (@lem4741483 A _55860 s f n)). Qed.
Lemma lem4741485 {A : Type'} (_55860 : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : (term1017 A s f _55860 n) = (term1021 A _55860 s f n).
Proof. exact (TRANS (@lem4741477 A _55860 s f n) (@lem4741484 A _55860 s f n)). Qed.
Lemma lem4741488 {A : Type'} (_55860 : nat) (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) (h4 : m' = n) : term1021 A _55860 s f n.
Proof. exact (EQ_MP (@lem4741485 A _55860 s f n) (@lem4741474 A _55860 s a f x m' n h1 h2 h3 h4)). Qed.
Lemma lem4741489 {A : Type'} (m : nat) (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) (h4 : m' = n) : term1021 A m s f n.
Proof. exact (@lem4741488 A m s a f x m' n h1 h2 h3 h4). Qed.
Lemma lem4741492 {A : Type'} (s : A -> Prop) (m : nat) (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m') = x) (h5 : m' = n) : term993 A m s f n.
Proof. exact (@lem4741489 A m s a f x m' n h1 h3 h4 h5 (@lem4741445 m n h2)). Qed.
Lemma lem4741493 {A : Type'} (s : A -> Prop) (m : nat) (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m') = x) (h5 : m' = n) : term998 A m s f n.
Proof. exact (fun h0 : term999 A m s f n => @lem4741492 A s m a f x m' n h1 h2 h3 h4 h5). Qed.
Lemma lem4741495 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741496 {A : Type'} (m : nat) (s : A -> Prop) (f : nat -> A) (n : nat) : (term998 A m s f n) = (term993 A m s f n).
Proof. exact (@lem4741495 (term993 A m s f n)). Qed.
Lemma lem4741497 {A : Type'} (s : A -> Prop) (m : nat) (a : A) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m') = x) (h5 : m' = n) : term993 A m s f n.
Proof. exact (EQ_MP (@lem4741496 A m s f n) (@lem4741493 A s m a f x m' n h1 h2 h3 h4 h5)). Qed.
Lemma lem4741499 {A : Type'} (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : (f m) = x) (h2 : (f m') = x) (h3 : m' = n) : (f m) = (f n).
Proof. exact (EQ_MP (@lem4734058 A m f m' n h3) (@lem4733825 A m f m' x h1 h2)). Qed.
Lemma lem4741500 {A : Type'} (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : (f m) = x) (h2 : (f m') = x) (h3 : m' = n) : term1000 A m f n.
Proof. exact (fun h0 : term1001 A m f n => @lem4741499 A m f x m' n h1 h2 h3). Qed.
Lemma lem4741502 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741503 {A : Type'} (m : nat) (f : nat -> A) (n : nat) : (term1000 A m f n) = ((f m) = (f n)).
Proof. exact (@lem4741502 ((f m) = (f n))). Qed.
Lemma lem4741504 {A : Type'} (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : (f m) = x) (h2 : (f m') = x) (h3 : m' = n) : (f m) = (f n).
Proof. exact (EQ_MP (@lem4741503 A m f n) (@lem4741500 A m f x m' n h1 h2 h3)). Qed.
Lemma lem4741506 (a : Prop) (b : Prop) : (term1002 a b) = (term1003 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4741507 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (_55873 : A) : (term963 A _55871 _55872 _55873) = (term1004 A _55871 _55872 _55873).
Proof. exact (@lem4741506 (term380 A _55872 _55871 _55873) (_55872 = _55873)). Qed.
Lemma lem4741509 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4741510 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (_55873 : A) : (term1004 A _55871 _55872 _55873) = (term1005 A _55871 _55872 _55873).
Proof. exact (@lem4741509 (term1006 A _55871 _55872 _55873)). Qed.
Lemma lem4741511 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (_55873 : A) : (term963 A _55871 _55872 _55873) = (term1005 A _55871 _55872 _55873).
Proof. exact (TRANS (@lem4741507 A _55871 _55872 _55873) (@lem4741510 A _55871 _55872 _55873)). Qed.
Lemma lem4741513 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term268 A n f s a) (h2 : Peano.lt m n) (h3 : a = x) (h4 : (f m) = x) (h5 : (f m') = x) (h6 : m' = n) : term1007 A s m f n.
Proof. exact (conj (@lem4741497 A s m a f x m' n h1 h2 h3 h5 h6) (@lem4741504 A m f x m' n h4 h5 h6)). Qed.
Lemma lem4741515 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (_55873 : A) (h1 : term323 A) : term1005 A _55871 _55872 _55873.
Proof. exact (EQ_MP (@lem4741511 A _55871 _55872 _55873) (@lem4734294 A _55871 _55872 _55873 h1)). Qed.
Lemma lem4741516 {A : Type'} (_55871 : A -> Prop) (_55872 : A) (_55873 : A) (h1 : term323 A) : term1005 A _55871 _55872 _55873.
Proof. exact (@lem4741515 A _55871 _55872 _55873 h1). Qed.
Lemma lem4741517 {A : Type'} (s : A -> Prop) (m : nat) (f : nat -> A) (n : nat) (h1 : term323 A) : term1008 A s m f n.
Proof. exact (@lem4741516 A s (f m) (f n) h1). Qed.
Lemma lem4741520 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (@lem4741517 A s m f n h1 (@lem4741513 A s a m f x m' n h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem4741521 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : term632.
Proof. exact (fun h0 : ~ False => @lem4741520 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem4741523 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741524 : term632 = False.
Proof. exact (@lem4741523 False). Qed.
Lemma lem4741525 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4741524) (@lem4741521 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem4741649 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4741650 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : term611 m' n.
Proof. exact (fun h0 : term312 m' n => @lem4741649 m' n h1). Qed.
Lemma lem4741652 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741653 (m' : nat) (n : nat) : (term611 m' n) = (Peano.lt m' n).
Proof. exact (@lem4741652 (Peano.lt m' n)). Qed.
Lemma lem4741654 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (EQ_MP (@lem4741653 m' n) (@lem4741650 m' n h1)). Qed.
Lemma lem4741657 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4741659 (m' : nat) (n : nat) : (term312 m' n) = (term991 m' n).
Proof. exact (@lem4741657 (Peano.lt m' n)). Qed.
Lemma lem4741662 (m' : nat) (n : nat) (h1 : term312 m' n) : term991 m' n.
Proof. exact (EQ_MP (@lem4741659 m' n) (@lem4734723 m' n h1)). Qed.
Lemma lem4741665 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (@lem4741662 m' n h1 (@lem4741654 m' n h2)). Qed.
Lemma lem4741666 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : term632.
Proof. exact (fun h0 : ~ False => @lem4741665 m' n h1 h2). Qed.
Lemma lem4741668 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741669 : term632 = False.
Proof. exact (@lem4741668 False). Qed.
Lemma lem4741670 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4741669) (@lem4741666 m' n h1 h2)). Qed.
Lemma lem4741794 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4741795 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : term611 m' n.
Proof. exact (fun h0 : term312 m' n => @lem4741794 m' n h1). Qed.
Lemma lem4741797 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741798 (m' : nat) (n : nat) : (term611 m' n) = (Peano.lt m' n).
Proof. exact (@lem4741797 (Peano.lt m' n)). Qed.
Lemma lem4741799 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (EQ_MP (@lem4741798 m' n) (@lem4741795 m' n h1)). Qed.
Lemma lem4741805 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4741806 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55888 : nat) (n : nat) : (term961 A n _55888 s f m') = (term992 A s f m' _55888 n).
Proof. exact (@lem4741805 (term993 A _55888 s f m') (term312 _55888 n)). Qed.
Lemma lem4741812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4741813 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55888 : nat) (n : nat) : (term994 A n _55888 s f m') = (term995 A s f m' _55888 n).
Proof. exact (MK_COMB (@lem4741812) (@lem4741806 A s f m' _55888 n)). Qed.
Lemma lem4741819 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55888 : nat) (n : nat) : (term992 A s f m' _55888 n) = (term992 A s f m' _55888 n).
Proof. exact (eq_refl (term992 A s f m' _55888 n)). Qed.
Lemma lem4741820 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55888 : nat) (n : nat) : ((term961 A n _55888 s f m') = (term992 A s f m' _55888 n)) = ((term992 A s f m' _55888 n) = (term992 A s f m' _55888 n)).
Proof. exact (MK_COMB (@lem4741813 A s f m' _55888 n) (@lem4741819 A s f m' _55888 n)). Qed.
Lemma lem4741822 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4741823 (x : Prop) : (x = x) = True.
Proof. exact (@lem4741822 Prop x). Qed.
Lemma lem4741824 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55888 : nat) (n : nat) : ((term992 A s f m' _55888 n) = (term992 A s f m' _55888 n)) = True.
Proof. exact (@lem4741823 (term992 A s f m' _55888 n)). Qed.
Lemma lem4741825 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55888 : nat) (n : nat) : ((term961 A n _55888 s f m') = (term992 A s f m' _55888 n)) = True.
Proof. exact (TRANS (@lem4741820 A s f m' _55888 n) (@lem4741824 A s f m' _55888 n)). Qed.
Lemma lem4741826 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55888 : nat) (n : nat) : True = ((term961 A n _55888 s f m') = (term992 A s f m' _55888 n)).
Proof. exact (SYM (@lem4741825 A s f m' _55888 n)). Qed.
Lemma lem4741827 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55888 : nat) (n : nat) : (term961 A n _55888 s f m') = (term992 A s f m' _55888 n).
Proof. exact (EQ_MP (@lem4741826 A s f m' _55888 n) (@lem0)). Qed.
Lemma lem4741828 {A : Type'} (_55888 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term992 A s f m' _55888 n.
Proof. exact (EQ_MP (@lem4741827 A s f m' _55888 n) (@lem4735291 A _55888 n s a f m' x h1 h2 h3)). Qed.
Lemma lem4741830 (b : Prop) (a : Prop) : (a \/ b) = (term616 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4741831 {A : Type'} (n : nat) (_55888 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term992 A s f m' _55888 n) = (term996 A n _55888 s f m').
Proof. exact (@lem4741830 (term312 _55888 n) (term993 A _55888 s f m')). Qed.
Lemma lem4741833 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4741834 (_55888 : nat) (n : nat) : (term618 _55888 n) = (Peano.lt _55888 n).
Proof. exact (@lem4741833 (Peano.lt _55888 n)). Qed.
Lemma lem4741835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4741836 (_55888 : nat) (n : nat) : (term619 _55888 n) = (term298 _55888 n).
Proof. exact (MK_COMB (@lem4741835) (@lem4741834 _55888 n)). Qed.
Lemma lem4741837 {A : Type'} (_55888 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term993 A _55888 s f m') = (term993 A _55888 s f m').
Proof. exact (eq_refl (term993 A _55888 s f m')). Qed.
Lemma lem4741838 {A : Type'} (n : nat) (_55888 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term996 A n _55888 s f m') = (term997 A n _55888 s f m').
Proof. exact (MK_COMB (@lem4741836 _55888 n) (@lem4741837 A _55888 s f m')). Qed.
Lemma lem4741839 {A : Type'} (n : nat) (_55888 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term992 A s f m' _55888 n) = (term997 A n _55888 s f m').
Proof. exact (TRANS (@lem4741831 A n _55888 s f m') (@lem4741838 A n _55888 s f m')). Qed.
Lemma lem4741842 {A : Type'} (_55888 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term997 A n _55888 s f m'.
Proof. exact (EQ_MP (@lem4741839 A n _55888 s f m') (@lem4741828 A _55888 n s a f m' x h1 h2 h3)). Qed.
Lemma lem4741843 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term1009 A n s f m'.
Proof. exact (@lem4741842 A m' n s a f m' x h1 h2 h3). Qed.
Lemma lem4741846 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m' n) (h3 : a = x) (h4 : (f m') = x) : term1010 A s f m'.
Proof. exact (@lem4741843 A n s a f m' x h1 h3 h4 (@lem4741799 m' n h2)). Qed.
Lemma lem4741847 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m' n) (h3 : a = x) (h4 : (f m') = x) : term1011 A s f m'.
Proof. exact (fun h0 : term1012 A s f m' => @lem4741846 A s n a f m' x h1 h2 h3 h4). Qed.
Lemma lem4741849 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741850 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) : (term1011 A s f m') = (term1010 A s f m').
Proof. exact (@lem4741849 (term1010 A s f m')). Qed.
Lemma lem4741851 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m' n) (h3 : a = x) (h4 : (f m') = x) : term1010 A s f m'.
Proof. exact (EQ_MP (@lem4741850 A s f m') (@lem4741847 A s n a f m' x h1 h2 h3 h4)). Qed.
Lemma lem4741853 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4741854 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4741853 A x). Qed.
Lemma lem4741855 {A : Type'} (f : nat -> A) (m' : nat) : (f m') = (f m').
Proof. exact (@lem4741854 A (f m')). Qed.
Lemma lem4741856 {A : Type'} (f : nat -> A) (m' : nat) : term1013 A f m'.
Proof. exact (fun h0 : term1014 A f m' => @lem4741855 A f m'). Qed.
Lemma lem4741858 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741859 {A : Type'} (f : nat -> A) (m' : nat) : (term1013 A f m') = ((f m') = (f m')).
Proof. exact (@lem4741858 ((f m') = (f m'))). Qed.
Lemma lem4741860 {A : Type'} (f : nat -> A) (m' : nat) : (f m') = (f m').
Proof. exact (EQ_MP (@lem4741859 A f m') (@lem4741856 A f m')). Qed.
Lemma lem4741862 (a : Prop) (b : Prop) : (term1002 a b) = (term1003 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4741863 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (_55901 : A) : (term963 A _55899 _55900 _55901) = (term1004 A _55899 _55900 _55901).
Proof. exact (@lem4741862 (term380 A _55900 _55899 _55901) (_55900 = _55901)). Qed.
Lemma lem4741865 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4741866 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (_55901 : A) : (term1004 A _55899 _55900 _55901) = (term1005 A _55899 _55900 _55901).
Proof. exact (@lem4741865 (term1006 A _55899 _55900 _55901)). Qed.
Lemma lem4741867 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (_55901 : A) : (term963 A _55899 _55900 _55901) = (term1005 A _55899 _55900 _55901).
Proof. exact (TRANS (@lem4741863 A _55899 _55900 _55901) (@lem4741866 A _55899 _55900 _55901)). Qed.
Lemma lem4741869 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m' n) (h3 : a = x) (h4 : (f m') = x) : term1015 A s f m'.
Proof. exact (conj (@lem4741851 A s n a f m' x h1 h2 h3 h4) (@lem4741860 A f m')). Qed.
Lemma lem4741871 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (_55901 : A) (h1 : term323 A) : term1005 A _55899 _55900 _55901.
Proof. exact (EQ_MP (@lem4741867 A _55899 _55900 _55901) (@lem4735417 A _55899 _55900 _55901 h1)). Qed.
Lemma lem4741872 {A : Type'} (_55899 : A -> Prop) (_55900 : A) (_55901 : A) (h1 : term323 A) : term1005 A _55899 _55900 _55901.
Proof. exact (@lem4741871 A _55899 _55900 _55901 h1). Qed.
Lemma lem4741873 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (h1 : term323 A) : term1016 A s f m'.
Proof. exact (@lem4741872 A s (f m') (f m') h1). Qed.
Lemma lem4741876 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (@lem4741873 A s f m' h1 (@lem4741869 A s n a f m' x h2 h3 h4 h5)). Qed.
Lemma lem4741877 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : term632.
Proof. exact (fun h0 : ~ False => @lem4741876 A s n a f m' x h1 h2 h3 h4 h5). Qed.
Lemma lem4741879 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4741880 : term632 = False.
Proof. exact (@lem4741879 False). Qed.
Lemma lem4741881 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4741880) (@lem4741877 A s n a f m' x h1 h2 h3 h4 h5)). Qed.
Lemma lem4742005 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4742006 (n : nat) : n = n.
Proof. exact (@lem4742005 n). Qed.
Lemma lem4742007 (n : nat) : term983 n.
Proof. exact (fun h0 : term981 n => @lem4742006 n). Qed.
Lemma lem4742009 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742010 (n : nat) : (term983 n) = (n = n).
Proof. exact (@lem4742009 (n = n)). Qed.
Lemma lem4742011 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem4742010 n) (@lem4742007 n)). Qed.
Lemma lem4742014 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4742016 (n : nat) : (term981 n) = (term1022 n).
Proof. exact (@lem4742014 (n = n)). Qed.
Lemma lem4742019 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term1022 n.
Proof. exact (EQ_MP (@lem4742016 n) (@lem4736026 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4742022 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (@lem4742019 A f x m m' n h1 h2 h3 (@lem4742011 n)). Qed.
Lemma lem4742023 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term632.
Proof. exact (fun h0 : ~ False => @lem4742022 A f x m m' n h1 h2 h3). Qed.
Lemma lem4742025 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742026 : term632 = False.
Proof. exact (@lem4742025 False). Qed.
Lemma lem4742151 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4742152 (n : nat) : n = n.
Proof. exact (@lem4742151 n). Qed.
Lemma lem4742153 (n : nat) : term983 n.
Proof. exact (fun h0 : term981 n => @lem4742152 n). Qed.
Lemma lem4742155 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742156 (n : nat) : (term983 n) = (n = n).
Proof. exact (@lem4742155 (n = n)). Qed.
Lemma lem4742157 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem4742156 n) (@lem4742153 n)). Qed.
Lemma lem4742160 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4742162 (n : nat) : (term981 n) = (term1022 n).
Proof. exact (@lem4742160 (n = n)). Qed.
Lemma lem4742165 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term1022 n.
Proof. exact (EQ_MP (@lem4742162 n) (@lem4736899 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4742168 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (@lem4742165 A f x m m' n h1 h2 h3 (@lem4742157 n)). Qed.
Lemma lem4742169 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term632.
Proof. exact (fun h0 : ~ False => @lem4742168 A f x m m' n h1 h2 h3). Qed.
Lemma lem4742171 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742172 : term632 = False.
Proof. exact (@lem4742171 False). Qed.
Lemma lem4742297 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4742298 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : term611 m' n.
Proof. exact (fun h0 : term312 m' n => @lem4742297 m' n h1). Qed.
Lemma lem4742300 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742301 (m' : nat) (n : nat) : (term611 m' n) = (Peano.lt m' n).
Proof. exact (@lem4742300 (Peano.lt m' n)). Qed.
Lemma lem4742302 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (EQ_MP (@lem4742301 m' n) (@lem4742298 m' n h1)). Qed.
Lemma lem4742305 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4742307 (m' : nat) (n : nat) : (term312 m' n) = (term991 m' n).
Proof. exact (@lem4742305 (Peano.lt m' n)). Qed.
Lemma lem4742310 (m' : nat) (n : nat) (h1 : term312 m' n) : term991 m' n.
Proof. exact (EQ_MP (@lem4742307 m' n) (@lem4737578 m' n h1)). Qed.
Lemma lem4742313 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (@lem4742310 m' n h1 (@lem4742302 m' n h2)). Qed.
Lemma lem4742314 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : term632.
Proof. exact (fun h0 : ~ False => @lem4742313 m' n h1 h2). Qed.
Lemma lem4742316 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742317 : term632 = False.
Proof. exact (@lem4742316 False). Qed.
Lemma lem4742318 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742317) (@lem4742314 m' n h1 h2)). Qed.
Lemma lem4742442 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (h1). Qed.
Lemma lem4742443 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : term611 m' n.
Proof. exact (fun h0 : term312 m' n => @lem4742442 m' n h1). Qed.
Lemma lem4742445 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742446 (m' : nat) (n : nat) : (term611 m' n) = (Peano.lt m' n).
Proof. exact (@lem4742445 (Peano.lt m' n)). Qed.
Lemma lem4742447 (m' : nat) (n : nat) (h1 : Peano.lt m' n) : Peano.lt m' n.
Proof. exact (EQ_MP (@lem4742446 m' n) (@lem4742443 m' n h1)). Qed.
Lemma lem4742453 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4742454 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55944 : nat) (n : nat) : (term961 A n _55944 s f m') = (term992 A s f m' _55944 n).
Proof. exact (@lem4742453 (term993 A _55944 s f m') (term312 _55944 n)). Qed.
Lemma lem4742460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4742461 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55944 : nat) (n : nat) : (term994 A n _55944 s f m') = (term995 A s f m' _55944 n).
Proof. exact (MK_COMB (@lem4742460) (@lem4742454 A s f m' _55944 n)). Qed.
Lemma lem4742467 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55944 : nat) (n : nat) : (term992 A s f m' _55944 n) = (term992 A s f m' _55944 n).
Proof. exact (eq_refl (term992 A s f m' _55944 n)). Qed.
Lemma lem4742468 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55944 : nat) (n : nat) : ((term961 A n _55944 s f m') = (term992 A s f m' _55944 n)) = ((term992 A s f m' _55944 n) = (term992 A s f m' _55944 n)).
Proof. exact (MK_COMB (@lem4742461 A s f m' _55944 n) (@lem4742467 A s f m' _55944 n)). Qed.
Lemma lem4742470 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4742471 (x : Prop) : (x = x) = True.
Proof. exact (@lem4742470 Prop x). Qed.
Lemma lem4742472 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55944 : nat) (n : nat) : ((term992 A s f m' _55944 n) = (term992 A s f m' _55944 n)) = True.
Proof. exact (@lem4742471 (term992 A s f m' _55944 n)). Qed.
Lemma lem4742473 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55944 : nat) (n : nat) : ((term961 A n _55944 s f m') = (term992 A s f m' _55944 n)) = True.
Proof. exact (TRANS (@lem4742468 A s f m' _55944 n) (@lem4742472 A s f m' _55944 n)). Qed.
Lemma lem4742474 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55944 : nat) (n : nat) : True = ((term961 A n _55944 s f m') = (term992 A s f m' _55944 n)).
Proof. exact (SYM (@lem4742473 A s f m' _55944 n)). Qed.
Lemma lem4742475 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (_55944 : nat) (n : nat) : (term961 A n _55944 s f m') = (term992 A s f m' _55944 n).
Proof. exact (EQ_MP (@lem4742474 A s f m' _55944 n) (@lem0)). Qed.
Lemma lem4742476 {A : Type'} (_55944 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term992 A s f m' _55944 n.
Proof. exact (EQ_MP (@lem4742475 A s f m' _55944 n) (@lem4738145 A _55944 n s a f m' x h1 h2 h3)). Qed.
Lemma lem4742478 (b : Prop) (a : Prop) : (a \/ b) = (term616 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4742479 {A : Type'} (n : nat) (_55944 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term992 A s f m' _55944 n) = (term996 A n _55944 s f m').
Proof. exact (@lem4742478 (term312 _55944 n) (term993 A _55944 s f m')). Qed.
Lemma lem4742481 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4742482 (_55944 : nat) (n : nat) : (term618 _55944 n) = (Peano.lt _55944 n).
Proof. exact (@lem4742481 (Peano.lt _55944 n)). Qed.
Lemma lem4742483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4742484 (_55944 : nat) (n : nat) : (term619 _55944 n) = (term298 _55944 n).
Proof. exact (MK_COMB (@lem4742483) (@lem4742482 _55944 n)). Qed.
Lemma lem4742485 {A : Type'} (_55944 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term993 A _55944 s f m') = (term993 A _55944 s f m').
Proof. exact (eq_refl (term993 A _55944 s f m')). Qed.
Lemma lem4742486 {A : Type'} (n : nat) (_55944 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term996 A n _55944 s f m') = (term997 A n _55944 s f m').
Proof. exact (MK_COMB (@lem4742484 _55944 n) (@lem4742485 A _55944 s f m')). Qed.
Lemma lem4742487 {A : Type'} (n : nat) (_55944 : nat) (s : A -> Prop) (f : nat -> A) (m' : nat) : (term992 A s f m' _55944 n) = (term997 A n _55944 s f m').
Proof. exact (TRANS (@lem4742479 A n _55944 s f m') (@lem4742486 A n _55944 s f m')). Qed.
Lemma lem4742490 {A : Type'} (_55944 : nat) (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term997 A n _55944 s f m'.
Proof. exact (EQ_MP (@lem4742487 A n _55944 s f m') (@lem4742476 A _55944 n s a f m' x h1 h2 h3)). Qed.
Lemma lem4742491 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : a = x) (h3 : (f m') = x) : term1009 A n s f m'.
Proof. exact (@lem4742490 A m' n s a f m' x h1 h2 h3). Qed.
Lemma lem4742494 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m' n) (h3 : a = x) (h4 : (f m') = x) : term1010 A s f m'.
Proof. exact (@lem4742491 A n s a f m' x h1 h3 h4 (@lem4742447 m' n h2)). Qed.
Lemma lem4742495 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m' n) (h3 : a = x) (h4 : (f m') = x) : term1011 A s f m'.
Proof. exact (fun h0 : term1012 A s f m' => @lem4742494 A s n a f m' x h1 h2 h3 h4). Qed.
Lemma lem4742497 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742498 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) : (term1011 A s f m') = (term1010 A s f m').
Proof. exact (@lem4742497 (term1010 A s f m')). Qed.
Lemma lem4742499 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m' n) (h3 : a = x) (h4 : (f m') = x) : term1010 A s f m'.
Proof. exact (EQ_MP (@lem4742498 A s f m') (@lem4742495 A s n a f m' x h1 h2 h3 h4)). Qed.
Lemma lem4742501 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4742502 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4742501 A x). Qed.
Lemma lem4742503 {A : Type'} (f : nat -> A) (m' : nat) : (f m') = (f m').
Proof. exact (@lem4742502 A (f m')). Qed.
Lemma lem4742504 {A : Type'} (f : nat -> A) (m' : nat) : term1013 A f m'.
Proof. exact (fun h0 : term1014 A f m' => @lem4742503 A f m'). Qed.
Lemma lem4742506 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742507 {A : Type'} (f : nat -> A) (m' : nat) : (term1013 A f m') = ((f m') = (f m')).
Proof. exact (@lem4742506 ((f m') = (f m'))). Qed.
Lemma lem4742508 {A : Type'} (f : nat -> A) (m' : nat) : (f m') = (f m').
Proof. exact (EQ_MP (@lem4742507 A f m') (@lem4742504 A f m')). Qed.
Lemma lem4742510 (a : Prop) (b : Prop) : (term1002 a b) = (term1003 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4742511 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (_55957 : A) : (term963 A _55955 _55956 _55957) = (term1004 A _55955 _55956 _55957).
Proof. exact (@lem4742510 (term380 A _55956 _55955 _55957) (_55956 = _55957)). Qed.
Lemma lem4742513 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4742514 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (_55957 : A) : (term1004 A _55955 _55956 _55957) = (term1005 A _55955 _55956 _55957).
Proof. exact (@lem4742513 (term1006 A _55955 _55956 _55957)). Qed.
Lemma lem4742515 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (_55957 : A) : (term963 A _55955 _55956 _55957) = (term1005 A _55955 _55956 _55957).
Proof. exact (TRANS (@lem4742511 A _55955 _55956 _55957) (@lem4742514 A _55955 _55956 _55957)). Qed.
Lemma lem4742517 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term268 A n f s a) (h2 : Peano.lt m' n) (h3 : a = x) (h4 : (f m') = x) : term1015 A s f m'.
Proof. exact (conj (@lem4742499 A s n a f m' x h1 h2 h3 h4) (@lem4742508 A f m')). Qed.
Lemma lem4742519 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (_55957 : A) (h1 : term323 A) : term1005 A _55955 _55956 _55957.
Proof. exact (EQ_MP (@lem4742515 A _55955 _55956 _55957) (@lem4738271 A _55955 _55956 _55957 h1)). Qed.
Lemma lem4742520 {A : Type'} (_55955 : A -> Prop) (_55956 : A) (_55957 : A) (h1 : term323 A) : term1005 A _55955 _55956 _55957.
Proof. exact (@lem4742519 A _55955 _55956 _55957 h1). Qed.
Lemma lem4742521 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (h1 : term323 A) : term1016 A s f m'.
Proof. exact (@lem4742520 A s (f m') (f m') h1). Qed.
Lemma lem4742524 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (@lem4742521 A s f m' h1 (@lem4742517 A s n a f m' x h2 h3 h4 h5)). Qed.
Lemma lem4742525 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : term632.
Proof. exact (fun h0 : ~ False => @lem4742524 A s n a f m' x h1 h2 h3 h4 h5). Qed.
Lemma lem4742527 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742528 : term632 = False.
Proof. exact (@lem4742527 False). Qed.
Lemma lem4742529 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742528) (@lem4742525 A s n a f m' x h1 h2 h3 h4 h5)). Qed.
Lemma lem4742653 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4742654 (n : nat) : n = n.
Proof. exact (@lem4742653 n). Qed.
Lemma lem4742655 (n : nat) : term983 n.
Proof. exact (fun h0 : term981 n => @lem4742654 n). Qed.
Lemma lem4742657 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742658 (n : nat) : (term983 n) = (n = n).
Proof. exact (@lem4742657 (n = n)). Qed.
Lemma lem4742659 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem4742658 n) (@lem4742655 n)). Qed.
Lemma lem4742662 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4742664 (n : nat) : (term981 n) = (term1022 n).
Proof. exact (@lem4742662 (n = n)). Qed.
Lemma lem4742667 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term1022 n.
Proof. exact (EQ_MP (@lem4742664 n) (@lem4739088 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4742670 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (@lem4742667 A f x m m' n h1 h2 h3 (@lem4742659 n)). Qed.
Lemma lem4742671 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term632.
Proof. exact (fun h0 : ~ False => @lem4742670 A f x m m' n h1 h2 h3). Qed.
Lemma lem4742673 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742674 : term632 = False.
Proof. exact (@lem4742673 False). Qed.
Lemma lem4742799 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4742800 (n : nat) : n = n.
Proof. exact (@lem4742799 n). Qed.
Lemma lem4742801 (n : nat) : term983 n.
Proof. exact (fun h0 : term981 n => @lem4742800 n). Qed.
Lemma lem4742803 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742804 (n : nat) : (term983 n) = (n = n).
Proof. exact (@lem4742803 (n = n)). Qed.
Lemma lem4742805 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem4742804 n) (@lem4742801 n)). Qed.
Lemma lem4742808 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4742810 (n : nat) : (term981 n) = (term1022 n).
Proof. exact (@lem4742808 (n = n)). Qed.
Lemma lem4742813 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term1022 n.
Proof. exact (EQ_MP (@lem4742810 n) (@lem4739945 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4742816 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (@lem4742813 A f x m m' n h1 h2 h3 (@lem4742805 n)). Qed.
Lemma lem4742817 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : term632.
Proof. exact (fun h0 : ~ False => @lem4742816 A f x m m' n h1 h2 h3). Qed.
Lemma lem4742819 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4742820 : term632 = False.
Proof. exact (@lem4742819 False). Qed.
Lemma lem4742823 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742820) (@lem4742817 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4742824 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742823 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4739545 m n h2)). Qed.
Lemma lem4742826 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742824 A f x m m' n h1 h2 h3) (@lem4739545 m n h2)). Qed.
Lemma lem4742827 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4742826 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4739338 m' n h3)). Qed.
Lemma lem4742828 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742827 A f x m m' n h1 h2 h3) (@lem4739338 m' n h3)). Qed.
Lemma lem4742829 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742828 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4739311 m n h2)). Qed.
Lemma lem4742831 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742829 A f x m m' n h1 h2 h3) (@lem4739311 m n h2)). Qed.
Lemma lem4742833 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742674) (@lem4742671 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4742834 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742833 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4738688 m n h2)). Qed.
Lemma lem4742836 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742834 A f x m m' n h1 h2 h3) (@lem4738688 m n h2)). Qed.
Lemma lem4742837 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742836 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4738452 m n h2)). Qed.
Lemma lem4742839 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742837 A f x m m' n h1 h2 h3) (@lem4738452 m n h2)). Qed.
Lemma lem4742840 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4742529 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4738243 m' n h3)). Qed.
Lemma lem4742842 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742840 A s n a f m' x h1 h2 h3 h4 h5) (@lem4738243 m' n h3)). Qed.
Lemma lem4742843 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4742842 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4738036 m' n h3)). Qed.
Lemma lem4742845 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742843 A s n a f m' x h1 h2 h3 h4 h5) (@lem4738036 m' n h3)). Qed.
Lemma lem4742846 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4742845 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4737814 m' n h3)). Qed.
Lemma lem4742848 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742846 A s n a f m' x h1 h2 h3 h4 h5) (@lem4737814 m' n h3)). Qed.
Lemma lem4742849 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742318 m' n h1 h2) (fun h3 : False => @lem4737578 m' n h1)). Qed.
Lemma lem4742850 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742849 m' n h1 h2) (@lem4737578 m' n h1)). Qed.
Lemma lem4742851 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4742850 m' n h1 h2) (fun h3 : False => @lem4737564 m' n h2)). Qed.
Lemma lem4742853 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742851 m' n h1 h2) (@lem4737564 m' n h2)). Qed.
Lemma lem4742854 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742853 m' n h1 h2) (fun h3 : False => @lem4737371 m' n h1)). Qed.
Lemma lem4742855 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742854 m' n h1 h2) (@lem4737371 m' n h1)). Qed.
Lemma lem4742856 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4742855 m' n h1 h2) (fun h3 : False => @lem4737357 m' n h2)). Qed.
Lemma lem4742858 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742856 m' n h1 h2) (@lem4737357 m' n h2)). Qed.
Lemma lem4742859 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742858 m' n h1 h2) (fun h3 : False => @lem4737150 m' n h1)). Qed.
Lemma lem4742860 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742859 m' n h1 h2) (@lem4737150 m' n h1)). Qed.
Lemma lem4742861 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4742860 m' n h1 h2) (fun h3 : False => @lem4737136 m' n h2)). Qed.
Lemma lem4742863 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742861 m' n h1 h2) (@lem4737136 m' n h2)). Qed.
Lemma lem4742865 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742172) (@lem4742169 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4742866 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742865 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4736498 m n h2)). Qed.
Lemma lem4742868 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742866 A f x m m' n h1 h2 h3) (@lem4736498 m n h2)). Qed.
Lemma lem4742869 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4742868 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4736291 m' n h3)). Qed.
Lemma lem4742870 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742869 A f x m m' n h1 h2 h3) (@lem4736291 m' n h3)). Qed.
Lemma lem4742871 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742870 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4736263 m n h2)). Qed.
Lemma lem4742873 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742871 A f x m m' n h1 h2 h3) (@lem4736263 m n h2)). Qed.
Lemma lem4742875 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742026) (@lem4742023 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4742876 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742875 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4735598 m n h2)). Qed.
Lemma lem4742878 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742876 A f x m m' n h1 h2 h3) (@lem4735598 m n h2)). Qed.
Lemma lem4742879 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4741881 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4735389 m' n h3)). Qed.
Lemma lem4742881 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742879 A s n a f m' x h1 h2 h3 h4 h5) (@lem4735389 m' n h3)). Qed.
Lemma lem4742882 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4742881 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4735182 m' n h3)). Qed.
Lemma lem4742884 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742882 A s n a f m' x h1 h2 h3 h4 h5) (@lem4735182 m' n h3)). Qed.
Lemma lem4742885 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4742884 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4734960 m' n h3)). Qed.
Lemma lem4742887 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742885 A s n a f m' x h1 h2 h3 h4 h5) (@lem4734960 m' n h3)). Qed.
Lemma lem4742888 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4741670 m' n h1 h2) (fun h3 : False => @lem4734723 m' n h1)). Qed.
Lemma lem4742889 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742888 m' n h1 h2) (@lem4734723 m' n h1)). Qed.
Lemma lem4742890 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4742889 m' n h1 h2) (fun h3 : False => @lem4734709 m' n h2)). Qed.
Lemma lem4742892 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742890 m' n h1 h2) (@lem4734709 m' n h2)). Qed.
Lemma lem4742893 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742892 m' n h1 h2) (fun h3 : False => @lem4734502 m' n h1)). Qed.
Lemma lem4742894 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742893 m' n h1 h2) (@lem4734502 m' n h1)). Qed.
Lemma lem4742895 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4742894 m' n h1 h2) (fun h3 : False => @lem4734488 m' n h2)). Qed.
Lemma lem4742897 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742895 m' n h1 h2) (@lem4734488 m' n h2)). Qed.
Lemma lem4742898 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h8 : Peano.lt m n => @lem4741525 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4734252 m n h3)). Qed.
Lemma lem4742900 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742898 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4734252 m n h3)). Qed.
Lemma lem4742901 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h8 : Peano.lt m n => @lem4742900 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4734046 m n h3)). Qed.
Lemma lem4742903 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742901 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4734046 m n h3)). Qed.
Lemma lem4742904 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h8 : m' = n => @lem4742903 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4733839 m' n h7)). Qed.
Lemma lem4742905 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742904 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4733839 m' n h7)). Qed.
Lemma lem4742906 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h8 : Peano.lt m n => @lem4742905 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4733812 m n h3)). Qed.
Lemma lem4742908 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742906 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4733812 m n h3)). Qed.
Lemma lem4742909 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m n => @lem4741316 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4733589 m n h3)). Qed.
Lemma lem4742911 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4742909 A s n a f m x h1 h2 h3 h4 h5) (@lem4733589 m n h3)). Qed.
Lemma lem4742912 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m n => @lem4742911 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4733382 m n h3)). Qed.
Lemma lem4742914 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4742912 A s n a f m x h1 h2 h3 h4 h5) (@lem4733382 m n h3)). Qed.
Lemma lem4742915 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h6 : (f m) = x => @lem4742914 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4733160 A f m x h5)). Qed.
Lemma lem4742916 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4742915 A s n a f m x h1 h2 h3 h4 h5) (@lem4733160 A f m x h5)). Qed.
Lemma lem4742917 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m n => @lem4742916 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4733146 m n h3)). Qed.
Lemma lem4742918 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4742917 A s n a f m x h1 h2 h3 h4 h5) (@lem4733146 m n h3)). Qed.
Lemma lem4742919 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4742918 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4733077 A a x h4)). Qed.
Lemma lem4742921 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4742919 A s n a f m x h1 h2 h3 h4 h5) (@lem4733077 A a x h4)). Qed.
Lemma lem4742922 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h7 : Peano.lt m n => @lem4741105 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4732909 m n h3)). Qed.
Lemma lem4742924 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742922 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4732909 m n h3)). Qed.
Lemma lem4742925 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h7 : Peano.lt m n => @lem4742924 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4732689 m n h3)). Qed.
Lemma lem4742927 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742925 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4732689 m n h3)). Qed.
Lemma lem4742928 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4740896 m' n h1 h2) (fun h3 : False => @lem4732480 m' n h1)). Qed.
Lemma lem4742929 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742928 m' n h1 h2) (@lem4732480 m' n h1)). Qed.
Lemma lem4742930 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4742929 m' n h1 h2) (fun h3 : False => @lem4732466 m' n h2)). Qed.
Lemma lem4742932 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742930 m' n h1 h2) (@lem4732466 m' n h2)). Qed.
Lemma lem4742933 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742932 m' n h1 h2) (fun h3 : False => @lem4732259 m' n h1)). Qed.
Lemma lem4742934 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742933 m' n h1 h2) (@lem4732259 m' n h1)). Qed.
Lemma lem4742935 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4742934 m' n h1 h2) (fun h3 : False => @lem4732245 m' n h2)). Qed.
Lemma lem4742937 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742935 m' n h1 h2) (@lem4732245 m' n h2)). Qed.
Lemma lem4742938 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4740751 m n h1 h2) (fun h3 : False => @lem4732022 m n h1)). Qed.
Lemma lem4742939 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742938 m n h1 h2) (@lem4732022 m n h1)). Qed.
Lemma lem4742940 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4742939 m n h1 h2) (fun h3 : False => @lem4732008 m n h2)). Qed.
Lemma lem4742942 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742940 m n h1 h2) (@lem4732008 m n h2)). Qed.
Lemma lem4742943 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4742942 m n h1 h2) (fun h3 : False => @lem4731815 m n h1)). Qed.
Lemma lem4742944 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742943 m n h1 h2) (@lem4731815 m n h1)). Qed.
Lemma lem4742945 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4742944 m n h1 h2) (fun h3 : False => @lem4731801 m n h2)). Qed.
Lemma lem4742947 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742945 m n h1 h2) (@lem4731801 m n h2)). Qed.
Lemma lem4742948 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4742947 m n h1 h2) (fun h3 : False => @lem4731580 m n h1)). Qed.
Lemma lem4742949 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742948 m n h1 h2) (@lem4731580 m n h1)). Qed.
Lemma lem4742950 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4742949 m n h1 h2) (fun h3 : False => @lem4731566 m n h2)). Qed.
Lemma lem4742952 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742950 m n h1 h2) (@lem4731566 m n h2)). Qed.
Lemma lem4742953 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4740606 m n h1 h2) (fun h3 : False => @lem4731343 m n h1)). Qed.
Lemma lem4742954 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742953 m n h1 h2) (@lem4731343 m n h1)). Qed.
Lemma lem4742955 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4742954 m n h1 h2) (fun h3 : False => @lem4731329 m n h2)). Qed.
Lemma lem4742957 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742955 m n h1 h2) (@lem4731329 m n h2)). Qed.
Lemma lem4742958 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4742957 m n h1 h2) (fun h3 : False => @lem4731123 m n h1)). Qed.
Lemma lem4742959 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742958 m n h1 h2) (@lem4731123 m n h1)). Qed.
Lemma lem4742960 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4742959 m n h1 h2) (fun h3 : False => @lem4731109 m n h2)). Qed.
Lemma lem4742962 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742960 m n h1 h2) (@lem4731109 m n h2)). Qed.
Lemma lem4742963 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4740461 m n h1 h2) (fun h3 : False => @lem4730886 m n h1)). Qed.
Lemma lem4742964 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742963 m n h1 h2) (@lem4730886 m n h1)). Qed.
Lemma lem4742965 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4742964 m n h1 h2) (fun h3 : False => @lem4730872 m n h2)). Qed.
Lemma lem4742967 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742965 m n h1 h2) (@lem4730872 m n h2)). Qed.
Lemma lem4742968 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4742967 m n h1 h2) (fun h3 : False => @lem4730665 m n h1)). Qed.
Lemma lem4742969 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742968 m n h1 h2) (@lem4730665 m n h1)). Qed.
Lemma lem4742970 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4742969 m n h1 h2) (fun h3 : False => @lem4730651 m n h2)). Qed.
Lemma lem4742972 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4742970 m n h1 h2) (@lem4730651 m n h2)). Qed.
Lemma lem4742973 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4740316 m' n h1 h2) (fun h3 : False => @lem4730442 m' n h1)). Qed.
Lemma lem4742974 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742973 m' n h1 h2) (@lem4730442 m' n h1)). Qed.
Lemma lem4742975 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4742974 m' n h1 h2) (fun h3 : False => @lem4730428 m' n h2)). Qed.
Lemma lem4742977 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742975 m' n h1 h2) (@lem4730428 m' n h2)). Qed.
Lemma lem4742978 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term803) (h2 : term883 A f x n) : False.
Proof. exact (EQ_MP (@lem4740170) (@lem4740167 A f x n h1 h2)). Qed.
Lemma lem4742979 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4742831 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4730016 m' n h3)). Qed.
Lemma lem4742980 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742979 A f x m m' n h1 h2 h3) (@lem4730016 m' n h3)). Qed.
Lemma lem4742981 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742980 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4730012 m n h2)). Qed.
Lemma lem4742982 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742981 A f x m m' n h1 h2 h3) (@lem4730012 m n h2)). Qed.
Lemma lem4742983 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4742839 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4729946 m' n h3)). Qed.
Lemma lem4742984 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742983 A f x m m' n h1 h2 h3) (@lem4729946 m' n h3)). Qed.
Lemma lem4742985 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742984 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4729942 m n h2)). Qed.
Lemma lem4742986 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742985 A f x m m' n h1 h2 h3) (@lem4729942 m n h2)). Qed.
Lemma lem4742987 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h6 : (f m') = x => @lem4742848 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4729878 A f m' x h5)). Qed.
Lemma lem4742988 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742987 A s n a f m' x h1 h2 h3 h4 h5) (@lem4729878 A f m' x h5)). Qed.
Lemma lem4742989 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4742988 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4729876 m' n h3)). Qed.
Lemma lem4742990 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742989 A s n a f m' x h1 h2 h3 h4 h5) (@lem4729876 m' n h3)). Qed.
Lemma lem4742991 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4742990 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4729846 A a x h4)). Qed.
Lemma lem4742992 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4742991 A s n a f m' x h1 h2 h3 h4 h5) (@lem4729846 A a x h4)). Qed.
Lemma lem4742993 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742863 m' n h1 h2) (fun h3 : False => @lem4729808 m' n h1)). Qed.
Lemma lem4742994 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742993 m' n h1 h2) (@lem4729808 m' n h1)). Qed.
Lemma lem4742995 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4742994 m' n h1 h2) (fun h3 : False => @lem4729806 m' n h2)). Qed.
Lemma lem4742996 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4742995 m' n h1 h2) (@lem4729806 m' n h2)). Qed.
Lemma lem4742997 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4742873 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4729736 m' n h3)). Qed.
Lemma lem4742998 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742997 A f x m m' n h1 h2 h3) (@lem4729736 m' n h3)). Qed.
Lemma lem4742999 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4742998 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4729732 m n h2)). Qed.
Lemma lem4743000 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4742999 A f x m m' n h1 h2 h3) (@lem4729732 m n h2)). Qed.
Lemma lem4743001 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4742878 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4729666 m' n h3)). Qed.
Lemma lem4743002 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743001 A f x m m' n h1 h2 h3) (@lem4729666 m' n h3)). Qed.
Lemma lem4743003 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4743002 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4729662 m n h2)). Qed.
Lemma lem4743004 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743003 A f x m m' n h1 h2 h3) (@lem4729662 m n h2)). Qed.
Lemma lem4743005 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h6 : (f m') = x => @lem4742887 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4729598 A f m' x h5)). Qed.
Lemma lem4743006 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743005 A s n a f m' x h1 h2 h3 h4 h5) (@lem4729598 A f m' x h5)). Qed.
Lemma lem4743007 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4743006 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4729596 m' n h3)). Qed.
Lemma lem4743008 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743007 A s n a f m' x h1 h2 h3 h4 h5) (@lem4729596 m' n h3)). Qed.
Lemma lem4743009 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743008 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4729566 A a x h4)). Qed.
Lemma lem4743010 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743009 A s n a f m' x h1 h2 h3 h4 h5) (@lem4729566 A a x h4)). Qed.
Lemma lem4743011 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742897 m' n h1 h2) (fun h3 : False => @lem4729528 m' n h1)). Qed.
Lemma lem4743012 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743011 m' n h1 h2) (@lem4729528 m' n h1)). Qed.
Lemma lem4743013 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743012 m' n h1 h2) (fun h3 : False => @lem4729526 m' n h2)). Qed.
Lemma lem4743014 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743013 m' n h1 h2) (@lem4729526 m' n h2)). Qed.
Lemma lem4743015 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h8 : (f m') = x => @lem4742908 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4729458 A f m' x h6)). Qed.
Lemma lem4743016 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743015 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4729458 A f m' x h6)). Qed.
Lemma lem4743017 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h8 : m' = n => @lem4743016 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4729456 m' n h7)). Qed.
Lemma lem4743018 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743017 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4729456 m' n h7)). Qed.
Lemma lem4743019 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h8 : (f m) = x => @lem4743018 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4729454 A f m x h5)). Qed.
Lemma lem4743020 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743019 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4729454 A f m x h5)). Qed.
Lemma lem4743021 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h8 : Peano.lt m n => @lem4743020 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4729452 m n h3)). Qed.
Lemma lem4743022 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743021 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4729452 m n h3)). Qed.
Lemma lem4743023 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (a = x) = False.
Proof. exact (prop_ext (fun h8 : a = x => @lem4743022 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4729426 A a x h4)). Qed.
Lemma lem4743024 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743023 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4729426 A a x h4)). Qed.
Lemma lem4743025 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h6 : (f m) = x => @lem4742921 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4729384 A f m x h5)). Qed.
Lemma lem4743026 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4743025 A s n a f m x h1 h2 h3 h4 h5) (@lem4729384 A f m x h5)). Qed.
Lemma lem4743027 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m n => @lem4743026 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4729382 m n h3)). Qed.
Lemma lem4743028 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4743027 A s n a f m x h1 h2 h3 h4 h5) (@lem4729382 m n h3)). Qed.
Lemma lem4743029 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743028 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4729356 A a x h4)). Qed.
Lemma lem4743030 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4743029 A s n a f m x h1 h2 h3 h4 h5) (@lem4729356 A a x h4)). Qed.
Lemma lem4743031 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h7 : (f m') = x => @lem4742927 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4729318 A f m' x h6)). Qed.
Lemma lem4743032 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743031 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4729318 A f m' x h6)). Qed.
Lemma lem4743033 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h7 : (f m) = x => @lem4743032 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4729314 A f m x h5)). Qed.
Lemma lem4743034 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743033 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4729314 A f m x h5)). Qed.
Lemma lem4743035 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h7 : Peano.lt m n => @lem4743034 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4729312 m n h3)). Qed.
Lemma lem4743036 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743035 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4729312 m n h3)). Qed.
Lemma lem4743037 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : (a = x) = False.
Proof. exact (prop_ext (fun h7 : a = x => @lem4743036 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4729286 A a x h4)). Qed.
Lemma lem4743038 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743037 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4729286 A a x h4)). Qed.
Lemma lem4743039 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742937 m' n h1 h2) (fun h3 : False => @lem4729248 m' n h1)). Qed.
Lemma lem4743040 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743039 m' n h1 h2) (@lem4729248 m' n h1)). Qed.
Lemma lem4743041 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743040 m' n h1 h2) (fun h3 : False => @lem4729246 m' n h2)). Qed.
Lemma lem4743042 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743041 m' n h1 h2) (@lem4729246 m' n h2)). Qed.
Lemma lem4743043 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4742952 m n h1 h2) (fun h3 : False => @lem4729174 m n h1)). Qed.
Lemma lem4743044 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743043 m n h1 h2) (@lem4729174 m n h1)). Qed.
Lemma lem4743045 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4743044 m n h1 h2) (fun h3 : False => @lem4729172 m n h2)). Qed.
Lemma lem4743046 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743045 m n h1 h2) (@lem4729172 m n h2)). Qed.
Lemma lem4743047 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4742962 m n h1 h2) (fun h3 : False => @lem4729104 m n h1)). Qed.
Lemma lem4743048 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743047 m n h1 h2) (@lem4729104 m n h1)). Qed.
Lemma lem4743049 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4743048 m n h1 h2) (fun h3 : False => @lem4729102 m n h2)). Qed.
Lemma lem4743050 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743049 m n h1 h2) (@lem4729102 m n h2)). Qed.
Lemma lem4743051 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4742972 m n h1 h2) (fun h3 : False => @lem4729034 m n h1)). Qed.
Lemma lem4743052 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743051 m n h1 h2) (@lem4729034 m n h1)). Qed.
Lemma lem4743053 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4743052 m n h1 h2) (fun h3 : False => @lem4729032 m n h2)). Qed.
Lemma lem4743054 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743053 m n h1 h2) (@lem4729032 m n h2)). Qed.
Lemma lem4743055 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742977 m' n h1 h2) (fun h3 : False => @lem4728968 m' n h1)). Qed.
Lemma lem4743056 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743055 m' n h1 h2) (@lem4728968 m' n h1)). Qed.
Lemma lem4743057 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743056 m' n h1 h2) (fun h3 : False => @lem4728966 m' n h2)). Qed.
Lemma lem4743058 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743057 m' n h1 h2) (@lem4728966 m' n h2)). Qed.
Lemma lem4743059 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4742982 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4728043 m' n h3)). Qed.
Lemma lem4743060 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743059 A f x m m' n h1 h2 h3) (@lem4728043 m' n h3)). Qed.
Lemma lem4743061 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4743060 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4728035 m n h2)). Qed.
Lemma lem4743062 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743061 A f x m m' n h1 h2 h3) (@lem4728035 m n h2)). Qed.
Lemma lem4743063 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4742986 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727879 m' n h3)). Qed.
Lemma lem4743064 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743063 A f x m m' n h1 h2 h3) (@lem4727879 m' n h3)). Qed.
Lemma lem4743065 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4743064 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727871 m n h2)). Qed.
Lemma lem4743066 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743065 A f x m m' n h1 h2 h3) (@lem4727871 m n h2)). Qed.
Lemma lem4743067 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h6 : (f m') = x => @lem4742992 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727719 A f m' x h5)). Qed.
Lemma lem4743068 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743067 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727719 A f m' x h5)). Qed.
Lemma lem4743069 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4743068 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727715 m' n h3)). Qed.
Lemma lem4743070 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743069 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727715 m' n h3)). Qed.
Lemma lem4743071 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743070 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727584 A a x h4)). Qed.
Lemma lem4743072 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743071 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727584 A a x h4)). Qed.
Lemma lem4743073 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4742996 m' n h1 h2) (fun h3 : False => @lem4727555 m' n h1)). Qed.
Lemma lem4743074 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743073 m' n h1 h2) (@lem4727555 m' n h1)). Qed.
Lemma lem4743075 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743074 m' n h1 h2) (fun h3 : False => @lem4727551 m' n h2)). Qed.
Lemma lem4743076 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743075 m' n h1 h2) (@lem4727551 m' n h2)). Qed.
Lemma lem4743077 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4743000 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727387 m' n h3)). Qed.
Lemma lem4743078 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743077 A f x m m' n h1 h2 h3) (@lem4727387 m' n h3)). Qed.
Lemma lem4743079 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4743078 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727379 m n h2)). Qed.
Lemma lem4743080 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743079 A f x m m' n h1 h2 h3) (@lem4727379 m n h2)). Qed.
Lemma lem4743081 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4743004 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727223 m' n h3)). Qed.
Lemma lem4743082 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743081 A f x m m' n h1 h2 h3) (@lem4727223 m' n h3)). Qed.
Lemma lem4743083 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4743082 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727215 m n h2)). Qed.
Lemma lem4743084 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743083 A f x m m' n h1 h2 h3) (@lem4727215 m n h2)). Qed.
Lemma lem4743085 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h6 : (f m') = x => @lem4743010 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727063 A f m' x h5)). Qed.
Lemma lem4743086 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743085 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727063 A f m' x h5)). Qed.
Lemma lem4743087 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4743086 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727059 m' n h3)). Qed.
Lemma lem4743088 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743087 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727059 m' n h3)). Qed.
Lemma lem4743089 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743088 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4726928 A a x h4)). Qed.
Lemma lem4743090 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743089 A s n a f m' x h1 h2 h3 h4 h5) (@lem4726928 A a x h4)). Qed.
Lemma lem4743091 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4743014 m' n h1 h2) (fun h3 : False => @lem4726899 m' n h1)). Qed.
Lemma lem4743092 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743091 m' n h1 h2) (@lem4726899 m' n h1)). Qed.
Lemma lem4743093 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743092 m' n h1 h2) (fun h3 : False => @lem4726895 m' n h2)). Qed.
Lemma lem4743094 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743093 m' n h1 h2) (@lem4726895 m' n h2)). Qed.
Lemma lem4743095 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h8 : (f m') = x => @lem4743024 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726735 A f m' x h6)). Qed.
Lemma lem4743096 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743095 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726735 A f m' x h6)). Qed.
Lemma lem4743097 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h8 : m' = n => @lem4743096 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726731 m' n h7)). Qed.
Lemma lem4743098 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743097 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726731 m' n h7)). Qed.
Lemma lem4743099 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h8 : (f m) = x => @lem4743098 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726727 A f m x h5)). Qed.
Lemma lem4743100 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743099 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726727 A f m x h5)). Qed.
Lemma lem4743101 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h8 : Peano.lt m n => @lem4743100 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726723 m n h3)). Qed.
Lemma lem4743102 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743101 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726723 m n h3)). Qed.
Lemma lem4743103 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (a = x) = False.
Proof. exact (prop_ext (fun h8 : a = x => @lem4743102 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726600 A a x h4)). Qed.
Lemma lem4743104 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743103 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726600 A a x h4)). Qed.
Lemma lem4743105 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h6 : (f m) = x => @lem4743030 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4726563 A f m x h5)). Qed.
Lemma lem4743106 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4743105 A s n a f m x h1 h2 h3 h4 h5) (@lem4726563 A f m x h5)). Qed.
Lemma lem4743107 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m n => @lem4743106 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4726559 m n h3)). Qed.
Lemma lem4743108 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4743107 A s n a f m x h1 h2 h3 h4 h5) (@lem4726559 m n h3)). Qed.
Lemma lem4743109 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743108 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4726436 A a x h4)). Qed.
Lemma lem4743110 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4743109 A s n a f m x h1 h2 h3 h4 h5) (@lem4726436 A a x h4)). Qed.
Lemma lem4743111 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h7 : (f m') = x => @lem4743038 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4726407 A f m' x h6)). Qed.
Lemma lem4743112 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743111 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4726407 A f m' x h6)). Qed.
Lemma lem4743113 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h7 : (f m) = x => @lem4743112 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4726399 A f m x h5)). Qed.
Lemma lem4743114 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743113 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4726399 A f m x h5)). Qed.
Lemma lem4743115 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h7 : Peano.lt m n => @lem4743114 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4726395 m n h3)). Qed.
Lemma lem4743116 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743115 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4726395 m n h3)). Qed.
Lemma lem4743117 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : (a = x) = False.
Proof. exact (prop_ext (fun h7 : a = x => @lem4743116 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4726272 A a x h4)). Qed.
Lemma lem4743118 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743117 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4726272 A a x h4)). Qed.
Lemma lem4743119 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4743042 m' n h1 h2) (fun h3 : False => @lem4726243 m' n h1)). Qed.
Lemma lem4743120 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743119 m' n h1 h2) (@lem4726243 m' n h1)). Qed.
Lemma lem4743121 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743120 m' n h1 h2) (fun h3 : False => @lem4726239 m' n h2)). Qed.
Lemma lem4743122 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743121 m' n h1 h2) (@lem4726239 m' n h2)). Qed.
Lemma lem4743123 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4743046 m n h1 h2) (fun h3 : False => @lem4726071 m n h1)). Qed.
Lemma lem4743124 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743123 m n h1 h2) (@lem4726071 m n h1)). Qed.
Lemma lem4743125 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4743124 m n h1 h2) (fun h3 : False => @lem4726067 m n h2)). Qed.
Lemma lem4743126 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743125 m n h1 h2) (@lem4726067 m n h2)). Qed.
Lemma lem4743127 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4743050 m n h1 h2) (fun h3 : False => @lem4725907 m n h1)). Qed.
Lemma lem4743128 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743127 m n h1 h2) (@lem4725907 m n h1)). Qed.
Lemma lem4743129 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4743128 m n h1 h2) (fun h3 : False => @lem4725903 m n h2)). Qed.
Lemma lem4743130 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743129 m n h1 h2) (@lem4725903 m n h2)). Qed.
Lemma lem4743131 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4743054 m n h1 h2) (fun h3 : False => @lem4725743 m n h1)). Qed.
Lemma lem4743132 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743131 m n h1 h2) (@lem4725743 m n h1)). Qed.
Lemma lem4743133 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4743132 m n h1 h2) (fun h3 : False => @lem4725739 m n h2)). Qed.
Lemma lem4743134 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743133 m n h1 h2) (@lem4725739 m n h2)). Qed.
Lemma lem4743135 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4743058 m' n h1 h2) (fun h3 : False => @lem4725587 m' n h1)). Qed.
Lemma lem4743136 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743135 m' n h1 h2) (@lem4725587 m' n h1)). Qed.
Lemma lem4743137 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743136 m' n h1 h2) (fun h3 : False => @lem4725583 m' n h2)). Qed.
Lemma lem4743138 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743137 m' n h1 h2) (@lem4725583 m' n h2)). Qed.
Lemma lem4743139 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4743062 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4728043 m' n h3)). Qed.
Lemma lem4743140 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743139 A f x m m' n h1 h2 h3) (@lem4728043 m' n h3)). Qed.
Lemma lem4743141 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4743140 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4728035 m n h2)). Qed.
Lemma lem4743142 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743141 A f x m m' n h1 h2 h3) (@lem4728035 m n h2)). Qed.
Lemma lem4743143 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4743066 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727879 m' n h3)). Qed.
Lemma lem4743144 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743143 A f x m m' n h1 h2 h3) (@lem4727879 m' n h3)). Qed.
Lemma lem4743145 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4743144 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727871 m n h2)). Qed.
Lemma lem4743146 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743145 A f x m m' n h1 h2 h3) (@lem4727871 m n h2)). Qed.
Lemma lem4743147 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h6 : (f m') = x => @lem4743072 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727719 A f m' x h5)). Qed.
Lemma lem4743148 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743147 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727719 A f m' x h5)). Qed.
Lemma lem4743149 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4743148 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727715 m' n h3)). Qed.
Lemma lem4743150 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743149 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727715 m' n h3)). Qed.
Lemma lem4743151 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743150 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727584 A a x h4)). Qed.
Lemma lem4743152 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743151 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727584 A a x h4)). Qed.
Lemma lem4743153 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4743076 m' n h1 h2) (fun h3 : False => @lem4727555 m' n h1)). Qed.
Lemma lem4743154 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743153 m' n h1 h2) (@lem4727555 m' n h1)). Qed.
Lemma lem4743155 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743154 m' n h1 h2) (fun h3 : False => @lem4727551 m' n h2)). Qed.
Lemma lem4743156 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743155 m' n h1 h2) (@lem4727551 m' n h2)). Qed.
Lemma lem4743157 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4743080 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727387 m' n h3)). Qed.
Lemma lem4743158 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743157 A f x m m' n h1 h2 h3) (@lem4727387 m' n h3)). Qed.
Lemma lem4743159 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4743158 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727379 m n h2)). Qed.
Lemma lem4743160 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743159 A f x m m' n h1 h2 h3) (@lem4727379 m n h2)). Qed.
Lemma lem4743161 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h4 : m' = n => @lem4743084 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727223 m' n h3)). Qed.
Lemma lem4743162 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743161 A f x m m' n h1 h2 h3) (@lem4727223 m' n h3)). Qed.
Lemma lem4743163 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : (m = n) = False.
Proof. exact (prop_ext (fun h4 : m = n => @lem4743162 A f x m m' n h1 h2 h3) (fun h4 : False => @lem4727215 m n h2)). Qed.
Lemma lem4743164 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743163 A f x m m' n h1 h2 h3) (@lem4727215 m n h2)). Qed.
Lemma lem4743165 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h6 : (f m') = x => @lem4743090 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727063 A f m' x h5)). Qed.
Lemma lem4743166 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743165 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727063 A f m' x h5)). Qed.
Lemma lem4743167 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m' n => @lem4743166 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4727059 m' n h3)). Qed.
Lemma lem4743168 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743167 A s n a f m' x h1 h2 h3 h4 h5) (@lem4727059 m' n h3)). Qed.
Lemma lem4743169 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743168 A s n a f m' x h1 h2 h3 h4 h5) (fun h6 : False => @lem4726928 A a x h4)). Qed.
Lemma lem4743170 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m' n) (h4 : a = x) (h5 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743169 A s n a f m' x h1 h2 h3 h4 h5) (@lem4726928 A a x h4)). Qed.
Lemma lem4743171 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4743094 m' n h1 h2) (fun h3 : False => @lem4726899 m' n h1)). Qed.
Lemma lem4743172 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743171 m' n h1 h2) (@lem4726899 m' n h1)). Qed.
Lemma lem4743173 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743172 m' n h1 h2) (fun h3 : False => @lem4726895 m' n h2)). Qed.
Lemma lem4743174 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743173 m' n h1 h2) (@lem4726895 m' n h2)). Qed.
Lemma lem4743175 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h8 : (f m') = x => @lem4743104 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726735 A f m' x h6)). Qed.
Lemma lem4743176 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743175 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726735 A f m' x h6)). Qed.
Lemma lem4743177 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (m' = n) = False.
Proof. exact (prop_ext (fun h8 : m' = n => @lem4743176 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726731 m' n h7)). Qed.
Lemma lem4743178 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743177 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726731 m' n h7)). Qed.
Lemma lem4743179 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h8 : (f m) = x => @lem4743178 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726727 A f m x h5)). Qed.
Lemma lem4743180 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743179 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726727 A f m x h5)). Qed.
Lemma lem4743181 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h8 : Peano.lt m n => @lem4743180 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726723 m n h3)). Qed.
Lemma lem4743182 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743181 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726723 m n h3)). Qed.
Lemma lem4743183 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : (a = x) = False.
Proof. exact (prop_ext (fun h8 : a = x => @lem4743182 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4726600 A a x h4)). Qed.
Lemma lem4743184 {A : Type'} (s : A -> Prop) (a : A) (m : nat) (f : nat -> A) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) (h7 : m' = n) : False.
Proof. exact (EQ_MP (@lem4743183 A s a m f x m' n h1 h2 h3 h4 h5 h6 h7) (@lem4726600 A a x h4)). Qed.
Lemma lem4743185 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h6 : (f m) = x => @lem4743110 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4726563 A f m x h5)). Qed.
Lemma lem4743186 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4743185 A s n a f m x h1 h2 h3 h4 h5) (@lem4726563 A f m x h5)). Qed.
Lemma lem4743187 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h6 : Peano.lt m n => @lem4743186 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4726559 m n h3)). Qed.
Lemma lem4743188 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4743187 A s n a f m x h1 h2 h3 h4 h5) (@lem4726559 m n h3)). Qed.
Lemma lem4743189 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743188 A s n a f m x h1 h2 h3 h4 h5) (fun h6 : False => @lem4726436 A a x h4)). Qed.
Lemma lem4743190 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) : False.
Proof. exact (EQ_MP (@lem4743189 A s n a f m x h1 h2 h3 h4 h5) (@lem4726436 A a x h4)). Qed.
Lemma lem4743191 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h7 : (f m') = x => @lem4743118 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4726407 A f m' x h6)). Qed.
Lemma lem4743192 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743191 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4726407 A f m' x h6)). Qed.
Lemma lem4743193 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : ((f m) = x) = False.
Proof. exact (prop_ext (fun h7 : (f m) = x => @lem4743192 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4726399 A f m x h5)). Qed.
Lemma lem4743194 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743193 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4726399 A f m x h5)). Qed.
Lemma lem4743195 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h7 : Peano.lt m n => @lem4743194 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4726395 m n h3)). Qed.
Lemma lem4743196 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743195 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4726395 m n h3)). Qed.
Lemma lem4743197 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : (a = x) = False.
Proof. exact (prop_ext (fun h7 : a = x => @lem4743196 A s n a m f m' x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4726272 A a x h4)). Qed.
Lemma lem4743198 {A : Type'} (s : A -> Prop) (n : nat) (a : A) (m : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : Peano.lt m n) (h4 : a = x) (h5 : (f m) = x) (h6 : (f m') = x) : False.
Proof. exact (EQ_MP (@lem4743197 A s n a m f m' x h1 h2 h3 h4 h5 h6) (@lem4726272 A a x h4)). Qed.
Lemma lem4743199 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4743122 m' n h1 h2) (fun h3 : False => @lem4726243 m' n h1)). Qed.
Lemma lem4743200 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743199 m' n h1 h2) (@lem4726243 m' n h1)). Qed.
Lemma lem4743201 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743200 m' n h1 h2) (fun h3 : False => @lem4726239 m' n h2)). Qed.
Lemma lem4743202 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743201 m' n h1 h2) (@lem4726239 m' n h2)). Qed.
Lemma lem4743203 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4743126 m n h1 h2) (fun h3 : False => @lem4726071 m n h1)). Qed.
Lemma lem4743204 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743203 m n h1 h2) (@lem4726071 m n h1)). Qed.
Lemma lem4743205 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4743204 m n h1 h2) (fun h3 : False => @lem4726067 m n h2)). Qed.
Lemma lem4743206 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743205 m n h1 h2) (@lem4726067 m n h2)). Qed.
Lemma lem4743207 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4743130 m n h1 h2) (fun h3 : False => @lem4725907 m n h1)). Qed.
Lemma lem4743208 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743207 m n h1 h2) (@lem4725907 m n h1)). Qed.
Lemma lem4743209 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4743208 m n h1 h2) (fun h3 : False => @lem4725903 m n h2)). Qed.
Lemma lem4743210 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743209 m n h1 h2) (@lem4725903 m n h2)). Qed.
Lemma lem4743211 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (term312 m n) = False.
Proof. exact (prop_ext (fun h3 : term312 m n => @lem4743134 m n h1 h2) (fun h3 : False => @lem4725743 m n h1)). Qed.
Lemma lem4743212 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743211 m n h1 h2) (@lem4725743 m n h1)). Qed.
Lemma lem4743213 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem4743212 m n h1 h2) (fun h3 : False => @lem4725739 m n h2)). Qed.
Lemma lem4743214 (m : nat) (n : nat) (h1 : term312 m n) (h2 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem4743213 m n h1 h2) (@lem4725739 m n h2)). Qed.
Lemma lem4743215 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4743138 m' n h1 h2) (fun h3 : False => @lem4725587 m' n h1)). Qed.
Lemma lem4743216 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743215 m' n h1 h2) (@lem4725587 m' n h1)). Qed.
Lemma lem4743217 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : (Peano.lt m' n) = False.
Proof. exact (prop_ext (fun h3 : Peano.lt m' n => @lem4743216 m' n h1 h2) (fun h3 : False => @lem4725583 m' n h2)). Qed.
Lemma lem4743218 (m' : nat) (n : nat) (h1 : term312 m' n) (h2 : Peano.lt m' n) : False.
Proof. exact (EQ_MP (@lem4743217 m' n h1 h2) (@lem4725583 m' n h2)). Qed.
Lemma lem4743219 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term803) (h2 : term883 A f x n) : term803 = False.
Proof. exact (prop_ext (fun h3 : term803 => @lem4742978 A f x n h1 h2) (fun h3 : False => @lem4725276 h1)). Qed.
Lemma lem4743220 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term803) (h2 : term883 A f x n) : False.
Proof. exact (EQ_MP (@lem4743219 A f x n h1 h2) (@lem4725276 h1)). Qed.
Lemma lem4743221 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (or_elim (@lem4725208 A f x n m' m h1) (fun h0 : term312 m' n => @lem4743146 A f x m m' n h1 h2 h3) (fun h0 : (f m') = x => @lem4743142 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4743222 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (m' : nat) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : Peano.lt m' n) (h5 : a = x) : False.
Proof. exact (or_elim (@lem4725208 A f x n m' m h3) (fun h0 : term312 m' n => @lem4743156 m' n h0 h4) (fun h0 : (f m') = x => @lem4743152 A s n a f m' x h1 h2 h4 h5 h0)). Qed.
Lemma lem4743223 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (a : A) (x : A) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : a = x) (h5 : m = n) : False.
Proof. exact (or_elim (@lem4725207 A f x n m' m h3) (fun h0 : Peano.lt m' n => @lem4743222 A s f m m' n a x h1 h2 h3 h0 h4) (fun h0 : m' = n => @lem4743221 A f x m m' n h3 h5 h0)). Qed.
Lemma lem4743224 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term870 A f x n m' m) (h2 : m = n) (h3 : m' = n) : False.
Proof. exact (or_elim (@lem4725208 A f x n m' m h1) (fun h0 : term312 m' n => @lem4743164 A f x m m' n h1 h2 h3) (fun h0 : (f m') = x => @lem4743160 A f x m m' n h1 h2 h3)). Qed.
Lemma lem4743225 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : nat) (m' : nat) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : Peano.lt m' n) (h5 : a = x) : False.
Proof. exact (or_elim (@lem4725208 A f x n m' m h3) (fun h0 : term312 m' n => @lem4743174 m' n h0 h4) (fun h0 : (f m') = x => @lem4743170 A s n a f m' x h1 h2 h4 h5 h0)). Qed.
Lemma lem4743226 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (a : A) (x : A) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : a = x) (h5 : m = n) : False.
Proof. exact (or_elim (@lem4725207 A f x n m' m h3) (fun h0 : Peano.lt m' n => @lem4743225 A s f m m' n a x h1 h2 h3 h0 h4) (fun h0 : m' = n => @lem4743224 A f x m m' n h3 h5 h0)). Qed.
Lemma lem4743227 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (a : A) (x : A) (m : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : a = x) (h5 : m = n) : False.
Proof. exact (or_elim (@lem4725210 A f x n m' m h3) (fun h0 : term312 m n => @lem4743226 A s f m' a x m n h1 h2 h3 h4 h5) (fun h0 : (f m) = x => @lem4743223 A s f m' a x m n h1 h2 h3 h4 h5)). Qed.
Lemma lem4743228 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (m : nat) (x : A) (m' : nat) (n : nat) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : Peano.lt m n) (h5 : a = x) (h6 : (f m) = x) (h7 : m' = n) : False.
Proof. exact (or_elim (@lem4725208 A f x n m' m h3) (fun h0 : term312 m' n => @lem4743190 A s n a f m x h1 h2 h4 h5 h6) (fun h0 : (f m') = x => @lem4743184 A s a m f x m' n h1 h2 h4 h5 h6 h0 h7)). Qed.
Lemma lem4743229 {A : Type'} (s : A -> Prop) (m' : nat) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : Peano.lt m n) (h5 : Peano.lt m' n) (h6 : a = x) (h7 : (f m) = x) : False.
Proof. exact (or_elim (@lem4725208 A f x n m' m h3) (fun h0 : term312 m' n => @lem4743202 m' n h0 h5) (fun h0 : (f m') = x => @lem4743198 A s n a m f m' x h1 h2 h4 h6 h7 h0)). Qed.
Lemma lem4743230 {A : Type'} (s : A -> Prop) (m' : nat) (n : nat) (a : A) (f : nat -> A) (m : nat) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : Peano.lt m n) (h5 : a = x) (h6 : (f m) = x) : False.
Proof. exact (or_elim (@lem4725207 A f x n m' m h3) (fun h0 : Peano.lt m' n => @lem4743229 A s m' n a f m x h1 h2 h3 h4 h0 h5 h6) (fun h0 : m' = n => @lem4743228 A s a f m x m' n h1 h2 h3 h4 h5 h6 h0)). Qed.
Lemma lem4743231 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (m : nat) (n : nat) (h1 : term312 m n) (h2 : term870 A f x n m' m) (h3 : Peano.lt m n) : False.
Proof. exact (or_elim (@lem4725208 A f x n m' m h2) (fun h0 : term312 m' n => @lem4743210 m n h1 h3) (fun h0 : (f m') = x => @lem4743206 m n h1 h3)). Qed.
Lemma lem4743232 {A : Type'} (f : nat -> A) (x : A) (m : nat) (m' : nat) (n : nat) (h1 : term312 m n) (h2 : term870 A f x n m' m) (h3 : Peano.lt m n) (h4 : Peano.lt m' n) : False.
Proof. exact (or_elim (@lem4725208 A f x n m' m h2) (fun h0 : term312 m' n => @lem4743218 m' n h0 h4) (fun h0 : (f m') = x => @lem4743214 m n h1 h3)). Qed.
Lemma lem4743233 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (m : nat) (n : nat) (h1 : term312 m n) (h2 : term870 A f x n m' m) (h3 : Peano.lt m n) : False.
Proof. exact (or_elim (@lem4725207 A f x n m' m h2) (fun h0 : Peano.lt m' n => @lem4743232 A f x m m' n h1 h2 h3 h0) (fun h0 : m' = n => @lem4743231 A f x m' m n h1 h2 h3)). Qed.
Lemma lem4743234 {A : Type'} (s : A -> Prop) (f : nat -> A) (m' : nat) (m : nat) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : Peano.lt m n) (h5 : a = x) : False.
Proof. exact (or_elim (@lem4725210 A f x n m' m h3) (fun h0 : term312 m n => @lem4743233 A f x m' m n h0 h3 h4) (fun h0 : (f m) = x => @lem4743230 A s m' n a f m x h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem4743235 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (m' : nat) (m : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term870 A f x n m' m) (h4 : a = x) : False.
Proof. exact (or_elim (@lem4725209 A f x n m' m h3) (fun h0 : Peano.lt m n => @lem4743234 A s f m' m n a x h1 h2 h3 h0 h4) (fun h0 : m = n => @lem4743227 A s f m' a x m n h1 h2 h3 h4 h0)). Qed.
Lemma lem4743236 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : a = x) (h5 : term928 A f x n m' m) : False.
Proof. exact (or_elim (@lem4725196 A f x n m' m h5) (fun h0 : term883 A f x n => @lem4743220 A f x n h2 h0) (fun h0 : term870 A f x n m' m => @lem4743235 A s f n m' m a x h1 h3 h0 h4)). Qed.
Lemma lem4743237 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : a = x) (h5 : term928 A f x n m' m) : (term928 A f x n m' m) = False.
Proof. exact (prop_ext (fun h6 : term928 A f x n m' m => @lem4743236 A s a f x n m' m h1 h2 h3 h4 h5) (fun h6 : False => @lem4725196 A f x n m' m h5)). Qed.
Lemma lem4743238 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : a = x) (h5 : term928 A f x n m' m) : False.
Proof. exact (EQ_MP (@lem4743237 A s a f x n m' m h1 h2 h3 h4 h5) (@lem4725196 A f x n m' m h5)). Qed.
Lemma lem4743239 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : a = x) (h5 : term928 A f x n m' m) : term803 = False.
Proof. exact (prop_ext (fun h6 : term803 => @lem4743238 A s a f x n m' m h1 h2 h3 h4 h5) (fun h6 : False => @lem4725073 h2)). Qed.
Lemma lem4743240 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : a = x) (h5 : term928 A f x n m' m) : False.
Proof. exact (EQ_MP (@lem4743239 A s a f x n m' m h1 h2 h3 h4 h5) (@lem4725073 h2)). Qed.
Lemma lem4743241 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : a = x) (h5 : term928 A f x n m' m) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743240 A s a f x n m' m h1 h2 h3 h4 h5) (fun h6 : False => @lem4724906 A a x h4)). Qed.
Lemma lem4743242 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : a = x) (h5 : term928 A f x n m' m) : False.
Proof. exact (EQ_MP (@lem4743241 A s a f x n m' m h1 h2 h3 h4 h5) (@lem4724906 A a x h4)). Qed.
Lemma lem4743243 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (m : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : term931 A f x n m) (h5 : a = x) : False.
Proof. exact (ex_elim (@lem4724852 A f x n m h4) (fun m' : nat => fun h0 : term930 A f x n m m' => @lem4743242 A s a f x n m' m h1 h2 h3 h5 h0)). Qed.
Lemma lem4743244 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : term796 A f x n) (h5 : a = x) : False.
Proof. exact (ex_elim (@lem4723940 A f x n h4) (fun m : nat => fun h0 : term932 A f x n m => @lem4743243 A s f n m a x h1 h2 h3 h0 h5)). Qed.
Lemma lem4743245 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : term796 A f x n) (h5 : a = x) : term803 = False.
Proof. exact (prop_ext (fun h6 : term803 => @lem4743244 A s f n a x h1 h2 h3 h4 h5) (fun h6 : False => @lem4724851 h2)). Qed.
Lemma lem4743246 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : term796 A f x n) (h5 : a = x) : False.
Proof. exact (EQ_MP (@lem4743245 A s f n a x h1 h2 h3 h4 h5) (@lem4724851 h2)). Qed.
Lemma lem4743247 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : term796 A f x n) (h5 : a = x) : (a = x) = False.
Proof. exact (prop_ext (fun h6 : a = x => @lem4743246 A s f n a x h1 h2 h3 h4 h5) (fun h6 : False => @lem4723625 A a x h5)). Qed.
Lemma lem4743248 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term803) (h3 : term268 A n f s a) (h4 : term796 A f x n) (h5 : a = x) : False.
Proof. exact (EQ_MP (@lem4743247 A s f n a x h1 h2 h3 h4 h5) (@lem4723625 A a x h5)). Qed.
Lemma lem4743249 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term796 A f x n) (h4 : a = x) : term801.
Proof. exact (fun h0 : term803 => @lem4743248 A s f n a x h1 h0 h2 h3 h4). Qed.
Lemma lem4743250 : term801 = term802.
Proof. exact (@lem69 term803). Qed.
Lemma lem4743251 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term796 A f x n) (h4 : a = x) : term802.
Proof. exact (EQ_MP (@lem4743250) (@lem4743249 A s f n a x h1 h2 h3 h4)). Qed.
Lemma lem4743252 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term323 A) (h2 : term268 A n f s a) (h3 : term796 A f x n) (h4 : a = x) : term806.
Proof. exact (fun h0 : term324 => @lem4743251 A s f n a x h1 h2 h3 h4). Qed.
Lemma lem4743253 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (a : A) (x : A) (h1 : term268 A n f s a) (h2 : term796 A f x n) (h3 : a = x) : term808 A.
Proof. exact (fun h0 : term323 A => @lem4743252 A s f n a x h0 h1 h2 h3). Qed.
Lemma lem4743254 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (x : A) (h1 : term268 A n f s a) (h2 : a = x) : term811 A f x n.
Proof. exact (fun h0 : term796 A f x n => @lem4743253 A s f n a x h1 h0 h2). Qed.
Lemma lem4743255 {A : Type'} (x : A) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term814 A a f x n.
Proof. exact (fun h0 : a = x => @lem4743254 A n f s a x h1 h0). Qed.
Lemma lem4743256 {A : Type'} (x : A) (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) (h1 : term268 A n f s a) : term816 A s a f x n.
Proof. exact (fun h0 : @IN A x s => @lem4743255 A x n f s a h1). Qed.
Lemma lem4743257 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term818 A s a f x n.
Proof. exact (fun h0 : term268 A n f s a => @lem4743256 A x n f s a h0). Qed.
Lemma lem4743258 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term820 A s a f x n.
Proof. exact (fun h0 : term252 A s a n => @lem4743257 A s a f x n). Qed.
Lemma lem4743259 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term821 A s a f x n.
Proof. exact (fun h0 : @IN A a s => @lem4743258 A s a f x n). Qed.
Lemma lem4743264 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : term825 A a f x n.
Proof. exact (fun s : A -> Prop => @lem4743259 A s a f x n). Qed.
Lemma lem4743269 {A : Type'} (f : nat -> A) (x : A) (n : nat) : term829 A f x n.
Proof. exact (fun a : A => @lem4743264 A a f x n). Qed.
Lemma lem4743274 {A : Type'} (x : A) (n : nat) : term833 A x n.
Proof. exact (fun f : nat -> A => @lem4743269 A f x n). Qed.
Lemma lem4743279 {A : Type'} (n : nat) : term837 A n.
Proof. exact (fun x : A => @lem4743274 A x n). Qed.
Lemma lem4743284 {A : Type'} : term841 A.
Proof. exact (fun n : nat => @lem4743279 A n). Qed.
Lemma lem4743285 {A : Type'} : term840 A.
Proof. exact (EQ_MP (@lem4723529 A) (@lem4743284 A)). Qed.
Lemma lem4743286 {A : Type'} (n : nat) : term1023 A n.
Proof. exact (@lem4743285 A n). Qed.
Lemma lem4743287 {A : Type'} (n : nat) : (term1023 A n) = (term836 A n).
Proof. exact (eq_refl (term1023 A n)). Qed.
Lemma lem4743288 {A : Type'} (n : nat) : term836 A n.
Proof. exact (EQ_MP (@lem4743287 A n) (@lem4743286 A n)). Qed.
Lemma lem4743289 {A : Type'} (n : nat) (x : A) : term1024 A n x.
Proof. exact (@lem4743288 A n x). Qed.
Lemma lem4743290 {A : Type'} (x : A) (n : nat) : (term1024 A n x) = (term832 A x n).
Proof. exact (eq_refl (term1024 A n x)). Qed.
Lemma lem4743291 {A : Type'} (x : A) (n : nat) : term832 A x n.
Proof. exact (EQ_MP (@lem4743290 A x n) (@lem4743289 A n x)). Qed.
Lemma lem4743292 {A : Type'} (x : A) (n : nat) (f : nat -> A) : term1025 A x n f.
Proof. exact (@lem4743291 A x n f). Qed.
Lemma lem4743293 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1025 A x n f) = (term828 A f x n).
Proof. exact (eq_refl (term1025 A x n f)). Qed.
Lemma lem4743294 {A : Type'} (f : nat -> A) (x : A) (n : nat) : term828 A f x n.
Proof. exact (EQ_MP (@lem4743293 A f x n) (@lem4743292 A x n f)). Qed.
Lemma lem4743295 {A : Type'} (f : nat -> A) (x : A) (n : nat) (a : A) : term1026 A f x n a.
Proof. exact (@lem4743294 A f x n a). Qed.
Lemma lem4743296 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term1026 A f x n a) = (term824 A a f x n).
Proof. exact (eq_refl (term1026 A f x n a)). Qed.
Lemma lem4743297 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : term824 A a f x n.
Proof. exact (EQ_MP (@lem4743296 A a f x n) (@lem4743295 A f x n a)). Qed.
Lemma lem4743298 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) (s : A -> Prop) : term1027 A a f x n s.
Proof. exact (@lem4743297 A a f x n s). Qed.
Lemma lem4743299 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1027 A a f x n s) = (term797 A s a f x n).
Proof. exact (eq_refl (term1027 A a f x n s)). Qed.
Lemma lem4743300 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term797 A s a f x n.
Proof. exact (EQ_MP (@lem4743299 A s a f x n) (@lem4743298 A a f x n s)). Qed.
Lemma lem4743302 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term797 A s a f x n.
Proof. exact (@lem4723146 A s a f x n (@lem4743300 A s a f x n)). Qed.
Lemma lem4743303 {A : Type'} (f : nat -> A) (x : A) (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term819 A s a f x n.
Proof. exact (@lem4743302 A s a f x n (@lem4715763 A a s h1)). Qed.
Lemma lem4743304 {A : Type'} (f : nat -> A) (x : A) (n : nat) (a : A) (s : A -> Prop) (h1 : term252 A s a n) (h2 : @IN A a s) : term817 A s a f x n.
Proof. exact (@lem4743303 A f x n a s h2 (@lem4715822 A s a n h1)). Qed.
Lemma lem4743305 {A : Type'} (x : A) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term252 A s a n) (h3 : @IN A a s) : term815 A s a f x n.
Proof. exact (@lem4743304 A f x n a s h2 h3 (@lem4715928 A n f s a h1)). Qed.
Lemma lem4743306 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term252 A s a n) (h3 : @IN A a s) (h4 : @IN A x s) : term813 A a f x n.
Proof. exact (@lem4743305 A x f n a s h1 h2 h3 (@lem4722014 A x s h4)). Qed.
Lemma lem4743307 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : a = x) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term810 A f x n.
Proof. exact (@lem4743306 A f n a x s h1 h3 h4 h5 (@lem4713737 A a x h2)). Qed.
Lemma lem4743308 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term796 A f x n) (h3 : a = x) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : term807 A.
Proof. exact (@lem4743307 A f n a x s h1 h3 h4 h5 h6 (@lem4723126 A f x n h2)). Qed.
Lemma lem4743309 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term796 A f x n) (h3 : a = x) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : term805.
Proof. exact (@lem4743308 A f n a x s h1 h2 h3 h4 h5 h6 (@lem4723127 A)). Qed.
Lemma lem4743310 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term796 A f x n) (h3 : a = x) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : term801.
Proof. exact (@lem4743309 A f n a x s h1 h2 h3 h4 h5 h6 (@lem4723130)). Qed.
Lemma lem4743311 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term796 A f x n) (h3 : a = x) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : False.
Proof. exact (@lem4743310 A f n a x s h1 h2 h3 h4 h5 h6 (@lem91686)). Qed.
Lemma lem4743312 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term796 A f x n) (h3 : a = x) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : (term796 A f x n) = False.
Proof. exact (prop_ext (fun h7 : term796 A f x n => @lem4743311 A f n a x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4723126 A f x n h2)). Qed.
Lemma lem4743313 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term796 A f x n) (h3 : a = x) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem4743312 A f n a x s h1 h2 h3 h4 h5 h6) (@lem4723126 A f x n h2)). Qed.
Lemma lem4743314 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : a = x) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term795 A f x n.
Proof. exact (fun h0 : term796 A f x n => @lem4743313 A f n a x s h1 h0 h2 h3 h4 h5). Qed.
Lemma lem4743315 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : a = x) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term773 A f x n.
Proof. exact (EQ_MP (@lem4723125 A f x n) (@lem4743314 A f n a x s h1 h2 h3 h4 h5)). Qed.
Lemma lem4743317 (p : Prop) : p = (term320 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4743318 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term794 A f x n) = (term1028 A f x n).
Proof. exact (@lem4743317 (term794 A f x n)). Qed.
Lemma lem4743319 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1028 A f x n) = (term794 A f x n).
Proof. exact (SYM (@lem4743318 A f x n)). Qed.
Lemma lem4743320 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term1029 A f x n) : term1029 A f x n.
Proof. exact (h1). Qed.
Lemma lem4743321 {A : Type'} : term323 A.
Proof. exact (@lem3205803 A). Qed.
Lemma lem4743326 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term1030 A s a f x n) : term1030 A s a f x n.
Proof. exact (h1). Qed.
Lemma lem4743327 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1031 A s a f x n.
Proof. exact (fun h0 : term1030 A s a f x n => @lem4743326 A s a f x n h0). Qed.
Lemma lem4743328 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term1031 A s a f x n) : term1031 A s a f x n.
Proof. exact (h1). Qed.
Lemma lem4743329 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term1030 A s a f x n) : term1030 A s a f x n.
Proof. exact (h1). Qed.
Lemma lem4743330 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term1031 A s a f x n) (h2 : term1030 A s a f x n) : term1030 A s a f x n.
Proof. exact (@lem4743328 A s a f x n h1 (@lem4743329 A s a f x n h2)). Qed.
Lemma lem4743331 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term1030 A s a f x n) : term1032 A s a f x n.
Proof. exact (fun h0 : term1031 A s a f x n => @lem4743330 A s a f x n h0 h1). Qed.
Lemma lem4743332 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term1031 A s a f x n) : term1031 A s a f x n.
Proof. exact (h1). Qed.
Lemma lem4743333 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term1031 A s a f x n) (h2 : term1030 A s a f x n) : term1030 A s a f x n.
Proof. exact (@lem4743331 A s a f x n h2 (@lem4743332 A s a f x n h1)). Qed.
Lemma lem4743334 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) (h1 : term1031 A s a f x n) : term1031 A s a f x n.
Proof. exact (fun h0 : term1030 A s a f x n => @lem4743333 A s a f x n h1 h0). Qed.
Lemma lem4743335 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1033 A s a f x n.
Proof. exact (fun h0 : term1031 A s a f x n => @lem4743334 A s a f x n h0). Qed.
Lemma lem4743338 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1031 A s a f x n.
Proof. exact (@lem4743335 A s a f x n (@lem4743327 A s a f x n)). Qed.
Lemma lem4743339 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1031 A s a f x n.
Proof. exact (@lem4743338 A s a f x n). Qed.
Lemma lem4743403 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4743404 : term801 = term802.
Proof. exact (@lem4743403 term803). Qed.
Lemma lem4743409 {A : Type'} : (term337 A) = (term337 A).
Proof. exact (eq_refl (term337 A)). Qed.
Lemma lem4743410 {A : Type'} : (term1034 A) = (term1035 A).
Proof. exact (MK_COMB (@lem4743409 A) (@lem4743404)). Qed.
Lemma lem4743413 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1036 A f x n) = (term1036 A f x n).
Proof. exact (eq_refl (term1036 A f x n)). Qed.
Lemma lem4743414 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1037 A f x n) = (term1038 A f x n).
Proof. exact (MK_COMB (@lem4743413 A f x n) (@lem4743410 A)). Qed.
Lemma lem4743417 {A : Type'} (a : A) (x : A) : (term704 A a x) = (term704 A a x).
Proof. exact (eq_refl (term704 A a x)). Qed.
Lemma lem4743418 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term1039 A a f x n) = (term1040 A a f x n).
Proof. exact (MK_COMB (@lem4743417 A a x) (@lem4743414 A f x n)). Qed.
Lemma lem4743421 {A : Type'} (x : A) (s : A -> Prop) : (term251 A x s) = (term251 A x s).
Proof. exact (eq_refl (term251 A x s)). Qed.
Lemma lem4743422 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1041 A s a f x n) = (term1042 A s a f x n).
Proof. exact (MK_COMB (@lem4743421 A x s) (@lem4743418 A a f x n)). Qed.
Lemma lem4743425 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term347 A n f s a) = (term347 A n f s a).
Proof. exact (eq_refl (term347 A n f s a)). Qed.
Lemma lem4743426 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1043 A s a f x n) = (term1044 A s a f x n).
Proof. exact (MK_COMB (@lem4743425 A n f s a) (@lem4743422 A s a f x n)). Qed.
Lemma lem4743429 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term255 A s a n) = (term255 A s a n).
Proof. exact (eq_refl (term255 A s a n)). Qed.
Lemma lem4743430 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1045 A s a f x n) = (term1046 A s a f x n).
Proof. exact (MK_COMB (@lem4743429 A s a n) (@lem4743426 A s a f x n)). Qed.
Lemma lem4743433 {A : Type'} (a : A) (s : A -> Prop) : (term251 A a s) = (term251 A a s).
Proof. exact (eq_refl (term251 A a s)). Qed.
Lemma lem4743434 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1030 A s a f x n) = (term1047 A s a f x n).
Proof. exact (MK_COMB (@lem4743433 A a s) (@lem4743430 A s a f x n)). Qed.
Lemma lem4743437 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term1048 A a f x n) = (term1049 A a f x n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4743434 A s a f x n)). Qed.
Lemma lem4743438 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4743439 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term1050 A a f x n) = (term1051 A a f x n).
Proof. exact (MK_COMB (@lem4743438 A) (@lem4743437 A a f x n)). Qed.
Lemma lem4743444 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1052 A f x n) = (term1053 A f x n).
Proof. exact (fun_ext (fun a : A => @lem4743439 A a f x n)). Qed.
Lemma lem4743445 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4743446 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1054 A f x n) = (term1055 A f x n).
Proof. exact (MK_COMB (@lem4743445 A) (@lem4743444 A f x n)). Qed.
Lemma lem4743451 {A : Type'} (x : A) (n : nat) : (term1056 A x n) = (term1057 A x n).
Proof. exact (fun_ext (fun f : nat -> A => @lem4743446 A f x n)). Qed.
Lemma lem4743452 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4743453 {A : Type'} (x : A) (n : nat) : (term1058 A x n) = (term1059 A x n).
Proof. exact (MK_COMB (@lem4743452 A) (@lem4743451 A x n)). Qed.
Lemma lem4743458 {A : Type'} (n : nat) : (term1060 A n) = (term1061 A n).
Proof. exact (fun_ext (fun x : A => @lem4743453 A x n)). Qed.
Lemma lem4743459 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4743460 {A : Type'} (n : nat) : (term1062 A n) = (term1063 A n).
Proof. exact (MK_COMB (@lem4743459 A) (@lem4743458 A n)). Qed.
Lemma lem4743465 {A : Type'} : (term1064 A) = (term1065 A).
Proof. exact (fun_ext (fun n : nat => @lem4743460 A n)). Qed.
Lemma lem4743466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743475 {A : Type'} : (term1066 A) = (term1067 A).
Proof. exact (MK_COMB (@lem4743466) (@lem4743465 A)). Qed.
Lemma lem4743478 (n : nat) : (term842 n) = (term842 n).
Proof. exact (eq_refl (term842 n)). Qed.
Lemma lem4743479 : term843 = term843.
Proof. exact (fun_ext (fun n : nat => @lem4743478 n)). Qed.
Lemma lem4743480 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743481 : term803 = term803.
Proof. exact (MK_COMB (@lem4743480) (@lem4743479)). Qed.
Lemma lem4743482 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4743483 : term802 = term802.
Proof. exact (MK_COMB (@lem4743482) (@lem4743481)). Qed.
Lemma lem4743494 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term380 A x s y) = (term381 A s x y)) = ((term380 A x s y) = (term381 A s x y)).
Proof. exact (eq_refl ((term380 A x s y) = (term381 A s x y))). Qed.
Lemma lem4743495 {A : Type'} (s : A -> Prop) (x : A) : (term382 A s x) = (term382 A s x).
Proof. exact (fun_ext (fun y : A => @lem4743494 A s x y)). Qed.
Lemma lem4743496 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4743497 {A : Type'} (s : A -> Prop) (x : A) : (term383 A s x) = (term383 A s x).
Proof. exact (MK_COMB (@lem4743496 A) (@lem4743495 A s x)). Qed.
Lemma lem4743498 {A : Type'} (s : A -> Prop) : (term384 A s) = (term384 A s).
Proof. exact (fun_ext (fun x : A => @lem4743497 A s x)). Qed.
Lemma lem4743499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4743500 {A : Type'} (s : A -> Prop) : (term385 A s) = (term385 A s).
Proof. exact (MK_COMB (@lem4743499 A) (@lem4743498 A s)). Qed.
Lemma lem4743501 {A : Type'} : (term386 A) = (term386 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4743500 A s)). Qed.
Lemma lem4743502 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4743503 {A : Type'} : (term323 A) = (term323 A).
Proof. exact (MK_COMB (@lem4743502 A) (@lem4743501 A)). Qed.
Lemma lem4743504 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4743505 {A : Type'} : (term337 A) = (term337 A).
Proof. exact (MK_COMB (@lem4743504) (@lem4743503 A)). Qed.
Lemma lem4743506 {A : Type'} : (term1035 A) = (term1035 A).
Proof. exact (MK_COMB (@lem4743505 A) (@lem4743483)). Qed.
Lemma lem4743515 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term789 A f x m n) = (term789 A f x m n).
Proof. exact (eq_refl (term789 A f x m n)). Qed.
Lemma lem4743516 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term790 A f x n) = (term790 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4743515 A f x m n)). Qed.
Lemma lem4743517 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4743518 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term791 A f x n) = (term791 A f x n).
Proof. exact (MK_COMB (@lem4743517) (@lem4743516 A f x n)). Qed.
Lemma lem4743523 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term387 A n f m x) = (term387 A n f m x).
Proof. exact (eq_refl (term387 A n f m x)). Qed.
Lemma lem4743524 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term388 A n f x) = (term388 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4743523 A n f m x)). Qed.
Lemma lem4743525 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem4743526 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term389 A n f x).
Proof. exact (MK_COMB (@lem4743525) (@lem4743524 A n f x)). Qed.
Lemma lem4743527 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4743528 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term1068 A n f x) = (term1068 A n f x).
Proof. exact (MK_COMB (@lem4743527) (@lem4743526 A n f x)). Qed.
Lemma lem4743529 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term794 A f x n) = (term794 A f x n).
Proof. exact (MK_COMB (@lem4743528 A n f x) (@lem4743518 A f x n)). Qed.
Lemma lem4743530 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4743531 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1029 A f x n) = (term1029 A f x n).
Proof. exact (MK_COMB (@lem4743530) (@lem4743529 A f x n)). Qed.
Lemma lem4743532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4743533 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1036 A f x n) = (term1036 A f x n).
Proof. exact (MK_COMB (@lem4743532) (@lem4743531 A f x n)). Qed.
Lemma lem4743534 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1038 A f x n) = (term1038 A f x n).
Proof. exact (MK_COMB (@lem4743533 A f x n) (@lem4743506 A)). Qed.
Lemma lem4743539 {A : Type'} (a : A) (x : A) : (term704 A a x) = (term704 A a x).
Proof. exact (eq_refl (term704 A a x)). Qed.
Lemma lem4743540 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term1040 A a f x n) = (term1040 A a f x n).
Proof. exact (MK_COMB (@lem4743539 A a x) (@lem4743534 A f x n)). Qed.
Lemma lem4743543 {A : Type'} (x : A) (s : A -> Prop) : (term251 A x s) = (term251 A x s).
Proof. exact (eq_refl (term251 A x s)). Qed.
Lemma lem4743544 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1042 A s a f x n) = (term1042 A s a f x n).
Proof. exact (MK_COMB (@lem4743543 A x s) (@lem4743540 A a f x n)). Qed.
Lemma lem4743549 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (s : A -> Prop) (a : A) : (term393 A n f m s a) = (term393 A n f m s a).
Proof. exact (eq_refl (term393 A n f m s a)). Qed.
Lemma lem4743550 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term394 A n f s a) = (term394 A n f s a).
Proof. exact (fun_ext (fun m : nat => @lem4743549 A n f m s a)). Qed.
Lemma lem4743551 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743552 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term268 A n f s a) = (term268 A n f s a).
Proof. exact (MK_COMB (@lem4743551) (@lem4743550 A n f s a)). Qed.
Lemma lem4743553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4743554 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (a : A) : (term347 A n f s a) = (term347 A n f s a).
Proof. exact (MK_COMB (@lem4743553) (@lem4743552 A n f s a)). Qed.
Lemma lem4743555 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1044 A s a f x n) = (term1044 A s a f x n).
Proof. exact (MK_COMB (@lem4743554 A n f s a) (@lem4743544 A s a f x n)). Qed.
Lemma lem4743558 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term255 A s a n) = (term255 A s a n).
Proof. exact (eq_refl (term255 A s a n)). Qed.
Lemma lem4743559 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1046 A s a f x n) = (term1046 A s a f x n).
Proof. exact (MK_COMB (@lem4743558 A s a n) (@lem4743555 A s a f x n)). Qed.
Lemma lem4743562 {A : Type'} (a : A) (s : A -> Prop) : (term251 A a s) = (term251 A a s).
Proof. exact (eq_refl (term251 A a s)). Qed.
Lemma lem4743563 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1047 A s a f x n) = (term1047 A s a f x n).
Proof. exact (MK_COMB (@lem4743562 A a s) (@lem4743559 A s a f x n)). Qed.
Lemma lem4743564 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term1049 A a f x n) = (term1049 A a f x n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4743563 A s a f x n)). Qed.
Lemma lem4743565 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4743566 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term1051 A a f x n) = (term1051 A a f x n).
Proof. exact (MK_COMB (@lem4743565 A) (@lem4743564 A a f x n)). Qed.
Lemma lem4743567 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1053 A f x n) = (term1053 A f x n).
Proof. exact (fun_ext (fun a : A => @lem4743566 A a f x n)). Qed.
Lemma lem4743568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4743569 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1055 A f x n) = (term1055 A f x n).
Proof. exact (MK_COMB (@lem4743568 A) (@lem4743567 A f x n)). Qed.
Lemma lem4743570 {A : Type'} (x : A) (n : nat) : (term1057 A x n) = (term1057 A x n).
Proof. exact (fun_ext (fun f : nat -> A => @lem4743569 A f x n)). Qed.
Lemma lem4743571 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4743572 {A : Type'} (x : A) (n : nat) : (term1059 A x n) = (term1059 A x n).
Proof. exact (MK_COMB (@lem4743571 A) (@lem4743570 A x n)). Qed.
Lemma lem4743573 {A : Type'} (n : nat) : (term1061 A n) = (term1061 A n).
Proof. exact (fun_ext (fun x : A => @lem4743572 A x n)). Qed.
Lemma lem4743574 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4743575 {A : Type'} (n : nat) : (term1063 A n) = (term1063 A n).
Proof. exact (MK_COMB (@lem4743574 A) (@lem4743573 A n)). Qed.
Lemma lem4743576 {A : Type'} : (term1065 A) = (term1065 A).
Proof. exact (fun_ext (fun n : nat => @lem4743575 A n)). Qed.
Lemma lem4743577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743578 {A : Type'} : (term1067 A) = (term1067 A).
Proof. exact (MK_COMB (@lem4743577) (@lem4743576 A)). Qed.
Lemma lem4743667 {A : Type'} : (term1066 A) = (term1067 A).
Proof. exact (TRANS (@lem4743475 A) (@lem4743578 A)). Qed.
Lemma lem4743668 {A : Type'} : (term1067 A) = (term1066 A).
Proof. exact (SYM (@lem4743667 A)). Qed.
Lemma lem4743674 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term1029 A f x n) : term1029 A f x n.
Proof. exact (h1). Qed.
Lemma lem4743772 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term399 A n f m x) = (term400 A n f m x).
Proof. exact (@lem17045 (Peano.lt m n) ((f m) = x)). Qed.
Lemma lem4743777 (m' : nat) (m : nat) : (m' = m) = (m' = m).
Proof. exact (eq_refl (m' = m)). Qed.
Lemma lem4743778 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4743779 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term401 A n f x m') = (term387 A n f m' x).
Proof. exact (eq_refl (term401 A n f x m')). Qed.
Lemma lem4743780 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term399 A n f m' x) = (term400 A n f m' x).
Proof. exact (@lem4743772 A n f m' x). Qed.
Lemma lem4743781 (P : nat -> Prop) : (@ex1 nat P) = (term402 P).
Proof. exact (@lem18897 nat P). Qed.
Lemma lem4743782 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term403 A n f x).
Proof. exact (@lem4743781 (term388 A n f x)). Qed.
Lemma lem4743783 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4743784 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term404 A n f x m') = (term399 A n f m' x).
Proof. exact (MK_COMB (@lem4743783) (@lem4743779 A n f m' x)). Qed.
Lemma lem4743785 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term404 A n f x m') = (term400 A n f m' x).
Proof. exact (TRANS (@lem4743784 A n f m' x) (@lem4743780 A n f m' x)). Qed.
Lemma lem4743786 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4743787 {A : Type'} (n : nat) (f : nat -> A) (m' : nat) (x : A) : (term405 A n f x m') = (term406 A n f m' x).
Proof. exact (MK_COMB (@lem4743786) (@lem4743785 A n f m' x)). Qed.
Lemma lem4743788 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term407 A n f x m' m) = (term408 A n f x m' m).
Proof. exact (MK_COMB (@lem4743787 A n f m' x) (@lem4743777 m' m)). Qed.
Lemma lem4743789 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4743790 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term404 A n f x m) = (term399 A n f m x).
Proof. exact (MK_COMB (@lem4743789) (@lem4743778 A n f m x)). Qed.
Lemma lem4743791 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term404 A n f x m) = (term400 A n f m x).
Proof. exact (TRANS (@lem4743790 A n f m x) (@lem4743772 A n f m x)). Qed.
Lemma lem4743792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4743793 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term405 A n f x m) = (term406 A n f m x).
Proof. exact (MK_COMB (@lem4743792) (@lem4743791 A n f m x)). Qed.
Lemma lem4743794 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term409 A n f x m' m) = (term410 A n f x m' m).
Proof. exact (MK_COMB (@lem4743793 A n f m x) (@lem4743788 A n f x m' m)). Qed.
Lemma lem4743795 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term411 A n f x m) = (term412 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4743794 A n f x m' m)). Qed.
Lemma lem4743796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743797 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term413 A n f x m) = (term414 A n f x m).
Proof. exact (MK_COMB (@lem4743796) (@lem4743795 A n f x m)). Qed.
Lemma lem4743798 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term415 A n f x) = (term416 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4743797 A n f x m)). Qed.
Lemma lem4743799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743800 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term417 A n f x) = (term418 A n f x).
Proof. exact (MK_COMB (@lem4743799) (@lem4743798 A n f x)). Qed.
Lemma lem4743801 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4743802 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term419 A n f x) = (term388 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4743801 A n f m x)). Qed.
Lemma lem4743803 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4743804 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term420 A n f x) = (term421 A n f x).
Proof. exact (MK_COMB (@lem4743803) (@lem4743802 A n f x)). Qed.
Lemma lem4743805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4743806 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term422 A n f x) = (term423 A n f x).
Proof. exact (MK_COMB (@lem4743805) (@lem4743804 A n f x)). Qed.
Lemma lem4743807 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term403 A n f x) = (term424 A n f x).
Proof. exact (MK_COMB (@lem4743806 A n f x) (@lem4743800 A n f x)). Qed.
Lemma lem4743808 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term389 A n f x) = (term424 A n f x).
Proof. exact (TRANS (@lem4743782 A n f x) (@lem4743807 A n f x)). Qed.
Lemma lem4743817 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term844 A n f m x) = (term845 A n f m x).
Proof. exact (@lem17362 (Peano.lt m n) ((f m) = x)). Qed.
Lemma lem4743822 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term757 A n f m x) = (term846 A n f m x).
Proof. exact (@lem17265 (Peano.lt m n) ((f m) = x)). Qed.
Lemma lem4743823 (m : nat) (n : nat) : (term312 m n) = (term312 m n).
Proof. exact (eq_refl (term312 m n)). Qed.
Lemma lem4743824 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem4743825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4743826 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term853 A n f m x) = (term854 A n f m x).
Proof. exact (MK_COMB (@lem4743825) (@lem4743817 A n f m x)). Qed.
Lemma lem4743827 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1069 A f x m n) = (term938 A f x m n).
Proof. exact (MK_COMB (@lem4743826 A n f m x) (@lem4743823 m n)). Qed.
Lemma lem4743828 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1070 A f x m n) = (term1069 A f x m n).
Proof. exact (@lem17045 (term757 A n f m x) (Peano.lt m n)). Qed.
Lemma lem4743829 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1070 A f x m n) = (term938 A f x m n).
Proof. exact (TRANS (@lem4743828 A f x m n) (@lem4743827 A f x m n)). Qed.
Lemma lem4743830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4743831 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term758 A n f m x) = (term858 A n f m x).
Proof. exact (MK_COMB (@lem4743830) (@lem4743822 A n f m x)). Qed.
Lemma lem4743832 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term789 A f x m n) = (term1071 A f x m n).
Proof. exact (MK_COMB (@lem4743831 A n f m x) (@lem4743824 m n)). Qed.
Lemma lem4743833 (m' : nat) (m : nat) : (term860 m' m) = (term860 m' m).
Proof. exact (eq_refl (term860 m' m)). Qed.
Lemma lem4743835 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1072 A f x n m) = (term789 A f x m n).
Proof. exact (eq_refl (term1072 A f x n m)). Qed.
Lemma lem4743836 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (n : nat) : (term1072 A f x n m') = (term789 A f x m' n).
Proof. exact (eq_refl (term1072 A f x n m')). Qed.
Lemma lem4743837 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (n : nat) : (term789 A f x m' n) = (term1071 A f x m' n).
Proof. exact (@lem4743832 A f x m' n). Qed.
Lemma lem4743838 (P : nat -> Prop) : (term862 P) = (term863 P).
Proof. exact (@lem18393 nat P). Qed.
Lemma lem4743839 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1073 A f x n) = (term1074 A f x n).
Proof. exact (@lem4743838 (term790 A f x n)). Qed.
Lemma lem4743840 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (n : nat) : (term1072 A f x n m') = (term1071 A f x m' n).
Proof. exact (TRANS (@lem4743836 A f x m' n) (@lem4743837 A f x m' n)). Qed.
Lemma lem4743841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4743842 {A : Type'} (f : nat -> A) (x : A) (m' : nat) (n : nat) : (term1075 A f x n m') = (term1076 A f x m' n).
Proof. exact (MK_COMB (@lem4743841) (@lem4743840 A f x m' n)). Qed.
Lemma lem4743843 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1077 A f x n m' m) = (term1078 A f x n m' m).
Proof. exact (MK_COMB (@lem4743842 A f x m' n) (@lem4743833 m' m)). Qed.
Lemma lem4743844 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1072 A f x n m) = (term1071 A f x m n).
Proof. exact (TRANS (@lem4743835 A f x m n) (@lem4743832 A f x m n)). Qed.
Lemma lem4743845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4743846 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1075 A f x n m) = (term1076 A f x m n).
Proof. exact (MK_COMB (@lem4743845) (@lem4743844 A f x m n)). Qed.
Lemma lem4743847 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1079 A f x n m' m) = (term1080 A f x n m' m).
Proof. exact (MK_COMB (@lem4743846 A f x m n) (@lem4743843 A f x n m' m)). Qed.
Lemma lem4743848 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1081 A f x n m) = (term1082 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4743847 A f x n m' m)). Qed.
Lemma lem4743849 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4743850 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1083 A f x n m) = (term1084 A f x n m).
Proof. exact (MK_COMB (@lem4743849) (@lem4743848 A f x n m)). Qed.
Lemma lem4743851 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1085 A f x n) = (term1086 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4743850 A f x n m)). Qed.
Lemma lem4743852 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4743853 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1087 A f x n) = (term1088 A f x n).
Proof. exact (MK_COMB (@lem4743852) (@lem4743851 A f x n)). Qed.
Lemma lem4743854 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4743855 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1089 A f x n m) = (term1070 A f x m n).
Proof. exact (MK_COMB (@lem4743854) (@lem4743835 A f x m n)). Qed.
Lemma lem4743856 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1089 A f x n m) = (term938 A f x m n).
Proof. exact (TRANS (@lem4743855 A f x m n) (@lem4743829 A f x m n)). Qed.
Lemma lem4743857 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1090 A f x n) = (term1091 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4743856 A f x m n)). Qed.
Lemma lem4743858 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743859 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1092 A f x n) = (term1093 A f x n).
Proof. exact (MK_COMB (@lem4743858) (@lem4743857 A f x n)). Qed.
Lemma lem4743860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4743861 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1094 A f x n) = (term1095 A f x n).
Proof. exact (MK_COMB (@lem4743860) (@lem4743859 A f x n)). Qed.
Lemma lem4743862 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1074 A f x n) = (term1096 A f x n).
Proof. exact (MK_COMB (@lem4743861 A f x n) (@lem4743853 A f x n)). Qed.
Lemma lem4743863 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1073 A f x n) = (term1096 A f x n).
Proof. exact (TRANS (@lem4743839 A f x n) (@lem4743862 A f x n)). Qed.
Lemma lem4743864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4743865 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term1097 A n f x) = (term1098 A n f x).
Proof. exact (MK_COMB (@lem4743864) (@lem4743808 A n f x)). Qed.
Lemma lem4743866 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1099 A f x n) = (term1100 A f x n).
Proof. exact (MK_COMB (@lem4743865 A n f x) (@lem4743863 A f x n)). Qed.
Lemma lem4743867 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1029 A f x n) = (term1099 A f x n).
Proof. exact (@lem17362 (term389 A n f x) (term791 A f x n)). Qed.
Lemma lem4743868 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1029 A f x n) = (term1100 A f x n).
Proof. exact (TRANS (@lem4743867 A f x n) (@lem4743866 A f x n)). Qed.
Lemma lem4743922 {A : Type'} (P : Prop) (Q : A -> Prop) : (term430 A P Q) = (term431 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem4743923 (P : Prop) (Q : nat -> Prop) : (term432 P Q) = (term433 P Q).
Proof. exact (@lem4743922 nat P Q). Qed.
Lemma lem4743924 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term434 A n f x m) = (term435 A n f x m).
Proof. exact (@lem4743923 (term400 A n f m x) (term436 A n f x m)). Qed.
Lemma lem4743925 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term437 A n f x m m') = (term408 A n f x m' m).
Proof. exact (eq_refl (term437 A n f x m m')). Qed.
Lemma lem4743926 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term406 A n f m x) = (term406 A n f m x).
Proof. exact (eq_refl (term406 A n f m x)). Qed.
Lemma lem4743927 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term438 A n f x m m') = (term410 A n f x m' m).
Proof. exact (MK_COMB (@lem4743926 A n f m x) (@lem4743925 A n f x m' m)). Qed.
Lemma lem4743928 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term439 A n f x m) = (term412 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4743927 A n f x m' m)). Qed.
Lemma lem4743929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743930 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term434 A n f x m) = (term414 A n f x m).
Proof. exact (MK_COMB (@lem4743929) (@lem4743928 A n f x m)). Qed.
Lemma lem4743931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4743932 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term440 A n f x m) = (term441 A n f x m).
Proof. exact (MK_COMB (@lem4743931) (@lem4743930 A n f x m)). Qed.
Lemma lem4743933 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term437 A n f x m m') = (term408 A n f x m' m).
Proof. exact (eq_refl (term437 A n f x m m')). Qed.
Lemma lem4743934 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term442 A n f x m) = (term436 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4743933 A n f x m' m)). Qed.
Lemma lem4743935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743936 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term443 A n f x m) = (term444 A n f x m).
Proof. exact (MK_COMB (@lem4743935) (@lem4743934 A n f x m)). Qed.
Lemma lem4743937 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term406 A n f m x) = (term406 A n f m x).
Proof. exact (eq_refl (term406 A n f m x)). Qed.
Lemma lem4743938 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term435 A n f x m) = (term445 A n f x m).
Proof. exact (MK_COMB (@lem4743937 A n f m x) (@lem4743936 A n f x m)). Qed.
Lemma lem4743939 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : ((term434 A n f x m) = (term435 A n f x m)) = ((term414 A n f x m) = (term445 A n f x m)).
Proof. exact (MK_COMB (@lem4743932 A n f x m) (@lem4743938 A n f x m)). Qed.
Lemma lem4743940 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term414 A n f x m) = (term445 A n f x m).
Proof. exact (EQ_MP (@lem4743939 A n f x m) (@lem4743924 A n f x m)). Qed.
Lemma lem4743989 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term416 A n f x) = (term446 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4743940 A n f x m)). Qed.
Lemma lem4743990 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4743991 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term418 A n f x) = (term447 A n f x).
Proof. exact (MK_COMB (@lem4743990) (@lem4743989 A n f x)). Qed.
Lemma lem4744040 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term423 A n f x) = (term423 A n f x).
Proof. exact (eq_refl (term423 A n f x)). Qed.
Lemma lem4744041 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term424 A n f x) = (term448 A n f x).
Proof. exact (MK_COMB (@lem4744040 A n f x) (@lem4743991 A n f x)). Qed.
Lemma lem4744042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4744043 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term1098 A n f x) = (term1101 A n f x).
Proof. exact (MK_COMB (@lem4744042) (@lem4744041 A n f x)). Qed.
Lemma lem4744097 {A : Type'} (P : Prop) (Q : A -> Prop) : (term887 A P Q) = (term888 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem4744098 (P : Prop) (Q : nat -> Prop) : (term889 P Q) = (term890 P Q).
Proof. exact (@lem4744097 nat P Q). Qed.
Lemma lem4744099 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1102 A f x n m) = (term1103 A f x n m).
Proof. exact (@lem4744098 (term1071 A f x m n) (term1104 A f x n m)). Qed.
Lemma lem4744100 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1105 A f x n m m') = (term1078 A f x n m' m).
Proof. exact (eq_refl (term1105 A f x n m m')). Qed.
Lemma lem4744101 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1076 A f x m n) = (term1076 A f x m n).
Proof. exact (eq_refl (term1076 A f x m n)). Qed.
Lemma lem4744102 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1106 A f x n m m') = (term1080 A f x n m' m).
Proof. exact (MK_COMB (@lem4744101 A f x m n) (@lem4744100 A f x n m' m)). Qed.
Lemma lem4744103 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1107 A f x n m) = (term1082 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4744102 A f x n m' m)). Qed.
Lemma lem4744104 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744105 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1102 A f x n m) = (term1084 A f x n m).
Proof. exact (MK_COMB (@lem4744104) (@lem4744103 A f x n m)). Qed.
Lemma lem4744106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4744107 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1108 A f x n m) = (term1109 A f x n m).
Proof. exact (MK_COMB (@lem4744106) (@lem4744105 A f x n m)). Qed.
Lemma lem4744108 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1105 A f x n m m') = (term1078 A f x n m' m).
Proof. exact (eq_refl (term1105 A f x n m m')). Qed.
Lemma lem4744109 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1110 A f x n m) = (term1104 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4744108 A f x n m' m)). Qed.
Lemma lem4744110 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744111 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1111 A f x n m) = (term1112 A f x n m).
Proof. exact (MK_COMB (@lem4744110) (@lem4744109 A f x n m)). Qed.
Lemma lem4744112 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1076 A f x m n) = (term1076 A f x m n).
Proof. exact (eq_refl (term1076 A f x m n)). Qed.
Lemma lem4744113 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1103 A f x n m) = (term1113 A f x n m).
Proof. exact (MK_COMB (@lem4744112 A f x m n) (@lem4744111 A f x n m)). Qed.
Lemma lem4744114 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : ((term1102 A f x n m) = (term1103 A f x n m)) = ((term1084 A f x n m) = (term1113 A f x n m)).
Proof. exact (MK_COMB (@lem4744107 A f x n m) (@lem4744113 A f x n m)). Qed.
Lemma lem4744115 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1084 A f x n m) = (term1113 A f x n m).
Proof. exact (EQ_MP (@lem4744114 A f x n m) (@lem4744099 A f x n m)). Qed.
Lemma lem4744164 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1086 A f x n) = (term1114 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4744115 A f x n m)). Qed.
Lemma lem4744165 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744166 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1088 A f x n) = (term1115 A f x n).
Proof. exact (MK_COMB (@lem4744165) (@lem4744164 A f x n)). Qed.
Lemma lem4744215 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1095 A f x n) = (term1095 A f x n).
Proof. exact (eq_refl (term1095 A f x n)). Qed.
Lemma lem4744216 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1096 A f x n) = (term1116 A f x n).
Proof. exact (MK_COMB (@lem4744215 A f x n) (@lem4744166 A f x n)). Qed.
Lemma lem4744217 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1100 A f x n) = (term1117 A f x n).
Proof. exact (MK_COMB (@lem4744043 A n f x) (@lem4744216 A f x n)). Qed.
Lemma lem4744219 {A : Type'} (P : A -> Prop) (Q : Prop) : (term452 A P Q) = (term453 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4744220 (P : nat -> Prop) (Q : Prop) : (term454 P Q) = (term455 P Q).
Proof. exact (@lem4744219 nat P Q). Qed.
Lemma lem4744221 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term456 A n f x) = (term457 A n f x).
Proof. exact (@lem4744220 (term388 A n f x) (term447 A n f x)). Qed.
Lemma lem4744222 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4744223 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term419 A n f x) = (term388 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4744222 A n f m x)). Qed.
Lemma lem4744224 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744225 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term420 A n f x) = (term421 A n f x).
Proof. exact (MK_COMB (@lem4744224) (@lem4744223 A n f x)). Qed.
Lemma lem4744226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4744227 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term422 A n f x) = (term423 A n f x).
Proof. exact (MK_COMB (@lem4744226) (@lem4744225 A n f x)). Qed.
Lemma lem4744228 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term447 A n f x) = (term447 A n f x).
Proof. exact (eq_refl (term447 A n f x)). Qed.
Lemma lem4744229 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term456 A n f x) = (term448 A n f x).
Proof. exact (MK_COMB (@lem4744227 A n f x) (@lem4744228 A n f x)). Qed.
Lemma lem4744230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4744231 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term458 A n f x) = (term459 A n f x).
Proof. exact (MK_COMB (@lem4744230) (@lem4744229 A n f x)). Qed.
Lemma lem4744232 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term401 A n f x m) = (term387 A n f m x).
Proof. exact (eq_refl (term401 A n f x m)). Qed.
Lemma lem4744233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4744234 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term460 A n f x m) = (term461 A n f m x).
Proof. exact (MK_COMB (@lem4744233) (@lem4744232 A n f m x)). Qed.
Lemma lem4744235 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term447 A n f x) = (term447 A n f x).
Proof. exact (eq_refl (term447 A n f x)). Qed.
Lemma lem4744236 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term462 A m n f x) = (term463 A m n f x).
Proof. exact (MK_COMB (@lem4744234 A n f m x) (@lem4744235 A n f x)). Qed.
Lemma lem4744237 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term464 A n f x) = (term465 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4744236 A m n f x)). Qed.
Lemma lem4744238 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744239 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term457 A n f x) = (term466 A n f x).
Proof. exact (MK_COMB (@lem4744238) (@lem4744237 A n f x)). Qed.
Lemma lem4744240 {A : Type'} (n : nat) (f : nat -> A) (x : A) : ((term456 A n f x) = (term457 A n f x)) = ((term448 A n f x) = (term466 A n f x)).
Proof. exact (MK_COMB (@lem4744231 A n f x) (@lem4744239 A n f x)). Qed.
Lemma lem4744241 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term448 A n f x) = (term466 A n f x).
Proof. exact (EQ_MP (@lem4744240 A n f x) (@lem4744221 A n f x)). Qed.
Lemma lem4744242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4744243 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term1101 A n f x) = (term1118 A n f x).
Proof. exact (MK_COMB (@lem4744242) (@lem4744241 A n f x)). Qed.
Lemma lem4744245 {A : Type'} (P : Prop) (Q : A -> Prop) : (term888 A P Q) = (term887 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4744246 (P : Prop) (Q : nat -> Prop) : (term890 P Q) = (term889 P Q).
Proof. exact (@lem4744245 nat P Q). Qed.
Lemma lem4744247 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1103 A f x n m) = (term1102 A f x n m).
Proof. exact (@lem4744246 (term1071 A f x m n) (term1104 A f x n m)). Qed.
Lemma lem4744248 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1105 A f x n m m') = (term1078 A f x n m' m).
Proof. exact (eq_refl (term1105 A f x n m m')). Qed.
Lemma lem4744249 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1110 A f x n m) = (term1104 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4744248 A f x n m' m)). Qed.
Lemma lem4744250 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744251 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1111 A f x n m) = (term1112 A f x n m).
Proof. exact (MK_COMB (@lem4744250) (@lem4744249 A f x n m)). Qed.
Lemma lem4744252 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1076 A f x m n) = (term1076 A f x m n).
Proof. exact (eq_refl (term1076 A f x m n)). Qed.
Lemma lem4744253 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1103 A f x n m) = (term1113 A f x n m).
Proof. exact (MK_COMB (@lem4744252 A f x m n) (@lem4744251 A f x n m)). Qed.
Lemma lem4744254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4744255 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1119 A f x n m) = (term1120 A f x n m).
Proof. exact (MK_COMB (@lem4744254) (@lem4744253 A f x n m)). Qed.
Lemma lem4744256 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1105 A f x n m m') = (term1078 A f x n m' m).
Proof. exact (eq_refl (term1105 A f x n m m')). Qed.
Lemma lem4744257 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term1076 A f x m n) = (term1076 A f x m n).
Proof. exact (eq_refl (term1076 A f x m n)). Qed.
Lemma lem4744258 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1106 A f x n m m') = (term1080 A f x n m' m).
Proof. exact (MK_COMB (@lem4744257 A f x m n) (@lem4744256 A f x n m' m)). Qed.
Lemma lem4744259 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1107 A f x n m) = (term1082 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4744258 A f x n m' m)). Qed.
Lemma lem4744260 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744261 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1102 A f x n m) = (term1084 A f x n m).
Proof. exact (MK_COMB (@lem4744260) (@lem4744259 A f x n m)). Qed.
Lemma lem4744262 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : ((term1103 A f x n m) = (term1102 A f x n m)) = ((term1113 A f x n m) = (term1084 A f x n m)).
Proof. exact (MK_COMB (@lem4744255 A f x n m) (@lem4744261 A f x n m)). Qed.
Lemma lem4744263 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1113 A f x n m) = (term1084 A f x n m).
Proof. exact (EQ_MP (@lem4744262 A f x n m) (@lem4744247 A f x n m)). Qed.
Lemma lem4744264 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1114 A f x n) = (term1086 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4744263 A f x n m)). Qed.
Lemma lem4744265 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744266 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1115 A f x n) = (term1088 A f x n).
Proof. exact (MK_COMB (@lem4744265) (@lem4744264 A f x n)). Qed.
Lemma lem4744267 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1095 A f x n) = (term1095 A f x n).
Proof. exact (eq_refl (term1095 A f x n)). Qed.
Lemma lem4744268 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1116 A f x n) = (term1096 A f x n).
Proof. exact (MK_COMB (@lem4744267 A f x n) (@lem4744266 A f x n)). Qed.
Lemma lem4744270 {A : Type'} (P : Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4744271 (P : Prop) (Q : nat -> Prop) : (term470 P Q) = (term471 P Q).
Proof. exact (@lem4744270 nat P Q). Qed.
Lemma lem4744272 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1121 A f x n) = (term1122 A f x n).
Proof. exact (@lem4744271 (term1093 A f x n) (term1086 A f x n)). Qed.
Lemma lem4744273 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1123 A f x n m) = (term1084 A f x n m).
Proof. exact (eq_refl (term1123 A f x n m)). Qed.
Lemma lem4744274 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1124 A f x n) = (term1086 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4744273 A f x n m)). Qed.
Lemma lem4744275 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744276 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1125 A f x n) = (term1088 A f x n).
Proof. exact (MK_COMB (@lem4744275) (@lem4744274 A f x n)). Qed.
Lemma lem4744277 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1095 A f x n) = (term1095 A f x n).
Proof. exact (eq_refl (term1095 A f x n)). Qed.
Lemma lem4744278 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1121 A f x n) = (term1096 A f x n).
Proof. exact (MK_COMB (@lem4744277 A f x n) (@lem4744276 A f x n)). Qed.
Lemma lem4744279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4744280 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1126 A f x n) = (term1127 A f x n).
Proof. exact (MK_COMB (@lem4744279) (@lem4744278 A f x n)). Qed.
Lemma lem4744281 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1123 A f x n m) = (term1084 A f x n m).
Proof. exact (eq_refl (term1123 A f x n m)). Qed.
Lemma lem4744282 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1095 A f x n) = (term1095 A f x n).
Proof. exact (eq_refl (term1095 A f x n)). Qed.
Lemma lem4744283 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1128 A f x n m) = (term1129 A f x n m).
Proof. exact (MK_COMB (@lem4744282 A f x n) (@lem4744281 A f x n m)). Qed.
Lemma lem4744284 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1130 A f x n) = (term1131 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4744283 A f x n m)). Qed.
Lemma lem4744285 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744286 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1122 A f x n) = (term1132 A f x n).
Proof. exact (MK_COMB (@lem4744285) (@lem4744284 A f x n)). Qed.
Lemma lem4744287 {A : Type'} (f : nat -> A) (x : A) (n : nat) : ((term1121 A f x n) = (term1122 A f x n)) = ((term1096 A f x n) = (term1132 A f x n)).
Proof. exact (MK_COMB (@lem4744280 A f x n) (@lem4744286 A f x n)). Qed.
Lemma lem4744288 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1096 A f x n) = (term1132 A f x n).
Proof. exact (EQ_MP (@lem4744287 A f x n) (@lem4744272 A f x n)). Qed.
Lemma lem4744290 {A : Type'} (P : Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4744291 (P : Prop) (Q : nat -> Prop) : (term470 P Q) = (term471 P Q).
Proof. exact (@lem4744290 nat P Q). Qed.
Lemma lem4744292 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1133 A f x n m) = (term1134 A f x n m).
Proof. exact (@lem4744291 (term1093 A f x n) (term1082 A f x n m)). Qed.
Lemma lem4744293 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1135 A f x n m m') = (term1080 A f x n m' m).
Proof. exact (eq_refl (term1135 A f x n m m')). Qed.
Lemma lem4744294 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1136 A f x n m) = (term1082 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4744293 A f x n m' m)). Qed.
Lemma lem4744295 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744296 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1137 A f x n m) = (term1084 A f x n m).
Proof. exact (MK_COMB (@lem4744295) (@lem4744294 A f x n m)). Qed.
Lemma lem4744297 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1095 A f x n) = (term1095 A f x n).
Proof. exact (eq_refl (term1095 A f x n)). Qed.
Lemma lem4744298 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1133 A f x n m) = (term1129 A f x n m).
Proof. exact (MK_COMB (@lem4744297 A f x n) (@lem4744296 A f x n m)). Qed.
Lemma lem4744299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4744300 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1138 A f x n m) = (term1139 A f x n m).
Proof. exact (MK_COMB (@lem4744299) (@lem4744298 A f x n m)). Qed.
Lemma lem4744301 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1135 A f x n m m') = (term1080 A f x n m' m).
Proof. exact (eq_refl (term1135 A f x n m m')). Qed.
Lemma lem4744302 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1095 A f x n) = (term1095 A f x n).
Proof. exact (eq_refl (term1095 A f x n)). Qed.
Lemma lem4744303 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) (m : nat) : (term1140 A f x n m m') = (term1141 A f x n m' m).
Proof. exact (MK_COMB (@lem4744302 A f x n) (@lem4744301 A f x n m' m)). Qed.
Lemma lem4744304 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1142 A f x n m) = (term1143 A f x n m).
Proof. exact (fun_ext (fun m' : nat => @lem4744303 A f x n m' m)). Qed.
Lemma lem4744305 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744306 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1134 A f x n m) = (term1144 A f x n m).
Proof. exact (MK_COMB (@lem4744305) (@lem4744304 A f x n m)). Qed.
Lemma lem4744307 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : ((term1133 A f x n m) = (term1134 A f x n m)) = ((term1129 A f x n m) = (term1144 A f x n m)).
Proof. exact (MK_COMB (@lem4744300 A f x n m) (@lem4744306 A f x n m)). Qed.
Lemma lem4744308 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1129 A f x n m) = (term1144 A f x n m).
Proof. exact (EQ_MP (@lem4744307 A f x n m) (@lem4744292 A f x n m)). Qed.
Lemma lem4744309 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1131 A f x n) = (term1145 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4744308 A f x n m)). Qed.
Lemma lem4744310 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744311 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1132 A f x n) = (term1146 A f x n).
Proof. exact (MK_COMB (@lem4744310) (@lem4744309 A f x n)). Qed.
Lemma lem4744312 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1096 A f x n) = (term1146 A f x n).
Proof. exact (TRANS (@lem4744288 A f x n) (@lem4744311 A f x n)). Qed.
Lemma lem4744313 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1116 A f x n) = (term1146 A f x n).
Proof. exact (TRANS (@lem4744268 A f x n) (@lem4744312 A f x n)). Qed.
Lemma lem4744314 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1117 A f x n) = (term1147 A f x n).
Proof. exact (MK_COMB (@lem4744243 A n f x) (@lem4744313 A f x n)). Qed.
Lemma lem4744316 {A : Type'} (P : A -> Prop) (Q : Prop) : (term452 A P Q) = (term453 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4744317 (P : nat -> Prop) (Q : Prop) : (term454 P Q) = (term455 P Q).
Proof. exact (@lem4744316 nat P Q). Qed.
Lemma lem4744318 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1148 A f x n) = (term1149 A f x n).
Proof. exact (@lem4744317 (term465 A n f x) (term1146 A f x n)). Qed.
Lemma lem4744319 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term475 A n f x m) = (term463 A m n f x).
Proof. exact (eq_refl (term475 A n f x m)). Qed.
Lemma lem4744320 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term476 A n f x) = (term465 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4744319 A m n f x)). Qed.
Lemma lem4744321 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744322 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term477 A n f x) = (term466 A n f x).
Proof. exact (MK_COMB (@lem4744321) (@lem4744320 A n f x)). Qed.
Lemma lem4744323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4744324 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term1150 A n f x) = (term1118 A n f x).
Proof. exact (MK_COMB (@lem4744323) (@lem4744322 A n f x)). Qed.
Lemma lem4744325 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1146 A f x n) = (term1146 A f x n).
Proof. exact (eq_refl (term1146 A f x n)). Qed.
Lemma lem4744326 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1148 A f x n) = (term1147 A f x n).
Proof. exact (MK_COMB (@lem4744324 A n f x) (@lem4744325 A f x n)). Qed.
Lemma lem4744327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4744328 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1151 A f x n) = (term1152 A f x n).
Proof. exact (MK_COMB (@lem4744327) (@lem4744326 A f x n)). Qed.
Lemma lem4744329 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term475 A n f x m) = (term463 A m n f x).
Proof. exact (eq_refl (term475 A n f x m)). Qed.
Lemma lem4744330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4744331 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term1153 A n f x m) = (term1154 A m n f x).
Proof. exact (MK_COMB (@lem4744330) (@lem4744329 A m n f x)). Qed.
Lemma lem4744332 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1146 A f x n) = (term1146 A f x n).
Proof. exact (eq_refl (term1146 A f x n)). Qed.
Lemma lem4744333 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1155 A m f x n) = (term1156 A m f x n).
Proof. exact (MK_COMB (@lem4744331 A m n f x) (@lem4744332 A f x n)). Qed.
Lemma lem4744334 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1157 A f x n) = (term1158 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4744333 A m f x n)). Qed.
Lemma lem4744335 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744336 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1149 A f x n) = (term1159 A f x n).
Proof. exact (MK_COMB (@lem4744335) (@lem4744334 A f x n)). Qed.
Lemma lem4744337 {A : Type'} (f : nat -> A) (x : A) (n : nat) : ((term1148 A f x n) = (term1149 A f x n)) = ((term1147 A f x n) = (term1159 A f x n)).
Proof. exact (MK_COMB (@lem4744328 A f x n) (@lem4744336 A f x n)). Qed.
Lemma lem4744338 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1147 A f x n) = (term1159 A f x n).
Proof. exact (EQ_MP (@lem4744337 A f x n) (@lem4744318 A f x n)). Qed.
Lemma lem4744340 {A : Type'} (P : Prop) (Q : A -> Prop) : (term888 A P Q) = (term887 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4744341 (P : Prop) (Q : nat -> Prop) : (term890 P Q) = (term889 P Q).
Proof. exact (@lem4744340 nat P Q). Qed.
Lemma lem4744342 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1160 A m f x n) = (term1161 A m f x n).
Proof. exact (@lem4744341 (term463 A m n f x) (term1145 A f x n)). Qed.
Lemma lem4744343 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m : nat) : (term1162 A f x n m) = (term1144 A f x n m).
Proof. exact (eq_refl (term1162 A f x n m)). Qed.
Lemma lem4744344 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1163 A f x n) = (term1145 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4744343 A f x n m)). Qed.
Lemma lem4744345 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744346 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1164 A f x n) = (term1146 A f x n).
Proof. exact (MK_COMB (@lem4744345) (@lem4744344 A f x n)). Qed.
Lemma lem4744347 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term1154 A m n f x) = (term1154 A m n f x).
Proof. exact (eq_refl (term1154 A m n f x)). Qed.
Lemma lem4744348 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1160 A m f x n) = (term1156 A m f x n).
Proof. exact (MK_COMB (@lem4744347 A m n f x) (@lem4744346 A f x n)). Qed.
Lemma lem4744349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4744350 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1165 A m f x n) = (term1166 A m f x n).
Proof. exact (MK_COMB (@lem4744349) (@lem4744348 A m f x n)). Qed.
Lemma lem4744351 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1162 A f x n m') = (term1144 A f x n m').
Proof. exact (eq_refl (term1162 A f x n m')). Qed.
Lemma lem4744352 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term1154 A m n f x) = (term1154 A m n f x).
Proof. exact (eq_refl (term1154 A m n f x)). Qed.
Lemma lem4744353 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1167 A m f x n m') = (term1168 A m f x n m').
Proof. exact (MK_COMB (@lem4744352 A m n f x) (@lem4744351 A f x n m')). Qed.
Lemma lem4744354 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1169 A m f x n) = (term1170 A m f x n).
Proof. exact (fun_ext (fun m' : nat => @lem4744353 A m f x n m')). Qed.
Lemma lem4744355 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744356 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1161 A m f x n) = (term1171 A m f x n).
Proof. exact (MK_COMB (@lem4744355) (@lem4744354 A m f x n)). Qed.
Lemma lem4744357 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : ((term1160 A m f x n) = (term1161 A m f x n)) = ((term1156 A m f x n) = (term1171 A m f x n)).
Proof. exact (MK_COMB (@lem4744350 A m f x n) (@lem4744356 A m f x n)). Qed.
Lemma lem4744358 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1156 A m f x n) = (term1171 A m f x n).
Proof. exact (EQ_MP (@lem4744357 A m f x n) (@lem4744342 A m f x n)). Qed.
Lemma lem4744360 {A : Type'} (P : Prop) (Q : A -> Prop) : (term888 A P Q) = (term887 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4744361 (P : Prop) (Q : nat -> Prop) : (term890 P Q) = (term889 P Q).
Proof. exact (@lem4744360 nat P Q). Qed.
Lemma lem4744362 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1172 A m f x n m') = (term1173 A m f x n m').
Proof. exact (@lem4744361 (term463 A m n f x) (term1143 A f x n m')). Qed.
Lemma lem4744363 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) : (term1174 A f x n m' m'') = (term1141 A f x n m'' m').
Proof. exact (eq_refl (term1174 A f x n m' m'')). Qed.
Lemma lem4744364 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1175 A f x n m') = (term1143 A f x n m').
Proof. exact (fun_ext (fun m'' : nat => @lem4744363 A f x n m'' m')). Qed.
Lemma lem4744365 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744366 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1176 A f x n m') = (term1144 A f x n m').
Proof. exact (MK_COMB (@lem4744365) (@lem4744364 A f x n m')). Qed.
Lemma lem4744367 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term1154 A m n f x) = (term1154 A m n f x).
Proof. exact (eq_refl (term1154 A m n f x)). Qed.
Lemma lem4744368 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1172 A m f x n m') = (term1168 A m f x n m').
Proof. exact (MK_COMB (@lem4744367 A m n f x) (@lem4744366 A f x n m')). Qed.
Lemma lem4744369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4744370 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1177 A m f x n m') = (term1178 A m f x n m').
Proof. exact (MK_COMB (@lem4744369) (@lem4744368 A m f x n m')). Qed.
Lemma lem4744371 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) : (term1174 A f x n m' m'') = (term1141 A f x n m'' m').
Proof. exact (eq_refl (term1174 A f x n m' m'')). Qed.
Lemma lem4744372 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term1154 A m n f x) = (term1154 A m n f x).
Proof. exact (eq_refl (term1154 A m n f x)). Qed.
Lemma lem4744373 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) : (term1179 A m f x n m' m'') = (term1180 A m f x n m'' m').
Proof. exact (MK_COMB (@lem4744372 A m n f x) (@lem4744371 A f x n m'' m')). Qed.
Lemma lem4744374 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1181 A m f x n m') = (term1182 A m f x n m').
Proof. exact (fun_ext (fun m'' : nat => @lem4744373 A m f x n m'' m')). Qed.
Lemma lem4744375 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744376 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1173 A m f x n m') = (term1183 A m f x n m').
Proof. exact (MK_COMB (@lem4744375) (@lem4744374 A m f x n m')). Qed.
Lemma lem4744377 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) : ((term1172 A m f x n m') = (term1173 A m f x n m')) = ((term1168 A m f x n m') = (term1183 A m f x n m')).
Proof. exact (MK_COMB (@lem4744370 A m f x n m') (@lem4744376 A m f x n m')). Qed.
Lemma lem4744378 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) : (term1168 A m f x n m') = (term1183 A m f x n m').
Proof. exact (EQ_MP (@lem4744377 A m f x n m') (@lem4744362 A m f x n m')). Qed.
Lemma lem4744379 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1170 A m f x n) = (term1184 A m f x n).
Proof. exact (fun_ext (fun m' : nat => @lem4744378 A m f x n m')). Qed.
Lemma lem4744380 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744381 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1171 A m f x n) = (term1185 A m f x n).
Proof. exact (MK_COMB (@lem4744380) (@lem4744379 A m f x n)). Qed.
Lemma lem4744382 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) : (term1156 A m f x n) = (term1185 A m f x n).
Proof. exact (TRANS (@lem4744358 A m f x n) (@lem4744381 A m f x n)). Qed.
Lemma lem4744383 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1158 A f x n) = (term1186 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4744382 A m f x n)). Qed.
Lemma lem4744384 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4744385 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1159 A f x n) = (term1187 A f x n).
Proof. exact (MK_COMB (@lem4744384) (@lem4744383 A f x n)). Qed.
Lemma lem4744386 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1147 A f x n) = (term1187 A f x n).
Proof. exact (TRANS (@lem4744338 A f x n) (@lem4744385 A f x n)). Qed.
Lemma lem4744387 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1117 A f x n) = (term1187 A f x n).
Proof. exact (TRANS (@lem4744314 A f x n) (@lem4744386 A f x n)). Qed.
Lemma lem4744388 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1100 A f x n) = (term1187 A f x n).
Proof. exact (TRANS (@lem4744217 A f x n) (@lem4744387 A f x n)). Qed.
Lemma lem4744389 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1029 A f x n) = (term1187 A f x n).
Proof. exact (TRANS (@lem4743868 A f x n) (@lem4744388 A f x n)). Qed.
Lemma lem4744390 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term1029 A f x n) : term1187 A f x n.
Proof. exact (EQ_MP (@lem4744389 A f x n) (@lem4743674 A f x n h1)). Qed.
Lemma lem4744853 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term1185 A m f x n) : term1185 A m f x n.
Proof. exact (h1). Qed.
Lemma lem4744854 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) (h1 : term1183 A m f x n m') : term1183 A m f x n m'.
Proof. exact (h1). Qed.
Lemma lem4744855 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term1180 A m f x n m'' m'.
Proof. exact (h1). Qed.
Lemma lem4745062 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) : (term1080 A f x n m'' m') = (term1080 A f x n m'' m').
Proof. exact (eq_refl (term1080 A f x n m'' m')). Qed.
Lemma lem4745089 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term938 A f x m n) = (term938 A f x m n).
Proof. exact (eq_refl (term938 A f x m n)). Qed.
Lemma lem4745090 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1091 A f x n) = (term1091 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4745089 A f x m n)). Qed.
Lemma lem4745091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4745092 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1093 A f x n) = (term1093 A f x n).
Proof. exact (MK_COMB (@lem4745091) (@lem4745090 A f x n)). Qed.
Lemma lem4745093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4745094 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1095 A f x n) = (term1095 A f x n).
Proof. exact (MK_COMB (@lem4745093) (@lem4745092 A f x n)). Qed.
Lemma lem4745095 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) : (term1141 A f x n m'' m') = (term1141 A f x n m'' m').
Proof. exact (MK_COMB (@lem4745094 A f x n) (@lem4745062 A f x n m'' m')). Qed.
Lemma lem4745122 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term408 A n f x m' m) = (term408 A n f x m' m).
Proof. exact (eq_refl (term408 A n f x m' m)). Qed.
Lemma lem4745123 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term436 A n f x m) = (term436 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4745122 A n f x m' m)). Qed.
Lemma lem4745124 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4745125 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term444 A n f x m) = (term444 A n f x m).
Proof. exact (MK_COMB (@lem4745124) (@lem4745123 A n f x m)). Qed.
Lemma lem4745146 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term406 A n f m x) = (term406 A n f m x).
Proof. exact (eq_refl (term406 A n f m x)). Qed.
Lemma lem4745147 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term445 A n f x m) = (term445 A n f x m).
Proof. exact (MK_COMB (@lem4745146 A n f m x) (@lem4745125 A n f x m)). Qed.
Lemma lem4745148 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term446 A n f x) = (term446 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4745147 A n f x m)). Qed.
Lemma lem4745149 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4745150 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term447 A n f x) = (term447 A n f x).
Proof. exact (MK_COMB (@lem4745149) (@lem4745148 A n f x)). Qed.
Lemma lem4745167 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term461 A n f m x) = (term461 A n f m x).
Proof. exact (eq_refl (term461 A n f m x)). Qed.
Lemma lem4745168 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term463 A m n f x) = (term463 A m n f x).
Proof. exact (MK_COMB (@lem4745167 A n f m x) (@lem4745150 A n f x)). Qed.
Lemma lem4745169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4745170 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (x : A) : (term1154 A m n f x) = (term1154 A m n f x).
Proof. exact (MK_COMB (@lem4745169) (@lem4745168 A m n f x)). Qed.
Lemma lem4745171 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) : (term1180 A m f x n m'' m') = (term1180 A m f x n m'' m').
Proof. exact (MK_COMB (@lem4745170 A m n f x) (@lem4745095 A f x n m'' m')). Qed.
Lemma lem4745172 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term1180 A m f x n m'' m'.
Proof. exact (EQ_MP (@lem4745171 A m f x n m'' m') (@lem4744855 A m f x n m'' m' h1)). Qed.
Lemma lem4745173 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term1141 A f x n m'' m'.
Proof. exact (proj2 (@lem4745172 A m f x n m'' m' h1)). Qed.
Lemma lem4745174 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term463 A m n f x.
Proof. exact (proj1 (@lem4745172 A m f x n m'' m' h1)). Qed.
Lemma lem4745175 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term447 A n f x.
Proof. exact (proj2 (@lem4745174 A m f x n m'' m' h1)). Qed.
Lemma lem4745176 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term387 A n f m x.
Proof. exact (proj1 (@lem4745174 A m f x n m'' m' h1)). Qed.
Lemma lem4745181 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term1093 A f x n) : term1093 A f x n.
Proof. exact (h1). Qed.
Lemma lem4745182 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term1080 A f x n m'' m'.
Proof. exact (h1). Qed.
Lemma lem4745183 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term1078 A f x n m'' m'.
Proof. exact (proj2 (@lem4745182 A f x n m'' m' h1)). Qed.
Lemma lem4745184 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term1071 A f x m' n.
Proof. exact (proj1 (@lem4745182 A f x n m'' m' h1)). Qed.
Lemma lem4745186 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term1071 A f x m'' n.
Proof. exact (proj1 (@lem4745183 A f x n m'' m' h1)). Qed.
Lemma lem4745188 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term846 A n f m'' x.
Proof. exact (proj1 (@lem4745186 A f x n m'' m' h1)). Qed.
Lemma lem4745190 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term846 A n f m' x.
Proof. exact (proj1 (@lem4745184 A f x n m'' m' h1)). Qed.
Lemma lem4745368 {A : Type'} (f : nat -> A) (x : A) (m : nat) (n : nat) : (term938 A f x m n) = (term939 A f x m n).
Proof. exact (@lem19699 (Peano.lt m n) (term937 A f m x) (term312 m n)). Qed.
Lemma lem4745369 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1091 A f x n) = (term1188 A f x n).
Proof. exact (fun_ext (fun m : nat => @lem4745368 A f x m n)). Qed.
Lemma lem4745370 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4745372 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1093 A f x n) = (term1189 A f x n).
Proof. exact (MK_COMB (@lem4745370) (@lem4745369 A f x n)). Qed.
Lemma lem4745373 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term1093 A f x n) : term1189 A f x n.
Proof. exact (EQ_MP (@lem4745372 A f x n) (@lem4745181 A f x n h1)). Qed.
Lemma lem4745547 (m'' : nat) (n : nat) (h1 : term312 m'' n) : term312 m'' n.
Proof. exact (h1). Qed.
Lemma lem4745717 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4745895 (m'' : nat) (n : nat) (h1 : term312 m'' n) : term312 m'' n.
Proof. exact (h1). Qed.
Lemma lem4745933 {A : Type'} (P : Prop) (Q : A -> Prop) : (term431 A P Q) = (term430 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4745934 (P : Prop) (Q : nat -> Prop) : (term433 P Q) = (term432 P Q).
Proof. exact (@lem4745933 nat P Q). Qed.
Lemma lem4745935 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term435 A n f x m) = (term434 A n f x m).
Proof. exact (@lem4745934 (term400 A n f m x) (term436 A n f x m)). Qed.
Lemma lem4745936 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term437 A n f x m m') = (term408 A n f x m' m).
Proof. exact (eq_refl (term437 A n f x m m')). Qed.
Lemma lem4745937 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term442 A n f x m) = (term436 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4745936 A n f x m' m)). Qed.
Lemma lem4745938 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4745939 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term443 A n f x m) = (term444 A n f x m).
Proof. exact (MK_COMB (@lem4745938) (@lem4745937 A n f x m)). Qed.
Lemma lem4745940 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term406 A n f m x) = (term406 A n f m x).
Proof. exact (eq_refl (term406 A n f m x)). Qed.
Lemma lem4745941 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term435 A n f x m) = (term445 A n f x m).
Proof. exact (MK_COMB (@lem4745940 A n f m x) (@lem4745939 A n f x m)). Qed.
Lemma lem4745942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4745943 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term1190 A n f x m) = (term1191 A n f x m).
Proof. exact (MK_COMB (@lem4745942) (@lem4745941 A n f x m)). Qed.
Lemma lem4745944 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term437 A n f x m m') = (term408 A n f x m' m).
Proof. exact (eq_refl (term437 A n f x m m')). Qed.
Lemma lem4745945 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (x : A) : (term406 A n f m x) = (term406 A n f m x).
Proof. exact (eq_refl (term406 A n f m x)). Qed.
Lemma lem4745946 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term438 A n f x m m') = (term410 A n f x m' m).
Proof. exact (MK_COMB (@lem4745945 A n f m x) (@lem4745944 A n f x m' m)). Qed.
Lemma lem4745947 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term439 A n f x m) = (term412 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4745946 A n f x m' m)). Qed.
Lemma lem4745948 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4745949 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term434 A n f x m) = (term414 A n f x m).
Proof. exact (MK_COMB (@lem4745948) (@lem4745947 A n f x m)). Qed.
Lemma lem4745950 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : ((term435 A n f x m) = (term434 A n f x m)) = ((term445 A n f x m) = (term414 A n f x m)).
Proof. exact (MK_COMB (@lem4745943 A n f x m) (@lem4745949 A n f x m)). Qed.
Lemma lem4745951 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term445 A n f x m) = (term414 A n f x m).
Proof. exact (EQ_MP (@lem4745950 A n f x m) (@lem4745935 A n f x m)). Qed.
Lemma lem4745952 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term446 A n f x) = (term416 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4745951 A n f x m)). Qed.
Lemma lem4745953 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4745954 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term447 A n f x) = (term418 A n f x).
Proof. exact (MK_COMB (@lem4745953) (@lem4745952 A n f x)). Qed.
Lemma lem4745979 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m' : nat) (m : nat) : (term410 A n f x m' m) = (term410 A n f x m' m).
Proof. exact (eq_refl (term410 A n f x m' m)). Qed.
Lemma lem4745980 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term412 A n f x m) = (term412 A n f x m).
Proof. exact (fun_ext (fun m' : nat => @lem4745979 A n f x m' m)). Qed.
Lemma lem4745981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4745982 {A : Type'} (n : nat) (f : nat -> A) (x : A) (m : nat) : (term414 A n f x m) = (term414 A n f x m).
Proof. exact (MK_COMB (@lem4745981) (@lem4745980 A n f x m)). Qed.
Lemma lem4745983 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term416 A n f x) = (term416 A n f x).
Proof. exact (fun_ext (fun m : nat => @lem4745982 A n f x m)). Qed.
Lemma lem4745984 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4745985 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term418 A n f x) = (term418 A n f x).
Proof. exact (MK_COMB (@lem4745984) (@lem4745983 A n f x)). Qed.
Lemma lem4745986 {A : Type'} (n : nat) (f : nat -> A) (x : A) : (term447 A n f x) = (term418 A n f x).
Proof. exact (TRANS (@lem4745954 A n f x) (@lem4745985 A n f x)). Qed.
Lemma lem4745987 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term418 A n f x.
Proof. exact (EQ_MP (@lem4745986 A n f x) (@lem4745175 A m f x n m'' m' h1)). Qed.
Lemma lem4746065 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4746069 {A : Type'} (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m'') = x) : (f m'') = x.
Proof. exact (h1). Qed.
Lemma lem4746100 {A : Type'} (_57876 : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term1093 A f x n) : term1192 A f x n _57876.
Proof. exact (@lem4745373 A f x n h1 _57876). Qed.
Lemma lem4746101 {A : Type'} (f : nat -> A) (x : A) (_57876 : nat) (n : nat) : (term1192 A f x n _57876) = (term939 A f x _57876 n).
Proof. exact (eq_refl (term1192 A f x n _57876)). Qed.
Lemma lem4746102 {A : Type'} (_57876 : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term1093 A f x n) : term939 A f x _57876 n.
Proof. exact (EQ_MP (@lem4746101 A f x _57876 n) (@lem4746100 A _57876 f x n h1)). Qed.
Lemma lem4746199 {A : Type'} (_57909 : nat) (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term1193 A n f x _57909.
Proof. exact (@lem4745987 A m f x n m'' m' h1 _57909). Qed.
Lemma lem4746200 {A : Type'} (n : nat) (f : nat -> A) (x : A) (_57909 : nat) : (term1193 A n f x _57909) = (term414 A n f x _57909).
Proof. exact (eq_refl (term1193 A n f x _57909)). Qed.
Lemma lem4746201 {A : Type'} (_57909 : nat) (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term414 A n f x _57909.
Proof. exact (EQ_MP (@lem4746200 A n f x _57909) (@lem4746199 A _57909 m f x n m'' m' h1)). Qed.
Lemma lem4746202 {A : Type'} (_57909 : nat) (_57910 : nat) (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term1194 A n f x _57909 _57910.
Proof. exact (@lem4746201 A _57909 m f x n m'' m' h1 _57910). Qed.
Lemma lem4746203 {A : Type'} (n : nat) (f : nat -> A) (x : A) (_57910 : nat) (_57909 : nat) : (term1194 A n f x _57909 _57910) = (term410 A n f x _57910 _57909).
Proof. exact (eq_refl (term1194 A n f x _57909 _57910)). Qed.
Lemma lem4746204 {A : Type'} (_57910 : nat) (_57909 : nat) (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term410 A n f x _57910 _57909.
Proof. exact (EQ_MP (@lem4746203 A n f x _57910 _57909) (@lem4746202 A _57909 _57910 m f x n m'' m' h1)). Qed.
Lemma lem4746276 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : (f m) = x.
Proof. exact (proj2 (@lem4745176 A m f x n m'' m' h1)). Qed.
Lemma lem4746298 {A : Type'} (_57876 : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term1093 A f x n) : term1195 A f x _57876 n.
Proof. exact (proj2 (@lem4746102 A _57876 f x n h1)). Qed.
Lemma lem4746372 (m'' : nat) (n : nat) (h1 : term312 m'' n) : term312 m'' n.
Proof. exact (h1). Qed.
Lemma lem4746444 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4746520 (m'' : nat) (n : nat) (h1 : term312 m'' n) : term312 m'' n.
Proof. exact (h1). Qed.
Lemma lem4746559 {A : Type'} (n : nat) (f : nat -> A) (x : A) (_57910 : nat) (_57909 : nat) : (term408 A n f x _57910 _57909) = (term1196 A n f x _57910 _57909).
Proof. exact (@lem4713733 (term312 _57910 n) (term937 A f _57910 x) (_57910 = _57909)). Qed.
Lemma lem4746560 {A : Type'} (n : nat) (f : nat -> A) (_57909 : nat) (x : A) : (term406 A n f _57909 x) = (term406 A n f _57909 x).
Proof. exact (eq_refl (term406 A n f _57909 x)). Qed.
Lemma lem4746561 {A : Type'} (n : nat) (f : nat -> A) (x : A) (_57910 : nat) (_57909 : nat) : (term410 A n f x _57910 _57909) = (term1197 A n f x _57910 _57909).
Proof. exact (MK_COMB (@lem4746560 A n f _57909 x) (@lem4746559 A n f x _57910 _57909)). Qed.
Lemma lem4746568 {A : Type'} (n : nat) (f : nat -> A) (x : A) (_57910 : nat) (_57909 : nat) : (term1197 A n f x _57910 _57909) = (term1198 A n f x _57910 _57909).
Proof. exact (@lem4713733 (term312 _57909 n) (term937 A f _57909 x) (term1196 A n f x _57910 _57909)). Qed.
Lemma lem4746569 {A : Type'} (n : nat) (f : nat -> A) (x : A) (_57910 : nat) (_57909 : nat) : (term410 A n f x _57910 _57909) = (term1198 A n f x _57910 _57909).
Proof. exact (TRANS (@lem4746561 A n f x _57910 _57909) (@lem4746568 A n f x _57910 _57909)). Qed.
Lemma lem4746570 {A : Type'} (_57910 : nat) (_57909 : nat) (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term1198 A n f x _57910 _57909.
Proof. exact (EQ_MP (@lem4746569 A n f x _57910 _57909) (@lem4746204 A _57910 _57909 m f x n m'' m' h1)). Qed.
Lemma lem4746592 {A : Type'} (f : nat -> A) (m' : nat) (x : A) (h1 : (f m') = x) : (f m') = x.
Proof. exact (h1). Qed.
Lemma lem4746594 {A : Type'} (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m'') = x) : (f m'') = x.
Proof. exact (h1). Qed.
Lemma lem4746607 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : x = (f m).
Proof. exact (SYM (@lem4746276 A m f x n m'' m' h1)). Qed.
Lemma lem4746759 {A : Type'} (f : nat -> A) (_57876 : nat) (n : nat) : (term1199 A f _57876 n) = (term1199 A f _57876 n).
Proof. exact (eq_refl (term1199 A f _57876 n)). Qed.
Lemma lem4746760 {A : Type'} (_57876 : nat) (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : (term1200 A f _57876 n x) = (term1201 A _57876 n f m).
Proof. exact (MK_COMB (@lem4746759 A f _57876 n) (@lem4746607 A m f x n m'' m' h1)). Qed.
Lemma lem4746761 {A : Type'} (f : nat -> A) (m : nat) (_57876 : nat) (n : nat) : (term1201 A _57876 n f m) = (term1202 A f m _57876 n).
Proof. exact (eq_refl (term1201 A _57876 n f m)). Qed.
Lemma lem4746762 {A : Type'} (f : nat -> A) (_57876 : nat) (n : nat) (x : A) : (term1203 A f _57876 n x) = (term1203 A f _57876 n x).
Proof. exact (eq_refl (term1203 A f _57876 n x)). Qed.
Lemma lem4746763 {A : Type'} (x : A) (f : nat -> A) (m : nat) (_57876 : nat) (n : nat) : ((term1200 A f _57876 n x) = (term1201 A _57876 n f m)) = ((term1200 A f _57876 n x) = (term1202 A f m _57876 n)).
Proof. exact (MK_COMB (@lem4746762 A f _57876 n x) (@lem4746761 A f m _57876 n)). Qed.
Lemma lem4746764 {A : Type'} (f : nat -> A) (x : A) (_57876 : nat) (n : nat) : (term1200 A f _57876 n x) = (term1195 A f x _57876 n).
Proof. exact (eq_refl (term1200 A f _57876 n x)). Qed.
Lemma lem4746765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4746766 {A : Type'} (f : nat -> A) (x : A) (_57876 : nat) (n : nat) : (term1203 A f _57876 n x) = (term1204 A f x _57876 n).
Proof. exact (MK_COMB (@lem4746765) (@lem4746764 A f x _57876 n)). Qed.
Lemma lem4746767 {A : Type'} (f : nat -> A) (m : nat) (_57876 : nat) (n : nat) : (term1202 A f m _57876 n) = (term1202 A f m _57876 n).
Proof. exact (eq_refl (term1202 A f m _57876 n)). Qed.
Lemma lem4746768 {A : Type'} (x : A) (f : nat -> A) (m : nat) (_57876 : nat) (n : nat) : ((term1200 A f _57876 n x) = (term1202 A f m _57876 n)) = ((term1195 A f x _57876 n) = (term1202 A f m _57876 n)).
Proof. exact (MK_COMB (@lem4746766 A f x _57876 n) (@lem4746767 A f m _57876 n)). Qed.
Lemma lem4746769 {A : Type'} (x : A) (f : nat -> A) (m : nat) (_57876 : nat) (n : nat) : ((term1200 A f _57876 n x) = (term1201 A _57876 n f m)) = ((term1195 A f x _57876 n) = (term1202 A f m _57876 n)).
Proof. exact (TRANS (@lem4746763 A x f m _57876 n) (@lem4746768 A x f m _57876 n)). Qed.
Lemma lem4746770 {A : Type'} (_57876 : nat) (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : (term1195 A f x _57876 n) = (term1202 A f m _57876 n).
Proof. exact (EQ_MP (@lem4746769 A x f m _57876 n) (@lem4746760 A _57876 m f x n m'' m' h1)). Qed.
Lemma lem4746771 {A : Type'} (_57876 : nat) (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1093 A f x n) (h2 : term1180 A m f x n m'' m') : term1202 A f m _57876 n.
Proof. exact (EQ_MP (@lem4746770 A _57876 m f x n m'' m' h2) (@lem4746298 A _57876 f x n h1)). Qed.
Lemma lem4747007 (m'' : nat) (n : nat) (h1 : term312 m'' n) : term312 m'' n.
Proof. exact (h1). Qed.
Lemma lem4747242 (m' : nat) (n : nat) (h1 : term312 m' n) : term312 m' n.
Proof. exact (h1). Qed.
Lemma lem4747477 (m'' : nat) (n : nat) (h1 : term312 m'' n) : term312 m'' n.
Proof. exact (h1). Qed.
Lemma lem4747506 {A : Type'} (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m'') = x) : x = (f m'').
Proof. exact (SYM (@lem4746594 A f m'' x h1)). Qed.
Lemma lem4747603 {A : Type'} (n : nat) (f : nat -> A) (_57910 : nat) (_57909 : nat) : (term1205 A n f _57910 _57909) = (term1205 A n f _57910 _57909).
Proof. exact (eq_refl (term1205 A n f _57910 _57909)). Qed.
Lemma lem4747604 {A : Type'} (n : nat) (_57910 : nat) (_57909 : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m'') = x) : (term1206 A n f _57910 _57909 x) = (term1207 A n _57910 _57909 f m'').
Proof. exact (MK_COMB (@lem4747603 A n f _57910 _57909) (@lem4747506 A f m'' x h1)). Qed.
Lemma lem4747605 {A : Type'} (n : nat) (f : nat -> A) (m'' : nat) (_57910 : nat) (_57909 : nat) : (term1207 A n _57910 _57909 f m'') = (term1208 A n f m'' _57910 _57909).
Proof. exact (eq_refl (term1207 A n _57910 _57909 f m'')). Qed.
Lemma lem4747606 {A : Type'} (n : nat) (f : nat -> A) (_57910 : nat) (_57909 : nat) (x : A) : (term1209 A n f _57910 _57909 x) = (term1209 A n f _57910 _57909 x).
Proof. exact (eq_refl (term1209 A n f _57910 _57909 x)). Qed.
Lemma lem4747607 {A : Type'} (x : A) (n : nat) (f : nat -> A) (m'' : nat) (_57910 : nat) (_57909 : nat) : ((term1206 A n f _57910 _57909 x) = (term1207 A n _57910 _57909 f m'')) = ((term1206 A n f _57910 _57909 x) = (term1208 A n f m'' _57910 _57909)).
Proof. exact (MK_COMB (@lem4747606 A n f _57910 _57909 x) (@lem4747605 A n f m'' _57910 _57909)). Qed.
Lemma lem4747608 {A : Type'} (n : nat) (f : nat -> A) (x : A) (_57910 : nat) (_57909 : nat) : (term1206 A n f _57910 _57909 x) = (term1198 A n f x _57910 _57909).
Proof. exact (eq_refl (term1206 A n f _57910 _57909 x)). Qed.
Lemma lem4747609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4747610 {A : Type'} (n : nat) (f : nat -> A) (x : A) (_57910 : nat) (_57909 : nat) : (term1209 A n f _57910 _57909 x) = (term1210 A n f x _57910 _57909).
Proof. exact (MK_COMB (@lem4747609) (@lem4747608 A n f x _57910 _57909)). Qed.
Lemma lem4747611 {A : Type'} (n : nat) (f : nat -> A) (m'' : nat) (_57910 : nat) (_57909 : nat) : (term1208 A n f m'' _57910 _57909) = (term1208 A n f m'' _57910 _57909).
Proof. exact (eq_refl (term1208 A n f m'' _57910 _57909)). Qed.
Lemma lem4747612 {A : Type'} (x : A) (n : nat) (f : nat -> A) (m'' : nat) (_57910 : nat) (_57909 : nat) : ((term1206 A n f _57910 _57909 x) = (term1208 A n f m'' _57910 _57909)) = ((term1198 A n f x _57910 _57909) = (term1208 A n f m'' _57910 _57909)).
Proof. exact (MK_COMB (@lem4747610 A n f x _57910 _57909) (@lem4747611 A n f m'' _57910 _57909)). Qed.
Lemma lem4747613 {A : Type'} (x : A) (n : nat) (f : nat -> A) (m'' : nat) (_57910 : nat) (_57909 : nat) : ((term1206 A n f _57910 _57909 x) = (term1207 A n _57910 _57909 f m'')) = ((term1198 A n f x _57910 _57909) = (term1208 A n f m'' _57910 _57909)).
Proof. exact (TRANS (@lem4747607 A x n f m'' _57910 _57909) (@lem4747612 A x n f m'' _57910 _57909)). Qed.
Lemma lem4747614 {A : Type'} (n : nat) (_57910 : nat) (_57909 : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m'') = x) : (term1198 A n f x _57910 _57909) = (term1208 A n f m'' _57910 _57909).
Proof. exact (EQ_MP (@lem4747613 A x n f m'' _57910 _57909) (@lem4747604 A n _57910 _57909 f m'' x h1)). Qed.
Lemma lem4747615 {A : Type'} (_57910 : nat) (_57909 : nat) (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : (f m'') = x) : term1208 A n f m'' _57910 _57909.
Proof. exact (EQ_MP (@lem4747614 A n _57910 _57909 f m'' x h2) (@lem4746570 A _57910 _57909 m f x n m'' m' h1)). Qed.
Lemma lem4747670 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term860 m'' m'.
Proof. exact (proj2 (@lem4745183 A f x n m'' m' h1)). Qed.
Lemma lem4747699 {A : Type'} (f : nat -> A) (m' : nat) : (term953 A f m') = (term953 A f m').
Proof. exact (eq_refl (term953 A f m')). Qed.
Lemma lem4747700 {A : Type'} (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m'') = x) : (term954 A f m' x) = (term955 A m' f m'').
Proof. exact (MK_COMB (@lem4747699 A f m') (@lem4747506 A f m'' x h1)). Qed.
Lemma lem4747701 {A : Type'} (m' : nat) (f : nat -> A) (m'' : nat) : (term955 A m' f m'') = ((f m') = (f m'')).
Proof. exact (eq_refl (term955 A m' f m'')). Qed.
Lemma lem4747702 {A : Type'} (f : nat -> A) (m' : nat) (x : A) : (term956 A f m' x) = (term956 A f m' x).
Proof. exact (eq_refl (term956 A f m' x)). Qed.
Lemma lem4747703 {A : Type'} (x : A) (m' : nat) (f : nat -> A) (m'' : nat) : ((term954 A f m' x) = (term955 A m' f m'')) = ((term954 A f m' x) = ((f m') = (f m''))).
Proof. exact (MK_COMB (@lem4747702 A f m' x) (@lem4747701 A m' f m'')). Qed.
Lemma lem4747704 {A : Type'} (f : nat -> A) (m' : nat) (x : A) : (term954 A f m' x) = ((f m') = x).
Proof. exact (eq_refl (term954 A f m' x)). Qed.
Lemma lem4747705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4747706 {A : Type'} (f : nat -> A) (m' : nat) (x : A) : (term956 A f m' x) = (term957 A f m' x).
Proof. exact (MK_COMB (@lem4747705) (@lem4747704 A f m' x)). Qed.
Lemma lem4747707 {A : Type'} (m' : nat) (f : nat -> A) (m'' : nat) : ((f m') = (f m'')) = ((f m') = (f m'')).
Proof. exact (eq_refl ((f m') = (f m''))). Qed.
Lemma lem4747708 {A : Type'} (x : A) (m' : nat) (f : nat -> A) (m'' : nat) : ((term954 A f m' x) = ((f m') = (f m''))) = (((f m') = x) = ((f m') = (f m''))).
Proof. exact (MK_COMB (@lem4747706 A f m' x) (@lem4747707 A m' f m'')). Qed.
Lemma lem4747709 {A : Type'} (x : A) (m' : nat) (f : nat -> A) (m'' : nat) : ((term954 A f m' x) = (term955 A m' f m'')) = (((f m') = x) = ((f m') = (f m''))).
Proof. exact (TRANS (@lem4747703 A x m' f m'') (@lem4747708 A x m' f m'')). Qed.
Lemma lem4747710 {A : Type'} (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m'') = x) : ((f m') = x) = ((f m') = (f m'')).
Proof. exact (EQ_MP (@lem4747709 A x m' f m'') (@lem4747700 A m' f m'' x h1)). Qed.
Lemma lem4747827 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4747828 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4747827 A x). Qed.
Lemma lem4747829 {A : Type'} (f : nat -> A) (m : nat) : (f m) = (f m).
Proof. exact (@lem4747828 A (f m)). Qed.
Lemma lem4747830 {A : Type'} (f : nat -> A) (m : nat) : term1013 A f m.
Proof. exact (fun h0 : term1014 A f m => @lem4747829 A f m). Qed.
Lemma lem4747832 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4747833 {A : Type'} (f : nat -> A) (m : nat) : (term1013 A f m) = ((f m) = (f m)).
Proof. exact (@lem4747832 ((f m) = (f m))). Qed.
Lemma lem4747834 {A : Type'} (f : nat -> A) (m : nat) : (f m) = (f m).
Proof. exact (EQ_MP (@lem4747833 A f m) (@lem4747830 A f m)). Qed.
Lemma lem4747836 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : Peano.lt m n.
Proof. exact (proj1 (@lem4745176 A m f x n m'' m' h1)). Qed.
Lemma lem4747837 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term611 m n.
Proof. exact (fun h0 : term312 m n => @lem4747836 A m f x n m'' m' h1). Qed.
Lemma lem4747839 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4747840 (m : nat) (n : nat) : (term611 m n) = (Peano.lt m n).
Proof. exact (@lem4747839 (Peano.lt m n)). Qed.
Lemma lem4747841 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : Peano.lt m n.
Proof. exact (EQ_MP (@lem4747840 m n) (@lem4747837 A m f x n m'' m' h1)). Qed.
Lemma lem4747843 (a : Prop) (b : Prop) : (term1002 a b) = (term1003 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4747844 {A : Type'} (f : nat -> A) (m : nat) (_57876 : nat) (n : nat) : (term1202 A f m _57876 n) = (term1211 A f m _57876 n).
Proof. exact (@lem4747843 ((f _57876) = (f m)) (Peano.lt _57876 n)). Qed.
Lemma lem4747846 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4747847 {A : Type'} (f : nat -> A) (m : nat) (_57876 : nat) (n : nat) : (term1211 A f m _57876 n) = (term1212 A f m _57876 n).
Proof. exact (@lem4747846 (term1213 A f m _57876 n)). Qed.
Lemma lem4747848 {A : Type'} (f : nat -> A) (m : nat) (_57876 : nat) (n : nat) : (term1202 A f m _57876 n) = (term1212 A f m _57876 n).
Proof. exact (TRANS (@lem4747844 A f m _57876 n) (@lem4747847 A f m _57876 n)). Qed.
Lemma lem4747850 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : term1214 A f m n.
Proof. exact (conj (@lem4747834 A f m) (@lem4747841 A m f x n m'' m' h1)). Qed.
Lemma lem4747852 {A : Type'} (_57876 : nat) (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1093 A f x n) (h2 : term1180 A m f x n m'' m') : term1212 A f m _57876 n.
Proof. exact (EQ_MP (@lem4747848 A f m _57876 n) (@lem4746771 A _57876 m f x n m'' m' h1 h2)). Qed.
Lemma lem4747853 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1093 A f x n) (h2 : term1180 A m f x n m'' m') : term1215 A f m n.
Proof. exact (@lem4747852 A m m f x n m'' m' h1 h2). Qed.
Lemma lem4747856 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1093 A f x n) (h2 : term1180 A m f x n m'' m') : False.
Proof. exact (@lem4747853 A m f x n m'' m' h1 h2 (@lem4747850 A m f x n m'' m' h2)). Qed.
Lemma lem4747857 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1093 A f x n) (h2 : term1180 A m f x n m'' m') : term632.
Proof. exact (fun h0 : ~ False => @lem4747856 A m f x n m'' m' h1 h2). Qed.
Lemma lem4747859 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4747860 : term632 = False.
Proof. exact (@lem4747859 False). Qed.
Lemma lem4747949 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m'' n.
Proof. exact (proj2 (@lem4745186 A f x n m'' m' h1)). Qed.
Lemma lem4747950 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term611 m'' n.
Proof. exact (fun h0 : term312 m'' n => @lem4747949 A f x n m'' m' h1). Qed.
Lemma lem4747952 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4747953 (m'' : nat) (n : nat) : (term611 m'' n) = (Peano.lt m'' n).
Proof. exact (@lem4747952 (Peano.lt m'' n)). Qed.
Lemma lem4747954 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m'' n.
Proof. exact (EQ_MP (@lem4747953 m'' n) (@lem4747950 A f x n m'' m' h1)). Qed.
Lemma lem4747957 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4747959 (m'' : nat) (n : nat) : (term312 m'' n) = (term991 m'' n).
Proof. exact (@lem4747957 (Peano.lt m'' n)). Qed.
Lemma lem4747962 (m'' : nat) (n : nat) (h1 : term312 m'' n) : term991 m'' n.
Proof. exact (EQ_MP (@lem4747959 m'' n) (@lem4747007 m'' n h1)). Qed.
Lemma lem4747965 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (@lem4747962 m'' n h1 (@lem4747954 A f x n m'' m' h2)). Qed.
Lemma lem4747966 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : term632.
Proof. exact (fun h0 : ~ False => @lem4747965 A f x n m'' m' h1 h2). Qed.
Lemma lem4747968 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4747969 : term632 = False.
Proof. exact (@lem4747968 False). Qed.
Lemma lem4747970 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4747969) (@lem4747966 A f x n m'' m' h1 h2)). Qed.
Lemma lem4748058 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m' n.
Proof. exact (proj2 (@lem4745184 A f x n m'' m' h1)). Qed.
Lemma lem4748059 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term611 m' n.
Proof. exact (fun h0 : term312 m' n => @lem4748058 A f x n m'' m' h1). Qed.
Lemma lem4748061 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748062 (m' : nat) (n : nat) : (term611 m' n) = (Peano.lt m' n).
Proof. exact (@lem4748061 (Peano.lt m' n)). Qed.
Lemma lem4748063 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m' n.
Proof. exact (EQ_MP (@lem4748062 m' n) (@lem4748059 A f x n m'' m' h1)). Qed.
Lemma lem4748066 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4748068 (m' : nat) (n : nat) : (term312 m' n) = (term991 m' n).
Proof. exact (@lem4748066 (Peano.lt m' n)). Qed.
Lemma lem4748071 (m' : nat) (n : nat) (h1 : term312 m' n) : term991 m' n.
Proof. exact (EQ_MP (@lem4748068 m' n) (@lem4747242 m' n h1)). Qed.
Lemma lem4748074 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (@lem4748071 m' n h1 (@lem4748063 A f x n m'' m' h2)). Qed.
Lemma lem4748075 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : term632.
Proof. exact (fun h0 : ~ False => @lem4748074 A f x n m'' m' h1 h2). Qed.
Lemma lem4748077 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748078 : term632 = False.
Proof. exact (@lem4748077 False). Qed.
Lemma lem4748079 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748078) (@lem4748075 A f x n m'' m' h1 h2)). Qed.
Lemma lem4748167 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m'' n.
Proof. exact (proj2 (@lem4745186 A f x n m'' m' h1)). Qed.
Lemma lem4748168 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term611 m'' n.
Proof. exact (fun h0 : term312 m'' n => @lem4748167 A f x n m'' m' h1). Qed.
Lemma lem4748170 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748171 (m'' : nat) (n : nat) : (term611 m'' n) = (Peano.lt m'' n).
Proof. exact (@lem4748170 (Peano.lt m'' n)). Qed.
Lemma lem4748172 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m'' n.
Proof. exact (EQ_MP (@lem4748171 m'' n) (@lem4748168 A f x n m'' m' h1)). Qed.
Lemma lem4748175 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4748177 (m'' : nat) (n : nat) : (term312 m'' n) = (term991 m'' n).
Proof. exact (@lem4748175 (Peano.lt m'' n)). Qed.
Lemma lem4748180 (m'' : nat) (n : nat) (h1 : term312 m'' n) : term991 m'' n.
Proof. exact (EQ_MP (@lem4748177 m'' n) (@lem4747477 m'' n h1)). Qed.
Lemma lem4748183 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (@lem4748180 m'' n h1 (@lem4748172 A f x n m'' m' h2)). Qed.
Lemma lem4748184 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : term632.
Proof. exact (fun h0 : ~ False => @lem4748183 A f x n m'' m' h1 h2). Qed.
Lemma lem4748186 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748187 : term632 = False.
Proof. exact (@lem4748186 False). Qed.
Lemma lem4748188 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748187) (@lem4748184 A f x n m'' m' h1 h2)). Qed.
Lemma lem4748276 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m' n.
Proof. exact (proj2 (@lem4745184 A f x n m'' m' h1)). Qed.
Lemma lem4748277 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term611 m' n.
Proof. exact (fun h0 : term312 m' n => @lem4748276 A f x n m'' m' h1). Qed.
Lemma lem4748279 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748280 (m' : nat) (n : nat) : (term611 m' n) = (Peano.lt m' n).
Proof. exact (@lem4748279 (Peano.lt m' n)). Qed.
Lemma lem4748281 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m' n.
Proof. exact (EQ_MP (@lem4748280 m' n) (@lem4748277 A f x n m'' m' h1)). Qed.
Lemma lem4748283 {A : Type'} (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m') = x) (h2 : (f m'') = x) : (f m') = (f m'').
Proof. exact (EQ_MP (@lem4747710 A m' f m'' x h2) (@lem4746592 A f m' x h1)). Qed.
Lemma lem4748284 {A : Type'} (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m') = x) (h2 : (f m'') = x) : term1000 A m' f m''.
Proof. exact (fun h0 : term1001 A m' f m'' => @lem4748283 A m' f m'' x h1 h2). Qed.
Lemma lem4748286 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748287 {A : Type'} (m' : nat) (f : nat -> A) (m'' : nat) : (term1000 A m' f m'') = ((f m') = (f m'')).
Proof. exact (@lem4748286 ((f m') = (f m''))). Qed.
Lemma lem4748288 {A : Type'} (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : (f m') = x) (h2 : (f m'') = x) : (f m') = (f m'').
Proof. exact (EQ_MP (@lem4748287 A m' f m'') (@lem4748284 A m' f m'' x h1 h2)). Qed.
Lemma lem4748290 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m'' n.
Proof. exact (proj2 (@lem4745186 A f x n m'' m' h1)). Qed.
Lemma lem4748291 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term611 m'' n.
Proof. exact (fun h0 : term312 m'' n => @lem4748290 A f x n m'' m' h1). Qed.
Lemma lem4748293 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748294 (m'' : nat) (n : nat) : (term611 m'' n) = (Peano.lt m'' n).
Proof. exact (@lem4748293 (Peano.lt m'' n)). Qed.
Lemma lem4748295 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : Peano.lt m'' n.
Proof. exact (EQ_MP (@lem4748294 m'' n) (@lem4748291 A f x n m'' m' h1)). Qed.
Lemma lem4748297 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4748298 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4748297 A x). Qed.
Lemma lem4748299 {A : Type'} (f : nat -> A) (m'' : nat) : (f m'') = (f m'').
Proof. exact (@lem4748298 A (f m'')). Qed.
Lemma lem4748300 {A : Type'} (f : nat -> A) (m'' : nat) : term1013 A f m''.
Proof. exact (fun h0 : term1014 A f m'' => @lem4748299 A f m''). Qed.
Lemma lem4748302 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748303 {A : Type'} (f : nat -> A) (m'' : nat) : (term1013 A f m'') = ((f m'') = (f m'')).
Proof. exact (@lem4748302 ((f m'') = (f m''))). Qed.
Lemma lem4748304 {A : Type'} (f : nat -> A) (m'' : nat) : (f m'') = (f m'').
Proof. exact (EQ_MP (@lem4748303 A f m'') (@lem4748300 A f m'')). Qed.
Lemma lem4748320 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4748321 {A : Type'} (n : nat) (f : nat -> A) (m'' : nat) (_57910 : nat) (_57909 : nat) : (term1216 A n f m'' _57910 _57909) = (term1217 A n f m'' _57910 _57909).
Proof. exact (@lem4748320 (term312 _57910 n) (term1001 A _57909 f m'') (term1218 A f m'' _57910 _57909)). Qed.
Lemma lem4748347 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4748348 {A : Type'} (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1218 A f m'' _57910 _57909) = (term1219 A _57909 _57910 f m'').
Proof. exact (@lem4748347 (_57910 = _57909) (term1001 A _57910 f m'')). Qed.
Lemma lem4748358 {A : Type'} (_57909 : nat) (f : nat -> A) (m'' : nat) : (term1220 A _57909 f m'') = (term1220 A _57909 f m'').
Proof. exact (eq_refl (term1220 A _57909 f m'')). Qed.
Lemma lem4748359 {A : Type'} (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1221 A f m'' _57910 _57909) = (term1222 A _57909 _57910 f m'').
Proof. exact (MK_COMB (@lem4748358 A _57909 f m'') (@lem4748348 A _57909 _57910 f m'')). Qed.
Lemma lem4748363 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4748364 {A : Type'} (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1222 A _57909 _57910 f m'') = (term1223 A _57909 _57910 f m'').
Proof. exact (@lem4748363 (_57910 = _57909) (term1001 A _57909 f m'') (term1001 A _57910 f m'')). Qed.
Lemma lem4748386 {A : Type'} (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1221 A f m'' _57910 _57909) = (term1223 A _57909 _57910 f m'').
Proof. exact (TRANS (@lem4748359 A _57909 _57910 f m'') (@lem4748364 A _57909 _57910 f m'')). Qed.
Lemma lem4748387 (_57910 : nat) (n : nat) : (term1224 _57910 n) = (term1224 _57910 n).
Proof. exact (eq_refl (term1224 _57910 n)). Qed.
Lemma lem4748388 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1217 A n f m'' _57910 _57909) = (term1225 A n _57909 _57910 f m'').
Proof. exact (MK_COMB (@lem4748387 _57910 n) (@lem4748386 A _57909 _57910 f m'')). Qed.
Lemma lem4748392 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4748393 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1225 A n _57909 _57910 f m'') = (term1226 A n _57909 _57910 f m'').
Proof. exact (@lem4748392 (_57910 = _57909) (term312 _57910 n) (term1227 A _57909 _57910 f m'')). Qed.
Lemma lem4748425 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1217 A n f m'' _57910 _57909) = (term1226 A n _57909 _57910 f m'').
Proof. exact (TRANS (@lem4748388 A n _57909 _57910 f m'') (@lem4748393 A n _57909 _57910 f m'')). Qed.
Lemma lem4748426 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1216 A n f m'' _57910 _57909) = (term1226 A n _57909 _57910 f m'').
Proof. exact (TRANS (@lem4748321 A n f m'' _57910 _57909) (@lem4748425 A n _57909 _57910 f m'')). Qed.
Lemma lem4748427 (_57909 : nat) (n : nat) : (term1224 _57909 n) = (term1224 _57909 n).
Proof. exact (eq_refl (term1224 _57909 n)). Qed.
Lemma lem4748428 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1208 A n f m'' _57910 _57909) = (term1228 A n _57909 _57910 f m'').
Proof. exact (MK_COMB (@lem4748427 _57909 n) (@lem4748426 A n _57909 _57910 f m'')). Qed.
Lemma lem4748432 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4748433 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1228 A n _57909 _57910 f m'') = (term1229 A n _57909 _57910 f m'').
Proof. exact (@lem4748432 (_57910 = _57909) (term312 _57909 n) (term1230 A n _57909 _57910 f m'')). Qed.
Lemma lem4748475 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1208 A n f m'' _57910 _57909) = (term1229 A n _57909 _57910 f m'').
Proof. exact (TRANS (@lem4748428 A n _57909 _57910 f m'') (@lem4748433 A n _57909 _57910 f m'')). Qed.
Lemma lem4748476 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4748477 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1231 A n f m'' _57910 _57909) = (term1232 A n _57909 _57910 f m'').
Proof. exact (MK_COMB (@lem4748476) (@lem4748475 A n _57909 _57910 f m'')). Qed.
Lemma lem4748503 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4748504 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1233 A _57909 n _57910 f m'') = (term1230 A n _57909 _57910 f m'').
Proof. exact (@lem4748503 (term312 _57910 n) (term1001 A _57909 f m'') (term1001 A _57910 f m'')). Qed.
Lemma lem4748524 (_57909 : nat) (n : nat) : (term1224 _57909 n) = (term1224 _57909 n).
Proof. exact (eq_refl (term1224 _57909 n)). Qed.
Lemma lem4748525 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1234 A _57909 n _57910 f m'') = (term1235 A n _57909 _57910 f m'').
Proof. exact (MK_COMB (@lem4748524 _57909 n) (@lem4748504 A n _57909 _57910 f m'')). Qed.
Lemma lem4748536 (_57910 : nat) (_57909 : nat) : (term754 _57910 _57909) = (term754 _57910 _57909).
Proof. exact (eq_refl (term754 _57910 _57909)). Qed.
Lemma lem4748537 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1236 A _57909 n _57910 f m'') = (term1229 A n _57909 _57910 f m'').
Proof. exact (MK_COMB (@lem4748536 _57910 _57909) (@lem4748525 A n _57909 _57910 f m'')). Qed.
Lemma lem4748548 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : ((term1208 A n f m'' _57910 _57909) = (term1236 A _57909 n _57910 f m'')) = ((term1229 A n _57909 _57910 f m'') = (term1229 A n _57909 _57910 f m'')).
Proof. exact (MK_COMB (@lem4748477 A n _57909 _57910 f m'') (@lem4748537 A n _57909 _57910 f m'')). Qed.
Lemma lem4748550 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4748551 (x : Prop) : (x = x) = True.
Proof. exact (@lem4748550 Prop x). Qed.
Lemma lem4748552 {A : Type'} (n : nat) (_57909 : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : ((term1229 A n _57909 _57910 f m'') = (term1229 A n _57909 _57910 f m'')) = True.
Proof. exact (@lem4748551 (term1229 A n _57909 _57910 f m'')). Qed.
Lemma lem4748553 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : ((term1208 A n f m'' _57910 _57909) = (term1236 A _57909 n _57910 f m'')) = True.
Proof. exact (TRANS (@lem4748548 A n _57909 _57910 f m'') (@lem4748552 A n _57909 _57910 f m'')). Qed.
Lemma lem4748554 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : True = ((term1208 A n f m'' _57910 _57909) = (term1236 A _57909 n _57910 f m'')).
Proof. exact (SYM (@lem4748553 A _57909 n _57910 f m'')). Qed.
Lemma lem4748555 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1208 A n f m'' _57910 _57909) = (term1236 A _57909 n _57910 f m'').
Proof. exact (EQ_MP (@lem4748554 A _57909 n _57910 f m'') (@lem0)). Qed.
Lemma lem4748556 {A : Type'} (_57909 : nat) (_57910 : nat) (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : (f m'') = x) : term1236 A _57909 n _57910 f m''.
Proof. exact (EQ_MP (@lem4748555 A _57909 n _57910 f m'') (@lem4747615 A _57910 _57909 m n m' f m'' x h1 h2)). Qed.
Lemma lem4748558 (b : Prop) (a : Prop) : (a \/ b) = (term616 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4748559 {A : Type'} (n : nat) (f : nat -> A) (m'' : nat) (_57910 : nat) (_57909 : nat) : (term1236 A _57909 n _57910 f m'') = (term1237 A n f m'' _57910 _57909).
Proof. exact (@lem4748558 (term1234 A _57909 n _57910 f m'') (_57910 = _57909)). Qed.
Lemma lem4748561 (a : Prop) (b : Prop) : (term1238 a b) = (term1239 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4748562 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1240 A _57909 n _57910 f m'') = (term1241 A _57909 n _57910 f m'').
Proof. exact (@lem4748561 (term312 _57909 n) (term1233 A _57909 n _57910 f m'')). Qed.
Lemma lem4748564 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4748565 (_57909 : nat) (n : nat) : (term618 _57909 n) = (Peano.lt _57909 n).
Proof. exact (@lem4748564 (Peano.lt _57909 n)). Qed.
Lemma lem4748566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4748567 (_57909 : nat) (n : nat) : (term1242 _57909 n) = (term1243 _57909 n).
Proof. exact (MK_COMB (@lem4748566) (@lem4748565 _57909 n)). Qed.
Lemma lem4748569 (a : Prop) (b : Prop) : (term1238 a b) = (term1239 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4748570 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1244 A _57909 n _57910 f m'') = (term1245 A _57909 n _57910 f m'').
Proof. exact (@lem4748569 (term1001 A _57909 f m'') (term1246 A n _57910 f m'')). Qed.
Lemma lem4748572 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4748573 {A : Type'} (_57909 : nat) (f : nat -> A) (m'' : nat) : (term1247 A _57909 f m'') = ((f _57909) = (f m'')).
Proof. exact (@lem4748572 ((f _57909) = (f m''))). Qed.
Lemma lem4748574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4748575 {A : Type'} (_57909 : nat) (f : nat -> A) (m'' : nat) : (term1248 A _57909 f m'') = (term1249 A _57909 f m'').
Proof. exact (MK_COMB (@lem4748574) (@lem4748573 A _57909 f m'')). Qed.
Lemma lem4748577 (a : Prop) (b : Prop) : (term1238 a b) = (term1239 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4748578 {A : Type'} (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1250 A n _57910 f m'') = (term1251 A n _57910 f m'').
Proof. exact (@lem4748577 (term312 _57910 n) (term1001 A _57910 f m'')). Qed.
Lemma lem4748580 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4748581 (_57910 : nat) (n : nat) : (term618 _57910 n) = (Peano.lt _57910 n).
Proof. exact (@lem4748580 (Peano.lt _57910 n)). Qed.
Lemma lem4748582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4748583 (_57910 : nat) (n : nat) : (term1242 _57910 n) = (term1243 _57910 n).
Proof. exact (MK_COMB (@lem4748582) (@lem4748581 _57910 n)). Qed.
Lemma lem4748585 (a : Prop) : (term242 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4748586 {A : Type'} (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1247 A _57910 f m'') = ((f _57910) = (f m'')).
Proof. exact (@lem4748585 ((f _57910) = (f m''))). Qed.
Lemma lem4748587 {A : Type'} (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1251 A n _57910 f m'') = (term1252 A n _57910 f m'').
Proof. exact (MK_COMB (@lem4748583 _57910 n) (@lem4748586 A _57910 f m'')). Qed.
Lemma lem4748588 {A : Type'} (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1250 A n _57910 f m'') = (term1252 A n _57910 f m'').
Proof. exact (TRANS (@lem4748578 A n _57910 f m'') (@lem4748587 A n _57910 f m'')). Qed.
Lemma lem4748589 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1245 A _57909 n _57910 f m'') = (term1253 A _57909 n _57910 f m'').
Proof. exact (MK_COMB (@lem4748575 A _57909 f m'') (@lem4748588 A n _57910 f m'')). Qed.
Lemma lem4748590 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1244 A _57909 n _57910 f m'') = (term1253 A _57909 n _57910 f m'').
Proof. exact (TRANS (@lem4748570 A _57909 n _57910 f m'') (@lem4748589 A _57909 n _57910 f m'')). Qed.
Lemma lem4748591 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1241 A _57909 n _57910 f m'') = (term1254 A _57909 n _57910 f m'').
Proof. exact (MK_COMB (@lem4748567 _57909 n) (@lem4748590 A _57909 n _57910 f m'')). Qed.
Lemma lem4748592 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1240 A _57909 n _57910 f m'') = (term1254 A _57909 n _57910 f m'').
Proof. exact (TRANS (@lem4748562 A _57909 n _57910 f m'') (@lem4748591 A _57909 n _57910 f m'')). Qed.
Lemma lem4748593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4748594 {A : Type'} (_57909 : nat) (n : nat) (_57910 : nat) (f : nat -> A) (m'' : nat) : (term1255 A _57909 n _57910 f m'') = (term1256 A _57909 n _57910 f m'').
Proof. exact (MK_COMB (@lem4748593) (@lem4748592 A _57909 n _57910 f m'')). Qed.
Lemma lem4748595 (_57910 : nat) (_57909 : nat) : (_57910 = _57909) = (_57910 = _57909).
Proof. exact (eq_refl (_57910 = _57909)). Qed.
Lemma lem4748596 {A : Type'} (n : nat) (f : nat -> A) (m'' : nat) (_57910 : nat) (_57909 : nat) : (term1237 A n f m'' _57910 _57909) = (term1257 A n f m'' _57910 _57909).
Proof. exact (MK_COMB (@lem4748594 A _57909 n _57910 f m'') (@lem4748595 _57910 _57909)). Qed.
Lemma lem4748597 {A : Type'} (n : nat) (f : nat -> A) (m'' : nat) (_57910 : nat) (_57909 : nat) : (term1236 A _57909 n _57910 f m'') = (term1257 A n f m'' _57910 _57909).
Proof. exact (TRANS (@lem4748559 A n f m'' _57910 _57909) (@lem4748596 A n f m'' _57910 _57909)). Qed.
Lemma lem4748599 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term1258 A n f m''.
Proof. exact (conj (@lem4748295 A f x n m'' m' h1) (@lem4748304 A f m'')). Qed.
Lemma lem4748600 {A : Type'} (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1080 A f x n m'' m') (h2 : (f m') = x) (h3 : (f m'') = x) : term1259 A m' n f m''.
Proof. exact (conj (@lem4748288 A m' f m'' x h2 h3) (@lem4748599 A f x n m'' m' h1)). Qed.
Lemma lem4748601 {A : Type'} (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1080 A f x n m'' m') (h2 : (f m') = x) (h3 : (f m'') = x) : term1260 A m' n f m''.
Proof. exact (conj (@lem4748281 A f x n m'' m' h1) (@lem4748600 A n m' f m'' x h1 h2 h3)). Qed.
Lemma lem4748603 {A : Type'} (_57910 : nat) (_57909 : nat) (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : (f m'') = x) : term1257 A n f m'' _57910 _57909.
Proof. exact (EQ_MP (@lem4748597 A n f m'' _57910 _57909) (@lem4748556 A _57909 _57910 m n m' f m'' x h1 h2)). Qed.
Lemma lem4748604 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : (f m'') = x) : term1261 A n f m'' m'.
Proof. exact (@lem4748603 A m'' m' m n m' f m'' x h1 h2). Qed.
Lemma lem4748607 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : m'' = m'.
Proof. exact (@lem4748604 A m n m' f m'' x h1 h4 (@lem4748601 A n m' f m'' x h2 h3 h4)). Qed.
Lemma lem4748608 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : term1262 m'' m'.
Proof. exact (fun h0 : term860 m'' m' => @lem4748607 A m n m' f m'' x h1 h2 h3 h4). Qed.
Lemma lem4748610 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748611 (m'' : nat) (m' : nat) : (term1262 m'' m') = (m'' = m').
Proof. exact (@lem4748610 (m'' = m')). Qed.
Lemma lem4748612 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : m'' = m'.
Proof. exact (EQ_MP (@lem4748611 m'' m') (@lem4748608 A m n m' f m'' x h1 h2 h3 h4)). Qed.
Lemma lem4748615 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4748617 (m'' : nat) (m' : nat) : (term860 m'' m') = (term1263 m'' m').
Proof. exact (@lem4748615 (m'' = m')). Qed.
Lemma lem4748620 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1080 A f x n m'' m') : term1263 m'' m'.
Proof. exact (EQ_MP (@lem4748617 m'' m') (@lem4747670 A f x n m'' m' h1)). Qed.
Lemma lem4748623 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : False.
Proof. exact (@lem4748620 A f x n m'' m' h2 (@lem4748612 A m n m' f m'' x h1 h2 h3 h4)). Qed.
Lemma lem4748624 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : term632.
Proof. exact (fun h0 : ~ False => @lem4748623 A m n m' f m'' x h1 h2 h3 h4). Qed.
Lemma lem4748626 (p : Prop) : (term612 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4748627 : term632 = False.
Proof. exact (@lem4748626 False). Qed.
Lemma lem4748629 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : False.
Proof. exact (EQ_MP (@lem4748627) (@lem4748624 A m n m' f m'' x h1 h2 h3 h4)). Qed.
Lemma lem4748630 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : (term312 m'' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m'' n => @lem4748188 A f x n m'' m' h1 h2) (fun h3 : False => @lem4747477 m'' n h1)). Qed.
Lemma lem4748632 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748630 A f x n m'' m' h1 h2) (@lem4747477 m'' n h1)). Qed.
Lemma lem4748633 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4748079 A f x n m'' m' h1 h2) (fun h3 : False => @lem4747242 m' n h1)). Qed.
Lemma lem4748635 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748633 A f x n m'' m' h1 h2) (@lem4747242 m' n h1)). Qed.
Lemma lem4748636 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : (term312 m'' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m'' n => @lem4747970 A f x n m'' m' h1 h2) (fun h3 : False => @lem4747007 m'' n h1)). Qed.
Lemma lem4748638 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748636 A f x n m'' m' h1 h2) (@lem4747007 m'' n h1)). Qed.
Lemma lem4748639 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1093 A f x n) (h2 : term1180 A m f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4747860) (@lem4747857 A m f x n m'' m' h1 h2)). Qed.
Lemma lem4748640 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : ((f m'') = x) = False.
Proof. exact (prop_ext (fun h5 : (f m'') = x => @lem4748629 A m n m' f m'' x h1 h2 h3 h4) (fun h5 : False => @lem4746594 A f m'' x h4)). Qed.
Lemma lem4748641 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : False.
Proof. exact (EQ_MP (@lem4748640 A m n m' f m'' x h1 h2 h3 h4) (@lem4746594 A f m'' x h4)). Qed.
Lemma lem4748642 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h5 : (f m') = x => @lem4748641 A m n m' f m'' x h1 h2 h3 h4) (fun h5 : False => @lem4746592 A f m' x h3)). Qed.
Lemma lem4748643 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : False.
Proof. exact (EQ_MP (@lem4748642 A m n m' f m'' x h1 h2 h3 h4) (@lem4746592 A f m' x h3)). Qed.
Lemma lem4748644 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : (term312 m'' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m'' n => @lem4748632 A f x n m'' m' h1 h2) (fun h3 : False => @lem4746520 m'' n h1)). Qed.
Lemma lem4748645 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748644 A f x n m'' m' h1 h2) (@lem4746520 m'' n h1)). Qed.
Lemma lem4748646 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4748635 A f x n m'' m' h1 h2) (fun h3 : False => @lem4746444 m' n h1)). Qed.
Lemma lem4748647 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748646 A f x n m'' m' h1 h2) (@lem4746444 m' n h1)). Qed.
Lemma lem4748648 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : (term312 m'' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m'' n => @lem4748638 A f x n m'' m' h1 h2) (fun h3 : False => @lem4746372 m'' n h1)). Qed.
Lemma lem4748649 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748648 A f x n m'' m' h1 h2) (@lem4746372 m'' n h1)). Qed.
Lemma lem4748650 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : ((f m'') = x) = False.
Proof. exact (prop_ext (fun h5 : (f m'') = x => @lem4748643 A m n m' f m'' x h1 h2 h3 h4) (fun h5 : False => @lem4746069 A f m'' x h4)). Qed.
Lemma lem4748651 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : False.
Proof. exact (EQ_MP (@lem4748650 A m n m' f m'' x h1 h2 h3 h4) (@lem4746069 A f m'' x h4)). Qed.
Lemma lem4748652 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h5 : (f m') = x => @lem4748651 A m n m' f m'' x h1 h2 h3 h4) (fun h5 : False => @lem4746065 A f m' x h3)). Qed.
Lemma lem4748653 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : False.
Proof. exact (EQ_MP (@lem4748652 A m n m' f m'' x h1 h2 h3 h4) (@lem4746065 A f m' x h3)). Qed.
Lemma lem4748654 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : (term312 m'' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m'' n => @lem4748645 A f x n m'' m' h1 h2) (fun h3 : False => @lem4745895 m'' n h1)). Qed.
Lemma lem4748655 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748654 A f x n m'' m' h1 h2) (@lem4745895 m'' n h1)). Qed.
Lemma lem4748656 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4748647 A f x n m'' m' h1 h2) (fun h3 : False => @lem4745717 m' n h1)). Qed.
Lemma lem4748657 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748656 A f x n m'' m' h1 h2) (@lem4745717 m' n h1)). Qed.
Lemma lem4748658 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : (term312 m'' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m'' n => @lem4748649 A f x n m'' m' h1 h2) (fun h3 : False => @lem4745547 m'' n h1)). Qed.
Lemma lem4748659 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748658 A f x n m'' m' h1 h2) (@lem4745547 m'' n h1)). Qed.
Lemma lem4748660 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : ((f m'') = x) = False.
Proof. exact (prop_ext (fun h5 : (f m'') = x => @lem4748653 A m n m' f m'' x h1 h2 h3 h4) (fun h5 : False => @lem4746069 A f m'' x h4)). Qed.
Lemma lem4748661 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : False.
Proof. exact (EQ_MP (@lem4748660 A m n m' f m'' x h1 h2 h3 h4) (@lem4746069 A f m'' x h4)). Qed.
Lemma lem4748662 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : ((f m') = x) = False.
Proof. exact (prop_ext (fun h5 : (f m') = x => @lem4748661 A m n m' f m'' x h1 h2 h3 h4) (fun h5 : False => @lem4746065 A f m' x h3)). Qed.
Lemma lem4748663 {A : Type'} (m : nat) (n : nat) (m' : nat) (f : nat -> A) (m'' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) (h4 : (f m'') = x) : False.
Proof. exact (EQ_MP (@lem4748662 A m n m' f m'' x h1 h2 h3 h4) (@lem4746065 A f m' x h3)). Qed.
Lemma lem4748664 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : (term312 m'' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m'' n => @lem4748655 A f x n m'' m' h1 h2) (fun h3 : False => @lem4745895 m'' n h1)). Qed.
Lemma lem4748665 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748664 A f x n m'' m' h1 h2) (@lem4745895 m'' n h1)). Qed.
Lemma lem4748666 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : (term312 m' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m' n => @lem4748657 A f x n m'' m' h1 h2) (fun h3 : False => @lem4745717 m' n h1)). Qed.
Lemma lem4748667 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748666 A f x n m'' m' h1 h2) (@lem4745717 m' n h1)). Qed.
Lemma lem4748668 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : (term312 m'' n) = False.
Proof. exact (prop_ext (fun h3 : term312 m'' n => @lem4748659 A f x n m'' m' h1 h2) (fun h3 : False => @lem4745547 m'' n h1)). Qed.
Lemma lem4748669 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m'' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748668 A f x n m'' m' h1 h2) (@lem4745547 m'' n h1)). Qed.
Lemma lem4748670 {A : Type'} (m : nat) (n : nat) (m'' : nat) (f : nat -> A) (m' : nat) (x : A) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') (h3 : (f m') = x) : False.
Proof. exact (or_elim (@lem4745188 A f x n m'' m' h2) (fun h0 : term312 m'' n => @lem4748665 A f x n m'' m' h0 h2) (fun h0 : (f m'') = x => @lem4748663 A m n m' f m'' x h1 h2 h3 h0)). Qed.
Lemma lem4748671 {A : Type'} (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term312 m' n) (h2 : term1080 A f x n m'' m') : False.
Proof. exact (or_elim (@lem4745188 A f x n m'' m' h2) (fun h0 : term312 m'' n => @lem4748669 A f x n m'' m' h0 h2) (fun h0 : (f m'') = x => @lem4748667 A f x n m'' m' h1 h2)). Qed.
Lemma lem4748672 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') (h2 : term1080 A f x n m'' m') : False.
Proof. exact (or_elim (@lem4745190 A f x n m'' m' h2) (fun h0 : term312 m' n => @lem4748671 A f x n m'' m' h0 h2) (fun h0 : (f m') = x => @lem4748670 A m n m'' f m' x h1 h2 h0)). Qed.
Lemma lem4748673 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : False.
Proof. exact (or_elim (@lem4745173 A m f x n m'' m' h1) (fun h0 : term1093 A f x n => @lem4748639 A m f x n m'' m' h0 h1) (fun h0 : term1080 A f x n m'' m' => @lem4748672 A m f x n m'' m' h1 h0)). Qed.
Lemma lem4748674 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : (term1180 A m f x n m'' m') = False.
Proof. exact (prop_ext (fun h2 : term1180 A m f x n m'' m' => @lem4748673 A m f x n m'' m' h1) (fun h2 : False => @lem4745172 A m f x n m'' m' h1)). Qed.
Lemma lem4748675 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m'' : nat) (m' : nat) (h1 : term1180 A m f x n m'' m') : False.
Proof. exact (EQ_MP (@lem4748674 A m f x n m'' m' h1) (@lem4745172 A m f x n m'' m' h1)). Qed.
Lemma lem4748676 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (m' : nat) (h1 : term1183 A m f x n m') : False.
Proof. exact (ex_elim (@lem4744854 A m f x n m' h1) (fun m'' : nat => fun h0 : term1182 A m f x n m' m'' => @lem4748675 A m f x n m'' m' h0)). Qed.
Lemma lem4748677 {A : Type'} (m : nat) (f : nat -> A) (x : A) (n : nat) (h1 : term1185 A m f x n) : False.
Proof. exact (ex_elim (@lem4744853 A m f x n h1) (fun m' : nat => fun h0 : term1184 A m f x n m' => @lem4748676 A m f x n m' h0)). Qed.
Lemma lem4748678 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term1029 A f x n) : False.
Proof. exact (ex_elim (@lem4744390 A f x n h1) (fun m : nat => fun h0 : term1186 A f x n m => @lem4748677 A m f x n h0)). Qed.
Lemma lem4748679 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term1029 A f x n) : term801.
Proof. exact (fun h0 : term803 => @lem4748678 A f x n h1). Qed.
Lemma lem4748680 : term801 = term802.
Proof. exact (@lem69 term803). Qed.
Lemma lem4748681 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term1029 A f x n) : term802.
Proof. exact (EQ_MP (@lem4748680) (@lem4748679 A f x n h1)). Qed.
Lemma lem4748682 {A : Type'} (f : nat -> A) (x : A) (n : nat) (h1 : term1029 A f x n) : term1035 A.
Proof. exact (fun h0 : term323 A => @lem4748681 A f x n h1). Qed.
Lemma lem4748683 {A : Type'} (f : nat -> A) (x : A) (n : nat) : term1038 A f x n.
Proof. exact (fun h0 : term1029 A f x n => @lem4748682 A f x n h0). Qed.
Lemma lem4748684 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : term1040 A a f x n.
Proof. exact (fun h0 : term9 A a x => @lem4748683 A f x n). Qed.
Lemma lem4748685 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1042 A s a f x n.
Proof. exact (fun h0 : @IN A x s => @lem4748684 A a f x n). Qed.
Lemma lem4748686 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1044 A s a f x n.
Proof. exact (fun h0 : term268 A n f s a => @lem4748685 A s a f x n). Qed.
Lemma lem4748687 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1046 A s a f x n.
Proof. exact (fun h0 : term252 A s a n => @lem4748686 A s a f x n). Qed.
Lemma lem4748688 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1047 A s a f x n.
Proof. exact (fun h0 : @IN A a s => @lem4748687 A s a f x n). Qed.
Lemma lem4748693 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : term1051 A a f x n.
Proof. exact (fun s : A -> Prop => @lem4748688 A s a f x n). Qed.
Lemma lem4748698 {A : Type'} (f : nat -> A) (x : A) (n : nat) : term1055 A f x n.
Proof. exact (fun a : A => @lem4748693 A a f x n). Qed.
Lemma lem4748703 {A : Type'} (x : A) (n : nat) : term1059 A x n.
Proof. exact (fun f : nat -> A => @lem4748698 A f x n). Qed.
Lemma lem4748708 {A : Type'} (n : nat) : term1063 A n.
Proof. exact (fun x : A => @lem4748703 A x n). Qed.
Lemma lem4748713 {A : Type'} : term1067 A.
Proof. exact (fun n : nat => @lem4748708 A n). Qed.
Lemma lem4748714 {A : Type'} : term1066 A.
Proof. exact (EQ_MP (@lem4743668 A) (@lem4748713 A)). Qed.
Lemma lem4748715 {A : Type'} (n : nat) : term1264 A n.
Proof. exact (@lem4748714 A n). Qed.
Lemma lem4748716 {A : Type'} (n : nat) : (term1264 A n) = (term1062 A n).
Proof. exact (eq_refl (term1264 A n)). Qed.
Lemma lem4748717 {A : Type'} (n : nat) : term1062 A n.
Proof. exact (EQ_MP (@lem4748716 A n) (@lem4748715 A n)). Qed.
Lemma lem4748718 {A : Type'} (n : nat) (x : A) : term1265 A n x.
Proof. exact (@lem4748717 A n x). Qed.
Lemma lem4748719 {A : Type'} (x : A) (n : nat) : (term1265 A n x) = (term1058 A x n).
Proof. exact (eq_refl (term1265 A n x)). Qed.
Lemma lem4748720 {A : Type'} (x : A) (n : nat) : term1058 A x n.
Proof. exact (EQ_MP (@lem4748719 A x n) (@lem4748718 A n x)). Qed.
Lemma lem4748721 {A : Type'} (x : A) (n : nat) (f : nat -> A) : term1266 A x n f.
Proof. exact (@lem4748720 A x n f). Qed.
Lemma lem4748722 {A : Type'} (f : nat -> A) (x : A) (n : nat) : (term1266 A x n f) = (term1054 A f x n).
Proof. exact (eq_refl (term1266 A x n f)). Qed.
Lemma lem4748723 {A : Type'} (f : nat -> A) (x : A) (n : nat) : term1054 A f x n.
Proof. exact (EQ_MP (@lem4748722 A f x n) (@lem4748721 A x n f)). Qed.
Lemma lem4748724 {A : Type'} (f : nat -> A) (x : A) (n : nat) (a : A) : term1267 A f x n a.
Proof. exact (@lem4748723 A f x n a). Qed.
Lemma lem4748725 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : (term1267 A f x n a) = (term1050 A a f x n).
Proof. exact (eq_refl (term1267 A f x n a)). Qed.
Lemma lem4748726 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) : term1050 A a f x n.
Proof. exact (EQ_MP (@lem4748725 A a f x n) (@lem4748724 A f x n a)). Qed.
Lemma lem4748727 {A : Type'} (a : A) (f : nat -> A) (x : A) (n : nat) (s : A -> Prop) : term1268 A a f x n s.
Proof. exact (@lem4748726 A a f x n s). Qed.
Lemma lem4748728 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : (term1268 A a f x n s) = (term1030 A s a f x n).
Proof. exact (eq_refl (term1268 A a f x n s)). Qed.
Lemma lem4748729 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1030 A s a f x n.
Proof. exact (EQ_MP (@lem4748728 A s a f x n) (@lem4748727 A a f x n s)). Qed.
Lemma lem4748731 {A : Type'} (s : A -> Prop) (a : A) (f : nat -> A) (x : A) (n : nat) : term1030 A s a f x n.
Proof. exact (@lem4743339 A s a f x n (@lem4748729 A s a f x n)). Qed.
Lemma lem4748732 {A : Type'} (f : nat -> A) (x : A) (n : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term1045 A s a f x n.
Proof. exact (@lem4748731 A s a f x n (@lem4715763 A a s h1)). Qed.
Lemma lem4748733 {A : Type'} (f : nat -> A) (x : A) (n : nat) (a : A) (s : A -> Prop) (h1 : term252 A s a n) (h2 : @IN A a s) : term1043 A s a f x n.
Proof. exact (@lem4748732 A f x n a s h2 (@lem4715822 A s a n h1)). Qed.
Lemma lem4748734 {A : Type'} (x : A) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term252 A s a n) (h3 : @IN A a s) : term1041 A s a f x n.
Proof. exact (@lem4748733 A f x n a s h2 h3 (@lem4715928 A n f s a h1)). Qed.
Lemma lem4748735 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term252 A s a n) (h3 : @IN A a s) (h4 : @IN A x s) : term1039 A a f x n.
Proof. exact (@lem4748734 A x f n a s h1 h2 h3 (@lem4722014 A x s h4)). Qed.
Lemma lem4748736 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term9 A a x) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term1037 A f x n.
Proof. exact (@lem4748735 A f n a x s h1 h3 h4 h5 (@lem4713738 A a x h2)). Qed.
Lemma lem4748737 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term9 A a x) (h3 : term1029 A f x n) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : term1034 A.
Proof. exact (@lem4748736 A f n a x s h1 h2 h4 h5 h6 (@lem4743320 A f x n h3)). Qed.
Lemma lem4748738 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term9 A a x) (h3 : term1029 A f x n) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : term801.
Proof. exact (@lem4748737 A f n a x s h1 h2 h3 h4 h5 h6 (@lem4743321 A)). Qed.
Lemma lem4748739 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term9 A a x) (h3 : term1029 A f x n) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : False.
Proof. exact (@lem4748738 A f n a x s h1 h2 h3 h4 h5 h6 (@lem91686)). Qed.
Lemma lem4748740 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term9 A a x) (h3 : term1029 A f x n) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : (term1029 A f x n) = False.
Proof. exact (prop_ext (fun h7 : term1029 A f x n => @lem4748739 A f n a x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4743320 A f x n h3)). Qed.
Lemma lem4748741 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term9 A a x) (h3 : term1029 A f x n) (h4 : term252 A s a n) (h5 : @IN A a s) (h6 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem4748740 A f n a x s h1 h2 h3 h4 h5 h6) (@lem4743320 A f x n h3)). Qed.
Lemma lem4748742 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term9 A a x) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term1028 A f x n.
Proof. exact (fun h0 : term1029 A f x n => @lem4748741 A f n a x s h1 h2 h0 h3 h4 h5). Qed.
Lemma lem4748743 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term9 A a x) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term794 A f x n.
Proof. exact (EQ_MP (@lem4743319 A f x n) (@lem4748742 A f n a x s h1 h2 h3 h4 h5)). Qed.
Lemma lem4748744 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term9 A a x) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term729 A f n a x.
Proof. exact (EQ_MP (@lem4723121 A f n a x h2) (@lem4748743 A f n a x s h1 h2 h3 h4 h5)). Qed.
Lemma lem4748745 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : a = x) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term729 A f n a x.
Proof. exact (EQ_MP (@lem4722682 A f n a x h2) (@lem4743315 A f n a x s h1 h2 h3 h4 h5)). Qed.
Lemma lem4748746 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term252 A s a n) (h3 : @IN A a s) (h4 : @IN A x s) : term729 A f n a x.
Proof. exact (or_elim (@lem4713736 A a x) (fun h0 : a = x => @lem4748745 A f n a x s h1 h0 h2 h3 h4) (fun h0 : term9 A a x => @lem4748744 A f n a x s h1 h0 h2 h3 h4)). Qed.
Lemma lem4748747 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term252 A s a n) (h3 : @IN A a s) (h4 : @IN A x s) : term709 A n f a x.
Proof. exact (EQ_MP (@lem4722161 A n f a x) (@lem4748746 A f n a x s h1 h2 h3 h4)). Qed.
Lemma lem4748748 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term252 A s a n) (h3 : @IN A a s) (h4 : @IN A x s) : term708 A s n f a x.
Proof. exact (EQ_MP (@lem4722138 A n f a x s h4) (@lem4748747 A f n a x s h1 h2 h3 h4)). Qed.
Lemma lem4748749 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term697 A n f a x.
Proof. exact (@lem4748748 A f n a x s h2 h3 h4 h5 (@lem4722068 A x s a n f h1)). Qed.
Lemma lem4748750 {A : Type'} (f : nat -> A) (n : nat) (a : A) (x : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) (h5 : @IN A x s) : term696 A n f a x.
Proof. exact (EQ_MP (@lem4722065 A n f a x) (@lem4748749 A f n a x s h1 h2 h3 h4 h5)). Qed.
Lemma lem4748751 {A : Type'} (x : A) (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term1269 A s n f a x.
Proof. exact (fun h0 : @IN A x s => @lem4748750 A f n a x s h1 h2 h3 h4 h0). Qed.
Lemma lem4748756 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term1270 A s n f a.
Proof. exact (fun x : A => @lem4748751 A x f n a s h1 h2 h3 h4). Qed.
Lemma lem4748757 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term1271 A s n f a.
Proof. exact (conj (@lem4722013 A f n a s h1 h2 h3 h4) (@lem4748756 A f n a s h1 h2 h3 h4)). Qed.
Lemma lem4748758 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term207 A s n.
Proof. exact (ex_intro (term206 A s n) (term273 A n f a) (@lem4748757 A f n a s h1 h2 h3 h4)). Qed.
Lemma lem4748759 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term266 A s a n f) : term267 A s a n f.
Proof. exact (proj2 (@lem4715926 A s a n f h1)). Qed.
Lemma lem4748760 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (f : nat -> A) (h1 : term266 A s a n f) : term268 A n f s a.
Proof. exact (proj1 (@lem4715926 A s a n f h1)). Qed.
Lemma lem4748761 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : (term267 A s a n f) = (term207 A s n).
Proof. exact (prop_ext (fun h5 : term267 A s a n f => @lem4748758 A f n a s h1 h2 h3 h4) (fun h5 : term207 A s n => @lem4715927 A s a n f h1)). Qed.
Lemma lem4748762 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term207 A s n.
Proof. exact (EQ_MP (@lem4748761 A f n a s h1 h2 h3 h4) (@lem4715927 A s a n f h1)). Qed.
Lemma lem4748763 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : (term268 A n f s a) = (term207 A s n).
Proof. exact (prop_ext (fun h5 : term268 A n f s a => @lem4748762 A f n a s h1 h2 h3 h4) (fun h5 : term207 A s n => @lem4715928 A n f s a h2)). Qed.
Lemma lem4748764 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term267 A s a n f) (h2 : term268 A n f s a) (h3 : term252 A s a n) (h4 : @IN A a s) : term207 A s n.
Proof. exact (EQ_MP (@lem4748763 A f n a s h1 h2 h3 h4) (@lem4715928 A n f s a h2)). Qed.
Lemma lem4748765 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term266 A s a n f) (h3 : term252 A s a n) (h4 : @IN A a s) : (term267 A s a n f) = (term207 A s n).
Proof. exact (prop_ext (fun h5 : term267 A s a n f => @lem4748764 A f n a s h5 h1 h3 h4) (fun h5 : term207 A s n => @lem4748759 A s a n f h2)). Qed.
Lemma lem4748766 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term268 A n f s a) (h2 : term266 A s a n f) (h3 : term252 A s a n) (h4 : @IN A a s) : term207 A s n.
Proof. exact (EQ_MP (@lem4748765 A f n a s h1 h2 h3 h4) (@lem4748759 A s a n f h2)). Qed.
Lemma lem4748767 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term266 A s a n f) (h2 : term252 A s a n) (h3 : @IN A a s) : (term268 A n f s a) = (term207 A s n).
Proof. exact (prop_ext (fun h4 : term268 A n f s a => @lem4748766 A f n a s h4 h1 h2 h3) (fun h4 : term207 A s n => @lem4748760 A s a n f h1)). Qed.
Lemma lem4748768 {A : Type'} (f : nat -> A) (n : nat) (a : A) (s : A -> Prop) (h1 : term266 A s a n f) (h2 : term252 A s a n) (h3 : @IN A a s) : term207 A s n.
Proof. exact (EQ_MP (@lem4748767 A f n a s h1 h2 h3) (@lem4748760 A s a n f h1)). Qed.
Lemma lem4748769 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term260 A s a n) (h2 : term252 A s a n) (h3 : @IN A a s) : term207 A s n.
Proof. exact (ex_elim (@lem4715925 A s a n h1) (fun f : nat -> A => fun h0 : term1272 A s a n f => @lem4748768 A f n a s h0 h2 h3)). Qed.
Lemma lem4748770 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term252 A s a n) (h2 : @IN A a s) : term265 A a s n.
Proof. exact (fun h0 : term260 A s a n => @lem4748769 A n a s h0 h1 h2). Qed.
Lemma lem4748771 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term252 A s a n) (h2 : @IN A a s) : term264 A a s n.
Proof. exact (EQ_MP (@lem4715924 A s a n h1) (@lem4748770 A n a s h1 h2)). Qed.
Lemma lem4748772 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term60 A n) (h2 : term252 A s a n) (h3 : @IN A a s) : term207 A s n.
Proof. exact (@lem4748771 A n a s h2 h3 (@lem4715825 A s a n h1)). Qed.
Lemma lem4748773 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term60 A n) (h2 : @IN A a s) : term257 A a s n.
Proof. exact (fun h0 : term252 A s a n => @lem4748772 A n a s h1 h0 h2). Qed.
Lemma lem4748774 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term60 A n) (h2 : @IN A a s) : term256 A a s n.
Proof. exact (EQ_MP (@lem4715821 A n a s h2) (@lem4748773 A n a s h1 h2)). Qed.
Lemma lem4748775 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term246 A s n) : term225 A s n.
Proof. exact (proj2 (@lem4715757 A s n h1)). Qed.
Lemma lem4748776 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term246 A s n) : term244 A s.
Proof. exact (proj1 (@lem4715757 A s n h1)). Qed.
Lemma lem4748777 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term225 A s n) (h2 : term60 A n) (h3 : @IN A a s) : term207 A s n.
Proof. exact (@lem4748774 A n a s h2 h3 (@lem4715761 A a s n h1)). Qed.
Lemma lem4748778 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term225 A s n) (h2 : term60 A n) (h3 : term244 A s) : term207 A s n.
Proof. exact (ex_elim (@lem4715762 A s h3) (fun a : A => fun h0 : term243 A s a => @lem4748777 A n a s h1 h2 h0)). Qed.
Lemma lem4748779 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term60 A n) (h2 : term244 A s) (h3 : term246 A s n) : (term225 A s n) = (term207 A s n).
Proof. exact (prop_ext (fun h4 : term225 A s n => @lem4748778 A n s h4 h1 h2) (fun h4 : term207 A s n => @lem4748775 A s n h3)). Qed.
Lemma lem4748780 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term60 A n) (h2 : term244 A s) (h3 : term246 A s n) : term207 A s n.
Proof. exact (EQ_MP (@lem4748779 A s n h1 h2 h3) (@lem4748775 A s n h3)). Qed.
Lemma lem4748781 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term60 A n) (h2 : term246 A s n) : (term244 A s) = (term207 A s n).
Proof. exact (prop_ext (fun h3 : term244 A s => @lem4748780 A s n h1 h3 h2) (fun h3 : term207 A s n => @lem4748776 A s n h2)). Qed.
Lemma lem4748782 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term60 A n) (h2 : term246 A s n) : term207 A s n.
Proof. exact (EQ_MP (@lem4748781 A s n h1 h2) (@lem4748776 A s n h2)). Qed.
Lemma lem4748783 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term60 A n) : term248 A s n.
Proof. exact (fun h0 : term246 A s n => @lem4748782 A s n h1 h0). Qed.
Lemma lem4748784 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term60 A n) : term229 A s n.
Proof. exact (EQ_MP (@lem4715756 A s n) (@lem4748783 A s n h1)). Qed.
Lemma lem4748785 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term60 A n) : term211 A s n.
Proof. exact (EQ_MP (@lem4715668 A s n) (@lem4748784 A s n h1)). Qed.
Lemma lem4748790 {A : Type'} (n : nat) (h1 : term60 A n) : term214 A n.
Proof. exact (fun s : A -> Prop => @lem4748785 A s n h1). Qed.
Lemma lem4748791 {A : Type'} (n : nat) (h1 : term60 A n) : term74 A n.
Proof. exact (EQ_MP (@lem4715576 A n) (@lem4748790 A n h1)). Qed.
Lemma lem4748792 {A : Type'} (n : nat) : term76 A n.
Proof. exact (fun h0 : term60 A n => @lem4748791 A n h0). Qed.
Lemma lem4748797 {A : Type'} : term80 A.
Proof. exact (fun n : nat => @lem4748792 A n). Qed.
Lemma lem4748798 {A : Type'} : term82 A.
Proof. exact (conj (@lem4714032 A) (@lem4748797 A)). Qed.
Lemma lem4748799 {A : Type'} : term63 A.
Proof. exact (@lem4713844 A (@lem4748798 A)). Qed.
Lemma lem4748800 {A : Type'} : term54 A.
Proof. exact (EQ_MP (@lem4713821 A) (@lem4748799 A)). Qed.
