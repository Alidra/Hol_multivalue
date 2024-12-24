Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONSTR_BOT_term_abbrevs.
Require Import CONSTR_spec.
Require Import MK_REC_INJ_spec.
Require Import ZCONSTR_ZBOT_spec.
Require Import ZRECSPACE_RULES_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1059220_spec.
Require Import thm1059234_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1059773 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1058926 A)). Qed.
Lemma lem1059774 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem1059775 {A : Type'} (c : nat) (h1 : term0 A) : term1 A c.
Proof. exact (@lem1059774 A h1 c). Qed.
Lemma lem1059776 {A : Type'} (c : nat) : (term1 A c) = (term2 A c).
Proof. exact (eq_refl (term1 A c)). Qed.
Lemma lem1059777 {A : Type'} (c : nat) (h1 : term0 A) : term2 A c.
Proof. exact (EQ_MP (@lem1059776 A c) (@lem1059775 A c h1)). Qed.
Lemma lem1059778 {A : Type'} (c : nat) (i : A) (h1 : term0 A) : term3 A c i.
Proof. exact (@lem1059777 A c h1 i). Qed.
Lemma lem1059779 {A : Type'} (c : nat) (i : A) : (term3 A c i) = (term4 A c i).
Proof. exact (eq_refl (term3 A c i)). Qed.
Lemma lem1059780 {A : Type'} (c : nat) (i : A) (h1 : term0 A) : term4 A c i.
Proof. exact (EQ_MP (@lem1059779 A c i) (@lem1059778 A c i h1)). Qed.
Lemma lem1059781 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term0 A) : term5 A c i r.
Proof. exact (@lem1059780 A c i h1 r). Qed.
Lemma lem1059782 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term5 A c i r) = (term6 A c i r).
Proof. exact (eq_refl (term5 A c i r)). Qed.
Lemma lem1059783 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term0 A) : term6 A c i r.
Proof. exact (EQ_MP (@lem1059782 A c i r) (@lem1059781 A c i r h1)). Qed.
Lemma lem1059784 {A : Type'} (r : type1600 A) (h1 : term7 A r) : term7 A r.
Proof. exact (h1). Qed.
Lemma lem1059785 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term0 A) (h2 : term7 A r) : term8 A c i r.
Proof. exact (@lem1059783 A c i r h1 (@lem1059784 A r h2)). Qed.
Lemma lem1059786 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term7 A r) : term9 A c i r.
Proof. exact (fun h0 : term0 A => @lem1059785 A c i r h0 h1). Qed.
Lemma lem1059787 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem1059788 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term0 A) (h2 : term7 A r) : term8 A c i r.
Proof. exact (@lem1059786 A c i r h2 (@lem1059787 A h1)). Qed.
Lemma lem1059789 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term0 A) : term6 A c i r.
Proof. exact (fun h0 : term7 A r => @lem1059788 A c i r h1 h0). Qed.
Lemma lem1059790 {A : Type'} (c : nat) (i : A) (h1 : term0 A) : term4 A c i.
Proof. exact (fun r : type1600 A => @lem1059789 A c i r h1). Qed.
Lemma lem1059791 {A : Type'} (c : nat) (h1 : term0 A) : term2 A c.
Proof. exact (fun i : A => @lem1059790 A c i h1). Qed.
Lemma lem1059792 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun c : nat => @lem1059791 A c h1). Qed.
Lemma lem1059793 {A : Type'} : term10 A.
Proof. exact (fun h0 : term0 A => @lem1059792 A h0). Qed.
Lemma lem1059794 {A : Type'} : term0 A.
Proof. exact (@lem1059793 A (@lem1059773 A)). Qed.
Lemma lem1059795 {A : Type'} (c : nat) : term1 A c.
Proof. exact (@lem1059794 A c). Qed.
Lemma lem1059796 {A : Type'} (c : nat) : (term1 A c) = (term2 A c).
Proof. exact (eq_refl (term1 A c)). Qed.
Lemma lem1059797 {A : Type'} (c : nat) : term2 A c.
Proof. exact (EQ_MP (@lem1059796 A c) (@lem1059795 A c)). Qed.
Lemma lem1059798 {A : Type'} (c : nat) (i : A) : term3 A c i.
Proof. exact (@lem1059797 A c i). Qed.
Lemma lem1059799 {A : Type'} (c : nat) (i : A) : (term3 A c i) = (term4 A c i).
Proof. exact (eq_refl (term3 A c i)). Qed.
Lemma lem1059800 {A : Type'} (c : nat) (i : A) : term4 A c i.
Proof. exact (EQ_MP (@lem1059799 A c i) (@lem1059798 A c i)). Qed.
Lemma lem1059801 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term5 A c i r.
Proof. exact (@lem1059800 A c i r). Qed.
Lemma lem1059802 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term5 A c i r) = (term6 A c i r).
Proof. exact (eq_refl (term5 A c i r)). Qed.
Lemma lem1059816 {A : Type'} : @ZRECSPACE A (@ZBOT A).
Proof. exact (proj1 (@lem1058926 A)). Qed.
Lemma lem1059817 {A : Type'} : (@ZRECSPACE A (@ZBOT A)) = ((@ZRECSPACE A (@ZBOT A)) = True).
Proof. exact (@lem7 (@ZRECSPACE A (@ZBOT A))). Qed.
Lemma lem1059819 {A : Type'} (c : nat) : term11 A c.
Proof. exact (@lem1058349 A c). Qed.
Lemma lem1059820 {A : Type'} (c : nat) : (term11 A c) = (term12 A c).
Proof. exact (eq_refl (term11 A c)). Qed.
Lemma lem1059821 {A : Type'} (c : nat) : term12 A c.
Proof. exact (EQ_MP (@lem1059820 A c) (@lem1059819 A c)). Qed.
Lemma lem1059822 {A : Type'} (c : nat) (i : A) : term13 A c i.
Proof. exact (@lem1059821 A c i). Qed.
Lemma lem1059823 {A : Type'} (c : nat) (i : A) : (term13 A c i) = (term14 A c i).
Proof. exact (eq_refl (term13 A c i)). Qed.
Lemma lem1059824 {A : Type'} (c : nat) (i : A) : term14 A c i.
Proof. exact (EQ_MP (@lem1059823 A c i) (@lem1059822 A c i)). Qed.
Lemma lem1059825 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term15 A c i r.
Proof. exact (@lem1059824 A c i r). Qed.
Lemma lem1059826 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term15 A c i r) = (term16 A c i r).
Proof. exact (eq_refl (term15 A c i r)). Qed.
Lemma lem1059827 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term16 A c i r.
Proof. exact (EQ_MP (@lem1059826 A c i r) (@lem1059825 A c i r)). Qed.
Lemma lem1059828 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term17 A c i r.
Proof. exact (@lem82 ((@ZCONSTR A c i r) = (@ZBOT A))). Qed.
Lemma lem1059841 {A : Type'} (x : type1597 A) : term18 A x.
Proof. exact (@lem1059697 A x). Qed.
Lemma lem1059842 {A : Type'} (x : type1597 A) : (term18 A x) = (term19 A x).
Proof. exact (eq_refl (term18 A x)). Qed.
Lemma lem1059843 {A : Type'} (x : type1597 A) : term19 A x.
Proof. exact (EQ_MP (@lem1059842 A x) (@lem1059841 A x)). Qed.
Lemma lem1059844 {A : Type'} (x : type1597 A) (y : type1597 A) : term20 A x y.
Proof. exact (@lem1059843 A x y). Qed.
Lemma lem1059845 {A : Type'} (x : type1597 A) (y : type1597 A) : (term20 A x y) = (term21 A x y).
Proof. exact (eq_refl (term20 A x y)). Qed.
Lemma lem1059847 {A : Type'} (c : nat) : term22 A c.
Proof. exact (@lem1059607 A c). Qed.
Lemma lem1059848 {A : Type'} (c : nat) : (term22 A c) = (term23 A c).
Proof. exact (eq_refl (term22 A c)). Qed.
Lemma lem1059849 {A : Type'} (c : nat) : term23 A c.
Proof. exact (EQ_MP (@lem1059848 A c) (@lem1059847 A c)). Qed.
Lemma lem1059850 {A : Type'} (c : nat) (i : A) : term24 A c i.
Proof. exact (@lem1059849 A c i). Qed.
Lemma lem1059851 {A : Type'} (c : nat) (i : A) : (term24 A c i) = (term25 A c i).
Proof. exact (eq_refl (term24 A c i)). Qed.
Lemma lem1059852 {A : Type'} (c : nat) (i : A) : term25 A c i.
Proof. exact (EQ_MP (@lem1059851 A c i) (@lem1059850 A c i)). Qed.
Lemma lem1059853 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term26 A c i r.
Proof. exact (@lem1059852 A c i r). Qed.
Lemma lem1059854 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term26 A c i r) = ((@CONSTR A c i r) = (term27 A c i r)).
Proof. exact (eq_refl (term26 A c i r)). Qed.
Lemma lem1059859 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (term27 A c i r).
Proof. exact (EQ_MP (@lem1059854 A c i r) (@lem1059853 A c i r)). Qed.
Lemma lem1059860 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (term27 A c i r).
Proof. exact (@lem1059859 A c i r). Qed.
Lemma lem1059861 {A : Type'} : (@eq (recspace A)) = (@eq (recspace A)).
Proof. exact (eq_refl (@eq (recspace A))). Qed.
Lemma lem1059862 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term28 A c i r) = (term29 A c i r).
Proof. exact (MK_COMB (@lem1059861 A) (@lem1059860 A c i r)). Qed.
Lemma lem1059864 {A : Type'} : (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
Proof. exact (TRANS (@lem1059220 A) (@lem1059234 A)). Qed.
Lemma lem1059865 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@CONSTR A c i r) = (@BOTTOM A)) = ((term27 A c i r) = (@_mk_rec A (@ZBOT A))).
Proof. exact (MK_COMB (@lem1059862 A c i r) (@lem1059864 A)). Qed.
Lemma lem1059868 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1059869 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term30 A c i r) = (term31 A c i r).
Proof. exact (MK_COMB (@lem1059868) (@lem1059865 A c i r)). Qed.
Lemma lem1059870 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term31 A c i r) = (term30 A c i r).
Proof. exact (SYM (@lem1059869 A c i r)). Qed.
Lemma lem1059871 {A : Type'} (c : nat) (i : A) (r : type1614 A) (h1 : (term27 A c i r) = (@_mk_rec A (@ZBOT A))) : (term27 A c i r) = (@_mk_rec A (@ZBOT A)).
Proof. exact (h1). Qed.
Lemma lem1059873 {A : Type'} (x : type1597 A) (y : type1597 A) : term21 A x y.
Proof. exact (EQ_MP (@lem1059845 A x y) (@lem1059844 A x y)). Qed.
Lemma lem1059874 {A : Type'} (x : type1597 A) (y : type1597 A) : term21 A x y.
Proof. exact (@lem1059873 A x y). Qed.
Lemma lem1059875 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term32 A c i r.
Proof. exact (@lem1059874 A (term33 A c i r) (@ZBOT A)). Qed.
Lemma lem1059876 {A : Type'} (c : nat) (i : A) (r : type1614 A) (h1 : (term27 A c i r) = (@_mk_rec A (@ZBOT A))) : term34 A c i r.
Proof. exact (@lem1059875 A c i r (@lem1059871 A c i r h1)). Qed.
Lemma lem1059878 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1059879 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term35 A c i r) = (term36 A c i r).
Proof. exact (@lem1059878 (term34 A c i r)). Qed.
Lemma lem1059885 {A : Type'} : (@ZRECSPACE A (@ZBOT A)) = True.
Proof. exact (EQ_MP (@lem1059817 A) (@lem1059816 A)). Qed.
Lemma lem1059886 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term37 A c i r) = (term37 A c i r).
Proof. exact (eq_refl (term37 A c i r)). Qed.
Lemma lem1059887 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term38 A c i r) = (term39 A c i r).
Proof. exact (MK_COMB (@lem1059886 A c i r) (@lem1059885 A)). Qed.
Lemma lem1059889 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1059890 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term39 A c i r) = (term40 A c i r).
Proof. exact (@lem1059889 (term40 A c i r)). Qed.
Lemma lem1059891 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term38 A c i r) = (term40 A c i r).
Proof. exact (TRANS (@lem1059887 A c i r) (@lem1059890 A c i r)). Qed.
Lemma lem1059892 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1059893 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term41 A c i r) = (term42 A c i r).
Proof. exact (MK_COMB (@lem1059892) (@lem1059891 A c i r)). Qed.
Lemma lem1059895 {A : Type'} (c : nat) (i : A) (r : type1600 A) : ((@ZCONSTR A c i r) = (@ZBOT A)) = False.
Proof. exact (@lem1059828 A c i r (@lem1059827 A c i r)). Qed.
Lemma lem1059896 {A : Type'} (c : nat) (i : A) (r : type1600 A) : ((@ZCONSTR A c i r) = (@ZBOT A)) = False.
Proof. exact (@lem1059895 A c i r). Qed.
Lemma lem1059897 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((term33 A c i r) = (@ZBOT A)) = False.
Proof. exact (@lem1059896 A c i (term43 A r)). Qed.
Lemma lem1059898 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term34 A c i r) = (term44 A c i r).
Proof. exact (MK_COMB (@lem1059893 A c i r) (@lem1059897 A c i r)). Qed.
Lemma lem1059900 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1059901 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term44 A c i r) = (term45 A c i r).
Proof. exact (@lem1059900 (term40 A c i r)). Qed.
Lemma lem1059902 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term34 A c i r) = (term45 A c i r).
Proof. exact (TRANS (@lem1059898 A c i r) (@lem1059901 A c i r)). Qed.
Lemma lem1059903 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1059904 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term36 A c i r) = (term46 A c i r).
Proof. exact (MK_COMB (@lem1059903) (@lem1059902 A c i r)). Qed.
Lemma lem1059906 (t : Prop) : (term47 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1059907 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term46 A c i r) = (term40 A c i r).
Proof. exact (@lem1059906 (term40 A c i r)). Qed.
Lemma lem1059908 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term36 A c i r) = (term40 A c i r).
Proof. exact (TRANS (@lem1059904 A c i r) (@lem1059907 A c i r)). Qed.
Lemma lem1059909 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term35 A c i r) = (term40 A c i r).
Proof. exact (TRANS (@lem1059879 A c i r) (@lem1059908 A c i r)). Qed.
Lemma lem1059910 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term40 A c i r) = (term35 A c i r).
Proof. exact (SYM (@lem1059909 A c i r)). Qed.
Lemma lem1059912 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term6 A c i r.
Proof. exact (EQ_MP (@lem1059802 A c i r) (@lem1059801 A c i r)). Qed.
Lemma lem1059913 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term6 A c i r.
Proof. exact (@lem1059912 A c i r). Qed.
Lemma lem1059914 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term48 A c i r.
Proof. exact (@lem1059913 A c i (term43 A r)). Qed.
Lemma lem1059920 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term49 A r) = r).
Proof. exact (@axiom_10 A r). Qed.
Lemma lem1059921 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term49 A r) = r).
Proof. exact (@lem1059920 A r). Qed.
Lemma lem1059922 {A : Type'} (r : type1614 A) (n : nat) : (term50 A r n) = ((term51 A r n) = (term52 A r n)).
Proof. exact (@lem1059921 A (term52 A r n)). Qed.
Lemma lem1059926 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1059927 {A : Type'} (f : type1600 A) (y : nat) : (term54 A f y) = (f y).
Proof. exact (@lem1059926 nat (type1597 A) f y). Qed.
Lemma lem1059928 {A : Type'} (r : type1614 A) (n : nat) : (term55 A r n) = (term52 A r n).
Proof. exact (@lem1059927 A (term43 A r) n). Qed.
Lemma lem1059929 {A : Type'} (r : type1614 A) (n : nat) : (term52 A r n) = (term56 A r n).
Proof. exact (eq_refl (term52 A r n)). Qed.
Lemma lem1059930 {A : Type'} (r : type1614 A) : (term57 A r) = (term43 A r).
Proof. exact (fun_ext (fun n : nat => @lem1059929 A r n)). Qed.
Lemma lem1059931 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1059932 {A : Type'} (r : type1614 A) (n : nat) : (term55 A r n) = (term52 A r n).
Proof. exact (MK_COMB (@lem1059930 A r) (@lem1059931 n)). Qed.
Lemma lem1059933 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1059934 {A : Type'} (r : type1614 A) (n : nat) : (term58 A r n) = (term59 A r n).
Proof. exact (MK_COMB (@lem1059933 A) (@lem1059932 A r n)). Qed.
Lemma lem1059935 {A : Type'} (r : type1614 A) (n : nat) : (term52 A r n) = (term56 A r n).
Proof. exact (eq_refl (term52 A r n)). Qed.
Lemma lem1059936 {A : Type'} (r : type1614 A) (n : nat) : ((term55 A r n) = (term52 A r n)) = ((term52 A r n) = (term56 A r n)).
Proof. exact (MK_COMB (@lem1059934 A r n) (@lem1059935 A r n)). Qed.
Lemma lem1059937 {A : Type'} (r : type1614 A) (n : nat) : (term52 A r n) = (term56 A r n).
Proof. exact (EQ_MP (@lem1059936 A r n) (@lem1059928 A r n)). Qed.
Lemma lem1059938 {A : Type'} : (@_mk_rec A) = (@_mk_rec A).
Proof. exact (eq_refl (@_mk_rec A)). Qed.
Lemma lem1059939 {A : Type'} (r : type1614 A) (n : nat) : (term60 A r n) = (term61 A r n).
Proof. exact (MK_COMB (@lem1059938 A) (@lem1059937 A r n)). Qed.
Lemma lem1059941 {A : Type'} (a : recspace A) : (term62 A a) = a.
Proof. exact (@axiom_9 A a). Qed.
Lemma lem1059942 {A : Type'} (a : recspace A) : (term62 A a) = a.
Proof. exact (@lem1059941 A a). Qed.
Lemma lem1059943 {A : Type'} (r : type1614 A) (n : nat) : (term61 A r n) = (r n).
Proof. exact (@lem1059942 A (r n)). Qed.
Lemma lem1059944 {A : Type'} (r : type1614 A) (n : nat) : (term60 A r n) = (r n).
Proof. exact (TRANS (@lem1059939 A r n) (@lem1059943 A r n)). Qed.
Lemma lem1059945 {A : Type'} : (@_dest_rec A) = (@_dest_rec A).
Proof. exact (eq_refl (@_dest_rec A)). Qed.
Lemma lem1059946 {A : Type'} (r : type1614 A) (n : nat) : (term51 A r n) = (term56 A r n).
Proof. exact (MK_COMB (@lem1059945 A) (@lem1059944 A r n)). Qed.
Lemma lem1059947 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1059948 {A : Type'} (r : type1614 A) (n : nat) : (term63 A r n) = (term64 A r n).
Proof. exact (MK_COMB (@lem1059947 A) (@lem1059946 A r n)). Qed.
Lemma lem1059950 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1059951 {A : Type'} (f : type1600 A) (y : nat) : (term54 A f y) = (f y).
Proof. exact (@lem1059950 nat (type1597 A) f y). Qed.
Lemma lem1059952 {A : Type'} (r : type1614 A) (n : nat) : (term55 A r n) = (term52 A r n).
Proof. exact (@lem1059951 A (term43 A r) n). Qed.
Lemma lem1059953 {A : Type'} (r : type1614 A) (n : nat) : (term52 A r n) = (term56 A r n).
Proof. exact (eq_refl (term52 A r n)). Qed.
Lemma lem1059954 {A : Type'} (r : type1614 A) : (term57 A r) = (term43 A r).
Proof. exact (fun_ext (fun n : nat => @lem1059953 A r n)). Qed.
Lemma lem1059955 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1059956 {A : Type'} (r : type1614 A) (n : nat) : (term55 A r n) = (term52 A r n).
Proof. exact (MK_COMB (@lem1059954 A r) (@lem1059955 n)). Qed.
Lemma lem1059957 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1059958 {A : Type'} (r : type1614 A) (n : nat) : (term58 A r n) = (term59 A r n).
Proof. exact (MK_COMB (@lem1059957 A) (@lem1059956 A r n)). Qed.
Lemma lem1059959 {A : Type'} (r : type1614 A) (n : nat) : (term52 A r n) = (term56 A r n).
Proof. exact (eq_refl (term52 A r n)). Qed.
Lemma lem1059960 {A : Type'} (r : type1614 A) (n : nat) : ((term55 A r n) = (term52 A r n)) = ((term52 A r n) = (term56 A r n)).
Proof. exact (MK_COMB (@lem1059958 A r n) (@lem1059959 A r n)). Qed.
Lemma lem1059961 {A : Type'} (r : type1614 A) (n : nat) : (term52 A r n) = (term56 A r n).
Proof. exact (EQ_MP (@lem1059960 A r n) (@lem1059952 A r n)). Qed.
Lemma lem1059962 {A : Type'} (r : type1614 A) (n : nat) : ((term51 A r n) = (term52 A r n)) = ((term56 A r n) = (term56 A r n)).
Proof. exact (MK_COMB (@lem1059948 A r n) (@lem1059961 A r n)). Qed.
Lemma lem1059964 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1059965 {A : Type'} (x : type1597 A) : (x = x) = True.
Proof. exact (@lem1059964 (type1597 A) x). Qed.
Lemma lem1059966 {A : Type'} (r : type1614 A) (n : nat) : ((term56 A r n) = (term56 A r n)) = True.
Proof. exact (@lem1059965 A (term56 A r n)). Qed.
Lemma lem1059967 {A : Type'} (r : type1614 A) (n : nat) : ((term51 A r n) = (term52 A r n)) = True.
Proof. exact (TRANS (@lem1059962 A r n) (@lem1059966 A r n)). Qed.
Lemma lem1059968 {A : Type'} (r : type1614 A) (n : nat) : (term50 A r n) = True.
Proof. exact (TRANS (@lem1059922 A r n) (@lem1059967 A r n)). Qed.
Lemma lem1059969 {A : Type'} (r : type1614 A) : (term65 A r) = term66.
Proof. exact (fun_ext (fun n : nat => @lem1059968 A r n)). Qed.
Lemma lem1059970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1059971 {A : Type'} (r : type1614 A) : (term67 A r) = term68.
Proof. exact (MK_COMB (@lem1059970) (@lem1059969 A r)). Qed.
Lemma lem1059973 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1059974 (t : Prop) : (term70 t) = t.
Proof. exact (@lem1059973 nat t). Qed.
Lemma lem1059975 : term68 = True.
Proof. exact (@lem1059974 True). Qed.
Lemma lem1059976 {A : Type'} (r : type1614 A) : (term67 A r) = True.
Proof. exact (TRANS (@lem1059971 A r) (@lem1059975)). Qed.
Lemma lem1059977 {A : Type'} (r : type1614 A) : True = (term67 A r).
Proof. exact (SYM (@lem1059976 A r)). Qed.
Lemma lem1059978 {A : Type'} (r : type1614 A) : term67 A r.
Proof. exact (EQ_MP (@lem1059977 A r) (@lem0)). Qed.
Lemma lem1059979 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term40 A c i r.
Proof. exact (@lem1059914 A c i r (@lem1059978 A r)). Qed.
Lemma lem1059980 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term35 A c i r.
Proof. exact (EQ_MP (@lem1059910 A c i r) (@lem1059979 A c i r)). Qed.
Lemma lem1059981 {A : Type'} (c : nat) (i : A) (r : type1614 A) (h1 : (term27 A c i r) = (@_mk_rec A (@ZBOT A))) : False.
Proof. exact (@lem1059980 A c i r (@lem1059876 A c i r h1)). Qed.
Lemma lem1059982 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term71 A c i r.
Proof. exact (fun h0 : (term27 A c i r) = (@_mk_rec A (@ZBOT A)) => @lem1059981 A c i r h0). Qed.
Lemma lem1059983 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term71 A c i r) = (term31 A c i r).
Proof. exact (@lem69 ((term27 A c i r) = (@_mk_rec A (@ZBOT A)))). Qed.
Lemma lem1059984 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term31 A c i r.
Proof. exact (EQ_MP (@lem1059983 A c i r) (@lem1059982 A c i r)). Qed.
Lemma lem1059985 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term30 A c i r.
Proof. exact (EQ_MP (@lem1059870 A c i r) (@lem1059984 A c i r)). Qed.
Lemma lem1059990 {A : Type'} (c : nat) (i : A) : term72 A c i.
Proof. exact (fun r : type1614 A => @lem1059985 A c i r). Qed.
Lemma lem1059995 {A : Type'} (c : nat) : term73 A c.
Proof. exact (fun i : A => @lem1059990 A c i). Qed.
Lemma lem1060000 {A : Type'} : term74 A.
Proof. exact (fun c : nat => @lem1059995 A c). Qed.
