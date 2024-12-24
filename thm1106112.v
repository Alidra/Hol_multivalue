Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1106112_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1105812 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1105813 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1105814 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1105813 A B f) (@lem1105812 A B f)). Qed.
Lemma lem1105815 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1105814 A B f y). Qed.
Lemma lem1105816 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1105819 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : FILTER' = (term4 _25594 _18018).
Proof. exact (h1). Qed.
Lemma lem1105820 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105821 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P) = (term5 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105819 _25594 FILTER' _18018 h1) (@lem1105820 _25594 P)). Qed.
Lemma lem1105823 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1105816 A B f y) (@lem1105815 A B f y)). Qed.
Lemma lem1105824 {_25594 : Type'} (f : type662 _25594) (y : _25594 -> Prop) : (term6 _25594 f y) = (f y).
Proof. exact (@lem1105823 (_25594 -> Prop) (type1138 _25594) f y). Qed.
Lemma lem1105825 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term7 _25594 _18018 P) = (term5 _25594 _18018 P).
Proof. exact (@lem1105824 _25594 (term4 _25594 _18018) P). Qed.
Lemma lem1105826 {_25594 : Type'} (_18018 : type1130 _25594) (_18016 : _25594 -> Prop) : (term5 _25594 _18018 _18016) = (term8 _25594 _18018 _18016).
Proof. exact (eq_refl (term5 _25594 _18018 _18016)). Qed.
Lemma lem1105827 {_25594 : Type'} (_18018 : type1130 _25594) : (term9 _25594 _18018) = (term4 _25594 _18018).
Proof. exact (fun_ext (fun _18016 : _25594 -> Prop => @lem1105826 _25594 _18018 _18016)). Qed.
Lemma lem1105828 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105829 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term7 _25594 _18018 P) = (term5 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105827 _25594 _18018) (@lem1105828 _25594 P)). Qed.
Lemma lem1105830 {_25594 : Type'} : (@eq ((list _25594) -> list _25594)) = (@eq ((list _25594) -> list _25594)).
Proof. exact (eq_refl (@eq ((list _25594) -> list _25594))). Qed.
Lemma lem1105831 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term10 _25594 _18018 P) = (term11 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105830 _25594) (@lem1105829 _25594 _18018 P)). Qed.
Lemma lem1105832 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term5 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (eq_refl (term5 _25594 _18018 P)). Qed.
Lemma lem1105833 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : ((term7 _25594 _18018 P) = (term5 _25594 _18018 P)) = ((term5 _25594 _18018 P) = (term8 _25594 _18018 P)).
Proof. exact (MK_COMB (@lem1105831 _25594 _18018 P) (@lem1105832 _25594 _18018 P)). Qed.
Lemma lem1105834 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term5 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (EQ_MP (@lem1105833 _25594 _18018 P) (@lem1105825 _25594 _18018 P)). Qed.
Lemma lem1105835 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P) = (term8 _25594 _18018 P).
Proof. exact (TRANS (@lem1105821 _25594 P FILTER' _18018 h1) (@lem1105834 _25594 _18018 P)). Qed.
Lemma lem1105836 {_25594 : Type'} : (@nil _25594) = (@nil _25594).
Proof. exact (eq_refl (@nil _25594)). Qed.
Lemma lem1105837 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P (@nil _25594)) = (term12 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105835 _25594 P FILTER' _18018 h1) (@lem1105836 _25594)). Qed.
Lemma lem1105839 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1105816 A B f y) (@lem1105815 A B f y)). Qed.
Lemma lem1105840 {_25594 : Type'} (f : type1138 _25594) (y : list _25594) : (term13 _25594 f y) = (f y).
Proof. exact (@lem1105839 (list _25594) (list _25594) f y). Qed.
Lemma lem1105841 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term14 _25594 _18018 P) = (term12 _25594 _18018 P).
Proof. exact (@lem1105840 _25594 (term8 _25594 _18018 P) (@nil _25594)). Qed.
Lemma lem1105842 {_25594 : Type'} (_18018 : type1130 _25594) (_18017 : list _25594) (P : _25594 -> Prop) : (term15 _25594 _18018 P _18017) = (_18018 _18017 P).
Proof. exact (eq_refl (term15 _25594 _18018 P _18017)). Qed.
Lemma lem1105843 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term16 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (fun_ext (fun _18017 : list _25594 => @lem1105842 _25594 _18018 _18017 P)). Qed.
Lemma lem1105844 {_25594 : Type'} : (@nil _25594) = (@nil _25594).
Proof. exact (eq_refl (@nil _25594)). Qed.
Lemma lem1105845 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term14 _25594 _18018 P) = (term12 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105843 _25594 _18018 P) (@lem1105844 _25594)). Qed.
Lemma lem1105846 {_25594 : Type'} : (@eq (list _25594)) = (@eq (list _25594)).
Proof. exact (eq_refl (@eq (list _25594))). Qed.
Lemma lem1105847 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term17 _25594 _18018 P) = (term18 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105846 _25594) (@lem1105845 _25594 _18018 P)). Qed.
Lemma lem1105848 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term12 _25594 _18018 P) = (_18018 (@nil _25594) P).
Proof. exact (eq_refl (term12 _25594 _18018 P)). Qed.
Lemma lem1105849 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : ((term14 _25594 _18018 P) = (term12 _25594 _18018 P)) = ((term12 _25594 _18018 P) = (_18018 (@nil _25594) P)).
Proof. exact (MK_COMB (@lem1105847 _25594 _18018 P) (@lem1105848 _25594 _18018 P)). Qed.
Lemma lem1105850 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term12 _25594 _18018 P) = (_18018 (@nil _25594) P).
Proof. exact (EQ_MP (@lem1105849 _25594 _18018 P) (@lem1105841 _25594 _18018 P)). Qed.
Lemma lem1105851 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P (@nil _25594)) = (_18018 (@nil _25594) P).
Proof. exact (TRANS (@lem1105837 _25594 P FILTER' _18018 h1) (@lem1105850 _25594 _18018 P)). Qed.
Lemma lem1105852 {_25594 : Type'} : (@eq (list _25594)) = (@eq (list _25594)).
Proof. exact (eq_refl (@eq (list _25594))). Qed.
Lemma lem1105853 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term19 _25594 FILTER' P) = (term20 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105852 _25594) (@lem1105851 _25594 P FILTER' _18018 h1)). Qed.
Lemma lem1105854 {_25594 : Type'} : (@nil _25594) = (@nil _25594).
Proof. exact (eq_refl (@nil _25594)). Qed.
Lemma lem1105855 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : ((FILTER' P (@nil _25594)) = (@nil _25594)) = ((_18018 (@nil _25594) P) = (@nil _25594)).
Proof. exact (MK_COMB (@lem1105853 _25594 P FILTER' _18018 h1) (@lem1105854 _25594)). Qed.
Lemma lem1105856 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term21 _25594 FILTER') = (term22 _25594 _18018).
Proof. exact (fun_ext (fun P : _25594 -> Prop => @lem1105855 _25594 P FILTER' _18018 h1)). Qed.
Lemma lem1105857 {_25594 : Type'} : (@all (_25594 -> Prop)) = (@all (_25594 -> Prop)).
Proof. exact (eq_refl (@all (_25594 -> Prop))). Qed.
Lemma lem1105858 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term23 _25594 FILTER') = (term24 _25594 _18018).
Proof. exact (MK_COMB (@lem1105857 _25594) (@lem1105856 _25594 FILTER' _18018 h1)). Qed.
Lemma lem1105859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1105860 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term25 _25594 FILTER') = (term26 _25594 _18018).
Proof. exact (MK_COMB (@lem1105859) (@lem1105858 _25594 FILTER' _18018 h1)). Qed.
Lemma lem1105862 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : FILTER' = (term4 _25594 _18018).
Proof. exact (h1). Qed.
Lemma lem1105863 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105864 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P) = (term5 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105862 _25594 FILTER' _18018 h1) (@lem1105863 _25594 P)). Qed.
Lemma lem1105866 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1105816 A B f y) (@lem1105815 A B f y)). Qed.
Lemma lem1105867 {_25594 : Type'} (f : type662 _25594) (y : _25594 -> Prop) : (term6 _25594 f y) = (f y).
Proof. exact (@lem1105866 (_25594 -> Prop) (type1138 _25594) f y). Qed.
Lemma lem1105868 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term7 _25594 _18018 P) = (term5 _25594 _18018 P).
Proof. exact (@lem1105867 _25594 (term4 _25594 _18018) P). Qed.
Lemma lem1105869 {_25594 : Type'} (_18018 : type1130 _25594) (_18016 : _25594 -> Prop) : (term5 _25594 _18018 _18016) = (term8 _25594 _18018 _18016).
Proof. exact (eq_refl (term5 _25594 _18018 _18016)). Qed.
Lemma lem1105870 {_25594 : Type'} (_18018 : type1130 _25594) : (term9 _25594 _18018) = (term4 _25594 _18018).
Proof. exact (fun_ext (fun _18016 : _25594 -> Prop => @lem1105869 _25594 _18018 _18016)). Qed.
Lemma lem1105871 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105872 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term7 _25594 _18018 P) = (term5 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105870 _25594 _18018) (@lem1105871 _25594 P)). Qed.
Lemma lem1105873 {_25594 : Type'} : (@eq ((list _25594) -> list _25594)) = (@eq ((list _25594) -> list _25594)).
Proof. exact (eq_refl (@eq ((list _25594) -> list _25594))). Qed.
Lemma lem1105874 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term10 _25594 _18018 P) = (term11 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105873 _25594) (@lem1105872 _25594 _18018 P)). Qed.
Lemma lem1105875 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term5 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (eq_refl (term5 _25594 _18018 P)). Qed.
Lemma lem1105876 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : ((term7 _25594 _18018 P) = (term5 _25594 _18018 P)) = ((term5 _25594 _18018 P) = (term8 _25594 _18018 P)).
Proof. exact (MK_COMB (@lem1105874 _25594 _18018 P) (@lem1105875 _25594 _18018 P)). Qed.
Lemma lem1105877 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term5 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (EQ_MP (@lem1105876 _25594 _18018 P) (@lem1105868 _25594 _18018 P)). Qed.
Lemma lem1105878 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P) = (term8 _25594 _18018 P).
Proof. exact (TRANS (@lem1105864 _25594 P FILTER' _18018 h1) (@lem1105877 _25594 _18018 P)). Qed.
Lemma lem1105879 {_25594 : Type'} (h : _25594) (t : list _25594) : (@cons _25594 h t) = (@cons _25594 h t).
Proof. exact (eq_refl (@cons _25594 h t)). Qed.
Lemma lem1105880 {_25594 : Type'} (P : _25594 -> Prop) (h : _25594) (t : list _25594) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term27 _25594 FILTER' P h t) = (term28 _25594 _18018 P h t).
Proof. exact (MK_COMB (@lem1105878 _25594 P FILTER' _18018 h1) (@lem1105879 _25594 h t)). Qed.
Lemma lem1105882 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1105816 A B f y) (@lem1105815 A B f y)). Qed.
Lemma lem1105883 {_25594 : Type'} (f : type1138 _25594) (y : list _25594) : (term13 _25594 f y) = (f y).
Proof. exact (@lem1105882 (list _25594) (list _25594) f y). Qed.
Lemma lem1105884 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) (h : _25594) (t : list _25594) : (term29 _25594 _18018 P h t) = (term28 _25594 _18018 P h t).
Proof. exact (@lem1105883 _25594 (term8 _25594 _18018 P) (@cons _25594 h t)). Qed.
Lemma lem1105885 {_25594 : Type'} (_18018 : type1130 _25594) (_18017 : list _25594) (P : _25594 -> Prop) : (term15 _25594 _18018 P _18017) = (_18018 _18017 P).
Proof. exact (eq_refl (term15 _25594 _18018 P _18017)). Qed.
Lemma lem1105886 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term16 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (fun_ext (fun _18017 : list _25594 => @lem1105885 _25594 _18018 _18017 P)). Qed.
Lemma lem1105887 {_25594 : Type'} (h : _25594) (t : list _25594) : (@cons _25594 h t) = (@cons _25594 h t).
Proof. exact (eq_refl (@cons _25594 h t)). Qed.
Lemma lem1105888 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) (h : _25594) (t : list _25594) : (term29 _25594 _18018 P h t) = (term28 _25594 _18018 P h t).
Proof. exact (MK_COMB (@lem1105886 _25594 _18018 P) (@lem1105887 _25594 h t)). Qed.
Lemma lem1105889 {_25594 : Type'} : (@eq (list _25594)) = (@eq (list _25594)).
Proof. exact (eq_refl (@eq (list _25594))). Qed.
Lemma lem1105890 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) (h : _25594) (t : list _25594) : (term30 _25594 _18018 P h t) = (term31 _25594 _18018 P h t).
Proof. exact (MK_COMB (@lem1105889 _25594) (@lem1105888 _25594 _18018 P h t)). Qed.
Lemma lem1105891 {_25594 : Type'} (_18018 : type1130 _25594) (h : _25594) (t : list _25594) (P : _25594 -> Prop) : (term28 _25594 _18018 P h t) = (term32 _25594 _18018 h t P).
Proof. exact (eq_refl (term28 _25594 _18018 P h t)). Qed.
Lemma lem1105892 {_25594 : Type'} (_18018 : type1130 _25594) (h : _25594) (t : list _25594) (P : _25594 -> Prop) : ((term29 _25594 _18018 P h t) = (term28 _25594 _18018 P h t)) = ((term28 _25594 _18018 P h t) = (term32 _25594 _18018 h t P)).
Proof. exact (MK_COMB (@lem1105890 _25594 _18018 P h t) (@lem1105891 _25594 _18018 h t P)). Qed.
Lemma lem1105893 {_25594 : Type'} (_18018 : type1130 _25594) (h : _25594) (t : list _25594) (P : _25594 -> Prop) : (term28 _25594 _18018 P h t) = (term32 _25594 _18018 h t P).
Proof. exact (EQ_MP (@lem1105892 _25594 _18018 h t P) (@lem1105884 _25594 _18018 P h t)). Qed.
Lemma lem1105894 {_25594 : Type'} (h : _25594) (t : list _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term27 _25594 FILTER' P h t) = (term32 _25594 _18018 h t P).
Proof. exact (TRANS (@lem1105880 _25594 P h t FILTER' _18018 h1) (@lem1105893 _25594 _18018 h t P)). Qed.
Lemma lem1105895 {_25594 : Type'} : (@eq (list _25594)) = (@eq (list _25594)).
Proof. exact (eq_refl (@eq (list _25594))). Qed.
Lemma lem1105896 {_25594 : Type'} (h : _25594) (t : list _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term33 _25594 FILTER' P h t) = (term34 _25594 _18018 h t P).
Proof. exact (MK_COMB (@lem1105895 _25594) (@lem1105894 _25594 h t P FILTER' _18018 h1)). Qed.
Lemma lem1105898 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : FILTER' = (term4 _25594 _18018).
Proof. exact (h1). Qed.
Lemma lem1105899 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105900 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P) = (term5 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105898 _25594 FILTER' _18018 h1) (@lem1105899 _25594 P)). Qed.
Lemma lem1105902 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1105816 A B f y) (@lem1105815 A B f y)). Qed.
Lemma lem1105903 {_25594 : Type'} (f : type662 _25594) (y : _25594 -> Prop) : (term6 _25594 f y) = (f y).
Proof. exact (@lem1105902 (_25594 -> Prop) (type1138 _25594) f y). Qed.
Lemma lem1105904 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term7 _25594 _18018 P) = (term5 _25594 _18018 P).
Proof. exact (@lem1105903 _25594 (term4 _25594 _18018) P). Qed.
Lemma lem1105905 {_25594 : Type'} (_18018 : type1130 _25594) (_18016 : _25594 -> Prop) : (term5 _25594 _18018 _18016) = (term8 _25594 _18018 _18016).
Proof. exact (eq_refl (term5 _25594 _18018 _18016)). Qed.
Lemma lem1105906 {_25594 : Type'} (_18018 : type1130 _25594) : (term9 _25594 _18018) = (term4 _25594 _18018).
Proof. exact (fun_ext (fun _18016 : _25594 -> Prop => @lem1105905 _25594 _18018 _18016)). Qed.
Lemma lem1105907 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105908 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term7 _25594 _18018 P) = (term5 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105906 _25594 _18018) (@lem1105907 _25594 P)). Qed.
Lemma lem1105909 {_25594 : Type'} : (@eq ((list _25594) -> list _25594)) = (@eq ((list _25594) -> list _25594)).
Proof. exact (eq_refl (@eq ((list _25594) -> list _25594))). Qed.
Lemma lem1105910 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term10 _25594 _18018 P) = (term11 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105909 _25594) (@lem1105908 _25594 _18018 P)). Qed.
Lemma lem1105911 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term5 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (eq_refl (term5 _25594 _18018 P)). Qed.
Lemma lem1105912 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : ((term7 _25594 _18018 P) = (term5 _25594 _18018 P)) = ((term5 _25594 _18018 P) = (term8 _25594 _18018 P)).
Proof. exact (MK_COMB (@lem1105910 _25594 _18018 P) (@lem1105911 _25594 _18018 P)). Qed.
Lemma lem1105913 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term5 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (EQ_MP (@lem1105912 _25594 _18018 P) (@lem1105904 _25594 _18018 P)). Qed.
Lemma lem1105914 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P) = (term8 _25594 _18018 P).
Proof. exact (TRANS (@lem1105900 _25594 P FILTER' _18018 h1) (@lem1105913 _25594 _18018 P)). Qed.
Lemma lem1105915 {_25594 : Type'} (t : list _25594) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1105916 {_25594 : Type'} (P : _25594 -> Prop) (t : list _25594) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P t) = (term15 _25594 _18018 P t).
Proof. exact (MK_COMB (@lem1105914 _25594 P FILTER' _18018 h1) (@lem1105915 _25594 t)). Qed.
Lemma lem1105918 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1105816 A B f y) (@lem1105815 A B f y)). Qed.
Lemma lem1105919 {_25594 : Type'} (f : type1138 _25594) (y : list _25594) : (term13 _25594 f y) = (f y).
Proof. exact (@lem1105918 (list _25594) (list _25594) f y). Qed.
Lemma lem1105920 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) (t : list _25594) : (term35 _25594 _18018 P t) = (term15 _25594 _18018 P t).
Proof. exact (@lem1105919 _25594 (term8 _25594 _18018 P) t). Qed.
Lemma lem1105921 {_25594 : Type'} (_18018 : type1130 _25594) (_18017 : list _25594) (P : _25594 -> Prop) : (term15 _25594 _18018 P _18017) = (_18018 _18017 P).
Proof. exact (eq_refl (term15 _25594 _18018 P _18017)). Qed.
Lemma lem1105922 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term16 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (fun_ext (fun _18017 : list _25594 => @lem1105921 _25594 _18018 _18017 P)). Qed.
Lemma lem1105923 {_25594 : Type'} (t : list _25594) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1105924 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) (t : list _25594) : (term35 _25594 _18018 P t) = (term15 _25594 _18018 P t).
Proof. exact (MK_COMB (@lem1105922 _25594 _18018 P) (@lem1105923 _25594 t)). Qed.
Lemma lem1105925 {_25594 : Type'} : (@eq (list _25594)) = (@eq (list _25594)).
Proof. exact (eq_refl (@eq (list _25594))). Qed.
Lemma lem1105926 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) (t : list _25594) : (term36 _25594 _18018 P t) = (term37 _25594 _18018 P t).
Proof. exact (MK_COMB (@lem1105925 _25594) (@lem1105924 _25594 _18018 P t)). Qed.
Lemma lem1105927 {_25594 : Type'} (_18018 : type1130 _25594) (t : list _25594) (P : _25594 -> Prop) : (term15 _25594 _18018 P t) = (_18018 t P).
Proof. exact (eq_refl (term15 _25594 _18018 P t)). Qed.
Lemma lem1105928 {_25594 : Type'} (_18018 : type1130 _25594) (t : list _25594) (P : _25594 -> Prop) : ((term35 _25594 _18018 P t) = (term15 _25594 _18018 P t)) = ((term15 _25594 _18018 P t) = (_18018 t P)).
Proof. exact (MK_COMB (@lem1105926 _25594 _18018 P t) (@lem1105927 _25594 _18018 t P)). Qed.
Lemma lem1105929 {_25594 : Type'} (_18018 : type1130 _25594) (t : list _25594) (P : _25594 -> Prop) : (term15 _25594 _18018 P t) = (_18018 t P).
Proof. exact (EQ_MP (@lem1105928 _25594 _18018 t P) (@lem1105920 _25594 _18018 P t)). Qed.
Lemma lem1105930 {_25594 : Type'} (t : list _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P t) = (_18018 t P).
Proof. exact (TRANS (@lem1105916 _25594 P t FILTER' _18018 h1) (@lem1105929 _25594 _18018 t P)). Qed.
Lemma lem1105931 {_25594 : Type'} (h : _25594) : (@cons _25594 h) = (@cons _25594 h).
Proof. exact (eq_refl (@cons _25594 h)). Qed.
Lemma lem1105932 {_25594 : Type'} (h : _25594) (t : list _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term38 _25594 h FILTER' P t) = (term39 _25594 h _18018 t P).
Proof. exact (MK_COMB (@lem1105931 _25594 h) (@lem1105930 _25594 t P FILTER' _18018 h1)). Qed.
Lemma lem1105933 {_25594 : Type'} (P : _25594 -> Prop) (h : _25594) : (term40 _25594 P h) = (term40 _25594 P h).
Proof. exact (eq_refl (term40 _25594 P h)). Qed.
Lemma lem1105934 {_25594 : Type'} (h : _25594) (t : list _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term41 _25594 h FILTER' P t) = (term42 _25594 h _18018 t P).
Proof. exact (MK_COMB (@lem1105933 _25594 P h) (@lem1105932 _25594 h t P FILTER' _18018 h1)). Qed.
Lemma lem1105936 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : FILTER' = (term4 _25594 _18018).
Proof. exact (h1). Qed.
Lemma lem1105937 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105938 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P) = (term5 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105936 _25594 FILTER' _18018 h1) (@lem1105937 _25594 P)). Qed.
Lemma lem1105940 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1105816 A B f y) (@lem1105815 A B f y)). Qed.
Lemma lem1105941 {_25594 : Type'} (f : type662 _25594) (y : _25594 -> Prop) : (term6 _25594 f y) = (f y).
Proof. exact (@lem1105940 (_25594 -> Prop) (type1138 _25594) f y). Qed.
Lemma lem1105942 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term7 _25594 _18018 P) = (term5 _25594 _18018 P).
Proof. exact (@lem1105941 _25594 (term4 _25594 _18018) P). Qed.
Lemma lem1105943 {_25594 : Type'} (_18018 : type1130 _25594) (_18016 : _25594 -> Prop) : (term5 _25594 _18018 _18016) = (term8 _25594 _18018 _18016).
Proof. exact (eq_refl (term5 _25594 _18018 _18016)). Qed.
Lemma lem1105944 {_25594 : Type'} (_18018 : type1130 _25594) : (term9 _25594 _18018) = (term4 _25594 _18018).
Proof. exact (fun_ext (fun _18016 : _25594 -> Prop => @lem1105943 _25594 _18018 _18016)). Qed.
Lemma lem1105945 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105946 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term7 _25594 _18018 P) = (term5 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105944 _25594 _18018) (@lem1105945 _25594 P)). Qed.
Lemma lem1105947 {_25594 : Type'} : (@eq ((list _25594) -> list _25594)) = (@eq ((list _25594) -> list _25594)).
Proof. exact (eq_refl (@eq ((list _25594) -> list _25594))). Qed.
Lemma lem1105948 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term10 _25594 _18018 P) = (term11 _25594 _18018 P).
Proof. exact (MK_COMB (@lem1105947 _25594) (@lem1105946 _25594 _18018 P)). Qed.
Lemma lem1105949 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term5 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (eq_refl (term5 _25594 _18018 P)). Qed.
Lemma lem1105950 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : ((term7 _25594 _18018 P) = (term5 _25594 _18018 P)) = ((term5 _25594 _18018 P) = (term8 _25594 _18018 P)).
Proof. exact (MK_COMB (@lem1105948 _25594 _18018 P) (@lem1105949 _25594 _18018 P)). Qed.
Lemma lem1105951 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term5 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (EQ_MP (@lem1105950 _25594 _18018 P) (@lem1105942 _25594 _18018 P)). Qed.
Lemma lem1105952 {_25594 : Type'} (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P) = (term8 _25594 _18018 P).
Proof. exact (TRANS (@lem1105938 _25594 P FILTER' _18018 h1) (@lem1105951 _25594 _18018 P)). Qed.
Lemma lem1105953 {_25594 : Type'} (t : list _25594) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1105954 {_25594 : Type'} (P : _25594 -> Prop) (t : list _25594) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P t) = (term15 _25594 _18018 P t).
Proof. exact (MK_COMB (@lem1105952 _25594 P FILTER' _18018 h1) (@lem1105953 _25594 t)). Qed.
Lemma lem1105956 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1105816 A B f y) (@lem1105815 A B f y)). Qed.
Lemma lem1105957 {_25594 : Type'} (f : type1138 _25594) (y : list _25594) : (term13 _25594 f y) = (f y).
Proof. exact (@lem1105956 (list _25594) (list _25594) f y). Qed.
Lemma lem1105958 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) (t : list _25594) : (term35 _25594 _18018 P t) = (term15 _25594 _18018 P t).
Proof. exact (@lem1105957 _25594 (term8 _25594 _18018 P) t). Qed.
Lemma lem1105959 {_25594 : Type'} (_18018 : type1130 _25594) (_18017 : list _25594) (P : _25594 -> Prop) : (term15 _25594 _18018 P _18017) = (_18018 _18017 P).
Proof. exact (eq_refl (term15 _25594 _18018 P _18017)). Qed.
Lemma lem1105960 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term16 _25594 _18018 P) = (term8 _25594 _18018 P).
Proof. exact (fun_ext (fun _18017 : list _25594 => @lem1105959 _25594 _18018 _18017 P)). Qed.
Lemma lem1105961 {_25594 : Type'} (t : list _25594) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1105962 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) (t : list _25594) : (term35 _25594 _18018 P t) = (term15 _25594 _18018 P t).
Proof. exact (MK_COMB (@lem1105960 _25594 _18018 P) (@lem1105961 _25594 t)). Qed.
Lemma lem1105963 {_25594 : Type'} : (@eq (list _25594)) = (@eq (list _25594)).
Proof. exact (eq_refl (@eq (list _25594))). Qed.
Lemma lem1105964 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) (t : list _25594) : (term36 _25594 _18018 P t) = (term37 _25594 _18018 P t).
Proof. exact (MK_COMB (@lem1105963 _25594) (@lem1105962 _25594 _18018 P t)). Qed.
Lemma lem1105965 {_25594 : Type'} (_18018 : type1130 _25594) (t : list _25594) (P : _25594 -> Prop) : (term15 _25594 _18018 P t) = (_18018 t P).
Proof. exact (eq_refl (term15 _25594 _18018 P t)). Qed.
Lemma lem1105966 {_25594 : Type'} (_18018 : type1130 _25594) (t : list _25594) (P : _25594 -> Prop) : ((term35 _25594 _18018 P t) = (term15 _25594 _18018 P t)) = ((term15 _25594 _18018 P t) = (_18018 t P)).
Proof. exact (MK_COMB (@lem1105964 _25594 _18018 P t) (@lem1105965 _25594 _18018 t P)). Qed.
Lemma lem1105967 {_25594 : Type'} (_18018 : type1130 _25594) (t : list _25594) (P : _25594 -> Prop) : (term15 _25594 _18018 P t) = (_18018 t P).
Proof. exact (EQ_MP (@lem1105966 _25594 _18018 t P) (@lem1105958 _25594 _18018 P t)). Qed.
Lemma lem1105968 {_25594 : Type'} (t : list _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (FILTER' P t) = (_18018 t P).
Proof. exact (TRANS (@lem1105954 _25594 P t FILTER' _18018 h1) (@lem1105967 _25594 _18018 t P)). Qed.
Lemma lem1105969 {_25594 : Type'} (h : _25594) (t : list _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term43 _25594 h FILTER' P t) = (term44 _25594 h _18018 t P).
Proof. exact (MK_COMB (@lem1105934 _25594 h t P FILTER' _18018 h1) (@lem1105968 _25594 t P FILTER' _18018 h1)). Qed.
Lemma lem1105970 {_25594 : Type'} (h : _25594) (t : list _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : ((term27 _25594 FILTER' P h t) = (term43 _25594 h FILTER' P t)) = ((term32 _25594 _18018 h t P) = (term44 _25594 h _18018 t P)).
Proof. exact (MK_COMB (@lem1105896 _25594 h t P FILTER' _18018 h1) (@lem1105969 _25594 h t P FILTER' _18018 h1)). Qed.
Lemma lem1105971 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term45 _25594 h FILTER' P) = (term46 _25594 h _18018 P).
Proof. exact (fun_ext (fun t : list _25594 => @lem1105970 _25594 h t P FILTER' _18018 h1)). Qed.
Lemma lem1105972 {_25594 : Type'} : (@all (list _25594)) = (@all (list _25594)).
Proof. exact (eq_refl (@all (list _25594))). Qed.
Lemma lem1105973 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term47 _25594 h FILTER' P) = (term48 _25594 h _18018 P).
Proof. exact (MK_COMB (@lem1105972 _25594) (@lem1105971 _25594 h P FILTER' _18018 h1)). Qed.
Lemma lem1105974 {_25594 : Type'} (h : _25594) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term49 _25594 h FILTER') = (term50 _25594 h _18018).
Proof. exact (fun_ext (fun P : _25594 -> Prop => @lem1105973 _25594 h P FILTER' _18018 h1)). Qed.
Lemma lem1105975 {_25594 : Type'} : (@all (_25594 -> Prop)) = (@all (_25594 -> Prop)).
Proof. exact (eq_refl (@all (_25594 -> Prop))). Qed.
Lemma lem1105976 {_25594 : Type'} (h : _25594) (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term51 _25594 h FILTER') = (term52 _25594 h _18018).
Proof. exact (MK_COMB (@lem1105975 _25594) (@lem1105974 _25594 h FILTER' _18018 h1)). Qed.
Lemma lem1105977 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term53 _25594 FILTER') = (term54 _25594 _18018).
Proof. exact (fun_ext (fun h : _25594 => @lem1105976 _25594 h FILTER' _18018 h1)). Qed.
Lemma lem1105978 {_25594 : Type'} : (@all _25594) = (@all _25594).
Proof. exact (eq_refl (@all _25594)). Qed.
Lemma lem1105979 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term55 _25594 FILTER') = (term56 _25594 _18018).
Proof. exact (MK_COMB (@lem1105978 _25594) (@lem1105977 _25594 FILTER' _18018 h1)). Qed.
Lemma lem1105980 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term57 _25594 FILTER') = (term58 _25594 _18018).
Proof. exact (MK_COMB (@lem1105860 _25594 FILTER' _18018 h1) (@lem1105979 _25594 FILTER' _18018 h1)). Qed.
Lemma lem1105981 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : (_18018 (@nil _25594)) = (term59 _25594)) : (_18018 (@nil _25594)) = (term59 _25594).
Proof. exact (h1). Qed.
Lemma lem1105982 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105983 {_25594 : Type'} (P : _25594 -> Prop) (_18018 : type1130 _25594) (h1 : (_18018 (@nil _25594)) = (term59 _25594)) : (_18018 (@nil _25594) P) = (term60 _25594 P).
Proof. exact (MK_COMB (@lem1105981 _25594 _18018 h1) (@lem1105982 _25594 P)). Qed.
Lemma lem1105984 {_25594 : Type'} (P : _25594 -> Prop) : (term60 _25594 P) = (@nil _25594).
Proof. exact (eq_refl (term60 _25594 P)). Qed.
Lemma lem1105985 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : (term20 _25594 _18018 P) = (term20 _25594 _18018 P).
Proof. exact (eq_refl (term20 _25594 _18018 P)). Qed.
Lemma lem1105986 {_25594 : Type'} (_18018 : type1130 _25594) (P : _25594 -> Prop) : ((_18018 (@nil _25594) P) = (term60 _25594 P)) = ((_18018 (@nil _25594) P) = (@nil _25594)).
Proof. exact (MK_COMB (@lem1105985 _25594 _18018 P) (@lem1105984 _25594 P)). Qed.
Lemma lem1105987 {_25594 : Type'} (P : _25594 -> Prop) (_18018 : type1130 _25594) (h1 : (_18018 (@nil _25594)) = (term59 _25594)) : (_18018 (@nil _25594) P) = (@nil _25594).
Proof. exact (EQ_MP (@lem1105986 _25594 _18018 P) (@lem1105983 _25594 P _18018 h1)). Qed.
Lemma lem1105988 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : (_18018 (@nil _25594)) = (term59 _25594)) : term24 _25594 _18018.
Proof. exact (fun P : _25594 -> Prop => @lem1105987 _25594 P _18018 h1). Qed.
Lemma lem1105989 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : term61 _25594 _18018.
Proof. exact (h1). Qed.
Lemma lem1105990 {_25594 : Type'} (h : _25594) (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : term62 _25594 _18018 h.
Proof. exact (@lem1105989 _25594 _18018 h1 h). Qed.
Lemma lem1105991 {_25594 : Type'} (h : _25594) (_18018 : type1130 _25594) : (term62 _25594 _18018 h) = (term63 _25594 h _18018).
Proof. exact (eq_refl (term62 _25594 _18018 h)). Qed.
Lemma lem1105992 {_25594 : Type'} (h : _25594) (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : term63 _25594 h _18018.
Proof. exact (EQ_MP (@lem1105991 _25594 h _18018) (@lem1105990 _25594 h _18018 h1)). Qed.
Lemma lem1105993 {_25594 : Type'} (h : _25594) (t : list _25594) (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : term64 _25594 h _18018 t.
Proof. exact (@lem1105992 _25594 h _18018 h1 t). Qed.
Lemma lem1105994 {_25594 : Type'} (h : _25594) (_18018 : type1130 _25594) (t : list _25594) : (term64 _25594 h _18018 t) = ((term65 _25594 _18018 h t) = (term66 _25594 h _18018 t)).
Proof. exact (eq_refl (term64 _25594 h _18018 t)). Qed.
Lemma lem1105995 {_25594 : Type'} (h : _25594) (t : list _25594) (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : (term65 _25594 _18018 h t) = (term66 _25594 h _18018 t).
Proof. exact (EQ_MP (@lem1105994 _25594 h _18018 t) (@lem1105993 _25594 h t _18018 h1)). Qed.
Lemma lem1105996 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1105997 {_25594 : Type'} (h : _25594) (t : list _25594) (P : _25594 -> Prop) (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : (term32 _25594 _18018 h t P) = (term67 _25594 h _18018 t P).
Proof. exact (MK_COMB (@lem1105995 _25594 h t _18018 h1) (@lem1105996 _25594 P)). Qed.
Lemma lem1105998 {_25594 : Type'} (h : _25594) (_18018 : type1130 _25594) (t : list _25594) (P : _25594 -> Prop) : (term67 _25594 h _18018 t P) = (term44 _25594 h _18018 t P).
Proof. exact (eq_refl (term67 _25594 h _18018 t P)). Qed.
Lemma lem1105999 {_25594 : Type'} (_18018 : type1130 _25594) (h : _25594) (t : list _25594) (P : _25594 -> Prop) : (term34 _25594 _18018 h t P) = (term34 _25594 _18018 h t P).
Proof. exact (eq_refl (term34 _25594 _18018 h t P)). Qed.
Lemma lem1106000 {_25594 : Type'} (h : _25594) (_18018 : type1130 _25594) (t : list _25594) (P : _25594 -> Prop) : ((term32 _25594 _18018 h t P) = (term67 _25594 h _18018 t P)) = ((term32 _25594 _18018 h t P) = (term44 _25594 h _18018 t P)).
Proof. exact (MK_COMB (@lem1105999 _25594 _18018 h t P) (@lem1105998 _25594 h _18018 t P)). Qed.
Lemma lem1106001 {_25594 : Type'} (h : _25594) (t : list _25594) (P : _25594 -> Prop) (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : (term32 _25594 _18018 h t P) = (term44 _25594 h _18018 t P).
Proof. exact (EQ_MP (@lem1106000 _25594 h _18018 t P) (@lem1105997 _25594 h t P _18018 h1)). Qed.
Lemma lem1106002 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : term48 _25594 h _18018 P.
Proof. exact (fun t : list _25594 => @lem1106001 _25594 h t P _18018 h1). Qed.
Lemma lem1106003 {_25594 : Type'} (h : _25594) (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : term52 _25594 h _18018.
Proof. exact (fun P : _25594 -> Prop => @lem1106002 _25594 h P _18018 h1). Qed.
Lemma lem1106004 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term61 _25594 _18018) : term56 _25594 _18018.
Proof. exact (fun h : _25594 => @lem1106003 _25594 h _18018 h1). Qed.
Lemma lem1106005 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term68 _25594 _18018.
Proof. exact (h1). Qed.
Lemma lem1106006 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term61 _25594 _18018.
Proof. exact (proj2 (@lem1106005 _25594 _18018 h1)). Qed.
Lemma lem1106007 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : (_18018 (@nil _25594)) = (term59 _25594).
Proof. exact (proj1 (@lem1106005 _25594 _18018 h1)). Qed.
Lemma lem1106008 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : ((_18018 (@nil _25594)) = (term59 _25594)) = (term24 _25594 _18018).
Proof. exact (prop_ext (fun h2 : (_18018 (@nil _25594)) = (term59 _25594) => @lem1105988 _25594 _18018 h2) (fun h2 : term24 _25594 _18018 => @lem1106007 _25594 _18018 h1)). Qed.
Lemma lem1106009 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term24 _25594 _18018.
Proof. exact (EQ_MP (@lem1106008 _25594 _18018 h1) (@lem1106007 _25594 _18018 h1)). Qed.
Lemma lem1106010 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : (term61 _25594 _18018) = (term56 _25594 _18018).
Proof. exact (prop_ext (fun h2 : term61 _25594 _18018 => @lem1106004 _25594 _18018 h2) (fun h2 : term56 _25594 _18018 => @lem1106006 _25594 _18018 h1)). Qed.
Lemma lem1106011 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term56 _25594 _18018.
Proof. exact (EQ_MP (@lem1106010 _25594 _18018 h1) (@lem1106006 _25594 _18018 h1)). Qed.
Lemma lem1106012 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term58 _25594 _18018.
Proof. exact (conj (@lem1106009 _25594 _18018 h1) (@lem1106011 _25594 _18018 h1)). Qed.
Lemma lem1106013 {A Z : Type'} (NIL' : Z) : term69 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1106014 {A Z : Type'} (NIL' : Z) : (term69 A Z NIL') = (term70 A Z NIL').
Proof. exact (eq_refl (term69 A Z NIL')). Qed.
Lemma lem1106015 {A Z : Type'} (NIL' : Z) : term70 A Z NIL'.
Proof. exact (EQ_MP (@lem1106014 A Z NIL') (@lem1106013 A Z NIL')). Qed.
Lemma lem1106016 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term71 A Z NIL' CONS'.
Proof. exact (@lem1106015 A Z NIL' CONS'). Qed.
Lemma lem1106017 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term71 A Z NIL' CONS') = (term72 A Z NIL' CONS').
Proof. exact (eq_refl (term71 A Z NIL' CONS')). Qed.
Lemma lem1106018 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term72 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1106017 A Z NIL' CONS') (@lem1106016 A Z NIL' CONS')). Qed.
Lemma lem1106019 {_25594 : Type'} (NIL' : type683 _25594) (CONS' : type1386 _25594) : term73 _25594 NIL' CONS'.
Proof. exact (@lem1106018 _25594 (type683 _25594) NIL' CONS'). Qed.
Lemma lem1106020 {_25594 : Type'} : term74 _25594.
Proof. exact (@lem1106019 _25594 (term59 _25594) (term75 _25594)). Qed.
Lemma lem1106021 {_25594 : Type'} (a0 : _25594) : (term76 _25594 a0) = (term77 _25594 a0).
Proof. exact (eq_refl (term76 _25594 a0)). Qed.
Lemma lem1106022 {_25594 : Type'} (a1 : list _25594) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1106023 {_25594 : Type'} (a0 : _25594) (a1 : list _25594) : (term78 _25594 a0 a1) = (term79 _25594 a0 a1).
Proof. exact (MK_COMB (@lem1106021 _25594 a0) (@lem1106022 _25594 a1)). Qed.
Lemma lem1106024 {_25594 : Type'} (a1 : list _25594) (a0 : _25594) : (term79 _25594 a0 a1) = (term80 _25594 a0).
Proof. exact (eq_refl (term79 _25594 a0 a1)). Qed.
Lemma lem1106025 {_25594 : Type'} (a1 : list _25594) (a0 : _25594) : (term78 _25594 a0 a1) = (term80 _25594 a0).
Proof. exact (TRANS (@lem1106023 _25594 a0 a1) (@lem1106024 _25594 a1 a0)). Qed.
Lemma lem1106026 {_25594 : Type'} (fn : type1130 _25594) (a1 : list _25594) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1106027 {_25594 : Type'} (a0 : _25594) (fn : type1130 _25594) (a1 : list _25594) : (term81 _25594 a0 fn a1) = (term82 _25594 a0 fn a1).
Proof. exact (MK_COMB (@lem1106025 _25594 a1 a0) (@lem1106026 _25594 fn a1)). Qed.
Lemma lem1106028 {_25594 : Type'} (a0 : _25594) (fn : type1130 _25594) (a1 : list _25594) : (term82 _25594 a0 fn a1) = (term66 _25594 a0 fn a1).
Proof. exact (eq_refl (term82 _25594 a0 fn a1)). Qed.
Lemma lem1106029 {_25594 : Type'} (a0 : _25594) (fn : type1130 _25594) (a1 : list _25594) : (term81 _25594 a0 fn a1) = (term66 _25594 a0 fn a1).
Proof. exact (TRANS (@lem1106027 _25594 a0 fn a1) (@lem1106028 _25594 a0 fn a1)). Qed.
Lemma lem1106030 {_25594 : Type'} (fn : type1130 _25594) (a0 : _25594) (a1 : list _25594) : (term83 _25594 fn a0 a1) = (term83 _25594 fn a0 a1).
Proof. exact (eq_refl (term83 _25594 fn a0 a1)). Qed.
Lemma lem1106031 {_25594 : Type'} (a0 : _25594) (fn : type1130 _25594) (a1 : list _25594) : ((term65 _25594 fn a0 a1) = (term81 _25594 a0 fn a1)) = ((term65 _25594 fn a0 a1) = (term66 _25594 a0 fn a1)).
Proof. exact (MK_COMB (@lem1106030 _25594 fn a0 a1) (@lem1106029 _25594 a0 fn a1)). Qed.
Lemma lem1106032 {_25594 : Type'} (a0 : _25594) (fn : type1130 _25594) : (term84 _25594 a0 fn) = (term85 _25594 a0 fn).
Proof. exact (fun_ext (fun a1 : list _25594 => @lem1106031 _25594 a0 fn a1)). Qed.
Lemma lem1106033 {_25594 : Type'} : (@all (list _25594)) = (@all (list _25594)).
Proof. exact (eq_refl (@all (list _25594))). Qed.
Lemma lem1106034 {_25594 : Type'} (a0 : _25594) (fn : type1130 _25594) : (term86 _25594 a0 fn) = (term63 _25594 a0 fn).
Proof. exact (MK_COMB (@lem1106033 _25594) (@lem1106032 _25594 a0 fn)). Qed.
Lemma lem1106035 {_25594 : Type'} (fn : type1130 _25594) : (term87 _25594 fn) = (term88 _25594 fn).
Proof. exact (fun_ext (fun a0 : _25594 => @lem1106034 _25594 a0 fn)). Qed.
Lemma lem1106036 {_25594 : Type'} : (@all _25594) = (@all _25594).
Proof. exact (eq_refl (@all _25594)). Qed.
Lemma lem1106037 {_25594 : Type'} (fn : type1130 _25594) : (term89 _25594 fn) = (term61 _25594 fn).
Proof. exact (MK_COMB (@lem1106036 _25594) (@lem1106035 _25594 fn)). Qed.
Lemma lem1106038 {_25594 : Type'} (fn : type1130 _25594) : (term90 _25594 fn) = (term90 _25594 fn).
Proof. exact (eq_refl (term90 _25594 fn)). Qed.
Lemma lem1106039 {_25594 : Type'} (fn : type1130 _25594) : (term91 _25594 fn) = (term68 _25594 fn).
Proof. exact (MK_COMB (@lem1106038 _25594 fn) (@lem1106037 _25594 fn)). Qed.
Lemma lem1106040 {_25594 : Type'} : (term92 _25594) = (term93 _25594).
Proof. exact (fun_ext (fun fn : type1130 _25594 => @lem1106039 _25594 fn)). Qed.
Lemma lem1106041 {_25594 : Type'} : (@ex ((list _25594) -> (_25594 -> Prop) -> list _25594)) = (@ex ((list _25594) -> (_25594 -> Prop) -> list _25594)).
Proof. exact (eq_refl (@ex ((list _25594) -> (_25594 -> Prop) -> list _25594))). Qed.
Lemma lem1106042 {_25594 : Type'} : (term74 _25594) = (term94 _25594).
Proof. exact (MK_COMB (@lem1106041 _25594) (@lem1106040 _25594)). Qed.
Lemma lem1106043 {_25594 : Type'} : term94 _25594.
Proof. exact (EQ_MP (@lem1106042 _25594) (@lem1106020 _25594)). Qed.
Lemma lem1106044 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term68 _25594 _18018.
Proof. exact (h1). Qed.
Lemma lem1106045 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term61 _25594 _18018.
Proof. exact (proj2 (@lem1106044 _25594 _18018 h1)). Qed.
Lemma lem1106046 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : (_18018 (@nil _25594)) = (term59 _25594).
Proof. exact (proj1 (@lem1106044 _25594 _18018 h1)). Qed.
Lemma lem1106047 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term68 _25594 _18018.
Proof. exact (conj (@lem1106046 _25594 _18018 h1) (@lem1106045 _25594 _18018 h1)). Qed.
Lemma lem1106048 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term94 _25594.
Proof. exact (ex_intro (term93 _25594) _18018 (@lem1106047 _25594 _18018 h1)). Qed.
Lemma lem1106049 {_25594 : Type'} (h1 : term94 _25594) : term94 _25594.
Proof. exact (h1). Qed.
Lemma lem1106050 {_25594 : Type'} (h1 : term94 _25594) : term94 _25594.
Proof. exact (ex_elim (@lem1106049 _25594 h1) (fun _18018 : type1130 _25594 => fun h0 : term93 _25594 _18018 => @lem1106048 _25594 _18018 h0)). Qed.
Lemma lem1106051 {_25594 : Type'} : (term94 _25594) = (term94 _25594).
Proof. exact (prop_ext (fun h1 : term94 _25594 => @lem1106050 _25594 h1) (fun h1 : term94 _25594 => @lem1106043 _25594)). Qed.
Lemma lem1106052 {_25594 : Type'} : term94 _25594.
Proof. exact (EQ_MP (@lem1106051 _25594) (@lem1106043 _25594)). Qed.
Lemma lem1106053 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term68 _25594 _18018) : term95 _25594.
Proof. exact (ex_intro (term96 _25594) _18018 (@lem1106012 _25594 _18018 h1)). Qed.
Lemma lem1106054 {_25594 : Type'} (h1 : term94 _25594) : term94 _25594.
Proof. exact (h1). Qed.
Lemma lem1106055 {_25594 : Type'} (h1 : term94 _25594) : term95 _25594.
Proof. exact (ex_elim (@lem1106054 _25594 h1) (fun _18018 : type1130 _25594 => fun h0 : term93 _25594 _18018 => @lem1106053 _25594 _18018 h0)). Qed.
Lemma lem1106056 {_25594 : Type'} : (term94 _25594) = (term95 _25594).
Proof. exact (prop_ext (fun h1 : term94 _25594 => @lem1106055 _25594 h1) (fun h1 : term95 _25594 => @lem1106052 _25594)). Qed.
Lemma lem1106057 {_25594 : Type'} : term95 _25594.
Proof. exact (EQ_MP (@lem1106056 _25594) (@lem1106052 _25594)). Qed.
Lemma lem1106058 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term58 _25594 _18018) : term58 _25594 _18018.
Proof. exact (h1). Qed.
Lemma lem1106059 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : FILTER' = (term4 _25594 _18018)) : (term58 _25594 _18018) = (term57 _25594 FILTER').
Proof. exact (SYM (@lem1105980 _25594 FILTER' _18018 h1)). Qed.
Lemma lem1106060 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : term58 _25594 _18018) (h2 : FILTER' = (term4 _25594 _18018)) : term57 _25594 FILTER'.
Proof. exact (EQ_MP (@lem1106059 _25594 FILTER' _18018 h2) (@lem1106058 _25594 _18018 h1)). Qed.
Lemma lem1106061 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : term58 _25594 _18018) (h2 : FILTER' = (term4 _25594 _18018)) : term97 _25594.
Proof. exact (ex_intro (term98 _25594) FILTER' (@lem1106060 _25594 FILTER' _18018 h1 h2)). Qed.
Lemma lem1106062 {_25594 : Type'} (_18018 : type1130 _25594) : (term4 _25594 _18018) = (term4 _25594 _18018).
Proof. exact (eq_refl (term4 _25594 _18018)). Qed.
Lemma lem1106063 {_25594 : Type'} (FILTER' : type662 _25594) (_18018 : type1130 _25594) (h1 : term58 _25594 _18018) : term99 _25594 FILTER' _18018.
Proof. exact (fun h0 : FILTER' = (term4 _25594 _18018) => @lem1106061 _25594 FILTER' _18018 h1 h0). Qed.
Lemma lem1106064 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term58 _25594 _18018) : term100 _25594 _18018.
Proof. exact (@lem1106063 _25594 (term4 _25594 _18018) _18018 h1). Qed.
Lemma lem1106065 {_25594 : Type'} (_18018 : type1130 _25594) (h1 : term58 _25594 _18018) : term97 _25594.
Proof. exact (@lem1106064 _25594 _18018 h1 (@lem1106062 _25594 _18018)). Qed.
Lemma lem1106066 {_25594 : Type'} (h1 : term95 _25594) : term95 _25594.
Proof. exact (h1). Qed.
Lemma lem1106067 {_25594 : Type'} (h1 : term95 _25594) : term97 _25594.
Proof. exact (ex_elim (@lem1106066 _25594 h1) (fun _18018 : type1130 _25594 => fun h0 : term96 _25594 _18018 => @lem1106065 _25594 _18018 h0)). Qed.
Lemma lem1106068 {_25594 : Type'} : (term95 _25594) = (term97 _25594).
Proof. exact (prop_ext (fun h1 : term95 _25594 => @lem1106067 _25594 h1) (fun h1 : term97 _25594 => @lem1106057 _25594)). Qed.
Lemma lem1106069 {_25594 : Type'} : term97 _25594.
Proof. exact (EQ_MP (@lem1106068 _25594) (@lem1106057 _25594)). Qed.
Lemma lem1106070 {_25594 : Type'} : term101 _25594.
Proof. exact (fun _18022 : type1671 => @lem1106069 _25594). Qed.
Lemma lem1106071 {A B : Type'} (P : type1413 A B) : term102 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1106072 {A B : Type'} (P : type1413 A B) : (term102 A B P) = ((term103 A B P) = (term104 A B P)).
Proof. exact (eq_refl (term102 A B P)). Qed.
Lemma lem1106075 {A B : Type'} (P : type1413 A B) : (term103 A B P) = (term104 A B P).
Proof. exact (EQ_MP (@lem1106072 A B P) (@lem1106071 A B P)). Qed.
Lemma lem1106076 {_25594 : Type'} (P : type1262 _25594) : (term105 _25594 P) = (term106 _25594 P).
Proof. exact (@lem1106075 type1671 (type662 _25594) P). Qed.
Lemma lem1106077 {_25594 : Type'} : (term107 _25594) = (term108 _25594).
Proof. exact (@lem1106076 _25594 (term109 _25594)). Qed.
Lemma lem1106078 {_25594 : Type'} (_18022 : type1671) : (term110 _25594 _18022) = (term98 _25594).
Proof. exact (eq_refl (term110 _25594 _18022)). Qed.
Lemma lem1106079 {_25594 : Type'} (FILTER' : type662 _25594) : FILTER' = FILTER'.
Proof. exact (eq_refl FILTER'). Qed.
Lemma lem1106080 {_25594 : Type'} (_18022 : type1671) (FILTER' : type662 _25594) : (term111 _25594 _18022 FILTER') = (term112 _25594 FILTER').
Proof. exact (MK_COMB (@lem1106078 _25594 _18022) (@lem1106079 _25594 FILTER')). Qed.
Lemma lem1106081 {_25594 : Type'} (FILTER' : type662 _25594) : (term112 _25594 FILTER') = (term57 _25594 FILTER').
Proof. exact (eq_refl (term112 _25594 FILTER')). Qed.
Lemma lem1106082 {_25594 : Type'} (_18022 : type1671) (FILTER' : type662 _25594) : (term111 _25594 _18022 FILTER') = (term57 _25594 FILTER').
Proof. exact (TRANS (@lem1106080 _25594 _18022 FILTER') (@lem1106081 _25594 FILTER')). Qed.
Lemma lem1106083 {_25594 : Type'} (_18022 : type1671) : (term113 _25594 _18022) = (term98 _25594).
Proof. exact (fun_ext (fun FILTER' : type662 _25594 => @lem1106082 _25594 _18022 FILTER')). Qed.
Lemma lem1106084 {_25594 : Type'} : (@ex ((_25594 -> Prop) -> (list _25594) -> list _25594)) = (@ex ((_25594 -> Prop) -> (list _25594) -> list _25594)).
Proof. exact (eq_refl (@ex ((_25594 -> Prop) -> (list _25594) -> list _25594))). Qed.
Lemma lem1106085 {_25594 : Type'} (_18022 : type1671) : (term114 _25594 _18022) = (term97 _25594).
Proof. exact (MK_COMB (@lem1106084 _25594) (@lem1106083 _25594 _18022)). Qed.
Lemma lem1106086 {_25594 : Type'} : (term115 _25594) = (term116 _25594).
Proof. exact (fun_ext (fun _18022 : type1671 => @lem1106085 _25594 _18022)). Qed.
Lemma lem1106087 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1106088 {_25594 : Type'} : (term107 _25594) = (term101 _25594).
Proof. exact (MK_COMB (@lem1106087) (@lem1106086 _25594)). Qed.
Lemma lem1106089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1106090 {_25594 : Type'} : (term117 _25594) = (term118 _25594).
Proof. exact (MK_COMB (@lem1106089) (@lem1106088 _25594)). Qed.
Lemma lem1106091 {_25594 : Type'} (_18022 : type1671) : (term110 _25594 _18022) = (term98 _25594).
Proof. exact (eq_refl (term110 _25594 _18022)). Qed.
Lemma lem1106092 {_25594 : Type'} (FILTER' : type1267 _25594) (_18022 : type1671) : (FILTER' _18022) = (FILTER' _18022).
Proof. exact (eq_refl (FILTER' _18022)). Qed.
Lemma lem1106093 {_25594 : Type'} (FILTER' : type1267 _25594) (_18022 : type1671) : (term119 _25594 FILTER' _18022) = (term120 _25594 FILTER' _18022).
Proof. exact (MK_COMB (@lem1106091 _25594 _18022) (@lem1106092 _25594 FILTER' _18022)). Qed.
Lemma lem1106094 {_25594 : Type'} (FILTER' : type1267 _25594) (_18022 : type1671) : (term120 _25594 FILTER' _18022) = (term121 _25594 FILTER' _18022).
Proof. exact (eq_refl (term120 _25594 FILTER' _18022)). Qed.
Lemma lem1106095 {_25594 : Type'} (FILTER' : type1267 _25594) (_18022 : type1671) : (term119 _25594 FILTER' _18022) = (term121 _25594 FILTER' _18022).
Proof. exact (TRANS (@lem1106093 _25594 FILTER' _18022) (@lem1106094 _25594 FILTER' _18022)). Qed.
Lemma lem1106096 {_25594 : Type'} (FILTER' : type1267 _25594) : (term122 _25594 FILTER') = (term123 _25594 FILTER').
Proof. exact (fun_ext (fun _18022 : type1671 => @lem1106095 _25594 FILTER' _18022)). Qed.
Lemma lem1106097 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1106098 {_25594 : Type'} (FILTER' : type1267 _25594) : (term124 _25594 FILTER') = (term125 _25594 FILTER').
Proof. exact (MK_COMB (@lem1106097) (@lem1106096 _25594 FILTER')). Qed.
Lemma lem1106099 {_25594 : Type'} : (term126 _25594) = (term127 _25594).
Proof. exact (fun_ext (fun FILTER' : type1267 _25594 => @lem1106098 _25594 FILTER')). Qed.
Lemma lem1106100 {_25594 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25594 -> Prop) -> (list _25594) -> list _25594)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25594 -> Prop) -> (list _25594) -> list _25594)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25594 -> Prop) -> (list _25594) -> list _25594))). Qed.
Lemma lem1106101 {_25594 : Type'} : (term108 _25594) = (term128 _25594).
Proof. exact (MK_COMB (@lem1106100 _25594) (@lem1106099 _25594)). Qed.
Lemma lem1106102 {_25594 : Type'} : ((term107 _25594) = (term108 _25594)) = ((term101 _25594) = (term128 _25594)).
Proof. exact (MK_COMB (@lem1106090 _25594) (@lem1106101 _25594)). Qed.
Lemma lem1106103 {_25594 : Type'} : (term101 _25594) = (term128 _25594).
Proof. exact (EQ_MP (@lem1106102 _25594) (@lem1106077 _25594)). Qed.
Lemma lem1106104 {_25594 : Type'} : term128 _25594.
Proof. exact (EQ_MP (@lem1106103 _25594) (@lem1106070 _25594)). Qed.
Lemma lem1106106 {A : Type'} : (@ex A) = (term129 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1106107 {_25594 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25594 -> Prop) -> (list _25594) -> list _25594)) = (term130 _25594).
Proof. exact (@lem1106106 (type1267 _25594)). Qed.
Lemma lem1106108 {_25594 : Type'} : (term127 _25594) = (term127 _25594).
Proof. exact (eq_refl (term127 _25594)). Qed.
Lemma lem1106109 {_25594 : Type'} : (term128 _25594) = (term131 _25594).
Proof. exact (MK_COMB (@lem1106107 _25594) (@lem1106108 _25594)). Qed.
Lemma lem1106110 {_25594 : Type'} : (term131 _25594) = (term132 _25594).
Proof. exact (eq_refl (term131 _25594)). Qed.
Lemma lem1106111 {_25594 : Type'} : (term128 _25594) = (term132 _25594).
Proof. exact (TRANS (@lem1106109 _25594) (@lem1106110 _25594)). Qed.
Lemma lem1106112 {_25594 : Type'} : term132 _25594.
Proof. exact (EQ_MP (@lem1106111 _25594) (@lem1106104 _25594)). Qed.
