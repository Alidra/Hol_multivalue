Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_FST_ZIP_term_abbrevs.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import ZIP_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm1097797_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Require Import thm82_spec.
Lemma lem1154805 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1154806 {_27114 : Type'} (P : type1143 _27114) : term0 _27114 P.
Proof. exact (@lem1154805 _27114 P). Qed.
Lemma lem1154807 {_27114 _27116 : Type'} : term1 _27114 _27116.
Proof. exact (@lem1154806 _27114 (term2 _27114 _27116)). Qed.
Lemma lem1154808 {_27114 _27116 : Type'} : (term3 _27114 _27116) = (term4 _27114 _27116).
Proof. exact (eq_refl (term3 _27114 _27116)). Qed.
Lemma lem1154809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1154810 {_27114 _27116 : Type'} : (term5 _27114 _27116) = (term6 _27114 _27116).
Proof. exact (MK_COMB (@lem1154809) (@lem1154808 _27114 _27116)). Qed.
Lemma lem1154811 {_27114 _27116 : Type'} (t : list _27114) : (term7 _27114 _27116 t) = (term8 _27114 _27116 t).
Proof. exact (eq_refl (term7 _27114 _27116 t)). Qed.
Lemma lem1154812 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1154813 {_27114 _27116 : Type'} (t : list _27114) : (term9 _27114 _27116 t) = (term10 _27114 _27116 t).
Proof. exact (MK_COMB (@lem1154812) (@lem1154811 _27114 _27116 t)). Qed.
Lemma lem1154814 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term11 _27114 _27116 h t) = (term12 _27114 _27116 h t).
Proof. exact (eq_refl (term11 _27114 _27116 h t)). Qed.
Lemma lem1154815 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term13 _27114 _27116 h t) = (term14 _27114 _27116 h t).
Proof. exact (MK_COMB (@lem1154813 _27114 _27116 t) (@lem1154814 _27114 _27116 h t)). Qed.
Lemma lem1154816 {_27114 _27116 : Type'} (h : _27114) : (term15 _27114 _27116 h) = (term16 _27114 _27116 h).
Proof. exact (fun_ext (fun t : list _27114 => @lem1154815 _27114 _27116 h t)). Qed.
Lemma lem1154817 {_27114 : Type'} : (@all (list _27114)) = (@all (list _27114)).
Proof. exact (eq_refl (@all (list _27114))). Qed.
Lemma lem1154818 {_27114 _27116 : Type'} (h : _27114) : (term17 _27114 _27116 h) = (term18 _27114 _27116 h).
Proof. exact (MK_COMB (@lem1154817 _27114) (@lem1154816 _27114 _27116 h)). Qed.
Lemma lem1154819 {_27114 _27116 : Type'} : (term19 _27114 _27116) = (term20 _27114 _27116).
Proof. exact (fun_ext (fun h : _27114 => @lem1154818 _27114 _27116 h)). Qed.
Lemma lem1154820 {_27114 : Type'} : (@all _27114) = (@all _27114).
Proof. exact (eq_refl (@all _27114)). Qed.
Lemma lem1154821 {_27114 _27116 : Type'} : (term21 _27114 _27116) = (term22 _27114 _27116).
Proof. exact (MK_COMB (@lem1154820 _27114) (@lem1154819 _27114 _27116)). Qed.
Lemma lem1154822 {_27114 _27116 : Type'} : (term23 _27114 _27116) = (term24 _27114 _27116).
Proof. exact (MK_COMB (@lem1154810 _27114 _27116) (@lem1154821 _27114 _27116)). Qed.
Lemma lem1154823 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1154824 {_27114 _27116 : Type'} : (term25 _27114 _27116) = (term26 _27114 _27116).
Proof. exact (MK_COMB (@lem1154823) (@lem1154822 _27114 _27116)). Qed.
Lemma lem1154825 {_27114 _27116 : Type'} (l1 : list _27114) : (term7 _27114 _27116 l1) = (term8 _27114 _27116 l1).
Proof. exact (eq_refl (term7 _27114 _27116 l1)). Qed.
Lemma lem1154826 {_27114 _27116 : Type'} : (term27 _27114 _27116) = (term2 _27114 _27116).
Proof. exact (fun_ext (fun l1 : list _27114 => @lem1154825 _27114 _27116 l1)). Qed.
Lemma lem1154827 {_27114 : Type'} : (@all (list _27114)) = (@all (list _27114)).
Proof. exact (eq_refl (@all (list _27114))). Qed.
Lemma lem1154828 {_27114 _27116 : Type'} : (term28 _27114 _27116) = (term29 _27114 _27116).
Proof. exact (MK_COMB (@lem1154827 _27114) (@lem1154826 _27114 _27116)). Qed.
Lemma lem1154829 {_27114 _27116 : Type'} : (term1 _27114 _27116) = (term30 _27114 _27116).
Proof. exact (MK_COMB (@lem1154824 _27114 _27116) (@lem1154828 _27114 _27116)). Qed.
Lemma lem1154830 {_27114 _27116 : Type'} : term30 _27114 _27116.
Proof. exact (EQ_MP (@lem1154829 _27114 _27116) (@lem1154807 _27114 _27116)). Qed.
Lemma lem1154831 {_27114 _27116 : Type'} (t : list _27114) (h1 : term8 _27114 _27116 t) : term8 _27114 _27116 t.
Proof. exact (h1). Qed.
Lemma lem1154833 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1154834 {_27116 : Type'} (P : type1143 _27116) : term0 _27116 P.
Proof. exact (@lem1154833 _27116 P). Qed.
Lemma lem1154835 {_27114 _27116 : Type'} : term31 _27114 _27116.
Proof. exact (@lem1154834 _27116 (term32 _27114 _27116)). Qed.
Lemma lem1154836 {_27114 _27116 : Type'} : (term33 _27114 _27116) = (term34 _27114 _27116).
Proof. exact (eq_refl (term33 _27114 _27116)). Qed.
Lemma lem1154837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1154838 {_27114 _27116 : Type'} : (term35 _27114 _27116) = (term36 _27114 _27116).
Proof. exact (MK_COMB (@lem1154837) (@lem1154836 _27114 _27116)). Qed.
Lemma lem1154839 {_27114 _27116 : Type'} (t : list _27116) : (term37 _27114 _27116 t) = (term38 _27114 _27116 t).
Proof. exact (eq_refl (term37 _27114 _27116 t)). Qed.
Lemma lem1154840 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1154841 {_27114 _27116 : Type'} (t : list _27116) : (term39 _27114 _27116 t) = (term40 _27114 _27116 t).
Proof. exact (MK_COMB (@lem1154840) (@lem1154839 _27114 _27116 t)). Qed.
Lemma lem1154842 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : (term41 _27114 _27116 h t) = (term42 _27114 _27116 h t).
Proof. exact (eq_refl (term41 _27114 _27116 h t)). Qed.
Lemma lem1154843 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : (term43 _27114 _27116 h t) = (term44 _27114 _27116 h t).
Proof. exact (MK_COMB (@lem1154841 _27114 _27116 t) (@lem1154842 _27114 _27116 h t)). Qed.
Lemma lem1154844 {_27114 _27116 : Type'} (h : _27116) : (term45 _27114 _27116 h) = (term46 _27114 _27116 h).
Proof. exact (fun_ext (fun t : list _27116 => @lem1154843 _27114 _27116 h t)). Qed.
Lemma lem1154845 {_27116 : Type'} : (@all (list _27116)) = (@all (list _27116)).
Proof. exact (eq_refl (@all (list _27116))). Qed.
Lemma lem1154846 {_27114 _27116 : Type'} (h : _27116) : (term47 _27114 _27116 h) = (term48 _27114 _27116 h).
Proof. exact (MK_COMB (@lem1154845 _27116) (@lem1154844 _27114 _27116 h)). Qed.
Lemma lem1154847 {_27114 _27116 : Type'} : (term49 _27114 _27116) = (term50 _27114 _27116).
Proof. exact (fun_ext (fun h : _27116 => @lem1154846 _27114 _27116 h)). Qed.
Lemma lem1154848 {_27116 : Type'} : (@all _27116) = (@all _27116).
Proof. exact (eq_refl (@all _27116)). Qed.
Lemma lem1154849 {_27114 _27116 : Type'} : (term51 _27114 _27116) = (term52 _27114 _27116).
Proof. exact (MK_COMB (@lem1154848 _27116) (@lem1154847 _27114 _27116)). Qed.
Lemma lem1154850 {_27114 _27116 : Type'} : (term53 _27114 _27116) = (term54 _27114 _27116).
Proof. exact (MK_COMB (@lem1154838 _27114 _27116) (@lem1154849 _27114 _27116)). Qed.
Lemma lem1154851 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1154852 {_27114 _27116 : Type'} : (term55 _27114 _27116) = (term56 _27114 _27116).
Proof. exact (MK_COMB (@lem1154851) (@lem1154850 _27114 _27116)). Qed.
Lemma lem1154853 {_27114 _27116 : Type'} (l2 : list _27116) : (term37 _27114 _27116 l2) = (term38 _27114 _27116 l2).
Proof. exact (eq_refl (term37 _27114 _27116 l2)). Qed.
Lemma lem1154854 {_27114 _27116 : Type'} : (term57 _27114 _27116) = (term32 _27114 _27116).
Proof. exact (fun_ext (fun l2 : list _27116 => @lem1154853 _27114 _27116 l2)). Qed.
Lemma lem1154855 {_27116 : Type'} : (@all (list _27116)) = (@all (list _27116)).
Proof. exact (eq_refl (@all (list _27116))). Qed.
Lemma lem1154856 {_27114 _27116 : Type'} : (term58 _27114 _27116) = (term4 _27114 _27116).
Proof. exact (MK_COMB (@lem1154855 _27116) (@lem1154854 _27114 _27116)). Qed.
Lemma lem1154857 {_27114 _27116 : Type'} : (term31 _27114 _27116) = (term59 _27114 _27116).
Proof. exact (MK_COMB (@lem1154852 _27114 _27116) (@lem1154856 _27114 _27116)). Qed.
Lemma lem1154858 {_27114 _27116 : Type'} : term59 _27114 _27116.
Proof. exact (EQ_MP (@lem1154857 _27114 _27116) (@lem1154835 _27114 _27116)). Qed.
Lemma lem1154861 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1154862 {_27116 : Type'} (P : type1143 _27116) : term0 _27116 P.
Proof. exact (@lem1154861 _27116 P). Qed.
Lemma lem1154863 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : term60 _27114 _27116 h t.
Proof. exact (@lem1154862 _27116 (term61 _27114 _27116 h t)). Qed.
Lemma lem1154864 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term62 _27114 _27116 h t) = (term63 _27114 _27116 h t).
Proof. exact (eq_refl (term62 _27114 _27116 h t)). Qed.
Lemma lem1154865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1154866 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term64 _27114 _27116 h t) = (term65 _27114 _27116 h t).
Proof. exact (MK_COMB (@lem1154865) (@lem1154864 _27114 _27116 h t)). Qed.
Lemma lem1154867 {_27114 _27116 : Type'} (t : list _27116) (h : _27114) (t' : list _27114) : (term66 _27114 _27116 h t' t) = (term67 _27114 _27116 t h t').
Proof. exact (eq_refl (term66 _27114 _27116 h t' t)). Qed.
Lemma lem1154868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1154869 {_27114 _27116 : Type'} (t : list _27116) (h : _27114) (t' : list _27114) : (term68 _27114 _27116 h t' t) = (term69 _27114 _27116 t h t').
Proof. exact (MK_COMB (@lem1154868) (@lem1154867 _27114 _27116 t h t')). Qed.
Lemma lem1154870 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (h' : _27114) (t' : list _27114) : (term70 _27114 _27116 h' t' h t) = (term71 _27114 _27116 h t h' t').
Proof. exact (eq_refl (term70 _27114 _27116 h' t' h t)). Qed.
Lemma lem1154871 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (h' : _27114) (t' : list _27114) : (term72 _27114 _27116 h' t' h t) = (term73 _27114 _27116 h t h' t').
Proof. exact (MK_COMB (@lem1154869 _27114 _27116 t h' t') (@lem1154870 _27114 _27116 h t h' t')). Qed.
Lemma lem1154872 {_27114 _27116 : Type'} (h : _27116) (h' : _27114) (t : list _27114) : (term74 _27114 _27116 h' t h) = (term75 _27114 _27116 h h' t).
Proof. exact (fun_ext (fun t' : list _27116 => @lem1154871 _27114 _27116 h t' h' t)). Qed.
Lemma lem1154873 {_27116 : Type'} : (@all (list _27116)) = (@all (list _27116)).
Proof. exact (eq_refl (@all (list _27116))). Qed.
Lemma lem1154874 {_27114 _27116 : Type'} (h : _27116) (h' : _27114) (t : list _27114) : (term76 _27114 _27116 h' t h) = (term77 _27114 _27116 h h' t).
Proof. exact (MK_COMB (@lem1154873 _27116) (@lem1154872 _27114 _27116 h h' t)). Qed.
Lemma lem1154875 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term78 _27114 _27116 h t) = (term79 _27114 _27116 h t).
Proof. exact (fun_ext (fun h' : _27116 => @lem1154874 _27114 _27116 h' h t)). Qed.
Lemma lem1154876 {_27116 : Type'} : (@all _27116) = (@all _27116).
Proof. exact (eq_refl (@all _27116)). Qed.
Lemma lem1154877 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term80 _27114 _27116 h t) = (term81 _27114 _27116 h t).
Proof. exact (MK_COMB (@lem1154876 _27116) (@lem1154875 _27114 _27116 h t)). Qed.
Lemma lem1154878 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term82 _27114 _27116 h t) = (term83 _27114 _27116 h t).
Proof. exact (MK_COMB (@lem1154866 _27114 _27116 h t) (@lem1154877 _27114 _27116 h t)). Qed.
Lemma lem1154879 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1154880 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term84 _27114 _27116 h t) = (term85 _27114 _27116 h t).
Proof. exact (MK_COMB (@lem1154879) (@lem1154878 _27114 _27116 h t)). Qed.
Lemma lem1154881 {_27114 _27116 : Type'} (l2 : list _27116) (h : _27114) (t : list _27114) : (term66 _27114 _27116 h t l2) = (term67 _27114 _27116 l2 h t).
Proof. exact (eq_refl (term66 _27114 _27116 h t l2)). Qed.
Lemma lem1154882 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term86 _27114 _27116 h t) = (term61 _27114 _27116 h t).
Proof. exact (fun_ext (fun l2 : list _27116 => @lem1154881 _27114 _27116 l2 h t)). Qed.
Lemma lem1154883 {_27116 : Type'} : (@all (list _27116)) = (@all (list _27116)).
Proof. exact (eq_refl (@all (list _27116))). Qed.
Lemma lem1154884 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term87 _27114 _27116 h t) = (term12 _27114 _27116 h t).
Proof. exact (MK_COMB (@lem1154883 _27116) (@lem1154882 _27114 _27116 h t)). Qed.
Lemma lem1154885 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term60 _27114 _27116 h t) = (term88 _27114 _27116 h t).
Proof. exact (MK_COMB (@lem1154880 _27114 _27116 h t) (@lem1154884 _27114 _27116 h t)). Qed.
Lemma lem1154886 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : term88 _27114 _27116 h t.
Proof. exact (EQ_MP (@lem1154885 _27114 _27116 h t) (@lem1154863 _27114 _27116 h t)). Qed.
Lemma lem1154922 {A B : Type'} : term89 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1154923 {A B : Type'} (f : A -> B) : term90 A B f.
Proof. exact (@lem1154922 A B f). Qed.
Lemma lem1154924 {A B : Type'} (f : A -> B) : (term90 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term90 A B f)). Qed.
Lemma lem1154945 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1154946 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem1154945 p q p' q'). Qed.
Lemma lem1154947 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem1154946 p q p'). Qed.
Lemma lem1154948 {_27114 _27116 : Type'} : term94 _27114 _27116.
Proof. exact (@lem1154947 ((@List.length _27114 (@nil _27114)) = (@List.length _27116 (@nil _27116))) ((term95 _27114 _27116) = (@nil _27114))). Qed.
Lemma lem1154949 {_27114 _27116 : Type'} (p' : Prop) : term96 _27114 _27116 p'.
Proof. exact (@lem1154948 _27114 _27116 p'). Qed.
Lemma lem1154950 {_27114 _27116 : Type'} (p' : Prop) : (term96 _27114 _27116 p') = (term97 _27114 _27116 p').
Proof. exact (eq_refl (term96 _27114 _27116 p')). Qed.
Lemma lem1154951 {_27114 _27116 : Type'} (p' : Prop) : term97 _27114 _27116 p'.
Proof. exact (EQ_MP (@lem1154950 _27114 _27116 p') (@lem1154949 _27114 _27116 p')). Qed.
Lemma lem1154952 {_27114 _27116 : Type'} (p' : Prop) (q' : Prop) : term98 _27114 _27116 p' q'.
Proof. exact (@lem1154951 _27114 _27116 p' q'). Qed.
Lemma lem1154953 {_27114 _27116 : Type'} (p' : Prop) (q' : Prop) : (term98 _27114 _27116 p' q') = (term99 _27114 _27116 p' q').
Proof. exact (eq_refl (term98 _27114 _27116 p' q')). Qed.
Lemma lem1154954 {_27114 _27116 : Type'} (p' : Prop) (q' : Prop) : term99 _27114 _27116 p' q'.
Proof. exact (EQ_MP (@lem1154953 _27114 _27116 p' q') (@lem1154952 _27114 _27116 p' q')). Qed.
Lemma lem1154958 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1154959 {_27114 : Type'} : (@List.length _27114 (@nil _27114)) = (NUMERAL 0).
Proof. exact (@lem1154958 _27114). Qed.
Lemma lem1154960 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1154961 {_27114 : Type'} : (term100 _27114) = term101.
Proof. exact (MK_COMB (@lem1154960) (@lem1154959 _27114)). Qed.
Lemma lem1154963 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1154964 {_27116 : Type'} : (@List.length _27116 (@nil _27116)) = (NUMERAL 0).
Proof. exact (@lem1154963 _27116). Qed.
Lemma lem1154965 {_27114 _27116 : Type'} : ((@List.length _27114 (@nil _27114)) = (@List.length _27116 (@nil _27116))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1154961 _27114) (@lem1154964 _27116)). Qed.
Lemma lem1154967 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1154968 (x : nat) : (x = x) = True.
Proof. exact (@lem1154967 nat x). Qed.
Lemma lem1154969 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1154968 (NUMERAL 0)). Qed.
Lemma lem1154970 {_27114 _27116 : Type'} : ((@List.length _27114 (@nil _27114)) = (@List.length _27116 (@nil _27116))) = True.
Proof. exact (TRANS (@lem1154965 _27114 _27116) (@lem1154969)). Qed.
Lemma lem1154971 {_27114 _27116 : Type'} (q' : Prop) : term102 _27114 _27116 q'.
Proof. exact (@lem1154954 _27114 _27116 True q'). Qed.
Lemma lem1154972 {_27114 _27116 : Type'} (q' : Prop) : term103 _27114 _27116 q'.
Proof. exact (@lem1154971 _27114 _27116 q' (@lem1154970 _27114 _27116)). Qed.
Lemma lem1154981 {_25738 _25739 : Type'} : (@ZIP _25738 _25739 (@nil _25738) (@nil _25739)) = (@nil (prod _25738 _25739)).
Proof. exact (proj1 (@lem1109008 _25738 _25739 Prop Prop (@el Prop) (@el Prop) (@el (list Prop)) (@el (list Prop)))). Qed.
Lemma lem1154982 {_27114 _27116 : Type'} : (@ZIP _27114 _27116 (@nil _27114) (@nil _27116)) = (@nil (prod _27114 _27116)).
Proof. exact (@lem1154981 _27114 _27116). Qed.
Lemma lem1154983 {_27114 _27116 : Type'} : (@List.map (prod _27114 _27116) _27114 (@fst _27114 _27116)) = (@List.map (prod _27114 _27116) _27114 (@fst _27114 _27116)).
Proof. exact (eq_refl (@List.map (prod _27114 _27116) _27114 (@fst _27114 _27116))). Qed.
Lemma lem1154984 {_27114 _27116 : Type'} : (term95 _27114 _27116) = (@List.map (prod _27114 _27116) _27114 (@fst _27114 _27116) (@nil (prod _27114 _27116))).
Proof. exact (MK_COMB (@lem1154983 _27114 _27116) (@lem1154982 _27114 _27116)). Qed.
Lemma lem1154986 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1154924 A B f) (@lem1154923 A B f)). Qed.
Lemma lem1154987 {_27114 _27116 : Type'} (f : type1207 _27114 _27116) : (@List.map (prod _27114 _27116) _27114 f (@nil (prod _27114 _27116))) = (@nil _27114).
Proof. exact (@lem1154986 (prod _27114 _27116) _27114 f). Qed.
Lemma lem1154988 {_27114 _27116 : Type'} : (@List.map (prod _27114 _27116) _27114 (@fst _27114 _27116) (@nil (prod _27114 _27116))) = (@nil _27114).
Proof. exact (@lem1154987 _27114 _27116 (@fst _27114 _27116)). Qed.
Lemma lem1154989 {_27114 _27116 : Type'} : (term95 _27114 _27116) = (@nil _27114).
Proof. exact (TRANS (@lem1154984 _27114 _27116) (@lem1154988 _27114 _27116)). Qed.
Lemma lem1154990 {_27114 : Type'} : (@eq (list _27114)) = (@eq (list _27114)).
Proof. exact (eq_refl (@eq (list _27114))). Qed.
Lemma lem1154991 {_27114 _27116 : Type'} : (term104 _27114 _27116) = (@eq (list _27114) (@nil _27114)).
Proof. exact (MK_COMB (@lem1154990 _27114) (@lem1154989 _27114 _27116)). Qed.
Lemma lem1154992 {_27114 : Type'} : (@nil _27114) = (@nil _27114).
Proof. exact (eq_refl (@nil _27114)). Qed.
Lemma lem1154993 {_27114 _27116 : Type'} : ((term95 _27114 _27116) = (@nil _27114)) = ((@nil _27114) = (@nil _27114)).
Proof. exact (MK_COMB (@lem1154991 _27114 _27116) (@lem1154992 _27114)). Qed.
Lemma lem1154995 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1154996 {_27114 : Type'} (x : list _27114) : (x = x) = True.
Proof. exact (@lem1154995 (list _27114) x). Qed.
Lemma lem1154997 {_27114 : Type'} : ((@nil _27114) = (@nil _27114)) = True.
Proof. exact (@lem1154996 _27114 (@nil _27114)). Qed.
Lemma lem1155000 {_27114 _27116 : Type'} : ((term95 _27114 _27116) = (@nil _27114)) = True.
Proof. exact (TRANS (@lem1154993 _27114 _27116) (@lem1154997 _27114)). Qed.
Lemma lem1155001 {_27114 _27116 : Type'} : term105 _27114 _27116.
Proof. exact (fun h0 : True => @lem1155000 _27114 _27116). Qed.
Lemma lem1155002 {_27114 _27116 : Type'} : term106 _27114 _27116.
Proof. exact (@lem1154972 _27114 _27116 True). Qed.
Lemma lem1155003 {_27114 _27116 : Type'} : (term34 _27114 _27116) = (True -> True).
Proof. exact (@lem1155002 _27114 _27116 (@lem1155001 _27114 _27116)). Qed.
Lemma lem1155005 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1155006 : (True -> True) = True.
Proof. exact (@lem1155005 True). Qed.
Lemma lem1155007 {_27114 _27116 : Type'} : (term34 _27114 _27116) = True.
Proof. exact (TRANS (@lem1155003 _27114 _27116) (@lem1155006)). Qed.
Lemma lem1155008 {_27114 _27116 : Type'} : True = (term34 _27114 _27116).
Proof. exact (SYM (@lem1155007 _27114 _27116)). Qed.
Lemma lem1155009 {_27114 _27116 : Type'} : term34 _27114 _27116.
Proof. exact (EQ_MP (@lem1155008 _27114 _27116) (@lem0)). Qed.
Lemma lem1155010 (n : nat) : term107 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1155011 (n : nat) : (term107 n) = (term108 n).
Proof. exact (eq_refl (term107 n)). Qed.
Lemma lem1155012 (n : nat) : term108 n.
Proof. exact (EQ_MP (@lem1155011 n) (@lem1155010 n)). Qed.
Lemma lem1155016 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1155017 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem1155016 n h1)). Qed.
Lemma lem1155018 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem1155019 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem1155018 n h1)). Qed.
Lemma lem1155020 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem1155017 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem1155019 n h1)). Qed.
Lemma lem1155021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1155022 (n : nat) : (term108 n) = (term109 n).
Proof. exact (MK_COMB (@lem1155021) (@lem1155020 n)). Qed.
Lemma lem1155023 (n : nat) : term109 n.
Proof. exact (EQ_MP (@lem1155022 n) (@lem1155012 n)). Qed.
Lemma lem1155024 (n : nat) : term110 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem1155054 {A : Type'} : term111 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1155055 {A : Type'} (h : A) : term112 A h.
Proof. exact (@lem1155054 A h). Qed.
Lemma lem1155056 {A : Type'} (h : A) : (term112 A h) = (term113 A h).
Proof. exact (eq_refl (term112 A h)). Qed.
Lemma lem1155057 {A : Type'} (h : A) : term113 A h.
Proof. exact (EQ_MP (@lem1155056 A h) (@lem1155055 A h)). Qed.
Lemma lem1155058 {A : Type'} (h : A) (t : list A) : term114 A h t.
Proof. exact (@lem1155057 A h t). Qed.
Lemma lem1155059 {A : Type'} (h : A) (t : list A) : (term114 A h t) = ((term115 A h t) = (term116 A t)).
Proof. exact (eq_refl (term114 A h t)). Qed.
Lemma lem1155074 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1155075 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem1155074 p q p' q'). Qed.
Lemma lem1155076 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem1155075 p q p'). Qed.
Lemma lem1155077 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : term117 _27114 _27116 h t.
Proof. exact (@lem1155076 ((@List.length _27114 (@nil _27114)) = (term115 _27116 h t)) ((term118 _27114 _27116 h t) = (@nil _27114))). Qed.
Lemma lem1155078 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (p' : Prop) : term119 _27114 _27116 h t p'.
Proof. exact (@lem1155077 _27114 _27116 h t p'). Qed.
Lemma lem1155079 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (p' : Prop) : (term119 _27114 _27116 h t p') = (term120 _27114 _27116 h t p').
Proof. exact (eq_refl (term119 _27114 _27116 h t p')). Qed.
Lemma lem1155080 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (p' : Prop) : term120 _27114 _27116 h t p'.
Proof. exact (EQ_MP (@lem1155079 _27114 _27116 h t p') (@lem1155078 _27114 _27116 h t p')). Qed.
Lemma lem1155081 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (p' : Prop) (q' : Prop) : term121 _27114 _27116 h t p' q'.
Proof. exact (@lem1155080 _27114 _27116 h t p' q'). Qed.
Lemma lem1155082 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (p' : Prop) (q' : Prop) : (term121 _27114 _27116 h t p' q') = (term122 _27114 _27116 h t p' q').
Proof. exact (eq_refl (term121 _27114 _27116 h t p' q')). Qed.
Lemma lem1155083 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (p' : Prop) (q' : Prop) : term122 _27114 _27116 h t p' q'.
Proof. exact (EQ_MP (@lem1155082 _27114 _27116 h t p' q') (@lem1155081 _27114 _27116 h t p' q')). Qed.
Lemma lem1155087 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1155088 {_27114 : Type'} : (@List.length _27114 (@nil _27114)) = (NUMERAL 0).
Proof. exact (@lem1155087 _27114). Qed.
Lemma lem1155089 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1155090 {_27114 : Type'} : (term100 _27114) = term101.
Proof. exact (MK_COMB (@lem1155089) (@lem1155088 _27114)). Qed.
Lemma lem1155092 {A : Type'} (h : A) (t : list A) : (term115 A h t) = (term116 A t).
Proof. exact (EQ_MP (@lem1155059 A h t) (@lem1155058 A h t)). Qed.
Lemma lem1155093 {_27116 : Type'} (h : _27116) (t : list _27116) : (term115 _27116 h t) = (term116 _27116 t).
Proof. exact (@lem1155092 _27116 h t). Qed.
Lemma lem1155094 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : ((@List.length _27114 (@nil _27114)) = (term115 _27116 h t)) = ((NUMERAL 0) = (term116 _27116 t)).
Proof. exact (MK_COMB (@lem1155090 _27114) (@lem1155093 _27116 h t)). Qed.
Lemma lem1155096 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem1155024 n (@lem1155023 n)). Qed.
Lemma lem1155097 {_27116 : Type'} (t : list _27116) : ((NUMERAL 0) = (term116 _27116 t)) = False.
Proof. exact (@lem1155096 (@List.length _27116 t)). Qed.
Lemma lem1155098 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : ((@List.length _27114 (@nil _27114)) = (term115 _27116 h t)) = False.
Proof. exact (TRANS (@lem1155094 _27114 _27116 h t) (@lem1155097 _27116 t)). Qed.
Lemma lem1155099 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (q' : Prop) : term123 _27114 _27116 h t q'.
Proof. exact (@lem1155083 _27114 _27116 h t False q'). Qed.
Lemma lem1155100 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) (q' : Prop) : term124 _27114 _27116 h t q'.
Proof. exact (@lem1155099 _27114 _27116 h t q' (@lem1155098 _27114 _27116 h t)). Qed.
Lemma lem1155106 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : ((term118 _27114 _27116 h t) = (@nil _27114)) = ((term118 _27114 _27116 h t) = (@nil _27114)).
Proof. exact (eq_refl ((term118 _27114 _27116 h t) = (@nil _27114))). Qed.
Lemma lem1155107 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : term125 _27114 _27116 h t.
Proof. exact (fun h0 : False => @lem1155106 _27114 _27116 h t). Qed.
Lemma lem1155108 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : term126 _27114 _27116 h t.
Proof. exact (@lem1155100 _27114 _27116 h t ((term118 _27114 _27116 h t) = (@nil _27114))). Qed.
Lemma lem1155109 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : (term42 _27114 _27116 h t) = (term127 _27114 _27116 h t).
Proof. exact (@lem1155108 _27114 _27116 h t (@lem1155107 _27114 _27116 h t)). Qed.
Lemma lem1155111 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1155112 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : (term127 _27114 _27116 h t) = True.
Proof. exact (@lem1155111 ((term118 _27114 _27116 h t) = (@nil _27114))). Qed.
Lemma lem1155113 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : (term42 _27114 _27116 h t) = True.
Proof. exact (TRANS (@lem1155109 _27114 _27116 h t) (@lem1155112 _27114 _27116 h t)). Qed.
Lemma lem1155114 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : True = (term42 _27114 _27116 h t).
Proof. exact (SYM (@lem1155113 _27114 _27116 h t)). Qed.
Lemma lem1155115 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : term42 _27114 _27116 h t.
Proof. exact (EQ_MP (@lem1155114 _27114 _27116 h t) (@lem0)). Qed.
Lemma lem1155116 (n : nat) : term107 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1155117 (n : nat) : (term107 n) = (term108 n).
Proof. exact (eq_refl (term107 n)). Qed.
Lemma lem1155118 (n : nat) : term108 n.
Proof. exact (EQ_MP (@lem1155117 n) (@lem1155116 n)). Qed.
Lemma lem1155119 (n : nat) : term128 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1155160 {A : Type'} : term111 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1155161 {A : Type'} (h : A) : term112 A h.
Proof. exact (@lem1155160 A h). Qed.
Lemma lem1155162 {A : Type'} (h : A) : (term112 A h) = (term113 A h).
Proof. exact (eq_refl (term112 A h)). Qed.
Lemma lem1155163 {A : Type'} (h : A) : term113 A h.
Proof. exact (EQ_MP (@lem1155162 A h) (@lem1155161 A h)). Qed.
Lemma lem1155164 {A : Type'} (h : A) (t : list A) : term114 A h t.
Proof. exact (@lem1155163 A h t). Qed.
Lemma lem1155165 {A : Type'} (h : A) (t : list A) : (term114 A h t) = ((term115 A h t) = (term116 A t)).
Proof. exact (eq_refl (term114 A h t)). Qed.
Lemma lem1155183 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1155184 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem1155183 p q p' q'). Qed.
Lemma lem1155185 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem1155184 p q p'). Qed.
Lemma lem1155186 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : term129 _27114 _27116 h t.
Proof. exact (@lem1155185 ((term115 _27114 h t) = (@List.length _27116 (@nil _27116))) ((term130 _27114 _27116 h t) = (@cons _27114 h t))). Qed.
Lemma lem1155187 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (p' : Prop) : term131 _27114 _27116 h t p'.
Proof. exact (@lem1155186 _27114 _27116 h t p'). Qed.
Lemma lem1155188 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (p' : Prop) : (term131 _27114 _27116 h t p') = (term132 _27114 _27116 h t p').
Proof. exact (eq_refl (term131 _27114 _27116 h t p')). Qed.
Lemma lem1155189 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (p' : Prop) : term132 _27114 _27116 h t p'.
Proof. exact (EQ_MP (@lem1155188 _27114 _27116 h t p') (@lem1155187 _27114 _27116 h t p')). Qed.
Lemma lem1155190 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (p' : Prop) (q' : Prop) : term133 _27114 _27116 h t p' q'.
Proof. exact (@lem1155189 _27114 _27116 h t p' q'). Qed.
Lemma lem1155191 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (p' : Prop) (q' : Prop) : (term133 _27114 _27116 h t p' q') = (term134 _27114 _27116 h t p' q').
Proof. exact (eq_refl (term133 _27114 _27116 h t p' q')). Qed.
Lemma lem1155192 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (p' : Prop) (q' : Prop) : term134 _27114 _27116 h t p' q'.
Proof. exact (EQ_MP (@lem1155191 _27114 _27116 h t p' q') (@lem1155190 _27114 _27116 h t p' q')). Qed.
Lemma lem1155196 {A : Type'} (h : A) (t : list A) : (term115 A h t) = (term116 A t).
Proof. exact (EQ_MP (@lem1155165 A h t) (@lem1155164 A h t)). Qed.
Lemma lem1155197 {_27114 : Type'} (h : _27114) (t : list _27114) : (term115 _27114 h t) = (term116 _27114 t).
Proof. exact (@lem1155196 _27114 h t). Qed.
Lemma lem1155198 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1155199 {_27114 : Type'} (h : _27114) (t : list _27114) : (term135 _27114 h t) = (term136 _27114 t).
Proof. exact (MK_COMB (@lem1155198) (@lem1155197 _27114 h t)). Qed.
Lemma lem1155201 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1155202 {_27116 : Type'} : (@List.length _27116 (@nil _27116)) = (NUMERAL 0).
Proof. exact (@lem1155201 _27116). Qed.
Lemma lem1155203 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : ((term115 _27114 h t) = (@List.length _27116 (@nil _27116))) = ((term116 _27114 t) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1155199 _27114 h t) (@lem1155202 _27116)). Qed.
Lemma lem1155205 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1155119 n (@lem1155118 n)). Qed.
Lemma lem1155206 {_27114 : Type'} (t : list _27114) : ((term116 _27114 t) = (NUMERAL 0)) = False.
Proof. exact (@lem1155205 (@List.length _27114 t)). Qed.
Lemma lem1155207 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : ((term115 _27114 h t) = (@List.length _27116 (@nil _27116))) = False.
Proof. exact (TRANS (@lem1155203 _27114 _27116 h t) (@lem1155206 _27114 t)). Qed.
Lemma lem1155208 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (q' : Prop) : term137 _27114 _27116 h t q'.
Proof. exact (@lem1155192 _27114 _27116 h t False q'). Qed.
Lemma lem1155209 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (q' : Prop) : term138 _27114 _27116 h t q'.
Proof. exact (@lem1155208 _27114 _27116 h t q' (@lem1155207 _27114 _27116 h t)). Qed.
Lemma lem1155215 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : ((term130 _27114 _27116 h t) = (@cons _27114 h t)) = ((term130 _27114 _27116 h t) = (@cons _27114 h t)).
Proof. exact (eq_refl ((term130 _27114 _27116 h t) = (@cons _27114 h t))). Qed.
Lemma lem1155216 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : term139 _27114 _27116 h t.
Proof. exact (fun h0 : False => @lem1155215 _27114 _27116 h t). Qed.
Lemma lem1155217 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : term140 _27114 _27116 h t.
Proof. exact (@lem1155209 _27114 _27116 h t ((term130 _27114 _27116 h t) = (@cons _27114 h t))). Qed.
Lemma lem1155218 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term63 _27114 _27116 h t) = (term141 _27114 _27116 h t).
Proof. exact (@lem1155217 _27114 _27116 h t (@lem1155216 _27114 _27116 h t)). Qed.
Lemma lem1155220 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1155221 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term141 _27114 _27116 h t) = True.
Proof. exact (@lem1155220 ((term130 _27114 _27116 h t) = (@cons _27114 h t))). Qed.
Lemma lem1155222 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : (term63 _27114 _27116 h t) = True.
Proof. exact (TRANS (@lem1155218 _27114 _27116 h t) (@lem1155221 _27114 _27116 h t)). Qed.
Lemma lem1155223 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : True = (term63 _27114 _27116 h t).
Proof. exact (SYM (@lem1155222 _27114 _27116 h t)). Qed.
Lemma lem1155224 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : term63 _27114 _27116 h t.
Proof. exact (EQ_MP (@lem1155223 _27114 _27116 h t) (@lem0)). Qed.
Lemma lem1155249 {A B : Type'} : term142 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1155250 {A B : Type'} (f : A -> B) : term143 A B f.
Proof. exact (@lem1155249 A B f). Qed.
Lemma lem1155251 {A B : Type'} (f : A -> B) : (term143 A B f) = (term144 A B f).
Proof. exact (eq_refl (term143 A B f)). Qed.
Lemma lem1155252 {A B : Type'} (f : A -> B) : term144 A B f.
Proof. exact (EQ_MP (@lem1155251 A B f) (@lem1155250 A B f)). Qed.
Lemma lem1155253 {A B : Type'} (f : A -> B) (h : A) : term145 A B f h.
Proof. exact (@lem1155252 A B f h). Qed.
Lemma lem1155254 {A B : Type'} (h : A) (f : A -> B) : (term145 A B f h) = (term146 A B h f).
Proof. exact (eq_refl (term145 A B f h)). Qed.
Lemma lem1155255 {A B : Type'} (h : A) (f : A -> B) : term146 A B h f.
Proof. exact (EQ_MP (@lem1155254 A B h f) (@lem1155253 A B f h)). Qed.
Lemma lem1155256 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term147 A B h f t.
Proof. exact (@lem1155255 A B h f t). Qed.
Lemma lem1155257 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term147 A B h f t) = ((term148 A B f h t) = (term149 A B h f t)).
Proof. exact (eq_refl (term147 A B h f t)). Qed.
Lemma lem1155263 (m : nat) : term150 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem1155264 (m : nat) : (term150 m) = (term151 m).
Proof. exact (eq_refl (term150 m)). Qed.
Lemma lem1155265 (m : nat) : term151 m.
Proof. exact (EQ_MP (@lem1155264 m) (@lem1155263 m)). Qed.
Lemma lem1155266 (m : nat) (n : nat) : term152 m n.
Proof. exact (@lem1155265 m n). Qed.
Lemma lem1155267 (m : nat) (n : nat) : (term152 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term152 m n)). Qed.
Lemma lem1155269 {A : Type'} : term111 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1155270 {A : Type'} (h : A) : term112 A h.
Proof. exact (@lem1155269 A h). Qed.
Lemma lem1155271 {A : Type'} (h : A) : (term112 A h) = (term113 A h).
Proof. exact (eq_refl (term112 A h)). Qed.
Lemma lem1155272 {A : Type'} (h : A) : term113 A h.
Proof. exact (EQ_MP (@lem1155271 A h) (@lem1155270 A h)). Qed.
Lemma lem1155273 {A : Type'} (h : A) (t : list A) : term114 A h t.
Proof. exact (@lem1155272 A h t). Qed.
Lemma lem1155274 {A : Type'} (h : A) (t : list A) : (term114 A h t) = ((term115 A h t) = (term116 A t)).
Proof. exact (eq_refl (term114 A h t)). Qed.
Lemma lem1155277 {_27114 _27116 : Type'} (l2 : list _27116) (t : list _27114) (h1 : term8 _27114 _27116 t) : term153 _27114 _27116 t l2.
Proof. exact (@lem1154831 _27114 _27116 t h1 l2). Qed.
Lemma lem1155278 {_27114 _27116 : Type'} (l2 : list _27116) (t : list _27114) : (term153 _27114 _27116 t l2) = (term154 _27114 _27116 l2 t).
Proof. exact (eq_refl (term153 _27114 _27116 t l2)). Qed.
Lemma lem1155279 {_27114 _27116 : Type'} (l2 : list _27116) (t : list _27114) (h1 : term8 _27114 _27116 t) : term154 _27114 _27116 l2 t.
Proof. exact (EQ_MP (@lem1155278 _27114 _27116 l2 t) (@lem1155277 _27114 _27116 l2 t h1)). Qed.
Lemma lem1155280 {_27114 _27116 : Type'} (t : list _27114) (l2 : list _27116) (h1 : (@List.length _27114 t) = (@List.length _27116 l2)) : (@List.length _27114 t) = (@List.length _27116 l2).
Proof. exact (h1). Qed.
Lemma lem1155281 {_27114 _27116 : Type'} (t : list _27114) (l2 : list _27116) (h1 : term8 _27114 _27116 t) (h2 : (@List.length _27114 t) = (@List.length _27116 l2)) : (term155 _27114 _27116 t l2) = t.
Proof. exact (@lem1155279 _27114 _27116 l2 t h1 (@lem1155280 _27114 _27116 t l2 h2)). Qed.
Lemma lem1155299 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1155300 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem1155299 p q p' q'). Qed.
Lemma lem1155301 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem1155300 p q p'). Qed.
Lemma lem1155302 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) : term156 _27114 _27116 h' t' h t.
Proof. exact (@lem1155301 ((term115 _27114 h t) = (term115 _27116 h' t')) ((term157 _27114 _27116 h t h' t') = (@cons _27114 h t))). Qed.
Lemma lem1155303 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (p' : Prop) : term158 _27114 _27116 h' t' h t p'.
Proof. exact (@lem1155302 _27114 _27116 h' t' h t p'). Qed.
Lemma lem1155304 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (p' : Prop) : (term158 _27114 _27116 h' t' h t p') = (term159 _27114 _27116 h' t' h t p').
Proof. exact (eq_refl (term158 _27114 _27116 h' t' h t p')). Qed.
Lemma lem1155305 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (p' : Prop) : term159 _27114 _27116 h' t' h t p'.
Proof. exact (EQ_MP (@lem1155304 _27114 _27116 h' t' h t p') (@lem1155303 _27114 _27116 h' t' h t p')). Qed.
Lemma lem1155306 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (p' : Prop) (q' : Prop) : term160 _27114 _27116 h' t' h t p' q'.
Proof. exact (@lem1155305 _27114 _27116 h' t' h t p' q'). Qed.
Lemma lem1155307 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (p' : Prop) (q' : Prop) : (term160 _27114 _27116 h' t' h t p' q') = (term161 _27114 _27116 h' t' h t p' q').
Proof. exact (eq_refl (term160 _27114 _27116 h' t' h t p' q')). Qed.
Lemma lem1155308 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (p' : Prop) (q' : Prop) : term161 _27114 _27116 h' t' h t p' q'.
Proof. exact (EQ_MP (@lem1155307 _27114 _27116 h' t' h t p' q') (@lem1155306 _27114 _27116 h' t' h t p' q')). Qed.
Lemma lem1155312 {A : Type'} (h : A) (t : list A) : (term115 A h t) = (term116 A t).
Proof. exact (EQ_MP (@lem1155274 A h t) (@lem1155273 A h t)). Qed.
Lemma lem1155313 {_27114 : Type'} (h : _27114) (t : list _27114) : (term115 _27114 h t) = (term116 _27114 t).
Proof. exact (@lem1155312 _27114 h t). Qed.
Lemma lem1155314 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1155315 {_27114 : Type'} (h : _27114) (t : list _27114) : (term135 _27114 h t) = (term136 _27114 t).
Proof. exact (MK_COMB (@lem1155314) (@lem1155313 _27114 h t)). Qed.
Lemma lem1155317 {A : Type'} (h : A) (t : list A) : (term115 A h t) = (term116 A t).
Proof. exact (EQ_MP (@lem1155274 A h t) (@lem1155273 A h t)). Qed.
Lemma lem1155318 {_27116 : Type'} (h : _27116) (t : list _27116) : (term115 _27116 h t) = (term116 _27116 t).
Proof. exact (@lem1155317 _27116 h t). Qed.
Lemma lem1155319 {_27116 : Type'} (h' : _27116) (t' : list _27116) : (term115 _27116 h' t') = (term116 _27116 t').
Proof. exact (@lem1155318 _27116 h' t'). Qed.
Lemma lem1155320 {_27114 _27116 : Type'} (h : _27114) (h' : _27116) (t : list _27114) (t' : list _27116) : ((term115 _27114 h t) = (term115 _27116 h' t')) = ((term116 _27114 t) = (term116 _27116 t')).
Proof. exact (MK_COMB (@lem1155315 _27114 h t) (@lem1155319 _27116 h' t')). Qed.
Lemma lem1155322 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1155267 m n) (@lem1155266 m n)). Qed.
Lemma lem1155323 {_27114 _27116 : Type'} (t : list _27114) (t' : list _27116) : ((term116 _27114 t) = (term116 _27116 t')) = ((@List.length _27114 t) = (@List.length _27116 t')).
Proof. exact (@lem1155322 (@List.length _27114 t) (@List.length _27116 t')). Qed.
Lemma lem1155326 {_27114 _27116 : Type'} (h : _27114) (h' : _27116) (t : list _27114) (t' : list _27116) : ((term115 _27114 h t) = (term115 _27116 h' t')) = ((@List.length _27114 t) = (@List.length _27116 t')).
Proof. exact (TRANS (@lem1155320 _27114 _27116 h h' t t') (@lem1155323 _27114 _27116 t t')). Qed.
Lemma lem1155327 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (t' : list _27116) (q' : Prop) : term162 _27114 _27116 h' h t t' q'.
Proof. exact (@lem1155308 _27114 _27116 h' t' h t ((@List.length _27114 t) = (@List.length _27116 t')) q'). Qed.
Lemma lem1155328 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (t' : list _27116) (q' : Prop) : term163 _27114 _27116 h' h t t' q'.
Proof. exact (@lem1155327 _27114 _27116 h' h t t' q' (@lem1155326 _27114 _27116 h h' t t')). Qed.
Lemma lem1155333 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term164 _25763 _25764 h1' t1 h2' t2) = (term165 _25763 _25764 h1' h2' t1 t2).
Proof. exact (proj2 (@lem1109008 Prop Prop _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1155334 {_27114 _27116 : Type'} (h1' : _27114) (h2' : _27116) (t1 : list _27114) (t2 : list _27116) : (term164 _27114 _27116 h1' t1 h2' t2) = (term165 _27114 _27116 h1' h2' t1 t2).
Proof. exact (@lem1155333 _27114 _27116 h1' h2' t1 t2). Qed.
Lemma lem1155335 {_27114 _27116 : Type'} (h : _27114) (h' : _27116) (t : list _27114) (t' : list _27116) : (term164 _27114 _27116 h t h' t') = (term165 _27114 _27116 h h' t t').
Proof. exact (@lem1155334 _27114 _27116 h h' t t'). Qed.
Lemma lem1155336 {_27114 _27116 : Type'} : (@List.map (prod _27114 _27116) _27114 (@fst _27114 _27116)) = (@List.map (prod _27114 _27116) _27114 (@fst _27114 _27116)).
Proof. exact (eq_refl (@List.map (prod _27114 _27116) _27114 (@fst _27114 _27116))). Qed.
Lemma lem1155337 {_27114 _27116 : Type'} (h : _27114) (h' : _27116) (t : list _27114) (t' : list _27116) : (term157 _27114 _27116 h t h' t') = (term166 _27114 _27116 h h' t t').
Proof. exact (MK_COMB (@lem1155336 _27114 _27116) (@lem1155335 _27114 _27116 h h' t t')). Qed.
Lemma lem1155339 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term148 A B f h t) = (term149 A B h f t).
Proof. exact (EQ_MP (@lem1155257 A B h f t) (@lem1155256 A B h f t)). Qed.
Lemma lem1155340 {_27114 _27116 : Type'} (h : prod _27114 _27116) (f : type1207 _27114 _27116) (t : type1640 _27114 _27116) : (term167 _27114 _27116 f h t) = (term168 _27114 _27116 h f t).
Proof. exact (@lem1155339 (prod _27114 _27116) _27114 h f t). Qed.
Lemma lem1155341 {_27114 _27116 : Type'} (h : _27114) (h' : _27116) (t : list _27114) (t' : list _27116) : (term166 _27114 _27116 h h' t t') = (term169 _27114 _27116 h h' t t').
Proof. exact (@lem1155340 _27114 _27116 (@pair _27114 _27116 h h') (@fst _27114 _27116) (@ZIP _27114 _27116 t t')). Qed.
Lemma lem1155343 {A B : Type'} (y : B) (x : A) : (term170 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem1155344 {_27114 _27116 : Type'} (y : _27116) (x : _27114) : (term170 _27114 _27116 x y) = x.
Proof. exact (@lem1155343 _27114 _27116 y x). Qed.
Lemma lem1155345 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) : (term170 _27114 _27116 h h') = h.
Proof. exact (@lem1155344 _27114 _27116 h' h). Qed.
Lemma lem1155346 {_27114 : Type'} : (@cons _27114) = (@cons _27114).
Proof. exact (eq_refl (@cons _27114)). Qed.
Lemma lem1155347 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) : (term171 _27114 _27116 h h') = (@cons _27114 h).
Proof. exact (MK_COMB (@lem1155346 _27114) (@lem1155345 _27114 _27116 h' h)). Qed.
Lemma lem1155349 {_27114 _27116 : Type'} (l2 : list _27116) (t : list _27114) (h1 : term8 _27114 _27116 t) : term154 _27114 _27116 l2 t.
Proof. exact (fun h0 : (@List.length _27114 t) = (@List.length _27116 l2) => @lem1155281 _27114 _27116 t l2 h1 h0). Qed.
Lemma lem1155350 {_27114 _27116 : Type'} (l2 : list _27116) (t : list _27114) (h1 : term8 _27114 _27116 t) : term154 _27114 _27116 l2 t.
Proof. exact (@lem1155349 _27114 _27116 l2 t h1). Qed.
Lemma lem1155351 {_27114 _27116 : Type'} (t' : list _27116) (t : list _27114) (h1 : term8 _27114 _27116 t) : term154 _27114 _27116 t' t.
Proof. exact (@lem1155350 _27114 _27116 t' t h1). Qed.
Lemma lem1155355 {_27114 _27116 : Type'} (t : list _27114) (t' : list _27116) (h1 : (@List.length _27114 t) = (@List.length _27116 t')) : (@List.length _27114 t) = (@List.length _27116 t').
Proof. exact (h1). Qed.
Lemma lem1155356 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1155357 {_27114 _27116 : Type'} (t : list _27114) (t' : list _27116) (h1 : (@List.length _27114 t) = (@List.length _27116 t')) : (term172 _27114 t) = (term172 _27116 t').
Proof. exact (MK_COMB (@lem1155356) (@lem1155355 _27114 _27116 t t' h1)). Qed.
Lemma lem1155358 {_27116 : Type'} (t' : list _27116) : (@List.length _27116 t') = (@List.length _27116 t').
Proof. exact (eq_refl (@List.length _27116 t')). Qed.
Lemma lem1155359 {_27114 _27116 : Type'} (t : list _27114) (t' : list _27116) (h1 : (@List.length _27114 t) = (@List.length _27116 t')) : ((@List.length _27114 t) = (@List.length _27116 t')) = ((@List.length _27116 t') = (@List.length _27116 t')).
Proof. exact (MK_COMB (@lem1155357 _27114 _27116 t t' h1) (@lem1155358 _27116 t')). Qed.
Lemma lem1155361 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1155362 (x : nat) : (x = x) = True.
Proof. exact (@lem1155361 nat x). Qed.
Lemma lem1155363 {_27116 : Type'} (t' : list _27116) : ((@List.length _27116 t') = (@List.length _27116 t')) = True.
Proof. exact (@lem1155362 (@List.length _27116 t')). Qed.
Lemma lem1155364 {_27114 _27116 : Type'} (t : list _27114) (t' : list _27116) (h1 : (@List.length _27114 t) = (@List.length _27116 t')) : ((@List.length _27114 t) = (@List.length _27116 t')) = True.
Proof. exact (TRANS (@lem1155359 _27114 _27116 t t' h1) (@lem1155363 _27116 t')). Qed.
Lemma lem1155365 {_27114 _27116 : Type'} (t : list _27114) (t' : list _27116) (h1 : (@List.length _27114 t) = (@List.length _27116 t')) : True = ((@List.length _27114 t) = (@List.length _27116 t')).
Proof. exact (SYM (@lem1155364 _27114 _27116 t t' h1)). Qed.
Lemma lem1155366 {_27114 _27116 : Type'} (t : list _27114) (t' : list _27116) (h1 : (@List.length _27114 t) = (@List.length _27116 t')) : (@List.length _27114 t) = (@List.length _27116 t').
Proof. exact (EQ_MP (@lem1155365 _27114 _27116 t t' h1) (@lem0)). Qed.
Lemma lem1155367 {_27114 _27116 : Type'} (t : list _27114) (t' : list _27116) (h1 : term8 _27114 _27116 t) (h2 : (@List.length _27114 t) = (@List.length _27116 t')) : (term155 _27114 _27116 t t') = t.
Proof. exact (@lem1155351 _27114 _27116 t' t h1 (@lem1155366 _27114 _27116 t t' h2)). Qed.
Lemma lem1155368 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (t' : list _27116) (h1 : term8 _27114 _27116 t) (h2 : (@List.length _27114 t) = (@List.length _27116 t')) : (term169 _27114 _27116 h h' t t') = (@cons _27114 h t).
Proof. exact (MK_COMB (@lem1155347 _27114 _27116 h' h) (@lem1155367 _27114 _27116 t t' h1 h2)). Qed.
Lemma lem1155369 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (t' : list _27116) (h1 : term8 _27114 _27116 t) (h2 : (@List.length _27114 t) = (@List.length _27116 t')) : (term166 _27114 _27116 h h' t t') = (@cons _27114 h t).
Proof. exact (TRANS (@lem1155341 _27114 _27116 h h' t t') (@lem1155368 _27114 _27116 h' h t t' h1 h2)). Qed.
Lemma lem1155370 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (t' : list _27116) (h1 : term8 _27114 _27116 t) (h2 : (@List.length _27114 t) = (@List.length _27116 t')) : (term157 _27114 _27116 h t h' t') = (@cons _27114 h t).
Proof. exact (TRANS (@lem1155337 _27114 _27116 h h' t t') (@lem1155369 _27114 _27116 h' h t t' h1 h2)). Qed.
Lemma lem1155371 {_27114 : Type'} : (@eq (list _27114)) = (@eq (list _27114)).
Proof. exact (eq_refl (@eq (list _27114))). Qed.
Lemma lem1155372 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (t' : list _27116) (h1 : term8 _27114 _27116 t) (h2 : (@List.length _27114 t) = (@List.length _27116 t')) : (term173 _27114 _27116 h t h' t') = (term174 _27114 h t).
Proof. exact (MK_COMB (@lem1155371 _27114) (@lem1155370 _27114 _27116 h' h t t' h1 h2)). Qed.
Lemma lem1155373 {_27114 : Type'} (h : _27114) (t : list _27114) : (@cons _27114 h t) = (@cons _27114 h t).
Proof. exact (eq_refl (@cons _27114 h t)). Qed.
Lemma lem1155374 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (t' : list _27116) (h1 : term8 _27114 _27116 t) (h2 : (@List.length _27114 t) = (@List.length _27116 t')) : ((term157 _27114 _27116 h t h' t') = (@cons _27114 h t)) = ((@cons _27114 h t) = (@cons _27114 h t)).
Proof. exact (MK_COMB (@lem1155372 _27114 _27116 h' h t t' h1 h2) (@lem1155373 _27114 h t)). Qed.
Lemma lem1155376 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1155377 {_27114 : Type'} (x : list _27114) : (x = x) = True.
Proof. exact (@lem1155376 (list _27114) x). Qed.
Lemma lem1155378 {_27114 : Type'} (h : _27114) (t : list _27114) : ((@cons _27114 h t) = (@cons _27114 h t)) = True.
Proof. exact (@lem1155377 _27114 (@cons _27114 h t)). Qed.
Lemma lem1155379 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (t' : list _27116) (h1 : term8 _27114 _27116 t) (h2 : (@List.length _27114 t) = (@List.length _27116 t')) : ((term157 _27114 _27116 h t h' t') = (@cons _27114 h t)) = True.
Proof. exact (TRANS (@lem1155374 _27114 _27116 h' h t t' h1 h2) (@lem1155378 _27114 h t)). Qed.
Lemma lem1155380 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (h1 : term8 _27114 _27116 t) : term175 _27114 _27116 h' t' h t.
Proof. exact (fun h0 : (@List.length _27114 t) = (@List.length _27116 t') => @lem1155379 _27114 _27116 h' h t t' h1 h0). Qed.
Lemma lem1155381 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (t' : list _27116) : term176 _27114 _27116 h' h t t'.
Proof. exact (@lem1155328 _27114 _27116 h' h t t' True). Qed.
Lemma lem1155382 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t' : list _27116) (t : list _27114) (h1 : term8 _27114 _27116 t) : (term71 _27114 _27116 h' t' h t) = (term177 _27114 _27116 t t').
Proof. exact (@lem1155381 _27114 _27116 h' h t t' (@lem1155380 _27114 _27116 h' t' h t h1)). Qed.
Lemma lem1155386 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1155387 {_27114 _27116 : Type'} (t : list _27114) (t' : list _27116) : (term177 _27114 _27116 t t') = True.
Proof. exact (@lem1155386 ((@List.length _27114 t) = (@List.length _27116 t'))). Qed.
Lemma lem1155388 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (h1 : term8 _27114 _27116 t) : (term71 _27114 _27116 h' t' h t) = True.
Proof. exact (TRANS (@lem1155382 _27114 _27116 h' h t' t h1) (@lem1155387 _27114 _27116 t t')). Qed.
Lemma lem1155389 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (h1 : term8 _27114 _27116 t) : True = (term71 _27114 _27116 h' t' h t).
Proof. exact (SYM (@lem1155388 _27114 _27116 h' t' h t h1)). Qed.
Lemma lem1155390 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (h1 : term8 _27114 _27116 t) : term71 _27114 _27116 h' t' h t.
Proof. exact (EQ_MP (@lem1155389 _27114 _27116 h' t' h t h1) (@lem0)). Qed.
Lemma lem1155391 {_27114 _27116 : Type'} (h' : _27116) (t' : list _27116) (h : _27114) (t : list _27114) (h1 : term8 _27114 _27116 t) : term73 _27114 _27116 h' t' h t.
Proof. exact (fun h0 : term67 _27114 _27116 t' h t => @lem1155390 _27114 _27116 h' t' h t h1). Qed.
Lemma lem1155396 {_27114 _27116 : Type'} (h' : _27116) (h : _27114) (t : list _27114) (h1 : term8 _27114 _27116 t) : term77 _27114 _27116 h' h t.
Proof. exact (fun t' : list _27116 => @lem1155391 _27114 _27116 h' t' h t h1). Qed.
Lemma lem1155401 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (h1 : term8 _27114 _27116 t) : term81 _27114 _27116 h t.
Proof. exact (fun h' : _27116 => @lem1155396 _27114 _27116 h' h t h1). Qed.
Lemma lem1155402 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (h1 : term8 _27114 _27116 t) : term83 _27114 _27116 h t.
Proof. exact (conj (@lem1155224 _27114 _27116 h t) (@lem1155401 _27114 _27116 h t h1)). Qed.
Lemma lem1155403 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) (h1 : term8 _27114 _27116 t) : term12 _27114 _27116 h t.
Proof. exact (@lem1154886 _27114 _27116 h t (@lem1155402 _27114 _27116 h t h1)). Qed.
Lemma lem1155404 {_27114 _27116 : Type'} (h : _27116) (t : list _27116) : term44 _27114 _27116 h t.
Proof. exact (fun h0 : term38 _27114 _27116 t => @lem1155115 _27114 _27116 h t). Qed.
Lemma lem1155409 {_27114 _27116 : Type'} (h : _27116) : term48 _27114 _27116 h.
Proof. exact (fun t : list _27116 => @lem1155404 _27114 _27116 h t). Qed.
Lemma lem1155414 {_27114 _27116 : Type'} : term52 _27114 _27116.
Proof. exact (fun h : _27116 => @lem1155409 _27114 _27116 h). Qed.
Lemma lem1155415 {_27114 _27116 : Type'} : term54 _27114 _27116.
Proof. exact (conj (@lem1155009 _27114 _27116) (@lem1155414 _27114 _27116)). Qed.
Lemma lem1155416 {_27114 _27116 : Type'} : term4 _27114 _27116.
Proof. exact (@lem1154858 _27114 _27116 (@lem1155415 _27114 _27116)). Qed.
Lemma lem1155417 {_27114 _27116 : Type'} (h : _27114) (t : list _27114) : term14 _27114 _27116 h t.
Proof. exact (fun h0 : term8 _27114 _27116 t => @lem1155403 _27114 _27116 h t h0). Qed.
Lemma lem1155422 {_27114 _27116 : Type'} (h : _27114) : term18 _27114 _27116 h.
Proof. exact (fun t : list _27114 => @lem1155417 _27114 _27116 h t). Qed.
Lemma lem1155427 {_27114 _27116 : Type'} : term22 _27114 _27116.
Proof. exact (fun h : _27114 => @lem1155422 _27114 _27116 h). Qed.
Lemma lem1155428 {_27114 _27116 : Type'} : term24 _27114 _27116.
Proof. exact (conj (@lem1155416 _27114 _27116) (@lem1155427 _27114 _27116)). Qed.
Lemma lem1155429 {_27114 _27116 : Type'} : term29 _27114 _27116.
Proof. exact (@lem1154830 _27114 _27116 (@lem1155428 _27114 _27116)). Qed.
