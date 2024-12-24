Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_ADD_ASSOC_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import TREAL_EQ_AP_spec.
Require Import thm0_spec.
Require Import thm1320203_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import treal_add_spec.
Lemma lem1327797 (x : hreal) : term0 x.
Proof. exact (@lem1320203 x). Qed.
Lemma lem1327798 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1327799 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1327798 x) (@lem1327797 x)). Qed.
Lemma lem1327800 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1327799 x y). Qed.
Lemma lem1327801 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1327802 (x : hreal) (y : hreal) : term3 x y.
Proof. exact (EQ_MP (@lem1327801 x y) (@lem1327800 x y)). Qed.
Lemma lem1327803 (x : hreal) (y : hreal) (z : hreal) : term4 x y z.
Proof. exact (@lem1327802 x y z). Qed.
Lemma lem1327804 (x : hreal) (y : hreal) (z : hreal) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem1327806 (x1 : hreal) : term7 x1.
Proof. exact (@lem1323802 x1). Qed.
Lemma lem1327807 (x1 : hreal) : (term7 x1) = (term8 x1).
Proof. exact (eq_refl (term7 x1)). Qed.
Lemma lem1327808 (x1 : hreal) : term8 x1.
Proof. exact (EQ_MP (@lem1327807 x1) (@lem1327806 x1)). Qed.
Lemma lem1327809 (x1 : hreal) (x2 : hreal) : term9 x1 x2.
Proof. exact (@lem1327808 x1 x2). Qed.
Lemma lem1327810 (x1 : hreal) (x2 : hreal) : (term9 x1 x2) = (term10 x1 x2).
Proof. exact (eq_refl (term9 x1 x2)). Qed.
Lemma lem1327811 (x1 : hreal) (x2 : hreal) : term10 x1 x2.
Proof. exact (EQ_MP (@lem1327810 x1 x2) (@lem1327809 x1 x2)). Qed.
Lemma lem1327812 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term11 x1 x2 y1.
Proof. exact (@lem1327811 x1 x2 y1). Qed.
Lemma lem1327813 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term11 x1 x2 y1) = (term12 x1 x2 y1).
Proof. exact (eq_refl (term11 x1 x2 y1)). Qed.
Lemma lem1327814 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term12 x1 x2 y1.
Proof. exact (EQ_MP (@lem1327813 x1 x2 y1) (@lem1327812 x1 x2 y1)). Qed.
Lemma lem1327815 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : term13 x1 x2 y1 y2.
Proof. exact (@lem1327814 x1 x2 y1 y2). Qed.
Lemma lem1327816 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term13 x1 x2 y1 y2) = ((term14 x1 y1 x2 y2) = (term15 x1 x2 y1 y2)).
Proof. exact (eq_refl (term13 x1 x2 y1 y2)). Qed.
Lemma lem1327818 (x : prod hreal hreal) : term16 x.
Proof. exact (@lem1326851 x). Qed.
Lemma lem1327819 (x : prod hreal hreal) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1327820 (x : prod hreal hreal) : term17 x.
Proof. exact (EQ_MP (@lem1327819 x) (@lem1327818 x)). Qed.
Lemma lem1327821 (x : prod hreal hreal) (y : prod hreal hreal) : term18 x y.
Proof. exact (@lem1327820 x y). Qed.
Lemma lem1327822 (x : prod hreal hreal) (y : prod hreal hreal) : (term18 x y) = (term19 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1327823 (x : prod hreal hreal) (y : prod hreal hreal) : term19 x y.
Proof. exact (EQ_MP (@lem1327822 x y) (@lem1327821 x y)). Qed.
Lemma lem1327824 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1327825 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : treal_eq x y.
Proof. exact (@lem1327823 x y (@lem1327824 x y h1)). Qed.
Lemma lem1327826 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((treal_eq x y) = True).
Proof. exact (@lem7 (treal_eq x y)). Qed.
Lemma lem1327827 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : (treal_eq x y) = True.
Proof. exact (EQ_MP (@lem1327826 x y) (@lem1327825 x y h1)). Qed.
Lemma lem1327833 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term20 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1327834 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term20 _5106 _5107 P) = ((term21 _5106 _5107 P) = (term22 _5106 _5107 P)).
Proof. exact (eq_refl (term20 _5106 _5107 P)). Qed.
Lemma lem1327841 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = (term22 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1327834 _5106 _5107 P) (@lem1327833 _5106 _5107 P)). Qed.
Lemma lem1327842 (P : type1233) : (term23 P) = (term24 P).
Proof. exact (@lem1327841 hreal hreal P). Qed.
Lemma lem1327843 : term25 = term26.
Proof. exact (@lem1327842 term27). Qed.
Lemma lem1327844 (x : prod hreal hreal) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1327845 : term30 = term27.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1327844 x)). Qed.
Lemma lem1327846 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1327847 : term25 = term31.
Proof. exact (MK_COMB (@lem1327846) (@lem1327845)). Qed.
Lemma lem1327848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1327849 : term32 = term33.
Proof. exact (MK_COMB (@lem1327848) (@lem1327847)). Qed.
Lemma lem1327850 (p1 : hreal) (p2 : hreal) : (term34 p1 p2) = (term35 p1 p2).
Proof. exact (eq_refl (term34 p1 p2)). Qed.
Lemma lem1327851 (p1 : hreal) : (term36 p1) = (term37 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1327850 p1 p2)). Qed.
Lemma lem1327852 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327853 (p1 : hreal) : (term38 p1) = (term39 p1).
Proof. exact (MK_COMB (@lem1327852) (@lem1327851 p1)). Qed.
Lemma lem1327854 : term40 = term41.
Proof. exact (fun_ext (fun p1 : hreal => @lem1327853 p1)). Qed.
Lemma lem1327855 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327856 : term26 = term42.
Proof. exact (MK_COMB (@lem1327855) (@lem1327854)). Qed.
Lemma lem1327857 : (term25 = term26) = (term31 = term42).
Proof. exact (MK_COMB (@lem1327849) (@lem1327856)). Qed.
Lemma lem1327858 : term31 = term42.
Proof. exact (EQ_MP (@lem1327857) (@lem1327843)). Qed.
Lemma lem1327876 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = (term22 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1327834 _5106 _5107 P) (@lem1327833 _5106 _5107 P)). Qed.
Lemma lem1327877 (P : type1233) : (term23 P) = (term24 P).
Proof. exact (@lem1327876 hreal hreal P). Qed.
Lemma lem1327878 (p1 : hreal) (p2 : hreal) : (term43 p1 p2) = (term44 p1 p2).
Proof. exact (@lem1327877 (term45 p1 p2)). Qed.
Lemma lem1327879 (p1 : hreal) (p2 : hreal) (y : prod hreal hreal) : (term46 p1 p2 y) = (term47 p1 p2 y).
Proof. exact (eq_refl (term46 p1 p2 y)). Qed.
Lemma lem1327880 (p1 : hreal) (p2 : hreal) : (term48 p1 p2) = (term45 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1327879 p1 p2 y)). Qed.
Lemma lem1327881 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1327882 (p1 : hreal) (p2 : hreal) : (term43 p1 p2) = (term35 p1 p2).
Proof. exact (MK_COMB (@lem1327881) (@lem1327880 p1 p2)). Qed.
Lemma lem1327883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1327884 (p1 : hreal) (p2 : hreal) : (term49 p1 p2) = (term50 p1 p2).
Proof. exact (MK_COMB (@lem1327883) (@lem1327882 p1 p2)). Qed.
Lemma lem1327885 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term51 p1 p2 p1' p2') = (term52 p1 p2 p1' p2').
Proof. exact (eq_refl (term51 p1 p2 p1' p2')). Qed.
Lemma lem1327886 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term53 p1 p2 p1') = (term54 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1327885 p1 p2 p1' p2')). Qed.
Lemma lem1327887 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327888 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term55 p1 p2 p1') = (term56 p1 p2 p1').
Proof. exact (MK_COMB (@lem1327887) (@lem1327886 p1 p2 p1')). Qed.
Lemma lem1327889 (p1 : hreal) (p2 : hreal) : (term57 p1 p2) = (term58 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1327888 p1 p2 p1')). Qed.
Lemma lem1327890 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327891 (p1 : hreal) (p2 : hreal) : (term44 p1 p2) = (term59 p1 p2).
Proof. exact (MK_COMB (@lem1327890) (@lem1327889 p1 p2)). Qed.
Lemma lem1327892 (p1 : hreal) (p2 : hreal) : ((term43 p1 p2) = (term44 p1 p2)) = ((term35 p1 p2) = (term59 p1 p2)).
Proof. exact (MK_COMB (@lem1327884 p1 p2) (@lem1327891 p1 p2)). Qed.
Lemma lem1327893 (p1 : hreal) (p2 : hreal) : (term35 p1 p2) = (term59 p1 p2).
Proof. exact (EQ_MP (@lem1327892 p1 p2) (@lem1327878 p1 p2)). Qed.
Lemma lem1327911 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = (term22 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1327834 _5106 _5107 P) (@lem1327833 _5106 _5107 P)). Qed.
Lemma lem1327912 (P : type1233) : (term23 P) = (term24 P).
Proof. exact (@lem1327911 hreal hreal P). Qed.
Lemma lem1327913 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term60 p1 p2 p1' p2') = (term61 p1 p2 p1' p2').
Proof. exact (@lem1327912 (term62 p1 p2 p1' p2')). Qed.
Lemma lem1327914 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (z : prod hreal hreal) : (term63 p1 p2 p1' p2' z) = (term64 p1 p2 p1' p2' z).
Proof. exact (eq_refl (term63 p1 p2 p1' p2' z)). Qed.
Lemma lem1327915 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term65 p1 p2 p1' p2') = (term62 p1 p2 p1' p2').
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1327914 p1 p2 p1' p2' z)). Qed.
Lemma lem1327916 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1327917 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term60 p1 p2 p1' p2') = (term52 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1327916) (@lem1327915 p1 p2 p1' p2')). Qed.
Lemma lem1327918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1327919 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term66 p1 p2 p1' p2') = (term67 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1327918) (@lem1327917 p1 p2 p1' p2')). Qed.
Lemma lem1327920 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : (term68 p1 p2 p1' p2' p1'' p2'') = (term69 p1 p2 p1' p2' p1'' p2'').
Proof. exact (eq_refl (term68 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1327921 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term70 p1 p2 p1' p2' p1'') = (term71 p1 p2 p1' p2' p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1327920 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1327922 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327923 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term72 p1 p2 p1' p2' p1'') = (term73 p1 p2 p1' p2' p1'').
Proof. exact (MK_COMB (@lem1327922) (@lem1327921 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1327924 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term74 p1 p2 p1' p2') = (term75 p1 p2 p1' p2').
Proof. exact (fun_ext (fun p1'' : hreal => @lem1327923 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1327925 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327926 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term61 p1 p2 p1' p2') = (term76 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1327925) (@lem1327924 p1 p2 p1' p2')). Qed.
Lemma lem1327927 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : ((term60 p1 p2 p1' p2') = (term61 p1 p2 p1' p2')) = ((term52 p1 p2 p1' p2') = (term76 p1 p2 p1' p2')).
Proof. exact (MK_COMB (@lem1327919 p1 p2 p1' p2') (@lem1327926 p1 p2 p1' p2')). Qed.
Lemma lem1327928 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term52 p1 p2 p1' p2') = (term76 p1 p2 p1' p2').
Proof. exact (EQ_MP (@lem1327927 p1 p2 p1' p2') (@lem1327913 p1 p2 p1' p2')). Qed.
Lemma lem1327942 (x : prod hreal hreal) (y : prod hreal hreal) : term77 x y.
Proof. exact (fun h0 : x = y => @lem1327827 x y h0). Qed.
Lemma lem1327943 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : term78 p1 p2 p1' p2' p1'' p2''.
Proof. exact (@lem1327942 (term79 p1 p2 p1' p2' p1'' p2'') (term80 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1327947 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term14 x1 y1 x2 y2) = (term15 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1327816 x1 x2 y1 y2) (@lem1327815 x1 x2 y1 y2)). Qed.
Lemma lem1327948 (p1' : hreal) (p1'' : hreal) (p2' : hreal) (p2'' : hreal) : (term14 p1' p2' p1'' p2'') = (term15 p1' p1'' p2' p2'').
Proof. exact (@lem1327947 p1' p1'' p2' p2''). Qed.
Lemma lem1327949 (p1 : hreal) (p2 : hreal) : (term81 p1 p2) = (term81 p1 p2).
Proof. exact (eq_refl (term81 p1 p2)). Qed.
Lemma lem1327950 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) (p2' : hreal) (p2'' : hreal) : (term79 p1 p2 p1' p2' p1'' p2'') = (term82 p1 p2 p1' p1'' p2' p2'').
Proof. exact (MK_COMB (@lem1327949 p1 p2) (@lem1327948 p1' p1'' p2' p2'')). Qed.
Lemma lem1327952 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term14 x1 y1 x2 y2) = (term15 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1327816 x1 x2 y1 y2) (@lem1327815 x1 x2 y1 y2)). Qed.
Lemma lem1327953 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term82 p1 p2 p1' p1'' p2' p2'') = (term83 p1 p1' p1'' p2 p2' p2'').
Proof. exact (@lem1327952 p1 (hreal_add p1' p1'') p2 (hreal_add p2' p2'')). Qed.
Lemma lem1327955 (x : hreal) (y : hreal) (z : hreal) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem1327804 x y z) (@lem1327803 x y z)). Qed.
Lemma lem1327956 (p1 : hreal) (p1' : hreal) (p1'' : hreal) : (term5 p1 p1' p1'') = (term6 p1 p1' p1'').
Proof. exact (@lem1327955 p1 p1' p1''). Qed.
Lemma lem1327957 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1327958 (p1 : hreal) (p1' : hreal) (p1'' : hreal) : (term84 p1 p1' p1'') = (term85 p1 p1' p1'').
Proof. exact (MK_COMB (@lem1327957) (@lem1327956 p1 p1' p1'')). Qed.
Lemma lem1327960 (x : hreal) (y : hreal) (z : hreal) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem1327804 x y z) (@lem1327803 x y z)). Qed.
Lemma lem1327961 (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term5 p2 p2' p2'') = (term6 p2 p2' p2'').
Proof. exact (@lem1327960 p2 p2' p2''). Qed.
Lemma lem1327962 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term83 p1 p1' p1'' p2 p2' p2'') = (term86 p1 p1' p1'' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1327958 p1 p1' p1'') (@lem1327961 p2 p2' p2'')). Qed.
Lemma lem1327963 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term82 p1 p2 p1' p1'' p2' p2'') = (term86 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1327953 p1 p1' p1'' p2 p2' p2'') (@lem1327962 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1327964 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term79 p1 p2 p1' p2' p1'' p2'') = (term86 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1327950 p1 p2 p1' p1'' p2' p2'') (@lem1327963 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1327965 : (@eq (prod hreal hreal)) = (@eq (prod hreal hreal)).
Proof. exact (eq_refl (@eq (prod hreal hreal))). Qed.
Lemma lem1327966 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term87 p1 p2 p1' p2' p1'' p2'') = (term88 p1 p1' p1'' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1327965) (@lem1327964 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1327968 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term14 x1 y1 x2 y2) = (term15 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1327816 x1 x2 y1 y2) (@lem1327815 x1 x2 y1 y2)). Qed.
Lemma lem1327969 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term14 p1 p2 p1' p2') = (term15 p1 p1' p2 p2').
Proof. exact (@lem1327968 p1 p1' p2 p2'). Qed.
Lemma lem1327970 : treal_add = treal_add.
Proof. exact (eq_refl treal_add). Qed.
Lemma lem1327971 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term89 p1 p2 p1' p2') = (term90 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1327970) (@lem1327969 p1 p1' p2 p2')). Qed.
Lemma lem1327972 (p1'' : hreal) (p2'' : hreal) : (@pair hreal hreal p1'' p2'') = (@pair hreal hreal p1'' p2'').
Proof. exact (eq_refl (@pair hreal hreal p1'' p2'')). Qed.
Lemma lem1327973 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : (term80 p1 p2 p1' p2' p1'' p2'') = (term91 p1 p1' p2 p2' p1'' p2'').
Proof. exact (MK_COMB (@lem1327971 p1 p1' p2 p2') (@lem1327972 p1'' p2'')). Qed.
Lemma lem1327975 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term14 x1 y1 x2 y2) = (term15 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1327816 x1 x2 y1 y2) (@lem1327815 x1 x2 y1 y2)). Qed.
Lemma lem1327976 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term91 p1 p1' p2 p2' p1'' p2'') = (term86 p1 p1' p1'' p2 p2' p2'').
Proof. exact (@lem1327975 (hreal_add p1 p1') p1'' (hreal_add p2 p2') p2''). Qed.
Lemma lem1327977 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term80 p1 p2 p1' p2' p1'' p2'') = (term86 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1327973 p1 p1' p2 p2' p1'' p2'') (@lem1327976 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1327978 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : ((term79 p1 p2 p1' p2' p1'' p2'') = (term80 p1 p2 p1' p2' p1'' p2'')) = ((term86 p1 p1' p1'' p2 p2' p2'') = (term86 p1 p1' p1'' p2 p2' p2'')).
Proof. exact (MK_COMB (@lem1327966 p1 p1' p1'' p2 p2' p2'') (@lem1327977 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1327980 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1327981 (x : prod hreal hreal) : (x = x) = True.
Proof. exact (@lem1327980 (prod hreal hreal) x). Qed.
Lemma lem1327982 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : ((term86 p1 p1' p1'' p2 p2' p2'') = (term86 p1 p1' p1'' p2 p2' p2'')) = True.
Proof. exact (@lem1327981 (term86 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1327983 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : ((term79 p1 p2 p1' p2' p1'' p2'') = (term80 p1 p2 p1' p2' p1'' p2'')) = True.
Proof. exact (TRANS (@lem1327978 p1 p1' p1'' p2 p2' p2'') (@lem1327982 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1327984 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : True = ((term79 p1 p2 p1' p2' p1'' p2'') = (term80 p1 p2 p1' p2' p1'' p2'')).
Proof. exact (SYM (@lem1327983 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1327985 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : (term79 p1 p2 p1' p2' p1'' p2'') = (term80 p1 p2 p1' p2' p1'' p2'').
Proof. exact (EQ_MP (@lem1327984 p1 p2 p1' p2' p1'' p2'') (@lem0)). Qed.
Lemma lem1327986 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : (term69 p1 p2 p1' p2' p1'' p2'') = True.
Proof. exact (@lem1327943 p1 p2 p1' p2' p1'' p2'' (@lem1327985 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1327987 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term71 p1 p2 p1' p2' p1'') = term92.
Proof. exact (fun_ext (fun p2'' : hreal => @lem1327986 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1327988 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327989 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term73 p1 p2 p1' p2' p1'') = term93.
Proof. exact (MK_COMB (@lem1327988) (@lem1327987 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1327991 {A : Type'} (t : Prop) : (term94 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327992 (t : Prop) : (term95 t) = t.
Proof. exact (@lem1327991 hreal t). Qed.
Lemma lem1327993 : term93 = True.
Proof. exact (@lem1327992 True). Qed.
Lemma lem1327994 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term73 p1 p2 p1' p2' p1'') = True.
Proof. exact (TRANS (@lem1327989 p1 p2 p1' p2' p1'') (@lem1327993)). Qed.
Lemma lem1327995 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term75 p1 p2 p1' p2') = term92.
Proof. exact (fun_ext (fun p1'' : hreal => @lem1327994 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1327996 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327997 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term76 p1 p2 p1' p2') = term93.
Proof. exact (MK_COMB (@lem1327996) (@lem1327995 p1 p2 p1' p2')). Qed.
Lemma lem1327999 {A : Type'} (t : Prop) : (term94 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328000 (t : Prop) : (term95 t) = t.
Proof. exact (@lem1327999 hreal t). Qed.
Lemma lem1328001 : term93 = True.
Proof. exact (@lem1328000 True). Qed.
Lemma lem1328002 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term76 p1 p2 p1' p2') = True.
Proof. exact (TRANS (@lem1327997 p1 p2 p1' p2') (@lem1328001)). Qed.
Lemma lem1328003 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term52 p1 p2 p1' p2') = True.
Proof. exact (TRANS (@lem1327928 p1 p2 p1' p2') (@lem1328002 p1 p2 p1' p2')). Qed.
Lemma lem1328004 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term54 p1 p2 p1') = term92.
Proof. exact (fun_ext (fun p2' : hreal => @lem1328003 p1 p2 p1' p2')). Qed.
Lemma lem1328005 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328006 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term56 p1 p2 p1') = term93.
Proof. exact (MK_COMB (@lem1328005) (@lem1328004 p1 p2 p1')). Qed.
Lemma lem1328008 {A : Type'} (t : Prop) : (term94 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328009 (t : Prop) : (term95 t) = t.
Proof. exact (@lem1328008 hreal t). Qed.
Lemma lem1328010 : term93 = True.
Proof. exact (@lem1328009 True). Qed.
Lemma lem1328011 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term56 p1 p2 p1') = True.
Proof. exact (TRANS (@lem1328006 p1 p2 p1') (@lem1328010)). Qed.
Lemma lem1328012 (p1 : hreal) (p2 : hreal) : (term58 p1 p2) = term92.
Proof. exact (fun_ext (fun p1' : hreal => @lem1328011 p1 p2 p1')). Qed.
Lemma lem1328013 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328014 (p1 : hreal) (p2 : hreal) : (term59 p1 p2) = term93.
Proof. exact (MK_COMB (@lem1328013) (@lem1328012 p1 p2)). Qed.
Lemma lem1328016 {A : Type'} (t : Prop) : (term94 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328017 (t : Prop) : (term95 t) = t.
Proof. exact (@lem1328016 hreal t). Qed.
Lemma lem1328018 : term93 = True.
Proof. exact (@lem1328017 True). Qed.
Lemma lem1328019 (p1 : hreal) (p2 : hreal) : (term59 p1 p2) = True.
Proof. exact (TRANS (@lem1328014 p1 p2) (@lem1328018)). Qed.
Lemma lem1328020 (p1 : hreal) (p2 : hreal) : (term35 p1 p2) = True.
Proof. exact (TRANS (@lem1327893 p1 p2) (@lem1328019 p1 p2)). Qed.
Lemma lem1328021 (p1 : hreal) : (term37 p1) = term92.
Proof. exact (fun_ext (fun p2 : hreal => @lem1328020 p1 p2)). Qed.
Lemma lem1328022 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328023 (p1 : hreal) : (term39 p1) = term93.
Proof. exact (MK_COMB (@lem1328022) (@lem1328021 p1)). Qed.
Lemma lem1328025 {A : Type'} (t : Prop) : (term94 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328026 (t : Prop) : (term95 t) = t.
Proof. exact (@lem1328025 hreal t). Qed.
Lemma lem1328027 : term93 = True.
Proof. exact (@lem1328026 True). Qed.
Lemma lem1328028 (p1 : hreal) : (term39 p1) = True.
Proof. exact (TRANS (@lem1328023 p1) (@lem1328027)). Qed.
Lemma lem1328029 : term41 = term92.
Proof. exact (fun_ext (fun p1 : hreal => @lem1328028 p1)). Qed.
Lemma lem1328030 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328031 : term42 = term93.
Proof. exact (MK_COMB (@lem1328030) (@lem1328029)). Qed.
Lemma lem1328033 {A : Type'} (t : Prop) : (term94 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328034 (t : Prop) : (term95 t) = t.
Proof. exact (@lem1328033 hreal t). Qed.
Lemma lem1328035 : term93 = True.
Proof. exact (@lem1328034 True). Qed.
Lemma lem1328036 : term42 = True.
Proof. exact (TRANS (@lem1328031) (@lem1328035)). Qed.
Lemma lem1328037 : term31 = True.
Proof. exact (TRANS (@lem1327858) (@lem1328036)). Qed.
Lemma lem1328038 : True = term31.
Proof. exact (SYM (@lem1328037)). Qed.
Lemma lem1328039 : term31.
Proof. exact (EQ_MP (@lem1328038) (@lem0)). Qed.
