Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_IMP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_INDUCT_spec.
Require Import FINITE_RULES_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import UNION_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem3603931 {A : Type'} : term0 A.
Proof. exact (proj1 (@lem3235853 A)). Qed.
Lemma lem3603932 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (@lem3603931 A s). Qed.
Lemma lem3603933 {A : Type'} (s : A -> Prop) : (term1 A s) = ((@UNION A (@EMPTY A) s) = s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3603935 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem3603936 {A : Type'} (FINITE' : type686 A) (h1 : term2 A) : term3 A FINITE'.
Proof. exact (@lem3603935 A h1 FINITE'). Qed.
Lemma lem3603937 {A : Type'} (FINITE' : type686 A) : (term3 A FINITE') = (term4 A FINITE').
Proof. exact (eq_refl (term3 A FINITE')). Qed.
Lemma lem3603938 {A : Type'} (FINITE' : type686 A) (h1 : term2 A) : term4 A FINITE'.
Proof. exact (EQ_MP (@lem3603937 A FINITE') (@lem3603936 A FINITE' h1)). Qed.
Lemma lem3603939 {A : Type'} (FINITE' : type686 A) (h1 : term5 A FINITE') : term5 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3603940 {A : Type'} (FINITE' : type686 A) (h1 : term2 A) (h2 : term5 A FINITE') : term6 A FINITE'.
Proof. exact (@lem3603938 A FINITE' h1 (@lem3603939 A FINITE' h2)). Qed.
Lemma lem3603941 {A : Type'} (FINITE' : type686 A) (h1 : term5 A FINITE') : term7 A FINITE'.
Proof. exact (fun h0 : term2 A => @lem3603940 A FINITE' h0 h1). Qed.
Lemma lem3603942 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem3603943 {A : Type'} (FINITE' : type686 A) (h1 : term2 A) (h2 : term5 A FINITE') : term6 A FINITE'.
Proof. exact (@lem3603941 A FINITE' h2 (@lem3603942 A h1)). Qed.
Lemma lem3603944 {A : Type'} (FINITE' : type686 A) (h1 : term2 A) : term4 A FINITE'.
Proof. exact (fun h0 : term5 A FINITE' => @lem3603943 A FINITE' h1 h0). Qed.
Lemma lem3603945 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (fun FINITE' : type686 A => @lem3603944 A FINITE' h1). Qed.
Lemma lem3603946 {A : Type'} : term8 A.
Proof. exact (fun h0 : term2 A => @lem3603945 A h0). Qed.
Lemma lem3603947 {A : Type'} : term2 A.
Proof. exact (@lem3603946 A (@lem3197567 A)). Qed.
Lemma lem3603948 {A : Type'} (FINITE' : type686 A) : term3 A FINITE'.
Proof. exact (@lem3603947 A FINITE'). Qed.
Lemma lem3603949 {A : Type'} (FINITE' : type686 A) : (term3 A FINITE') = (term4 A FINITE').
Proof. exact (eq_refl (term3 A FINITE')). Qed.
Lemma lem3603951 {A : Type'} (P : Prop) : term9 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem3603952 {A : Type'} (P : Prop) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem3603953 {A : Type'} (P : Prop) : term10 A P.
Proof. exact (EQ_MP (@lem3603952 A P) (@lem3603951 A P)). Qed.
Lemma lem3603954 {A : Type'} (P : Prop) (Q : A -> Prop) : term11 A P Q.
Proof. exact (@lem3603953 A P Q). Qed.
Lemma lem3603955 {A : Type'} (P : Prop) (Q : A -> Prop) : (term11 A P Q) = ((term12 A P Q) = (term13 A P Q)).
Proof. exact (eq_refl (term11 A P Q)). Qed.
Lemma lem3603966 (p : Prop) (q : Prop) (r : Prop) : (term14 p q r) = (term15 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3603967 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = (term17 A s t).
Proof. exact (@lem3603966 (@FINITE A s) (@FINITE A t) (term18 A s t)). Qed.
Lemma lem3603972 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3603967 A s t)). Qed.
Lemma lem3603973 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3603974 {A : Type'} (s : A -> Prop) : (term21 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3603973 A) (@lem3603972 A s)). Qed.
Lemma lem3603979 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3603974 A s)). Qed.
Lemma lem3603980 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3603981 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (MK_COMB (@lem3603980 A) (@lem3603979 A)). Qed.
Lemma lem3603986 {A : Type'} : (term26 A) = (term25 A).
Proof. exact (SYM (@lem3603981 A)). Qed.
Lemma lem3603992 {A : Type'} (P : Prop) (Q : A -> Prop) : (term12 A P Q) = (term13 A P Q).
Proof. exact (EQ_MP (@lem3603955 A P Q) (@lem3603954 A P Q)). Qed.
Lemma lem3603993 {A : Type'} (P : Prop) (Q : type686 A) : (term27 A P Q) = (term28 A P Q).
Proof. exact (@lem3603992 (A -> Prop) P Q). Qed.
Lemma lem3603994 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (@lem3603993 A (@FINITE A s) (term31 A s)). Qed.
Lemma lem3603995 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term33 A s t).
Proof. exact (eq_refl (term32 A s t)). Qed.
Lemma lem3603996 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem3603997 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term17 A s t).
Proof. exact (MK_COMB (@lem3603996 A s) (@lem3603995 A s t)). Qed.
Lemma lem3603998 {A : Type'} (s : A -> Prop) : (term36 A s) = (term20 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3603997 A s t)). Qed.
Lemma lem3603999 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604000 {A : Type'} (s : A -> Prop) : (term29 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3603999 A) (@lem3603998 A s)). Qed.
Lemma lem3604001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3604002 {A : Type'} (s : A -> Prop) : (term37 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3604001) (@lem3604000 A s)). Qed.
Lemma lem3604003 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term33 A s t).
Proof. exact (eq_refl (term32 A s t)). Qed.
Lemma lem3604004 {A : Type'} (s : A -> Prop) : (term39 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3604003 A s t)). Qed.
Lemma lem3604005 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604006 {A : Type'} (s : A -> Prop) : (term40 A s) = (term41 A s).
Proof. exact (MK_COMB (@lem3604005 A) (@lem3604004 A s)). Qed.
Lemma lem3604007 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem3604008 {A : Type'} (s : A -> Prop) : (term30 A s) = (term42 A s).
Proof. exact (MK_COMB (@lem3604007 A s) (@lem3604006 A s)). Qed.
Lemma lem3604009 {A : Type'} (s : A -> Prop) : ((term29 A s) = (term30 A s)) = ((term22 A s) = (term42 A s)).
Proof. exact (MK_COMB (@lem3604002 A s) (@lem3604008 A s)). Qed.
Lemma lem3604010 {A : Type'} (s : A -> Prop) : (term22 A s) = (term42 A s).
Proof. exact (EQ_MP (@lem3604009 A s) (@lem3603994 A s)). Qed.
Lemma lem3604039 {A : Type'} : (term24 A) = (term43 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3604010 A s)). Qed.
Lemma lem3604040 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604041 {A : Type'} : (term26 A) = (term44 A).
Proof. exact (MK_COMB (@lem3604040 A) (@lem3604039 A)). Qed.
Lemma lem3604066 {A : Type'} : (term44 A) = (term26 A).
Proof. exact (SYM (@lem3604041 A)). Qed.
Lemma lem3604068 {A : Type'} (FINITE' : type686 A) : term4 A FINITE'.
Proof. exact (EQ_MP (@lem3603949 A FINITE') (@lem3603948 A FINITE')). Qed.
Lemma lem3604069 {A : Type'} (FINITE' : type686 A) : term4 A FINITE'.
Proof. exact (@lem3604068 A FINITE'). Qed.
Lemma lem3604070 {A : Type'} : term45 A.
Proof. exact (@lem3604069 A (term46 A)). Qed.
Lemma lem3604071 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (eq_refl (term47 A)). Qed.
Lemma lem3604072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3604073 {A : Type'} : (term49 A) = (term50 A).
Proof. exact (MK_COMB (@lem3604072) (@lem3604071 A)). Qed.
Lemma lem3604074 {A : Type'} (s : A -> Prop) : (term51 A s) = (term41 A s).
Proof. exact (eq_refl (term51 A s)). Qed.
Lemma lem3604075 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3604076 {A : Type'} (s : A -> Prop) : (term52 A s) = (term53 A s).
Proof. exact (MK_COMB (@lem3604075) (@lem3604074 A s)). Qed.
Lemma lem3604077 {A : Type'} (x : A) (s : A -> Prop) : (term54 A x s) = (term55 A x s).
Proof. exact (eq_refl (term54 A x s)). Qed.
Lemma lem3604078 {A : Type'} (x : A) (s : A -> Prop) : (term56 A x s) = (term57 A x s).
Proof. exact (MK_COMB (@lem3604076 A s) (@lem3604077 A x s)). Qed.
Lemma lem3604079 {A : Type'} (x : A) : (term58 A x) = (term59 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3604078 A x s)). Qed.
Lemma lem3604080 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604081 {A : Type'} (x : A) : (term60 A x) = (term61 A x).
Proof. exact (MK_COMB (@lem3604080 A) (@lem3604079 A x)). Qed.
Lemma lem3604082 {A : Type'} : (term62 A) = (term63 A).
Proof. exact (fun_ext (fun x : A => @lem3604081 A x)). Qed.
Lemma lem3604083 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3604084 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (MK_COMB (@lem3604083 A) (@lem3604082 A)). Qed.
Lemma lem3604085 {A : Type'} : (term66 A) = (term67 A).
Proof. exact (MK_COMB (@lem3604073 A) (@lem3604084 A)). Qed.
Lemma lem3604086 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3604087 {A : Type'} : (term68 A) = (term69 A).
Proof. exact (MK_COMB (@lem3604086) (@lem3604085 A)). Qed.
Lemma lem3604088 {A : Type'} (s : A -> Prop) : (term51 A s) = (term41 A s).
Proof. exact (eq_refl (term51 A s)). Qed.
Lemma lem3604089 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem3604090 {A : Type'} (s : A -> Prop) : (term70 A s) = (term42 A s).
Proof. exact (MK_COMB (@lem3604089 A s) (@lem3604088 A s)). Qed.
Lemma lem3604091 {A : Type'} : (term71 A) = (term43 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3604090 A s)). Qed.
Lemma lem3604092 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604093 {A : Type'} : (term72 A) = (term44 A).
Proof. exact (MK_COMB (@lem3604092 A) (@lem3604091 A)). Qed.
Lemma lem3604094 {A : Type'} : (term45 A) = (term73 A).
Proof. exact (MK_COMB (@lem3604087 A) (@lem3604093 A)). Qed.
Lemma lem3604095 {A : Type'} : term73 A.
Proof. exact (EQ_MP (@lem3604094 A) (@lem3604070 A)). Qed.
Lemma lem3604105 {A : Type'} (s : A -> Prop) : (@UNION A (@EMPTY A) s) = s.
Proof. exact (EQ_MP (@lem3603933 A s) (@lem3603932 A s)). Qed.
Lemma lem3604106 {A : Type'} (s : A -> Prop) : (@UNION A (@EMPTY A) s) = s.
Proof. exact (@lem3604105 A s). Qed.
Lemma lem3604107 {A : Type'} (t : A -> Prop) : (@UNION A (@EMPTY A) t) = t.
Proof. exact (@lem3604106 A t). Qed.
Lemma lem3604108 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3604109 {A : Type'} (t : A -> Prop) : (term74 A t) = (@FINITE A t).
Proof. exact (MK_COMB (@lem3604108 A) (@lem3604107 A t)). Qed.
Lemma lem3604110 {A : Type'} (t : A -> Prop) : (term34 A t) = (term34 A t).
Proof. exact (eq_refl (term34 A t)). Qed.
Lemma lem3604111 {A : Type'} (t : A -> Prop) : (term75 A t) = (term76 A t).
Proof. exact (MK_COMB (@lem3604110 A t) (@lem3604109 A t)). Qed.
Lemma lem3604113 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3604114 {A : Type'} (t : A -> Prop) : (term76 A t) = True.
Proof. exact (@lem3604113 (@FINITE A t)). Qed.
Lemma lem3604115 {A : Type'} (t : A -> Prop) : (term75 A t) = True.
Proof. exact (TRANS (@lem3604111 A t) (@lem3604114 A t)). Qed.
Lemma lem3604116 {A : Type'} : (term77 A) = (term78 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3604115 A t)). Qed.
Lemma lem3604117 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604118 {A : Type'} : (term48 A) = (term79 A).
Proof. exact (MK_COMB (@lem3604117 A) (@lem3604116 A)). Qed.
Lemma lem3604120 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3604121 {A : Type'} (t : Prop) : (term81 A t) = t.
Proof. exact (@lem3604120 (A -> Prop) t). Qed.
Lemma lem3604122 {A : Type'} : (term79 A) = True.
Proof. exact (@lem3604121 A True). Qed.
Lemma lem3604123 {A : Type'} : (term48 A) = True.
Proof. exact (TRANS (@lem3604118 A) (@lem3604122 A)). Qed.
Lemma lem3604124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3604125 {A : Type'} : (term50 A) = (and True).
Proof. exact (MK_COMB (@lem3604124) (@lem3604123 A)). Qed.
Lemma lem3604148 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (eq_refl (term65 A)). Qed.
Lemma lem3604149 {A : Type'} : (term67 A) = (term82 A).
Proof. exact (MK_COMB (@lem3604125 A) (@lem3604148 A)). Qed.
Lemma lem3604151 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3604152 {A : Type'} : (term82 A) = (term65 A).
Proof. exact (@lem3604151 (term65 A)). Qed.
Lemma lem3604175 {A : Type'} : (term67 A) = (term65 A).
Proof. exact (TRANS (@lem3604149 A) (@lem3604152 A)). Qed.
Lemma lem3604176 {A : Type'} : (term65 A) = (term67 A).
Proof. exact (SYM (@lem3604175 A)). Qed.
Lemma lem3604177 {A : Type'} (h1 : term83 A) : term83 A.
Proof. exact (h1). Qed.
Lemma lem3604178 {A : Type'} (x : A) (h1 : term83 A) : term84 A x.
Proof. exact (@lem3604177 A h1 x). Qed.
Lemma lem3604179 {A : Type'} (x : A) : (term84 A x) = (term85 A x).
Proof. exact (eq_refl (term84 A x)). Qed.
Lemma lem3604180 {A : Type'} (x : A) (h1 : term83 A) : term85 A x.
Proof. exact (EQ_MP (@lem3604179 A x) (@lem3604178 A x h1)). Qed.
Lemma lem3604181 {A : Type'} (x : A) (s : A -> Prop) (h1 : term83 A) : term86 A x s.
Proof. exact (@lem3604180 A x h1 s). Qed.
Lemma lem3604182 {A : Type'} (x : A) (s : A -> Prop) : (term86 A x s) = (term87 A x s).
Proof. exact (eq_refl (term86 A x s)). Qed.
Lemma lem3604183 {A : Type'} (x : A) (s : A -> Prop) (h1 : term83 A) : term87 A x s.
Proof. exact (EQ_MP (@lem3604182 A x s) (@lem3604181 A x s h1)). Qed.
Lemma lem3604184 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term83 A) : term88 A x s t.
Proof. exact (@lem3604183 A x s h1 t). Qed.
Lemma lem3604185 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term88 A x s t) = ((term89 A x s t) = (term90 A x s t)).
Proof. exact (eq_refl (term88 A x s t)). Qed.
Lemma lem3604210 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term83 A) : (term89 A x s t) = (term90 A x s t).
Proof. exact (EQ_MP (@lem3604185 A x s t) (@lem3604184 A x s t h1)). Qed.
Lemma lem3604211 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term83 A) : (term89 A x s t) = (term90 A x s t).
Proof. exact (@lem3604210 A x s t h1). Qed.
Lemma lem3604212 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3604213 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term83 A) : (term91 A x s t) = (term92 A x s t).
Proof. exact (MK_COMB (@lem3604212 A) (@lem3604211 A x s t h1)). Qed.
Lemma lem3604214 {A : Type'} (t : A -> Prop) : (term34 A t) = (term34 A t).
Proof. exact (eq_refl (term34 A t)). Qed.
Lemma lem3604215 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term83 A) : (term93 A x s t) = (term94 A x s t).
Proof. exact (MK_COMB (@lem3604214 A t) (@lem3604213 A x s t h1)). Qed.
Lemma lem3604218 {A : Type'} (x : A) (s : A -> Prop) (h1 : term83 A) : (term95 A x s) = (term96 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3604215 A x s t h1)). Qed.
Lemma lem3604219 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604220 {A : Type'} (x : A) (s : A -> Prop) (h1 : term83 A) : (term55 A x s) = (term97 A x s).
Proof. exact (MK_COMB (@lem3604219 A) (@lem3604218 A x s h1)). Qed.
Lemma lem3604225 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (eq_refl (term53 A s)). Qed.
Lemma lem3604226 {A : Type'} (x : A) (s : A -> Prop) (h1 : term83 A) : (term57 A x s) = (term98 A x s).
Proof. exact (MK_COMB (@lem3604225 A s) (@lem3604220 A x s h1)). Qed.
Lemma lem3604229 {A : Type'} (x : A) (h1 : term83 A) : (term59 A x) = (term99 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3604226 A x s h1)). Qed.
Lemma lem3604230 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604231 {A : Type'} (x : A) (h1 : term83 A) : (term61 A x) = (term100 A x).
Proof. exact (MK_COMB (@lem3604230 A) (@lem3604229 A x h1)). Qed.
Lemma lem3604236 {A : Type'} (h1 : term83 A) : (term63 A) = (term101 A).
Proof. exact (fun_ext (fun x : A => @lem3604231 A x h1)). Qed.
Lemma lem3604237 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3604238 {A : Type'} (h1 : term83 A) : (term65 A) = (term102 A).
Proof. exact (MK_COMB (@lem3604237 A) (@lem3604236 A h1)). Qed.
Lemma lem3604243 {A : Type'} (h1 : term83 A) : (term102 A) = (term65 A).
Proof. exact (SYM (@lem3604238 A h1)). Qed.
Lemma lem3604259 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term103 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3604260 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term103 A s t).
Proof. exact (@lem3604259 A s t). Qed.
Lemma lem3604261 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term89 A x s t) = (term90 A x s t)) = (term104 A x s t).
Proof. exact (@lem3604260 A (term89 A x s t) (term90 A x s t)). Qed.
Lemma lem3604270 {A : Type'} (x : A) (s : A -> Prop) : (term105 A x s) = (term106 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3604261 A x s t)). Qed.
Lemma lem3604271 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604272 {A : Type'} (x : A) (s : A -> Prop) : (term87 A x s) = (term107 A x s).
Proof. exact (MK_COMB (@lem3604271 A) (@lem3604270 A x s)). Qed.
Lemma lem3604277 {A : Type'} (x : A) : (term108 A x) = (term109 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3604272 A x s)). Qed.
Lemma lem3604278 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604279 {A : Type'} (x : A) : (term85 A x) = (term110 A x).
Proof. exact (MK_COMB (@lem3604278 A) (@lem3604277 A x)). Qed.
Lemma lem3604284 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (fun_ext (fun x : A => @lem3604279 A x)). Qed.
Lemma lem3604285 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3604286 {A : Type'} : (term83 A) = (term113 A).
Proof. exact (MK_COMB (@lem3604285 A) (@lem3604284 A)). Qed.
Lemma lem3604291 {A : Type'} : (term113 A) = (term83 A).
Proof. exact (SYM (@lem3604286 A)). Qed.
Lemma lem3604311 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term114 A x s t) = (term115 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3604312 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term114 A x s t) = (term115 A s x t).
Proof. exact (@lem3604311 A s x t). Qed.
Lemma lem3604313 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term116 A x' x s t) = (term117 A x s x' t).
Proof. exact (@lem3604312 A (@INSERT A x s) x' t). Qed.
Lemma lem3604317 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term118 A x y s) = (term119 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3604318 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term118 A x y s) = (term119 A y x s).
Proof. exact (@lem3604317 A y x s). Qed.
Lemma lem3604319 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term118 A x' x s) = (term119 A x x' s).
Proof. exact (@lem3604318 A x x' s). Qed.
Lemma lem3604325 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3604326 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3604325 A P x). Qed.
Lemma lem3604327 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3604326 A s x'). Qed.
Lemma lem3604328 {A : Type'} (x' : A) (x : A) : (term120 A x' x) = (term120 A x' x).
Proof. exact (eq_refl (term120 A x' x)). Qed.
Lemma lem3604329 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term119 A x x' s) = (term121 A x s x').
Proof. exact (MK_COMB (@lem3604328 A x' x) (@lem3604327 A s x')). Qed.
Lemma lem3604332 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term118 A x' x s) = (term121 A x s x').
Proof. exact (TRANS (@lem3604319 A x x' s) (@lem3604329 A x s x')). Qed.
Lemma lem3604333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3604334 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term122 A x' x s) = (term123 A x s x').
Proof. exact (MK_COMB (@lem3604333) (@lem3604332 A x s x')). Qed.
Lemma lem3604336 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3604337 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3604336 A P x). Qed.
Lemma lem3604338 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3604337 A t x'). Qed.
Lemma lem3604339 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term117 A x s x' t) = (term124 A x s t x').
Proof. exact (MK_COMB (@lem3604334 A x s x') (@lem3604338 A t x')). Qed.
Lemma lem3604342 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term116 A x' x s t) = (term124 A x s t x').
Proof. exact (TRANS (@lem3604313 A x s x' t) (@lem3604339 A x s t x')). Qed.
Lemma lem3604343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3604344 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term125 A x' x s t) = (term126 A x s t x').
Proof. exact (MK_COMB (@lem3604343) (@lem3604342 A x s t x')). Qed.
Lemma lem3604346 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term118 A x y s) = (term119 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3604347 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term118 A x y s) = (term119 A y x s).
Proof. exact (@lem3604346 A y x s). Qed.
Lemma lem3604348 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term127 A x' x s t) = (term128 A x x' s t).
Proof. exact (@lem3604347 A x x' (@UNION A s t)). Qed.
Lemma lem3604354 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term114 A x s t) = (term115 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3604355 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term114 A x s t) = (term115 A s x t).
Proof. exact (@lem3604354 A s x t). Qed.
Lemma lem3604356 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term114 A x' s t) = (term115 A s x' t).
Proof. exact (@lem3604355 A s x' t). Qed.
Lemma lem3604360 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3604361 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3604360 A P x). Qed.
Lemma lem3604362 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3604361 A s x'). Qed.
Lemma lem3604363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3604364 {A : Type'} (s : A -> Prop) (x' : A) : (term129 A x' s) = (term130 A s x').
Proof. exact (MK_COMB (@lem3604363) (@lem3604362 A s x')). Qed.
Lemma lem3604366 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3604367 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3604366 A P x). Qed.
Lemma lem3604368 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3604367 A t x'). Qed.
Lemma lem3604369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term115 A s x' t) = (term131 A s t x').
Proof. exact (MK_COMB (@lem3604364 A s x') (@lem3604368 A t x')). Qed.
Lemma lem3604372 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term114 A x' s t) = (term131 A s t x').
Proof. exact (TRANS (@lem3604356 A s x' t) (@lem3604369 A s t x')). Qed.
Lemma lem3604373 {A : Type'} (x' : A) (x : A) : (term120 A x' x) = (term120 A x' x).
Proof. exact (eq_refl (term120 A x' x)). Qed.
Lemma lem3604374 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term128 A x x' s t) = (term132 A x s t x').
Proof. exact (MK_COMB (@lem3604373 A x' x) (@lem3604372 A s t x')). Qed.
Lemma lem3604377 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term127 A x' x s t) = (term132 A x s t x').
Proof. exact (TRANS (@lem3604348 A x x' s t) (@lem3604374 A x s t x')). Qed.
Lemma lem3604378 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term116 A x' x s t) = (term127 A x' x s t)) = ((term124 A x s t x') = (term132 A x s t x')).
Proof. exact (MK_COMB (@lem3604344 A x s t x') (@lem3604377 A x s t x')). Qed.
Lemma lem3604381 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term133 A x s t) = (term134 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3604378 A x s t x')). Qed.
Lemma lem3604382 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3604383 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term104 A x s t) = (term135 A x s t).
Proof. exact (MK_COMB (@lem3604382 A) (@lem3604381 A x s t)). Qed.
Lemma lem3604388 {A : Type'} (x : A) (s : A -> Prop) : (term106 A x s) = (term136 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3604383 A x s t)). Qed.
Lemma lem3604389 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604390 {A : Type'} (x : A) (s : A -> Prop) : (term107 A x s) = (term137 A x s).
Proof. exact (MK_COMB (@lem3604389 A) (@lem3604388 A x s)). Qed.
Lemma lem3604395 {A : Type'} (x : A) : (term109 A x) = (term138 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3604390 A x s)). Qed.
Lemma lem3604396 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604397 {A : Type'} (x : A) : (term110 A x) = (term139 A x).
Proof. exact (MK_COMB (@lem3604396 A) (@lem3604395 A x)). Qed.
Lemma lem3604402 {A : Type'} : (term112 A) = (term140 A).
Proof. exact (fun_ext (fun x : A => @lem3604397 A x)). Qed.
Lemma lem3604403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3604404 {A : Type'} : (term113 A) = (term141 A).
Proof. exact (MK_COMB (@lem3604403 A) (@lem3604402 A)). Qed.
Lemma lem3604409 {A : Type'} : (term141 A) = (term113 A).
Proof. exact (SYM (@lem3604404 A)). Qed.
Lemma lem3604411 (p : Prop) : p = (term142 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3604412 {A : Type'} : (term141 A) = (term143 A).
Proof. exact (@lem3604411 (term141 A)). Qed.
Lemma lem3604413 {A : Type'} : (term143 A) = (term141 A).
Proof. exact (SYM (@lem3604412 A)). Qed.
Lemma lem3604414 {A : Type'} (h1 : term144 A) : term144 A.
Proof. exact (h1). Qed.
Lemma lem3604417 {A : Type'} (h1 : term143 A) : term143 A.
Proof. exact (h1). Qed.
Lemma lem3604418 {A : Type'} : term145 A.
Proof. exact (fun h0 : term143 A => @lem3604417 A h0). Qed.
Lemma lem3604419 {A : Type'} (h1 : term145 A) : term145 A.
Proof. exact (h1). Qed.
Lemma lem3604420 {A : Type'} (h1 : term143 A) : term143 A.
Proof. exact (h1). Qed.
Lemma lem3604421 {A : Type'} (h1 : term143 A) (h2 : term145 A) : term143 A.
Proof. exact (@lem3604419 A h2 (@lem3604420 A h1)). Qed.
Lemma lem3604422 {A : Type'} (h1 : term143 A) : term146 A.
Proof. exact (fun h0 : term145 A => @lem3604421 A h1 h0). Qed.
Lemma lem3604423 {A : Type'} (h1 : term145 A) : term145 A.
Proof. exact (h1). Qed.
Lemma lem3604424 {A : Type'} (h1 : term143 A) (h2 : term145 A) : term143 A.
Proof. exact (@lem3604422 A h1 (@lem3604423 A h2)). Qed.
Lemma lem3604425 {A : Type'} (h1 : term145 A) : term145 A.
Proof. exact (fun h0 : term143 A => @lem3604424 A h0 h1). Qed.
Lemma lem3604426 {A : Type'} : term147 A.
Proof. exact (fun h0 : term145 A => @lem3604425 A h0). Qed.
Lemma lem3604429 {A : Type'} : term145 A.
Proof. exact (@lem3604426 A (@lem3604418 A)). Qed.
Lemma lem3604430 {A : Type'} : term145 A.
Proof. exact (@lem3604429 A). Qed.
Lemma lem3604432 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3604433 {A : Type'} : (term143 A) = (term148 A).
Proof. exact (@lem3604432 (term144 A)). Qed.
Lemma lem3604435 (t : Prop) : (term149 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3604436 {A : Type'} : (term148 A) = (term141 A).
Proof. exact (@lem3604435 (term141 A)). Qed.
Lemma lem3604465 {A : Type'} : (term143 A) = (term141 A).
Proof. exact (TRANS (@lem3604433 A) (@lem3604436 A)). Qed.
Lemma lem3604486 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term124 A x s t x') = (term132 A x s t x')) = ((term124 A x s t x') = (term132 A x s t x')).
Proof. exact (eq_refl ((term124 A x s t x') = (term132 A x s t x'))). Qed.
Lemma lem3604487 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term134 A x s t) = (term134 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3604486 A x s t x')). Qed.
Lemma lem3604488 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3604489 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term135 A x s t) = (term135 A x s t).
Proof. exact (MK_COMB (@lem3604488 A) (@lem3604487 A x s t)). Qed.
Lemma lem3604490 {A : Type'} (x : A) (s : A -> Prop) : (term136 A x s) = (term136 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3604489 A x s t)). Qed.
Lemma lem3604491 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604492 {A : Type'} (x : A) (s : A -> Prop) : (term137 A x s) = (term137 A x s).
Proof. exact (MK_COMB (@lem3604491 A) (@lem3604490 A x s)). Qed.
Lemma lem3604493 {A : Type'} (x : A) : (term138 A x) = (term138 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3604492 A x s)). Qed.
Lemma lem3604494 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3604495 {A : Type'} (x : A) : (term139 A x) = (term139 A x).
Proof. exact (MK_COMB (@lem3604494 A) (@lem3604493 A x)). Qed.
Lemma lem3604496 {A : Type'} : (term140 A) = (term140 A).
Proof. exact (fun_ext (fun x : A => @lem3604495 A x)). Qed.
Lemma lem3604497 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3604498 {A : Type'} : (term141 A) = (term141 A).
Proof. exact (MK_COMB (@lem3604497 A) (@lem3604496 A)). Qed.
Lemma lem3604533 {A : Type'} : (term143 A) = (term141 A).
Proof. exact (TRANS (@lem3604465 A) (@lem3604498 A)). Qed.
Lemma lem3604534 {A : Type'} : (term141 A) = (term143 A).
Proof. exact (SYM (@lem3604533 A)). Qed.
Lemma lem3604536 (p : Prop) : p = (term142 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3604537 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term124 A x s t x') = (term132 A x s t x')) = (term150 A x s t x').
Proof. exact (@lem3604536 ((term124 A x s t x') = (term132 A x s t x'))). Qed.
Lemma lem3604538 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term150 A x s t x') = ((term124 A x s t x') = (term132 A x s t x')).
Proof. exact (SYM (@lem3604537 A x s t x')). Qed.
Lemma lem3604539 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term151 A x s t x') : term151 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3604548 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term152 A x s x') = (term153 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3604552 {A : Type'} (t : A -> Prop) (x' : A) : (term154 A t x') = (term154 A t x').
Proof. exact (eq_refl (term154 A t x')). Qed.
Lemma lem3604554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3604555 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term155 A x s x') = (term156 A x s x').
Proof. exact (MK_COMB (@lem3604554) (@lem3604548 A x s x')). Qed.
Lemma lem3604556 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term157 A x s t x') = (term158 A x s t x').
Proof. exact (MK_COMB (@lem3604555 A x s x') (@lem3604552 A t x')). Qed.
Lemma lem3604557 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term159 A x s t x') = (term157 A x s t x').
Proof. exact (@lem17160 (term121 A x s x') (t x')). Qed.
Lemma lem3604558 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term159 A x s t x') = (term158 A x s t x').
Proof. exact (TRANS (@lem3604557 A x s t x') (@lem3604556 A x s t x')). Qed.
Lemma lem3604572 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term160 A s t x') = (term161 A s t x').
Proof. exact (@lem17160 (s x') (t x')). Qed.
Lemma lem3604577 {A : Type'} (x' : A) (x : A) : (term162 A x' x) = (term162 A x' x).
Proof. exact (eq_refl (term162 A x' x)). Qed.
Lemma lem3604578 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term163 A x s t x') = (term164 A x s t x').
Proof. exact (MK_COMB (@lem3604577 A x' x) (@lem3604572 A s t x')). Qed.
Lemma lem3604579 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term165 A x s t x') = (term163 A x s t x').
Proof. exact (@lem17160 (x' = x) (term131 A s t x')). Qed.
Lemma lem3604580 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term165 A x s t x') = (term164 A x s t x').
Proof. exact (TRANS (@lem3604579 A x s t x') (@lem3604578 A x s t x')). Qed.
Lemma lem3604583 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term132 A x s t x') = (term132 A x s t x').
Proof. exact (eq_refl (term132 A x s t x')). Qed.
Lemma lem3604584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3604585 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term166 A x s t x') = (term167 A x s t x').
Proof. exact (MK_COMB (@lem3604584) (@lem3604558 A x s t x')). Qed.
Lemma lem3604586 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term168 A x s t x') = (term169 A x s t x').
Proof. exact (MK_COMB (@lem3604585 A x s t x') (@lem3604583 A x s t x')). Qed.
Lemma lem3604588 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term170 A x s t x') = (term170 A x s t x').
Proof. exact (eq_refl (term170 A x s t x')). Qed.
Lemma lem3604589 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term171 A x s t x') = (term172 A x s t x').
Proof. exact (MK_COMB (@lem3604588 A x s t x') (@lem3604580 A x s t x')). Qed.
Lemma lem3604590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3604591 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term173 A x s t x') = (term174 A x s t x').
Proof. exact (MK_COMB (@lem3604590) (@lem3604589 A x s t x')). Qed.
Lemma lem3604592 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term175 A x s t x') = (term176 A x s t x').
Proof. exact (MK_COMB (@lem3604591 A x s t x') (@lem3604586 A x s t x')). Qed.
Lemma lem3604593 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term151 A x s t x') = (term175 A x s t x').
Proof. exact (@lem17646 (term124 A x s t x') (term132 A x s t x')). Qed.
Lemma lem3604598 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term151 A x s t x') = (term176 A x s t x').
Proof. exact (TRANS (@lem3604593 A x s t x') (@lem3604592 A x s t x')). Qed.
Lemma lem3604689 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term151 A x s t x') : term176 A x s t x'.
Proof. exact (EQ_MP (@lem3604598 A x s t x') (@lem3604539 A x s t x' h1)). Qed.
Lemma lem3604690 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : term172 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3604691 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : term169 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3604692 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : term164 A x s t x'.
Proof. exact (proj2 (@lem3604690 A x s t x' h1)). Qed.
Lemma lem3604693 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : term124 A x s t x'.
Proof. exact (proj1 (@lem3604690 A x s t x' h1)). Qed.
Lemma lem3604694 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : term161 A s t x'.
Proof. exact (proj2 (@lem3604692 A x s t x' h1)). Qed.
Lemma lem3604698 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term121 A x s x') : term121 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3604702 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : term132 A x s t x'.
Proof. exact (proj2 (@lem3604691 A x s t x' h1)). Qed.
Lemma lem3604703 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : term158 A x s t x'.
Proof. exact (proj1 (@lem3604691 A x s t x' h1)). Qed.
Lemma lem3604705 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : term153 A x s x'.
Proof. exact (proj1 (@lem3604703 A x s t x' h1)). Qed.
Lemma lem3604709 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A s t x') : term131 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3604727 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3604743 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3604759 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3604775 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3604791 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3604807 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3604809 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : term177 A x' x.
Proof. exact (proj1 (@lem3604692 A x s t x' h1)). Qed.
Lemma lem3604815 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3604819 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : term154 A s x'.
Proof. exact (proj1 (@lem3604694 A x s t x' h1)). Qed.
Lemma lem3604823 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3604829 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : term154 A t x'.
Proof. exact (proj2 (@lem3604694 A x s t x' h1)). Qed.
Lemma lem3604831 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3604835 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : term177 A x' x.
Proof. exact (proj1 (@lem3604705 A x s t x' h1)). Qed.
Lemma lem3604839 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3604845 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : term154 A s x'.
Proof. exact (proj2 (@lem3604705 A x s t x' h1)). Qed.
Lemma lem3604847 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3604849 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : term154 A t x'.
Proof. exact (proj2 (@lem3604703 A x s t x' h1)). Qed.
Lemma lem3604855 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3604870 {A : Type'} (x : A) : (term178 A x) = (term178 A x).
Proof. exact (eq_refl (term178 A x)). Qed.
Lemma lem3604871 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term179 A x x') = (term180 A x).
Proof. exact (MK_COMB (@lem3604870 A x) (@lem3604815 A x' x h1)). Qed.
Lemma lem3604872 {A : Type'} (x : A) : (term180 A x) = (term181 A x).
Proof. exact (eq_refl (term180 A x)). Qed.
Lemma lem3604873 {A : Type'} (x : A) (x' : A) : (term182 A x x') = (term182 A x x').
Proof. exact (eq_refl (term182 A x x')). Qed.
Lemma lem3604874 {A : Type'} (x' : A) (x : A) : ((term179 A x x') = (term180 A x)) = ((term179 A x x') = (term181 A x)).
Proof. exact (MK_COMB (@lem3604873 A x x') (@lem3604872 A x)). Qed.
Lemma lem3604875 {A : Type'} (x' : A) (x : A) : (term179 A x x') = (term177 A x' x).
Proof. exact (eq_refl (term179 A x x')). Qed.
Lemma lem3604876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3604877 {A : Type'} (x' : A) (x : A) : (term182 A x x') = (term183 A x' x).
Proof. exact (MK_COMB (@lem3604876) (@lem3604875 A x' x)). Qed.
Lemma lem3604878 {A : Type'} (x : A) : (term181 A x) = (term181 A x).
Proof. exact (eq_refl (term181 A x)). Qed.
Lemma lem3604879 {A : Type'} (x' : A) (x : A) : ((term179 A x x') = (term181 A x)) = ((term177 A x' x) = (term181 A x)).
Proof. exact (MK_COMB (@lem3604877 A x' x) (@lem3604878 A x)). Qed.
Lemma lem3604880 {A : Type'} (x' : A) (x : A) : ((term179 A x x') = (term180 A x)) = ((term177 A x' x) = (term181 A x)).
Proof. exact (TRANS (@lem3604874 A x' x) (@lem3604879 A x' x)). Qed.
Lemma lem3604881 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term177 A x' x) = (term181 A x).
Proof. exact (EQ_MP (@lem3604880 A x' x) (@lem3604871 A x' x h1)). Qed.
Lemma lem3604882 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : term181 A x.
Proof. exact (EQ_MP (@lem3604881 A x' x h2) (@lem3604809 A x s t x' h1)). Qed.
Lemma lem3604936 {A : Type'} (x : A) : (term178 A x) = (term178 A x).
Proof. exact (eq_refl (term178 A x)). Qed.
Lemma lem3604937 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term179 A x x') = (term180 A x).
Proof. exact (MK_COMB (@lem3604936 A x) (@lem3604839 A x' x h1)). Qed.
Lemma lem3604938 {A : Type'} (x : A) : (term180 A x) = (term181 A x).
Proof. exact (eq_refl (term180 A x)). Qed.
Lemma lem3604939 {A : Type'} (x : A) (x' : A) : (term182 A x x') = (term182 A x x').
Proof. exact (eq_refl (term182 A x x')). Qed.
Lemma lem3604940 {A : Type'} (x' : A) (x : A) : ((term179 A x x') = (term180 A x)) = ((term179 A x x') = (term181 A x)).
Proof. exact (MK_COMB (@lem3604939 A x x') (@lem3604938 A x)). Qed.
Lemma lem3604941 {A : Type'} (x' : A) (x : A) : (term179 A x x') = (term177 A x' x).
Proof. exact (eq_refl (term179 A x x')). Qed.
Lemma lem3604942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3604943 {A : Type'} (x' : A) (x : A) : (term182 A x x') = (term183 A x' x).
Proof. exact (MK_COMB (@lem3604942) (@lem3604941 A x' x)). Qed.
Lemma lem3604944 {A : Type'} (x : A) : (term181 A x) = (term181 A x).
Proof. exact (eq_refl (term181 A x)). Qed.
Lemma lem3604945 {A : Type'} (x' : A) (x : A) : ((term179 A x x') = (term181 A x)) = ((term177 A x' x) = (term181 A x)).
Proof. exact (MK_COMB (@lem3604943 A x' x) (@lem3604944 A x)). Qed.
Lemma lem3604946 {A : Type'} (x' : A) (x : A) : ((term179 A x x') = (term180 A x)) = ((term177 A x' x) = (term181 A x)).
Proof. exact (TRANS (@lem3604940 A x' x) (@lem3604945 A x' x)). Qed.
Lemma lem3604947 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term177 A x' x) = (term181 A x).
Proof. exact (EQ_MP (@lem3604946 A x' x) (@lem3604937 A x' x h1)). Qed.
Lemma lem3604948 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : term181 A x.
Proof. exact (EQ_MP (@lem3604947 A x' x h2) (@lem3604835 A x s t x' h1)). Qed.
Lemma lem3604989 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3604990 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3604989 A x). Qed.
Lemma lem3604991 {A : Type'} (x : A) : term184 A x.
Proof. exact (fun h0 : term181 A x => @lem3604990 A x). Qed.
Lemma lem3604993 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3604994 {A : Type'} (x : A) : (term184 A x) = (x = x).
Proof. exact (@lem3604993 (x = x)). Qed.
Lemma lem3604995 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3604994 A x) (@lem3604991 A x)). Qed.
Lemma lem3604998 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3605000 {A : Type'} (x : A) : (term181 A x) = (term186 A x).
Proof. exact (@lem3604998 (x = x)). Qed.
Lemma lem3605003 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : term186 A x.
Proof. exact (EQ_MP (@lem3605000 A x) (@lem3604882 A s t x' x h1 h2)). Qed.
Lemma lem3605006 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3605003 A s t x' x h1 h2 (@lem3604995 A x)). Qed.
Lemma lem3605007 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : term187.
Proof. exact (fun h0 : ~ False => @lem3605006 A s t x' x h1 h2). Qed.
Lemma lem3605009 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605010 : term187 = False.
Proof. exact (@lem3605009 False). Qed.
Lemma lem3605039 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3605040 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term188 A s x'.
Proof. exact (fun h0 : term154 A s x' => @lem3605039 A s x' h1). Qed.
Lemma lem3605042 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605043 {A : Type'} (s : A -> Prop) (x' : A) : (term188 A s x') = (s x').
Proof. exact (@lem3605042 (s x')). Qed.
Lemma lem3605044 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3605043 A s x') (@lem3605040 A s x' h1)). Qed.
Lemma lem3605047 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3605049 {A : Type'} (s : A -> Prop) (x' : A) : (term154 A s x') = (term189 A s x').
Proof. exact (@lem3605047 (s x')). Qed.
Lemma lem3605052 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : term189 A s x'.
Proof. exact (EQ_MP (@lem3605049 A s x') (@lem3604819 A x s t x' h1)). Qed.
Lemma lem3605055 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term172 A x s t x') : False.
Proof. exact (@lem3605052 A x s t x' h2 (@lem3605044 A s x' h1)). Qed.
Lemma lem3605056 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term172 A x s t x') : term187.
Proof. exact (fun h0 : ~ False => @lem3605055 A x s t x' h1 h2). Qed.
Lemma lem3605058 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605059 : term187 = False.
Proof. exact (@lem3605058 False). Qed.
Lemma lem3605060 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term172 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605059) (@lem3605056 A x s t x' h1 h2)). Qed.
Lemma lem3605088 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3605089 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term188 A t x'.
Proof. exact (fun h0 : term154 A t x' => @lem3605088 A t x' h1). Qed.
Lemma lem3605091 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605092 {A : Type'} (t : A -> Prop) (x' : A) : (term188 A t x') = (t x').
Proof. exact (@lem3605091 (t x')). Qed.
Lemma lem3605093 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3605092 A t x') (@lem3605089 A t x' h1)). Qed.
Lemma lem3605096 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3605098 {A : Type'} (t : A -> Prop) (x' : A) : (term154 A t x') = (term189 A t x').
Proof. exact (@lem3605096 (t x')). Qed.
Lemma lem3605101 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : term189 A t x'.
Proof. exact (EQ_MP (@lem3605098 A t x') (@lem3604829 A x s t x' h1)). Qed.
Lemma lem3605104 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term172 A x s t x') : False.
Proof. exact (@lem3605101 A x s t x' h2 (@lem3605093 A t x' h1)). Qed.
Lemma lem3605105 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term172 A x s t x') : term187.
Proof. exact (fun h0 : ~ False => @lem3605104 A x s t x' h1 h2). Qed.
Lemma lem3605107 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605108 : term187 = False.
Proof. exact (@lem3605107 False). Qed.
Lemma lem3605109 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term172 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605108) (@lem3605105 A x s t x' h1 h2)). Qed.
Lemma lem3605137 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3605138 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3605137 A x). Qed.
Lemma lem3605139 {A : Type'} (x : A) : term184 A x.
Proof. exact (fun h0 : term181 A x => @lem3605138 A x). Qed.
Lemma lem3605141 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605142 {A : Type'} (x : A) : (term184 A x) = (x = x).
Proof. exact (@lem3605141 (x = x)). Qed.
Lemma lem3605143 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3605142 A x) (@lem3605139 A x)). Qed.
Lemma lem3605146 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3605148 {A : Type'} (x : A) : (term181 A x) = (term186 A x).
Proof. exact (@lem3605146 (x = x)). Qed.
Lemma lem3605151 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : term186 A x.
Proof. exact (EQ_MP (@lem3605148 A x) (@lem3604948 A s t x' x h1 h2)). Qed.
Lemma lem3605154 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3605151 A s t x' x h1 h2 (@lem3605143 A x)). Qed.
Lemma lem3605155 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : term187.
Proof. exact (fun h0 : ~ False => @lem3605154 A s t x' x h1 h2). Qed.
Lemma lem3605157 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605158 : term187 = False.
Proof. exact (@lem3605157 False). Qed.
Lemma lem3605187 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3605188 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term188 A s x'.
Proof. exact (fun h0 : term154 A s x' => @lem3605187 A s x' h1). Qed.
Lemma lem3605190 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605191 {A : Type'} (s : A -> Prop) (x' : A) : (term188 A s x') = (s x').
Proof. exact (@lem3605190 (s x')). Qed.
Lemma lem3605192 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3605191 A s x') (@lem3605188 A s x' h1)). Qed.
Lemma lem3605195 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3605197 {A : Type'} (s : A -> Prop) (x' : A) : (term154 A s x') = (term189 A s x').
Proof. exact (@lem3605195 (s x')). Qed.
Lemma lem3605200 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : term189 A s x'.
Proof. exact (EQ_MP (@lem3605197 A s x') (@lem3604845 A x s t x' h1)). Qed.
Lemma lem3605203 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term169 A x s t x') : False.
Proof. exact (@lem3605200 A x s t x' h2 (@lem3605192 A s x' h1)). Qed.
Lemma lem3605204 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term169 A x s t x') : term187.
Proof. exact (fun h0 : ~ False => @lem3605203 A x s t x' h1 h2). Qed.
Lemma lem3605206 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605207 : term187 = False.
Proof. exact (@lem3605206 False). Qed.
Lemma lem3605208 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term169 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605207) (@lem3605204 A x s t x' h1 h2)). Qed.
Lemma lem3605236 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3605237 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term188 A t x'.
Proof. exact (fun h0 : term154 A t x' => @lem3605236 A t x' h1). Qed.
Lemma lem3605239 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605240 {A : Type'} (t : A -> Prop) (x' : A) : (term188 A t x') = (t x').
Proof. exact (@lem3605239 (t x')). Qed.
Lemma lem3605241 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3605240 A t x') (@lem3605237 A t x' h1)). Qed.
Lemma lem3605244 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3605246 {A : Type'} (t : A -> Prop) (x' : A) : (term154 A t x') = (term189 A t x').
Proof. exact (@lem3605244 (t x')). Qed.
Lemma lem3605249 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : term189 A t x'.
Proof. exact (EQ_MP (@lem3605246 A t x') (@lem3604849 A x s t x' h1)). Qed.
Lemma lem3605252 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term169 A x s t x') : False.
Proof. exact (@lem3605249 A x s t x' h2 (@lem3605241 A t x' h1)). Qed.
Lemma lem3605253 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term169 A x s t x') : term187.
Proof. exact (fun h0 : ~ False => @lem3605252 A x s t x' h1 h2). Qed.
Lemma lem3605255 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605256 : term187 = False.
Proof. exact (@lem3605255 False). Qed.
Lemma lem3605257 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term169 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605256) (@lem3605253 A x s t x' h1 h2)). Qed.
Lemma lem3605258 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3605158) (@lem3605155 A s t x' x h1 h2)). Qed.
Lemma lem3605259 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3605010) (@lem3605007 A s t x' x h1 h2)). Qed.
Lemma lem3605260 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term169 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3605257 A x s t x' h1 h2) (fun h3 : False => @lem3604855 A t x' h1)). Qed.
Lemma lem3605261 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term169 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605260 A x s t x' h1 h2) (@lem3604855 A t x' h1)). Qed.
Lemma lem3605262 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term169 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3605208 A x s t x' h1 h2) (fun h3 : False => @lem3604847 A s x' h1)). Qed.
Lemma lem3605263 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term169 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605262 A x s t x' h1 h2) (@lem3604847 A s x' h1)). Qed.
Lemma lem3605264 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3605258 A s t x' x h1 h2) (fun h3 : False => @lem3604839 A x' x h2)). Qed.
Lemma lem3605265 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3605264 A s t x' x h1 h2) (@lem3604839 A x' x h2)). Qed.
Lemma lem3605266 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term172 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3605109 A x s t x' h1 h2) (fun h3 : False => @lem3604831 A t x' h1)). Qed.
Lemma lem3605267 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term172 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605266 A x s t x' h1 h2) (@lem3604831 A t x' h1)). Qed.
Lemma lem3605268 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term172 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3605060 A x s t x' h1 h2) (fun h3 : False => @lem3604823 A s x' h1)). Qed.
Lemma lem3605269 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term172 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605268 A x s t x' h1 h2) (@lem3604823 A s x' h1)). Qed.
Lemma lem3605270 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3605259 A s t x' x h1 h2) (fun h3 : False => @lem3604815 A x' x h2)). Qed.
Lemma lem3605271 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3605270 A s t x' x h1 h2) (@lem3604815 A x' x h2)). Qed.
Lemma lem3605272 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term169 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3605261 A x s t x' h1 h2) (fun h3 : False => @lem3604807 A t x' h1)). Qed.
Lemma lem3605273 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term169 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605272 A x s t x' h1 h2) (@lem3604807 A t x' h1)). Qed.
Lemma lem3605274 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term169 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3605263 A x s t x' h1 h2) (fun h3 : False => @lem3604791 A s x' h1)). Qed.
Lemma lem3605275 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term169 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605274 A x s t x' h1 h2) (@lem3604791 A s x' h1)). Qed.
Lemma lem3605276 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3605265 A s t x' x h1 h2) (fun h3 : False => @lem3604775 A x' x h2)). Qed.
Lemma lem3605277 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3605276 A s t x' x h1 h2) (@lem3604775 A x' x h2)). Qed.
Lemma lem3605278 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term172 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3605267 A x s t x' h1 h2) (fun h3 : False => @lem3604759 A t x' h1)). Qed.
Lemma lem3605279 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term172 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605278 A x s t x' h1 h2) (@lem3604759 A t x' h1)). Qed.
Lemma lem3605280 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term172 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3605269 A x s t x' h1 h2) (fun h3 : False => @lem3604743 A s x' h1)). Qed.
Lemma lem3605281 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term172 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605280 A x s t x' h1 h2) (@lem3604743 A s x' h1)). Qed.
Lemma lem3605282 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3605271 A s t x' x h1 h2) (fun h3 : False => @lem3604727 A x' x h2)). Qed.
Lemma lem3605283 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3605282 A s t x' x h1 h2) (@lem3604727 A x' x h2)). Qed.
Lemma lem3605284 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term169 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3605273 A x s t x' h1 h2) (fun h3 : False => @lem3604807 A t x' h1)). Qed.
Lemma lem3605285 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term169 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605284 A x s t x' h1 h2) (@lem3604807 A t x' h1)). Qed.
Lemma lem3605286 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term169 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3605275 A x s t x' h1 h2) (fun h3 : False => @lem3604791 A s x' h1)). Qed.
Lemma lem3605287 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term169 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605286 A x s t x' h1 h2) (@lem3604791 A s x' h1)). Qed.
Lemma lem3605288 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3605277 A s t x' x h1 h2) (fun h3 : False => @lem3604775 A x' x h2)). Qed.
Lemma lem3605289 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term169 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3605288 A s t x' x h1 h2) (@lem3604775 A x' x h2)). Qed.
Lemma lem3605290 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term172 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3605279 A x s t x' h1 h2) (fun h3 : False => @lem3604759 A t x' h1)). Qed.
Lemma lem3605291 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term172 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605290 A x s t x' h1 h2) (@lem3604759 A t x' h1)). Qed.
Lemma lem3605292 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term172 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3605281 A x s t x' h1 h2) (fun h3 : False => @lem3604743 A s x' h1)). Qed.
Lemma lem3605293 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term172 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605292 A x s t x' h1 h2) (@lem3604743 A s x' h1)). Qed.
Lemma lem3605294 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3605283 A s t x' x h1 h2) (fun h3 : False => @lem3604727 A x' x h2)). Qed.
Lemma lem3605295 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term172 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3605294 A s t x' x h1 h2) (@lem3604727 A x' x h2)). Qed.
Lemma lem3605296 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') (h2 : term131 A s t x') : False.
Proof. exact (or_elim (@lem3604709 A s t x' h2) (fun h0 : s x' => @lem3605287 A x s t x' h0 h1) (fun h0 : t x' => @lem3605285 A x s t x' h0 h1)). Qed.
Lemma lem3605297 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term169 A x s t x') : False.
Proof. exact (or_elim (@lem3604702 A x s t x' h1) (fun h0 : x' = x => @lem3605289 A s t x' x h1 h0) (fun h0 : term131 A s t x' => @lem3605296 A x s t x' h1 h0)). Qed.
Lemma lem3605298 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term172 A x s t x') (h2 : term121 A x s x') : False.
Proof. exact (or_elim (@lem3604698 A x s x' h2) (fun h0 : x' = x => @lem3605295 A s t x' x h1 h0) (fun h0 : s x' => @lem3605293 A x s t x' h0 h1)). Qed.
Lemma lem3605299 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term172 A x s t x') : False.
Proof. exact (or_elim (@lem3604693 A x s t x' h1) (fun h0 : term121 A x s x' => @lem3605298 A t x s x' h1 h0) (fun h0 : t x' => @lem3605291 A x s t x' h0 h1)). Qed.
Lemma lem3605300 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term151 A x s t x') : False.
Proof. exact (or_elim (@lem3604689 A x s t x' h1) (fun h0 : term172 A x s t x' => @lem3605299 A x s t x' h0) (fun h0 : term169 A x s t x' => @lem3605297 A x s t x' h0)). Qed.
Lemma lem3605301 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term151 A x s t x') : (term151 A x s t x') = False.
Proof. exact (prop_ext (fun h2 : term151 A x s t x' => @lem3605300 A x s t x' h1) (fun h2 : False => @lem3604539 A x s t x' h1)). Qed.
Lemma lem3605302 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term151 A x s t x') : False.
Proof. exact (EQ_MP (@lem3605301 A x s t x' h1) (@lem3604539 A x s t x' h1)). Qed.
Lemma lem3605303 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : term150 A x s t x'.
Proof. exact (fun h0 : term151 A x s t x' => @lem3605302 A x s t x' h0). Qed.
Lemma lem3605304 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term124 A x s t x') = (term132 A x s t x').
Proof. exact (EQ_MP (@lem3604538 A x s t x') (@lem3605303 A x s t x')). Qed.
Lemma lem3605309 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term135 A x s t.
Proof. exact (fun x' : A => @lem3605304 A x s t x'). Qed.
Lemma lem3605314 {A : Type'} (x : A) (s : A -> Prop) : term137 A x s.
Proof. exact (fun t : A -> Prop => @lem3605309 A x s t). Qed.
Lemma lem3605319 {A : Type'} (x : A) : term139 A x.
Proof. exact (fun s : A -> Prop => @lem3605314 A x s). Qed.
Lemma lem3605324 {A : Type'} : term141 A.
Proof. exact (fun x : A => @lem3605319 A x). Qed.
Lemma lem3605325 {A : Type'} : term143 A.
Proof. exact (EQ_MP (@lem3604534 A) (@lem3605324 A)). Qed.
Lemma lem3605327 {A : Type'} : term143 A.
Proof. exact (@lem3604430 A (@lem3605325 A)). Qed.
Lemma lem3605328 {A : Type'} (h1 : term144 A) : False.
Proof. exact (@lem3605327 A (@lem3604414 A h1)). Qed.
Lemma lem3605329 {A : Type'} (h1 : term144 A) : (term144 A) = False.
Proof. exact (prop_ext (fun h2 : term144 A => @lem3605328 A h1) (fun h2 : False => @lem3604414 A h1)). Qed.
Lemma lem3605330 {A : Type'} (h1 : term144 A) : False.
Proof. exact (EQ_MP (@lem3605329 A h1) (@lem3604414 A h1)). Qed.
Lemma lem3605331 {A : Type'} : term143 A.
Proof. exact (fun h0 : term144 A => @lem3605330 A h0). Qed.
Lemma lem3605332 {A : Type'} : term141 A.
Proof. exact (EQ_MP (@lem3604413 A) (@lem3605331 A)). Qed.
Lemma lem3605333 {A : Type'} : term113 A.
Proof. exact (EQ_MP (@lem3604409 A) (@lem3605332 A)). Qed.
Lemma lem3605334 {A : Type'} : term83 A.
Proof. exact (EQ_MP (@lem3604291 A) (@lem3605333 A)). Qed.
Lemma lem3605336 (p : Prop) : p = (term142 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3605337 {A : Type'} : (term102 A) = (term190 A).
Proof. exact (@lem3605336 (term102 A)). Qed.
Lemma lem3605338 {A : Type'} : (term190 A) = (term102 A).
Proof. exact (SYM (@lem3605337 A)). Qed.
Lemma lem3605339 {A : Type'} (h1 : term191 A) : term191 A.
Proof. exact (h1). Qed.
Lemma lem3605340 {A : Type'} : term192 A.
Proof. exact (@lem3197565 A). Qed.
Lemma lem3605344 {A : Type'} (h1 : term193 A) : term193 A.
Proof. exact (h1). Qed.
Lemma lem3605345 {A : Type'} : term194 A.
Proof. exact (fun h0 : term193 A => @lem3605344 A h0). Qed.
Lemma lem3605346 {A : Type'} (h1 : term194 A) : term194 A.
Proof. exact (h1). Qed.
Lemma lem3605347 {A : Type'} (h1 : term193 A) : term193 A.
Proof. exact (h1). Qed.
Lemma lem3605348 {A : Type'} (h1 : term193 A) (h2 : term194 A) : term193 A.
Proof. exact (@lem3605346 A h2 (@lem3605347 A h1)). Qed.
Lemma lem3605349 {A : Type'} (h1 : term193 A) : term195 A.
Proof. exact (fun h0 : term194 A => @lem3605348 A h1 h0). Qed.
Lemma lem3605350 {A : Type'} (h1 : term194 A) : term194 A.
Proof. exact (h1). Qed.
Lemma lem3605351 {A : Type'} (h1 : term193 A) (h2 : term194 A) : term193 A.
Proof. exact (@lem3605349 A h1 (@lem3605350 A h2)). Qed.
Lemma lem3605352 {A : Type'} (h1 : term194 A) : term194 A.
Proof. exact (fun h0 : term193 A => @lem3605351 A h0 h1). Qed.
Lemma lem3605353 {A : Type'} : term196 A.
Proof. exact (fun h0 : term194 A => @lem3605352 A h0). Qed.
Lemma lem3605356 {A : Type'} : term194 A.
Proof. exact (@lem3605353 A (@lem3605345 A)). Qed.
Lemma lem3605357 {A : Type'} : term194 A.
Proof. exact (@lem3605356 A). Qed.
Lemma lem3605383 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3605384 {A : Type'} : (term197 A) = (term198 A).
Proof. exact (@lem3605383 (term192 A)). Qed.
Lemma lem3605397 {A : Type'} : (term199 A) = (term199 A).
Proof. exact (eq_refl (term199 A)). Qed.
Lemma lem3605404 {A : Type'} : (term193 A) = (term200 A).
Proof. exact (MK_COMB (@lem3605397 A) (@lem3605384 A)). Qed.
Lemma lem3605409 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3605410 {A : Type'} (x : A) : (term202 A x) = (term202 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3605409 A x s)). Qed.
Lemma lem3605411 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605412 {A : Type'} (x : A) : (term203 A x) = (term203 A x).
Proof. exact (MK_COMB (@lem3605411 A) (@lem3605410 A x)). Qed.
Lemma lem3605413 {A : Type'} : (term204 A) = (term204 A).
Proof. exact (fun_ext (fun x : A => @lem3605412 A x)). Qed.
Lemma lem3605414 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3605415 {A : Type'} : (term205 A) = (term205 A).
Proof. exact (MK_COMB (@lem3605414 A) (@lem3605413 A)). Qed.
Lemma lem3605418 {A : Type'} : (term206 A) = (term206 A).
Proof. exact (eq_refl (term206 A)). Qed.
Lemma lem3605419 {A : Type'} : (term192 A) = (term192 A).
Proof. exact (MK_COMB (@lem3605418 A) (@lem3605415 A)). Qed.
Lemma lem3605420 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3605421 {A : Type'} : (term198 A) = (term198 A).
Proof. exact (MK_COMB (@lem3605420) (@lem3605419 A)). Qed.
Lemma lem3605426 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term94 A x s t) = (term94 A x s t).
Proof. exact (eq_refl (term94 A x s t)). Qed.
Lemma lem3605427 {A : Type'} (x : A) (s : A -> Prop) : (term96 A x s) = (term96 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3605426 A x s t)). Qed.
Lemma lem3605428 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605429 {A : Type'} (x : A) (s : A -> Prop) : (term97 A x s) = (term97 A x s).
Proof. exact (MK_COMB (@lem3605428 A) (@lem3605427 A x s)). Qed.
Lemma lem3605434 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term33 A s t).
Proof. exact (eq_refl (term33 A s t)). Qed.
Lemma lem3605435 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3605434 A s t)). Qed.
Lemma lem3605436 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605437 {A : Type'} (s : A -> Prop) : (term41 A s) = (term41 A s).
Proof. exact (MK_COMB (@lem3605436 A) (@lem3605435 A s)). Qed.
Lemma lem3605438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3605439 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (MK_COMB (@lem3605438) (@lem3605437 A s)). Qed.
Lemma lem3605440 {A : Type'} (x : A) (s : A -> Prop) : (term98 A x s) = (term98 A x s).
Proof. exact (MK_COMB (@lem3605439 A s) (@lem3605429 A x s)). Qed.
Lemma lem3605441 {A : Type'} (x : A) : (term99 A x) = (term99 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3605440 A x s)). Qed.
Lemma lem3605442 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605443 {A : Type'} (x : A) : (term100 A x) = (term100 A x).
Proof. exact (MK_COMB (@lem3605442 A) (@lem3605441 A x)). Qed.
Lemma lem3605444 {A : Type'} : (term101 A) = (term101 A).
Proof. exact (fun_ext (fun x : A => @lem3605443 A x)). Qed.
Lemma lem3605445 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3605446 {A : Type'} : (term102 A) = (term102 A).
Proof. exact (MK_COMB (@lem3605445 A) (@lem3605444 A)). Qed.
Lemma lem3605447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3605448 {A : Type'} : (term191 A) = (term191 A).
Proof. exact (MK_COMB (@lem3605447) (@lem3605446 A)). Qed.
Lemma lem3605449 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3605450 {A : Type'} : (term199 A) = (term199 A).
Proof. exact (MK_COMB (@lem3605449) (@lem3605448 A)). Qed.
Lemma lem3605451 {A : Type'} : (term200 A) = (term200 A).
Proof. exact (MK_COMB (@lem3605450 A) (@lem3605421 A)). Qed.
Lemma lem3605502 {A : Type'} : (term193 A) = (term200 A).
Proof. exact (TRANS (@lem3605404 A) (@lem3605451 A)). Qed.
Lemma lem3605503 {A : Type'} : (term200 A) = (term193 A).
Proof. exact (SYM (@lem3605502 A)). Qed.
Lemma lem3605504 {A : Type'} (h1 : term191 A) : term191 A.
Proof. exact (h1). Qed.
Lemma lem3605505 {A : Type'} (h1 : term192 A) : term192 A.
Proof. exact (h1). Qed.
Lemma lem3605512 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term207 A s t).
Proof. exact (@lem17265 (@FINITE A t) (term18 A s t)). Qed.
Lemma lem3605513 {A : Type'} (s : A -> Prop) : (term31 A s) = (term208 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3605512 A s t)). Qed.
Lemma lem3605514 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605515 {A : Type'} (s : A -> Prop) : (term41 A s) = (term209 A s).
Proof. exact (MK_COMB (@lem3605514 A) (@lem3605513 A s)). Qed.
Lemma lem3605522 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term210 A x s t) = (term211 A x s t).
Proof. exact (@lem17362 (@FINITE A t) (term92 A x s t)). Qed.
Lemma lem3605523 {A : Type'} (P : type686 A) : (term212 A P) = (term213 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3605524 {A : Type'} (x : A) (s : A -> Prop) : (term214 A x s) = (term215 A x s).
Proof. exact (@lem3605523 A (term96 A x s)). Qed.
Lemma lem3605525 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term216 A x s t) = (term94 A x s t).
Proof. exact (eq_refl (term216 A x s t)). Qed.
Lemma lem3605526 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3605527 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term217 A x s t) = (term210 A x s t).
Proof. exact (MK_COMB (@lem3605526) (@lem3605525 A x s t)). Qed.
Lemma lem3605528 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term217 A x s t) = (term211 A x s t).
Proof. exact (TRANS (@lem3605527 A x s t) (@lem3605522 A x s t)). Qed.
Lemma lem3605529 {A : Type'} (x : A) (s : A -> Prop) : (term218 A x s) = (term219 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3605528 A x s t)). Qed.
Lemma lem3605530 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3605531 {A : Type'} (x : A) (s : A -> Prop) : (term215 A x s) = (term220 A x s).
Proof. exact (MK_COMB (@lem3605530 A) (@lem3605529 A x s)). Qed.
Lemma lem3605532 {A : Type'} (x : A) (s : A -> Prop) : (term214 A x s) = (term220 A x s).
Proof. exact (TRANS (@lem3605524 A x s) (@lem3605531 A x s)). Qed.
Lemma lem3605533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3605534 {A : Type'} (s : A -> Prop) : (term221 A s) = (term222 A s).
Proof. exact (MK_COMB (@lem3605533) (@lem3605515 A s)). Qed.
Lemma lem3605535 {A : Type'} (x : A) (s : A -> Prop) : (term223 A x s) = (term224 A x s).
Proof. exact (MK_COMB (@lem3605534 A s) (@lem3605532 A x s)). Qed.
Lemma lem3605536 {A : Type'} (x : A) (s : A -> Prop) : (term225 A x s) = (term223 A x s).
Proof. exact (@lem17362 (term41 A s) (term97 A x s)). Qed.
Lemma lem3605537 {A : Type'} (x : A) (s : A -> Prop) : (term225 A x s) = (term224 A x s).
Proof. exact (TRANS (@lem3605536 A x s) (@lem3605535 A x s)). Qed.
Lemma lem3605538 {A : Type'} (P : type686 A) : (term212 A P) = (term213 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3605539 {A : Type'} (x : A) : (term226 A x) = (term227 A x).
Proof. exact (@lem3605538 A (term99 A x)). Qed.
Lemma lem3605540 {A : Type'} (x : A) (s : A -> Prop) : (term228 A x s) = (term98 A x s).
Proof. exact (eq_refl (term228 A x s)). Qed.
Lemma lem3605541 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3605542 {A : Type'} (x : A) (s : A -> Prop) : (term229 A x s) = (term225 A x s).
Proof. exact (MK_COMB (@lem3605541) (@lem3605540 A x s)). Qed.
Lemma lem3605543 {A : Type'} (x : A) (s : A -> Prop) : (term229 A x s) = (term224 A x s).
Proof. exact (TRANS (@lem3605542 A x s) (@lem3605537 A x s)). Qed.
Lemma lem3605544 {A : Type'} (x : A) : (term230 A x) = (term231 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3605543 A x s)). Qed.
Lemma lem3605545 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3605546 {A : Type'} (x : A) : (term227 A x) = (term232 A x).
Proof. exact (MK_COMB (@lem3605545 A) (@lem3605544 A x)). Qed.
Lemma lem3605547 {A : Type'} (x : A) : (term226 A x) = (term232 A x).
Proof. exact (TRANS (@lem3605539 A x) (@lem3605546 A x)). Qed.
Lemma lem3605548 {A : Type'} (P : A -> Prop) : (term233 A P) = (term234 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3605549 {A : Type'} : (term191 A) = (term235 A).
Proof. exact (@lem3605548 A (term101 A)). Qed.
Lemma lem3605550 {A : Type'} (x : A) : (term236 A x) = (term100 A x).
Proof. exact (eq_refl (term236 A x)). Qed.
Lemma lem3605551 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3605552 {A : Type'} (x : A) : (term237 A x) = (term226 A x).
Proof. exact (MK_COMB (@lem3605551) (@lem3605550 A x)). Qed.
Lemma lem3605553 {A : Type'} (x : A) : (term237 A x) = (term232 A x).
Proof. exact (TRANS (@lem3605552 A x) (@lem3605547 A x)). Qed.
Lemma lem3605554 {A : Type'} : (term238 A) = (term239 A).
Proof. exact (fun_ext (fun x : A => @lem3605553 A x)). Qed.
Lemma lem3605555 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3605556 {A : Type'} : (term235 A) = (term240 A).
Proof. exact (MK_COMB (@lem3605555 A) (@lem3605554 A)). Qed.
Lemma lem3605557 {A : Type'} : (term191 A) = (term240 A).
Proof. exact (TRANS (@lem3605549 A) (@lem3605556 A)). Qed.
Lemma lem3605688 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3605689 {A : Type'} (P : Prop) (Q : type686 A) : (term243 A P Q) = (term244 A P Q).
Proof. exact (@lem3605688 (A -> Prop) P Q). Qed.
Lemma lem3605690 {A : Type'} (x : A) (s : A -> Prop) : (term245 A x s) = (term246 A x s).
Proof. exact (@lem3605689 A (term209 A s) (term219 A x s)). Qed.
Lemma lem3605691 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term247 A x s t) = (term211 A x s t).
Proof. exact (eq_refl (term247 A x s t)). Qed.
Lemma lem3605692 {A : Type'} (x : A) (s : A -> Prop) : (term248 A x s) = (term219 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3605691 A x s t)). Qed.
Lemma lem3605693 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3605694 {A : Type'} (x : A) (s : A -> Prop) : (term249 A x s) = (term220 A x s).
Proof. exact (MK_COMB (@lem3605693 A) (@lem3605692 A x s)). Qed.
Lemma lem3605695 {A : Type'} (s : A -> Prop) : (term222 A s) = (term222 A s).
Proof. exact (eq_refl (term222 A s)). Qed.
Lemma lem3605696 {A : Type'} (x : A) (s : A -> Prop) : (term245 A x s) = (term224 A x s).
Proof. exact (MK_COMB (@lem3605695 A s) (@lem3605694 A x s)). Qed.
Lemma lem3605697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3605698 {A : Type'} (x : A) (s : A -> Prop) : (term250 A x s) = (term251 A x s).
Proof. exact (MK_COMB (@lem3605697) (@lem3605696 A x s)). Qed.
Lemma lem3605699 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term247 A x s t) = (term211 A x s t).
Proof. exact (eq_refl (term247 A x s t)). Qed.
Lemma lem3605700 {A : Type'} (s : A -> Prop) : (term222 A s) = (term222 A s).
Proof. exact (eq_refl (term222 A s)). Qed.
Lemma lem3605701 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term252 A x s t) = (term253 A x s t).
Proof. exact (MK_COMB (@lem3605700 A s) (@lem3605699 A x s t)). Qed.
Lemma lem3605702 {A : Type'} (x : A) (s : A -> Prop) : (term254 A x s) = (term255 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3605701 A x s t)). Qed.
Lemma lem3605703 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3605704 {A : Type'} (x : A) (s : A -> Prop) : (term246 A x s) = (term256 A x s).
Proof. exact (MK_COMB (@lem3605703 A) (@lem3605702 A x s)). Qed.
Lemma lem3605705 {A : Type'} (x : A) (s : A -> Prop) : ((term245 A x s) = (term246 A x s)) = ((term224 A x s) = (term256 A x s)).
Proof. exact (MK_COMB (@lem3605698 A x s) (@lem3605704 A x s)). Qed.
Lemma lem3605706 {A : Type'} (x : A) (s : A -> Prop) : (term224 A x s) = (term256 A x s).
Proof. exact (EQ_MP (@lem3605705 A x s) (@lem3605690 A x s)). Qed.
Lemma lem3605707 {A : Type'} (x : A) : (term231 A x) = (term257 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3605706 A x s)). Qed.
Lemma lem3605708 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3605709 {A : Type'} (x : A) : (term232 A x) = (term258 A x).
Proof. exact (MK_COMB (@lem3605708 A) (@lem3605707 A x)). Qed.
Lemma lem3605710 {A : Type'} : (term239 A) = (term259 A).
Proof. exact (fun_ext (fun x : A => @lem3605709 A x)). Qed.
Lemma lem3605711 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3605713 {A : Type'} : (term240 A) = (term260 A).
Proof. exact (MK_COMB (@lem3605711 A) (@lem3605710 A)). Qed.
Lemma lem3605714 {A : Type'} : (term191 A) = (term260 A).
Proof. exact (TRANS (@lem3605557 A) (@lem3605713 A)). Qed.
Lemma lem3605715 {A : Type'} (h1 : term191 A) : term260 A.
Proof. exact (EQ_MP (@lem3605714 A) (@lem3605504 A h1)). Qed.
Lemma lem3605723 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term261 A x s).
Proof. exact (@lem17265 (@FINITE A s) (term262 A x s)). Qed.
Lemma lem3605724 {A : Type'} (x : A) : (term202 A x) = (term263 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3605723 A x s)). Qed.
Lemma lem3605725 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605726 {A : Type'} (x : A) : (term203 A x) = (term264 A x).
Proof. exact (MK_COMB (@lem3605725 A) (@lem3605724 A x)). Qed.
Lemma lem3605727 {A : Type'} : (term204 A) = (term265 A).
Proof. exact (fun_ext (fun x : A => @lem3605726 A x)). Qed.
Lemma lem3605728 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3605729 {A : Type'} : (term205 A) = (term266 A).
Proof. exact (MK_COMB (@lem3605728 A) (@lem3605727 A)). Qed.
Lemma lem3605731 {A : Type'} : (term206 A) = (term206 A).
Proof. exact (eq_refl (term206 A)). Qed.
Lemma lem3605788 {A : Type'} : (term192 A) = (term267 A).
Proof. exact (MK_COMB (@lem3605731 A) (@lem3605729 A)). Qed.
Lemma lem3605789 {A : Type'} (h1 : term192 A) : term267 A.
Proof. exact (EQ_MP (@lem3605788 A) (@lem3605505 A h1)). Qed.
Lemma lem3605790 {A : Type'} (x : A) (h1 : term258 A x) : term258 A x.
Proof. exact (h1). Qed.
Lemma lem3605791 {A : Type'} (x : A) (s : A -> Prop) (h1 : term256 A x s) : term256 A x s.
Proof. exact (h1). Qed.
Lemma lem3605792 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term253 A x s t.
Proof. exact (h1). Qed.
Lemma lem3605807 {A : Type'} (x : A) (s : A -> Prop) : (term261 A x s) = (term261 A x s).
Proof. exact (eq_refl (term261 A x s)). Qed.
Lemma lem3605808 {A : Type'} (x : A) : (term263 A x) = (term263 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3605807 A x s)). Qed.
Lemma lem3605809 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605810 {A : Type'} (x : A) : (term264 A x) = (term264 A x).
Proof. exact (MK_COMB (@lem3605809 A) (@lem3605808 A x)). Qed.
Lemma lem3605811 {A : Type'} : (term265 A) = (term265 A).
Proof. exact (fun_ext (fun x : A => @lem3605810 A x)). Qed.
Lemma lem3605812 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3605813 {A : Type'} : (term266 A) = (term266 A).
Proof. exact (MK_COMB (@lem3605812 A) (@lem3605811 A)). Qed.
Lemma lem3605818 {A : Type'} : (term206 A) = (term206 A).
Proof. exact (eq_refl (term206 A)). Qed.
Lemma lem3605819 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem3605818 A) (@lem3605813 A)). Qed.
Lemma lem3605820 {A : Type'} (h1 : term192 A) : term267 A.
Proof. exact (EQ_MP (@lem3605819 A) (@lem3605789 A h1)). Qed.
Lemma lem3605839 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term211 A x s t) = (term211 A x s t).
Proof. exact (eq_refl (term211 A x s t)). Qed.
Lemma lem3605854 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term207 A s t) = (term207 A s t).
Proof. exact (eq_refl (term207 A s t)). Qed.
Lemma lem3605855 {A : Type'} (s : A -> Prop) : (term208 A s) = (term208 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3605854 A s t)). Qed.
Lemma lem3605856 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605857 {A : Type'} (s : A -> Prop) : (term209 A s) = (term209 A s).
Proof. exact (MK_COMB (@lem3605856 A) (@lem3605855 A s)). Qed.
Lemma lem3605858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3605859 {A : Type'} (s : A -> Prop) : (term222 A s) = (term222 A s).
Proof. exact (MK_COMB (@lem3605858) (@lem3605857 A s)). Qed.
Lemma lem3605860 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term253 A x s t) = (term253 A x s t).
Proof. exact (MK_COMB (@lem3605859 A s) (@lem3605839 A x s t)). Qed.
Lemma lem3605861 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term253 A x s t.
Proof. exact (EQ_MP (@lem3605860 A x s t) (@lem3605792 A x s t h1)). Qed.
Lemma lem3605862 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term211 A x s t.
Proof. exact (proj2 (@lem3605861 A x s t h1)). Qed.
Lemma lem3605863 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term209 A s.
Proof. exact (proj1 (@lem3605861 A x s t h1)). Qed.
Lemma lem3605866 {A : Type'} (h1 : term192 A) : term266 A.
Proof. exact (proj2 (@lem3605820 A h1)). Qed.
Lemma lem3605875 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term207 A s t) = (term207 A s t).
Proof. exact (eq_refl (term207 A s t)). Qed.
Lemma lem3605876 {A : Type'} (s : A -> Prop) : (term208 A s) = (term208 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3605875 A s t)). Qed.
Lemma lem3605877 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605879 {A : Type'} (s : A -> Prop) : (term209 A s) = (term209 A s).
Proof. exact (MK_COMB (@lem3605877 A) (@lem3605876 A s)). Qed.
Lemma lem3605880 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term209 A s.
Proof. exact (EQ_MP (@lem3605879 A s) (@lem3605863 A x s t h1)). Qed.
Lemma lem3605900 {A : Type'} (x : A) (s : A -> Prop) : (term261 A x s) = (term261 A x s).
Proof. exact (eq_refl (term261 A x s)). Qed.
Lemma lem3605901 {A : Type'} (x : A) : (term263 A x) = (term263 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3605900 A x s)). Qed.
Lemma lem3605902 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3605903 {A : Type'} (x : A) : (term264 A x) = (term264 A x).
Proof. exact (MK_COMB (@lem3605902 A) (@lem3605901 A x)). Qed.
Lemma lem3605904 {A : Type'} : (term265 A) = (term265 A).
Proof. exact (fun_ext (fun x : A => @lem3605903 A x)). Qed.
Lemma lem3605905 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3605907 {A : Type'} : (term266 A) = (term266 A).
Proof. exact (MK_COMB (@lem3605905 A) (@lem3605904 A)). Qed.
Lemma lem3605908 {A : Type'} (h1 : term192 A) : term266 A.
Proof. exact (EQ_MP (@lem3605907 A) (@lem3605866 A h1)). Qed.
Lemma lem3605909 {A : Type'} (_39082 : A -> Prop) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term268 A s _39082.
Proof. exact (@lem3605880 A x s t h1 _39082). Qed.
Lemma lem3605910 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : (term268 A s _39082) = (term207 A s _39082).
Proof. exact (eq_refl (term268 A s _39082)). Qed.
Lemma lem3605912 {A : Type'} (_39083 : A) (h1 : term192 A) : term269 A _39083.
Proof. exact (@lem3605908 A h1 _39083). Qed.
Lemma lem3605913 {A : Type'} (_39083 : A) : (term269 A _39083) = (term264 A _39083).
Proof. exact (eq_refl (term269 A _39083)). Qed.
Lemma lem3605914 {A : Type'} (_39083 : A) (h1 : term192 A) : term264 A _39083.
Proof. exact (EQ_MP (@lem3605913 A _39083) (@lem3605912 A _39083 h1)). Qed.
Lemma lem3605915 {A : Type'} (_39083 : A) (_39084 : A -> Prop) (h1 : term192 A) : term270 A _39083 _39084.
Proof. exact (@lem3605914 A _39083 h1 _39084). Qed.
Lemma lem3605916 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : (term270 A _39083 _39084) = (term261 A _39083 _39084).
Proof. exact (eq_refl (term270 A _39083 _39084)). Qed.
Lemma lem3605923 {A : Type'} (_39082 : A -> Prop) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term207 A s _39082.
Proof. exact (EQ_MP (@lem3605910 A s _39082) (@lem3605909 A _39082 x s t h1)). Qed.
Lemma lem3605927 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term271 A x s t.
Proof. exact (proj2 (@lem3605862 A x s t h1)). Qed.
Lemma lem3605935 {A : Type'} (_39083 : A) (_39084 : A -> Prop) (h1 : term192 A) : term261 A _39083 _39084.
Proof. exact (EQ_MP (@lem3605916 A _39083 _39084) (@lem3605915 A _39083 _39084 h1)). Qed.
Lemma lem3605937 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : @FINITE A t.
Proof. exact (proj1 (@lem3605862 A x s t h1)). Qed.
Lemma lem3605938 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term272 A t.
Proof. exact (fun h0 : term273 A t => @lem3605937 A x s t h1). Qed.
Lemma lem3605940 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605941 {A : Type'} (t : A -> Prop) : (term272 A t) = (@FINITE A t).
Proof. exact (@lem3605940 (@FINITE A t)). Qed.
Lemma lem3605942 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : @FINITE A t.
Proof. exact (EQ_MP (@lem3605941 A t) (@lem3605938 A x s t h1)). Qed.
Lemma lem3605948 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3605949 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : (term207 A s _39082) = (term274 A s _39082).
Proof. exact (@lem3605948 (term18 A s _39082) (term273 A _39082)). Qed.
Lemma lem3605955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3605956 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : (term275 A s _39082) = (term276 A s _39082).
Proof. exact (MK_COMB (@lem3605955) (@lem3605949 A s _39082)). Qed.
Lemma lem3605962 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : (term274 A s _39082) = (term274 A s _39082).
Proof. exact (eq_refl (term274 A s _39082)). Qed.
Lemma lem3605963 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : ((term207 A s _39082) = (term274 A s _39082)) = ((term274 A s _39082) = (term274 A s _39082)).
Proof. exact (MK_COMB (@lem3605956 A s _39082) (@lem3605962 A s _39082)). Qed.
Lemma lem3605965 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3605966 (x : Prop) : (x = x) = True.
Proof. exact (@lem3605965 Prop x). Qed.
Lemma lem3605967 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : ((term274 A s _39082) = (term274 A s _39082)) = True.
Proof. exact (@lem3605966 (term274 A s _39082)). Qed.
Lemma lem3605968 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : ((term207 A s _39082) = (term274 A s _39082)) = True.
Proof. exact (TRANS (@lem3605963 A s _39082) (@lem3605967 A s _39082)). Qed.
Lemma lem3605969 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : True = ((term207 A s _39082) = (term274 A s _39082)).
Proof. exact (SYM (@lem3605968 A s _39082)). Qed.
Lemma lem3605970 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : (term207 A s _39082) = (term274 A s _39082).
Proof. exact (EQ_MP (@lem3605969 A s _39082) (@lem0)). Qed.
Lemma lem3605971 {A : Type'} (_39082 : A -> Prop) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term274 A s _39082.
Proof. exact (EQ_MP (@lem3605970 A s _39082) (@lem3605923 A _39082 x s t h1)). Qed.
Lemma lem3605973 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3605974 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : (term274 A s _39082) = (term278 A s _39082).
Proof. exact (@lem3605973 (term273 A _39082) (term18 A s _39082)). Qed.
Lemma lem3605976 (a : Prop) : (term149 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3605977 {A : Type'} (_39082 : A -> Prop) : (term279 A _39082) = (@FINITE A _39082).
Proof. exact (@lem3605976 (@FINITE A _39082)). Qed.
Lemma lem3605978 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3605979 {A : Type'} (_39082 : A -> Prop) : (term280 A _39082) = (term34 A _39082).
Proof. exact (MK_COMB (@lem3605978) (@lem3605977 A _39082)). Qed.
Lemma lem3605980 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : (term18 A s _39082) = (term18 A s _39082).
Proof. exact (eq_refl (term18 A s _39082)). Qed.
Lemma lem3605981 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : (term278 A s _39082) = (term33 A s _39082).
Proof. exact (MK_COMB (@lem3605979 A _39082) (@lem3605980 A s _39082)). Qed.
Lemma lem3605982 {A : Type'} (s : A -> Prop) (_39082 : A -> Prop) : (term274 A s _39082) = (term33 A s _39082).
Proof. exact (TRANS (@lem3605974 A s _39082) (@lem3605981 A s _39082)). Qed.
Lemma lem3605985 {A : Type'} (_39082 : A -> Prop) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term33 A s _39082.
Proof. exact (EQ_MP (@lem3605982 A s _39082) (@lem3605971 A _39082 x s t h1)). Qed.
Lemma lem3605986 {A : Type'} (_39082 : A -> Prop) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term33 A s _39082.
Proof. exact (@lem3605985 A _39082 x s t h1). Qed.
Lemma lem3605987 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term33 A s t.
Proof. exact (@lem3605986 A t x s t h1). Qed.
Lemma lem3605990 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term18 A s t.
Proof. exact (@lem3605987 A x s t h1 (@lem3605942 A x s t h1)). Qed.
Lemma lem3605991 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term281 A s t.
Proof. exact (fun h0 : term282 A s t => @lem3605990 A x s t h1). Qed.
Lemma lem3605993 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3605994 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term281 A s t) = (term18 A s t).
Proof. exact (@lem3605993 (term18 A s t)). Qed.
Lemma lem3605995 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term18 A s t.
Proof. exact (EQ_MP (@lem3605994 A s t) (@lem3605991 A x s t h1)). Qed.
Lemma lem3606001 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3606002 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : (term261 A _39083 _39084) = (term283 A _39083 _39084).
Proof. exact (@lem3606001 (term262 A _39083 _39084) (term273 A _39084)). Qed.
Lemma lem3606008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3606009 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : (term284 A _39083 _39084) = (term285 A _39083 _39084).
Proof. exact (MK_COMB (@lem3606008) (@lem3606002 A _39083 _39084)). Qed.
Lemma lem3606015 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : (term283 A _39083 _39084) = (term283 A _39083 _39084).
Proof. exact (eq_refl (term283 A _39083 _39084)). Qed.
Lemma lem3606016 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : ((term261 A _39083 _39084) = (term283 A _39083 _39084)) = ((term283 A _39083 _39084) = (term283 A _39083 _39084)).
Proof. exact (MK_COMB (@lem3606009 A _39083 _39084) (@lem3606015 A _39083 _39084)). Qed.
Lemma lem3606018 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3606019 (x : Prop) : (x = x) = True.
Proof. exact (@lem3606018 Prop x). Qed.
Lemma lem3606020 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : ((term283 A _39083 _39084) = (term283 A _39083 _39084)) = True.
Proof. exact (@lem3606019 (term283 A _39083 _39084)). Qed.
Lemma lem3606021 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : ((term261 A _39083 _39084) = (term283 A _39083 _39084)) = True.
Proof. exact (TRANS (@lem3606016 A _39083 _39084) (@lem3606020 A _39083 _39084)). Qed.
Lemma lem3606022 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : True = ((term261 A _39083 _39084) = (term283 A _39083 _39084)).
Proof. exact (SYM (@lem3606021 A _39083 _39084)). Qed.
Lemma lem3606023 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : (term261 A _39083 _39084) = (term283 A _39083 _39084).
Proof. exact (EQ_MP (@lem3606022 A _39083 _39084) (@lem0)). Qed.
Lemma lem3606024 {A : Type'} (_39083 : A) (_39084 : A -> Prop) (h1 : term192 A) : term283 A _39083 _39084.
Proof. exact (EQ_MP (@lem3606023 A _39083 _39084) (@lem3605935 A _39083 _39084 h1)). Qed.
Lemma lem3606026 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3606027 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : (term283 A _39083 _39084) = (term286 A _39083 _39084).
Proof. exact (@lem3606026 (term273 A _39084) (term262 A _39083 _39084)). Qed.
Lemma lem3606029 (a : Prop) : (term149 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3606030 {A : Type'} (_39084 : A -> Prop) : (term279 A _39084) = (@FINITE A _39084).
Proof. exact (@lem3606029 (@FINITE A _39084)). Qed.
Lemma lem3606031 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3606032 {A : Type'} (_39084 : A -> Prop) : (term280 A _39084) = (term34 A _39084).
Proof. exact (MK_COMB (@lem3606031) (@lem3606030 A _39084)). Qed.
Lemma lem3606033 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : (term262 A _39083 _39084) = (term262 A _39083 _39084).
Proof. exact (eq_refl (term262 A _39083 _39084)). Qed.
Lemma lem3606034 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : (term286 A _39083 _39084) = (term201 A _39083 _39084).
Proof. exact (MK_COMB (@lem3606032 A _39084) (@lem3606033 A _39083 _39084)). Qed.
Lemma lem3606035 {A : Type'} (_39083 : A) (_39084 : A -> Prop) : (term283 A _39083 _39084) = (term201 A _39083 _39084).
Proof. exact (TRANS (@lem3606027 A _39083 _39084) (@lem3606034 A _39083 _39084)). Qed.
Lemma lem3606038 {A : Type'} (_39083 : A) (_39084 : A -> Prop) (h1 : term192 A) : term201 A _39083 _39084.
Proof. exact (EQ_MP (@lem3606035 A _39083 _39084) (@lem3606024 A _39083 _39084 h1)). Qed.
Lemma lem3606039 {A : Type'} (_39083 : A) (_39084 : A -> Prop) (h1 : term192 A) : term201 A _39083 _39084.
Proof. exact (@lem3606038 A _39083 _39084 h1). Qed.
Lemma lem3606040 {A : Type'} (_39083 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term192 A) : term287 A _39083 s t.
Proof. exact (@lem3606039 A _39083 (@UNION A s t) h1). Qed.
Lemma lem3606043 {A : Type'} (_39083 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : term92 A _39083 s t.
Proof. exact (@lem3606040 A _39083 s t h2 (@lem3605995 A x s t h1)). Qed.
Lemma lem3606044 {A : Type'} (_39083 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : term92 A _39083 s t.
Proof. exact (@lem3606043 A _39083 x s t h1 h2). Qed.
Lemma lem3606045 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : term92 A x s t.
Proof. exact (@lem3606044 A x x s t h1 h2). Qed.
Lemma lem3606046 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : term288 A x s t.
Proof. exact (fun h0 : term271 A x s t => @lem3606045 A x s t h1 h2). Qed.
Lemma lem3606048 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3606049 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term288 A x s t) = (term92 A x s t).
Proof. exact (@lem3606048 (term92 A x s t)). Qed.
Lemma lem3606050 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : term92 A x s t.
Proof. exact (EQ_MP (@lem3606049 A x s t) (@lem3606046 A x s t h1 h2)). Qed.
Lemma lem3606053 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3606055 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term271 A x s t) = (term289 A x s t).
Proof. exact (@lem3606053 (term92 A x s t)). Qed.
Lemma lem3606058 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) : term289 A x s t.
Proof. exact (EQ_MP (@lem3606055 A x s t) (@lem3605927 A x s t h1)). Qed.
Lemma lem3606061 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : False.
Proof. exact (@lem3606058 A x s t h1 (@lem3606050 A x s t h1 h2)). Qed.
Lemma lem3606062 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : term187.
Proof. exact (fun h0 : ~ False => @lem3606061 A x s t h1 h2). Qed.
Lemma lem3606064 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3606065 : term187 = False.
Proof. exact (@lem3606064 False). Qed.
Lemma lem3606066 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : False.
Proof. exact (EQ_MP (@lem3606065) (@lem3606062 A x s t h1 h2)). Qed.
Lemma lem3606067 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : (term253 A x s t) = False.
Proof. exact (prop_ext (fun h3 : term253 A x s t => @lem3606066 A x s t h1 h2) (fun h3 : False => @lem3605861 A x s t h1)). Qed.
Lemma lem3606068 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term253 A x s t) (h2 : term192 A) : False.
Proof. exact (EQ_MP (@lem3606067 A x s t h1 h2) (@lem3605861 A x s t h1)). Qed.
Lemma lem3606069 {A : Type'} (x : A) (s : A -> Prop) (h1 : term256 A x s) (h2 : term192 A) : False.
Proof. exact (ex_elim (@lem3605791 A x s h1) (fun t : A -> Prop => fun h0 : term255 A x s t => @lem3606068 A x s t h0 h2)). Qed.
Lemma lem3606070 {A : Type'} (x : A) (h1 : term258 A x) (h2 : term192 A) : False.
Proof. exact (ex_elim (@lem3605790 A x h1) (fun s : A -> Prop => fun h0 : term257 A x s => @lem3606069 A x s h0 h2)). Qed.
Lemma lem3606071 {A : Type'} (h1 : term191 A) (h2 : term192 A) : False.
Proof. exact (ex_elim (@lem3605715 A h1) (fun x : A => fun h0 : term259 A x => @lem3606070 A x h0 h2)). Qed.
Lemma lem3606072 {A : Type'} (h1 : term191 A) : term197 A.
Proof. exact (fun h0 : term192 A => @lem3606071 A h1 h0). Qed.
Lemma lem3606073 {A : Type'} : (term197 A) = (term198 A).
Proof. exact (@lem69 (term192 A)). Qed.
Lemma lem3606074 {A : Type'} (h1 : term191 A) : term198 A.
Proof. exact (EQ_MP (@lem3606073 A) (@lem3606072 A h1)). Qed.
Lemma lem3606075 {A : Type'} : term200 A.
Proof. exact (fun h0 : term191 A => @lem3606074 A h0). Qed.
Lemma lem3606076 {A : Type'} : term193 A.
Proof. exact (EQ_MP (@lem3605503 A) (@lem3606075 A)). Qed.
Lemma lem3606078 {A : Type'} : term193 A.
Proof. exact (@lem3605357 A (@lem3606076 A)). Qed.
Lemma lem3606079 {A : Type'} (h1 : term191 A) : term197 A.
Proof. exact (@lem3606078 A (@lem3605339 A h1)). Qed.
Lemma lem3606080 {A : Type'} (h1 : term191 A) : False.
Proof. exact (@lem3606079 A h1 (@lem3605340 A)). Qed.
Lemma lem3606081 {A : Type'} (h1 : term191 A) : (term191 A) = False.
Proof. exact (prop_ext (fun h2 : term191 A => @lem3606080 A h1) (fun h2 : False => @lem3605339 A h1)). Qed.
Lemma lem3606082 {A : Type'} (h1 : term191 A) : False.
Proof. exact (EQ_MP (@lem3606081 A h1) (@lem3605339 A h1)). Qed.
Lemma lem3606083 {A : Type'} : term190 A.
Proof. exact (fun h0 : term191 A => @lem3606082 A h0). Qed.
Lemma lem3606084 {A : Type'} : term102 A.
Proof. exact (EQ_MP (@lem3605338 A) (@lem3606083 A)). Qed.
Lemma lem3606085 {A : Type'} (h1 : term83 A) : term65 A.
Proof. exact (EQ_MP (@lem3604243 A h1) (@lem3606084 A)). Qed.
Lemma lem3606086 {A : Type'} : (term83 A) = (term65 A).
Proof. exact (prop_ext (fun h1 : term83 A => @lem3606085 A h1) (fun h1 : term65 A => @lem3605334 A)). Qed.
Lemma lem3606087 {A : Type'} : term65 A.
Proof. exact (EQ_MP (@lem3606086 A) (@lem3605334 A)). Qed.
Lemma lem3606088 {A : Type'} : term67 A.
Proof. exact (EQ_MP (@lem3604176 A) (@lem3606087 A)). Qed.
Lemma lem3606089 {A : Type'} : term44 A.
Proof. exact (@lem3604095 A (@lem3606088 A)). Qed.
Lemma lem3606090 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem3604066 A) (@lem3606089 A)). Qed.
Lemma lem3606091 {A : Type'} : term25 A.
Proof. exact (EQ_MP (@lem3603986 A) (@lem3606090 A)). Qed.
