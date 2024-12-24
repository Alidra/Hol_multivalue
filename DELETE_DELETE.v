Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DELETE_DELETE_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3306883 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3306884 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3306883 A s t). Qed.
Lemma lem3306885 {A : Type'} (s : A -> Prop) (x : A) : ((term1 A s x) = (@DELETE A s x)) = (term2 A s x).
Proof. exact (@lem3306884 A (term1 A s x) (@DELETE A s x)). Qed.
Lemma lem3306894 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3306885 A s x)). Qed.
Lemma lem3306895 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3306896 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (MK_COMB (@lem3306895 A) (@lem3306894 A x)). Qed.
Lemma lem3306901 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun x : A => @lem3306896 A x)). Qed.
Lemma lem3306902 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3306903 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3306902 A) (@lem3306901 A)). Qed.
Lemma lem3306908 {A : Type'} : (term10 A) = (term9 A).
Proof. exact (SYM (@lem3306903 A)). Qed.
Lemma lem3306924 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3306925 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (@lem3306924 A s x y). Qed.
Lemma lem3306926 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term13 A x' s x) = (term14 A s x' x).
Proof. exact (@lem3306925 A (@DELETE A s x) x' x). Qed.
Lemma lem3306930 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3306931 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (@lem3306930 A s x y). Qed.
Lemma lem3306932 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term11 A x' s x) = (term12 A s x' x).
Proof. exact (@lem3306931 A s x' x). Qed.
Lemma lem3306936 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3306937 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3306936 A P x). Qed.
Lemma lem3306938 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3306937 A s x'). Qed.
Lemma lem3306939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3306940 {A : Type'} (s : A -> Prop) (x' : A) : (term15 A x' s) = (term16 A s x').
Proof. exact (MK_COMB (@lem3306939) (@lem3306938 A s x')). Qed.
Lemma lem3306943 {A : Type'} (x' : A) (x : A) : (term17 A x' x) = (term17 A x' x).
Proof. exact (eq_refl (term17 A x' x)). Qed.
Lemma lem3306944 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term12 A s x' x) = (term18 A s x' x).
Proof. exact (MK_COMB (@lem3306940 A s x') (@lem3306943 A x' x)). Qed.
Lemma lem3306947 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term11 A x' s x) = (term18 A s x' x).
Proof. exact (TRANS (@lem3306932 A s x' x) (@lem3306944 A s x' x)). Qed.
Lemma lem3306948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3306949 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term19 A x' s x) = (term20 A s x' x).
Proof. exact (MK_COMB (@lem3306948) (@lem3306947 A s x' x)). Qed.
Lemma lem3306952 {A : Type'} (x' : A) (x : A) : (term17 A x' x) = (term17 A x' x).
Proof. exact (eq_refl (term17 A x' x)). Qed.
Lemma lem3306953 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term14 A s x' x) = (term21 A s x' x).
Proof. exact (MK_COMB (@lem3306949 A s x' x) (@lem3306952 A x' x)). Qed.
Lemma lem3306956 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term13 A x' s x) = (term21 A s x' x).
Proof. exact (TRANS (@lem3306926 A s x' x) (@lem3306953 A s x' x)). Qed.
Lemma lem3306957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3306958 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term22 A x' s x) = (term23 A s x' x).
Proof. exact (MK_COMB (@lem3306957) (@lem3306956 A s x' x)). Qed.
Lemma lem3306960 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3306961 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (@lem3306960 A s x y). Qed.
Lemma lem3306962 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term11 A x' s x) = (term12 A s x' x).
Proof. exact (@lem3306961 A s x' x). Qed.
Lemma lem3306966 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3306967 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3306966 A P x). Qed.
Lemma lem3306968 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3306967 A s x'). Qed.
Lemma lem3306969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3306970 {A : Type'} (s : A -> Prop) (x' : A) : (term15 A x' s) = (term16 A s x').
Proof. exact (MK_COMB (@lem3306969) (@lem3306968 A s x')). Qed.
Lemma lem3306973 {A : Type'} (x' : A) (x : A) : (term17 A x' x) = (term17 A x' x).
Proof. exact (eq_refl (term17 A x' x)). Qed.
Lemma lem3306974 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term12 A s x' x) = (term18 A s x' x).
Proof. exact (MK_COMB (@lem3306970 A s x') (@lem3306973 A x' x)). Qed.
Lemma lem3306977 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term11 A x' s x) = (term18 A s x' x).
Proof. exact (TRANS (@lem3306962 A s x' x) (@lem3306974 A s x' x)). Qed.
Lemma lem3306978 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term13 A x' s x) = (term11 A x' s x)) = ((term21 A s x' x) = (term18 A s x' x)).
Proof. exact (MK_COMB (@lem3306958 A s x' x) (@lem3306977 A s x' x)). Qed.
Lemma lem3306981 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term25 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3306978 A s x' x)). Qed.
Lemma lem3306982 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3306983 {A : Type'} (s : A -> Prop) (x : A) : (term2 A s x) = (term26 A s x).
Proof. exact (MK_COMB (@lem3306982 A) (@lem3306981 A s x)). Qed.
Lemma lem3306988 {A : Type'} (x : A) : (term4 A x) = (term27 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3306983 A s x)). Qed.
Lemma lem3306989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3306990 {A : Type'} (x : A) : (term6 A x) = (term28 A x).
Proof. exact (MK_COMB (@lem3306989 A) (@lem3306988 A x)). Qed.
Lemma lem3306995 {A : Type'} : (term8 A) = (term29 A).
Proof. exact (fun_ext (fun x : A => @lem3306990 A x)). Qed.
Lemma lem3306996 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3306997 {A : Type'} : (term10 A) = (term30 A).
Proof. exact (MK_COMB (@lem3306996 A) (@lem3306995 A)). Qed.
Lemma lem3307002 {A : Type'} : (term30 A) = (term10 A).
Proof. exact (SYM (@lem3306997 A)). Qed.
Lemma lem3307004 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3307005 {A : Type'} : (term30 A) = (term32 A).
Proof. exact (@lem3307004 (term30 A)). Qed.
Lemma lem3307006 {A : Type'} : (term32 A) = (term30 A).
Proof. exact (SYM (@lem3307005 A)). Qed.
Lemma lem3307007 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3307010 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3307011 {A : Type'} : term34 A.
Proof. exact (fun h0 : term32 A => @lem3307010 A h0). Qed.
Lemma lem3307012 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem3307013 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3307014 {A : Type'} (h1 : term32 A) (h2 : term34 A) : term32 A.
Proof. exact (@lem3307012 A h2 (@lem3307013 A h1)). Qed.
Lemma lem3307015 {A : Type'} (h1 : term32 A) : term35 A.
Proof. exact (fun h0 : term34 A => @lem3307014 A h1 h0). Qed.
Lemma lem3307016 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem3307017 {A : Type'} (h1 : term32 A) (h2 : term34 A) : term32 A.
Proof. exact (@lem3307015 A h1 (@lem3307016 A h2)). Qed.
Lemma lem3307018 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (fun h0 : term32 A => @lem3307017 A h0 h1). Qed.
Lemma lem3307019 {A : Type'} : term36 A.
Proof. exact (fun h0 : term34 A => @lem3307018 A h0). Qed.
Lemma lem3307022 {A : Type'} : term34 A.
Proof. exact (@lem3307019 A (@lem3307011 A)). Qed.
Lemma lem3307023 {A : Type'} : term34 A.
Proof. exact (@lem3307022 A). Qed.
Lemma lem3307025 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3307026 {A : Type'} : (term32 A) = (term37 A).
Proof. exact (@lem3307025 (term33 A)). Qed.
Lemma lem3307028 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3307029 {A : Type'} : (term37 A) = (term30 A).
Proof. exact (@lem3307028 (term30 A)). Qed.
Lemma lem3307052 {A : Type'} : (term32 A) = (term30 A).
Proof. exact (TRANS (@lem3307026 A) (@lem3307029 A)). Qed.
Lemma lem3307075 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term21 A s x' x) = (term18 A s x' x)) = ((term21 A s x' x) = (term18 A s x' x)).
Proof. exact (eq_refl ((term21 A s x' x) = (term18 A s x' x))). Qed.
Lemma lem3307076 {A : Type'} (s : A -> Prop) (x : A) : (term25 A s x) = (term25 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3307075 A s x' x)). Qed.
Lemma lem3307077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3307078 {A : Type'} (s : A -> Prop) (x : A) : (term26 A s x) = (term26 A s x).
Proof. exact (MK_COMB (@lem3307077 A) (@lem3307076 A s x)). Qed.
Lemma lem3307079 {A : Type'} (x : A) : (term27 A x) = (term27 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3307078 A s x)). Qed.
Lemma lem3307080 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3307081 {A : Type'} (x : A) : (term28 A x) = (term28 A x).
Proof. exact (MK_COMB (@lem3307080 A) (@lem3307079 A x)). Qed.
Lemma lem3307082 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (fun_ext (fun x : A => @lem3307081 A x)). Qed.
Lemma lem3307083 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3307084 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (MK_COMB (@lem3307083 A) (@lem3307082 A)). Qed.
Lemma lem3307111 {A : Type'} : (term32 A) = (term30 A).
Proof. exact (TRANS (@lem3307052 A) (@lem3307084 A)). Qed.
Lemma lem3307112 {A : Type'} : (term30 A) = (term32 A).
Proof. exact (SYM (@lem3307111 A)). Qed.
Lemma lem3307114 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3307115 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term21 A s x' x) = (term18 A s x' x)) = (term39 A s x' x).
Proof. exact (@lem3307114 ((term21 A s x' x) = (term18 A s x' x))). Qed.
Lemma lem3307116 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term39 A s x' x) = ((term21 A s x' x) = (term18 A s x' x)).
Proof. exact (SYM (@lem3307115 A s x' x)). Qed.
Lemma lem3307117 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term40 A s x' x) : term40 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3307123 {A : Type'} (x' : A) (x : A) : (term41 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3307125 {A : Type'} (s : A -> Prop) (x' : A) : (term42 A s x') = (term42 A s x').
Proof. exact (eq_refl (term42 A s x')). Qed.
Lemma lem3307126 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term43 A s x' x) = (term44 A s x' x).
Proof. exact (MK_COMB (@lem3307125 A s x') (@lem3307123 A x' x)). Qed.
Lemma lem3307127 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term45 A s x' x) = (term43 A s x' x).
Proof. exact (@lem17045 (s x') (term17 A x' x)). Qed.
Lemma lem3307128 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term45 A s x' x) = (term44 A s x' x).
Proof. exact (TRANS (@lem3307127 A s x' x) (@lem3307126 A s x' x)). Qed.
Lemma lem3307135 {A : Type'} (x' : A) (x : A) : (term41 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3307136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3307137 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term46 A s x' x) = (term47 A s x' x).
Proof. exact (MK_COMB (@lem3307136) (@lem3307128 A s x' x)). Qed.
Lemma lem3307138 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term48 A s x' x) = (term49 A s x' x).
Proof. exact (MK_COMB (@lem3307137 A s x' x) (@lem3307135 A x' x)). Qed.
Lemma lem3307139 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term50 A s x' x) = (term48 A s x' x).
Proof. exact (@lem17045 (term18 A s x' x) (term17 A x' x)). Qed.
Lemma lem3307140 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term50 A s x' x) = (term49 A s x' x).
Proof. exact (TRANS (@lem3307139 A s x' x) (@lem3307138 A s x' x)). Qed.
Lemma lem3307149 {A : Type'} (x' : A) (x : A) : (term41 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3307151 {A : Type'} (s : A -> Prop) (x' : A) : (term42 A s x') = (term42 A s x').
Proof. exact (eq_refl (term42 A s x')). Qed.
Lemma lem3307152 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term43 A s x' x) = (term44 A s x' x).
Proof. exact (MK_COMB (@lem3307151 A s x') (@lem3307149 A x' x)). Qed.
Lemma lem3307153 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term45 A s x' x) = (term43 A s x' x).
Proof. exact (@lem17045 (s x') (term17 A x' x)). Qed.
Lemma lem3307154 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term45 A s x' x) = (term44 A s x' x).
Proof. exact (TRANS (@lem3307153 A s x' x) (@lem3307152 A s x' x)). Qed.
Lemma lem3307157 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term18 A s x' x) = (term18 A s x' x).
Proof. exact (eq_refl (term18 A s x' x)). Qed.
Lemma lem3307158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3307159 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term51 A s x' x) = (term52 A s x' x).
Proof. exact (MK_COMB (@lem3307158) (@lem3307140 A s x' x)). Qed.
Lemma lem3307160 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term53 A s x' x) = (term54 A s x' x).
Proof. exact (MK_COMB (@lem3307159 A s x' x) (@lem3307157 A s x' x)). Qed.
Lemma lem3307162 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term55 A s x' x) = (term55 A s x' x).
Proof. exact (eq_refl (term55 A s x' x)). Qed.
Lemma lem3307163 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term56 A s x' x) = (term57 A s x' x).
Proof. exact (MK_COMB (@lem3307162 A s x' x) (@lem3307154 A s x' x)). Qed.
Lemma lem3307164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3307165 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term58 A s x' x) = (term59 A s x' x).
Proof. exact (MK_COMB (@lem3307164) (@lem3307163 A s x' x)). Qed.
Lemma lem3307166 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term60 A s x' x) = (term61 A s x' x).
Proof. exact (MK_COMB (@lem3307165 A s x' x) (@lem3307160 A s x' x)). Qed.
Lemma lem3307167 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term40 A s x' x) = (term60 A s x' x).
Proof. exact (@lem17646 (term21 A s x' x) (term18 A s x' x)). Qed.
Lemma lem3307172 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term40 A s x' x) = (term61 A s x' x).
Proof. exact (TRANS (@lem3307167 A s x' x) (@lem3307166 A s x' x)). Qed.
Lemma lem3307253 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term40 A s x' x) : term61 A s x' x.
Proof. exact (EQ_MP (@lem3307172 A s x' x) (@lem3307117 A s x' x h1)). Qed.
Lemma lem3307254 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) : term57 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3307255 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) : term54 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3307256 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) : term44 A s x' x.
Proof. exact (proj2 (@lem3307254 A s x' x h1)). Qed.
Lemma lem3307257 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) : term21 A s x' x.
Proof. exact (proj1 (@lem3307254 A s x' x h1)). Qed.
Lemma lem3307259 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) : term18 A s x' x.
Proof. exact (proj1 (@lem3307257 A s x' x h1)). Qed.
Lemma lem3307264 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) : term18 A s x' x.
Proof. exact (proj2 (@lem3307255 A s x' x h1)). Qed.
Lemma lem3307265 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) : term49 A s x' x.
Proof. exact (proj1 (@lem3307255 A s x' x h1)). Qed.
Lemma lem3307268 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term44 A s x' x) : term44 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3307287 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term62 A s x'.
Proof. exact (h1). Qed.
Lemma lem3307303 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3307315 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term62 A s x'.
Proof. exact (h1). Qed.
Lemma lem3307327 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3307339 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3307347 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term62 A s x'.
Proof. exact (h1). Qed.
Lemma lem3307349 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) : term17 A x' x.
Proof. exact (proj2 (@lem3307257 A s x' x h1)). Qed.
Lemma lem3307355 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3307361 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term62 A s x'.
Proof. exact (h1). Qed.
Lemma lem3307365 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) : term17 A x' x.
Proof. exact (proj2 (@lem3307264 A s x' x h1)). Qed.
Lemma lem3307367 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3307371 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) : term17 A x' x.
Proof. exact (proj2 (@lem3307264 A s x' x h1)). Qed.
Lemma lem3307373 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3307388 {A : Type'} (x : A) : (term63 A x) = (term63 A x).
Proof. exact (eq_refl (term63 A x)). Qed.
Lemma lem3307389 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term64 A x x') = (term65 A x).
Proof. exact (MK_COMB (@lem3307388 A x) (@lem3307355 A x' x h1)). Qed.
Lemma lem3307390 {A : Type'} (x : A) : (term65 A x) = (term66 A x).
Proof. exact (eq_refl (term65 A x)). Qed.
Lemma lem3307391 {A : Type'} (x : A) (x' : A) : (term67 A x x') = (term67 A x x').
Proof. exact (eq_refl (term67 A x x')). Qed.
Lemma lem3307392 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term64 A x x') = (term66 A x)).
Proof. exact (MK_COMB (@lem3307391 A x x') (@lem3307390 A x)). Qed.
Lemma lem3307393 {A : Type'} (x' : A) (x : A) : (term64 A x x') = (term17 A x' x).
Proof. exact (eq_refl (term64 A x x')). Qed.
Lemma lem3307394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3307395 {A : Type'} (x' : A) (x : A) : (term67 A x x') = (term68 A x' x).
Proof. exact (MK_COMB (@lem3307394) (@lem3307393 A x' x)). Qed.
Lemma lem3307396 {A : Type'} (x : A) : (term66 A x) = (term66 A x).
Proof. exact (eq_refl (term66 A x)). Qed.
Lemma lem3307397 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term66 A x)) = ((term17 A x' x) = (term66 A x)).
Proof. exact (MK_COMB (@lem3307395 A x' x) (@lem3307396 A x)). Qed.
Lemma lem3307398 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term17 A x' x) = (term66 A x)).
Proof. exact (TRANS (@lem3307392 A x' x) (@lem3307397 A x' x)). Qed.
Lemma lem3307399 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term17 A x' x) = (term66 A x).
Proof. exact (EQ_MP (@lem3307398 A x' x) (@lem3307389 A x' x h1)). Qed.
Lemma lem3307400 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : term66 A x.
Proof. exact (EQ_MP (@lem3307399 A x' x h2) (@lem3307349 A s x' x h1)). Qed.
Lemma lem3307454 {A : Type'} (x : A) : (term63 A x) = (term63 A x).
Proof. exact (eq_refl (term63 A x)). Qed.
Lemma lem3307455 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term64 A x x') = (term65 A x).
Proof. exact (MK_COMB (@lem3307454 A x) (@lem3307367 A x' x h1)). Qed.
Lemma lem3307456 {A : Type'} (x : A) : (term65 A x) = (term66 A x).
Proof. exact (eq_refl (term65 A x)). Qed.
Lemma lem3307457 {A : Type'} (x : A) (x' : A) : (term67 A x x') = (term67 A x x').
Proof. exact (eq_refl (term67 A x x')). Qed.
Lemma lem3307458 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term64 A x x') = (term66 A x)).
Proof. exact (MK_COMB (@lem3307457 A x x') (@lem3307456 A x)). Qed.
Lemma lem3307459 {A : Type'} (x' : A) (x : A) : (term64 A x x') = (term17 A x' x).
Proof. exact (eq_refl (term64 A x x')). Qed.
Lemma lem3307460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3307461 {A : Type'} (x' : A) (x : A) : (term67 A x x') = (term68 A x' x).
Proof. exact (MK_COMB (@lem3307460) (@lem3307459 A x' x)). Qed.
Lemma lem3307462 {A : Type'} (x : A) : (term66 A x) = (term66 A x).
Proof. exact (eq_refl (term66 A x)). Qed.
Lemma lem3307463 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term66 A x)) = ((term17 A x' x) = (term66 A x)).
Proof. exact (MK_COMB (@lem3307461 A x' x) (@lem3307462 A x)). Qed.
Lemma lem3307464 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term17 A x' x) = (term66 A x)).
Proof. exact (TRANS (@lem3307458 A x' x) (@lem3307463 A x' x)). Qed.
Lemma lem3307465 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term17 A x' x) = (term66 A x).
Proof. exact (EQ_MP (@lem3307464 A x' x) (@lem3307455 A x' x h1)). Qed.
Lemma lem3307466 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : term66 A x.
Proof. exact (EQ_MP (@lem3307465 A x' x h2) (@lem3307365 A s x' x h1)). Qed.
Lemma lem3307494 {A : Type'} (x : A) : (term63 A x) = (term63 A x).
Proof. exact (eq_refl (term63 A x)). Qed.
Lemma lem3307495 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term64 A x x') = (term65 A x).
Proof. exact (MK_COMB (@lem3307494 A x) (@lem3307373 A x' x h1)). Qed.
Lemma lem3307496 {A : Type'} (x : A) : (term65 A x) = (term66 A x).
Proof. exact (eq_refl (term65 A x)). Qed.
Lemma lem3307497 {A : Type'} (x : A) (x' : A) : (term67 A x x') = (term67 A x x').
Proof. exact (eq_refl (term67 A x x')). Qed.
Lemma lem3307498 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term64 A x x') = (term66 A x)).
Proof. exact (MK_COMB (@lem3307497 A x x') (@lem3307496 A x)). Qed.
Lemma lem3307499 {A : Type'} (x' : A) (x : A) : (term64 A x x') = (term17 A x' x).
Proof. exact (eq_refl (term64 A x x')). Qed.
Lemma lem3307500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3307501 {A : Type'} (x' : A) (x : A) : (term67 A x x') = (term68 A x' x).
Proof. exact (MK_COMB (@lem3307500) (@lem3307499 A x' x)). Qed.
Lemma lem3307502 {A : Type'} (x : A) : (term66 A x) = (term66 A x).
Proof. exact (eq_refl (term66 A x)). Qed.
Lemma lem3307503 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term66 A x)) = ((term17 A x' x) = (term66 A x)).
Proof. exact (MK_COMB (@lem3307501 A x' x) (@lem3307502 A x)). Qed.
Lemma lem3307504 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term17 A x' x) = (term66 A x)).
Proof. exact (TRANS (@lem3307498 A x' x) (@lem3307503 A x' x)). Qed.
Lemma lem3307505 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term17 A x' x) = (term66 A x).
Proof. exact (EQ_MP (@lem3307504 A x' x) (@lem3307495 A x' x h1)). Qed.
Lemma lem3307506 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : term66 A x.
Proof. exact (EQ_MP (@lem3307505 A x' x h2) (@lem3307371 A s x' x h1)). Qed.
Lemma lem3307522 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) : s x'.
Proof. exact (proj1 (@lem3307259 A s x' x h1)). Qed.
Lemma lem3307523 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) : term69 A s x'.
Proof. exact (fun h0 : term62 A s x' => @lem3307522 A s x' x h1). Qed.
Lemma lem3307525 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307526 {A : Type'} (s : A -> Prop) (x' : A) : (term69 A s x') = (s x').
Proof. exact (@lem3307525 (s x')). Qed.
Lemma lem3307527 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3307526 A s x') (@lem3307523 A s x' x h1)). Qed.
Lemma lem3307530 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3307532 {A : Type'} (s : A -> Prop) (x' : A) : (term62 A s x') = (term71 A s x').
Proof. exact (@lem3307530 (s x')). Qed.
Lemma lem3307535 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term71 A s x'.
Proof. exact (EQ_MP (@lem3307532 A s x') (@lem3307347 A s x' h1)). Qed.
Lemma lem3307538 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s x' x) : False.
Proof. exact (@lem3307535 A s x' h1 (@lem3307527 A s x' x h2)). Qed.
Lemma lem3307539 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s x' x) : term72.
Proof. exact (fun h0 : ~ False => @lem3307538 A s x' x h1 h2). Qed.
Lemma lem3307541 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307542 : term72 = False.
Proof. exact (@lem3307541 False). Qed.
Lemma lem3307543 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s x' x) : False.
Proof. exact (EQ_MP (@lem3307542) (@lem3307539 A s x' x h1 h2)). Qed.
Lemma lem3307559 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3307560 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3307559 A x). Qed.
Lemma lem3307561 {A : Type'} (x : A) : term73 A x.
Proof. exact (fun h0 : term66 A x => @lem3307560 A x). Qed.
Lemma lem3307563 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307564 {A : Type'} (x : A) : (term73 A x) = (x = x).
Proof. exact (@lem3307563 (x = x)). Qed.
Lemma lem3307565 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3307564 A x) (@lem3307561 A x)). Qed.
Lemma lem3307568 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3307570 {A : Type'} (x : A) : (term66 A x) = (term74 A x).
Proof. exact (@lem3307568 (x = x)). Qed.
Lemma lem3307573 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : term74 A x.
Proof. exact (EQ_MP (@lem3307570 A x) (@lem3307400 A s x' x h1 h2)). Qed.
Lemma lem3307576 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : False.
Proof. exact (@lem3307573 A s x' x h1 h2 (@lem3307565 A x)). Qed.
Lemma lem3307577 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : term72.
Proof. exact (fun h0 : ~ False => @lem3307576 A s x' x h1 h2). Qed.
Lemma lem3307579 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307580 : term72 = False.
Proof. exact (@lem3307579 False). Qed.
Lemma lem3307597 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) : s x'.
Proof. exact (proj1 (@lem3307264 A s x' x h1)). Qed.
Lemma lem3307598 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) : term69 A s x'.
Proof. exact (fun h0 : term62 A s x' => @lem3307597 A s x' x h1). Qed.
Lemma lem3307600 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307601 {A : Type'} (s : A -> Prop) (x' : A) : (term69 A s x') = (s x').
Proof. exact (@lem3307600 (s x')). Qed.
Lemma lem3307602 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3307601 A s x') (@lem3307598 A s x' x h1)). Qed.
Lemma lem3307605 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3307607 {A : Type'} (s : A -> Prop) (x' : A) : (term62 A s x') = (term71 A s x').
Proof. exact (@lem3307605 (s x')). Qed.
Lemma lem3307610 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term71 A s x'.
Proof. exact (EQ_MP (@lem3307607 A s x') (@lem3307361 A s x' h1)). Qed.
Lemma lem3307613 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s x' x) : False.
Proof. exact (@lem3307610 A s x' h1 (@lem3307602 A s x' x h2)). Qed.
Lemma lem3307614 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s x' x) : term72.
Proof. exact (fun h0 : ~ False => @lem3307613 A s x' x h1 h2). Qed.
Lemma lem3307616 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307617 : term72 = False.
Proof. exact (@lem3307616 False). Qed.
Lemma lem3307618 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s x' x) : False.
Proof. exact (EQ_MP (@lem3307617) (@lem3307614 A s x' x h1 h2)). Qed.
Lemma lem3307634 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3307635 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3307634 A x). Qed.
Lemma lem3307636 {A : Type'} (x : A) : term73 A x.
Proof. exact (fun h0 : term66 A x => @lem3307635 A x). Qed.
Lemma lem3307638 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307639 {A : Type'} (x : A) : (term73 A x) = (x = x).
Proof. exact (@lem3307638 (x = x)). Qed.
Lemma lem3307640 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3307639 A x) (@lem3307636 A x)). Qed.
Lemma lem3307643 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3307645 {A : Type'} (x : A) : (term66 A x) = (term74 A x).
Proof. exact (@lem3307643 (x = x)). Qed.
Lemma lem3307648 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : term74 A x.
Proof. exact (EQ_MP (@lem3307645 A x) (@lem3307466 A s x' x h1 h2)). Qed.
Lemma lem3307651 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (@lem3307648 A s x' x h1 h2 (@lem3307640 A x)). Qed.
Lemma lem3307652 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : term72.
Proof. exact (fun h0 : ~ False => @lem3307651 A s x' x h1 h2). Qed.
Lemma lem3307654 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307655 : term72 = False.
Proof. exact (@lem3307654 False). Qed.
Lemma lem3307672 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3307673 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3307672 A x). Qed.
Lemma lem3307674 {A : Type'} (x : A) : term73 A x.
Proof. exact (fun h0 : term66 A x => @lem3307673 A x). Qed.
Lemma lem3307676 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307677 {A : Type'} (x : A) : (term73 A x) = (x = x).
Proof. exact (@lem3307676 (x = x)). Qed.
Lemma lem3307678 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3307677 A x) (@lem3307674 A x)). Qed.
Lemma lem3307681 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3307683 {A : Type'} (x : A) : (term66 A x) = (term74 A x).
Proof. exact (@lem3307681 (x = x)). Qed.
Lemma lem3307686 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : term74 A x.
Proof. exact (EQ_MP (@lem3307683 A x) (@lem3307506 A s x' x h1 h2)). Qed.
Lemma lem3307689 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (@lem3307686 A s x' x h1 h2 (@lem3307678 A x)). Qed.
Lemma lem3307690 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : term72.
Proof. exact (fun h0 : ~ False => @lem3307689 A s x' x h1 h2). Qed.
Lemma lem3307692 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3307693 : term72 = False.
Proof. exact (@lem3307692 False). Qed.
Lemma lem3307695 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307693) (@lem3307690 A s x' x h1 h2)). Qed.
Lemma lem3307696 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307655) (@lem3307652 A s x' x h1 h2)). Qed.
Lemma lem3307697 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307580) (@lem3307577 A s x' x h1 h2)). Qed.
Lemma lem3307698 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3307695 A s x' x h1 h2) (fun h3 : False => @lem3307373 A x' x h2)). Qed.
Lemma lem3307699 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307698 A s x' x h1 h2) (@lem3307373 A x' x h2)). Qed.
Lemma lem3307700 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3307696 A s x' x h1 h2) (fun h3 : False => @lem3307367 A x' x h2)). Qed.
Lemma lem3307701 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307700 A s x' x h1 h2) (@lem3307367 A x' x h2)). Qed.
Lemma lem3307702 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3307618 A s x' x h1 h2) (fun h3 : False => @lem3307361 A s x' h1)). Qed.
Lemma lem3307703 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s x' x) : False.
Proof. exact (EQ_MP (@lem3307702 A s x' x h1 h2) (@lem3307361 A s x' h1)). Qed.
Lemma lem3307704 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3307697 A s x' x h1 h2) (fun h3 : False => @lem3307355 A x' x h2)). Qed.
Lemma lem3307705 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307704 A s x' x h1 h2) (@lem3307355 A x' x h2)). Qed.
Lemma lem3307706 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3307543 A s x' x h1 h2) (fun h3 : False => @lem3307347 A s x' h1)). Qed.
Lemma lem3307707 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s x' x) : False.
Proof. exact (EQ_MP (@lem3307706 A s x' x h1 h2) (@lem3307347 A s x' h1)). Qed.
Lemma lem3307708 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3307699 A s x' x h1 h2) (fun h3 : False => @lem3307339 A x' x h2)). Qed.
Lemma lem3307709 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307708 A s x' x h1 h2) (@lem3307339 A x' x h2)). Qed.
Lemma lem3307710 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3307701 A s x' x h1 h2) (fun h3 : False => @lem3307327 A x' x h2)). Qed.
Lemma lem3307711 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307710 A s x' x h1 h2) (@lem3307327 A x' x h2)). Qed.
Lemma lem3307712 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3307703 A s x' x h1 h2) (fun h3 : False => @lem3307315 A s x' h1)). Qed.
Lemma lem3307713 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s x' x) : False.
Proof. exact (EQ_MP (@lem3307712 A s x' x h1 h2) (@lem3307315 A s x' h1)). Qed.
Lemma lem3307714 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3307705 A s x' x h1 h2) (fun h3 : False => @lem3307303 A x' x h2)). Qed.
Lemma lem3307715 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307714 A s x' x h1 h2) (@lem3307303 A x' x h2)). Qed.
Lemma lem3307716 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3307707 A s x' x h1 h2) (fun h3 : False => @lem3307287 A s x' h1)). Qed.
Lemma lem3307717 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s x' x) : False.
Proof. exact (EQ_MP (@lem3307716 A s x' x h1 h2) (@lem3307287 A s x' h1)). Qed.
Lemma lem3307718 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3307709 A s x' x h1 h2) (fun h3 : False => @lem3307339 A x' x h2)). Qed.
Lemma lem3307719 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307718 A s x' x h1 h2) (@lem3307339 A x' x h2)). Qed.
Lemma lem3307720 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3307711 A s x' x h1 h2) (fun h3 : False => @lem3307327 A x' x h2)). Qed.
Lemma lem3307721 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307720 A s x' x h1 h2) (@lem3307327 A x' x h2)). Qed.
Lemma lem3307722 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3307713 A s x' x h1 h2) (fun h3 : False => @lem3307315 A s x' h1)). Qed.
Lemma lem3307723 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s x' x) : False.
Proof. exact (EQ_MP (@lem3307722 A s x' x h1 h2) (@lem3307315 A s x' h1)). Qed.
Lemma lem3307724 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3307715 A s x' x h1 h2) (fun h3 : False => @lem3307303 A x' x h2)). Qed.
Lemma lem3307725 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3307724 A s x' x h1 h2) (@lem3307303 A x' x h2)). Qed.
Lemma lem3307726 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3307717 A s x' x h1 h2) (fun h3 : False => @lem3307287 A s x' h1)). Qed.
Lemma lem3307727 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s x' x) : False.
Proof. exact (EQ_MP (@lem3307726 A s x' x h1 h2) (@lem3307287 A s x' h1)). Qed.
Lemma lem3307728 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) (h2 : term44 A s x' x) : False.
Proof. exact (or_elim (@lem3307268 A s x' x h2) (fun h0 : term62 A s x' => @lem3307723 A s x' x h0 h1) (fun h0 : x' = x => @lem3307721 A s x' x h1 h0)). Qed.
Lemma lem3307729 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s x' x) : False.
Proof. exact (or_elim (@lem3307265 A s x' x h1) (fun h0 : term44 A s x' x => @lem3307728 A s x' x h1 h0) (fun h0 : x' = x => @lem3307719 A s x' x h1 h0)). Qed.
Lemma lem3307730 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term57 A s x' x) : False.
Proof. exact (or_elim (@lem3307256 A s x' x h1) (fun h0 : term62 A s x' => @lem3307727 A s x' x h0 h1) (fun h0 : x' = x => @lem3307725 A s x' x h1 h0)). Qed.
Lemma lem3307731 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term40 A s x' x) : False.
Proof. exact (or_elim (@lem3307253 A s x' x h1) (fun h0 : term57 A s x' x => @lem3307730 A s x' x h0) (fun h0 : term54 A s x' x => @lem3307729 A s x' x h0)). Qed.
Lemma lem3307732 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term40 A s x' x) : (term40 A s x' x) = False.
Proof. exact (prop_ext (fun h2 : term40 A s x' x => @lem3307731 A s x' x h1) (fun h2 : False => @lem3307117 A s x' x h1)). Qed.
Lemma lem3307733 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term40 A s x' x) : False.
Proof. exact (EQ_MP (@lem3307732 A s x' x h1) (@lem3307117 A s x' x h1)). Qed.
Lemma lem3307734 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : term39 A s x' x.
Proof. exact (fun h0 : term40 A s x' x => @lem3307733 A s x' x h0). Qed.
Lemma lem3307735 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term21 A s x' x) = (term18 A s x' x).
Proof. exact (EQ_MP (@lem3307116 A s x' x) (@lem3307734 A s x' x)). Qed.
Lemma lem3307740 {A : Type'} (s : A -> Prop) (x : A) : term26 A s x.
Proof. exact (fun x' : A => @lem3307735 A s x' x). Qed.
Lemma lem3307745 {A : Type'} (x : A) : term28 A x.
Proof. exact (fun s : A -> Prop => @lem3307740 A s x). Qed.
Lemma lem3307750 {A : Type'} : term30 A.
Proof. exact (fun x : A => @lem3307745 A x). Qed.
Lemma lem3307751 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem3307112 A) (@lem3307750 A)). Qed.
Lemma lem3307753 {A : Type'} : term32 A.
Proof. exact (@lem3307023 A (@lem3307751 A)). Qed.
Lemma lem3307754 {A : Type'} (h1 : term33 A) : False.
Proof. exact (@lem3307753 A (@lem3307007 A h1)). Qed.
Lemma lem3307755 {A : Type'} (h1 : term33 A) : (term33 A) = False.
Proof. exact (prop_ext (fun h2 : term33 A => @lem3307754 A h1) (fun h2 : False => @lem3307007 A h1)). Qed.
Lemma lem3307756 {A : Type'} (h1 : term33 A) : False.
Proof. exact (EQ_MP (@lem3307755 A h1) (@lem3307007 A h1)). Qed.
Lemma lem3307757 {A : Type'} : term32 A.
Proof. exact (fun h0 : term33 A => @lem3307756 A h0). Qed.
Lemma lem3307758 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem3307006 A) (@lem3307757 A)). Qed.
Lemma lem3307759 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3307002 A) (@lem3307758 A)). Qed.
Lemma lem3307760 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3306908 A) (@lem3307759 A)). Qed.
