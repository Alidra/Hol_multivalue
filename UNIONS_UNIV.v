Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_UNIV_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_SING_spec.
Require Import IN_UNIONS_spec.
Require Import IN_UNIV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem3349940 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem3349941 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3349942 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem3349941 A x) (@lem3349940 A x)). Qed.
Lemma lem3349943 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem3349945 {A : Type'} (s : type686 A) : term1 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3349946 {A : Type'} (s : type686 A) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3349947 {A : Type'} (s : type686 A) : term2 A s.
Proof. exact (EQ_MP (@lem3349946 A s) (@lem3349945 A s)). Qed.
Lemma lem3349948 {A : Type'} (s : type686 A) (x : A) : term3 A s x.
Proof. exact (@lem3349947 A s x). Qed.
Lemma lem3349949 {A : Type'} (s : type686 A) (x : A) : (term3 A s x) = ((term4 A x s) = (term5 A s x)).
Proof. exact (eq_refl (term3 A s x)). Qed.
Lemma lem3349951 {A : Type'} (s : A -> Prop) : term6 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3349952 {A : Type'} (s : A -> Prop) : (term6 A s) = (term7 A s).
Proof. exact (eq_refl (term6 A s)). Qed.
Lemma lem3349953 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (EQ_MP (@lem3349952 A s) (@lem3349951 A s)). Qed.
Lemma lem3349954 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term8 A s t.
Proof. exact (@lem3349953 A s t). Qed.
Lemma lem3349955 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term8 A s t) = ((s = t) = (term9 A s t)).
Proof. exact (eq_refl (term8 A s t)). Qed.
Lemma lem3349960 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (EQ_MP (@lem3349955 A s t) (@lem3349954 A s t)). Qed.
Lemma lem3349961 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (@lem3349960 A s t). Qed.
Lemma lem3349962 {A : Type'} : ((@UNIONS A (@UNIV (A -> Prop))) = (@UNIV A)) = (term10 A).
Proof. exact (@lem3349961 A (@UNIONS A (@UNIV (A -> Prop))) (@UNIV A)). Qed.
Lemma lem3349972 {A : Type'} (s : type686 A) (x : A) : (term4 A x s) = (term5 A s x).
Proof. exact (EQ_MP (@lem3349949 A s x) (@lem3349948 A s x)). Qed.
Lemma lem3349973 {A : Type'} (s : type686 A) (x : A) : (term4 A x s) = (term5 A s x).
Proof. exact (@lem3349972 A s x). Qed.
Lemma lem3349974 {A : Type'} (x : A) : (term11 A x) = (term12 A x).
Proof. exact (@lem3349973 A (@UNIV (A -> Prop)) x). Qed.
Lemma lem3349982 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3349943 A x) (@lem3349942 A x)). Qed.
Lemma lem3349983 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@UNIV (A -> Prop))) = True.
Proof. exact (@lem3349982 (A -> Prop) x). Qed.
Lemma lem3349984 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t (@UNIV (A -> Prop))) = True.
Proof. exact (@lem3349983 A t). Qed.
Lemma lem3349985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3349986 {A : Type'} (t : A -> Prop) : (term13 A t) = (and True).
Proof. exact (MK_COMB (@lem3349985) (@lem3349984 A t)). Qed.
Lemma lem3349987 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@IN A x t).
Proof. exact (eq_refl (@IN A x t)). Qed.
Lemma lem3349988 {A : Type'} (x : A) (t : A -> Prop) : (term14 A x t) = (term15 A x t).
Proof. exact (MK_COMB (@lem3349986 A t) (@lem3349987 A x t)). Qed.
Lemma lem3349990 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3349991 {A : Type'} (x : A) (t : A -> Prop) : (term15 A x t) = (@IN A x t).
Proof. exact (@lem3349990 (@IN A x t)). Qed.
Lemma lem3349992 {A : Type'} (x : A) (t : A -> Prop) : (term14 A x t) = (@IN A x t).
Proof. exact (TRANS (@lem3349988 A x t) (@lem3349991 A x t)). Qed.
Lemma lem3349993 {A : Type'} (x : A) : (term16 A x) = (term17 A x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3349992 A x t)). Qed.
Lemma lem3349994 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3349995 {A : Type'} (x : A) : (term12 A x) = (term18 A x).
Proof. exact (MK_COMB (@lem3349994 A) (@lem3349993 A x)). Qed.
Lemma lem3350000 {A : Type'} (x : A) : (term11 A x) = (term18 A x).
Proof. exact (TRANS (@lem3349974 A x) (@lem3349995 A x)). Qed.
Lemma lem3350001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3350002 {A : Type'} (x : A) : (term19 A x) = (term20 A x).
Proof. exact (MK_COMB (@lem3350001) (@lem3350000 A x)). Qed.
Lemma lem3350004 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3349943 A x) (@lem3349942 A x)). Qed.
Lemma lem3350005 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3350004 A x). Qed.
Lemma lem3350006 {A : Type'} (x : A) : ((term11 A x) = (@IN A x (@UNIV A))) = ((term18 A x) = True).
Proof. exact (MK_COMB (@lem3350002 A x) (@lem3350005 A x)). Qed.
Lemma lem3350008 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem3350009 {A : Type'} (x : A) : ((term18 A x) = True) = (term18 A x).
Proof. exact (@lem3350008 (term18 A x)). Qed.
Lemma lem3350014 {A : Type'} (x : A) : ((term11 A x) = (@IN A x (@UNIV A))) = (term18 A x).
Proof. exact (TRANS (@lem3350006 A x) (@lem3350009 A x)). Qed.
Lemma lem3350015 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (fun_ext (fun x : A => @lem3350014 A x)). Qed.
Lemma lem3350016 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350017 {A : Type'} : (term10 A) = (term23 A).
Proof. exact (MK_COMB (@lem3350016 A) (@lem3350015 A)). Qed.
Lemma lem3350022 {A : Type'} : ((@UNIONS A (@UNIV (A -> Prop))) = (@UNIV A)) = (term23 A).
Proof. exact (TRANS (@lem3349962 A) (@lem3350017 A)). Qed.
Lemma lem3350023 {A : Type'} : (term23 A) = ((@UNIONS A (@UNIV (A -> Prop))) = (@UNIV A)).
Proof. exact (SYM (@lem3350022 A)). Qed.
Lemma lem3350025 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3350026 {A : Type'} : (term23 A) = (term25 A).
Proof. exact (@lem3350025 (term23 A)). Qed.
Lemma lem3350027 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (SYM (@lem3350026 A)). Qed.
Lemma lem3350028 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3350029 {A : Type'} : term27 A.
Proof. exact (@lem3205876 A). Qed.
Lemma lem3350032 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3350033 {A : Type'} : term29 A.
Proof. exact (fun h0 : term28 A => @lem3350032 A h0). Qed.
Lemma lem3350034 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3350035 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3350036 {A : Type'} (h1 : term28 A) (h2 : term29 A) : term28 A.
Proof. exact (@lem3350034 A h2 (@lem3350035 A h1)). Qed.
Lemma lem3350037 {A : Type'} (h1 : term28 A) : term30 A.
Proof. exact (fun h0 : term29 A => @lem3350036 A h1 h0). Qed.
Lemma lem3350038 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3350039 {A : Type'} (h1 : term28 A) (h2 : term29 A) : term28 A.
Proof. exact (@lem3350037 A h1 (@lem3350038 A h2)). Qed.
Lemma lem3350040 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (fun h0 : term28 A => @lem3350039 A h0 h1). Qed.
Lemma lem3350041 {A : Type'} : term31 A.
Proof. exact (fun h0 : term29 A => @lem3350040 A h0). Qed.
Lemma lem3350044 {A : Type'} : term29 A.
Proof. exact (@lem3350041 A (@lem3350033 A)). Qed.
Lemma lem3350045 {A : Type'} : term29 A.
Proof. exact (@lem3350044 A). Qed.
Lemma lem3350057 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3350058 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (@lem3350057 (term27 A)). Qed.
Lemma lem3350067 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (eq_refl (term34 A)). Qed.
Lemma lem3350074 {A : Type'} : (term28 A) = (term35 A).
Proof. exact (MK_COMB (@lem3350067 A) (@lem3350058 A)). Qed.
Lemma lem3350079 {A : Type'} (x : A) (y : A) : ((term36 A x y) = (x = y)) = ((term36 A x y) = (x = y)).
Proof. exact (eq_refl ((term36 A x y) = (x = y))). Qed.
Lemma lem3350080 {A : Type'} (x : A) : (term37 A x) = (term37 A x).
Proof. exact (fun_ext (fun y : A => @lem3350079 A x y)). Qed.
Lemma lem3350081 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350082 {A : Type'} (x : A) : (term38 A x) = (term38 A x).
Proof. exact (MK_COMB (@lem3350081 A) (@lem3350080 A x)). Qed.
Lemma lem3350083 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun x : A => @lem3350082 A x)). Qed.
Lemma lem3350084 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350085 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem3350084 A) (@lem3350083 A)). Qed.
Lemma lem3350086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3350087 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem3350086) (@lem3350085 A)). Qed.
Lemma lem3350088 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@IN A x t).
Proof. exact (eq_refl (@IN A x t)). Qed.
Lemma lem3350089 {A : Type'} (x : A) : (term17 A x) = (term17 A x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3350088 A x t)). Qed.
Lemma lem3350090 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3350091 {A : Type'} (x : A) : (term18 A x) = (term18 A x).
Proof. exact (MK_COMB (@lem3350090 A) (@lem3350089 A x)). Qed.
Lemma lem3350092 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (fun_ext (fun x : A => @lem3350091 A x)). Qed.
Lemma lem3350093 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350094 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem3350093 A) (@lem3350092 A)). Qed.
Lemma lem3350095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3350096 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem3350095) (@lem3350094 A)). Qed.
Lemma lem3350097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3350098 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem3350097) (@lem3350096 A)). Qed.
Lemma lem3350099 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (MK_COMB (@lem3350098 A) (@lem3350087 A)). Qed.
Lemma lem3350128 {A : Type'} : (term28 A) = (term35 A).
Proof. exact (TRANS (@lem3350074 A) (@lem3350099 A)). Qed.
Lemma lem3350129 {A : Type'} : (term35 A) = (term28 A).
Proof. exact (SYM (@lem3350128 A)). Qed.
Lemma lem3350130 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3350131 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3350133 {A : Type'} (P : type686 A) : (term40 A P) = (term41 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3350134 {A : Type'} (x : A) : (term42 A x) = (term43 A x).
Proof. exact (@lem3350133 A (term17 A x)). Qed.
Lemma lem3350135 {A : Type'} (x : A) (t : A -> Prop) : (term44 A x t) = (@IN A x t).
Proof. exact (eq_refl (term44 A x t)). Qed.
Lemma lem3350136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3350138 {A : Type'} (x : A) (t : A -> Prop) : (term45 A x t) = (term46 A x t).
Proof. exact (MK_COMB (@lem3350136) (@lem3350135 A x t)). Qed.
Lemma lem3350139 {A : Type'} (x : A) : (term47 A x) = (term48 A x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3350138 A x t)). Qed.
Lemma lem3350140 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3350141 {A : Type'} (x : A) : (term43 A x) = (term49 A x).
Proof. exact (MK_COMB (@lem3350140 A) (@lem3350139 A x)). Qed.
Lemma lem3350142 {A : Type'} (x : A) : (term42 A x) = (term49 A x).
Proof. exact (TRANS (@lem3350134 A x) (@lem3350141 A x)). Qed.
Lemma lem3350143 {A : Type'} (P : A -> Prop) : (term50 A P) = (term51 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3350144 {A : Type'} : (term26 A) = (term52 A).
Proof. exact (@lem3350143 A (term22 A)). Qed.
Lemma lem3350145 {A : Type'} (x : A) : (term53 A x) = (term18 A x).
Proof. exact (eq_refl (term53 A x)). Qed.
Lemma lem3350146 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3350147 {A : Type'} (x : A) : (term54 A x) = (term42 A x).
Proof. exact (MK_COMB (@lem3350146) (@lem3350145 A x)). Qed.
Lemma lem3350148 {A : Type'} (x : A) : (term54 A x) = (term49 A x).
Proof. exact (TRANS (@lem3350147 A x) (@lem3350142 A x)). Qed.
Lemma lem3350149 {A : Type'} : (term55 A) = (term56 A).
Proof. exact (fun_ext (fun x : A => @lem3350148 A x)). Qed.
Lemma lem3350150 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3350151 {A : Type'} : (term52 A) = (term57 A).
Proof. exact (MK_COMB (@lem3350150 A) (@lem3350149 A)). Qed.
Lemma lem3350164 {A : Type'} : (term26 A) = (term57 A).
Proof. exact (TRANS (@lem3350144 A) (@lem3350151 A)). Qed.
Lemma lem3350165 {A : Type'} (h1 : term26 A) : term57 A.
Proof. exact (EQ_MP (@lem3350164 A) (@lem3350130 A h1)). Qed.
Lemma lem3350180 {A : Type'} (x : A) (y : A) : ((term36 A x y) = (x = y)) = (term58 A x y).
Proof. exact (@lem17784 (term36 A x y) (x = y)). Qed.
Lemma lem3350181 {A : Type'} (x : A) : (term37 A x) = (term59 A x).
Proof. exact (fun_ext (fun y : A => @lem3350180 A x y)). Qed.
Lemma lem3350182 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350183 {A : Type'} (x : A) : (term38 A x) = (term60 A x).
Proof. exact (MK_COMB (@lem3350182 A) (@lem3350181 A x)). Qed.
Lemma lem3350184 {A : Type'} : (term39 A) = (term61 A).
Proof. exact (fun_ext (fun x : A => @lem3350183 A x)). Qed.
Lemma lem3350185 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350186 {A : Type'} : (term27 A) = (term62 A).
Proof. exact (MK_COMB (@lem3350185 A) (@lem3350184 A)). Qed.
Lemma lem3350192 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3350193 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (@lem3350192 A P Q). Qed.
Lemma lem3350194 {A : Type'} (x : A) : (term65 A x) = (term66 A x).
Proof. exact (@lem3350193 A (term67 A x) (term68 A x)). Qed.
Lemma lem3350195 {A : Type'} (x : A) (y : A) : (term69 A x y) = (term70 A x y).
Proof. exact (eq_refl (term69 A x y)). Qed.
Lemma lem3350196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3350197 {A : Type'} (x : A) (y : A) : (term71 A x y) = (term72 A x y).
Proof. exact (MK_COMB (@lem3350196) (@lem3350195 A x y)). Qed.
Lemma lem3350198 {A : Type'} (x : A) (y : A) : (term73 A x y) = (term74 A x y).
Proof. exact (eq_refl (term73 A x y)). Qed.
Lemma lem3350199 {A : Type'} (x : A) (y : A) : (term75 A x y) = (term58 A x y).
Proof. exact (MK_COMB (@lem3350197 A x y) (@lem3350198 A x y)). Qed.
Lemma lem3350200 {A : Type'} (x : A) : (term76 A x) = (term59 A x).
Proof. exact (fun_ext (fun y : A => @lem3350199 A x y)). Qed.
Lemma lem3350201 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350202 {A : Type'} (x : A) : (term65 A x) = (term60 A x).
Proof. exact (MK_COMB (@lem3350201 A) (@lem3350200 A x)). Qed.
Lemma lem3350203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3350204 {A : Type'} (x : A) : (term77 A x) = (term78 A x).
Proof. exact (MK_COMB (@lem3350203) (@lem3350202 A x)). Qed.
Lemma lem3350205 {A : Type'} (x : A) (y : A) : (term69 A x y) = (term70 A x y).
Proof. exact (eq_refl (term69 A x y)). Qed.
Lemma lem3350206 {A : Type'} (x : A) : (term79 A x) = (term67 A x).
Proof. exact (fun_ext (fun y : A => @lem3350205 A x y)). Qed.
Lemma lem3350207 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350208 {A : Type'} (x : A) : (term80 A x) = (term81 A x).
Proof. exact (MK_COMB (@lem3350207 A) (@lem3350206 A x)). Qed.
Lemma lem3350209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3350210 {A : Type'} (x : A) : (term82 A x) = (term83 A x).
Proof. exact (MK_COMB (@lem3350209) (@lem3350208 A x)). Qed.
Lemma lem3350211 {A : Type'} (x : A) (y : A) : (term73 A x y) = (term74 A x y).
Proof. exact (eq_refl (term73 A x y)). Qed.
Lemma lem3350212 {A : Type'} (x : A) : (term84 A x) = (term68 A x).
Proof. exact (fun_ext (fun y : A => @lem3350211 A x y)). Qed.
Lemma lem3350213 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350214 {A : Type'} (x : A) : (term85 A x) = (term86 A x).
Proof. exact (MK_COMB (@lem3350213 A) (@lem3350212 A x)). Qed.
Lemma lem3350215 {A : Type'} (x : A) : (term66 A x) = (term87 A x).
Proof. exact (MK_COMB (@lem3350210 A x) (@lem3350214 A x)). Qed.
Lemma lem3350216 {A : Type'} (x : A) : ((term65 A x) = (term66 A x)) = ((term60 A x) = (term87 A x)).
Proof. exact (MK_COMB (@lem3350204 A x) (@lem3350215 A x)). Qed.
Lemma lem3350217 {A : Type'} (x : A) : (term60 A x) = (term87 A x).
Proof. exact (EQ_MP (@lem3350216 A x) (@lem3350194 A x)). Qed.
Lemma lem3350314 {A : Type'} : (term61 A) = (term88 A).
Proof. exact (fun_ext (fun x : A => @lem3350217 A x)). Qed.
Lemma lem3350315 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350316 {A : Type'} : (term62 A) = (term89 A).
Proof. exact (MK_COMB (@lem3350315 A) (@lem3350314 A)). Qed.
Lemma lem3350318 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3350319 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (@lem3350318 A P Q). Qed.
Lemma lem3350320 {A : Type'} : (term90 A) = (term91 A).
Proof. exact (@lem3350319 A (term92 A) (term93 A)). Qed.
Lemma lem3350321 {A : Type'} (x : A) : (term94 A x) = (term81 A x).
Proof. exact (eq_refl (term94 A x)). Qed.
Lemma lem3350322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3350323 {A : Type'} (x : A) : (term95 A x) = (term83 A x).
Proof. exact (MK_COMB (@lem3350322) (@lem3350321 A x)). Qed.
Lemma lem3350324 {A : Type'} (x : A) : (term96 A x) = (term86 A x).
Proof. exact (eq_refl (term96 A x)). Qed.
Lemma lem3350325 {A : Type'} (x : A) : (term97 A x) = (term87 A x).
Proof. exact (MK_COMB (@lem3350323 A x) (@lem3350324 A x)). Qed.
Lemma lem3350326 {A : Type'} : (term98 A) = (term88 A).
Proof. exact (fun_ext (fun x : A => @lem3350325 A x)). Qed.
Lemma lem3350327 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350328 {A : Type'} : (term90 A) = (term89 A).
Proof. exact (MK_COMB (@lem3350327 A) (@lem3350326 A)). Qed.
Lemma lem3350329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3350330 {A : Type'} : (term99 A) = (term100 A).
Proof. exact (MK_COMB (@lem3350329) (@lem3350328 A)). Qed.
Lemma lem3350331 {A : Type'} (x : A) : (term94 A x) = (term81 A x).
Proof. exact (eq_refl (term94 A x)). Qed.
Lemma lem3350332 {A : Type'} : (term101 A) = (term92 A).
Proof. exact (fun_ext (fun x : A => @lem3350331 A x)). Qed.
Lemma lem3350333 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350334 {A : Type'} : (term102 A) = (term103 A).
Proof. exact (MK_COMB (@lem3350333 A) (@lem3350332 A)). Qed.
Lemma lem3350335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3350336 {A : Type'} : (term104 A) = (term105 A).
Proof. exact (MK_COMB (@lem3350335) (@lem3350334 A)). Qed.
Lemma lem3350337 {A : Type'} (x : A) : (term96 A x) = (term86 A x).
Proof. exact (eq_refl (term96 A x)). Qed.
Lemma lem3350338 {A : Type'} : (term106 A) = (term93 A).
Proof. exact (fun_ext (fun x : A => @lem3350337 A x)). Qed.
Lemma lem3350339 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350340 {A : Type'} : (term107 A) = (term108 A).
Proof. exact (MK_COMB (@lem3350339 A) (@lem3350338 A)). Qed.
Lemma lem3350341 {A : Type'} : (term91 A) = (term109 A).
Proof. exact (MK_COMB (@lem3350336 A) (@lem3350340 A)). Qed.
Lemma lem3350342 {A : Type'} : ((term90 A) = (term91 A)) = ((term89 A) = (term109 A)).
Proof. exact (MK_COMB (@lem3350330 A) (@lem3350341 A)). Qed.
Lemma lem3350343 {A : Type'} : (term89 A) = (term109 A).
Proof. exact (EQ_MP (@lem3350342 A) (@lem3350320 A)). Qed.
Lemma lem3350450 {A : Type'} : (term62 A) = (term109 A).
Proof. exact (TRANS (@lem3350316 A) (@lem3350343 A)). Qed.
Lemma lem3350451 {A : Type'} : (term27 A) = (term109 A).
Proof. exact (TRANS (@lem3350186 A) (@lem3350450 A)). Qed.
Lemma lem3350452 {A : Type'} (h1 : term27 A) : term109 A.
Proof. exact (EQ_MP (@lem3350451 A) (@lem3350131 A h1)). Qed.
Lemma lem3350453 {A : Type'} (x : A) (h1 : term49 A x) : term49 A x.
Proof. exact (h1). Qed.
Lemma lem3350472 {A : Type'} (x : A) (y : A) : (term74 A x y) = (term74 A x y).
Proof. exact (eq_refl (term74 A x y)). Qed.
Lemma lem3350473 {A : Type'} (x : A) : (term68 A x) = (term68 A x).
Proof. exact (fun_ext (fun y : A => @lem3350472 A x y)). Qed.
Lemma lem3350474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350475 {A : Type'} (x : A) : (term86 A x) = (term86 A x).
Proof. exact (MK_COMB (@lem3350474 A) (@lem3350473 A x)). Qed.
Lemma lem3350476 {A : Type'} : (term93 A) = (term93 A).
Proof. exact (fun_ext (fun x : A => @lem3350475 A x)). Qed.
Lemma lem3350477 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350478 {A : Type'} : (term108 A) = (term108 A).
Proof. exact (MK_COMB (@lem3350477 A) (@lem3350476 A)). Qed.
Lemma lem3350497 {A : Type'} (x : A) (y : A) : (term70 A x y) = (term70 A x y).
Proof. exact (eq_refl (term70 A x y)). Qed.
Lemma lem3350498 {A : Type'} (x : A) : (term67 A x) = (term67 A x).
Proof. exact (fun_ext (fun y : A => @lem3350497 A x y)). Qed.
Lemma lem3350499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350500 {A : Type'} (x : A) : (term81 A x) = (term81 A x).
Proof. exact (MK_COMB (@lem3350499 A) (@lem3350498 A x)). Qed.
Lemma lem3350501 {A : Type'} : (term92 A) = (term92 A).
Proof. exact (fun_ext (fun x : A => @lem3350500 A x)). Qed.
Lemma lem3350502 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350503 {A : Type'} : (term103 A) = (term103 A).
Proof. exact (MK_COMB (@lem3350502 A) (@lem3350501 A)). Qed.
Lemma lem3350504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3350505 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (MK_COMB (@lem3350504) (@lem3350503 A)). Qed.
Lemma lem3350506 {A : Type'} : (term109 A) = (term109 A).
Proof. exact (MK_COMB (@lem3350505 A) (@lem3350478 A)). Qed.
Lemma lem3350507 {A : Type'} (h1 : term27 A) : term109 A.
Proof. exact (EQ_MP (@lem3350506 A) (@lem3350452 A h1)). Qed.
Lemma lem3350514 {A : Type'} (x : A) (t : A -> Prop) : (term46 A x t) = (term46 A x t).
Proof. exact (eq_refl (term46 A x t)). Qed.
Lemma lem3350515 {A : Type'} (x : A) : (term48 A x) = (term48 A x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3350514 A x t)). Qed.
Lemma lem3350516 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3350517 {A : Type'} (x : A) : (term49 A x) = (term49 A x).
Proof. exact (MK_COMB (@lem3350516 A) (@lem3350515 A x)). Qed.
Lemma lem3350518 {A : Type'} (x : A) (h1 : term49 A x) : term49 A x.
Proof. exact (EQ_MP (@lem3350517 A x) (@lem3350453 A x h1)). Qed.
Lemma lem3350520 {A : Type'} (h1 : term27 A) : term103 A.
Proof. exact (proj1 (@lem3350507 A h1)). Qed.
Lemma lem3350522 {A : Type'} (x : A) (t : A -> Prop) : (term46 A x t) = (term46 A x t).
Proof. exact (eq_refl (term46 A x t)). Qed.
Lemma lem3350523 {A : Type'} (x : A) : (term48 A x) = (term48 A x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3350522 A x t)). Qed.
Lemma lem3350524 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3350526 {A : Type'} (x : A) : (term49 A x) = (term49 A x).
Proof. exact (MK_COMB (@lem3350524 A) (@lem3350523 A x)). Qed.
Lemma lem3350527 {A : Type'} (x : A) (h1 : term49 A x) : term49 A x.
Proof. exact (EQ_MP (@lem3350526 A x) (@lem3350518 A x h1)). Qed.
Lemma lem3350535 {A : Type'} (x : A) (y : A) : (term70 A x y) = (term70 A x y).
Proof. exact (eq_refl (term70 A x y)). Qed.
Lemma lem3350536 {A : Type'} (x : A) : (term67 A x) = (term67 A x).
Proof. exact (fun_ext (fun y : A => @lem3350535 A x y)). Qed.
Lemma lem3350537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350538 {A : Type'} (x : A) : (term81 A x) = (term81 A x).
Proof. exact (MK_COMB (@lem3350537 A) (@lem3350536 A x)). Qed.
Lemma lem3350539 {A : Type'} : (term92 A) = (term92 A).
Proof. exact (fun_ext (fun x : A => @lem3350538 A x)). Qed.
Lemma lem3350540 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3350542 {A : Type'} : (term103 A) = (term103 A).
Proof. exact (MK_COMB (@lem3350540 A) (@lem3350539 A)). Qed.
Lemma lem3350543 {A : Type'} (h1 : term27 A) : term103 A.
Proof. exact (EQ_MP (@lem3350542 A) (@lem3350520 A h1)). Qed.
Lemma lem3350560 {A : Type'} (_34934 : A -> Prop) (x : A) (h1 : term49 A x) : term110 A x _34934.
Proof. exact (@lem3350527 A x h1 _34934). Qed.
Lemma lem3350561 {A : Type'} (x : A) (_34934 : A -> Prop) : (term110 A x _34934) = (term46 A x _34934).
Proof. exact (eq_refl (term110 A x _34934)). Qed.
Lemma lem3350563 {A : Type'} (_34935 : A) (h1 : term27 A) : term94 A _34935.
Proof. exact (@lem3350543 A h1 _34935). Qed.
Lemma lem3350564 {A : Type'} (_34935 : A) : (term94 A _34935) = (term81 A _34935).
Proof. exact (eq_refl (term94 A _34935)). Qed.
Lemma lem3350565 {A : Type'} (_34935 : A) (h1 : term27 A) : term81 A _34935.
Proof. exact (EQ_MP (@lem3350564 A _34935) (@lem3350563 A _34935 h1)). Qed.
Lemma lem3350566 {A : Type'} (_34935 : A) (_34936 : A) (h1 : term27 A) : term69 A _34935 _34936.
Proof. exact (@lem3350565 A _34935 h1 _34936). Qed.
Lemma lem3350567 {A : Type'} (_34935 : A) (_34936 : A) : (term69 A _34935 _34936) = (term70 A _34935 _34936).
Proof. exact (eq_refl (term69 A _34935 _34936)). Qed.
Lemma lem3350576 {A : Type'} (_34934 : A -> Prop) (x : A) (h1 : term49 A x) : term46 A x _34934.
Proof. exact (EQ_MP (@lem3350561 A x _34934) (@lem3350560 A _34934 x h1)). Qed.
Lemma lem3350582 {A : Type'} (_34935 : A) (_34936 : A) (h1 : term27 A) : term70 A _34935 _34936.
Proof. exact (EQ_MP (@lem3350567 A _34935 _34936) (@lem3350566 A _34935 _34936 h1)). Qed.
Lemma lem3350628 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3350629 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3350628 A x). Qed.
Lemma lem3350630 {A : Type'} (x : A) : term111 A x.
Proof. exact (fun h0 : term112 A x => @lem3350629 A x). Qed.
Lemma lem3350632 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3350633 {A : Type'} (x : A) : (term111 A x) = (x = x).
Proof. exact (@lem3350632 (x = x)). Qed.
Lemma lem3350634 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3350633 A x) (@lem3350630 A x)). Qed.
Lemma lem3350636 (b : Prop) (a : Prop) : (a \/ b) = (term114 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3350637 {A : Type'} (_34935 : A) (_34936 : A) : (term70 A _34935 _34936) = (term115 A _34935 _34936).
Proof. exact (@lem3350636 (term116 A _34935 _34936) (term36 A _34935 _34936)). Qed.
Lemma lem3350639 (a : Prop) : (term117 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3350640 {A : Type'} (_34935 : A) (_34936 : A) : (term118 A _34935 _34936) = (_34935 = _34936).
Proof. exact (@lem3350639 (_34935 = _34936)). Qed.
Lemma lem3350641 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3350642 {A : Type'} (_34935 : A) (_34936 : A) : (term119 A _34935 _34936) = (term120 A _34935 _34936).
Proof. exact (MK_COMB (@lem3350641) (@lem3350640 A _34935 _34936)). Qed.
Lemma lem3350643 {A : Type'} (_34935 : A) (_34936 : A) : (term36 A _34935 _34936) = (term36 A _34935 _34936).
Proof. exact (eq_refl (term36 A _34935 _34936)). Qed.
Lemma lem3350644 {A : Type'} (_34935 : A) (_34936 : A) : (term115 A _34935 _34936) = (term121 A _34935 _34936).
Proof. exact (MK_COMB (@lem3350642 A _34935 _34936) (@lem3350643 A _34935 _34936)). Qed.
Lemma lem3350645 {A : Type'} (_34935 : A) (_34936 : A) : (term70 A _34935 _34936) = (term121 A _34935 _34936).
Proof. exact (TRANS (@lem3350637 A _34935 _34936) (@lem3350644 A _34935 _34936)). Qed.
Lemma lem3350648 {A : Type'} (_34935 : A) (_34936 : A) (h1 : term27 A) : term121 A _34935 _34936.
Proof. exact (EQ_MP (@lem3350645 A _34935 _34936) (@lem3350582 A _34935 _34936 h1)). Qed.
Lemma lem3350649 {A : Type'} (_34935 : A) (_34936 : A) (h1 : term27 A) : term121 A _34935 _34936.
Proof. exact (@lem3350648 A _34935 _34936 h1). Qed.
Lemma lem3350650 {A : Type'} (x : A) (h1 : term27 A) : term122 A x.
Proof. exact (@lem3350649 A x x h1). Qed.
Lemma lem3350653 {A : Type'} (x : A) (h1 : term27 A) : term123 A x.
Proof. exact (@lem3350650 A x h1 (@lem3350634 A x)). Qed.
Lemma lem3350654 {A : Type'} (x : A) (h1 : term27 A) : term123 A x.
Proof. exact (@lem3350653 A x h1). Qed.
Lemma lem3350655 {A : Type'} (x : A) (h1 : term27 A) : term124 A x.
Proof. exact (fun h0 : term125 A x => @lem3350654 A x h1). Qed.
Lemma lem3350657 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3350658 {A : Type'} (x : A) : (term124 A x) = (term123 A x).
Proof. exact (@lem3350657 (term123 A x)). Qed.
Lemma lem3350659 {A : Type'} (x : A) (h1 : term27 A) : term123 A x.
Proof. exact (EQ_MP (@lem3350658 A x) (@lem3350655 A x h1)). Qed.
Lemma lem3350662 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3350664 {A : Type'} (x : A) (_34934 : A -> Prop) : (term46 A x _34934) = (term126 A x _34934).
Proof. exact (@lem3350662 (@IN A x _34934)). Qed.
Lemma lem3350667 {A : Type'} (_34934 : A -> Prop) (x : A) (h1 : term49 A x) : term126 A x _34934.
Proof. exact (EQ_MP (@lem3350664 A x _34934) (@lem3350576 A _34934 x h1)). Qed.
Lemma lem3350668 {A : Type'} (_34934 : A -> Prop) (x : A) (h1 : term49 A x) : term126 A x _34934.
Proof. exact (@lem3350667 A _34934 x h1). Qed.
Lemma lem3350669 {A : Type'} (x : A) (h1 : term49 A x) : term127 A x.
Proof. exact (@lem3350668 A (@INSERT A x (@EMPTY A)) x h1). Qed.
Lemma lem3350672 {A : Type'} (x : A) (h1 : term27 A) (h2 : term49 A x) : False.
Proof. exact (@lem3350669 A x h2 (@lem3350659 A x h1)). Qed.
Lemma lem3350673 {A : Type'} (x : A) (h1 : term27 A) (h2 : term49 A x) : term128.
Proof. exact (fun h0 : ~ False => @lem3350672 A x h1 h2). Qed.
Lemma lem3350675 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3350676 : term128 = False.
Proof. exact (@lem3350675 False). Qed.
Lemma lem3350677 {A : Type'} (x : A) (h1 : term27 A) (h2 : term49 A x) : False.
Proof. exact (EQ_MP (@lem3350676) (@lem3350673 A x h1 h2)). Qed.
Lemma lem3350678 {A : Type'} (x : A) (h1 : term27 A) (h2 : term49 A x) : (term49 A x) = False.
Proof. exact (prop_ext (fun h3 : term49 A x => @lem3350677 A x h1 h2) (fun h3 : False => @lem3350527 A x h2)). Qed.
Lemma lem3350679 {A : Type'} (x : A) (h1 : term27 A) (h2 : term49 A x) : False.
Proof. exact (EQ_MP (@lem3350678 A x h1 h2) (@lem3350527 A x h2)). Qed.
Lemma lem3350680 {A : Type'} (x : A) (h1 : term27 A) (h2 : term49 A x) : (term49 A x) = False.
Proof. exact (prop_ext (fun h3 : term49 A x => @lem3350679 A x h1 h2) (fun h3 : False => @lem3350518 A x h2)). Qed.
Lemma lem3350681 {A : Type'} (x : A) (h1 : term27 A) (h2 : term49 A x) : False.
Proof. exact (EQ_MP (@lem3350680 A x h1 h2) (@lem3350518 A x h2)). Qed.
Lemma lem3350682 {A : Type'} (h1 : term27 A) (h2 : term26 A) : False.
Proof. exact (ex_elim (@lem3350165 A h2) (fun x : A => fun h0 : term56 A x => @lem3350681 A x h1 h0)). Qed.
Lemma lem3350683 {A : Type'} (h1 : term26 A) : term32 A.
Proof. exact (fun h0 : term27 A => @lem3350682 A h0 h1). Qed.
Lemma lem3350684 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (@lem69 (term27 A)). Qed.
Lemma lem3350685 {A : Type'} (h1 : term26 A) : term33 A.
Proof. exact (EQ_MP (@lem3350684 A) (@lem3350683 A h1)). Qed.
Lemma lem3350686 {A : Type'} : term35 A.
Proof. exact (fun h0 : term26 A => @lem3350685 A h0). Qed.
Lemma lem3350687 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem3350129 A) (@lem3350686 A)). Qed.
Lemma lem3350689 {A : Type'} : term28 A.
Proof. exact (@lem3350045 A (@lem3350687 A)). Qed.
Lemma lem3350690 {A : Type'} (h1 : term26 A) : term32 A.
Proof. exact (@lem3350689 A (@lem3350028 A h1)). Qed.
Lemma lem3350691 {A : Type'} (h1 : term26 A) : False.
Proof. exact (@lem3350690 A h1 (@lem3350029 A)). Qed.
Lemma lem3350692 {A : Type'} (h1 : term26 A) : (term26 A) = False.
Proof. exact (prop_ext (fun h2 : term26 A => @lem3350691 A h1) (fun h2 : False => @lem3350028 A h1)). Qed.
Lemma lem3350693 {A : Type'} (h1 : term26 A) : False.
Proof. exact (EQ_MP (@lem3350692 A h1) (@lem3350028 A h1)). Qed.
Lemma lem3350694 {A : Type'} : term25 A.
Proof. exact (fun h0 : term26 A => @lem3350693 A h0). Qed.
Lemma lem3350695 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem3350027 A) (@lem3350694 A)). Qed.
Lemma lem3350696 {A : Type'} : (@UNIONS A (@UNIV (A -> Prop))) = (@UNIV A).
Proof. exact (EQ_MP (@lem3350023 A) (@lem3350695 A)). Qed.
