Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_ASSOC_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3231941 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3231942 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3231941 A s t). Qed.
Lemma lem3231943 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term1 A s t u) = (term2 A s t u)) = (term3 A s t u).
Proof. exact (@lem3231942 A (term1 A s t u) (term2 A s t u)). Qed.
Lemma lem3231952 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term5 A s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3231943 A s t u)). Qed.
Lemma lem3231953 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3231954 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term6 A s t) = (term7 A s t).
Proof. exact (MK_COMB (@lem3231953 A) (@lem3231952 A s t)). Qed.
Lemma lem3231959 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3231954 A s t)). Qed.
Lemma lem3231960 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3231961 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (MK_COMB (@lem3231960 A) (@lem3231959 A s)). Qed.
Lemma lem3231966 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3231961 A s)). Qed.
Lemma lem3231967 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3231968 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3231967 A) (@lem3231966 A)). Qed.
Lemma lem3231973 {A : Type'} : (term15 A) = (term14 A).
Proof. exact (SYM (@lem3231968 A)). Qed.
Lemma lem3231993 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3231994 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3231993 A s x t). Qed.
Lemma lem3231995 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (u : A -> Prop) : (term18 A x s t u) = (term19 A s t x u).
Proof. exact (@lem3231994 A (@UNION A s t) x u). Qed.
Lemma lem3231999 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3232000 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3231999 A s x t). Qed.
Lemma lem3232004 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232005 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232004 A P x). Qed.
Lemma lem3232006 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3232005 A s x). Qed.
Lemma lem3232007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3232008 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3232007) (@lem3232006 A s x)). Qed.
Lemma lem3232010 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232011 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232010 A P x). Qed.
Lemma lem3232012 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3232011 A t x). Qed.
Lemma lem3232013 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A s x t) = (term22 A s t x).
Proof. exact (MK_COMB (@lem3232008 A s x) (@lem3232012 A t x)). Qed.
Lemma lem3232016 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term16 A x s t) = (term22 A s t x).
Proof. exact (TRANS (@lem3232000 A s x t) (@lem3232013 A s t x)). Qed.
Lemma lem3232017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3232018 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term23 A x s t) = (term24 A s t x).
Proof. exact (MK_COMB (@lem3232017) (@lem3232016 A s t x)). Qed.
Lemma lem3232020 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232021 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232020 A P x). Qed.
Lemma lem3232022 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3232021 A u x). Qed.
Lemma lem3232023 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term19 A s t x u) = (term25 A s t u x).
Proof. exact (MK_COMB (@lem3232018 A s t x) (@lem3232022 A u x)). Qed.
Lemma lem3232026 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term18 A x s t u) = (term25 A s t u x).
Proof. exact (TRANS (@lem3231995 A s t x u) (@lem3232023 A s t u x)). Qed.
Lemma lem3232027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3232028 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term26 A x s t u) = (term27 A s t u x).
Proof. exact (MK_COMB (@lem3232027) (@lem3232026 A s t u x)). Qed.
Lemma lem3232030 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3232031 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3232030 A s x t). Qed.
Lemma lem3232032 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term28 A x s t u) = (term29 A s x t u).
Proof. exact (@lem3232031 A s x (@UNION A t u)). Qed.
Lemma lem3232036 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232037 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232036 A P x). Qed.
Lemma lem3232038 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3232037 A s x). Qed.
Lemma lem3232039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3232040 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3232039) (@lem3232038 A s x)). Qed.
Lemma lem3232042 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3232043 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3232042 A s x t). Qed.
Lemma lem3232044 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term16 A x t u) = (term17 A t x u).
Proof. exact (@lem3232043 A t x u). Qed.
Lemma lem3232048 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232049 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232048 A P x). Qed.
Lemma lem3232050 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3232049 A t x). Qed.
Lemma lem3232051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3232052 {A : Type'} (t : A -> Prop) (x : A) : (term20 A x t) = (term21 A t x).
Proof. exact (MK_COMB (@lem3232051) (@lem3232050 A t x)). Qed.
Lemma lem3232054 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232055 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232054 A P x). Qed.
Lemma lem3232056 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3232055 A u x). Qed.
Lemma lem3232057 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term17 A t x u) = (term22 A t u x).
Proof. exact (MK_COMB (@lem3232052 A t x) (@lem3232056 A u x)). Qed.
Lemma lem3232060 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term16 A x t u) = (term22 A t u x).
Proof. exact (TRANS (@lem3232044 A t x u) (@lem3232057 A t u x)). Qed.
Lemma lem3232061 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term29 A s x t u) = (term30 A s t u x).
Proof. exact (MK_COMB (@lem3232040 A s x) (@lem3232060 A t u x)). Qed.
Lemma lem3232064 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term28 A x s t u) = (term30 A s t u x).
Proof. exact (TRANS (@lem3232032 A s x t u) (@lem3232061 A s t u x)). Qed.
Lemma lem3232065 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : ((term18 A x s t u) = (term28 A x s t u)) = ((term25 A s t u x) = (term30 A s t u x)).
Proof. exact (MK_COMB (@lem3232028 A s t u x) (@lem3232064 A s t u x)). Qed.
Lemma lem3232068 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term31 A s t u) = (term32 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3232065 A s t u x)). Qed.
Lemma lem3232069 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3232070 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term3 A s t u) = (term33 A s t u).
Proof. exact (MK_COMB (@lem3232069 A) (@lem3232068 A s t u)). Qed.
Lemma lem3232075 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = (term34 A s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3232070 A s t u)). Qed.
Lemma lem3232076 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232077 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3232076 A) (@lem3232075 A s t)). Qed.
Lemma lem3232082 {A : Type'} (s : A -> Prop) : (term9 A s) = (term36 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3232077 A s t)). Qed.
Lemma lem3232083 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232084 {A : Type'} (s : A -> Prop) : (term11 A s) = (term37 A s).
Proof. exact (MK_COMB (@lem3232083 A) (@lem3232082 A s)). Qed.
Lemma lem3232089 {A : Type'} : (term13 A) = (term38 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3232084 A s)). Qed.
Lemma lem3232090 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232091 {A : Type'} : (term15 A) = (term39 A).
Proof. exact (MK_COMB (@lem3232090 A) (@lem3232089 A)). Qed.
Lemma lem3232096 {A : Type'} : (term39 A) = (term15 A).
Proof. exact (SYM (@lem3232091 A)). Qed.
Lemma lem3232098 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3232099 {A : Type'} : (term39 A) = (term41 A).
Proof. exact (@lem3232098 (term39 A)). Qed.
Lemma lem3232100 {A : Type'} : (term41 A) = (term39 A).
Proof. exact (SYM (@lem3232099 A)). Qed.
Lemma lem3232101 {A : Type'} (h1 : term42 A) : term42 A.
Proof. exact (h1). Qed.
Lemma lem3232104 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3232105 {A : Type'} : term43 A.
Proof. exact (fun h0 : term41 A => @lem3232104 A h0). Qed.
Lemma lem3232106 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem3232107 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3232108 {A : Type'} (h1 : term41 A) (h2 : term43 A) : term41 A.
Proof. exact (@lem3232106 A h2 (@lem3232107 A h1)). Qed.
Lemma lem3232109 {A : Type'} (h1 : term41 A) : term44 A.
Proof. exact (fun h0 : term43 A => @lem3232108 A h1 h0). Qed.
Lemma lem3232110 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem3232111 {A : Type'} (h1 : term41 A) (h2 : term43 A) : term41 A.
Proof. exact (@lem3232109 A h1 (@lem3232110 A h2)). Qed.
Lemma lem3232112 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (fun h0 : term41 A => @lem3232111 A h0 h1). Qed.
Lemma lem3232113 {A : Type'} : term45 A.
Proof. exact (fun h0 : term43 A => @lem3232112 A h0). Qed.
Lemma lem3232116 {A : Type'} : term43 A.
Proof. exact (@lem3232113 A (@lem3232105 A)). Qed.
Lemma lem3232117 {A : Type'} : term43 A.
Proof. exact (@lem3232116 A). Qed.
Lemma lem3232119 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3232120 {A : Type'} : (term41 A) = (term46 A).
Proof. exact (@lem3232119 (term42 A)). Qed.
Lemma lem3232122 (t : Prop) : (term47 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3232123 {A : Type'} : (term46 A) = (term39 A).
Proof. exact (@lem3232122 (term39 A)). Qed.
Lemma lem3232152 {A : Type'} : (term41 A) = (term39 A).
Proof. exact (TRANS (@lem3232120 A) (@lem3232123 A)). Qed.
Lemma lem3232173 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : ((term25 A s t u x) = (term30 A s t u x)) = ((term25 A s t u x) = (term30 A s t u x)).
Proof. exact (eq_refl ((term25 A s t u x) = (term30 A s t u x))). Qed.
Lemma lem3232174 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term32 A s t u) = (term32 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3232173 A s t u x)). Qed.
Lemma lem3232175 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3232176 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term33 A s t u) = (term33 A s t u).
Proof. exact (MK_COMB (@lem3232175 A) (@lem3232174 A s t u)). Qed.
Lemma lem3232177 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term34 A s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3232176 A s t u)). Qed.
Lemma lem3232178 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232179 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3232178 A) (@lem3232177 A s t)). Qed.
Lemma lem3232180 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3232179 A s t)). Qed.
Lemma lem3232181 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232182 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (MK_COMB (@lem3232181 A) (@lem3232180 A s)). Qed.
Lemma lem3232183 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3232182 A s)). Qed.
Lemma lem3232184 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232185 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (MK_COMB (@lem3232184 A) (@lem3232183 A)). Qed.
Lemma lem3232220 {A : Type'} : (term41 A) = (term39 A).
Proof. exact (TRANS (@lem3232152 A) (@lem3232185 A)). Qed.
Lemma lem3232221 {A : Type'} : (term39 A) = (term41 A).
Proof. exact (SYM (@lem3232220 A)). Qed.
Lemma lem3232223 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3232224 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : ((term25 A s t u x) = (term30 A s t u x)) = (term48 A s t u x).
Proof. exact (@lem3232223 ((term25 A s t u x) = (term30 A s t u x))). Qed.
Lemma lem3232225 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term48 A s t u x) = ((term25 A s t u x) = (term30 A s t u x)).
Proof. exact (SYM (@lem3232224 A s t u x)). Qed.
Lemma lem3232226 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : term49 A s t u x.
Proof. exact (h1). Qed.
Lemma lem3232235 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term50 A s t x) = (term51 A s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3232239 {A : Type'} (u : A -> Prop) (x : A) : (term52 A u x) = (term52 A u x).
Proof. exact (eq_refl (term52 A u x)). Qed.
Lemma lem3232241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3232242 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term54 A s t x).
Proof. exact (MK_COMB (@lem3232241) (@lem3232235 A s t x)). Qed.
Lemma lem3232243 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term55 A s t u x) = (term56 A s t u x).
Proof. exact (MK_COMB (@lem3232242 A s t x) (@lem3232239 A u x)). Qed.
Lemma lem3232244 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term57 A s t u x) = (term55 A s t u x).
Proof. exact (@lem17160 (term22 A s t x) (u x)). Qed.
Lemma lem3232245 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term57 A s t u x) = (term56 A s t u x).
Proof. exact (TRANS (@lem3232244 A s t u x) (@lem3232243 A s t u x)). Qed.
Lemma lem3232259 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term50 A t u x) = (term51 A t u x).
Proof. exact (@lem17160 (t x) (u x)). Qed.
Lemma lem3232264 {A : Type'} (s : A -> Prop) (x : A) : (term58 A s x) = (term58 A s x).
Proof. exact (eq_refl (term58 A s x)). Qed.
Lemma lem3232265 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term59 A s t u x) = (term60 A s t u x).
Proof. exact (MK_COMB (@lem3232264 A s x) (@lem3232259 A t u x)). Qed.
Lemma lem3232266 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term61 A s t u x) = (term59 A s t u x).
Proof. exact (@lem17160 (s x) (term22 A t u x)). Qed.
Lemma lem3232267 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term61 A s t u x) = (term60 A s t u x).
Proof. exact (TRANS (@lem3232266 A s t u x) (@lem3232265 A s t u x)). Qed.
Lemma lem3232270 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term30 A s t u x) = (term30 A s t u x).
Proof. exact (eq_refl (term30 A s t u x)). Qed.
Lemma lem3232271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3232272 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term62 A s t u x) = (term63 A s t u x).
Proof. exact (MK_COMB (@lem3232271) (@lem3232245 A s t u x)). Qed.
Lemma lem3232273 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term64 A s t u x) = (term65 A s t u x).
Proof. exact (MK_COMB (@lem3232272 A s t u x) (@lem3232270 A s t u x)). Qed.
Lemma lem3232275 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term66 A s t u x) = (term66 A s t u x).
Proof. exact (eq_refl (term66 A s t u x)). Qed.
Lemma lem3232276 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term67 A s t u x) = (term68 A s t u x).
Proof. exact (MK_COMB (@lem3232275 A s t u x) (@lem3232267 A s t u x)). Qed.
Lemma lem3232277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3232278 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term69 A s t u x) = (term70 A s t u x).
Proof. exact (MK_COMB (@lem3232277) (@lem3232276 A s t u x)). Qed.
Lemma lem3232279 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term71 A s t u x) = (term72 A s t u x).
Proof. exact (MK_COMB (@lem3232278 A s t u x) (@lem3232273 A s t u x)). Qed.
Lemma lem3232280 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term49 A s t u x) = (term71 A s t u x).
Proof. exact (@lem17646 (term25 A s t u x) (term30 A s t u x)). Qed.
Lemma lem3232285 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term49 A s t u x) = (term72 A s t u x).
Proof. exact (TRANS (@lem3232280 A s t u x) (@lem3232279 A s t u x)). Qed.
Lemma lem3232368 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : term72 A s t u x.
Proof. exact (EQ_MP (@lem3232285 A s t u x) (@lem3232226 A s t u x h1)). Qed.
Lemma lem3232369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term68 A s t u x.
Proof. exact (h1). Qed.
Lemma lem3232370 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term65 A s t u x.
Proof. exact (h1). Qed.
Lemma lem3232371 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term60 A s t u x.
Proof. exact (proj2 (@lem3232369 A s t u x h1)). Qed.
Lemma lem3232372 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term25 A s t u x.
Proof. exact (proj1 (@lem3232369 A s t u x h1)). Qed.
Lemma lem3232373 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term51 A t u x.
Proof. exact (proj2 (@lem3232371 A s t u x h1)). Qed.
Lemma lem3232377 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term22 A s t x) : term22 A s t x.
Proof. exact (h1). Qed.
Lemma lem3232381 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term30 A s t u x.
Proof. exact (proj2 (@lem3232370 A s t u x h1)). Qed.
Lemma lem3232382 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term56 A s t u x.
Proof. exact (proj1 (@lem3232370 A s t u x h1)). Qed.
Lemma lem3232384 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term51 A s t x.
Proof. exact (proj1 (@lem3232382 A s t u x h1)). Qed.
Lemma lem3232388 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term22 A t u x) : term22 A t u x.
Proof. exact (h1). Qed.
Lemma lem3232406 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3232422 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3232438 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3232454 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3232470 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3232486 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3232488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term52 A s x.
Proof. exact (proj1 (@lem3232371 A s t u x h1)). Qed.
Lemma lem3232494 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3232498 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term52 A t x.
Proof. exact (proj1 (@lem3232373 A s t u x h1)). Qed.
Lemma lem3232502 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3232508 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term52 A u x.
Proof. exact (proj2 (@lem3232373 A s t u x h1)). Qed.
Lemma lem3232510 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3232514 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term52 A s x.
Proof. exact (proj1 (@lem3232384 A s t u x h1)). Qed.
Lemma lem3232518 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3232524 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term52 A t x.
Proof. exact (proj2 (@lem3232384 A s t u x h1)). Qed.
Lemma lem3232526 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3232528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term52 A u x.
Proof. exact (proj2 (@lem3232382 A s t u x h1)). Qed.
Lemma lem3232534 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3232536 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3232537 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term73 A s x.
Proof. exact (fun h0 : term52 A s x => @lem3232536 A s x h1). Qed.
Lemma lem3232539 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232540 {A : Type'} (s : A -> Prop) (x : A) : (term73 A s x) = (s x).
Proof. exact (@lem3232539 (s x)). Qed.
Lemma lem3232541 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3232540 A s x) (@lem3232537 A s x h1)). Qed.
Lemma lem3232544 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3232546 {A : Type'} (s : A -> Prop) (x : A) : (term52 A s x) = (term75 A s x).
Proof. exact (@lem3232544 (s x)). Qed.
Lemma lem3232549 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term75 A s x.
Proof. exact (EQ_MP (@lem3232546 A s x) (@lem3232488 A s t u x h1)). Qed.
Lemma lem3232552 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term68 A s t u x) : False.
Proof. exact (@lem3232549 A s t u x h2 (@lem3232541 A s x h1)). Qed.
Lemma lem3232553 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term68 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3232552 A s t u x h1 h2). Qed.
Lemma lem3232555 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232556 : term76 = False.
Proof. exact (@lem3232555 False). Qed.
Lemma lem3232557 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232556) (@lem3232553 A s t u x h1 h2)). Qed.
Lemma lem3232559 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3232560 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term73 A t x.
Proof. exact (fun h0 : term52 A t x => @lem3232559 A t x h1). Qed.
Lemma lem3232562 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232563 {A : Type'} (t : A -> Prop) (x : A) : (term73 A t x) = (t x).
Proof. exact (@lem3232562 (t x)). Qed.
Lemma lem3232564 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3232563 A t x) (@lem3232560 A t x h1)). Qed.
Lemma lem3232567 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3232569 {A : Type'} (t : A -> Prop) (x : A) : (term52 A t x) = (term75 A t x).
Proof. exact (@lem3232567 (t x)). Qed.
Lemma lem3232572 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term75 A t x.
Proof. exact (EQ_MP (@lem3232569 A t x) (@lem3232498 A s t u x h1)). Qed.
Lemma lem3232575 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term68 A s t u x) : False.
Proof. exact (@lem3232572 A s t u x h2 (@lem3232564 A t x h1)). Qed.
Lemma lem3232576 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term68 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3232575 A s t u x h1 h2). Qed.
Lemma lem3232578 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232579 : term76 = False.
Proof. exact (@lem3232578 False). Qed.
Lemma lem3232580 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232579) (@lem3232576 A s t u x h1 h2)). Qed.
Lemma lem3232582 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3232583 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : term73 A u x.
Proof. exact (fun h0 : term52 A u x => @lem3232582 A u x h1). Qed.
Lemma lem3232585 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232586 {A : Type'} (u : A -> Prop) (x : A) : (term73 A u x) = (u x).
Proof. exact (@lem3232585 (u x)). Qed.
Lemma lem3232587 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem3232586 A u x) (@lem3232583 A u x h1)). Qed.
Lemma lem3232590 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3232592 {A : Type'} (u : A -> Prop) (x : A) : (term52 A u x) = (term75 A u x).
Proof. exact (@lem3232590 (u x)). Qed.
Lemma lem3232595 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term75 A u x.
Proof. exact (EQ_MP (@lem3232592 A u x) (@lem3232508 A s t u x h1)). Qed.
Lemma lem3232598 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term68 A s t u x) : False.
Proof. exact (@lem3232595 A s t u x h2 (@lem3232587 A u x h1)). Qed.
Lemma lem3232599 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term68 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3232598 A s t u x h1 h2). Qed.
Lemma lem3232601 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232602 : term76 = False.
Proof. exact (@lem3232601 False). Qed.
Lemma lem3232603 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232602) (@lem3232599 A s t u x h1 h2)). Qed.
Lemma lem3232605 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3232606 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term73 A s x.
Proof. exact (fun h0 : term52 A s x => @lem3232605 A s x h1). Qed.
Lemma lem3232608 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232609 {A : Type'} (s : A -> Prop) (x : A) : (term73 A s x) = (s x).
Proof. exact (@lem3232608 (s x)). Qed.
Lemma lem3232610 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3232609 A s x) (@lem3232606 A s x h1)). Qed.
Lemma lem3232613 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3232615 {A : Type'} (s : A -> Prop) (x : A) : (term52 A s x) = (term75 A s x).
Proof. exact (@lem3232613 (s x)). Qed.
Lemma lem3232618 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term75 A s x.
Proof. exact (EQ_MP (@lem3232615 A s x) (@lem3232514 A s t u x h1)). Qed.
Lemma lem3232621 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term65 A s t u x) : False.
Proof. exact (@lem3232618 A s t u x h2 (@lem3232610 A s x h1)). Qed.
Lemma lem3232622 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term65 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3232621 A s t u x h1 h2). Qed.
Lemma lem3232624 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232625 : term76 = False.
Proof. exact (@lem3232624 False). Qed.
Lemma lem3232626 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232625) (@lem3232622 A s t u x h1 h2)). Qed.
Lemma lem3232628 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3232629 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term73 A t x.
Proof. exact (fun h0 : term52 A t x => @lem3232628 A t x h1). Qed.
Lemma lem3232631 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232632 {A : Type'} (t : A -> Prop) (x : A) : (term73 A t x) = (t x).
Proof. exact (@lem3232631 (t x)). Qed.
Lemma lem3232633 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3232632 A t x) (@lem3232629 A t x h1)). Qed.
Lemma lem3232636 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3232638 {A : Type'} (t : A -> Prop) (x : A) : (term52 A t x) = (term75 A t x).
Proof. exact (@lem3232636 (t x)). Qed.
Lemma lem3232641 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term75 A t x.
Proof. exact (EQ_MP (@lem3232638 A t x) (@lem3232524 A s t u x h1)). Qed.
Lemma lem3232644 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term65 A s t u x) : False.
Proof. exact (@lem3232641 A s t u x h2 (@lem3232633 A t x h1)). Qed.
Lemma lem3232645 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term65 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3232644 A s t u x h1 h2). Qed.
Lemma lem3232647 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232648 : term76 = False.
Proof. exact (@lem3232647 False). Qed.
Lemma lem3232649 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232648) (@lem3232645 A s t u x h1 h2)). Qed.
Lemma lem3232651 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3232652 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : term73 A u x.
Proof. exact (fun h0 : term52 A u x => @lem3232651 A u x h1). Qed.
Lemma lem3232654 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232655 {A : Type'} (u : A -> Prop) (x : A) : (term73 A u x) = (u x).
Proof. exact (@lem3232654 (u x)). Qed.
Lemma lem3232656 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem3232655 A u x) (@lem3232652 A u x h1)). Qed.
Lemma lem3232659 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3232661 {A : Type'} (u : A -> Prop) (x : A) : (term52 A u x) = (term75 A u x).
Proof. exact (@lem3232659 (u x)). Qed.
Lemma lem3232664 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term75 A u x.
Proof. exact (EQ_MP (@lem3232661 A u x) (@lem3232528 A s t u x h1)). Qed.
Lemma lem3232667 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term65 A s t u x) : False.
Proof. exact (@lem3232664 A s t u x h2 (@lem3232656 A u x h1)). Qed.
Lemma lem3232668 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term65 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3232667 A s t u x h1 h2). Qed.
Lemma lem3232670 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3232671 : term76 = False.
Proof. exact (@lem3232670 False). Qed.
Lemma lem3232672 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232671) (@lem3232668 A s t u x h1 h2)). Qed.
Lemma lem3232673 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term65 A s t u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3232672 A s t u x h1 h2) (fun h3 : False => @lem3232534 A u x h1)). Qed.
Lemma lem3232674 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232673 A s t u x h1 h2) (@lem3232534 A u x h1)). Qed.
Lemma lem3232675 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term65 A s t u x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3232649 A s t u x h1 h2) (fun h3 : False => @lem3232526 A t x h1)). Qed.
Lemma lem3232676 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232675 A s t u x h1 h2) (@lem3232526 A t x h1)). Qed.
Lemma lem3232677 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term65 A s t u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3232626 A s t u x h1 h2) (fun h3 : False => @lem3232518 A s x h1)). Qed.
Lemma lem3232678 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232677 A s t u x h1 h2) (@lem3232518 A s x h1)). Qed.
Lemma lem3232679 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term68 A s t u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3232603 A s t u x h1 h2) (fun h3 : False => @lem3232510 A u x h1)). Qed.
Lemma lem3232680 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232679 A s t u x h1 h2) (@lem3232510 A u x h1)). Qed.
Lemma lem3232681 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term68 A s t u x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3232580 A s t u x h1 h2) (fun h3 : False => @lem3232502 A t x h1)). Qed.
Lemma lem3232682 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232681 A s t u x h1 h2) (@lem3232502 A t x h1)). Qed.
Lemma lem3232683 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term68 A s t u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3232557 A s t u x h1 h2) (fun h3 : False => @lem3232494 A s x h1)). Qed.
Lemma lem3232684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232683 A s t u x h1 h2) (@lem3232494 A s x h1)). Qed.
Lemma lem3232685 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term65 A s t u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3232674 A s t u x h1 h2) (fun h3 : False => @lem3232486 A u x h1)). Qed.
Lemma lem3232686 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232685 A s t u x h1 h2) (@lem3232486 A u x h1)). Qed.
Lemma lem3232687 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term65 A s t u x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3232676 A s t u x h1 h2) (fun h3 : False => @lem3232470 A t x h1)). Qed.
Lemma lem3232688 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232687 A s t u x h1 h2) (@lem3232470 A t x h1)). Qed.
Lemma lem3232689 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term65 A s t u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3232678 A s t u x h1 h2) (fun h3 : False => @lem3232454 A s x h1)). Qed.
Lemma lem3232690 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232689 A s t u x h1 h2) (@lem3232454 A s x h1)). Qed.
Lemma lem3232691 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term68 A s t u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3232680 A s t u x h1 h2) (fun h3 : False => @lem3232438 A u x h1)). Qed.
Lemma lem3232692 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232691 A s t u x h1 h2) (@lem3232438 A u x h1)). Qed.
Lemma lem3232693 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term68 A s t u x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3232682 A s t u x h1 h2) (fun h3 : False => @lem3232422 A t x h1)). Qed.
Lemma lem3232694 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232693 A s t u x h1 h2) (@lem3232422 A t x h1)). Qed.
Lemma lem3232695 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term68 A s t u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3232684 A s t u x h1 h2) (fun h3 : False => @lem3232406 A s x h1)). Qed.
Lemma lem3232696 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232695 A s t u x h1 h2) (@lem3232406 A s x h1)). Qed.
Lemma lem3232697 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term65 A s t u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3232686 A s t u x h1 h2) (fun h3 : False => @lem3232486 A u x h1)). Qed.
Lemma lem3232698 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232697 A s t u x h1 h2) (@lem3232486 A u x h1)). Qed.
Lemma lem3232699 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term65 A s t u x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3232688 A s t u x h1 h2) (fun h3 : False => @lem3232470 A t x h1)). Qed.
Lemma lem3232700 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232699 A s t u x h1 h2) (@lem3232470 A t x h1)). Qed.
Lemma lem3232701 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term65 A s t u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3232690 A s t u x h1 h2) (fun h3 : False => @lem3232454 A s x h1)). Qed.
Lemma lem3232702 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232701 A s t u x h1 h2) (@lem3232454 A s x h1)). Qed.
Lemma lem3232703 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term68 A s t u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3232692 A s t u x h1 h2) (fun h3 : False => @lem3232438 A u x h1)). Qed.
Lemma lem3232704 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232703 A s t u x h1 h2) (@lem3232438 A u x h1)). Qed.
Lemma lem3232705 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term68 A s t u x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3232694 A s t u x h1 h2) (fun h3 : False => @lem3232422 A t x h1)). Qed.
Lemma lem3232706 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232705 A s t u x h1 h2) (@lem3232422 A t x h1)). Qed.
Lemma lem3232707 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term68 A s t u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3232696 A s t u x h1 h2) (fun h3 : False => @lem3232406 A s x h1)). Qed.
Lemma lem3232708 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232707 A s t u x h1 h2) (@lem3232406 A s x h1)). Qed.
Lemma lem3232709 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) (h2 : term22 A t u x) : False.
Proof. exact (or_elim (@lem3232388 A t u x h2) (fun h0 : t x => @lem3232700 A s t u x h0 h1) (fun h0 : u x => @lem3232698 A s t u x h0 h1)). Qed.
Lemma lem3232710 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : False.
Proof. exact (or_elim (@lem3232381 A s t u x h1) (fun h0 : s x => @lem3232702 A s t u x h0 h1) (fun h0 : term22 A t u x => @lem3232709 A s t u x h1 h0)). Qed.
Lemma lem3232711 {A : Type'} (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term68 A s t u x) (h2 : term22 A s t x) : False.
Proof. exact (or_elim (@lem3232377 A s t x h2) (fun h0 : s x => @lem3232708 A s t u x h0 h1) (fun h0 : t x => @lem3232706 A s t u x h0 h1)). Qed.
Lemma lem3232712 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : False.
Proof. exact (or_elim (@lem3232372 A s t u x h1) (fun h0 : term22 A s t x => @lem3232711 A u s t x h1 h0) (fun h0 : u x => @lem3232704 A s t u x h0 h1)). Qed.
Lemma lem3232713 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : False.
Proof. exact (or_elim (@lem3232368 A s t u x h1) (fun h0 : term68 A s t u x => @lem3232712 A s t u x h0) (fun h0 : term65 A s t u x => @lem3232710 A s t u x h0)). Qed.
Lemma lem3232714 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : (term49 A s t u x) = False.
Proof. exact (prop_ext (fun h2 : term49 A s t u x => @lem3232713 A s t u x h1) (fun h2 : False => @lem3232226 A s t u x h1)). Qed.
Lemma lem3232715 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : False.
Proof. exact (EQ_MP (@lem3232714 A s t u x h1) (@lem3232226 A s t u x h1)). Qed.
Lemma lem3232716 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : term48 A s t u x.
Proof. exact (fun h0 : term49 A s t u x => @lem3232715 A s t u x h0). Qed.
Lemma lem3232717 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term25 A s t u x) = (term30 A s t u x).
Proof. exact (EQ_MP (@lem3232225 A s t u x) (@lem3232716 A s t u x)). Qed.
Lemma lem3232722 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term33 A s t u.
Proof. exact (fun x : A => @lem3232717 A s t u x). Qed.
Lemma lem3232727 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term35 A s t.
Proof. exact (fun u : A -> Prop => @lem3232722 A s t u). Qed.
Lemma lem3232732 {A : Type'} (s : A -> Prop) : term37 A s.
Proof. exact (fun t : A -> Prop => @lem3232727 A s t). Qed.
Lemma lem3232737 {A : Type'} : term39 A.
Proof. exact (fun s : A -> Prop => @lem3232732 A s). Qed.
Lemma lem3232738 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem3232221 A) (@lem3232737 A)). Qed.
Lemma lem3232740 {A : Type'} : term41 A.
Proof. exact (@lem3232117 A (@lem3232738 A)). Qed.
Lemma lem3232741 {A : Type'} (h1 : term42 A) : False.
Proof. exact (@lem3232740 A (@lem3232101 A h1)). Qed.
Lemma lem3232742 {A : Type'} (h1 : term42 A) : (term42 A) = False.
Proof. exact (prop_ext (fun h2 : term42 A => @lem3232741 A h1) (fun h2 : False => @lem3232101 A h1)). Qed.
Lemma lem3232743 {A : Type'} (h1 : term42 A) : False.
Proof. exact (EQ_MP (@lem3232742 A h1) (@lem3232101 A h1)). Qed.
Lemma lem3232744 {A : Type'} : term41 A.
Proof. exact (fun h0 : term42 A => @lem3232743 A h0). Qed.
Lemma lem3232745 {A : Type'} : term39 A.
Proof. exact (EQ_MP (@lem3232100 A) (@lem3232744 A)). Qed.
Lemma lem3232746 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3232096 A) (@lem3232745 A)). Qed.
Lemma lem3232747 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3231973 A) (@lem3232746 A)). Qed.
