Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DELETE_SUBSET_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3308947 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3308948 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3308947 A s t). Qed.
Lemma lem3308949 {A : Type'} (x : A) (s : A -> Prop) : (term1 A x s) = (term2 A x s).
Proof. exact (@lem3308948 A (@DELETE A s x) s). Qed.
Lemma lem3308956 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3308949 A x s)). Qed.
Lemma lem3308957 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3308958 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (MK_COMB (@lem3308957 A) (@lem3308956 A x)). Qed.
Lemma lem3308963 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun x : A => @lem3308958 A x)). Qed.
Lemma lem3308964 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3308965 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3308964 A) (@lem3308963 A)). Qed.
Lemma lem3308970 {A : Type'} : (term10 A) = (term9 A).
Proof. exact (SYM (@lem3308965 A)). Qed.
Lemma lem3308986 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3308987 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (@lem3308986 A s x y). Qed.
Lemma lem3308988 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term11 A x' s x) = (term12 A s x' x).
Proof. exact (@lem3308987 A s x' x). Qed.
Lemma lem3308992 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3308993 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3308992 A P x). Qed.
Lemma lem3308994 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3308993 A s x'). Qed.
Lemma lem3308995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3308996 {A : Type'} (s : A -> Prop) (x' : A) : (term13 A x' s) = (term14 A s x').
Proof. exact (MK_COMB (@lem3308995) (@lem3308994 A s x')). Qed.
Lemma lem3308999 {A : Type'} (x' : A) (x : A) : (term15 A x' x) = (term15 A x' x).
Proof. exact (eq_refl (term15 A x' x)). Qed.
Lemma lem3309000 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term12 A s x' x) = (term16 A s x' x).
Proof. exact (MK_COMB (@lem3308996 A s x') (@lem3308999 A x' x)). Qed.
Lemma lem3309003 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term11 A x' s x) = (term16 A s x' x).
Proof. exact (TRANS (@lem3308988 A s x' x) (@lem3309000 A s x' x)). Qed.
Lemma lem3309004 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3309005 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term17 A x' s x) = (term18 A s x' x).
Proof. exact (MK_COMB (@lem3309004) (@lem3309003 A s x' x)). Qed.
Lemma lem3309007 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3309008 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3309007 A P x). Qed.
Lemma lem3309009 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3309008 A s x'). Qed.
Lemma lem3309010 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term19 A x x' s) = (term20 A x s x').
Proof. exact (MK_COMB (@lem3309005 A s x' x) (@lem3309009 A s x')). Qed.
Lemma lem3309013 {A : Type'} (x : A) (s : A -> Prop) : (term21 A x s) = (term22 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3309010 A x s x')). Qed.
Lemma lem3309014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309015 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term23 A x s).
Proof. exact (MK_COMB (@lem3309014 A) (@lem3309013 A x s)). Qed.
Lemma lem3309020 {A : Type'} (x : A) : (term4 A x) = (term24 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3309015 A x s)). Qed.
Lemma lem3309021 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3309022 {A : Type'} (x : A) : (term6 A x) = (term25 A x).
Proof. exact (MK_COMB (@lem3309021 A) (@lem3309020 A x)). Qed.
Lemma lem3309027 {A : Type'} : (term8 A) = (term26 A).
Proof. exact (fun_ext (fun x : A => @lem3309022 A x)). Qed.
Lemma lem3309028 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309029 {A : Type'} : (term10 A) = (term27 A).
Proof. exact (MK_COMB (@lem3309028 A) (@lem3309027 A)). Qed.
Lemma lem3309034 {A : Type'} : (term27 A) = (term10 A).
Proof. exact (SYM (@lem3309029 A)). Qed.
Lemma lem3309036 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3309037 {A : Type'} : (term27 A) = (term29 A).
Proof. exact (@lem3309036 (term27 A)). Qed.
Lemma lem3309038 {A : Type'} : (term29 A) = (term27 A).
Proof. exact (SYM (@lem3309037 A)). Qed.
Lemma lem3309039 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem3309042 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3309043 {A : Type'} : term31 A.
Proof. exact (fun h0 : term29 A => @lem3309042 A h0). Qed.
Lemma lem3309044 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3309045 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3309046 {A : Type'} (h1 : term29 A) (h2 : term31 A) : term29 A.
Proof. exact (@lem3309044 A h2 (@lem3309045 A h1)). Qed.
Lemma lem3309047 {A : Type'} (h1 : term29 A) : term32 A.
Proof. exact (fun h0 : term31 A => @lem3309046 A h1 h0). Qed.
Lemma lem3309048 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3309049 {A : Type'} (h1 : term29 A) (h2 : term31 A) : term29 A.
Proof. exact (@lem3309047 A h1 (@lem3309048 A h2)). Qed.
Lemma lem3309050 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (fun h0 : term29 A => @lem3309049 A h0 h1). Qed.
Lemma lem3309051 {A : Type'} : term33 A.
Proof. exact (fun h0 : term31 A => @lem3309050 A h0). Qed.
Lemma lem3309054 {A : Type'} : term31 A.
Proof. exact (@lem3309051 A (@lem3309043 A)). Qed.
Lemma lem3309055 {A : Type'} : term31 A.
Proof. exact (@lem3309054 A). Qed.
Lemma lem3309057 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3309058 {A : Type'} : (term29 A) = (term34 A).
Proof. exact (@lem3309057 (term30 A)). Qed.
Lemma lem3309060 (t : Prop) : (term35 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3309061 {A : Type'} : (term34 A) = (term27 A).
Proof. exact (@lem3309060 (term27 A)). Qed.
Lemma lem3309082 {A : Type'} : (term29 A) = (term27 A).
Proof. exact (TRANS (@lem3309058 A) (@lem3309061 A)). Qed.
Lemma lem3309093 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term20 A x s x') = (term20 A x s x').
Proof. exact (eq_refl (term20 A x s x')). Qed.
Lemma lem3309094 {A : Type'} (x : A) (s : A -> Prop) : (term22 A x s) = (term22 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3309093 A x s x')). Qed.
Lemma lem3309095 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309096 {A : Type'} (x : A) (s : A -> Prop) : (term23 A x s) = (term23 A x s).
Proof. exact (MK_COMB (@lem3309095 A) (@lem3309094 A x s)). Qed.
Lemma lem3309097 {A : Type'} (x : A) : (term24 A x) = (term24 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3309096 A x s)). Qed.
Lemma lem3309098 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3309099 {A : Type'} (x : A) : (term25 A x) = (term25 A x).
Proof. exact (MK_COMB (@lem3309098 A) (@lem3309097 A x)). Qed.
Lemma lem3309100 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (fun_ext (fun x : A => @lem3309099 A x)). Qed.
Lemma lem3309101 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309102 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem3309101 A) (@lem3309100 A)). Qed.
Lemma lem3309127 {A : Type'} : (term29 A) = (term27 A).
Proof. exact (TRANS (@lem3309082 A) (@lem3309102 A)). Qed.
Lemma lem3309128 {A : Type'} : (term27 A) = (term29 A).
Proof. exact (SYM (@lem3309127 A)). Qed.
Lemma lem3309131 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3309132 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (term36 A s x').
Proof. exact (@lem3309131 (s x')). Qed.
Lemma lem3309133 {A : Type'} (s : A -> Prop) (x' : A) : (term36 A s x') = (s x').
Proof. exact (SYM (@lem3309132 A s x')). Qed.
Lemma lem3309134 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3309144 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term16 A s x' x) : term16 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3309150 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3309164 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term16 A s x' x) : term16 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3309170 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3309176 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3309186 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3309206 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term16 A s x' x) : s x'.
Proof. exact (proj1 (@lem3309164 A s x' x h1)). Qed.
Lemma lem3309207 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term16 A s x' x) : term38 A s x'.
Proof. exact (fun h0 : term37 A s x' => @lem3309206 A s x' x h1). Qed.
Lemma lem3309209 (p : Prop) : (term39 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3309210 {A : Type'} (s : A -> Prop) (x' : A) : (term38 A s x') = (s x').
Proof. exact (@lem3309209 (s x')). Qed.
Lemma lem3309211 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term16 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3309210 A s x') (@lem3309207 A s x' x h1)). Qed.
Lemma lem3309214 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3309216 {A : Type'} (s : A -> Prop) (x' : A) : (term37 A s x') = (term40 A s x').
Proof. exact (@lem3309214 (s x')). Qed.
Lemma lem3309219 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term40 A s x'.
Proof. exact (EQ_MP (@lem3309216 A s x') (@lem3309186 A s x' h1)). Qed.
Lemma lem3309222 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (@lem3309219 A s x' h1 (@lem3309211 A s x' x h2)). Qed.
Lemma lem3309223 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : term41.
Proof. exact (fun h0 : ~ False => @lem3309222 A s x' x h1 h2). Qed.
Lemma lem3309225 (p : Prop) : (term39 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3309226 : term41 = False.
Proof. exact (@lem3309225 False). Qed.
Lemma lem3309227 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (EQ_MP (@lem3309226) (@lem3309223 A s x' x h1 h2)). Qed.
Lemma lem3309228 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3309227 A s x' x h1 h2) (fun h3 : False => @lem3309186 A s x' h1)). Qed.
Lemma lem3309229 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (EQ_MP (@lem3309228 A s x' x h1 h2) (@lem3309186 A s x' h1)). Qed.
Lemma lem3309230 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3309229 A s x' x h1 h2) (fun h3 : False => @lem3309176 A s x' h1)). Qed.
Lemma lem3309231 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (EQ_MP (@lem3309230 A s x' x h1 h2) (@lem3309176 A s x' h1)). Qed.
Lemma lem3309232 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3309231 A s x' x h1 h2) (fun h3 : False => @lem3309176 A s x' h1)). Qed.
Lemma lem3309233 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (EQ_MP (@lem3309232 A s x' x h1 h2) (@lem3309176 A s x' h1)). Qed.
Lemma lem3309234 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3309233 A s x' x h1 h2) (fun h3 : False => @lem3309170 A s x' h1)). Qed.
Lemma lem3309235 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (EQ_MP (@lem3309234 A s x' x h1 h2) (@lem3309170 A s x' h1)). Qed.
Lemma lem3309236 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : (term16 A s x' x) = False.
Proof. exact (prop_ext (fun h3 : term16 A s x' x => @lem3309235 A s x' x h1 h2) (fun h3 : False => @lem3309164 A s x' x h2)). Qed.
Lemma lem3309237 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (EQ_MP (@lem3309236 A s x' x h1 h2) (@lem3309164 A s x' x h2)). Qed.
Lemma lem3309238 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3309237 A s x' x h1 h2) (fun h3 : False => @lem3309150 A s x' h1)). Qed.
Lemma lem3309239 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (EQ_MP (@lem3309238 A s x' x h1 h2) (@lem3309150 A s x' h1)). Qed.
Lemma lem3309240 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : (term16 A s x' x) = False.
Proof. exact (prop_ext (fun h3 : term16 A s x' x => @lem3309239 A s x' x h1 h2) (fun h3 : False => @lem3309144 A s x' x h2)). Qed.
Lemma lem3309241 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (EQ_MP (@lem3309240 A s x' x h1 h2) (@lem3309144 A s x' x h2)). Qed.
Lemma lem3309242 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3309241 A s x' x h1 h2) (fun h3 : False => @lem3309134 A s x' h1)). Qed.
Lemma lem3309243 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term16 A s x' x) : False.
Proof. exact (EQ_MP (@lem3309242 A s x' x h1 h2) (@lem3309134 A s x' h1)). Qed.
Lemma lem3309244 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term16 A s x' x) : term36 A s x'.
Proof. exact (fun h0 : term37 A s x' => @lem3309243 A s x' x h0 h1). Qed.
Lemma lem3309245 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term16 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3309133 A s x') (@lem3309244 A s x' x h1)). Qed.
Lemma lem3309246 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : term20 A x s x'.
Proof. exact (fun h0 : term16 A s x' x => @lem3309245 A s x' x h0). Qed.
Lemma lem3309251 {A : Type'} (x : A) (s : A -> Prop) : term23 A x s.
Proof. exact (fun x' : A => @lem3309246 A x s x'). Qed.
Lemma lem3309256 {A : Type'} (x : A) : term25 A x.
Proof. exact (fun s : A -> Prop => @lem3309251 A x s). Qed.
Lemma lem3309261 {A : Type'} : term27 A.
Proof. exact (fun x : A => @lem3309256 A x). Qed.
Lemma lem3309262 {A : Type'} : term29 A.
Proof. exact (EQ_MP (@lem3309128 A) (@lem3309261 A)). Qed.
Lemma lem3309264 {A : Type'} : term29 A.
Proof. exact (@lem3309055 A (@lem3309262 A)). Qed.
Lemma lem3309265 {A : Type'} (h1 : term30 A) : False.
Proof. exact (@lem3309264 A (@lem3309039 A h1)). Qed.
Lemma lem3309266 {A : Type'} (h1 : term30 A) : (term30 A) = False.
Proof. exact (prop_ext (fun h2 : term30 A => @lem3309265 A h1) (fun h2 : False => @lem3309039 A h1)). Qed.
Lemma lem3309267 {A : Type'} (h1 : term30 A) : False.
Proof. exact (EQ_MP (@lem3309266 A h1) (@lem3309039 A h1)). Qed.
Lemma lem3309268 {A : Type'} : term29 A.
Proof. exact (fun h0 : term30 A => @lem3309267 A h0). Qed.
Lemma lem3309269 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem3309038 A) (@lem3309268 A)). Qed.
Lemma lem3309270 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3309034 A) (@lem3309269 A)). Qed.
Lemma lem3309271 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3308970 A) (@lem3309270 A)). Qed.
