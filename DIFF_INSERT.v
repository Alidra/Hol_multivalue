Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_INSERT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3311931 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3311932 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3311931 A s t). Qed.
Lemma lem3311933 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term1 A s x t) = (term2 A s x t)) = (term3 A s x t).
Proof. exact (@lem3311932 A (term1 A s x t) (term2 A s x t)). Qed.
Lemma lem3311942 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term5 A s t).
Proof. exact (fun_ext (fun x : A => @lem3311933 A s x t)). Qed.
Lemma lem3311943 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3311944 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term6 A s t) = (term7 A s t).
Proof. exact (MK_COMB (@lem3311943 A) (@lem3311942 A s t)). Qed.
Lemma lem3311949 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3311944 A s t)). Qed.
Lemma lem3311950 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3311951 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (MK_COMB (@lem3311950 A) (@lem3311949 A s)). Qed.
Lemma lem3311956 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3311951 A s)). Qed.
Lemma lem3311957 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3311958 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3311957 A) (@lem3311956 A)). Qed.
Lemma lem3311963 {A : Type'} : (term15 A) = (term14 A).
Proof. exact (SYM (@lem3311958 A)). Qed.
Lemma lem3311983 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3311984 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3311983 A s x t). Qed.
Lemma lem3311985 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (t : A -> Prop) : (term18 A x' s x t) = (term19 A s x' x t).
Proof. exact (@lem3311984 A s x' (@INSERT A x t)). Qed.
Lemma lem3311989 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3311990 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3311989 A P x). Qed.
Lemma lem3311991 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3311990 A s x'). Qed.
Lemma lem3311992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3311993 {A : Type'} (s : A -> Prop) (x' : A) : (term20 A x' s) = (term21 A s x').
Proof. exact (MK_COMB (@lem3311992) (@lem3311991 A s x')). Qed.
Lemma lem3311995 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term22 A x y s) = (term23 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3311996 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term22 A x y s) = (term23 A y x s).
Proof. exact (@lem3311995 A y x s). Qed.
Lemma lem3311997 {A : Type'} (x : A) (x' : A) (t : A -> Prop) : (term22 A x' x t) = (term23 A x x' t).
Proof. exact (@lem3311996 A x x' t). Qed.
Lemma lem3312003 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3312004 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3312003 A P x). Qed.
Lemma lem3312005 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3312004 A t x'). Qed.
Lemma lem3312006 {A : Type'} (x' : A) (x : A) : (term24 A x' x) = (term24 A x' x).
Proof. exact (eq_refl (term24 A x' x)). Qed.
Lemma lem3312007 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term23 A x x' t) = (term25 A x t x').
Proof. exact (MK_COMB (@lem3312006 A x' x) (@lem3312005 A t x')). Qed.
Lemma lem3312010 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term22 A x' x t) = (term25 A x t x').
Proof. exact (TRANS (@lem3311997 A x x' t) (@lem3312007 A x t x')). Qed.
Lemma lem3312011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3312012 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term26 A x' x t) = (term27 A x t x').
Proof. exact (MK_COMB (@lem3312011) (@lem3312010 A x t x')). Qed.
Lemma lem3312013 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term19 A s x' x t) = (term28 A s x t x').
Proof. exact (MK_COMB (@lem3311993 A s x') (@lem3312012 A x t x')). Qed.
Lemma lem3312016 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term18 A x' s x t) = (term28 A s x t x').
Proof. exact (TRANS (@lem3311985 A s x' x t) (@lem3312013 A s x t x')). Qed.
Lemma lem3312017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3312018 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term29 A x' s x t) = (term30 A s x t x').
Proof. exact (MK_COMB (@lem3312017) (@lem3312016 A s x t x')). Qed.
Lemma lem3312020 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3312021 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3312020 A s x t). Qed.
Lemma lem3312022 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (t : A -> Prop) : (term31 A x' s x t) = (term32 A s x x' t).
Proof. exact (@lem3312021 A (@DELETE A s x) x' t). Qed.
Lemma lem3312026 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term33 A x s y) = (term34 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3312027 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term33 A x s y) = (term34 A s x y).
Proof. exact (@lem3312026 A s x y). Qed.
Lemma lem3312028 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term33 A x' s x) = (term34 A s x' x).
Proof. exact (@lem3312027 A s x' x). Qed.
Lemma lem3312032 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3312033 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3312032 A P x). Qed.
Lemma lem3312034 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3312033 A s x'). Qed.
Lemma lem3312035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3312036 {A : Type'} (s : A -> Prop) (x' : A) : (term20 A x' s) = (term21 A s x').
Proof. exact (MK_COMB (@lem3312035) (@lem3312034 A s x')). Qed.
Lemma lem3312039 {A : Type'} (x' : A) (x : A) : (term35 A x' x) = (term35 A x' x).
Proof. exact (eq_refl (term35 A x' x)). Qed.
Lemma lem3312040 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term34 A s x' x) = (term36 A s x' x).
Proof. exact (MK_COMB (@lem3312036 A s x') (@lem3312039 A x' x)). Qed.
Lemma lem3312043 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term33 A x' s x) = (term36 A s x' x).
Proof. exact (TRANS (@lem3312028 A s x' x) (@lem3312040 A s x' x)). Qed.
Lemma lem3312044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3312045 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term37 A x' s x) = (term38 A s x' x).
Proof. exact (MK_COMB (@lem3312044) (@lem3312043 A s x' x)). Qed.
Lemma lem3312047 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3312048 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3312047 A P x). Qed.
Lemma lem3312049 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3312048 A t x'). Qed.
Lemma lem3312050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3312051 {A : Type'} (t : A -> Prop) (x' : A) : (term39 A x' t) = (term40 A t x').
Proof. exact (MK_COMB (@lem3312050) (@lem3312049 A t x')). Qed.
Lemma lem3312052 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term32 A s x x' t) = (term41 A s x t x').
Proof. exact (MK_COMB (@lem3312045 A s x' x) (@lem3312051 A t x')). Qed.
Lemma lem3312055 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term31 A x' s x t) = (term41 A s x t x').
Proof. exact (TRANS (@lem3312022 A s x x' t) (@lem3312052 A s x t x')). Qed.
Lemma lem3312056 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : ((term18 A x' s x t) = (term31 A x' s x t)) = ((term28 A s x t x') = (term41 A s x t x')).
Proof. exact (MK_COMB (@lem3312018 A s x t x') (@lem3312055 A s x t x')). Qed.
Lemma lem3312059 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term42 A s x t) = (term43 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3312056 A s x t x')). Qed.
Lemma lem3312060 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3312061 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term3 A s x t) = (term44 A s x t).
Proof. exact (MK_COMB (@lem3312060 A) (@lem3312059 A s x t)). Qed.
Lemma lem3312066 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = (term45 A s t).
Proof. exact (fun_ext (fun x : A => @lem3312061 A s x t)). Qed.
Lemma lem3312067 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3312068 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term46 A s t).
Proof. exact (MK_COMB (@lem3312067 A) (@lem3312066 A s t)). Qed.
Lemma lem3312073 {A : Type'} (s : A -> Prop) : (term9 A s) = (term47 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3312068 A s t)). Qed.
Lemma lem3312074 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3312075 {A : Type'} (s : A -> Prop) : (term11 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3312074 A) (@lem3312073 A s)). Qed.
Lemma lem3312080 {A : Type'} : (term13 A) = (term49 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3312075 A s)). Qed.
Lemma lem3312081 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3312082 {A : Type'} : (term15 A) = (term50 A).
Proof. exact (MK_COMB (@lem3312081 A) (@lem3312080 A)). Qed.
Lemma lem3312087 {A : Type'} : (term50 A) = (term15 A).
Proof. exact (SYM (@lem3312082 A)). Qed.
Lemma lem3312089 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3312090 {A : Type'} : (term50 A) = (term52 A).
Proof. exact (@lem3312089 (term50 A)). Qed.
Lemma lem3312091 {A : Type'} : (term52 A) = (term50 A).
Proof. exact (SYM (@lem3312090 A)). Qed.
Lemma lem3312092 {A : Type'} (h1 : term53 A) : term53 A.
Proof. exact (h1). Qed.
Lemma lem3312095 {A : Type'} (h1 : term52 A) : term52 A.
Proof. exact (h1). Qed.
Lemma lem3312096 {A : Type'} : term54 A.
Proof. exact (fun h0 : term52 A => @lem3312095 A h0). Qed.
Lemma lem3312097 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3312098 {A : Type'} (h1 : term52 A) : term52 A.
Proof. exact (h1). Qed.
Lemma lem3312099 {A : Type'} (h1 : term52 A) (h2 : term54 A) : term52 A.
Proof. exact (@lem3312097 A h2 (@lem3312098 A h1)). Qed.
Lemma lem3312100 {A : Type'} (h1 : term52 A) : term55 A.
Proof. exact (fun h0 : term54 A => @lem3312099 A h1 h0). Qed.
Lemma lem3312101 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3312102 {A : Type'} (h1 : term52 A) (h2 : term54 A) : term52 A.
Proof. exact (@lem3312100 A h1 (@lem3312101 A h2)). Qed.
Lemma lem3312103 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (fun h0 : term52 A => @lem3312102 A h0 h1). Qed.
Lemma lem3312104 {A : Type'} : term56 A.
Proof. exact (fun h0 : term54 A => @lem3312103 A h0). Qed.
Lemma lem3312107 {A : Type'} : term54 A.
Proof. exact (@lem3312104 A (@lem3312096 A)). Qed.
Lemma lem3312108 {A : Type'} : term54 A.
Proof. exact (@lem3312107 A). Qed.
Lemma lem3312110 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3312111 {A : Type'} : (term52 A) = (term57 A).
Proof. exact (@lem3312110 (term53 A)). Qed.
Lemma lem3312113 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3312114 {A : Type'} : (term57 A) = (term50 A).
Proof. exact (@lem3312113 (term50 A)). Qed.
Lemma lem3312143 {A : Type'} : (term52 A) = (term50 A).
Proof. exact (TRANS (@lem3312111 A) (@lem3312114 A)). Qed.
Lemma lem3312170 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : ((term28 A s x t x') = (term41 A s x t x')) = ((term28 A s x t x') = (term41 A s x t x')).
Proof. exact (eq_refl ((term28 A s x t x') = (term41 A s x t x'))). Qed.
Lemma lem3312171 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term43 A s x t) = (term43 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3312170 A s x t x')). Qed.
Lemma lem3312172 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3312173 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term44 A s x t) = (term44 A s x t).
Proof. exact (MK_COMB (@lem3312172 A) (@lem3312171 A s x t)). Qed.
Lemma lem3312174 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term45 A s t) = (term45 A s t).
Proof. exact (fun_ext (fun x : A => @lem3312173 A s x t)). Qed.
Lemma lem3312175 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3312176 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term46 A s t) = (term46 A s t).
Proof. exact (MK_COMB (@lem3312175 A) (@lem3312174 A s t)). Qed.
Lemma lem3312177 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3312176 A s t)). Qed.
Lemma lem3312178 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3312179 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3312178 A) (@lem3312177 A s)). Qed.
Lemma lem3312180 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3312179 A s)). Qed.
Lemma lem3312181 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3312182 {A : Type'} : (term50 A) = (term50 A).
Proof. exact (MK_COMB (@lem3312181 A) (@lem3312180 A)). Qed.
Lemma lem3312217 {A : Type'} : (term52 A) = (term50 A).
Proof. exact (TRANS (@lem3312143 A) (@lem3312182 A)). Qed.
Lemma lem3312218 {A : Type'} : (term50 A) = (term52 A).
Proof. exact (SYM (@lem3312217 A)). Qed.
Lemma lem3312220 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3312221 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : ((term28 A s x t x') = (term41 A s x t x')) = (term59 A s x t x').
Proof. exact (@lem3312220 ((term28 A s x t x') = (term41 A s x t x'))). Qed.
Lemma lem3312222 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term59 A s x t x') = ((term28 A s x t x') = (term41 A s x t x')).
Proof. exact (SYM (@lem3312221 A s x t x')). Qed.
Lemma lem3312223 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term60 A s x t x') : term60 A s x t x'.
Proof. exact (h1). Qed.
Lemma lem3312234 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term27 A x t x') = (term61 A x t x').
Proof. exact (@lem17160 (x' = x) (t x')). Qed.
Lemma lem3312239 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term62 A x t x') = (term25 A x t x').
Proof. exact (@lem16933 (term25 A x t x')). Qed.
Lemma lem3312241 {A : Type'} (s : A -> Prop) (x' : A) : (term63 A s x') = (term63 A s x').
Proof. exact (eq_refl (term63 A s x')). Qed.
Lemma lem3312242 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term64 A s x t x') = (term65 A s x t x').
Proof. exact (MK_COMB (@lem3312241 A s x') (@lem3312239 A x t x')). Qed.
Lemma lem3312243 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term66 A s x t x') = (term64 A s x t x').
Proof. exact (@lem17045 (s x') (term27 A x t x')). Qed.
Lemma lem3312244 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term66 A s x t x') = (term65 A s x t x').
Proof. exact (TRANS (@lem3312243 A s x t x') (@lem3312242 A s x t x')). Qed.
Lemma lem3312246 {A : Type'} (s : A -> Prop) (x' : A) : (term21 A s x') = (term21 A s x').
Proof. exact (eq_refl (term21 A s x')). Qed.
Lemma lem3312247 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term28 A s x t x') = (term67 A s x t x').
Proof. exact (MK_COMB (@lem3312246 A s x') (@lem3312234 A x t x')). Qed.
Lemma lem3312253 {A : Type'} (x' : A) (x : A) : (term68 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3312255 {A : Type'} (s : A -> Prop) (x' : A) : (term63 A s x') = (term63 A s x').
Proof. exact (eq_refl (term63 A s x')). Qed.
Lemma lem3312256 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term69 A s x' x) = (term70 A s x' x).
Proof. exact (MK_COMB (@lem3312255 A s x') (@lem3312253 A x' x)). Qed.
Lemma lem3312257 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term71 A s x' x) = (term69 A s x' x).
Proof. exact (@lem17045 (s x') (term35 A x' x)). Qed.
Lemma lem3312258 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term71 A s x' x) = (term70 A s x' x).
Proof. exact (TRANS (@lem3312257 A s x' x) (@lem3312256 A s x' x)). Qed.
Lemma lem3312265 {A : Type'} (t : A -> Prop) (x' : A) : (term72 A t x') = (t x').
Proof. exact (@lem16933 (t x')). Qed.
Lemma lem3312266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3312267 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term73 A s x' x) = (term74 A s x' x).
Proof. exact (MK_COMB (@lem3312266) (@lem3312258 A s x' x)). Qed.
Lemma lem3312268 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term75 A s x t x') = (term76 A s x t x').
Proof. exact (MK_COMB (@lem3312267 A s x' x) (@lem3312265 A t x')). Qed.
Lemma lem3312269 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term77 A s x t x') = (term75 A s x t x').
Proof. exact (@lem17045 (term36 A s x' x) (term40 A t x')). Qed.
Lemma lem3312270 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term77 A s x t x') = (term76 A s x t x').
Proof. exact (TRANS (@lem3312269 A s x t x') (@lem3312268 A s x t x')). Qed.
Lemma lem3312273 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term41 A s x t x') = (term41 A s x t x').
Proof. exact (eq_refl (term41 A s x t x')). Qed.
Lemma lem3312274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3312275 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term78 A s x t x') = (term79 A s x t x').
Proof. exact (MK_COMB (@lem3312274) (@lem3312244 A s x t x')). Qed.
Lemma lem3312276 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term80 A s x t x') = (term81 A s x t x').
Proof. exact (MK_COMB (@lem3312275 A s x t x') (@lem3312273 A s x t x')). Qed.
Lemma lem3312277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3312278 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term82 A s x t x') = (term83 A s x t x').
Proof. exact (MK_COMB (@lem3312277) (@lem3312247 A s x t x')). Qed.
Lemma lem3312279 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term84 A s x t x') = (term85 A s x t x').
Proof. exact (MK_COMB (@lem3312278 A s x t x') (@lem3312270 A s x t x')). Qed.
Lemma lem3312280 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3312281 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term86 A s x t x') = (term87 A s x t x').
Proof. exact (MK_COMB (@lem3312280) (@lem3312279 A s x t x')). Qed.
Lemma lem3312282 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term88 A s x t x') = (term89 A s x t x').
Proof. exact (MK_COMB (@lem3312281 A s x t x') (@lem3312276 A s x t x')). Qed.
Lemma lem3312283 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term60 A s x t x') = (term88 A s x t x').
Proof. exact (@lem17646 (term28 A s x t x') (term41 A s x t x')). Qed.
Lemma lem3312288 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term60 A s x t x') = (term89 A s x t x').
Proof. exact (TRANS (@lem3312283 A s x t x') (@lem3312282 A s x t x')). Qed.
Lemma lem3312379 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term60 A s x t x') : term89 A s x t x'.
Proof. exact (EQ_MP (@lem3312288 A s x t x') (@lem3312223 A s x t x' h1)). Qed.
Lemma lem3312380 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : term85 A s x t x'.
Proof. exact (h1). Qed.
Lemma lem3312381 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : term81 A s x t x'.
Proof. exact (h1). Qed.
Lemma lem3312382 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : term76 A s x t x'.
Proof. exact (proj2 (@lem3312380 A s x t x' h1)). Qed.
Lemma lem3312383 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : term67 A s x t x'.
Proof. exact (proj1 (@lem3312380 A s x t x' h1)). Qed.
Lemma lem3312384 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : term61 A x t x'.
Proof. exact (proj2 (@lem3312383 A s x t x' h1)). Qed.
Lemma lem3312388 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A s x' x) : term70 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3312392 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : term41 A s x t x'.
Proof. exact (proj2 (@lem3312381 A s x t x' h1)). Qed.
Lemma lem3312393 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : term65 A s x t x'.
Proof. exact (proj1 (@lem3312381 A s x t x' h1)). Qed.
Lemma lem3312395 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : term36 A s x' x.
Proof. exact (proj1 (@lem3312392 A s x t x' h1)). Qed.
Lemma lem3312399 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term25 A x t x') : term25 A x t x'.
Proof. exact (h1). Qed.
Lemma lem3312417 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term40 A s x') : term40 A s x'.
Proof. exact (h1). Qed.
Lemma lem3312433 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3312449 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3312465 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term40 A s x') : term40 A s x'.
Proof. exact (h1). Qed.
Lemma lem3312481 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3312497 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3312505 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term40 A s x') : term40 A s x'.
Proof. exact (h1). Qed.
Lemma lem3312509 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : term35 A x' x.
Proof. exact (proj1 (@lem3312384 A s x t x' h1)). Qed.
Lemma lem3312513 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3312519 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : term40 A t x'.
Proof. exact (proj2 (@lem3312384 A s x t x' h1)). Qed.
Lemma lem3312521 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3312529 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term40 A s x') : term40 A s x'.
Proof. exact (h1). Qed.
Lemma lem3312535 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : term35 A x' x.
Proof. exact (proj2 (@lem3312395 A s x t x' h1)). Qed.
Lemma lem3312537 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3312539 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : term40 A t x'.
Proof. exact (proj2 (@lem3312392 A s x t x' h1)). Qed.
Lemma lem3312545 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3312573 {A : Type'} (x : A) : (term90 A x) = (term90 A x).
Proof. exact (eq_refl (term90 A x)). Qed.
Lemma lem3312574 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term91 A x x') = (term92 A x).
Proof. exact (MK_COMB (@lem3312573 A x) (@lem3312513 A x' x h1)). Qed.
Lemma lem3312575 {A : Type'} (x : A) : (term92 A x) = (term93 A x).
Proof. exact (eq_refl (term92 A x)). Qed.
Lemma lem3312576 {A : Type'} (x : A) (x' : A) : (term94 A x x') = (term94 A x x').
Proof. exact (eq_refl (term94 A x x')). Qed.
Lemma lem3312577 {A : Type'} (x' : A) (x : A) : ((term91 A x x') = (term92 A x)) = ((term91 A x x') = (term93 A x)).
Proof. exact (MK_COMB (@lem3312576 A x x') (@lem3312575 A x)). Qed.
Lemma lem3312578 {A : Type'} (x' : A) (x : A) : (term91 A x x') = (term35 A x' x).
Proof. exact (eq_refl (term91 A x x')). Qed.
Lemma lem3312579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3312580 {A : Type'} (x' : A) (x : A) : (term94 A x x') = (term95 A x' x).
Proof. exact (MK_COMB (@lem3312579) (@lem3312578 A x' x)). Qed.
Lemma lem3312581 {A : Type'} (x : A) : (term93 A x) = (term93 A x).
Proof. exact (eq_refl (term93 A x)). Qed.
Lemma lem3312582 {A : Type'} (x' : A) (x : A) : ((term91 A x x') = (term93 A x)) = ((term35 A x' x) = (term93 A x)).
Proof. exact (MK_COMB (@lem3312580 A x' x) (@lem3312581 A x)). Qed.
Lemma lem3312583 {A : Type'} (x' : A) (x : A) : ((term91 A x x') = (term92 A x)) = ((term35 A x' x) = (term93 A x)).
Proof. exact (TRANS (@lem3312577 A x' x) (@lem3312582 A x' x)). Qed.
Lemma lem3312584 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term35 A x' x) = (term93 A x).
Proof. exact (EQ_MP (@lem3312583 A x' x) (@lem3312574 A x' x h1)). Qed.
Lemma lem3312585 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : term93 A x.
Proof. exact (EQ_MP (@lem3312584 A x' x h2) (@lem3312509 A s x t x' h1)). Qed.
Lemma lem3312639 {A : Type'} (x : A) : (term90 A x) = (term90 A x).
Proof. exact (eq_refl (term90 A x)). Qed.
Lemma lem3312640 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term91 A x x') = (term92 A x).
Proof. exact (MK_COMB (@lem3312639 A x) (@lem3312537 A x' x h1)). Qed.
Lemma lem3312641 {A : Type'} (x : A) : (term92 A x) = (term93 A x).
Proof. exact (eq_refl (term92 A x)). Qed.
Lemma lem3312642 {A : Type'} (x : A) (x' : A) : (term94 A x x') = (term94 A x x').
Proof. exact (eq_refl (term94 A x x')). Qed.
Lemma lem3312643 {A : Type'} (x' : A) (x : A) : ((term91 A x x') = (term92 A x)) = ((term91 A x x') = (term93 A x)).
Proof. exact (MK_COMB (@lem3312642 A x x') (@lem3312641 A x)). Qed.
Lemma lem3312644 {A : Type'} (x' : A) (x : A) : (term91 A x x') = (term35 A x' x).
Proof. exact (eq_refl (term91 A x x')). Qed.
Lemma lem3312645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3312646 {A : Type'} (x' : A) (x : A) : (term94 A x x') = (term95 A x' x).
Proof. exact (MK_COMB (@lem3312645) (@lem3312644 A x' x)). Qed.
Lemma lem3312647 {A : Type'} (x : A) : (term93 A x) = (term93 A x).
Proof. exact (eq_refl (term93 A x)). Qed.
Lemma lem3312648 {A : Type'} (x' : A) (x : A) : ((term91 A x x') = (term93 A x)) = ((term35 A x' x) = (term93 A x)).
Proof. exact (MK_COMB (@lem3312646 A x' x) (@lem3312647 A x)). Qed.
Lemma lem3312649 {A : Type'} (x' : A) (x : A) : ((term91 A x x') = (term92 A x)) = ((term35 A x' x) = (term93 A x)).
Proof. exact (TRANS (@lem3312643 A x' x) (@lem3312648 A x' x)). Qed.
Lemma lem3312650 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term35 A x' x) = (term93 A x).
Proof. exact (EQ_MP (@lem3312649 A x' x) (@lem3312640 A x' x h1)). Qed.
Lemma lem3312651 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : term93 A x.
Proof. exact (EQ_MP (@lem3312650 A x' x h2) (@lem3312535 A s x t x' h1)). Qed.
Lemma lem3312679 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : s x'.
Proof. exact (proj1 (@lem3312383 A s x t x' h1)). Qed.
Lemma lem3312680 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : term96 A s x'.
Proof. exact (fun h0 : term40 A s x' => @lem3312679 A s x t x' h1). Qed.
Lemma lem3312682 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312683 {A : Type'} (s : A -> Prop) (x' : A) : (term96 A s x') = (s x').
Proof. exact (@lem3312682 (s x')). Qed.
Lemma lem3312684 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : s x'.
Proof. exact (EQ_MP (@lem3312683 A s x') (@lem3312680 A s x t x' h1)). Qed.
Lemma lem3312687 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3312689 {A : Type'} (s : A -> Prop) (x' : A) : (term40 A s x') = (term98 A s x').
Proof. exact (@lem3312687 (s x')). Qed.
Lemma lem3312692 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term40 A s x') : term98 A s x'.
Proof. exact (EQ_MP (@lem3312689 A s x') (@lem3312505 A s x' h1)). Qed.
Lemma lem3312695 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term85 A s x t x') : False.
Proof. exact (@lem3312692 A s x' h1 (@lem3312684 A s x t x' h2)). Qed.
Lemma lem3312696 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term85 A s x t x') : term99.
Proof. exact (fun h0 : ~ False => @lem3312695 A s x t x' h1 h2). Qed.
Lemma lem3312698 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312699 : term99 = False.
Proof. exact (@lem3312698 False). Qed.
Lemma lem3312700 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term85 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312699) (@lem3312696 A s x t x' h1 h2)). Qed.
Lemma lem3312728 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3312729 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3312728 A x). Qed.
Lemma lem3312730 {A : Type'} (x : A) : term100 A x.
Proof. exact (fun h0 : term93 A x => @lem3312729 A x). Qed.
Lemma lem3312732 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312733 {A : Type'} (x : A) : (term100 A x) = (x = x).
Proof. exact (@lem3312732 (x = x)). Qed.
Lemma lem3312734 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3312733 A x) (@lem3312730 A x)). Qed.
Lemma lem3312737 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3312739 {A : Type'} (x : A) : (term93 A x) = (term101 A x).
Proof. exact (@lem3312737 (x = x)). Qed.
Lemma lem3312742 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : term101 A x.
Proof. exact (EQ_MP (@lem3312739 A x) (@lem3312585 A s t x' x h1 h2)). Qed.
Lemma lem3312745 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : False.
Proof. exact (@lem3312742 A s t x' x h1 h2 (@lem3312734 A x)). Qed.
Lemma lem3312746 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : term99.
Proof. exact (fun h0 : ~ False => @lem3312745 A s t x' x h1 h2). Qed.
Lemma lem3312748 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312749 : term99 = False.
Proof. exact (@lem3312748 False). Qed.
Lemma lem3312778 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3312779 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term96 A t x'.
Proof. exact (fun h0 : term40 A t x' => @lem3312778 A t x' h1). Qed.
Lemma lem3312781 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312782 {A : Type'} (t : A -> Prop) (x' : A) : (term96 A t x') = (t x').
Proof. exact (@lem3312781 (t x')). Qed.
Lemma lem3312783 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3312782 A t x') (@lem3312779 A t x' h1)). Qed.
Lemma lem3312786 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3312788 {A : Type'} (t : A -> Prop) (x' : A) : (term40 A t x') = (term98 A t x').
Proof. exact (@lem3312786 (t x')). Qed.
Lemma lem3312791 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : term98 A t x'.
Proof. exact (EQ_MP (@lem3312788 A t x') (@lem3312519 A s x t x' h1)). Qed.
Lemma lem3312794 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term85 A s x t x') : False.
Proof. exact (@lem3312791 A s x t x' h2 (@lem3312783 A t x' h1)). Qed.
Lemma lem3312795 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term85 A s x t x') : term99.
Proof. exact (fun h0 : ~ False => @lem3312794 A s x t x' h1 h2). Qed.
Lemma lem3312797 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312798 : term99 = False.
Proof. exact (@lem3312797 False). Qed.
Lemma lem3312799 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term85 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312798) (@lem3312795 A s x t x' h1 h2)). Qed.
Lemma lem3312827 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : s x'.
Proof. exact (proj1 (@lem3312395 A s x t x' h1)). Qed.
Lemma lem3312828 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : term96 A s x'.
Proof. exact (fun h0 : term40 A s x' => @lem3312827 A s x t x' h1). Qed.
Lemma lem3312830 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312831 {A : Type'} (s : A -> Prop) (x' : A) : (term96 A s x') = (s x').
Proof. exact (@lem3312830 (s x')). Qed.
Lemma lem3312832 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : s x'.
Proof. exact (EQ_MP (@lem3312831 A s x') (@lem3312828 A s x t x' h1)). Qed.
Lemma lem3312835 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3312837 {A : Type'} (s : A -> Prop) (x' : A) : (term40 A s x') = (term98 A s x').
Proof. exact (@lem3312835 (s x')). Qed.
Lemma lem3312840 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term40 A s x') : term98 A s x'.
Proof. exact (EQ_MP (@lem3312837 A s x') (@lem3312529 A s x' h1)). Qed.
Lemma lem3312843 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term81 A s x t x') : False.
Proof. exact (@lem3312840 A s x' h1 (@lem3312832 A s x t x' h2)). Qed.
Lemma lem3312844 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term81 A s x t x') : term99.
Proof. exact (fun h0 : ~ False => @lem3312843 A s x t x' h1 h2). Qed.
Lemma lem3312846 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312847 : term99 = False.
Proof. exact (@lem3312846 False). Qed.
Lemma lem3312848 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term81 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312847) (@lem3312844 A s x t x' h1 h2)). Qed.
Lemma lem3312876 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3312877 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3312876 A x). Qed.
Lemma lem3312878 {A : Type'} (x : A) : term100 A x.
Proof. exact (fun h0 : term93 A x => @lem3312877 A x). Qed.
Lemma lem3312880 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312881 {A : Type'} (x : A) : (term100 A x) = (x = x).
Proof. exact (@lem3312880 (x = x)). Qed.
Lemma lem3312882 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3312881 A x) (@lem3312878 A x)). Qed.
Lemma lem3312885 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3312887 {A : Type'} (x : A) : (term93 A x) = (term101 A x).
Proof. exact (@lem3312885 (x = x)). Qed.
Lemma lem3312890 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : term101 A x.
Proof. exact (EQ_MP (@lem3312887 A x) (@lem3312651 A s t x' x h1 h2)). Qed.
Lemma lem3312893 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : False.
Proof. exact (@lem3312890 A s t x' x h1 h2 (@lem3312882 A x)). Qed.
Lemma lem3312894 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : term99.
Proof. exact (fun h0 : ~ False => @lem3312893 A s t x' x h1 h2). Qed.
Lemma lem3312896 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312897 : term99 = False.
Proof. exact (@lem3312896 False). Qed.
Lemma lem3312926 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3312927 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term96 A t x'.
Proof. exact (fun h0 : term40 A t x' => @lem3312926 A t x' h1). Qed.
Lemma lem3312929 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312930 {A : Type'} (t : A -> Prop) (x' : A) : (term96 A t x') = (t x').
Proof. exact (@lem3312929 (t x')). Qed.
Lemma lem3312931 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3312930 A t x') (@lem3312927 A t x' h1)). Qed.
Lemma lem3312934 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3312936 {A : Type'} (t : A -> Prop) (x' : A) : (term40 A t x') = (term98 A t x').
Proof. exact (@lem3312934 (t x')). Qed.
Lemma lem3312939 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : term98 A t x'.
Proof. exact (EQ_MP (@lem3312936 A t x') (@lem3312539 A s x t x' h1)). Qed.
Lemma lem3312942 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term81 A s x t x') : False.
Proof. exact (@lem3312939 A s x t x' h2 (@lem3312931 A t x' h1)). Qed.
Lemma lem3312943 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term81 A s x t x') : term99.
Proof. exact (fun h0 : ~ False => @lem3312942 A s x t x' h1 h2). Qed.
Lemma lem3312945 (p : Prop) : (term97 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3312946 : term99 = False.
Proof. exact (@lem3312945 False). Qed.
Lemma lem3312947 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term81 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312946) (@lem3312943 A s x t x' h1 h2)). Qed.
Lemma lem3312948 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3312897) (@lem3312894 A s t x' x h1 h2)). Qed.
Lemma lem3312949 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3312749) (@lem3312746 A s t x' x h1 h2)). Qed.
Lemma lem3312950 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term81 A s x t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3312947 A s x t x' h1 h2) (fun h3 : False => @lem3312545 A t x' h1)). Qed.
Lemma lem3312951 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term81 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312950 A s x t x' h1 h2) (@lem3312545 A t x' h1)). Qed.
Lemma lem3312952 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3312948 A s t x' x h1 h2) (fun h3 : False => @lem3312537 A x' x h2)). Qed.
Lemma lem3312953 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3312952 A s t x' x h1 h2) (@lem3312537 A x' x h2)). Qed.
Lemma lem3312954 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term81 A s x t x') : (term40 A s x') = False.
Proof. exact (prop_ext (fun h3 : term40 A s x' => @lem3312848 A s x t x' h1 h2) (fun h3 : False => @lem3312529 A s x' h1)). Qed.
Lemma lem3312955 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term81 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312954 A s x t x' h1 h2) (@lem3312529 A s x' h1)). Qed.
Lemma lem3312956 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term85 A s x t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3312799 A s x t x' h1 h2) (fun h3 : False => @lem3312521 A t x' h1)). Qed.
Lemma lem3312957 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term85 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312956 A s x t x' h1 h2) (@lem3312521 A t x' h1)). Qed.
Lemma lem3312958 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3312949 A s t x' x h1 h2) (fun h3 : False => @lem3312513 A x' x h2)). Qed.
Lemma lem3312959 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3312958 A s t x' x h1 h2) (@lem3312513 A x' x h2)). Qed.
Lemma lem3312960 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term85 A s x t x') : (term40 A s x') = False.
Proof. exact (prop_ext (fun h3 : term40 A s x' => @lem3312700 A s x t x' h1 h2) (fun h3 : False => @lem3312505 A s x' h1)). Qed.
Lemma lem3312961 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term85 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312960 A s x t x' h1 h2) (@lem3312505 A s x' h1)). Qed.
Lemma lem3312962 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term81 A s x t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3312951 A s x t x' h1 h2) (fun h3 : False => @lem3312497 A t x' h1)). Qed.
Lemma lem3312963 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term81 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312962 A s x t x' h1 h2) (@lem3312497 A t x' h1)). Qed.
Lemma lem3312964 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3312953 A s t x' x h1 h2) (fun h3 : False => @lem3312481 A x' x h2)). Qed.
Lemma lem3312965 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3312964 A s t x' x h1 h2) (@lem3312481 A x' x h2)). Qed.
Lemma lem3312966 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term81 A s x t x') : (term40 A s x') = False.
Proof. exact (prop_ext (fun h3 : term40 A s x' => @lem3312955 A s x t x' h1 h2) (fun h3 : False => @lem3312465 A s x' h1)). Qed.
Lemma lem3312967 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term81 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312966 A s x t x' h1 h2) (@lem3312465 A s x' h1)). Qed.
Lemma lem3312968 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term85 A s x t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3312957 A s x t x' h1 h2) (fun h3 : False => @lem3312449 A t x' h1)). Qed.
Lemma lem3312969 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term85 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312968 A s x t x' h1 h2) (@lem3312449 A t x' h1)). Qed.
Lemma lem3312970 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3312959 A s t x' x h1 h2) (fun h3 : False => @lem3312433 A x' x h2)). Qed.
Lemma lem3312971 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3312970 A s t x' x h1 h2) (@lem3312433 A x' x h2)). Qed.
Lemma lem3312972 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term85 A s x t x') : (term40 A s x') = False.
Proof. exact (prop_ext (fun h3 : term40 A s x' => @lem3312961 A s x t x' h1 h2) (fun h3 : False => @lem3312417 A s x' h1)). Qed.
Lemma lem3312973 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term85 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312972 A s x t x' h1 h2) (@lem3312417 A s x' h1)). Qed.
Lemma lem3312974 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term81 A s x t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3312963 A s x t x' h1 h2) (fun h3 : False => @lem3312497 A t x' h1)). Qed.
Lemma lem3312975 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term81 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312974 A s x t x' h1 h2) (@lem3312497 A t x' h1)). Qed.
Lemma lem3312976 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3312965 A s t x' x h1 h2) (fun h3 : False => @lem3312481 A x' x h2)). Qed.
Lemma lem3312977 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3312976 A s t x' x h1 h2) (@lem3312481 A x' x h2)). Qed.
Lemma lem3312978 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term81 A s x t x') : (term40 A s x') = False.
Proof. exact (prop_ext (fun h3 : term40 A s x' => @lem3312967 A s x t x' h1 h2) (fun h3 : False => @lem3312465 A s x' h1)). Qed.
Lemma lem3312979 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term81 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312978 A s x t x' h1 h2) (@lem3312465 A s x' h1)). Qed.
Lemma lem3312980 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term85 A s x t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3312969 A s x t x' h1 h2) (fun h3 : False => @lem3312449 A t x' h1)). Qed.
Lemma lem3312981 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term85 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312980 A s x t x' h1 h2) (@lem3312449 A t x' h1)). Qed.
Lemma lem3312982 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3312971 A s t x' x h1 h2) (fun h3 : False => @lem3312433 A x' x h2)). Qed.
Lemma lem3312983 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3312982 A s t x' x h1 h2) (@lem3312433 A x' x h2)). Qed.
Lemma lem3312984 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term85 A s x t x') : (term40 A s x') = False.
Proof. exact (prop_ext (fun h3 : term40 A s x' => @lem3312973 A s x t x' h1 h2) (fun h3 : False => @lem3312417 A s x' h1)). Qed.
Lemma lem3312985 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term40 A s x') (h2 : term85 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312984 A s x t x' h1 h2) (@lem3312417 A s x' h1)). Qed.
Lemma lem3312986 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') (h2 : term25 A x t x') : False.
Proof. exact (or_elim (@lem3312399 A x t x' h2) (fun h0 : x' = x => @lem3312977 A s t x' x h1 h0) (fun h0 : t x' => @lem3312975 A s x t x' h0 h1)). Qed.
Lemma lem3312987 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term81 A s x t x') : False.
Proof. exact (or_elim (@lem3312393 A s x t x' h1) (fun h0 : term40 A s x' => @lem3312979 A s x t x' h0 h1) (fun h0 : term25 A x t x' => @lem3312986 A s x t x' h1 h0)). Qed.
Lemma lem3312988 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (x : A) (h1 : term85 A s x t x') (h2 : term70 A s x' x) : False.
Proof. exact (or_elim (@lem3312388 A s x' x h2) (fun h0 : term40 A s x' => @lem3312985 A s x t x' h0 h1) (fun h0 : x' = x => @lem3312983 A s t x' x h1 h0)). Qed.
Lemma lem3312989 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term85 A s x t x') : False.
Proof. exact (or_elim (@lem3312382 A s x t x' h1) (fun h0 : term70 A s x' x => @lem3312988 A t s x' x h1 h0) (fun h0 : t x' => @lem3312981 A s x t x' h0 h1)). Qed.
Lemma lem3312990 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term60 A s x t x') : False.
Proof. exact (or_elim (@lem3312379 A s x t x' h1) (fun h0 : term85 A s x t x' => @lem3312989 A s x t x' h0) (fun h0 : term81 A s x t x' => @lem3312987 A s x t x' h0)). Qed.
Lemma lem3312991 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term60 A s x t x') : (term60 A s x t x') = False.
Proof. exact (prop_ext (fun h2 : term60 A s x t x' => @lem3312990 A s x t x' h1) (fun h2 : False => @lem3312223 A s x t x' h1)). Qed.
Lemma lem3312992 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term60 A s x t x') : False.
Proof. exact (EQ_MP (@lem3312991 A s x t x' h1) (@lem3312223 A s x t x' h1)). Qed.
Lemma lem3312993 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : term59 A s x t x'.
Proof. exact (fun h0 : term60 A s x t x' => @lem3312992 A s x t x' h0). Qed.
Lemma lem3312994 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term28 A s x t x') = (term41 A s x t x').
Proof. exact (EQ_MP (@lem3312222 A s x t x') (@lem3312993 A s x t x')). Qed.
Lemma lem3312999 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term44 A s x t.
Proof. exact (fun x' : A => @lem3312994 A s x t x'). Qed.
Lemma lem3313004 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term46 A s t.
Proof. exact (fun x : A => @lem3312999 A s x t). Qed.
Lemma lem3313009 {A : Type'} (s : A -> Prop) : term48 A s.
Proof. exact (fun t : A -> Prop => @lem3313004 A s t). Qed.
Lemma lem3313014 {A : Type'} : term50 A.
Proof. exact (fun s : A -> Prop => @lem3313009 A s). Qed.
Lemma lem3313015 {A : Type'} : term52 A.
Proof. exact (EQ_MP (@lem3312218 A) (@lem3313014 A)). Qed.
Lemma lem3313017 {A : Type'} : term52 A.
Proof. exact (@lem3312108 A (@lem3313015 A)). Qed.
Lemma lem3313018 {A : Type'} (h1 : term53 A) : False.
Proof. exact (@lem3313017 A (@lem3312092 A h1)). Qed.
Lemma lem3313019 {A : Type'} (h1 : term53 A) : (term53 A) = False.
Proof. exact (prop_ext (fun h2 : term53 A => @lem3313018 A h1) (fun h2 : False => @lem3312092 A h1)). Qed.
Lemma lem3313020 {A : Type'} (h1 : term53 A) : False.
Proof. exact (EQ_MP (@lem3313019 A h1) (@lem3312092 A h1)). Qed.
Lemma lem3313021 {A : Type'} : term52 A.
Proof. exact (fun h0 : term53 A => @lem3313020 A h0). Qed.
Lemma lem3313022 {A : Type'} : term50 A.
Proof. exact (EQ_MP (@lem3312091 A) (@lem3313021 A)). Qed.
Lemma lem3313023 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3312087 A) (@lem3313022 A)). Qed.
Lemma lem3313024 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3311963 A) (@lem3313023 A)). Qed.
