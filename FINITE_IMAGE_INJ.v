Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_IMAGE_INJ_term_abbrevs.
Require Import FINITE_IMAGE_INJ_GENERAL_spec.
Require Import IN_UNIV_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem3618991 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem3618992 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3618993 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem3618992 A x) (@lem3618991 A x)). Qed.
Lemma lem3618994 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem3618996 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem3616275 A B f). Qed.
Lemma lem3618997 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem3618998 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem3618997 A B f) (@lem3618996 A B f)). Qed.
Lemma lem3618999 {A B : Type'} (f : A -> B) (A' : B -> Prop) : term3 A B f A'.
Proof. exact (@lem3618998 A B f A'). Qed.
Lemma lem3619000 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term3 A B f A') = (term4 A B f A').
Proof. exact (eq_refl (term3 A B f A')). Qed.
Lemma lem3619001 {A B : Type'} (f : A -> B) (A' : B -> Prop) : term4 A B f A'.
Proof. exact (EQ_MP (@lem3619000 A B f A') (@lem3618999 A B f A')). Qed.
Lemma lem3619002 {A B : Type'} (f : A -> B) (A' : B -> Prop) : term5 A B f A'.
Proof. exact (@lem3619001 A B f A' (@UNIV A)). Qed.
Lemma lem3619003 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term5 A B f A') = (term6 A B f A').
Proof. exact (eq_refl (term5 A B f A')). Qed.
Lemma lem3619004 {A B : Type'} (f : A -> B) (A' : B -> Prop) : term6 A B f A'.
Proof. exact (EQ_MP (@lem3619003 A B f A') (@lem3619002 A B f A')). Qed.
Lemma lem3619024 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3618994 A x) (@lem3618993 A x)). Qed.
Lemma lem3619025 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3619024 A x). Qed.
Lemma lem3619026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3619027 {A : Type'} (x : A) : (term7 A x) = (and True).
Proof. exact (MK_COMB (@lem3619026) (@lem3619025 A x)). Qed.
Lemma lem3619031 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3618994 A x) (@lem3618993 A x)). Qed.
Lemma lem3619032 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3619031 A x). Qed.
Lemma lem3619033 {A : Type'} (y : A) : (@IN A y (@UNIV A)) = True.
Proof. exact (@lem3619032 A y). Qed.
Lemma lem3619034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3619035 {A : Type'} (y : A) : (term7 A y) = (and True).
Proof. exact (MK_COMB (@lem3619034) (@lem3619033 A y)). Qed.
Lemma lem3619038 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3619039 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term8 A B x f y) = (term9 A B x f y).
Proof. exact (MK_COMB (@lem3619035 A y) (@lem3619038 A B x f y)). Qed.
Lemma lem3619041 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3619042 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term9 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem3619041 ((f x) = (f y))). Qed.
Lemma lem3619045 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term8 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem3619039 A B x f y) (@lem3619042 A B x f y)). Qed.
Lemma lem3619046 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term10 A B x f y) = (term9 A B x f y).
Proof. exact (MK_COMB (@lem3619027 A x) (@lem3619045 A B x f y)). Qed.
Lemma lem3619048 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3619049 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term9 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem3619048 ((f x) = (f y))). Qed.
Lemma lem3619052 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term10 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem3619046 A B x f y) (@lem3619049 A B x f y)). Qed.
Lemma lem3619053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619054 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term11 A B x f y) = (term12 A B x f y).
Proof. exact (MK_COMB (@lem3619053) (@lem3619052 A B x f y)). Qed.
Lemma lem3619057 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3619058 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term13 A B f x y) = (term14 A B f x y).
Proof. exact (MK_COMB (@lem3619054 A B x f y) (@lem3619057 A x y)). Qed.
Lemma lem3619063 {A B : Type'} (f : A -> B) (x : A) : (term15 A B f x) = (term16 A B f x).
Proof. exact (fun_ext (fun y : A => @lem3619058 A B f x y)). Qed.
Lemma lem3619064 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3619065 {A B : Type'} (f : A -> B) (x : A) : (term17 A B f x) = (term18 A B f x).
Proof. exact (MK_COMB (@lem3619064 A) (@lem3619063 A B f x)). Qed.
Lemma lem3619070 {A B : Type'} (f : A -> B) : (term19 A B f) = (term20 A B f).
Proof. exact (fun_ext (fun x : A => @lem3619065 A B f x)). Qed.
Lemma lem3619071 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3619072 {A B : Type'} (f : A -> B) : (term21 A B f) = (term22 A B f).
Proof. exact (MK_COMB (@lem3619071 A) (@lem3619070 A B f)). Qed.
Lemma lem3619077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3619078 {A B : Type'} (f : A -> B) : (term23 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3619077) (@lem3619072 A B f)). Qed.
Lemma lem3619079 {B : Type'} (A : B -> Prop) : (@FINITE B A) = (@FINITE B A).
Proof. exact (eq_refl (@FINITE B A)). Qed.
Lemma lem3619080 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term25 A B f A') = (term26 A B f A').
Proof. exact (MK_COMB (@lem3619078 A B f) (@lem3619079 B A')). Qed.
Lemma lem3619083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619084 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term27 A B f A') = (term28 A B f A').
Proof. exact (MK_COMB (@lem3619083) (@lem3619080 A B f A')). Qed.
Lemma lem3619092 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3618994 A x) (@lem3618993 A x)). Qed.
Lemma lem3619093 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3619092 A x). Qed.
Lemma lem3619094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3619095 {A : Type'} (x : A) : (term7 A x) = (and True).
Proof. exact (MK_COMB (@lem3619094) (@lem3619093 A x)). Qed.
Lemma lem3619096 {A B : Type'} (f : A -> B) (x : A) (A' : B -> Prop) : (term29 A B f x A') = (term29 A B f x A').
Proof. exact (eq_refl (term29 A B f x A')). Qed.
Lemma lem3619097 {A B : Type'} (f : A -> B) (x : A) (A' : B -> Prop) : (term30 A B f x A') = (term31 A B f x A').
Proof. exact (MK_COMB (@lem3619095 A x) (@lem3619096 A B f x A')). Qed.
Lemma lem3619099 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3619100 {A B : Type'} (f : A -> B) (x : A) (A' : B -> Prop) : (term31 A B f x A') = (term29 A B f x A').
Proof. exact (@lem3619099 (term29 A B f x A')). Qed.
Lemma lem3619101 {A B : Type'} (f : A -> B) (x : A) (A' : B -> Prop) : (term30 A B f x A') = (term29 A B f x A').
Proof. exact (TRANS (@lem3619097 A B f x A') (@lem3619100 A B f x A')). Qed.
Lemma lem3619102 {A : Type'} (GEN_PVAR_95 : A) : (@SETSPEC A GEN_PVAR_95) = (@SETSPEC A GEN_PVAR_95).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_95)). Qed.
Lemma lem3619103 {A B : Type'} (GEN_PVAR_95 : A) (f : A -> B) (x : A) (A' : B -> Prop) : (term32 A B GEN_PVAR_95 f x A') = (term33 A B GEN_PVAR_95 f x A').
Proof. exact (MK_COMB (@lem3619102 A GEN_PVAR_95) (@lem3619101 A B f x A')). Qed.
Lemma lem3619104 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3619105 {A B : Type'} (GEN_PVAR_95 : A) (f : A -> B) (A' : B -> Prop) (x : A) : (term34 A B GEN_PVAR_95 f A' x) = (term35 A B GEN_PVAR_95 f A' x).
Proof. exact (MK_COMB (@lem3619103 A B GEN_PVAR_95 f x A') (@lem3619104 A x)). Qed.
Lemma lem3619106 {A B : Type'} (GEN_PVAR_95 : A) (f : A -> B) (A' : B -> Prop) : (term36 A B GEN_PVAR_95 f A') = (term37 A B GEN_PVAR_95 f A').
Proof. exact (fun_ext (fun x : A => @lem3619105 A B GEN_PVAR_95 f A' x)). Qed.
Lemma lem3619107 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3619108 {A B : Type'} (GEN_PVAR_95 : A) (f : A -> B) (A' : B -> Prop) : (term38 A B GEN_PVAR_95 f A') = (term39 A B GEN_PVAR_95 f A').
Proof. exact (MK_COMB (@lem3619107 A) (@lem3619106 A B GEN_PVAR_95 f A')). Qed.
Lemma lem3619113 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term40 A B f A') = (term41 A B f A').
Proof. exact (fun_ext (fun GEN_PVAR_95 : A => @lem3619108 A B GEN_PVAR_95 f A')). Qed.
Lemma lem3619114 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3619115 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term42 A B f A') = (term43 A B f A').
Proof. exact (MK_COMB (@lem3619114 A) (@lem3619113 A B f A')). Qed.
Lemma lem3619116 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3619117 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term44 A B f A') = (term45 A B f A').
Proof. exact (MK_COMB (@lem3619116 A) (@lem3619115 A B f A')). Qed.
Lemma lem3619118 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term6 A B f A') = (term46 A B f A').
Proof. exact (MK_COMB (@lem3619084 A B f A') (@lem3619117 A B f A')). Qed.
Lemma lem3619121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619122 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term47 A B f A') = (term48 A B f A').
Proof. exact (MK_COMB (@lem3619121) (@lem3619118 A B f A')). Qed.
Lemma lem3619147 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term46 A B f A') = (term46 A B f A').
Proof. exact (eq_refl (term46 A B f A')). Qed.
Lemma lem3619148 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term49 A B f A') = (term50 A B f A').
Proof. exact (MK_COMB (@lem3619122 A B f A') (@lem3619147 A B f A')). Qed.
Lemma lem3619150 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3619151 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term50 A B f A') = True.
Proof. exact (@lem3619150 (term46 A B f A')). Qed.
Lemma lem3619154 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term51 A B f A') = (term51 A B f A').
Proof. exact (eq_refl (term51 A B f A')). Qed.
Lemma lem3619155 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term51 A B f A') = ((term50 A B f A') = True).
Proof. exact (eq_refl (term51 A B f A')). Qed.
Lemma lem3619156 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term52 A B f A') = (term52 A B f A').
Proof. exact (eq_refl (term52 A B f A')). Qed.
Lemma lem3619157 {A B : Type'} (f : A -> B) (A' : B -> Prop) : ((term51 A B f A') = (term51 A B f A')) = ((term51 A B f A') = ((term50 A B f A') = True)).
Proof. exact (MK_COMB (@lem3619156 A B f A') (@lem3619155 A B f A')). Qed.
Lemma lem3619158 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term51 A B f A') = ((term50 A B f A') = True).
Proof. exact (eq_refl (term51 A B f A')). Qed.
Lemma lem3619159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3619160 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term52 A B f A') = (term53 A B f A').
Proof. exact (MK_COMB (@lem3619159) (@lem3619158 A B f A')). Qed.
Lemma lem3619161 {A B : Type'} (f : A -> B) (A' : B -> Prop) : ((term50 A B f A') = True) = ((term50 A B f A') = True).
Proof. exact (eq_refl ((term50 A B f A') = True)). Qed.
Lemma lem3619162 {A B : Type'} (f : A -> B) (A' : B -> Prop) : ((term51 A B f A') = ((term50 A B f A') = True)) = (((term50 A B f A') = True) = ((term50 A B f A') = True)).
Proof. exact (MK_COMB (@lem3619160 A B f A') (@lem3619161 A B f A')). Qed.
Lemma lem3619163 {A B : Type'} (f : A -> B) (A' : B -> Prop) : ((term51 A B f A') = (term51 A B f A')) = (((term50 A B f A') = True) = ((term50 A B f A') = True)).
Proof. exact (TRANS (@lem3619157 A B f A') (@lem3619162 A B f A')). Qed.
Lemma lem3619164 {A B : Type'} (f : A -> B) (A' : B -> Prop) : ((term50 A B f A') = True) = ((term50 A B f A') = True).
Proof. exact (EQ_MP (@lem3619163 A B f A') (@lem3619154 A B f A')). Qed.
Lemma lem3619165 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term50 A B f A') = True.
Proof. exact (EQ_MP (@lem3619164 A B f A') (@lem3619151 A B f A')). Qed.
Lemma lem3619166 {A B : Type'} (f : A -> B) (A' : B -> Prop) : (term49 A B f A') = True.
Proof. exact (TRANS (@lem3619148 A B f A') (@lem3619165 A B f A')). Qed.
Lemma lem3619167 {A B : Type'} (f : A -> B) (A' : B -> Prop) : True = (term49 A B f A').
Proof. exact (SYM (@lem3619166 A B f A')). Qed.
Lemma lem3619168 {A B : Type'} (f : A -> B) (A' : B -> Prop) : term49 A B f A'.
Proof. exact (EQ_MP (@lem3619167 A B f A') (@lem0)). Qed.
Lemma lem3619169 {A B : Type'} (f : A -> B) (A' : B -> Prop) : term46 A B f A'.
Proof. exact (@lem3619168 A B f A' (@lem3619004 A B f A')). Qed.
Lemma lem3619174 {A B : Type'} (f : A -> B) : term54 A B f.
Proof. exact (fun A' : B -> Prop => @lem3619169 A B f A'). Qed.
Lemma lem3619179 {A B : Type'} : term55 A B.
Proof. exact (fun f : A -> B => @lem3619174 A B f). Qed.
