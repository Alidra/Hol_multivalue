Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm310219_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import WF_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem310021 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem310022 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem310023 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem310022 a) (@lem310021 a)). Qed.
Lemma lem310024 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem310025 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem310034 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem310035 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem310034 b) (@lem310024 a h1)). Qed.
Lemma lem310036 (b : Prop) : (term4 b) = ((True = (~ b)) = ((~ True) = b)).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem310037 (b : Prop) (a : Prop) : (term5 b a) = (term5 b a).
Proof. exact (eq_refl (term5 b a)). Qed.
Lemma lem310038 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = ((True = (~ b)) = ((~ True) = b))).
Proof. exact (MK_COMB (@lem310037 b a) (@lem310036 b)). Qed.
Lemma lem310039 (a : Prop) (b : Prop) : (term3 b a) = ((a = (~ b)) = ((~ a) = b)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem310040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310041 (a : Prop) (b : Prop) : (term5 b a) = (term6 a b).
Proof. exact (MK_COMB (@lem310040) (@lem310039 a b)). Qed.
Lemma lem310042 (b : Prop) : ((True = (~ b)) = ((~ True) = b)) = ((True = (~ b)) = ((~ True) = b)).
Proof. exact (eq_refl ((True = (~ b)) = ((~ True) = b))). Qed.
Lemma lem310043 (a : Prop) (b : Prop) : ((term3 b a) = ((True = (~ b)) = ((~ True) = b))) = (((a = (~ b)) = ((~ a) = b)) = ((True = (~ b)) = ((~ True) = b))).
Proof. exact (MK_COMB (@lem310041 a b) (@lem310042 b)). Qed.
Lemma lem310044 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = (((a = (~ b)) = ((~ a) = b)) = ((True = (~ b)) = ((~ True) = b))).
Proof. exact (TRANS (@lem310038 a b) (@lem310043 a b)). Qed.
Lemma lem310045 (b : Prop) (a : Prop) (h1 : a = True) : ((a = (~ b)) = ((~ a) = b)) = ((True = (~ b)) = ((~ True) = b)).
Proof. exact (EQ_MP (@lem310044 a b) (@lem310035 b a h1)). Qed.
Lemma lem310046 (b : Prop) (a : Prop) (h1 : a = True) : ((True = (~ b)) = ((~ True) = b)) = ((a = (~ b)) = ((~ a) = b)).
Proof. exact (SYM (@lem310045 b a h1)). Qed.
Lemma lem310047 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem310048 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term7 b).
Proof. exact (MK_COMB (@lem310047 b) (@lem310025 a h1)). Qed.
Lemma lem310049 (b : Prop) : (term7 b) = ((False = (~ b)) = ((~ False) = b)).
Proof. exact (eq_refl (term7 b)). Qed.
Lemma lem310050 (b : Prop) (a : Prop) : (term5 b a) = (term5 b a).
Proof. exact (eq_refl (term5 b a)). Qed.
Lemma lem310051 (a : Prop) (b : Prop) : ((term3 b a) = (term7 b)) = ((term3 b a) = ((False = (~ b)) = ((~ False) = b))).
Proof. exact (MK_COMB (@lem310050 b a) (@lem310049 b)). Qed.
Lemma lem310052 (a : Prop) (b : Prop) : (term3 b a) = ((a = (~ b)) = ((~ a) = b)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem310053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310054 (a : Prop) (b : Prop) : (term5 b a) = (term6 a b).
Proof. exact (MK_COMB (@lem310053) (@lem310052 a b)). Qed.
Lemma lem310055 (b : Prop) : ((False = (~ b)) = ((~ False) = b)) = ((False = (~ b)) = ((~ False) = b)).
Proof. exact (eq_refl ((False = (~ b)) = ((~ False) = b))). Qed.
Lemma lem310056 (a : Prop) (b : Prop) : ((term3 b a) = ((False = (~ b)) = ((~ False) = b))) = (((a = (~ b)) = ((~ a) = b)) = ((False = (~ b)) = ((~ False) = b))).
Proof. exact (MK_COMB (@lem310054 a b) (@lem310055 b)). Qed.
Lemma lem310057 (a : Prop) (b : Prop) : ((term3 b a) = (term7 b)) = (((a = (~ b)) = ((~ a) = b)) = ((False = (~ b)) = ((~ False) = b))).
Proof. exact (TRANS (@lem310051 a b) (@lem310056 a b)). Qed.
Lemma lem310058 (b : Prop) (a : Prop) (h1 : a = False) : ((a = (~ b)) = ((~ a) = b)) = ((False = (~ b)) = ((~ False) = b)).
Proof. exact (EQ_MP (@lem310057 a b) (@lem310048 b a h1)). Qed.
Lemma lem310059 (b : Prop) (a : Prop) (h1 : a = False) : ((False = (~ b)) = ((~ False) = b)) = ((a = (~ b)) = ((~ a) = b)).
Proof. exact (SYM (@lem310058 b a h1)). Qed.
Lemma lem310063 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem310064 (b : Prop) : (True = (~ b)) = (~ b).
Proof. exact (@lem310063 (~ b)). Qed.
Lemma lem310065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310066 (b : Prop) : (term8 b) = (term9 b).
Proof. exact (MK_COMB (@lem310065) (@lem310064 b)). Qed.
Lemma lem310070 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem310071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310072 : term10 = (@eq Prop False).
Proof. exact (MK_COMB (@lem310071) (@lem310070)). Qed.
Lemma lem310073 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem310074 (b : Prop) : ((~ True) = b) = (False = b).
Proof. exact (MK_COMB (@lem310072) (@lem310073 b)). Qed.
Lemma lem310076 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem310077 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem310076 b). Qed.
Lemma lem310078 (b : Prop) : ((~ True) = b) = (~ b).
Proof. exact (TRANS (@lem310074 b) (@lem310077 b)). Qed.
Lemma lem310079 (b : Prop) : ((True = (~ b)) = ((~ True) = b)) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem310066 b) (@lem310078 b)). Qed.
Lemma lem310081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem310082 (x : Prop) : (x = x) = True.
Proof. exact (@lem310081 Prop x). Qed.
Lemma lem310083 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem310082 (~ b)). Qed.
Lemma lem310084 (b : Prop) : ((True = (~ b)) = ((~ True) = b)) = True.
Proof. exact (TRANS (@lem310079 b) (@lem310083 b)). Qed.
Lemma lem310085 (b : Prop) : True = ((True = (~ b)) = ((~ True) = b)).
Proof. exact (SYM (@lem310084 b)). Qed.
Lemma lem310086 (b : Prop) : (True = (~ b)) = ((~ True) = b).
Proof. exact (EQ_MP (@lem310085 b) (@lem0)). Qed.
Lemma lem310090 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem310091 (b : Prop) : (False = (~ b)) = (term11 b).
Proof. exact (@lem310090 (~ b)). Qed.
Lemma lem310093 (t : Prop) : (term11 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem310094 (b : Prop) : (term11 b) = b.
Proof. exact (@lem310093 b). Qed.
Lemma lem310095 (b : Prop) : (False = (~ b)) = b.
Proof. exact (TRANS (@lem310091 b) (@lem310094 b)). Qed.
Lemma lem310096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310097 (b : Prop) : (term12 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem310096) (@lem310095 b)). Qed.
Lemma lem310101 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem310102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310103 : term13 = (@eq Prop True).
Proof. exact (MK_COMB (@lem310102) (@lem310101)). Qed.
Lemma lem310104 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem310105 (b : Prop) : ((~ False) = b) = (True = b).
Proof. exact (MK_COMB (@lem310103) (@lem310104 b)). Qed.
Lemma lem310107 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem310108 (b : Prop) : (True = b) = b.
Proof. exact (@lem310107 b). Qed.
Lemma lem310109 (b : Prop) : ((~ False) = b) = b.
Proof. exact (TRANS (@lem310105 b) (@lem310108 b)). Qed.
Lemma lem310110 (b : Prop) : ((False = (~ b)) = ((~ False) = b)) = (b = b).
Proof. exact (MK_COMB (@lem310097 b) (@lem310109 b)). Qed.
Lemma lem310112 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem310113 (x : Prop) : (x = x) = True.
Proof. exact (@lem310112 Prop x). Qed.
Lemma lem310114 (b : Prop) : (b = b) = True.
Proof. exact (@lem310113 b). Qed.
Lemma lem310115 (b : Prop) : ((False = (~ b)) = ((~ False) = b)) = True.
Proof. exact (TRANS (@lem310110 b) (@lem310114 b)). Qed.
Lemma lem310116 (b : Prop) : True = ((False = (~ b)) = ((~ False) = b)).
Proof. exact (SYM (@lem310115 b)). Qed.
Lemma lem310117 (b : Prop) : (False = (~ b)) = ((~ False) = b).
Proof. exact (EQ_MP (@lem310116 b) (@lem0)). Qed.
Lemma lem310118 (b : Prop) (a : Prop) (h1 : a = False) : (a = (~ b)) = ((~ a) = b).
Proof. exact (EQ_MP (@lem310059 b a h1) (@lem310117 b)). Qed.
Lemma lem310119 (b : Prop) (a : Prop) (h1 : a = True) : (a = (~ b)) = ((~ a) = b).
Proof. exact (EQ_MP (@lem310046 b a h1) (@lem310086 b)). Qed.
Lemma lem310123 {A : Type'} (P : A -> Prop) : term14 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem310124 {A : Type'} (P : A -> Prop) : (term14 A P) = ((term15 A P) = (term16 A P)).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem310126 {A : Type'} (lt2 : type1402 A) : term17 A lt2.
Proof. exact (@lem303045 A lt2). Qed.
Lemma lem310127 {A : Type'} (lt2 : type1402 A) : (term17 A lt2) = ((@WF A lt2) = (term18 A lt2)).
Proof. exact (eq_refl (term17 A lt2)). Qed.
Lemma lem310130 (a : Prop) (b : Prop) : (a = (~ b)) = ((~ a) = b).
Proof. exact (or_elim (@lem310023 a) (fun h0 : a = True => @lem310119 b a h0) (fun h0 : a = False => @lem310118 b a h0)). Qed.
Lemma lem310131 {A : Type'} (lt2 : type1402 A) : ((@WF A lt2) = (term19 A lt2)) = ((term20 A lt2) = (term21 A lt2)).
Proof. exact (@lem310130 (@WF A lt2) (term21 A lt2)). Qed.
Lemma lem310135 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term18 A lt2).
Proof. exact (EQ_MP (@lem310127 A lt2) (@lem310126 A lt2)). Qed.
Lemma lem310136 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term18 A lt2).
Proof. exact (@lem310135 A lt2). Qed.
Lemma lem310159 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem310160 {A : Type'} (lt2 : type1402 A) : (term20 A lt2) = (term22 A lt2).
Proof. exact (MK_COMB (@lem310159) (@lem310136 A lt2)). Qed.
Lemma lem310162 {A : Type'} (P : A -> Prop) : (term15 A P) = (term16 A P).
Proof. exact (EQ_MP (@lem310124 A P) (@lem310123 A P)). Qed.
Lemma lem310163 {A : Type'} (P : type686 A) : (term23 A P) = (term24 A P).
Proof. exact (@lem310162 (A -> Prop) P). Qed.
Lemma lem310164 {A : Type'} (lt2 : type1402 A) : (term25 A lt2) = (term26 A lt2).
Proof. exact (@lem310163 A (term27 A lt2)). Qed.
Lemma lem310165 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term28 A lt2 P) = (term29 A lt2 P).
Proof. exact (eq_refl (term28 A lt2 P)). Qed.
Lemma lem310166 {A : Type'} (lt2 : type1402 A) : (term30 A lt2) = (term27 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem310165 A lt2 P)). Qed.
Lemma lem310167 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem310168 {A : Type'} (lt2 : type1402 A) : (term31 A lt2) = (term18 A lt2).
Proof. exact (MK_COMB (@lem310167 A) (@lem310166 A lt2)). Qed.
Lemma lem310169 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem310170 {A : Type'} (lt2 : type1402 A) : (term25 A lt2) = (term22 A lt2).
Proof. exact (MK_COMB (@lem310169) (@lem310168 A lt2)). Qed.
Lemma lem310171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310172 {A : Type'} (lt2 : type1402 A) : (term32 A lt2) = (term33 A lt2).
Proof. exact (MK_COMB (@lem310171) (@lem310170 A lt2)). Qed.
Lemma lem310173 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term28 A lt2 P) = (term29 A lt2 P).
Proof. exact (eq_refl (term28 A lt2 P)). Qed.
Lemma lem310174 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem310175 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term34 A lt2 P) = (term35 A lt2 P).
Proof. exact (MK_COMB (@lem310174) (@lem310173 A lt2 P)). Qed.
Lemma lem310176 {A : Type'} (lt2 : type1402 A) : (term36 A lt2) = (term37 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem310175 A lt2 P)). Qed.
Lemma lem310177 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem310178 {A : Type'} (lt2 : type1402 A) : (term26 A lt2) = (term38 A lt2).
Proof. exact (MK_COMB (@lem310177 A) (@lem310176 A lt2)). Qed.
Lemma lem310179 {A : Type'} (lt2 : type1402 A) : ((term25 A lt2) = (term26 A lt2)) = ((term22 A lt2) = (term38 A lt2)).
Proof. exact (MK_COMB (@lem310172 A lt2) (@lem310178 A lt2)). Qed.
Lemma lem310180 {A : Type'} (lt2 : type1402 A) : (term22 A lt2) = (term38 A lt2).
Proof. exact (EQ_MP (@lem310179 A lt2) (@lem310164 A lt2)). Qed.
Lemma lem310203 {A : Type'} (lt2 : type1402 A) : (term20 A lt2) = (term38 A lt2).
Proof. exact (TRANS (@lem310160 A lt2) (@lem310180 A lt2)). Qed.
Lemma lem310204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310205 {A : Type'} (lt2 : type1402 A) : (term39 A lt2) = (term40 A lt2).
Proof. exact (MK_COMB (@lem310204) (@lem310203 A lt2)). Qed.
Lemma lem310214 {A : Type'} (lt2 : type1402 A) : (term21 A lt2) = (term21 A lt2).
Proof. exact (eq_refl (term21 A lt2)). Qed.
Lemma lem310215 {A : Type'} (lt2 : type1402 A) : ((term20 A lt2) = (term21 A lt2)) = ((term38 A lt2) = (term21 A lt2)).
Proof. exact (MK_COMB (@lem310205 A lt2) (@lem310214 A lt2)). Qed.
Lemma lem310218 {A : Type'} (lt2 : type1402 A) : ((@WF A lt2) = (term19 A lt2)) = ((term38 A lt2) = (term21 A lt2)).
Proof. exact (TRANS (@lem310131 A lt2) (@lem310215 A lt2)). Qed.
Lemma lem310219 {A : Type'} (lt2 : type1402 A) : ((term38 A lt2) = (term21 A lt2)) = ((@WF A lt2) = (term19 A lt2)).
Proof. exact (SYM (@lem310218 A lt2)). Qed.
