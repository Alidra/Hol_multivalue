Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_IMP_EXISTS_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import NOT_IMP_spec.
Require Import RIGHT_AND_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem12017 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5348 A P). Qed.
Lemma lem12018 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem12019 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem12018 A P) (@lem12017 A P)). Qed.
Lemma lem12020 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem12019 A P Q). Qed.
Lemma lem12021 {A : Type'} (P : Prop) (Q : A -> Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem12023 (t1 : Prop) : term5 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem12024 (t1 : Prop) : (term5 t1) = (term6 t1).
Proof. exact (eq_refl (term5 t1)). Qed.
Lemma lem12025 (t1 : Prop) : term6 t1.
Proof. exact (EQ_MP (@lem12024 t1) (@lem12023 t1)). Qed.
Lemma lem12026 (t1 : Prop) (t2 : Prop) : term7 t1 t2.
Proof. exact (@lem12025 t1 t2). Qed.
Lemma lem12027 (t1 : Prop) (t2 : Prop) : (term7 t1 t2) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (eq_refl (term7 t1 t2)). Qed.
Lemma lem12029 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem12030 {A : Type'} (P : A -> Prop) : (term10 A P) = ((term11 A P) = (term12 A P)).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem12040 (a : Prop) : term13 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem12041 (a : Prop) : (term13 a) = (term14 a).
Proof. exact (eq_refl (term13 a)). Qed.
Lemma lem12042 (a : Prop) : term14 a.
Proof. exact (EQ_MP (@lem12041 a) (@lem12040 a)). Qed.
Lemma lem12043 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem12044 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem12053 (b : Prop) : (term15 b) = (term15 b).
Proof. exact (eq_refl (term15 b)). Qed.
Lemma lem12054 (b : Prop) (a : Prop) (h1 : a = True) : (term16 b a) = (term17 b).
Proof. exact (MK_COMB (@lem12053 b) (@lem12043 a h1)). Qed.
Lemma lem12055 (b : Prop) : (term17 b) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl (term17 b)). Qed.
Lemma lem12056 (b : Prop) (a : Prop) : (term18 b a) = (term18 b a).
Proof. exact (eq_refl (term18 b a)). Qed.
Lemma lem12057 (a : Prop) (b : Prop) : ((term16 b a) = (term17 b)) = ((term16 b a) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem12056 b a) (@lem12055 b)). Qed.
Lemma lem12058 (a : Prop) (b : Prop) : (term16 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term16 b a)). Qed.
Lemma lem12059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12060 (a : Prop) (b : Prop) : (term18 b a) = (term19 a b).
Proof. exact (MK_COMB (@lem12059) (@lem12058 a b)). Qed.
Lemma lem12061 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl ((True = b) = ((~ True) = (~ b)))). Qed.
Lemma lem12062 (a : Prop) (b : Prop) : ((term16 b a) = ((True = b) = ((~ True) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem12060 a b) (@lem12061 b)). Qed.
Lemma lem12063 (a : Prop) (b : Prop) : ((term16 b a) = (term17 b)) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (TRANS (@lem12057 a b) (@lem12062 a b)). Qed.
Lemma lem12064 (b : Prop) (a : Prop) (h1 : a = True) : ((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (EQ_MP (@lem12063 a b) (@lem12054 b a h1)). Qed.
Lemma lem12065 (b : Prop) (a : Prop) (h1 : a = True) : ((True = b) = ((~ True) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem12064 b a h1)). Qed.
Lemma lem12066 (b : Prop) : (term15 b) = (term15 b).
Proof. exact (eq_refl (term15 b)). Qed.
Lemma lem12067 (b : Prop) (a : Prop) (h1 : a = False) : (term16 b a) = (term20 b).
Proof. exact (MK_COMB (@lem12066 b) (@lem12044 a h1)). Qed.
Lemma lem12068 (b : Prop) : (term20 b) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem12069 (b : Prop) (a : Prop) : (term18 b a) = (term18 b a).
Proof. exact (eq_refl (term18 b a)). Qed.
Lemma lem12070 (a : Prop) (b : Prop) : ((term16 b a) = (term20 b)) = ((term16 b a) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem12069 b a) (@lem12068 b)). Qed.
Lemma lem12071 (a : Prop) (b : Prop) : (term16 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term16 b a)). Qed.
Lemma lem12072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12073 (a : Prop) (b : Prop) : (term18 b a) = (term19 a b).
Proof. exact (MK_COMB (@lem12072) (@lem12071 a b)). Qed.
Lemma lem12074 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl ((False = b) = ((~ False) = (~ b)))). Qed.
Lemma lem12075 (a : Prop) (b : Prop) : ((term16 b a) = ((False = b) = ((~ False) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem12073 a b) (@lem12074 b)). Qed.
Lemma lem12076 (a : Prop) (b : Prop) : ((term16 b a) = (term20 b)) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (TRANS (@lem12070 a b) (@lem12075 a b)). Qed.
Lemma lem12077 (b : Prop) (a : Prop) (h1 : a = False) : ((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (EQ_MP (@lem12076 a b) (@lem12067 b a h1)). Qed.
Lemma lem12078 (b : Prop) (a : Prop) (h1 : a = False) : ((False = b) = ((~ False) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem12077 b a h1)). Qed.
Lemma lem12082 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem12083 (b : Prop) : (True = b) = b.
Proof. exact (@lem12082 b). Qed.
Lemma lem12084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12085 (b : Prop) : (term21 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem12084) (@lem12083 b)). Qed.
Lemma lem12089 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem12090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12091 : term22 = (@eq Prop False).
Proof. exact (MK_COMB (@lem12090) (@lem12089)). Qed.
Lemma lem12092 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem12093 (b : Prop) : ((~ True) = (~ b)) = (False = (~ b)).
Proof. exact (MK_COMB (@lem12091) (@lem12092 b)). Qed.
Lemma lem12095 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem12096 (b : Prop) : (False = (~ b)) = (term23 b).
Proof. exact (@lem12095 (~ b)). Qed.
Lemma lem12097 (b : Prop) : ((~ True) = (~ b)) = (term23 b).
Proof. exact (TRANS (@lem12093 b) (@lem12096 b)). Qed.
Lemma lem12098 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = (b = (term23 b)).
Proof. exact (MK_COMB (@lem12085 b) (@lem12097 b)). Qed.
Lemma lem12101 (b : Prop) : (b = (term23 b)) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (SYM (@lem12098 b)). Qed.
Lemma lem12110 (t : Prop) : (term23 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem12111 (b : Prop) : (term23 b) = b.
Proof. exact (@lem12110 b). Qed.
Lemma lem12112 (b : Prop) : (@eq Prop b) = (@eq Prop b).
Proof. exact (eq_refl (@eq Prop b)). Qed.
Lemma lem12113 (b : Prop) : (b = (term23 b)) = (b = b).
Proof. exact (MK_COMB (@lem12112 b) (@lem12111 b)). Qed.
Lemma lem12115 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12116 (x : Prop) : (x = x) = True.
Proof. exact (@lem12115 Prop x). Qed.
Lemma lem12117 (b : Prop) : (b = b) = True.
Proof. exact (@lem12116 b). Qed.
Lemma lem12118 (b : Prop) : (b = (term23 b)) = True.
Proof. exact (TRANS (@lem12113 b) (@lem12117 b)). Qed.
Lemma lem12119 (b : Prop) : True = (b = (term23 b)).
Proof. exact (SYM (@lem12118 b)). Qed.
Lemma lem12120 (b : Prop) : b = (term23 b).
Proof. exact (EQ_MP (@lem12119 b) (@lem0)). Qed.
Lemma lem12121 (b : Prop) : (True = b) = ((~ True) = (~ b)).
Proof. exact (EQ_MP (@lem12101 b) (@lem12120 b)). Qed.
Lemma lem12125 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem12126 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem12125 b). Qed.
Lemma lem12127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12128 (b : Prop) : (term24 b) = (term25 b).
Proof. exact (MK_COMB (@lem12127) (@lem12126 b)). Qed.
Lemma lem12132 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem12133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12134 : term26 = (@eq Prop True).
Proof. exact (MK_COMB (@lem12133) (@lem12132)). Qed.
Lemma lem12135 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem12136 (b : Prop) : ((~ False) = (~ b)) = (True = (~ b)).
Proof. exact (MK_COMB (@lem12134) (@lem12135 b)). Qed.
Lemma lem12138 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem12139 (b : Prop) : (True = (~ b)) = (~ b).
Proof. exact (@lem12138 (~ b)). Qed.
Lemma lem12140 (b : Prop) : ((~ False) = (~ b)) = (~ b).
Proof. exact (TRANS (@lem12136 b) (@lem12139 b)). Qed.
Lemma lem12141 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem12128 b) (@lem12140 b)). Qed.
Lemma lem12143 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12144 (x : Prop) : (x = x) = True.
Proof. exact (@lem12143 Prop x). Qed.
Lemma lem12145 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem12144 (~ b)). Qed.
Lemma lem12146 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = True.
Proof. exact (TRANS (@lem12141 b) (@lem12145 b)). Qed.
Lemma lem12147 (b : Prop) : True = ((False = b) = ((~ False) = (~ b))).
Proof. exact (SYM (@lem12146 b)). Qed.
Lemma lem12148 (b : Prop) : (False = b) = ((~ False) = (~ b)).
Proof. exact (EQ_MP (@lem12147 b) (@lem0)). Qed.
Lemma lem12149 (b : Prop) (a : Prop) (h1 : a = False) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem12078 b a h1) (@lem12148 b)). Qed.
Lemma lem12150 (b : Prop) (a : Prop) (h1 : a = True) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem12065 b a h1) (@lem12121 b)). Qed.
Lemma lem12157 (a : Prop) (b : Prop) : (a = b) = ((~ a) = (~ b)).
Proof. exact (or_elim (@lem12042 a) (fun h0 : a = True => @lem12150 b a h0) (fun h0 : a = False => @lem12149 b a h0)). Qed.
Lemma lem12158 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term27 A P Q) = (term28 A P Q)) = ((term29 A P Q) = (term30 A P Q)).
Proof. exact (@lem12157 (term27 A P Q) (term28 A P Q)). Qed.
Lemma lem12159 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term29 A P Q) = (term30 A P Q)) = ((term27 A P Q) = (term28 A P Q)).
Proof. exact (SYM (@lem12158 A P Q)). Qed.
Lemma lem12163 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (EQ_MP (@lem12027 t1 t2) (@lem12026 t1 t2)). Qed.
Lemma lem12164 {A : Type'} (P : Prop) (Q : A -> Prop) : (term29 A P Q) = (term31 A P Q).
Proof. exact (@lem12163 P (term32 A Q)). Qed.
Lemma lem12168 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem12030 A P) (@lem12029 A P)). Qed.
Lemma lem12169 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (@lem12168 A P). Qed.
Lemma lem12170 {A : Type'} (Q : A -> Prop) : (term11 A Q) = (term12 A Q).
Proof. exact (@lem12169 A Q). Qed.
Lemma lem12175 (P : Prop) : (and P) = (and P).
Proof. exact (eq_refl (and P)). Qed.
Lemma lem12176 {A : Type'} (P : Prop) (Q : A -> Prop) : (term31 A P Q) = (term33 A P Q).
Proof. exact (MK_COMB (@lem12175 P) (@lem12170 A Q)). Qed.
Lemma lem12178 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem12021 A P Q) (@lem12020 A P Q)). Qed.
Lemma lem12179 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (@lem12178 A P Q). Qed.
Lemma lem12180 {A : Type'} (P : Prop) (Q : A -> Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (@lem12179 A P (term36 A Q)). Qed.
Lemma lem12181 {A : Type'} (Q : A -> Prop) (x : A) : (term37 A Q x) = (term38 A Q x).
Proof. exact (eq_refl (term37 A Q x)). Qed.
Lemma lem12182 {A : Type'} (Q : A -> Prop) : (term39 A Q) = (term36 A Q).
Proof. exact (fun_ext (fun x : A => @lem12181 A Q x)). Qed.
Lemma lem12183 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem12184 {A : Type'} (Q : A -> Prop) : (term40 A Q) = (term12 A Q).
Proof. exact (MK_COMB (@lem12183 A) (@lem12182 A Q)). Qed.
Lemma lem12185 (P : Prop) : (and P) = (and P).
Proof. exact (eq_refl (and P)). Qed.
Lemma lem12186 {A : Type'} (P : Prop) (Q : A -> Prop) : (term34 A P Q) = (term33 A P Q).
Proof. exact (MK_COMB (@lem12185 P) (@lem12184 A Q)). Qed.
Lemma lem12187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12188 {A : Type'} (P : Prop) (Q : A -> Prop) : (term41 A P Q) = (term42 A P Q).
Proof. exact (MK_COMB (@lem12187) (@lem12186 A P Q)). Qed.
Lemma lem12189 {A : Type'} (Q : A -> Prop) (x : A) : (term37 A Q x) = (term38 A Q x).
Proof. exact (eq_refl (term37 A Q x)). Qed.
Lemma lem12190 (P : Prop) : (and P) = (and P).
Proof. exact (eq_refl (and P)). Qed.
Lemma lem12191 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term43 A P Q x) = (term44 A P Q x).
Proof. exact (MK_COMB (@lem12190 P) (@lem12189 A Q x)). Qed.
Lemma lem12192 {A : Type'} (P : Prop) (Q : A -> Prop) : (term45 A P Q) = (term46 A P Q).
Proof. exact (fun_ext (fun x : A => @lem12191 A P Q x)). Qed.
Lemma lem12193 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem12194 {A : Type'} (P : Prop) (Q : A -> Prop) : (term35 A P Q) = (term47 A P Q).
Proof. exact (MK_COMB (@lem12193 A) (@lem12192 A P Q)). Qed.
Lemma lem12195 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term34 A P Q) = (term35 A P Q)) = ((term33 A P Q) = (term47 A P Q)).
Proof. exact (MK_COMB (@lem12188 A P Q) (@lem12194 A P Q)). Qed.
Lemma lem12196 {A : Type'} (P : Prop) (Q : A -> Prop) : (term33 A P Q) = (term47 A P Q).
Proof. exact (EQ_MP (@lem12195 A P Q) (@lem12180 A P Q)). Qed.
Lemma lem12203 {A : Type'} (P : Prop) (Q : A -> Prop) : (term31 A P Q) = (term47 A P Q).
Proof. exact (TRANS (@lem12176 A P Q) (@lem12196 A P Q)). Qed.
Lemma lem12204 {A : Type'} (P : Prop) (Q : A -> Prop) : (term29 A P Q) = (term47 A P Q).
Proof. exact (TRANS (@lem12164 A P Q) (@lem12203 A P Q)). Qed.
Lemma lem12205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12206 {A : Type'} (P : Prop) (Q : A -> Prop) : (term48 A P Q) = (term49 A P Q).
Proof. exact (MK_COMB (@lem12205) (@lem12204 A P Q)). Qed.
Lemma lem12208 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem12030 A P) (@lem12029 A P)). Qed.
Lemma lem12209 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (@lem12208 A P). Qed.
Lemma lem12210 {A : Type'} (P : Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (@lem12209 A (term52 A P Q)). Qed.
Lemma lem12211 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term53 A P Q x) = (term54 A P Q x).
Proof. exact (eq_refl (term53 A P Q x)). Qed.
Lemma lem12212 {A : Type'} (P : Prop) (Q : A -> Prop) : (term55 A P Q) = (term52 A P Q).
Proof. exact (fun_ext (fun x : A => @lem12211 A P Q x)). Qed.
Lemma lem12213 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem12214 {A : Type'} (P : Prop) (Q : A -> Prop) : (term56 A P Q) = (term28 A P Q).
Proof. exact (MK_COMB (@lem12213 A) (@lem12212 A P Q)). Qed.
Lemma lem12215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem12216 {A : Type'} (P : Prop) (Q : A -> Prop) : (term50 A P Q) = (term30 A P Q).
Proof. exact (MK_COMB (@lem12215) (@lem12214 A P Q)). Qed.
Lemma lem12217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12218 {A : Type'} (P : Prop) (Q : A -> Prop) : (term57 A P Q) = (term58 A P Q).
Proof. exact (MK_COMB (@lem12217) (@lem12216 A P Q)). Qed.
Lemma lem12219 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term53 A P Q x) = (term54 A P Q x).
Proof. exact (eq_refl (term53 A P Q x)). Qed.
Lemma lem12220 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem12221 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term59 A P Q x) = (term60 A P Q x).
Proof. exact (MK_COMB (@lem12220) (@lem12219 A P Q x)). Qed.
Lemma lem12222 {A : Type'} (P : Prop) (Q : A -> Prop) : (term61 A P Q) = (term62 A P Q).
Proof. exact (fun_ext (fun x : A => @lem12221 A P Q x)). Qed.
Lemma lem12223 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem12224 {A : Type'} (P : Prop) (Q : A -> Prop) : (term51 A P Q) = (term63 A P Q).
Proof. exact (MK_COMB (@lem12223 A) (@lem12222 A P Q)). Qed.
Lemma lem12225 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term50 A P Q) = (term51 A P Q)) = ((term30 A P Q) = (term63 A P Q)).
Proof. exact (MK_COMB (@lem12218 A P Q) (@lem12224 A P Q)). Qed.
Lemma lem12226 {A : Type'} (P : Prop) (Q : A -> Prop) : (term30 A P Q) = (term63 A P Q).
Proof. exact (EQ_MP (@lem12225 A P Q) (@lem12210 A P Q)). Qed.
Lemma lem12232 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (EQ_MP (@lem12027 t1 t2) (@lem12026 t1 t2)). Qed.
Lemma lem12233 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term60 A P Q x) = (term44 A P Q x).
Proof. exact (@lem12232 P (Q x)). Qed.
Lemma lem12236 {A : Type'} (P : Prop) (Q : A -> Prop) : (term62 A P Q) = (term46 A P Q).
Proof. exact (fun_ext (fun x : A => @lem12233 A P Q x)). Qed.
Lemma lem12237 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem12238 {A : Type'} (P : Prop) (Q : A -> Prop) : (term63 A P Q) = (term47 A P Q).
Proof. exact (MK_COMB (@lem12237 A) (@lem12236 A P Q)). Qed.
Lemma lem12243 {A : Type'} (P : Prop) (Q : A -> Prop) : (term30 A P Q) = (term47 A P Q).
Proof. exact (TRANS (@lem12226 A P Q) (@lem12238 A P Q)). Qed.
Lemma lem12244 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term29 A P Q) = (term30 A P Q)) = ((term47 A P Q) = (term47 A P Q)).
Proof. exact (MK_COMB (@lem12206 A P Q) (@lem12243 A P Q)). Qed.
Lemma lem12246 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12247 (x : Prop) : (x = x) = True.
Proof. exact (@lem12246 Prop x). Qed.
Lemma lem12248 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term47 A P Q) = (term47 A P Q)) = True.
Proof. exact (@lem12247 (term47 A P Q)). Qed.
Lemma lem12249 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term29 A P Q) = (term30 A P Q)) = True.
Proof. exact (TRANS (@lem12244 A P Q) (@lem12248 A P Q)). Qed.
Lemma lem12250 {A : Type'} (P : Prop) (Q : A -> Prop) : True = ((term29 A P Q) = (term30 A P Q)).
Proof. exact (SYM (@lem12249 A P Q)). Qed.
Lemma lem12251 {A : Type'} (P : Prop) (Q : A -> Prop) : (term29 A P Q) = (term30 A P Q).
Proof. exact (EQ_MP (@lem12250 A P Q) (@lem0)). Qed.
Lemma lem12252 {A : Type'} (P : Prop) (Q : A -> Prop) : (term27 A P Q) = (term28 A P Q).
Proof. exact (EQ_MP (@lem12159 A P Q) (@lem12251 A P Q)). Qed.
Lemma lem12257 {A : Type'} (P : Prop) : term64 A P.
Proof. exact (fun Q : A -> Prop => @lem12252 A P Q). Qed.
Lemma lem12262 {A : Type'} : term65 A.
Proof. exact (fun P : Prop => @lem12257 A P). Qed.
