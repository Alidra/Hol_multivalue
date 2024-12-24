Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ONE_OR_PRIME_term_abbrevs.
Require Import DIVIDES_ONE_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import prime_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem3137998 (p : nat) : term0 p.
Proof. exact (@lem9784 (p = term1)). Qed.
Lemma lem3137999 (p : nat) : (term0 p) = (term2 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem3138000 (p : nat) : term2 p.
Proof. exact (EQ_MP (@lem3137999 p) (@lem3137998 p)). Qed.
Lemma lem3138002 (p : nat) (h1 : term3 p) : term3 p.
Proof. exact (h1). Qed.
Lemma lem3138003 (p : nat) : term4 p.
Proof. exact (@lem3137997 p). Qed.
Lemma lem3138004 (p : nat) : (term4 p) = ((prime p) = (term5 p)).
Proof. exact (eq_refl (term4 p)). Qed.
Lemma lem3138013 (p : nat) : (prime p) = (term5 p).
Proof. exact (EQ_MP (@lem3138004 p) (@lem3138003 p)). Qed.
Lemma lem3138030 (p : nat) : (term6 p) = (term6 p).
Proof. exact (eq_refl (term6 p)). Qed.
Lemma lem3138031 (p : nat) : (term7 p) = (term8 p).
Proof. exact (MK_COMB (@lem3138030 p) (@lem3138013 p)). Qed.
Lemma lem3138034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3138035 (p : nat) : (term9 p) = (term10 p).
Proof. exact (MK_COMB (@lem3138034) (@lem3138031 p)). Qed.
Lemma lem3138048 (p : nat) : (term11 p) = (term11 p).
Proof. exact (eq_refl (term11 p)). Qed.
Lemma lem3138049 (p : nat) : ((term7 p) = (term11 p)) = ((term8 p) = (term11 p)).
Proof. exact (MK_COMB (@lem3138035 p) (@lem3138048 p)). Qed.
Lemma lem3138052 (p : nat) : ((term8 p) = (term11 p)) = ((term7 p) = (term11 p)).
Proof. exact (SYM (@lem3138049 p)). Qed.
Lemma lem3138053 (n : nat) : term12 n.
Proof. exact (@lem3110728 n). Qed.
Lemma lem3138054 (n : nat) : (term12 n) = ((term13 n) = (n = term1)).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem3138063 (p : nat) (h1 : p = term1) : p = term1.
Proof. exact (h1). Qed.
Lemma lem3138064 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3138065 (p : nat) (h1 : p = term1) : (@eq nat p) = term14.
Proof. exact (MK_COMB (@lem3138064) (@lem3138063 p h1)). Qed.
Lemma lem3138066 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem3138067 (p : nat) (h1 : p = term1) : (p = term1) = (term1 = term1).
Proof. exact (MK_COMB (@lem3138065 p h1) (@lem3138066)). Qed.
Lemma lem3138069 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3138070 (x : nat) : (x = x) = True.
Proof. exact (@lem3138069 nat x). Qed.
Lemma lem3138071 : (term1 = term1) = True.
Proof. exact (@lem3138070 term1). Qed.
Lemma lem3138072 (p : nat) (h1 : p = term1) : (p = term1) = True.
Proof. exact (TRANS (@lem3138067 p h1) (@lem3138071)). Qed.
Lemma lem3138073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3138074 (p : nat) (h1 : p = term1) : (term6 p) = (or True).
Proof. exact (MK_COMB (@lem3138073) (@lem3138072 p h1)). Qed.
Lemma lem3138080 (p : nat) (h1 : p = term1) : p = term1.
Proof. exact (h1). Qed.
Lemma lem3138081 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3138082 (p : nat) (h1 : p = term1) : (@eq nat p) = term14.
Proof. exact (MK_COMB (@lem3138081) (@lem3138080 p h1)). Qed.
Lemma lem3138083 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem3138084 (p : nat) (h1 : p = term1) : (p = term1) = (term1 = term1).
Proof. exact (MK_COMB (@lem3138082 p h1) (@lem3138083)). Qed.
Lemma lem3138086 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3138087 (x : nat) : (x = x) = True.
Proof. exact (@lem3138086 nat x). Qed.
Lemma lem3138088 : (term1 = term1) = True.
Proof. exact (@lem3138087 term1). Qed.
Lemma lem3138089 (p : nat) (h1 : p = term1) : (p = term1) = True.
Proof. exact (TRANS (@lem3138084 p h1) (@lem3138088)). Qed.
Lemma lem3138090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3138091 (p : nat) (h1 : p = term1) : (term3 p) = (~ True).
Proof. exact (MK_COMB (@lem3138090) (@lem3138089 p h1)). Qed.
Lemma lem3138093 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3138094 (p : nat) (h1 : p = term1) : (term3 p) = False.
Proof. exact (TRANS (@lem3138091 p h1) (@lem3138093)). Qed.
Lemma lem3138095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3138096 (p : nat) (h1 : p = term1) : (term15 p) = (and False).
Proof. exact (MK_COMB (@lem3138095) (@lem3138094 p h1)). Qed.
Lemma lem3138104 (p : nat) (h1 : p = term1) : p = term1.
Proof. exact (h1). Qed.
Lemma lem3138105 (x : nat) : (num_divides x) = (num_divides x).
Proof. exact (eq_refl (num_divides x)). Qed.
Lemma lem3138106 (x : nat) (p : nat) (h1 : p = term1) : (num_divides x p) = (term13 x).
Proof. exact (MK_COMB (@lem3138105 x) (@lem3138104 p h1)). Qed.
Lemma lem3138108 (n : nat) : (term13 n) = (n = term1).
Proof. exact (EQ_MP (@lem3138054 n) (@lem3138053 n)). Qed.
Lemma lem3138109 (x : nat) : (term13 x) = (x = term1).
Proof. exact (@lem3138108 x). Qed.
Lemma lem3138112 (x : nat) (p : nat) (h1 : p = term1) : (num_divides x p) = (x = term1).
Proof. exact (TRANS (@lem3138106 x p h1) (@lem3138109 x)). Qed.
Lemma lem3138113 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3138114 (x : nat) (p : nat) (h1 : p = term1) : (term16 x p) = (term17 x).
Proof. exact (MK_COMB (@lem3138113) (@lem3138112 x p h1)). Qed.
Lemma lem3138122 (p : nat) (h1 : p = term1) : p = term1.
Proof. exact (h1). Qed.
Lemma lem3138123 (x : nat) : (@eq nat x) = (@eq nat x).
Proof. exact (eq_refl (@eq nat x)). Qed.
Lemma lem3138124 (x : nat) (p : nat) (h1 : p = term1) : (x = p) = (x = term1).
Proof. exact (MK_COMB (@lem3138123 x) (@lem3138122 p h1)). Qed.
Lemma lem3138127 (x : nat) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem3138128 (x : nat) (p : nat) (h1 : p = term1) : (term18 x p) = (term19 x).
Proof. exact (MK_COMB (@lem3138127 x) (@lem3138124 x p h1)). Qed.
Lemma lem3138130 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem3138131 (x : nat) : (term19 x) = (x = term1).
Proof. exact (@lem3138130 (x = term1)). Qed.
Lemma lem3138134 (x : nat) (p : nat) (h1 : p = term1) : (term18 x p) = (x = term1).
Proof. exact (TRANS (@lem3138128 x p h1) (@lem3138131 x)). Qed.
Lemma lem3138135 (x : nat) (p : nat) (h1 : p = term1) : (term20 x p) = (term21 x).
Proof. exact (MK_COMB (@lem3138114 x p h1) (@lem3138134 x p h1)). Qed.
Lemma lem3138139 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3138140 (x : nat) : (term21 x) = True.
Proof. exact (@lem3138139 (x = term1)). Qed.
Lemma lem3138141 (x : nat) (p : nat) (h1 : p = term1) : (term20 x p) = True.
Proof. exact (TRANS (@lem3138135 x p h1) (@lem3138140 x)). Qed.
Lemma lem3138142 (p : nat) (h1 : p = term1) : (term22 p) = term23.
Proof. exact (fun_ext (fun x : nat => @lem3138141 x p h1)). Qed.
Lemma lem3138143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3138144 (p : nat) (h1 : p = term1) : (term11 p) = term24.
Proof. exact (MK_COMB (@lem3138143) (@lem3138142 p h1)). Qed.
Lemma lem3138146 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3138147 (t : Prop) : (term26 t) = t.
Proof. exact (@lem3138146 nat t). Qed.
Lemma lem3138148 : term24 = True.
Proof. exact (@lem3138147 True). Qed.
Lemma lem3138149 (p : nat) (h1 : p = term1) : (term11 p) = True.
Proof. exact (TRANS (@lem3138144 p h1) (@lem3138148)). Qed.
Lemma lem3138150 (p : nat) (h1 : p = term1) : (term5 p) = (False /\ True).
Proof. exact (MK_COMB (@lem3138096 p h1) (@lem3138149 p h1)). Qed.
Lemma lem3138152 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3138153 : (False /\ True) = False.
Proof. exact (@lem3138152 True). Qed.
Lemma lem3138154 (p : nat) (h1 : p = term1) : (term5 p) = False.
Proof. exact (TRANS (@lem3138150 p h1) (@lem3138153)). Qed.
Lemma lem3138155 (p : nat) (h1 : p = term1) : (term8 p) = (True \/ False).
Proof. exact (MK_COMB (@lem3138074 p h1) (@lem3138154 p h1)). Qed.
Lemma lem3138157 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3138158 : (True \/ False) = True.
Proof. exact (@lem3138157 False). Qed.
Lemma lem3138159 (p : nat) (h1 : p = term1) : (term8 p) = True.
Proof. exact (TRANS (@lem3138155 p h1) (@lem3138158)). Qed.
Lemma lem3138160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3138161 (p : nat) (h1 : p = term1) : (term10 p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3138160) (@lem3138159 p h1)). Qed.
Lemma lem3138169 (p : nat) (h1 : p = term1) : p = term1.
Proof. exact (h1). Qed.
Lemma lem3138170 (n : nat) : (num_divides n) = (num_divides n).
Proof. exact (eq_refl (num_divides n)). Qed.
Lemma lem3138171 (n : nat) (p : nat) (h1 : p = term1) : (num_divides n p) = (term13 n).
Proof. exact (MK_COMB (@lem3138170 n) (@lem3138169 p h1)). Qed.
Lemma lem3138173 (n : nat) : (term13 n) = (n = term1).
Proof. exact (EQ_MP (@lem3138054 n) (@lem3138053 n)). Qed.
Lemma lem3138176 (n : nat) (p : nat) (h1 : p = term1) : (num_divides n p) = (n = term1).
Proof. exact (TRANS (@lem3138171 n p h1) (@lem3138173 n)). Qed.
Lemma lem3138177 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3138178 (n : nat) (p : nat) (h1 : p = term1) : (term16 n p) = (term17 n).
Proof. exact (MK_COMB (@lem3138177) (@lem3138176 n p h1)). Qed.
Lemma lem3138186 (p : nat) (h1 : p = term1) : p = term1.
Proof. exact (h1). Qed.
Lemma lem3138187 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem3138188 (n : nat) (p : nat) (h1 : p = term1) : (n = p) = (n = term1).
Proof. exact (MK_COMB (@lem3138187 n) (@lem3138186 p h1)). Qed.
Lemma lem3138191 (n : nat) : (term6 n) = (term6 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem3138192 (n : nat) (p : nat) (h1 : p = term1) : (term18 n p) = (term19 n).
Proof. exact (MK_COMB (@lem3138191 n) (@lem3138188 n p h1)). Qed.
Lemma lem3138194 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem3138195 (n : nat) : (term19 n) = (n = term1).
Proof. exact (@lem3138194 (n = term1)). Qed.
Lemma lem3138198 (n : nat) (p : nat) (h1 : p = term1) : (term18 n p) = (n = term1).
Proof. exact (TRANS (@lem3138192 n p h1) (@lem3138195 n)). Qed.
Lemma lem3138199 (n : nat) (p : nat) (h1 : p = term1) : (term20 n p) = (term21 n).
Proof. exact (MK_COMB (@lem3138178 n p h1) (@lem3138198 n p h1)). Qed.
Lemma lem3138203 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3138204 (n : nat) : (term21 n) = True.
Proof. exact (@lem3138203 (n = term1)). Qed.
Lemma lem3138205 (n : nat) (p : nat) (h1 : p = term1) : (term20 n p) = True.
Proof. exact (TRANS (@lem3138199 n p h1) (@lem3138204 n)). Qed.
Lemma lem3138206 (p : nat) (h1 : p = term1) : (term22 p) = term23.
Proof. exact (fun_ext (fun n : nat => @lem3138205 n p h1)). Qed.
Lemma lem3138207 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3138208 (p : nat) (h1 : p = term1) : (term11 p) = term24.
Proof. exact (MK_COMB (@lem3138207) (@lem3138206 p h1)). Qed.
Lemma lem3138210 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3138211 (t : Prop) : (term26 t) = t.
Proof. exact (@lem3138210 nat t). Qed.
Lemma lem3138212 : term24 = True.
Proof. exact (@lem3138211 True). Qed.
Lemma lem3138213 (p : nat) (h1 : p = term1) : (term11 p) = True.
Proof. exact (TRANS (@lem3138208 p h1) (@lem3138212)). Qed.
Lemma lem3138214 (p : nat) (h1 : p = term1) : ((term8 p) = (term11 p)) = (True = True).
Proof. exact (MK_COMB (@lem3138161 p h1) (@lem3138213 p h1)). Qed.
Lemma lem3138216 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3138217 : (True = True) = True.
Proof. exact (@lem3138216 True). Qed.
Lemma lem3138218 (p : nat) (h1 : p = term1) : ((term8 p) = (term11 p)) = True.
Proof. exact (TRANS (@lem3138214 p h1) (@lem3138217)). Qed.
Lemma lem3138219 (p : nat) (h1 : p = term1) : True = ((term8 p) = (term11 p)).
Proof. exact (SYM (@lem3138218 p h1)). Qed.
Lemma lem3138220 (p : nat) (h1 : p = term1) : (term8 p) = (term11 p).
Proof. exact (EQ_MP (@lem3138219 p h1) (@lem0)). Qed.
Lemma lem3138224 (p : nat) : term27 p.
Proof. exact (@lem82 (p = term1)). Qed.
Lemma lem3138242 (p : nat) (h1 : term3 p) : (p = term1) = False.
Proof. exact (@lem3138224 p (@lem3138002 p h1)). Qed.
Lemma lem3138243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3138244 (p : nat) (h1 : term3 p) : (term6 p) = (or False).
Proof. exact (MK_COMB (@lem3138243) (@lem3138242 p h1)). Qed.
Lemma lem3138248 (p : nat) (h1 : term3 p) : (p = term1) = False.
Proof. exact (@lem3138224 p (@lem3138002 p h1)). Qed.
Lemma lem3138249 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3138250 (p : nat) (h1 : term3 p) : (term3 p) = (~ False).
Proof. exact (MK_COMB (@lem3138249) (@lem3138248 p h1)). Qed.
Lemma lem3138252 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3138253 (p : nat) (h1 : term3 p) : (term3 p) = True.
Proof. exact (TRANS (@lem3138250 p h1) (@lem3138252)). Qed.
Lemma lem3138254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3138255 (p : nat) (h1 : term3 p) : (term15 p) = (and True).
Proof. exact (MK_COMB (@lem3138254) (@lem3138253 p h1)). Qed.
Lemma lem3138268 (p : nat) : (term11 p) = (term11 p).
Proof. exact (eq_refl (term11 p)). Qed.
Lemma lem3138269 (p : nat) (h1 : term3 p) : (term5 p) = (term28 p).
Proof. exact (MK_COMB (@lem3138255 p h1) (@lem3138268 p)). Qed.
Lemma lem3138271 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3138272 (p : nat) : (term28 p) = (term11 p).
Proof. exact (@lem3138271 (term11 p)). Qed.
Lemma lem3138285 (p : nat) (h1 : term3 p) : (term5 p) = (term11 p).
Proof. exact (TRANS (@lem3138269 p h1) (@lem3138272 p)). Qed.
Lemma lem3138286 (p : nat) (h1 : term3 p) : (term8 p) = (term29 p).
Proof. exact (MK_COMB (@lem3138244 p h1) (@lem3138285 p h1)). Qed.
Lemma lem3138288 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem3138289 (p : nat) : (term29 p) = (term11 p).
Proof. exact (@lem3138288 (term11 p)). Qed.
Lemma lem3138302 (p : nat) (h1 : term3 p) : (term8 p) = (term11 p).
Proof. exact (TRANS (@lem3138286 p h1) (@lem3138289 p)). Qed.
Lemma lem3138303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3138304 (p : nat) (h1 : term3 p) : (term10 p) = (term30 p).
Proof. exact (MK_COMB (@lem3138303) (@lem3138302 p h1)). Qed.
Lemma lem3138317 (p : nat) : (term11 p) = (term11 p).
Proof. exact (eq_refl (term11 p)). Qed.
Lemma lem3138318 (p : nat) (h1 : term3 p) : ((term8 p) = (term11 p)) = ((term11 p) = (term11 p)).
Proof. exact (MK_COMB (@lem3138304 p h1) (@lem3138317 p)). Qed.
Lemma lem3138320 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3138321 (x : Prop) : (x = x) = True.
Proof. exact (@lem3138320 Prop x). Qed.
Lemma lem3138322 (p : nat) : ((term11 p) = (term11 p)) = True.
Proof. exact (@lem3138321 (term11 p)). Qed.
Lemma lem3138325 (p : nat) : (term31 p) = (term31 p).
Proof. exact (eq_refl (term31 p)). Qed.
Lemma lem3138326 (p : nat) : (term31 p) = (((term11 p) = (term11 p)) = True).
Proof. exact (eq_refl (term31 p)). Qed.
Lemma lem3138327 (p : nat) : (term32 p) = (term32 p).
Proof. exact (eq_refl (term32 p)). Qed.
Lemma lem3138328 (p : nat) : ((term31 p) = (term31 p)) = ((term31 p) = (((term11 p) = (term11 p)) = True)).
Proof. exact (MK_COMB (@lem3138327 p) (@lem3138326 p)). Qed.
Lemma lem3138329 (p : nat) : (term31 p) = (((term11 p) = (term11 p)) = True).
Proof. exact (eq_refl (term31 p)). Qed.
Lemma lem3138330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3138331 (p : nat) : (term32 p) = (term33 p).
Proof. exact (MK_COMB (@lem3138330) (@lem3138329 p)). Qed.
Lemma lem3138332 (p : nat) : (((term11 p) = (term11 p)) = True) = (((term11 p) = (term11 p)) = True).
Proof. exact (eq_refl (((term11 p) = (term11 p)) = True)). Qed.
Lemma lem3138333 (p : nat) : ((term31 p) = (((term11 p) = (term11 p)) = True)) = ((((term11 p) = (term11 p)) = True) = (((term11 p) = (term11 p)) = True)).
Proof. exact (MK_COMB (@lem3138331 p) (@lem3138332 p)). Qed.
Lemma lem3138334 (p : nat) : ((term31 p) = (term31 p)) = ((((term11 p) = (term11 p)) = True) = (((term11 p) = (term11 p)) = True)).
Proof. exact (TRANS (@lem3138328 p) (@lem3138333 p)). Qed.
Lemma lem3138335 (p : nat) : (((term11 p) = (term11 p)) = True) = (((term11 p) = (term11 p)) = True).
Proof. exact (EQ_MP (@lem3138334 p) (@lem3138325 p)). Qed.
Lemma lem3138336 (p : nat) : ((term11 p) = (term11 p)) = True.
Proof. exact (EQ_MP (@lem3138335 p) (@lem3138322 p)). Qed.
Lemma lem3138337 (p : nat) (h1 : term3 p) : ((term8 p) = (term11 p)) = True.
Proof. exact (TRANS (@lem3138318 p h1) (@lem3138336 p)). Qed.
Lemma lem3138338 (p : nat) (h1 : term3 p) : True = ((term8 p) = (term11 p)).
Proof. exact (SYM (@lem3138337 p h1)). Qed.
Lemma lem3138339 (p : nat) (h1 : term3 p) : (term8 p) = (term11 p).
Proof. exact (EQ_MP (@lem3138338 p h1) (@lem0)). Qed.
Lemma lem3138340 (p : nat) : (term8 p) = (term11 p).
Proof. exact (or_elim (@lem3138000 p) (fun h0 : p = term1 => @lem3138220 p h0) (fun h0 : term3 p => @lem3138339 p h0)). Qed.
Lemma lem3138341 (p : nat) : (term7 p) = (term11 p).
Proof. exact (EQ_MP (@lem3138052 p) (@lem3138340 p)). Qed.
Lemma lem3138346 : term34.
Proof. exact (fun p : nat => @lem3138341 p). Qed.
