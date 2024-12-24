Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_EQ_term_abbrevs.
Require Import sup_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem5133934 (s : real -> Prop) : term0 s.
Proof. exact (@lem5133933 s). Qed.
Lemma lem5133935 (s : real -> Prop) : (term0 s) = ((sup s) = (term1 s)).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem5133948 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term2 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5133949 (p : Prop) (q : Prop) (p' : Prop) : term3 p q p'.
Proof. exact (fun q' : Prop => @lem5133948 p q p' q'). Qed.
Lemma lem5133950 (p : Prop) (q : Prop) : term4 p q.
Proof. exact (fun p' : Prop => @lem5133949 p q p'). Qed.
Lemma lem5133951 (s : real -> Prop) (t : real -> Prop) : term5 s t.
Proof. exact (@lem5133950 (term6 s t) ((sup s) = (sup t))). Qed.
Lemma lem5133952 (s : real -> Prop) (t : real -> Prop) (p' : Prop) : term7 s t p'.
Proof. exact (@lem5133951 s t p'). Qed.
Lemma lem5133953 (s : real -> Prop) (t : real -> Prop) (p' : Prop) : (term7 s t p') = (term8 s t p').
Proof. exact (eq_refl (term7 s t p')). Qed.
Lemma lem5133954 (s : real -> Prop) (t : real -> Prop) (p' : Prop) : term8 s t p'.
Proof. exact (EQ_MP (@lem5133953 s t p') (@lem5133952 s t p')). Qed.
Lemma lem5133955 (s : real -> Prop) (t : real -> Prop) (p' : Prop) (q' : Prop) : term9 s t p' q'.
Proof. exact (@lem5133954 s t p' q'). Qed.
Lemma lem5133956 (s : real -> Prop) (t : real -> Prop) (p' : Prop) (q' : Prop) : (term9 s t p' q') = (term10 s t p' q').
Proof. exact (eq_refl (term9 s t p' q')). Qed.
Lemma lem5133957 (s : real -> Prop) (t : real -> Prop) (p' : Prop) (q' : Prop) : term10 s t p' q'.
Proof. exact (EQ_MP (@lem5133956 s t p' q') (@lem5133955 s t p' q')). Qed.
Lemma lem5134018 (s : real -> Prop) (t : real -> Prop) : (term6 s t) = (term6 s t).
Proof. exact (eq_refl (term6 s t)). Qed.
Lemma lem5134019 (s : real -> Prop) (t : real -> Prop) (q' : Prop) : term11 s t q'.
Proof. exact (@lem5133957 s t (term6 s t) q'). Qed.
Lemma lem5134020 (s : real -> Prop) (t : real -> Prop) (q' : Prop) : term12 s t q'.
Proof. exact (@lem5134019 s t q' (@lem5134018 s t)). Qed.
Lemma lem5134021 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : term6 s t.
Proof. exact (h1). Qed.
Lemma lem5134022 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : term13 s t b.
Proof. exact (@lem5134021 s t h1 b). Qed.
Lemma lem5134023 (s : real -> Prop) (t : real -> Prop) (b : real) : (term13 s t b) = ((term14 s b) = (term14 t b)).
Proof. exact (eq_refl (term13 s t b)). Qed.
Lemma lem5134028 (s : real -> Prop) : (sup s) = (term1 s).
Proof. exact (EQ_MP (@lem5133935 s) (@lem5133934 s)). Qed.
Lemma lem5134032 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term14 s b) = (term14 t b).
Proof. exact (EQ_MP (@lem5134023 s t b) (@lem5134022 b s t h1)). Qed.
Lemma lem5134033 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term14 s a) = (term14 t a).
Proof. exact (@lem5134032 a s t h1). Qed.
Lemma lem5134061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5134062 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term15 s a) = (term15 t a).
Proof. exact (MK_COMB (@lem5134061) (@lem5134033 a s t h1)). Qed.
Lemma lem5134097 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term2 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5134098 (p : Prop) (q : Prop) (p' : Prop) : term3 p q p'.
Proof. exact (fun q' : Prop => @lem5134097 p q p' q'). Qed.
Lemma lem5134099 (p : Prop) (q : Prop) : term4 p q.
Proof. exact (fun p' : Prop => @lem5134098 p q p'). Qed.
Lemma lem5134100 (s : real -> Prop) (a : real) (b : real) : term16 s a b.
Proof. exact (@lem5134099 (term14 s b) (real_le a b)). Qed.
Lemma lem5134101 (s : real -> Prop) (a : real) (b : real) (p' : Prop) : term17 s a b p'.
Proof. exact (@lem5134100 s a b p'). Qed.
Lemma lem5134102 (s : real -> Prop) (a : real) (b : real) (p' : Prop) : (term17 s a b p') = (term18 s a b p').
Proof. exact (eq_refl (term17 s a b p')). Qed.
Lemma lem5134103 (s : real -> Prop) (a : real) (b : real) (p' : Prop) : term18 s a b p'.
Proof. exact (EQ_MP (@lem5134102 s a b p') (@lem5134101 s a b p')). Qed.
Lemma lem5134104 (s : real -> Prop) (a : real) (b : real) (p' : Prop) (q' : Prop) : term19 s a b p' q'.
Proof. exact (@lem5134103 s a b p' q'). Qed.
Lemma lem5134105 (s : real -> Prop) (a : real) (b : real) (p' : Prop) (q' : Prop) : (term19 s a b p' q') = (term20 s a b p' q').
Proof. exact (eq_refl (term19 s a b p' q')). Qed.
Lemma lem5134106 (s : real -> Prop) (a : real) (b : real) (p' : Prop) (q' : Prop) : term20 s a b p' q'.
Proof. exact (EQ_MP (@lem5134105 s a b p' q') (@lem5134104 s a b p' q')). Qed.
Lemma lem5134108 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term14 s b) = (term14 t b).
Proof. exact (EQ_MP (@lem5134023 s t b) (@lem5134022 b s t h1)). Qed.
Lemma lem5134136 (s : real -> Prop) (a : real) (t : real -> Prop) (b : real) (q' : Prop) : term21 s a t b q'.
Proof. exact (@lem5134106 s a b (term14 t b) q'). Qed.
Lemma lem5134137 (a : real) (b : real) (q' : Prop) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : term22 s a t b q'.
Proof. exact (@lem5134136 s a t b q' (@lem5134108 b s t h1)). Qed.
Lemma lem5134156 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5134157 (t : real -> Prop) (a : real) (b : real) : term23 t a b.
Proof. exact (fun h0 : term14 t b => @lem5134156 a b). Qed.
Lemma lem5134158 (a : real) (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : term24 s t a b.
Proof. exact (@lem5134137 a b (real_le a b) s t h1). Qed.
Lemma lem5134159 (a : real) (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term25 s a b) = (term25 t a b).
Proof. exact (@lem5134158 a b s t h1 (@lem5134157 t a b)). Qed.
Lemma lem5134252 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term26 s a) = (term26 t a).
Proof. exact (fun_ext (fun b : real => @lem5134159 a b s t h1)). Qed.
Lemma lem5134345 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5134346 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term27 s a) = (term27 t a).
Proof. exact (MK_COMB (@lem5134345) (@lem5134252 a s t h1)). Qed.
Lemma lem5134443 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term28 s a) = (term28 t a).
Proof. exact (MK_COMB (@lem5134062 a s t h1) (@lem5134346 a s t h1)). Qed.
Lemma lem5134569 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term29 s) = (term29 t).
Proof. exact (fun_ext (fun a : real => @lem5134443 a s t h1)). Qed.
Lemma lem5134695 : (@ε real) = (@ε real).
Proof. exact (eq_refl (@ε real)). Qed.
Lemma lem5134696 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term1 s) = (term1 t).
Proof. exact (MK_COMB (@lem5134695) (@lem5134569 s t h1)). Qed.
Lemma lem5134822 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (sup s) = (term1 t).
Proof. exact (TRANS (@lem5134028 s) (@lem5134696 s t h1)). Qed.
Lemma lem5134823 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5134824 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term30 s) = (term31 t).
Proof. exact (MK_COMB (@lem5134823) (@lem5134822 s t h1)). Qed.
Lemma lem5134951 (s : real -> Prop) : (sup s) = (term1 s).
Proof. exact (EQ_MP (@lem5133935 s) (@lem5133934 s)). Qed.
Lemma lem5134952 (t : real -> Prop) : (sup t) = (term1 t).
Proof. exact (@lem5134951 t). Qed.
Lemma lem5135078 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : ((sup s) = (sup t)) = ((term1 t) = (term1 t)).
Proof. exact (MK_COMB (@lem5134824 s t h1) (@lem5134952 t)). Qed.
Lemma lem5135080 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5135081 (x : real) : (x = x) = True.
Proof. exact (@lem5135080 real x). Qed.
Lemma lem5135082 (t : real -> Prop) : ((term1 t) = (term1 t)) = True.
Proof. exact (@lem5135081 (term1 t)). Qed.
Lemma lem5135083 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : ((sup s) = (sup t)) = True.
Proof. exact (TRANS (@lem5135078 s t h1) (@lem5135082 t)). Qed.
Lemma lem5135084 (s : real -> Prop) (t : real -> Prop) : term32 s t.
Proof. exact (fun h0 : term6 s t => @lem5135083 s t h0). Qed.
Lemma lem5135085 (s : real -> Prop) (t : real -> Prop) : term33 s t.
Proof. exact (@lem5134020 s t True). Qed.
Lemma lem5135086 (s : real -> Prop) (t : real -> Prop) : (term34 s t) = (term35 s t).
Proof. exact (@lem5135085 s t (@lem5135084 s t)). Qed.
Lemma lem5135088 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5135089 (s : real -> Prop) (t : real -> Prop) : (term35 s t) = True.
Proof. exact (@lem5135088 (term6 s t)). Qed.
Lemma lem5135090 (s : real -> Prop) (t : real -> Prop) : (term34 s t) = True.
Proof. exact (TRANS (@lem5135086 s t) (@lem5135089 s t)). Qed.
Lemma lem5135091 (s : real -> Prop) : (term36 s) = term37.
Proof. exact (fun_ext (fun t : real -> Prop => @lem5135090 s t)). Qed.
Lemma lem5135092 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135093 (s : real -> Prop) : (term38 s) = term39.
Proof. exact (MK_COMB (@lem5135092) (@lem5135091 s)). Qed.
Lemma lem5135095 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5135096 (t : Prop) : (term41 t) = t.
Proof. exact (@lem5135095 (real -> Prop) t). Qed.
Lemma lem5135097 : term39 = True.
Proof. exact (@lem5135096 True). Qed.
Lemma lem5135098 (s : real -> Prop) : (term38 s) = True.
Proof. exact (TRANS (@lem5135093 s) (@lem5135097)). Qed.
Lemma lem5135099 : term42 = term37.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135098 s)). Qed.
Lemma lem5135100 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135101 : term43 = term39.
Proof. exact (MK_COMB (@lem5135100) (@lem5135099)). Qed.
Lemma lem5135103 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5135104 (t : Prop) : (term41 t) = t.
Proof. exact (@lem5135103 (real -> Prop) t). Qed.
Lemma lem5135105 : term39 = True.
Proof. exact (@lem5135104 True). Qed.
Lemma lem5135106 : term43 = True.
Proof. exact (TRANS (@lem5135101) (@lem5135105)). Qed.
Lemma lem5135107 : True = term43.
Proof. exact (SYM (@lem5135106)). Qed.
Lemma lem5135108 : term43.
Proof. exact (EQ_MP (@lem5135107) (@lem0)). Qed.
