Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import pair_RECURSION_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem48127 {A B : Type'} (x : A) : term0 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem48128 {A B : Type'} (x : A) : (term0 A B x) = (term1 A B x).
Proof. exact (eq_refl (term0 A B x)). Qed.
Lemma lem48129 {A B : Type'} (x : A) : term1 A B x.
Proof. exact (EQ_MP (@lem48128 A B x) (@lem48127 A B x)). Qed.
Lemma lem48130 {A B : Type'} (x : A) (y : B) : term2 A B x y.
Proof. exact (@lem48129 A B x y). Qed.
Lemma lem48131 {A B : Type'} (x : A) (y : B) : (term2 A B x y) = ((term3 A B x y) = y).
Proof. exact (eq_refl (term2 A B x y)). Qed.
Lemma lem48133 {A B : Type'} (x : A) : term4 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem48134 {A B : Type'} (x : A) : (term4 A B x) = (term5 A B x).
Proof. exact (eq_refl (term4 A B x)). Qed.
Lemma lem48135 {A B : Type'} (x : A) : term5 A B x.
Proof. exact (EQ_MP (@lem48134 A B x) (@lem48133 A B x)). Qed.
Lemma lem48136 {A B : Type'} (x : A) (y : B) : term6 A B x y.
Proof. exact (@lem48135 A B x y). Qed.
Lemma lem48137 {A B : Type'} (y : B) (x : A) : (term6 A B x y) = ((term7 A B x y) = x).
Proof. exact (eq_refl (term6 A B x y)). Qed.
Lemma lem48150 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem48151 {A B C : Type'} (f : type1209 A B C) (y : prod A B) : (term9 A B C f y) = (f y).
Proof. exact (@lem48150 (prod A B) C f y). Qed.
Lemma lem48152 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : (term10 A B C PAIR' a0 a1) = (term11 A B C PAIR' a0 a1).
Proof. exact (@lem48151 A B C (term12 A B C PAIR') (@pair A B a0 a1)). Qed.
Lemma lem48153 {A B C : Type'} (PAIR' : type1412 A B C) (p : prod A B) : (term13 A B C PAIR' p) = (term14 A B C PAIR' p).
Proof. exact (eq_refl (term13 A B C PAIR' p)). Qed.
Lemma lem48154 {A B C : Type'} (PAIR' : type1412 A B C) : (term15 A B C PAIR') = (term12 A B C PAIR').
Proof. exact (fun_ext (fun p : prod A B => @lem48153 A B C PAIR' p)). Qed.
Lemma lem48155 {A B : Type'} (a0 : A) (a1 : B) : (@pair A B a0 a1) = (@pair A B a0 a1).
Proof. exact (eq_refl (@pair A B a0 a1)). Qed.
Lemma lem48156 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : (term10 A B C PAIR' a0 a1) = (term11 A B C PAIR' a0 a1).
Proof. exact (MK_COMB (@lem48154 A B C PAIR') (@lem48155 A B a0 a1)). Qed.
Lemma lem48157 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem48158 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : (term16 A B C PAIR' a0 a1) = (term17 A B C PAIR' a0 a1).
Proof. exact (MK_COMB (@lem48157 C) (@lem48156 A B C PAIR' a0 a1)). Qed.
Lemma lem48159 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : (term11 A B C PAIR' a0 a1) = (term18 A B C PAIR' a0 a1).
Proof. exact (eq_refl (term11 A B C PAIR' a0 a1)). Qed.
Lemma lem48160 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : ((term10 A B C PAIR' a0 a1) = (term11 A B C PAIR' a0 a1)) = ((term11 A B C PAIR' a0 a1) = (term18 A B C PAIR' a0 a1)).
Proof. exact (MK_COMB (@lem48158 A B C PAIR' a0 a1) (@lem48159 A B C PAIR' a0 a1)). Qed.
Lemma lem48161 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : (term11 A B C PAIR' a0 a1) = (term18 A B C PAIR' a0 a1).
Proof. exact (EQ_MP (@lem48160 A B C PAIR' a0 a1) (@lem48152 A B C PAIR' a0 a1)). Qed.
Lemma lem48163 {A B : Type'} (y : B) (x : A) : (term7 A B x y) = x.
Proof. exact (EQ_MP (@lem48137 A B y x) (@lem48136 A B x y)). Qed.
Lemma lem48164 {A B : Type'} (y : B) (x : A) : (term7 A B x y) = x.
Proof. exact (@lem48163 A B y x). Qed.
Lemma lem48165 {A B : Type'} (a1 : B) (a0 : A) : (term7 A B a0 a1) = a0.
Proof. exact (@lem48164 A B a1 a0). Qed.
Lemma lem48166 {A B C : Type'} (PAIR' : type1412 A B C) : PAIR' = PAIR'.
Proof. exact (eq_refl PAIR'). Qed.
Lemma lem48167 {A B C : Type'} (a1 : B) (PAIR' : type1412 A B C) (a0 : A) : (term19 A B C PAIR' a0 a1) = (PAIR' a0).
Proof. exact (MK_COMB (@lem48166 A B C PAIR') (@lem48165 A B a1 a0)). Qed.
Lemma lem48169 {A B : Type'} (x : A) (y : B) : (term3 A B x y) = y.
Proof. exact (EQ_MP (@lem48131 A B x y) (@lem48130 A B x y)). Qed.
Lemma lem48170 {A B : Type'} (x : A) (y : B) : (term3 A B x y) = y.
Proof. exact (@lem48169 A B x y). Qed.
Lemma lem48171 {A B : Type'} (a0 : A) (a1 : B) : (term3 A B a0 a1) = a1.
Proof. exact (@lem48170 A B a0 a1). Qed.
Lemma lem48172 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : (term18 A B C PAIR' a0 a1) = (PAIR' a0 a1).
Proof. exact (MK_COMB (@lem48167 A B C a1 PAIR' a0) (@lem48171 A B a0 a1)). Qed.
Lemma lem48173 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : (term11 A B C PAIR' a0 a1) = (PAIR' a0 a1).
Proof. exact (TRANS (@lem48161 A B C PAIR' a0 a1) (@lem48172 A B C PAIR' a0 a1)). Qed.
Lemma lem48174 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem48175 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : (term17 A B C PAIR' a0 a1) = (term20 A B C PAIR' a0 a1).
Proof. exact (MK_COMB (@lem48174 C) (@lem48173 A B C PAIR' a0 a1)). Qed.
Lemma lem48176 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : (PAIR' a0 a1) = (PAIR' a0 a1).
Proof. exact (eq_refl (PAIR' a0 a1)). Qed.
Lemma lem48177 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : ((term11 A B C PAIR' a0 a1) = (PAIR' a0 a1)) = ((PAIR' a0 a1) = (PAIR' a0 a1)).
Proof. exact (MK_COMB (@lem48175 A B C PAIR' a0 a1) (@lem48176 A B C PAIR' a0 a1)). Qed.
Lemma lem48179 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem48180 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem48179 C x). Qed.
Lemma lem48181 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : ((PAIR' a0 a1) = (PAIR' a0 a1)) = True.
Proof. exact (@lem48180 C (PAIR' a0 a1)). Qed.
Lemma lem48182 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) (a1 : B) : ((term11 A B C PAIR' a0 a1) = (PAIR' a0 a1)) = True.
Proof. exact (TRANS (@lem48177 A B C PAIR' a0 a1) (@lem48181 A B C PAIR' a0 a1)). Qed.
Lemma lem48183 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) : (term21 A B C PAIR' a0) = (term22 B).
Proof. exact (fun_ext (fun a1 : B => @lem48182 A B C PAIR' a0 a1)). Qed.
Lemma lem48184 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem48185 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) : (term23 A B C PAIR' a0) = (term24 B).
Proof. exact (MK_COMB (@lem48184 B) (@lem48183 A B C PAIR' a0)). Qed.
Lemma lem48187 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem48188 {B : Type'} (t : Prop) : (term25 B t) = t.
Proof. exact (@lem48187 B t). Qed.
Lemma lem48189 {B : Type'} : (term24 B) = True.
Proof. exact (@lem48188 B True). Qed.
Lemma lem48190 {A B C : Type'} (PAIR' : type1412 A B C) (a0 : A) : (term23 A B C PAIR' a0) = True.
Proof. exact (TRANS (@lem48185 A B C PAIR' a0) (@lem48189 B)). Qed.
Lemma lem48191 {A B C : Type'} (PAIR' : type1412 A B C) : (term26 A B C PAIR') = (term22 A).
Proof. exact (fun_ext (fun a0 : A => @lem48190 A B C PAIR' a0)). Qed.
Lemma lem48192 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem48193 {A B C : Type'} (PAIR' : type1412 A B C) : (term27 A B C PAIR') = (term24 A).
Proof. exact (MK_COMB (@lem48192 A) (@lem48191 A B C PAIR')). Qed.
Lemma lem48195 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem48196 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (@lem48195 A t). Qed.
Lemma lem48197 {A : Type'} : (term24 A) = True.
Proof. exact (@lem48196 A True). Qed.
Lemma lem48198 {A B C : Type'} (PAIR' : type1412 A B C) : (term27 A B C PAIR') = True.
Proof. exact (TRANS (@lem48193 A B C PAIR') (@lem48197 A)). Qed.
Lemma lem48199 {A B C : Type'} (PAIR' : type1412 A B C) : True = (term27 A B C PAIR').
Proof. exact (SYM (@lem48198 A B C PAIR')). Qed.
Lemma lem48200 {A B C : Type'} (PAIR' : type1412 A B C) : term27 A B C PAIR'.
Proof. exact (EQ_MP (@lem48199 A B C PAIR') (@lem0)). Qed.
Lemma lem48201 {A B C : Type'} (PAIR' : type1412 A B C) : term28 A B C PAIR'.
Proof. exact (ex_intro (term29 A B C PAIR') (term12 A B C PAIR') (@lem48200 A B C PAIR')). Qed.
Lemma lem48206 {A B C : Type'} : term30 A B C.
Proof. exact (fun PAIR' : type1412 A B C => @lem48201 A B C PAIR'). Qed.
