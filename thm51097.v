Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm51097_term_abbrevs.
Require Import pair_RECURSION_spec.
Lemma lem51074 {A B C : Type'} (PAIR' : type1412 A B C) : term0 A B C PAIR'.
Proof. exact (@lem48206 A B C PAIR'). Qed.
Lemma lem51075 {A B C : Type'} (PAIR' : type1412 A B C) : (term0 A B C PAIR') = (term1 A B C PAIR').
Proof. exact (eq_refl (term0 A B C PAIR')). Qed.
Lemma lem51076 {A B C : Type'} (PAIR' : type1412 A B C) : term1 A B C PAIR'.
Proof. exact (EQ_MP (@lem51075 A B C PAIR') (@lem51074 A B C PAIR')). Qed.
Lemma lem51077 {A B C : Type'} (_1393 : type1412 A B C) : term2 A B C _1393.
Proof. exact (@lem51076 A B C (term3 A B C _1393)). Qed.
Lemma lem51078 {A B C : Type'} (fn : type1209 A B C) (_1393 : type1412 A B C) (h1 : term4 A B C fn _1393) : term4 A B C fn _1393.
Proof. exact (h1). Qed.
Lemma lem51079 {A B C : Type'} (_1393 : type1412 A B C) (a0 : A) : (term5 A B C _1393 a0) = (term6 A B C _1393 a0).
Proof. exact (eq_refl (term5 A B C _1393 a0)). Qed.
Lemma lem51080 {B : Type'} (a1 : B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem51081 {A B C : Type'} (_1393 : type1412 A B C) (a0 : A) (a1 : B) : (term7 A B C _1393 a0 a1) = (term8 A B C _1393 a0 a1).
Proof. exact (MK_COMB (@lem51079 A B C _1393 a0) (@lem51080 B a1)). Qed.
Lemma lem51082 {A B C : Type'} (_1393 : type1412 A B C) (a0 : A) (a1 : B) : (term8 A B C _1393 a0 a1) = (_1393 a0 a1).
Proof. exact (eq_refl (term8 A B C _1393 a0 a1)). Qed.
Lemma lem51083 {A B C : Type'} (_1393 : type1412 A B C) (a0 : A) (a1 : B) : (term7 A B C _1393 a0 a1) = (_1393 a0 a1).
Proof. exact (TRANS (@lem51081 A B C _1393 a0 a1) (@lem51082 A B C _1393 a0 a1)). Qed.
Lemma lem51084 {A B C : Type'} (fn : type1209 A B C) (a0 : A) (a1 : B) : (term9 A B C fn a0 a1) = (term9 A B C fn a0 a1).
Proof. exact (eq_refl (term9 A B C fn a0 a1)). Qed.
Lemma lem51085 {A B C : Type'} (fn : type1209 A B C) (_1393 : type1412 A B C) (a0 : A) (a1 : B) : ((term10 A B C fn a0 a1) = (term7 A B C _1393 a0 a1)) = ((term10 A B C fn a0 a1) = (_1393 a0 a1)).
Proof. exact (MK_COMB (@lem51084 A B C fn a0 a1) (@lem51083 A B C _1393 a0 a1)). Qed.
Lemma lem51086 {A B C : Type'} (fn : type1209 A B C) (_1393 : type1412 A B C) (a0 : A) : (term11 A B C fn _1393 a0) = (term12 A B C fn _1393 a0).
Proof. exact (fun_ext (fun a1 : B => @lem51085 A B C fn _1393 a0 a1)). Qed.
Lemma lem51087 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51088 {A B C : Type'} (fn : type1209 A B C) (_1393 : type1412 A B C) (a0 : A) : (term13 A B C fn _1393 a0) = (term14 A B C fn _1393 a0).
Proof. exact (MK_COMB (@lem51087 B) (@lem51086 A B C fn _1393 a0)). Qed.
Lemma lem51089 {A B C : Type'} (fn : type1209 A B C) (_1393 : type1412 A B C) : (term15 A B C fn _1393) = (term16 A B C fn _1393).
Proof. exact (fun_ext (fun a0 : A => @lem51088 A B C fn _1393 a0)). Qed.
Lemma lem51090 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51091 {A B C : Type'} (fn : type1209 A B C) (_1393 : type1412 A B C) : (term4 A B C fn _1393) = (term17 A B C fn _1393).
Proof. exact (MK_COMB (@lem51090 A) (@lem51089 A B C fn _1393)). Qed.
Lemma lem51092 {A B C : Type'} (fn : type1209 A B C) (_1393 : type1412 A B C) (h1 : term4 A B C fn _1393) : term17 A B C fn _1393.
Proof. exact (EQ_MP (@lem51091 A B C fn _1393) (@lem51078 A B C fn _1393 h1)). Qed.
Lemma lem51093 {A B C : Type'} (fn : type1209 A B C) (_1393 : type1412 A B C) (h1 : term4 A B C fn _1393) : term1 A B C _1393.
Proof. exact (ex_intro (term18 A B C _1393) fn (@lem51092 A B C fn _1393 h1)). Qed.
Lemma lem51094 {A B C : Type'} (_1393 : type1412 A B C) (h1 : term2 A B C _1393) : term2 A B C _1393.
Proof. exact (h1). Qed.
Lemma lem51095 {A B C : Type'} (_1393 : type1412 A B C) (h1 : term2 A B C _1393) : term1 A B C _1393.
Proof. exact (ex_elim (@lem51094 A B C _1393 h1) (fun fn : type1209 A B C => fun h0 : term19 A B C _1393 fn => @lem51093 A B C fn _1393 h0)). Qed.
Lemma lem51096 {A B C : Type'} (_1393 : type1412 A B C) : (term2 A B C _1393) = (term1 A B C _1393).
Proof. exact (prop_ext (fun h1 : term2 A B C _1393 => @lem51095 A B C _1393 h1) (fun h1 : term1 A B C _1393 => @lem51077 A B C _1393)). Qed.
Lemma lem51097 {A B C : Type'} (_1393 : type1412 A B C) : term1 A B C _1393.
Proof. exact (EQ_MP (@lem51096 A B C _1393) (@lem51077 A B C _1393)). Qed.
