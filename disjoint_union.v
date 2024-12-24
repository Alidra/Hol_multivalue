Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import disjoint_union_term_abbrevs.
Lemma lem4464403 {A K : Type'} : (@disjoint_union A K) = (term0 A K).
Proof. exact (@disjoint_union_def A K). Qed.
Lemma lem4464404 {K : Type'} (_51662 : K -> Prop) : _51662 = _51662.
Proof. exact (eq_refl _51662). Qed.
Lemma lem4464405 {A K : Type'} (_51662 : K -> Prop) : (@disjoint_union A K _51662) = (term1 A K _51662).
Proof. exact (MK_COMB (@lem4464403 A K) (@lem4464404 K _51662)). Qed.
Lemma lem4464406 {A K : Type'} (_51662 : K -> Prop) : (term1 A K _51662) = (term2 A K _51662).
Proof. exact (eq_refl (term1 A K _51662)). Qed.
Lemma lem4464407 {A K : Type'} (_51662 : K -> Prop) : (@disjoint_union A K _51662) = (term2 A K _51662).
Proof. exact (TRANS (@lem4464405 A K _51662) (@lem4464406 A K _51662)). Qed.
Lemma lem4464408 {A K : Type'} (_51663 : type1470 A K) : _51663 = _51663.
Proof. exact (eq_refl _51663). Qed.
Lemma lem4464409 {A K : Type'} (_51662 : K -> Prop) (_51663 : type1470 A K) : (@disjoint_union A K _51662 _51663) = (term3 A K _51662 _51663).
Proof. exact (MK_COMB (@lem4464407 A K _51662) (@lem4464408 A K _51663)). Qed.
Lemma lem4464410 {A K : Type'} (_51662 : K -> Prop) (_51663 : type1470 A K) : (term3 A K _51662 _51663) = (term4 A K _51662 _51663).
Proof. exact (eq_refl (term3 A K _51662 _51663)). Qed.
Lemma lem4464411 {A K : Type'} (_51662 : K -> Prop) (_51663 : type1470 A K) : (@disjoint_union A K _51662 _51663) = (term4 A K _51662 _51663).
Proof. exact (TRANS (@lem4464409 A K _51662 _51663) (@lem4464410 A K _51662 _51663)). Qed.
Lemma lem4464412 {A K : Type'} (_51662 : K -> Prop) : term5 A K _51662.
Proof. exact (fun _51663 : type1470 A K => @lem4464411 A K _51662 _51663). Qed.
Lemma lem4464413 {A K : Type'} : term6 A K.
Proof. exact (fun _51662 : K -> Prop => @lem4464412 A K _51662). Qed.
Lemma lem4464414 {A K : Type'} (_51662 : K -> Prop) : term7 A K _51662.
Proof. exact (@lem4464413 A K _51662). Qed.
Lemma lem4464415 {A K : Type'} (_51662 : K -> Prop) : (term7 A K _51662) = (term5 A K _51662).
Proof. exact (eq_refl (term7 A K _51662)). Qed.
Lemma lem4464416 {A K : Type'} (_51662 : K -> Prop) : term5 A K _51662.
Proof. exact (EQ_MP (@lem4464415 A K _51662) (@lem4464414 A K _51662)). Qed.
Lemma lem4464417 {A K : Type'} (_51662 : K -> Prop) (_51663 : type1470 A K) : term8 A K _51662 _51663.
Proof. exact (@lem4464416 A K _51662 _51663). Qed.
Lemma lem4464418 {A K : Type'} (_51662 : K -> Prop) (_51663 : type1470 A K) : (term8 A K _51662 _51663) = ((@disjoint_union A K _51662 _51663) = (term4 A K _51662 _51663)).
Proof. exact (eq_refl (term8 A K _51662 _51663)). Qed.
Lemma lem4464419 {A K : Type'} (_51662 : K -> Prop) (_51663 : type1470 A K) : (@disjoint_union A K _51662 _51663) = (term4 A K _51662 _51663).
Proof. exact (EQ_MP (@lem4464418 A K _51662 _51663) (@lem4464417 A K _51662 _51663)). Qed.
Lemma lem4464462 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term4 A K k s).
Proof. exact (@lem4464419 A K k s). Qed.
Lemma lem4464463 {A K : Type'} (k : K -> Prop) : term5 A K k.
Proof. exact (fun s : type1470 A K => @lem4464462 A K k s). Qed.
Lemma lem4464464 {A K : Type'} : term6 A K.
Proof. exact (fun k : K -> Prop => @lem4464463 A K k). Qed.
