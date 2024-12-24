Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import product_map_term_abbrevs.
Lemma lem4456691 {A B K : Type'} : (@product_map A B K) = (term0 A B K).
Proof. exact (@product_map_def A B K). Qed.
Lemma lem4456692 {K : Type'} (_51526 : K -> Prop) : _51526 = _51526.
Proof. exact (eq_refl _51526). Qed.
Lemma lem4456693 {A B K : Type'} (_51526 : K -> Prop) : (@product_map A B K _51526) = (term1 A B K _51526).
Proof. exact (MK_COMB (@lem4456691 A B K) (@lem4456692 K _51526)). Qed.
Lemma lem4456694 {A B K : Type'} (_51526 : K -> Prop) : (term1 A B K _51526) = (term2 A B K _51526).
Proof. exact (eq_refl (term1 A B K _51526)). Qed.
Lemma lem4456695 {A B K : Type'} (_51526 : K -> Prop) : (@product_map A B K _51526) = (term2 A B K _51526).
Proof. exact (TRANS (@lem4456693 A B K _51526) (@lem4456694 A B K _51526)). Qed.
Lemma lem4456696 {A B K : Type'} (_51527 : type1514 A B K) : _51527 = _51527.
Proof. exact (eq_refl _51527). Qed.
Lemma lem4456697 {A B K : Type'} (_51526 : K -> Prop) (_51527 : type1514 A B K) : (@product_map A B K _51526 _51527) = (term3 A B K _51526 _51527).
Proof. exact (MK_COMB (@lem4456695 A B K _51526) (@lem4456696 A B K _51527)). Qed.
Lemma lem4456698 {A B K : Type'} (_51526 : K -> Prop) (_51527 : type1514 A B K) : (term3 A B K _51526 _51527) = (term4 A B K _51526 _51527).
Proof. exact (eq_refl (term3 A B K _51526 _51527)). Qed.
Lemma lem4456699 {A B K : Type'} (_51526 : K -> Prop) (_51527 : type1514 A B K) : (@product_map A B K _51526 _51527) = (term4 A B K _51526 _51527).
Proof. exact (TRANS (@lem4456697 A B K _51526 _51527) (@lem4456698 A B K _51526 _51527)). Qed.
Lemma lem4456700 {A B K : Type'} (_51526 : K -> Prop) : term5 A B K _51526.
Proof. exact (fun _51527 : type1514 A B K => @lem4456699 A B K _51526 _51527). Qed.
Lemma lem4456701 {A B K : Type'} : term6 A B K.
Proof. exact (fun _51526 : K -> Prop => @lem4456700 A B K _51526). Qed.
Lemma lem4456702 {A B K : Type'} (_51526 : K -> Prop) : term7 A B K _51526.
Proof. exact (@lem4456701 A B K _51526). Qed.
Lemma lem4456703 {A B K : Type'} (_51526 : K -> Prop) : (term7 A B K _51526) = (term5 A B K _51526).
Proof. exact (eq_refl (term7 A B K _51526)). Qed.
Lemma lem4456704 {A B K : Type'} (_51526 : K -> Prop) : term5 A B K _51526.
Proof. exact (EQ_MP (@lem4456703 A B K _51526) (@lem4456702 A B K _51526)). Qed.
Lemma lem4456705 {A B K : Type'} (_51526 : K -> Prop) (_51527 : type1514 A B K) : term8 A B K _51526 _51527.
Proof. exact (@lem4456704 A B K _51526 _51527). Qed.
Lemma lem4456706 {A B K : Type'} (_51526 : K -> Prop) (_51527 : type1514 A B K) : (term8 A B K _51526 _51527) = ((@product_map A B K _51526 _51527) = (term4 A B K _51526 _51527)).
Proof. exact (eq_refl (term8 A B K _51526 _51527)). Qed.
Lemma lem4456707 {A B K : Type'} (_51526 : K -> Prop) (_51527 : type1514 A B K) : (@product_map A B K _51526 _51527) = (term4 A B K _51526 _51527).
Proof. exact (EQ_MP (@lem4456706 A B K _51526 _51527) (@lem4456705 A B K _51526 _51527)). Qed.
Lemma lem4456750 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (@product_map A B K k f) = (term4 A B K k f).
Proof. exact (@lem4456707 A B K k f). Qed.
Lemma lem4456751 {A B K : Type'} (k : K -> Prop) : term5 A B K k.
Proof. exact (fun f : type1514 A B K => @lem4456750 A B K k f). Qed.
Lemma lem4456752 {A B K : Type'} : term6 A B K.
Proof. exact (fun k : K -> Prop => @lem4456751 A B K k). Qed.
