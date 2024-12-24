Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm51073_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Lemma lem51069 {A B : Type'} (f : A -> B) (y : A) : (term0 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem51070 {_5146 _5153 _5154 : Type'} (f : type1228 _5146 _5153 _5154) (y : prod _5154 _5153) : (term1 _5146 _5153 _5154 f y) = (f y).
Proof. exact (@lem51069 (prod _5154 _5153) _5146 f y). Qed.
Lemma lem51071 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) (p2 : _5153) : (term2 _5146 _5153 _5154 t p1 p2) = (term3 _5146 _5153 _5154 t p1 p2).
Proof. exact (@lem51070 _5146 _5153 _5154 t (@pair _5154 _5153 p1 p2)). Qed.
Lemma lem51072 {_5146 : Type'} : (@eq _5146) = (@eq _5146).
Proof. exact (eq_refl (@eq _5146)). Qed.
Lemma lem51073 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) (p2 : _5153) : (term4 _5146 _5153 _5154 t p1 p2) = (term5 _5146 _5153 _5154 t p1 p2).
Proof. exact (MK_COMB (@lem51072 _5146) (@lem51071 _5146 _5153 _5154 t p1 p2)). Qed.
