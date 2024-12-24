Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SING_term_abbrevs.
Require Import FINITE_INSERT_spec.
Require Import FINITE_RULES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem3608326 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem3608327 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3608329 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem3608330 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3608331 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3608330 A s) (@lem3608329 A s)). Qed.
Lemma lem3608332 {A : Type'} (s : A -> Prop) (x : A) : term2 A s x.
Proof. exact (@lem3608331 A s x). Qed.
Lemma lem3608333 {A : Type'} (x : A) (s : A -> Prop) : (term2 A s x) = ((term3 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term2 A s x)). Qed.
Lemma lem3608340 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3608333 A x s) (@lem3608332 A s x)). Qed.
Lemma lem3608341 {_92373 : Type'} (x : _92373) (s : _92373 -> Prop) : (term3 _92373 x s) = (@FINITE _92373 s).
Proof. exact (@lem3608340 _92373 x s). Qed.
Lemma lem3608342 {_92373 : Type'} (a : _92373) : (term4 _92373 a) = (@FINITE _92373 (@EMPTY _92373)).
Proof. exact (@lem3608341 _92373 a (@EMPTY _92373)). Qed.
Lemma lem3608344 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3608327 A) (@lem3608326 A)). Qed.
Lemma lem3608345 {_92373 : Type'} : (@FINITE _92373 (@EMPTY _92373)) = True.
Proof. exact (@lem3608344 _92373). Qed.
Lemma lem3608346 {_92373 : Type'} (a : _92373) : (term4 _92373 a) = True.
Proof. exact (TRANS (@lem3608342 _92373 a) (@lem3608345 _92373)). Qed.
Lemma lem3608347 {_92373 : Type'} : (term5 _92373) = (term6 _92373).
Proof. exact (fun_ext (fun a : _92373 => @lem3608346 _92373 a)). Qed.
Lemma lem3608348 {_92373 : Type'} : (@all _92373) = (@all _92373).
Proof. exact (eq_refl (@all _92373)). Qed.
Lemma lem3608349 {_92373 : Type'} : (term7 _92373) = (term8 _92373).
Proof. exact (MK_COMB (@lem3608348 _92373) (@lem3608347 _92373)). Qed.
Lemma lem3608351 {A : Type'} (t : Prop) : (term9 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3608352 {_92373 : Type'} (t : Prop) : (term9 _92373 t) = t.
Proof. exact (@lem3608351 _92373 t). Qed.
Lemma lem3608353 {_92373 : Type'} : (term8 _92373) = True.
Proof. exact (@lem3608352 _92373 True). Qed.
Lemma lem3608354 {_92373 : Type'} : (term7 _92373) = True.
Proof. exact (TRANS (@lem3608349 _92373) (@lem3608353 _92373)). Qed.
Lemma lem3608355 {_92373 : Type'} : True = (term7 _92373).
Proof. exact (SYM (@lem3608354 _92373)). Qed.
Lemma lem3608356 {_92373 : Type'} : term7 _92373.
Proof. exact (EQ_MP (@lem3608355 _92373) (@lem0)). Qed.
