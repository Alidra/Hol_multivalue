Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import char_RECURSION_term_abbrevs.
Require Import thm1241957_spec.
Require Import thm1242354_spec.
Lemma lem1242368 {Z : Type'} (f : type1540 Z) : term0 Z f.
Proof. exact (@lem1241957 Z f). Qed.
Lemma lem1242369 {Z : Type'} (f : type1540 Z) : (term0 Z f) = (term1 Z f).
Proof. exact (eq_refl (term0 Z f)). Qed.
Lemma lem1242370 {Z : Type'} (f : type1540 Z) : term1 Z f.
Proof. exact (EQ_MP (@lem1242369 Z f) (@lem1242368 Z f)). Qed.
Lemma lem1242371 {Z : Type'} (f : type1540 Z) : (term2 Z f) = (term2 Z f).
Proof. exact (eq_refl (term2 Z f)). Qed.
Lemma lem1242372 {Z : Type'} (f : type1540 Z) : (term3 Z f) = (term4 Z f).
Proof. exact (MK_COMB (@lem1242371 Z f) (@lem1242354)). Qed.
Lemma lem1242373 {Z : Type'} (f : type1540 Z) : (term4 Z f) = (term5 Z f).
Proof. exact (eq_refl (term4 Z f)). Qed.
Lemma lem1242374 {Z : Type'} (f : type1540 Z) : (term6 Z f) = (term6 Z f).
Proof. exact (eq_refl (term6 Z f)). Qed.
Lemma lem1242375 {Z : Type'} (f : type1540 Z) : ((term3 Z f) = (term4 Z f)) = ((term3 Z f) = (term5 Z f)).
Proof. exact (MK_COMB (@lem1242374 Z f) (@lem1242373 Z f)). Qed.
Lemma lem1242376 {Z : Type'} (f : type1540 Z) : (term3 Z f) = (term1 Z f).
Proof. exact (eq_refl (term3 Z f)). Qed.
Lemma lem1242377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1242378 {Z : Type'} (f : type1540 Z) : (term6 Z f) = (term7 Z f).
Proof. exact (MK_COMB (@lem1242377) (@lem1242376 Z f)). Qed.
Lemma lem1242379 {Z : Type'} (f : type1540 Z) : (term5 Z f) = (term5 Z f).
Proof. exact (eq_refl (term5 Z f)). Qed.
Lemma lem1242380 {Z : Type'} (f : type1540 Z) : ((term3 Z f) = (term5 Z f)) = ((term1 Z f) = (term5 Z f)).
Proof. exact (MK_COMB (@lem1242378 Z f) (@lem1242379 Z f)). Qed.
Lemma lem1242381 {Z : Type'} (f : type1540 Z) : ((term3 Z f) = (term4 Z f)) = ((term1 Z f) = (term5 Z f)).
Proof. exact (TRANS (@lem1242375 Z f) (@lem1242380 Z f)). Qed.
Lemma lem1242382 {Z : Type'} (f : type1540 Z) : (term1 Z f) = (term5 Z f).
Proof. exact (EQ_MP (@lem1242381 Z f) (@lem1242372 Z f)). Qed.
Lemma lem1242383 {Z : Type'} (f : type1540 Z) : term5 Z f.
Proof. exact (EQ_MP (@lem1242382 Z f) (@lem1242370 Z f)). Qed.
Lemma lem1242384 {Z : Type'} : term8 Z.
Proof. exact (fun f : type1540 Z => @lem1242383 Z f). Qed.
