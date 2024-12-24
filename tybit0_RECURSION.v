Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import tybit0_RECURSION_term_abbrevs.
Require Import thm7926680_spec.
Require Import thm7927969_spec.
Lemma lem7927983 {A Z : Type'} (f : type47 A Z) : term0 A Z f.
Proof. exact (@lem7926680 A Z f). Qed.
Lemma lem7927984 {A Z : Type'} (f : type47 A Z) : (term0 A Z f) = (term1 A Z f).
Proof. exact (eq_refl (term0 A Z f)). Qed.
Lemma lem7927985 {A Z : Type'} (f : type47 A Z) : term1 A Z f.
Proof. exact (EQ_MP (@lem7927984 A Z f) (@lem7927983 A Z f)). Qed.
Lemma lem7927986 {A Z : Type'} (f : type47 A Z) : (term2 A Z f) = (term2 A Z f).
Proof. exact (eq_refl (term2 A Z f)). Qed.
Lemma lem7927987 {A Z : Type'} (f : type47 A Z) : (term3 A Z f) = (term4 A Z f).
Proof. exact (MK_COMB (@lem7927986 A Z f) (@lem7927969 A)). Qed.
Lemma lem7927988 {A Z : Type'} (f : type47 A Z) : (term4 A Z f) = (term5 A Z f).
Proof. exact (eq_refl (term4 A Z f)). Qed.
Lemma lem7927989 {A Z : Type'} (f : type47 A Z) : (term6 A Z f) = (term6 A Z f).
Proof. exact (eq_refl (term6 A Z f)). Qed.
Lemma lem7927990 {A Z : Type'} (f : type47 A Z) : ((term3 A Z f) = (term4 A Z f)) = ((term3 A Z f) = (term5 A Z f)).
Proof. exact (MK_COMB (@lem7927989 A Z f) (@lem7927988 A Z f)). Qed.
Lemma lem7927991 {A Z : Type'} (f : type47 A Z) : (term3 A Z f) = (term1 A Z f).
Proof. exact (eq_refl (term3 A Z f)). Qed.
Lemma lem7927992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7927993 {A Z : Type'} (f : type47 A Z) : (term6 A Z f) = (term7 A Z f).
Proof. exact (MK_COMB (@lem7927992) (@lem7927991 A Z f)). Qed.
Lemma lem7927994 {A Z : Type'} (f : type47 A Z) : (term5 A Z f) = (term5 A Z f).
Proof. exact (eq_refl (term5 A Z f)). Qed.
Lemma lem7927995 {A Z : Type'} (f : type47 A Z) : ((term3 A Z f) = (term5 A Z f)) = ((term1 A Z f) = (term5 A Z f)).
Proof. exact (MK_COMB (@lem7927993 A Z f) (@lem7927994 A Z f)). Qed.
Lemma lem7927996 {A Z : Type'} (f : type47 A Z) : ((term3 A Z f) = (term4 A Z f)) = ((term1 A Z f) = (term5 A Z f)).
Proof. exact (TRANS (@lem7927990 A Z f) (@lem7927995 A Z f)). Qed.
Lemma lem7927997 {A Z : Type'} (f : type47 A Z) : (term1 A Z f) = (term5 A Z f).
Proof. exact (EQ_MP (@lem7927996 A Z f) (@lem7927987 A Z f)). Qed.
Lemma lem7927998 {A Z : Type'} (f : type47 A Z) : term5 A Z f.
Proof. exact (EQ_MP (@lem7927997 A Z f) (@lem7927985 A Z f)). Qed.
Lemma lem7927999 {A Z : Type'} : term8 A Z.
Proof. exact (fun f : type47 A Z => @lem7927998 A Z f). Qed.
