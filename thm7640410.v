Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7640410_term_abbrevs.
Require Import dimindex_spec.
Lemma lem7640399 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem7590231 A s). Qed.
Lemma lem7640400 {A : Type'} (s : A -> Prop) : (term0 A s) = ((@dimindex A s) = (term1 A)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem7640403 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term1 A).
Proof. exact (EQ_MP (@lem7640400 A s) (@lem7640399 A s)). Qed.
Lemma lem7640404 {M N : Type'} (s : type49 M N) : (@dimindex (finite_sum M N) s) = (term2 M N).
Proof. exact (@lem7640403 (finite_sum M N) s). Qed.
Lemma lem7640405 {M N : Type'} : (@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term2 M N).
Proof. exact (@lem7640404 M N (@UNIV (finite_sum M N))). Qed.
Lemma lem7640406 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7640407 {M N : Type'} : (term3 M N) = (term4 M N).
Proof. exact (MK_COMB (@lem7640406) (@lem7640405 M N)). Qed.
Lemma lem7640408 {M N : Type'} : (term5 M N) = (term5 M N).
Proof. exact (eq_refl (term5 M N)). Qed.
Lemma lem7640409 {M N : Type'} : ((@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term5 M N)) = ((term2 M N) = (term5 M N)).
Proof. exact (MK_COMB (@lem7640407 M N) (@lem7640408 M N)). Qed.
Lemma lem7640410 {M N : Type'} : ((term2 M N) = (term5 M N)) = ((@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term5 M N)).
Proof. exact (SYM (@lem7640409 M N)). Qed.
