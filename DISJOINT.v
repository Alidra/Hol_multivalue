Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_term_abbrevs.
Lemma lem3196049 {A : Type'} : (@DISJOINT A) = (term0 A).
Proof. exact (@DISJOINT_def A). Qed.
Lemma lem3196050 {A : Type'} (_32833 : A -> Prop) : _32833 = _32833.
Proof. exact (eq_refl _32833). Qed.
Lemma lem3196051 {A : Type'} (_32833 : A -> Prop) : (@DISJOINT A _32833) = (term1 A _32833).
Proof. exact (MK_COMB (@lem3196049 A) (@lem3196050 A _32833)). Qed.
Lemma lem3196052 {A : Type'} (_32833 : A -> Prop) : (term1 A _32833) = (term2 A _32833).
Proof. exact (eq_refl (term1 A _32833)). Qed.
Lemma lem3196053 {A : Type'} (_32833 : A -> Prop) : (@DISJOINT A _32833) = (term2 A _32833).
Proof. exact (TRANS (@lem3196051 A _32833) (@lem3196052 A _32833)). Qed.
Lemma lem3196054 {A : Type'} (_32834 : A -> Prop) : _32834 = _32834.
Proof. exact (eq_refl _32834). Qed.
Lemma lem3196055 {A : Type'} (_32833 : A -> Prop) (_32834 : A -> Prop) : (@DISJOINT A _32833 _32834) = (term3 A _32833 _32834).
Proof. exact (MK_COMB (@lem3196053 A _32833) (@lem3196054 A _32834)). Qed.
Lemma lem3196056 {A : Type'} (_32833 : A -> Prop) (_32834 : A -> Prop) : (term3 A _32833 _32834) = ((@INTER A _32833 _32834) = (@EMPTY A)).
Proof. exact (eq_refl (term3 A _32833 _32834)). Qed.
Lemma lem3196057 {A : Type'} (_32833 : A -> Prop) (_32834 : A -> Prop) : (@DISJOINT A _32833 _32834) = ((@INTER A _32833 _32834) = (@EMPTY A)).
Proof. exact (TRANS (@lem3196055 A _32833 _32834) (@lem3196056 A _32833 _32834)). Qed.
Lemma lem3196058 {A : Type'} (_32833 : A -> Prop) : term4 A _32833.
Proof. exact (fun _32834 : A -> Prop => @lem3196057 A _32833 _32834). Qed.
Lemma lem3196059 {A : Type'} : term5 A.
Proof. exact (fun _32833 : A -> Prop => @lem3196058 A _32833). Qed.
Lemma lem3196060 {A : Type'} (_32833 : A -> Prop) : term6 A _32833.
Proof. exact (@lem3196059 A _32833). Qed.
Lemma lem3196061 {A : Type'} (_32833 : A -> Prop) : (term6 A _32833) = (term4 A _32833).
Proof. exact (eq_refl (term6 A _32833)). Qed.
Lemma lem3196062 {A : Type'} (_32833 : A -> Prop) : term4 A _32833.
Proof. exact (EQ_MP (@lem3196061 A _32833) (@lem3196060 A _32833)). Qed.
Lemma lem3196063 {A : Type'} (_32833 : A -> Prop) (_32834 : A -> Prop) : term7 A _32833 _32834.
Proof. exact (@lem3196062 A _32833 _32834). Qed.
Lemma lem3196064 {A : Type'} (_32833 : A -> Prop) (_32834 : A -> Prop) : (term7 A _32833 _32834) = ((@DISJOINT A _32833 _32834) = ((@INTER A _32833 _32834) = (@EMPTY A))).
Proof. exact (eq_refl (term7 A _32833 _32834)). Qed.
Lemma lem3196065 {A : Type'} (_32833 : A -> Prop) (_32834 : A -> Prop) : (@DISJOINT A _32833 _32834) = ((@INTER A _32833 _32834) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3196064 A _32833 _32834) (@lem3196063 A _32833 _32834)). Qed.
Lemma lem3196108 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3196065 A s t). Qed.
Lemma lem3196109 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (fun t : A -> Prop => @lem3196108 A s t). Qed.
Lemma lem3196110 {A : Type'} : term5 A.
Proof. exact (fun s : A -> Prop => @lem3196109 A s). Qed.
