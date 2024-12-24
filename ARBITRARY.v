Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_term_abbrevs.
Lemma lem4852980 {A : Type'} : (@ARBITRARY A) = (term0 A).
Proof. exact (@ARBITRARY_def A). Qed.
Lemma lem4852981 {A : Type'} (_60180 : type686 A) : _60180 = _60180.
Proof. exact (eq_refl _60180). Qed.
Lemma lem4852982 {A : Type'} (_60180 : type686 A) : (@ARBITRARY A _60180) = (term1 A _60180).
Proof. exact (MK_COMB (@lem4852980 A) (@lem4852981 A _60180)). Qed.
Lemma lem4852983 {A : Type'} (_60180 : type686 A) : (term1 A _60180) = True.
Proof. exact (eq_refl (term1 A _60180)). Qed.
Lemma lem4852984 {A : Type'} (_60180 : type686 A) : (@ARBITRARY A _60180) = True.
Proof. exact (TRANS (@lem4852982 A _60180) (@lem4852983 A _60180)). Qed.
Lemma lem4852985 {A : Type'} : term2 A.
Proof. exact (fun _60180 : type686 A => @lem4852984 A _60180). Qed.
Lemma lem4852986 {A : Type'} (_60180 : type686 A) : term3 A _60180.
Proof. exact (@lem4852985 A _60180). Qed.
Lemma lem4852987 {A : Type'} (_60180 : type686 A) : (term3 A _60180) = ((@ARBITRARY A _60180) = True).
Proof. exact (eq_refl (term3 A _60180)). Qed.
Lemma lem4852988 {A : Type'} (_60180 : type686 A) : (@ARBITRARY A _60180) = True.
Proof. exact (EQ_MP (@lem4852987 A _60180) (@lem4852986 A _60180)). Qed.
Lemma lem4853018 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4852988 A s). Qed.
Lemma lem4853019 {A : Type'} : term2 A.
Proof. exact (fun s : type686 A => @lem4853018 A s). Qed.
