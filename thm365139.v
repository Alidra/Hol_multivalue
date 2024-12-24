Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm365139_term_abbrevs.
Require Import num_WF_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm307612_spec.
Require Import thm309905_spec.
Require Import thm7_spec.
Lemma lem365115 (P : nat -> Prop) : term0 P.
Proof. exact (@lem115780 P). Qed.
Lemma lem365116 (P : nat -> Prop) : (term0 P) = (term1 P).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem365117 (P : nat -> Prop) : term1 P.
Proof. exact (EQ_MP (@lem365116 P) (@lem365115 P)). Qed.
Lemma lem365118 (P : nat -> Prop) : (term1 P) = ((term1 P) = True).
Proof. exact (@lem7 (term1 P)). Qed.
Lemma lem365121 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term2 A lt2).
Proof. exact (EQ_MP (@lem307612 A lt2) (@lem309905 A lt2)). Qed.
Lemma lem365122 (lt2 : type1605) : (@WF nat lt2) = (term3 lt2).
Proof. exact (@lem365121 nat lt2). Qed.
Lemma lem365123 : (@WF nat Peano.lt) = term4.
Proof. exact (@lem365122 Peano.lt). Qed.
Lemma lem365129 (P : nat -> Prop) : (term1 P) = True.
Proof. exact (EQ_MP (@lem365118 P) (@lem365117 P)). Qed.
Lemma lem365130 : term5 = term6.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem365129 P)). Qed.
Lemma lem365131 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem365132 : term4 = term7.
Proof. exact (MK_COMB (@lem365131) (@lem365130)). Qed.
Lemma lem365134 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem365135 (t : Prop) : (term9 t) = t.
Proof. exact (@lem365134 (nat -> Prop) t). Qed.
Lemma lem365136 : term7 = True.
Proof. exact (@lem365135 True). Qed.
Lemma lem365137 : term4 = True.
Proof. exact (TRANS (@lem365132) (@lem365136)). Qed.
Lemma lem365138 : (@WF nat Peano.lt) = True.
Proof. exact (TRANS (@lem365123) (@lem365137)). Qed.
Lemma lem365139 : True = (@WF nat Peano.lt).
Proof. exact (SYM (@lem365138)). Qed.
