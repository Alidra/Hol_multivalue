Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1321215_term_abbrevs.
Require Import thm1317782_spec.
Require Import thm1317787_spec.
Require Import thm1318233_spec.
Require Import thm1318238_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1321194 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1321195 : term1 = (term2 = term3).
Proof. exact (@lem1321194 term4 term5). Qed.
Lemma lem1321199 (x : nadd) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem1318238 x) (@lem1318233 x)). Qed.
Lemma lem1321200 : term2 = term8.
Proof. exact (@lem1321199 term5). Qed.
Lemma lem1321202 (m : nat) : (term9 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1321203 : term3 = term10.
Proof. exact (@lem1321202 (NUMERAL 0)). Qed.
Lemma lem1321204 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1321205 : term8 = term11.
Proof. exact (MK_COMB (@lem1321204) (@lem1321203)). Qed.
Lemma lem1321206 : term2 = term11.
Proof. exact (TRANS (@lem1321200) (@lem1321205)). Qed.
Lemma lem1321207 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1321208 : term12 = term13.
Proof. exact (MK_COMB (@lem1321207) (@lem1321206)). Qed.
Lemma lem1321210 (m : nat) : (term9 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1321211 : term3 = term10.
Proof. exact (@lem1321210 (NUMERAL 0)). Qed.
Lemma lem1321212 : (term2 = term3) = (term11 = term10).
Proof. exact (MK_COMB (@lem1321208) (@lem1321211)). Qed.
Lemma lem1321215 : term1 = (term11 = term10).
Proof. exact (TRANS (@lem1321195) (@lem1321212)). Qed.
