Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FACT_LE_term_abbrevs.
Require Import FACT_LT_spec.
Require Import LE_SUC_LT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Require Import thm80360_spec.
Lemma lem146213 (n : nat) : term0 n.
Proof. exact (@lem146212 n). Qed.
Lemma lem146214 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem146215 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem146214 n) (@lem146213 n)). Qed.
Lemma lem146216 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem146218 (m : nat) : term2 m.
Proof. exact (@lem91144 m). Qed.
Lemma lem146219 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem146220 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem146219 m) (@lem146218 m)). Qed.
Lemma lem146221 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem146220 m n). Qed.
Lemma lem146222 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem146229 : term6 = term7.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem146230 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem146231 : term8 = term9.
Proof. exact (MK_COMB (@lem146230) (@lem146229)). Qed.
Lemma lem146232 (n : nat) : (Factorial.fact n) = (Factorial.fact n).
Proof. exact (eq_refl (Factorial.fact n)). Qed.
Lemma lem146233 (n : nat) : (term10 n) = (term11 n).
Proof. exact (MK_COMB (@lem146231) (@lem146232 n)). Qed.
Lemma lem146235 (m : nat) (n : nat) : (term5 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem146222 m n) (@lem146221 m n)). Qed.
Lemma lem146236 (n : nat) : (term11 n) = (term1 n).
Proof. exact (@lem146235 (NUMERAL 0) (Factorial.fact n)). Qed.
Lemma lem146238 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem146216 n) (@lem146215 n)). Qed.
Lemma lem146239 (n : nat) : (term11 n) = True.
Proof. exact (TRANS (@lem146236 n) (@lem146238 n)). Qed.
Lemma lem146240 (n : nat) : (term10 n) = True.
Proof. exact (TRANS (@lem146233 n) (@lem146239 n)). Qed.
Lemma lem146241 : term12 = term13.
Proof. exact (fun_ext (fun n : nat => @lem146240 n)). Qed.
Lemma lem146242 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146243 : term14 = term15.
Proof. exact (MK_COMB (@lem146242) (@lem146241)). Qed.
Lemma lem146245 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem146246 (t : Prop) : (term17 t) = t.
Proof. exact (@lem146245 nat t). Qed.
Lemma lem146247 : term15 = True.
Proof. exact (@lem146246 True). Qed.
Lemma lem146248 : term14 = True.
Proof. exact (TRANS (@lem146243) (@lem146247)). Qed.
Lemma lem146249 : True = term14.
Proof. exact (SYM (@lem146248)). Qed.
Lemma lem146250 : term14.
Proof. exact (EQ_MP (@lem146249) (@lem0)). Qed.
