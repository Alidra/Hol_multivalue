Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_SUBR2_term_abbrevs.
Require Import LE_ADD_spec.
Require Import SUB_EQ_0_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem136260 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem136261 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem136262 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem136261 m) (@lem136260 m)). Qed.
Lemma lem136263 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem136262 m n). Qed.
Lemma lem136264 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem136265 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem136264 m n) (@lem136263 m n)). Qed.
Lemma lem136266 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem136268 (m : nat) : term4 m.
Proof. exact (@lem136259 m). Qed.
Lemma lem136269 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem136270 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem136269 m) (@lem136268 m)). Qed.
Lemma lem136271 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem136270 m n). Qed.
Lemma lem136272 (m : nat) (n : nat) : (term6 m n) = (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem136283 (m : nat) (n : nat) : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n).
Proof. exact (EQ_MP (@lem136272 m n) (@lem136271 m n)). Qed.
Lemma lem136284 (m : nat) (n : nat) : ((term7 m n) = (NUMERAL 0)) = (term3 m n).
Proof. exact (@lem136283 m (Nat.add m n)). Qed.
Lemma lem136286 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem136266 m n) (@lem136265 m n)). Qed.
Lemma lem136287 (m : nat) (n : nat) : ((term7 m n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem136284 m n) (@lem136286 m n)). Qed.
Lemma lem136288 (m : nat) : (term8 m) = term9.
Proof. exact (fun_ext (fun n : nat => @lem136287 m n)). Qed.
Lemma lem136289 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136290 (m : nat) : (term10 m) = term11.
Proof. exact (MK_COMB (@lem136289) (@lem136288 m)). Qed.
Lemma lem136292 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem136293 (t : Prop) : (term13 t) = t.
Proof. exact (@lem136292 nat t). Qed.
Lemma lem136294 : term11 = True.
Proof. exact (@lem136293 True). Qed.
Lemma lem136295 (m : nat) : (term10 m) = True.
Proof. exact (TRANS (@lem136290 m) (@lem136294)). Qed.
Lemma lem136296 : term14 = term9.
Proof. exact (fun_ext (fun m : nat => @lem136295 m)). Qed.
Lemma lem136297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136298 : term15 = term11.
Proof. exact (MK_COMB (@lem136297) (@lem136296)). Qed.
Lemma lem136300 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem136301 (t : Prop) : (term13 t) = t.
Proof. exact (@lem136300 nat t). Qed.
Lemma lem136302 : term11 = True.
Proof. exact (@lem136301 True). Qed.
Lemma lem136303 : term15 = True.
Proof. exact (TRANS (@lem136298) (@lem136302)). Qed.
Lemma lem136304 : True = term15.
Proof. exact (SYM (@lem136303)). Qed.
Lemma lem136305 : term15.
Proof. exact (EQ_MP (@lem136304) (@lem0)). Qed.
