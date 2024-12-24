Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_LADD_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import ADD_SUB2_spec.
Require Import ADD_SUBR2_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1245153 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1245169 : term1.
Proof. exact (proj1 (@lem1245153)). Qed.
Lemma lem1245170 (m : nat) : term2 m.
Proof. exact (@lem1245169 m). Qed.
Lemma lem1245171 (m : nat) : (term2 m) = ((term3 m) = m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem1245177 (m : nat) : term4 m.
Proof. exact (@lem136305 m). Qed.
Lemma lem1245178 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1245179 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1245178 m) (@lem1245177 m)). Qed.
Lemma lem1245180 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1245179 m n). Qed.
Lemma lem1245181 (m : nat) (n : nat) : (term6 m n) = ((term7 m n) = (NUMERAL 0)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1245183 (m : nat) : term8 m.
Proof. exact (@lem135939 m). Qed.
Lemma lem1245184 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1245185 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1245184 m) (@lem1245183 m)). Qed.
Lemma lem1245186 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem1245185 m n). Qed.
Lemma lem1245187 (m : nat) (n : nat) : (term10 m n) = ((term11 n m) = n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1245189 (n : nat) : term12 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1245190 (n : nat) : (term12 n) = (term13 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem1245191 (n : nat) : term13 n.
Proof. exact (EQ_MP (@lem1245190 n) (@lem1245189 n)). Qed.
Lemma lem1245192 (n : nat) (m : nat) : term14 n m.
Proof. exact (@lem1245191 n m). Qed.
Lemma lem1245193 (n : nat) (m : nat) : (term14 n m) = ((term15 m n) = (term16 n m)).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem1245206 (n : nat) (m : nat) : (term15 m n) = (term16 n m).
Proof. exact (EQ_MP (@lem1245193 n m) (@lem1245192 n m)). Qed.
Lemma lem1245207 (m : nat) (n : nat) : (term17 n m) = (term18 m n).
Proof. exact (@lem1245206 m (Nat.add m n)). Qed.
Lemma lem1245209 (m : nat) (n : nat) : (term11 n m) = n.
Proof. exact (EQ_MP (@lem1245187 m n) (@lem1245186 m n)). Qed.
Lemma lem1245210 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1245211 (m : nat) (n : nat) : (term19 n m) = (Nat.add n).
Proof. exact (MK_COMB (@lem1245210) (@lem1245209 m n)). Qed.
Lemma lem1245213 (m : nat) (n : nat) : (term7 m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1245181 m n) (@lem1245180 m n)). Qed.
Lemma lem1245214 (m : nat) (n : nat) : (term18 m n) = (term3 n).
Proof. exact (MK_COMB (@lem1245211 m n) (@lem1245213 m n)). Qed.
Lemma lem1245216 (m : nat) : (term3 m) = m.
Proof. exact (EQ_MP (@lem1245171 m) (@lem1245170 m)). Qed.
Lemma lem1245217 (n : nat) : (term3 n) = n.
Proof. exact (@lem1245216 n). Qed.
Lemma lem1245218 (m : nat) (n : nat) : (term18 m n) = n.
Proof. exact (TRANS (@lem1245214 m n) (@lem1245217 n)). Qed.
Lemma lem1245219 (m : nat) (n : nat) : (term17 n m) = n.
Proof. exact (TRANS (@lem1245207 m n) (@lem1245218 m n)). Qed.
Lemma lem1245220 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1245221 (m : nat) (n : nat) : (term20 n m) = (@eq nat n).
Proof. exact (MK_COMB (@lem1245220) (@lem1245219 m n)). Qed.
Lemma lem1245222 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1245223 (m : nat) (n : nat) : ((term17 n m) = n) = (n = n).
Proof. exact (MK_COMB (@lem1245221 m n) (@lem1245222 n)). Qed.
Lemma lem1245225 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1245226 (x : nat) : (x = x) = True.
Proof. exact (@lem1245225 nat x). Qed.
Lemma lem1245227 (n : nat) : (n = n) = True.
Proof. exact (@lem1245226 n). Qed.
Lemma lem1245228 (m : nat) (n : nat) : ((term17 n m) = n) = True.
Proof. exact (TRANS (@lem1245223 m n) (@lem1245227 n)). Qed.
Lemma lem1245229 (m : nat) : (term21 m) = term22.
Proof. exact (fun_ext (fun n : nat => @lem1245228 m n)). Qed.
Lemma lem1245230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245231 (m : nat) : (term23 m) = term24.
Proof. exact (MK_COMB (@lem1245230) (@lem1245229 m)). Qed.
Lemma lem1245233 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245234 (t : Prop) : (term26 t) = t.
Proof. exact (@lem1245233 nat t). Qed.
Lemma lem1245235 : term24 = True.
Proof. exact (@lem1245234 True). Qed.
Lemma lem1245236 (m : nat) : (term23 m) = True.
Proof. exact (TRANS (@lem1245231 m) (@lem1245235)). Qed.
Lemma lem1245237 : term27 = term22.
Proof. exact (fun_ext (fun m : nat => @lem1245236 m)). Qed.
Lemma lem1245238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245239 : term28 = term24.
Proof. exact (MK_COMB (@lem1245238) (@lem1245237)). Qed.
Lemma lem1245241 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245242 (t : Prop) : (term26 t) = t.
Proof. exact (@lem1245241 nat t). Qed.
Lemma lem1245243 : term24 = True.
Proof. exact (@lem1245242 True). Qed.
Lemma lem1245244 : term28 = True.
Proof. exact (TRANS (@lem1245239) (@lem1245243)). Qed.
Lemma lem1245245 : True = term28.
Proof. exact (SYM (@lem1245244)). Qed.
Lemma lem1245246 : term28.
Proof. exact (EQ_MP (@lem1245245) (@lem0)). Qed.
