Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_RADD_0_term_abbrevs.
Require Import DIST_LADD_0_spec.
Require Import DIST_SYM_spec.
Lemma lem1245247 (m : nat) : term0 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1245248 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1245249 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1245248 m) (@lem1245247 m)). Qed.
Lemma lem1245250 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1245249 m n). Qed.
Lemma lem1245251 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = (term3 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1245264 (n : nat) (m : nat) : (term3 m n) = (term3 n m).
Proof. exact (EQ_MP (@lem1245251 n m) (@lem1245250 m n)). Qed.
Lemma lem1245265 (n : nat) (m : nat) : (term4 m n) = (term5 n m).
Proof. exact (@lem1245264 (Nat.add m n) m). Qed.
Lemma lem1245266 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1245267 (n : nat) (m : nat) : (term6 m n) = (term7 n m).
Proof. exact (MK_COMB (@lem1245266) (@lem1245265 n m)). Qed.
Lemma lem1245268 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1245269 (m : nat) (n : nat) : ((term4 m n) = n) = ((term5 n m) = n).
Proof. exact (MK_COMB (@lem1245267 n m) (@lem1245268 n)). Qed.
Lemma lem1245270 (m : nat) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem1245269 m n)). Qed.
Lemma lem1245271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245272 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem1245271) (@lem1245270 m)). Qed.
Lemma lem1245273 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem1245272 m)). Qed.
Lemma lem1245274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245275 : term14 = term15.
Proof. exact (MK_COMB (@lem1245274) (@lem1245273)). Qed.
Lemma lem1245276 : term15 = term14.
Proof. exact (SYM (@lem1245275)). Qed.
Lemma lem1245277 (m : nat) : term16 m.
Proof. exact (@lem1245246 m). Qed.
Lemma lem1245278 (m : nat) : (term16 m) = (term11 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem1245279 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1245278 m) (@lem1245277 m)). Qed.
Lemma lem1245280 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem1245279 m n). Qed.
Lemma lem1245281 (m : nat) (n : nat) : (term17 m n) = ((term5 n m) = n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem1245284 (m : nat) (n : nat) : (term5 n m) = n.
Proof. exact (EQ_MP (@lem1245281 m n) (@lem1245280 m n)). Qed.
Lemma lem1245289 (m : nat) : term11 m.
Proof. exact (fun n : nat => @lem1245284 m n). Qed.
Lemma lem1245294 : term15.
Proof. exact (fun m : nat => @lem1245289 m). Qed.
Lemma lem1245295 : term14.
Proof. exact (EQ_MP (@lem1245276) (@lem1245294)). Qed.
