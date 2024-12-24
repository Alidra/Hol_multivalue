Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_MULT_RCANCEL_term_abbrevs.
Require Import DISJ_SYM_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import MULT_SYM_spec.
Lemma lem104209 (t1 : Prop) : term0 t1.
Proof. exact (@lem720 t1). Qed.
Lemma lem104210 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem104211 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem104210 t1) (@lem104209 t1)). Qed.
Lemma lem104212 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem104211 t1 t2). Qed.
Lemma lem104213 (t2 : Prop) (t1 : Prop) : (term2 t1 t2) = ((t1 \/ t2) = (t2 \/ t1)).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem104215 (m : nat) : term3 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem104216 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem104217 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem104216 m) (@lem104215 m)). Qed.
Lemma lem104218 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem104217 m n). Qed.
Lemma lem104219 (n : nat) (m : nat) : (term5 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem104236 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem104219 n m) (@lem104218 m n)). Qed.
Lemma lem104237 (p : nat) (m : nat) : (Nat.mul m p) = (Nat.mul p m).
Proof. exact (@lem104236 p m). Qed.
Lemma lem104238 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem104239 (p : nat) (m : nat) : (term6 m p) = (term6 p m).
Proof. exact (MK_COMB (@lem104238) (@lem104237 p m)). Qed.
Lemma lem104241 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem104219 n m) (@lem104218 m n)). Qed.
Lemma lem104242 (p : nat) (n : nat) : (Nat.mul n p) = (Nat.mul p n).
Proof. exact (@lem104241 p n). Qed.
Lemma lem104243 (m : nat) (p : nat) (n : nat) : (term7 m n p) = (term8 m p n).
Proof. exact (MK_COMB (@lem104239 p m) (@lem104242 p n)). Qed.
Lemma lem104244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem104245 (m : nat) (p : nat) (n : nat) : (term9 m n p) = (term10 m p n).
Proof. exact (MK_COMB (@lem104244) (@lem104243 m p n)). Qed.
Lemma lem104249 (t2 : Prop) (t1 : Prop) : (t1 \/ t2) = (t2 \/ t1).
Proof. exact (EQ_MP (@lem104213 t2 t1) (@lem104212 t1 t2)). Qed.
Lemma lem104250 (p : nat) (m : nat) (n : nat) : (term11 m n p) = (term12 p m n).
Proof. exact (@lem104249 (p = (NUMERAL 0)) (Peano.le m n)). Qed.
Lemma lem104251 (p : nat) (m : nat) (n : nat) : ((term7 m n p) = (term11 m n p)) = ((term8 m p n) = (term12 p m n)).
Proof. exact (MK_COMB (@lem104245 m p n) (@lem104250 p m n)). Qed.
Lemma lem104252 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (fun_ext (fun p : nat => @lem104251 p m n)). Qed.
Lemma lem104253 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104254 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (MK_COMB (@lem104253) (@lem104252 m n)). Qed.
Lemma lem104255 (m : nat) : (term17 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem104254 m n)). Qed.
Lemma lem104256 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104257 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem104256) (@lem104255 m)). Qed.
Lemma lem104258 : term21 = term22.
Proof. exact (fun_ext (fun m : nat => @lem104257 m)). Qed.
Lemma lem104259 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104260 : term23 = term24.
Proof. exact (MK_COMB (@lem104259) (@lem104258)). Qed.
Lemma lem104261 : term24 = term23.
Proof. exact (SYM (@lem104260)). Qed.
Lemma lem104262 (m : nat) : term25 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem104263 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem104264 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem104263 m) (@lem104262 m)). Qed.
Lemma lem104265 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem104264 m n). Qed.
Lemma lem104266 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem104267 (m : nat) (n : nat) : term28 m n.
Proof. exact (EQ_MP (@lem104266 m n) (@lem104265 m n)). Qed.
Lemma lem104268 (m : nat) (n : nat) (p : nat) : term29 m n p.
Proof. exact (@lem104267 m n p). Qed.
Lemma lem104269 (m : nat) (n : nat) (p : nat) : (term29 m n p) = ((term8 n m p) = (term12 m n p)).
Proof. exact (eq_refl (term29 m n p)). Qed.
Lemma lem104272 (m : nat) (n : nat) (p : nat) : (term8 n m p) = (term12 m n p).
Proof. exact (EQ_MP (@lem104269 m n p) (@lem104268 m n p)). Qed.
Lemma lem104273 (p : nat) (m : nat) (n : nat) : (term8 m p n) = (term12 p m n).
Proof. exact (@lem104272 p m n). Qed.
Lemma lem104278 (m : nat) (n : nat) : term16 m n.
Proof. exact (fun p : nat => @lem104273 p m n). Qed.
Lemma lem104283 (m : nat) : term20 m.
Proof. exact (fun n : nat => @lem104278 m n). Qed.
Lemma lem104288 : term24.
Proof. exact (fun m : nat => @lem104283 m). Qed.
Lemma lem104289 : term23.
Proof. exact (EQ_MP (@lem104261) (@lem104288)). Qed.
