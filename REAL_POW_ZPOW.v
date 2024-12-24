Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_ZPOW_term_abbrevs.
Require Import INT_POS_spec.
Require Import NUM_OF_INT_OF_NUM_spec.
Require Import real_zpow_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem3169165 (n : nat) : term0 n.
Proof. exact (@lem2833991 n). Qed.
Lemma lem3169166 (n : nat) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem3169168 (n : nat) : term2 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem3169169 (n : nat) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem3169170 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem3169169 n) (@lem3169168 n)). Qed.
Lemma lem3169171 (n : nat) : (term3 n) = ((term3 n) = True).
Proof. exact (@lem7 (term3 n)). Qed.
Lemma lem3169173 (z : real) : term4 z.
Proof. exact (@lem3169164 z). Qed.
Lemma lem3169174 (z : real) : (term4 z) = (term5 z).
Proof. exact (eq_refl (term4 z)). Qed.
Lemma lem3169175 (z : real) : term5 z.
Proof. exact (EQ_MP (@lem3169174 z) (@lem3169173 z)). Qed.
Lemma lem3169176 (z : real) (i : int) : term6 z i.
Proof. exact (@lem3169175 z i). Qed.
Lemma lem3169177 (z : real) (i : int) : (term6 z i) = ((real_zpow z i) = (term7 z i)).
Proof. exact (eq_refl (term6 z i)). Qed.
Lemma lem3169190 (z : real) (i : int) : (real_zpow z i) = (term7 z i).
Proof. exact (EQ_MP (@lem3169177 z i) (@lem3169176 z i)). Qed.
Lemma lem3169191 (x : real) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (@lem3169190 x (int_of_num n)). Qed.
Lemma lem3169193 (n : nat) : (term3 n) = True.
Proof. exact (EQ_MP (@lem3169171 n) (@lem3169170 n)). Qed.
Lemma lem3169194 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3169195 (n : nat) : (term10 n) = (@COND real True).
Proof. exact (MK_COMB (@lem3169194) (@lem3169193 n)). Qed.
Lemma lem3169197 (n : nat) : (term1 n) = n.
Proof. exact (EQ_MP (@lem3169166 n) (@lem3169165 n)). Qed.
Lemma lem3169198 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem3169199 (x : real) (n : nat) : (term11 x n) = (real_pow x n).
Proof. exact (MK_COMB (@lem3169198 x) (@lem3169197 n)). Qed.
Lemma lem3169200 (x : real) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (MK_COMB (@lem3169195 n) (@lem3169199 x n)). Qed.
Lemma lem3169201 (x : real) (n : nat) : (term14 x n) = (term14 x n).
Proof. exact (eq_refl (term14 x n)). Qed.
Lemma lem3169202 (x : real) (n : nat) : (term9 x n) = (term15 x n).
Proof. exact (MK_COMB (@lem3169200 x n) (@lem3169201 x n)). Qed.
Lemma lem3169204 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem3169205 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem3169204 real t2 t1). Qed.
Lemma lem3169206 (x : real) (n : nat) : (term15 x n) = (real_pow x n).
Proof. exact (@lem3169205 (term14 x n) (real_pow x n)). Qed.
Lemma lem3169207 (x : real) (n : nat) : (term9 x n) = (real_pow x n).
Proof. exact (TRANS (@lem3169202 x n) (@lem3169206 x n)). Qed.
Lemma lem3169208 (x : real) (n : nat) : (term8 x n) = (real_pow x n).
Proof. exact (TRANS (@lem3169191 x n) (@lem3169207 x n)). Qed.
Lemma lem3169209 (x : real) (n : nat) : (term16 x n) = (term16 x n).
Proof. exact (eq_refl (term16 x n)). Qed.
Lemma lem3169210 (x : real) (n : nat) : ((real_pow x n) = (term8 x n)) = ((real_pow x n) = (real_pow x n)).
Proof. exact (MK_COMB (@lem3169209 x n) (@lem3169208 x n)). Qed.
Lemma lem3169212 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3169213 (x : real) : (x = x) = True.
Proof. exact (@lem3169212 real x). Qed.
Lemma lem3169214 (x : real) (n : nat) : ((real_pow x n) = (real_pow x n)) = True.
Proof. exact (@lem3169213 (real_pow x n)). Qed.
Lemma lem3169215 (x : real) (n : nat) : ((real_pow x n) = (term8 x n)) = True.
Proof. exact (TRANS (@lem3169210 x n) (@lem3169214 x n)). Qed.
Lemma lem3169216 (x : real) : (term17 x) = term18.
Proof. exact (fun_ext (fun n : nat => @lem3169215 x n)). Qed.
Lemma lem3169217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3169218 (x : real) : (term19 x) = term20.
Proof. exact (MK_COMB (@lem3169217) (@lem3169216 x)). Qed.
Lemma lem3169220 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3169221 (t : Prop) : (term22 t) = t.
Proof. exact (@lem3169220 nat t). Qed.
Lemma lem3169222 : term20 = True.
Proof. exact (@lem3169221 True). Qed.
Lemma lem3169223 (x : real) : (term19 x) = True.
Proof. exact (TRANS (@lem3169218 x) (@lem3169222)). Qed.
Lemma lem3169224 : term23 = term24.
Proof. exact (fun_ext (fun x : real => @lem3169223 x)). Qed.
Lemma lem3169225 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3169226 : term25 = term26.
Proof. exact (MK_COMB (@lem3169225) (@lem3169224)). Qed.
Lemma lem3169228 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3169229 (t : Prop) : (term27 t) = t.
Proof. exact (@lem3169228 real t). Qed.
Lemma lem3169230 : term26 = True.
Proof. exact (@lem3169229 True). Qed.
Lemma lem3169231 : term25 = True.
Proof. exact (TRANS (@lem3169226) (@lem3169230)). Qed.
Lemma lem3169232 : True = term25.
Proof. exact (SYM (@lem3169231)). Qed.
Lemma lem3169233 : term25.
Proof. exact (EQ_MP (@lem3169232) (@lem0)). Qed.
