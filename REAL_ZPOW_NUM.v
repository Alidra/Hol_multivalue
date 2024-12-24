Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_NUM_term_abbrevs.
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
Lemma lem3169234 (n : nat) : term0 n.
Proof. exact (@lem2833991 n). Qed.
Lemma lem3169235 (n : nat) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem3169237 (n : nat) : term2 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem3169238 (n : nat) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem3169239 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem3169238 n) (@lem3169237 n)). Qed.
Lemma lem3169240 (n : nat) : (term3 n) = ((term3 n) = True).
Proof. exact (@lem7 (term3 n)). Qed.
Lemma lem3169242 (z : real) : term4 z.
Proof. exact (@lem3169164 z). Qed.
Lemma lem3169243 (z : real) : (term4 z) = (term5 z).
Proof. exact (eq_refl (term4 z)). Qed.
Lemma lem3169244 (z : real) : term5 z.
Proof. exact (EQ_MP (@lem3169243 z) (@lem3169242 z)). Qed.
Lemma lem3169245 (z : real) (i : int) : term6 z i.
Proof. exact (@lem3169244 z i). Qed.
Lemma lem3169246 (z : real) (i : int) : (term6 z i) = ((real_zpow z i) = (term7 z i)).
Proof. exact (eq_refl (term6 z i)). Qed.
Lemma lem3169259 (z : real) (i : int) : (real_zpow z i) = (term7 z i).
Proof. exact (EQ_MP (@lem3169246 z i) (@lem3169245 z i)). Qed.
Lemma lem3169260 (x : real) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (@lem3169259 x (int_of_num n)). Qed.
Lemma lem3169262 (n : nat) : (term3 n) = True.
Proof. exact (EQ_MP (@lem3169240 n) (@lem3169239 n)). Qed.
Lemma lem3169263 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3169264 (n : nat) : (term10 n) = (@COND real True).
Proof. exact (MK_COMB (@lem3169263) (@lem3169262 n)). Qed.
Lemma lem3169266 (n : nat) : (term1 n) = n.
Proof. exact (EQ_MP (@lem3169235 n) (@lem3169234 n)). Qed.
Lemma lem3169267 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem3169268 (x : real) (n : nat) : (term11 x n) = (real_pow x n).
Proof. exact (MK_COMB (@lem3169267 x) (@lem3169266 n)). Qed.
Lemma lem3169269 (x : real) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (MK_COMB (@lem3169264 n) (@lem3169268 x n)). Qed.
Lemma lem3169270 (x : real) (n : nat) : (term14 x n) = (term14 x n).
Proof. exact (eq_refl (term14 x n)). Qed.
Lemma lem3169271 (x : real) (n : nat) : (term9 x n) = (term15 x n).
Proof. exact (MK_COMB (@lem3169269 x n) (@lem3169270 x n)). Qed.
Lemma lem3169273 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem3169274 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem3169273 real t2 t1). Qed.
Lemma lem3169275 (x : real) (n : nat) : (term15 x n) = (real_pow x n).
Proof. exact (@lem3169274 (term14 x n) (real_pow x n)). Qed.
Lemma lem3169276 (x : real) (n : nat) : (term9 x n) = (real_pow x n).
Proof. exact (TRANS (@lem3169271 x n) (@lem3169275 x n)). Qed.
Lemma lem3169277 (x : real) (n : nat) : (term8 x n) = (real_pow x n).
Proof. exact (TRANS (@lem3169260 x n) (@lem3169276 x n)). Qed.
Lemma lem3169278 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3169279 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem3169278) (@lem3169277 x n)). Qed.
Lemma lem3169280 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem3169281 (x : real) (n : nat) : ((term8 x n) = (real_pow x n)) = ((real_pow x n) = (real_pow x n)).
Proof. exact (MK_COMB (@lem3169279 x n) (@lem3169280 x n)). Qed.
Lemma lem3169283 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3169284 (x : real) : (x = x) = True.
Proof. exact (@lem3169283 real x). Qed.
Lemma lem3169285 (x : real) (n : nat) : ((real_pow x n) = (real_pow x n)) = True.
Proof. exact (@lem3169284 (real_pow x n)). Qed.
Lemma lem3169286 (x : real) (n : nat) : ((term8 x n) = (real_pow x n)) = True.
Proof. exact (TRANS (@lem3169281 x n) (@lem3169285 x n)). Qed.
Lemma lem3169287 (x : real) : (term18 x) = term19.
Proof. exact (fun_ext (fun n : nat => @lem3169286 x n)). Qed.
Lemma lem3169288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3169289 (x : real) : (term20 x) = term21.
Proof. exact (MK_COMB (@lem3169288) (@lem3169287 x)). Qed.
Lemma lem3169291 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3169292 (t : Prop) : (term23 t) = t.
Proof. exact (@lem3169291 nat t). Qed.
Lemma lem3169293 : term21 = True.
Proof. exact (@lem3169292 True). Qed.
Lemma lem3169294 (x : real) : (term20 x) = True.
Proof. exact (TRANS (@lem3169289 x) (@lem3169293)). Qed.
Lemma lem3169295 : term24 = term25.
Proof. exact (fun_ext (fun x : real => @lem3169294 x)). Qed.
Lemma lem3169296 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3169297 : term26 = term27.
Proof. exact (MK_COMB (@lem3169296) (@lem3169295)). Qed.
Lemma lem3169299 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3169300 (t : Prop) : (term28 t) = t.
Proof. exact (@lem3169299 real t). Qed.
Lemma lem3169301 : term27 = True.
Proof. exact (@lem3169300 True). Qed.
Lemma lem3169302 : term26 = True.
Proof. exact (TRANS (@lem3169297) (@lem3169301)). Qed.
Lemma lem3169303 : True = term26.
Proof. exact (SYM (@lem3169302)). Qed.
Lemma lem3169304 : term26.
Proof. exact (EQ_MP (@lem3169303) (@lem0)). Qed.
