Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_POW_R1_term_abbrevs.
Require Import REAL_MUL_RID_spec.
Require Import REAL_POW_ONE_spec.
Require Import REAL_SUB_POW_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Lemma lem7332275 (x : real) : term0 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem7332276 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem7332278 (n : nat) : term2 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem7332279 (n : nat) : (term2 n) = ((term3 n) = term4).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem7332281 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem7332282 (x : real) (h1 : term5) : term6 x.
Proof. exact (@lem7332281 h1 x). Qed.
Lemma lem7332283 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem7332284 (x : real) (h1 : term5) : term7 x.
Proof. exact (EQ_MP (@lem7332283 x) (@lem7332282 x h1)). Qed.
Lemma lem7332285 (x : real) (y : real) (h1 : term5) : term8 x y.
Proof. exact (@lem7332284 x h1 y). Qed.
Lemma lem7332286 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem7332287 (x : real) (y : real) (h1 : term5) : term9 x y.
Proof. exact (EQ_MP (@lem7332286 x y) (@lem7332285 x y h1)). Qed.
Lemma lem7332288 (x : real) (y : real) (n : nat) (h1 : term5) : term10 x y n.
Proof. exact (@lem7332287 x y h1 n). Qed.
Lemma lem7332289 (x : real) (y : real) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (eq_refl (term10 x y n)). Qed.
Lemma lem7332290 (x : real) (y : real) (n : nat) (h1 : term5) : term11 x y n.
Proof. exact (EQ_MP (@lem7332289 x y n) (@lem7332288 x y n h1)). Qed.
Lemma lem7332291 (n : nat) (h1 : term12 n) : term12 n.
Proof. exact (h1). Qed.
Lemma lem7332292 (x : real) (y : real) (n : nat) (h1 : term5) (h2 : term12 n) : (term13 x y n) = (term14 x y n).
Proof. exact (@lem7332290 x y n h1 (@lem7332291 n h2)). Qed.
Lemma lem7332293 (x : real) (n : nat) (h1 : term5) (h2 : term12 n) : term15 x n.
Proof. exact (fun y : real => @lem7332292 x y n h1 h2). Qed.
Lemma lem7332294 (n : nat) (h1 : term5) (h2 : term12 n) : term16 n.
Proof. exact (fun x : real => @lem7332293 x n h1 h2). Qed.
Lemma lem7332295 (n : nat) (h1 : term5) : term17 n.
Proof. exact (fun h0 : term12 n => @lem7332294 n h1 h0). Qed.
Lemma lem7332296 (h1 : term5) : term18.
Proof. exact (fun n : nat => @lem7332295 n h1). Qed.
Lemma lem7332297 : term19.
Proof. exact (fun h0 : term5 => @lem7332296 h0). Qed.
Lemma lem7332298 : term18.
Proof. exact (@lem7332297 (@lem7332274)). Qed.
Lemma lem7332299 (n : nat) : term20 n.
Proof. exact (@lem7332298 n). Qed.
Lemma lem7332300 (n : nat) : (term20 n) = (term17 n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem7332302 (n : nat) (h1 : term12 n) : term12 n.
Proof. exact (h1). Qed.
Lemma lem7332304 (n : nat) : term17 n.
Proof. exact (EQ_MP (@lem7332300 n) (@lem7332299 n)). Qed.
Lemma lem7332305 (n : nat) (h1 : term12 n) : term16 n.
Proof. exact (@lem7332304 n (@lem7332302 n h1)). Qed.
Lemma lem7332306 (x : real) (n : nat) (h1 : term12 n) : term21 n x.
Proof. exact (@lem7332305 n h1 x). Qed.
Lemma lem7332307 (x : real) (n : nat) : (term21 n x) = (term15 x n).
Proof. exact (eq_refl (term21 n x)). Qed.
Lemma lem7332308 (x : real) (n : nat) (h1 : term12 n) : term15 x n.
Proof. exact (EQ_MP (@lem7332307 x n) (@lem7332306 x n h1)). Qed.
Lemma lem7332309 (x : real) (n : nat) (h1 : term12 n) : term22 x n.
Proof. exact (@lem7332308 x n h1 term4). Qed.
Lemma lem7332310 (x : real) (n : nat) : (term22 x n) = ((term23 x n) = (term24 x n)).
Proof. exact (eq_refl (term22 x n)). Qed.
Lemma lem7332311 (x : real) (n : nat) (h1 : term12 n) : (term23 x n) = (term24 x n).
Proof. exact (EQ_MP (@lem7332310 x n) (@lem7332309 x n h1)). Qed.
Lemma lem7332319 (n : nat) : (term3 n) = term4.
Proof. exact (EQ_MP (@lem7332279 n) (@lem7332278 n)). Qed.
Lemma lem7332320 (x : real) (n : nat) : (term25 x n) = (term25 x n).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem7332321 (x : real) (n : nat) : (term23 x n) = (term26 x n).
Proof. exact (MK_COMB (@lem7332320 x n) (@lem7332319 n)). Qed.
Lemma lem7332322 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7332323 (x : real) (n : nat) : (term27 x n) = (term28 x n).
Proof. exact (MK_COMB (@lem7332322) (@lem7332321 x n)). Qed.
Lemma lem7332325 (n : nat) : (term3 n) = term4.
Proof. exact (EQ_MP (@lem7332279 n) (@lem7332278 n)). Qed.
Lemma lem7332326 (n : nat) (i : nat) : (term29 n i) = term4.
Proof. exact (@lem7332325 (term30 n i)). Qed.
Lemma lem7332327 (x : real) (i : nat) : (term31 x i) = (term31 x i).
Proof. exact (eq_refl (term31 x i)). Qed.
Lemma lem7332328 (n : nat) (x : real) (i : nat) : (term32 x n i) = (term33 x i).
Proof. exact (MK_COMB (@lem7332327 x i) (@lem7332326 n i)). Qed.
Lemma lem7332330 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem7332276 x) (@lem7332275 x)). Qed.
Lemma lem7332331 (x : real) (i : nat) : (term33 x i) = (real_pow x i).
Proof. exact (@lem7332330 (real_pow x i)). Qed.
Lemma lem7332332 (n : nat) (x : real) (i : nat) : (term32 x n i) = (real_pow x i).
Proof. exact (TRANS (@lem7332328 n x i) (@lem7332331 x i)). Qed.
Lemma lem7332333 (n : nat) (x : real) : (term34 x n) = (term35 x).
Proof. exact (fun_ext (fun i : nat => @lem7332332 n x i)). Qed.
Lemma lem7332334 (n : nat) : (term36 n) = (term36 n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem7332335 (n : nat) (x : real) : (term37 x n) = (term38 n x).
Proof. exact (MK_COMB (@lem7332334 n) (@lem7332333 n x)). Qed.
Lemma lem7332336 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem7332337 (n : nat) (x : real) : (term24 x n) = (term40 n x).
Proof. exact (MK_COMB (@lem7332336 x) (@lem7332335 n x)). Qed.
Lemma lem7332338 (n : nat) (x : real) : ((term23 x n) = (term24 x n)) = ((term26 x n) = (term40 n x)).
Proof. exact (MK_COMB (@lem7332323 x n) (@lem7332337 n x)). Qed.
Lemma lem7332341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7332342 (n : nat) (x : real) : (term41 x n) = (term42 n x).
Proof. exact (MK_COMB (@lem7332341) (@lem7332338 n x)). Qed.
Lemma lem7332345 (n : nat) (x : real) : ((term26 x n) = (term40 n x)) = ((term26 x n) = (term40 n x)).
Proof. exact (eq_refl ((term26 x n) = (term40 n x))). Qed.
Lemma lem7332346 (n : nat) (x : real) : (term43 n x) = (term44 n x).
Proof. exact (MK_COMB (@lem7332342 n x) (@lem7332345 n x)). Qed.
Lemma lem7332350 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7332351 (n : nat) (x : real) : (term44 n x) = True.
Proof. exact (@lem7332350 ((term26 x n) = (term40 n x))). Qed.
Lemma lem7332352 (n : nat) (x : real) : (term43 n x) = True.
Proof. exact (TRANS (@lem7332346 n x) (@lem7332351 n x)). Qed.
Lemma lem7332353 (n : nat) (x : real) : True = (term43 n x).
Proof. exact (SYM (@lem7332352 n x)). Qed.
Lemma lem7332354 (n : nat) (x : real) : term43 n x.
Proof. exact (EQ_MP (@lem7332353 n x) (@lem0)). Qed.
Lemma lem7332355 (x : real) (n : nat) (h1 : term12 n) : (term26 x n) = (term40 n x).
Proof. exact (@lem7332354 n x (@lem7332311 x n h1)). Qed.
Lemma lem7332356 (n : nat) (x : real) : term45 n x.
Proof. exact (fun h0 : term12 n => @lem7332355 x n h0). Qed.
Lemma lem7332361 (x : real) : term46 x.
Proof. exact (fun n : nat => @lem7332356 n x). Qed.
Lemma lem7332366 : term47.
Proof. exact (fun x : real => @lem7332361 x). Qed.
