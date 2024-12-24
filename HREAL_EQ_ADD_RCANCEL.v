Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_EQ_ADD_RCANCEL_term_abbrevs.
Require Import HREAL_EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm1320004_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1321347 (m : hreal) : term0 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1321348 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1321349 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1321348 m) (@lem1321347 m)). Qed.
Lemma lem1321350 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1321349 m n). Qed.
Lemma lem1321351 (m : hreal) (n : hreal) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1321352 (m : hreal) (n : hreal) : term3 m n.
Proof. exact (EQ_MP (@lem1321351 m n) (@lem1321350 m n)). Qed.
Lemma lem1321353 (m : hreal) (n : hreal) (p : hreal) : term4 m n p.
Proof. exact (@lem1321352 m n p). Qed.
Lemma lem1321354 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1321356 (x : hreal) : term5 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1321357 (x : hreal) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1321358 (x : hreal) : term6 x.
Proof. exact (EQ_MP (@lem1321357 x) (@lem1321356 x)). Qed.
Lemma lem1321359 (x : hreal) (y : hreal) : term7 x y.
Proof. exact (@lem1321358 x y). Qed.
Lemma lem1321360 (y : hreal) (x : hreal) : (term7 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1321379 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1321360 y x) (@lem1321359 x y)). Qed.
Lemma lem1321380 (p : hreal) (m : hreal) : (hreal_add m p) = (hreal_add p m).
Proof. exact (@lem1321379 p m). Qed.
Lemma lem1321381 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1321382 (p : hreal) (m : hreal) : (term8 m p) = (term8 p m).
Proof. exact (MK_COMB (@lem1321381) (@lem1321380 p m)). Qed.
Lemma lem1321384 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1321360 y x) (@lem1321359 x y)). Qed.
Lemma lem1321385 (p : hreal) (n : hreal) : (hreal_add n p) = (hreal_add p n).
Proof. exact (@lem1321384 p n). Qed.
Lemma lem1321386 (m : hreal) (p : hreal) (n : hreal) : ((hreal_add m p) = (hreal_add n p)) = ((hreal_add p m) = (hreal_add p n)).
Proof. exact (MK_COMB (@lem1321382 p m) (@lem1321385 p n)). Qed.
Lemma lem1321387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1321388 (m : hreal) (p : hreal) (n : hreal) : (term9 m n p) = (term10 m p n).
Proof. exact (MK_COMB (@lem1321387) (@lem1321386 m p n)). Qed.
Lemma lem1321391 (m : hreal) (n : hreal) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem1321392 (p : hreal) (m : hreal) (n : hreal) : (((hreal_add m p) = (hreal_add n p)) = (m = n)) = (((hreal_add p m) = (hreal_add p n)) = (m = n)).
Proof. exact (MK_COMB (@lem1321388 m p n) (@lem1321391 m n)). Qed.
Lemma lem1321393 (m : hreal) (n : hreal) : (term11 m n) = (term12 m n).
Proof. exact (fun_ext (fun p : hreal => @lem1321392 p m n)). Qed.
Lemma lem1321394 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321395 (m : hreal) (n : hreal) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem1321394) (@lem1321393 m n)). Qed.
Lemma lem1321396 (m : hreal) : (term15 m) = (term16 m).
Proof. exact (fun_ext (fun n : hreal => @lem1321395 m n)). Qed.
Lemma lem1321397 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321398 (m : hreal) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem1321397) (@lem1321396 m)). Qed.
Lemma lem1321399 : term19 = term20.
Proof. exact (fun_ext (fun m : hreal => @lem1321398 m)). Qed.
Lemma lem1321400 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321401 : term21 = term22.
Proof. exact (MK_COMB (@lem1321400) (@lem1321399)). Qed.
Lemma lem1321402 : term22 = term21.
Proof. exact (SYM (@lem1321401)). Qed.
Lemma lem1321418 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1321354 m n p) (@lem1321353 m n p)). Qed.
Lemma lem1321419 (p : hreal) (m : hreal) (n : hreal) : ((hreal_add p m) = (hreal_add p n)) = (m = n).
Proof. exact (@lem1321418 p m n). Qed.
Lemma lem1321422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1321423 (p : hreal) (m : hreal) (n : hreal) : (term10 m p n) = (term23 m n).
Proof. exact (MK_COMB (@lem1321422) (@lem1321419 p m n)). Qed.
Lemma lem1321426 (m : hreal) (n : hreal) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem1321427 (p : hreal) (m : hreal) (n : hreal) : (((hreal_add p m) = (hreal_add p n)) = (m = n)) = ((m = n) = (m = n)).
Proof. exact (MK_COMB (@lem1321423 p m n) (@lem1321426 m n)). Qed.
Lemma lem1321429 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1321430 (x : Prop) : (x = x) = True.
Proof. exact (@lem1321429 Prop x). Qed.
Lemma lem1321431 (m : hreal) (n : hreal) : ((m = n) = (m = n)) = True.
Proof. exact (@lem1321430 (m = n)). Qed.
Lemma lem1321432 (p : hreal) (m : hreal) (n : hreal) : (((hreal_add p m) = (hreal_add p n)) = (m = n)) = True.
Proof. exact (TRANS (@lem1321427 p m n) (@lem1321431 m n)). Qed.
Lemma lem1321433 (m : hreal) (n : hreal) : (term12 m n) = term24.
Proof. exact (fun_ext (fun p : hreal => @lem1321432 p m n)). Qed.
Lemma lem1321434 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321435 (m : hreal) (n : hreal) : (term14 m n) = term25.
Proof. exact (MK_COMB (@lem1321434) (@lem1321433 m n)). Qed.
Lemma lem1321437 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1321438 (t : Prop) : (term27 t) = t.
Proof. exact (@lem1321437 hreal t). Qed.
Lemma lem1321439 : term25 = True.
Proof. exact (@lem1321438 True). Qed.
Lemma lem1321440 (m : hreal) (n : hreal) : (term14 m n) = True.
Proof. exact (TRANS (@lem1321435 m n) (@lem1321439)). Qed.
Lemma lem1321441 (m : hreal) : (term16 m) = term24.
Proof. exact (fun_ext (fun n : hreal => @lem1321440 m n)). Qed.
Lemma lem1321442 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321443 (m : hreal) : (term18 m) = term25.
Proof. exact (MK_COMB (@lem1321442) (@lem1321441 m)). Qed.
Lemma lem1321445 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1321446 (t : Prop) : (term27 t) = t.
Proof. exact (@lem1321445 hreal t). Qed.
Lemma lem1321447 : term25 = True.
Proof. exact (@lem1321446 True). Qed.
Lemma lem1321448 (m : hreal) : (term18 m) = True.
Proof. exact (TRANS (@lem1321443 m) (@lem1321447)). Qed.
Lemma lem1321449 : term20 = term24.
Proof. exact (fun_ext (fun m : hreal => @lem1321448 m)). Qed.
Lemma lem1321450 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321451 : term22 = term25.
Proof. exact (MK_COMB (@lem1321450) (@lem1321449)). Qed.
Lemma lem1321453 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1321454 (t : Prop) : (term27 t) = t.
Proof. exact (@lem1321453 hreal t). Qed.
Lemma lem1321455 : term25 = True.
Proof. exact (@lem1321454 True). Qed.
Lemma lem1321456 : term22 = True.
Proof. exact (TRANS (@lem1321451) (@lem1321455)). Qed.
Lemma lem1321457 : True = term22.
Proof. exact (SYM (@lem1321456)). Qed.
Lemma lem1321458 : term22.
Proof. exact (EQ_MP (@lem1321457) (@lem0)). Qed.
Lemma lem1321459 : term21.
Proof. exact (EQ_MP (@lem1321402) (@lem1321458)). Qed.
