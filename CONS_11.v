Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONS_11_term_abbrevs.
Require Import thm0_spec.
Require Import thm1073632_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1113348 {A : Type'} (a0 : A) : term0 A a0.
Proof. exact (@lem1073632 A a0). Qed.
Lemma lem1113349 {A : Type'} (a0 : A) : (term0 A a0) = (term1 A a0).
Proof. exact (eq_refl (term0 A a0)). Qed.
Lemma lem1113350 {A : Type'} (a0 : A) : term1 A a0.
Proof. exact (EQ_MP (@lem1113349 A a0) (@lem1113348 A a0)). Qed.
Lemma lem1113351 {A : Type'} (a0 : A) (a1 : list A) : term2 A a0 a1.
Proof. exact (@lem1113350 A a0 a1). Qed.
Lemma lem1113352 {A : Type'} (a0 : A) (a1 : list A) : (term2 A a0 a1) = (term3 A a0 a1).
Proof. exact (eq_refl (term2 A a0 a1)). Qed.
Lemma lem1113353 {A : Type'} (a0 : A) (a1 : list A) : term3 A a0 a1.
Proof. exact (EQ_MP (@lem1113352 A a0 a1) (@lem1113351 A a0 a1)). Qed.
Lemma lem1113354 {A : Type'} (a0 : A) (a1 : list A) (a0' : A) : term4 A a0 a1 a0'.
Proof. exact (@lem1113353 A a0 a1 a0'). Qed.
Lemma lem1113355 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) : (term4 A a0 a1 a0') = (term5 A a0 a0' a1).
Proof. exact (eq_refl (term4 A a0 a1 a0')). Qed.
Lemma lem1113356 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) : term5 A a0 a0' a1.
Proof. exact (EQ_MP (@lem1113355 A a0 a0' a1) (@lem1113354 A a0 a1 a0')). Qed.
Lemma lem1113357 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) : term6 A a0 a0' a1 a1'.
Proof. exact (@lem1113356 A a0 a0' a1 a1'). Qed.
Lemma lem1113358 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) : (term6 A a0 a0' a1 a1') = (((@cons A a0 a1) = (@cons A a0' a1')) = (term7 A a0 a0' a1 a1')).
Proof. exact (eq_refl (term6 A a0 a0' a1 a1')). Qed.
Lemma lem1113379 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) : ((@cons A a0 a1) = (@cons A a0' a1')) = (term7 A a0 a0' a1 a1').
Proof. exact (EQ_MP (@lem1113358 A a0 a0' a1 a1') (@lem1113357 A a0 a0' a1 a1')). Qed.
Lemma lem1113380 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) : ((@cons A a0 a1) = (@cons A a0' a1')) = (term7 A a0 a0' a1 a1').
Proof. exact (@lem1113379 A a0 a0' a1 a1'). Qed.
Lemma lem1113381 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term7 A h1' h2' t1 t2).
Proof. exact (@lem1113380 A h1' h2' t1 t2). Qed.
Lemma lem1113388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1113389 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term8 A h1' t1 h2' t2) = (term9 A h1' h2' t1 t2).
Proof. exact (MK_COMB (@lem1113388) (@lem1113381 A h1' h2' t1 t2)). Qed.
Lemma lem1113396 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term7 A h1' h2' t1 t2) = (term7 A h1' h2' t1 t2).
Proof. exact (eq_refl (term7 A h1' h2' t1 t2)). Qed.
Lemma lem1113397 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (((@cons A h1' t1) = (@cons A h2' t2)) = (term7 A h1' h2' t1 t2)) = ((term7 A h1' h2' t1 t2) = (term7 A h1' h2' t1 t2)).
Proof. exact (MK_COMB (@lem1113389 A h1' h2' t1 t2) (@lem1113396 A h1' h2' t1 t2)). Qed.
Lemma lem1113399 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1113400 (x : Prop) : (x = x) = True.
Proof. exact (@lem1113399 Prop x). Qed.
Lemma lem1113401 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((term7 A h1' h2' t1 t2) = (term7 A h1' h2' t1 t2)) = True.
Proof. exact (@lem1113400 (term7 A h1' h2' t1 t2)). Qed.
Lemma lem1113402 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (((@cons A h1' t1) = (@cons A h2' t2)) = (term7 A h1' h2' t1 t2)) = True.
Proof. exact (TRANS (@lem1113397 A h1' h2' t1 t2) (@lem1113401 A h1' h2' t1 t2)). Qed.
Lemma lem1113403 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term10 A h1' h2' t1) = (term11 A).
Proof. exact (fun_ext (fun t2 : list A => @lem1113402 A h1' h2' t1 t2)). Qed.
Lemma lem1113404 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113405 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term5 A h1' h2' t1) = (term12 A).
Proof. exact (MK_COMB (@lem1113404 A) (@lem1113403 A h1' h2' t1)). Qed.
Lemma lem1113407 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1113408 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (@lem1113407 (list A) t). Qed.
Lemma lem1113409 {A : Type'} : (term12 A) = True.
Proof. exact (@lem1113408 A True). Qed.
Lemma lem1113410 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term5 A h1' h2' t1) = True.
Proof. exact (TRANS (@lem1113405 A h1' h2' t1) (@lem1113409 A)). Qed.
Lemma lem1113411 {A : Type'} (h1' : A) (h2' : A) : (term15 A h1' h2') = (term11 A).
Proof. exact (fun_ext (fun t1 : list A => @lem1113410 A h1' h2' t1)). Qed.
Lemma lem1113412 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113413 {A : Type'} (h1' : A) (h2' : A) : (term16 A h1' h2') = (term12 A).
Proof. exact (MK_COMB (@lem1113412 A) (@lem1113411 A h1' h2')). Qed.
Lemma lem1113415 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1113416 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (@lem1113415 (list A) t). Qed.
Lemma lem1113417 {A : Type'} : (term12 A) = True.
Proof. exact (@lem1113416 A True). Qed.
Lemma lem1113418 {A : Type'} (h1' : A) (h2' : A) : (term16 A h1' h2') = True.
Proof. exact (TRANS (@lem1113413 A h1' h2') (@lem1113417 A)). Qed.
Lemma lem1113419 {A : Type'} (h1' : A) : (term17 A h1') = (term18 A).
Proof. exact (fun_ext (fun h2' : A => @lem1113418 A h1' h2')). Qed.
Lemma lem1113420 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1113421 {A : Type'} (h1' : A) : (term19 A h1') = (term20 A).
Proof. exact (MK_COMB (@lem1113420 A) (@lem1113419 A h1')). Qed.
Lemma lem1113423 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1113424 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (@lem1113423 A t). Qed.
Lemma lem1113425 {A : Type'} : (term20 A) = True.
Proof. exact (@lem1113424 A True). Qed.
Lemma lem1113426 {A : Type'} (h1' : A) : (term19 A h1') = True.
Proof. exact (TRANS (@lem1113421 A h1') (@lem1113425 A)). Qed.
Lemma lem1113427 {A : Type'} : (term21 A) = (term18 A).
Proof. exact (fun_ext (fun h1' : A => @lem1113426 A h1')). Qed.
Lemma lem1113428 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1113429 {A : Type'} : (term22 A) = (term20 A).
Proof. exact (MK_COMB (@lem1113428 A) (@lem1113427 A)). Qed.
Lemma lem1113431 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1113432 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (@lem1113431 A t). Qed.
Lemma lem1113433 {A : Type'} : (term20 A) = True.
Proof. exact (@lem1113432 A True). Qed.
Lemma lem1113434 {A : Type'} : (term22 A) = True.
Proof. exact (TRANS (@lem1113429 A) (@lem1113433 A)). Qed.
Lemma lem1113435 {A : Type'} : True = (term22 A).
Proof. exact (SYM (@lem1113434 A)). Qed.
Lemma lem1113436 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem1113435 A) (@lem0)). Qed.
