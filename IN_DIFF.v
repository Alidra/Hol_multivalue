Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_DIFF_term_abbrevs.
Require Import DIFF_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3205365 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3192076 A s). Qed.
Lemma lem3205366 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3205367 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3205366 A s) (@lem3205365 A s)). Qed.
Lemma lem3205368 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3205367 A s t). Qed.
Lemma lem3205369 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = ((@DIFF A s t) = (term3 A s t)).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3205395 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3205396 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem3205395 _83095 p). Qed.
Lemma lem3205397 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem3205398 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem3205397 _83095 p) (@lem3205396 _83095 p)). Qed.
Lemma lem3205399 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem3205398 _83095 p x). Qed.
Lemma lem3205400 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem3205424 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DIFF A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3205369 A s t) (@lem3205368 A s t)). Qed.
Lemma lem3205425 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DIFF A s t) = (term3 A s t).
Proof. exact (@lem3205424 A s t). Qed.
Lemma lem3205432 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205433 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term9 A x s t) = (term10 A x s t).
Proof. exact (MK_COMB (@lem3205432 A x) (@lem3205425 A s t)). Qed.
Lemma lem3205435 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3205400 _83095 p x) (@lem3205399 _83095 p x)). Qed.
Lemma lem3205436 {A : Type'} (p : A -> Prop) (x : A) : (term8 A x p) = (p x).
Proof. exact (@lem3205435 A p x). Qed.
Lemma lem3205437 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term11 A x s t) = (term12 A s t x).
Proof. exact (@lem3205436 A (term13 A s t) x). Qed.
Lemma lem3205438 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A s t x) = (term14 A s x t).
Proof. exact (eq_refl (term12 A s t x)). Qed.
Lemma lem3205439 {A : Type'} (GEN_PVAR_4 : A) : (@SETSPEC A GEN_PVAR_4) = (@SETSPEC A GEN_PVAR_4).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_4)). Qed.
Lemma lem3205440 {A : Type'} (GEN_PVAR_4 : A) (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A GEN_PVAR_4 s t x) = (term16 A GEN_PVAR_4 s x t).
Proof. exact (MK_COMB (@lem3205439 A GEN_PVAR_4) (@lem3205438 A s x t)). Qed.
Lemma lem3205441 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3205442 {A : Type'} (GEN_PVAR_4 : A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A GEN_PVAR_4 s t x) = (term18 A GEN_PVAR_4 s t x).
Proof. exact (MK_COMB (@lem3205440 A GEN_PVAR_4 s x t) (@lem3205441 A x)). Qed.
Lemma lem3205443 {A : Type'} (GEN_PVAR_4 : A) (s : A -> Prop) (t : A -> Prop) : (term19 A GEN_PVAR_4 s t) = (term20 A GEN_PVAR_4 s t).
Proof. exact (fun_ext (fun x : A => @lem3205442 A GEN_PVAR_4 s t x)). Qed.
Lemma lem3205444 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3205445 {A : Type'} (GEN_PVAR_4 : A) (s : A -> Prop) (t : A -> Prop) : (term21 A GEN_PVAR_4 s t) = (term22 A GEN_PVAR_4 s t).
Proof. exact (MK_COMB (@lem3205444 A) (@lem3205443 A GEN_PVAR_4 s t)). Qed.
Lemma lem3205446 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term24 A s t).
Proof. exact (fun_ext (fun GEN_PVAR_4 : A => @lem3205445 A GEN_PVAR_4 s t)). Qed.
Lemma lem3205447 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3205448 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term3 A s t).
Proof. exact (MK_COMB (@lem3205447 A) (@lem3205446 A s t)). Qed.
Lemma lem3205449 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205450 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term11 A x s t) = (term10 A x s t).
Proof. exact (MK_COMB (@lem3205449 A x) (@lem3205448 A s t)). Qed.
Lemma lem3205451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205452 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term26 A x s t) = (term27 A x s t).
Proof. exact (MK_COMB (@lem3205451) (@lem3205450 A x s t)). Qed.
Lemma lem3205453 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A s t x) = (term14 A s x t).
Proof. exact (eq_refl (term12 A s t x)). Qed.
Lemma lem3205454 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term11 A x s t) = (term12 A s t x)) = ((term10 A x s t) = (term14 A s x t)).
Proof. exact (MK_COMB (@lem3205452 A x s t) (@lem3205453 A s x t)). Qed.
Lemma lem3205455 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term14 A s x t).
Proof. exact (EQ_MP (@lem3205454 A s x t) (@lem3205437 A s t x)). Qed.
Lemma lem3205458 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term9 A x s t) = (term14 A s x t).
Proof. exact (TRANS (@lem3205433 A x s t) (@lem3205455 A s x t)). Qed.
Lemma lem3205459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205460 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (MK_COMB (@lem3205459) (@lem3205458 A s x t)). Qed.
Lemma lem3205463 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A s x t) = (term14 A s x t).
Proof. exact (eq_refl (term14 A s x t)). Qed.
Lemma lem3205464 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term9 A x s t) = (term14 A s x t)) = ((term14 A s x t) = (term14 A s x t)).
Proof. exact (MK_COMB (@lem3205460 A s x t) (@lem3205463 A s x t)). Qed.
Lemma lem3205466 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3205467 (x : Prop) : (x = x) = True.
Proof. exact (@lem3205466 Prop x). Qed.
Lemma lem3205468 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term14 A s x t) = (term14 A s x t)) = True.
Proof. exact (@lem3205467 (term14 A s x t)). Qed.
Lemma lem3205469 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term9 A x s t) = (term14 A s x t)) = True.
Proof. exact (TRANS (@lem3205464 A s x t) (@lem3205468 A s x t)). Qed.
Lemma lem3205470 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term30 A s t) = (term31 A).
Proof. exact (fun_ext (fun x : A => @lem3205469 A s x t)). Qed.
Lemma lem3205471 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205472 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term33 A).
Proof. exact (MK_COMB (@lem3205471 A) (@lem3205470 A s t)). Qed.
Lemma lem3205474 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205475 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (@lem3205474 A t). Qed.
Lemma lem3205476 {A : Type'} : (term33 A) = True.
Proof. exact (@lem3205475 A True). Qed.
Lemma lem3205477 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = True.
Proof. exact (TRANS (@lem3205472 A s t) (@lem3205476 A)). Qed.
Lemma lem3205478 {A : Type'} (s : A -> Prop) : (term35 A s) = (term36 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3205477 A s t)). Qed.
Lemma lem3205479 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3205480 {A : Type'} (s : A -> Prop) : (term37 A s) = (term38 A).
Proof. exact (MK_COMB (@lem3205479 A) (@lem3205478 A s)). Qed.
Lemma lem3205482 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205483 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem3205482 (A -> Prop) t). Qed.
Lemma lem3205484 {A : Type'} : (term38 A) = True.
Proof. exact (@lem3205483 A True). Qed.
Lemma lem3205485 {A : Type'} (s : A -> Prop) : (term37 A s) = True.
Proof. exact (TRANS (@lem3205480 A s) (@lem3205484 A)). Qed.
Lemma lem3205486 {A : Type'} : (term40 A) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3205485 A s)). Qed.
Lemma lem3205487 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3205488 {A : Type'} : (term41 A) = (term38 A).
Proof. exact (MK_COMB (@lem3205487 A) (@lem3205486 A)). Qed.
Lemma lem3205490 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205491 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem3205490 (A -> Prop) t). Qed.
Lemma lem3205492 {A : Type'} : (term38 A) = True.
Proof. exact (@lem3205491 A True). Qed.
Lemma lem3205493 {A : Type'} : (term41 A) = True.
Proof. exact (TRANS (@lem3205488 A) (@lem3205492 A)). Qed.
Lemma lem3205494 {A : Type'} : True = (term41 A).
Proof. exact (SYM (@lem3205493 A)). Qed.
Lemma lem3205495 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem3205494 A) (@lem0)). Qed.
