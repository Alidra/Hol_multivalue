Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_CROSS_term_abbrevs.
Require Import CROSS_spec.
Require Import HAS_SIZE_PRODUCT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem4325366 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4324156 A B s). Qed.
Lemma lem4325367 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4325368 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4325367 A B s) (@lem4325366 A B s)). Qed.
Lemma lem4325369 {A B : Type'} (s : A -> Prop) (m : nat) : term2 A B s m.
Proof. exact (@lem4325368 A B s m). Qed.
Lemma lem4325370 {A B : Type'} (s : A -> Prop) (m : nat) : (term2 A B s m) = (term3 A B s m).
Proof. exact (eq_refl (term2 A B s m)). Qed.
Lemma lem4325371 {A B : Type'} (s : A -> Prop) (m : nat) : term3 A B s m.
Proof. exact (EQ_MP (@lem4325370 A B s m) (@lem4325369 A B s m)). Qed.
Lemma lem4325372 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) : term4 A B s m t.
Proof. exact (@lem4325371 A B s m t). Qed.
Lemma lem4325373 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) : (term4 A B s m t) = (term5 A B s t m).
Proof. exact (eq_refl (term4 A B s m t)). Qed.
Lemma lem4325374 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) : term5 A B s t m.
Proof. exact (EQ_MP (@lem4325373 A B s t m) (@lem4325372 A B s m t)). Qed.
Lemma lem4325375 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : term6 A B s t m n.
Proof. exact (@lem4325374 A B s t m n). Qed.
Lemma lem4325376 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : (term6 A B s t m n) = (term7 A B s t m n).
Proof. exact (eq_refl (term6 A B s t m n)). Qed.
Lemma lem4325377 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : term7 A B s t m n.
Proof. exact (EQ_MP (@lem4325376 A B s t m n) (@lem4325375 A B s t m n)). Qed.
Lemma lem4325378 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : (term7 A B s t m n) = ((term7 A B s t m n) = True).
Proof. exact (@lem7 (term7 A B s t m n)). Qed.
Lemma lem4325380 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term8 _103681 _103682 s.
Proof. exact (@lem4325236 _103681 _103682 s). Qed.
Lemma lem4325381 {_103681 _103682 : Type'} (s : _103682 -> Prop) : (term8 _103681 _103682 s) = (term9 _103681 _103682 s).
Proof. exact (eq_refl (term8 _103681 _103682 s)). Qed.
Lemma lem4325382 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term9 _103681 _103682 s.
Proof. exact (EQ_MP (@lem4325381 _103681 _103682 s) (@lem4325380 _103681 _103682 s)). Qed.
Lemma lem4325383 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : term10 _103681 _103682 s t.
Proof. exact (@lem4325382 _103681 _103682 s t). Qed.
Lemma lem4325384 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (term10 _103681 _103682 s t) = ((@CROSS _103681 _103682 s t) = (term11 _103681 _103682 s t)).
Proof. exact (eq_refl (term10 _103681 _103682 s t)). Qed.
Lemma lem4325407 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (@CROSS _103681 _103682 s t) = (term11 _103681 _103682 s t).
Proof. exact (EQ_MP (@lem4325384 _103681 _103682 s t) (@lem4325383 _103681 _103682 s t)). Qed.
Lemma lem4325408 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) : (@CROSS _103749 _103746 s t) = (term12 _103746 _103749 s t).
Proof. exact (@lem4325407 _103749 _103746 s t). Qed.
Lemma lem4325419 {_103746 _103749 : Type'} : (@HAS_SIZE (prod _103746 _103749)) = (@HAS_SIZE (prod _103746 _103749)).
Proof. exact (eq_refl (@HAS_SIZE (prod _103746 _103749))). Qed.
Lemma lem4325420 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) : (term13 _103746 _103749 s t) = (term14 _103746 _103749 s t).
Proof. exact (MK_COMB (@lem4325419 _103746 _103749) (@lem4325408 _103746 _103749 s t)). Qed.
Lemma lem4325421 (m : nat) (n : nat) : (Nat.mul m n) = (Nat.mul m n).
Proof. exact (eq_refl (Nat.mul m n)). Qed.
Lemma lem4325422 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) (m : nat) (n : nat) : (term15 _103746 _103749 s t m n) = (term16 _103746 _103749 s t m n).
Proof. exact (MK_COMB (@lem4325420 _103746 _103749 s t) (@lem4325421 m n)). Qed.
Lemma lem4325423 {_103746 _103749 : Type'} (s : _103746 -> Prop) (m : nat) (t : _103749 -> Prop) (n : nat) : (term17 _103746 _103749 s m t n) = (term17 _103746 _103749 s m t n).
Proof. exact (eq_refl (term17 _103746 _103749 s m t n)). Qed.
Lemma lem4325424 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) (m : nat) (n : nat) : (term18 _103746 _103749 s t m n) = (term7 _103746 _103749 s t m n).
Proof. exact (MK_COMB (@lem4325423 _103746 _103749 s m t n) (@lem4325422 _103746 _103749 s t m n)). Qed.
Lemma lem4325426 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : (term7 A B s t m n) = True.
Proof. exact (EQ_MP (@lem4325378 A B s t m n) (@lem4325377 A B s t m n)). Qed.
Lemma lem4325427 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) (m : nat) (n : nat) : (term7 _103746 _103749 s t m n) = True.
Proof. exact (@lem4325426 _103746 _103749 s t m n). Qed.
Lemma lem4325428 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) (m : nat) (n : nat) : (term18 _103746 _103749 s t m n) = True.
Proof. exact (TRANS (@lem4325424 _103746 _103749 s t m n) (@lem4325427 _103746 _103749 s t m n)). Qed.
Lemma lem4325429 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) (m : nat) : (term19 _103746 _103749 s t m) = term20.
Proof. exact (fun_ext (fun n : nat => @lem4325428 _103746 _103749 s t m n)). Qed.
Lemma lem4325430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4325431 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) (m : nat) : (term21 _103746 _103749 s t m) = term22.
Proof. exact (MK_COMB (@lem4325430) (@lem4325429 _103746 _103749 s t m)). Qed.
Lemma lem4325433 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325434 (t : Prop) : (term24 t) = t.
Proof. exact (@lem4325433 nat t). Qed.
Lemma lem4325435 : term22 = True.
Proof. exact (@lem4325434 True). Qed.
Lemma lem4325436 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) (m : nat) : (term21 _103746 _103749 s t m) = True.
Proof. exact (TRANS (@lem4325431 _103746 _103749 s t m) (@lem4325435)). Qed.
Lemma lem4325437 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) : (term25 _103746 _103749 s t) = term20.
Proof. exact (fun_ext (fun m : nat => @lem4325436 _103746 _103749 s t m)). Qed.
Lemma lem4325438 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4325439 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) : (term26 _103746 _103749 s t) = term22.
Proof. exact (MK_COMB (@lem4325438) (@lem4325437 _103746 _103749 s t)). Qed.
Lemma lem4325441 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325442 (t : Prop) : (term24 t) = t.
Proof. exact (@lem4325441 nat t). Qed.
Lemma lem4325443 : term22 = True.
Proof. exact (@lem4325442 True). Qed.
Lemma lem4325444 {_103746 _103749 : Type'} (s : _103746 -> Prop) (t : _103749 -> Prop) : (term26 _103746 _103749 s t) = True.
Proof. exact (TRANS (@lem4325439 _103746 _103749 s t) (@lem4325443)). Qed.
Lemma lem4325445 {_103746 _103749 : Type'} (s : _103746 -> Prop) : (term27 _103746 _103749 s) = (term28 _103749).
Proof. exact (fun_ext (fun t : _103749 -> Prop => @lem4325444 _103746 _103749 s t)). Qed.
Lemma lem4325446 {_103749 : Type'} : (@all (_103749 -> Prop)) = (@all (_103749 -> Prop)).
Proof. exact (eq_refl (@all (_103749 -> Prop))). Qed.
Lemma lem4325447 {_103746 _103749 : Type'} (s : _103746 -> Prop) : (term29 _103746 _103749 s) = (term30 _103749).
Proof. exact (MK_COMB (@lem4325446 _103749) (@lem4325445 _103746 _103749 s)). Qed.
Lemma lem4325449 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325450 {_103749 : Type'} (t : Prop) : (term31 _103749 t) = t.
Proof. exact (@lem4325449 (_103749 -> Prop) t). Qed.
Lemma lem4325451 {_103749 : Type'} : (term30 _103749) = True.
Proof. exact (@lem4325450 _103749 True). Qed.
Lemma lem4325452 {_103746 _103749 : Type'} (s : _103746 -> Prop) : (term29 _103746 _103749 s) = True.
Proof. exact (TRANS (@lem4325447 _103746 _103749 s) (@lem4325451 _103749)). Qed.
Lemma lem4325453 {_103746 _103749 : Type'} : (term32 _103746 _103749) = (term28 _103746).
Proof. exact (fun_ext (fun s : _103746 -> Prop => @lem4325452 _103746 _103749 s)). Qed.
Lemma lem4325454 {_103746 : Type'} : (@all (_103746 -> Prop)) = (@all (_103746 -> Prop)).
Proof. exact (eq_refl (@all (_103746 -> Prop))). Qed.
Lemma lem4325455 {_103746 _103749 : Type'} : (term33 _103746 _103749) = (term30 _103746).
Proof. exact (MK_COMB (@lem4325454 _103746) (@lem4325453 _103746 _103749)). Qed.
Lemma lem4325457 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325458 {_103746 : Type'} (t : Prop) : (term31 _103746 t) = t.
Proof. exact (@lem4325457 (_103746 -> Prop) t). Qed.
Lemma lem4325459 {_103746 : Type'} : (term30 _103746) = True.
Proof. exact (@lem4325458 _103746 True). Qed.
Lemma lem4325460 {_103746 _103749 : Type'} : (term33 _103746 _103749) = True.
Proof. exact (TRANS (@lem4325455 _103746 _103749) (@lem4325459 _103746)). Qed.
Lemma lem4325461 {_103746 _103749 : Type'} : True = (term33 _103746 _103749).
Proof. exact (SYM (@lem4325460 _103746 _103749)). Qed.
Lemma lem4325462 {_103746 _103749 : Type'} : term33 _103746 _103749.
Proof. exact (EQ_MP (@lem4325461 _103746 _103749) (@lem0)). Qed.
