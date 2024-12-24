Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1099508_term_abbrevs.
Require Import thm1099092_spec.
Require Import thm1099454_spec.
Lemma lem1099455 {_25272 : Type'} : (term0 _25272) = (term1 _25272).
Proof. exact (eq_refl (term0 _25272)). Qed.
Lemma lem1099456 {_25272 : Type'} : term1 _25272.
Proof. exact (EQ_MP (@lem1099455 _25272) (@lem1099092 _25272)). Qed.
Lemma lem1099457 {_25272 : Type'} : term2 _25272.
Proof. exact (@lem1099456 _25272 term3). Qed.
Lemma lem1099458 {_25272 : Type'} : (term2 _25272) = (term4 _25272).
Proof. exact (eq_refl (term2 _25272)). Qed.
Lemma lem1099459 {_25272 : Type'} : term4 _25272.
Proof. exact (EQ_MP (@lem1099458 _25272) (@lem1099457 _25272)). Qed.
Lemma lem1099460 {_25272 : Type'} (h1 : (@repeat_with_perm_args _25272) = (term5 _25272)) : (@repeat_with_perm_args _25272) = (term5 _25272).
Proof. exact (h1). Qed.
Lemma lem1099461 {_25272 : Type'} (h1 : (@repeat_with_perm_args _25272) = (term5 _25272)) : (term5 _25272) = (@repeat_with_perm_args _25272).
Proof. exact (SYM (@lem1099460 _25272 h1)). Qed.
Lemma lem1099462 {_25272 : Type'} (h1 : (term5 _25272) = (@repeat_with_perm_args _25272)) : (term5 _25272) = (@repeat_with_perm_args _25272).
Proof. exact (h1). Qed.
Lemma lem1099463 {_25272 : Type'} (h1 : (term5 _25272) = (@repeat_with_perm_args _25272)) : (@repeat_with_perm_args _25272) = (term5 _25272).
Proof. exact (SYM (@lem1099462 _25272 h1)). Qed.
Lemma lem1099464 {_25272 : Type'} : ((@repeat_with_perm_args _25272) = (term5 _25272)) = ((term5 _25272) = (@repeat_with_perm_args _25272)).
Proof. exact (prop_ext (fun h1 : (@repeat_with_perm_args _25272) = (term5 _25272) => @lem1099461 _25272 h1) (fun h1 : (term5 _25272) = (@repeat_with_perm_args _25272) => @lem1099463 _25272 h1)). Qed.
Lemma lem1099467 {_25272 : Type'} : (term5 _25272) = (@repeat_with_perm_args _25272).
Proof. exact (EQ_MP (@lem1099464 _25272) (@lem1099454 _25272)). Qed.
Lemma lem1099468 {_25272 : Type'} : (term5 _25272) = (@repeat_with_perm_args _25272).
Proof. exact (@lem1099467 _25272). Qed.
Lemma lem1099469 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1099470 {_25272 : Type'} : (term6 _25272) = (term7 _25272).
Proof. exact (MK_COMB (@lem1099468 _25272) (@lem1099469)). Qed.
Lemma lem1099471 {_25272 : Type'} (x : _25272) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1099472 {_25272 : Type'} (x : _25272) : (term8 _25272 x) = (term9 _25272 x).
Proof. exact (MK_COMB (@lem1099470 _25272) (@lem1099471 _25272 x)). Qed.
Lemma lem1099473 {_25272 : Type'} : (@eq (list _25272)) = (@eq (list _25272)).
Proof. exact (eq_refl (@eq (list _25272))). Qed.
Lemma lem1099474 {_25272 : Type'} (x : _25272) : (term10 _25272 x) = (term11 _25272 x).
Proof. exact (MK_COMB (@lem1099473 _25272) (@lem1099472 _25272 x)). Qed.
Lemma lem1099475 {_25272 : Type'} : (@nil _25272) = (@nil _25272).
Proof. exact (eq_refl (@nil _25272)). Qed.
Lemma lem1099476 {_25272 : Type'} (x : _25272) : ((term8 _25272 x) = (@nil _25272)) = ((term9 _25272 x) = (@nil _25272)).
Proof. exact (MK_COMB (@lem1099474 _25272 x) (@lem1099475 _25272)). Qed.
Lemma lem1099477 {_25272 : Type'} : (term12 _25272) = (term13 _25272).
Proof. exact (fun_ext (fun x : _25272 => @lem1099476 _25272 x)). Qed.
Lemma lem1099478 {_25272 : Type'} : (@all _25272) = (@all _25272).
Proof. exact (eq_refl (@all _25272)). Qed.
Lemma lem1099479 {_25272 : Type'} : (term14 _25272) = (term15 _25272).
Proof. exact (MK_COMB (@lem1099478 _25272) (@lem1099477 _25272)). Qed.
Lemma lem1099480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1099481 {_25272 : Type'} : (term16 _25272) = (term17 _25272).
Proof. exact (MK_COMB (@lem1099480) (@lem1099479 _25272)). Qed.
Lemma lem1099483 {_25272 : Type'} : (term5 _25272) = (@repeat_with_perm_args _25272).
Proof. exact (EQ_MP (@lem1099464 _25272) (@lem1099454 _25272)). Qed.
Lemma lem1099484 {_25272 : Type'} : (term5 _25272) = (@repeat_with_perm_args _25272).
Proof. exact (@lem1099483 _25272). Qed.
Lemma lem1099485 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1099486 {_25272 : Type'} (n : nat) : (term18 _25272 n) = (term19 _25272 n).
Proof. exact (MK_COMB (@lem1099484 _25272) (@lem1099485 n)). Qed.
Lemma lem1099487 {_25272 : Type'} (x : _25272) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1099488 {_25272 : Type'} (n : nat) (x : _25272) : (term20 _25272 n x) = (term21 _25272 n x).
Proof. exact (MK_COMB (@lem1099486 _25272 n) (@lem1099487 _25272 x)). Qed.
Lemma lem1099489 {_25272 : Type'} : (@eq (list _25272)) = (@eq (list _25272)).
Proof. exact (eq_refl (@eq (list _25272))). Qed.
Lemma lem1099490 {_25272 : Type'} (n : nat) (x : _25272) : (term22 _25272 n x) = (term23 _25272 n x).
Proof. exact (MK_COMB (@lem1099489 _25272) (@lem1099488 _25272 n x)). Qed.
Lemma lem1099492 {_25272 : Type'} : (term5 _25272) = (@repeat_with_perm_args _25272).
Proof. exact (EQ_MP (@lem1099464 _25272) (@lem1099454 _25272)). Qed.
Lemma lem1099493 {_25272 : Type'} : (term5 _25272) = (@repeat_with_perm_args _25272).
Proof. exact (@lem1099492 _25272). Qed.
Lemma lem1099494 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1099495 {_25272 : Type'} (n : nat) : (term24 _25272 n) = (@repeat_with_perm_args _25272 n).
Proof. exact (MK_COMB (@lem1099493 _25272) (@lem1099494 n)). Qed.
Lemma lem1099496 {_25272 : Type'} (x : _25272) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1099497 {_25272 : Type'} (n : nat) (x : _25272) : (term25 _25272 n x) = (@repeat_with_perm_args _25272 n x).
Proof. exact (MK_COMB (@lem1099495 _25272 n) (@lem1099496 _25272 x)). Qed.
Lemma lem1099498 {_25272 : Type'} (x : _25272) : (@cons _25272 x) = (@cons _25272 x).
Proof. exact (eq_refl (@cons _25272 x)). Qed.
Lemma lem1099499 {_25272 : Type'} (n : nat) (x : _25272) : (term26 _25272 n x) = (term27 _25272 n x).
Proof. exact (MK_COMB (@lem1099498 _25272 x) (@lem1099497 _25272 n x)). Qed.
Lemma lem1099500 {_25272 : Type'} (n : nat) (x : _25272) : ((term20 _25272 n x) = (term26 _25272 n x)) = ((term21 _25272 n x) = (term27 _25272 n x)).
Proof. exact (MK_COMB (@lem1099490 _25272 n x) (@lem1099499 _25272 n x)). Qed.
Lemma lem1099501 {_25272 : Type'} (n : nat) : (term28 _25272 n) = (term29 _25272 n).
Proof. exact (fun_ext (fun x : _25272 => @lem1099500 _25272 n x)). Qed.
Lemma lem1099502 {_25272 : Type'} : (@all _25272) = (@all _25272).
Proof. exact (eq_refl (@all _25272)). Qed.
Lemma lem1099503 {_25272 : Type'} (n : nat) : (term30 _25272 n) = (term31 _25272 n).
Proof. exact (MK_COMB (@lem1099502 _25272) (@lem1099501 _25272 n)). Qed.
Lemma lem1099504 {_25272 : Type'} : (term32 _25272) = (term33 _25272).
Proof. exact (fun_ext (fun n : nat => @lem1099503 _25272 n)). Qed.
Lemma lem1099505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1099506 {_25272 : Type'} : (term34 _25272) = (term35 _25272).
Proof. exact (MK_COMB (@lem1099505) (@lem1099504 _25272)). Qed.
Lemma lem1099507 {_25272 : Type'} : (term4 _25272) = (term36 _25272).
Proof. exact (MK_COMB (@lem1099481 _25272) (@lem1099506 _25272)). Qed.
Lemma lem1099508 {_25272 : Type'} : term36 _25272.
Proof. exact (EQ_MP (@lem1099507 _25272) (@lem1099459 _25272)). Qed.
