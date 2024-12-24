Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1111457_term_abbrevs.
Require Import thm1111009_spec.
Require Import thm1111401_spec.
Lemma lem1111402 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1111403 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1111402 A) (@lem1111009 A)). Qed.
Lemma lem1111404 {A : Type'} : term2 A.
Proof. exact (@lem1111403 A term3). Qed.
Lemma lem1111405 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1111406 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1111405 A) (@lem1111404 A)). Qed.
Lemma lem1111407 {A : Type'} (h1 : (@list_of_seq A) = (term5 A)) : (@list_of_seq A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem1111408 {A : Type'} (h1 : (@list_of_seq A) = (term5 A)) : (term5 A) = (@list_of_seq A).
Proof. exact (SYM (@lem1111407 A h1)). Qed.
Lemma lem1111409 {A : Type'} (h1 : (term5 A) = (@list_of_seq A)) : (term5 A) = (@list_of_seq A).
Proof. exact (h1). Qed.
Lemma lem1111410 {A : Type'} (h1 : (term5 A) = (@list_of_seq A)) : (@list_of_seq A) = (term5 A).
Proof. exact (SYM (@lem1111409 A h1)). Qed.
Lemma lem1111411 {A : Type'} : ((@list_of_seq A) = (term5 A)) = ((term5 A) = (@list_of_seq A)).
Proof. exact (prop_ext (fun h1 : (@list_of_seq A) = (term5 A) => @lem1111408 A h1) (fun h1 : (term5 A) = (@list_of_seq A) => @lem1111410 A h1)). Qed.
Lemma lem1111414 {A : Type'} : (term5 A) = (@list_of_seq A).
Proof. exact (EQ_MP (@lem1111411 A) (@lem1111401 A)). Qed.
Lemma lem1111415 {A : Type'} : (term5 A) = (@list_of_seq A).
Proof. exact (@lem1111414 A). Qed.
Lemma lem1111416 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1111417 {A : Type'} (s : nat -> A) : (term6 A s) = (@list_of_seq A s).
Proof. exact (MK_COMB (@lem1111415 A) (@lem1111416 A s)). Qed.
Lemma lem1111418 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1111419 {A : Type'} (s : nat -> A) : (term7 A s) = (term8 A s).
Proof. exact (MK_COMB (@lem1111417 A s) (@lem1111418)). Qed.
Lemma lem1111420 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1111421 {A : Type'} (s : nat -> A) : (term9 A s) = (term10 A s).
Proof. exact (MK_COMB (@lem1111420 A) (@lem1111419 A s)). Qed.
Lemma lem1111422 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1111423 {A : Type'} (s : nat -> A) : ((term7 A s) = (@nil A)) = ((term8 A s) = (@nil A)).
Proof. exact (MK_COMB (@lem1111421 A s) (@lem1111422 A)). Qed.
Lemma lem1111424 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem1111423 A s)). Qed.
Lemma lem1111425 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem1111426 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem1111425 A) (@lem1111424 A)). Qed.
Lemma lem1111427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1111428 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem1111427) (@lem1111426 A)). Qed.
Lemma lem1111430 {A : Type'} : (term5 A) = (@list_of_seq A).
Proof. exact (EQ_MP (@lem1111411 A) (@lem1111401 A)). Qed.
Lemma lem1111431 {A : Type'} : (term5 A) = (@list_of_seq A).
Proof. exact (@lem1111430 A). Qed.
Lemma lem1111432 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1111433 {A : Type'} (s : nat -> A) : (term6 A s) = (@list_of_seq A s).
Proof. exact (MK_COMB (@lem1111431 A) (@lem1111432 A s)). Qed.
Lemma lem1111434 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1111435 {A : Type'} (s : nat -> A) (n : nat) : (term17 A s n) = (term18 A s n).
Proof. exact (MK_COMB (@lem1111433 A s) (@lem1111434 n)). Qed.
Lemma lem1111436 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1111437 {A : Type'} (s : nat -> A) (n : nat) : (term19 A s n) = (term20 A s n).
Proof. exact (MK_COMB (@lem1111436 A) (@lem1111435 A s n)). Qed.
Lemma lem1111439 {A : Type'} : (term5 A) = (@list_of_seq A).
Proof. exact (EQ_MP (@lem1111411 A) (@lem1111401 A)). Qed.
Lemma lem1111440 {A : Type'} : (term5 A) = (@list_of_seq A).
Proof. exact (@lem1111439 A). Qed.
Lemma lem1111441 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1111442 {A : Type'} (s : nat -> A) : (term6 A s) = (@list_of_seq A s).
Proof. exact (MK_COMB (@lem1111440 A) (@lem1111441 A s)). Qed.
Lemma lem1111443 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1111444 {A : Type'} (s : nat -> A) (n : nat) : (term21 A s n) = (@list_of_seq A s n).
Proof. exact (MK_COMB (@lem1111442 A s) (@lem1111443 n)). Qed.
Lemma lem1111445 {A : Type'} : (@List.app A) = (@List.app A).
Proof. exact (eq_refl (@List.app A)). Qed.
Lemma lem1111446 {A : Type'} (s : nat -> A) (n : nat) : (term22 A s n) = (term23 A s n).
Proof. exact (MK_COMB (@lem1111445 A) (@lem1111444 A s n)). Qed.
Lemma lem1111447 {A : Type'} (s : nat -> A) (n : nat) : (term24 A s n) = (term24 A s n).
Proof. exact (eq_refl (term24 A s n)). Qed.
Lemma lem1111448 {A : Type'} (s : nat -> A) (n : nat) : (term25 A s n) = (term26 A s n).
Proof. exact (MK_COMB (@lem1111446 A s n) (@lem1111447 A s n)). Qed.
Lemma lem1111449 {A : Type'} (s : nat -> A) (n : nat) : ((term17 A s n) = (term25 A s n)) = ((term18 A s n) = (term26 A s n)).
Proof. exact (MK_COMB (@lem1111437 A s n) (@lem1111448 A s n)). Qed.
Lemma lem1111450 {A : Type'} (s : nat -> A) : (term27 A s) = (term28 A s).
Proof. exact (fun_ext (fun n : nat => @lem1111449 A s n)). Qed.
Lemma lem1111451 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1111452 {A : Type'} (s : nat -> A) : (term29 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem1111451) (@lem1111450 A s)). Qed.
Lemma lem1111453 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem1111452 A s)). Qed.
Lemma lem1111454 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem1111455 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (MK_COMB (@lem1111454 A) (@lem1111453 A)). Qed.
Lemma lem1111456 {A : Type'} : (term4 A) = (term35 A).
Proof. exact (MK_COMB (@lem1111428 A) (@lem1111455 A)). Qed.
Lemma lem1111457 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem1111456 A) (@lem1111406 A)). Qed.
