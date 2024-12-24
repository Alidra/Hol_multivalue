Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337531_term_abbrevs.
Require Import thm32_spec.
Require Import thm9127_spec.
Lemma lem1337494 : real_of_num = term0.
Proof. exact (@real_of_num_def). Qed.
Lemma lem1337495 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1337496 (m : nat) : (real_of_num m) = (term1 m).
Proof. exact (MK_COMB (@lem1337494) (@lem1337495 m)). Qed.
Lemma lem1337497 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1337498 (m : nat) : (term3 m) = (term3 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1337499 (m : nat) : ((real_of_num m) = (term1 m)) = ((real_of_num m) = (term2 m)).
Proof. exact (MK_COMB (@lem1337498 m) (@lem1337497 m)). Qed.
Lemma lem1337506 (m : nat) : (real_of_num m) = (term2 m).
Proof. exact (EQ_MP (@lem1337499 m) (@lem1337496 m)). Qed.
Lemma lem1337507 (m : nat) (u : prod hreal hreal) (h1 : term4 m u) : term4 m u.
Proof. exact (h1). Qed.
Lemma lem1337508 (m : nat) (u : prod hreal hreal) (h1 : term4 m u) : term4 m u.
Proof. exact (h1). Qed.
Lemma lem1337509 (m : nat) (u : prod hreal hreal) (h1 : term4 m u) : term4 m u.
Proof. exact (h1). Qed.
Lemma lem1337512 (m : nat) (u : prod hreal hreal) : term5 m u.
Proof. exact (fun h0 : term4 m u => @lem1337509 m u h0). Qed.
Lemma lem1337513 (m : nat) (u : prod hreal hreal) (h1 : term4 m u) : term4 m u.
Proof. exact (@lem1337512 m u (@lem1337508 m u h1)). Qed.
Lemma lem1337514 (m : nat) (u : prod hreal hreal) : term5 m u.
Proof. exact (fun h0 : term4 m u => @lem1337513 m u h0). Qed.
Lemma lem1337515 (m : nat) (u : prod hreal hreal) : term5 m u.
Proof. exact (fun h0 : term4 m u => @lem1337507 m u h0). Qed.
Lemma lem1337516 (m : nat) (u : prod hreal hreal) : term6 m u.
Proof. exact (conj (@lem1337515 m u) (@lem1337514 m u)). Qed.
Lemma lem1337517 (m : nat) (u : prod hreal hreal) : (term6 m u) = ((term4 m u) = (term4 m u)).
Proof. exact (@lem32 (term4 m u) (term4 m u)). Qed.
Lemma lem1337518 (m : nat) (u : prod hreal hreal) : (term4 m u) = (term4 m u).
Proof. exact (EQ_MP (@lem1337517 m u) (@lem1337516 m u)). Qed.
Lemma lem1337519 (m : nat) : (term7 m) = (term7 m).
Proof. exact (fun_ext (fun u : prod hreal hreal => @lem1337518 m u)). Qed.
Lemma lem1337520 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1337521 (m : nat) : (term2 m) = (term2 m).
Proof. exact (MK_COMB (@lem1337520) (@lem1337519 m)). Qed.
Lemma lem1337522 (m : nat) : (real_of_num m) = (term2 m).
Proof. exact (TRANS (@lem1337506 m) (@lem1337521 m)). Qed.
Lemma lem1337523 (t : type1233) : (term8 t) = t.
Proof. exact (@lem9127 (prod hreal hreal) Prop t). Qed.
Lemma lem1337526 (m : nat) : (term7 m) = (term9 m).
Proof. exact (@lem1337523 (term9 m)). Qed.
Lemma lem1337527 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1337528 (m : nat) : (term2 m) = (term10 m).
Proof. exact (MK_COMB (@lem1337527) (@lem1337526 m)). Qed.
Lemma lem1337529 (m : nat) : (term3 m) = (term3 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1337530 (m : nat) : ((real_of_num m) = (term2 m)) = ((real_of_num m) = (term10 m)).
Proof. exact (MK_COMB (@lem1337529 m) (@lem1337528 m)). Qed.
Lemma lem1337531 (m : nat) : (real_of_num m) = (term10 m).
Proof. exact (EQ_MP (@lem1337530 m) (@lem1337522 m)). Qed.
