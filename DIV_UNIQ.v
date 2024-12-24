Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_UNIQ_term_abbrevs.
Require Import DIVMOD_UNIQ_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem169706 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : term0 m q r n.
Proof. exact (h1). Qed.
Lemma lem169707 (m : nat) : term1 m.
Proof. exact (@lem169651 m). Qed.
Lemma lem169708 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem169709 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem169708 m) (@lem169707 m)). Qed.
Lemma lem169710 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem169709 m n). Qed.
Lemma lem169711 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem169712 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem169711 m n) (@lem169710 m n)). Qed.
Lemma lem169713 (m : nat) (n : nat) (q : nat) : term5 m n q.
Proof. exact (@lem169712 m n q). Qed.
Lemma lem169714 (q : nat) (m : nat) (n : nat) : (term5 m n q) = (term6 q m n).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem169715 (q : nat) (m : nat) (n : nat) : term6 q m n.
Proof. exact (EQ_MP (@lem169714 q m n) (@lem169713 m n q)). Qed.
Lemma lem169716 (q : nat) (m : nat) (n : nat) (r : nat) : term7 q m n r.
Proof. exact (@lem169715 q m n r). Qed.
Lemma lem169717 (q : nat) (m : nat) (n : nat) (r : nat) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem169720 (q : nat) (m : nat) (n : nat) (r : nat) : term8 q m n r.
Proof. exact (EQ_MP (@lem169717 q m n r) (@lem169716 q m n r)). Qed.
Lemma lem169721 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : term9 q m n r.
Proof. exact (@lem169720 q m n r (@lem169706 m q r n h1)). Qed.
Lemma lem169727 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : (Nat.div m n) = q.
Proof. exact (proj1 (@lem169721 m q r n h1)). Qed.
Lemma lem169728 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem169729 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : (term10 m n) = (@eq nat q).
Proof. exact (MK_COMB (@lem169728) (@lem169727 m q r n h1)). Qed.
Lemma lem169730 (q : nat) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem169731 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : ((Nat.div m n) = q) = (q = q).
Proof. exact (MK_COMB (@lem169729 m q r n h1) (@lem169730 q)). Qed.
Lemma lem169733 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem169734 (x : nat) : (x = x) = True.
Proof. exact (@lem169733 nat x). Qed.
Lemma lem169735 (q : nat) : (q = q) = True.
Proof. exact (@lem169734 q). Qed.
Lemma lem169736 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : ((Nat.div m n) = q) = True.
Proof. exact (TRANS (@lem169731 m q r n h1) (@lem169735 q)). Qed.
Lemma lem169737 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : True = ((Nat.div m n) = q).
Proof. exact (SYM (@lem169736 m q r n h1)). Qed.
Lemma lem169738 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : (Nat.div m n) = q.
Proof. exact (EQ_MP (@lem169737 m q r n h1) (@lem0)). Qed.
Lemma lem169739 (r : nat) (m : nat) (n : nat) (q : nat) : term11 r m n q.
Proof. exact (fun h0 : term0 m q r n => @lem169738 m q r n h0). Qed.
Lemma lem169744 (m : nat) (n : nat) (q : nat) : term12 m n q.
Proof. exact (fun r : nat => @lem169739 r m n q). Qed.
Lemma lem169749 (m : nat) (n : nat) : term13 m n.
Proof. exact (fun q : nat => @lem169744 m n q). Qed.
Lemma lem169754 (m : nat) : term14 m.
Proof. exact (fun n : nat => @lem169749 m n). Qed.
Lemma lem169759 : term15.
Proof. exact (fun m : nat => @lem169754 m). Qed.
