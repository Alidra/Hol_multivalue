Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1317782_term_abbrevs.
Require Import thm32_spec.
Require Import thm9127_spec.
Lemma lem1317745 : hreal_of_num = term0.
Proof. exact (@hreal_of_num_def). Qed.
Lemma lem1317746 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1317747 (m : nat) : (hreal_of_num m) = (term1 m).
Proof. exact (MK_COMB (@lem1317745) (@lem1317746 m)). Qed.
Lemma lem1317748 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1317749 (m : nat) : (term3 m) = (term3 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1317750 (m : nat) : ((hreal_of_num m) = (term1 m)) = ((hreal_of_num m) = (term2 m)).
Proof. exact (MK_COMB (@lem1317749 m) (@lem1317748 m)). Qed.
Lemma lem1317757 (m : nat) : (hreal_of_num m) = (term2 m).
Proof. exact (EQ_MP (@lem1317750 m) (@lem1317747 m)). Qed.
Lemma lem1317758 (m : nat) (u : nadd) (h1 : term4 m u) : term4 m u.
Proof. exact (h1). Qed.
Lemma lem1317759 (m : nat) (u : nadd) (h1 : term4 m u) : term4 m u.
Proof. exact (h1). Qed.
Lemma lem1317760 (m : nat) (u : nadd) (h1 : term4 m u) : term4 m u.
Proof. exact (h1). Qed.
Lemma lem1317763 (m : nat) (u : nadd) : term5 m u.
Proof. exact (fun h0 : term4 m u => @lem1317760 m u h0). Qed.
Lemma lem1317764 (m : nat) (u : nadd) (h1 : term4 m u) : term4 m u.
Proof. exact (@lem1317763 m u (@lem1317759 m u h1)). Qed.
Lemma lem1317765 (m : nat) (u : nadd) : term5 m u.
Proof. exact (fun h0 : term4 m u => @lem1317764 m u h0). Qed.
Lemma lem1317766 (m : nat) (u : nadd) : term5 m u.
Proof. exact (fun h0 : term4 m u => @lem1317758 m u h0). Qed.
Lemma lem1317767 (m : nat) (u : nadd) : term6 m u.
Proof. exact (conj (@lem1317766 m u) (@lem1317765 m u)). Qed.
Lemma lem1317768 (m : nat) (u : nadd) : (term6 m u) = ((term4 m u) = (term4 m u)).
Proof. exact (@lem32 (term4 m u) (term4 m u)). Qed.
Lemma lem1317769 (m : nat) (u : nadd) : (term4 m u) = (term4 m u).
Proof. exact (EQ_MP (@lem1317768 m u) (@lem1317767 m u)). Qed.
Lemma lem1317770 (m : nat) : (term7 m) = (term7 m).
Proof. exact (fun_ext (fun u : nadd => @lem1317769 m u)). Qed.
Lemma lem1317771 : mk_hreal = mk_hreal.
Proof. exact (eq_refl mk_hreal). Qed.
Lemma lem1317772 (m : nat) : (term2 m) = (term2 m).
Proof. exact (MK_COMB (@lem1317771) (@lem1317770 m)). Qed.
Lemma lem1317773 (m : nat) : (hreal_of_num m) = (term2 m).
Proof. exact (TRANS (@lem1317757 m) (@lem1317772 m)). Qed.
Lemma lem1317774 (t : nadd -> Prop) : (term8 t) = t.
Proof. exact (@lem9127 nadd Prop t). Qed.
Lemma lem1317777 (m : nat) : (term7 m) = (term9 m).
Proof. exact (@lem1317774 (term9 m)). Qed.
Lemma lem1317778 : mk_hreal = mk_hreal.
Proof. exact (eq_refl mk_hreal). Qed.
Lemma lem1317779 (m : nat) : (term2 m) = (term10 m).
Proof. exact (MK_COMB (@lem1317778) (@lem1317777 m)). Qed.
Lemma lem1317780 (m : nat) : (term3 m) = (term3 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1317781 (m : nat) : ((hreal_of_num m) = (term2 m)) = ((hreal_of_num m) = (term10 m)).
Proof. exact (MK_COMB (@lem1317780 m) (@lem1317779 m)). Qed.
Lemma lem1317782 (m : nat) : (hreal_of_num m) = (term10 m).
Proof. exact (EQ_MP (@lem1317781 m) (@lem1317773 m)). Qed.
