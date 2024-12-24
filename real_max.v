Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_max_term_abbrevs.
Lemma lem1345503 : real_max = term0.
Proof. exact (@real_max_def). Qed.
Lemma lem1345504 (_23971 : real) : _23971 = _23971.
Proof. exact (eq_refl _23971). Qed.
Lemma lem1345505 (_23971 : real) : (real_max _23971) = (term1 _23971).
Proof. exact (MK_COMB (@lem1345503) (@lem1345504 _23971)). Qed.
Lemma lem1345506 (_23971 : real) : (term1 _23971) = (term2 _23971).
Proof. exact (eq_refl (term1 _23971)). Qed.
Lemma lem1345507 (_23971 : real) : (real_max _23971) = (term2 _23971).
Proof. exact (TRANS (@lem1345505 _23971) (@lem1345506 _23971)). Qed.
Lemma lem1345508 (_23972 : real) : _23972 = _23972.
Proof. exact (eq_refl _23972). Qed.
Lemma lem1345509 (_23971 : real) (_23972 : real) : (real_max _23971 _23972) = (term3 _23971 _23972).
Proof. exact (MK_COMB (@lem1345507 _23971) (@lem1345508 _23972)). Qed.
Lemma lem1345510 (_23972 : real) (_23971 : real) : (term3 _23971 _23972) = (term4 _23972 _23971).
Proof. exact (eq_refl (term3 _23971 _23972)). Qed.
Lemma lem1345511 (_23972 : real) (_23971 : real) : (real_max _23971 _23972) = (term4 _23972 _23971).
Proof. exact (TRANS (@lem1345509 _23971 _23972) (@lem1345510 _23972 _23971)). Qed.
Lemma lem1345512 (_23971 : real) : term5 _23971.
Proof. exact (fun _23972 : real => @lem1345511 _23972 _23971). Qed.
Lemma lem1345513 : term6.
Proof. exact (fun _23971 : real => @lem1345512 _23971). Qed.
Lemma lem1345514 (_23971 : real) : term7 _23971.
Proof. exact (@lem1345513 _23971). Qed.
Lemma lem1345515 (_23971 : real) : (term7 _23971) = (term5 _23971).
Proof. exact (eq_refl (term7 _23971)). Qed.
Lemma lem1345516 (_23971 : real) : term5 _23971.
Proof. exact (EQ_MP (@lem1345515 _23971) (@lem1345514 _23971)). Qed.
Lemma lem1345517 (_23971 : real) (_23972 : real) : term8 _23971 _23972.
Proof. exact (@lem1345516 _23971 _23972). Qed.
Lemma lem1345518 (_23972 : real) (_23971 : real) : (term8 _23971 _23972) = ((real_max _23971 _23972) = (term4 _23972 _23971)).
Proof. exact (eq_refl (term8 _23971 _23972)). Qed.
Lemma lem1345519 (_23972 : real) (_23971 : real) : (real_max _23971 _23972) = (term4 _23972 _23971).
Proof. exact (EQ_MP (@lem1345518 _23972 _23971) (@lem1345517 _23971 _23972)). Qed.
Lemma lem1345562 (n : real) (m : real) : (real_max m n) = (term4 n m).
Proof. exact (@lem1345519 n m). Qed.
Lemma lem1345563 (n : real) : term9 n.
Proof. exact (fun m : real => @lem1345562 n m). Qed.
Lemma lem1345564 : term10.
Proof. exact (fun n : real => @lem1345563 n). Qed.
