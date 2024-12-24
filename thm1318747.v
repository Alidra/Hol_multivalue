Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318747_term_abbrevs.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_SYM_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import thm1317735_spec.
Require Import thm1317744_spec.
Require Import thm38926_spec.
Lemma lem1318737 : term0.
Proof. exact (fun a : hreal => @lem1317735 a). Qed.
Lemma lem1318738 : term1.
Proof. exact (fun r : nadd -> Prop => @lem1317744 r). Qed.
Lemma lem1318739 : term2.
Proof. exact (conj (@lem1318737) (@lem1318738)). Qed.
Lemma lem1318740 : term3.
Proof. exact (conj (@lem1268295) (@lem1318739)). Qed.
Lemma lem1318741 : term4.
Proof. exact (conj (@lem1268060) (@lem1318740)). Qed.
Lemma lem1318742 : term5.
Proof. exact (conj (@lem1267990) (@lem1318741)). Qed.
Lemma lem1318744 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) : term6 Absty Repty mk R dest.
Proof. exact (fun h0 : term7 Absty Repty R dest mk => @lem38926 Absty Repty R dest mk h0). Qed.
Lemma lem1318745 (mk : type926) (R : type1554) (dest : type1546) : term8 mk R dest.
Proof. exact (@lem1318744 hreal nadd mk R dest). Qed.
Lemma lem1318746 : term9.
Proof. exact (@lem1318745 mk_hreal nadd_eq dest_hreal). Qed.
Lemma lem1318747 : term10.
Proof. exact (@lem1318746 (@lem1318742)). Qed.
