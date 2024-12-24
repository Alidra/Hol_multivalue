Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338093_term_abbrevs.
Require Import TREAL_EQ_REFL_spec.
Require Import TREAL_EQ_SYM_spec.
Require Import TREAL_EQ_TRANS_spec.
Require Import thm1337484_spec.
Require Import thm1337493_spec.
Require Import thm38926_spec.
Lemma lem1338083 : term0.
Proof. exact (fun a : real => @lem1337484 a). Qed.
Lemma lem1338084 : term1.
Proof. exact (fun r : type1233 => @lem1337493 r). Qed.
Lemma lem1338085 : term2.
Proof. exact (conj (@lem1338083) (@lem1338084)). Qed.
Lemma lem1338086 : term3.
Proof. exact (conj (@lem1326778) (@lem1338085)). Qed.
Lemma lem1338087 : term4.
Proof. exact (conj (@lem1326359) (@lem1338086)). Qed.
Lemma lem1338088 : term5.
Proof. exact (conj (@lem1326193) (@lem1338087)). Qed.
Lemma lem1338090 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) : term6 Absty Repty mk R dest.
Proof. exact (fun h0 : term7 Absty Repty R dest mk => @lem38926 Absty Repty R dest mk h0). Qed.
Lemma lem1338091 (mk : type334) (R : type1232) (dest : type1619) : term8 mk R dest.
Proof. exact (@lem1338090 real (prod hreal hreal) mk R dest). Qed.
Lemma lem1338092 : term9.
Proof. exact (@lem1338091 mk_real treal_eq dest_real). Qed.
Lemma lem1338093 : term10.
Proof. exact (@lem1338092 (@lem1338088)). Qed.
