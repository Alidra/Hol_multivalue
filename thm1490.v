Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1490_term_abbrevs.
Require Import NOT_DEF_spec.
Require Import thm0_spec.
Require Import thm98_spec.
Lemma lem1472 (h1 : ~ True) : ~ True.
Proof. exact (h1). Qed.
Lemma lem1473 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1474 : (~ True) = term0.
Proof. exact (MK_COMB (@lem56) (@lem1473)). Qed.
Lemma lem1475 : term0 = (True -> False).
Proof. exact (eq_refl term0). Qed.
Lemma lem1476 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1477 : ((~ True) = term0) = ((~ True) = (True -> False)).
Proof. exact (MK_COMB (@lem1476) (@lem1475)). Qed.
Lemma lem1478 : (~ True) = (True -> False).
Proof. exact (EQ_MP (@lem1477) (@lem1474)). Qed.
Lemma lem1479 (h1 : ~ True) : True -> False.
Proof. exact (EQ_MP (@lem1478) (@lem1472 h1)). Qed.
Lemma lem1480 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem1481 (h1 : True) (h2 : ~ True) : False.
Proof. exact (@lem1479 h2 (@lem1480 h1)). Qed.
Lemma lem1482 (h1 : ~ True) : True = False.
Proof. exact (prop_ext (fun h2 : True => @lem1481 h2 h1) (fun h2 : False => @lem0)). Qed.
Lemma lem1483 (h1 : ~ True) : False.
Proof. exact (EQ_MP (@lem1482 h1) (@lem0)). Qed.
Lemma lem1484 : term2.
Proof. exact (fun h0 : ~ True => @lem1483 h0). Qed.
Lemma lem1485 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1486 (h1 : False) : ~ True.
Proof. exact (@lem98 (~ True) h1). Qed.
Lemma lem1487 (h1 : False) : False = (~ True).
Proof. exact (prop_ext (fun h2 : False => @lem1486 h1) (fun h2 : ~ True => @lem1485 h1)). Qed.
Lemma lem1488 (h1 : False) : ~ True.
Proof. exact (EQ_MP (@lem1487 h1) (@lem1485 h1)). Qed.
Lemma lem1489 : term3.
Proof. exact (fun h0 : False => @lem1488 h0). Qed.
Lemma lem1490 : term4.
Proof. exact (conj (@lem1484) (@lem1489)). Qed.
