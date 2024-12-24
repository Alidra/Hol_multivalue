Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import AND_CLAUSES_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm98_spec.
Lemma lem1505 (t : Prop) (h1 : True /\ t) : True /\ t.
Proof. exact (h1). Qed.
Lemma lem1506 (t : Prop) (h1 : True /\ t) : t.
Proof. exact (proj2 (@lem1505 t h1)). Qed.
Lemma lem1508 (t : Prop) : term0 t.
Proof. exact (fun h0 : True /\ t => @lem1506 t h0). Qed.
Lemma lem1509 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1510 (t : Prop) (h1 : t) : True /\ t.
Proof. exact (conj (@lem0) (@lem1509 t h1)). Qed.
Lemma lem1511 (t : Prop) : term1 t.
Proof. exact (fun h0 : t => @lem1510 t h0). Qed.
Lemma lem1512 (t : Prop) : term2 t.
Proof. exact (conj (@lem1508 t) (@lem1511 t)). Qed.
Lemma lem1513 (t : Prop) : (term2 t) = ((True /\ t) = t).
Proof. exact (@lem32 (True /\ t) t). Qed.
Lemma lem1514 (t : Prop) : (True /\ t) = t.
Proof. exact (EQ_MP (@lem1513 t) (@lem1512 t)). Qed.
Lemma lem1515 (t : Prop) (h1 : t /\ True) : t /\ True.
Proof. exact (h1). Qed.
Lemma lem1517 (t : Prop) (h1 : t /\ True) : t.
Proof. exact (proj1 (@lem1515 t h1)). Qed.
Lemma lem1518 (t : Prop) : term3 t.
Proof. exact (fun h0 : t /\ True => @lem1517 t h0). Qed.
Lemma lem1519 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1520 (t : Prop) (h1 : t) : t /\ True.
Proof. exact (conj (@lem1519 t h1) (@lem0)). Qed.
Lemma lem1521 (t : Prop) : term4 t.
Proof. exact (fun h0 : t => @lem1520 t h0). Qed.
Lemma lem1522 (t : Prop) : term5 t.
Proof. exact (conj (@lem1518 t) (@lem1521 t)). Qed.
Lemma lem1523 (t : Prop) : (term5 t) = ((t /\ True) = t).
Proof. exact (@lem32 (t /\ True) t). Qed.
Lemma lem1524 (t : Prop) : (t /\ True) = t.
Proof. exact (EQ_MP (@lem1523 t) (@lem1522 t)). Qed.
Lemma lem1525 (t : Prop) (h1 : False /\ t) : False /\ t.
Proof. exact (h1). Qed.
Lemma lem1527 (t : Prop) (h1 : False /\ t) : False.
Proof. exact (proj1 (@lem1525 t h1)). Qed.
Lemma lem1528 (t : Prop) : term6 t.
Proof. exact (fun h0 : False /\ t => @lem1527 t h0). Qed.
Lemma lem1529 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1530 (t : Prop) (h1 : False) : False /\ t.
Proof. exact (@lem98 (False /\ t) h1). Qed.
Lemma lem1531 (t : Prop) (h1 : False) : False = (False /\ t).
Proof. exact (prop_ext (fun h2 : False => @lem1530 t h1) (fun h2 : False /\ t => @lem1529 h1)). Qed.
Lemma lem1532 (t : Prop) (h1 : False) : False /\ t.
Proof. exact (EQ_MP (@lem1531 t h1) (@lem1529 h1)). Qed.
Lemma lem1533 (t : Prop) : term7 t.
Proof. exact (fun h0 : False => @lem1532 t h0). Qed.
Lemma lem1534 (t : Prop) : term8 t.
Proof. exact (conj (@lem1528 t) (@lem1533 t)). Qed.
Lemma lem1535 (t : Prop) : (term8 t) = ((False /\ t) = False).
Proof. exact (@lem32 (False /\ t) False). Qed.
Lemma lem1536 (t : Prop) : (False /\ t) = False.
Proof. exact (EQ_MP (@lem1535 t) (@lem1534 t)). Qed.
Lemma lem1537 (t : Prop) (h1 : t /\ False) : t /\ False.
Proof. exact (h1). Qed.
Lemma lem1538 (t : Prop) (h1 : t /\ False) : False.
Proof. exact (proj2 (@lem1537 t h1)). Qed.
Lemma lem1540 (t : Prop) : term9 t.
Proof. exact (fun h0 : t /\ False => @lem1538 t h0). Qed.
Lemma lem1541 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1542 (t : Prop) (h1 : False) : t /\ False.
Proof. exact (@lem98 (t /\ False) h1). Qed.
Lemma lem1543 (t : Prop) (h1 : False) : False = (t /\ False).
Proof. exact (prop_ext (fun h2 : False => @lem1542 t h1) (fun h2 : t /\ False => @lem1541 h1)). Qed.
Lemma lem1544 (t : Prop) (h1 : False) : t /\ False.
Proof. exact (EQ_MP (@lem1543 t h1) (@lem1541 h1)). Qed.
Lemma lem1545 (t : Prop) : term10 t.
Proof. exact (fun h0 : False => @lem1544 t h0). Qed.
Lemma lem1546 (t : Prop) : term11 t.
Proof. exact (conj (@lem1540 t) (@lem1545 t)). Qed.
Lemma lem1547 (t : Prop) : (term11 t) = ((t /\ False) = False).
Proof. exact (@lem32 (t /\ False) False). Qed.
Lemma lem1548 (t : Prop) : (t /\ False) = False.
Proof. exact (EQ_MP (@lem1547 t) (@lem1546 t)). Qed.
Lemma lem1549 (t : Prop) (h1 : t /\ t) : t /\ t.
Proof. exact (h1). Qed.
Lemma lem1550 (t : Prop) (h1 : t /\ t) : t.
Proof. exact (proj2 (@lem1549 t h1)). Qed.
Lemma lem1552 (t : Prop) : term12 t.
Proof. exact (fun h0 : t /\ t => @lem1550 t h0). Qed.
Lemma lem1553 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1554 (t : Prop) (h1 : t) : t /\ t.
Proof. exact (conj (@lem1553 t h1) (@lem1553 t h1)). Qed.
Lemma lem1555 (t : Prop) : term13 t.
Proof. exact (fun h0 : t => @lem1554 t h0). Qed.
Lemma lem1556 (t : Prop) : term14 t.
Proof. exact (conj (@lem1552 t) (@lem1555 t)). Qed.
Lemma lem1557 (t : Prop) : (term14 t) = ((t /\ t) = t).
Proof. exact (@lem32 (t /\ t) t). Qed.
Lemma lem1558 (t : Prop) : (t /\ t) = t.
Proof. exact (EQ_MP (@lem1557 t) (@lem1556 t)). Qed.
Lemma lem1559 (t : Prop) : term15 t.
Proof. exact (conj (@lem1548 t) (@lem1558 t)). Qed.
Lemma lem1560 (t : Prop) : term16 t.
Proof. exact (conj (@lem1536 t) (@lem1559 t)). Qed.
Lemma lem1561 (t : Prop) : term17 t.
Proof. exact (conj (@lem1524 t) (@lem1560 t)). Qed.
Lemma lem1562 (t : Prop) : term18 t.
Proof. exact (conj (@lem1514 t) (@lem1561 t)). Qed.
Lemma lem1567 : term19.
Proof. exact (fun t : Prop => @lem1562 t). Qed.
