Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import OR_CLAUSES_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm98_spec.
Lemma lem1569 (t : Prop) : term0 t.
Proof. exact (fun h0 : True \/ t => @lem0). Qed.
Lemma lem1570 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem1571 (t : Prop) (h1 : True) : True \/ t.
Proof. exact (or_intro1 (@lem1570 h1) t). Qed.
Lemma lem1572 (t : Prop) : term1 t.
Proof. exact (fun h0 : True => @lem1571 t h0). Qed.
Lemma lem1573 (t : Prop) : term2 t.
Proof. exact (conj (@lem1569 t) (@lem1572 t)). Qed.
Lemma lem1574 (t : Prop) : (term2 t) = ((True \/ t) = True).
Proof. exact (@lem32 (True \/ t) True). Qed.
Lemma lem1575 (t : Prop) : (True \/ t) = True.
Proof. exact (EQ_MP (@lem1574 t) (@lem1573 t)). Qed.
Lemma lem1577 (t : Prop) : term3 t.
Proof. exact (fun h0 : t \/ True => @lem0). Qed.
Lemma lem1578 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem1579 (t : Prop) (h1 : True) : t \/ True.
Proof. exact (or_intro2 t (@lem1578 h1)). Qed.
Lemma lem1580 (t : Prop) : term4 t.
Proof. exact (fun h0 : True => @lem1579 t h0). Qed.
Lemma lem1581 (t : Prop) : term5 t.
Proof. exact (conj (@lem1577 t) (@lem1580 t)). Qed.
Lemma lem1582 (t : Prop) : (term5 t) = ((t \/ True) = True).
Proof. exact (@lem32 (t \/ True) True). Qed.
Lemma lem1583 (t : Prop) : (t \/ True) = True.
Proof. exact (EQ_MP (@lem1582 t) (@lem1581 t)). Qed.
Lemma lem1584 (t : Prop) (h1 : False \/ t) : False \/ t.
Proof. exact (h1). Qed.
Lemma lem1585 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1586 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1587 (t : Prop) (h1 : False) : t.
Proof. exact (@lem98 t h1). Qed.
Lemma lem1588 (t : Prop) (h1 : False) : False = t.
Proof. exact (prop_ext (fun h2 : False => @lem1587 t h1) (fun h2 : t => @lem1585 h1)). Qed.
Lemma lem1589 (t : Prop) (h1 : False) : t.
Proof. exact (EQ_MP (@lem1588 t h1) (@lem1585 h1)). Qed.
Lemma lem1590 (t : Prop) (h1 : False \/ t) : t.
Proof. exact (or_elim (@lem1584 t h1) (fun h0 : False => @lem1589 t h0) (fun h0 : t => @lem1586 t h0)). Qed.
Lemma lem1591 (t : Prop) : term6 t.
Proof. exact (fun h0 : False \/ t => @lem1590 t h0). Qed.
Lemma lem1592 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1593 (t : Prop) (h1 : t) : False \/ t.
Proof. exact (or_intro2 False (@lem1592 t h1)). Qed.
Lemma lem1594 (t : Prop) : term7 t.
Proof. exact (fun h0 : t => @lem1593 t h0). Qed.
Lemma lem1595 (t : Prop) : term8 t.
Proof. exact (conj (@lem1591 t) (@lem1594 t)). Qed.
Lemma lem1596 (t : Prop) : (term8 t) = ((False \/ t) = t).
Proof. exact (@lem32 (False \/ t) t). Qed.
Lemma lem1597 (t : Prop) : (False \/ t) = t.
Proof. exact (EQ_MP (@lem1596 t) (@lem1595 t)). Qed.
Lemma lem1598 (t : Prop) (h1 : t \/ False) : t \/ False.
Proof. exact (h1). Qed.
Lemma lem1599 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1600 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1601 (t : Prop) (h1 : False) : t.
Proof. exact (@lem98 t h1). Qed.
Lemma lem1602 (t : Prop) (h1 : False) : False = t.
Proof. exact (prop_ext (fun h2 : False => @lem1601 t h1) (fun h2 : t => @lem1600 h1)). Qed.
Lemma lem1603 (t : Prop) (h1 : False) : t.
Proof. exact (EQ_MP (@lem1602 t h1) (@lem1600 h1)). Qed.
Lemma lem1604 (t : Prop) (h1 : t \/ False) : t.
Proof. exact (or_elim (@lem1598 t h1) (fun h0 : t => @lem1599 t h0) (fun h0 : False => @lem1603 t h0)). Qed.
Lemma lem1605 (t : Prop) : term9 t.
Proof. exact (fun h0 : t \/ False => @lem1604 t h0). Qed.
Lemma lem1606 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1607 (t : Prop) (h1 : t) : t \/ False.
Proof. exact (or_intro1 (@lem1606 t h1) False). Qed.
Lemma lem1608 (t : Prop) : term10 t.
Proof. exact (fun h0 : t => @lem1607 t h0). Qed.
Lemma lem1609 (t : Prop) : term11 t.
Proof. exact (conj (@lem1605 t) (@lem1608 t)). Qed.
Lemma lem1610 (t : Prop) : (term11 t) = ((t \/ False) = t).
Proof. exact (@lem32 (t \/ False) t). Qed.
Lemma lem1611 (t : Prop) : (t \/ False) = t.
Proof. exact (EQ_MP (@lem1610 t) (@lem1609 t)). Qed.
Lemma lem1612 (t : Prop) (h1 : t \/ t) : t \/ t.
Proof. exact (h1). Qed.
Lemma lem1613 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1614 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1615 (t : Prop) (h1 : t \/ t) : t.
Proof. exact (or_elim (@lem1612 t h1) (fun h0 : t => @lem1613 t h0) (fun h0 : t => @lem1614 t h0)). Qed.
Lemma lem1616 (t : Prop) : term12 t.
Proof. exact (fun h0 : t \/ t => @lem1615 t h0). Qed.
Lemma lem1617 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1618 (t : Prop) (h1 : t) : t \/ t.
Proof. exact (or_intro1 (@lem1617 t h1) t). Qed.
Lemma lem1619 (t : Prop) : term13 t.
Proof. exact (fun h0 : t => @lem1618 t h0). Qed.
Lemma lem1620 (t : Prop) : term14 t.
Proof. exact (conj (@lem1616 t) (@lem1619 t)). Qed.
Lemma lem1621 (t : Prop) : (term14 t) = ((t \/ t) = t).
Proof. exact (@lem32 (t \/ t) t). Qed.
Lemma lem1622 (t : Prop) : (t \/ t) = t.
Proof. exact (EQ_MP (@lem1621 t) (@lem1620 t)). Qed.
Lemma lem1623 (t : Prop) : term15 t.
Proof. exact (conj (@lem1611 t) (@lem1622 t)). Qed.
Lemma lem1624 (t : Prop) : term16 t.
Proof. exact (conj (@lem1597 t) (@lem1623 t)). Qed.
Lemma lem1625 (t : Prop) : term17 t.
Proof. exact (conj (@lem1583 t) (@lem1624 t)). Qed.
Lemma lem1626 (t : Prop) : term18 t.
Proof. exact (conj (@lem1575 t) (@lem1625 t)). Qed.
Lemma lem1631 : term19.
Proof. exact (fun t : Prop => @lem1626 t). Qed.
