Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMP_CLAUSES_term_abbrevs.
Require Import NOT_DEF_spec.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm98_spec.
Lemma lem1684 (t : Prop) (h1 : True -> t) : True -> t.
Proof. exact (h1). Qed.
Lemma lem1685 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem1686 (t : Prop) (h1 : True) (h2 : True -> t) : t.
Proof. exact (@lem1684 t h2 (@lem1685 h1)). Qed.
Lemma lem1687 (t : Prop) (h1 : True -> t) : True = t.
Proof. exact (prop_ext (fun h2 : True => @lem1686 t h2 h1) (fun h2 : t => @lem0)). Qed.
Lemma lem1688 (t : Prop) (h1 : True -> t) : t.
Proof. exact (EQ_MP (@lem1687 t h1) (@lem0)). Qed.
Lemma lem1689 (t : Prop) : term0 t.
Proof. exact (fun h0 : True -> t => @lem1688 t h0). Qed.
Lemma lem1690 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1692 (t : Prop) (h1 : t) : True -> t.
Proof. exact (fun h0 : True => @lem1690 t h1). Qed.
Lemma lem1693 (t : Prop) : term1 t.
Proof. exact (fun h0 : t => @lem1692 t h0). Qed.
Lemma lem1694 (t : Prop) : term2 t.
Proof. exact (conj (@lem1689 t) (@lem1693 t)). Qed.
Lemma lem1695 (t : Prop) : (term2 t) = ((True -> t) = t).
Proof. exact (@lem32 (True -> t) t). Qed.
Lemma lem1696 (t : Prop) : (True -> t) = t.
Proof. exact (EQ_MP (@lem1695 t) (@lem1694 t)). Qed.
Lemma lem1698 (t : Prop) : term3 t.
Proof. exact (fun h0 : t -> True => @lem0). Qed.
Lemma lem1699 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem1701 (t : Prop) (h1 : True) : t -> True.
Proof. exact (fun h0 : t => @lem1699 h1). Qed.
Lemma lem1702 (t : Prop) : term4 t.
Proof. exact (fun h0 : True => @lem1701 t h0). Qed.
Lemma lem1703 (t : Prop) : term5 t.
Proof. exact (conj (@lem1698 t) (@lem1702 t)). Qed.
Lemma lem1704 (t : Prop) : (term5 t) = ((t -> True) = True).
Proof. exact (@lem32 (t -> True) True). Qed.
Lemma lem1705 (t : Prop) : (t -> True) = True.
Proof. exact (EQ_MP (@lem1704 t) (@lem1703 t)). Qed.
Lemma lem1707 (t : Prop) : term6 t.
Proof. exact (fun h0 : False -> t => @lem0). Qed.
Lemma lem1709 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1710 (t : Prop) (h1 : False) : t.
Proof. exact (@lem98 t h1). Qed.
Lemma lem1711 (t : Prop) (h1 : False) : False = t.
Proof. exact (prop_ext (fun h2 : False => @lem1710 t h1) (fun h2 : t => @lem1709 h1)). Qed.
Lemma lem1712 (t : Prop) (h1 : False) : t.
Proof. exact (EQ_MP (@lem1711 t h1) (@lem1709 h1)). Qed.
Lemma lem1713 (t : Prop) : False -> t.
Proof. exact (fun h0 : False => @lem1712 t h0). Qed.
Lemma lem1714 (t : Prop) : term7 t.
Proof. exact (fun h0 : True => @lem1713 t). Qed.
Lemma lem1715 (t : Prop) : term8 t.
Proof. exact (conj (@lem1707 t) (@lem1714 t)). Qed.
Lemma lem1716 (t : Prop) : (term8 t) = ((False -> t) = True).
Proof. exact (@lem32 (False -> t) True). Qed.
Lemma lem1717 (t : Prop) : (False -> t) = True.
Proof. exact (EQ_MP (@lem1716 t) (@lem1715 t)). Qed.
Lemma lem1719 (t : Prop) : term9 t.
Proof. exact (fun h0 : t -> t => @lem0). Qed.
Lemma lem1721 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1722 (t : Prop) : t -> t.
Proof. exact (fun h0 : t => @lem1721 t h0). Qed.
Lemma lem1723 (t : Prop) : term10 t.
Proof. exact (fun h0 : True => @lem1722 t). Qed.
Lemma lem1724 (t : Prop) : term11 t.
Proof. exact (conj (@lem1719 t) (@lem1723 t)). Qed.
Lemma lem1725 (t : Prop) : (term11 t) = ((t -> t) = True).
Proof. exact (@lem32 (t -> t) True). Qed.
Lemma lem1726 (t : Prop) : (t -> t) = True.
Proof. exact (EQ_MP (@lem1725 t) (@lem1724 t)). Qed.
Lemma lem1727 (t : Prop) (h1 : t -> False) : t -> False.
Proof. exact (h1). Qed.
Lemma lem1728 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1729 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1730 (t : Prop) (h1 : t) (h2 : t -> False) : False.
Proof. exact (@lem1727 t h2 (@lem1729 t h1)). Qed.
Lemma lem1731 (t : Prop) (h1 : t) (h2 : t -> False) : t = False.
Proof. exact (prop_ext (fun h3 : t => @lem1730 t h1 h2) (fun h3 : False => @lem1728 t h1)). Qed.
Lemma lem1732 (t : Prop) (h1 : t) (h2 : t -> False) : False.
Proof. exact (EQ_MP (@lem1731 t h1 h2) (@lem1728 t h1)). Qed.
Lemma lem1733 (t : Prop) (h1 : t -> False) : t -> False.
Proof. exact (fun h0 : t => @lem1732 t h0 h1). Qed.
Lemma lem1734 (t : Prop) : (t -> False) = (~ t).
Proof. exact (@lem69 t). Qed.
Lemma lem1735 (t : Prop) (h1 : t -> False) : ~ t.
Proof. exact (EQ_MP (@lem1734 t) (@lem1733 t h1)). Qed.
Lemma lem1736 (t : Prop) : term12 t.
Proof. exact (fun h0 : t -> False => @lem1735 t h0). Qed.
Lemma lem1737 (t : Prop) (h1 : ~ t) : ~ t.
Proof. exact (h1). Qed.
Lemma lem1738 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1739 (t : Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1740 (t : Prop) : (~ t) = (term13 t).
Proof. exact (MK_COMB (@lem56) (@lem1739 t)). Qed.
Lemma lem1741 (t : Prop) : (term13 t) = (t -> False).
Proof. exact (eq_refl (term13 t)). Qed.
Lemma lem1742 (t : Prop) : (term14 t) = (term14 t).
Proof. exact (eq_refl (term14 t)). Qed.
Lemma lem1743 (t : Prop) : ((~ t) = (term13 t)) = ((~ t) = (t -> False)).
Proof. exact (MK_COMB (@lem1742 t) (@lem1741 t)). Qed.
Lemma lem1744 (t : Prop) : (~ t) = (t -> False).
Proof. exact (EQ_MP (@lem1743 t) (@lem1740 t)). Qed.
Lemma lem1745 (t : Prop) (h1 : ~ t) : t -> False.
Proof. exact (EQ_MP (@lem1744 t) (@lem1737 t h1)). Qed.
Lemma lem1746 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1747 (t : Prop) (h1 : t) (h2 : ~ t) : False.
Proof. exact (@lem1745 t h2 (@lem1746 t h1)). Qed.
Lemma lem1748 (t : Prop) (h1 : t) (h2 : ~ t) : t = False.
Proof. exact (prop_ext (fun h3 : t => @lem1747 t h1 h2) (fun h3 : False => @lem1738 t h1)). Qed.
Lemma lem1749 (t : Prop) (h1 : t) (h2 : ~ t) : False.
Proof. exact (EQ_MP (@lem1748 t h1 h2) (@lem1738 t h1)). Qed.
Lemma lem1750 (t : Prop) (h1 : ~ t) : t -> False.
Proof. exact (fun h0 : t => @lem1749 t h0 h1). Qed.
Lemma lem1751 (t : Prop) : term15 t.
Proof. exact (fun h0 : ~ t => @lem1750 t h0). Qed.
Lemma lem1752 (t : Prop) : term16 t.
Proof. exact (conj (@lem1736 t) (@lem1751 t)). Qed.
Lemma lem1753 (t : Prop) : (term16 t) = ((t -> False) = (~ t)).
Proof. exact (@lem32 (t -> False) (~ t)). Qed.
Lemma lem1754 (t : Prop) : (t -> False) = (~ t).
Proof. exact (EQ_MP (@lem1753 t) (@lem1752 t)). Qed.
Lemma lem1755 (t : Prop) : term17 t.
Proof. exact (conj (@lem1726 t) (@lem1754 t)). Qed.
Lemma lem1756 (t : Prop) : term18 t.
Proof. exact (conj (@lem1717 t) (@lem1755 t)). Qed.
Lemma lem1757 (t : Prop) : term19 t.
Proof. exact (conj (@lem1705 t) (@lem1756 t)). Qed.
Lemma lem1758 (t : Prop) : term20 t.
Proof. exact (conj (@lem1696 t) (@lem1757 t)). Qed.
Lemma lem1763 : term21.
Proof. exact (fun t : Prop => @lem1758 t). Qed.
