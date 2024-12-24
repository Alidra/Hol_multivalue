Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONSTR_IND_term_abbrevs.
Require Import BOTTOM_spec.
Require Import CONSTR_spec.
Require Import ETA_AX_spec.
Require Import FORALL_AND_THM_spec.
Require Import ZRECSPACE_INDUCT_spec.
Require Import ZRECSPACE_RULES_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1060647 (a : Prop) (b : Prop) (h1 : term0 a b) : term0 a b.
Proof. exact (h1). Qed.
Lemma lem1060648 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem1060649 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem1060650 (a : Prop) (b : Prop) (h1 : a) (h2 : term0 a b) : a /\ b.
Proof. exact (@lem1060647 a b h2 (@lem1060649 a h1)). Qed.
Lemma lem1060651 (a : Prop) (b : Prop) (h1 : a) (h2 : term0 a b) : b.
Proof. exact (proj2 (@lem1060650 a b h1 h2)). Qed.
Lemma lem1060652 (a : Prop) (b : Prop) (h1 : a) (h2 : term0 a b) : a.
Proof. exact (proj1 (@lem1060650 a b h1 h2)). Qed.
Lemma lem1060653 (a : Prop) (b : Prop) (h1 : a) (h2 : term0 a b) : a = b.
Proof. exact (prop_ext (fun h3 : a => @lem1060651 a b h1 h2) (fun h3 : b => @lem1060652 a b h1 h2)). Qed.
Lemma lem1060654 (a : Prop) (b : Prop) (h1 : a) (h2 : term0 a b) : b.
Proof. exact (EQ_MP (@lem1060653 a b h1 h2) (@lem1060652 a b h1 h2)). Qed.
Lemma lem1060655 (a : Prop) (b : Prop) (h1 : a) (h2 : term0 a b) : a = b.
Proof. exact (prop_ext (fun h3 : a => @lem1060654 a b h1 h2) (fun h3 : b => @lem1060648 a h1)). Qed.
Lemma lem1060656 (a : Prop) (b : Prop) (h1 : a) (h2 : term0 a b) : b.
Proof. exact (EQ_MP (@lem1060655 a b h1 h2) (@lem1060648 a h1)). Qed.
Lemma lem1060657 (a : Prop) (b : Prop) (h1 : term0 a b) : a -> b.
Proof. exact (fun h0 : a => @lem1060656 a b h0 h1). Qed.
Lemma lem1060658 (a : Prop) (b : Prop) : term1 a b.
Proof. exact (fun h0 : term0 a b => @lem1060657 a b h0). Qed.
Lemma lem1060659 (a : Prop) (b : Prop) (h1 : a -> b) : a -> b.
Proof. exact (h1). Qed.
Lemma lem1060660 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem1060661 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem1060662 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : b.
Proof. exact (@lem1060659 a b h2 (@lem1060661 a h1)). Qed.
Lemma lem1060663 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : a = b.
Proof. exact (prop_ext (fun h3 : a => @lem1060662 a b h1 h2) (fun h3 : b => @lem1060660 a h1)). Qed.
Lemma lem1060664 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : b.
Proof. exact (EQ_MP (@lem1060663 a b h1 h2) (@lem1060660 a h1)). Qed.
Lemma lem1060665 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : a /\ b.
Proof. exact (conj (@lem1060660 a h1) (@lem1060664 a b h1 h2)). Qed.
Lemma lem1060666 (a : Prop) (b : Prop) (h1 : a -> b) : term0 a b.
Proof. exact (fun h0 : a => @lem1060665 a b h0 h1). Qed.
Lemma lem1060667 (a : Prop) (b : Prop) : term2 a b.
Proof. exact (fun h0 : a -> b => @lem1060666 a b h0). Qed.
Lemma lem1060668 (a : Prop) (b : Prop) : term3 a b.
Proof. exact (conj (@lem1060658 a b) (@lem1060667 a b)). Qed.
Lemma lem1060669 (a : Prop) (b : Prop) : (term3 a b) = ((term0 a b) = (a -> b)).
Proof. exact (@lem32 (term0 a b) (a -> b)). Qed.
Lemma lem1060671 {A : Type'} (c : nat) : term4 A c.
Proof. exact (@lem1059607 A c). Qed.
Lemma lem1060672 {A : Type'} (c : nat) : (term4 A c) = (term5 A c).
Proof. exact (eq_refl (term4 A c)). Qed.
Lemma lem1060673 {A : Type'} (c : nat) : term5 A c.
Proof. exact (EQ_MP (@lem1060672 A c) (@lem1060671 A c)). Qed.
Lemma lem1060674 {A : Type'} (c : nat) (i : A) : term6 A c i.
Proof. exact (@lem1060673 A c i). Qed.
Lemma lem1060675 {A : Type'} (c : nat) (i : A) : (term6 A c i) = (term7 A c i).
Proof. exact (eq_refl (term6 A c i)). Qed.
Lemma lem1060676 {A : Type'} (c : nat) (i : A) : term7 A c i.
Proof. exact (EQ_MP (@lem1060675 A c i) (@lem1060674 A c i)). Qed.
Lemma lem1060677 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term8 A c i r.
Proof. exact (@lem1060676 A c i r). Qed.
Lemma lem1060678 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term8 A c i r) = ((@CONSTR A c i r) = (term9 A c i r)).
Proof. exact (eq_refl (term8 A c i r)). Qed.
Lemma lem1060680 {A : Type'} : term10 A.
Proof. exact (proj2 (@lem1058926 A)). Qed.
Lemma lem1060681 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem1060682 {A : Type'} (c : nat) (h1 : term10 A) : term11 A c.
Proof. exact (@lem1060681 A h1 c). Qed.
Lemma lem1060683 {A : Type'} (c : nat) : (term11 A c) = (term12 A c).
Proof. exact (eq_refl (term11 A c)). Qed.
Lemma lem1060684 {A : Type'} (c : nat) (h1 : term10 A) : term12 A c.
Proof. exact (EQ_MP (@lem1060683 A c) (@lem1060682 A c h1)). Qed.
Lemma lem1060685 {A : Type'} (c : nat) (i : A) (h1 : term10 A) : term13 A c i.
Proof. exact (@lem1060684 A c h1 i). Qed.
Lemma lem1060686 {A : Type'} (c : nat) (i : A) : (term13 A c i) = (term14 A c i).
Proof. exact (eq_refl (term13 A c i)). Qed.
Lemma lem1060687 {A : Type'} (c : nat) (i : A) (h1 : term10 A) : term14 A c i.
Proof. exact (EQ_MP (@lem1060686 A c i) (@lem1060685 A c i h1)). Qed.
Lemma lem1060688 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term10 A) : term15 A c i r.
Proof. exact (@lem1060687 A c i h1 r). Qed.
Lemma lem1060689 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term15 A c i r) = (term16 A c i r).
Proof. exact (eq_refl (term15 A c i r)). Qed.
Lemma lem1060690 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term10 A) : term16 A c i r.
Proof. exact (EQ_MP (@lem1060689 A c i r) (@lem1060688 A c i r h1)). Qed.
Lemma lem1060691 {A : Type'} (r : type1600 A) (h1 : term17 A r) : term17 A r.
Proof. exact (h1). Qed.
Lemma lem1060692 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term10 A) (h2 : term17 A r) : term18 A c i r.
Proof. exact (@lem1060690 A c i r h1 (@lem1060691 A r h2)). Qed.
Lemma lem1060693 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term17 A r) : term19 A c i r.
Proof. exact (fun h0 : term10 A => @lem1060692 A c i r h0 h1). Qed.
Lemma lem1060694 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem1060695 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term10 A) (h2 : term17 A r) : term18 A c i r.
Proof. exact (@lem1060693 A c i r h2 (@lem1060694 A h1)). Qed.
Lemma lem1060696 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term10 A) : term16 A c i r.
Proof. exact (fun h0 : term17 A r => @lem1060695 A c i r h1 h0). Qed.
Lemma lem1060697 {A : Type'} (c : nat) (i : A) (h1 : term10 A) : term14 A c i.
Proof. exact (fun r : type1600 A => @lem1060696 A c i r h1). Qed.
Lemma lem1060698 {A : Type'} (c : nat) (h1 : term10 A) : term12 A c.
Proof. exact (fun i : A => @lem1060697 A c i h1). Qed.
Lemma lem1060699 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (fun c : nat => @lem1060698 A c h1). Qed.
Lemma lem1060700 {A : Type'} : term20 A.
Proof. exact (fun h0 : term10 A => @lem1060699 A h0). Qed.
Lemma lem1060701 {A : Type'} : term10 A.
Proof. exact (@lem1060700 A (@lem1060680 A)). Qed.
Lemma lem1060702 {A : Type'} (c : nat) : term11 A c.
Proof. exact (@lem1060701 A c). Qed.
Lemma lem1060703 {A : Type'} (c : nat) : (term11 A c) = (term12 A c).
Proof. exact (eq_refl (term11 A c)). Qed.
Lemma lem1060704 {A : Type'} (c : nat) : term12 A c.
Proof. exact (EQ_MP (@lem1060703 A c) (@lem1060702 A c)). Qed.
Lemma lem1060705 {A : Type'} (c : nat) (i : A) : term13 A c i.
Proof. exact (@lem1060704 A c i). Qed.
Lemma lem1060706 {A : Type'} (c : nat) (i : A) : (term13 A c i) = (term14 A c i).
Proof. exact (eq_refl (term13 A c i)). Qed.
Lemma lem1060707 {A : Type'} (c : nat) (i : A) : term14 A c i.
Proof. exact (EQ_MP (@lem1060706 A c i) (@lem1060705 A c i)). Qed.
Lemma lem1060708 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term15 A c i r.
Proof. exact (@lem1060707 A c i r). Qed.
Lemma lem1060709 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term15 A c i r) = (term16 A c i r).
Proof. exact (eq_refl (term15 A c i r)). Qed.
Lemma lem1060711 {A : Type'} (P : A -> Prop) : term21 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem1060712 {A : Type'} (P : A -> Prop) : (term21 A P) = (term22 A P).
Proof. exact (eq_refl (term21 A P)). Qed.
Lemma lem1060713 {A : Type'} (P : A -> Prop) : term22 A P.
Proof. exact (EQ_MP (@lem1060712 A P) (@lem1060711 A P)). Qed.
Lemma lem1060714 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term23 A P Q.
Proof. exact (@lem1060713 A P Q). Qed.
Lemma lem1060715 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term23 A P Q) = ((term24 A P Q) = (term25 A P Q)).
Proof. exact (eq_refl (term23 A P Q)). Qed.
Lemma lem1060717 {A : Type'} (h1 : (@BOTTOM A) = (@_mk_rec A (@ZBOT A))) : (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
Proof. exact (h1). Qed.
Lemma lem1060718 {A : Type'} (h1 : (@BOTTOM A) = (@_mk_rec A (@ZBOT A))) : (@_mk_rec A (@ZBOT A)) = (@BOTTOM A).
Proof. exact (SYM (@lem1060717 A h1)). Qed.
Lemma lem1060719 {A : Type'} (h1 : (@_mk_rec A (@ZBOT A)) = (@BOTTOM A)) : (@_mk_rec A (@ZBOT A)) = (@BOTTOM A).
Proof. exact (h1). Qed.
Lemma lem1060720 {A : Type'} (h1 : (@_mk_rec A (@ZBOT A)) = (@BOTTOM A)) : (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
Proof. exact (SYM (@lem1060719 A h1)). Qed.
Lemma lem1060721 {A : Type'} : ((@BOTTOM A) = (@_mk_rec A (@ZBOT A))) = ((@_mk_rec A (@ZBOT A)) = (@BOTTOM A)).
Proof. exact (prop_ext (fun h1 : (@BOTTOM A) = (@_mk_rec A (@ZBOT A)) => @lem1060718 A h1) (fun h1 : (@_mk_rec A (@ZBOT A)) = (@BOTTOM A) => @lem1060720 A h1)). Qed.
Lemma lem1060723 {A : Type'} (P : type1338 A) : term26 A P.
Proof. exact (@lem1058928 A (term27 A P)). Qed.
Lemma lem1060724 {A : Type'} (P : type1338 A) : (term26 A P) = (term28 A P).
Proof. exact (eq_refl (term26 A P)). Qed.
Lemma lem1060725 {A : Type'} (P : type1338 A) : term28 A P.
Proof. exact (EQ_MP (@lem1060724 A P) (@lem1060723 A P)). Qed.
Lemma lem1060726 {A : Type'} (P : type1338 A) (h1 : term29 A P) : term29 A P.
Proof. exact (h1). Qed.
Lemma lem1060727 {A : Type'} (P : type1338 A) (h1 : term30 A P) : term30 A P.
Proof. exact (h1). Qed.
Lemma lem1060728 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : P (@BOTTOM A).
Proof. exact (h1). Qed.
Lemma lem1060729 {A : Type'} (P : type1338 A) : (term31 A P) = (term32 A P).
Proof. exact (eq_refl (term31 A P)). Qed.
Lemma lem1060730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1060731 {A : Type'} (P : type1338 A) : (term33 A P) = (term34 A P).
Proof. exact (MK_COMB (@lem1060730) (@lem1060729 A P)). Qed.
Lemma lem1060732 {A : Type'} (P : type1338 A) (r : type1600 A) (n : nat) : (term35 A P r n) = (term36 A P r n).
Proof. exact (eq_refl (term35 A P r n)). Qed.
Lemma lem1060733 {A : Type'} (P : type1338 A) (r : type1600 A) : (term37 A P r) = (term38 A P r).
Proof. exact (fun_ext (fun n : nat => @lem1060732 A P r n)). Qed.
Lemma lem1060734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060735 {A : Type'} (P : type1338 A) (r : type1600 A) : (term39 A P r) = (term40 A P r).
Proof. exact (MK_COMB (@lem1060734) (@lem1060733 A P r)). Qed.
Lemma lem1060736 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060737 {A : Type'} (P : type1338 A) (r : type1600 A) : (term41 A P r) = (term42 A P r).
Proof. exact (MK_COMB (@lem1060736) (@lem1060735 A P r)). Qed.
Lemma lem1060738 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term43 A P c i r) = (term44 A P c i r).
Proof. exact (eq_refl (term43 A P c i r)). Qed.
Lemma lem1060739 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term45 A P c i r) = (term46 A P c i r).
Proof. exact (MK_COMB (@lem1060737 A P r) (@lem1060738 A P c i r)). Qed.
Lemma lem1060740 {A : Type'} (P : type1338 A) (c : nat) (i : A) : (term47 A P c i) = (term48 A P c i).
Proof. exact (fun_ext (fun r : type1600 A => @lem1060739 A P c i r)). Qed.
Lemma lem1060741 {A : Type'} : (@all (nat -> nat -> A -> Prop)) = (@all (nat -> nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> A -> Prop))). Qed.
Lemma lem1060742 {A : Type'} (P : type1338 A) (c : nat) (i : A) : (term49 A P c i) = (term50 A P c i).
Proof. exact (MK_COMB (@lem1060741 A) (@lem1060740 A P c i)). Qed.
Lemma lem1060743 {A : Type'} (P : type1338 A) (c : nat) : (term51 A P c) = (term52 A P c).
Proof. exact (fun_ext (fun i : A => @lem1060742 A P c i)). Qed.
Lemma lem1060744 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1060745 {A : Type'} (P : type1338 A) (c : nat) : (term53 A P c) = (term54 A P c).
Proof. exact (MK_COMB (@lem1060744 A) (@lem1060743 A P c)). Qed.
Lemma lem1060746 {A : Type'} (P : type1338 A) : (term55 A P) = (term56 A P).
Proof. exact (fun_ext (fun c : nat => @lem1060745 A P c)). Qed.
Lemma lem1060747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060748 {A : Type'} (P : type1338 A) : (term57 A P) = (term58 A P).
Proof. exact (MK_COMB (@lem1060747) (@lem1060746 A P)). Qed.
Lemma lem1060749 {A : Type'} (P : type1338 A) : (term59 A P) = (term60 A P).
Proof. exact (MK_COMB (@lem1060731 A P) (@lem1060748 A P)). Qed.
Lemma lem1060750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060751 {A : Type'} (P : type1338 A) : (term61 A P) = (term62 A P).
Proof. exact (MK_COMB (@lem1060750) (@lem1060749 A P)). Qed.
Lemma lem1060752 {A : Type'} (P : type1338 A) (a : type1597 A) : (term63 A P a) = (term64 A P a).
Proof. exact (eq_refl (term63 A P a)). Qed.
Lemma lem1060753 {A : Type'} (a : type1597 A) : (term65 A a) = (term65 A a).
Proof. exact (eq_refl (term65 A a)). Qed.
Lemma lem1060754 {A : Type'} (P : type1338 A) (a : type1597 A) : (term66 A P a) = (term67 A P a).
Proof. exact (MK_COMB (@lem1060753 A a) (@lem1060752 A P a)). Qed.
Lemma lem1060755 {A : Type'} (P : type1338 A) : (term68 A P) = (term69 A P).
Proof. exact (fun_ext (fun a : type1597 A => @lem1060754 A P a)). Qed.
Lemma lem1060756 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem1060757 {A : Type'} (P : type1338 A) : (term70 A P) = (term71 A P).
Proof. exact (MK_COMB (@lem1060756 A) (@lem1060755 A P)). Qed.
Lemma lem1060758 {A : Type'} (P : type1338 A) : (term28 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem1060751 A P) (@lem1060757 A P)). Qed.
Lemma lem1060759 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060760 {A : Type'} (P : type1338 A) : (term73 A P) = (term74 A P).
Proof. exact (MK_COMB (@lem1060759) (@lem1060758 A P)). Qed.
Lemma lem1060761 {A : Type'} (P : type1338 A) (x : recspace A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1060762 {A : Type'} (P : type1338 A) (x : recspace A) : (term75 A P x) = (term76 A P x).
Proof. exact (MK_COMB (@lem1060760 A P) (@lem1060761 A P x)). Qed.
Lemma lem1060763 {A : Type'} (P : type1338 A) (x : recspace A) : (term76 A P x) = (term75 A P x).
Proof. exact (SYM (@lem1060762 A P x)). Qed.
Lemma lem1060776 {A : Type'} : @ZRECSPACE A (@ZBOT A).
Proof. exact (proj1 (@lem1058926 A)). Qed.
Lemma lem1060777 {A : Type'} : (@ZRECSPACE A (@ZBOT A)) = ((@ZRECSPACE A (@ZBOT A)) = True).
Proof. exact (@lem7 (@ZRECSPACE A (@ZBOT A))). Qed.
Lemma lem1060779 {A : Type'} (P : type1338 A) : (P (@BOTTOM A)) = ((P (@BOTTOM A)) = True).
Proof. exact (@lem7 (P (@BOTTOM A))). Qed.
Lemma lem1060801 {A : Type'} : (@ZRECSPACE A (@ZBOT A)) = True.
Proof. exact (EQ_MP (@lem1060777 A) (@lem1060776 A)). Qed.
Lemma lem1060802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1060803 {A : Type'} : (term77 A) = (and True).
Proof. exact (MK_COMB (@lem1060802) (@lem1060801 A)). Qed.
Lemma lem1060805 {A : Type'} : (@_mk_rec A (@ZBOT A)) = (@BOTTOM A).
Proof. exact (EQ_MP (@lem1060721 A) (@lem1059235 A)). Qed.
Lemma lem1060806 {A : Type'} (P : type1338 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1060807 {A : Type'} (P : type1338 A) : (term78 A P) = (P (@BOTTOM A)).
Proof. exact (MK_COMB (@lem1060806 A P) (@lem1060805 A)). Qed.
Lemma lem1060809 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (P (@BOTTOM A)) = True.
Proof. exact (EQ_MP (@lem1060779 A P) (@lem1060728 A P h1)). Qed.
Lemma lem1060810 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (term78 A P) = True.
Proof. exact (TRANS (@lem1060807 A P) (@lem1060809 A P h1)). Qed.
Lemma lem1060811 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (term32 A P) = (True /\ True).
Proof. exact (MK_COMB (@lem1060803 A) (@lem1060810 A P h1)). Qed.
Lemma lem1060813 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1060814 : (True /\ True) = True.
Proof. exact (@lem1060813 True). Qed.
Lemma lem1060815 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (term32 A P) = True.
Proof. exact (TRANS (@lem1060811 A P h1) (@lem1060814)). Qed.
Lemma lem1060816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1060817 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (term34 A P) = (and True).
Proof. exact (MK_COMB (@lem1060816) (@lem1060815 A P h1)). Qed.
Lemma lem1060840 {A : Type'} (P : type1338 A) : (term58 A P) = (term58 A P).
Proof. exact (eq_refl (term58 A P)). Qed.
Lemma lem1060841 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (term60 A P) = (term79 A P).
Proof. exact (MK_COMB (@lem1060817 A P h1) (@lem1060840 A P)). Qed.
Lemma lem1060843 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1060844 {A : Type'} (P : type1338 A) : (term79 A P) = (term58 A P).
Proof. exact (@lem1060843 (term58 A P)). Qed.
Lemma lem1060867 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (term60 A P) = (term58 A P).
Proof. exact (TRANS (@lem1060841 A P h1) (@lem1060844 A P)). Qed.
Lemma lem1060868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060869 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (term62 A P) = (term80 A P).
Proof. exact (MK_COMB (@lem1060868) (@lem1060867 A P h1)). Qed.
Lemma lem1060878 {A : Type'} (P : type1338 A) : (term71 A P) = (term71 A P).
Proof. exact (eq_refl (term71 A P)). Qed.
Lemma lem1060879 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (term72 A P) = (term81 A P).
Proof. exact (MK_COMB (@lem1060869 A P h1) (@lem1060878 A P)). Qed.
Lemma lem1060882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060883 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) : (term74 A P) = (term82 A P).
Proof. exact (MK_COMB (@lem1060882) (@lem1060879 A P h1)). Qed.
Lemma lem1060884 {A : Type'} (P : type1338 A) (x : recspace A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1060885 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : P (@BOTTOM A)) : (term76 A P x) = (term83 A P x).
Proof. exact (MK_COMB (@lem1060883 A P h1) (@lem1060884 A P x)). Qed.
Lemma lem1060888 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : P (@BOTTOM A)) : (term83 A P x) = (term76 A P x).
Proof. exact (SYM (@lem1060885 A x P h1)). Qed.
Lemma lem1060889 {A : Type'} (P : type1338 A) (h1 : term58 A P) : term58 A P.
Proof. exact (h1). Qed.
Lemma lem1060893 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term24 A P Q) = (term25 A P Q).
Proof. exact (EQ_MP (@lem1060715 A P Q) (@lem1060714 A P Q)). Qed.
Lemma lem1060894 (P : nat -> Prop) (Q : nat -> Prop) : (term84 P Q) = (term85 P Q).
Proof. exact (@lem1060893 nat P Q). Qed.
Lemma lem1060895 {A : Type'} (P : type1338 A) (r : type1600 A) : (term86 A P r) = (term87 A P r).
Proof. exact (@lem1060894 (term88 A r) (term89 A P r)). Qed.
Lemma lem1060896 {A : Type'} (r : type1600 A) (n : nat) : (term90 A r n) = (term91 A r n).
Proof. exact (eq_refl (term90 A r n)). Qed.
Lemma lem1060897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1060898 {A : Type'} (r : type1600 A) (n : nat) : (term92 A r n) = (term93 A r n).
Proof. exact (MK_COMB (@lem1060897) (@lem1060896 A r n)). Qed.
Lemma lem1060899 {A : Type'} (P : type1338 A) (r : type1600 A) (n : nat) : (term94 A P r n) = (term95 A P r n).
Proof. exact (eq_refl (term94 A P r n)). Qed.
Lemma lem1060900 {A : Type'} (P : type1338 A) (r : type1600 A) (n : nat) : (term96 A P r n) = (term36 A P r n).
Proof. exact (MK_COMB (@lem1060898 A r n) (@lem1060899 A P r n)). Qed.
Lemma lem1060901 {A : Type'} (P : type1338 A) (r : type1600 A) : (term97 A P r) = (term38 A P r).
Proof. exact (fun_ext (fun n : nat => @lem1060900 A P r n)). Qed.
Lemma lem1060902 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060903 {A : Type'} (P : type1338 A) (r : type1600 A) : (term86 A P r) = (term40 A P r).
Proof. exact (MK_COMB (@lem1060902) (@lem1060901 A P r)). Qed.
Lemma lem1060904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1060905 {A : Type'} (P : type1338 A) (r : type1600 A) : (term98 A P r) = (term99 A P r).
Proof. exact (MK_COMB (@lem1060904) (@lem1060903 A P r)). Qed.
Lemma lem1060906 {A : Type'} (r : type1600 A) (n : nat) : (term90 A r n) = (term91 A r n).
Proof. exact (eq_refl (term90 A r n)). Qed.
Lemma lem1060907 {A : Type'} (r : type1600 A) : (term100 A r) = (term88 A r).
Proof. exact (fun_ext (fun n : nat => @lem1060906 A r n)). Qed.
Lemma lem1060908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060909 {A : Type'} (r : type1600 A) : (term101 A r) = (term17 A r).
Proof. exact (MK_COMB (@lem1060908) (@lem1060907 A r)). Qed.
Lemma lem1060910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1060911 {A : Type'} (r : type1600 A) : (term102 A r) = (term103 A r).
Proof. exact (MK_COMB (@lem1060910) (@lem1060909 A r)). Qed.
Lemma lem1060912 {A : Type'} (P : type1338 A) (r : type1600 A) (n : nat) : (term94 A P r n) = (term95 A P r n).
Proof. exact (eq_refl (term94 A P r n)). Qed.
Lemma lem1060913 {A : Type'} (P : type1338 A) (r : type1600 A) : (term104 A P r) = (term89 A P r).
Proof. exact (fun_ext (fun n : nat => @lem1060912 A P r n)). Qed.
Lemma lem1060914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060915 {A : Type'} (P : type1338 A) (r : type1600 A) : (term105 A P r) = (term106 A P r).
Proof. exact (MK_COMB (@lem1060914) (@lem1060913 A P r)). Qed.
Lemma lem1060916 {A : Type'} (P : type1338 A) (r : type1600 A) : (term87 A P r) = (term107 A P r).
Proof. exact (MK_COMB (@lem1060911 A r) (@lem1060915 A P r)). Qed.
Lemma lem1060917 {A : Type'} (P : type1338 A) (r : type1600 A) : ((term86 A P r) = (term87 A P r)) = ((term40 A P r) = (term107 A P r)).
Proof. exact (MK_COMB (@lem1060905 A P r) (@lem1060916 A P r)). Qed.
Lemma lem1060918 {A : Type'} (P : type1338 A) (r : type1600 A) : (term40 A P r) = (term107 A P r).
Proof. exact (EQ_MP (@lem1060917 A P r) (@lem1060895 A P r)). Qed.
Lemma lem1060929 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060930 {A : Type'} (P : type1338 A) (r : type1600 A) : (term42 A P r) = (term108 A P r).
Proof. exact (MK_COMB (@lem1060929) (@lem1060918 A P r)). Qed.
Lemma lem1060933 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term44 A P c i r) = (term44 A P c i r).
Proof. exact (eq_refl (term44 A P c i r)). Qed.
Lemma lem1060934 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term46 A P c i r) = (term109 A P c i r).
Proof. exact (MK_COMB (@lem1060930 A P r) (@lem1060933 A P c i r)). Qed.
Lemma lem1060937 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term109 A P c i r) = (term46 A P c i r).
Proof. exact (SYM (@lem1060934 A P c i r)). Qed.
Lemma lem1060938 {A : Type'} (P : type1338 A) (r : type1600 A) (h1 : term107 A P r) : term107 A P r.
Proof. exact (h1). Qed.
Lemma lem1060939 {A : Type'} (P : type1338 A) (r : type1600 A) (h1 : term106 A P r) : term106 A P r.
Proof. exact (h1). Qed.
Lemma lem1060940 {A : Type'} (r : type1600 A) (h1 : term17 A r) : term17 A r.
Proof. exact (h1). Qed.
Lemma lem1060942 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term16 A c i r.
Proof. exact (EQ_MP (@lem1060709 A c i r) (@lem1060708 A c i r)). Qed.
Lemma lem1060943 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term16 A c i r.
Proof. exact (@lem1060942 A c i r). Qed.
Lemma lem1060957 {A : Type'} (n : nat) (r : type1600 A) (h1 : term17 A r) : term90 A r n.
Proof. exact (@lem1060940 A r h1 n). Qed.
Lemma lem1060958 {A : Type'} (r : type1600 A) (n : nat) : (term90 A r n) = (term91 A r n).
Proof. exact (eq_refl (term90 A r n)). Qed.
Lemma lem1060959 {A : Type'} (n : nat) (r : type1600 A) (h1 : term17 A r) : term91 A r n.
Proof. exact (EQ_MP (@lem1060958 A r n) (@lem1060957 A n r h1)). Qed.
Lemma lem1060960 {A : Type'} (r : type1600 A) (n : nat) : (term91 A r n) = ((term91 A r n) = True).
Proof. exact (@lem7 (term91 A r n)). Qed.
Lemma lem1060972 {A : Type'} (n : nat) (r : type1600 A) (h1 : term17 A r) : (term91 A r n) = True.
Proof. exact (EQ_MP (@lem1060960 A r n) (@lem1060959 A n r h1)). Qed.
Lemma lem1060973 {A : Type'} (r : type1600 A) (h1 : term17 A r) : (term88 A r) = term110.
Proof. exact (fun_ext (fun n : nat => @lem1060972 A n r h1)). Qed.
Lemma lem1060974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060975 {A : Type'} (r : type1600 A) (h1 : term17 A r) : (term17 A r) = term111.
Proof. exact (MK_COMB (@lem1060974) (@lem1060973 A r h1)). Qed.
Lemma lem1060977 {A : Type'} (t : Prop) : (term112 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1060978 (t : Prop) : (term113 t) = t.
Proof. exact (@lem1060977 nat t). Qed.
Lemma lem1060979 : term111 = True.
Proof. exact (@lem1060978 True). Qed.
Lemma lem1060980 {A : Type'} (r : type1600 A) (h1 : term17 A r) : (term17 A r) = True.
Proof. exact (TRANS (@lem1060975 A r h1) (@lem1060979)). Qed.
Lemma lem1060981 {A : Type'} (r : type1600 A) (h1 : term17 A r) : True = (term17 A r).
Proof. exact (SYM (@lem1060980 A r h1)). Qed.
Lemma lem1060982 {A : Type'} (r : type1600 A) (h1 : term17 A r) : term17 A r.
Proof. exact (EQ_MP (@lem1060981 A r h1) (@lem0)). Qed.
Lemma lem1060983 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term17 A r) : term18 A c i r.
Proof. exact (@lem1060943 A c i r (@lem1060982 A r h1)). Qed.
Lemma lem1060984 {A : Type'} (P : type1338 A) (h1 : term30 A P) : term30 A P.
Proof. exact (h1). Qed.
Lemma lem1060985 {A : Type'} (c : nat) (P : type1338 A) (h1 : term30 A P) : term114 A P c.
Proof. exact (@lem1060984 A P h1 c). Qed.
Lemma lem1060986 {A : Type'} (P : type1338 A) (c : nat) : (term114 A P c) = (term115 A P c).
Proof. exact (eq_refl (term114 A P c)). Qed.
Lemma lem1060987 {A : Type'} (c : nat) (P : type1338 A) (h1 : term30 A P) : term115 A P c.
Proof. exact (EQ_MP (@lem1060986 A P c) (@lem1060985 A c P h1)). Qed.
Lemma lem1060988 {A : Type'} (c : nat) (i : A) (P : type1338 A) (h1 : term30 A P) : term116 A P c i.
Proof. exact (@lem1060987 A c P h1 i). Qed.
Lemma lem1060989 {A : Type'} (P : type1338 A) (c : nat) (i : A) : (term116 A P c i) = (term117 A P c i).
Proof. exact (eq_refl (term116 A P c i)). Qed.
Lemma lem1060990 {A : Type'} (c : nat) (i : A) (P : type1338 A) (h1 : term30 A P) : term117 A P c i.
Proof. exact (EQ_MP (@lem1060989 A P c i) (@lem1060988 A c i P h1)). Qed.
Lemma lem1060991 {A : Type'} (c : nat) (i : A) (r : type1614 A) (P : type1338 A) (h1 : term30 A P) : term118 A P c i r.
Proof. exact (@lem1060990 A c i P h1 r). Qed.
Lemma lem1060992 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1614 A) : (term118 A P c i r) = (term119 A P c i r).
Proof. exact (eq_refl (term118 A P c i r)). Qed.
Lemma lem1060993 {A : Type'} (c : nat) (i : A) (r : type1614 A) (P : type1338 A) (h1 : term30 A P) : term119 A P c i r.
Proof. exact (EQ_MP (@lem1060992 A P c i r) (@lem1060991 A c i r P h1)). Qed.
Lemma lem1060994 {A : Type'} (P : type1338 A) (r : type1614 A) (h1 : term120 A P r) : term120 A P r.
Proof. exact (h1). Qed.
Lemma lem1060995 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1614 A) (h1 : term30 A P) (h2 : term120 A P r) : term121 A P c i r.
Proof. exact (@lem1060993 A c i r P h1 (@lem1060994 A P r h2)). Qed.
Lemma lem1060996 {A : Type'} (c : nat) (P : type1338 A) (r : type1614 A) (h1 : term30 A P) (h2 : term120 A P r) : term122 A P c r.
Proof. exact (fun i : A => @lem1060995 A c i P r h1 h2). Qed.
Lemma lem1060997 {A : Type'} (P : type1338 A) (r : type1614 A) (h1 : term30 A P) (h2 : term120 A P r) : term123 A P r.
Proof. exact (fun c : nat => @lem1060996 A c P r h1 h2). Qed.
Lemma lem1060998 {A : Type'} (r : type1614 A) (P : type1338 A) (h1 : term30 A P) : term124 A P r.
Proof. exact (fun h0 : term120 A P r => @lem1060997 A P r h1 h0). Qed.
Lemma lem1060999 {A : Type'} (P : type1338 A) (h1 : term30 A P) : term125 A P.
Proof. exact (fun r : type1614 A => @lem1060998 A r P h1). Qed.
Lemma lem1061000 {A : Type'} (P : type1338 A) : term126 A P.
Proof. exact (fun h0 : term30 A P => @lem1060999 A P h0). Qed.
Lemma lem1061001 {A : Type'} (P : type1338 A) (h1 : term30 A P) : term125 A P.
Proof. exact (@lem1061000 A P (@lem1060727 A P h1)). Qed.
Lemma lem1061002 {A : Type'} (r : type1614 A) (P : type1338 A) (h1 : term30 A P) : term127 A P r.
Proof. exact (@lem1061001 A P h1 r). Qed.
Lemma lem1061003 {A : Type'} (P : type1338 A) (r : type1614 A) : (term127 A P r) = (term124 A P r).
Proof. exact (eq_refl (term127 A P r)). Qed.
Lemma lem1061006 {A : Type'} (r : type1614 A) (P : type1338 A) (h1 : term30 A P) : term124 A P r.
Proof. exact (EQ_MP (@lem1061003 A P r) (@lem1061002 A r P h1)). Qed.
Lemma lem1061007 {A : Type'} (r : type1614 A) (P : type1338 A) (h1 : term30 A P) : term124 A P r.
Proof. exact (@lem1061006 A r P h1). Qed.
Lemma lem1061008 {A : Type'} (r : type1600 A) (P : type1338 A) (h1 : term30 A P) : term128 A P r.
Proof. exact (@lem1061007 A (term129 A r) P h1). Qed.
Lemma lem1061009 {A : Type'} (r : type1600 A) (n : nat) : (term130 A r n) = (term131 A r n).
Proof. exact (eq_refl (term130 A r n)). Qed.
Lemma lem1061010 {A : Type'} (P : type1338 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1061011 {A : Type'} (P : type1338 A) (r : type1600 A) (n : nat) : (term132 A P r n) = (term95 A P r n).
Proof. exact (MK_COMB (@lem1061010 A P) (@lem1061009 A r n)). Qed.
Lemma lem1061012 {A : Type'} (P : type1338 A) (r : type1600 A) : (term133 A P r) = (term89 A P r).
Proof. exact (fun_ext (fun n : nat => @lem1061011 A P r n)). Qed.
Lemma lem1061013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1061014 {A : Type'} (P : type1338 A) (r : type1600 A) : (term134 A P r) = (term106 A P r).
Proof. exact (MK_COMB (@lem1061013) (@lem1061012 A P r)). Qed.
Lemma lem1061015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1061016 {A : Type'} (P : type1338 A) (r : type1600 A) : (term135 A P r) = (term136 A P r).
Proof. exact (MK_COMB (@lem1061015) (@lem1061014 A P r)). Qed.
Lemma lem1061017 {A : Type'} (P : type1338 A) (r : type1600 A) : (term137 A P r) = (term137 A P r).
Proof. exact (eq_refl (term137 A P r)). Qed.
Lemma lem1061018 {A : Type'} (P : type1338 A) (r : type1600 A) : (term128 A P r) = (term138 A P r).
Proof. exact (MK_COMB (@lem1061016 A P r) (@lem1061017 A P r)). Qed.
Lemma lem1061019 {A : Type'} (r : type1600 A) (P : type1338 A) (h1 : term30 A P) : term138 A P r.
Proof. exact (EQ_MP (@lem1061018 A P r) (@lem1061008 A r P h1)). Qed.
Lemma lem1061020 {A : Type'} (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term106 A P r) : term137 A P r.
Proof. exact (@lem1061019 A r P h1 (@lem1060939 A P r h2)). Qed.
Lemma lem1061032 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (term9 A c i r).
Proof. exact (EQ_MP (@lem1060678 A c i r) (@lem1060677 A c i r)). Qed.
Lemma lem1061033 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (term9 A c i r).
Proof. exact (@lem1061032 A c i r). Qed.
Lemma lem1061034 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term139 A c i r) = (term140 A c i r).
Proof. exact (@lem1061033 A c i (term129 A r)). Qed.
Lemma lem1061036 {A B : Type'} (f : A -> B) (y : A) : (term141 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1061037 {A : Type'} (f : type1614 A) (y : nat) : (term142 A f y) = (f y).
Proof. exact (@lem1061036 nat (recspace A) f y). Qed.
Lemma lem1061038 {A : Type'} (r : type1600 A) (n : nat) : (term143 A r n) = (term130 A r n).
Proof. exact (@lem1061037 A (term129 A r) n). Qed.
Lemma lem1061039 {A : Type'} (r : type1600 A) (n : nat) : (term130 A r n) = (term131 A r n).
Proof. exact (eq_refl (term130 A r n)). Qed.
Lemma lem1061040 {A : Type'} (r : type1600 A) : (term144 A r) = (term129 A r).
Proof. exact (fun_ext (fun n : nat => @lem1061039 A r n)). Qed.
Lemma lem1061041 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1061042 {A : Type'} (r : type1600 A) (n : nat) : (term143 A r n) = (term130 A r n).
Proof. exact (MK_COMB (@lem1061040 A r) (@lem1061041 n)). Qed.
Lemma lem1061043 {A : Type'} : (@eq (recspace A)) = (@eq (recspace A)).
Proof. exact (eq_refl (@eq (recspace A))). Qed.
Lemma lem1061044 {A : Type'} (r : type1600 A) (n : nat) : (term145 A r n) = (term146 A r n).
Proof. exact (MK_COMB (@lem1061043 A) (@lem1061042 A r n)). Qed.
Lemma lem1061045 {A : Type'} (r : type1600 A) (n : nat) : (term130 A r n) = (term131 A r n).
Proof. exact (eq_refl (term130 A r n)). Qed.
Lemma lem1061046 {A : Type'} (r : type1600 A) (n : nat) : ((term143 A r n) = (term130 A r n)) = ((term130 A r n) = (term131 A r n)).
Proof. exact (MK_COMB (@lem1061044 A r n) (@lem1061045 A r n)). Qed.
Lemma lem1061047 {A : Type'} (r : type1600 A) (n : nat) : (term130 A r n) = (term131 A r n).
Proof. exact (EQ_MP (@lem1061046 A r n) (@lem1061038 A r n)). Qed.
Lemma lem1061048 {A : Type'} : (@_dest_rec A) = (@_dest_rec A).
Proof. exact (eq_refl (@_dest_rec A)). Qed.
Lemma lem1061049 {A : Type'} (r : type1600 A) (n : nat) : (term147 A r n) = (term148 A r n).
Proof. exact (MK_COMB (@lem1061048 A) (@lem1061047 A r n)). Qed.
Lemma lem1061050 {A : Type'} (r : type1600 A) : (term149 A r) = (term150 A r).
Proof. exact (fun_ext (fun n : nat => @lem1061049 A r n)). Qed.
Lemma lem1061051 {A : Type'} (c : nat) (i : A) : (@ZCONSTR A c i) = (@ZCONSTR A c i).
Proof. exact (eq_refl (@ZCONSTR A c i)). Qed.
Lemma lem1061052 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term151 A c i r) = (term152 A c i r).
Proof. exact (MK_COMB (@lem1061051 A c i) (@lem1061050 A r)). Qed.
Lemma lem1061053 {A : Type'} : (@_mk_rec A) = (@_mk_rec A).
Proof. exact (eq_refl (@_mk_rec A)). Qed.
Lemma lem1061054 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term140 A c i r) = (term153 A c i r).
Proof. exact (MK_COMB (@lem1061053 A) (@lem1061052 A c i r)). Qed.
Lemma lem1061055 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term139 A c i r) = (term153 A c i r).
Proof. exact (TRANS (@lem1061034 A c i r) (@lem1061054 A c i r)). Qed.
Lemma lem1061056 {A : Type'} (P : type1338 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1061057 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term154 A P c i r) = (term155 A P c i r).
Proof. exact (MK_COMB (@lem1061056 A P) (@lem1061055 A c i r)). Qed.
Lemma lem1061058 {A : Type'} (P : type1338 A) (c : nat) (r : type1600 A) : (term156 A P c r) = (term157 A P c r).
Proof. exact (fun_ext (fun i : A => @lem1061057 A P c i r)). Qed.
Lemma lem1061059 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1061060 {A : Type'} (P : type1338 A) (c : nat) (r : type1600 A) : (term158 A P c r) = (term159 A P c r).
Proof. exact (MK_COMB (@lem1061059 A) (@lem1061058 A P c r)). Qed.
Lemma lem1061065 {A : Type'} (P : type1338 A) (r : type1600 A) : (term160 A P r) = (term161 A P r).
Proof. exact (fun_ext (fun c : nat => @lem1061060 A P c r)). Qed.
Lemma lem1061066 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1061067 {A : Type'} (P : type1338 A) (r : type1600 A) : (term137 A P r) = (term162 A P r).
Proof. exact (MK_COMB (@lem1061066) (@lem1061065 A P r)). Qed.
Lemma lem1061072 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1061073 {A : Type'} (P : type1338 A) (r : type1600 A) : (term163 A P r) = (term164 A P r).
Proof. exact (MK_COMB (@lem1061072) (@lem1061067 A P r)). Qed.
Lemma lem1061074 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term165 A P c i r) = (term165 A P c i r).
Proof. exact (eq_refl (term165 A P c i r)). Qed.
Lemma lem1061075 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term166 A P c i r) = (term167 A P c i r).
Proof. exact (MK_COMB (@lem1061073 A P r) (@lem1061074 A P c i r)). Qed.
Lemma lem1061078 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term167 A P c i r) = (term166 A P c i r).
Proof. exact (SYM (@lem1061075 A P c i r)). Qed.
Lemma lem1061106 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term168 A r) = r).
Proof. exact (@axiom_10 A r). Qed.
Lemma lem1061107 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term168 A r) = r).
Proof. exact (@lem1061106 A r). Qed.
Lemma lem1061108 {A : Type'} (r : type1600 A) (n : nat) : (term91 A r n) = ((term148 A r n) = (r n)).
Proof. exact (@lem1061107 A (r n)). Qed.
Lemma lem1061111 {A : Type'} (r : type1600 A) : (term88 A r) = (term169 A r).
Proof. exact (fun_ext (fun n : nat => @lem1061108 A r n)). Qed.
Lemma lem1061112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1061113 {A : Type'} (r : type1600 A) : (term17 A r) = (term170 A r).
Proof. exact (MK_COMB (@lem1061112) (@lem1061111 A r)). Qed.
Lemma lem1061118 {A : Type'} (r : type1600 A) (h1 : term17 A r) : term170 A r.
Proof. exact (EQ_MP (@lem1061113 A r) (@lem1060940 A r h1)). Qed.
Lemma lem1061125 {A B : Type'} (t : A -> B) : term171 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem1061126 {A B : Type'} (t : A -> B) : (term171 A B t) = ((term172 A B t) = t).
Proof. exact (eq_refl (term171 A B t)). Qed.
Lemma lem1061127 {A B : Type'} (t : A -> B) : (term172 A B t) = t.
Proof. exact (EQ_MP (@lem1061126 A B t) (@lem1061125 A B t)). Qed.
Lemma lem1061148 {A : Type'} (n : nat) (r : type1600 A) (h1 : term17 A r) : term173 A r n.
Proof. exact (@lem1061118 A r h1 n). Qed.
Lemma lem1061149 {A : Type'} (r : type1600 A) (n : nat) : (term173 A r n) = ((term148 A r n) = (r n)).
Proof. exact (eq_refl (term173 A r n)). Qed.
Lemma lem1061159 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term174 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1061160 (p : Prop) (q : Prop) (p' : Prop) : term175 p q p'.
Proof. exact (fun q' : Prop => @lem1061159 p q p' q'). Qed.
Lemma lem1061161 (p : Prop) (q : Prop) : term176 p q.
Proof. exact (fun p' : Prop => @lem1061160 p q p'). Qed.
Lemma lem1061162 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : term177 A P c i r.
Proof. exact (@lem1061161 (term162 A P r) (term165 A P c i r)). Qed.
Lemma lem1061163 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (p' : Prop) : term178 A P c i r p'.
Proof. exact (@lem1061162 A P c i r p'). Qed.
Lemma lem1061164 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (p' : Prop) : (term178 A P c i r p') = (term179 A P c i r p').
Proof. exact (eq_refl (term178 A P c i r p')). Qed.
Lemma lem1061165 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (p' : Prop) : term179 A P c i r p'.
Proof. exact (EQ_MP (@lem1061164 A P c i r p') (@lem1061163 A P c i r p')). Qed.
Lemma lem1061166 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (p' : Prop) (q' : Prop) : term180 A P c i r p' q'.
Proof. exact (@lem1061165 A P c i r p' q'). Qed.
Lemma lem1061167 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (p' : Prop) (q' : Prop) : (term180 A P c i r p' q') = (term181 A P c i r p' q').
Proof. exact (eq_refl (term180 A P c i r p' q')). Qed.
Lemma lem1061168 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (p' : Prop) (q' : Prop) : term181 A P c i r p' q'.
Proof. exact (EQ_MP (@lem1061167 A P c i r p' q') (@lem1061166 A P c i r p' q')). Qed.
Lemma lem1061178 {A : Type'} (n : nat) (r : type1600 A) (h1 : term17 A r) : (term148 A r n) = (r n).
Proof. exact (EQ_MP (@lem1061149 A r n) (@lem1061148 A n r h1)). Qed.
Lemma lem1061179 {A : Type'} (r : type1600 A) (h1 : term17 A r) : (term150 A r) = (term182 A r).
Proof. exact (fun_ext (fun n : nat => @lem1061178 A n r h1)). Qed.
Lemma lem1061180 {A : Type'} (t : type1600 A) : (term182 A t) = t.
Proof. exact (@lem1061127 nat (type1597 A) t). Qed.
Lemma lem1061181 {A : Type'} (r : type1600 A) : (term182 A r) = r.
Proof. exact (@lem1061180 A r). Qed.
Lemma lem1061182 {A : Type'} (r : type1600 A) (h1 : term17 A r) : (term150 A r) = r.
Proof. exact (TRANS (@lem1061179 A r h1) (@lem1061181 A r)). Qed.
Lemma lem1061183 {A : Type'} (c : nat) (i : A) : (@ZCONSTR A c i) = (@ZCONSTR A c i).
Proof. exact (eq_refl (@ZCONSTR A c i)). Qed.
Lemma lem1061184 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term17 A r) : (term152 A c i r) = (@ZCONSTR A c i r).
Proof. exact (MK_COMB (@lem1061183 A c i) (@lem1061182 A r h1)). Qed.
Lemma lem1061185 {A : Type'} : (@_mk_rec A) = (@_mk_rec A).
Proof. exact (eq_refl (@_mk_rec A)). Qed.
Lemma lem1061186 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term17 A r) : (term153 A c i r) = (term183 A c i r).
Proof. exact (MK_COMB (@lem1061185 A) (@lem1061184 A c i r h1)). Qed.
Lemma lem1061187 {A : Type'} (P : type1338 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1061188 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (h1 : term17 A r) : (term155 A P c i r) = (term165 A P c i r).
Proof. exact (MK_COMB (@lem1061187 A P) (@lem1061186 A c i r h1)). Qed.
Lemma lem1061189 {A : Type'} (P : type1338 A) (c : nat) (r : type1600 A) (h1 : term17 A r) : (term157 A P c r) = (term184 A P c r).
Proof. exact (fun_ext (fun i : A => @lem1061188 A P c i r h1)). Qed.
Lemma lem1061190 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1061191 {A : Type'} (P : type1338 A) (c : nat) (r : type1600 A) (h1 : term17 A r) : (term159 A P c r) = (term185 A P c r).
Proof. exact (MK_COMB (@lem1061190 A) (@lem1061189 A P c r h1)). Qed.
Lemma lem1061196 {A : Type'} (P : type1338 A) (r : type1600 A) (h1 : term17 A r) : (term161 A P r) = (term186 A P r).
Proof. exact (fun_ext (fun c : nat => @lem1061191 A P c r h1)). Qed.
Lemma lem1061201 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1061202 {A : Type'} (P : type1338 A) (r : type1600 A) (h1 : term17 A r) : (term162 A P r) = (term187 A P r).
Proof. exact (MK_COMB (@lem1061201) (@lem1061196 A P r h1)). Qed.
Lemma lem1061211 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (q' : Prop) : term188 A c i P r q'.
Proof. exact (@lem1061168 A P c i r (term187 A P r) q'). Qed.
Lemma lem1061212 {A : Type'} (c : nat) (i : A) (P : type1338 A) (q' : Prop) (r : type1600 A) (h1 : term17 A r) : term189 A c i P r q'.
Proof. exact (@lem1061211 A c i P r q' (@lem1061202 A P r h1)). Qed.
Lemma lem1061213 {A : Type'} (P : type1338 A) (r : type1600 A) (h1 : term187 A P r) : term187 A P r.
Proof. exact (h1). Qed.
Lemma lem1061214 {A : Type'} (c : nat) (P : type1338 A) (r : type1600 A) (h1 : term187 A P r) : term190 A P r c.
Proof. exact (@lem1061213 A P r h1 c). Qed.
Lemma lem1061215 {A : Type'} (P : type1338 A) (c : nat) (r : type1600 A) : (term190 A P r c) = (term185 A P c r).
Proof. exact (eq_refl (term190 A P r c)). Qed.
Lemma lem1061216 {A : Type'} (c : nat) (P : type1338 A) (r : type1600 A) (h1 : term187 A P r) : term185 A P c r.
Proof. exact (EQ_MP (@lem1061215 A P c r) (@lem1061214 A c P r h1)). Qed.
Lemma lem1061217 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term187 A P r) : term191 A P c r i.
Proof. exact (@lem1061216 A c P r h1 i). Qed.
Lemma lem1061218 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term191 A P c r i) = (term165 A P c i r).
Proof. exact (eq_refl (term191 A P c r i)). Qed.
Lemma lem1061219 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term187 A P r) : term165 A P c i r.
Proof. exact (EQ_MP (@lem1061218 A P c i r) (@lem1061217 A c i P r h1)). Qed.
Lemma lem1061220 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term165 A P c i r) = ((term165 A P c i r) = True).
Proof. exact (@lem7 (term165 A P c i r)). Qed.
Lemma lem1061223 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term187 A P r) : (term165 A P c i r) = True.
Proof. exact (EQ_MP (@lem1061220 A P c i r) (@lem1061219 A c i P r h1)). Qed.
Lemma lem1061224 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term187 A P r) : (term165 A P c i r) = True.
Proof. exact (@lem1061223 A c i P r h1). Qed.
Lemma lem1061225 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : term192 A P c i r.
Proof. exact (fun h0 : term187 A P r => @lem1061224 A c i P r h0). Qed.
Lemma lem1061226 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term17 A r) : term193 A c i P r.
Proof. exact (@lem1061212 A c i P True r h1). Qed.
Lemma lem1061227 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term17 A r) : (term167 A P c i r) = (term194 A P r).
Proof. exact (@lem1061226 A c i P r h1 (@lem1061225 A P c i r)). Qed.
Lemma lem1061229 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1061230 {A : Type'} (P : type1338 A) (r : type1600 A) : (term194 A P r) = True.
Proof. exact (@lem1061229 (term187 A P r)). Qed.
Lemma lem1061231 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (h1 : term17 A r) : (term167 A P c i r) = True.
Proof. exact (TRANS (@lem1061227 A c i P r h1) (@lem1061230 A P r)). Qed.
Lemma lem1061232 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (h1 : term17 A r) : True = (term167 A P c i r).
Proof. exact (SYM (@lem1061231 A P c i r h1)). Qed.
Lemma lem1061233 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (h1 : term17 A r) : term167 A P c i r.
Proof. exact (EQ_MP (@lem1061232 A P c i r h1) (@lem0)). Qed.
Lemma lem1061234 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) (h1 : term17 A r) : term166 A P c i r.
Proof. exact (EQ_MP (@lem1061078 A P c i r) (@lem1061233 A P c i r h1)). Qed.
Lemma lem1061235 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term17 A r) (h3 : term106 A P r) : term165 A P c i r.
Proof. exact (@lem1061234 A P c i r h2 (@lem1061020 A P r h1 h3)). Qed.
Lemma lem1061236 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term17 A r) (h3 : term106 A P r) : term44 A P c i r.
Proof. exact (conj (@lem1060983 A c i r h2) (@lem1061235 A c i P r h1 h2 h3)). Qed.
Lemma lem1061237 {A : Type'} (P : type1338 A) (r : type1600 A) (h1 : term107 A P r) : term106 A P r.
Proof. exact (proj2 (@lem1060938 A P r h1)). Qed.
Lemma lem1061238 {A : Type'} (P : type1338 A) (r : type1600 A) (h1 : term107 A P r) : term17 A r.
Proof. exact (proj1 (@lem1060938 A P r h1)). Qed.
Lemma lem1061239 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term17 A r) (h3 : term106 A P r) : (term106 A P r) = (term44 A P c i r).
Proof. exact (prop_ext (fun h4 : term106 A P r => @lem1061236 A c i P r h1 h2 h3) (fun h4 : term44 A P c i r => @lem1060939 A P r h3)). Qed.
Lemma lem1061240 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term17 A r) (h3 : term106 A P r) : term44 A P c i r.
Proof. exact (EQ_MP (@lem1061239 A c i P r h1 h2 h3) (@lem1060939 A P r h3)). Qed.
Lemma lem1061241 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term17 A r) (h3 : term106 A P r) : (term17 A r) = (term44 A P c i r).
Proof. exact (prop_ext (fun h4 : term17 A r => @lem1061240 A c i P r h1 h2 h3) (fun h4 : term44 A P c i r => @lem1060940 A r h2)). Qed.
Lemma lem1061242 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term17 A r) (h3 : term106 A P r) : term44 A P c i r.
Proof. exact (EQ_MP (@lem1061241 A c i P r h1 h2 h3) (@lem1060940 A r h2)). Qed.
Lemma lem1061243 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term17 A r) (h3 : term107 A P r) : (term106 A P r) = (term44 A P c i r).
Proof. exact (prop_ext (fun h4 : term106 A P r => @lem1061242 A c i P r h1 h2 h4) (fun h4 : term44 A P c i r => @lem1061237 A P r h3)). Qed.
Lemma lem1061244 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term17 A r) (h3 : term107 A P r) : term44 A P c i r.
Proof. exact (EQ_MP (@lem1061243 A c i P r h1 h2 h3) (@lem1061237 A P r h3)). Qed.
Lemma lem1061245 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term107 A P r) : (term17 A r) = (term44 A P c i r).
Proof. exact (prop_ext (fun h3 : term17 A r => @lem1061244 A c i P r h1 h3 h2) (fun h3 : term44 A P c i r => @lem1061238 A P r h2)). Qed.
Lemma lem1061246 {A : Type'} (c : nat) (i : A) (P : type1338 A) (r : type1600 A) (h1 : term30 A P) (h2 : term107 A P r) : term44 A P c i r.
Proof. exact (EQ_MP (@lem1061245 A c i P r h1 h2) (@lem1061238 A P r h2)). Qed.
Lemma lem1061247 {A : Type'} (c : nat) (i : A) (r : type1600 A) (P : type1338 A) (h1 : term30 A P) : term109 A P c i r.
Proof. exact (fun h0 : term107 A P r => @lem1061246 A c i P r h1 h0). Qed.
Lemma lem1061248 {A : Type'} (c : nat) (i : A) (r : type1600 A) (P : type1338 A) (h1 : term30 A P) : term46 A P c i r.
Proof. exact (EQ_MP (@lem1060937 A P c i r) (@lem1061247 A c i r P h1)). Qed.
Lemma lem1061253 {A : Type'} (c : nat) (i : A) (P : type1338 A) (h1 : term30 A P) : term50 A P c i.
Proof. exact (fun r : type1600 A => @lem1061248 A c i r P h1). Qed.
Lemma lem1061258 {A : Type'} (c : nat) (P : type1338 A) (h1 : term30 A P) : term54 A P c.
Proof. exact (fun i : A => @lem1061253 A c i P h1). Qed.
Lemma lem1061263 {A : Type'} (P : type1338 A) (h1 : term30 A P) : term58 A P.
Proof. exact (fun c : nat => @lem1061258 A c P h1). Qed.
Lemma lem1061277 {A : Type'} (c : nat) (P : type1338 A) (h1 : term58 A P) : term195 A P c.
Proof. exact (@lem1060889 A P h1 c). Qed.
Lemma lem1061278 {A : Type'} (P : type1338 A) (c : nat) : (term195 A P c) = (term54 A P c).
Proof. exact (eq_refl (term195 A P c)). Qed.
Lemma lem1061279 {A : Type'} (c : nat) (P : type1338 A) (h1 : term58 A P) : term54 A P c.
Proof. exact (EQ_MP (@lem1061278 A P c) (@lem1061277 A c P h1)). Qed.
Lemma lem1061280 {A : Type'} (c : nat) (i : A) (P : type1338 A) (h1 : term58 A P) : term196 A P c i.
Proof. exact (@lem1061279 A c P h1 i). Qed.
Lemma lem1061281 {A : Type'} (P : type1338 A) (c : nat) (i : A) : (term196 A P c i) = (term50 A P c i).
Proof. exact (eq_refl (term196 A P c i)). Qed.
Lemma lem1061282 {A : Type'} (c : nat) (i : A) (P : type1338 A) (h1 : term58 A P) : term50 A P c i.
Proof. exact (EQ_MP (@lem1061281 A P c i) (@lem1061280 A c i P h1)). Qed.
Lemma lem1061283 {A : Type'} (c : nat) (i : A) (r : type1600 A) (P : type1338 A) (h1 : term58 A P) : term197 A P c i r.
Proof. exact (@lem1061282 A c i P h1 r). Qed.
Lemma lem1061284 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term197 A P c i r) = (term46 A P c i r).
Proof. exact (eq_refl (term197 A P c i r)). Qed.
Lemma lem1061285 {A : Type'} (c : nat) (i : A) (r : type1600 A) (P : type1338 A) (h1 : term58 A P) : term46 A P c i r.
Proof. exact (EQ_MP (@lem1061284 A P c i r) (@lem1061283 A c i r P h1)). Qed.
Lemma lem1061286 {A : Type'} (P : type1338 A) (c : nat) (i : A) (r : type1600 A) : (term46 A P c i r) = ((term46 A P c i r) = True).
Proof. exact (@lem7 (term46 A P c i r)). Qed.
Lemma lem1061305 {A : Type'} (c : nat) (i : A) (r : type1600 A) (P : type1338 A) (h1 : term58 A P) : (term46 A P c i r) = True.
Proof. exact (EQ_MP (@lem1061286 A P c i r) (@lem1061285 A c i r P h1)). Qed.
Lemma lem1061306 {A : Type'} (c : nat) (i : A) (r : type1600 A) (P : type1338 A) (h1 : term58 A P) : (term46 A P c i r) = True.
Proof. exact (@lem1061305 A c i r P h1). Qed.
Lemma lem1061307 {A : Type'} (c : nat) (i : A) (P : type1338 A) (h1 : term58 A P) : (term48 A P c i) = (term198 A).
Proof. exact (fun_ext (fun r : type1600 A => @lem1061306 A c i r P h1)). Qed.
Lemma lem1061308 {A : Type'} : (@all (nat -> nat -> A -> Prop)) = (@all (nat -> nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> A -> Prop))). Qed.
Lemma lem1061309 {A : Type'} (c : nat) (i : A) (P : type1338 A) (h1 : term58 A P) : (term50 A P c i) = (term199 A).
Proof. exact (MK_COMB (@lem1061308 A) (@lem1061307 A c i P h1)). Qed.
Lemma lem1061311 {A : Type'} (t : Prop) : (term112 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1061312 {A : Type'} (t : Prop) : (term200 A t) = t.
Proof. exact (@lem1061311 (type1600 A) t). Qed.
Lemma lem1061313 {A : Type'} : (term199 A) = True.
Proof. exact (@lem1061312 A True). Qed.
Lemma lem1061314 {A : Type'} (c : nat) (i : A) (P : type1338 A) (h1 : term58 A P) : (term50 A P c i) = True.
Proof. exact (TRANS (@lem1061309 A c i P h1) (@lem1061313 A)). Qed.
Lemma lem1061315 {A : Type'} (c : nat) (P : type1338 A) (h1 : term58 A P) : (term52 A P c) = (term201 A).
Proof. exact (fun_ext (fun i : A => @lem1061314 A c i P h1)). Qed.
Lemma lem1061316 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1061317 {A : Type'} (c : nat) (P : type1338 A) (h1 : term58 A P) : (term54 A P c) = (term202 A).
Proof. exact (MK_COMB (@lem1061316 A) (@lem1061315 A c P h1)). Qed.
Lemma lem1061319 {A : Type'} (t : Prop) : (term112 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1061320 {A : Type'} (t : Prop) : (term112 A t) = t.
Proof. exact (@lem1061319 A t). Qed.
Lemma lem1061321 {A : Type'} : (term202 A) = True.
Proof. exact (@lem1061320 A True). Qed.
Lemma lem1061322 {A : Type'} (c : nat) (P : type1338 A) (h1 : term58 A P) : (term54 A P c) = True.
Proof. exact (TRANS (@lem1061317 A c P h1) (@lem1061321 A)). Qed.
Lemma lem1061323 {A : Type'} (P : type1338 A) (h1 : term58 A P) : (term56 A P) = term110.
Proof. exact (fun_ext (fun c : nat => @lem1061322 A c P h1)). Qed.
Lemma lem1061324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1061325 {A : Type'} (P : type1338 A) (h1 : term58 A P) : (term58 A P) = term111.
Proof. exact (MK_COMB (@lem1061324) (@lem1061323 A P h1)). Qed.
Lemma lem1061327 {A : Type'} (t : Prop) : (term112 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1061328 (t : Prop) : (term113 t) = t.
Proof. exact (@lem1061327 nat t). Qed.
Lemma lem1061329 : term111 = True.
Proof. exact (@lem1061328 True). Qed.
Lemma lem1061330 {A : Type'} (P : type1338 A) (h1 : term58 A P) : (term58 A P) = True.
Proof. exact (TRANS (@lem1061325 A P h1) (@lem1061329)). Qed.
Lemma lem1061331 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1061332 {A : Type'} (P : type1338 A) (h1 : term58 A P) : (term80 A P) = (imp True).
Proof. exact (MK_COMB (@lem1061331) (@lem1061330 A P h1)). Qed.
Lemma lem1061341 {A : Type'} (P : type1338 A) : (term71 A P) = (term71 A P).
Proof. exact (eq_refl (term71 A P)). Qed.
Lemma lem1061342 {A : Type'} (P : type1338 A) (h1 : term58 A P) : (term81 A P) = (term203 A P).
Proof. exact (MK_COMB (@lem1061332 A P h1) (@lem1061341 A P)). Qed.
Lemma lem1061344 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1061345 {A : Type'} (P : type1338 A) : (term203 A P) = (term71 A P).
Proof. exact (@lem1061344 (term71 A P)). Qed.
Lemma lem1061354 {A : Type'} (P : type1338 A) (h1 : term58 A P) : (term81 A P) = (term71 A P).
Proof. exact (TRANS (@lem1061342 A P h1) (@lem1061345 A P)). Qed.
Lemma lem1061355 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1061356 {A : Type'} (P : type1338 A) (h1 : term58 A P) : (term82 A P) = (term204 A P).
Proof. exact (MK_COMB (@lem1061355) (@lem1061354 A P h1)). Qed.
Lemma lem1061357 {A : Type'} (P : type1338 A) (x : recspace A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1061358 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term58 A P) : (term83 A P x) = (term205 A P x).
Proof. exact (MK_COMB (@lem1061356 A P h1) (@lem1061357 A P x)). Qed.
Lemma lem1061361 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term58 A P) : (term205 A P x) = (term83 A P x).
Proof. exact (SYM (@lem1061358 A x P h1)). Qed.
Lemma lem1061362 {A : Type'} (P : type1338 A) (h1 : term71 A P) : term71 A P.
Proof. exact (h1). Qed.
Lemma lem1061363 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term71 A P) : term206 A P x.
Proof. exact (@lem1061362 A P h1 (@_dest_rec A x)). Qed.
Lemma lem1061364 {A : Type'} (P : type1338 A) (x : recspace A) : (term206 A P x) = (term207 A P x).
Proof. exact (eq_refl (term206 A P x)). Qed.
Lemma lem1061365 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term71 A P) : term207 A P x.
Proof. exact (EQ_MP (@lem1061364 A P x) (@lem1061363 A x P h1)). Qed.
Lemma lem1061373 {A : Type'} (a : recspace A) : (term208 A a) = a.
Proof. exact (@axiom_9 A a). Qed.
Lemma lem1061374 {A : Type'} (a : recspace A) : (term208 A a) = a.
Proof. exact (@lem1061373 A a). Qed.
Lemma lem1061375 {A : Type'} (x : recspace A) : (term208 A x) = x.
Proof. exact (@lem1061374 A x). Qed.
Lemma lem1061376 {A : Type'} (P : type1338 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1061377 {A : Type'} (P : type1338 A) (x : recspace A) : (term209 A P x) = (P x).
Proof. exact (MK_COMB (@lem1061376 A P) (@lem1061375 A x)). Qed.
Lemma lem1061378 {A : Type'} (x : recspace A) : (term210 A x) = (term210 A x).
Proof. exact (eq_refl (term210 A x)). Qed.
Lemma lem1061379 {A : Type'} (P : type1338 A) (x : recspace A) : (term211 A P x) = (term212 A P x).
Proof. exact (MK_COMB (@lem1061378 A x) (@lem1061377 A P x)). Qed.
Lemma lem1061382 {A : Type'} (x : recspace A) : (term213 A x) = (term213 A x).
Proof. exact (eq_refl (term213 A x)). Qed.
Lemma lem1061383 {A : Type'} (P : type1338 A) (x : recspace A) : (term207 A P x) = (term214 A P x).
Proof. exact (MK_COMB (@lem1061382 A x) (@lem1061379 A P x)). Qed.
Lemma lem1061386 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1061387 {A : Type'} (P : type1338 A) (x : recspace A) : (term215 A P x) = (term216 A P x).
Proof. exact (MK_COMB (@lem1061386) (@lem1061383 A P x)). Qed.
Lemma lem1061388 {A : Type'} (P : type1338 A) (x : recspace A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1061389 {A : Type'} (P : type1338 A) (x : recspace A) : (term217 A P x) = (term218 A P x).
Proof. exact (MK_COMB (@lem1061387 A P x) (@lem1061388 A P x)). Qed.
Lemma lem1061392 {A : Type'} (P : type1338 A) (x : recspace A) : (term218 A P x) = (term217 A P x).
Proof. exact (SYM (@lem1061389 A P x)). Qed.
Lemma lem1061396 (a : Prop) (b : Prop) : (term0 a b) = (a -> b).
Proof. exact (EQ_MP (@lem1060669 a b) (@lem1060668 a b)). Qed.
Lemma lem1061397 {A : Type'} (P : type1338 A) (x : recspace A) : (term214 A P x) = (term219 A P x).
Proof. exact (@lem1061396 (term220 A x) (P x)). Qed.
Lemma lem1061400 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1061401 {A : Type'} (P : type1338 A) (x : recspace A) : (term216 A P x) = (term221 A P x).
Proof. exact (MK_COMB (@lem1061400) (@lem1061397 A P x)). Qed.
Lemma lem1061402 {A : Type'} (P : type1338 A) (x : recspace A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1061403 {A : Type'} (P : type1338 A) (x : recspace A) : (term218 A P x) = (term222 A P x).
Proof. exact (MK_COMB (@lem1061401 A P x) (@lem1061402 A P x)). Qed.
Lemma lem1061406 {A : Type'} (P : type1338 A) (x : recspace A) : (term222 A P x) = (term218 A P x).
Proof. exact (SYM (@lem1061403 A P x)). Qed.
Lemma lem1061407 {A : Type'} (P : type1338 A) (x : recspace A) (h1 : term219 A P x) : term219 A P x.
Proof. exact (h1). Qed.
Lemma lem1061408 {A : Type'} (P : type1338 A) (x : recspace A) (h1 : term219 A P x) : term219 A P x.
Proof. exact (h1). Qed.
Lemma lem1061409 {A : Type'} (x : recspace A) (h1 : term220 A x) : term220 A x.
Proof. exact (h1). Qed.
Lemma lem1061410 {A : Type'} (P : type1338 A) (x : recspace A) (h1 : term220 A x) (h2 : term219 A P x) : P x.
Proof. exact (@lem1061408 A P x h2 (@lem1061409 A x h1)). Qed.
Lemma lem1061411 {A : Type'} (P : type1338 A) (x : recspace A) (h1 : term220 A x) : term222 A P x.
Proof. exact (fun h0 : term219 A P x => @lem1061410 A P x h1 h0). Qed.
Lemma lem1061412 {A : Type'} (P : type1338 A) (x : recspace A) (h1 : term219 A P x) : term219 A P x.
Proof. exact (h1). Qed.
Lemma lem1061413 {A : Type'} (P : type1338 A) (x : recspace A) (h1 : term220 A x) (h2 : term219 A P x) : P x.
Proof. exact (@lem1061411 A P x h1 (@lem1061412 A P x h2)). Qed.
Lemma lem1061414 {A : Type'} (P : type1338 A) (x : recspace A) (h1 : term219 A P x) : term219 A P x.
Proof. exact (fun h0 : term220 A x => @lem1061413 A P x h0 h1). Qed.
Lemma lem1061415 {A : Type'} (P : type1338 A) (x : recspace A) : term223 A P x.
Proof. exact (fun h0 : term219 A P x => @lem1061414 A P x h0). Qed.
Lemma lem1061418 {A : Type'} (P : type1338 A) (x : recspace A) (h1 : term219 A P x) : term219 A P x.
Proof. exact (@lem1061415 A P x (@lem1061407 A P x h1)). Qed.
Lemma lem1061420 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term168 A r) = r).
Proof. exact (@axiom_10 A r). Qed.
Lemma lem1061421 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term168 A r) = r).
Proof. exact (@lem1061420 A r). Qed.
Lemma lem1061422 {A : Type'} (x : recspace A) : (term220 A x) = ((term224 A x) = (@_dest_rec A x)).
Proof. exact (@lem1061421 A (@_dest_rec A x)). Qed.
Lemma lem1061426 {A : Type'} (a : recspace A) : (term208 A a) = a.
Proof. exact (@axiom_9 A a). Qed.
Lemma lem1061427 {A : Type'} (a : recspace A) : (term208 A a) = a.
Proof. exact (@lem1061426 A a). Qed.
Lemma lem1061428 {A : Type'} (x : recspace A) : (term208 A x) = x.
Proof. exact (@lem1061427 A x). Qed.
Lemma lem1061429 {A : Type'} : (@_dest_rec A) = (@_dest_rec A).
Proof. exact (eq_refl (@_dest_rec A)). Qed.
Lemma lem1061430 {A : Type'} (x : recspace A) : (term224 A x) = (@_dest_rec A x).
Proof. exact (MK_COMB (@lem1061429 A) (@lem1061428 A x)). Qed.
Lemma lem1061431 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1061432 {A : Type'} (x : recspace A) : (term225 A x) = (term226 A x).
Proof. exact (MK_COMB (@lem1061431 A) (@lem1061430 A x)). Qed.
Lemma lem1061433 {A : Type'} (x : recspace A) : (@_dest_rec A x) = (@_dest_rec A x).
Proof. exact (eq_refl (@_dest_rec A x)). Qed.
Lemma lem1061434 {A : Type'} (x : recspace A) : ((term224 A x) = (@_dest_rec A x)) = ((@_dest_rec A x) = (@_dest_rec A x)).
Proof. exact (MK_COMB (@lem1061432 A x) (@lem1061433 A x)). Qed.
Lemma lem1061436 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1061437 {A : Type'} (x : type1597 A) : (x = x) = True.
Proof. exact (@lem1061436 (type1597 A) x). Qed.
Lemma lem1061438 {A : Type'} (x : recspace A) : ((@_dest_rec A x) = (@_dest_rec A x)) = True.
Proof. exact (@lem1061437 A (@_dest_rec A x)). Qed.
Lemma lem1061439 {A : Type'} (x : recspace A) : ((term224 A x) = (@_dest_rec A x)) = True.
Proof. exact (TRANS (@lem1061434 A x) (@lem1061438 A x)). Qed.
Lemma lem1061440 {A : Type'} (x : recspace A) : (term220 A x) = True.
Proof. exact (TRANS (@lem1061422 A x) (@lem1061439 A x)). Qed.
Lemma lem1061441 {A : Type'} (x : recspace A) : True = (term220 A x).
Proof. exact (SYM (@lem1061440 A x)). Qed.
Lemma lem1061442 {A : Type'} (x : recspace A) : term220 A x.
Proof. exact (EQ_MP (@lem1061441 A x) (@lem0)). Qed.
Lemma lem1061443 {A : Type'} (P : type1338 A) (x : recspace A) (h1 : term219 A P x) : P x.
Proof. exact (@lem1061418 A P x h1 (@lem1061442 A x)). Qed.
Lemma lem1061444 {A : Type'} (P : type1338 A) (x : recspace A) : term222 A P x.
Proof. exact (fun h0 : term219 A P x => @lem1061443 A P x h0). Qed.
Lemma lem1061445 {A : Type'} (P : type1338 A) (x : recspace A) : term218 A P x.
Proof. exact (EQ_MP (@lem1061406 A P x) (@lem1061444 A P x)). Qed.
Lemma lem1061446 {A : Type'} (P : type1338 A) (x : recspace A) : term217 A P x.
Proof. exact (EQ_MP (@lem1061392 A P x) (@lem1061445 A P x)). Qed.
Lemma lem1061447 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term71 A P) : P x.
Proof. exact (@lem1061446 A P x (@lem1061365 A x P h1)). Qed.
Lemma lem1061448 {A : Type'} (P : type1338 A) (x : recspace A) : term205 A P x.
Proof. exact (fun h0 : term71 A P => @lem1061447 A x P h0). Qed.
Lemma lem1061449 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term58 A P) : term83 A P x.
Proof. exact (EQ_MP (@lem1061361 A x P h1) (@lem1061448 A P x)). Qed.
Lemma lem1061450 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term58 A P) : (term58 A P) = (term83 A P x).
Proof. exact (prop_ext (fun h2 : term58 A P => @lem1061449 A x P h1) (fun h2 : term83 A P x => @lem1060889 A P h1)). Qed.
Lemma lem1061451 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term58 A P) : term83 A P x.
Proof. exact (EQ_MP (@lem1061450 A x P h1) (@lem1060889 A P h1)). Qed.
Lemma lem1061452 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term30 A P) : (term58 A P) = (term83 A P x).
Proof. exact (prop_ext (fun h2 : term58 A P => @lem1061451 A x P h2) (fun h2 : term83 A P x => @lem1061263 A P h1)). Qed.
Lemma lem1061453 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term30 A P) : term83 A P x.
Proof. exact (EQ_MP (@lem1061452 A x P h1) (@lem1061263 A P h1)). Qed.
Lemma lem1061454 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term30 A P) (h2 : P (@BOTTOM A)) : term76 A P x.
Proof. exact (EQ_MP (@lem1060888 A x P h2) (@lem1061453 A x P h1)). Qed.
Lemma lem1061455 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term30 A P) (h2 : P (@BOTTOM A)) : term75 A P x.
Proof. exact (EQ_MP (@lem1060763 A P x) (@lem1061454 A x P h1 h2)). Qed.
Lemma lem1061456 {A : Type'} (x : recspace A) (P : type1338 A) (h1 : term30 A P) (h2 : P (@BOTTOM A)) : P x.
Proof. exact (@lem1061455 A x P h1 h2 (@lem1060725 A P)). Qed.
Lemma lem1061461 {A : Type'} (P : type1338 A) (h1 : term30 A P) (h2 : P (@BOTTOM A)) : term227 A P.
Proof. exact (fun x : recspace A => @lem1061456 A x P h1 h2). Qed.
Lemma lem1061462 {A : Type'} (P : type1338 A) (h1 : term29 A P) : term30 A P.
Proof. exact (proj2 (@lem1060726 A P h1)). Qed.
Lemma lem1061463 {A : Type'} (P : type1338 A) (h1 : term29 A P) : P (@BOTTOM A).
Proof. exact (proj1 (@lem1060726 A P h1)). Qed.
Lemma lem1061464 {A : Type'} (P : type1338 A) (h1 : term30 A P) (h2 : P (@BOTTOM A)) : (term30 A P) = (term227 A P).
Proof. exact (prop_ext (fun h3 : term30 A P => @lem1061461 A P h1 h2) (fun h3 : term227 A P => @lem1060727 A P h1)). Qed.
Lemma lem1061465 {A : Type'} (P : type1338 A) (h1 : term30 A P) (h2 : P (@BOTTOM A)) : term227 A P.
Proof. exact (EQ_MP (@lem1061464 A P h1 h2) (@lem1060727 A P h1)). Qed.
Lemma lem1061466 {A : Type'} (P : type1338 A) (h1 : term30 A P) (h2 : P (@BOTTOM A)) : (P (@BOTTOM A)) = (term227 A P).
Proof. exact (prop_ext (fun h3 : P (@BOTTOM A) => @lem1061465 A P h1 h2) (fun h3 : term227 A P => @lem1060728 A P h2)). Qed.
Lemma lem1061467 {A : Type'} (P : type1338 A) (h1 : term30 A P) (h2 : P (@BOTTOM A)) : term227 A P.
Proof. exact (EQ_MP (@lem1061466 A P h1 h2) (@lem1060728 A P h2)). Qed.
Lemma lem1061468 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) (h2 : term29 A P) : (term30 A P) = (term227 A P).
Proof. exact (prop_ext (fun h3 : term30 A P => @lem1061467 A P h3 h1) (fun h3 : term227 A P => @lem1061462 A P h2)). Qed.
Lemma lem1061469 {A : Type'} (P : type1338 A) (h1 : P (@BOTTOM A)) (h2 : term29 A P) : term227 A P.
Proof. exact (EQ_MP (@lem1061468 A P h1 h2) (@lem1061462 A P h2)). Qed.
Lemma lem1061470 {A : Type'} (P : type1338 A) (h1 : term29 A P) : (P (@BOTTOM A)) = (term227 A P).
Proof. exact (prop_ext (fun h2 : P (@BOTTOM A) => @lem1061469 A P h2 h1) (fun h2 : term227 A P => @lem1061463 A P h1)). Qed.
Lemma lem1061471 {A : Type'} (P : type1338 A) (h1 : term29 A P) : term227 A P.
Proof. exact (EQ_MP (@lem1061470 A P h1) (@lem1061463 A P h1)). Qed.
Lemma lem1061472 {A : Type'} (P : type1338 A) : term228 A P.
Proof. exact (fun h0 : term29 A P => @lem1061471 A P h0). Qed.
Lemma lem1061477 {A : Type'} : term229 A.
Proof. exact (fun P : type1338 A => @lem1061472 A P). Qed.
