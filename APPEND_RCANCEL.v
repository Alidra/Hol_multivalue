Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import APPEND_RCANCEL_term_abbrevs.
Require Import APPEND_LCANCEL_spec.
Require Import DISJ_ACI_spec.
Require Import REVERSE_APPEND_spec.
Require Import REVERSE_REVERSE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1187629 {A : Type'} (l1 : list A) : term0 A l1.
Proof. exact (@lem1187628 A l1). Qed.
Lemma lem1187630 {A : Type'} (l1 : list A) : (term0 A l1) = (term1 A l1).
Proof. exact (eq_refl (term0 A l1)). Qed.
Lemma lem1187631 {A : Type'} (l1 : list A) : term1 A l1.
Proof. exact (EQ_MP (@lem1187630 A l1) (@lem1187629 A l1)). Qed.
Lemma lem1187632 {A : Type'} (l1 : list A) (l2 : list A) : term2 A l1 l2.
Proof. exact (@lem1187631 A l1 l2). Qed.
Lemma lem1187633 {A : Type'} (l1 : list A) (l2 : list A) : (term2 A l1 l2) = (term3 A l1 l2).
Proof. exact (eq_refl (term2 A l1 l2)). Qed.
Lemma lem1187634 {A : Type'} (l1 : list A) (l2 : list A) : term3 A l1 l2.
Proof. exact (EQ_MP (@lem1187633 A l1 l2) (@lem1187632 A l1 l2)). Qed.
Lemma lem1187635 {A : Type'} (l1 : list A) (l2 : list A) (l3 : list A) : term4 A l1 l2 l3.
Proof. exact (@lem1187634 A l1 l2 l3). Qed.
Lemma lem1187636 {A : Type'} (l1 : list A) (l2 : list A) (l3 : list A) : (term4 A l1 l2 l3) = (((@List.app A l1 l2) = (@List.app A l1 l3)) = (l2 = l3)).
Proof. exact (eq_refl (term4 A l1 l2 l3)). Qed.
Lemma lem1187638 {A : Type'} (l : list A) : term5 A l.
Proof. exact (@lem1112107 A l). Qed.
Lemma lem1187639 {A : Type'} (l : list A) : (term5 A l) = (term6 A l).
Proof. exact (eq_refl (term5 A l)). Qed.
Lemma lem1187640 {A : Type'} (l : list A) : term6 A l.
Proof. exact (EQ_MP (@lem1187639 A l) (@lem1187638 A l)). Qed.
Lemma lem1187641 {A : Type'} (l : list A) (m : list A) : term7 A l m.
Proof. exact (@lem1187640 A l m). Qed.
Lemma lem1187642 {A : Type'} (m : list A) (l : list A) : (term7 A l m) = ((term8 A l m) = (term9 A m l)).
Proof. exact (eq_refl (term7 A l m)). Qed.
Lemma lem1187655 (p : Prop) : p = (term10 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1187656 {_27693 : Type'} (l : list _27693) (l' : list _27693) : ((l = l') = ((@List.rev _27693 l) = (@List.rev _27693 l'))) = (term11 _27693 l l').
Proof. exact (@lem1187655 ((l = l') = ((@List.rev _27693 l) = (@List.rev _27693 l')))). Qed.
Lemma lem1187657 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term11 _27693 l l') = ((l = l') = ((@List.rev _27693 l) = (@List.rev _27693 l'))).
Proof. exact (SYM (@lem1187656 _27693 l l')). Qed.
Lemma lem1187658 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term12 _27693 l l') : term12 _27693 l l'.
Proof. exact (h1). Qed.
Lemma lem1187659 {_27693 : Type'} : term13 _27693.
Proof. exact (@lem1112270 _27693). Qed.
Lemma lem1187663 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term14 _27693 l l') : term14 _27693 l l'.
Proof. exact (h1). Qed.
Lemma lem1187664 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term15 _27693 l l'.
Proof. exact (fun h0 : term14 _27693 l l' => @lem1187663 _27693 l l' h0). Qed.
Lemma lem1187665 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term15 _27693 l l') : term15 _27693 l l'.
Proof. exact (h1). Qed.
Lemma lem1187666 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term14 _27693 l l') : term14 _27693 l l'.
Proof. exact (h1). Qed.
Lemma lem1187667 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term14 _27693 l l') (h2 : term15 _27693 l l') : term14 _27693 l l'.
Proof. exact (@lem1187665 _27693 l l' h2 (@lem1187666 _27693 l l' h1)). Qed.
Lemma lem1187668 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term14 _27693 l l') : term16 _27693 l l'.
Proof. exact (fun h0 : term15 _27693 l l' => @lem1187667 _27693 l l' h1 h0). Qed.
Lemma lem1187669 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term15 _27693 l l') : term15 _27693 l l'.
Proof. exact (h1). Qed.
Lemma lem1187670 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term14 _27693 l l') (h2 : term15 _27693 l l') : term14 _27693 l l'.
Proof. exact (@lem1187668 _27693 l l' h1 (@lem1187669 _27693 l l' h2)). Qed.
Lemma lem1187671 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term15 _27693 l l') : term15 _27693 l l'.
Proof. exact (fun h0 : term14 _27693 l l' => @lem1187670 _27693 l l' h0 h1). Qed.
Lemma lem1187672 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term17 _27693 l l'.
Proof. exact (fun h0 : term15 _27693 l l' => @lem1187671 _27693 l l' h0). Qed.
Lemma lem1187675 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term15 _27693 l l'.
Proof. exact (@lem1187672 _27693 l l' (@lem1187664 _27693 l l')). Qed.
Lemma lem1187676 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term15 _27693 l l'.
Proof. exact (@lem1187675 _27693 l l'). Qed.
Lemma lem1187688 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1187689 {_27693 : Type'} : (term18 _27693) = (term19 _27693).
Proof. exact (@lem1187688 (term13 _27693)). Qed.
Lemma lem1187694 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term20 _27693 l l') = (term20 _27693 l l').
Proof. exact (eq_refl (term20 _27693 l l')). Qed.
Lemma lem1187695 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term14 _27693 l l') = (term21 _27693 l l').
Proof. exact (MK_COMB (@lem1187694 _27693 l l') (@lem1187689 _27693)). Qed.
Lemma lem1187698 {_27693 : Type'} (l' : list _27693) : (term22 _27693 l') = (term23 _27693 l').
Proof. exact (fun_ext (fun l : list _27693 => @lem1187695 _27693 l l')). Qed.
Lemma lem1187699 {_27693 : Type'} : (@all (list _27693)) = (@all (list _27693)).
Proof. exact (eq_refl (@all (list _27693))). Qed.
Lemma lem1187700 {_27693 : Type'} (l' : list _27693) : (term24 _27693 l') = (term25 _27693 l').
Proof. exact (MK_COMB (@lem1187699 _27693) (@lem1187698 _27693 l')). Qed.
Lemma lem1187705 {_27693 : Type'} : (term26 _27693) = (term27 _27693).
Proof. exact (fun_ext (fun l' : list _27693 => @lem1187700 _27693 l')). Qed.
Lemma lem1187706 {_27693 : Type'} : (@all (list _27693)) = (@all (list _27693)).
Proof. exact (eq_refl (@all (list _27693))). Qed.
Lemma lem1187715 {_27693 : Type'} : (term28 _27693) = (term29 _27693).
Proof. exact (MK_COMB (@lem1187706 _27693) (@lem1187705 _27693)). Qed.
Lemma lem1187716 {_27693 : Type'} (l : list _27693) : ((term30 _27693 l) = l) = ((term30 _27693 l) = l).
Proof. exact (eq_refl ((term30 _27693 l) = l)). Qed.
Lemma lem1187717 {_27693 : Type'} : (term31 _27693) = (term31 _27693).
Proof. exact (fun_ext (fun l : list _27693 => @lem1187716 _27693 l)). Qed.
Lemma lem1187718 {_27693 : Type'} : (@all (list _27693)) = (@all (list _27693)).
Proof. exact (eq_refl (@all (list _27693))). Qed.
Lemma lem1187719 {_27693 : Type'} : (term13 _27693) = (term13 _27693).
Proof. exact (MK_COMB (@lem1187718 _27693) (@lem1187717 _27693)). Qed.
Lemma lem1187720 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1187721 {_27693 : Type'} : (term19 _27693) = (term19 _27693).
Proof. exact (MK_COMB (@lem1187720) (@lem1187719 _27693)). Qed.
Lemma lem1187730 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term20 _27693 l l') = (term20 _27693 l l').
Proof. exact (eq_refl (term20 _27693 l l')). Qed.
Lemma lem1187731 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term21 _27693 l l') = (term21 _27693 l l').
Proof. exact (MK_COMB (@lem1187730 _27693 l l') (@lem1187721 _27693)). Qed.
Lemma lem1187732 {_27693 : Type'} (l' : list _27693) : (term23 _27693 l') = (term23 _27693 l').
Proof. exact (fun_ext (fun l : list _27693 => @lem1187731 _27693 l l')). Qed.
Lemma lem1187733 {_27693 : Type'} : (@all (list _27693)) = (@all (list _27693)).
Proof. exact (eq_refl (@all (list _27693))). Qed.
Lemma lem1187734 {_27693 : Type'} (l' : list _27693) : (term25 _27693 l') = (term25 _27693 l').
Proof. exact (MK_COMB (@lem1187733 _27693) (@lem1187732 _27693 l')). Qed.
Lemma lem1187735 {_27693 : Type'} : (term27 _27693) = (term27 _27693).
Proof. exact (fun_ext (fun l' : list _27693 => @lem1187734 _27693 l')). Qed.
Lemma lem1187736 {_27693 : Type'} : (@all (list _27693)) = (@all (list _27693)).
Proof. exact (eq_refl (@all (list _27693))). Qed.
Lemma lem1187737 {_27693 : Type'} : (term29 _27693) = (term29 _27693).
Proof. exact (MK_COMB (@lem1187736 _27693) (@lem1187735 _27693)). Qed.
Lemma lem1187760 {_27693 : Type'} : (term28 _27693) = (term29 _27693).
Proof. exact (TRANS (@lem1187715 _27693) (@lem1187737 _27693)). Qed.
Lemma lem1187761 {_27693 : Type'} : (term29 _27693) = (term28 _27693).
Proof. exact (SYM (@lem1187760 _27693)). Qed.
Lemma lem1187762 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term12 _27693 l l') : term12 _27693 l l'.
Proof. exact (h1). Qed.
Lemma lem1187763 {_27693 : Type'} (h1 : term13 _27693) : term13 _27693.
Proof. exact (h1). Qed.
Lemma lem1187782 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term12 _27693 l l') = (term32 _27693 l l').
Proof. exact (@lem17646 (l = l') ((@List.rev _27693 l) = (@List.rev _27693 l'))). Qed.
Lemma lem1187784 {_27693 : Type'} (l : list _27693) : ((term30 _27693 l) = l) = ((term30 _27693 l) = l).
Proof. exact (eq_refl ((term30 _27693 l) = l)). Qed.
Lemma lem1187785 {_27693 : Type'} : (term31 _27693) = (term31 _27693).
Proof. exact (fun_ext (fun l : list _27693 => @lem1187784 _27693 l)). Qed.
Lemma lem1187786 {_27693 : Type'} : (@all (list _27693)) = (@all (list _27693)).
Proof. exact (eq_refl (@all (list _27693))). Qed.
Lemma lem1187795 {_27693 : Type'} : (term13 _27693) = (term13 _27693).
Proof. exact (MK_COMB (@lem1187786 _27693) (@lem1187785 _27693)). Qed.
Lemma lem1187796 {_27693 : Type'} (h1 : term13 _27693) : term13 _27693.
Proof. exact (EQ_MP (@lem1187795 _27693) (@lem1187763 _27693 h1)). Qed.
Lemma lem1187838 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term12 _27693 l l') : term32 _27693 l l'.
Proof. exact (EQ_MP (@lem1187782 _27693 l l') (@lem1187762 _27693 l l' h1)). Qed.
Lemma lem1187847 {_27693 : Type'} (l : list _27693) : ((term30 _27693 l) = l) = ((term30 _27693 l) = l).
Proof. exact (eq_refl ((term30 _27693 l) = l)). Qed.
Lemma lem1187848 {_27693 : Type'} : (term31 _27693) = (term31 _27693).
Proof. exact (fun_ext (fun l : list _27693 => @lem1187847 _27693 l)). Qed.
Lemma lem1187849 {_27693 : Type'} : (@all (list _27693)) = (@all (list _27693)).
Proof. exact (eq_refl (@all (list _27693))). Qed.
Lemma lem1187850 {_27693 : Type'} : (term13 _27693) = (term13 _27693).
Proof. exact (MK_COMB (@lem1187849 _27693) (@lem1187848 _27693)). Qed.
Lemma lem1187851 {_27693 : Type'} (h1 : term13 _27693) : term13 _27693.
Proof. exact (EQ_MP (@lem1187850 _27693) (@lem1187796 _27693 h1)). Qed.
Lemma lem1187852 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : term33 _27693 l l'.
Proof. exact (h1). Qed.
Lemma lem1187853 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term34 _27693 l l') : term34 _27693 l l'.
Proof. exact (h1). Qed.
Lemma lem1187874 {_27693 : Type'} (l : list _27693) : ((term30 _27693 l) = l) = ((term30 _27693 l) = l).
Proof. exact (eq_refl ((term30 _27693 l) = l)). Qed.
Lemma lem1187875 {_27693 : Type'} : (term31 _27693) = (term31 _27693).
Proof. exact (fun_ext (fun l : list _27693 => @lem1187874 _27693 l)). Qed.
Lemma lem1187876 {_27693 : Type'} : (@all (list _27693)) = (@all (list _27693)).
Proof. exact (eq_refl (@all (list _27693))). Qed.
Lemma lem1187878 {_27693 : Type'} : (term13 _27693) = (term13 _27693).
Proof. exact (MK_COMB (@lem1187876 _27693) (@lem1187875 _27693)). Qed.
Lemma lem1187879 {_27693 : Type'} (h1 : term13 _27693) : term13 _27693.
Proof. exact (EQ_MP (@lem1187878 _27693) (@lem1187851 _27693 h1)). Qed.
Lemma lem1187891 {_27693 : Type'} (_21217 : list _27693) (h1 : term13 _27693) : term35 _27693 _21217.
Proof. exact (@lem1187879 _27693 h1 _21217). Qed.
Lemma lem1187892 {_27693 : Type'} (_21217 : list _27693) : (term35 _27693 _21217) = ((term30 _27693 _21217) = _21217).
Proof. exact (eq_refl (term35 _27693 _21217)). Qed.
Lemma lem1187897 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : l = l'.
Proof. exact (proj1 (@lem1187852 _27693 l l' h1)). Qed.
Lemma lem1187899 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : term36 _27693 l l'.
Proof. exact (proj2 (@lem1187852 _27693 l l' h1)). Qed.
Lemma lem1187903 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term34 _27693 l l') : term37 _27693 l l'.
Proof. exact (proj1 (@lem1187853 _27693 l l' h1)). Qed.
Lemma lem1187934 {_27693 : Type'} (l' : list _27693) : (term38 _27693 l') = (term38 _27693 l').
Proof. exact (eq_refl (term38 _27693 l')). Qed.
Lemma lem1187935 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : (term39 _27693 l' l) = (term40 _27693 l').
Proof. exact (MK_COMB (@lem1187934 _27693 l') (@lem1187897 _27693 l l' h1)). Qed.
Lemma lem1187936 {_27693 : Type'} (l' : list _27693) : (term40 _27693 l') = (term41 _27693 l').
Proof. exact (eq_refl (term40 _27693 l')). Qed.
Lemma lem1187937 {_27693 : Type'} (l' : list _27693) (l : list _27693) : (term42 _27693 l' l) = (term42 _27693 l' l).
Proof. exact (eq_refl (term42 _27693 l' l)). Qed.
Lemma lem1187938 {_27693 : Type'} (l : list _27693) (l' : list _27693) : ((term39 _27693 l' l) = (term40 _27693 l')) = ((term39 _27693 l' l) = (term41 _27693 l')).
Proof. exact (MK_COMB (@lem1187937 _27693 l' l) (@lem1187936 _27693 l')). Qed.
Lemma lem1187939 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term39 _27693 l' l) = (term36 _27693 l l').
Proof. exact (eq_refl (term39 _27693 l' l)). Qed.
Lemma lem1187940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1187941 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term42 _27693 l' l) = (term43 _27693 l l').
Proof. exact (MK_COMB (@lem1187940) (@lem1187939 _27693 l l')). Qed.
Lemma lem1187942 {_27693 : Type'} (l' : list _27693) : (term41 _27693 l') = (term41 _27693 l').
Proof. exact (eq_refl (term41 _27693 l')). Qed.
Lemma lem1187943 {_27693 : Type'} (l : list _27693) (l' : list _27693) : ((term39 _27693 l' l) = (term41 _27693 l')) = ((term36 _27693 l l') = (term41 _27693 l')).
Proof. exact (MK_COMB (@lem1187941 _27693 l l') (@lem1187942 _27693 l')). Qed.
Lemma lem1187944 {_27693 : Type'} (l : list _27693) (l' : list _27693) : ((term39 _27693 l' l) = (term40 _27693 l')) = ((term36 _27693 l l') = (term41 _27693 l')).
Proof. exact (TRANS (@lem1187938 _27693 l l') (@lem1187943 _27693 l l')). Qed.
Lemma lem1187945 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : (term36 _27693 l l') = (term41 _27693 l').
Proof. exact (EQ_MP (@lem1187944 _27693 l l') (@lem1187935 _27693 l l' h1)). Qed.
Lemma lem1187946 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : term41 _27693 l'.
Proof. exact (EQ_MP (@lem1187945 _27693 l l' h1) (@lem1187899 _27693 l l' h1)). Qed.
Lemma lem1187958 {_27693 : Type'} (x : list _27693) : x = x.
Proof. exact (@lem21386 (list _27693) x). Qed.
Lemma lem1187959 {_27693 : Type'} (x : list _27693) : x = x.
Proof. exact (@lem1187958 _27693 x). Qed.
Lemma lem1187960 {_27693 : Type'} (l' : list _27693) : (@List.rev _27693 l') = (@List.rev _27693 l').
Proof. exact (@lem1187959 _27693 (@List.rev _27693 l')). Qed.
Lemma lem1187961 {_27693 : Type'} (l' : list _27693) : term44 _27693 l'.
Proof. exact (fun h0 : term41 _27693 l' => @lem1187960 _27693 l'). Qed.
Lemma lem1187963 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1187964 {_27693 : Type'} (l' : list _27693) : (term44 _27693 l') = ((@List.rev _27693 l') = (@List.rev _27693 l')).
Proof. exact (@lem1187963 ((@List.rev _27693 l') = (@List.rev _27693 l'))). Qed.
Lemma lem1187965 {_27693 : Type'} (l' : list _27693) : (@List.rev _27693 l') = (@List.rev _27693 l').
Proof. exact (EQ_MP (@lem1187964 _27693 l') (@lem1187961 _27693 l')). Qed.
Lemma lem1187968 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1187970 {_27693 : Type'} (l' : list _27693) : (term41 _27693 l') = (term46 _27693 l').
Proof. exact (@lem1187968 ((@List.rev _27693 l') = (@List.rev _27693 l'))). Qed.
Lemma lem1187973 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : term46 _27693 l'.
Proof. exact (EQ_MP (@lem1187970 _27693 l') (@lem1187946 _27693 l l' h1)). Qed.
Lemma lem1187976 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : False.
Proof. exact (@lem1187973 _27693 l l' h1 (@lem1187965 _27693 l')). Qed.
Lemma lem1187977 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : term47.
Proof. exact (fun h0 : ~ False => @lem1187976 _27693 l l' h1). Qed.
Lemma lem1187979 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1187980 : term47 = False.
Proof. exact (@lem1187979 False). Qed.
Lemma lem1187982 {_27693 : Type'} : (@List.rev _27693) = (@List.rev _27693).
Proof. exact (eq_refl (@List.rev _27693)). Qed.
Lemma lem1187983 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) (h1 : _21226 = _21227) : _21226 = _21227.
Proof. exact (h1). Qed.
Lemma lem1187984 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) (h1 : _21226 = _21227) : (@List.rev _27693 _21226) = (@List.rev _27693 _21227).
Proof. exact (MK_COMB (@lem1187982 _27693) (@lem1187983 _27693 _21226 _21227 h1)). Qed.
Lemma lem1187985 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : term48 _27693 _21226 _21227.
Proof. exact (fun h0 : _21226 = _21227 => @lem1187984 _27693 _21226 _21227 h0). Qed.
Lemma lem1187987 (a : Prop) (b : Prop) : (a -> b) = (term49 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1187988 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term48 _27693 _21226 _21227) = (term50 _27693 _21226 _21227).
Proof. exact (@lem1187987 (_21226 = _21227) ((@List.rev _27693 _21226) = (@List.rev _27693 _21227))). Qed.
Lemma lem1187989 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : term50 _27693 _21226 _21227.
Proof. exact (EQ_MP (@lem1187988 _27693 _21226 _21227) (@lem1187985 _27693 _21226 _21227)). Qed.
Lemma lem1187991 {_27693 : Type'} (x : list _27693) (y : list _27693) (z : list _27693) : term51 _27693 x y z.
Proof. exact (@lem21385 (list _27693) x y z). Qed.
Lemma lem1187993 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term34 _27693 l l') : (@List.rev _27693 l) = (@List.rev _27693 l').
Proof. exact (proj2 (@lem1187853 _27693 l l' h1)). Qed.
Lemma lem1187994 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term34 _27693 l l') : term52 _27693 l l'.
Proof. exact (fun h0 : term36 _27693 l l' => @lem1187993 _27693 l l' h1). Qed.
Lemma lem1187996 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1187997 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term52 _27693 l l') = ((@List.rev _27693 l) = (@List.rev _27693 l')).
Proof. exact (@lem1187996 ((@List.rev _27693 l) = (@List.rev _27693 l'))). Qed.
Lemma lem1187998 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term34 _27693 l l') : (@List.rev _27693 l) = (@List.rev _27693 l').
Proof. exact (EQ_MP (@lem1187997 _27693 l l') (@lem1187994 _27693 l l' h1)). Qed.
Lemma lem1188004 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1188005 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term50 _27693 _21226 _21227) = (term53 _27693 _21226 _21227).
Proof. exact (@lem1188004 ((@List.rev _27693 _21226) = (@List.rev _27693 _21227)) (term37 _27693 _21226 _21227)). Qed.
Lemma lem1188015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1188016 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term54 _27693 _21226 _21227) = (term55 _27693 _21226 _21227).
Proof. exact (MK_COMB (@lem1188015) (@lem1188005 _27693 _21226 _21227)). Qed.
Lemma lem1188026 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term53 _27693 _21226 _21227) = (term53 _27693 _21226 _21227).
Proof. exact (eq_refl (term53 _27693 _21226 _21227)). Qed.
Lemma lem1188027 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : ((term50 _27693 _21226 _21227) = (term53 _27693 _21226 _21227)) = ((term53 _27693 _21226 _21227) = (term53 _27693 _21226 _21227)).
Proof. exact (MK_COMB (@lem1188016 _27693 _21226 _21227) (@lem1188026 _27693 _21226 _21227)). Qed.
Lemma lem1188029 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1188030 (x : Prop) : (x = x) = True.
Proof. exact (@lem1188029 Prop x). Qed.
Lemma lem1188031 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : ((term53 _27693 _21226 _21227) = (term53 _27693 _21226 _21227)) = True.
Proof. exact (@lem1188030 (term53 _27693 _21226 _21227)). Qed.
Lemma lem1188032 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : ((term50 _27693 _21226 _21227) = (term53 _27693 _21226 _21227)) = True.
Proof. exact (TRANS (@lem1188027 _27693 _21226 _21227) (@lem1188031 _27693 _21226 _21227)). Qed.
Lemma lem1188033 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : True = ((term50 _27693 _21226 _21227) = (term53 _27693 _21226 _21227)).
Proof. exact (SYM (@lem1188032 _27693 _21226 _21227)). Qed.
Lemma lem1188034 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term50 _27693 _21226 _21227) = (term53 _27693 _21226 _21227).
Proof. exact (EQ_MP (@lem1188033 _27693 _21226 _21227) (@lem0)). Qed.
Lemma lem1188035 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : term53 _27693 _21226 _21227.
Proof. exact (EQ_MP (@lem1188034 _27693 _21226 _21227) (@lem1187989 _27693 _21226 _21227)). Qed.
Lemma lem1188037 (b : Prop) (a : Prop) : (a \/ b) = (term56 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1188038 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term53 _27693 _21226 _21227) = (term57 _27693 _21226 _21227).
Proof. exact (@lem1188037 (term37 _27693 _21226 _21227) ((@List.rev _27693 _21226) = (@List.rev _27693 _21227))). Qed.
Lemma lem1188040 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1188041 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term59 _27693 _21226 _21227) = (_21226 = _21227).
Proof. exact (@lem1188040 (_21226 = _21227)). Qed.
Lemma lem1188042 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1188043 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term60 _27693 _21226 _21227) = (term61 _27693 _21226 _21227).
Proof. exact (MK_COMB (@lem1188042) (@lem1188041 _27693 _21226 _21227)). Qed.
Lemma lem1188044 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : ((@List.rev _27693 _21226) = (@List.rev _27693 _21227)) = ((@List.rev _27693 _21226) = (@List.rev _27693 _21227)).
Proof. exact (eq_refl ((@List.rev _27693 _21226) = (@List.rev _27693 _21227))). Qed.
Lemma lem1188045 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term57 _27693 _21226 _21227) = (term48 _27693 _21226 _21227).
Proof. exact (MK_COMB (@lem1188043 _27693 _21226 _21227) (@lem1188044 _27693 _21226 _21227)). Qed.
Lemma lem1188046 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : (term53 _27693 _21226 _21227) = (term48 _27693 _21226 _21227).
Proof. exact (TRANS (@lem1188038 _27693 _21226 _21227) (@lem1188045 _27693 _21226 _21227)). Qed.
Lemma lem1188049 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : term48 _27693 _21226 _21227.
Proof. exact (EQ_MP (@lem1188046 _27693 _21226 _21227) (@lem1188035 _27693 _21226 _21227)). Qed.
Lemma lem1188050 {_27693 : Type'} (_21226 : list _27693) (_21227 : list _27693) : term48 _27693 _21226 _21227.
Proof. exact (@lem1188049 _27693 _21226 _21227). Qed.
Lemma lem1188051 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term62 _27693 l l'.
Proof. exact (@lem1188050 _27693 (@List.rev _27693 l) (@List.rev _27693 l')). Qed.
Lemma lem1188054 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term34 _27693 l l') : (term30 _27693 l) = (term30 _27693 l').
Proof. exact (@lem1188051 _27693 l l' (@lem1187998 _27693 l l' h1)). Qed.
Lemma lem1188055 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term34 _27693 l l') : term63 _27693 l l'.
Proof. exact (fun h0 : term64 _27693 l l' => @lem1188054 _27693 l l' h1). Qed.
Lemma lem1188057 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1188058 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term63 _27693 l l') = ((term30 _27693 l) = (term30 _27693 l')).
Proof. exact (@lem1188057 ((term30 _27693 l) = (term30 _27693 l'))). Qed.
Lemma lem1188059 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term34 _27693 l l') : (term30 _27693 l) = (term30 _27693 l').
Proof. exact (EQ_MP (@lem1188058 _27693 l l') (@lem1188055 _27693 l l' h1)). Qed.
Lemma lem1188061 {_27693 : Type'} (_21217 : list _27693) (h1 : term13 _27693) : (term30 _27693 _21217) = _21217.
Proof. exact (EQ_MP (@lem1187892 _27693 _21217) (@lem1187891 _27693 _21217 h1)). Qed.
Lemma lem1188062 {_27693 : Type'} (_21217 : list _27693) (h1 : term13 _27693) : (term30 _27693 _21217) = _21217.
Proof. exact (@lem1188061 _27693 _21217 h1). Qed.
Lemma lem1188063 {_27693 : Type'} (l : list _27693) (h1 : term13 _27693) : (term30 _27693 l) = l.
Proof. exact (@lem1188062 _27693 l h1). Qed.
Lemma lem1188064 {_27693 : Type'} (l : list _27693) (h1 : term13 _27693) : term65 _27693 l.
Proof. exact (fun h0 : term66 _27693 l => @lem1188063 _27693 l h1). Qed.
Lemma lem1188066 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1188067 {_27693 : Type'} (l : list _27693) : (term65 _27693 l) = ((term30 _27693 l) = l).
Proof. exact (@lem1188066 ((term30 _27693 l) = l)). Qed.
Lemma lem1188068 {_27693 : Type'} (l : list _27693) (h1 : term13 _27693) : (term30 _27693 l) = l.
Proof. exact (EQ_MP (@lem1188067 _27693 l) (@lem1188064 _27693 l h1)). Qed.
Lemma lem1188086 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1188087 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term67 _27693 x y z) = (term68 _27693 y x z).
Proof. exact (@lem1188086 (y = z) (term37 _27693 x z)). Qed.
Lemma lem1188097 {_27693 : Type'} (x : list _27693) (y : list _27693) : (term69 _27693 x y) = (term69 _27693 x y).
Proof. exact (eq_refl (term69 _27693 x y)). Qed.
Lemma lem1188098 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term51 _27693 x y z) = (term70 _27693 y x z).
Proof. exact (MK_COMB (@lem1188097 _27693 x y) (@lem1188087 _27693 y x z)). Qed.
Lemma lem1188102 (q : Prop) (p : Prop) (r : Prop) : (term71 p q r) = (term71 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1188103 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term70 _27693 y x z) = (term72 _27693 y x z).
Proof. exact (@lem1188102 (y = z) (term37 _27693 x y) (term37 _27693 x z)). Qed.
Lemma lem1188125 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term51 _27693 x y z) = (term72 _27693 y x z).
Proof. exact (TRANS (@lem1188098 _27693 y x z) (@lem1188103 _27693 y x z)). Qed.
Lemma lem1188126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1188127 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term73 _27693 x y z) = (term74 _27693 y x z).
Proof. exact (MK_COMB (@lem1188126) (@lem1188125 _27693 y x z)). Qed.
Lemma lem1188149 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term72 _27693 y x z) = (term72 _27693 y x z).
Proof. exact (eq_refl (term72 _27693 y x z)). Qed.
Lemma lem1188150 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : ((term51 _27693 x y z) = (term72 _27693 y x z)) = ((term72 _27693 y x z) = (term72 _27693 y x z)).
Proof. exact (MK_COMB (@lem1188127 _27693 y x z) (@lem1188149 _27693 y x z)). Qed.
Lemma lem1188152 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1188153 (x : Prop) : (x = x) = True.
Proof. exact (@lem1188152 Prop x). Qed.
Lemma lem1188154 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : ((term72 _27693 y x z) = (term72 _27693 y x z)) = True.
Proof. exact (@lem1188153 (term72 _27693 y x z)). Qed.
Lemma lem1188155 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : ((term51 _27693 x y z) = (term72 _27693 y x z)) = True.
Proof. exact (TRANS (@lem1188150 _27693 y x z) (@lem1188154 _27693 y x z)). Qed.
Lemma lem1188156 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : True = ((term51 _27693 x y z) = (term72 _27693 y x z)).
Proof. exact (SYM (@lem1188155 _27693 y x z)). Qed.
Lemma lem1188157 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term51 _27693 x y z) = (term72 _27693 y x z).
Proof. exact (EQ_MP (@lem1188156 _27693 y x z) (@lem0)). Qed.
Lemma lem1188158 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : term72 _27693 y x z.
Proof. exact (EQ_MP (@lem1188157 _27693 y x z) (@lem1187991 _27693 x y z)). Qed.
Lemma lem1188160 (b : Prop) (a : Prop) : (a \/ b) = (term56 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1188161 {_27693 : Type'} (x : list _27693) (y : list _27693) (z : list _27693) : (term72 _27693 y x z) = (term75 _27693 x y z).
Proof. exact (@lem1188160 (term76 _27693 y x z) (y = z)). Qed.
Lemma lem1188163 (a : Prop) (b : Prop) : (term77 a b) = (term78 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1188164 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term79 _27693 y x z) = (term80 _27693 y x z).
Proof. exact (@lem1188163 (term37 _27693 x y) (term37 _27693 x z)). Qed.
Lemma lem1188166 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1188167 {_27693 : Type'} (x : list _27693) (y : list _27693) : (term59 _27693 x y) = (x = y).
Proof. exact (@lem1188166 (x = y)). Qed.
Lemma lem1188168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1188169 {_27693 : Type'} (x : list _27693) (y : list _27693) : (term81 _27693 x y) = (term82 _27693 x y).
Proof. exact (MK_COMB (@lem1188168) (@lem1188167 _27693 x y)). Qed.
Lemma lem1188171 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1188172 {_27693 : Type'} (x : list _27693) (z : list _27693) : (term59 _27693 x z) = (x = z).
Proof. exact (@lem1188171 (x = z)). Qed.
Lemma lem1188173 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term80 _27693 y x z) = (term83 _27693 y x z).
Proof. exact (MK_COMB (@lem1188169 _27693 x y) (@lem1188172 _27693 x z)). Qed.
Lemma lem1188174 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term79 _27693 y x z) = (term83 _27693 y x z).
Proof. exact (TRANS (@lem1188164 _27693 y x z) (@lem1188173 _27693 y x z)). Qed.
Lemma lem1188175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1188176 {_27693 : Type'} (y : list _27693) (x : list _27693) (z : list _27693) : (term84 _27693 y x z) = (term85 _27693 y x z).
Proof. exact (MK_COMB (@lem1188175) (@lem1188174 _27693 y x z)). Qed.
Lemma lem1188177 {_27693 : Type'} (y : list _27693) (z : list _27693) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1188178 {_27693 : Type'} (x : list _27693) (y : list _27693) (z : list _27693) : (term75 _27693 x y z) = (term86 _27693 x y z).
Proof. exact (MK_COMB (@lem1188176 _27693 y x z) (@lem1188177 _27693 y z)). Qed.
Lemma lem1188179 {_27693 : Type'} (x : list _27693) (y : list _27693) (z : list _27693) : (term72 _27693 y x z) = (term86 _27693 x y z).
Proof. exact (TRANS (@lem1188161 _27693 x y z) (@lem1188178 _27693 x y z)). Qed.
Lemma lem1188181 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : term87 _27693 l' l.
Proof. exact (conj (@lem1188059 _27693 l l' h2) (@lem1188068 _27693 l h1)). Qed.
Lemma lem1188183 {_27693 : Type'} (x : list _27693) (y : list _27693) (z : list _27693) : term86 _27693 x y z.
Proof. exact (EQ_MP (@lem1188179 _27693 x y z) (@lem1188158 _27693 y x z)). Qed.
Lemma lem1188184 {_27693 : Type'} (x : list _27693) (y : list _27693) (z : list _27693) : term86 _27693 x y z.
Proof. exact (@lem1188183 _27693 x y z). Qed.
Lemma lem1188185 {_27693 : Type'} (l' : list _27693) (l : list _27693) : term88 _27693 l' l.
Proof. exact (@lem1188184 _27693 (term30 _27693 l) (term30 _27693 l') l). Qed.
Lemma lem1188188 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : (term30 _27693 l') = l.
Proof. exact (@lem1188185 _27693 l' l (@lem1188181 _27693 l l' h1 h2)). Qed.
Lemma lem1188189 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : term89 _27693 l' l.
Proof. exact (fun h0 : term90 _27693 l' l => @lem1188188 _27693 l l' h1 h2). Qed.
Lemma lem1188191 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1188192 {_27693 : Type'} (l' : list _27693) (l : list _27693) : (term89 _27693 l' l) = ((term30 _27693 l') = l).
Proof. exact (@lem1188191 ((term30 _27693 l') = l)). Qed.
Lemma lem1188193 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : (term30 _27693 l') = l.
Proof. exact (EQ_MP (@lem1188192 _27693 l' l) (@lem1188189 _27693 l l' h1 h2)). Qed.
Lemma lem1188195 {_27693 : Type'} (_21217 : list _27693) (h1 : term13 _27693) : (term30 _27693 _21217) = _21217.
Proof. exact (EQ_MP (@lem1187892 _27693 _21217) (@lem1187891 _27693 _21217 h1)). Qed.
Lemma lem1188196 {_27693 : Type'} (_21217 : list _27693) (h1 : term13 _27693) : (term30 _27693 _21217) = _21217.
Proof. exact (@lem1188195 _27693 _21217 h1). Qed.
Lemma lem1188197 {_27693 : Type'} (l' : list _27693) (h1 : term13 _27693) : (term30 _27693 l') = l'.
Proof. exact (@lem1188196 _27693 l' h1). Qed.
Lemma lem1188198 {_27693 : Type'} (l' : list _27693) (h1 : term13 _27693) : term65 _27693 l'.
Proof. exact (fun h0 : term66 _27693 l' => @lem1188197 _27693 l' h1). Qed.
Lemma lem1188200 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1188201 {_27693 : Type'} (l' : list _27693) : (term65 _27693 l') = ((term30 _27693 l') = l').
Proof. exact (@lem1188200 ((term30 _27693 l') = l')). Qed.
Lemma lem1188202 {_27693 : Type'} (l' : list _27693) (h1 : term13 _27693) : (term30 _27693 l') = l'.
Proof. exact (EQ_MP (@lem1188201 _27693 l') (@lem1188198 _27693 l' h1)). Qed.
Lemma lem1188203 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : term91 _27693 l l'.
Proof. exact (conj (@lem1188193 _27693 l l' h1 h2) (@lem1188202 _27693 l' h1)). Qed.
Lemma lem1188205 {_27693 : Type'} (x : list _27693) (y : list _27693) (z : list _27693) : term86 _27693 x y z.
Proof. exact (EQ_MP (@lem1188179 _27693 x y z) (@lem1188158 _27693 y x z)). Qed.
Lemma lem1188206 {_27693 : Type'} (x : list _27693) (y : list _27693) (z : list _27693) : term86 _27693 x y z.
Proof. exact (@lem1188205 _27693 x y z). Qed.
Lemma lem1188207 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term92 _27693 l l'.
Proof. exact (@lem1188206 _27693 (term30 _27693 l') l l'). Qed.
Lemma lem1188210 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : l = l'.
Proof. exact (@lem1188207 _27693 l l' (@lem1188203 _27693 l l' h1 h2)). Qed.
Lemma lem1188211 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : term93 _27693 l l'.
Proof. exact (fun h0 : term37 _27693 l l' => @lem1188210 _27693 l l' h1 h2). Qed.
Lemma lem1188213 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1188214 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term93 _27693 l l') = (l = l').
Proof. exact (@lem1188213 (l = l')). Qed.
Lemma lem1188215 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : l = l'.
Proof. exact (EQ_MP (@lem1188214 _27693 l l') (@lem1188211 _27693 l l' h1 h2)). Qed.
Lemma lem1188218 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1188220 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term37 _27693 l l') = (term94 _27693 l l').
Proof. exact (@lem1188218 (l = l')). Qed.
Lemma lem1188223 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term34 _27693 l l') : term94 _27693 l l'.
Proof. exact (EQ_MP (@lem1188220 _27693 l l') (@lem1187903 _27693 l l' h1)). Qed.
Lemma lem1188226 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : False.
Proof. exact (@lem1188223 _27693 l l' h2 (@lem1188215 _27693 l l' h1 h2)). Qed.
Lemma lem1188227 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : term47.
Proof. exact (fun h0 : ~ False => @lem1188226 _27693 l l' h1 h2). Qed.
Lemma lem1188229 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1188230 : term47 = False.
Proof. exact (@lem1188229 False). Qed.
Lemma lem1188231 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : False.
Proof. exact (EQ_MP (@lem1188230) (@lem1188227 _27693 l l' h1 h2)). Qed.
Lemma lem1188232 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term33 _27693 l l') : False.
Proof. exact (EQ_MP (@lem1187980) (@lem1187977 _27693 l l' h1)). Qed.
Lemma lem1188233 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : (term13 _27693) = False.
Proof. exact (prop_ext (fun h3 : term13 _27693 => @lem1188231 _27693 l l' h1 h2) (fun h3 : False => @lem1187879 _27693 h1)). Qed.
Lemma lem1188234 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term34 _27693 l l') : False.
Proof. exact (EQ_MP (@lem1188233 _27693 l l' h1 h2) (@lem1187879 _27693 h1)). Qed.
Lemma lem1188235 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term12 _27693 l l') : False.
Proof. exact (or_elim (@lem1187838 _27693 l l' h2) (fun h0 : term33 _27693 l l' => @lem1188232 _27693 l l' h0) (fun h0 : term34 _27693 l l' => @lem1188234 _27693 l l' h1 h0)). Qed.
Lemma lem1188236 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term12 _27693 l l') : (term13 _27693) = False.
Proof. exact (prop_ext (fun h3 : term13 _27693 => @lem1188235 _27693 l l' h1 h2) (fun h3 : False => @lem1187851 _27693 h1)). Qed.
Lemma lem1188237 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term12 _27693 l l') : False.
Proof. exact (EQ_MP (@lem1188236 _27693 l l' h1 h2) (@lem1187851 _27693 h1)). Qed.
Lemma lem1188238 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term12 _27693 l l') : (term13 _27693) = False.
Proof. exact (prop_ext (fun h3 : term13 _27693 => @lem1188237 _27693 l l' h1 h2) (fun h3 : False => @lem1187796 _27693 h1)). Qed.
Lemma lem1188239 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term13 _27693) (h2 : term12 _27693 l l') : False.
Proof. exact (EQ_MP (@lem1188238 _27693 l l' h1 h2) (@lem1187796 _27693 h1)). Qed.
Lemma lem1188240 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term12 _27693 l l') : term18 _27693.
Proof. exact (fun h0 : term13 _27693 => @lem1188239 _27693 l l' h0 h1). Qed.
Lemma lem1188241 {_27693 : Type'} : (term18 _27693) = (term19 _27693).
Proof. exact (@lem69 (term13 _27693)). Qed.
Lemma lem1188242 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term12 _27693 l l') : term19 _27693.
Proof. exact (EQ_MP (@lem1188241 _27693) (@lem1188240 _27693 l l' h1)). Qed.
Lemma lem1188243 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term21 _27693 l l'.
Proof. exact (fun h0 : term12 _27693 l l' => @lem1188242 _27693 l l' h0). Qed.
Lemma lem1188248 {_27693 : Type'} (l' : list _27693) : term25 _27693 l'.
Proof. exact (fun l : list _27693 => @lem1188243 _27693 l l'). Qed.
Lemma lem1188253 {_27693 : Type'} : term29 _27693.
Proof. exact (fun l' : list _27693 => @lem1188248 _27693 l'). Qed.
Lemma lem1188254 {_27693 : Type'} : term28 _27693.
Proof. exact (EQ_MP (@lem1187761 _27693) (@lem1188253 _27693)). Qed.
Lemma lem1188255 {_27693 : Type'} (l' : list _27693) : term95 _27693 l'.
Proof. exact (@lem1188254 _27693 l'). Qed.
Lemma lem1188256 {_27693 : Type'} (l' : list _27693) : (term95 _27693 l') = (term24 _27693 l').
Proof. exact (eq_refl (term95 _27693 l')). Qed.
Lemma lem1188257 {_27693 : Type'} (l' : list _27693) : term24 _27693 l'.
Proof. exact (EQ_MP (@lem1188256 _27693 l') (@lem1188255 _27693 l')). Qed.
Lemma lem1188258 {_27693 : Type'} (l' : list _27693) (l : list _27693) : term96 _27693 l' l.
Proof. exact (@lem1188257 _27693 l' l). Qed.
Lemma lem1188259 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (term96 _27693 l' l) = (term14 _27693 l l').
Proof. exact (eq_refl (term96 _27693 l' l)). Qed.
Lemma lem1188260 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term14 _27693 l l'.
Proof. exact (EQ_MP (@lem1188259 _27693 l l') (@lem1188258 _27693 l' l)). Qed.
Lemma lem1188262 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term14 _27693 l l'.
Proof. exact (@lem1187676 _27693 l l' (@lem1188260 _27693 l l')). Qed.
Lemma lem1188263 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term12 _27693 l l') : term18 _27693.
Proof. exact (@lem1188262 _27693 l l' (@lem1187658 _27693 l l' h1)). Qed.
Lemma lem1188264 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term12 _27693 l l') : False.
Proof. exact (@lem1188263 _27693 l l' h1 (@lem1187659 _27693)). Qed.
Lemma lem1188265 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term12 _27693 l l') : (term12 _27693 l l') = False.
Proof. exact (prop_ext (fun h2 : term12 _27693 l l' => @lem1188264 _27693 l l' h1) (fun h2 : False => @lem1187658 _27693 l l' h1)). Qed.
Lemma lem1188266 {_27693 : Type'} (l : list _27693) (l' : list _27693) (h1 : term12 _27693 l l') : False.
Proof. exact (EQ_MP (@lem1188265 _27693 l l' h1) (@lem1187658 _27693 l l' h1)). Qed.
Lemma lem1188267 {_27693 : Type'} (l : list _27693) (l' : list _27693) : term11 _27693 l l'.
Proof. exact (fun h0 : term12 _27693 l l' => @lem1188266 _27693 l l' h0). Qed.
Lemma lem1188288 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (l = l') = ((@List.rev _27693 l) = (@List.rev _27693 l')).
Proof. exact (EQ_MP (@lem1187657 _27693 l l') (@lem1188267 _27693 l l')). Qed.
Lemma lem1188289 {A : Type'} (l : list A) (l' : list A) : (l = l') = ((@List.rev A l) = (@List.rev A l')).
Proof. exact (@lem1188288 A l l'). Qed.
Lemma lem1188290 {A : Type'} (l1 : list A) (l2 : list A) (l3 : list A) : ((@List.app A l1 l3) = (@List.app A l2 l3)) = ((term8 A l1 l3) = (term8 A l2 l3)).
Proof. exact (@lem1188289 A (@List.app A l1 l3) (@List.app A l2 l3)). Qed.
Lemma lem1188291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1188292 {A : Type'} (l1 : list A) (l2 : list A) (l3 : list A) : (term97 A l1 l2 l3) = (term98 A l1 l2 l3).
Proof. exact (MK_COMB (@lem1188291) (@lem1188290 A l1 l2 l3)). Qed.
Lemma lem1188296 {_27693 : Type'} (l : list _27693) (l' : list _27693) : (l = l') = ((@List.rev _27693 l) = (@List.rev _27693 l')).
Proof. exact (EQ_MP (@lem1187657 _27693 l l') (@lem1188267 _27693 l l')). Qed.
Lemma lem1188297 {A : Type'} (l : list A) (l' : list A) : (l = l') = ((@List.rev A l) = (@List.rev A l')).
Proof. exact (@lem1188296 A l l'). Qed.
Lemma lem1188298 {A : Type'} (l1 : list A) (l2 : list A) : (l1 = l2) = ((@List.rev A l1) = (@List.rev A l2)).
Proof. exact (@lem1188297 A l1 l2). Qed.
Lemma lem1188299 {A : Type'} (l3 : list A) (l1 : list A) (l2 : list A) : (((@List.app A l1 l3) = (@List.app A l2 l3)) = (l1 = l2)) = (((term8 A l1 l3) = (term8 A l2 l3)) = ((@List.rev A l1) = (@List.rev A l2))).
Proof. exact (MK_COMB (@lem1188292 A l1 l2 l3) (@lem1188298 A l1 l2)). Qed.
Lemma lem1188300 {A : Type'} (l1 : list A) (l2 : list A) : (term99 A l1 l2) = (term100 A l1 l2).
Proof. exact (fun_ext (fun l3 : list A => @lem1188299 A l3 l1 l2)). Qed.
Lemma lem1188301 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1188302 {A : Type'} (l1 : list A) (l2 : list A) : (term101 A l1 l2) = (term102 A l1 l2).
Proof. exact (MK_COMB (@lem1188301 A) (@lem1188300 A l1 l2)). Qed.
Lemma lem1188303 {A : Type'} (l1 : list A) : (term103 A l1) = (term104 A l1).
Proof. exact (fun_ext (fun l2 : list A => @lem1188302 A l1 l2)). Qed.
Lemma lem1188304 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1188305 {A : Type'} (l1 : list A) : (term105 A l1) = (term106 A l1).
Proof. exact (MK_COMB (@lem1188304 A) (@lem1188303 A l1)). Qed.
Lemma lem1188306 {A : Type'} : (term107 A) = (term108 A).
Proof. exact (fun_ext (fun l1 : list A => @lem1188305 A l1)). Qed.
Lemma lem1188307 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1188308 {A : Type'} : (term109 A) = (term110 A).
Proof. exact (MK_COMB (@lem1188307 A) (@lem1188306 A)). Qed.
Lemma lem1188309 {A : Type'} : (term110 A) = (term109 A).
Proof. exact (SYM (@lem1188308 A)). Qed.
Lemma lem1188327 {A : Type'} (m : list A) (l : list A) : (term8 A l m) = (term9 A m l).
Proof. exact (EQ_MP (@lem1187642 A m l) (@lem1187641 A l m)). Qed.
Lemma lem1188328 {A : Type'} (m : list A) (l : list A) : (term8 A l m) = (term9 A m l).
Proof. exact (@lem1188327 A m l). Qed.
Lemma lem1188329 {A : Type'} (l3 : list A) (l1 : list A) : (term8 A l1 l3) = (term9 A l3 l1).
Proof. exact (@lem1188328 A l3 l1). Qed.
Lemma lem1188330 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1188331 {A : Type'} (l3 : list A) (l1 : list A) : (term111 A l1 l3) = (term112 A l3 l1).
Proof. exact (MK_COMB (@lem1188330 A) (@lem1188329 A l3 l1)). Qed.
Lemma lem1188333 {A : Type'} (m : list A) (l : list A) : (term8 A l m) = (term9 A m l).
Proof. exact (EQ_MP (@lem1187642 A m l) (@lem1187641 A l m)). Qed.
Lemma lem1188334 {A : Type'} (m : list A) (l : list A) : (term8 A l m) = (term9 A m l).
Proof. exact (@lem1188333 A m l). Qed.
Lemma lem1188335 {A : Type'} (l3 : list A) (l2 : list A) : (term8 A l2 l3) = (term9 A l3 l2).
Proof. exact (@lem1188334 A l3 l2). Qed.
Lemma lem1188336 {A : Type'} (l1 : list A) (l3 : list A) (l2 : list A) : ((term8 A l1 l3) = (term8 A l2 l3)) = ((term9 A l3 l1) = (term9 A l3 l2)).
Proof. exact (MK_COMB (@lem1188331 A l3 l1) (@lem1188335 A l3 l2)). Qed.
Lemma lem1188338 {A : Type'} (l1 : list A) (l2 : list A) (l3 : list A) : ((@List.app A l1 l2) = (@List.app A l1 l3)) = (l2 = l3).
Proof. exact (EQ_MP (@lem1187636 A l1 l2 l3) (@lem1187635 A l1 l2 l3)). Qed.
Lemma lem1188339 {A : Type'} (l1 : list A) (l2 : list A) (l3 : list A) : ((@List.app A l1 l2) = (@List.app A l1 l3)) = (l2 = l3).
Proof. exact (@lem1188338 A l1 l2 l3). Qed.
Lemma lem1188340 {A : Type'} (l3 : list A) (l1 : list A) (l2 : list A) : ((term9 A l3 l1) = (term9 A l3 l2)) = ((@List.rev A l1) = (@List.rev A l2)).
Proof. exact (@lem1188339 A (@List.rev A l3) (@List.rev A l1) (@List.rev A l2)). Qed.
Lemma lem1188343 {A : Type'} (l3 : list A) (l1 : list A) (l2 : list A) : ((term8 A l1 l3) = (term8 A l2 l3)) = ((@List.rev A l1) = (@List.rev A l2)).
Proof. exact (TRANS (@lem1188336 A l1 l3 l2) (@lem1188340 A l3 l1 l2)). Qed.
Lemma lem1188344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1188345 {A : Type'} (l3 : list A) (l1 : list A) (l2 : list A) : (term98 A l1 l2 l3) = (term113 A l1 l2).
Proof. exact (MK_COMB (@lem1188344) (@lem1188343 A l3 l1 l2)). Qed.
Lemma lem1188348 {A : Type'} (l1 : list A) (l2 : list A) : ((@List.rev A l1) = (@List.rev A l2)) = ((@List.rev A l1) = (@List.rev A l2)).
Proof. exact (eq_refl ((@List.rev A l1) = (@List.rev A l2))). Qed.
Lemma lem1188349 {A : Type'} (l3 : list A) (l1 : list A) (l2 : list A) : (((term8 A l1 l3) = (term8 A l2 l3)) = ((@List.rev A l1) = (@List.rev A l2))) = (((@List.rev A l1) = (@List.rev A l2)) = ((@List.rev A l1) = (@List.rev A l2))).
Proof. exact (MK_COMB (@lem1188345 A l3 l1 l2) (@lem1188348 A l1 l2)). Qed.
Lemma lem1188351 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1188352 (x : Prop) : (x = x) = True.
Proof. exact (@lem1188351 Prop x). Qed.
Lemma lem1188353 {A : Type'} (l1 : list A) (l2 : list A) : (((@List.rev A l1) = (@List.rev A l2)) = ((@List.rev A l1) = (@List.rev A l2))) = True.
Proof. exact (@lem1188352 ((@List.rev A l1) = (@List.rev A l2))). Qed.
Lemma lem1188354 {A : Type'} (l3 : list A) (l1 : list A) (l2 : list A) : (((term8 A l1 l3) = (term8 A l2 l3)) = ((@List.rev A l1) = (@List.rev A l2))) = True.
Proof. exact (TRANS (@lem1188349 A l3 l1 l2) (@lem1188353 A l1 l2)). Qed.
Lemma lem1188355 {A : Type'} (l1 : list A) (l2 : list A) : (term100 A l1 l2) = (term114 A).
Proof. exact (fun_ext (fun l3 : list A => @lem1188354 A l3 l1 l2)). Qed.
Lemma lem1188356 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1188357 {A : Type'} (l1 : list A) (l2 : list A) : (term102 A l1 l2) = (term115 A).
Proof. exact (MK_COMB (@lem1188356 A) (@lem1188355 A l1 l2)). Qed.
Lemma lem1188359 {A : Type'} (t : Prop) : (term116 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1188360 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (@lem1188359 (list A) t). Qed.
Lemma lem1188361 {A : Type'} : (term115 A) = True.
Proof. exact (@lem1188360 A True). Qed.
Lemma lem1188362 {A : Type'} (l1 : list A) (l2 : list A) : (term102 A l1 l2) = True.
Proof. exact (TRANS (@lem1188357 A l1 l2) (@lem1188361 A)). Qed.
Lemma lem1188363 {A : Type'} (l1 : list A) : (term104 A l1) = (term114 A).
Proof. exact (fun_ext (fun l2 : list A => @lem1188362 A l1 l2)). Qed.
Lemma lem1188364 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1188365 {A : Type'} (l1 : list A) : (term106 A l1) = (term115 A).
Proof. exact (MK_COMB (@lem1188364 A) (@lem1188363 A l1)). Qed.
Lemma lem1188367 {A : Type'} (t : Prop) : (term116 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1188368 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (@lem1188367 (list A) t). Qed.
Lemma lem1188369 {A : Type'} : (term115 A) = True.
Proof. exact (@lem1188368 A True). Qed.
Lemma lem1188370 {A : Type'} (l1 : list A) : (term106 A l1) = True.
Proof. exact (TRANS (@lem1188365 A l1) (@lem1188369 A)). Qed.
Lemma lem1188371 {A : Type'} : (term108 A) = (term114 A).
Proof. exact (fun_ext (fun l1 : list A => @lem1188370 A l1)). Qed.
Lemma lem1188372 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1188373 {A : Type'} : (term110 A) = (term115 A).
Proof. exact (MK_COMB (@lem1188372 A) (@lem1188371 A)). Qed.
Lemma lem1188375 {A : Type'} (t : Prop) : (term116 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1188376 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (@lem1188375 (list A) t). Qed.
Lemma lem1188377 {A : Type'} : (term115 A) = True.
Proof. exact (@lem1188376 A True). Qed.
Lemma lem1188378 {A : Type'} : (term110 A) = True.
Proof. exact (TRANS (@lem1188373 A) (@lem1188377 A)). Qed.
Lemma lem1188379 {A : Type'} : True = (term110 A).
Proof. exact (SYM (@lem1188378 A)). Qed.
Lemma lem1188380 {A : Type'} : term110 A.
Proof. exact (EQ_MP (@lem1188379 A) (@lem0)). Qed.
Lemma lem1188381 {A : Type'} : term109 A.
Proof. exact (EQ_MP (@lem1188309 A) (@lem1188380 A)). Qed.
