Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_TL_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUC_SUB1_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1097080_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm522778_spec.
Require Import thm523589_spec.
Lemma lem1203022 (n : nat) : term0 n.
Proof. exact (@lem137156 n). Qed.
Lemma lem1203023 (n : nat) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1203037 : term2.
Proof. exact (EQ_MP (@lem522778) (@lem523589)). Qed.
Lemma lem1203038 : term3.
Proof. exact (proj2 (@lem1203037)). Qed.
Lemma lem1203039 : term4.
Proof. exact (proj2 (@lem1203038)). Qed.
Lemma lem1203040 : term5.
Proof. exact (proj2 (@lem1203039)). Qed.
Lemma lem1203082 : term6.
Proof. exact (proj1 (@lem1203040)). Qed.
Lemma lem1203083 (n : nat) : term7 n.
Proof. exact (@lem1203082 n). Qed.
Lemma lem1203084 (n : nat) : (term7 n) = ((term8 n) = 0).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1203091 : term9.
Proof. exact (proj1 (@lem1203037)). Qed.
Lemma lem1203092 (m : nat) : term10 m.
Proof. exact (@lem1203091 m). Qed.
Lemma lem1203093 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem1203094 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1203093 m) (@lem1203092 m)). Qed.
Lemma lem1203095 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem1203094 m n). Qed.
Lemma lem1203096 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1203669 {A : Type'} : term15 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1203670 {A : Type'} (h : A) : term16 A h.
Proof. exact (@lem1203669 A h). Qed.
Lemma lem1203671 {A : Type'} (h : A) : (term16 A h) = (term17 A h).
Proof. exact (eq_refl (term16 A h)). Qed.
Lemma lem1203672 {A : Type'} (h : A) : term17 A h.
Proof. exact (EQ_MP (@lem1203671 A h) (@lem1203670 A h)). Qed.
Lemma lem1203673 {A : Type'} (h : A) (t : list A) : term18 A h t.
Proof. exact (@lem1203672 A h t). Qed.
Lemma lem1203674 {A : Type'} (h : A) (t : list A) : (term18 A h t) = ((term19 A h t) = (term20 A t)).
Proof. exact (eq_refl (term18 A h t)). Qed.
Lemma lem1203678 {A : Type'} (P : type1143 A) : term21 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1203679 {_28117 : Type'} (P : type1143 _28117) : term21 _28117 P.
Proof. exact (@lem1203678 _28117 P). Qed.
Lemma lem1203680 {_28117 : Type'} : term22 _28117.
Proof. exact (@lem1203679 _28117 (term23 _28117)). Qed.
Lemma lem1203681 {_28117 : Type'} : (term24 _28117) = (term25 _28117).
Proof. exact (eq_refl (term24 _28117)). Qed.
Lemma lem1203682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1203683 {_28117 : Type'} : (term26 _28117) = (term27 _28117).
Proof. exact (MK_COMB (@lem1203682) (@lem1203681 _28117)). Qed.
Lemma lem1203684 {_28117 : Type'} (t : list _28117) : (term28 _28117 t) = (term29 _28117 t).
Proof. exact (eq_refl (term28 _28117 t)). Qed.
Lemma lem1203685 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1203686 {_28117 : Type'} (t : list _28117) : (term30 _28117 t) = (term31 _28117 t).
Proof. exact (MK_COMB (@lem1203685) (@lem1203684 _28117 t)). Qed.
Lemma lem1203687 {_28117 : Type'} (h : _28117) (t : list _28117) : (term32 _28117 h t) = (term33 _28117 h t).
Proof. exact (eq_refl (term32 _28117 h t)). Qed.
Lemma lem1203688 {_28117 : Type'} (h : _28117) (t : list _28117) : (term34 _28117 h t) = (term35 _28117 h t).
Proof. exact (MK_COMB (@lem1203686 _28117 t) (@lem1203687 _28117 h t)). Qed.
Lemma lem1203689 {_28117 : Type'} (h : _28117) : (term36 _28117 h) = (term37 _28117 h).
Proof. exact (fun_ext (fun t : list _28117 => @lem1203688 _28117 h t)). Qed.
Lemma lem1203690 {_28117 : Type'} : (@all (list _28117)) = (@all (list _28117)).
Proof. exact (eq_refl (@all (list _28117))). Qed.
Lemma lem1203691 {_28117 : Type'} (h : _28117) : (term38 _28117 h) = (term39 _28117 h).
Proof. exact (MK_COMB (@lem1203690 _28117) (@lem1203689 _28117 h)). Qed.
Lemma lem1203692 {_28117 : Type'} : (term40 _28117) = (term41 _28117).
Proof. exact (fun_ext (fun h : _28117 => @lem1203691 _28117 h)). Qed.
Lemma lem1203693 {_28117 : Type'} : (@all _28117) = (@all _28117).
Proof. exact (eq_refl (@all _28117)). Qed.
Lemma lem1203694 {_28117 : Type'} : (term42 _28117) = (term43 _28117).
Proof. exact (MK_COMB (@lem1203693 _28117) (@lem1203692 _28117)). Qed.
Lemma lem1203695 {_28117 : Type'} : (term44 _28117) = (term45 _28117).
Proof. exact (MK_COMB (@lem1203683 _28117) (@lem1203694 _28117)). Qed.
Lemma lem1203696 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1203697 {_28117 : Type'} : (term46 _28117) = (term47 _28117).
Proof. exact (MK_COMB (@lem1203696) (@lem1203695 _28117)). Qed.
Lemma lem1203698 {_28117 : Type'} (l : list _28117) : (term28 _28117 l) = (term29 _28117 l).
Proof. exact (eq_refl (term28 _28117 l)). Qed.
Lemma lem1203699 {_28117 : Type'} : (term48 _28117) = (term23 _28117).
Proof. exact (fun_ext (fun l : list _28117 => @lem1203698 _28117 l)). Qed.
Lemma lem1203700 {_28117 : Type'} : (@all (list _28117)) = (@all (list _28117)).
Proof. exact (eq_refl (@all (list _28117))). Qed.
Lemma lem1203701 {_28117 : Type'} : (term49 _28117) = (term50 _28117).
Proof. exact (MK_COMB (@lem1203700 _28117) (@lem1203699 _28117)). Qed.
Lemma lem1203702 {_28117 : Type'} : (term22 _28117) = (term51 _28117).
Proof. exact (MK_COMB (@lem1203697 _28117) (@lem1203701 _28117)). Qed.
Lemma lem1203703 {_28117 : Type'} : term51 _28117.
Proof. exact (EQ_MP (@lem1203702 _28117) (@lem1203680 _28117)). Qed.
Lemma lem1203708 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1203709 {_28117 : Type'} (x : list _28117) : (x = x) = True.
Proof. exact (@lem1203708 (list _28117) x). Qed.
Lemma lem1203710 {_28117 : Type'} : ((@nil _28117) = (@nil _28117)) = True.
Proof. exact (@lem1203709 _28117 (@nil _28117)). Qed.
Lemma lem1203711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1203712 {_28117 : Type'} : (term52 _28117) = (~ True).
Proof. exact (MK_COMB (@lem1203711) (@lem1203710 _28117)). Qed.
Lemma lem1203714 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1203715 {_28117 : Type'} : (term52 _28117) = False.
Proof. exact (TRANS (@lem1203712 _28117) (@lem1203714)). Qed.
Lemma lem1203716 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1203717 {_28117 : Type'} : (term53 _28117) = (imp False).
Proof. exact (MK_COMB (@lem1203716) (@lem1203715 _28117)). Qed.
Lemma lem1203721 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1203722 {_28117 : Type'} : (@List.length _28117 (@nil _28117)) = (NUMERAL 0).
Proof. exact (@lem1203721 _28117). Qed.
Lemma lem1203723 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem1203724 {_28117 : Type'} : (term54 _28117) = term55.
Proof. exact (MK_COMB (@lem1203723) (@lem1203722 _28117)). Qed.
Lemma lem1203725 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem1203726 {_28117 : Type'} : (term57 _28117) = term58.
Proof. exact (MK_COMB (@lem1203724 _28117) (@lem1203725)). Qed.
Lemma lem1203728 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem1203096 m n) (@lem1203095 m n)). Qed.
Lemma lem1203729 : term58 = term59.
Proof. exact (@lem1203728 0 (BIT1 0)). Qed.
Lemma lem1203731 (n : nat) : (term8 n) = 0.
Proof. exact (EQ_MP (@lem1203084 n) (@lem1203083 n)). Qed.
Lemma lem1203732 : term60 = 0.
Proof. exact (@lem1203731 0). Qed.
Lemma lem1203733 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1203734 : term59 = (NUMERAL 0).
Proof. exact (MK_COMB (@lem1203733) (@lem1203732)). Qed.
Lemma lem1203735 : term58 = (NUMERAL 0).
Proof. exact (TRANS (@lem1203729) (@lem1203734)). Qed.
Lemma lem1203736 {_28117 : Type'} : (term57 _28117) = (NUMERAL 0).
Proof. exact (TRANS (@lem1203726 _28117) (@lem1203735)). Qed.
Lemma lem1203737 {_28117 : Type'} : (term61 _28117) = (term61 _28117).
Proof. exact (eq_refl (term61 _28117)). Qed.
Lemma lem1203738 {_28117 : Type'} : ((term62 _28117) = (term57 _28117)) = ((term62 _28117) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1203737 _28117) (@lem1203736 _28117)). Qed.
Lemma lem1203741 {_28117 : Type'} : (term25 _28117) = (term63 _28117).
Proof. exact (MK_COMB (@lem1203717 _28117) (@lem1203738 _28117)). Qed.
Lemma lem1203743 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1203744 {_28117 : Type'} : (term63 _28117) = True.
Proof. exact (@lem1203743 ((term62 _28117) = (NUMERAL 0))). Qed.
Lemma lem1203745 {_28117 : Type'} : (term25 _28117) = True.
Proof. exact (TRANS (@lem1203741 _28117) (@lem1203744 _28117)). Qed.
Lemma lem1203746 {_28117 : Type'} : True = (term25 _28117).
Proof. exact (SYM (@lem1203745 _28117)). Qed.
Lemma lem1203747 {_28117 : Type'} : term25 _28117.
Proof. exact (EQ_MP (@lem1203746 _28117) (@lem0)). Qed.
Lemma lem1203755 {A : Type'} (h : A) (t : list A) : (term64 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1203756 {_28117 : Type'} (h : _28117) (t : list _28117) : (term64 _28117 h t) = t.
Proof. exact (@lem1203755 _28117 h t). Qed.
Lemma lem1203757 {_28117 : Type'} : (@List.length _28117) = (@List.length _28117).
Proof. exact (eq_refl (@List.length _28117)). Qed.
Lemma lem1203758 {_28117 : Type'} (h : _28117) (t : list _28117) : (term65 _28117 h t) = (@List.length _28117 t).
Proof. exact (MK_COMB (@lem1203757 _28117) (@lem1203756 _28117 h t)). Qed.
Lemma lem1203759 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1203760 {_28117 : Type'} (h : _28117) (t : list _28117) : (term66 _28117 h t) = (term67 _28117 t).
Proof. exact (MK_COMB (@lem1203759) (@lem1203758 _28117 h t)). Qed.
Lemma lem1203762 {A : Type'} (h : A) (t : list A) : (term19 A h t) = (term20 A t).
Proof. exact (EQ_MP (@lem1203674 A h t) (@lem1203673 A h t)). Qed.
Lemma lem1203763 {_28117 : Type'} (h : _28117) (t : list _28117) : (term19 _28117 h t) = (term20 _28117 t).
Proof. exact (@lem1203762 _28117 h t). Qed.
Lemma lem1203764 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem1203765 {_28117 : Type'} (h : _28117) (t : list _28117) : (term68 _28117 h t) = (term69 _28117 t).
Proof. exact (MK_COMB (@lem1203764) (@lem1203763 _28117 h t)). Qed.
Lemma lem1203766 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem1203767 {_28117 : Type'} (h : _28117) (t : list _28117) : (term70 _28117 h t) = (term71 _28117 t).
Proof. exact (MK_COMB (@lem1203765 _28117 h t) (@lem1203766)). Qed.
Lemma lem1203769 (n : nat) : (term1 n) = n.
Proof. exact (EQ_MP (@lem1203023 n) (@lem1203022 n)). Qed.
Lemma lem1203770 {_28117 : Type'} (t : list _28117) : (term71 _28117 t) = (@List.length _28117 t).
Proof. exact (@lem1203769 (@List.length _28117 t)). Qed.
Lemma lem1203771 {_28117 : Type'} (h : _28117) (t : list _28117) : (term70 _28117 h t) = (@List.length _28117 t).
Proof. exact (TRANS (@lem1203767 _28117 h t) (@lem1203770 _28117 t)). Qed.
Lemma lem1203772 {_28117 : Type'} (h : _28117) (t : list _28117) : ((term65 _28117 h t) = (term70 _28117 h t)) = ((@List.length _28117 t) = (@List.length _28117 t)).
Proof. exact (MK_COMB (@lem1203760 _28117 h t) (@lem1203771 _28117 h t)). Qed.
Lemma lem1203774 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1203775 (x : nat) : (x = x) = True.
Proof. exact (@lem1203774 nat x). Qed.
Lemma lem1203776 {_28117 : Type'} (t : list _28117) : ((@List.length _28117 t) = (@List.length _28117 t)) = True.
Proof. exact (@lem1203775 (@List.length _28117 t)). Qed.
Lemma lem1203777 {_28117 : Type'} (h : _28117) (t : list _28117) : ((term65 _28117 h t) = (term70 _28117 h t)) = True.
Proof. exact (TRANS (@lem1203772 _28117 h t) (@lem1203776 _28117 t)). Qed.
Lemma lem1203778 {_28117 : Type'} (h : _28117) (t : list _28117) : (term72 _28117 h t) = (term72 _28117 h t).
Proof. exact (eq_refl (term72 _28117 h t)). Qed.
Lemma lem1203779 {_28117 : Type'} (h : _28117) (t : list _28117) : (term33 _28117 h t) = (term73 _28117 h t).
Proof. exact (MK_COMB (@lem1203778 _28117 h t) (@lem1203777 _28117 h t)). Qed.
Lemma lem1203781 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1203782 {_28117 : Type'} (h : _28117) (t : list _28117) : (term73 _28117 h t) = True.
Proof. exact (@lem1203781 (term74 _28117 h t)). Qed.
Lemma lem1203783 {_28117 : Type'} (h : _28117) (t : list _28117) : (term33 _28117 h t) = True.
Proof. exact (TRANS (@lem1203779 _28117 h t) (@lem1203782 _28117 h t)). Qed.
Lemma lem1203784 {_28117 : Type'} (h : _28117) (t : list _28117) : True = (term33 _28117 h t).
Proof. exact (SYM (@lem1203783 _28117 h t)). Qed.
Lemma lem1203785 {_28117 : Type'} (h : _28117) (t : list _28117) : term33 _28117 h t.
Proof. exact (EQ_MP (@lem1203784 _28117 h t) (@lem0)). Qed.
Lemma lem1203786 {_28117 : Type'} (h : _28117) (t : list _28117) : term35 _28117 h t.
Proof. exact (fun h0 : term29 _28117 t => @lem1203785 _28117 h t). Qed.
Lemma lem1203791 {_28117 : Type'} (h : _28117) : term39 _28117 h.
Proof. exact (fun t : list _28117 => @lem1203786 _28117 h t). Qed.
Lemma lem1203796 {_28117 : Type'} : term43 _28117.
Proof. exact (fun h : _28117 => @lem1203791 _28117 h). Qed.
Lemma lem1203797 {_28117 : Type'} : term45 _28117.
Proof. exact (conj (@lem1203747 _28117) (@lem1203796 _28117)). Qed.
Lemma lem1203798 {_28117 : Type'} : term50 _28117.
Proof. exact (@lem1203703 _28117 (@lem1203797 _28117)). Qed.
