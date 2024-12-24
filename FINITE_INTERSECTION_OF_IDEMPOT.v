Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INTERSECTION_OF_IDEMPOT_term_abbrevs.
Require Import COMPL_COMPL_spec.
Require Import ETA_AX_spec.
Require Import FINITE_INTERSECTION_OF_COMPLEMENT_spec.
Require Import FINITE_UNION_OF_IDEMPOT_spec.
Require Import FUN_EQ_THM_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4886668 {A : Type'} (P : type686 A) : term0 A P.
Proof. exact (@lem4886667 A P). Qed.
Lemma lem4886669 {A : Type'} (P : type686 A) : (term0 A P) = ((term1 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P)).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4886673 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term2 A B f g)) : (f = g) = (term2 A B f g).
Proof. exact (h1). Qed.
Lemma lem4886674 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term2 A B f g)) : (term2 A B f g) = (f = g).
Proof. exact (SYM (@lem4886673 A B f g h1)). Qed.
Lemma lem4886675 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term2 A B f g) = (f = g)) : (term2 A B f g) = (f = g).
Proof. exact (h1). Qed.
Lemma lem4886676 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term2 A B f g) = (f = g)) : (f = g) = (term2 A B f g).
Proof. exact (SYM (@lem4886675 A B f g h1)). Qed.
Lemma lem4886677 {A B : Type'} (f : A -> B) (g : A -> B) : ((f = g) = (term2 A B f g)) = ((term2 A B f g) = (f = g)).
Proof. exact (prop_ext (fun h1 : (f = g) = (term2 A B f g) => @lem4886674 A B f g h1) (fun h1 : (term2 A B f g) = (f = g) => @lem4886676 A B f g h1)). Qed.
Lemma lem4886678 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (fun_ext (fun g : A -> B => @lem4886677 A B f g)). Qed.
Lemma lem4886679 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4886680 {A B : Type'} (f : A -> B) : (term5 A B f) = (term6 A B f).
Proof. exact (MK_COMB (@lem4886679 A B) (@lem4886678 A B f)). Qed.
Lemma lem4886681 {A B : Type'} : (term7 A B) = (term8 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4886680 A B f)). Qed.
Lemma lem4886682 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4886683 {A B : Type'} : (term9 A B) = (term10 A B).
Proof. exact (MK_COMB (@lem4886682 A B) (@lem4886681 A B)). Qed.
Lemma lem4886684 {A B : Type'} : term10 A B.
Proof. exact (EQ_MP (@lem4886683 A B) (@lem9220 A B)). Qed.
Lemma lem4886685 {A B : Type'} (t : A -> B) : term11 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem4886686 {A B : Type'} (t : A -> B) : (term11 A B t) = ((term12 A B t) = t).
Proof. exact (eq_refl (term11 A B t)). Qed.
Lemma lem4886687 {A B : Type'} (t : A -> B) : (term12 A B t) = t.
Proof. exact (EQ_MP (@lem4886686 A B t) (@lem4886685 A B t)). Qed.
Lemma lem4886688 {A B : Type'} (f : A -> B) : term13 A B f.
Proof. exact (@lem4886684 A B f). Qed.
Lemma lem4886689 {A B : Type'} (f : A -> B) : (term13 A B f) = (term6 A B f).
Proof. exact (eq_refl (term13 A B f)). Qed.
Lemma lem4886690 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (EQ_MP (@lem4886689 A B f) (@lem4886688 A B f)). Qed.
Lemma lem4886691 {A B : Type'} (f : A -> B) (g : A -> B) : term14 A B f g.
Proof. exact (@lem4886690 A B f g). Qed.
Lemma lem4886692 {A B : Type'} (f : A -> B) (g : A -> B) : (term14 A B f g) = ((term2 A B f g) = (f = g)).
Proof. exact (eq_refl (term14 A B f g)). Qed.
Lemma lem4886699 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = (f = g).
Proof. exact (EQ_MP (@lem4886692 A B f g) (@lem4886691 A B f g)). Qed.
Lemma lem4886700 {A : Type'} (f : type686 A) (g : type686 A) : (term15 A f g) = (f = g).
Proof. exact (@lem4886699 (A -> Prop) Prop f g). Qed.
Lemma lem4886701 {A : Type'} (P : type686 A) : (term16 A P) = ((term17 A P) = (term18 A P)).
Proof. exact (@lem4886700 A (term17 A P) (term18 A P)). Qed.
Lemma lem4886702 {A : Type'} (P : type686 A) (s : A -> Prop) : (term19 A P s) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s).
Proof. exact (eq_refl (term19 A P s)). Qed.
Lemma lem4886703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4886704 {A : Type'} (P : type686 A) (s : A -> Prop) : (term20 A P s) = (term21 A P s).
Proof. exact (MK_COMB (@lem4886703) (@lem4886702 A P s)). Qed.
Lemma lem4886705 {A : Type'} (P : type686 A) (s : A -> Prop) : (term22 A P s) = (term23 A P s).
Proof. exact (eq_refl (term22 A P s)). Qed.
Lemma lem4886706 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term19 A P s) = (term22 A P s)) = ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term23 A P s)).
Proof. exact (MK_COMB (@lem4886704 A P s) (@lem4886705 A P s)). Qed.
Lemma lem4886707 {A : Type'} (P : type686 A) : (term24 A P) = (term25 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4886706 A P s)). Qed.
Lemma lem4886708 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4886709 {A : Type'} (P : type686 A) : (term16 A P) = (term26 A P).
Proof. exact (MK_COMB (@lem4886708 A) (@lem4886707 A P)). Qed.
Lemma lem4886710 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4886711 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (MK_COMB (@lem4886710) (@lem4886709 A P)). Qed.
Lemma lem4886712 {A : Type'} (P : type686 A) : ((term17 A P) = (term18 A P)) = ((term17 A P) = (term18 A P)).
Proof. exact (eq_refl ((term17 A P) = (term18 A P))). Qed.
Lemma lem4886713 {A : Type'} (P : type686 A) : ((term16 A P) = ((term17 A P) = (term18 A P))) = ((term26 A P) = ((term17 A P) = (term18 A P))).
Proof. exact (MK_COMB (@lem4886711 A P) (@lem4886712 A P)). Qed.
Lemma lem4886714 {A : Type'} (P : type686 A) : (term26 A P) = ((term17 A P) = (term18 A P)).
Proof. exact (EQ_MP (@lem4886713 A P) (@lem4886701 A P)). Qed.
Lemma lem4886717 {A : Type'} (t : type686 A) : (term29 A t) = t.
Proof. exact (@lem4886687 (A -> Prop) Prop t). Qed.
Lemma lem4886718 {A : Type'} (P : type686 A) : (term17 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (@lem4886717 A (@INTERSECTION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4886719 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4886720 {A : Type'} (P : type686 A) : (term30 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4886719 A) (@lem4886718 A P)). Qed.
Lemma lem4886721 {A : Type'} (P : type686 A) : (term18 A P) = (term18 A P).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem4886722 {A : Type'} (P : type686 A) : ((term17 A P) = (term18 A P)) = ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4886720 A P) (@lem4886721 A P)). Qed.
Lemma lem4886725 {A : Type'} (P : type686 A) : (term26 A P) = ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term18 A P)).
Proof. exact (TRANS (@lem4886714 A P) (@lem4886722 A P)). Qed.
Lemma lem4886726 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4886725 A P)). Qed.
Lemma lem4886727 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4886728 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (MK_COMB (@lem4886727 A) (@lem4886726 A)). Qed.
Lemma lem4886730 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = (f = g).
Proof. exact (EQ_MP (@lem4886692 A B f g) (@lem4886691 A B f g)). Qed.
Lemma lem4886731 {A : Type'} (f : type174 A) (g : type174 A) : (term36 A f g) = (f = g).
Proof. exact (@lem4886730 (type686 A) (type686 A) f g). Qed.
Lemma lem4886732 {A : Type'} : (term37 A) = ((term38 A) = (term39 A)).
Proof. exact (@lem4886731 A (term38 A) (term39 A)). Qed.
Lemma lem4886733 {A : Type'} (P : type686 A) : (term40 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (eq_refl (term40 A P)). Qed.
Lemma lem4886734 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4886735 {A : Type'} (P : type686 A) : (term41 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4886734 A) (@lem4886733 A P)). Qed.
Lemma lem4886736 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4886737 {A : Type'} (P : type686 A) : ((term40 A P) = (term42 A P)) = ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4886735 A P) (@lem4886736 A P)). Qed.
Lemma lem4886738 {A : Type'} : (term43 A) = (term33 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4886737 A P)). Qed.
Lemma lem4886739 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4886740 {A : Type'} : (term37 A) = (term35 A).
Proof. exact (MK_COMB (@lem4886739 A) (@lem4886738 A)). Qed.
Lemma lem4886741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4886742 {A : Type'} : (term44 A) = (term45 A).
Proof. exact (MK_COMB (@lem4886741) (@lem4886740 A)). Qed.
Lemma lem4886743 {A : Type'} : ((term38 A) = (term39 A)) = ((term38 A) = (term39 A)).
Proof. exact (eq_refl ((term38 A) = (term39 A))). Qed.
Lemma lem4886744 {A : Type'} : ((term37 A) = ((term38 A) = (term39 A))) = ((term35 A) = ((term38 A) = (term39 A))).
Proof. exact (MK_COMB (@lem4886742 A) (@lem4886743 A)). Qed.
Lemma lem4886745 {A : Type'} : (term35 A) = ((term38 A) = (term39 A)).
Proof. exact (EQ_MP (@lem4886744 A) (@lem4886732 A)). Qed.
Lemma lem4886748 {A : Type'} (t : type174 A) : (term46 A t) = t.
Proof. exact (@lem4886687 (type686 A) (type686 A) t). Qed.
Lemma lem4886749 {A : Type'} : (term38 A) = (@INTERSECTION_OF A (@FINITE (A -> Prop))).
Proof. exact (@lem4886748 A (@INTERSECTION_OF A (@FINITE (A -> Prop)))). Qed.
Lemma lem4886750 {A : Type'} : (@eq (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop)) = (@eq (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4886751 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (MK_COMB (@lem4886750 A) (@lem4886749 A)). Qed.
Lemma lem4886752 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (eq_refl (term39 A)). Qed.
Lemma lem4886753 {A : Type'} : ((term38 A) = (term39 A)) = ((@INTERSECTION_OF A (@FINITE (A -> Prop))) = (term39 A)).
Proof. exact (MK_COMB (@lem4886751 A) (@lem4886752 A)). Qed.
Lemma lem4886756 {A : Type'} : (term35 A) = ((@INTERSECTION_OF A (@FINITE (A -> Prop))) = (term39 A)).
Proof. exact (TRANS (@lem4886745 A) (@lem4886753 A)). Qed.
Lemma lem4886757 {A : Type'} : (term34 A) = ((@INTERSECTION_OF A (@FINITE (A -> Prop))) = (term39 A)).
Proof. exact (TRANS (@lem4886728 A) (@lem4886756 A)). Qed.
Lemma lem4886759 {A B : Type'} (t : A -> B) : term11 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem4886760 {A B : Type'} (t : A -> B) : (term11 A B t) = ((term12 A B t) = t).
Proof. exact (eq_refl (term11 A B t)). Qed.
Lemma lem4886761 {A B : Type'} (t : A -> B) : (term12 A B t) = t.
Proof. exact (EQ_MP (@lem4886760 A B t) (@lem4886759 A B t)). Qed.
Lemma lem4886762 {A : Type'} (s : A -> Prop) : term49 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4886763 {A : Type'} (s : A -> Prop) : (term49 A s) = ((term50 A s) = s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem4886772 {A : Type'} : (@INTERSECTION_OF A (@FINITE (A -> Prop))) = (term39 A).
Proof. exact (EQ_MP (@lem4886757 A) (@lem4879380 A)). Qed.
Lemma lem4886774 {A : Type'} : (@INTERSECTION_OF A (@FINITE (A -> Prop))) = (term39 A).
Proof. exact (EQ_MP (@lem4886757 A) (@lem4879380 A)). Qed.
Lemma lem4886775 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4886776 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term42 A P).
Proof. exact (MK_COMB (@lem4886774 A) (@lem4886775 A P)). Qed.
Lemma lem4886778 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4886779 {A : Type'} (f : type174 A) (y : type686 A) : (term52 A f y) = (f y).
Proof. exact (@lem4886778 (type686 A) (type686 A) f y). Qed.
Lemma lem4886780 {A : Type'} (P : type686 A) : (term53 A P) = (term42 A P).
Proof. exact (@lem4886779 A (term39 A) P). Qed.
Lemma lem4886781 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4886782 {A : Type'} : (term54 A) = (term39 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4886781 A P)). Qed.
Lemma lem4886783 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4886784 {A : Type'} (P : type686 A) : (term53 A P) = (term42 A P).
Proof. exact (MK_COMB (@lem4886782 A) (@lem4886783 A P)). Qed.
Lemma lem4886785 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4886786 {A : Type'} (P : type686 A) : (term55 A P) = (term56 A P).
Proof. exact (MK_COMB (@lem4886785 A) (@lem4886784 A P)). Qed.
Lemma lem4886787 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4886788 {A : Type'} (P : type686 A) : ((term53 A P) = (term42 A P)) = ((term42 A P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4886786 A P) (@lem4886787 A P)). Qed.
Lemma lem4886789 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (EQ_MP (@lem4886788 A P) (@lem4886780 A P)). Qed.
Lemma lem4886790 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term18 A P).
Proof. exact (TRANS (@lem4886776 A P) (@lem4886789 A P)). Qed.
Lemma lem4886791 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (MK_COMB (@lem4886772 A) (@lem4886790 A P)). Qed.
Lemma lem4886793 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4886794 {A : Type'} (f : type174 A) (y : type686 A) : (term52 A f y) = (f y).
Proof. exact (@lem4886793 (type686 A) (type686 A) f y). Qed.
Lemma lem4886795 {A : Type'} (P : type686 A) : (term59 A P) = (term58 A P).
Proof. exact (@lem4886794 A (term39 A) (term18 A P)). Qed.
Lemma lem4886796 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4886797 {A : Type'} : (term54 A) = (term39 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4886796 A P)). Qed.
Lemma lem4886798 {A : Type'} (P : type686 A) : (term18 A P) = (term18 A P).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem4886799 {A : Type'} (P : type686 A) : (term59 A P) = (term58 A P).
Proof. exact (MK_COMB (@lem4886797 A) (@lem4886798 A P)). Qed.
Lemma lem4886800 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4886801 {A : Type'} (P : type686 A) : (term60 A P) = (term61 A P).
Proof. exact (MK_COMB (@lem4886800 A) (@lem4886799 A P)). Qed.
Lemma lem4886802 {A : Type'} (P : type686 A) : (term58 A P) = (term62 A P).
Proof. exact (eq_refl (term58 A P)). Qed.
Lemma lem4886803 {A : Type'} (P : type686 A) : ((term59 A P) = (term58 A P)) = ((term58 A P) = (term62 A P)).
Proof. exact (MK_COMB (@lem4886801 A P) (@lem4886802 A P)). Qed.
Lemma lem4886804 {A : Type'} (P : type686 A) : (term58 A P) = (term62 A P).
Proof. exact (EQ_MP (@lem4886803 A P) (@lem4886795 A P)). Qed.
Lemma lem4886806 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4886807 {A : Type'} (f : type686 A) (y : A -> Prop) : (term63 A f y) = (f y).
Proof. exact (@lem4886806 (A -> Prop) Prop f y). Qed.
Lemma lem4886808 {A : Type'} (P : type686 A) (s : A -> Prop) : (term64 A P s) = (term65 A P s).
Proof. exact (@lem4886807 A (term18 A P) (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4886809 {A : Type'} (P : type686 A) (s : A -> Prop) : (term22 A P s) = (term23 A P s).
Proof. exact (eq_refl (term22 A P s)). Qed.
Lemma lem4886810 {A : Type'} (P : type686 A) : (term66 A P) = (term18 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4886809 A P s)). Qed.
Lemma lem4886811 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4886812 {A : Type'} (P : type686 A) (s : A -> Prop) : (term64 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4886810 A P) (@lem4886811 A s)). Qed.
Lemma lem4886813 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4886814 {A : Type'} (P : type686 A) (s : A -> Prop) : (term67 A P s) = (term68 A P s).
Proof. exact (MK_COMB (@lem4886813) (@lem4886812 A P s)). Qed.
Lemma lem4886815 {A : Type'} (P : type686 A) (s : A -> Prop) : (term65 A P s) = (term69 A P s).
Proof. exact (eq_refl (term65 A P s)). Qed.
Lemma lem4886816 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term64 A P s) = (term65 A P s)) = ((term65 A P s) = (term69 A P s)).
Proof. exact (MK_COMB (@lem4886814 A P s) (@lem4886815 A P s)). Qed.
Lemma lem4886817 {A : Type'} (P : type686 A) (s : A -> Prop) : (term65 A P s) = (term69 A P s).
Proof. exact (EQ_MP (@lem4886816 A P s) (@lem4886808 A P s)). Qed.
Lemma lem4886819 {A : Type'} (s : A -> Prop) : (term50 A s) = s.
Proof. exact (EQ_MP (@lem4886763 A s) (@lem4886762 A s)). Qed.
Lemma lem4886820 {A : Type'} (s : A -> Prop) : (term50 A s) = s.
Proof. exact (@lem4886819 A s). Qed.
Lemma lem4886821 {A : Type'} (P : type686 A) : (term70 A P) = (term70 A P).
Proof. exact (eq_refl (term70 A P)). Qed.
Lemma lem4886822 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term71 A P s).
Proof. exact (MK_COMB (@lem4886821 A P) (@lem4886820 A s)). Qed.
Lemma lem4886823 {A : Type'} (P : type686 A) (s : A -> Prop) : (term65 A P s) = (term71 A P s).
Proof. exact (TRANS (@lem4886817 A P s) (@lem4886822 A P s)). Qed.
Lemma lem4886824 {A : Type'} (P : type686 A) : (term72 A P) = (term73 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4886823 A P s)). Qed.
Lemma lem4886825 {A : Type'} (t : type686 A) : (term29 A t) = t.
Proof. exact (@lem4886761 (A -> Prop) Prop t). Qed.
Lemma lem4886826 {A : Type'} (P : type686 A) : (term73 A P) = (term70 A P).
Proof. exact (@lem4886825 A (term70 A P)). Qed.
Lemma lem4886827 {A : Type'} (P : type686 A) : (term72 A P) = (term70 A P).
Proof. exact (TRANS (@lem4886824 A P) (@lem4886826 A P)). Qed.
Lemma lem4886828 {A : Type'} : (@UNION_OF A (@FINITE (A -> Prop))) = (@UNION_OF A (@FINITE (A -> Prop))).
Proof. exact (eq_refl (@UNION_OF A (@FINITE (A -> Prop)))). Qed.
Lemma lem4886829 {A : Type'} (P : type686 A) : (term74 A P) = (term75 A P).
Proof. exact (MK_COMB (@lem4886828 A) (@lem4886827 A P)). Qed.
Lemma lem4886830 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4886831 {A : Type'} (P : type686 A) (s : A -> Prop) : (term76 A P s) = (term77 A P s).
Proof. exact (MK_COMB (@lem4886829 A P) (@lem4886830 A s)). Qed.
Lemma lem4886832 {A : Type'} (P : type686 A) : (term62 A P) = (term78 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4886831 A P s)). Qed.
Lemma lem4886833 {A : Type'} (P : type686 A) : (term58 A P) = (term78 A P).
Proof. exact (TRANS (@lem4886804 A P) (@lem4886832 A P)). Qed.
Lemma lem4886834 {A : Type'} (P : type686 A) : (term57 A P) = (term78 A P).
Proof. exact (TRANS (@lem4886791 A P) (@lem4886833 A P)). Qed.
Lemma lem4886835 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4886836 {A : Type'} (P : type686 A) : (term79 A P) = (term80 A P).
Proof. exact (MK_COMB (@lem4886835 A) (@lem4886834 A P)). Qed.
Lemma lem4886838 {A : Type'} : (@INTERSECTION_OF A (@FINITE (A -> Prop))) = (term39 A).
Proof. exact (EQ_MP (@lem4886757 A) (@lem4879380 A)). Qed.
Lemma lem4886839 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4886840 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term42 A P).
Proof. exact (MK_COMB (@lem4886838 A) (@lem4886839 A P)). Qed.
Lemma lem4886842 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4886843 {A : Type'} (f : type174 A) (y : type686 A) : (term52 A f y) = (f y).
Proof. exact (@lem4886842 (type686 A) (type686 A) f y). Qed.
Lemma lem4886844 {A : Type'} (P : type686 A) : (term53 A P) = (term42 A P).
Proof. exact (@lem4886843 A (term39 A) P). Qed.
Lemma lem4886845 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4886846 {A : Type'} : (term54 A) = (term39 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4886845 A P)). Qed.
Lemma lem4886847 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4886848 {A : Type'} (P : type686 A) : (term53 A P) = (term42 A P).
Proof. exact (MK_COMB (@lem4886846 A) (@lem4886847 A P)). Qed.
Lemma lem4886849 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4886850 {A : Type'} (P : type686 A) : (term55 A P) = (term56 A P).
Proof. exact (MK_COMB (@lem4886849 A) (@lem4886848 A P)). Qed.
Lemma lem4886851 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4886852 {A : Type'} (P : type686 A) : ((term53 A P) = (term42 A P)) = ((term42 A P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4886850 A P) (@lem4886851 A P)). Qed.
Lemma lem4886853 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (EQ_MP (@lem4886852 A P) (@lem4886844 A P)). Qed.
Lemma lem4886854 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term18 A P).
Proof. exact (TRANS (@lem4886840 A P) (@lem4886853 A P)). Qed.
Lemma lem4886855 {A : Type'} (P : type686 A) : ((term57 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P)) = ((term78 A P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4886836 A P) (@lem4886854 A P)). Qed.
Lemma lem4886858 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4886855 A P)). Qed.
Lemma lem4886859 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4886860 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (MK_COMB (@lem4886859 A) (@lem4886858 A)). Qed.
Lemma lem4886865 {A : Type'} : (term84 A) = (term83 A).
Proof. exact (SYM (@lem4886860 A)). Qed.
Lemma lem4886873 {A : Type'} (P : type686 A) : (term1 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (EQ_MP (@lem4886669 A P) (@lem4886668 A P)). Qed.
Lemma lem4886874 {A : Type'} (P : type686 A) : (term1 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (@lem4886873 A P). Qed.
Lemma lem4886875 {A : Type'} (P : type686 A) : (term75 A P) = (term70 A P).
Proof. exact (@lem4886874 A (term85 A P)). Qed.
Lemma lem4886876 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4886877 {A : Type'} (P : type686 A) (s : A -> Prop) : (term77 A P s) = (term23 A P s).
Proof. exact (MK_COMB (@lem4886875 A P) (@lem4886876 A s)). Qed.
Lemma lem4886878 {A : Type'} (P : type686 A) : (term78 A P) = (term18 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4886877 A P s)). Qed.
Lemma lem4886879 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4886880 {A : Type'} (P : type686 A) : (term80 A P) = (term86 A P).
Proof. exact (MK_COMB (@lem4886879 A) (@lem4886878 A P)). Qed.
Lemma lem4886881 {A : Type'} (P : type686 A) : (term18 A P) = (term18 A P).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem4886882 {A : Type'} (P : type686 A) : ((term78 A P) = (term18 A P)) = ((term18 A P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4886880 A P) (@lem4886881 A P)). Qed.
Lemma lem4886884 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4886885 {A : Type'} (x : type686 A) : (x = x) = True.
Proof. exact (@lem4886884 (type686 A) x). Qed.
Lemma lem4886886 {A : Type'} (P : type686 A) : ((term18 A P) = (term18 A P)) = True.
Proof. exact (@lem4886885 A (term18 A P)). Qed.
Lemma lem4886887 {A : Type'} (P : type686 A) : ((term78 A P) = (term18 A P)) = True.
Proof. exact (TRANS (@lem4886882 A P) (@lem4886886 A P)). Qed.
Lemma lem4886888 {A : Type'} : (term82 A) = (term87 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4886887 A P)). Qed.
Lemma lem4886889 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4886890 {A : Type'} : (term84 A) = (term88 A).
Proof. exact (MK_COMB (@lem4886889 A) (@lem4886888 A)). Qed.
Lemma lem4886892 {A : Type'} (t : Prop) : (term89 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4886893 {A : Type'} (t : Prop) : (term90 A t) = t.
Proof. exact (@lem4886892 (type686 A) t). Qed.
Lemma lem4886894 {A : Type'} : (term88 A) = True.
Proof. exact (@lem4886893 A True). Qed.
Lemma lem4886895 {A : Type'} : (term84 A) = True.
Proof. exact (TRANS (@lem4886890 A) (@lem4886894 A)). Qed.
Lemma lem4886896 {A : Type'} : True = (term84 A).
Proof. exact (SYM (@lem4886895 A)). Qed.
Lemma lem4886897 {A : Type'} : term84 A.
Proof. exact (EQ_MP (@lem4886896 A) (@lem0)). Qed.
Lemma lem4886898 {A : Type'} : term83 A.
Proof. exact (EQ_MP (@lem4886865 A) (@lem4886897 A)). Qed.
