Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_FINITE_PREIMAGE_term_abbrevs.
Require Import FINITE_FINITE_PREIMAGE_GENERAL_spec.
Require Import IN_UNIV_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem3617663 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem3617664 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3617665 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem3617664 A x) (@lem3617663 A x)). Qed.
Lemma lem3617666 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem3617668 {A B : Type'} : term1 A B.
Proof. exact (@lem3617662 A B). Qed.
Lemma lem3617669 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (@lem3617668 A B f). Qed.
Lemma lem3617670 {A B : Type'} (f : A -> B) : (term2 A B f) = (term3 A B f).
Proof. exact (eq_refl (term2 A B f)). Qed.
Lemma lem3617671 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (EQ_MP (@lem3617670 A B f) (@lem3617669 A B f)). Qed.
Lemma lem3617672 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (@lem3617671 A B f (@UNIV A)). Qed.
Lemma lem3617673 {A B : Type'} (f : A -> B) : (term4 A B f) = (term5 A B f).
Proof. exact (eq_refl (term4 A B f)). Qed.
Lemma lem3617674 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (EQ_MP (@lem3617673 A B f) (@lem3617672 A B f)). Qed.
Lemma lem3617675 {A B : Type'} (f : A -> B) (t : B -> Prop) : term6 A B f t.
Proof. exact (@lem3617674 A B f t). Qed.
Lemma lem3617676 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term6 A B f t) = (term7 A B f t).
Proof. exact (eq_refl (term6 A B f t)). Qed.
Lemma lem3617677 {A B : Type'} (f : A -> B) (t : B -> Prop) : term7 A B f t.
Proof. exact (EQ_MP (@lem3617676 A B f t) (@lem3617675 A B f t)). Qed.
Lemma lem3617697 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3617666 A x) (@lem3617665 A x)). Qed.
Lemma lem3617698 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3617697 A x). Qed.
Lemma lem3617699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3617700 {A : Type'} (x : A) : (term8 A x) = (and True).
Proof. exact (MK_COMB (@lem3617699) (@lem3617698 A x)). Qed.
Lemma lem3617703 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3617704 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term9 A B f x y) = (term10 A B f x y).
Proof. exact (MK_COMB (@lem3617700 A x) (@lem3617703 A B f x y)). Qed.
Lemma lem3617706 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3617707 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term10 A B f x y) = ((f x) = y).
Proof. exact (@lem3617706 ((f x) = y)). Qed.
Lemma lem3617710 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term9 A B f x y) = ((f x) = y).
Proof. exact (TRANS (@lem3617704 A B f x y) (@lem3617707 A B f x y)). Qed.
Lemma lem3617711 {A : Type'} (GEN_PVAR_98 : A) : (@SETSPEC A GEN_PVAR_98) = (@SETSPEC A GEN_PVAR_98).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_98)). Qed.
Lemma lem3617712 {A B : Type'} (GEN_PVAR_98 : A) (f : A -> B) (x : A) (y : B) : (term11 A B GEN_PVAR_98 f x y) = (term12 A B GEN_PVAR_98 f x y).
Proof. exact (MK_COMB (@lem3617711 A GEN_PVAR_98) (@lem3617710 A B f x y)). Qed.
Lemma lem3617713 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3617714 {A B : Type'} (GEN_PVAR_98 : A) (f : A -> B) (y : B) (x : A) : (term13 A B GEN_PVAR_98 f y x) = (term14 A B GEN_PVAR_98 f y x).
Proof. exact (MK_COMB (@lem3617712 A B GEN_PVAR_98 f x y) (@lem3617713 A x)). Qed.
Lemma lem3617715 {A B : Type'} (GEN_PVAR_98 : A) (f : A -> B) (y : B) : (term15 A B GEN_PVAR_98 f y) = (term16 A B GEN_PVAR_98 f y).
Proof. exact (fun_ext (fun x : A => @lem3617714 A B GEN_PVAR_98 f y x)). Qed.
Lemma lem3617716 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3617717 {A B : Type'} (GEN_PVAR_98 : A) (f : A -> B) (y : B) : (term17 A B GEN_PVAR_98 f y) = (term18 A B GEN_PVAR_98 f y).
Proof. exact (MK_COMB (@lem3617716 A) (@lem3617715 A B GEN_PVAR_98 f y)). Qed.
Lemma lem3617722 {A B : Type'} (f : A -> B) (y : B) : (term19 A B f y) = (term20 A B f y).
Proof. exact (fun_ext (fun GEN_PVAR_98 : A => @lem3617717 A B GEN_PVAR_98 f y)). Qed.
Lemma lem3617723 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3617724 {A B : Type'} (f : A -> B) (y : B) : (term21 A B f y) = (term22 A B f y).
Proof. exact (MK_COMB (@lem3617723 A) (@lem3617722 A B f y)). Qed.
Lemma lem3617725 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3617726 {A B : Type'} (f : A -> B) (y : B) : (term23 A B f y) = (term24 A B f y).
Proof. exact (MK_COMB (@lem3617725 A) (@lem3617724 A B f y)). Qed.
Lemma lem3617727 {B : Type'} (y : B) (t : B -> Prop) : (term25 B y t) = (term25 B y t).
Proof. exact (eq_refl (term25 B y t)). Qed.
Lemma lem3617728 {A B : Type'} (t : B -> Prop) (f : A -> B) (y : B) : (term26 A B t f y) = (term27 A B t f y).
Proof. exact (MK_COMB (@lem3617727 B y t) (@lem3617726 A B f y)). Qed.
Lemma lem3617731 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term28 A B t f) = (term29 A B t f).
Proof. exact (fun_ext (fun y : B => @lem3617728 A B t f y)). Qed.
Lemma lem3617732 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3617733 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term30 A B t f) = (term31 A B t f).
Proof. exact (MK_COMB (@lem3617732 B) (@lem3617731 A B t f)). Qed.
Lemma lem3617738 {B : Type'} (t : B -> Prop) : (term32 B t) = (term32 B t).
Proof. exact (eq_refl (term32 B t)). Qed.
Lemma lem3617739 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term33 A B t f) = (term34 A B t f).
Proof. exact (MK_COMB (@lem3617738 B t) (@lem3617733 A B t f)). Qed.
Lemma lem3617742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3617743 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term35 A B t f) = (term36 A B t f).
Proof. exact (MK_COMB (@lem3617742) (@lem3617739 A B t f)). Qed.
Lemma lem3617751 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3617666 A x) (@lem3617665 A x)). Qed.
Lemma lem3617752 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3617751 A x). Qed.
Lemma lem3617753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3617754 {A : Type'} (x : A) : (term8 A x) = (and True).
Proof. exact (MK_COMB (@lem3617753) (@lem3617752 A x)). Qed.
Lemma lem3617755 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term37 A B f x t) = (term37 A B f x t).
Proof. exact (eq_refl (term37 A B f x t)). Qed.
Lemma lem3617756 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term38 A B f x t) = (term39 A B f x t).
Proof. exact (MK_COMB (@lem3617754 A x) (@lem3617755 A B f x t)). Qed.
Lemma lem3617758 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3617759 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term39 A B f x t) = (term37 A B f x t).
Proof. exact (@lem3617758 (term37 A B f x t)). Qed.
Lemma lem3617760 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term38 A B f x t) = (term37 A B f x t).
Proof. exact (TRANS (@lem3617756 A B f x t) (@lem3617759 A B f x t)). Qed.
Lemma lem3617761 {A : Type'} (GEN_PVAR_99 : A) : (@SETSPEC A GEN_PVAR_99) = (@SETSPEC A GEN_PVAR_99).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_99)). Qed.
Lemma lem3617762 {A B : Type'} (GEN_PVAR_99 : A) (f : A -> B) (x : A) (t : B -> Prop) : (term40 A B GEN_PVAR_99 f x t) = (term41 A B GEN_PVAR_99 f x t).
Proof. exact (MK_COMB (@lem3617761 A GEN_PVAR_99) (@lem3617760 A B f x t)). Qed.
Lemma lem3617763 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3617764 {A B : Type'} (GEN_PVAR_99 : A) (f : A -> B) (t : B -> Prop) (x : A) : (term42 A B GEN_PVAR_99 f t x) = (term43 A B GEN_PVAR_99 f t x).
Proof. exact (MK_COMB (@lem3617762 A B GEN_PVAR_99 f x t) (@lem3617763 A x)). Qed.
Lemma lem3617765 {A B : Type'} (GEN_PVAR_99 : A) (f : A -> B) (t : B -> Prop) : (term44 A B GEN_PVAR_99 f t) = (term45 A B GEN_PVAR_99 f t).
Proof. exact (fun_ext (fun x : A => @lem3617764 A B GEN_PVAR_99 f t x)). Qed.
Lemma lem3617766 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3617767 {A B : Type'} (GEN_PVAR_99 : A) (f : A -> B) (t : B -> Prop) : (term46 A B GEN_PVAR_99 f t) = (term47 A B GEN_PVAR_99 f t).
Proof. exact (MK_COMB (@lem3617766 A) (@lem3617765 A B GEN_PVAR_99 f t)). Qed.
Lemma lem3617772 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term48 A B f t) = (term49 A B f t).
Proof. exact (fun_ext (fun GEN_PVAR_99 : A => @lem3617767 A B GEN_PVAR_99 f t)). Qed.
Lemma lem3617773 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3617774 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term50 A B f t) = (term51 A B f t).
Proof. exact (MK_COMB (@lem3617773 A) (@lem3617772 A B f t)). Qed.
Lemma lem3617775 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3617776 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term52 A B f t) = (term53 A B f t).
Proof. exact (MK_COMB (@lem3617775 A) (@lem3617774 A B f t)). Qed.
Lemma lem3617777 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term7 A B f t) = (term54 A B f t).
Proof. exact (MK_COMB (@lem3617743 A B t f) (@lem3617776 A B f t)). Qed.
Lemma lem3617780 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3617781 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term55 A B f t) = (term56 A B f t).
Proof. exact (MK_COMB (@lem3617780) (@lem3617777 A B f t)). Qed.
Lemma lem3617802 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term54 A B f t) = (term54 A B f t).
Proof. exact (eq_refl (term54 A B f t)). Qed.
Lemma lem3617803 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term57 A B f t) = (term58 A B f t).
Proof. exact (MK_COMB (@lem3617781 A B f t) (@lem3617802 A B f t)). Qed.
Lemma lem3617805 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3617806 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term58 A B f t) = True.
Proof. exact (@lem3617805 (term54 A B f t)). Qed.
Lemma lem3617809 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term59 A B f t) = (term59 A B f t).
Proof. exact (eq_refl (term59 A B f t)). Qed.
Lemma lem3617810 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term59 A B f t) = ((term58 A B f t) = True).
Proof. exact (eq_refl (term59 A B f t)). Qed.
Lemma lem3617811 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term60 A B f t) = (term60 A B f t).
Proof. exact (eq_refl (term60 A B f t)). Qed.
Lemma lem3617812 {A B : Type'} (f : A -> B) (t : B -> Prop) : ((term59 A B f t) = (term59 A B f t)) = ((term59 A B f t) = ((term58 A B f t) = True)).
Proof. exact (MK_COMB (@lem3617811 A B f t) (@lem3617810 A B f t)). Qed.
Lemma lem3617813 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term59 A B f t) = ((term58 A B f t) = True).
Proof. exact (eq_refl (term59 A B f t)). Qed.
Lemma lem3617814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3617815 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term60 A B f t) = (term61 A B f t).
Proof. exact (MK_COMB (@lem3617814) (@lem3617813 A B f t)). Qed.
Lemma lem3617816 {A B : Type'} (f : A -> B) (t : B -> Prop) : ((term58 A B f t) = True) = ((term58 A B f t) = True).
Proof. exact (eq_refl ((term58 A B f t) = True)). Qed.
Lemma lem3617817 {A B : Type'} (f : A -> B) (t : B -> Prop) : ((term59 A B f t) = ((term58 A B f t) = True)) = (((term58 A B f t) = True) = ((term58 A B f t) = True)).
Proof. exact (MK_COMB (@lem3617815 A B f t) (@lem3617816 A B f t)). Qed.
Lemma lem3617818 {A B : Type'} (f : A -> B) (t : B -> Prop) : ((term59 A B f t) = (term59 A B f t)) = (((term58 A B f t) = True) = ((term58 A B f t) = True)).
Proof. exact (TRANS (@lem3617812 A B f t) (@lem3617817 A B f t)). Qed.
Lemma lem3617819 {A B : Type'} (f : A -> B) (t : B -> Prop) : ((term58 A B f t) = True) = ((term58 A B f t) = True).
Proof. exact (EQ_MP (@lem3617818 A B f t) (@lem3617809 A B f t)). Qed.
Lemma lem3617820 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term58 A B f t) = True.
Proof. exact (EQ_MP (@lem3617819 A B f t) (@lem3617806 A B f t)). Qed.
Lemma lem3617821 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term57 A B f t) = True.
Proof. exact (TRANS (@lem3617803 A B f t) (@lem3617820 A B f t)). Qed.
Lemma lem3617822 {A B : Type'} (f : A -> B) (t : B -> Prop) : True = (term57 A B f t).
Proof. exact (SYM (@lem3617821 A B f t)). Qed.
Lemma lem3617823 {A B : Type'} (f : A -> B) (t : B -> Prop) : term57 A B f t.
Proof. exact (EQ_MP (@lem3617822 A B f t) (@lem0)). Qed.
Lemma lem3617824 {A B : Type'} (f : A -> B) (t : B -> Prop) : term54 A B f t.
Proof. exact (@lem3617823 A B f t (@lem3617677 A B f t)). Qed.
Lemma lem3617829 {A B : Type'} (f : A -> B) : term62 A B f.
Proof. exact (fun t : B -> Prop => @lem3617824 A B f t). Qed.
Lemma lem3617834 {A B : Type'} : term63 A B.
Proof. exact (fun f : A -> B => @lem3617829 A B f). Qed.
