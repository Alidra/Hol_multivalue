Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_ANTIMONO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3361614 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3361615 {_87386 : Type'} (s : type686 _87386) (t : type686 _87386) : (@SUBSET (_87386 -> Prop) s t) = (term1 _87386 s t).
Proof. exact (@lem3361614 (_87386 -> Prop) s t). Qed.
Lemma lem3361616 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (@SUBSET (_87386 -> Prop) g f) = (term1 _87386 g f).
Proof. exact (@lem3361615 _87386 g f). Qed.
Lemma lem3361623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361624 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term2 _87386 g f) = (term3 _87386 g f).
Proof. exact (MK_COMB (@lem3361623) (@lem3361616 _87386 g f)). Qed.
Lemma lem3361626 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3361627 {_87386 : Type'} (s : _87386 -> Prop) (t : _87386 -> Prop) : (@SUBSET _87386 s t) = (term0 _87386 s t).
Proof. exact (@lem3361626 _87386 s t). Qed.
Lemma lem3361628 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) : (term4 _87386 f g) = (term5 _87386 f g).
Proof. exact (@lem3361627 _87386 (@INTERS _87386 f) (@INTERS _87386 g)). Qed.
Lemma lem3361635 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) : (term6 _87386 f g) = (term7 _87386 f g).
Proof. exact (MK_COMB (@lem3361624 _87386 g f) (@lem3361628 _87386 f g)). Qed.
Lemma lem3361638 {_87386 : Type'} (f : type686 _87386) : (term8 _87386 f) = (term9 _87386 f).
Proof. exact (fun_ext (fun g : type686 _87386 => @lem3361635 _87386 f g)). Qed.
Lemma lem3361639 {_87386 : Type'} : (@all ((_87386 -> Prop) -> Prop)) = (@all ((_87386 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87386 -> Prop) -> Prop))). Qed.
Lemma lem3361640 {_87386 : Type'} (f : type686 _87386) : (term10 _87386 f) = (term11 _87386 f).
Proof. exact (MK_COMB (@lem3361639 _87386) (@lem3361638 _87386 f)). Qed.
Lemma lem3361645 {_87386 : Type'} : (term12 _87386) = (term13 _87386).
Proof. exact (fun_ext (fun f : type686 _87386 => @lem3361640 _87386 f)). Qed.
Lemma lem3361646 {_87386 : Type'} : (@all ((_87386 -> Prop) -> Prop)) = (@all ((_87386 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87386 -> Prop) -> Prop))). Qed.
Lemma lem3361647 {_87386 : Type'} : (term14 _87386) = (term15 _87386).
Proof. exact (MK_COMB (@lem3361646 _87386) (@lem3361645 _87386)). Qed.
Lemma lem3361652 {_87386 : Type'} : (term15 _87386) = (term14 _87386).
Proof. exact (SYM (@lem3361647 _87386)). Qed.
Lemma lem3361670 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3361671 {_87386 : Type'} (P : type686 _87386) (x : _87386 -> Prop) : (@IN (_87386 -> Prop) x P) = (P x).
Proof. exact (@lem3361670 (_87386 -> Prop) P x). Qed.
Lemma lem3361672 {_87386 : Type'} (g : type686 _87386) (x : _87386 -> Prop) : (@IN (_87386 -> Prop) x g) = (g x).
Proof. exact (@lem3361671 _87386 g x). Qed.
Lemma lem3361673 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361674 {_87386 : Type'} (g : type686 _87386) (x : _87386 -> Prop) : (term16 _87386 x g) = (term17 _87386 g x).
Proof. exact (MK_COMB (@lem3361673) (@lem3361672 _87386 g x)). Qed.
Lemma lem3361676 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3361677 {_87386 : Type'} (P : type686 _87386) (x : _87386 -> Prop) : (@IN (_87386 -> Prop) x P) = (P x).
Proof. exact (@lem3361676 (_87386 -> Prop) P x). Qed.
Lemma lem3361678 {_87386 : Type'} (f : type686 _87386) (x : _87386 -> Prop) : (@IN (_87386 -> Prop) x f) = (f x).
Proof. exact (@lem3361677 _87386 f x). Qed.
Lemma lem3361679 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (x : _87386 -> Prop) : (term18 _87386 g x f) = (term19 _87386 g f x).
Proof. exact (MK_COMB (@lem3361674 _87386 g x) (@lem3361678 _87386 f x)). Qed.
Lemma lem3361682 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term20 _87386 g f) = (term21 _87386 g f).
Proof. exact (fun_ext (fun x : _87386 -> Prop => @lem3361679 _87386 g f x)). Qed.
Lemma lem3361683 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3361684 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term1 _87386 g f) = (term22 _87386 g f).
Proof. exact (MK_COMB (@lem3361683 _87386) (@lem3361682 _87386 g f)). Qed.
Lemma lem3361689 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361690 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term3 _87386 g f) = (term23 _87386 g f).
Proof. exact (MK_COMB (@lem3361689) (@lem3361684 _87386 g f)). Qed.
Lemma lem3361698 {A : Type'} (s : type686 A) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3361699 {_87386 : Type'} (s : type686 _87386) (x : _87386) : (term24 _87386 x s) = (term25 _87386 s x).
Proof. exact (@lem3361698 _87386 s x). Qed.
Lemma lem3361700 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term24 _87386 x f) = (term25 _87386 f x).
Proof. exact (@lem3361699 _87386 f x). Qed.
Lemma lem3361708 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3361709 {_87386 : Type'} (P : type686 _87386) (x : _87386 -> Prop) : (@IN (_87386 -> Prop) x P) = (P x).
Proof. exact (@lem3361708 (_87386 -> Prop) P x). Qed.
Lemma lem3361710 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) : (@IN (_87386 -> Prop) t f) = (f t).
Proof. exact (@lem3361709 _87386 f t). Qed.
Lemma lem3361711 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361712 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) : (term16 _87386 t f) = (term17 _87386 f t).
Proof. exact (MK_COMB (@lem3361711) (@lem3361710 _87386 f t)). Qed.
Lemma lem3361714 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3361715 {_87386 : Type'} (P : _87386 -> Prop) (x : _87386) : (@IN _87386 x P) = (P x).
Proof. exact (@lem3361714 _87386 P x). Qed.
Lemma lem3361716 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) : (@IN _87386 x t) = (t x).
Proof. exact (@lem3361715 _87386 t x). Qed.
Lemma lem3361717 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) (x : _87386) : (term26 _87386 f x t) = (term27 _87386 f t x).
Proof. exact (MK_COMB (@lem3361712 _87386 f t) (@lem3361716 _87386 t x)). Qed.
Lemma lem3361720 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term28 _87386 f x) = (term29 _87386 f x).
Proof. exact (fun_ext (fun t : _87386 -> Prop => @lem3361717 _87386 f t x)). Qed.
Lemma lem3361721 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3361722 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term25 _87386 f x) = (term30 _87386 f x).
Proof. exact (MK_COMB (@lem3361721 _87386) (@lem3361720 _87386 f x)). Qed.
Lemma lem3361727 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term24 _87386 x f) = (term30 _87386 f x).
Proof. exact (TRANS (@lem3361700 _87386 f x) (@lem3361722 _87386 f x)). Qed.
Lemma lem3361728 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361729 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term31 _87386 x f) = (term32 _87386 f x).
Proof. exact (MK_COMB (@lem3361728) (@lem3361727 _87386 f x)). Qed.
Lemma lem3361731 {A : Type'} (s : type686 A) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3361732 {_87386 : Type'} (s : type686 _87386) (x : _87386) : (term24 _87386 x s) = (term25 _87386 s x).
Proof. exact (@lem3361731 _87386 s x). Qed.
Lemma lem3361733 {_87386 : Type'} (g : type686 _87386) (x : _87386) : (term24 _87386 x g) = (term25 _87386 g x).
Proof. exact (@lem3361732 _87386 g x). Qed.
Lemma lem3361741 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3361742 {_87386 : Type'} (P : type686 _87386) (x : _87386 -> Prop) : (@IN (_87386 -> Prop) x P) = (P x).
Proof. exact (@lem3361741 (_87386 -> Prop) P x). Qed.
Lemma lem3361743 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) : (@IN (_87386 -> Prop) t g) = (g t).
Proof. exact (@lem3361742 _87386 g t). Qed.
Lemma lem3361744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361745 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) : (term16 _87386 t g) = (term17 _87386 g t).
Proof. exact (MK_COMB (@lem3361744) (@lem3361743 _87386 g t)). Qed.
Lemma lem3361747 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3361748 {_87386 : Type'} (P : _87386 -> Prop) (x : _87386) : (@IN _87386 x P) = (P x).
Proof. exact (@lem3361747 _87386 P x). Qed.
Lemma lem3361749 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) : (@IN _87386 x t) = (t x).
Proof. exact (@lem3361748 _87386 t x). Qed.
Lemma lem3361750 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) (x : _87386) : (term26 _87386 g x t) = (term27 _87386 g t x).
Proof. exact (MK_COMB (@lem3361745 _87386 g t) (@lem3361749 _87386 t x)). Qed.
Lemma lem3361753 {_87386 : Type'} (g : type686 _87386) (x : _87386) : (term28 _87386 g x) = (term29 _87386 g x).
Proof. exact (fun_ext (fun t : _87386 -> Prop => @lem3361750 _87386 g t x)). Qed.
Lemma lem3361754 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3361755 {_87386 : Type'} (g : type686 _87386) (x : _87386) : (term25 _87386 g x) = (term30 _87386 g x).
Proof. exact (MK_COMB (@lem3361754 _87386) (@lem3361753 _87386 g x)). Qed.
Lemma lem3361760 {_87386 : Type'} (g : type686 _87386) (x : _87386) : (term24 _87386 x g) = (term30 _87386 g x).
Proof. exact (TRANS (@lem3361733 _87386 g x) (@lem3361755 _87386 g x)). Qed.
Lemma lem3361761 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (x : _87386) : (term33 _87386 f x g) = (term34 _87386 f g x).
Proof. exact (MK_COMB (@lem3361729 _87386 f x) (@lem3361760 _87386 g x)). Qed.
Lemma lem3361764 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) : (term35 _87386 f g) = (term36 _87386 f g).
Proof. exact (fun_ext (fun x : _87386 => @lem3361761 _87386 f g x)). Qed.
Lemma lem3361765 {_87386 : Type'} : (@all _87386) = (@all _87386).
Proof. exact (eq_refl (@all _87386)). Qed.
Lemma lem3361766 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) : (term5 _87386 f g) = (term37 _87386 f g).
Proof. exact (MK_COMB (@lem3361765 _87386) (@lem3361764 _87386 f g)). Qed.
Lemma lem3361771 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) : (term7 _87386 f g) = (term38 _87386 f g).
Proof. exact (MK_COMB (@lem3361690 _87386 g f) (@lem3361766 _87386 f g)). Qed.
Lemma lem3361774 {_87386 : Type'} (f : type686 _87386) : (term9 _87386 f) = (term39 _87386 f).
Proof. exact (fun_ext (fun g : type686 _87386 => @lem3361771 _87386 f g)). Qed.
Lemma lem3361775 {_87386 : Type'} : (@all ((_87386 -> Prop) -> Prop)) = (@all ((_87386 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87386 -> Prop) -> Prop))). Qed.
Lemma lem3361776 {_87386 : Type'} (f : type686 _87386) : (term11 _87386 f) = (term40 _87386 f).
Proof. exact (MK_COMB (@lem3361775 _87386) (@lem3361774 _87386 f)). Qed.
Lemma lem3361781 {_87386 : Type'} : (term13 _87386) = (term41 _87386).
Proof. exact (fun_ext (fun f : type686 _87386 => @lem3361776 _87386 f)). Qed.
Lemma lem3361782 {_87386 : Type'} : (@all ((_87386 -> Prop) -> Prop)) = (@all ((_87386 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87386 -> Prop) -> Prop))). Qed.
Lemma lem3361783 {_87386 : Type'} : (term15 _87386) = (term42 _87386).
Proof. exact (MK_COMB (@lem3361782 _87386) (@lem3361781 _87386)). Qed.
Lemma lem3361788 {_87386 : Type'} : (term42 _87386) = (term15 _87386).
Proof. exact (SYM (@lem3361783 _87386)). Qed.
Lemma lem3361790 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3361791 {_87386 : Type'} : (term42 _87386) = (term44 _87386).
Proof. exact (@lem3361790 (term42 _87386)). Qed.
Lemma lem3361792 {_87386 : Type'} : (term44 _87386) = (term42 _87386).
Proof. exact (SYM (@lem3361791 _87386)). Qed.
Lemma lem3361793 {_87386 : Type'} (h1 : term45 _87386) : term45 _87386.
Proof. exact (h1). Qed.
Lemma lem3361796 {_87386 : Type'} (h1 : term44 _87386) : term44 _87386.
Proof. exact (h1). Qed.
Lemma lem3361797 {_87386 : Type'} : term46 _87386.
Proof. exact (fun h0 : term44 _87386 => @lem3361796 _87386 h0). Qed.
Lemma lem3361798 {_87386 : Type'} (h1 : term46 _87386) : term46 _87386.
Proof. exact (h1). Qed.
Lemma lem3361799 {_87386 : Type'} (h1 : term44 _87386) : term44 _87386.
Proof. exact (h1). Qed.
Lemma lem3361800 {_87386 : Type'} (h1 : term44 _87386) (h2 : term46 _87386) : term44 _87386.
Proof. exact (@lem3361798 _87386 h2 (@lem3361799 _87386 h1)). Qed.
Lemma lem3361801 {_87386 : Type'} (h1 : term44 _87386) : term47 _87386.
Proof. exact (fun h0 : term46 _87386 => @lem3361800 _87386 h1 h0). Qed.
Lemma lem3361802 {_87386 : Type'} (h1 : term46 _87386) : term46 _87386.
Proof. exact (h1). Qed.
Lemma lem3361803 {_87386 : Type'} (h1 : term44 _87386) (h2 : term46 _87386) : term44 _87386.
Proof. exact (@lem3361801 _87386 h1 (@lem3361802 _87386 h2)). Qed.
Lemma lem3361804 {_87386 : Type'} (h1 : term46 _87386) : term46 _87386.
Proof. exact (fun h0 : term44 _87386 => @lem3361803 _87386 h0 h1). Qed.
Lemma lem3361805 {_87386 : Type'} : term48 _87386.
Proof. exact (fun h0 : term46 _87386 => @lem3361804 _87386 h0). Qed.
Lemma lem3361808 {_87386 : Type'} : term46 _87386.
Proof. exact (@lem3361805 _87386 (@lem3361797 _87386)). Qed.
Lemma lem3361809 {_87386 : Type'} : term46 _87386.
Proof. exact (@lem3361808 _87386). Qed.
Lemma lem3361811 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3361812 {_87386 : Type'} : (term44 _87386) = (term49 _87386).
Proof. exact (@lem3361811 (term45 _87386)). Qed.
Lemma lem3361814 (t : Prop) : (term50 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3361815 {_87386 : Type'} : (term49 _87386) = (term42 _87386).
Proof. exact (@lem3361814 (term42 _87386)). Qed.
Lemma lem3361854 {_87386 : Type'} : (term44 _87386) = (term42 _87386).
Proof. exact (TRANS (@lem3361812 _87386) (@lem3361815 _87386)). Qed.
Lemma lem3361859 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) (x : _87386) : (term27 _87386 g t x) = (term27 _87386 g t x).
Proof. exact (eq_refl (term27 _87386 g t x)). Qed.
Lemma lem3361860 {_87386 : Type'} (g : type686 _87386) (x : _87386) : (term29 _87386 g x) = (term29 _87386 g x).
Proof. exact (fun_ext (fun t : _87386 -> Prop => @lem3361859 _87386 g t x)). Qed.
Lemma lem3361861 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3361862 {_87386 : Type'} (g : type686 _87386) (x : _87386) : (term30 _87386 g x) = (term30 _87386 g x).
Proof. exact (MK_COMB (@lem3361861 _87386) (@lem3361860 _87386 g x)). Qed.
Lemma lem3361867 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) (x : _87386) : (term27 _87386 f t x) = (term27 _87386 f t x).
Proof. exact (eq_refl (term27 _87386 f t x)). Qed.
Lemma lem3361868 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term29 _87386 f x) = (term29 _87386 f x).
Proof. exact (fun_ext (fun t : _87386 -> Prop => @lem3361867 _87386 f t x)). Qed.
Lemma lem3361869 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3361870 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term30 _87386 f x) = (term30 _87386 f x).
Proof. exact (MK_COMB (@lem3361869 _87386) (@lem3361868 _87386 f x)). Qed.
Lemma lem3361871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361872 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term32 _87386 f x) = (term32 _87386 f x).
Proof. exact (MK_COMB (@lem3361871) (@lem3361870 _87386 f x)). Qed.
Lemma lem3361873 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (x : _87386) : (term34 _87386 f g x) = (term34 _87386 f g x).
Proof. exact (MK_COMB (@lem3361872 _87386 f x) (@lem3361862 _87386 g x)). Qed.
Lemma lem3361874 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) : (term36 _87386 f g) = (term36 _87386 f g).
Proof. exact (fun_ext (fun x : _87386 => @lem3361873 _87386 f g x)). Qed.
Lemma lem3361875 {_87386 : Type'} : (@all _87386) = (@all _87386).
Proof. exact (eq_refl (@all _87386)). Qed.
Lemma lem3361876 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) : (term37 _87386 f g) = (term37 _87386 f g).
Proof. exact (MK_COMB (@lem3361875 _87386) (@lem3361874 _87386 f g)). Qed.
Lemma lem3361881 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (x : _87386 -> Prop) : (term19 _87386 g f x) = (term19 _87386 g f x).
Proof. exact (eq_refl (term19 _87386 g f x)). Qed.
Lemma lem3361882 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term21 _87386 g f) = (term21 _87386 g f).
Proof. exact (fun_ext (fun x : _87386 -> Prop => @lem3361881 _87386 g f x)). Qed.
Lemma lem3361883 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3361884 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term22 _87386 g f) = (term22 _87386 g f).
Proof. exact (MK_COMB (@lem3361883 _87386) (@lem3361882 _87386 g f)). Qed.
Lemma lem3361885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361886 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term23 _87386 g f) = (term23 _87386 g f).
Proof. exact (MK_COMB (@lem3361885) (@lem3361884 _87386 g f)). Qed.
Lemma lem3361887 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) : (term38 _87386 f g) = (term38 _87386 f g).
Proof. exact (MK_COMB (@lem3361886 _87386 g f) (@lem3361876 _87386 f g)). Qed.
Lemma lem3361888 {_87386 : Type'} (f : type686 _87386) : (term39 _87386 f) = (term39 _87386 f).
Proof. exact (fun_ext (fun g : type686 _87386 => @lem3361887 _87386 f g)). Qed.
Lemma lem3361889 {_87386 : Type'} : (@all ((_87386 -> Prop) -> Prop)) = (@all ((_87386 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87386 -> Prop) -> Prop))). Qed.
Lemma lem3361890 {_87386 : Type'} (f : type686 _87386) : (term40 _87386 f) = (term40 _87386 f).
Proof. exact (MK_COMB (@lem3361889 _87386) (@lem3361888 _87386 f)). Qed.
Lemma lem3361891 {_87386 : Type'} : (term41 _87386) = (term41 _87386).
Proof. exact (fun_ext (fun f : type686 _87386 => @lem3361890 _87386 f)). Qed.
Lemma lem3361892 {_87386 : Type'} : (@all ((_87386 -> Prop) -> Prop)) = (@all ((_87386 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87386 -> Prop) -> Prop))). Qed.
Lemma lem3361893 {_87386 : Type'} : (term42 _87386) = (term42 _87386).
Proof. exact (MK_COMB (@lem3361892 _87386) (@lem3361891 _87386)). Qed.
Lemma lem3361942 {_87386 : Type'} : (term44 _87386) = (term42 _87386).
Proof. exact (TRANS (@lem3361854 _87386) (@lem3361893 _87386)). Qed.
Lemma lem3361943 {_87386 : Type'} : (term42 _87386) = (term44 _87386).
Proof. exact (SYM (@lem3361942 _87386)). Qed.
Lemma lem3361944 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term22 _87386 g f.
Proof. exact (h1). Qed.
Lemma lem3361945 {_87386 : Type'} (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term30 _87386 f x.
Proof. exact (h1). Qed.
Lemma lem3361948 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3361949 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) : (t x) = (term51 _87386 t x).
Proof. exact (@lem3361948 (t x)). Qed.
Lemma lem3361950 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) : (term51 _87386 t x) = (t x).
Proof. exact (SYM (@lem3361949 _87386 t x)). Qed.
Lemma lem3361951 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) (h1 : term52 _87386 t x) : term52 _87386 t x.
Proof. exact (h1). Qed.
Lemma lem3361958 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (x : _87386 -> Prop) : (term19 _87386 g f x) = (term53 _87386 g f x).
Proof. exact (@lem17265 (g x) (f x)). Qed.
Lemma lem3361959 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term21 _87386 g f) = (term54 _87386 g f).
Proof. exact (fun_ext (fun x : _87386 -> Prop => @lem3361958 _87386 g f x)). Qed.
Lemma lem3361960 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3361997 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term22 _87386 g f) = (term55 _87386 g f).
Proof. exact (MK_COMB (@lem3361960 _87386) (@lem3361959 _87386 g f)). Qed.
Lemma lem3361998 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term55 _87386 g f.
Proof. exact (EQ_MP (@lem3361997 _87386 g f) (@lem3361944 _87386 g f h1)). Qed.
Lemma lem3362005 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) (x : _87386) : (term27 _87386 f t x) = (term56 _87386 f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem3362006 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term29 _87386 f x) = (term57 _87386 f x).
Proof. exact (fun_ext (fun t : _87386 -> Prop => @lem3362005 _87386 f t x)). Qed.
Lemma lem3362007 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3362060 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term30 _87386 f x) = (term58 _87386 f x).
Proof. exact (MK_COMB (@lem3362007 _87386) (@lem3362006 _87386 f x)). Qed.
Lemma lem3362061 {_87386 : Type'} (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term58 _87386 f x.
Proof. exact (EQ_MP (@lem3362060 _87386 f x) (@lem3361945 _87386 f x h1)). Qed.
Lemma lem3362067 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) (h1 : g t) : g t.
Proof. exact (h1). Qed.
Lemma lem3362073 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) (h1 : term52 _87386 t x) : term52 _87386 t x.
Proof. exact (h1). Qed.
Lemma lem3362078 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3362080 {_87386 : Type'} (f : type686 _87386) (x : _87386 -> Prop) : (f x) = (@I ((_87386 -> Prop) -> Prop) f x).
Proof. exact (@lem3362078 (_87386 -> Prop) Prop f x). Qed.
Lemma lem3362081 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3362086 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3362087 {_87386 : Type'} (f : type686 _87386) (x : _87386 -> Prop) : (f x) = (@I ((_87386 -> Prop) -> Prop) f x).
Proof. exact (@lem3362086 (_87386 -> Prop) Prop f x). Qed.
Lemma lem3362089 {_87386 : Type'} (g : type686 _87386) (x : _87386 -> Prop) : (g x) = (@I ((_87386 -> Prop) -> Prop) g x).
Proof. exact (@lem3362087 _87386 g x). Qed.
Lemma lem3362090 {_87386 : Type'} (g : type686 _87386) (x : _87386 -> Prop) : (term59 _87386 g x) = (term60 _87386 g x).
Proof. exact (MK_COMB (@lem3362081) (@lem3362089 _87386 g x)). Qed.
Lemma lem3362091 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3362092 {_87386 : Type'} (g : type686 _87386) (x : _87386 -> Prop) : (term61 _87386 g x) = (term62 _87386 g x).
Proof. exact (MK_COMB (@lem3362091) (@lem3362090 _87386 g x)). Qed.
Lemma lem3362093 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (x : _87386 -> Prop) : (term53 _87386 g f x) = (term63 _87386 g f x).
Proof. exact (MK_COMB (@lem3362092 _87386 g x) (@lem3362080 _87386 f x)). Qed.
Lemma lem3362094 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term54 _87386 g f) = (term64 _87386 g f).
Proof. exact (fun_ext (fun x : _87386 -> Prop => @lem3362093 _87386 g f x)). Qed.
Lemma lem3362095 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3362096 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term55 _87386 g f) = (term65 _87386 g f).
Proof. exact (MK_COMB (@lem3362095 _87386) (@lem3362094 _87386 g f)). Qed.
Lemma lem3362097 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term65 _87386 g f.
Proof. exact (EQ_MP (@lem3362096 _87386 g f) (@lem3361998 _87386 g f h1)). Qed.
Lemma lem3362102 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3362103 {_87386 : Type'} (f : _87386 -> Prop) (x : _87386) : (f x) = (@I (_87386 -> Prop) f x).
Proof. exact (@lem3362102 _87386 Prop f x). Qed.
Lemma lem3362105 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) : (t x) = (@I (_87386 -> Prop) t x).
Proof. exact (@lem3362103 _87386 t x). Qed.
Lemma lem3362106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3362111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3362112 {_87386 : Type'} (f : type686 _87386) (x : _87386 -> Prop) : (f x) = (@I ((_87386 -> Prop) -> Prop) f x).
Proof. exact (@lem3362111 (_87386 -> Prop) Prop f x). Qed.
Lemma lem3362114 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) : (f t) = (@I ((_87386 -> Prop) -> Prop) f t).
Proof. exact (@lem3362112 _87386 f t). Qed.
Lemma lem3362115 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) : (term59 _87386 f t) = (term60 _87386 f t).
Proof. exact (MK_COMB (@lem3362106) (@lem3362114 _87386 f t)). Qed.
Lemma lem3362116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3362117 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) : (term61 _87386 f t) = (term62 _87386 f t).
Proof. exact (MK_COMB (@lem3362116) (@lem3362115 _87386 f t)). Qed.
Lemma lem3362118 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) (x : _87386) : (term56 _87386 f t x) = (term66 _87386 f t x).
Proof. exact (MK_COMB (@lem3362117 _87386 f t) (@lem3362105 _87386 t x)). Qed.
Lemma lem3362119 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term57 _87386 f x) = (term67 _87386 f x).
Proof. exact (fun_ext (fun t : _87386 -> Prop => @lem3362118 _87386 f t x)). Qed.
Lemma lem3362120 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3362121 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term58 _87386 f x) = (term68 _87386 f x).
Proof. exact (MK_COMB (@lem3362120 _87386) (@lem3362119 _87386 f x)). Qed.
Lemma lem3362122 {_87386 : Type'} (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term68 _87386 f x.
Proof. exact (EQ_MP (@lem3362121 _87386 f x) (@lem3362061 _87386 f x h1)). Qed.
Lemma lem3362127 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3362128 {_87386 : Type'} (f : type686 _87386) (x : _87386 -> Prop) : (f x) = (@I ((_87386 -> Prop) -> Prop) f x).
Proof. exact (@lem3362127 (_87386 -> Prop) Prop f x). Qed.
Lemma lem3362130 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) : (g t) = (@I ((_87386 -> Prop) -> Prop) g t).
Proof. exact (@lem3362128 _87386 g t). Qed.
Lemma lem3362132 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3362137 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3362138 {_87386 : Type'} (f : _87386 -> Prop) (x : _87386) : (f x) = (@I (_87386 -> Prop) f x).
Proof. exact (@lem3362137 _87386 Prop f x). Qed.
Lemma lem3362140 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) : (t x) = (@I (_87386 -> Prop) t x).
Proof. exact (@lem3362138 _87386 t x). Qed.
Lemma lem3362141 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) : (term52 _87386 t x) = (term69 _87386 t x).
Proof. exact (MK_COMB (@lem3362132) (@lem3362140 _87386 t x)). Qed.
Lemma lem3362150 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (x : _87386 -> Prop) : (term63 _87386 g f x) = (term63 _87386 g f x).
Proof. exact (eq_refl (term63 _87386 g f x)). Qed.
Lemma lem3362151 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term64 _87386 g f) = (term64 _87386 g f).
Proof. exact (fun_ext (fun x : _87386 -> Prop => @lem3362150 _87386 g f x)). Qed.
Lemma lem3362152 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3362154 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) : (term65 _87386 g f) = (term65 _87386 g f).
Proof. exact (MK_COMB (@lem3362152 _87386) (@lem3362151 _87386 g f)). Qed.
Lemma lem3362155 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term65 _87386 g f.
Proof. exact (EQ_MP (@lem3362154 _87386 g f) (@lem3362097 _87386 g f h1)). Qed.
Lemma lem3362163 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) (x : _87386) : (term66 _87386 f t x) = (term66 _87386 f t x).
Proof. exact (eq_refl (term66 _87386 f t x)). Qed.
Lemma lem3362164 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term67 _87386 f x) = (term67 _87386 f x).
Proof. exact (fun_ext (fun t : _87386 -> Prop => @lem3362163 _87386 f t x)). Qed.
Lemma lem3362165 {_87386 : Type'} : (@all (_87386 -> Prop)) = (@all (_87386 -> Prop)).
Proof. exact (eq_refl (@all (_87386 -> Prop))). Qed.
Lemma lem3362167 {_87386 : Type'} (f : type686 _87386) (x : _87386) : (term68 _87386 f x) = (term68 _87386 f x).
Proof. exact (MK_COMB (@lem3362165 _87386) (@lem3362164 _87386 f x)). Qed.
Lemma lem3362168 {_87386 : Type'} (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term68 _87386 f x.
Proof. exact (EQ_MP (@lem3362167 _87386 f x) (@lem3362122 _87386 f x h1)). Qed.
Lemma lem3362177 {_87386 : Type'} (_35070 : _87386 -> Prop) (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term70 _87386 g f _35070.
Proof. exact (@lem3362155 _87386 g f h1 _35070). Qed.
Lemma lem3362178 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (_35070 : _87386 -> Prop) : (term70 _87386 g f _35070) = (term63 _87386 g f _35070).
Proof. exact (eq_refl (term70 _87386 g f _35070)). Qed.
Lemma lem3362180 {_87386 : Type'} (_35071 : _87386 -> Prop) (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term71 _87386 f x _35071.
Proof. exact (@lem3362168 _87386 f x h1 _35071). Qed.
Lemma lem3362181 {_87386 : Type'} (f : type686 _87386) (_35071 : _87386 -> Prop) (x : _87386) : (term71 _87386 f x _35071) = (term66 _87386 f _35071 x).
Proof. exact (eq_refl (term71 _87386 f x _35071)). Qed.
Lemma lem3362188 {_87386 : Type'} (_35070 : _87386 -> Prop) (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term63 _87386 g f _35070.
Proof. exact (EQ_MP (@lem3362178 _87386 g f _35070) (@lem3362177 _87386 _35070 g f h1)). Qed.
Lemma lem3362194 {_87386 : Type'} (_35071 : _87386 -> Prop) (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term66 _87386 f _35071 x.
Proof. exact (EQ_MP (@lem3362181 _87386 f _35071 x) (@lem3362180 _87386 _35071 f x h1)). Qed.
Lemma lem3362198 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) (h1 : term52 _87386 t x) : term69 _87386 t x.
Proof. exact (EQ_MP (@lem3362141 _87386 t x) (@lem3362073 _87386 t x h1)). Qed.
Lemma lem3362200 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) (h1 : g t) : @I ((_87386 -> Prop) -> Prop) g t.
Proof. exact (EQ_MP (@lem3362130 _87386 g t) (@lem3362067 _87386 g t h1)). Qed.
Lemma lem3362201 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) (h1 : g t) : term72 _87386 g t.
Proof. exact (fun h0 : term60 _87386 g t => @lem3362200 _87386 g t h1). Qed.
Lemma lem3362203 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3362204 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) : (term72 _87386 g t) = (@I ((_87386 -> Prop) -> Prop) g t).
Proof. exact (@lem3362203 (@I ((_87386 -> Prop) -> Prop) g t)). Qed.
Lemma lem3362205 {_87386 : Type'} (g : type686 _87386) (t : _87386 -> Prop) (h1 : g t) : @I ((_87386 -> Prop) -> Prop) g t.
Proof. exact (EQ_MP (@lem3362204 _87386 g t) (@lem3362201 _87386 g t h1)). Qed.
Lemma lem3362211 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3362212 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (_35070 : _87386 -> Prop) : (term63 _87386 g f _35070) = (term74 _87386 f g _35070).
Proof. exact (@lem3362211 (@I ((_87386 -> Prop) -> Prop) f _35070) (term60 _87386 g _35070)). Qed.
Lemma lem3362218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3362219 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (_35070 : _87386 -> Prop) : (term75 _87386 g f _35070) = (term76 _87386 f g _35070).
Proof. exact (MK_COMB (@lem3362218) (@lem3362212 _87386 f g _35070)). Qed.
Lemma lem3362225 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (_35070 : _87386 -> Prop) : (term74 _87386 f g _35070) = (term74 _87386 f g _35070).
Proof. exact (eq_refl (term74 _87386 f g _35070)). Qed.
Lemma lem3362226 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (_35070 : _87386 -> Prop) : ((term63 _87386 g f _35070) = (term74 _87386 f g _35070)) = ((term74 _87386 f g _35070) = (term74 _87386 f g _35070)).
Proof. exact (MK_COMB (@lem3362219 _87386 f g _35070) (@lem3362225 _87386 f g _35070)). Qed.
Lemma lem3362228 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3362229 (x : Prop) : (x = x) = True.
Proof. exact (@lem3362228 Prop x). Qed.
Lemma lem3362230 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (_35070 : _87386 -> Prop) : ((term74 _87386 f g _35070) = (term74 _87386 f g _35070)) = True.
Proof. exact (@lem3362229 (term74 _87386 f g _35070)). Qed.
Lemma lem3362231 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (_35070 : _87386 -> Prop) : ((term63 _87386 g f _35070) = (term74 _87386 f g _35070)) = True.
Proof. exact (TRANS (@lem3362226 _87386 f g _35070) (@lem3362230 _87386 f g _35070)). Qed.
Lemma lem3362232 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (_35070 : _87386 -> Prop) : True = ((term63 _87386 g f _35070) = (term74 _87386 f g _35070)).
Proof. exact (SYM (@lem3362231 _87386 f g _35070)). Qed.
Lemma lem3362233 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (_35070 : _87386 -> Prop) : (term63 _87386 g f _35070) = (term74 _87386 f g _35070).
Proof. exact (EQ_MP (@lem3362232 _87386 f g _35070) (@lem0)). Qed.
Lemma lem3362234 {_87386 : Type'} (_35070 : _87386 -> Prop) (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term74 _87386 f g _35070.
Proof. exact (EQ_MP (@lem3362233 _87386 f g _35070) (@lem3362188 _87386 _35070 g f h1)). Qed.
Lemma lem3362236 (b : Prop) (a : Prop) : (a \/ b) = (term77 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3362237 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (_35070 : _87386 -> Prop) : (term74 _87386 f g _35070) = (term78 _87386 g f _35070).
Proof. exact (@lem3362236 (term60 _87386 g _35070) (@I ((_87386 -> Prop) -> Prop) f _35070)). Qed.
Lemma lem3362239 (a : Prop) : (term50 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3362240 {_87386 : Type'} (g : type686 _87386) (_35070 : _87386 -> Prop) : (term79 _87386 g _35070) = (@I ((_87386 -> Prop) -> Prop) g _35070).
Proof. exact (@lem3362239 (@I ((_87386 -> Prop) -> Prop) g _35070)). Qed.
Lemma lem3362241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3362242 {_87386 : Type'} (g : type686 _87386) (_35070 : _87386 -> Prop) : (term80 _87386 g _35070) = (term81 _87386 g _35070).
Proof. exact (MK_COMB (@lem3362241) (@lem3362240 _87386 g _35070)). Qed.
Lemma lem3362243 {_87386 : Type'} (f : type686 _87386) (_35070 : _87386 -> Prop) : (@I ((_87386 -> Prop) -> Prop) f _35070) = (@I ((_87386 -> Prop) -> Prop) f _35070).
Proof. exact (eq_refl (@I ((_87386 -> Prop) -> Prop) f _35070)). Qed.
Lemma lem3362244 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (_35070 : _87386 -> Prop) : (term78 _87386 g f _35070) = (term82 _87386 g f _35070).
Proof. exact (MK_COMB (@lem3362242 _87386 g _35070) (@lem3362243 _87386 f _35070)). Qed.
Lemma lem3362245 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (_35070 : _87386 -> Prop) : (term74 _87386 f g _35070) = (term82 _87386 g f _35070).
Proof. exact (TRANS (@lem3362237 _87386 g f _35070) (@lem3362244 _87386 g f _35070)). Qed.
Lemma lem3362248 {_87386 : Type'} (_35070 : _87386 -> Prop) (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term82 _87386 g f _35070.
Proof. exact (EQ_MP (@lem3362245 _87386 g f _35070) (@lem3362234 _87386 _35070 g f h1)). Qed.
Lemma lem3362249 {_87386 : Type'} (_35070 : _87386 -> Prop) (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term82 _87386 g f _35070.
Proof. exact (@lem3362248 _87386 _35070 g f h1). Qed.
Lemma lem3362250 {_87386 : Type'} (t : _87386 -> Prop) (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term82 _87386 g f t.
Proof. exact (@lem3362249 _87386 t g f h1). Qed.
Lemma lem3362253 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term22 _87386 g f) (h2 : g t) : @I ((_87386 -> Prop) -> Prop) f t.
Proof. exact (@lem3362250 _87386 t g f h1 (@lem3362205 _87386 g t h2)). Qed.
Lemma lem3362254 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term22 _87386 g f) (h2 : g t) : term72 _87386 f t.
Proof. exact (fun h0 : term60 _87386 f t => @lem3362253 _87386 f g t h1 h2). Qed.
Lemma lem3362256 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3362257 {_87386 : Type'} (f : type686 _87386) (t : _87386 -> Prop) : (term72 _87386 f t) = (@I ((_87386 -> Prop) -> Prop) f t).
Proof. exact (@lem3362256 (@I ((_87386 -> Prop) -> Prop) f t)). Qed.
Lemma lem3362258 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term22 _87386 g f) (h2 : g t) : @I ((_87386 -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3362257 _87386 f t) (@lem3362254 _87386 f g t h1 h2)). Qed.
Lemma lem3362264 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3362265 {_87386 : Type'} (x : _87386) (f : type686 _87386) (_35071 : _87386 -> Prop) : (term66 _87386 f _35071 x) = (term83 _87386 x f _35071).
Proof. exact (@lem3362264 (@I (_87386 -> Prop) _35071 x) (term60 _87386 f _35071)). Qed.
Lemma lem3362271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3362272 {_87386 : Type'} (x : _87386) (f : type686 _87386) (_35071 : _87386 -> Prop) : (term84 _87386 f _35071 x) = (term85 _87386 x f _35071).
Proof. exact (MK_COMB (@lem3362271) (@lem3362265 _87386 x f _35071)). Qed.
Lemma lem3362278 {_87386 : Type'} (x : _87386) (f : type686 _87386) (_35071 : _87386 -> Prop) : (term83 _87386 x f _35071) = (term83 _87386 x f _35071).
Proof. exact (eq_refl (term83 _87386 x f _35071)). Qed.
Lemma lem3362279 {_87386 : Type'} (x : _87386) (f : type686 _87386) (_35071 : _87386 -> Prop) : ((term66 _87386 f _35071 x) = (term83 _87386 x f _35071)) = ((term83 _87386 x f _35071) = (term83 _87386 x f _35071)).
Proof. exact (MK_COMB (@lem3362272 _87386 x f _35071) (@lem3362278 _87386 x f _35071)). Qed.
Lemma lem3362281 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3362282 (x : Prop) : (x = x) = True.
Proof. exact (@lem3362281 Prop x). Qed.
Lemma lem3362283 {_87386 : Type'} (x : _87386) (f : type686 _87386) (_35071 : _87386 -> Prop) : ((term83 _87386 x f _35071) = (term83 _87386 x f _35071)) = True.
Proof. exact (@lem3362282 (term83 _87386 x f _35071)). Qed.
Lemma lem3362284 {_87386 : Type'} (x : _87386) (f : type686 _87386) (_35071 : _87386 -> Prop) : ((term66 _87386 f _35071 x) = (term83 _87386 x f _35071)) = True.
Proof. exact (TRANS (@lem3362279 _87386 x f _35071) (@lem3362283 _87386 x f _35071)). Qed.
Lemma lem3362285 {_87386 : Type'} (x : _87386) (f : type686 _87386) (_35071 : _87386 -> Prop) : True = ((term66 _87386 f _35071 x) = (term83 _87386 x f _35071)).
Proof. exact (SYM (@lem3362284 _87386 x f _35071)). Qed.
Lemma lem3362286 {_87386 : Type'} (x : _87386) (f : type686 _87386) (_35071 : _87386 -> Prop) : (term66 _87386 f _35071 x) = (term83 _87386 x f _35071).
Proof. exact (EQ_MP (@lem3362285 _87386 x f _35071) (@lem0)). Qed.
Lemma lem3362287 {_87386 : Type'} (_35071 : _87386 -> Prop) (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term83 _87386 x f _35071.
Proof. exact (EQ_MP (@lem3362286 _87386 x f _35071) (@lem3362194 _87386 _35071 f x h1)). Qed.
Lemma lem3362289 (b : Prop) (a : Prop) : (a \/ b) = (term77 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3362290 {_87386 : Type'} (f : type686 _87386) (_35071 : _87386 -> Prop) (x : _87386) : (term83 _87386 x f _35071) = (term86 _87386 f _35071 x).
Proof. exact (@lem3362289 (term60 _87386 f _35071) (@I (_87386 -> Prop) _35071 x)). Qed.
Lemma lem3362292 (a : Prop) : (term50 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3362293 {_87386 : Type'} (f : type686 _87386) (_35071 : _87386 -> Prop) : (term79 _87386 f _35071) = (@I ((_87386 -> Prop) -> Prop) f _35071).
Proof. exact (@lem3362292 (@I ((_87386 -> Prop) -> Prop) f _35071)). Qed.
Lemma lem3362294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3362295 {_87386 : Type'} (f : type686 _87386) (_35071 : _87386 -> Prop) : (term80 _87386 f _35071) = (term81 _87386 f _35071).
Proof. exact (MK_COMB (@lem3362294) (@lem3362293 _87386 f _35071)). Qed.
Lemma lem3362296 {_87386 : Type'} (_35071 : _87386 -> Prop) (x : _87386) : (@I (_87386 -> Prop) _35071 x) = (@I (_87386 -> Prop) _35071 x).
Proof. exact (eq_refl (@I (_87386 -> Prop) _35071 x)). Qed.
Lemma lem3362297 {_87386 : Type'} (f : type686 _87386) (_35071 : _87386 -> Prop) (x : _87386) : (term86 _87386 f _35071 x) = (term87 _87386 f _35071 x).
Proof. exact (MK_COMB (@lem3362295 _87386 f _35071) (@lem3362296 _87386 _35071 x)). Qed.
Lemma lem3362298 {_87386 : Type'} (f : type686 _87386) (_35071 : _87386 -> Prop) (x : _87386) : (term83 _87386 x f _35071) = (term87 _87386 f _35071 x).
Proof. exact (TRANS (@lem3362290 _87386 f _35071 x) (@lem3362297 _87386 f _35071 x)). Qed.
Lemma lem3362301 {_87386 : Type'} (_35071 : _87386 -> Prop) (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term87 _87386 f _35071 x.
Proof. exact (EQ_MP (@lem3362298 _87386 f _35071 x) (@lem3362287 _87386 _35071 f x h1)). Qed.
Lemma lem3362302 {_87386 : Type'} (_35071 : _87386 -> Prop) (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term87 _87386 f _35071 x.
Proof. exact (@lem3362301 _87386 _35071 f x h1). Qed.
Lemma lem3362303 {_87386 : Type'} (t : _87386 -> Prop) (f : type686 _87386) (x : _87386) (h1 : term30 _87386 f x) : term87 _87386 f t x.
Proof. exact (@lem3362302 _87386 t f x h1). Qed.
Lemma lem3362306 {_87386 : Type'} (x : _87386) (f : type686 _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : g t) : @I (_87386 -> Prop) t x.
Proof. exact (@lem3362303 _87386 t f x h1 (@lem3362258 _87386 f g t h2 h3)). Qed.
Lemma lem3362307 {_87386 : Type'} (x : _87386) (f : type686 _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : g t) : term88 _87386 t x.
Proof. exact (fun h0 : term69 _87386 t x => @lem3362306 _87386 x f g t h1 h2 h3). Qed.
Lemma lem3362309 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3362310 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) : (term88 _87386 t x) = (@I (_87386 -> Prop) t x).
Proof. exact (@lem3362309 (@I (_87386 -> Prop) t x)). Qed.
Lemma lem3362311 {_87386 : Type'} (x : _87386) (f : type686 _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : g t) : @I (_87386 -> Prop) t x.
Proof. exact (EQ_MP (@lem3362310 _87386 t x) (@lem3362307 _87386 x f g t h1 h2 h3)). Qed.
Lemma lem3362314 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3362316 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) : (term69 _87386 t x) = (term89 _87386 t x).
Proof. exact (@lem3362314 (@I (_87386 -> Prop) t x)). Qed.
Lemma lem3362319 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) (h1 : term52 _87386 t x) : term89 _87386 t x.
Proof. exact (EQ_MP (@lem3362316 _87386 t x) (@lem3362198 _87386 t x h1)). Qed.
Lemma lem3362322 {_87386 : Type'} (f : type686 _87386) (x : _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : term52 _87386 t x) (h4 : g t) : False.
Proof. exact (@lem3362319 _87386 t x h3 (@lem3362311 _87386 x f g t h1 h2 h4)). Qed.
Lemma lem3362323 {_87386 : Type'} (f : type686 _87386) (x : _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : term52 _87386 t x) (h4 : g t) : term90.
Proof. exact (fun h0 : ~ False => @lem3362322 _87386 f x g t h1 h2 h3 h4). Qed.
Lemma lem3362325 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3362326 : term90 = False.
Proof. exact (@lem3362325 False). Qed.
Lemma lem3362327 {_87386 : Type'} (f : type686 _87386) (x : _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : term52 _87386 t x) (h4 : g t) : False.
Proof. exact (EQ_MP (@lem3362326) (@lem3362323 _87386 f x g t h1 h2 h3 h4)). Qed.
Lemma lem3362328 {_87386 : Type'} (f : type686 _87386) (x : _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : term52 _87386 t x) (h4 : g t) : (term52 _87386 t x) = False.
Proof. exact (prop_ext (fun h5 : term52 _87386 t x => @lem3362327 _87386 f x g t h1 h2 h3 h4) (fun h5 : False => @lem3362073 _87386 t x h3)). Qed.
Lemma lem3362329 {_87386 : Type'} (f : type686 _87386) (x : _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : term52 _87386 t x) (h4 : g t) : False.
Proof. exact (EQ_MP (@lem3362328 _87386 f x g t h1 h2 h3 h4) (@lem3362073 _87386 t x h3)). Qed.
Lemma lem3362330 {_87386 : Type'} (f : type686 _87386) (x : _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : term52 _87386 t x) (h4 : g t) : (g t) = False.
Proof. exact (prop_ext (fun h5 : g t => @lem3362329 _87386 f x g t h1 h2 h3 h4) (fun h5 : False => @lem3362067 _87386 g t h4)). Qed.
Lemma lem3362331 {_87386 : Type'} (f : type686 _87386) (x : _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : term52 _87386 t x) (h4 : g t) : False.
Proof. exact (EQ_MP (@lem3362330 _87386 f x g t h1 h2 h3 h4) (@lem3362067 _87386 g t h4)). Qed.
Lemma lem3362332 {_87386 : Type'} (f : type686 _87386) (x : _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : term52 _87386 t x) (h4 : g t) : (term52 _87386 t x) = False.
Proof. exact (prop_ext (fun h5 : term52 _87386 t x => @lem3362331 _87386 f x g t h1 h2 h3 h4) (fun h5 : False => @lem3361951 _87386 t x h3)). Qed.
Lemma lem3362333 {_87386 : Type'} (f : type686 _87386) (x : _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : term52 _87386 t x) (h4 : g t) : False.
Proof. exact (EQ_MP (@lem3362332 _87386 f x g t h1 h2 h3 h4) (@lem3361951 _87386 t x h3)). Qed.
Lemma lem3362334 {_87386 : Type'} (x : _87386) (f : type686 _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : g t) : term51 _87386 t x.
Proof. exact (fun h0 : term52 _87386 t x => @lem3362333 _87386 f x g t h1 h2 h0 h3). Qed.
Lemma lem3362335 {_87386 : Type'} (x : _87386) (f : type686 _87386) (g : type686 _87386) (t : _87386 -> Prop) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) (h3 : g t) : t x.
Proof. exact (EQ_MP (@lem3361950 _87386 t x) (@lem3362334 _87386 x f g t h1 h2 h3)). Qed.
Lemma lem3362336 {_87386 : Type'} (t : _87386 -> Prop) (x : _87386) (g : type686 _87386) (f : type686 _87386) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) : term27 _87386 g t x.
Proof. exact (fun h0 : g t => @lem3362335 _87386 x f g t h1 h2 h0). Qed.
Lemma lem3362341 {_87386 : Type'} (x : _87386) (g : type686 _87386) (f : type686 _87386) (h1 : term30 _87386 f x) (h2 : term22 _87386 g f) : term30 _87386 g x.
Proof. exact (fun t : _87386 -> Prop => @lem3362336 _87386 t x g f h1 h2). Qed.
Lemma lem3362342 {_87386 : Type'} (x : _87386) (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term34 _87386 f g x.
Proof. exact (fun h0 : term30 _87386 f x => @lem3362341 _87386 x g f h0 h1). Qed.
Lemma lem3362347 {_87386 : Type'} (g : type686 _87386) (f : type686 _87386) (h1 : term22 _87386 g f) : term37 _87386 f g.
Proof. exact (fun x : _87386 => @lem3362342 _87386 x g f h1). Qed.
Lemma lem3362348 {_87386 : Type'} (f : type686 _87386) (g : type686 _87386) : term38 _87386 f g.
Proof. exact (fun h0 : term22 _87386 g f => @lem3362347 _87386 g f h0). Qed.
Lemma lem3362353 {_87386 : Type'} (f : type686 _87386) : term40 _87386 f.
Proof. exact (fun g : type686 _87386 => @lem3362348 _87386 f g). Qed.
Lemma lem3362358 {_87386 : Type'} : term42 _87386.
Proof. exact (fun f : type686 _87386 => @lem3362353 _87386 f). Qed.
Lemma lem3362359 {_87386 : Type'} : term44 _87386.
Proof. exact (EQ_MP (@lem3361943 _87386) (@lem3362358 _87386)). Qed.
Lemma lem3362361 {_87386 : Type'} : term44 _87386.
Proof. exact (@lem3361809 _87386 (@lem3362359 _87386)). Qed.
Lemma lem3362362 {_87386 : Type'} (h1 : term45 _87386) : False.
Proof. exact (@lem3362361 _87386 (@lem3361793 _87386 h1)). Qed.
Lemma lem3362363 {_87386 : Type'} (h1 : term45 _87386) : (term45 _87386) = False.
Proof. exact (prop_ext (fun h2 : term45 _87386 => @lem3362362 _87386 h1) (fun h2 : False => @lem3361793 _87386 h1)). Qed.
Lemma lem3362364 {_87386 : Type'} (h1 : term45 _87386) : False.
Proof. exact (EQ_MP (@lem3362363 _87386 h1) (@lem3361793 _87386 h1)). Qed.
Lemma lem3362365 {_87386 : Type'} : term44 _87386.
Proof. exact (fun h0 : term45 _87386 => @lem3362364 _87386 h0). Qed.
Lemma lem3362366 {_87386 : Type'} : term42 _87386.
Proof. exact (EQ_MP (@lem3361792 _87386) (@lem3362365 _87386)). Qed.
Lemma lem3362367 {_87386 : Type'} : term15 _87386.
Proof. exact (EQ_MP (@lem3361788 _87386) (@lem3362366 _87386)). Qed.
Lemma lem3362368 {_87386 : Type'} : term14 _87386.
Proof. exact (EQ_MP (@lem3361652 _87386) (@lem3362367 _87386)). Qed.
