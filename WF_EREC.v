Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_EREC_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import WF_REC_spec.
Require Import WF_UREC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18393_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem346582 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem346583 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem346584 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem346583 t1) (@lem346582 t1)). Qed.
Lemma lem346585 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem346584 t1 t2). Qed.
Lemma lem346586 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem346587 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem346586 t1 t2) (@lem346585 t1 t2)). Qed.
Lemma lem346588 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem346587 t1 t2 t3). Qed.
Lemma lem346589 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem346590 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem346589 t1 t2 t3) (@lem346588 t1 t2 t3)). Qed.
Lemma lem346591 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem346590 t1 t2 t3)). Qed.
Lemma lem346592 {A B : Type'} : term7 A B.
Proof. exact (fun lt2 : type1402 A => @lem339315 A B lt2). Qed.
Lemma lem346593 {A B : Type'} : term8 A B.
Proof. exact (fun lt2 : type1402 A => @lem318395 A B lt2). Qed.
Lemma lem346595 (p : Prop) : p = (term9 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem346596 {A B : Type'} (lt2 : type1402 A) : (term10 A B lt2) = (term11 A B lt2).
Proof. exact (@lem346595 (term10 A B lt2)). Qed.
Lemma lem346597 {A B : Type'} (lt2 : type1402 A) : (term11 A B lt2) = (term10 A B lt2).
Proof. exact (SYM (@lem346596 A B lt2)). Qed.
Lemma lem346598 {A B : Type'} (lt2 : type1402 A) (h1 : term12 A B lt2) : term12 A B lt2.
Proof. exact (h1). Qed.
Lemma lem346599 {A B : Type'} : term7 A B.
Proof. exact (@lem346592 A B). Qed.
Lemma lem346601 {A B : Type'} : term8 A B.
Proof. exact (@lem346593 A B). Qed.
Lemma lem346605 {A B : Type'} (lt2 : type1402 A) (h1 : term13 A B lt2) : term13 A B lt2.
Proof. exact (h1). Qed.
Lemma lem346606 {A B : Type'} (lt2 : type1402 A) : term14 A B lt2.
Proof. exact (fun h0 : term13 A B lt2 => @lem346605 A B lt2 h0). Qed.
Lemma lem346607 {A B : Type'} (lt2 : type1402 A) (h1 : term14 A B lt2) : term14 A B lt2.
Proof. exact (h1). Qed.
Lemma lem346608 {A B : Type'} (lt2 : type1402 A) (h1 : term13 A B lt2) : term13 A B lt2.
Proof. exact (h1). Qed.
Lemma lem346609 {A B : Type'} (lt2 : type1402 A) (h1 : term13 A B lt2) (h2 : term14 A B lt2) : term13 A B lt2.
Proof. exact (@lem346607 A B lt2 h2 (@lem346608 A B lt2 h1)). Qed.
Lemma lem346610 {A B : Type'} (lt2 : type1402 A) (h1 : term13 A B lt2) : term15 A B lt2.
Proof. exact (fun h0 : term14 A B lt2 => @lem346609 A B lt2 h1 h0). Qed.
Lemma lem346611 {A B : Type'} (lt2 : type1402 A) (h1 : term14 A B lt2) : term14 A B lt2.
Proof. exact (h1). Qed.
Lemma lem346612 {A B : Type'} (lt2 : type1402 A) (h1 : term13 A B lt2) (h2 : term14 A B lt2) : term13 A B lt2.
Proof. exact (@lem346610 A B lt2 h1 (@lem346611 A B lt2 h2)). Qed.
Lemma lem346613 {A B : Type'} (lt2 : type1402 A) (h1 : term14 A B lt2) : term14 A B lt2.
Proof. exact (fun h0 : term13 A B lt2 => @lem346612 A B lt2 h0 h1). Qed.
Lemma lem346614 {A B : Type'} (lt2 : type1402 A) : term16 A B lt2.
Proof. exact (fun h0 : term14 A B lt2 => @lem346613 A B lt2 h0). Qed.
Lemma lem346617 {A B : Type'} (lt2 : type1402 A) : term14 A B lt2.
Proof. exact (@lem346614 A B lt2 (@lem346606 A B lt2)). Qed.
Lemma lem346618 {A B : Type'} (lt2 : type1402 A) : term14 A B lt2.
Proof. exact (@lem346617 A B lt2). Qed.
Lemma lem346712 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem346713 {A B : Type'} : (term17 A B) = (term18 A B).
Proof. exact (@lem346712 (term7 A B)). Qed.
Lemma lem346754 {A B : Type'} : (term19 A B) = (term19 A B).
Proof. exact (eq_refl (term19 A B)). Qed.
Lemma lem346755 {A B : Type'} : (term20 A B) = (term21 A B).
Proof. exact (MK_COMB (@lem346754 A B) (@lem346713 A B)). Qed.
Lemma lem346758 {A B : Type'} (lt2 : type1402 A) : (term22 A B lt2) = (term22 A B lt2).
Proof. exact (eq_refl (term22 A B lt2)). Qed.
Lemma lem346759 {A B : Type'} (lt2 : type1402 A) : (term13 A B lt2) = (term23 A B lt2).
Proof. exact (MK_COMB (@lem346758 A B lt2) (@lem346755 A B)). Qed.
Lemma lem346762 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem346759 A B lt2)). Qed.
Lemma lem346763 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem346772 {A B : Type'} : (term26 A B) = (term27 A B).
Proof. exact (MK_COMB (@lem346763 A) (@lem346762 A B)). Qed.
Lemma lem346773 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : ((f x) = (H f x)) = ((f x) = (H f x)).
Proof. exact (eq_refl ((f x) = (H f x))). Qed.
Lemma lem346774 {A B : Type'} (H : type549 A B) (f : A -> B) : (term28 A B H f) = (term28 A B H f).
Proof. exact (fun_ext (fun x : A => @lem346773 A B H f x)). Qed.
Lemma lem346775 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346776 {A B : Type'} (H : type549 A B) (f : A -> B) : (term29 A B H f) = (term29 A B H f).
Proof. exact (MK_COMB (@lem346775 A) (@lem346774 A B H f)). Qed.
Lemma lem346777 {A B : Type'} (H : type549 A B) : (term30 A B H) = (term30 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem346776 A B H f)). Qed.
Lemma lem346778 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem346779 {A B : Type'} (H : type549 A B) : (term31 A B H) = (term31 A B H).
Proof. exact (MK_COMB (@lem346778 A B) (@lem346777 A B H)). Qed.
Lemma lem346780 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : ((H f x) = (H g x)) = ((H f x) = (H g x)).
Proof. exact (eq_refl ((H f x) = (H g x))). Qed.
Lemma lem346785 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term32 A B lt2 x f g z) = (term32 A B lt2 x f g z).
Proof. exact (eq_refl (term32 A B lt2 x f g z)). Qed.
Lemma lem346786 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term33 A B lt2 x f g) = (term33 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem346785 A B lt2 x f g z)). Qed.
Lemma lem346787 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346788 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term34 A B lt2 x f g) = (term34 A B lt2 x f g).
Proof. exact (MK_COMB (@lem346787 A) (@lem346786 A B lt2 x f g)). Qed.
Lemma lem346789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem346790 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term35 A B lt2 x f g) = (term35 A B lt2 x f g).
Proof. exact (MK_COMB (@lem346789) (@lem346788 A B lt2 x f g)). Qed.
Lemma lem346791 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term36 A B lt2 f H g x) = (term36 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem346790 A B lt2 x f g) (@lem346780 A B f H g x)). Qed.
Lemma lem346792 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term37 A B lt2 f H g) = (term37 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem346791 A B lt2 f H g x)). Qed.
Lemma lem346793 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346794 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term38 A B lt2 f H g) = (term38 A B lt2 f H g).
Proof. exact (MK_COMB (@lem346793 A) (@lem346792 A B lt2 f H g)). Qed.
Lemma lem346795 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term39 A B lt2 f H) = (term39 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem346794 A B lt2 f H g)). Qed.
Lemma lem346796 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem346797 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term40 A B lt2 f H) = (term40 A B lt2 f H).
Proof. exact (MK_COMB (@lem346796 A B) (@lem346795 A B lt2 f H)). Qed.
Lemma lem346798 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term41 A B lt2 H) = (term41 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem346797 A B lt2 f H)). Qed.
Lemma lem346799 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem346800 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term42 A B lt2 H) = (term42 A B lt2 H).
Proof. exact (MK_COMB (@lem346799 A B) (@lem346798 A B lt2 H)). Qed.
Lemma lem346801 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem346802 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term43 A B lt2 H) = (term43 A B lt2 H).
Proof. exact (MK_COMB (@lem346801) (@lem346800 A B lt2 H)). Qed.
Lemma lem346803 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term44 A B lt2 H) = (term44 A B lt2 H).
Proof. exact (MK_COMB (@lem346802 A B lt2 H) (@lem346779 A B H)). Qed.
Lemma lem346804 {A B : Type'} (lt2 : type1402 A) : (term45 A B lt2) = (term45 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem346803 A B lt2 H)). Qed.
Lemma lem346805 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem346806 {A B : Type'} (lt2 : type1402 A) : (term46 A B lt2) = (term46 A B lt2).
Proof. exact (MK_COMB (@lem346805 A B) (@lem346804 A B lt2)). Qed.
Lemma lem346809 {A : Type'} (lt2 : type1402 A) : (term47 A lt2) = (term47 A lt2).
Proof. exact (eq_refl (term47 A lt2)). Qed.
Lemma lem346810 {A B : Type'} (lt2 : type1402 A) : (term48 A B lt2) = (term48 A B lt2).
Proof. exact (MK_COMB (@lem346809 A lt2) (@lem346806 A B lt2)). Qed.
Lemma lem346811 {A B : Type'} : (term49 A B) = (term49 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem346810 A B lt2)). Qed.
Lemma lem346812 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem346813 {A B : Type'} : (term7 A B) = (term7 A B).
Proof. exact (MK_COMB (@lem346812 A) (@lem346811 A B)). Qed.
Lemma lem346814 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem346815 {A B : Type'} : (term18 A B) = (term18 A B).
Proof. exact (MK_COMB (@lem346814) (@lem346813 A B)). Qed.
Lemma lem346816 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (f = g).
Proof. exact (eq_refl (f = g)). Qed.
Lemma lem346817 {A B : Type'} (H : type549 A B) (g : A -> B) (x : A) : ((g x) = (H g x)) = ((g x) = (H g x)).
Proof. exact (eq_refl ((g x) = (H g x))). Qed.
Lemma lem346818 {A B : Type'} (H : type549 A B) (g : A -> B) : (term28 A B H g) = (term28 A B H g).
Proof. exact (fun_ext (fun x : A => @lem346817 A B H g x)). Qed.
Lemma lem346819 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346820 {A B : Type'} (H : type549 A B) (g : A -> B) : (term29 A B H g) = (term29 A B H g).
Proof. exact (MK_COMB (@lem346819 A) (@lem346818 A B H g)). Qed.
Lemma lem346821 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : ((f x) = (H f x)) = ((f x) = (H f x)).
Proof. exact (eq_refl ((f x) = (H f x))). Qed.
Lemma lem346822 {A B : Type'} (H : type549 A B) (f : A -> B) : (term28 A B H f) = (term28 A B H f).
Proof. exact (fun_ext (fun x : A => @lem346821 A B H f x)). Qed.
Lemma lem346823 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346824 {A B : Type'} (H : type549 A B) (f : A -> B) : (term29 A B H f) = (term29 A B H f).
Proof. exact (MK_COMB (@lem346823 A) (@lem346822 A B H f)). Qed.
Lemma lem346825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem346826 {A B : Type'} (H : type549 A B) (f : A -> B) : (term50 A B H f) = (term50 A B H f).
Proof. exact (MK_COMB (@lem346825) (@lem346824 A B H f)). Qed.
Lemma lem346827 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term51 A B f H g) = (term51 A B f H g).
Proof. exact (MK_COMB (@lem346826 A B H f) (@lem346820 A B H g)). Qed.
Lemma lem346828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem346829 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term52 A B f H g) = (term52 A B f H g).
Proof. exact (MK_COMB (@lem346828) (@lem346827 A B f H g)). Qed.
Lemma lem346830 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term53 A B H f g) = (term53 A B H f g).
Proof. exact (MK_COMB (@lem346829 A B f H g) (@lem346816 A B f g)). Qed.
Lemma lem346831 {A B : Type'} (H : type549 A B) (f : A -> B) : (term54 A B H f) = (term54 A B H f).
Proof. exact (fun_ext (fun g : A -> B => @lem346830 A B H f g)). Qed.
Lemma lem346832 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem346833 {A B : Type'} (H : type549 A B) (f : A -> B) : (term55 A B H f) = (term55 A B H f).
Proof. exact (MK_COMB (@lem346832 A B) (@lem346831 A B H f)). Qed.
Lemma lem346834 {A B : Type'} (H : type549 A B) : (term56 A B H) = (term56 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem346833 A B H f)). Qed.
Lemma lem346835 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem346836 {A B : Type'} (H : type549 A B) : (term57 A B H) = (term57 A B H).
Proof. exact (MK_COMB (@lem346835 A B) (@lem346834 A B H)). Qed.
Lemma lem346837 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : ((H f x) = (H g x)) = ((H f x) = (H g x)).
Proof. exact (eq_refl ((H f x) = (H g x))). Qed.
Lemma lem346842 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term32 A B lt2 x f g z) = (term32 A B lt2 x f g z).
Proof. exact (eq_refl (term32 A B lt2 x f g z)). Qed.
Lemma lem346843 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term33 A B lt2 x f g) = (term33 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem346842 A B lt2 x f g z)). Qed.
Lemma lem346844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346845 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term34 A B lt2 x f g) = (term34 A B lt2 x f g).
Proof. exact (MK_COMB (@lem346844 A) (@lem346843 A B lt2 x f g)). Qed.
Lemma lem346846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem346847 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term35 A B lt2 x f g) = (term35 A B lt2 x f g).
Proof. exact (MK_COMB (@lem346846) (@lem346845 A B lt2 x f g)). Qed.
Lemma lem346848 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term36 A B lt2 f H g x) = (term36 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem346847 A B lt2 x f g) (@lem346837 A B f H g x)). Qed.
Lemma lem346849 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term37 A B lt2 f H g) = (term37 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem346848 A B lt2 f H g x)). Qed.
Lemma lem346850 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346851 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term38 A B lt2 f H g) = (term38 A B lt2 f H g).
Proof. exact (MK_COMB (@lem346850 A) (@lem346849 A B lt2 f H g)). Qed.
Lemma lem346852 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term39 A B lt2 f H) = (term39 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem346851 A B lt2 f H g)). Qed.
Lemma lem346853 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem346854 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term40 A B lt2 f H) = (term40 A B lt2 f H).
Proof. exact (MK_COMB (@lem346853 A B) (@lem346852 A B lt2 f H)). Qed.
Lemma lem346855 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term41 A B lt2 H) = (term41 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem346854 A B lt2 f H)). Qed.
Lemma lem346856 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem346857 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term42 A B lt2 H) = (term42 A B lt2 H).
Proof. exact (MK_COMB (@lem346856 A B) (@lem346855 A B lt2 H)). Qed.
Lemma lem346858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem346859 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term43 A B lt2 H) = (term43 A B lt2 H).
Proof. exact (MK_COMB (@lem346858) (@lem346857 A B lt2 H)). Qed.
Lemma lem346860 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term58 A B lt2 H) = (term58 A B lt2 H).
Proof. exact (MK_COMB (@lem346859 A B lt2 H) (@lem346836 A B H)). Qed.
Lemma lem346861 {A B : Type'} (lt2 : type1402 A) : (term59 A B lt2) = (term59 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem346860 A B lt2 H)). Qed.
Lemma lem346862 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem346863 {A B : Type'} (lt2 : type1402 A) : (term60 A B lt2) = (term60 A B lt2).
Proof. exact (MK_COMB (@lem346862 A B) (@lem346861 A B lt2)). Qed.
Lemma lem346866 {A : Type'} (lt2 : type1402 A) : (term47 A lt2) = (term47 A lt2).
Proof. exact (eq_refl (term47 A lt2)). Qed.
Lemma lem346867 {A B : Type'} (lt2 : type1402 A) : (term61 A B lt2) = (term61 A B lt2).
Proof. exact (MK_COMB (@lem346866 A lt2) (@lem346863 A B lt2)). Qed.
Lemma lem346868 {A B : Type'} : (term62 A B) = (term62 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem346867 A B lt2)). Qed.
Lemma lem346869 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem346870 {A B : Type'} : (term8 A B) = (term8 A B).
Proof. exact (MK_COMB (@lem346869 A) (@lem346868 A B)). Qed.
Lemma lem346871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem346872 {A B : Type'} : (term19 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem346871) (@lem346870 A B)). Qed.
Lemma lem346873 {A B : Type'} : (term21 A B) = (term21 A B).
Proof. exact (MK_COMB (@lem346872 A B) (@lem346815 A B)). Qed.
Lemma lem346874 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : ((f x) = (H f x)) = ((f x) = (H f x)).
Proof. exact (eq_refl ((f x) = (H f x))). Qed.
Lemma lem346875 {A B : Type'} (H : type549 A B) (f : A -> B) : (term28 A B H f) = (term28 A B H f).
Proof. exact (fun_ext (fun x : A => @lem346874 A B H f x)). Qed.
Lemma lem346876 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346877 {A B : Type'} (H : type549 A B) (f : A -> B) : (term29 A B H f) = (term29 A B H f).
Proof. exact (MK_COMB (@lem346876 A) (@lem346875 A B H f)). Qed.
Lemma lem346878 {A B : Type'} (H : type549 A B) : (term30 A B H) = (term30 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem346877 A B H f)). Qed.
Lemma lem346879 {A B : Type'} : (@ex1 (A -> B)) = (@ex1 (A -> B)).
Proof. exact (eq_refl (@ex1 (A -> B))). Qed.
Lemma lem346880 {A B : Type'} (H : type549 A B) : (term63 A B H) = (term63 A B H).
Proof. exact (MK_COMB (@lem346879 A B) (@lem346878 A B H)). Qed.
Lemma lem346881 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : ((H f x) = (H g x)) = ((H f x) = (H g x)).
Proof. exact (eq_refl ((H f x) = (H g x))). Qed.
Lemma lem346886 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term32 A B lt2 x f g z) = (term32 A B lt2 x f g z).
Proof. exact (eq_refl (term32 A B lt2 x f g z)). Qed.
Lemma lem346887 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term33 A B lt2 x f g) = (term33 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem346886 A B lt2 x f g z)). Qed.
Lemma lem346888 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346889 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term34 A B lt2 x f g) = (term34 A B lt2 x f g).
Proof. exact (MK_COMB (@lem346888 A) (@lem346887 A B lt2 x f g)). Qed.
Lemma lem346890 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem346891 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term35 A B lt2 x f g) = (term35 A B lt2 x f g).
Proof. exact (MK_COMB (@lem346890) (@lem346889 A B lt2 x f g)). Qed.
Lemma lem346892 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term36 A B lt2 f H g x) = (term36 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem346891 A B lt2 x f g) (@lem346881 A B f H g x)). Qed.
Lemma lem346893 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term37 A B lt2 f H g) = (term37 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem346892 A B lt2 f H g x)). Qed.
Lemma lem346894 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem346895 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term38 A B lt2 f H g) = (term38 A B lt2 f H g).
Proof. exact (MK_COMB (@lem346894 A) (@lem346893 A B lt2 f H g)). Qed.
Lemma lem346896 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term39 A B lt2 f H) = (term39 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem346895 A B lt2 f H g)). Qed.
Lemma lem346897 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem346898 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term40 A B lt2 f H) = (term40 A B lt2 f H).
Proof. exact (MK_COMB (@lem346897 A B) (@lem346896 A B lt2 f H)). Qed.
Lemma lem346899 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term41 A B lt2 H) = (term41 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem346898 A B lt2 f H)). Qed.
Lemma lem346900 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem346901 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term42 A B lt2 H) = (term42 A B lt2 H).
Proof. exact (MK_COMB (@lem346900 A B) (@lem346899 A B lt2 H)). Qed.
Lemma lem346902 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem346903 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term43 A B lt2 H) = (term43 A B lt2 H).
Proof. exact (MK_COMB (@lem346902) (@lem346901 A B lt2 H)). Qed.
Lemma lem346904 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term64 A B lt2 H) = (term64 A B lt2 H).
Proof. exact (MK_COMB (@lem346903 A B lt2 H) (@lem346880 A B H)). Qed.
Lemma lem346905 {A B : Type'} (lt2 : type1402 A) : (term65 A B lt2) = (term65 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem346904 A B lt2 H)). Qed.
Lemma lem346906 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem346907 {A B : Type'} (lt2 : type1402 A) : (term66 A B lt2) = (term66 A B lt2).
Proof. exact (MK_COMB (@lem346906 A B) (@lem346905 A B lt2)). Qed.
Lemma lem346910 {A : Type'} (lt2 : type1402 A) : (term47 A lt2) = (term47 A lt2).
Proof. exact (eq_refl (term47 A lt2)). Qed.
Lemma lem346911 {A B : Type'} (lt2 : type1402 A) : (term10 A B lt2) = (term10 A B lt2).
Proof. exact (MK_COMB (@lem346910 A lt2) (@lem346907 A B lt2)). Qed.
Lemma lem346912 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem346913 {A B : Type'} (lt2 : type1402 A) : (term12 A B lt2) = (term12 A B lt2).
Proof. exact (MK_COMB (@lem346912) (@lem346911 A B lt2)). Qed.
Lemma lem346914 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem346915 {A B : Type'} (lt2 : type1402 A) : (term22 A B lt2) = (term22 A B lt2).
Proof. exact (MK_COMB (@lem346914) (@lem346913 A B lt2)). Qed.
Lemma lem346916 {A B : Type'} (lt2 : type1402 A) : (term23 A B lt2) = (term23 A B lt2).
Proof. exact (MK_COMB (@lem346915 A B lt2) (@lem346873 A B)). Qed.
Lemma lem346917 {A B : Type'} : (term25 A B) = (term25 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem346916 A B lt2)). Qed.
Lemma lem346918 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem346919 {A B : Type'} : (term27 A B) = (term27 A B).
Proof. exact (MK_COMB (@lem346918 A) (@lem346917 A B)). Qed.
Lemma lem347104 {A B : Type'} : (term26 A B) = (term27 A B).
Proof. exact (TRANS (@lem346772 A B) (@lem346919 A B)). Qed.
Lemma lem347105 {A B : Type'} : (term27 A B) = (term26 A B).
Proof. exact (SYM (@lem347104 A B)). Qed.
Lemma lem347106 {A B : Type'} (lt2 : type1402 A) (h1 : term12 A B lt2) : term12 A B lt2.
Proof. exact (h1). Qed.
Lemma lem347107 {A B : Type'} (h1 : term8 A B) : term8 A B.
Proof. exact (h1). Qed.
Lemma lem347108 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem347116 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term67 A B lt2 x f g z) = (term68 A B lt2 x f g z).
Proof. exact (@lem17362 (lt2 z x) ((f z) = (g z))). Qed.
Lemma lem347117 {A : Type'} (P : A -> Prop) : (term69 A P) = (term70 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem347118 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term71 A B lt2 x f g) = (term72 A B lt2 x f g).
Proof. exact (@lem347117 A (term33 A B lt2 x f g)). Qed.
Lemma lem347119 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term73 A B lt2 x f g z) = (term32 A B lt2 x f g z).
Proof. exact (eq_refl (term73 A B lt2 x f g z)). Qed.
Lemma lem347120 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem347121 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term74 A B lt2 x f g z) = (term67 A B lt2 x f g z).
Proof. exact (MK_COMB (@lem347120) (@lem347119 A B lt2 x f g z)). Qed.
Lemma lem347122 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term74 A B lt2 x f g z) = (term68 A B lt2 x f g z).
Proof. exact (TRANS (@lem347121 A B lt2 x f g z) (@lem347116 A B lt2 x f g z)). Qed.
Lemma lem347123 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term75 A B lt2 x f g) = (term76 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem347122 A B lt2 x f g z)). Qed.
Lemma lem347124 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem347125 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term72 A B lt2 x f g) = (term77 A B lt2 x f g).
Proof. exact (MK_COMB (@lem347124 A) (@lem347123 A B lt2 x f g)). Qed.
Lemma lem347126 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term71 A B lt2 x f g) = (term77 A B lt2 x f g).
Proof. exact (TRANS (@lem347118 A B lt2 x f g) (@lem347125 A B lt2 x f g)). Qed.
Lemma lem347127 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : ((H f x) = (H g x)) = ((H f x) = (H g x)).
Proof. exact (eq_refl ((H f x) = (H g x))). Qed.
Lemma lem347128 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem347129 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term78 A B lt2 x f g) = (term79 A B lt2 x f g).
Proof. exact (MK_COMB (@lem347128) (@lem347126 A B lt2 x f g)). Qed.
Lemma lem347130 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term80 A B lt2 f H g x) = (term81 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem347129 A B lt2 x f g) (@lem347127 A B f H g x)). Qed.
Lemma lem347131 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term36 A B lt2 f H g x) = (term80 A B lt2 f H g x).
Proof. exact (@lem17265 (term34 A B lt2 x f g) ((H f x) = (H g x))). Qed.
Lemma lem347132 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term36 A B lt2 f H g x) = (term81 A B lt2 f H g x).
Proof. exact (TRANS (@lem347131 A B lt2 f H g x) (@lem347130 A B lt2 f H g x)). Qed.
Lemma lem347133 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term37 A B lt2 f H g) = (term82 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem347132 A B lt2 f H g x)). Qed.
Lemma lem347134 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem347135 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term38 A B lt2 f H g) = (term83 A B lt2 f H g).
Proof. exact (MK_COMB (@lem347134 A) (@lem347133 A B lt2 f H g)). Qed.
Lemma lem347136 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term39 A B lt2 f H) = (term84 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem347135 A B lt2 f H g)). Qed.
Lemma lem347137 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347138 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term40 A B lt2 f H) = (term85 A B lt2 f H).
Proof. exact (MK_COMB (@lem347137 A B) (@lem347136 A B lt2 f H)). Qed.
Lemma lem347139 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term41 A B lt2 H) = (term86 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem347138 A B lt2 f H)). Qed.
Lemma lem347140 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347141 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term42 A B lt2 H) = (term87 A B lt2 H).
Proof. exact (MK_COMB (@lem347140 A B) (@lem347139 A B lt2 H)). Qed.
Lemma lem347143 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : ((f x) = (H f x)) = ((f x) = (H f x)).
Proof. exact (eq_refl ((f x) = (H f x))). Qed.
Lemma lem347144 {A : Type'} (P : A -> Prop) : (term69 A P) = (term70 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem347145 {A B : Type'} (H : type549 A B) (f : A -> B) : (term88 A B H f) = (term89 A B H f).
Proof. exact (@lem347144 A (term28 A B H f)). Qed.
Lemma lem347146 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term90 A B H f x) = ((f x) = (H f x)).
Proof. exact (eq_refl (term90 A B H f x)). Qed.
Lemma lem347147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem347149 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term91 A B H f x) = (term92 A B H f x).
Proof. exact (MK_COMB (@lem347147) (@lem347146 A B H f x)). Qed.
Lemma lem347150 {A B : Type'} (H : type549 A B) (f : A -> B) : (term93 A B H f) = (term94 A B H f).
Proof. exact (fun_ext (fun x : A => @lem347149 A B H f x)). Qed.
Lemma lem347151 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem347152 {A B : Type'} (H : type549 A B) (f : A -> B) : (term89 A B H f) = (term95 A B H f).
Proof. exact (MK_COMB (@lem347151 A) (@lem347150 A B H f)). Qed.
Lemma lem347153 {A B : Type'} (H : type549 A B) (f : A -> B) : (term88 A B H f) = (term95 A B H f).
Proof. exact (TRANS (@lem347145 A B H f) (@lem347152 A B H f)). Qed.
Lemma lem347154 {A B : Type'} (H : type549 A B) (f : A -> B) : (term28 A B H f) = (term28 A B H f).
Proof. exact (fun_ext (fun x : A => @lem347143 A B H f x)). Qed.
Lemma lem347155 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem347156 {A B : Type'} (H : type549 A B) (f : A -> B) : (term29 A B H f) = (term29 A B H f).
Proof. exact (MK_COMB (@lem347155 A) (@lem347154 A B H f)). Qed.
Lemma lem347157 {A B : Type'} (f' : A -> B) (f : A -> B) : (term96 A B f' f) = (term96 A B f' f).
Proof. exact (eq_refl (term96 A B f' f)). Qed.
Lemma lem347159 {A B : Type'} (H : type549 A B) (f : A -> B) : (term97 A B H f) = (term29 A B H f).
Proof. exact (eq_refl (term97 A B H f)). Qed.
Lemma lem347160 {A B : Type'} (H : type549 A B) (f' : A -> B) : (term97 A B H f') = (term29 A B H f').
Proof. exact (eq_refl (term97 A B H f')). Qed.
Lemma lem347161 {A B : Type'} (H : type549 A B) (f' : A -> B) : (term29 A B H f') = (term29 A B H f').
Proof. exact (@lem347156 A B H f'). Qed.
Lemma lem347162 {A B : Type'} (P : type572 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (@lem18393 (A -> B) P). Qed.
Lemma lem347163 {A B : Type'} (H : type549 A B) : (term100 A B H) = (term101 A B H).
Proof. exact (@lem347162 A B (term30 A B H)). Qed.
Lemma lem347164 {A B : Type'} (H : type549 A B) (f' : A -> B) : (term97 A B H f') = (term29 A B H f').
Proof. exact (TRANS (@lem347160 A B H f') (@lem347161 A B H f')). Qed.
Lemma lem347165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem347166 {A B : Type'} (H : type549 A B) (f' : A -> B) : (term102 A B H f') = (term50 A B H f').
Proof. exact (MK_COMB (@lem347165) (@lem347164 A B H f')). Qed.
Lemma lem347167 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term103 A B H f' f) = (term104 A B H f' f).
Proof. exact (MK_COMB (@lem347166 A B H f') (@lem347157 A B f' f)). Qed.
Lemma lem347168 {A B : Type'} (H : type549 A B) (f : A -> B) : (term97 A B H f) = (term29 A B H f).
Proof. exact (TRANS (@lem347159 A B H f) (@lem347156 A B H f)). Qed.
Lemma lem347169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem347170 {A B : Type'} (H : type549 A B) (f : A -> B) : (term102 A B H f) = (term50 A B H f).
Proof. exact (MK_COMB (@lem347169) (@lem347168 A B H f)). Qed.
Lemma lem347171 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term105 A B H f' f) = (term106 A B H f' f).
Proof. exact (MK_COMB (@lem347170 A B H f) (@lem347167 A B H f' f)). Qed.
Lemma lem347172 {A B : Type'} (H : type549 A B) (f : A -> B) : (term107 A B H f) = (term108 A B H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem347171 A B H f' f)). Qed.
Lemma lem347173 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347174 {A B : Type'} (H : type549 A B) (f : A -> B) : (term109 A B H f) = (term110 A B H f).
Proof. exact (MK_COMB (@lem347173 A B) (@lem347172 A B H f)). Qed.
Lemma lem347175 {A B : Type'} (H : type549 A B) : (term111 A B H) = (term112 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem347174 A B H f)). Qed.
Lemma lem347176 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347177 {A B : Type'} (H : type549 A B) : (term113 A B H) = (term114 A B H).
Proof. exact (MK_COMB (@lem347176 A B) (@lem347175 A B H)). Qed.
Lemma lem347178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem347179 {A B : Type'} (H : type549 A B) (f : A -> B) : (term115 A B H f) = (term88 A B H f).
Proof. exact (MK_COMB (@lem347178) (@lem347159 A B H f)). Qed.
Lemma lem347180 {A B : Type'} (H : type549 A B) (f : A -> B) : (term115 A B H f) = (term95 A B H f).
Proof. exact (TRANS (@lem347179 A B H f) (@lem347153 A B H f)). Qed.
Lemma lem347181 {A B : Type'} (H : type549 A B) : (term116 A B H) = (term117 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem347180 A B H f)). Qed.
Lemma lem347182 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347183 {A B : Type'} (H : type549 A B) : (term118 A B H) = (term119 A B H).
Proof. exact (MK_COMB (@lem347182 A B) (@lem347181 A B H)). Qed.
Lemma lem347184 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem347185 {A B : Type'} (H : type549 A B) : (term120 A B H) = (term121 A B H).
Proof. exact (MK_COMB (@lem347184) (@lem347183 A B H)). Qed.
Lemma lem347186 {A B : Type'} (H : type549 A B) : (term101 A B H) = (term122 A B H).
Proof. exact (MK_COMB (@lem347185 A B H) (@lem347177 A B H)). Qed.
Lemma lem347187 {A B : Type'} (H : type549 A B) : (term100 A B H) = (term122 A B H).
Proof. exact (TRANS (@lem347163 A B H) (@lem347186 A B H)). Qed.
Lemma lem347188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem347189 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term123 A B lt2 H) = (term124 A B lt2 H).
Proof. exact (MK_COMB (@lem347188) (@lem347141 A B lt2 H)). Qed.
Lemma lem347190 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term125 A B lt2 H) = (term126 A B lt2 H).
Proof. exact (MK_COMB (@lem347189 A B lt2 H) (@lem347187 A B H)). Qed.
Lemma lem347191 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term127 A B lt2 H) = (term125 A B lt2 H).
Proof. exact (@lem17362 (term42 A B lt2 H) (term63 A B H)). Qed.
Lemma lem347192 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term127 A B lt2 H) = (term126 A B lt2 H).
Proof. exact (TRANS (@lem347191 A B lt2 H) (@lem347190 A B lt2 H)). Qed.
Lemma lem347193 {A B : Type'} (P : type111 A B) : (term128 A B P) = (term129 A B P).
Proof. exact (@lem18392 (type549 A B) P). Qed.
Lemma lem347194 {A B : Type'} (lt2 : type1402 A) : (term130 A B lt2) = (term131 A B lt2).
Proof. exact (@lem347193 A B (term65 A B lt2)). Qed.
Lemma lem347195 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term132 A B lt2 H) = (term64 A B lt2 H).
Proof. exact (eq_refl (term132 A B lt2 H)). Qed.
Lemma lem347196 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem347197 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term133 A B lt2 H) = (term127 A B lt2 H).
Proof. exact (MK_COMB (@lem347196) (@lem347195 A B lt2 H)). Qed.
Lemma lem347198 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term133 A B lt2 H) = (term126 A B lt2 H).
Proof. exact (TRANS (@lem347197 A B lt2 H) (@lem347192 A B lt2 H)). Qed.
Lemma lem347199 {A B : Type'} (lt2 : type1402 A) : (term134 A B lt2) = (term135 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem347198 A B lt2 H)). Qed.
Lemma lem347200 {A B : Type'} : (@ex ((A -> B) -> A -> B)) = (@ex ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> B))). Qed.
Lemma lem347201 {A B : Type'} (lt2 : type1402 A) : (term131 A B lt2) = (term136 A B lt2).
Proof. exact (MK_COMB (@lem347200 A B) (@lem347199 A B lt2)). Qed.
Lemma lem347202 {A B : Type'} (lt2 : type1402 A) : (term130 A B lt2) = (term136 A B lt2).
Proof. exact (TRANS (@lem347194 A B lt2) (@lem347201 A B lt2)). Qed.
Lemma lem347204 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347205 {A B : Type'} (lt2 : type1402 A) : (term138 A B lt2) = (term139 A B lt2).
Proof. exact (MK_COMB (@lem347204 A lt2) (@lem347202 A B lt2)). Qed.
Lemma lem347206 {A B : Type'} (lt2 : type1402 A) : (term12 A B lt2) = (term138 A B lt2).
Proof. exact (@lem17362 (@WF A lt2) (term66 A B lt2)). Qed.
Lemma lem347207 {A B : Type'} (lt2 : type1402 A) : (term12 A B lt2) = (term139 A B lt2).
Proof. exact (TRANS (@lem347206 A B lt2) (@lem347205 A B lt2)). Qed.
Lemma lem347373 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem347374 {A B : Type'} (P : Prop) (Q : type572 A B) : (term142 A B P Q) = (term143 A B P Q).
Proof. exact (@lem347373 (A -> B) P Q). Qed.
Lemma lem347375 {A B : Type'} (H : type549 A B) (f : A -> B) : (term144 A B H f) = (term145 A B H f).
Proof. exact (@lem347374 A B (term29 A B H f) (term146 A B H f)). Qed.
Lemma lem347376 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term147 A B H f f') = (term104 A B H f' f).
Proof. exact (eq_refl (term147 A B H f f')). Qed.
Lemma lem347377 {A B : Type'} (H : type549 A B) (f : A -> B) : (term50 A B H f) = (term50 A B H f).
Proof. exact (eq_refl (term50 A B H f)). Qed.
Lemma lem347378 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term148 A B H f f') = (term106 A B H f' f).
Proof. exact (MK_COMB (@lem347377 A B H f) (@lem347376 A B H f' f)). Qed.
Lemma lem347379 {A B : Type'} (H : type549 A B) (f : A -> B) : (term149 A B H f) = (term108 A B H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem347378 A B H f' f)). Qed.
Lemma lem347380 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347381 {A B : Type'} (H : type549 A B) (f : A -> B) : (term144 A B H f) = (term110 A B H f).
Proof. exact (MK_COMB (@lem347380 A B) (@lem347379 A B H f)). Qed.
Lemma lem347382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347383 {A B : Type'} (H : type549 A B) (f : A -> B) : (term150 A B H f) = (term151 A B H f).
Proof. exact (MK_COMB (@lem347382) (@lem347381 A B H f)). Qed.
Lemma lem347384 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term147 A B H f f') = (term104 A B H f' f).
Proof. exact (eq_refl (term147 A B H f f')). Qed.
Lemma lem347385 {A B : Type'} (H : type549 A B) (f : A -> B) : (term152 A B H f) = (term146 A B H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem347384 A B H f' f)). Qed.
Lemma lem347386 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347387 {A B : Type'} (H : type549 A B) (f : A -> B) : (term153 A B H f) = (term154 A B H f).
Proof. exact (MK_COMB (@lem347386 A B) (@lem347385 A B H f)). Qed.
Lemma lem347388 {A B : Type'} (H : type549 A B) (f : A -> B) : (term50 A B H f) = (term50 A B H f).
Proof. exact (eq_refl (term50 A B H f)). Qed.
Lemma lem347389 {A B : Type'} (H : type549 A B) (f : A -> B) : (term145 A B H f) = (term155 A B H f).
Proof. exact (MK_COMB (@lem347388 A B H f) (@lem347387 A B H f)). Qed.
Lemma lem347390 {A B : Type'} (H : type549 A B) (f : A -> B) : ((term144 A B H f) = (term145 A B H f)) = ((term110 A B H f) = (term155 A B H f)).
Proof. exact (MK_COMB (@lem347383 A B H f) (@lem347389 A B H f)). Qed.
Lemma lem347391 {A B : Type'} (H : type549 A B) (f : A -> B) : (term110 A B H f) = (term155 A B H f).
Proof. exact (EQ_MP (@lem347390 A B H f) (@lem347375 A B H f)). Qed.
Lemma lem347448 {A B : Type'} (H : type549 A B) : (term112 A B H) = (term156 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem347391 A B H f)). Qed.
Lemma lem347449 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347450 {A B : Type'} (H : type549 A B) : (term114 A B H) = (term157 A B H).
Proof. exact (MK_COMB (@lem347449 A B) (@lem347448 A B H)). Qed.
Lemma lem347499 {A B : Type'} (H : type549 A B) : (term121 A B H) = (term121 A B H).
Proof. exact (eq_refl (term121 A B H)). Qed.
Lemma lem347500 {A B : Type'} (H : type549 A B) : (term122 A B H) = (term158 A B H).
Proof. exact (MK_COMB (@lem347499 A B H) (@lem347450 A B H)). Qed.
Lemma lem347501 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term124 A B lt2 H) = (term124 A B lt2 H).
Proof. exact (eq_refl (term124 A B lt2 H)). Qed.
Lemma lem347502 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term126 A B lt2 H) = (term159 A B lt2 H).
Proof. exact (MK_COMB (@lem347501 A B lt2 H) (@lem347500 A B H)). Qed.
Lemma lem347503 {A B : Type'} (lt2 : type1402 A) : (term135 A B lt2) = (term160 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem347502 A B lt2 H)). Qed.
Lemma lem347504 {A B : Type'} : (@ex ((A -> B) -> A -> B)) = (@ex ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> B))). Qed.
Lemma lem347505 {A B : Type'} (lt2 : type1402 A) : (term136 A B lt2) = (term161 A B lt2).
Proof. exact (MK_COMB (@lem347504 A B) (@lem347503 A B lt2)). Qed.
Lemma lem347554 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347555 {A B : Type'} (lt2 : type1402 A) : (term139 A B lt2) = (term162 A B lt2).
Proof. exact (MK_COMB (@lem347554 A lt2) (@lem347505 A B lt2)). Qed.
Lemma lem347557 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem347558 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (@lem347557 A P Q). Qed.
Lemma lem347559 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term165 A B lt2 f H g x) = (term166 A B lt2 f H g x).
Proof. exact (@lem347558 A (term76 A B lt2 x f g) ((H f x) = (H g x))). Qed.
Lemma lem347560 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term167 A B lt2 x f g z) = (term68 A B lt2 x f g z).
Proof. exact (eq_refl (term167 A B lt2 x f g z)). Qed.
Lemma lem347561 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term168 A B lt2 x f g) = (term76 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem347560 A B lt2 x f g z)). Qed.
Lemma lem347562 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem347563 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term169 A B lt2 x f g) = (term77 A B lt2 x f g).
Proof. exact (MK_COMB (@lem347562 A) (@lem347561 A B lt2 x f g)). Qed.
Lemma lem347564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem347565 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term170 A B lt2 x f g) = (term79 A B lt2 x f g).
Proof. exact (MK_COMB (@lem347564) (@lem347563 A B lt2 x f g)). Qed.
Lemma lem347566 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : ((H f x) = (H g x)) = ((H f x) = (H g x)).
Proof. exact (eq_refl ((H f x) = (H g x))). Qed.
Lemma lem347567 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term165 A B lt2 f H g x) = (term81 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem347565 A B lt2 x f g) (@lem347566 A B f H g x)). Qed.
Lemma lem347568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347569 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term171 A B lt2 f H g x) = (term172 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem347568) (@lem347567 A B lt2 f H g x)). Qed.
Lemma lem347570 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term167 A B lt2 x f g z) = (term68 A B lt2 x f g z).
Proof. exact (eq_refl (term167 A B lt2 x f g z)). Qed.
Lemma lem347571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem347572 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term173 A B lt2 x f g z) = (term174 A B lt2 x f g z).
Proof. exact (MK_COMB (@lem347571) (@lem347570 A B lt2 x f g z)). Qed.
Lemma lem347573 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : ((H f x) = (H g x)) = ((H f x) = (H g x)).
Proof. exact (eq_refl ((H f x) = (H g x))). Qed.
Lemma lem347574 {A B : Type'} (lt2 : type1402 A) (z : A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term175 A B lt2 z f H g x) = (term176 A B lt2 z f H g x).
Proof. exact (MK_COMB (@lem347572 A B lt2 x f g z) (@lem347573 A B f H g x)). Qed.
Lemma lem347575 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term177 A B lt2 f H g x) = (term178 A B lt2 f H g x).
Proof. exact (fun_ext (fun z : A => @lem347574 A B lt2 z f H g x)). Qed.
Lemma lem347576 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem347577 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term166 A B lt2 f H g x) = (term179 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem347576 A) (@lem347575 A B lt2 f H g x)). Qed.
Lemma lem347578 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : ((term165 A B lt2 f H g x) = (term166 A B lt2 f H g x)) = ((term81 A B lt2 f H g x) = (term179 A B lt2 f H g x)).
Proof. exact (MK_COMB (@lem347569 A B lt2 f H g x) (@lem347577 A B lt2 f H g x)). Qed.
Lemma lem347579 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term81 A B lt2 f H g x) = (term179 A B lt2 f H g x).
Proof. exact (EQ_MP (@lem347578 A B lt2 f H g x) (@lem347559 A B lt2 f H g x)). Qed.
Lemma lem347580 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term82 A B lt2 f H g) = (term180 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem347579 A B lt2 f H g x)). Qed.
Lemma lem347581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem347582 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term83 A B lt2 f H g) = (term181 A B lt2 f H g).
Proof. exact (MK_COMB (@lem347581 A) (@lem347580 A B lt2 f H g)). Qed.
Lemma lem347584 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem347585 {A : Type'} (P : type1402 A) : (term184 A P) = (term185 A P).
Proof. exact (@lem347584 A A P). Qed.
Lemma lem347586 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term186 A B lt2 f H g) = (term187 A B lt2 f H g).
Proof. exact (@lem347585 A (term188 A B lt2 f H g)). Qed.
Lemma lem347587 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term189 A B lt2 f H g x) = (term178 A B lt2 f H g x).
Proof. exact (eq_refl (term189 A B lt2 f H g x)). Qed.
Lemma lem347588 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem347589 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) (z : A) : (term190 A B lt2 f H g x z) = (term191 A B lt2 f H g x z).
Proof. exact (MK_COMB (@lem347587 A B lt2 f H g x) (@lem347588 A z)). Qed.
Lemma lem347590 {A B : Type'} (lt2 : type1402 A) (z : A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term191 A B lt2 f H g x z) = (term176 A B lt2 z f H g x).
Proof. exact (eq_refl (term191 A B lt2 f H g x z)). Qed.
Lemma lem347591 {A B : Type'} (lt2 : type1402 A) (z : A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term190 A B lt2 f H g x z) = (term176 A B lt2 z f H g x).
Proof. exact (TRANS (@lem347589 A B lt2 f H g x z) (@lem347590 A B lt2 z f H g x)). Qed.
Lemma lem347592 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term192 A B lt2 f H g x) = (term178 A B lt2 f H g x).
Proof. exact (fun_ext (fun z : A => @lem347591 A B lt2 z f H g x)). Qed.
Lemma lem347593 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem347594 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term193 A B lt2 f H g x) = (term179 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem347593 A) (@lem347592 A B lt2 f H g x)). Qed.
Lemma lem347595 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term194 A B lt2 f H g) = (term180 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem347594 A B lt2 f H g x)). Qed.
Lemma lem347596 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem347597 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term186 A B lt2 f H g) = (term181 A B lt2 f H g).
Proof. exact (MK_COMB (@lem347596 A) (@lem347595 A B lt2 f H g)). Qed.
Lemma lem347598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347599 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term195 A B lt2 f H g) = (term196 A B lt2 f H g).
Proof. exact (MK_COMB (@lem347598) (@lem347597 A B lt2 f H g)). Qed.
Lemma lem347600 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term189 A B lt2 f H g x) = (term178 A B lt2 f H g x).
Proof. exact (eq_refl (term189 A B lt2 f H g x)). Qed.
Lemma lem347601 {A : Type'} (z : A -> A) (x : A) : (z x) = (z x).
Proof. exact (eq_refl (z x)). Qed.
Lemma lem347602 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (z : A -> A) (x : A) : (term197 A B lt2 f H g z x) = (term198 A B lt2 f H g z x).
Proof. exact (MK_COMB (@lem347600 A B lt2 f H g x) (@lem347601 A z x)). Qed.
Lemma lem347603 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term198 A B lt2 f H g z x) = (term199 A B lt2 z f H g x).
Proof. exact (eq_refl (term198 A B lt2 f H g z x)). Qed.
Lemma lem347604 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term197 A B lt2 f H g z x) = (term199 A B lt2 z f H g x).
Proof. exact (TRANS (@lem347602 A B lt2 f H g z x) (@lem347603 A B lt2 z f H g x)). Qed.
Lemma lem347605 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term200 A B lt2 f H g z) = (term201 A B lt2 z f H g).
Proof. exact (fun_ext (fun x : A => @lem347604 A B lt2 z f H g x)). Qed.
Lemma lem347606 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem347607 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term202 A B lt2 f H g z) = (term203 A B lt2 z f H g).
Proof. exact (MK_COMB (@lem347606 A) (@lem347605 A B lt2 z f H g)). Qed.
Lemma lem347608 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term204 A B lt2 f H g) = (term205 A B lt2 f H g).
Proof. exact (fun_ext (fun z : A -> A => @lem347607 A B lt2 z f H g)). Qed.
Lemma lem347609 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem347610 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term187 A B lt2 f H g) = (term206 A B lt2 f H g).
Proof. exact (MK_COMB (@lem347609 A) (@lem347608 A B lt2 f H g)). Qed.
Lemma lem347611 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : ((term186 A B lt2 f H g) = (term187 A B lt2 f H g)) = ((term181 A B lt2 f H g) = (term206 A B lt2 f H g)).
Proof. exact (MK_COMB (@lem347599 A B lt2 f H g) (@lem347610 A B lt2 f H g)). Qed.
Lemma lem347612 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term181 A B lt2 f H g) = (term206 A B lt2 f H g).
Proof. exact (EQ_MP (@lem347611 A B lt2 f H g) (@lem347586 A B lt2 f H g)). Qed.
Lemma lem347613 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term83 A B lt2 f H g) = (term206 A B lt2 f H g).
Proof. exact (TRANS (@lem347582 A B lt2 f H g) (@lem347612 A B lt2 f H g)). Qed.
Lemma lem347614 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term84 A B lt2 f H) = (term207 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem347613 A B lt2 f H g)). Qed.
Lemma lem347615 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347616 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term85 A B lt2 f H) = (term208 A B lt2 f H).
Proof. exact (MK_COMB (@lem347615 A B) (@lem347614 A B lt2 f H)). Qed.
Lemma lem347618 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem347619 {A B : Type'} (P : type513 A B) : (term209 A B P) = (term210 A B P).
Proof. exact (@lem347618 (A -> B) (A -> A) P). Qed.
Lemma lem347620 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term211 A B lt2 f H) = (term212 A B lt2 f H).
Proof. exact (@lem347619 A B (term213 A B lt2 f H)). Qed.
Lemma lem347621 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term214 A B lt2 f H g) = (term205 A B lt2 f H g).
Proof. exact (eq_refl (term214 A B lt2 f H g)). Qed.
Lemma lem347622 {A : Type'} (z : A -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem347623 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (z : A -> A) : (term215 A B lt2 f H g z) = (term216 A B lt2 f H g z).
Proof. exact (MK_COMB (@lem347621 A B lt2 f H g) (@lem347622 A z)). Qed.
Lemma lem347624 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term216 A B lt2 f H g z) = (term203 A B lt2 z f H g).
Proof. exact (eq_refl (term216 A B lt2 f H g z)). Qed.
Lemma lem347625 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term215 A B lt2 f H g z) = (term203 A B lt2 z f H g).
Proof. exact (TRANS (@lem347623 A B lt2 f H g z) (@lem347624 A B lt2 z f H g)). Qed.
Lemma lem347626 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term217 A B lt2 f H g) = (term205 A B lt2 f H g).
Proof. exact (fun_ext (fun z : A -> A => @lem347625 A B lt2 z f H g)). Qed.
Lemma lem347627 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem347628 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term218 A B lt2 f H g) = (term206 A B lt2 f H g).
Proof. exact (MK_COMB (@lem347627 A) (@lem347626 A B lt2 f H g)). Qed.
Lemma lem347629 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term219 A B lt2 f H) = (term207 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem347628 A B lt2 f H g)). Qed.
Lemma lem347630 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347631 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term211 A B lt2 f H) = (term208 A B lt2 f H).
Proof. exact (MK_COMB (@lem347630 A B) (@lem347629 A B lt2 f H)). Qed.
Lemma lem347632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347633 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term220 A B lt2 f H) = (term221 A B lt2 f H).
Proof. exact (MK_COMB (@lem347632) (@lem347631 A B lt2 f H)). Qed.
Lemma lem347634 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term214 A B lt2 f H g) = (term205 A B lt2 f H g).
Proof. exact (eq_refl (term214 A B lt2 f H g)). Qed.
Lemma lem347635 {A B : Type'} (z : type548 A B) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem347636 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (z : type548 A B) (g : A -> B) : (term222 A B lt2 f H z g) = (term223 A B lt2 f H z g).
Proof. exact (MK_COMB (@lem347634 A B lt2 f H g) (@lem347635 A B z g)). Qed.
Lemma lem347637 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (H : type549 A B) (g : A -> B) : (term223 A B lt2 f H z g) = (term224 A B lt2 z f H g).
Proof. exact (eq_refl (term223 A B lt2 f H z g)). Qed.
Lemma lem347638 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (H : type549 A B) (g : A -> B) : (term222 A B lt2 f H z g) = (term224 A B lt2 z f H g).
Proof. exact (TRANS (@lem347636 A B lt2 f H z g) (@lem347637 A B lt2 z f H g)). Qed.
Lemma lem347639 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (H : type549 A B) : (term225 A B lt2 f H z) = (term226 A B lt2 z f H).
Proof. exact (fun_ext (fun g : A -> B => @lem347638 A B lt2 z f H g)). Qed.
Lemma lem347640 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347641 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (H : type549 A B) : (term227 A B lt2 f H z) = (term228 A B lt2 z f H).
Proof. exact (MK_COMB (@lem347640 A B) (@lem347639 A B lt2 z f H)). Qed.
Lemma lem347642 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term229 A B lt2 f H) = (term230 A B lt2 f H).
Proof. exact (fun_ext (fun z : type548 A B => @lem347641 A B lt2 z f H)). Qed.
Lemma lem347643 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem347644 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term212 A B lt2 f H) = (term231 A B lt2 f H).
Proof. exact (MK_COMB (@lem347643 A B) (@lem347642 A B lt2 f H)). Qed.
Lemma lem347645 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : ((term211 A B lt2 f H) = (term212 A B lt2 f H)) = ((term208 A B lt2 f H) = (term231 A B lt2 f H)).
Proof. exact (MK_COMB (@lem347633 A B lt2 f H) (@lem347644 A B lt2 f H)). Qed.
Lemma lem347646 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term208 A B lt2 f H) = (term231 A B lt2 f H).
Proof. exact (EQ_MP (@lem347645 A B lt2 f H) (@lem347620 A B lt2 f H)). Qed.
Lemma lem347647 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term85 A B lt2 f H) = (term231 A B lt2 f H).
Proof. exact (TRANS (@lem347616 A B lt2 f H) (@lem347646 A B lt2 f H)). Qed.
Lemma lem347648 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term86 A B lt2 H) = (term232 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem347647 A B lt2 f H)). Qed.
Lemma lem347649 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347650 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term87 A B lt2 H) = (term233 A B lt2 H).
Proof. exact (MK_COMB (@lem347649 A B) (@lem347648 A B lt2 H)). Qed.
Lemma lem347652 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem347653 {A B : Type'} (P : type493 A B) : (term234 A B P) = (term235 A B P).
Proof. exact (@lem347652 (A -> B) (type548 A B) P). Qed.
Lemma lem347654 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term236 A B lt2 H) = (term237 A B lt2 H).
Proof. exact (@lem347653 A B (term238 A B lt2 H)). Qed.
Lemma lem347655 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term239 A B lt2 H f) = (term230 A B lt2 f H).
Proof. exact (eq_refl (term239 A B lt2 H f)). Qed.
Lemma lem347656 {A B : Type'} (z : type548 A B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem347657 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (z : type548 A B) : (term240 A B lt2 H f z) = (term241 A B lt2 f H z).
Proof. exact (MK_COMB (@lem347655 A B lt2 f H) (@lem347656 A B z)). Qed.
Lemma lem347658 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (H : type549 A B) : (term241 A B lt2 f H z) = (term228 A B lt2 z f H).
Proof. exact (eq_refl (term241 A B lt2 f H z)). Qed.
Lemma lem347659 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (H : type549 A B) : (term240 A B lt2 H f z) = (term228 A B lt2 z f H).
Proof. exact (TRANS (@lem347657 A B lt2 f H z) (@lem347658 A B lt2 z f H)). Qed.
Lemma lem347660 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term242 A B lt2 H f) = (term230 A B lt2 f H).
Proof. exact (fun_ext (fun z : type548 A B => @lem347659 A B lt2 z f H)). Qed.
Lemma lem347661 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem347662 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term243 A B lt2 H f) = (term231 A B lt2 f H).
Proof. exact (MK_COMB (@lem347661 A B) (@lem347660 A B lt2 f H)). Qed.
Lemma lem347663 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term244 A B lt2 H) = (term232 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem347662 A B lt2 f H)). Qed.
Lemma lem347664 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347665 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term236 A B lt2 H) = (term233 A B lt2 H).
Proof. exact (MK_COMB (@lem347664 A B) (@lem347663 A B lt2 H)). Qed.
Lemma lem347666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347667 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term245 A B lt2 H) = (term246 A B lt2 H).
Proof. exact (MK_COMB (@lem347666) (@lem347665 A B lt2 H)). Qed.
Lemma lem347668 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term239 A B lt2 H f) = (term230 A B lt2 f H).
Proof. exact (eq_refl (term239 A B lt2 H f)). Qed.
Lemma lem347669 {A B : Type'} (z : type515 A B) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem347670 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (z : type515 A B) (f : A -> B) : (term247 A B lt2 H z f) = (term248 A B lt2 H z f).
Proof. exact (MK_COMB (@lem347668 A B lt2 f H) (@lem347669 A B z f)). Qed.
Lemma lem347671 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) : (term248 A B lt2 H z f) = (term249 A B lt2 z f H).
Proof. exact (eq_refl (term248 A B lt2 H z f)). Qed.
Lemma lem347672 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) : (term247 A B lt2 H z f) = (term249 A B lt2 z f H).
Proof. exact (TRANS (@lem347670 A B lt2 H z f) (@lem347671 A B lt2 z f H)). Qed.
Lemma lem347673 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term250 A B lt2 H z) = (term251 A B lt2 z H).
Proof. exact (fun_ext (fun f : A -> B => @lem347672 A B lt2 z f H)). Qed.
Lemma lem347674 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347675 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term252 A B lt2 H z) = (term253 A B lt2 z H).
Proof. exact (MK_COMB (@lem347674 A B) (@lem347673 A B lt2 z H)). Qed.
Lemma lem347676 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term254 A B lt2 H) = (term255 A B lt2 H).
Proof. exact (fun_ext (fun z : type515 A B => @lem347675 A B lt2 z H)). Qed.
Lemma lem347677 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A -> A)) = (@ex ((A -> B) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A -> A))). Qed.
Lemma lem347678 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term237 A B lt2 H) = (term256 A B lt2 H).
Proof. exact (MK_COMB (@lem347677 A B) (@lem347676 A B lt2 H)). Qed.
Lemma lem347679 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : ((term236 A B lt2 H) = (term237 A B lt2 H)) = ((term233 A B lt2 H) = (term256 A B lt2 H)).
Proof. exact (MK_COMB (@lem347667 A B lt2 H) (@lem347678 A B lt2 H)). Qed.
Lemma lem347680 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term233 A B lt2 H) = (term256 A B lt2 H).
Proof. exact (EQ_MP (@lem347679 A B lt2 H) (@lem347654 A B lt2 H)). Qed.
Lemma lem347681 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term87 A B lt2 H) = (term256 A B lt2 H).
Proof. exact (TRANS (@lem347650 A B lt2 H) (@lem347680 A B lt2 H)). Qed.
Lemma lem347682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem347683 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term124 A B lt2 H) = (term257 A B lt2 H).
Proof. exact (MK_COMB (@lem347682) (@lem347681 A B lt2 H)). Qed.
Lemma lem347685 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem347686 {A B : Type'} (P : type551 A B) : (term258 A B P) = (term259 A B P).
Proof. exact (@lem347685 (A -> B) A P). Qed.
Lemma lem347687 {A B : Type'} (H : type549 A B) : (term260 A B H) = (term261 A B H).
Proof. exact (@lem347686 A B (term262 A B H)). Qed.
Lemma lem347688 {A B : Type'} (H : type549 A B) (f : A -> B) : (term263 A B H f) = (term94 A B H f).
Proof. exact (eq_refl (term263 A B H f)). Qed.
Lemma lem347689 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem347690 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term264 A B H f x) = (term265 A B H f x).
Proof. exact (MK_COMB (@lem347688 A B H f) (@lem347689 A x)). Qed.
Lemma lem347691 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term265 A B H f x) = (term92 A B H f x).
Proof. exact (eq_refl (term265 A B H f x)). Qed.
Lemma lem347692 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term264 A B H f x) = (term92 A B H f x).
Proof. exact (TRANS (@lem347690 A B H f x) (@lem347691 A B H f x)). Qed.
Lemma lem347693 {A B : Type'} (H : type549 A B) (f : A -> B) : (term266 A B H f) = (term94 A B H f).
Proof. exact (fun_ext (fun x : A => @lem347692 A B H f x)). Qed.
Lemma lem347694 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem347695 {A B : Type'} (H : type549 A B) (f : A -> B) : (term267 A B H f) = (term95 A B H f).
Proof. exact (MK_COMB (@lem347694 A) (@lem347693 A B H f)). Qed.
Lemma lem347696 {A B : Type'} (H : type549 A B) : (term268 A B H) = (term117 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem347695 A B H f)). Qed.
Lemma lem347697 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347698 {A B : Type'} (H : type549 A B) : (term260 A B H) = (term119 A B H).
Proof. exact (MK_COMB (@lem347697 A B) (@lem347696 A B H)). Qed.
Lemma lem347699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347700 {A B : Type'} (H : type549 A B) : (term269 A B H) = (term270 A B H).
Proof. exact (MK_COMB (@lem347699) (@lem347698 A B H)). Qed.
Lemma lem347701 {A B : Type'} (H : type549 A B) (f : A -> B) : (term263 A B H f) = (term94 A B H f).
Proof. exact (eq_refl (term263 A B H f)). Qed.
Lemma lem347702 {A B : Type'} (x : type569 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem347703 {A B : Type'} (H : type549 A B) (x : type569 A B) (f : A -> B) : (term271 A B H x f) = (term272 A B H x f).
Proof. exact (MK_COMB (@lem347701 A B H f) (@lem347702 A B x f)). Qed.
Lemma lem347704 {A B : Type'} (H : type549 A B) (x : type569 A B) (f : A -> B) : (term272 A B H x f) = (term273 A B H x f).
Proof. exact (eq_refl (term272 A B H x f)). Qed.
Lemma lem347705 {A B : Type'} (H : type549 A B) (x : type569 A B) (f : A -> B) : (term271 A B H x f) = (term273 A B H x f).
Proof. exact (TRANS (@lem347703 A B H x f) (@lem347704 A B H x f)). Qed.
Lemma lem347706 {A B : Type'} (H : type549 A B) (x : type569 A B) : (term274 A B H x) = (term275 A B H x).
Proof. exact (fun_ext (fun f : A -> B => @lem347705 A B H x f)). Qed.
Lemma lem347707 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem347708 {A B : Type'} (H : type549 A B) (x : type569 A B) : (term276 A B H x) = (term277 A B H x).
Proof. exact (MK_COMB (@lem347707 A B) (@lem347706 A B H x)). Qed.
Lemma lem347709 {A B : Type'} (H : type549 A B) : (term278 A B H) = (term279 A B H).
Proof. exact (fun_ext (fun x : type569 A B => @lem347708 A B H x)). Qed.
Lemma lem347710 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem347711 {A B : Type'} (H : type549 A B) : (term261 A B H) = (term280 A B H).
Proof. exact (MK_COMB (@lem347710 A B) (@lem347709 A B H)). Qed.
Lemma lem347712 {A B : Type'} (H : type549 A B) : ((term260 A B H) = (term261 A B H)) = ((term119 A B H) = (term280 A B H)).
Proof. exact (MK_COMB (@lem347700 A B H) (@lem347711 A B H)). Qed.
Lemma lem347713 {A B : Type'} (H : type549 A B) : (term119 A B H) = (term280 A B H).
Proof. exact (EQ_MP (@lem347712 A B H) (@lem347687 A B H)). Qed.
Lemma lem347714 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem347715 {A B : Type'} (H : type549 A B) : (term121 A B H) = (term281 A B H).
Proof. exact (MK_COMB (@lem347714) (@lem347713 A B H)). Qed.
Lemma lem347717 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem347718 {A B : Type'} (P : Prop) (Q : type572 A B) : (term143 A B P Q) = (term142 A B P Q).
Proof. exact (@lem347717 (A -> B) P Q). Qed.
Lemma lem347719 {A B : Type'} (H : type549 A B) (f : A -> B) : (term145 A B H f) = (term144 A B H f).
Proof. exact (@lem347718 A B (term29 A B H f) (term146 A B H f)). Qed.
Lemma lem347720 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term147 A B H f f') = (term104 A B H f' f).
Proof. exact (eq_refl (term147 A B H f f')). Qed.
Lemma lem347721 {A B : Type'} (H : type549 A B) (f : A -> B) : (term152 A B H f) = (term146 A B H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem347720 A B H f' f)). Qed.
Lemma lem347722 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347723 {A B : Type'} (H : type549 A B) (f : A -> B) : (term153 A B H f) = (term154 A B H f).
Proof. exact (MK_COMB (@lem347722 A B) (@lem347721 A B H f)). Qed.
Lemma lem347724 {A B : Type'} (H : type549 A B) (f : A -> B) : (term50 A B H f) = (term50 A B H f).
Proof. exact (eq_refl (term50 A B H f)). Qed.
Lemma lem347725 {A B : Type'} (H : type549 A B) (f : A -> B) : (term145 A B H f) = (term155 A B H f).
Proof. exact (MK_COMB (@lem347724 A B H f) (@lem347723 A B H f)). Qed.
Lemma lem347726 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347727 {A B : Type'} (H : type549 A B) (f : A -> B) : (term282 A B H f) = (term283 A B H f).
Proof. exact (MK_COMB (@lem347726) (@lem347725 A B H f)). Qed.
Lemma lem347728 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term147 A B H f f') = (term104 A B H f' f).
Proof. exact (eq_refl (term147 A B H f f')). Qed.
Lemma lem347729 {A B : Type'} (H : type549 A B) (f : A -> B) : (term50 A B H f) = (term50 A B H f).
Proof. exact (eq_refl (term50 A B H f)). Qed.
Lemma lem347730 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term148 A B H f f') = (term106 A B H f' f).
Proof. exact (MK_COMB (@lem347729 A B H f) (@lem347728 A B H f' f)). Qed.
Lemma lem347731 {A B : Type'} (H : type549 A B) (f : A -> B) : (term149 A B H f) = (term108 A B H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem347730 A B H f' f)). Qed.
Lemma lem347732 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347733 {A B : Type'} (H : type549 A B) (f : A -> B) : (term144 A B H f) = (term110 A B H f).
Proof. exact (MK_COMB (@lem347732 A B) (@lem347731 A B H f)). Qed.
Lemma lem347734 {A B : Type'} (H : type549 A B) (f : A -> B) : ((term145 A B H f) = (term144 A B H f)) = ((term155 A B H f) = (term110 A B H f)).
Proof. exact (MK_COMB (@lem347727 A B H f) (@lem347733 A B H f)). Qed.
Lemma lem347735 {A B : Type'} (H : type549 A B) (f : A -> B) : (term155 A B H f) = (term110 A B H f).
Proof. exact (EQ_MP (@lem347734 A B H f) (@lem347719 A B H f)). Qed.
Lemma lem347736 {A B : Type'} (H : type549 A B) : (term156 A B H) = (term112 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem347735 A B H f)). Qed.
Lemma lem347737 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347738 {A B : Type'} (H : type549 A B) : (term157 A B H) = (term114 A B H).
Proof. exact (MK_COMB (@lem347737 A B) (@lem347736 A B H)). Qed.
Lemma lem347739 {A B : Type'} (H : type549 A B) : (term158 A B H) = (term284 A B H).
Proof. exact (MK_COMB (@lem347715 A B H) (@lem347738 A B H)). Qed.
Lemma lem347743 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem347744 {A B : Type'} (P : type118 A B) (Q : Prop) : (term285 A B P Q) = (term286 A B P Q).
Proof. exact (@lem347743 (type569 A B) P Q). Qed.
Lemma lem347745 {A B : Type'} (H : type549 A B) : (term287 A B H) = (term288 A B H).
Proof. exact (@lem347744 A B (term279 A B H) (term114 A B H)). Qed.
Lemma lem347746 {A B : Type'} (H : type549 A B) (x : type569 A B) : (term289 A B H x) = (term277 A B H x).
Proof. exact (eq_refl (term289 A B H x)). Qed.
Lemma lem347747 {A B : Type'} (H : type549 A B) : (term290 A B H) = (term279 A B H).
Proof. exact (fun_ext (fun x : type569 A B => @lem347746 A B H x)). Qed.
Lemma lem347748 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem347749 {A B : Type'} (H : type549 A B) : (term291 A B H) = (term280 A B H).
Proof. exact (MK_COMB (@lem347748 A B) (@lem347747 A B H)). Qed.
Lemma lem347750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem347751 {A B : Type'} (H : type549 A B) : (term292 A B H) = (term281 A B H).
Proof. exact (MK_COMB (@lem347750) (@lem347749 A B H)). Qed.
Lemma lem347752 {A B : Type'} (H : type549 A B) : (term114 A B H) = (term114 A B H).
Proof. exact (eq_refl (term114 A B H)). Qed.
Lemma lem347753 {A B : Type'} (H : type549 A B) : (term287 A B H) = (term284 A B H).
Proof. exact (MK_COMB (@lem347751 A B H) (@lem347752 A B H)). Qed.
Lemma lem347754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347755 {A B : Type'} (H : type549 A B) : (term293 A B H) = (term294 A B H).
Proof. exact (MK_COMB (@lem347754) (@lem347753 A B H)). Qed.
Lemma lem347756 {A B : Type'} (H : type549 A B) (x : type569 A B) : (term289 A B H x) = (term277 A B H x).
Proof. exact (eq_refl (term289 A B H x)). Qed.
Lemma lem347757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem347758 {A B : Type'} (H : type549 A B) (x : type569 A B) : (term295 A B H x) = (term296 A B H x).
Proof. exact (MK_COMB (@lem347757) (@lem347756 A B H x)). Qed.
Lemma lem347759 {A B : Type'} (H : type549 A B) : (term114 A B H) = (term114 A B H).
Proof. exact (eq_refl (term114 A B H)). Qed.
Lemma lem347760 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term297 A B x H) = (term298 A B x H).
Proof. exact (MK_COMB (@lem347758 A B H x) (@lem347759 A B H)). Qed.
Lemma lem347761 {A B : Type'} (H : type549 A B) : (term299 A B H) = (term300 A B H).
Proof. exact (fun_ext (fun x : type569 A B => @lem347760 A B x H)). Qed.
Lemma lem347762 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem347763 {A B : Type'} (H : type549 A B) : (term288 A B H) = (term301 A B H).
Proof. exact (MK_COMB (@lem347762 A B) (@lem347761 A B H)). Qed.
Lemma lem347764 {A B : Type'} (H : type549 A B) : ((term287 A B H) = (term288 A B H)) = ((term284 A B H) = (term301 A B H)).
Proof. exact (MK_COMB (@lem347755 A B H) (@lem347763 A B H)). Qed.
Lemma lem347765 {A B : Type'} (H : type549 A B) : (term284 A B H) = (term301 A B H).
Proof. exact (EQ_MP (@lem347764 A B H) (@lem347745 A B H)). Qed.
Lemma lem347767 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem347768 {A B : Type'} (P : Prop) (Q : type572 A B) : (term304 A B P Q) = (term305 A B P Q).
Proof. exact (@lem347767 (A -> B) P Q). Qed.
Lemma lem347769 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term306 A B x H) = (term307 A B x H).
Proof. exact (@lem347768 A B (term277 A B H x) (term112 A B H)). Qed.
Lemma lem347770 {A B : Type'} (H : type549 A B) (f : A -> B) : (term308 A B H f) = (term110 A B H f).
Proof. exact (eq_refl (term308 A B H f)). Qed.
Lemma lem347771 {A B : Type'} (H : type549 A B) : (term309 A B H) = (term112 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem347770 A B H f)). Qed.
Lemma lem347772 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347773 {A B : Type'} (H : type549 A B) : (term310 A B H) = (term114 A B H).
Proof. exact (MK_COMB (@lem347772 A B) (@lem347771 A B H)). Qed.
Lemma lem347774 {A B : Type'} (H : type549 A B) (x : type569 A B) : (term296 A B H x) = (term296 A B H x).
Proof. exact (eq_refl (term296 A B H x)). Qed.
Lemma lem347775 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term306 A B x H) = (term298 A B x H).
Proof. exact (MK_COMB (@lem347774 A B H x) (@lem347773 A B H)). Qed.
Lemma lem347776 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347777 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term311 A B x H) = (term312 A B x H).
Proof. exact (MK_COMB (@lem347776) (@lem347775 A B x H)). Qed.
Lemma lem347778 {A B : Type'} (H : type549 A B) (f : A -> B) : (term308 A B H f) = (term110 A B H f).
Proof. exact (eq_refl (term308 A B H f)). Qed.
Lemma lem347779 {A B : Type'} (H : type549 A B) (x : type569 A B) : (term296 A B H x) = (term296 A B H x).
Proof. exact (eq_refl (term296 A B H x)). Qed.
Lemma lem347780 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term313 A B x H f) = (term314 A B x H f).
Proof. exact (MK_COMB (@lem347779 A B H x) (@lem347778 A B H f)). Qed.
Lemma lem347781 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term315 A B x H) = (term316 A B x H).
Proof. exact (fun_ext (fun f : A -> B => @lem347780 A B x H f)). Qed.
Lemma lem347782 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347783 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term307 A B x H) = (term317 A B x H).
Proof. exact (MK_COMB (@lem347782 A B) (@lem347781 A B x H)). Qed.
Lemma lem347784 {A B : Type'} (x : type569 A B) (H : type549 A B) : ((term306 A B x H) = (term307 A B x H)) = ((term298 A B x H) = (term317 A B x H)).
Proof. exact (MK_COMB (@lem347777 A B x H) (@lem347783 A B x H)). Qed.
Lemma lem347785 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term298 A B x H) = (term317 A B x H).
Proof. exact (EQ_MP (@lem347784 A B x H) (@lem347769 A B x H)). Qed.
Lemma lem347787 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem347788 {A B : Type'} (P : Prop) (Q : type572 A B) : (term304 A B P Q) = (term305 A B P Q).
Proof. exact (@lem347787 (A -> B) P Q). Qed.
Lemma lem347789 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term318 A B x H f) = (term319 A B x H f).
Proof. exact (@lem347788 A B (term277 A B H x) (term108 A B H f)). Qed.
Lemma lem347790 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term320 A B H f f') = (term106 A B H f' f).
Proof. exact (eq_refl (term320 A B H f f')). Qed.
Lemma lem347791 {A B : Type'} (H : type549 A B) (f : A -> B) : (term321 A B H f) = (term108 A B H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem347790 A B H f' f)). Qed.
Lemma lem347792 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347793 {A B : Type'} (H : type549 A B) (f : A -> B) : (term322 A B H f) = (term110 A B H f).
Proof. exact (MK_COMB (@lem347792 A B) (@lem347791 A B H f)). Qed.
Lemma lem347794 {A B : Type'} (H : type549 A B) (x : type569 A B) : (term296 A B H x) = (term296 A B H x).
Proof. exact (eq_refl (term296 A B H x)). Qed.
Lemma lem347795 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term318 A B x H f) = (term314 A B x H f).
Proof. exact (MK_COMB (@lem347794 A B H x) (@lem347793 A B H f)). Qed.
Lemma lem347796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347797 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term323 A B x H f) = (term324 A B x H f).
Proof. exact (MK_COMB (@lem347796) (@lem347795 A B x H f)). Qed.
Lemma lem347798 {A B : Type'} (H : type549 A B) (f' : A -> B) (f : A -> B) : (term320 A B H f f') = (term106 A B H f' f).
Proof. exact (eq_refl (term320 A B H f f')). Qed.
Lemma lem347799 {A B : Type'} (H : type549 A B) (x : type569 A B) : (term296 A B H x) = (term296 A B H x).
Proof. exact (eq_refl (term296 A B H x)). Qed.
Lemma lem347800 {A B : Type'} (x : type569 A B) (H : type549 A B) (f' : A -> B) (f : A -> B) : (term325 A B x H f f') = (term326 A B x H f' f).
Proof. exact (MK_COMB (@lem347799 A B H x) (@lem347798 A B H f' f)). Qed.
Lemma lem347801 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term327 A B x H f) = (term328 A B x H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem347800 A B x H f' f)). Qed.
Lemma lem347802 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347803 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term319 A B x H f) = (term329 A B x H f).
Proof. exact (MK_COMB (@lem347802 A B) (@lem347801 A B x H f)). Qed.
Lemma lem347804 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : ((term318 A B x H f) = (term319 A B x H f)) = ((term314 A B x H f) = (term329 A B x H f)).
Proof. exact (MK_COMB (@lem347797 A B x H f) (@lem347803 A B x H f)). Qed.
Lemma lem347805 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term314 A B x H f) = (term329 A B x H f).
Proof. exact (EQ_MP (@lem347804 A B x H f) (@lem347789 A B x H f)). Qed.
Lemma lem347806 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term316 A B x H) = (term330 A B x H).
Proof. exact (fun_ext (fun f : A -> B => @lem347805 A B x H f)). Qed.
Lemma lem347807 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347808 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term317 A B x H) = (term331 A B x H).
Proof. exact (MK_COMB (@lem347807 A B) (@lem347806 A B x H)). Qed.
Lemma lem347809 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term298 A B x H) = (term331 A B x H).
Proof. exact (TRANS (@lem347785 A B x H) (@lem347808 A B x H)). Qed.
Lemma lem347810 {A B : Type'} (H : type549 A B) : (term300 A B H) = (term332 A B H).
Proof. exact (fun_ext (fun x : type569 A B => @lem347809 A B x H)). Qed.
Lemma lem347811 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem347812 {A B : Type'} (H : type549 A B) : (term301 A B H) = (term333 A B H).
Proof. exact (MK_COMB (@lem347811 A B) (@lem347810 A B H)). Qed.
Lemma lem347813 {A B : Type'} (H : type549 A B) : (term284 A B H) = (term333 A B H).
Proof. exact (TRANS (@lem347765 A B H) (@lem347812 A B H)). Qed.
Lemma lem347814 {A B : Type'} (H : type549 A B) : (term158 A B H) = (term333 A B H).
Proof. exact (TRANS (@lem347739 A B H) (@lem347813 A B H)). Qed.
Lemma lem347815 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term159 A B lt2 H) = (term334 A B lt2 H).
Proof. exact (MK_COMB (@lem347683 A B lt2 H) (@lem347814 A B H)). Qed.
Lemma lem347817 {A : Type'} (P : A -> Prop) (Q : Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem347818 {A B : Type'} (P : type94 A B) (Q : Prop) : (term337 A B P Q) = (term338 A B P Q).
Proof. exact (@lem347817 (type515 A B) P Q). Qed.
Lemma lem347819 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term339 A B lt2 H) = (term340 A B lt2 H).
Proof. exact (@lem347818 A B (term255 A B lt2 H) (term333 A B H)). Qed.
Lemma lem347820 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term341 A B lt2 H z) = (term253 A B lt2 z H).
Proof. exact (eq_refl (term341 A B lt2 H z)). Qed.
Lemma lem347821 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term342 A B lt2 H) = (term255 A B lt2 H).
Proof. exact (fun_ext (fun z : type515 A B => @lem347820 A B lt2 z H)). Qed.
Lemma lem347822 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A -> A)) = (@ex ((A -> B) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A -> A))). Qed.
Lemma lem347823 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term343 A B lt2 H) = (term256 A B lt2 H).
Proof. exact (MK_COMB (@lem347822 A B) (@lem347821 A B lt2 H)). Qed.
Lemma lem347824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem347825 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term344 A B lt2 H) = (term257 A B lt2 H).
Proof. exact (MK_COMB (@lem347824) (@lem347823 A B lt2 H)). Qed.
Lemma lem347826 {A B : Type'} (H : type549 A B) : (term333 A B H) = (term333 A B H).
Proof. exact (eq_refl (term333 A B H)). Qed.
Lemma lem347827 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term339 A B lt2 H) = (term334 A B lt2 H).
Proof. exact (MK_COMB (@lem347825 A B lt2 H) (@lem347826 A B H)). Qed.
Lemma lem347828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347829 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term345 A B lt2 H) = (term346 A B lt2 H).
Proof. exact (MK_COMB (@lem347828) (@lem347827 A B lt2 H)). Qed.
Lemma lem347830 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term341 A B lt2 H z) = (term253 A B lt2 z H).
Proof. exact (eq_refl (term341 A B lt2 H z)). Qed.
Lemma lem347831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem347832 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term347 A B lt2 H z) = (term348 A B lt2 z H).
Proof. exact (MK_COMB (@lem347831) (@lem347830 A B lt2 z H)). Qed.
Lemma lem347833 {A B : Type'} (H : type549 A B) : (term333 A B H) = (term333 A B H).
Proof. exact (eq_refl (term333 A B H)). Qed.
Lemma lem347834 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term349 A B lt2 z H) = (term350 A B lt2 z H).
Proof. exact (MK_COMB (@lem347832 A B lt2 z H) (@lem347833 A B H)). Qed.
Lemma lem347835 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term351 A B lt2 H) = (term352 A B lt2 H).
Proof. exact (fun_ext (fun z : type515 A B => @lem347834 A B lt2 z H)). Qed.
Lemma lem347836 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A -> A)) = (@ex ((A -> B) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A -> A))). Qed.
Lemma lem347837 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term340 A B lt2 H) = (term353 A B lt2 H).
Proof. exact (MK_COMB (@lem347836 A B) (@lem347835 A B lt2 H)). Qed.
Lemma lem347838 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : ((term339 A B lt2 H) = (term340 A B lt2 H)) = ((term334 A B lt2 H) = (term353 A B lt2 H)).
Proof. exact (MK_COMB (@lem347829 A B lt2 H) (@lem347837 A B lt2 H)). Qed.
Lemma lem347839 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term334 A B lt2 H) = (term353 A B lt2 H).
Proof. exact (EQ_MP (@lem347838 A B lt2 H) (@lem347819 A B lt2 H)). Qed.
Lemma lem347841 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem347842 {A B : Type'} (P : Prop) (Q : type118 A B) : (term354 A B P Q) = (term355 A B P Q).
Proof. exact (@lem347841 (type569 A B) P Q). Qed.
Lemma lem347843 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term356 A B lt2 z H) = (term357 A B lt2 z H).
Proof. exact (@lem347842 A B (term253 A B lt2 z H) (term332 A B H)). Qed.
Lemma lem347844 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term358 A B H x) = (term331 A B x H).
Proof. exact (eq_refl (term358 A B H x)). Qed.
Lemma lem347845 {A B : Type'} (H : type549 A B) : (term359 A B H) = (term332 A B H).
Proof. exact (fun_ext (fun x : type569 A B => @lem347844 A B x H)). Qed.
Lemma lem347846 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem347847 {A B : Type'} (H : type549 A B) : (term360 A B H) = (term333 A B H).
Proof. exact (MK_COMB (@lem347846 A B) (@lem347845 A B H)). Qed.
Lemma lem347848 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term348 A B lt2 z H) = (term348 A B lt2 z H).
Proof. exact (eq_refl (term348 A B lt2 z H)). Qed.
Lemma lem347849 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term356 A B lt2 z H) = (term350 A B lt2 z H).
Proof. exact (MK_COMB (@lem347848 A B lt2 z H) (@lem347847 A B H)). Qed.
Lemma lem347850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347851 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term361 A B lt2 z H) = (term362 A B lt2 z H).
Proof. exact (MK_COMB (@lem347850) (@lem347849 A B lt2 z H)). Qed.
Lemma lem347852 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term358 A B H x) = (term331 A B x H).
Proof. exact (eq_refl (term358 A B H x)). Qed.
Lemma lem347853 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term348 A B lt2 z H) = (term348 A B lt2 z H).
Proof. exact (eq_refl (term348 A B lt2 z H)). Qed.
Lemma lem347854 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term363 A B lt2 z H x) = (term364 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347853 A B lt2 z H) (@lem347852 A B x H)). Qed.
Lemma lem347855 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term365 A B lt2 z H) = (term366 A B lt2 z H).
Proof. exact (fun_ext (fun x : type569 A B => @lem347854 A B lt2 z x H)). Qed.
Lemma lem347856 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem347857 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term357 A B lt2 z H) = (term367 A B lt2 z H).
Proof. exact (MK_COMB (@lem347856 A B) (@lem347855 A B lt2 z H)). Qed.
Lemma lem347858 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : ((term356 A B lt2 z H) = (term357 A B lt2 z H)) = ((term350 A B lt2 z H) = (term367 A B lt2 z H)).
Proof. exact (MK_COMB (@lem347851 A B lt2 z H) (@lem347857 A B lt2 z H)). Qed.
Lemma lem347859 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term350 A B lt2 z H) = (term367 A B lt2 z H).
Proof. exact (EQ_MP (@lem347858 A B lt2 z H) (@lem347843 A B lt2 z H)). Qed.
Lemma lem347861 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem347862 {A B : Type'} (P : Prop) (Q : type572 A B) : (term143 A B P Q) = (term142 A B P Q).
Proof. exact (@lem347861 (A -> B) P Q). Qed.
Lemma lem347863 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term368 A B lt2 z x H) = (term369 A B lt2 z x H).
Proof. exact (@lem347862 A B (term253 A B lt2 z H) (term330 A B x H)). Qed.
Lemma lem347864 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term370 A B x H f) = (term329 A B x H f).
Proof. exact (eq_refl (term370 A B x H f)). Qed.
Lemma lem347865 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term371 A B x H) = (term330 A B x H).
Proof. exact (fun_ext (fun f : A -> B => @lem347864 A B x H f)). Qed.
Lemma lem347866 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347867 {A B : Type'} (x : type569 A B) (H : type549 A B) : (term372 A B x H) = (term331 A B x H).
Proof. exact (MK_COMB (@lem347866 A B) (@lem347865 A B x H)). Qed.
Lemma lem347868 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term348 A B lt2 z H) = (term348 A B lt2 z H).
Proof. exact (eq_refl (term348 A B lt2 z H)). Qed.
Lemma lem347869 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term368 A B lt2 z x H) = (term364 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347868 A B lt2 z H) (@lem347867 A B x H)). Qed.
Lemma lem347870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347871 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term373 A B lt2 z x H) = (term374 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347870) (@lem347869 A B lt2 z x H)). Qed.
Lemma lem347872 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term370 A B x H f) = (term329 A B x H f).
Proof. exact (eq_refl (term370 A B x H f)). Qed.
Lemma lem347873 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term348 A B lt2 z H) = (term348 A B lt2 z H).
Proof. exact (eq_refl (term348 A B lt2 z H)). Qed.
Lemma lem347874 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term375 A B lt2 z x H f) = (term376 A B lt2 z x H f).
Proof. exact (MK_COMB (@lem347873 A B lt2 z H) (@lem347872 A B x H f)). Qed.
Lemma lem347875 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term377 A B lt2 z x H) = (term378 A B lt2 z x H).
Proof. exact (fun_ext (fun f : A -> B => @lem347874 A B lt2 z x H f)). Qed.
Lemma lem347876 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347877 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term369 A B lt2 z x H) = (term379 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347876 A B) (@lem347875 A B lt2 z x H)). Qed.
Lemma lem347878 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : ((term368 A B lt2 z x H) = (term369 A B lt2 z x H)) = ((term364 A B lt2 z x H) = (term379 A B lt2 z x H)).
Proof. exact (MK_COMB (@lem347871 A B lt2 z x H) (@lem347877 A B lt2 z x H)). Qed.
Lemma lem347879 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term364 A B lt2 z x H) = (term379 A B lt2 z x H).
Proof. exact (EQ_MP (@lem347878 A B lt2 z x H) (@lem347863 A B lt2 z x H)). Qed.
Lemma lem347881 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem347882 {A B : Type'} (P : Prop) (Q : type572 A B) : (term143 A B P Q) = (term142 A B P Q).
Proof. exact (@lem347881 (A -> B) P Q). Qed.
Lemma lem347883 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term380 A B lt2 z x H f) = (term381 A B lt2 z x H f).
Proof. exact (@lem347882 A B (term253 A B lt2 z H) (term328 A B x H f)). Qed.
Lemma lem347884 {A B : Type'} (x : type569 A B) (H : type549 A B) (f' : A -> B) (f : A -> B) : (term382 A B x H f f') = (term326 A B x H f' f).
Proof. exact (eq_refl (term382 A B x H f f')). Qed.
Lemma lem347885 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term383 A B x H f) = (term328 A B x H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem347884 A B x H f' f)). Qed.
Lemma lem347886 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347887 {A B : Type'} (x : type569 A B) (H : type549 A B) (f : A -> B) : (term384 A B x H f) = (term329 A B x H f).
Proof. exact (MK_COMB (@lem347886 A B) (@lem347885 A B x H f)). Qed.
Lemma lem347888 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term348 A B lt2 z H) = (term348 A B lt2 z H).
Proof. exact (eq_refl (term348 A B lt2 z H)). Qed.
Lemma lem347889 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term380 A B lt2 z x H f) = (term376 A B lt2 z x H f).
Proof. exact (MK_COMB (@lem347888 A B lt2 z H) (@lem347887 A B x H f)). Qed.
Lemma lem347890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347891 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term385 A B lt2 z x H f) = (term386 A B lt2 z x H f).
Proof. exact (MK_COMB (@lem347890) (@lem347889 A B lt2 z x H f)). Qed.
Lemma lem347892 {A B : Type'} (x : type569 A B) (H : type549 A B) (f' : A -> B) (f : A -> B) : (term382 A B x H f f') = (term326 A B x H f' f).
Proof. exact (eq_refl (term382 A B x H f f')). Qed.
Lemma lem347893 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term348 A B lt2 z H) = (term348 A B lt2 z H).
Proof. exact (eq_refl (term348 A B lt2 z H)). Qed.
Lemma lem347894 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f' : A -> B) (f : A -> B) : (term387 A B lt2 z x H f f') = (term388 A B lt2 z x H f' f).
Proof. exact (MK_COMB (@lem347893 A B lt2 z H) (@lem347892 A B x H f' f)). Qed.
Lemma lem347895 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term389 A B lt2 z x H f) = (term390 A B lt2 z x H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem347894 A B lt2 z x H f' f)). Qed.
Lemma lem347896 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347897 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term381 A B lt2 z x H f) = (term391 A B lt2 z x H f).
Proof. exact (MK_COMB (@lem347896 A B) (@lem347895 A B lt2 z x H f)). Qed.
Lemma lem347898 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : ((term380 A B lt2 z x H f) = (term381 A B lt2 z x H f)) = ((term376 A B lt2 z x H f) = (term391 A B lt2 z x H f)).
Proof. exact (MK_COMB (@lem347891 A B lt2 z x H f) (@lem347897 A B lt2 z x H f)). Qed.
Lemma lem347899 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term376 A B lt2 z x H f) = (term391 A B lt2 z x H f).
Proof. exact (EQ_MP (@lem347898 A B lt2 z x H f) (@lem347883 A B lt2 z x H f)). Qed.
Lemma lem347900 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term378 A B lt2 z x H) = (term392 A B lt2 z x H).
Proof. exact (fun_ext (fun f : A -> B => @lem347899 A B lt2 z x H f)). Qed.
Lemma lem347901 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347902 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term379 A B lt2 z x H) = (term393 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347901 A B) (@lem347900 A B lt2 z x H)). Qed.
Lemma lem347903 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term364 A B lt2 z x H) = (term393 A B lt2 z x H).
Proof. exact (TRANS (@lem347879 A B lt2 z x H) (@lem347902 A B lt2 z x H)). Qed.
Lemma lem347904 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term366 A B lt2 z H) = (term394 A B lt2 z H).
Proof. exact (fun_ext (fun x : type569 A B => @lem347903 A B lt2 z x H)). Qed.
Lemma lem347905 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem347906 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term367 A B lt2 z H) = (term395 A B lt2 z H).
Proof. exact (MK_COMB (@lem347905 A B) (@lem347904 A B lt2 z H)). Qed.
Lemma lem347907 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term350 A B lt2 z H) = (term395 A B lt2 z H).
Proof. exact (TRANS (@lem347859 A B lt2 z H) (@lem347906 A B lt2 z H)). Qed.
Lemma lem347908 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term352 A B lt2 H) = (term396 A B lt2 H).
Proof. exact (fun_ext (fun z : type515 A B => @lem347907 A B lt2 z H)). Qed.
Lemma lem347909 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A -> A)) = (@ex ((A -> B) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A -> A))). Qed.
Lemma lem347910 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term353 A B lt2 H) = (term397 A B lt2 H).
Proof. exact (MK_COMB (@lem347909 A B) (@lem347908 A B lt2 H)). Qed.
Lemma lem347911 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term334 A B lt2 H) = (term397 A B lt2 H).
Proof. exact (TRANS (@lem347839 A B lt2 H) (@lem347910 A B lt2 H)). Qed.
Lemma lem347912 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term159 A B lt2 H) = (term397 A B lt2 H).
Proof. exact (TRANS (@lem347815 A B lt2 H) (@lem347911 A B lt2 H)). Qed.
Lemma lem347913 {A B : Type'} (lt2 : type1402 A) : (term160 A B lt2) = (term398 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem347912 A B lt2 H)). Qed.
Lemma lem347914 {A B : Type'} : (@ex ((A -> B) -> A -> B)) = (@ex ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> B))). Qed.
Lemma lem347915 {A B : Type'} (lt2 : type1402 A) : (term161 A B lt2) = (term399 A B lt2).
Proof. exact (MK_COMB (@lem347914 A B) (@lem347913 A B lt2)). Qed.
Lemma lem347916 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347917 {A B : Type'} (lt2 : type1402 A) : (term162 A B lt2) = (term400 A B lt2).
Proof. exact (MK_COMB (@lem347916 A lt2) (@lem347915 A B lt2)). Qed.
Lemma lem347919 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem347920 {A B : Type'} (P : Prop) (Q : type111 A B) : (term401 A B P Q) = (term402 A B P Q).
Proof. exact (@lem347919 (type549 A B) P Q). Qed.
Lemma lem347921 {A B : Type'} (lt2 : type1402 A) : (term403 A B lt2) = (term404 A B lt2).
Proof. exact (@lem347920 A B (@WF A lt2) (term398 A B lt2)). Qed.
Lemma lem347922 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term405 A B lt2 H) = (term397 A B lt2 H).
Proof. exact (eq_refl (term405 A B lt2 H)). Qed.
Lemma lem347923 {A B : Type'} (lt2 : type1402 A) : (term406 A B lt2) = (term398 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem347922 A B lt2 H)). Qed.
Lemma lem347924 {A B : Type'} : (@ex ((A -> B) -> A -> B)) = (@ex ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> B))). Qed.
Lemma lem347925 {A B : Type'} (lt2 : type1402 A) : (term407 A B lt2) = (term399 A B lt2).
Proof. exact (MK_COMB (@lem347924 A B) (@lem347923 A B lt2)). Qed.
Lemma lem347926 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347927 {A B : Type'} (lt2 : type1402 A) : (term403 A B lt2) = (term400 A B lt2).
Proof. exact (MK_COMB (@lem347926 A lt2) (@lem347925 A B lt2)). Qed.
Lemma lem347928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347929 {A B : Type'} (lt2 : type1402 A) : (term408 A B lt2) = (term409 A B lt2).
Proof. exact (MK_COMB (@lem347928) (@lem347927 A B lt2)). Qed.
Lemma lem347930 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term405 A B lt2 H) = (term397 A B lt2 H).
Proof. exact (eq_refl (term405 A B lt2 H)). Qed.
Lemma lem347931 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347932 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term410 A B lt2 H) = (term411 A B lt2 H).
Proof. exact (MK_COMB (@lem347931 A lt2) (@lem347930 A B lt2 H)). Qed.
Lemma lem347933 {A B : Type'} (lt2 : type1402 A) : (term412 A B lt2) = (term413 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem347932 A B lt2 H)). Qed.
Lemma lem347934 {A B : Type'} : (@ex ((A -> B) -> A -> B)) = (@ex ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> B))). Qed.
Lemma lem347935 {A B : Type'} (lt2 : type1402 A) : (term404 A B lt2) = (term414 A B lt2).
Proof. exact (MK_COMB (@lem347934 A B) (@lem347933 A B lt2)). Qed.
Lemma lem347936 {A B : Type'} (lt2 : type1402 A) : ((term403 A B lt2) = (term404 A B lt2)) = ((term400 A B lt2) = (term414 A B lt2)).
Proof. exact (MK_COMB (@lem347929 A B lt2) (@lem347935 A B lt2)). Qed.
Lemma lem347937 {A B : Type'} (lt2 : type1402 A) : (term400 A B lt2) = (term414 A B lt2).
Proof. exact (EQ_MP (@lem347936 A B lt2) (@lem347921 A B lt2)). Qed.
Lemma lem347939 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem347940 {A B : Type'} (P : Prop) (Q : type94 A B) : (term415 A B P Q) = (term416 A B P Q).
Proof. exact (@lem347939 (type515 A B) P Q). Qed.
Lemma lem347941 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term417 A B lt2 H) = (term418 A B lt2 H).
Proof. exact (@lem347940 A B (@WF A lt2) (term396 A B lt2 H)). Qed.
Lemma lem347942 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term419 A B lt2 H z) = (term395 A B lt2 z H).
Proof. exact (eq_refl (term419 A B lt2 H z)). Qed.
Lemma lem347943 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term420 A B lt2 H) = (term396 A B lt2 H).
Proof. exact (fun_ext (fun z : type515 A B => @lem347942 A B lt2 z H)). Qed.
Lemma lem347944 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A -> A)) = (@ex ((A -> B) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A -> A))). Qed.
Lemma lem347945 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term421 A B lt2 H) = (term397 A B lt2 H).
Proof. exact (MK_COMB (@lem347944 A B) (@lem347943 A B lt2 H)). Qed.
Lemma lem347946 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347947 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term417 A B lt2 H) = (term411 A B lt2 H).
Proof. exact (MK_COMB (@lem347946 A lt2) (@lem347945 A B lt2 H)). Qed.
Lemma lem347948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347949 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term422 A B lt2 H) = (term423 A B lt2 H).
Proof. exact (MK_COMB (@lem347948) (@lem347947 A B lt2 H)). Qed.
Lemma lem347950 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term419 A B lt2 H z) = (term395 A B lt2 z H).
Proof. exact (eq_refl (term419 A B lt2 H z)). Qed.
Lemma lem347951 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347952 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term424 A B lt2 H z) = (term425 A B lt2 z H).
Proof. exact (MK_COMB (@lem347951 A lt2) (@lem347950 A B lt2 z H)). Qed.
Lemma lem347953 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term426 A B lt2 H) = (term427 A B lt2 H).
Proof. exact (fun_ext (fun z : type515 A B => @lem347952 A B lt2 z H)). Qed.
Lemma lem347954 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A -> A)) = (@ex ((A -> B) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A -> A))). Qed.
Lemma lem347955 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term418 A B lt2 H) = (term428 A B lt2 H).
Proof. exact (MK_COMB (@lem347954 A B) (@lem347953 A B lt2 H)). Qed.
Lemma lem347956 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : ((term417 A B lt2 H) = (term418 A B lt2 H)) = ((term411 A B lt2 H) = (term428 A B lt2 H)).
Proof. exact (MK_COMB (@lem347949 A B lt2 H) (@lem347955 A B lt2 H)). Qed.
Lemma lem347957 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term411 A B lt2 H) = (term428 A B lt2 H).
Proof. exact (EQ_MP (@lem347956 A B lt2 H) (@lem347941 A B lt2 H)). Qed.
Lemma lem347959 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem347960 {A B : Type'} (P : Prop) (Q : type118 A B) : (term354 A B P Q) = (term355 A B P Q).
Proof. exact (@lem347959 (type569 A B) P Q). Qed.
Lemma lem347961 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term429 A B lt2 z H) = (term430 A B lt2 z H).
Proof. exact (@lem347960 A B (@WF A lt2) (term394 A B lt2 z H)). Qed.
Lemma lem347962 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term431 A B lt2 z H x) = (term393 A B lt2 z x H).
Proof. exact (eq_refl (term431 A B lt2 z H x)). Qed.
Lemma lem347963 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term432 A B lt2 z H) = (term394 A B lt2 z H).
Proof. exact (fun_ext (fun x : type569 A B => @lem347962 A B lt2 z x H)). Qed.
Lemma lem347964 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem347965 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term433 A B lt2 z H) = (term395 A B lt2 z H).
Proof. exact (MK_COMB (@lem347964 A B) (@lem347963 A B lt2 z H)). Qed.
Lemma lem347966 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347967 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term429 A B lt2 z H) = (term425 A B lt2 z H).
Proof. exact (MK_COMB (@lem347966 A lt2) (@lem347965 A B lt2 z H)). Qed.
Lemma lem347968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347969 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term434 A B lt2 z H) = (term435 A B lt2 z H).
Proof. exact (MK_COMB (@lem347968) (@lem347967 A B lt2 z H)). Qed.
Lemma lem347970 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term431 A B lt2 z H x) = (term393 A B lt2 z x H).
Proof. exact (eq_refl (term431 A B lt2 z H x)). Qed.
Lemma lem347971 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347972 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term436 A B lt2 z H x) = (term437 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347971 A lt2) (@lem347970 A B lt2 z x H)). Qed.
Lemma lem347973 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term438 A B lt2 z H) = (term439 A B lt2 z H).
Proof. exact (fun_ext (fun x : type569 A B => @lem347972 A B lt2 z x H)). Qed.
Lemma lem347974 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem347975 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term430 A B lt2 z H) = (term440 A B lt2 z H).
Proof. exact (MK_COMB (@lem347974 A B) (@lem347973 A B lt2 z H)). Qed.
Lemma lem347976 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : ((term429 A B lt2 z H) = (term430 A B lt2 z H)) = ((term425 A B lt2 z H) = (term440 A B lt2 z H)).
Proof. exact (MK_COMB (@lem347969 A B lt2 z H) (@lem347975 A B lt2 z H)). Qed.
Lemma lem347977 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term425 A B lt2 z H) = (term440 A B lt2 z H).
Proof. exact (EQ_MP (@lem347976 A B lt2 z H) (@lem347961 A B lt2 z H)). Qed.
Lemma lem347979 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem347980 {A B : Type'} (P : Prop) (Q : type572 A B) : (term143 A B P Q) = (term142 A B P Q).
Proof. exact (@lem347979 (A -> B) P Q). Qed.
Lemma lem347981 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term441 A B lt2 z x H) = (term442 A B lt2 z x H).
Proof. exact (@lem347980 A B (@WF A lt2) (term392 A B lt2 z x H)). Qed.
Lemma lem347982 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term443 A B lt2 z x H f) = (term391 A B lt2 z x H f).
Proof. exact (eq_refl (term443 A B lt2 z x H f)). Qed.
Lemma lem347983 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term444 A B lt2 z x H) = (term392 A B lt2 z x H).
Proof. exact (fun_ext (fun f : A -> B => @lem347982 A B lt2 z x H f)). Qed.
Lemma lem347984 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347985 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term445 A B lt2 z x H) = (term393 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347984 A B) (@lem347983 A B lt2 z x H)). Qed.
Lemma lem347986 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347987 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term441 A B lt2 z x H) = (term437 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347986 A lt2) (@lem347985 A B lt2 z x H)). Qed.
Lemma lem347988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem347989 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term446 A B lt2 z x H) = (term447 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347988) (@lem347987 A B lt2 z x H)). Qed.
Lemma lem347990 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term443 A B lt2 z x H f) = (term391 A B lt2 z x H f).
Proof. exact (eq_refl (term443 A B lt2 z x H f)). Qed.
Lemma lem347991 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem347992 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term448 A B lt2 z x H f) = (term449 A B lt2 z x H f).
Proof. exact (MK_COMB (@lem347991 A lt2) (@lem347990 A B lt2 z x H f)). Qed.
Lemma lem347993 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term450 A B lt2 z x H) = (term451 A B lt2 z x H).
Proof. exact (fun_ext (fun f : A -> B => @lem347992 A B lt2 z x H f)). Qed.
Lemma lem347994 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem347995 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term442 A B lt2 z x H) = (term452 A B lt2 z x H).
Proof. exact (MK_COMB (@lem347994 A B) (@lem347993 A B lt2 z x H)). Qed.
Lemma lem347996 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : ((term441 A B lt2 z x H) = (term442 A B lt2 z x H)) = ((term437 A B lt2 z x H) = (term452 A B lt2 z x H)).
Proof. exact (MK_COMB (@lem347989 A B lt2 z x H) (@lem347995 A B lt2 z x H)). Qed.
Lemma lem347997 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term437 A B lt2 z x H) = (term452 A B lt2 z x H).
Proof. exact (EQ_MP (@lem347996 A B lt2 z x H) (@lem347981 A B lt2 z x H)). Qed.
Lemma lem347999 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem348000 {A B : Type'} (P : Prop) (Q : type572 A B) : (term143 A B P Q) = (term142 A B P Q).
Proof. exact (@lem347999 (A -> B) P Q). Qed.
Lemma lem348001 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term453 A B lt2 z x H f) = (term454 A B lt2 z x H f).
Proof. exact (@lem348000 A B (@WF A lt2) (term390 A B lt2 z x H f)). Qed.
Lemma lem348002 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f' : A -> B) (f : A -> B) : (term455 A B lt2 z x H f f') = (term388 A B lt2 z x H f' f).
Proof. exact (eq_refl (term455 A B lt2 z x H f f')). Qed.
Lemma lem348003 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term456 A B lt2 z x H f) = (term390 A B lt2 z x H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem348002 A B lt2 z x H f' f)). Qed.
Lemma lem348004 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348005 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term457 A B lt2 z x H f) = (term391 A B lt2 z x H f).
Proof. exact (MK_COMB (@lem348004 A B) (@lem348003 A B lt2 z x H f)). Qed.
Lemma lem348006 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem348007 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term453 A B lt2 z x H f) = (term449 A B lt2 z x H f).
Proof. exact (MK_COMB (@lem348006 A lt2) (@lem348005 A B lt2 z x H f)). Qed.
Lemma lem348008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348009 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term458 A B lt2 z x H f) = (term459 A B lt2 z x H f).
Proof. exact (MK_COMB (@lem348008) (@lem348007 A B lt2 z x H f)). Qed.
Lemma lem348010 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f' : A -> B) (f : A -> B) : (term455 A B lt2 z x H f f') = (term388 A B lt2 z x H f' f).
Proof. exact (eq_refl (term455 A B lt2 z x H f f')). Qed.
Lemma lem348011 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term137 A lt2).
Proof. exact (eq_refl (term137 A lt2)). Qed.
Lemma lem348012 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f' : A -> B) (f : A -> B) : (term460 A B lt2 z x H f f') = (term461 A B lt2 z x H f' f).
Proof. exact (MK_COMB (@lem348011 A lt2) (@lem348010 A B lt2 z x H f' f)). Qed.
Lemma lem348013 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term462 A B lt2 z x H f) = (term463 A B lt2 z x H f).
Proof. exact (fun_ext (fun f' : A -> B => @lem348012 A B lt2 z x H f' f)). Qed.
Lemma lem348014 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348015 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term454 A B lt2 z x H f) = (term464 A B lt2 z x H f).
Proof. exact (MK_COMB (@lem348014 A B) (@lem348013 A B lt2 z x H f)). Qed.
Lemma lem348016 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : ((term453 A B lt2 z x H f) = (term454 A B lt2 z x H f)) = ((term449 A B lt2 z x H f) = (term464 A B lt2 z x H f)).
Proof. exact (MK_COMB (@lem348009 A B lt2 z x H f) (@lem348015 A B lt2 z x H f)). Qed.
Lemma lem348017 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) (f : A -> B) : (term449 A B lt2 z x H f) = (term464 A B lt2 z x H f).
Proof. exact (EQ_MP (@lem348016 A B lt2 z x H f) (@lem348001 A B lt2 z x H f)). Qed.
Lemma lem348018 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term451 A B lt2 z x H) = (term465 A B lt2 z x H).
Proof. exact (fun_ext (fun f : A -> B => @lem348017 A B lt2 z x H f)). Qed.
Lemma lem348019 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348020 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term452 A B lt2 z x H) = (term466 A B lt2 z x H).
Proof. exact (MK_COMB (@lem348019 A B) (@lem348018 A B lt2 z x H)). Qed.
Lemma lem348021 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x : type569 A B) (H : type549 A B) : (term437 A B lt2 z x H) = (term466 A B lt2 z x H).
Proof. exact (TRANS (@lem347997 A B lt2 z x H) (@lem348020 A B lt2 z x H)). Qed.
Lemma lem348022 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term439 A B lt2 z H) = (term467 A B lt2 z H).
Proof. exact (fun_ext (fun x : type569 A B => @lem348021 A B lt2 z x H)). Qed.
Lemma lem348023 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem348024 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term440 A B lt2 z H) = (term468 A B lt2 z H).
Proof. exact (MK_COMB (@lem348023 A B) (@lem348022 A B lt2 z H)). Qed.
Lemma lem348025 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term425 A B lt2 z H) = (term468 A B lt2 z H).
Proof. exact (TRANS (@lem347977 A B lt2 z H) (@lem348024 A B lt2 z H)). Qed.
Lemma lem348026 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term427 A B lt2 H) = (term469 A B lt2 H).
Proof. exact (fun_ext (fun z : type515 A B => @lem348025 A B lt2 z H)). Qed.
Lemma lem348027 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A -> A)) = (@ex ((A -> B) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A -> A))). Qed.
Lemma lem348028 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term428 A B lt2 H) = (term470 A B lt2 H).
Proof. exact (MK_COMB (@lem348027 A B) (@lem348026 A B lt2 H)). Qed.
Lemma lem348029 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term411 A B lt2 H) = (term470 A B lt2 H).
Proof. exact (TRANS (@lem347957 A B lt2 H) (@lem348028 A B lt2 H)). Qed.
Lemma lem348030 {A B : Type'} (lt2 : type1402 A) : (term413 A B lt2) = (term471 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem348029 A B lt2 H)). Qed.
Lemma lem348031 {A B : Type'} : (@ex ((A -> B) -> A -> B)) = (@ex ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> B))). Qed.
Lemma lem348032 {A B : Type'} (lt2 : type1402 A) : (term414 A B lt2) = (term472 A B lt2).
Proof. exact (MK_COMB (@lem348031 A B) (@lem348030 A B lt2)). Qed.
Lemma lem348033 {A B : Type'} (lt2 : type1402 A) : (term400 A B lt2) = (term472 A B lt2).
Proof. exact (TRANS (@lem347937 A B lt2) (@lem348032 A B lt2)). Qed.
Lemma lem348034 {A B : Type'} (lt2 : type1402 A) : (term162 A B lt2) = (term472 A B lt2).
Proof. exact (TRANS (@lem347917 A B lt2) (@lem348033 A B lt2)). Qed.
Lemma lem348035 {A B : Type'} (lt2 : type1402 A) : (term139 A B lt2) = (term472 A B lt2).
Proof. exact (TRANS (@lem347555 A B lt2) (@lem348034 A B lt2)). Qed.
Lemma lem348036 {A B : Type'} (lt2 : type1402 A) : (term12 A B lt2) = (term472 A B lt2).
Proof. exact (TRANS (@lem347207 A B lt2) (@lem348035 A B lt2)). Qed.
Lemma lem348037 {A B : Type'} (lt2 : type1402 A) (h1 : term12 A B lt2) : term472 A B lt2.
Proof. exact (EQ_MP (@lem348036 A B lt2) (@lem347106 A B lt2 h1)). Qed.
Lemma lem348045 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term32 A B lt2 x f g z) = (term473 A B lt2 x f g z).
Proof. exact (@lem17265 (lt2 z x) ((f z) = (g z))). Qed.
Lemma lem348046 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term33 A B lt2 x f g) = (term474 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem348045 A B lt2 x f g z)). Qed.
Lemma lem348047 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem348048 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term34 A B lt2 x f g) = (term475 A B lt2 x f g).
Proof. exact (MK_COMB (@lem348047 A) (@lem348046 A B lt2 x f g)). Qed.
Lemma lem348049 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term476 A B f H g x) = (term476 A B f H g x).
Proof. exact (eq_refl (term476 A B f H g x)). Qed.
Lemma lem348050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem348051 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term477 A B lt2 x f g) = (term478 A B lt2 x f g).
Proof. exact (MK_COMB (@lem348050) (@lem348048 A B lt2 x f g)). Qed.
Lemma lem348052 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term479 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem348051 A B lt2 x f g) (@lem348049 A B f H g x)). Qed.
Lemma lem348053 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term481 A B lt2 f H g x) = (term479 A B lt2 f H g x).
Proof. exact (@lem17362 (term34 A B lt2 x f g) ((H f x) = (H g x))). Qed.
Lemma lem348054 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term481 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (TRANS (@lem348053 A B lt2 f H g x) (@lem348052 A B lt2 f H g x)). Qed.
Lemma lem348055 {A : Type'} (P : A -> Prop) : (term69 A P) = (term70 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem348056 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term482 A B lt2 f H g) = (term483 A B lt2 f H g).
Proof. exact (@lem348055 A (term37 A B lt2 f H g)). Qed.
Lemma lem348057 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term484 A B lt2 f H g x) = (term36 A B lt2 f H g x).
Proof. exact (eq_refl (term484 A B lt2 f H g x)). Qed.
Lemma lem348058 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem348059 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term485 A B lt2 f H g x) = (term481 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem348058) (@lem348057 A B lt2 f H g x)). Qed.
Lemma lem348060 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term485 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (TRANS (@lem348059 A B lt2 f H g x) (@lem348054 A B lt2 f H g x)). Qed.
Lemma lem348061 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term486 A B lt2 f H g) = (term487 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem348060 A B lt2 f H g x)). Qed.
Lemma lem348062 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348063 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term483 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (MK_COMB (@lem348062 A) (@lem348061 A B lt2 f H g)). Qed.
Lemma lem348064 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term482 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (TRANS (@lem348056 A B lt2 f H g) (@lem348063 A B lt2 f H g)). Qed.
Lemma lem348065 {A B : Type'} (P : type572 A B) : (term489 A B P) = (term490 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem348066 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term491 A B lt2 f H) = (term492 A B lt2 f H).
Proof. exact (@lem348065 A B (term39 A B lt2 f H)). Qed.
Lemma lem348067 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term493 A B lt2 f H g) = (term38 A B lt2 f H g).
Proof. exact (eq_refl (term493 A B lt2 f H g)). Qed.
Lemma lem348068 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem348069 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term494 A B lt2 f H g) = (term482 A B lt2 f H g).
Proof. exact (MK_COMB (@lem348068) (@lem348067 A B lt2 f H g)). Qed.
Lemma lem348070 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term494 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (TRANS (@lem348069 A B lt2 f H g) (@lem348064 A B lt2 f H g)). Qed.
Lemma lem348071 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term495 A B lt2 f H) = (term496 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem348070 A B lt2 f H g)). Qed.
Lemma lem348072 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348073 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term492 A B lt2 f H) = (term497 A B lt2 f H).
Proof. exact (MK_COMB (@lem348072 A B) (@lem348071 A B lt2 f H)). Qed.
Lemma lem348074 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term491 A B lt2 f H) = (term497 A B lt2 f H).
Proof. exact (TRANS (@lem348066 A B lt2 f H) (@lem348073 A B lt2 f H)). Qed.
Lemma lem348075 {A B : Type'} (P : type572 A B) : (term489 A B P) = (term490 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem348076 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term498 A B lt2 H) = (term499 A B lt2 H).
Proof. exact (@lem348075 A B (term41 A B lt2 H)). Qed.
Lemma lem348077 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term500 A B lt2 H f) = (term40 A B lt2 f H).
Proof. exact (eq_refl (term500 A B lt2 H f)). Qed.
Lemma lem348078 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem348079 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term501 A B lt2 H f) = (term491 A B lt2 f H).
Proof. exact (MK_COMB (@lem348078) (@lem348077 A B lt2 f H)). Qed.
Lemma lem348080 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term501 A B lt2 H f) = (term497 A B lt2 f H).
Proof. exact (TRANS (@lem348079 A B lt2 f H) (@lem348074 A B lt2 f H)). Qed.
Lemma lem348081 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term502 A B lt2 H) = (term503 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem348080 A B lt2 f H)). Qed.
Lemma lem348082 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348083 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term499 A B lt2 H) = (term504 A B lt2 H).
Proof. exact (MK_COMB (@lem348082 A B) (@lem348081 A B lt2 H)). Qed.
Lemma lem348084 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term498 A B lt2 H) = (term504 A B lt2 H).
Proof. exact (TRANS (@lem348076 A B lt2 H) (@lem348083 A B lt2 H)). Qed.
Lemma lem348086 {A : Type'} (P : A -> Prop) : (term69 A P) = (term70 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem348087 {A B : Type'} (H : type549 A B) (f : A -> B) : (term88 A B H f) = (term89 A B H f).
Proof. exact (@lem348086 A (term28 A B H f)). Qed.
Lemma lem348088 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term90 A B H f x) = ((f x) = (H f x)).
Proof. exact (eq_refl (term90 A B H f x)). Qed.
Lemma lem348089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem348091 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term91 A B H f x) = (term92 A B H f x).
Proof. exact (MK_COMB (@lem348089) (@lem348088 A B H f x)). Qed.
Lemma lem348092 {A B : Type'} (H : type549 A B) (f : A -> B) : (term93 A B H f) = (term94 A B H f).
Proof. exact (fun_ext (fun x : A => @lem348091 A B H f x)). Qed.
Lemma lem348093 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348094 {A B : Type'} (H : type549 A B) (f : A -> B) : (term89 A B H f) = (term95 A B H f).
Proof. exact (MK_COMB (@lem348093 A) (@lem348092 A B H f)). Qed.
Lemma lem348095 {A B : Type'} (H : type549 A B) (f : A -> B) : (term88 A B H f) = (term95 A B H f).
Proof. exact (TRANS (@lem348087 A B H f) (@lem348094 A B H f)). Qed.
Lemma lem348097 {A : Type'} (P : A -> Prop) : (term69 A P) = (term70 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem348098 {A B : Type'} (H : type549 A B) (g : A -> B) : (term88 A B H g) = (term89 A B H g).
Proof. exact (@lem348097 A (term28 A B H g)). Qed.
Lemma lem348099 {A B : Type'} (H : type549 A B) (g : A -> B) (x : A) : (term90 A B H g x) = ((g x) = (H g x)).
Proof. exact (eq_refl (term90 A B H g x)). Qed.
Lemma lem348100 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem348102 {A B : Type'} (H : type549 A B) (g : A -> B) (x : A) : (term91 A B H g x) = (term92 A B H g x).
Proof. exact (MK_COMB (@lem348100) (@lem348099 A B H g x)). Qed.
Lemma lem348103 {A B : Type'} (H : type549 A B) (g : A -> B) : (term93 A B H g) = (term94 A B H g).
Proof. exact (fun_ext (fun x : A => @lem348102 A B H g x)). Qed.
Lemma lem348104 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348105 {A B : Type'} (H : type549 A B) (g : A -> B) : (term89 A B H g) = (term95 A B H g).
Proof. exact (MK_COMB (@lem348104 A) (@lem348103 A B H g)). Qed.
Lemma lem348106 {A B : Type'} (H : type549 A B) (g : A -> B) : (term88 A B H g) = (term95 A B H g).
Proof. exact (TRANS (@lem348098 A B H g) (@lem348105 A B H g)). Qed.
Lemma lem348107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348108 {A B : Type'} (H : type549 A B) (f : A -> B) : (term505 A B H f) = (term506 A B H f).
Proof. exact (MK_COMB (@lem348107) (@lem348095 A B H f)). Qed.
Lemma lem348109 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term507 A B f H g) = (term508 A B f H g).
Proof. exact (MK_COMB (@lem348108 A B H f) (@lem348106 A B H g)). Qed.
Lemma lem348110 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term509 A B f H g) = (term507 A B f H g).
Proof. exact (@lem17045 (term29 A B H f) (term29 A B H g)). Qed.
Lemma lem348111 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term509 A B f H g) = (term508 A B f H g).
Proof. exact (TRANS (@lem348110 A B f H g) (@lem348109 A B f H g)). Qed.
Lemma lem348112 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (f = g).
Proof. exact (eq_refl (f = g)). Qed.
Lemma lem348113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348114 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term510 A B f H g) = (term511 A B f H g).
Proof. exact (MK_COMB (@lem348113) (@lem348111 A B f H g)). Qed.
Lemma lem348115 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term512 A B H f g) = (term513 A B H f g).
Proof. exact (MK_COMB (@lem348114 A B f H g) (@lem348112 A B f g)). Qed.
Lemma lem348116 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term53 A B H f g) = (term512 A B H f g).
Proof. exact (@lem17265 (term51 A B f H g) (f = g)). Qed.
Lemma lem348117 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term53 A B H f g) = (term513 A B H f g).
Proof. exact (TRANS (@lem348116 A B H f g) (@lem348115 A B H f g)). Qed.
Lemma lem348118 {A B : Type'} (H : type549 A B) (f : A -> B) : (term54 A B H f) = (term514 A B H f).
Proof. exact (fun_ext (fun g : A -> B => @lem348117 A B H f g)). Qed.
Lemma lem348119 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem348120 {A B : Type'} (H : type549 A B) (f : A -> B) : (term55 A B H f) = (term515 A B H f).
Proof. exact (MK_COMB (@lem348119 A B) (@lem348118 A B H f)). Qed.
Lemma lem348121 {A B : Type'} (H : type549 A B) : (term56 A B H) = (term516 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem348120 A B H f)). Qed.
Lemma lem348122 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem348123 {A B : Type'} (H : type549 A B) : (term57 A B H) = (term517 A B H).
Proof. exact (MK_COMB (@lem348122 A B) (@lem348121 A B H)). Qed.
Lemma lem348124 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348125 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term518 A B lt2 H) = (term519 A B lt2 H).
Proof. exact (MK_COMB (@lem348124) (@lem348084 A B lt2 H)). Qed.
Lemma lem348126 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term520 A B lt2 H) = (term521 A B lt2 H).
Proof. exact (MK_COMB (@lem348125 A B lt2 H) (@lem348123 A B H)). Qed.
Lemma lem348127 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term58 A B lt2 H) = (term520 A B lt2 H).
Proof. exact (@lem17265 (term42 A B lt2 H) (term57 A B H)). Qed.
Lemma lem348128 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term58 A B lt2 H) = (term521 A B lt2 H).
Proof. exact (TRANS (@lem348127 A B lt2 H) (@lem348126 A B lt2 H)). Qed.
Lemma lem348129 {A B : Type'} (lt2 : type1402 A) : (term59 A B lt2) = (term522 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem348128 A B lt2 H)). Qed.
Lemma lem348130 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348131 {A B : Type'} (lt2 : type1402 A) : (term60 A B lt2) = (term523 A B lt2).
Proof. exact (MK_COMB (@lem348130 A B) (@lem348129 A B lt2)). Qed.
Lemma lem348133 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348134 {A B : Type'} (lt2 : type1402 A) : (term525 A B lt2) = (term526 A B lt2).
Proof. exact (MK_COMB (@lem348133 A lt2) (@lem348131 A B lt2)). Qed.
Lemma lem348135 {A B : Type'} (lt2 : type1402 A) : (term61 A B lt2) = (term525 A B lt2).
Proof. exact (@lem17265 (@WF A lt2) (term60 A B lt2)). Qed.
Lemma lem348136 {A B : Type'} (lt2 : type1402 A) : (term61 A B lt2) = (term526 A B lt2).
Proof. exact (TRANS (@lem348135 A B lt2) (@lem348134 A B lt2)). Qed.
Lemma lem348137 {A B : Type'} : (term62 A B) = (term527 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348136 A B lt2)). Qed.
Lemma lem348138 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348139 {A B : Type'} : (term8 A B) = (term528 A B).
Proof. exact (MK_COMB (@lem348138 A) (@lem348137 A B)). Qed.
Lemma lem348402 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term529 A P Q) = (term530 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem348403 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term529 A P Q) = (term530 A P Q).
Proof. exact (@lem348402 A P Q). Qed.
Lemma lem348404 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term531 A B f H g) = (term532 A B f H g).
Proof. exact (@lem348403 A (term94 A B H f) (term94 A B H g)). Qed.
Lemma lem348405 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term265 A B H f x) = (term92 A B H f x).
Proof. exact (eq_refl (term265 A B H f x)). Qed.
Lemma lem348406 {A B : Type'} (H : type549 A B) (f : A -> B) : (term533 A B H f) = (term94 A B H f).
Proof. exact (fun_ext (fun x : A => @lem348405 A B H f x)). Qed.
Lemma lem348407 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348408 {A B : Type'} (H : type549 A B) (f : A -> B) : (term534 A B H f) = (term95 A B H f).
Proof. exact (MK_COMB (@lem348407 A) (@lem348406 A B H f)). Qed.
Lemma lem348409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348410 {A B : Type'} (H : type549 A B) (f : A -> B) : (term535 A B H f) = (term506 A B H f).
Proof. exact (MK_COMB (@lem348409) (@lem348408 A B H f)). Qed.
Lemma lem348411 {A B : Type'} (H : type549 A B) (g : A -> B) (x : A) : (term265 A B H g x) = (term92 A B H g x).
Proof. exact (eq_refl (term265 A B H g x)). Qed.
Lemma lem348412 {A B : Type'} (H : type549 A B) (g : A -> B) : (term533 A B H g) = (term94 A B H g).
Proof. exact (fun_ext (fun x : A => @lem348411 A B H g x)). Qed.
Lemma lem348413 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348414 {A B : Type'} (H : type549 A B) (g : A -> B) : (term534 A B H g) = (term95 A B H g).
Proof. exact (MK_COMB (@lem348413 A) (@lem348412 A B H g)). Qed.
Lemma lem348415 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term531 A B f H g) = (term508 A B f H g).
Proof. exact (MK_COMB (@lem348410 A B H f) (@lem348414 A B H g)). Qed.
Lemma lem348416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348417 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term536 A B f H g) = (term537 A B f H g).
Proof. exact (MK_COMB (@lem348416) (@lem348415 A B f H g)). Qed.
Lemma lem348418 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term265 A B H f x) = (term92 A B H f x).
Proof. exact (eq_refl (term265 A B H f x)). Qed.
Lemma lem348419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348420 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term538 A B H f x) = (term539 A B H f x).
Proof. exact (MK_COMB (@lem348419) (@lem348418 A B H f x)). Qed.
Lemma lem348421 {A B : Type'} (H : type549 A B) (g : A -> B) (x : A) : (term265 A B H g x) = (term92 A B H g x).
Proof. exact (eq_refl (term265 A B H g x)). Qed.
Lemma lem348422 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term540 A B f H g x) = (term541 A B f H g x).
Proof. exact (MK_COMB (@lem348420 A B H f x) (@lem348421 A B H g x)). Qed.
Lemma lem348423 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term542 A B f H g) = (term543 A B f H g).
Proof. exact (fun_ext (fun x : A => @lem348422 A B f H g x)). Qed.
Lemma lem348424 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348425 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term532 A B f H g) = (term544 A B f H g).
Proof. exact (MK_COMB (@lem348424 A) (@lem348423 A B f H g)). Qed.
Lemma lem348426 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : ((term531 A B f H g) = (term532 A B f H g)) = ((term508 A B f H g) = (term544 A B f H g)).
Proof. exact (MK_COMB (@lem348417 A B f H g) (@lem348425 A B f H g)). Qed.
Lemma lem348427 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term508 A B f H g) = (term544 A B f H g).
Proof. exact (EQ_MP (@lem348426 A B f H g) (@lem348404 A B f H g)). Qed.
Lemma lem348428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348429 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term511 A B f H g) = (term545 A B f H g).
Proof. exact (MK_COMB (@lem348428) (@lem348427 A B f H g)). Qed.
Lemma lem348430 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (f = g).
Proof. exact (eq_refl (f = g)). Qed.
Lemma lem348431 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term513 A B H f g) = (term546 A B H f g).
Proof. exact (MK_COMB (@lem348429 A B f H g) (@lem348430 A B f g)). Qed.
Lemma lem348433 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem348434 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (@lem348433 A P Q). Qed.
Lemma lem348435 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term547 A B H f g) = (term548 A B H f g).
Proof. exact (@lem348434 A (term543 A B f H g) (f = g)). Qed.
Lemma lem348436 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term549 A B f H g x) = (term541 A B f H g x).
Proof. exact (eq_refl (term549 A B f H g x)). Qed.
Lemma lem348437 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term550 A B f H g) = (term543 A B f H g).
Proof. exact (fun_ext (fun x : A => @lem348436 A B f H g x)). Qed.
Lemma lem348438 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348439 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term551 A B f H g) = (term544 A B f H g).
Proof. exact (MK_COMB (@lem348438 A) (@lem348437 A B f H g)). Qed.
Lemma lem348440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348441 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) : (term552 A B f H g) = (term545 A B f H g).
Proof. exact (MK_COMB (@lem348440) (@lem348439 A B f H g)). Qed.
Lemma lem348442 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (f = g).
Proof. exact (eq_refl (f = g)). Qed.
Lemma lem348443 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term547 A B H f g) = (term546 A B H f g).
Proof. exact (MK_COMB (@lem348441 A B f H g) (@lem348442 A B f g)). Qed.
Lemma lem348444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348445 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term553 A B H f g) = (term554 A B H f g).
Proof. exact (MK_COMB (@lem348444) (@lem348443 A B H f g)). Qed.
Lemma lem348446 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term549 A B f H g x) = (term541 A B f H g x).
Proof. exact (eq_refl (term549 A B f H g x)). Qed.
Lemma lem348447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348448 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term555 A B f H g x) = (term556 A B f H g x).
Proof. exact (MK_COMB (@lem348447) (@lem348446 A B f H g x)). Qed.
Lemma lem348449 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (f = g).
Proof. exact (eq_refl (f = g)). Qed.
Lemma lem348450 {A B : Type'} (H : type549 A B) (x : A) (f : A -> B) (g : A -> B) : (term557 A B H x f g) = (term558 A B H x f g).
Proof. exact (MK_COMB (@lem348448 A B f H g x) (@lem348449 A B f g)). Qed.
Lemma lem348451 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term559 A B H f g) = (term560 A B H f g).
Proof. exact (fun_ext (fun x : A => @lem348450 A B H x f g)). Qed.
Lemma lem348452 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348453 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term548 A B H f g) = (term561 A B H f g).
Proof. exact (MK_COMB (@lem348452 A) (@lem348451 A B H f g)). Qed.
Lemma lem348454 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : ((term547 A B H f g) = (term548 A B H f g)) = ((term546 A B H f g) = (term561 A B H f g)).
Proof. exact (MK_COMB (@lem348445 A B H f g) (@lem348453 A B H f g)). Qed.
Lemma lem348455 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term546 A B H f g) = (term561 A B H f g).
Proof. exact (EQ_MP (@lem348454 A B H f g) (@lem348435 A B H f g)). Qed.
Lemma lem348456 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term513 A B H f g) = (term561 A B H f g).
Proof. exact (TRANS (@lem348431 A B H f g) (@lem348455 A B H f g)). Qed.
Lemma lem348457 {A B : Type'} (H : type549 A B) (f : A -> B) : (term514 A B H f) = (term562 A B H f).
Proof. exact (fun_ext (fun g : A -> B => @lem348456 A B H f g)). Qed.
Lemma lem348458 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem348459 {A B : Type'} (H : type549 A B) (f : A -> B) : (term515 A B H f) = (term563 A B H f).
Proof. exact (MK_COMB (@lem348458 A B) (@lem348457 A B H f)). Qed.
Lemma lem348461 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348462 {A B : Type'} (P : type551 A B) : (term258 A B P) = (term259 A B P).
Proof. exact (@lem348461 (A -> B) A P). Qed.
Lemma lem348463 {A B : Type'} (H : type549 A B) (f : A -> B) : (term564 A B H f) = (term565 A B H f).
Proof. exact (@lem348462 A B (term566 A B H f)). Qed.
Lemma lem348464 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term567 A B H f g) = (term560 A B H f g).
Proof. exact (eq_refl (term567 A B H f g)). Qed.
Lemma lem348465 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem348466 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) (x : A) : (term568 A B H f g x) = (term569 A B H f g x).
Proof. exact (MK_COMB (@lem348464 A B H f g) (@lem348465 A x)). Qed.
Lemma lem348467 {A B : Type'} (H : type549 A B) (x : A) (f : A -> B) (g : A -> B) : (term569 A B H f g x) = (term558 A B H x f g).
Proof. exact (eq_refl (term569 A B H f g x)). Qed.
Lemma lem348468 {A B : Type'} (H : type549 A B) (x : A) (f : A -> B) (g : A -> B) : (term568 A B H f g x) = (term558 A B H x f g).
Proof. exact (TRANS (@lem348466 A B H f g x) (@lem348467 A B H x f g)). Qed.
Lemma lem348469 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term570 A B H f g) = (term560 A B H f g).
Proof. exact (fun_ext (fun x : A => @lem348468 A B H x f g)). Qed.
Lemma lem348470 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348471 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term571 A B H f g) = (term561 A B H f g).
Proof. exact (MK_COMB (@lem348470 A) (@lem348469 A B H f g)). Qed.
Lemma lem348472 {A B : Type'} (H : type549 A B) (f : A -> B) : (term572 A B H f) = (term562 A B H f).
Proof. exact (fun_ext (fun g : A -> B => @lem348471 A B H f g)). Qed.
Lemma lem348473 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem348474 {A B : Type'} (H : type549 A B) (f : A -> B) : (term564 A B H f) = (term563 A B H f).
Proof. exact (MK_COMB (@lem348473 A B) (@lem348472 A B H f)). Qed.
Lemma lem348475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348476 {A B : Type'} (H : type549 A B) (f : A -> B) : (term573 A B H f) = (term574 A B H f).
Proof. exact (MK_COMB (@lem348475) (@lem348474 A B H f)). Qed.
Lemma lem348477 {A B : Type'} (H : type549 A B) (f : A -> B) (g : A -> B) : (term567 A B H f g) = (term560 A B H f g).
Proof. exact (eq_refl (term567 A B H f g)). Qed.
Lemma lem348478 {A B : Type'} (x : type569 A B) (g : A -> B) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem348479 {A B : Type'} (H : type549 A B) (f : A -> B) (x : type569 A B) (g : A -> B) : (term575 A B H f x g) = (term576 A B H f x g).
Proof. exact (MK_COMB (@lem348477 A B H f g) (@lem348478 A B x g)). Qed.
Lemma lem348480 {A B : Type'} (H : type549 A B) (x : type569 A B) (f : A -> B) (g : A -> B) : (term576 A B H f x g) = (term577 A B H x f g).
Proof. exact (eq_refl (term576 A B H f x g)). Qed.
Lemma lem348481 {A B : Type'} (H : type549 A B) (x : type569 A B) (f : A -> B) (g : A -> B) : (term575 A B H f x g) = (term577 A B H x f g).
Proof. exact (TRANS (@lem348479 A B H f x g) (@lem348480 A B H x f g)). Qed.
Lemma lem348482 {A B : Type'} (H : type549 A B) (x : type569 A B) (f : A -> B) : (term578 A B H f x) = (term579 A B H x f).
Proof. exact (fun_ext (fun g : A -> B => @lem348481 A B H x f g)). Qed.
Lemma lem348483 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem348484 {A B : Type'} (H : type549 A B) (x : type569 A B) (f : A -> B) : (term580 A B H f x) = (term581 A B H x f).
Proof. exact (MK_COMB (@lem348483 A B) (@lem348482 A B H x f)). Qed.
Lemma lem348485 {A B : Type'} (H : type549 A B) (f : A -> B) : (term582 A B H f) = (term583 A B H f).
Proof. exact (fun_ext (fun x : type569 A B => @lem348484 A B H x f)). Qed.
Lemma lem348486 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem348487 {A B : Type'} (H : type549 A B) (f : A -> B) : (term565 A B H f) = (term584 A B H f).
Proof. exact (MK_COMB (@lem348486 A B) (@lem348485 A B H f)). Qed.
Lemma lem348488 {A B : Type'} (H : type549 A B) (f : A -> B) : ((term564 A B H f) = (term565 A B H f)) = ((term563 A B H f) = (term584 A B H f)).
Proof. exact (MK_COMB (@lem348476 A B H f) (@lem348487 A B H f)). Qed.
Lemma lem348489 {A B : Type'} (H : type549 A B) (f : A -> B) : (term563 A B H f) = (term584 A B H f).
Proof. exact (EQ_MP (@lem348488 A B H f) (@lem348463 A B H f)). Qed.
Lemma lem348490 {A B : Type'} (H : type549 A B) (f : A -> B) : (term515 A B H f) = (term584 A B H f).
Proof. exact (TRANS (@lem348459 A B H f) (@lem348489 A B H f)). Qed.
Lemma lem348491 {A B : Type'} (H : type549 A B) : (term516 A B H) = (term585 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem348490 A B H f)). Qed.
Lemma lem348492 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem348493 {A B : Type'} (H : type549 A B) : (term517 A B H) = (term586 A B H).
Proof. exact (MK_COMB (@lem348492 A B) (@lem348491 A B H)). Qed.
Lemma lem348495 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348496 {A B : Type'} (P : type499 A B) : (term587 A B P) = (term588 A B P).
Proof. exact (@lem348495 (A -> B) (type569 A B) P). Qed.
Lemma lem348497 {A B : Type'} (H : type549 A B) : (term589 A B H) = (term590 A B H).
Proof. exact (@lem348496 A B (term591 A B H)). Qed.
Lemma lem348498 {A B : Type'} (H : type549 A B) (f : A -> B) : (term592 A B H f) = (term583 A B H f).
Proof. exact (eq_refl (term592 A B H f)). Qed.
Lemma lem348499 {A B : Type'} (x : type569 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem348500 {A B : Type'} (H : type549 A B) (f : A -> B) (x : type569 A B) : (term593 A B H f x) = (term594 A B H f x).
Proof. exact (MK_COMB (@lem348498 A B H f) (@lem348499 A B x)). Qed.
Lemma lem348501 {A B : Type'} (H : type549 A B) (x : type569 A B) (f : A -> B) : (term594 A B H f x) = (term581 A B H x f).
Proof. exact (eq_refl (term594 A B H f x)). Qed.
Lemma lem348502 {A B : Type'} (H : type549 A B) (x : type569 A B) (f : A -> B) : (term593 A B H f x) = (term581 A B H x f).
Proof. exact (TRANS (@lem348500 A B H f x) (@lem348501 A B H x f)). Qed.
Lemma lem348503 {A B : Type'} (H : type549 A B) (f : A -> B) : (term595 A B H f) = (term583 A B H f).
Proof. exact (fun_ext (fun x : type569 A B => @lem348502 A B H x f)). Qed.
Lemma lem348504 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem348505 {A B : Type'} (H : type549 A B) (f : A -> B) : (term596 A B H f) = (term584 A B H f).
Proof. exact (MK_COMB (@lem348504 A B) (@lem348503 A B H f)). Qed.
Lemma lem348506 {A B : Type'} (H : type549 A B) : (term597 A B H) = (term585 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem348505 A B H f)). Qed.
Lemma lem348507 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem348508 {A B : Type'} (H : type549 A B) : (term589 A B H) = (term586 A B H).
Proof. exact (MK_COMB (@lem348507 A B) (@lem348506 A B H)). Qed.
Lemma lem348509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348510 {A B : Type'} (H : type549 A B) : (term598 A B H) = (term599 A B H).
Proof. exact (MK_COMB (@lem348509) (@lem348508 A B H)). Qed.
Lemma lem348511 {A B : Type'} (H : type549 A B) (f : A -> B) : (term592 A B H f) = (term583 A B H f).
Proof. exact (eq_refl (term592 A B H f)). Qed.
Lemma lem348512 {A B : Type'} (x : type522 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem348513 {A B : Type'} (H : type549 A B) (x : type522 A B) (f : A -> B) : (term600 A B H x f) = (term601 A B H x f).
Proof. exact (MK_COMB (@lem348511 A B H f) (@lem348512 A B x f)). Qed.
Lemma lem348514 {A B : Type'} (H : type549 A B) (x : type522 A B) (f : A -> B) : (term601 A B H x f) = (term602 A B H x f).
Proof. exact (eq_refl (term601 A B H x f)). Qed.
Lemma lem348515 {A B : Type'} (H : type549 A B) (x : type522 A B) (f : A -> B) : (term600 A B H x f) = (term602 A B H x f).
Proof. exact (TRANS (@lem348513 A B H x f) (@lem348514 A B H x f)). Qed.
Lemma lem348516 {A B : Type'} (H : type549 A B) (x : type522 A B) : (term603 A B H x) = (term604 A B H x).
Proof. exact (fun_ext (fun f : A -> B => @lem348515 A B H x f)). Qed.
Lemma lem348517 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem348518 {A B : Type'} (H : type549 A B) (x : type522 A B) : (term605 A B H x) = (term606 A B H x).
Proof. exact (MK_COMB (@lem348517 A B) (@lem348516 A B H x)). Qed.
Lemma lem348519 {A B : Type'} (H : type549 A B) : (term607 A B H) = (term608 A B H).
Proof. exact (fun_ext (fun x : type522 A B => @lem348518 A B H x)). Qed.
Lemma lem348520 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A)) = (@ex ((A -> B) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A))). Qed.
Lemma lem348521 {A B : Type'} (H : type549 A B) : (term590 A B H) = (term609 A B H).
Proof. exact (MK_COMB (@lem348520 A B) (@lem348519 A B H)). Qed.
Lemma lem348522 {A B : Type'} (H : type549 A B) : ((term589 A B H) = (term590 A B H)) = ((term586 A B H) = (term609 A B H)).
Proof. exact (MK_COMB (@lem348510 A B H) (@lem348521 A B H)). Qed.
Lemma lem348523 {A B : Type'} (H : type549 A B) : (term586 A B H) = (term609 A B H).
Proof. exact (EQ_MP (@lem348522 A B H) (@lem348497 A B H)). Qed.
Lemma lem348524 {A B : Type'} (H : type549 A B) : (term517 A B H) = (term609 A B H).
Proof. exact (TRANS (@lem348493 A B H) (@lem348523 A B H)). Qed.
Lemma lem348525 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term519 A B lt2 H) = (term519 A B lt2 H).
Proof. exact (eq_refl (term519 A B lt2 H)). Qed.
Lemma lem348526 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term521 A B lt2 H) = (term610 A B lt2 H).
Proof. exact (MK_COMB (@lem348525 A B lt2 H) (@lem348524 A B H)). Qed.
Lemma lem348530 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem348531 {A B : Type'} (P : type572 A B) (Q : Prop) : (term611 A B P Q) = (term612 A B P Q).
Proof. exact (@lem348530 (A -> B) P Q). Qed.
Lemma lem348532 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term613 A B lt2 H) = (term614 A B lt2 H).
Proof. exact (@lem348531 A B (term503 A B lt2 H) (term609 A B H)). Qed.
Lemma lem348533 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term615 A B lt2 H f) = (term497 A B lt2 f H).
Proof. exact (eq_refl (term615 A B lt2 H f)). Qed.
Lemma lem348534 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term616 A B lt2 H) = (term503 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem348533 A B lt2 f H)). Qed.
Lemma lem348535 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348536 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term617 A B lt2 H) = (term504 A B lt2 H).
Proof. exact (MK_COMB (@lem348535 A B) (@lem348534 A B lt2 H)). Qed.
Lemma lem348537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348538 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term618 A B lt2 H) = (term519 A B lt2 H).
Proof. exact (MK_COMB (@lem348537) (@lem348536 A B lt2 H)). Qed.
Lemma lem348539 {A B : Type'} (H : type549 A B) : (term609 A B H) = (term609 A B H).
Proof. exact (eq_refl (term609 A B H)). Qed.
Lemma lem348540 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term613 A B lt2 H) = (term610 A B lt2 H).
Proof. exact (MK_COMB (@lem348538 A B lt2 H) (@lem348539 A B H)). Qed.
Lemma lem348541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348542 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term619 A B lt2 H) = (term620 A B lt2 H).
Proof. exact (MK_COMB (@lem348541) (@lem348540 A B lt2 H)). Qed.
Lemma lem348543 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term615 A B lt2 H f) = (term497 A B lt2 f H).
Proof. exact (eq_refl (term615 A B lt2 H f)). Qed.
Lemma lem348544 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348545 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term621 A B lt2 H f) = (term622 A B lt2 f H).
Proof. exact (MK_COMB (@lem348544) (@lem348543 A B lt2 f H)). Qed.
Lemma lem348546 {A B : Type'} (H : type549 A B) : (term609 A B H) = (term609 A B H).
Proof. exact (eq_refl (term609 A B H)). Qed.
Lemma lem348547 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term623 A B lt2 f H) = (term624 A B lt2 f H).
Proof. exact (MK_COMB (@lem348545 A B lt2 f H) (@lem348546 A B H)). Qed.
Lemma lem348548 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term625 A B lt2 H) = (term626 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem348547 A B lt2 f H)). Qed.
Lemma lem348549 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348550 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term614 A B lt2 H) = (term627 A B lt2 H).
Proof. exact (MK_COMB (@lem348549 A B) (@lem348548 A B lt2 H)). Qed.
Lemma lem348551 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : ((term613 A B lt2 H) = (term614 A B lt2 H)) = ((term610 A B lt2 H) = (term627 A B lt2 H)).
Proof. exact (MK_COMB (@lem348542 A B lt2 H) (@lem348550 A B lt2 H)). Qed.
Lemma lem348552 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term610 A B lt2 H) = (term627 A B lt2 H).
Proof. exact (EQ_MP (@lem348551 A B lt2 H) (@lem348532 A B lt2 H)). Qed.
Lemma lem348556 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem348557 {A B : Type'} (P : type572 A B) (Q : Prop) : (term611 A B P Q) = (term612 A B P Q).
Proof. exact (@lem348556 (A -> B) P Q). Qed.
Lemma lem348558 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term628 A B lt2 f H) = (term629 A B lt2 f H).
Proof. exact (@lem348557 A B (term496 A B lt2 f H) (term609 A B H)). Qed.
Lemma lem348559 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term630 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (eq_refl (term630 A B lt2 f H g)). Qed.
Lemma lem348560 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term631 A B lt2 f H) = (term496 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem348559 A B lt2 f H g)). Qed.
Lemma lem348561 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348562 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term632 A B lt2 f H) = (term497 A B lt2 f H).
Proof. exact (MK_COMB (@lem348561 A B) (@lem348560 A B lt2 f H)). Qed.
Lemma lem348563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348564 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term633 A B lt2 f H) = (term622 A B lt2 f H).
Proof. exact (MK_COMB (@lem348563) (@lem348562 A B lt2 f H)). Qed.
Lemma lem348565 {A B : Type'} (H : type549 A B) : (term609 A B H) = (term609 A B H).
Proof. exact (eq_refl (term609 A B H)). Qed.
Lemma lem348566 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term628 A B lt2 f H) = (term624 A B lt2 f H).
Proof. exact (MK_COMB (@lem348564 A B lt2 f H) (@lem348565 A B H)). Qed.
Lemma lem348567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348568 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term634 A B lt2 f H) = (term635 A B lt2 f H).
Proof. exact (MK_COMB (@lem348567) (@lem348566 A B lt2 f H)). Qed.
Lemma lem348569 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term630 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (eq_refl (term630 A B lt2 f H g)). Qed.
Lemma lem348570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348571 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term636 A B lt2 f H g) = (term637 A B lt2 f H g).
Proof. exact (MK_COMB (@lem348570) (@lem348569 A B lt2 f H g)). Qed.
Lemma lem348572 {A B : Type'} (H : type549 A B) : (term609 A B H) = (term609 A B H).
Proof. exact (eq_refl (term609 A B H)). Qed.
Lemma lem348573 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term638 A B lt2 f g H) = (term639 A B lt2 f g H).
Proof. exact (MK_COMB (@lem348571 A B lt2 f H g) (@lem348572 A B H)). Qed.
Lemma lem348574 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term640 A B lt2 f H) = (term641 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem348573 A B lt2 f g H)). Qed.
Lemma lem348575 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348576 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term629 A B lt2 f H) = (term642 A B lt2 f H).
Proof. exact (MK_COMB (@lem348575 A B) (@lem348574 A B lt2 f H)). Qed.
Lemma lem348577 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : ((term628 A B lt2 f H) = (term629 A B lt2 f H)) = ((term624 A B lt2 f H) = (term642 A B lt2 f H)).
Proof. exact (MK_COMB (@lem348568 A B lt2 f H) (@lem348576 A B lt2 f H)). Qed.
Lemma lem348578 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term624 A B lt2 f H) = (term642 A B lt2 f H).
Proof. exact (EQ_MP (@lem348577 A B lt2 f H) (@lem348558 A B lt2 f H)). Qed.
Lemma lem348582 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem348583 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (@lem348582 A P Q). Qed.
Lemma lem348584 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term643 A B lt2 f g H) = (term644 A B lt2 f g H).
Proof. exact (@lem348583 A (term487 A B lt2 f H g) (term609 A B H)). Qed.
Lemma lem348585 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term645 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (eq_refl (term645 A B lt2 f H g x)). Qed.
Lemma lem348586 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term646 A B lt2 f H g) = (term487 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem348585 A B lt2 f H g x)). Qed.
Lemma lem348587 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348588 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term647 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (MK_COMB (@lem348587 A) (@lem348586 A B lt2 f H g)). Qed.
Lemma lem348589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348590 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term648 A B lt2 f H g) = (term637 A B lt2 f H g).
Proof. exact (MK_COMB (@lem348589) (@lem348588 A B lt2 f H g)). Qed.
Lemma lem348591 {A B : Type'} (H : type549 A B) : (term609 A B H) = (term609 A B H).
Proof. exact (eq_refl (term609 A B H)). Qed.
Lemma lem348592 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term643 A B lt2 f g H) = (term639 A B lt2 f g H).
Proof. exact (MK_COMB (@lem348590 A B lt2 f H g) (@lem348591 A B H)). Qed.
Lemma lem348593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348594 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term649 A B lt2 f g H) = (term650 A B lt2 f g H).
Proof. exact (MK_COMB (@lem348593) (@lem348592 A B lt2 f g H)). Qed.
Lemma lem348595 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term645 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (eq_refl (term645 A B lt2 f H g x)). Qed.
Lemma lem348596 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem348597 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term651 A B lt2 f H g x) = (term652 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem348596) (@lem348595 A B lt2 f H g x)). Qed.
Lemma lem348598 {A B : Type'} (H : type549 A B) : (term609 A B H) = (term609 A B H).
Proof. exact (eq_refl (term609 A B H)). Qed.
Lemma lem348599 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) (H : type549 A B) : (term653 A B lt2 f g x H) = (term654 A B lt2 f g x H).
Proof. exact (MK_COMB (@lem348597 A B lt2 f H g x) (@lem348598 A B H)). Qed.
Lemma lem348600 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term655 A B lt2 f g H) = (term656 A B lt2 f g H).
Proof. exact (fun_ext (fun x : A => @lem348599 A B lt2 f g x H)). Qed.
Lemma lem348601 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348602 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term644 A B lt2 f g H) = (term657 A B lt2 f g H).
Proof. exact (MK_COMB (@lem348601 A) (@lem348600 A B lt2 f g H)). Qed.
Lemma lem348603 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : ((term643 A B lt2 f g H) = (term644 A B lt2 f g H)) = ((term639 A B lt2 f g H) = (term657 A B lt2 f g H)).
Proof. exact (MK_COMB (@lem348594 A B lt2 f g H) (@lem348602 A B lt2 f g H)). Qed.
Lemma lem348604 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term639 A B lt2 f g H) = (term657 A B lt2 f g H).
Proof. exact (EQ_MP (@lem348603 A B lt2 f g H) (@lem348584 A B lt2 f g H)). Qed.
Lemma lem348606 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem348607 {A B : Type'} (P : Prop) (Q : type98 A B) : (term658 A B P Q) = (term659 A B P Q).
Proof. exact (@lem348606 (type522 A B) P Q). Qed.
Lemma lem348608 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) (H : type549 A B) : (term660 A B lt2 f g x H) = (term661 A B lt2 f g x H).
Proof. exact (@lem348607 A B (term480 A B lt2 f H g x) (term608 A B H)). Qed.
Lemma lem348609 {A B : Type'} (H : type549 A B) (x : type522 A B) : (term662 A B H x) = (term606 A B H x).
Proof. exact (eq_refl (term662 A B H x)). Qed.
Lemma lem348610 {A B : Type'} (H : type549 A B) : (term663 A B H) = (term608 A B H).
Proof. exact (fun_ext (fun x : type522 A B => @lem348609 A B H x)). Qed.
Lemma lem348611 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A)) = (@ex ((A -> B) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A))). Qed.
Lemma lem348612 {A B : Type'} (H : type549 A B) : (term664 A B H) = (term609 A B H).
Proof. exact (MK_COMB (@lem348611 A B) (@lem348610 A B H)). Qed.
Lemma lem348613 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term652 A B lt2 f H g x) = (term652 A B lt2 f H g x).
Proof. exact (eq_refl (term652 A B lt2 f H g x)). Qed.
Lemma lem348614 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) (H : type549 A B) : (term660 A B lt2 f g x H) = (term654 A B lt2 f g x H).
Proof. exact (MK_COMB (@lem348613 A B lt2 f H g x) (@lem348612 A B H)). Qed.
Lemma lem348615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348616 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) (H : type549 A B) : (term665 A B lt2 f g x H) = (term666 A B lt2 f g x H).
Proof. exact (MK_COMB (@lem348615) (@lem348614 A B lt2 f g x H)). Qed.
Lemma lem348617 {A B : Type'} (H : type549 A B) (x : type522 A B) : (term662 A B H x) = (term606 A B H x).
Proof. exact (eq_refl (term662 A B H x)). Qed.
Lemma lem348618 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term652 A B lt2 f H g x) = (term652 A B lt2 f H g x).
Proof. exact (eq_refl (term652 A B lt2 f H g x)). Qed.
Lemma lem348619 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) (H : type549 A B) (x' : type522 A B) : (term667 A B lt2 f g x H x') = (term668 A B lt2 f g x H x').
Proof. exact (MK_COMB (@lem348618 A B lt2 f H g x) (@lem348617 A B H x')). Qed.
Lemma lem348620 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) (H : type549 A B) : (term669 A B lt2 f g x H) = (term670 A B lt2 f g x H).
Proof. exact (fun_ext (fun x' : type522 A B => @lem348619 A B lt2 f g x H x')). Qed.
Lemma lem348621 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A)) = (@ex ((A -> B) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A))). Qed.
Lemma lem348622 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) (H : type549 A B) : (term661 A B lt2 f g x H) = (term671 A B lt2 f g x H).
Proof. exact (MK_COMB (@lem348621 A B) (@lem348620 A B lt2 f g x H)). Qed.
Lemma lem348623 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) (H : type549 A B) : ((term660 A B lt2 f g x H) = (term661 A B lt2 f g x H)) = ((term654 A B lt2 f g x H) = (term671 A B lt2 f g x H)).
Proof. exact (MK_COMB (@lem348616 A B lt2 f g x H) (@lem348622 A B lt2 f g x H)). Qed.
Lemma lem348624 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) (H : type549 A B) : (term654 A B lt2 f g x H) = (term671 A B lt2 f g x H).
Proof. exact (EQ_MP (@lem348623 A B lt2 f g x H) (@lem348608 A B lt2 f g x H)). Qed.
Lemma lem348625 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term656 A B lt2 f g H) = (term672 A B lt2 f g H).
Proof. exact (fun_ext (fun x : A => @lem348624 A B lt2 f g x H)). Qed.
Lemma lem348626 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348627 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term657 A B lt2 f g H) = (term673 A B lt2 f g H).
Proof. exact (MK_COMB (@lem348626 A) (@lem348625 A B lt2 f g H)). Qed.
Lemma lem348628 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (H : type549 A B) : (term639 A B lt2 f g H) = (term673 A B lt2 f g H).
Proof. exact (TRANS (@lem348604 A B lt2 f g H) (@lem348627 A B lt2 f g H)). Qed.
Lemma lem348629 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term641 A B lt2 f H) = (term674 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem348628 A B lt2 f g H)). Qed.
Lemma lem348630 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348631 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term642 A B lt2 f H) = (term675 A B lt2 f H).
Proof. exact (MK_COMB (@lem348630 A B) (@lem348629 A B lt2 f H)). Qed.
Lemma lem348632 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term624 A B lt2 f H) = (term675 A B lt2 f H).
Proof. exact (TRANS (@lem348578 A B lt2 f H) (@lem348631 A B lt2 f H)). Qed.
Lemma lem348633 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term626 A B lt2 H) = (term676 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem348632 A B lt2 f H)). Qed.
Lemma lem348634 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348635 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term627 A B lt2 H) = (term677 A B lt2 H).
Proof. exact (MK_COMB (@lem348634 A B) (@lem348633 A B lt2 H)). Qed.
Lemma lem348636 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term610 A B lt2 H) = (term677 A B lt2 H).
Proof. exact (TRANS (@lem348552 A B lt2 H) (@lem348635 A B lt2 H)). Qed.
Lemma lem348637 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term521 A B lt2 H) = (term677 A B lt2 H).
Proof. exact (TRANS (@lem348526 A B lt2 H) (@lem348636 A B lt2 H)). Qed.
Lemma lem348638 {A B : Type'} (lt2 : type1402 A) : (term522 A B lt2) = (term678 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem348637 A B lt2 H)). Qed.
Lemma lem348639 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348640 {A B : Type'} (lt2 : type1402 A) : (term523 A B lt2) = (term679 A B lt2).
Proof. exact (MK_COMB (@lem348639 A B) (@lem348638 A B lt2)). Qed.
Lemma lem348642 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348643 {A B : Type'} (P : type107 A B) : (term680 A B P) = (term681 A B P).
Proof. exact (@lem348642 (type549 A B) (A -> B) P). Qed.
Lemma lem348644 {A B : Type'} (lt2 : type1402 A) : (term682 A B lt2) = (term683 A B lt2).
Proof. exact (@lem348643 A B (term684 A B lt2)). Qed.
Lemma lem348645 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term685 A B lt2 H) = (term676 A B lt2 H).
Proof. exact (eq_refl (term685 A B lt2 H)). Qed.
Lemma lem348646 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem348647 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term686 A B lt2 H f) = (term687 A B lt2 H f).
Proof. exact (MK_COMB (@lem348645 A B lt2 H) (@lem348646 A B f)). Qed.
Lemma lem348648 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term687 A B lt2 H f) = (term675 A B lt2 f H).
Proof. exact (eq_refl (term687 A B lt2 H f)). Qed.
Lemma lem348649 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term686 A B lt2 H f) = (term675 A B lt2 f H).
Proof. exact (TRANS (@lem348647 A B lt2 H f) (@lem348648 A B lt2 f H)). Qed.
Lemma lem348650 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term688 A B lt2 H) = (term676 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem348649 A B lt2 f H)). Qed.
Lemma lem348651 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348652 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term689 A B lt2 H) = (term677 A B lt2 H).
Proof. exact (MK_COMB (@lem348651 A B) (@lem348650 A B lt2 H)). Qed.
Lemma lem348653 {A B : Type'} (lt2 : type1402 A) : (term690 A B lt2) = (term678 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem348652 A B lt2 H)). Qed.
Lemma lem348654 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348655 {A B : Type'} (lt2 : type1402 A) : (term682 A B lt2) = (term679 A B lt2).
Proof. exact (MK_COMB (@lem348654 A B) (@lem348653 A B lt2)). Qed.
Lemma lem348656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348657 {A B : Type'} (lt2 : type1402 A) : (term691 A B lt2) = (term692 A B lt2).
Proof. exact (MK_COMB (@lem348656) (@lem348655 A B lt2)). Qed.
Lemma lem348658 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term685 A B lt2 H) = (term676 A B lt2 H).
Proof. exact (eq_refl (term685 A B lt2 H)). Qed.
Lemma lem348659 {A B : Type'} (f : type108 A B) (H : type549 A B) : (f H) = (f H).
Proof. exact (eq_refl (f H)). Qed.
Lemma lem348660 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term693 A B lt2 f H) = (term694 A B lt2 f H).
Proof. exact (MK_COMB (@lem348658 A B lt2 H) (@lem348659 A B f H)). Qed.
Lemma lem348661 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term694 A B lt2 f H) = (term695 A B lt2 f H).
Proof. exact (eq_refl (term694 A B lt2 f H)). Qed.
Lemma lem348662 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term693 A B lt2 f H) = (term695 A B lt2 f H).
Proof. exact (TRANS (@lem348660 A B lt2 f H) (@lem348661 A B lt2 f H)). Qed.
Lemma lem348663 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term696 A B lt2 f) = (term697 A B lt2 f).
Proof. exact (fun_ext (fun H : type549 A B => @lem348662 A B lt2 f H)). Qed.
Lemma lem348664 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348665 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term698 A B lt2 f) = (term699 A B lt2 f).
Proof. exact (MK_COMB (@lem348664 A B) (@lem348663 A B lt2 f)). Qed.
Lemma lem348666 {A B : Type'} (lt2 : type1402 A) : (term700 A B lt2) = (term701 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem348665 A B lt2 f)). Qed.
Lemma lem348667 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348668 {A B : Type'} (lt2 : type1402 A) : (term683 A B lt2) = (term702 A B lt2).
Proof. exact (MK_COMB (@lem348667 A B) (@lem348666 A B lt2)). Qed.
Lemma lem348669 {A B : Type'} (lt2 : type1402 A) : ((term682 A B lt2) = (term683 A B lt2)) = ((term679 A B lt2) = (term702 A B lt2)).
Proof. exact (MK_COMB (@lem348657 A B lt2) (@lem348668 A B lt2)). Qed.
Lemma lem348670 {A B : Type'} (lt2 : type1402 A) : (term679 A B lt2) = (term702 A B lt2).
Proof. exact (EQ_MP (@lem348669 A B lt2) (@lem348644 A B lt2)). Qed.
Lemma lem348672 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348673 {A B : Type'} (P : type107 A B) : (term680 A B P) = (term681 A B P).
Proof. exact (@lem348672 (type549 A B) (A -> B) P). Qed.
Lemma lem348674 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term703 A B lt2 f) = (term704 A B lt2 f).
Proof. exact (@lem348673 A B (term705 A B lt2 f)). Qed.
Lemma lem348675 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term706 A B lt2 f H) = (term707 A B lt2 f H).
Proof. exact (eq_refl (term706 A B lt2 f H)). Qed.
Lemma lem348676 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem348677 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) (g : A -> B) : (term708 A B lt2 f H g) = (term709 A B lt2 f H g).
Proof. exact (MK_COMB (@lem348675 A B lt2 f H) (@lem348676 A B g)). Qed.
Lemma lem348678 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : A -> B) (H : type549 A B) : (term709 A B lt2 f H g) = (term710 A B lt2 f g H).
Proof. exact (eq_refl (term709 A B lt2 f H g)). Qed.
Lemma lem348679 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : A -> B) (H : type549 A B) : (term708 A B lt2 f H g) = (term710 A B lt2 f g H).
Proof. exact (TRANS (@lem348677 A B lt2 f H g) (@lem348678 A B lt2 f g H)). Qed.
Lemma lem348680 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term711 A B lt2 f H) = (term707 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem348679 A B lt2 f g H)). Qed.
Lemma lem348681 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem348682 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term712 A B lt2 f H) = (term695 A B lt2 f H).
Proof. exact (MK_COMB (@lem348681 A B) (@lem348680 A B lt2 f H)). Qed.
Lemma lem348683 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term713 A B lt2 f) = (term697 A B lt2 f).
Proof. exact (fun_ext (fun H : type549 A B => @lem348682 A B lt2 f H)). Qed.
Lemma lem348684 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348685 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term703 A B lt2 f) = (term699 A B lt2 f).
Proof. exact (MK_COMB (@lem348684 A B) (@lem348683 A B lt2 f)). Qed.
Lemma lem348686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348687 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term714 A B lt2 f) = (term715 A B lt2 f).
Proof. exact (MK_COMB (@lem348686) (@lem348685 A B lt2 f)). Qed.
Lemma lem348688 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term706 A B lt2 f H) = (term707 A B lt2 f H).
Proof. exact (eq_refl (term706 A B lt2 f H)). Qed.
Lemma lem348689 {A B : Type'} (g : type108 A B) (H : type549 A B) : (g H) = (g H).
Proof. exact (eq_refl (g H)). Qed.
Lemma lem348690 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (H : type549 A B) : (term716 A B lt2 f g H) = (term717 A B lt2 f g H).
Proof. exact (MK_COMB (@lem348688 A B lt2 f H) (@lem348689 A B g H)). Qed.
Lemma lem348691 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (H : type549 A B) : (term717 A B lt2 f g H) = (term718 A B lt2 f g H).
Proof. exact (eq_refl (term717 A B lt2 f g H)). Qed.
Lemma lem348692 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (H : type549 A B) : (term716 A B lt2 f g H) = (term718 A B lt2 f g H).
Proof. exact (TRANS (@lem348690 A B lt2 f g H) (@lem348691 A B lt2 f g H)). Qed.
Lemma lem348693 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term719 A B lt2 f g) = (term720 A B lt2 f g).
Proof. exact (fun_ext (fun H : type549 A B => @lem348692 A B lt2 f g H)). Qed.
Lemma lem348694 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348695 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term721 A B lt2 f g) = (term722 A B lt2 f g).
Proof. exact (MK_COMB (@lem348694 A B) (@lem348693 A B lt2 f g)). Qed.
Lemma lem348696 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term723 A B lt2 f) = (term724 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem348695 A B lt2 f g)). Qed.
Lemma lem348697 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348698 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term704 A B lt2 f) = (term725 A B lt2 f).
Proof. exact (MK_COMB (@lem348697 A B) (@lem348696 A B lt2 f)). Qed.
Lemma lem348699 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : ((term703 A B lt2 f) = (term704 A B lt2 f)) = ((term699 A B lt2 f) = (term725 A B lt2 f)).
Proof. exact (MK_COMB (@lem348687 A B lt2 f) (@lem348698 A B lt2 f)). Qed.
Lemma lem348700 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term699 A B lt2 f) = (term725 A B lt2 f).
Proof. exact (EQ_MP (@lem348699 A B lt2 f) (@lem348674 A B lt2 f)). Qed.
Lemma lem348702 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348703 {A B : Type'} (P : type109 A B) : (term726 A B P) = (term727 A B P).
Proof. exact (@lem348702 (type549 A B) A P). Qed.
Lemma lem348704 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term728 A B lt2 f g) = (term729 A B lt2 f g).
Proof. exact (@lem348703 A B (term730 A B lt2 f g)). Qed.
Lemma lem348705 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (H : type549 A B) : (term731 A B lt2 f g H) = (term732 A B lt2 f g H).
Proof. exact (eq_refl (term731 A B lt2 f g H)). Qed.
Lemma lem348706 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem348707 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (H : type549 A B) (x : A) : (term733 A B lt2 f g H x) = (term734 A B lt2 f g H x).
Proof. exact (MK_COMB (@lem348705 A B lt2 f g H) (@lem348706 A x)). Qed.
Lemma lem348708 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : A) (H : type549 A B) : (term734 A B lt2 f g H x) = (term735 A B lt2 f g x H).
Proof. exact (eq_refl (term734 A B lt2 f g H x)). Qed.
Lemma lem348709 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : A) (H : type549 A B) : (term733 A B lt2 f g H x) = (term735 A B lt2 f g x H).
Proof. exact (TRANS (@lem348707 A B lt2 f g H x) (@lem348708 A B lt2 f g x H)). Qed.
Lemma lem348710 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (H : type549 A B) : (term736 A B lt2 f g H) = (term732 A B lt2 f g H).
Proof. exact (fun_ext (fun x : A => @lem348709 A B lt2 f g x H)). Qed.
Lemma lem348711 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem348712 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (H : type549 A B) : (term737 A B lt2 f g H) = (term718 A B lt2 f g H).
Proof. exact (MK_COMB (@lem348711 A) (@lem348710 A B lt2 f g H)). Qed.
Lemma lem348713 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term738 A B lt2 f g) = (term720 A B lt2 f g).
Proof. exact (fun_ext (fun H : type549 A B => @lem348712 A B lt2 f g H)). Qed.
Lemma lem348714 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348715 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term728 A B lt2 f g) = (term722 A B lt2 f g).
Proof. exact (MK_COMB (@lem348714 A B) (@lem348713 A B lt2 f g)). Qed.
Lemma lem348716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348717 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term739 A B lt2 f g) = (term740 A B lt2 f g).
Proof. exact (MK_COMB (@lem348716) (@lem348715 A B lt2 f g)). Qed.
Lemma lem348718 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (H : type549 A B) : (term731 A B lt2 f g H) = (term732 A B lt2 f g H).
Proof. exact (eq_refl (term731 A B lt2 f g H)). Qed.
Lemma lem348719 {A B : Type'} (x : type110 A B) (H : type549 A B) : (x H) = (x H).
Proof. exact (eq_refl (x H)). Qed.
Lemma lem348720 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) : (term741 A B lt2 f g x H) = (term742 A B lt2 f g x H).
Proof. exact (MK_COMB (@lem348718 A B lt2 f g H) (@lem348719 A B x H)). Qed.
Lemma lem348721 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) : (term742 A B lt2 f g x H) = (term743 A B lt2 f g x H).
Proof. exact (eq_refl (term742 A B lt2 f g x H)). Qed.
Lemma lem348722 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) : (term741 A B lt2 f g x H) = (term743 A B lt2 f g x H).
Proof. exact (TRANS (@lem348720 A B lt2 f g x H) (@lem348721 A B lt2 f g x H)). Qed.
Lemma lem348723 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term744 A B lt2 f g x) = (term745 A B lt2 f g x).
Proof. exact (fun_ext (fun H : type549 A B => @lem348722 A B lt2 f g x H)). Qed.
Lemma lem348724 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348725 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term746 A B lt2 f g x) = (term747 A B lt2 f g x).
Proof. exact (MK_COMB (@lem348724 A B) (@lem348723 A B lt2 f g x)). Qed.
Lemma lem348726 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term748 A B lt2 f g) = (term749 A B lt2 f g).
Proof. exact (fun_ext (fun x : type110 A B => @lem348725 A B lt2 f g x)). Qed.
Lemma lem348727 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem348728 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term729 A B lt2 f g) = (term750 A B lt2 f g).
Proof. exact (MK_COMB (@lem348727 A B) (@lem348726 A B lt2 f g)). Qed.
Lemma lem348729 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : ((term728 A B lt2 f g) = (term729 A B lt2 f g)) = ((term722 A B lt2 f g) = (term750 A B lt2 f g)).
Proof. exact (MK_COMB (@lem348717 A B lt2 f g) (@lem348728 A B lt2 f g)). Qed.
Lemma lem348730 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term722 A B lt2 f g) = (term750 A B lt2 f g).
Proof. exact (EQ_MP (@lem348729 A B lt2 f g) (@lem348704 A B lt2 f g)). Qed.
Lemma lem348732 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348733 {A B : Type'} (P : type105 A B) : (term751 A B P) = (term752 A B P).
Proof. exact (@lem348732 (type549 A B) (type522 A B) P). Qed.
Lemma lem348734 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term753 A B lt2 f g x) = (term754 A B lt2 f g x).
Proof. exact (@lem348733 A B (term755 A B lt2 f g x)). Qed.
Lemma lem348735 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) : (term756 A B lt2 f g x H) = (term757 A B lt2 f g x H).
Proof. exact (eq_refl (term756 A B lt2 f g x H)). Qed.
Lemma lem348736 {A B : Type'} (x : type522 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem348737 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) (x' : type522 A B) : (term758 A B lt2 f g x H x') = (term759 A B lt2 f g x H x').
Proof. exact (MK_COMB (@lem348735 A B lt2 f g x H) (@lem348736 A B x')). Qed.
Lemma lem348738 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) (x' : type522 A B) : (term759 A B lt2 f g x H x') = (term760 A B lt2 f g x H x').
Proof. exact (eq_refl (term759 A B lt2 f g x H x')). Qed.
Lemma lem348739 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) (x' : type522 A B) : (term758 A B lt2 f g x H x') = (term760 A B lt2 f g x H x').
Proof. exact (TRANS (@lem348737 A B lt2 f g x H x') (@lem348738 A B lt2 f g x H x')). Qed.
Lemma lem348740 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) : (term761 A B lt2 f g x H) = (term757 A B lt2 f g x H).
Proof. exact (fun_ext (fun x' : type522 A B => @lem348739 A B lt2 f g x H x')). Qed.
Lemma lem348741 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A)) = (@ex ((A -> B) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A))). Qed.
Lemma lem348742 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) : (term762 A B lt2 f g x H) = (term743 A B lt2 f g x H).
Proof. exact (MK_COMB (@lem348741 A B) (@lem348740 A B lt2 f g x H)). Qed.
Lemma lem348743 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term763 A B lt2 f g x) = (term745 A B lt2 f g x).
Proof. exact (fun_ext (fun H : type549 A B => @lem348742 A B lt2 f g x H)). Qed.
Lemma lem348744 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348745 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term753 A B lt2 f g x) = (term747 A B lt2 f g x).
Proof. exact (MK_COMB (@lem348744 A B) (@lem348743 A B lt2 f g x)). Qed.
Lemma lem348746 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348747 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term764 A B lt2 f g x) = (term765 A B lt2 f g x).
Proof. exact (MK_COMB (@lem348746) (@lem348745 A B lt2 f g x)). Qed.
Lemma lem348748 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (H : type549 A B) : (term756 A B lt2 f g x H) = (term757 A B lt2 f g x H).
Proof. exact (eq_refl (term756 A B lt2 f g x H)). Qed.
Lemma lem348749 {A B : Type'} (x : type106 A B) (H : type549 A B) : (x H) = (x H).
Proof. exact (eq_refl (x H)). Qed.
Lemma lem348750 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (x' : type106 A B) (H : type549 A B) : (term766 A B lt2 f g x x' H) = (term767 A B lt2 f g x x' H).
Proof. exact (MK_COMB (@lem348748 A B lt2 f g x H) (@lem348749 A B x' H)). Qed.
Lemma lem348751 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (x' : type106 A B) (H : type549 A B) : (term767 A B lt2 f g x x' H) = (term768 A B lt2 f g x x' H).
Proof. exact (eq_refl (term767 A B lt2 f g x x' H)). Qed.
Lemma lem348752 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (x' : type106 A B) (H : type549 A B) : (term766 A B lt2 f g x x' H) = (term768 A B lt2 f g x x' H).
Proof. exact (TRANS (@lem348750 A B lt2 f g x x' H) (@lem348751 A B lt2 f g x x' H)). Qed.
Lemma lem348753 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (x' : type106 A B) : (term769 A B lt2 f g x x') = (term770 A B lt2 f g x x').
Proof. exact (fun_ext (fun H : type549 A B => @lem348752 A B lt2 f g x x' H)). Qed.
Lemma lem348754 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem348755 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (x' : type106 A B) : (term771 A B lt2 f g x x') = (term772 A B lt2 f g x x').
Proof. exact (MK_COMB (@lem348754 A B) (@lem348753 A B lt2 f g x x')). Qed.
Lemma lem348756 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term773 A B lt2 f g x) = (term774 A B lt2 f g x).
Proof. exact (fun_ext (fun x' : type106 A B => @lem348755 A B lt2 f g x x')). Qed.
Lemma lem348757 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A))). Qed.
Lemma lem348758 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term754 A B lt2 f g x) = (term775 A B lt2 f g x).
Proof. exact (MK_COMB (@lem348757 A B) (@lem348756 A B lt2 f g x)). Qed.
Lemma lem348759 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : ((term753 A B lt2 f g x) = (term754 A B lt2 f g x)) = ((term747 A B lt2 f g x) = (term775 A B lt2 f g x)).
Proof. exact (MK_COMB (@lem348747 A B lt2 f g x) (@lem348758 A B lt2 f g x)). Qed.
Lemma lem348760 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term747 A B lt2 f g x) = (term775 A B lt2 f g x).
Proof. exact (EQ_MP (@lem348759 A B lt2 f g x) (@lem348734 A B lt2 f g x)). Qed.
Lemma lem348761 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term749 A B lt2 f g) = (term776 A B lt2 f g).
Proof. exact (fun_ext (fun x : type110 A B => @lem348760 A B lt2 f g x)). Qed.
Lemma lem348762 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem348763 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term750 A B lt2 f g) = (term777 A B lt2 f g).
Proof. exact (MK_COMB (@lem348762 A B) (@lem348761 A B lt2 f g)). Qed.
Lemma lem348764 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term722 A B lt2 f g) = (term777 A B lt2 f g).
Proof. exact (TRANS (@lem348730 A B lt2 f g) (@lem348763 A B lt2 f g)). Qed.
Lemma lem348765 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term724 A B lt2 f) = (term778 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem348764 A B lt2 f g)). Qed.
Lemma lem348766 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348767 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term725 A B lt2 f) = (term779 A B lt2 f).
Proof. exact (MK_COMB (@lem348766 A B) (@lem348765 A B lt2 f)). Qed.
Lemma lem348768 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term699 A B lt2 f) = (term779 A B lt2 f).
Proof. exact (TRANS (@lem348700 A B lt2 f) (@lem348767 A B lt2 f)). Qed.
Lemma lem348769 {A B : Type'} (lt2 : type1402 A) : (term701 A B lt2) = (term780 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem348768 A B lt2 f)). Qed.
Lemma lem348770 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348771 {A B : Type'} (lt2 : type1402 A) : (term702 A B lt2) = (term781 A B lt2).
Proof. exact (MK_COMB (@lem348770 A B) (@lem348769 A B lt2)). Qed.
Lemma lem348772 {A B : Type'} (lt2 : type1402 A) : (term679 A B lt2) = (term781 A B lt2).
Proof. exact (TRANS (@lem348670 A B lt2) (@lem348771 A B lt2)). Qed.
Lemma lem348773 {A B : Type'} (lt2 : type1402 A) : (term523 A B lt2) = (term781 A B lt2).
Proof. exact (TRANS (@lem348640 A B lt2) (@lem348772 A B lt2)). Qed.
Lemma lem348774 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348775 {A B : Type'} (lt2 : type1402 A) : (term526 A B lt2) = (term782 A B lt2).
Proof. exact (MK_COMB (@lem348774 A lt2) (@lem348773 A B lt2)). Qed.
Lemma lem348777 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem348778 {A B : Type'} (P : Prop) (Q : type66 A B) : (term783 A B P Q) = (term784 A B P Q).
Proof. exact (@lem348777 (type108 A B) P Q). Qed.
Lemma lem348779 {A B : Type'} (lt2 : type1402 A) : (term785 A B lt2) = (term786 A B lt2).
Proof. exact (@lem348778 A B (term787 A lt2) (term780 A B lt2)). Qed.
Lemma lem348780 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term788 A B lt2 f) = (term779 A B lt2 f).
Proof. exact (eq_refl (term788 A B lt2 f)). Qed.
Lemma lem348781 {A B : Type'} (lt2 : type1402 A) : (term789 A B lt2) = (term780 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem348780 A B lt2 f)). Qed.
Lemma lem348782 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348783 {A B : Type'} (lt2 : type1402 A) : (term790 A B lt2) = (term781 A B lt2).
Proof. exact (MK_COMB (@lem348782 A B) (@lem348781 A B lt2)). Qed.
Lemma lem348784 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348785 {A B : Type'} (lt2 : type1402 A) : (term785 A B lt2) = (term782 A B lt2).
Proof. exact (MK_COMB (@lem348784 A lt2) (@lem348783 A B lt2)). Qed.
Lemma lem348786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348787 {A B : Type'} (lt2 : type1402 A) : (term791 A B lt2) = (term792 A B lt2).
Proof. exact (MK_COMB (@lem348786) (@lem348785 A B lt2)). Qed.
Lemma lem348788 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term788 A B lt2 f) = (term779 A B lt2 f).
Proof. exact (eq_refl (term788 A B lt2 f)). Qed.
Lemma lem348789 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348790 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term793 A B lt2 f) = (term794 A B lt2 f).
Proof. exact (MK_COMB (@lem348789 A lt2) (@lem348788 A B lt2 f)). Qed.
Lemma lem348791 {A B : Type'} (lt2 : type1402 A) : (term795 A B lt2) = (term796 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem348790 A B lt2 f)). Qed.
Lemma lem348792 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348793 {A B : Type'} (lt2 : type1402 A) : (term786 A B lt2) = (term797 A B lt2).
Proof. exact (MK_COMB (@lem348792 A B) (@lem348791 A B lt2)). Qed.
Lemma lem348794 {A B : Type'} (lt2 : type1402 A) : ((term785 A B lt2) = (term786 A B lt2)) = ((term782 A B lt2) = (term797 A B lt2)).
Proof. exact (MK_COMB (@lem348787 A B lt2) (@lem348793 A B lt2)). Qed.
Lemma lem348795 {A B : Type'} (lt2 : type1402 A) : (term782 A B lt2) = (term797 A B lt2).
Proof. exact (EQ_MP (@lem348794 A B lt2) (@lem348779 A B lt2)). Qed.
Lemma lem348797 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem348798 {A B : Type'} (P : Prop) (Q : type66 A B) : (term783 A B P Q) = (term784 A B P Q).
Proof. exact (@lem348797 (type108 A B) P Q). Qed.
Lemma lem348799 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term798 A B lt2 f) = (term799 A B lt2 f).
Proof. exact (@lem348798 A B (term787 A lt2) (term778 A B lt2 f)). Qed.
Lemma lem348800 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term800 A B lt2 f g) = (term777 A B lt2 f g).
Proof. exact (eq_refl (term800 A B lt2 f g)). Qed.
Lemma lem348801 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term801 A B lt2 f) = (term778 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem348800 A B lt2 f g)). Qed.
Lemma lem348802 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348803 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term802 A B lt2 f) = (term779 A B lt2 f).
Proof. exact (MK_COMB (@lem348802 A B) (@lem348801 A B lt2 f)). Qed.
Lemma lem348804 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348805 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term798 A B lt2 f) = (term794 A B lt2 f).
Proof. exact (MK_COMB (@lem348804 A lt2) (@lem348803 A B lt2 f)). Qed.
Lemma lem348806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348807 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term803 A B lt2 f) = (term804 A B lt2 f).
Proof. exact (MK_COMB (@lem348806) (@lem348805 A B lt2 f)). Qed.
Lemma lem348808 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term800 A B lt2 f g) = (term777 A B lt2 f g).
Proof. exact (eq_refl (term800 A B lt2 f g)). Qed.
Lemma lem348809 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348810 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term805 A B lt2 f g) = (term806 A B lt2 f g).
Proof. exact (MK_COMB (@lem348809 A lt2) (@lem348808 A B lt2 f g)). Qed.
Lemma lem348811 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term807 A B lt2 f) = (term808 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem348810 A B lt2 f g)). Qed.
Lemma lem348812 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348813 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term799 A B lt2 f) = (term809 A B lt2 f).
Proof. exact (MK_COMB (@lem348812 A B) (@lem348811 A B lt2 f)). Qed.
Lemma lem348814 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : ((term798 A B lt2 f) = (term799 A B lt2 f)) = ((term794 A B lt2 f) = (term809 A B lt2 f)).
Proof. exact (MK_COMB (@lem348807 A B lt2 f) (@lem348813 A B lt2 f)). Qed.
Lemma lem348815 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term794 A B lt2 f) = (term809 A B lt2 f).
Proof. exact (EQ_MP (@lem348814 A B lt2 f) (@lem348799 A B lt2 f)). Qed.
Lemma lem348817 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem348818 {A B : Type'} (P : Prop) (Q : type67 A B) : (term810 A B P Q) = (term811 A B P Q).
Proof. exact (@lem348817 (type110 A B) P Q). Qed.
Lemma lem348819 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term812 A B lt2 f g) = (term813 A B lt2 f g).
Proof. exact (@lem348818 A B (term787 A lt2) (term776 A B lt2 f g)). Qed.
Lemma lem348820 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term814 A B lt2 f g x) = (term775 A B lt2 f g x).
Proof. exact (eq_refl (term814 A B lt2 f g x)). Qed.
Lemma lem348821 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term815 A B lt2 f g) = (term776 A B lt2 f g).
Proof. exact (fun_ext (fun x : type110 A B => @lem348820 A B lt2 f g x)). Qed.
Lemma lem348822 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem348823 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term816 A B lt2 f g) = (term777 A B lt2 f g).
Proof. exact (MK_COMB (@lem348822 A B) (@lem348821 A B lt2 f g)). Qed.
Lemma lem348824 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348825 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term812 A B lt2 f g) = (term806 A B lt2 f g).
Proof. exact (MK_COMB (@lem348824 A lt2) (@lem348823 A B lt2 f g)). Qed.
Lemma lem348826 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348827 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term817 A B lt2 f g) = (term818 A B lt2 f g).
Proof. exact (MK_COMB (@lem348826) (@lem348825 A B lt2 f g)). Qed.
Lemma lem348828 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term814 A B lt2 f g x) = (term775 A B lt2 f g x).
Proof. exact (eq_refl (term814 A B lt2 f g x)). Qed.
Lemma lem348829 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348830 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term819 A B lt2 f g x) = (term820 A B lt2 f g x).
Proof. exact (MK_COMB (@lem348829 A lt2) (@lem348828 A B lt2 f g x)). Qed.
Lemma lem348831 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term821 A B lt2 f g) = (term822 A B lt2 f g).
Proof. exact (fun_ext (fun x : type110 A B => @lem348830 A B lt2 f g x)). Qed.
Lemma lem348832 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem348833 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term813 A B lt2 f g) = (term823 A B lt2 f g).
Proof. exact (MK_COMB (@lem348832 A B) (@lem348831 A B lt2 f g)). Qed.
Lemma lem348834 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : ((term812 A B lt2 f g) = (term813 A B lt2 f g)) = ((term806 A B lt2 f g) = (term823 A B lt2 f g)).
Proof. exact (MK_COMB (@lem348827 A B lt2 f g) (@lem348833 A B lt2 f g)). Qed.
Lemma lem348835 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term806 A B lt2 f g) = (term823 A B lt2 f g).
Proof. exact (EQ_MP (@lem348834 A B lt2 f g) (@lem348819 A B lt2 f g)). Qed.
Lemma lem348837 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem348838 {A B : Type'} (P : Prop) (Q : type65 A B) : (term824 A B P Q) = (term825 A B P Q).
Proof. exact (@lem348837 (type106 A B) P Q). Qed.
Lemma lem348839 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term826 A B lt2 f g x) = (term827 A B lt2 f g x).
Proof. exact (@lem348838 A B (term787 A lt2) (term774 A B lt2 f g x)). Qed.
Lemma lem348840 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (x' : type106 A B) : (term828 A B lt2 f g x x') = (term772 A B lt2 f g x x').
Proof. exact (eq_refl (term828 A B lt2 f g x x')). Qed.
Lemma lem348841 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term829 A B lt2 f g x) = (term774 A B lt2 f g x).
Proof. exact (fun_ext (fun x' : type106 A B => @lem348840 A B lt2 f g x x')). Qed.
Lemma lem348842 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A))). Qed.
Lemma lem348843 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term830 A B lt2 f g x) = (term775 A B lt2 f g x).
Proof. exact (MK_COMB (@lem348842 A B) (@lem348841 A B lt2 f g x)). Qed.
Lemma lem348844 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348845 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term826 A B lt2 f g x) = (term820 A B lt2 f g x).
Proof. exact (MK_COMB (@lem348844 A lt2) (@lem348843 A B lt2 f g x)). Qed.
Lemma lem348846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348847 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term831 A B lt2 f g x) = (term832 A B lt2 f g x).
Proof. exact (MK_COMB (@lem348846) (@lem348845 A B lt2 f g x)). Qed.
Lemma lem348848 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (x' : type106 A B) : (term828 A B lt2 f g x x') = (term772 A B lt2 f g x x').
Proof. exact (eq_refl (term828 A B lt2 f g x x')). Qed.
Lemma lem348849 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem348850 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) (x' : type106 A B) : (term833 A B lt2 f g x x') = (term834 A B lt2 f g x x').
Proof. exact (MK_COMB (@lem348849 A lt2) (@lem348848 A B lt2 f g x x')). Qed.
Lemma lem348851 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term835 A B lt2 f g x) = (term836 A B lt2 f g x).
Proof. exact (fun_ext (fun x' : type106 A B => @lem348850 A B lt2 f g x x')). Qed.
Lemma lem348852 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A))). Qed.
Lemma lem348853 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term827 A B lt2 f g x) = (term837 A B lt2 f g x).
Proof. exact (MK_COMB (@lem348852 A B) (@lem348851 A B lt2 f g x)). Qed.
Lemma lem348854 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : ((term826 A B lt2 f g x) = (term827 A B lt2 f g x)) = ((term820 A B lt2 f g x) = (term837 A B lt2 f g x)).
Proof. exact (MK_COMB (@lem348847 A B lt2 f g x) (@lem348853 A B lt2 f g x)). Qed.
Lemma lem348855 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (x : type110 A B) : (term820 A B lt2 f g x) = (term837 A B lt2 f g x).
Proof. exact (EQ_MP (@lem348854 A B lt2 f g x) (@lem348839 A B lt2 f g x)). Qed.
Lemma lem348856 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term822 A B lt2 f g) = (term838 A B lt2 f g).
Proof. exact (fun_ext (fun x : type110 A B => @lem348855 A B lt2 f g x)). Qed.
Lemma lem348857 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem348858 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term823 A B lt2 f g) = (term839 A B lt2 f g).
Proof. exact (MK_COMB (@lem348857 A B) (@lem348856 A B lt2 f g)). Qed.
Lemma lem348859 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) : (term806 A B lt2 f g) = (term839 A B lt2 f g).
Proof. exact (TRANS (@lem348835 A B lt2 f g) (@lem348858 A B lt2 f g)). Qed.
Lemma lem348860 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term808 A B lt2 f) = (term840 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem348859 A B lt2 f g)). Qed.
Lemma lem348861 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348862 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term809 A B lt2 f) = (term841 A B lt2 f).
Proof. exact (MK_COMB (@lem348861 A B) (@lem348860 A B lt2 f)). Qed.
Lemma lem348863 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term794 A B lt2 f) = (term841 A B lt2 f).
Proof. exact (TRANS (@lem348815 A B lt2 f) (@lem348862 A B lt2 f)). Qed.
Lemma lem348864 {A B : Type'} (lt2 : type1402 A) : (term796 A B lt2) = (term842 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem348863 A B lt2 f)). Qed.
Lemma lem348865 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348866 {A B : Type'} (lt2 : type1402 A) : (term797 A B lt2) = (term843 A B lt2).
Proof. exact (MK_COMB (@lem348865 A B) (@lem348864 A B lt2)). Qed.
Lemma lem348867 {A B : Type'} (lt2 : type1402 A) : (term782 A B lt2) = (term843 A B lt2).
Proof. exact (TRANS (@lem348795 A B lt2) (@lem348866 A B lt2)). Qed.
Lemma lem348868 {A B : Type'} (lt2 : type1402 A) : (term526 A B lt2) = (term843 A B lt2).
Proof. exact (TRANS (@lem348775 A B lt2) (@lem348867 A B lt2)). Qed.
Lemma lem348869 {A B : Type'} : (term527 A B) = (term844 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348868 A B lt2)). Qed.
Lemma lem348870 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348871 {A B : Type'} : (term528 A B) = (term845 A B).
Proof. exact (MK_COMB (@lem348870 A) (@lem348869 A B)). Qed.
Lemma lem348873 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348874 {A B : Type'} (P : type406 A B) : (term846 A B P) = (term847 A B P).
Proof. exact (@lem348873 (type1402 A) (type108 A B) P). Qed.
Lemma lem348875 {A B : Type'} : (term848 A B) = (term849 A B).
Proof. exact (@lem348874 A B (term850 A B)). Qed.
Lemma lem348876 {A B : Type'} (lt2 : type1402 A) : (term851 A B lt2) = (term842 A B lt2).
Proof. exact (eq_refl (term851 A B lt2)). Qed.
Lemma lem348877 {A B : Type'} (f : type108 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem348878 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term852 A B lt2 f) = (term853 A B lt2 f).
Proof. exact (MK_COMB (@lem348876 A B lt2) (@lem348877 A B f)). Qed.
Lemma lem348879 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term853 A B lt2 f) = (term841 A B lt2 f).
Proof. exact (eq_refl (term853 A B lt2 f)). Qed.
Lemma lem348880 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term852 A B lt2 f) = (term841 A B lt2 f).
Proof. exact (TRANS (@lem348878 A B lt2 f) (@lem348879 A B lt2 f)). Qed.
Lemma lem348881 {A B : Type'} (lt2 : type1402 A) : (term854 A B lt2) = (term842 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem348880 A B lt2 f)). Qed.
Lemma lem348882 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348883 {A B : Type'} (lt2 : type1402 A) : (term855 A B lt2) = (term843 A B lt2).
Proof. exact (MK_COMB (@lem348882 A B) (@lem348881 A B lt2)). Qed.
Lemma lem348884 {A B : Type'} : (term856 A B) = (term844 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348883 A B lt2)). Qed.
Lemma lem348885 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348886 {A B : Type'} : (term848 A B) = (term845 A B).
Proof. exact (MK_COMB (@lem348885 A) (@lem348884 A B)). Qed.
Lemma lem348887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348888 {A B : Type'} : (term857 A B) = (term858 A B).
Proof. exact (MK_COMB (@lem348887) (@lem348886 A B)). Qed.
Lemma lem348889 {A B : Type'} (lt2 : type1402 A) : (term851 A B lt2) = (term842 A B lt2).
Proof. exact (eq_refl (term851 A B lt2)). Qed.
Lemma lem348890 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (f lt2) = (f lt2).
Proof. exact (eq_refl (f lt2)). Qed.
Lemma lem348891 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term859 A B f lt2) = (term860 A B f lt2).
Proof. exact (MK_COMB (@lem348889 A B lt2) (@lem348890 A B f lt2)). Qed.
Lemma lem348892 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term860 A B f lt2) = (term861 A B f lt2).
Proof. exact (eq_refl (term860 A B f lt2)). Qed.
Lemma lem348893 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term859 A B f lt2) = (term861 A B f lt2).
Proof. exact (TRANS (@lem348891 A B f lt2) (@lem348892 A B f lt2)). Qed.
Lemma lem348894 {A B : Type'} (f : type409 A B) : (term862 A B f) = (term863 A B f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348893 A B f lt2)). Qed.
Lemma lem348895 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348896 {A B : Type'} (f : type409 A B) : (term864 A B f) = (term865 A B f).
Proof. exact (MK_COMB (@lem348895 A) (@lem348894 A B f)). Qed.
Lemma lem348897 {A B : Type'} : (term866 A B) = (term867 A B).
Proof. exact (fun_ext (fun f : type409 A B => @lem348896 A B f)). Qed.
Lemma lem348898 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348899 {A B : Type'} : (term849 A B) = (term868 A B).
Proof. exact (MK_COMB (@lem348898 A B) (@lem348897 A B)). Qed.
Lemma lem348900 {A B : Type'} : ((term848 A B) = (term849 A B)) = ((term845 A B) = (term868 A B)).
Proof. exact (MK_COMB (@lem348888 A B) (@lem348899 A B)). Qed.
Lemma lem348901 {A B : Type'} : (term845 A B) = (term868 A B).
Proof. exact (EQ_MP (@lem348900 A B) (@lem348875 A B)). Qed.
Lemma lem348903 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348904 {A B : Type'} (P : type406 A B) : (term846 A B P) = (term847 A B P).
Proof. exact (@lem348903 (type1402 A) (type108 A B) P). Qed.
Lemma lem348905 {A B : Type'} (f : type409 A B) : (term869 A B f) = (term870 A B f).
Proof. exact (@lem348904 A B (term871 A B f)). Qed.
Lemma lem348906 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term872 A B f lt2) = (term873 A B f lt2).
Proof. exact (eq_refl (term872 A B f lt2)). Qed.
Lemma lem348907 {A B : Type'} (g : type108 A B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem348908 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (g : type108 A B) : (term874 A B f lt2 g) = (term875 A B f lt2 g).
Proof. exact (MK_COMB (@lem348906 A B f lt2) (@lem348907 A B g)). Qed.
Lemma lem348909 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (g : type108 A B) : (term875 A B f lt2 g) = (term876 A B f lt2 g).
Proof. exact (eq_refl (term875 A B f lt2 g)). Qed.
Lemma lem348910 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (g : type108 A B) : (term874 A B f lt2 g) = (term876 A B f lt2 g).
Proof. exact (TRANS (@lem348908 A B f lt2 g) (@lem348909 A B f lt2 g)). Qed.
Lemma lem348911 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term877 A B f lt2) = (term873 A B f lt2).
Proof. exact (fun_ext (fun g : type108 A B => @lem348910 A B f lt2 g)). Qed.
Lemma lem348912 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348913 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term878 A B f lt2) = (term861 A B f lt2).
Proof. exact (MK_COMB (@lem348912 A B) (@lem348911 A B f lt2)). Qed.
Lemma lem348914 {A B : Type'} (f : type409 A B) : (term879 A B f) = (term863 A B f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348913 A B f lt2)). Qed.
Lemma lem348915 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348916 {A B : Type'} (f : type409 A B) : (term869 A B f) = (term865 A B f).
Proof. exact (MK_COMB (@lem348915 A) (@lem348914 A B f)). Qed.
Lemma lem348917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348918 {A B : Type'} (f : type409 A B) : (term880 A B f) = (term881 A B f).
Proof. exact (MK_COMB (@lem348917) (@lem348916 A B f)). Qed.
Lemma lem348919 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term872 A B f lt2) = (term873 A B f lt2).
Proof. exact (eq_refl (term872 A B f lt2)). Qed.
Lemma lem348920 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) : (g lt2) = (g lt2).
Proof. exact (eq_refl (g lt2)). Qed.
Lemma lem348921 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) : (term882 A B f g lt2) = (term883 A B f g lt2).
Proof. exact (MK_COMB (@lem348919 A B f lt2) (@lem348920 A B g lt2)). Qed.
Lemma lem348922 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) : (term883 A B f g lt2) = (term884 A B f g lt2).
Proof. exact (eq_refl (term883 A B f g lt2)). Qed.
Lemma lem348923 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) : (term882 A B f g lt2) = (term884 A B f g lt2).
Proof. exact (TRANS (@lem348921 A B f g lt2) (@lem348922 A B f g lt2)). Qed.
Lemma lem348924 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term885 A B f g) = (term886 A B f g).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348923 A B f g lt2)). Qed.
Lemma lem348925 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348926 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term887 A B f g) = (term888 A B f g).
Proof. exact (MK_COMB (@lem348925 A) (@lem348924 A B f g)). Qed.
Lemma lem348927 {A B : Type'} (f : type409 A B) : (term889 A B f) = (term890 A B f).
Proof. exact (fun_ext (fun g : type409 A B => @lem348926 A B f g)). Qed.
Lemma lem348928 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348929 {A B : Type'} (f : type409 A B) : (term870 A B f) = (term891 A B f).
Proof. exact (MK_COMB (@lem348928 A B) (@lem348927 A B f)). Qed.
Lemma lem348930 {A B : Type'} (f : type409 A B) : ((term869 A B f) = (term870 A B f)) = ((term865 A B f) = (term891 A B f)).
Proof. exact (MK_COMB (@lem348918 A B f) (@lem348929 A B f)). Qed.
Lemma lem348931 {A B : Type'} (f : type409 A B) : (term865 A B f) = (term891 A B f).
Proof. exact (EQ_MP (@lem348930 A B f) (@lem348905 A B f)). Qed.
Lemma lem348933 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348934 {A B : Type'} (P : type407 A B) : (term892 A B P) = (term893 A B P).
Proof. exact (@lem348933 (type1402 A) (type110 A B) P). Qed.
Lemma lem348935 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term894 A B f g) = (term895 A B f g).
Proof. exact (@lem348934 A B (term896 A B f g)). Qed.
Lemma lem348936 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) : (term897 A B f g lt2) = (term898 A B f g lt2).
Proof. exact (eq_refl (term897 A B f g lt2)). Qed.
Lemma lem348937 {A B : Type'} (x : type110 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem348938 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (x : type110 A B) : (term899 A B f g lt2 x) = (term900 A B f g lt2 x).
Proof. exact (MK_COMB (@lem348936 A B f g lt2) (@lem348937 A B x)). Qed.
Lemma lem348939 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (x : type110 A B) : (term900 A B f g lt2 x) = (term901 A B f g lt2 x).
Proof. exact (eq_refl (term900 A B f g lt2 x)). Qed.
Lemma lem348940 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (x : type110 A B) : (term899 A B f g lt2 x) = (term901 A B f g lt2 x).
Proof. exact (TRANS (@lem348938 A B f g lt2 x) (@lem348939 A B f g lt2 x)). Qed.
Lemma lem348941 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) : (term902 A B f g lt2) = (term898 A B f g lt2).
Proof. exact (fun_ext (fun x : type110 A B => @lem348940 A B f g lt2 x)). Qed.
Lemma lem348942 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem348943 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) : (term903 A B f g lt2) = (term884 A B f g lt2).
Proof. exact (MK_COMB (@lem348942 A B) (@lem348941 A B f g lt2)). Qed.
Lemma lem348944 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term904 A B f g) = (term886 A B f g).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348943 A B f g lt2)). Qed.
Lemma lem348945 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348946 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term894 A B f g) = (term888 A B f g).
Proof. exact (MK_COMB (@lem348945 A) (@lem348944 A B f g)). Qed.
Lemma lem348947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348948 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term905 A B f g) = (term906 A B f g).
Proof. exact (MK_COMB (@lem348947) (@lem348946 A B f g)). Qed.
Lemma lem348949 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) : (term897 A B f g lt2) = (term898 A B f g lt2).
Proof. exact (eq_refl (term897 A B f g lt2)). Qed.
Lemma lem348950 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) : (x lt2) = (x lt2).
Proof. exact (eq_refl (x lt2)). Qed.
Lemma lem348951 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) : (term907 A B f g x lt2) = (term908 A B f g x lt2).
Proof. exact (MK_COMB (@lem348949 A B f g lt2) (@lem348950 A B x lt2)). Qed.
Lemma lem348952 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) : (term908 A B f g x lt2) = (term909 A B f g x lt2).
Proof. exact (eq_refl (term908 A B f g x lt2)). Qed.
Lemma lem348953 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) : (term907 A B f g x lt2) = (term909 A B f g x lt2).
Proof. exact (TRANS (@lem348951 A B f g x lt2) (@lem348952 A B f g x lt2)). Qed.
Lemma lem348954 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : (term910 A B f g x) = (term911 A B f g x).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348953 A B f g x lt2)). Qed.
Lemma lem348955 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348956 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : (term912 A B f g x) = (term913 A B f g x).
Proof. exact (MK_COMB (@lem348955 A) (@lem348954 A B f g x)). Qed.
Lemma lem348957 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term914 A B f g) = (term915 A B f g).
Proof. exact (fun_ext (fun x : type410 A B => @lem348956 A B f g x)). Qed.
Lemma lem348958 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A))). Qed.
Lemma lem348959 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term895 A B f g) = (term916 A B f g).
Proof. exact (MK_COMB (@lem348958 A B) (@lem348957 A B f g)). Qed.
Lemma lem348960 {A B : Type'} (f : type409 A B) (g : type409 A B) : ((term894 A B f g) = (term895 A B f g)) = ((term888 A B f g) = (term916 A B f g)).
Proof. exact (MK_COMB (@lem348948 A B f g) (@lem348959 A B f g)). Qed.
Lemma lem348961 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term888 A B f g) = (term916 A B f g).
Proof. exact (EQ_MP (@lem348960 A B f g) (@lem348935 A B f g)). Qed.
Lemma lem348963 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem348964 {A B : Type'} (P : type405 A B) : (term917 A B P) = (term918 A B P).
Proof. exact (@lem348963 (type1402 A) (type106 A B) P). Qed.
Lemma lem348965 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : (term919 A B f g x) = (term920 A B f g x).
Proof. exact (@lem348964 A B (term921 A B f g x)). Qed.
Lemma lem348966 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) : (term922 A B f g x lt2) = (term923 A B f g x lt2).
Proof. exact (eq_refl (term922 A B f g x lt2)). Qed.
Lemma lem348967 {A B : Type'} (x : type106 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem348968 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (x' : type106 A B) : (term924 A B f g x lt2 x') = (term925 A B f g x lt2 x').
Proof. exact (MK_COMB (@lem348966 A B f g x lt2) (@lem348967 A B x')). Qed.
Lemma lem348969 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (x' : type106 A B) : (term925 A B f g x lt2 x') = (term926 A B f g x lt2 x').
Proof. exact (eq_refl (term925 A B f g x lt2 x')). Qed.
Lemma lem348970 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (x' : type106 A B) : (term924 A B f g x lt2 x') = (term926 A B f g x lt2 x').
Proof. exact (TRANS (@lem348968 A B f g x lt2 x') (@lem348969 A B f g x lt2 x')). Qed.
Lemma lem348971 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) : (term927 A B f g x lt2) = (term923 A B f g x lt2).
Proof. exact (fun_ext (fun x' : type106 A B => @lem348970 A B f g x lt2 x')). Qed.
Lemma lem348972 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A))). Qed.
Lemma lem348973 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) : (term928 A B f g x lt2) = (term909 A B f g x lt2).
Proof. exact (MK_COMB (@lem348972 A B) (@lem348971 A B f g x lt2)). Qed.
Lemma lem348974 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : (term929 A B f g x) = (term911 A B f g x).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348973 A B f g x lt2)). Qed.
Lemma lem348975 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348976 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : (term919 A B f g x) = (term913 A B f g x).
Proof. exact (MK_COMB (@lem348975 A) (@lem348974 A B f g x)). Qed.
Lemma lem348977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem348978 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : (term930 A B f g x) = (term931 A B f g x).
Proof. exact (MK_COMB (@lem348977) (@lem348976 A B f g x)). Qed.
Lemma lem348979 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) : (term922 A B f g x lt2) = (term923 A B f g x lt2).
Proof. exact (eq_refl (term922 A B f g x lt2)). Qed.
Lemma lem348980 {A B : Type'} (x : type408 A B) (lt2 : type1402 A) : (x lt2) = (x lt2).
Proof. exact (eq_refl (x lt2)). Qed.
Lemma lem348981 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (x' : type408 A B) (lt2 : type1402 A) : (term932 A B f g x x' lt2) = (term933 A B f g x x' lt2).
Proof. exact (MK_COMB (@lem348979 A B f g x lt2) (@lem348980 A B x' lt2)). Qed.
Lemma lem348982 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (x' : type408 A B) (lt2 : type1402 A) : (term933 A B f g x x' lt2) = (term934 A B f g x x' lt2).
Proof. exact (eq_refl (term933 A B f g x x' lt2)). Qed.
Lemma lem348983 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (x' : type408 A B) (lt2 : type1402 A) : (term932 A B f g x x' lt2) = (term934 A B f g x x' lt2).
Proof. exact (TRANS (@lem348981 A B f g x x' lt2) (@lem348982 A B f g x x' lt2)). Qed.
Lemma lem348984 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (x' : type408 A B) : (term935 A B f g x x') = (term936 A B f g x x').
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem348983 A B f g x x' lt2)). Qed.
Lemma lem348985 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem348986 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (x' : type408 A B) : (term937 A B f g x x') = (term938 A B f g x x').
Proof. exact (MK_COMB (@lem348985 A) (@lem348984 A B f g x x')). Qed.
Lemma lem348987 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : (term939 A B f g x) = (term940 A B f g x).
Proof. exact (fun_ext (fun x' : type408 A B => @lem348986 A B f g x x')). Qed.
Lemma lem348988 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A))). Qed.
Lemma lem348989 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : (term920 A B f g x) = (term941 A B f g x).
Proof. exact (MK_COMB (@lem348988 A B) (@lem348987 A B f g x)). Qed.
Lemma lem348990 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : ((term919 A B f g x) = (term920 A B f g x)) = ((term913 A B f g x) = (term941 A B f g x)).
Proof. exact (MK_COMB (@lem348978 A B f g x) (@lem348989 A B f g x)). Qed.
Lemma lem348991 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) : (term913 A B f g x) = (term941 A B f g x).
Proof. exact (EQ_MP (@lem348990 A B f g x) (@lem348965 A B f g x)). Qed.
Lemma lem348992 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term915 A B f g) = (term942 A B f g).
Proof. exact (fun_ext (fun x : type410 A B => @lem348991 A B f g x)). Qed.
Lemma lem348993 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A))). Qed.
Lemma lem348994 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term916 A B f g) = (term943 A B f g).
Proof. exact (MK_COMB (@lem348993 A B) (@lem348992 A B f g)). Qed.
Lemma lem348995 {A B : Type'} (f : type409 A B) (g : type409 A B) : (term888 A B f g) = (term943 A B f g).
Proof. exact (TRANS (@lem348961 A B f g) (@lem348994 A B f g)). Qed.
Lemma lem348996 {A B : Type'} (f : type409 A B) : (term890 A B f) = (term944 A B f).
Proof. exact (fun_ext (fun g : type409 A B => @lem348995 A B f g)). Qed.
Lemma lem348997 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem348998 {A B : Type'} (f : type409 A B) : (term891 A B f) = (term945 A B f).
Proof. exact (MK_COMB (@lem348997 A B) (@lem348996 A B f)). Qed.
Lemma lem348999 {A B : Type'} (f : type409 A B) : (term865 A B f) = (term945 A B f).
Proof. exact (TRANS (@lem348931 A B f) (@lem348998 A B f)). Qed.
Lemma lem349000 {A B : Type'} : (term867 A B) = (term946 A B).
Proof. exact (fun_ext (fun f : type409 A B => @lem348999 A B f)). Qed.
Lemma lem349001 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349002 {A B : Type'} : (term868 A B) = (term947 A B).
Proof. exact (MK_COMB (@lem349001 A B) (@lem349000 A B)). Qed.
Lemma lem349003 {A B : Type'} : (term845 A B) = (term947 A B).
Proof. exact (TRANS (@lem348901 A B) (@lem349002 A B)). Qed.
Lemma lem349005 {A B : Type'} : (term528 A B) = (term947 A B).
Proof. exact (TRANS (@lem348871 A B) (@lem349003 A B)). Qed.
Lemma lem349006 {A B : Type'} : (term8 A B) = (term947 A B).
Proof. exact (TRANS (@lem348139 A B) (@lem349005 A B)). Qed.
Lemma lem349007 {A B : Type'} (h1 : term8 A B) : term947 A B.
Proof. exact (EQ_MP (@lem349006 A B) (@lem347107 A B h1)). Qed.
Lemma lem349015 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term32 A B lt2 x f g z) = (term473 A B lt2 x f g z).
Proof. exact (@lem17265 (lt2 z x) ((f z) = (g z))). Qed.
Lemma lem349016 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term33 A B lt2 x f g) = (term474 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem349015 A B lt2 x f g z)). Qed.
Lemma lem349017 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem349018 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term34 A B lt2 x f g) = (term475 A B lt2 x f g).
Proof. exact (MK_COMB (@lem349017 A) (@lem349016 A B lt2 x f g)). Qed.
Lemma lem349019 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term476 A B f H g x) = (term476 A B f H g x).
Proof. exact (eq_refl (term476 A B f H g x)). Qed.
Lemma lem349020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem349021 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term477 A B lt2 x f g) = (term478 A B lt2 x f g).
Proof. exact (MK_COMB (@lem349020) (@lem349018 A B lt2 x f g)). Qed.
Lemma lem349022 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term479 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem349021 A B lt2 x f g) (@lem349019 A B f H g x)). Qed.
Lemma lem349023 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term481 A B lt2 f H g x) = (term479 A B lt2 f H g x).
Proof. exact (@lem17362 (term34 A B lt2 x f g) ((H f x) = (H g x))). Qed.
Lemma lem349024 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term481 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (TRANS (@lem349023 A B lt2 f H g x) (@lem349022 A B lt2 f H g x)). Qed.
Lemma lem349025 {A : Type'} (P : A -> Prop) : (term69 A P) = (term70 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem349026 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term482 A B lt2 f H g) = (term483 A B lt2 f H g).
Proof. exact (@lem349025 A (term37 A B lt2 f H g)). Qed.
Lemma lem349027 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term484 A B lt2 f H g x) = (term36 A B lt2 f H g x).
Proof. exact (eq_refl (term484 A B lt2 f H g x)). Qed.
Lemma lem349028 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem349029 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term485 A B lt2 f H g x) = (term481 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem349028) (@lem349027 A B lt2 f H g x)). Qed.
Lemma lem349030 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term485 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (TRANS (@lem349029 A B lt2 f H g x) (@lem349024 A B lt2 f H g x)). Qed.
Lemma lem349031 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term486 A B lt2 f H g) = (term487 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem349030 A B lt2 f H g x)). Qed.
Lemma lem349032 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem349033 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term483 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (MK_COMB (@lem349032 A) (@lem349031 A B lt2 f H g)). Qed.
Lemma lem349034 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term482 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (TRANS (@lem349026 A B lt2 f H g) (@lem349033 A B lt2 f H g)). Qed.
Lemma lem349035 {A B : Type'} (P : type572 A B) : (term489 A B P) = (term490 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem349036 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term491 A B lt2 f H) = (term492 A B lt2 f H).
Proof. exact (@lem349035 A B (term39 A B lt2 f H)). Qed.
Lemma lem349037 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term493 A B lt2 f H g) = (term38 A B lt2 f H g).
Proof. exact (eq_refl (term493 A B lt2 f H g)). Qed.
Lemma lem349038 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem349039 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term494 A B lt2 f H g) = (term482 A B lt2 f H g).
Proof. exact (MK_COMB (@lem349038) (@lem349037 A B lt2 f H g)). Qed.
Lemma lem349040 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term494 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (TRANS (@lem349039 A B lt2 f H g) (@lem349034 A B lt2 f H g)). Qed.
Lemma lem349041 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term495 A B lt2 f H) = (term496 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem349040 A B lt2 f H g)). Qed.
Lemma lem349042 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349043 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term492 A B lt2 f H) = (term497 A B lt2 f H).
Proof. exact (MK_COMB (@lem349042 A B) (@lem349041 A B lt2 f H)). Qed.
Lemma lem349044 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term491 A B lt2 f H) = (term497 A B lt2 f H).
Proof. exact (TRANS (@lem349036 A B lt2 f H) (@lem349043 A B lt2 f H)). Qed.
Lemma lem349045 {A B : Type'} (P : type572 A B) : (term489 A B P) = (term490 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem349046 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term498 A B lt2 H) = (term499 A B lt2 H).
Proof. exact (@lem349045 A B (term41 A B lt2 H)). Qed.
Lemma lem349047 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term500 A B lt2 H f) = (term40 A B lt2 f H).
Proof. exact (eq_refl (term500 A B lt2 H f)). Qed.
Lemma lem349048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem349049 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term501 A B lt2 H f) = (term491 A B lt2 f H).
Proof. exact (MK_COMB (@lem349048) (@lem349047 A B lt2 f H)). Qed.
Lemma lem349050 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term501 A B lt2 H f) = (term497 A B lt2 f H).
Proof. exact (TRANS (@lem349049 A B lt2 f H) (@lem349044 A B lt2 f H)). Qed.
Lemma lem349051 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term502 A B lt2 H) = (term503 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem349050 A B lt2 f H)). Qed.
Lemma lem349052 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349053 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term499 A B lt2 H) = (term504 A B lt2 H).
Proof. exact (MK_COMB (@lem349052 A B) (@lem349051 A B lt2 H)). Qed.
Lemma lem349054 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term498 A B lt2 H) = (term504 A B lt2 H).
Proof. exact (TRANS (@lem349046 A B lt2 H) (@lem349053 A B lt2 H)). Qed.
Lemma lem349055 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : ((f x) = (H f x)) = ((f x) = (H f x)).
Proof. exact (eq_refl ((f x) = (H f x))). Qed.
Lemma lem349056 {A B : Type'} (H : type549 A B) (f : A -> B) : (term28 A B H f) = (term28 A B H f).
Proof. exact (fun_ext (fun x : A => @lem349055 A B H f x)). Qed.
Lemma lem349057 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem349058 {A B : Type'} (H : type549 A B) (f : A -> B) : (term29 A B H f) = (term29 A B H f).
Proof. exact (MK_COMB (@lem349057 A) (@lem349056 A B H f)). Qed.
Lemma lem349059 {A B : Type'} (H : type549 A B) : (term30 A B H) = (term30 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem349058 A B H f)). Qed.
Lemma lem349060 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349061 {A B : Type'} (H : type549 A B) : (term31 A B H) = (term31 A B H).
Proof. exact (MK_COMB (@lem349060 A B) (@lem349059 A B H)). Qed.
Lemma lem349062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349063 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term518 A B lt2 H) = (term519 A B lt2 H).
Proof. exact (MK_COMB (@lem349062) (@lem349054 A B lt2 H)). Qed.
Lemma lem349064 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term948 A B lt2 H) = (term949 A B lt2 H).
Proof. exact (MK_COMB (@lem349063 A B lt2 H) (@lem349061 A B H)). Qed.
Lemma lem349065 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term44 A B lt2 H) = (term948 A B lt2 H).
Proof. exact (@lem17265 (term42 A B lt2 H) (term31 A B H)). Qed.
Lemma lem349066 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term44 A B lt2 H) = (term949 A B lt2 H).
Proof. exact (TRANS (@lem349065 A B lt2 H) (@lem349064 A B lt2 H)). Qed.
Lemma lem349067 {A B : Type'} (lt2 : type1402 A) : (term45 A B lt2) = (term950 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem349066 A B lt2 H)). Qed.
Lemma lem349068 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem349069 {A B : Type'} (lt2 : type1402 A) : (term46 A B lt2) = (term951 A B lt2).
Proof. exact (MK_COMB (@lem349068 A B) (@lem349067 A B lt2)). Qed.
Lemma lem349071 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem349072 {A B : Type'} (lt2 : type1402 A) : (term952 A B lt2) = (term953 A B lt2).
Proof. exact (MK_COMB (@lem349071 A lt2) (@lem349069 A B lt2)). Qed.
Lemma lem349073 {A B : Type'} (lt2 : type1402 A) : (term48 A B lt2) = (term952 A B lt2).
Proof. exact (@lem17265 (@WF A lt2) (term46 A B lt2)). Qed.
Lemma lem349074 {A B : Type'} (lt2 : type1402 A) : (term48 A B lt2) = (term953 A B lt2).
Proof. exact (TRANS (@lem349073 A B lt2) (@lem349072 A B lt2)). Qed.
Lemma lem349075 {A B : Type'} : (term49 A B) = (term954 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem349074 A B lt2)). Qed.
Lemma lem349076 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem349077 {A B : Type'} : (term7 A B) = (term955 A B).
Proof. exact (MK_COMB (@lem349076 A) (@lem349075 A B)). Qed.
Lemma lem349288 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term529 A P Q) = (term530 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem349289 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term956 A B P Q) = (term957 A B P Q).
Proof. exact (@lem349288 (A -> B) P Q). Qed.
Lemma lem349290 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term958 A B lt2 H) = (term959 A B lt2 H).
Proof. exact (@lem349289 A B (term503 A B lt2 H) (term30 A B H)). Qed.
Lemma lem349291 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term615 A B lt2 H f) = (term497 A B lt2 f H).
Proof. exact (eq_refl (term615 A B lt2 H f)). Qed.
Lemma lem349292 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term616 A B lt2 H) = (term503 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem349291 A B lt2 f H)). Qed.
Lemma lem349293 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349294 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term617 A B lt2 H) = (term504 A B lt2 H).
Proof. exact (MK_COMB (@lem349293 A B) (@lem349292 A B lt2 H)). Qed.
Lemma lem349295 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349296 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term618 A B lt2 H) = (term519 A B lt2 H).
Proof. exact (MK_COMB (@lem349295) (@lem349294 A B lt2 H)). Qed.
Lemma lem349297 {A B : Type'} (H : type549 A B) (f : A -> B) : (term97 A B H f) = (term29 A B H f).
Proof. exact (eq_refl (term97 A B H f)). Qed.
Lemma lem349298 {A B : Type'} (H : type549 A B) : (term960 A B H) = (term30 A B H).
Proof. exact (fun_ext (fun f : A -> B => @lem349297 A B H f)). Qed.
Lemma lem349299 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349300 {A B : Type'} (H : type549 A B) : (term961 A B H) = (term31 A B H).
Proof. exact (MK_COMB (@lem349299 A B) (@lem349298 A B H)). Qed.
Lemma lem349301 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term958 A B lt2 H) = (term949 A B lt2 H).
Proof. exact (MK_COMB (@lem349296 A B lt2 H) (@lem349300 A B H)). Qed.
Lemma lem349302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349303 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term962 A B lt2 H) = (term963 A B lt2 H).
Proof. exact (MK_COMB (@lem349302) (@lem349301 A B lt2 H)). Qed.
Lemma lem349304 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term615 A B lt2 H f) = (term497 A B lt2 f H).
Proof. exact (eq_refl (term615 A B lt2 H f)). Qed.
Lemma lem349305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349306 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term621 A B lt2 H f) = (term622 A B lt2 f H).
Proof. exact (MK_COMB (@lem349305) (@lem349304 A B lt2 f H)). Qed.
Lemma lem349307 {A B : Type'} (H : type549 A B) (f : A -> B) : (term97 A B H f) = (term29 A B H f).
Proof. exact (eq_refl (term97 A B H f)). Qed.
Lemma lem349308 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term964 A B lt2 H f) = (term965 A B lt2 H f).
Proof. exact (MK_COMB (@lem349306 A B lt2 f H) (@lem349307 A B H f)). Qed.
Lemma lem349309 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term966 A B lt2 H) = (term967 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem349308 A B lt2 H f)). Qed.
Lemma lem349310 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349311 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term959 A B lt2 H) = (term968 A B lt2 H).
Proof. exact (MK_COMB (@lem349310 A B) (@lem349309 A B lt2 H)). Qed.
Lemma lem349312 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : ((term958 A B lt2 H) = (term959 A B lt2 H)) = ((term949 A B lt2 H) = (term968 A B lt2 H)).
Proof. exact (MK_COMB (@lem349303 A B lt2 H) (@lem349311 A B lt2 H)). Qed.
Lemma lem349313 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term949 A B lt2 H) = (term968 A B lt2 H).
Proof. exact (EQ_MP (@lem349312 A B lt2 H) (@lem349290 A B lt2 H)). Qed.
Lemma lem349315 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem349316 {A B : Type'} (P : type572 A B) (Q : Prop) : (term611 A B P Q) = (term612 A B P Q).
Proof. exact (@lem349315 (A -> B) P Q). Qed.
Lemma lem349317 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term969 A B lt2 H f) = (term970 A B lt2 H f).
Proof. exact (@lem349316 A B (term496 A B lt2 f H) (term29 A B H f)). Qed.
Lemma lem349318 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term630 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (eq_refl (term630 A B lt2 f H g)). Qed.
Lemma lem349319 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term631 A B lt2 f H) = (term496 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem349318 A B lt2 f H g)). Qed.
Lemma lem349320 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349321 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term632 A B lt2 f H) = (term497 A B lt2 f H).
Proof. exact (MK_COMB (@lem349320 A B) (@lem349319 A B lt2 f H)). Qed.
Lemma lem349322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349323 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term633 A B lt2 f H) = (term622 A B lt2 f H).
Proof. exact (MK_COMB (@lem349322) (@lem349321 A B lt2 f H)). Qed.
Lemma lem349324 {A B : Type'} (H : type549 A B) (f : A -> B) : (term29 A B H f) = (term29 A B H f).
Proof. exact (eq_refl (term29 A B H f)). Qed.
Lemma lem349325 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term969 A B lt2 H f) = (term965 A B lt2 H f).
Proof. exact (MK_COMB (@lem349323 A B lt2 f H) (@lem349324 A B H f)). Qed.
Lemma lem349326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349327 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term971 A B lt2 H f) = (term972 A B lt2 H f).
Proof. exact (MK_COMB (@lem349326) (@lem349325 A B lt2 H f)). Qed.
Lemma lem349328 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term630 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (eq_refl (term630 A B lt2 f H g)). Qed.
Lemma lem349329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349330 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term636 A B lt2 f H g) = (term637 A B lt2 f H g).
Proof. exact (MK_COMB (@lem349329) (@lem349328 A B lt2 f H g)). Qed.
Lemma lem349331 {A B : Type'} (H : type549 A B) (f : A -> B) : (term29 A B H f) = (term29 A B H f).
Proof. exact (eq_refl (term29 A B H f)). Qed.
Lemma lem349332 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (H : type549 A B) (f : A -> B) : (term973 A B lt2 g H f) = (term974 A B lt2 g H f).
Proof. exact (MK_COMB (@lem349330 A B lt2 f H g) (@lem349331 A B H f)). Qed.
Lemma lem349333 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term975 A B lt2 H f) = (term976 A B lt2 H f).
Proof. exact (fun_ext (fun g : A -> B => @lem349332 A B lt2 g H f)). Qed.
Lemma lem349334 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349335 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term970 A B lt2 H f) = (term977 A B lt2 H f).
Proof. exact (MK_COMB (@lem349334 A B) (@lem349333 A B lt2 H f)). Qed.
Lemma lem349336 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : ((term969 A B lt2 H f) = (term970 A B lt2 H f)) = ((term965 A B lt2 H f) = (term977 A B lt2 H f)).
Proof. exact (MK_COMB (@lem349327 A B lt2 H f) (@lem349335 A B lt2 H f)). Qed.
Lemma lem349337 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term965 A B lt2 H f) = (term977 A B lt2 H f).
Proof. exact (EQ_MP (@lem349336 A B lt2 H f) (@lem349317 A B lt2 H f)). Qed.
Lemma lem349339 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem349340 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (@lem349339 A P Q). Qed.
Lemma lem349341 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (H : type549 A B) (f : A -> B) : (term978 A B lt2 g H f) = (term979 A B lt2 g H f).
Proof. exact (@lem349340 A (term487 A B lt2 f H g) (term29 A B H f)). Qed.
Lemma lem349342 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term645 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (eq_refl (term645 A B lt2 f H g x)). Qed.
Lemma lem349343 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term646 A B lt2 f H g) = (term487 A B lt2 f H g).
Proof. exact (fun_ext (fun x : A => @lem349342 A B lt2 f H g x)). Qed.
Lemma lem349344 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem349345 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term647 A B lt2 f H g) = (term488 A B lt2 f H g).
Proof. exact (MK_COMB (@lem349344 A) (@lem349343 A B lt2 f H g)). Qed.
Lemma lem349346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349347 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term648 A B lt2 f H g) = (term637 A B lt2 f H g).
Proof. exact (MK_COMB (@lem349346) (@lem349345 A B lt2 f H g)). Qed.
Lemma lem349348 {A B : Type'} (H : type549 A B) (f : A -> B) : (term29 A B H f) = (term29 A B H f).
Proof. exact (eq_refl (term29 A B H f)). Qed.
Lemma lem349349 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (H : type549 A B) (f : A -> B) : (term978 A B lt2 g H f) = (term974 A B lt2 g H f).
Proof. exact (MK_COMB (@lem349347 A B lt2 f H g) (@lem349348 A B H f)). Qed.
Lemma lem349350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349351 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (H : type549 A B) (f : A -> B) : (term980 A B lt2 g H f) = (term981 A B lt2 g H f).
Proof. exact (MK_COMB (@lem349350) (@lem349349 A B lt2 g H f)). Qed.
Lemma lem349352 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term645 A B lt2 f H g x) = (term480 A B lt2 f H g x).
Proof. exact (eq_refl (term645 A B lt2 f H g x)). Qed.
Lemma lem349353 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349354 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term651 A B lt2 f H g x) = (term652 A B lt2 f H g x).
Proof. exact (MK_COMB (@lem349353) (@lem349352 A B lt2 f H g x)). Qed.
Lemma lem349355 {A B : Type'} (H : type549 A B) (f : A -> B) : (term29 A B H f) = (term29 A B H f).
Proof. exact (eq_refl (term29 A B H f)). Qed.
Lemma lem349356 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (x : A) (H : type549 A B) (f : A -> B) : (term982 A B lt2 g x H f) = (term983 A B lt2 g x H f).
Proof. exact (MK_COMB (@lem349354 A B lt2 f H g x) (@lem349355 A B H f)). Qed.
Lemma lem349357 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (H : type549 A B) (f : A -> B) : (term984 A B lt2 g H f) = (term985 A B lt2 g H f).
Proof. exact (fun_ext (fun x : A => @lem349356 A B lt2 g x H f)). Qed.
Lemma lem349358 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem349359 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (H : type549 A B) (f : A -> B) : (term979 A B lt2 g H f) = (term986 A B lt2 g H f).
Proof. exact (MK_COMB (@lem349358 A) (@lem349357 A B lt2 g H f)). Qed.
Lemma lem349360 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (H : type549 A B) (f : A -> B) : ((term978 A B lt2 g H f) = (term979 A B lt2 g H f)) = ((term974 A B lt2 g H f) = (term986 A B lt2 g H f)).
Proof. exact (MK_COMB (@lem349351 A B lt2 g H f) (@lem349359 A B lt2 g H f)). Qed.
Lemma lem349361 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (H : type549 A B) (f : A -> B) : (term974 A B lt2 g H f) = (term986 A B lt2 g H f).
Proof. exact (EQ_MP (@lem349360 A B lt2 g H f) (@lem349341 A B lt2 g H f)). Qed.
Lemma lem349362 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term976 A B lt2 H f) = (term987 A B lt2 H f).
Proof. exact (fun_ext (fun g : A -> B => @lem349361 A B lt2 g H f)). Qed.
Lemma lem349363 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349364 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term977 A B lt2 H f) = (term988 A B lt2 H f).
Proof. exact (MK_COMB (@lem349363 A B) (@lem349362 A B lt2 H f)). Qed.
Lemma lem349365 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term965 A B lt2 H f) = (term988 A B lt2 H f).
Proof. exact (TRANS (@lem349337 A B lt2 H f) (@lem349364 A B lt2 H f)). Qed.
Lemma lem349366 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term967 A B lt2 H) = (term989 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem349365 A B lt2 H f)). Qed.
Lemma lem349367 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349368 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term968 A B lt2 H) = (term990 A B lt2 H).
Proof. exact (MK_COMB (@lem349367 A B) (@lem349366 A B lt2 H)). Qed.
Lemma lem349369 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term949 A B lt2 H) = (term990 A B lt2 H).
Proof. exact (TRANS (@lem349313 A B lt2 H) (@lem349368 A B lt2 H)). Qed.
Lemma lem349370 {A B : Type'} (lt2 : type1402 A) : (term950 A B lt2) = (term991 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem349369 A B lt2 H)). Qed.
Lemma lem349371 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem349372 {A B : Type'} (lt2 : type1402 A) : (term951 A B lt2) = (term992 A B lt2).
Proof. exact (MK_COMB (@lem349371 A B) (@lem349370 A B lt2)). Qed.
Lemma lem349374 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem349375 {A B : Type'} (P : type107 A B) : (term680 A B P) = (term681 A B P).
Proof. exact (@lem349374 (type549 A B) (A -> B) P). Qed.
Lemma lem349376 {A B : Type'} (lt2 : type1402 A) : (term993 A B lt2) = (term994 A B lt2).
Proof. exact (@lem349375 A B (term995 A B lt2)). Qed.
Lemma lem349377 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term996 A B lt2 H) = (term989 A B lt2 H).
Proof. exact (eq_refl (term996 A B lt2 H)). Qed.
Lemma lem349378 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem349379 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term997 A B lt2 H f) = (term998 A B lt2 H f).
Proof. exact (MK_COMB (@lem349377 A B lt2 H) (@lem349378 A B f)). Qed.
Lemma lem349380 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term998 A B lt2 H f) = (term988 A B lt2 H f).
Proof. exact (eq_refl (term998 A B lt2 H f)). Qed.
Lemma lem349381 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term997 A B lt2 H f) = (term988 A B lt2 H f).
Proof. exact (TRANS (@lem349379 A B lt2 H f) (@lem349380 A B lt2 H f)). Qed.
Lemma lem349382 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term999 A B lt2 H) = (term989 A B lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem349381 A B lt2 H f)). Qed.
Lemma lem349383 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349384 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term1000 A B lt2 H) = (term990 A B lt2 H).
Proof. exact (MK_COMB (@lem349383 A B) (@lem349382 A B lt2 H)). Qed.
Lemma lem349385 {A B : Type'} (lt2 : type1402 A) : (term1001 A B lt2) = (term991 A B lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem349384 A B lt2 H)). Qed.
Lemma lem349386 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem349387 {A B : Type'} (lt2 : type1402 A) : (term993 A B lt2) = (term992 A B lt2).
Proof. exact (MK_COMB (@lem349386 A B) (@lem349385 A B lt2)). Qed.
Lemma lem349388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349389 {A B : Type'} (lt2 : type1402 A) : (term1002 A B lt2) = (term1003 A B lt2).
Proof. exact (MK_COMB (@lem349388) (@lem349387 A B lt2)). Qed.
Lemma lem349390 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term996 A B lt2 H) = (term989 A B lt2 H).
Proof. exact (eq_refl (term996 A B lt2 H)). Qed.
Lemma lem349391 {A B : Type'} (f : type108 A B) (H : type549 A B) : (f H) = (f H).
Proof. exact (eq_refl (f H)). Qed.
Lemma lem349392 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term1004 A B lt2 f H) = (term1005 A B lt2 f H).
Proof. exact (MK_COMB (@lem349390 A B lt2 H) (@lem349391 A B f H)). Qed.
Lemma lem349393 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term1005 A B lt2 f H) = (term1006 A B lt2 f H).
Proof. exact (eq_refl (term1005 A B lt2 f H)). Qed.
Lemma lem349394 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term1004 A B lt2 f H) = (term1006 A B lt2 f H).
Proof. exact (TRANS (@lem349392 A B lt2 f H) (@lem349393 A B lt2 f H)). Qed.
Lemma lem349395 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1007 A B lt2 f) = (term1008 A B lt2 f).
Proof. exact (fun_ext (fun H : type549 A B => @lem349394 A B lt2 f H)). Qed.
Lemma lem349396 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem349397 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1009 A B lt2 f) = (term1010 A B lt2 f).
Proof. exact (MK_COMB (@lem349396 A B) (@lem349395 A B lt2 f)). Qed.
Lemma lem349398 {A B : Type'} (lt2 : type1402 A) : (term1011 A B lt2) = (term1012 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem349397 A B lt2 f)). Qed.
Lemma lem349399 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349400 {A B : Type'} (lt2 : type1402 A) : (term994 A B lt2) = (term1013 A B lt2).
Proof. exact (MK_COMB (@lem349399 A B) (@lem349398 A B lt2)). Qed.
Lemma lem349401 {A B : Type'} (lt2 : type1402 A) : ((term993 A B lt2) = (term994 A B lt2)) = ((term992 A B lt2) = (term1013 A B lt2)).
Proof. exact (MK_COMB (@lem349389 A B lt2) (@lem349400 A B lt2)). Qed.
Lemma lem349402 {A B : Type'} (lt2 : type1402 A) : (term992 A B lt2) = (term1013 A B lt2).
Proof. exact (EQ_MP (@lem349401 A B lt2) (@lem349376 A B lt2)). Qed.
Lemma lem349404 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem349405 {A B : Type'} (P : type107 A B) : (term680 A B P) = (term681 A B P).
Proof. exact (@lem349404 (type549 A B) (A -> B) P). Qed.
Lemma lem349406 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1014 A B lt2 f) = (term1015 A B lt2 f).
Proof. exact (@lem349405 A B (term1016 A B lt2 f)). Qed.
Lemma lem349407 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term1017 A B lt2 f H) = (term1018 A B lt2 f H).
Proof. exact (eq_refl (term1017 A B lt2 f H)). Qed.
Lemma lem349408 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem349409 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) (g : A -> B) : (term1019 A B lt2 f H g) = (term1020 A B lt2 f H g).
Proof. exact (MK_COMB (@lem349407 A B lt2 f H) (@lem349408 A B g)). Qed.
Lemma lem349410 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (f : type108 A B) (H : type549 A B) : (term1020 A B lt2 f H g) = (term1021 A B lt2 g f H).
Proof. exact (eq_refl (term1020 A B lt2 f H g)). Qed.
Lemma lem349411 {A B : Type'} (lt2 : type1402 A) (g : A -> B) (f : type108 A B) (H : type549 A B) : (term1019 A B lt2 f H g) = (term1021 A B lt2 g f H).
Proof. exact (TRANS (@lem349409 A B lt2 f H g) (@lem349410 A B lt2 g f H)). Qed.
Lemma lem349412 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term1022 A B lt2 f H) = (term1018 A B lt2 f H).
Proof. exact (fun_ext (fun g : A -> B => @lem349411 A B lt2 g f H)). Qed.
Lemma lem349413 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem349414 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term1023 A B lt2 f H) = (term1006 A B lt2 f H).
Proof. exact (MK_COMB (@lem349413 A B) (@lem349412 A B lt2 f H)). Qed.
Lemma lem349415 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1024 A B lt2 f) = (term1008 A B lt2 f).
Proof. exact (fun_ext (fun H : type549 A B => @lem349414 A B lt2 f H)). Qed.
Lemma lem349416 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem349417 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1014 A B lt2 f) = (term1010 A B lt2 f).
Proof. exact (MK_COMB (@lem349416 A B) (@lem349415 A B lt2 f)). Qed.
Lemma lem349418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349419 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1025 A B lt2 f) = (term1026 A B lt2 f).
Proof. exact (MK_COMB (@lem349418) (@lem349417 A B lt2 f)). Qed.
Lemma lem349420 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (H : type549 A B) : (term1017 A B lt2 f H) = (term1018 A B lt2 f H).
Proof. exact (eq_refl (term1017 A B lt2 f H)). Qed.
Lemma lem349421 {A B : Type'} (g : type108 A B) (H : type549 A B) : (g H) = (g H).
Proof. exact (eq_refl (g H)). Qed.
Lemma lem349422 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) (g : type108 A B) (H : type549 A B) : (term1027 A B lt2 f g H) = (term1028 A B lt2 f g H).
Proof. exact (MK_COMB (@lem349420 A B lt2 f H) (@lem349421 A B g H)). Qed.
Lemma lem349423 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) (H : type549 A B) : (term1028 A B lt2 f g H) = (term1029 A B lt2 g f H).
Proof. exact (eq_refl (term1028 A B lt2 f g H)). Qed.
Lemma lem349424 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) (H : type549 A B) : (term1027 A B lt2 f g H) = (term1029 A B lt2 g f H).
Proof. exact (TRANS (@lem349422 A B lt2 f g H) (@lem349423 A B lt2 g f H)). Qed.
Lemma lem349425 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1030 A B lt2 f g) = (term1031 A B lt2 g f).
Proof. exact (fun_ext (fun H : type549 A B => @lem349424 A B lt2 g f H)). Qed.
Lemma lem349426 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem349427 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1032 A B lt2 f g) = (term1033 A B lt2 g f).
Proof. exact (MK_COMB (@lem349426 A B) (@lem349425 A B lt2 g f)). Qed.
Lemma lem349428 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1034 A B lt2 f) = (term1035 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem349427 A B lt2 g f)). Qed.
Lemma lem349429 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349430 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1015 A B lt2 f) = (term1036 A B lt2 f).
Proof. exact (MK_COMB (@lem349429 A B) (@lem349428 A B lt2 f)). Qed.
Lemma lem349431 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : ((term1014 A B lt2 f) = (term1015 A B lt2 f)) = ((term1010 A B lt2 f) = (term1036 A B lt2 f)).
Proof. exact (MK_COMB (@lem349419 A B lt2 f) (@lem349430 A B lt2 f)). Qed.
Lemma lem349432 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1010 A B lt2 f) = (term1036 A B lt2 f).
Proof. exact (EQ_MP (@lem349431 A B lt2 f) (@lem349406 A B lt2 f)). Qed.
Lemma lem349434 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem349435 {A B : Type'} (P : type109 A B) : (term726 A B P) = (term727 A B P).
Proof. exact (@lem349434 (type549 A B) A P). Qed.
Lemma lem349436 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1037 A B lt2 g f) = (term1038 A B lt2 g f).
Proof. exact (@lem349435 A B (term1039 A B lt2 g f)). Qed.
Lemma lem349437 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) (H : type549 A B) : (term1040 A B lt2 g f H) = (term1041 A B lt2 g f H).
Proof. exact (eq_refl (term1040 A B lt2 g f H)). Qed.
Lemma lem349438 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem349439 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) (H : type549 A B) (x : A) : (term1042 A B lt2 g f H x) = (term1043 A B lt2 g f H x).
Proof. exact (MK_COMB (@lem349437 A B lt2 g f H) (@lem349438 A x)). Qed.
Lemma lem349440 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (x : A) (f : type108 A B) (H : type549 A B) : (term1043 A B lt2 g f H x) = (term1044 A B lt2 g x f H).
Proof. exact (eq_refl (term1043 A B lt2 g f H x)). Qed.
Lemma lem349441 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (x : A) (f : type108 A B) (H : type549 A B) : (term1042 A B lt2 g f H x) = (term1044 A B lt2 g x f H).
Proof. exact (TRANS (@lem349439 A B lt2 g f H x) (@lem349440 A B lt2 g x f H)). Qed.
Lemma lem349442 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) (H : type549 A B) : (term1045 A B lt2 g f H) = (term1041 A B lt2 g f H).
Proof. exact (fun_ext (fun x : A => @lem349441 A B lt2 g x f H)). Qed.
Lemma lem349443 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem349444 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) (H : type549 A B) : (term1046 A B lt2 g f H) = (term1029 A B lt2 g f H).
Proof. exact (MK_COMB (@lem349443 A) (@lem349442 A B lt2 g f H)). Qed.
Lemma lem349445 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1047 A B lt2 g f) = (term1031 A B lt2 g f).
Proof. exact (fun_ext (fun H : type549 A B => @lem349444 A B lt2 g f H)). Qed.
Lemma lem349446 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem349447 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1037 A B lt2 g f) = (term1033 A B lt2 g f).
Proof. exact (MK_COMB (@lem349446 A B) (@lem349445 A B lt2 g f)). Qed.
Lemma lem349448 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349449 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1048 A B lt2 g f) = (term1049 A B lt2 g f).
Proof. exact (MK_COMB (@lem349448) (@lem349447 A B lt2 g f)). Qed.
Lemma lem349450 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) (H : type549 A B) : (term1040 A B lt2 g f H) = (term1041 A B lt2 g f H).
Proof. exact (eq_refl (term1040 A B lt2 g f H)). Qed.
Lemma lem349451 {A B : Type'} (x : type110 A B) (H : type549 A B) : (x H) = (x H).
Proof. exact (eq_refl (x H)). Qed.
Lemma lem349452 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) (x : type110 A B) (H : type549 A B) : (term1050 A B lt2 g f x H) = (term1051 A B lt2 g f x H).
Proof. exact (MK_COMB (@lem349450 A B lt2 g f H) (@lem349451 A B x H)). Qed.
Lemma lem349453 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (x : type110 A B) (f : type108 A B) (H : type549 A B) : (term1051 A B lt2 g f x H) = (term1052 A B lt2 g x f H).
Proof. exact (eq_refl (term1051 A B lt2 g f x H)). Qed.
Lemma lem349454 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (x : type110 A B) (f : type108 A B) (H : type549 A B) : (term1050 A B lt2 g f x H) = (term1052 A B lt2 g x f H).
Proof. exact (TRANS (@lem349452 A B lt2 g f x H) (@lem349453 A B lt2 g x f H)). Qed.
Lemma lem349455 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (x : type110 A B) (f : type108 A B) : (term1053 A B lt2 g f x) = (term1054 A B lt2 g x f).
Proof. exact (fun_ext (fun H : type549 A B => @lem349454 A B lt2 g x f H)). Qed.
Lemma lem349456 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem349457 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (x : type110 A B) (f : type108 A B) : (term1055 A B lt2 g f x) = (term1056 A B lt2 g x f).
Proof. exact (MK_COMB (@lem349456 A B) (@lem349455 A B lt2 g x f)). Qed.
Lemma lem349458 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1057 A B lt2 g f) = (term1058 A B lt2 g f).
Proof. exact (fun_ext (fun x : type110 A B => @lem349457 A B lt2 g x f)). Qed.
Lemma lem349459 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem349460 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1038 A B lt2 g f) = (term1059 A B lt2 g f).
Proof. exact (MK_COMB (@lem349459 A B) (@lem349458 A B lt2 g f)). Qed.
Lemma lem349461 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : ((term1037 A B lt2 g f) = (term1038 A B lt2 g f)) = ((term1033 A B lt2 g f) = (term1059 A B lt2 g f)).
Proof. exact (MK_COMB (@lem349449 A B lt2 g f) (@lem349460 A B lt2 g f)). Qed.
Lemma lem349462 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1033 A B lt2 g f) = (term1059 A B lt2 g f).
Proof. exact (EQ_MP (@lem349461 A B lt2 g f) (@lem349436 A B lt2 g f)). Qed.
Lemma lem349463 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1035 A B lt2 f) = (term1060 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem349462 A B lt2 g f)). Qed.
Lemma lem349464 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349465 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1036 A B lt2 f) = (term1061 A B lt2 f).
Proof. exact (MK_COMB (@lem349464 A B) (@lem349463 A B lt2 f)). Qed.
Lemma lem349466 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1010 A B lt2 f) = (term1061 A B lt2 f).
Proof. exact (TRANS (@lem349432 A B lt2 f) (@lem349465 A B lt2 f)). Qed.
Lemma lem349467 {A B : Type'} (lt2 : type1402 A) : (term1012 A B lt2) = (term1062 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem349466 A B lt2 f)). Qed.
Lemma lem349468 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349469 {A B : Type'} (lt2 : type1402 A) : (term1013 A B lt2) = (term1063 A B lt2).
Proof. exact (MK_COMB (@lem349468 A B) (@lem349467 A B lt2)). Qed.
Lemma lem349470 {A B : Type'} (lt2 : type1402 A) : (term992 A B lt2) = (term1063 A B lt2).
Proof. exact (TRANS (@lem349402 A B lt2) (@lem349469 A B lt2)). Qed.
Lemma lem349471 {A B : Type'} (lt2 : type1402 A) : (term951 A B lt2) = (term1063 A B lt2).
Proof. exact (TRANS (@lem349372 A B lt2) (@lem349470 A B lt2)). Qed.
Lemma lem349472 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem349473 {A B : Type'} (lt2 : type1402 A) : (term953 A B lt2) = (term1064 A B lt2).
Proof. exact (MK_COMB (@lem349472 A lt2) (@lem349471 A B lt2)). Qed.
Lemma lem349475 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem349476 {A B : Type'} (P : Prop) (Q : type66 A B) : (term783 A B P Q) = (term784 A B P Q).
Proof. exact (@lem349475 (type108 A B) P Q). Qed.
Lemma lem349477 {A B : Type'} (lt2 : type1402 A) : (term1065 A B lt2) = (term1066 A B lt2).
Proof. exact (@lem349476 A B (term787 A lt2) (term1062 A B lt2)). Qed.
Lemma lem349478 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1067 A B lt2 f) = (term1061 A B lt2 f).
Proof. exact (eq_refl (term1067 A B lt2 f)). Qed.
Lemma lem349479 {A B : Type'} (lt2 : type1402 A) : (term1068 A B lt2) = (term1062 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem349478 A B lt2 f)). Qed.
Lemma lem349480 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349481 {A B : Type'} (lt2 : type1402 A) : (term1069 A B lt2) = (term1063 A B lt2).
Proof. exact (MK_COMB (@lem349480 A B) (@lem349479 A B lt2)). Qed.
Lemma lem349482 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem349483 {A B : Type'} (lt2 : type1402 A) : (term1065 A B lt2) = (term1064 A B lt2).
Proof. exact (MK_COMB (@lem349482 A lt2) (@lem349481 A B lt2)). Qed.
Lemma lem349484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349485 {A B : Type'} (lt2 : type1402 A) : (term1070 A B lt2) = (term1071 A B lt2).
Proof. exact (MK_COMB (@lem349484) (@lem349483 A B lt2)). Qed.
Lemma lem349486 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1067 A B lt2 f) = (term1061 A B lt2 f).
Proof. exact (eq_refl (term1067 A B lt2 f)). Qed.
Lemma lem349487 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem349488 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1072 A B lt2 f) = (term1073 A B lt2 f).
Proof. exact (MK_COMB (@lem349487 A lt2) (@lem349486 A B lt2 f)). Qed.
Lemma lem349489 {A B : Type'} (lt2 : type1402 A) : (term1074 A B lt2) = (term1075 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem349488 A B lt2 f)). Qed.
Lemma lem349490 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349491 {A B : Type'} (lt2 : type1402 A) : (term1066 A B lt2) = (term1076 A B lt2).
Proof. exact (MK_COMB (@lem349490 A B) (@lem349489 A B lt2)). Qed.
Lemma lem349492 {A B : Type'} (lt2 : type1402 A) : ((term1065 A B lt2) = (term1066 A B lt2)) = ((term1064 A B lt2) = (term1076 A B lt2)).
Proof. exact (MK_COMB (@lem349485 A B lt2) (@lem349491 A B lt2)). Qed.
Lemma lem349493 {A B : Type'} (lt2 : type1402 A) : (term1064 A B lt2) = (term1076 A B lt2).
Proof. exact (EQ_MP (@lem349492 A B lt2) (@lem349477 A B lt2)). Qed.
Lemma lem349495 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem349496 {A B : Type'} (P : Prop) (Q : type66 A B) : (term783 A B P Q) = (term784 A B P Q).
Proof. exact (@lem349495 (type108 A B) P Q). Qed.
Lemma lem349497 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1077 A B lt2 f) = (term1078 A B lt2 f).
Proof. exact (@lem349496 A B (term787 A lt2) (term1060 A B lt2 f)). Qed.
Lemma lem349498 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1079 A B lt2 f g) = (term1059 A B lt2 g f).
Proof. exact (eq_refl (term1079 A B lt2 f g)). Qed.
Lemma lem349499 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1080 A B lt2 f) = (term1060 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem349498 A B lt2 g f)). Qed.
Lemma lem349500 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349501 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1081 A B lt2 f) = (term1061 A B lt2 f).
Proof. exact (MK_COMB (@lem349500 A B) (@lem349499 A B lt2 f)). Qed.
Lemma lem349502 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem349503 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1077 A B lt2 f) = (term1073 A B lt2 f).
Proof. exact (MK_COMB (@lem349502 A lt2) (@lem349501 A B lt2 f)). Qed.
Lemma lem349504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349505 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1082 A B lt2 f) = (term1083 A B lt2 f).
Proof. exact (MK_COMB (@lem349504) (@lem349503 A B lt2 f)). Qed.
Lemma lem349506 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1079 A B lt2 f g) = (term1059 A B lt2 g f).
Proof. exact (eq_refl (term1079 A B lt2 f g)). Qed.
Lemma lem349507 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem349508 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1084 A B lt2 f g) = (term1085 A B lt2 g f).
Proof. exact (MK_COMB (@lem349507 A lt2) (@lem349506 A B lt2 g f)). Qed.
Lemma lem349509 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1086 A B lt2 f) = (term1087 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem349508 A B lt2 g f)). Qed.
Lemma lem349510 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349511 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1078 A B lt2 f) = (term1088 A B lt2 f).
Proof. exact (MK_COMB (@lem349510 A B) (@lem349509 A B lt2 f)). Qed.
Lemma lem349512 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : ((term1077 A B lt2 f) = (term1078 A B lt2 f)) = ((term1073 A B lt2 f) = (term1088 A B lt2 f)).
Proof. exact (MK_COMB (@lem349505 A B lt2 f) (@lem349511 A B lt2 f)). Qed.
Lemma lem349513 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1073 A B lt2 f) = (term1088 A B lt2 f).
Proof. exact (EQ_MP (@lem349512 A B lt2 f) (@lem349497 A B lt2 f)). Qed.
Lemma lem349515 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem349516 {A B : Type'} (P : Prop) (Q : type67 A B) : (term810 A B P Q) = (term811 A B P Q).
Proof. exact (@lem349515 (type110 A B) P Q). Qed.
Lemma lem349517 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1089 A B lt2 g f) = (term1090 A B lt2 g f).
Proof. exact (@lem349516 A B (term787 A lt2) (term1058 A B lt2 g f)). Qed.
Lemma lem349518 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (x : type110 A B) (f : type108 A B) : (term1091 A B lt2 g f x) = (term1056 A B lt2 g x f).
Proof. exact (eq_refl (term1091 A B lt2 g f x)). Qed.
Lemma lem349519 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1092 A B lt2 g f) = (term1058 A B lt2 g f).
Proof. exact (fun_ext (fun x : type110 A B => @lem349518 A B lt2 g x f)). Qed.
Lemma lem349520 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem349521 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1093 A B lt2 g f) = (term1059 A B lt2 g f).
Proof. exact (MK_COMB (@lem349520 A B) (@lem349519 A B lt2 g f)). Qed.
Lemma lem349522 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem349523 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1089 A B lt2 g f) = (term1085 A B lt2 g f).
Proof. exact (MK_COMB (@lem349522 A lt2) (@lem349521 A B lt2 g f)). Qed.
Lemma lem349524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349525 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1094 A B lt2 g f) = (term1095 A B lt2 g f).
Proof. exact (MK_COMB (@lem349524) (@lem349523 A B lt2 g f)). Qed.
Lemma lem349526 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (x : type110 A B) (f : type108 A B) : (term1091 A B lt2 g f x) = (term1056 A B lt2 g x f).
Proof. exact (eq_refl (term1091 A B lt2 g f x)). Qed.
Lemma lem349527 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term524 A lt2).
Proof. exact (eq_refl (term524 A lt2)). Qed.
Lemma lem349528 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (x : type110 A B) (f : type108 A B) : (term1096 A B lt2 g f x) = (term1097 A B lt2 g x f).
Proof. exact (MK_COMB (@lem349527 A lt2) (@lem349526 A B lt2 g x f)). Qed.
Lemma lem349529 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1098 A B lt2 g f) = (term1099 A B lt2 g f).
Proof. exact (fun_ext (fun x : type110 A B => @lem349528 A B lt2 g x f)). Qed.
Lemma lem349530 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem349531 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1090 A B lt2 g f) = (term1100 A B lt2 g f).
Proof. exact (MK_COMB (@lem349530 A B) (@lem349529 A B lt2 g f)). Qed.
Lemma lem349532 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : ((term1089 A B lt2 g f) = (term1090 A B lt2 g f)) = ((term1085 A B lt2 g f) = (term1100 A B lt2 g f)).
Proof. exact (MK_COMB (@lem349525 A B lt2 g f) (@lem349531 A B lt2 g f)). Qed.
Lemma lem349533 {A B : Type'} (lt2 : type1402 A) (g : type108 A B) (f : type108 A B) : (term1085 A B lt2 g f) = (term1100 A B lt2 g f).
Proof. exact (EQ_MP (@lem349532 A B lt2 g f) (@lem349517 A B lt2 g f)). Qed.
Lemma lem349534 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1087 A B lt2 f) = (term1101 A B lt2 f).
Proof. exact (fun_ext (fun g : type108 A B => @lem349533 A B lt2 g f)). Qed.
Lemma lem349535 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349536 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1088 A B lt2 f) = (term1102 A B lt2 f).
Proof. exact (MK_COMB (@lem349535 A B) (@lem349534 A B lt2 f)). Qed.
Lemma lem349537 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1073 A B lt2 f) = (term1102 A B lt2 f).
Proof. exact (TRANS (@lem349513 A B lt2 f) (@lem349536 A B lt2 f)). Qed.
Lemma lem349538 {A B : Type'} (lt2 : type1402 A) : (term1075 A B lt2) = (term1103 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem349537 A B lt2 f)). Qed.
Lemma lem349539 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349540 {A B : Type'} (lt2 : type1402 A) : (term1076 A B lt2) = (term1104 A B lt2).
Proof. exact (MK_COMB (@lem349539 A B) (@lem349538 A B lt2)). Qed.
Lemma lem349541 {A B : Type'} (lt2 : type1402 A) : (term1064 A B lt2) = (term1104 A B lt2).
Proof. exact (TRANS (@lem349493 A B lt2) (@lem349540 A B lt2)). Qed.
Lemma lem349542 {A B : Type'} (lt2 : type1402 A) : (term953 A B lt2) = (term1104 A B lt2).
Proof. exact (TRANS (@lem349473 A B lt2) (@lem349541 A B lt2)). Qed.
Lemma lem349543 {A B : Type'} : (term954 A B) = (term1105 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem349542 A B lt2)). Qed.
Lemma lem349544 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem349545 {A B : Type'} : (term955 A B) = (term1106 A B).
Proof. exact (MK_COMB (@lem349544 A) (@lem349543 A B)). Qed.
Lemma lem349547 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem349548 {A B : Type'} (P : type406 A B) : (term846 A B P) = (term847 A B P).
Proof. exact (@lem349547 (type1402 A) (type108 A B) P). Qed.
Lemma lem349549 {A B : Type'} : (term1107 A B) = (term1108 A B).
Proof. exact (@lem349548 A B (term1109 A B)). Qed.
Lemma lem349550 {A B : Type'} (lt2 : type1402 A) : (term1110 A B lt2) = (term1103 A B lt2).
Proof. exact (eq_refl (term1110 A B lt2)). Qed.
Lemma lem349551 {A B : Type'} (f : type108 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem349552 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1111 A B lt2 f) = (term1112 A B lt2 f).
Proof. exact (MK_COMB (@lem349550 A B lt2) (@lem349551 A B f)). Qed.
Lemma lem349553 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1112 A B lt2 f) = (term1102 A B lt2 f).
Proof. exact (eq_refl (term1112 A B lt2 f)). Qed.
Lemma lem349554 {A B : Type'} (lt2 : type1402 A) (f : type108 A B) : (term1111 A B lt2 f) = (term1102 A B lt2 f).
Proof. exact (TRANS (@lem349552 A B lt2 f) (@lem349553 A B lt2 f)). Qed.
Lemma lem349555 {A B : Type'} (lt2 : type1402 A) : (term1113 A B lt2) = (term1103 A B lt2).
Proof. exact (fun_ext (fun f : type108 A B => @lem349554 A B lt2 f)). Qed.
Lemma lem349556 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349557 {A B : Type'} (lt2 : type1402 A) : (term1114 A B lt2) = (term1104 A B lt2).
Proof. exact (MK_COMB (@lem349556 A B) (@lem349555 A B lt2)). Qed.
Lemma lem349558 {A B : Type'} : (term1115 A B) = (term1105 A B).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem349557 A B lt2)). Qed.
Lemma lem349559 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem349560 {A B : Type'} : (term1107 A B) = (term1106 A B).
Proof. exact (MK_COMB (@lem349559 A) (@lem349558 A B)). Qed.
Lemma lem349561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349562 {A B : Type'} : (term1116 A B) = (term1117 A B).
Proof. exact (MK_COMB (@lem349561) (@lem349560 A B)). Qed.
Lemma lem349563 {A B : Type'} (lt2 : type1402 A) : (term1110 A B lt2) = (term1103 A B lt2).
Proof. exact (eq_refl (term1110 A B lt2)). Qed.
Lemma lem349564 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (f lt2) = (f lt2).
Proof. exact (eq_refl (f lt2)). Qed.
Lemma lem349565 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term1118 A B f lt2) = (term1119 A B f lt2).
Proof. exact (MK_COMB (@lem349563 A B lt2) (@lem349564 A B f lt2)). Qed.
Lemma lem349566 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term1119 A B f lt2) = (term1120 A B f lt2).
Proof. exact (eq_refl (term1119 A B f lt2)). Qed.
Lemma lem349567 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term1118 A B f lt2) = (term1120 A B f lt2).
Proof. exact (TRANS (@lem349565 A B f lt2) (@lem349566 A B f lt2)). Qed.
Lemma lem349568 {A B : Type'} (f : type409 A B) : (term1121 A B f) = (term1122 A B f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem349567 A B f lt2)). Qed.
Lemma lem349569 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem349570 {A B : Type'} (f : type409 A B) : (term1123 A B f) = (term1124 A B f).
Proof. exact (MK_COMB (@lem349569 A) (@lem349568 A B f)). Qed.
Lemma lem349571 {A B : Type'} : (term1125 A B) = (term1126 A B).
Proof. exact (fun_ext (fun f : type409 A B => @lem349570 A B f)). Qed.
Lemma lem349572 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349573 {A B : Type'} : (term1108 A B) = (term1127 A B).
Proof. exact (MK_COMB (@lem349572 A B) (@lem349571 A B)). Qed.
Lemma lem349574 {A B : Type'} : ((term1107 A B) = (term1108 A B)) = ((term1106 A B) = (term1127 A B)).
Proof. exact (MK_COMB (@lem349562 A B) (@lem349573 A B)). Qed.
Lemma lem349575 {A B : Type'} : (term1106 A B) = (term1127 A B).
Proof. exact (EQ_MP (@lem349574 A B) (@lem349549 A B)). Qed.
Lemma lem349577 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem349578 {A B : Type'} (P : type406 A B) : (term846 A B P) = (term847 A B P).
Proof. exact (@lem349577 (type1402 A) (type108 A B) P). Qed.
Lemma lem349579 {A B : Type'} (f : type409 A B) : (term1128 A B f) = (term1129 A B f).
Proof. exact (@lem349578 A B (term1130 A B f)). Qed.
Lemma lem349580 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term1131 A B f lt2) = (term1132 A B f lt2).
Proof. exact (eq_refl (term1131 A B f lt2)). Qed.
Lemma lem349581 {A B : Type'} (g : type108 A B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem349582 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (g : type108 A B) : (term1133 A B f lt2 g) = (term1134 A B f lt2 g).
Proof. exact (MK_COMB (@lem349580 A B f lt2) (@lem349581 A B g)). Qed.
Lemma lem349583 {A B : Type'} (g : type108 A B) (f : type409 A B) (lt2 : type1402 A) : (term1134 A B f lt2 g) = (term1135 A B g f lt2).
Proof. exact (eq_refl (term1134 A B f lt2 g)). Qed.
Lemma lem349584 {A B : Type'} (g : type108 A B) (f : type409 A B) (lt2 : type1402 A) : (term1133 A B f lt2 g) = (term1135 A B g f lt2).
Proof. exact (TRANS (@lem349582 A B f lt2 g) (@lem349583 A B g f lt2)). Qed.
Lemma lem349585 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term1136 A B f lt2) = (term1132 A B f lt2).
Proof. exact (fun_ext (fun g : type108 A B => @lem349584 A B g f lt2)). Qed.
Lemma lem349586 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A -> B)) = (@ex (((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349587 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term1137 A B f lt2) = (term1120 A B f lt2).
Proof. exact (MK_COMB (@lem349586 A B) (@lem349585 A B f lt2)). Qed.
Lemma lem349588 {A B : Type'} (f : type409 A B) : (term1138 A B f) = (term1122 A B f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem349587 A B f lt2)). Qed.
Lemma lem349589 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem349590 {A B : Type'} (f : type409 A B) : (term1128 A B f) = (term1124 A B f).
Proof. exact (MK_COMB (@lem349589 A) (@lem349588 A B f)). Qed.
Lemma lem349591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349592 {A B : Type'} (f : type409 A B) : (term1139 A B f) = (term1140 A B f).
Proof. exact (MK_COMB (@lem349591) (@lem349590 A B f)). Qed.
Lemma lem349593 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (term1131 A B f lt2) = (term1132 A B f lt2).
Proof. exact (eq_refl (term1131 A B f lt2)). Qed.
Lemma lem349594 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) : (g lt2) = (g lt2).
Proof. exact (eq_refl (g lt2)). Qed.
Lemma lem349595 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) : (term1141 A B f g lt2) = (term1142 A B f g lt2).
Proof. exact (MK_COMB (@lem349593 A B f lt2) (@lem349594 A B g lt2)). Qed.
Lemma lem349596 {A B : Type'} (g : type409 A B) (f : type409 A B) (lt2 : type1402 A) : (term1142 A B f g lt2) = (term1143 A B g f lt2).
Proof. exact (eq_refl (term1142 A B f g lt2)). Qed.
Lemma lem349597 {A B : Type'} (g : type409 A B) (f : type409 A B) (lt2 : type1402 A) : (term1141 A B f g lt2) = (term1143 A B g f lt2).
Proof. exact (TRANS (@lem349595 A B f g lt2) (@lem349596 A B g f lt2)). Qed.
Lemma lem349598 {A B : Type'} (g : type409 A B) (f : type409 A B) : (term1144 A B f g) = (term1145 A B g f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem349597 A B g f lt2)). Qed.
Lemma lem349599 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem349600 {A B : Type'} (g : type409 A B) (f : type409 A B) : (term1146 A B f g) = (term1147 A B g f).
Proof. exact (MK_COMB (@lem349599 A) (@lem349598 A B g f)). Qed.
Lemma lem349601 {A B : Type'} (f : type409 A B) : (term1148 A B f) = (term1149 A B f).
Proof. exact (fun_ext (fun g : type409 A B => @lem349600 A B g f)). Qed.
Lemma lem349602 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349603 {A B : Type'} (f : type409 A B) : (term1129 A B f) = (term1150 A B f).
Proof. exact (MK_COMB (@lem349602 A B) (@lem349601 A B f)). Qed.
Lemma lem349604 {A B : Type'} (f : type409 A B) : ((term1128 A B f) = (term1129 A B f)) = ((term1124 A B f) = (term1150 A B f)).
Proof. exact (MK_COMB (@lem349592 A B f) (@lem349603 A B f)). Qed.
Lemma lem349605 {A B : Type'} (f : type409 A B) : (term1124 A B f) = (term1150 A B f).
Proof. exact (EQ_MP (@lem349604 A B f) (@lem349579 A B f)). Qed.
Lemma lem349607 {A B : Type'} (P : type1413 A B) : (term182 A B P) = (term183 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem349608 {A B : Type'} (P : type407 A B) : (term892 A B P) = (term893 A B P).
Proof. exact (@lem349607 (type1402 A) (type110 A B) P). Qed.
Lemma lem349609 {A B : Type'} (g : type409 A B) (f : type409 A B) : (term1151 A B g f) = (term1152 A B g f).
Proof. exact (@lem349608 A B (term1153 A B g f)). Qed.
Lemma lem349610 {A B : Type'} (g : type409 A B) (f : type409 A B) (lt2 : type1402 A) : (term1154 A B g f lt2) = (term1155 A B g f lt2).
Proof. exact (eq_refl (term1154 A B g f lt2)). Qed.
Lemma lem349611 {A B : Type'} (x : type110 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem349612 {A B : Type'} (g : type409 A B) (f : type409 A B) (lt2 : type1402 A) (x : type110 A B) : (term1156 A B g f lt2 x) = (term1157 A B g f lt2 x).
Proof. exact (MK_COMB (@lem349610 A B g f lt2) (@lem349611 A B x)). Qed.
Lemma lem349613 {A B : Type'} (g : type409 A B) (x : type110 A B) (f : type409 A B) (lt2 : type1402 A) : (term1157 A B g f lt2 x) = (term1158 A B g x f lt2).
Proof. exact (eq_refl (term1157 A B g f lt2 x)). Qed.
Lemma lem349614 {A B : Type'} (g : type409 A B) (x : type110 A B) (f : type409 A B) (lt2 : type1402 A) : (term1156 A B g f lt2 x) = (term1158 A B g x f lt2).
Proof. exact (TRANS (@lem349612 A B g f lt2 x) (@lem349613 A B g x f lt2)). Qed.
Lemma lem349615 {A B : Type'} (g : type409 A B) (f : type409 A B) (lt2 : type1402 A) : (term1159 A B g f lt2) = (term1155 A B g f lt2).
Proof. exact (fun_ext (fun x : type110 A B => @lem349614 A B g x f lt2)). Qed.
Lemma lem349616 {A B : Type'} : (@ex (((A -> B) -> A -> B) -> A)) = (@ex (((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex (((A -> B) -> A -> B) -> A))). Qed.
Lemma lem349617 {A B : Type'} (g : type409 A B) (f : type409 A B) (lt2 : type1402 A) : (term1160 A B g f lt2) = (term1143 A B g f lt2).
Proof. exact (MK_COMB (@lem349616 A B) (@lem349615 A B g f lt2)). Qed.
Lemma lem349618 {A B : Type'} (g : type409 A B) (f : type409 A B) : (term1161 A B g f) = (term1145 A B g f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem349617 A B g f lt2)). Qed.
Lemma lem349619 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem349620 {A B : Type'} (g : type409 A B) (f : type409 A B) : (term1151 A B g f) = (term1147 A B g f).
Proof. exact (MK_COMB (@lem349619 A) (@lem349618 A B g f)). Qed.
Lemma lem349621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem349622 {A B : Type'} (g : type409 A B) (f : type409 A B) : (term1162 A B g f) = (term1163 A B g f).
Proof. exact (MK_COMB (@lem349621) (@lem349620 A B g f)). Qed.
Lemma lem349623 {A B : Type'} (g : type409 A B) (f : type409 A B) (lt2 : type1402 A) : (term1154 A B g f lt2) = (term1155 A B g f lt2).
Proof. exact (eq_refl (term1154 A B g f lt2)). Qed.
Lemma lem349624 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) : (x lt2) = (x lt2).
Proof. exact (eq_refl (x lt2)). Qed.
Lemma lem349625 {A B : Type'} (g : type409 A B) (f : type409 A B) (x : type410 A B) (lt2 : type1402 A) : (term1164 A B g f x lt2) = (term1165 A B g f x lt2).
Proof. exact (MK_COMB (@lem349623 A B g f lt2) (@lem349624 A B x lt2)). Qed.
Lemma lem349626 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1165 A B g f x lt2) = (term1166 A B g x f lt2).
Proof. exact (eq_refl (term1165 A B g f x lt2)). Qed.
Lemma lem349627 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1164 A B g f x lt2) = (term1166 A B g x f lt2).
Proof. exact (TRANS (@lem349625 A B g f x lt2) (@lem349626 A B g x f lt2)). Qed.
Lemma lem349628 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) : (term1167 A B g f x) = (term1168 A B g x f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem349627 A B g x f lt2)). Qed.
Lemma lem349629 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem349630 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) : (term1169 A B g f x) = (term1170 A B g x f).
Proof. exact (MK_COMB (@lem349629 A) (@lem349628 A B g x f)). Qed.
Lemma lem349631 {A B : Type'} (g : type409 A B) (f : type409 A B) : (term1171 A B g f) = (term1172 A B g f).
Proof. exact (fun_ext (fun x : type410 A B => @lem349630 A B g x f)). Qed.
Lemma lem349632 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A))). Qed.
Lemma lem349633 {A B : Type'} (g : type409 A B) (f : type409 A B) : (term1152 A B g f) = (term1173 A B g f).
Proof. exact (MK_COMB (@lem349632 A B) (@lem349631 A B g f)). Qed.
Lemma lem349634 {A B : Type'} (g : type409 A B) (f : type409 A B) : ((term1151 A B g f) = (term1152 A B g f)) = ((term1147 A B g f) = (term1173 A B g f)).
Proof. exact (MK_COMB (@lem349622 A B g f) (@lem349633 A B g f)). Qed.
Lemma lem349635 {A B : Type'} (g : type409 A B) (f : type409 A B) : (term1147 A B g f) = (term1173 A B g f).
Proof. exact (EQ_MP (@lem349634 A B g f) (@lem349609 A B g f)). Qed.
Lemma lem349636 {A B : Type'} (f : type409 A B) : (term1149 A B f) = (term1174 A B f).
Proof. exact (fun_ext (fun g : type409 A B => @lem349635 A B g f)). Qed.
Lemma lem349637 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349638 {A B : Type'} (f : type409 A B) : (term1150 A B f) = (term1175 A B f).
Proof. exact (MK_COMB (@lem349637 A B) (@lem349636 A B f)). Qed.
Lemma lem349639 {A B : Type'} (f : type409 A B) : (term1124 A B f) = (term1175 A B f).
Proof. exact (TRANS (@lem349605 A B f) (@lem349638 A B f)). Qed.
Lemma lem349640 {A B : Type'} : (term1126 A B) = (term1176 A B).
Proof. exact (fun_ext (fun f : type409 A B => @lem349639 A B f)). Qed.
Lemma lem349641 {A B : Type'} : (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)) = (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B))). Qed.
Lemma lem349642 {A B : Type'} : (term1127 A B) = (term1177 A B).
Proof. exact (MK_COMB (@lem349641 A B) (@lem349640 A B)). Qed.
Lemma lem349643 {A B : Type'} : (term1106 A B) = (term1177 A B).
Proof. exact (TRANS (@lem349575 A B) (@lem349642 A B)). Qed.
Lemma lem349645 {A B : Type'} : (term955 A B) = (term1177 A B).
Proof. exact (TRANS (@lem349545 A B) (@lem349643 A B)). Qed.
Lemma lem349646 {A B : Type'} : (term7 A B) = (term1177 A B).
Proof. exact (TRANS (@lem349077 A B) (@lem349645 A B)). Qed.
Lemma lem349647 {A B : Type'} (h1 : term7 A B) : term1177 A B.
Proof. exact (EQ_MP (@lem349646 A B) (@lem347108 A B h1)). Qed.
Lemma lem349648 {A B : Type'} (f : type409 A B) (h1 : term1175 A B f) : term1175 A B f.
Proof. exact (h1). Qed.
Lemma lem349649 {A B : Type'} (g : type409 A B) (f : type409 A B) (h1 : term1173 A B g f) : term1173 A B g f.
Proof. exact (h1). Qed.
Lemma lem349650 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1170 A B g x f.
Proof. exact (h1). Qed.
Lemma lem349651 {A B : Type'} (f' : type409 A B) (h1 : term945 A B f') : term945 A B f'.
Proof. exact (h1). Qed.
Lemma lem349652 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (h1 : term943 A B f' g') : term943 A B f' g'.
Proof. exact (h1). Qed.
Lemma lem349653 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (h1 : term941 A B f' g' x') : term941 A B f' g' x'.
Proof. exact (h1). Qed.
Lemma lem349654 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term938 A B f' g' x' x''.
Proof. exact (h1). Qed.
Lemma lem349655 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term470 A B lt2 H) : term470 A B lt2 H.
Proof. exact (h1). Qed.
Lemma lem349656 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) (h1 : term468 A B lt2 z H) : term468 A B lt2 z H.
Proof. exact (h1). Qed.
Lemma lem349657 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (h1 : term466 A B lt2 z x''' H) : term466 A B lt2 z x''' H.
Proof. exact (h1). Qed.
Lemma lem349658 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f'' : A -> B) (h1 : term464 A B lt2 z x''' H f'') : term464 A B lt2 z x''' H f''.
Proof. exact (h1). Qed.
Lemma lem349659 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term461 A B lt2 z x''' H f''' f''.
Proof. exact (h1). Qed.
Lemma lem349660 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem349669 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349670 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349669 (type1402 A) (type108 A B) f x). Qed.
Lemma lem349671 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (f lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2).
Proof. exact (@lem349670 A B f lt2). Qed.
Lemma lem349672 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349673 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2 H).
Proof. exact (MK_COMB (@lem349671 A B f lt2) (@lem349672 A B H)). Qed.
Lemma lem349675 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349676 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349675 (type549 A B) (A -> B) f x). Qed.
Lemma lem349677 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2 H) = (term1178 A B f lt2 H).
Proof. exact (@lem349676 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2) H). Qed.
Lemma lem349678 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f lt2 H) = (term1178 A B f lt2 H).
Proof. exact (TRANS (@lem349673 A B f lt2 H) (@lem349677 A B f lt2 H)). Qed.
Lemma lem349679 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem349680 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (f lt2 H x) = (term1179 A B f lt2 H x).
Proof. exact (MK_COMB (@lem349678 A B f lt2 H) (@lem349679 A x)). Qed.
Lemma lem349682 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349683 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem349682 A B f x). Qed.
Lemma lem349684 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (term1179 A B f lt2 H x) = (term1180 A B f lt2 H x).
Proof. exact (@lem349683 A B (term1178 A B f lt2 H) x). Qed.
Lemma lem349686 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (f lt2 H x) = (term1180 A B f lt2 H x).
Proof. exact (TRANS (@lem349680 A B f lt2 H x) (@lem349684 A B f lt2 H x)). Qed.
Lemma lem349687 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349694 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349695 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349694 (type1402 A) (type108 A B) f x). Qed.
Lemma lem349696 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (f lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2).
Proof. exact (@lem349695 A B f lt2). Qed.
Lemma lem349697 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349698 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2 H).
Proof. exact (MK_COMB (@lem349696 A B f lt2) (@lem349697 A B H)). Qed.
Lemma lem349700 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349701 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349700 (type549 A B) (A -> B) f x). Qed.
Lemma lem349702 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2 H) = (term1178 A B f lt2 H).
Proof. exact (@lem349701 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2) H). Qed.
Lemma lem349704 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f lt2 H) = (term1178 A B f lt2 H).
Proof. exact (TRANS (@lem349698 A B f lt2 H) (@lem349702 A B f lt2 H)). Qed.
Lemma lem349705 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem349706 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1181 A B f lt2 H) = (term1182 A B f lt2 H).
Proof. exact (MK_COMB (@lem349687 A B H) (@lem349704 A B f lt2 H)). Qed.
Lemma lem349707 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (term1183 A B f lt2 H x) = (term1184 A B f lt2 H x).
Proof. exact (MK_COMB (@lem349706 A B f lt2 H) (@lem349705 A x)). Qed.
Lemma lem349709 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349710 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem349709 (A -> B) (A -> B) f x). Qed.
Lemma lem349711 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1182 A B f lt2 H) = (term1185 A B f lt2 H).
Proof. exact (@lem349710 A B H (term1178 A B f lt2 H)). Qed.
Lemma lem349712 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem349713 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (term1184 A B f lt2 H x) = (term1186 A B f lt2 H x).
Proof. exact (MK_COMB (@lem349711 A B f lt2 H) (@lem349712 A x)). Qed.
Lemma lem349715 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349716 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem349715 A B f x). Qed.
Lemma lem349717 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (term1186 A B f lt2 H x) = (term1187 A B f lt2 H x).
Proof. exact (@lem349716 A B (term1185 A B f lt2 H) x). Qed.
Lemma lem349718 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (term1184 A B f lt2 H x) = (term1187 A B f lt2 H x).
Proof. exact (TRANS (@lem349713 A B f lt2 H x) (@lem349717 A B f lt2 H x)). Qed.
Lemma lem349719 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (term1183 A B f lt2 H x) = (term1187 A B f lt2 H x).
Proof. exact (TRANS (@lem349707 A B f lt2 H x) (@lem349718 A B f lt2 H x)). Qed.
Lemma lem349720 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (term1188 A B f lt2 H x) = (term1189 A B f lt2 H x).
Proof. exact (MK_COMB (@lem349660 B) (@lem349686 A B f lt2 H x)). Qed.
Lemma lem349721 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : ((f lt2 H x) = (term1183 A B f lt2 H x)) = ((term1180 A B f lt2 H x) = (term1187 A B f lt2 H x)).
Proof. exact (MK_COMB (@lem349720 A B f lt2 H x) (@lem349719 A B f lt2 H x)). Qed.
Lemma lem349722 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1190 A B f lt2 H) = (term1191 A B f lt2 H).
Proof. exact (fun_ext (fun x : A => @lem349721 A B f lt2 H x)). Qed.
Lemma lem349723 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem349724 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1192 A B f lt2 H) = (term1193 A B f lt2 H).
Proof. exact (MK_COMB (@lem349723 A) (@lem349722 A B f lt2 H)). Qed.
Lemma lem349725 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem349726 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem349727 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349734 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349735 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349734 (type1402 A) (type108 A B) f x). Qed.
Lemma lem349736 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (f lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2).
Proof. exact (@lem349735 A B f lt2). Qed.
Lemma lem349737 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349738 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2 H).
Proof. exact (MK_COMB (@lem349736 A B f lt2) (@lem349737 A B H)). Qed.
Lemma lem349740 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349741 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349740 (type549 A B) (A -> B) f x). Qed.
Lemma lem349742 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2 H) = (term1178 A B f lt2 H).
Proof. exact (@lem349741 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2) H). Qed.
Lemma lem349744 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f lt2 H) = (term1178 A B f lt2 H).
Proof. exact (TRANS (@lem349738 A B f lt2 H) (@lem349742 A B f lt2 H)). Qed.
Lemma lem349751 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349752 {A B : Type'} (f : type410 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem349751 (type1402 A) (type110 A B) f x). Qed.
Lemma lem349753 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) : (x lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2).
Proof. exact (@lem349752 A B x lt2). Qed.
Lemma lem349754 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349755 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2 H).
Proof. exact (MK_COMB (@lem349753 A B x lt2) (@lem349754 A B H)). Qed.
Lemma lem349757 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349758 {A B : Type'} (f : type110 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem349757 (type549 A B) A f x). Qed.
Lemma lem349759 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2 H) = (term1194 A B x lt2 H).
Proof. exact (@lem349758 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2) H). Qed.
Lemma lem349761 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x lt2 H) = (term1194 A B x lt2 H).
Proof. exact (TRANS (@lem349755 A B x lt2 H) (@lem349759 A B x lt2 H)). Qed.
Lemma lem349762 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1181 A B f lt2 H) = (term1182 A B f lt2 H).
Proof. exact (MK_COMB (@lem349727 A B H) (@lem349744 A B f lt2 H)). Qed.
Lemma lem349763 {A B : Type'} (f : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1195 A B f x lt2 H) = (term1196 A B f x lt2 H).
Proof. exact (MK_COMB (@lem349762 A B f lt2 H) (@lem349761 A B x lt2 H)). Qed.
Lemma lem349765 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349766 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem349765 (A -> B) (A -> B) f x). Qed.
Lemma lem349767 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1182 A B f lt2 H) = (term1185 A B f lt2 H).
Proof. exact (@lem349766 A B H (term1178 A B f lt2 H)). Qed.
Lemma lem349768 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1194 A B x lt2 H) = (term1194 A B x lt2 H).
Proof. exact (eq_refl (term1194 A B x lt2 H)). Qed.
Lemma lem349769 {A B : Type'} (f : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1196 A B f x lt2 H) = (term1197 A B f x lt2 H).
Proof. exact (MK_COMB (@lem349767 A B f lt2 H) (@lem349768 A B x lt2 H)). Qed.
Lemma lem349771 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349772 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem349771 A B f x). Qed.
Lemma lem349773 {A B : Type'} (f : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1197 A B f x lt2 H) = (term1198 A B f x lt2 H).
Proof. exact (@lem349772 A B (term1185 A B f lt2 H) (term1194 A B x lt2 H)). Qed.
Lemma lem349774 {A B : Type'} (f : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1196 A B f x lt2 H) = (term1198 A B f x lt2 H).
Proof. exact (TRANS (@lem349769 A B f x lt2 H) (@lem349773 A B f x lt2 H)). Qed.
Lemma lem349775 {A B : Type'} (f : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1195 A B f x lt2 H) = (term1198 A B f x lt2 H).
Proof. exact (TRANS (@lem349763 A B f x lt2 H) (@lem349774 A B f x lt2 H)). Qed.
Lemma lem349776 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349783 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349784 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349783 (type1402 A) (type108 A B) f x). Qed.
Lemma lem349785 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) : (g lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g lt2).
Proof. exact (@lem349784 A B g lt2). Qed.
Lemma lem349786 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349787 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (g lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g lt2 H).
Proof. exact (MK_COMB (@lem349785 A B g lt2) (@lem349786 A B H)). Qed.
Lemma lem349789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349790 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349789 (type549 A B) (A -> B) f x). Qed.
Lemma lem349791 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g lt2 H) = (term1178 A B g lt2 H).
Proof. exact (@lem349790 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g lt2) H). Qed.
Lemma lem349793 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (g lt2 H) = (term1178 A B g lt2 H).
Proof. exact (TRANS (@lem349787 A B g lt2 H) (@lem349791 A B g lt2 H)). Qed.
Lemma lem349800 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349801 {A B : Type'} (f : type410 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem349800 (type1402 A) (type110 A B) f x). Qed.
Lemma lem349802 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) : (x lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2).
Proof. exact (@lem349801 A B x lt2). Qed.
Lemma lem349803 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349804 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2 H).
Proof. exact (MK_COMB (@lem349802 A B x lt2) (@lem349803 A B H)). Qed.
Lemma lem349806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349807 {A B : Type'} (f : type110 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem349806 (type549 A B) A f x). Qed.
Lemma lem349808 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2 H) = (term1194 A B x lt2 H).
Proof. exact (@lem349807 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2) H). Qed.
Lemma lem349810 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x lt2 H) = (term1194 A B x lt2 H).
Proof. exact (TRANS (@lem349804 A B x lt2 H) (@lem349808 A B x lt2 H)). Qed.
Lemma lem349811 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1181 A B g lt2 H) = (term1182 A B g lt2 H).
Proof. exact (MK_COMB (@lem349776 A B H) (@lem349793 A B g lt2 H)). Qed.
Lemma lem349812 {A B : Type'} (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1195 A B g x lt2 H) = (term1196 A B g x lt2 H).
Proof. exact (MK_COMB (@lem349811 A B g lt2 H) (@lem349810 A B x lt2 H)). Qed.
Lemma lem349814 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349815 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem349814 (A -> B) (A -> B) f x). Qed.
Lemma lem349816 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1182 A B g lt2 H) = (term1185 A B g lt2 H).
Proof. exact (@lem349815 A B H (term1178 A B g lt2 H)). Qed.
Lemma lem349817 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1194 A B x lt2 H) = (term1194 A B x lt2 H).
Proof. exact (eq_refl (term1194 A B x lt2 H)). Qed.
Lemma lem349818 {A B : Type'} (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1196 A B g x lt2 H) = (term1197 A B g x lt2 H).
Proof. exact (MK_COMB (@lem349816 A B g lt2 H) (@lem349817 A B x lt2 H)). Qed.
Lemma lem349820 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349821 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem349820 A B f x). Qed.
Lemma lem349822 {A B : Type'} (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1197 A B g x lt2 H) = (term1198 A B g x lt2 H).
Proof. exact (@lem349821 A B (term1185 A B g lt2 H) (term1194 A B x lt2 H)). Qed.
Lemma lem349823 {A B : Type'} (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1196 A B g x lt2 H) = (term1198 A B g x lt2 H).
Proof. exact (TRANS (@lem349818 A B g x lt2 H) (@lem349822 A B g x lt2 H)). Qed.
Lemma lem349824 {A B : Type'} (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1195 A B g x lt2 H) = (term1198 A B g x lt2 H).
Proof. exact (TRANS (@lem349812 A B g x lt2 H) (@lem349823 A B g x lt2 H)). Qed.
Lemma lem349825 {A B : Type'} (f : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1199 A B f x lt2 H) = (term1200 A B f x lt2 H).
Proof. exact (MK_COMB (@lem349726 B) (@lem349775 A B f x lt2 H)). Qed.
Lemma lem349826 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1195 A B f x lt2 H) = (term1195 A B g x lt2 H)) = ((term1198 A B f x lt2 H) = (term1198 A B g x lt2 H)).
Proof. exact (MK_COMB (@lem349825 A B f x lt2 H) (@lem349824 A B g x lt2 H)). Qed.
Lemma lem349827 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1201 A B f g x lt2 H) = (term1202 A B f g x lt2 H).
Proof. exact (MK_COMB (@lem349725) (@lem349826 A B f g x lt2 H)). Qed.
Lemma lem349828 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem349837 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349838 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349837 (type1402 A) (type108 A B) f x). Qed.
Lemma lem349839 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) : (f lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2).
Proof. exact (@lem349838 A B f lt2). Qed.
Lemma lem349840 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349841 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2 H).
Proof. exact (MK_COMB (@lem349839 A B f lt2) (@lem349840 A B H)). Qed.
Lemma lem349843 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349844 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349843 (type549 A B) (A -> B) f x). Qed.
Lemma lem349845 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2 H) = (term1178 A B f lt2 H).
Proof. exact (@lem349844 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f lt2) H). Qed.
Lemma lem349846 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f lt2 H) = (term1178 A B f lt2 H).
Proof. exact (TRANS (@lem349841 A B f lt2 H) (@lem349845 A B f lt2 H)). Qed.
Lemma lem349847 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem349848 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (f lt2 H z) = (term1179 A B f lt2 H z).
Proof. exact (MK_COMB (@lem349846 A B f lt2 H) (@lem349847 A z)). Qed.
Lemma lem349850 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349851 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem349850 A B f x). Qed.
Lemma lem349852 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1179 A B f lt2 H z) = (term1180 A B f lt2 H z).
Proof. exact (@lem349851 A B (term1178 A B f lt2 H) z). Qed.
Lemma lem349854 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (f lt2 H z) = (term1180 A B f lt2 H z).
Proof. exact (TRANS (@lem349848 A B f lt2 H z) (@lem349852 A B f lt2 H z)). Qed.
Lemma lem349863 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349864 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349863 (type1402 A) (type108 A B) f x). Qed.
Lemma lem349865 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) : (g lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g lt2).
Proof. exact (@lem349864 A B g lt2). Qed.
Lemma lem349866 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349867 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (g lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g lt2 H).
Proof. exact (MK_COMB (@lem349865 A B g lt2) (@lem349866 A B H)). Qed.
Lemma lem349869 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349870 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem349869 (type549 A B) (A -> B) f x). Qed.
Lemma lem349871 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g lt2 H) = (term1178 A B g lt2 H).
Proof. exact (@lem349870 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g lt2) H). Qed.
Lemma lem349872 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (g lt2 H) = (term1178 A B g lt2 H).
Proof. exact (TRANS (@lem349867 A B g lt2 H) (@lem349871 A B g lt2 H)). Qed.
Lemma lem349873 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem349874 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (g lt2 H z) = (term1179 A B g lt2 H z).
Proof. exact (MK_COMB (@lem349872 A B g lt2 H) (@lem349873 A z)). Qed.
Lemma lem349876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349877 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem349876 A B f x). Qed.
Lemma lem349878 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1179 A B g lt2 H z) = (term1180 A B g lt2 H z).
Proof. exact (@lem349877 A B (term1178 A B g lt2 H) z). Qed.
Lemma lem349880 {A B : Type'} (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (g lt2 H z) = (term1180 A B g lt2 H z).
Proof. exact (TRANS (@lem349874 A B g lt2 H z) (@lem349878 A B g lt2 H z)). Qed.
Lemma lem349881 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1188 A B f lt2 H z) = (term1189 A B f lt2 H z).
Proof. exact (MK_COMB (@lem349828 B) (@lem349854 A B f lt2 H z)). Qed.
Lemma lem349882 {A B : Type'} (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : ((f lt2 H z) = (g lt2 H z)) = ((term1180 A B f lt2 H z) = (term1180 A B g lt2 H z)).
Proof. exact (MK_COMB (@lem349881 A B f lt2 H z) (@lem349880 A B g lt2 H z)). Qed.
Lemma lem349883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem349892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349893 {A B : Type'} (f : type410 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem349892 (type1402 A) (type110 A B) f x). Qed.
Lemma lem349894 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) : (x lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2).
Proof. exact (@lem349893 A B x lt2). Qed.
Lemma lem349895 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349896 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2 H).
Proof. exact (MK_COMB (@lem349894 A B x lt2) (@lem349895 A B H)). Qed.
Lemma lem349898 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349899 {A B : Type'} (f : type110 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem349898 (type549 A B) A f x). Qed.
Lemma lem349900 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2 H) = (term1194 A B x lt2 H).
Proof. exact (@lem349899 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x lt2) H). Qed.
Lemma lem349902 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x lt2 H) = (term1194 A B x lt2 H).
Proof. exact (TRANS (@lem349896 A B x lt2 H) (@lem349900 A B x lt2 H)). Qed.
Lemma lem349903 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem349904 {A B : Type'} (z : A) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1203 A B z x lt2 H) = (term1204 A B z x lt2 H).
Proof. exact (MK_COMB (@lem349903 A lt2 z) (@lem349902 A B x lt2 H)). Qed.
Lemma lem349906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349907 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem349906 A (A -> Prop) f x). Qed.
Lemma lem349908 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem349907 A lt2 z). Qed.
Lemma lem349909 {A B : Type'} (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1194 A B x lt2 H) = (term1194 A B x lt2 H).
Proof. exact (eq_refl (term1194 A B x lt2 H)). Qed.
Lemma lem349910 {A B : Type'} (z : A) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1204 A B z x lt2 H) = (term1205 A B z x lt2 H).
Proof. exact (MK_COMB (@lem349908 A lt2 z) (@lem349909 A B x lt2 H)). Qed.
Lemma lem349912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349913 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem349912 A Prop f x). Qed.
Lemma lem349914 {A B : Type'} (z : A) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1205 A B z x lt2 H) = (term1206 A B z x lt2 H).
Proof. exact (@lem349913 A (@I (A -> A -> Prop) lt2 z) (term1194 A B x lt2 H)). Qed.
Lemma lem349915 {A B : Type'} (z : A) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1204 A B z x lt2 H) = (term1206 A B z x lt2 H).
Proof. exact (TRANS (@lem349910 A B z x lt2 H) (@lem349914 A B z x lt2 H)). Qed.
Lemma lem349916 {A B : Type'} (z : A) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1203 A B z x lt2 H) = (term1206 A B z x lt2 H).
Proof. exact (TRANS (@lem349904 A B z x lt2 H) (@lem349915 A B z x lt2 H)). Qed.
Lemma lem349917 {A B : Type'} (z : A) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1207 A B z x lt2 H) = (term1208 A B z x lt2 H).
Proof. exact (MK_COMB (@lem349883) (@lem349916 A B z x lt2 H)). Qed.
Lemma lem349918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349919 {A B : Type'} (z : A) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1209 A B z x lt2 H) = (term1210 A B z x lt2 H).
Proof. exact (MK_COMB (@lem349918) (@lem349917 A B z x lt2 H)). Qed.
Lemma lem349920 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1211 A B x f g lt2 H z) = (term1212 A B x f g lt2 H z).
Proof. exact (MK_COMB (@lem349919 A B z x lt2 H) (@lem349882 A B f g lt2 H z)). Qed.
Lemma lem349921 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1213 A B x f g lt2 H) = (term1214 A B x f g lt2 H).
Proof. exact (fun_ext (fun z : A => @lem349920 A B x f g lt2 H z)). Qed.
Lemma lem349922 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem349923 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1215 A B x f g lt2 H) = (term1216 A B x f g lt2 H).
Proof. exact (MK_COMB (@lem349922 A) (@lem349921 A B x f g lt2 H)). Qed.
Lemma lem349924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem349925 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1217 A B x f g lt2 H) = (term1218 A B x f g lt2 H).
Proof. exact (MK_COMB (@lem349924) (@lem349923 A B x f g lt2 H)). Qed.
Lemma lem349926 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1219 A B f g x lt2 H) = (term1220 A B f g x lt2 H).
Proof. exact (MK_COMB (@lem349925 A B x f g lt2 H) (@lem349827 A B f g x lt2 H)). Qed.
Lemma lem349927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349928 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1221 A B f g x lt2 H) = (term1222 A B f g x lt2 H).
Proof. exact (MK_COMB (@lem349927) (@lem349926 A B f g x lt2 H)). Qed.
Lemma lem349929 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1223 A B g x f lt2 H) = (term1224 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem349928 A B f g x lt2 H) (@lem349724 A B f lt2 H)). Qed.
Lemma lem349930 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1225 A B g x f lt2) = (term1226 A B g x f lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem349929 A B g x f lt2 H)). Qed.
Lemma lem349931 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem349932 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1227 A B g x f lt2) = (term1228 A B g x f lt2).
Proof. exact (MK_COMB (@lem349931 A B) (@lem349930 A B g x f lt2)). Qed.
Lemma lem349933 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem349938 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349939 {A : Type'} (f : type421 A) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> Prop) f x).
Proof. exact (@lem349938 (type1402 A) Prop f x). Qed.
Lemma lem349941 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem349939 A (@WF A) lt2). Qed.
Lemma lem349942 {A : Type'} (lt2 : type1402 A) : (term787 A lt2) = (term1229 A lt2).
Proof. exact (MK_COMB (@lem349933) (@lem349941 A lt2)). Qed.
Lemma lem349943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem349944 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term1230 A lt2).
Proof. exact (MK_COMB (@lem349943) (@lem349942 A lt2)). Qed.
Lemma lem349945 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1166 A B g x f lt2) = (term1231 A B g x f lt2).
Proof. exact (MK_COMB (@lem349944 A lt2) (@lem349932 A B g x f lt2)). Qed.
Lemma lem349946 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) : (term1168 A B g x f) = (term1232 A B g x f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem349945 A B g x f lt2)). Qed.
Lemma lem349947 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem349948 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) : (term1170 A B g x f) = (term1233 A B g x f).
Proof. exact (MK_COMB (@lem349947 A) (@lem349946 A B g x f)). Qed.
Lemma lem349949 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1233 A B g x f.
Proof. exact (EQ_MP (@lem349948 A B g x f) (@lem349650 A B g x f h1)). Qed.
Lemma lem349954 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (f = g).
Proof. exact (eq_refl (f = g)). Qed.
Lemma lem349955 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem349956 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem349957 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem349968 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349969 {A B : Type'} (f : type408 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem349968 (type1402 A) (type106 A B) f x). Qed.
Lemma lem349970 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) : (x'' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2).
Proof. exact (@lem349969 A B x'' lt2). Qed.
Lemma lem349971 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem349972 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (x'' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2 H).
Proof. exact (MK_COMB (@lem349970 A B x'' lt2) (@lem349971 A B H)). Qed.
Lemma lem349974 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349975 {A B : Type'} (f : type106 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem349974 (type549 A B) (type522 A B) f x). Qed.
Lemma lem349976 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2 H) = (term1234 A B x'' lt2 H).
Proof. exact (@lem349975 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2) H). Qed.
Lemma lem349977 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (x'' lt2 H) = (term1234 A B x'' lt2 H).
Proof. exact (TRANS (@lem349972 A B x'' lt2 H) (@lem349976 A B x'' lt2 H)). Qed.
Lemma lem349978 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem349979 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (x'' lt2 H f) = (term1235 A B x'' lt2 H f).
Proof. exact (MK_COMB (@lem349977 A B x'' lt2 H) (@lem349978 A B f)). Qed.
Lemma lem349981 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349982 {A B : Type'} (f : type522 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem349981 (A -> B) (type569 A B) f x). Qed.
Lemma lem349983 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1235 A B x'' lt2 H f) = (term1236 A B x'' lt2 H f).
Proof. exact (@lem349982 A B (term1234 A B x'' lt2 H) f). Qed.
Lemma lem349984 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (x'' lt2 H f) = (term1236 A B x'' lt2 H f).
Proof. exact (TRANS (@lem349979 A B x'' lt2 H f) (@lem349983 A B x'' lt2 H f)). Qed.
Lemma lem349985 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem349986 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (x'' lt2 H f g) = (term1237 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem349984 A B x'' lt2 H f) (@lem349985 A B g)). Qed.
Lemma lem349988 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349989 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem349988 (A -> B) A f x). Qed.
Lemma lem349990 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1237 A B x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (@lem349989 A B (term1236 A B x'' lt2 H f) g). Qed.
Lemma lem349992 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem349986 A B x'' lt2 H f g) (@lem349990 A B x'' lt2 H f g)). Qed.
Lemma lem349993 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1239 A B x'' lt2 H f g) = (term1240 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem349957 A B g) (@lem349992 A B x'' lt2 H f g)). Qed.
Lemma lem349995 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem349996 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem349995 A B f x). Qed.
Lemma lem349997 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1240 A B x'' lt2 H f g) = (term1241 A B x'' lt2 H f g).
Proof. exact (@lem349996 A B g (term1238 A B x'' lt2 H f g)). Qed.
Lemma lem349998 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1239 A B x'' lt2 H f g) = (term1241 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem349993 A B x'' lt2 H f g) (@lem349997 A B x'' lt2 H f g)). Qed.
Lemma lem350011 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350012 {A B : Type'} (f : type408 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem350011 (type1402 A) (type106 A B) f x). Qed.
Lemma lem350013 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) : (x'' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2).
Proof. exact (@lem350012 A B x'' lt2). Qed.
Lemma lem350014 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350015 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (x'' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2 H).
Proof. exact (MK_COMB (@lem350013 A B x'' lt2) (@lem350014 A B H)). Qed.
Lemma lem350017 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350018 {A B : Type'} (f : type106 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem350017 (type549 A B) (type522 A B) f x). Qed.
Lemma lem350019 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2 H) = (term1234 A B x'' lt2 H).
Proof. exact (@lem350018 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2) H). Qed.
Lemma lem350020 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (x'' lt2 H) = (term1234 A B x'' lt2 H).
Proof. exact (TRANS (@lem350015 A B x'' lt2 H) (@lem350019 A B x'' lt2 H)). Qed.
Lemma lem350021 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem350022 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (x'' lt2 H f) = (term1235 A B x'' lt2 H f).
Proof. exact (MK_COMB (@lem350020 A B x'' lt2 H) (@lem350021 A B f)). Qed.
Lemma lem350024 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350025 {A B : Type'} (f : type522 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem350024 (A -> B) (type569 A B) f x). Qed.
Lemma lem350026 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1235 A B x'' lt2 H f) = (term1236 A B x'' lt2 H f).
Proof. exact (@lem350025 A B (term1234 A B x'' lt2 H) f). Qed.
Lemma lem350027 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (x'' lt2 H f) = (term1236 A B x'' lt2 H f).
Proof. exact (TRANS (@lem350022 A B x'' lt2 H f) (@lem350026 A B x'' lt2 H f)). Qed.
Lemma lem350028 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem350029 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (x'' lt2 H f g) = (term1237 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350027 A B x'' lt2 H f) (@lem350028 A B g)). Qed.
Lemma lem350031 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350032 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem350031 (A -> B) A f x). Qed.
Lemma lem350033 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1237 A B x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (@lem350032 A B (term1236 A B x'' lt2 H f) g). Qed.
Lemma lem350035 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem350029 A B x'' lt2 H f g) (@lem350033 A B x'' lt2 H f g)). Qed.
Lemma lem350036 {A B : Type'} (H : type549 A B) (g : A -> B) : (H g) = (H g).
Proof. exact (eq_refl (H g)). Qed.
Lemma lem350037 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1242 A B x'' lt2 H f g) = (term1243 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350036 A B H g) (@lem350035 A B x'' lt2 H f g)). Qed.
Lemma lem350039 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350040 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem350039 (A -> B) (A -> B) f x). Qed.
Lemma lem350041 {A B : Type'} (H : type549 A B) (g : A -> B) : (H g) = (@I ((A -> B) -> A -> B) H g).
Proof. exact (@lem350040 A B H g). Qed.
Lemma lem350042 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1238 A B x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (eq_refl (term1238 A B x'' lt2 H f g)). Qed.
Lemma lem350043 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1243 A B x'' lt2 H f g) = (term1244 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350041 A B H g) (@lem350042 A B x'' lt2 H f g)). Qed.
Lemma lem350045 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350046 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350045 A B f x). Qed.
Lemma lem350047 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1244 A B x'' lt2 H f g) = (term1245 A B x'' lt2 H f g).
Proof. exact (@lem350046 A B (@I ((A -> B) -> A -> B) H g) (term1238 A B x'' lt2 H f g)). Qed.
Lemma lem350048 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1243 A B x'' lt2 H f g) = (term1245 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem350043 A B x'' lt2 H f g) (@lem350047 A B x'' lt2 H f g)). Qed.
Lemma lem350049 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1242 A B x'' lt2 H f g) = (term1245 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem350037 A B x'' lt2 H f g) (@lem350048 A B x'' lt2 H f g)). Qed.
Lemma lem350050 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1246 A B x'' lt2 H f g) = (term1247 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem349956 B) (@lem349998 A B x'' lt2 H f g)). Qed.
Lemma lem350051 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : ((term1239 A B x'' lt2 H f g) = (term1242 A B x'' lt2 H f g)) = ((term1241 A B x'' lt2 H f g) = (term1245 A B x'' lt2 H f g)).
Proof. exact (MK_COMB (@lem350050 A B x'' lt2 H f g) (@lem350049 A B x'' lt2 H f g)). Qed.
Lemma lem350052 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1248 A B x'' lt2 H f g) = (term1249 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem349955) (@lem350051 A B x'' lt2 H f g)). Qed.
Lemma lem350053 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem350054 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem350055 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem350066 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350067 {A B : Type'} (f : type408 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem350066 (type1402 A) (type106 A B) f x). Qed.
Lemma lem350068 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) : (x'' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2).
Proof. exact (@lem350067 A B x'' lt2). Qed.
Lemma lem350069 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350070 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (x'' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2 H).
Proof. exact (MK_COMB (@lem350068 A B x'' lt2) (@lem350069 A B H)). Qed.
Lemma lem350072 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350073 {A B : Type'} (f : type106 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem350072 (type549 A B) (type522 A B) f x). Qed.
Lemma lem350074 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2 H) = (term1234 A B x'' lt2 H).
Proof. exact (@lem350073 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2) H). Qed.
Lemma lem350075 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (x'' lt2 H) = (term1234 A B x'' lt2 H).
Proof. exact (TRANS (@lem350070 A B x'' lt2 H) (@lem350074 A B x'' lt2 H)). Qed.
Lemma lem350076 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem350077 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (x'' lt2 H f) = (term1235 A B x'' lt2 H f).
Proof. exact (MK_COMB (@lem350075 A B x'' lt2 H) (@lem350076 A B f)). Qed.
Lemma lem350079 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350080 {A B : Type'} (f : type522 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem350079 (A -> B) (type569 A B) f x). Qed.
Lemma lem350081 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1235 A B x'' lt2 H f) = (term1236 A B x'' lt2 H f).
Proof. exact (@lem350080 A B (term1234 A B x'' lt2 H) f). Qed.
Lemma lem350082 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (x'' lt2 H f) = (term1236 A B x'' lt2 H f).
Proof. exact (TRANS (@lem350077 A B x'' lt2 H f) (@lem350081 A B x'' lt2 H f)). Qed.
Lemma lem350083 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem350084 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (x'' lt2 H f g) = (term1237 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350082 A B x'' lt2 H f) (@lem350083 A B g)). Qed.
Lemma lem350086 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350087 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem350086 (A -> B) A f x). Qed.
Lemma lem350088 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1237 A B x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (@lem350087 A B (term1236 A B x'' lt2 H f) g). Qed.
Lemma lem350090 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem350084 A B x'' lt2 H f g) (@lem350088 A B x'' lt2 H f g)). Qed.
Lemma lem350091 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1250 A B x'' lt2 H f g) = (term1251 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350055 A B f) (@lem350090 A B x'' lt2 H f g)). Qed.
Lemma lem350093 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350094 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350093 A B f x). Qed.
Lemma lem350095 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1251 A B x'' lt2 H f g) = (term1252 A B x'' lt2 H f g).
Proof. exact (@lem350094 A B f (term1238 A B x'' lt2 H f g)). Qed.
Lemma lem350096 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1250 A B x'' lt2 H f g) = (term1252 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem350091 A B x'' lt2 H f g) (@lem350095 A B x'' lt2 H f g)). Qed.
Lemma lem350109 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350110 {A B : Type'} (f : type408 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem350109 (type1402 A) (type106 A B) f x). Qed.
Lemma lem350111 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) : (x'' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2).
Proof. exact (@lem350110 A B x'' lt2). Qed.
Lemma lem350112 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350113 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (x'' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2 H).
Proof. exact (MK_COMB (@lem350111 A B x'' lt2) (@lem350112 A B H)). Qed.
Lemma lem350115 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350116 {A B : Type'} (f : type106 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem350115 (type549 A B) (type522 A B) f x). Qed.
Lemma lem350117 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2 H) = (term1234 A B x'' lt2 H).
Proof. exact (@lem350116 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> (A -> B) -> (A -> B) -> A) x'' lt2) H). Qed.
Lemma lem350118 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (x'' lt2 H) = (term1234 A B x'' lt2 H).
Proof. exact (TRANS (@lem350113 A B x'' lt2 H) (@lem350117 A B x'' lt2 H)). Qed.
Lemma lem350119 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem350120 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (x'' lt2 H f) = (term1235 A B x'' lt2 H f).
Proof. exact (MK_COMB (@lem350118 A B x'' lt2 H) (@lem350119 A B f)). Qed.
Lemma lem350122 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350123 {A B : Type'} (f : type522 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> A) f x).
Proof. exact (@lem350122 (A -> B) (type569 A B) f x). Qed.
Lemma lem350124 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1235 A B x'' lt2 H f) = (term1236 A B x'' lt2 H f).
Proof. exact (@lem350123 A B (term1234 A B x'' lt2 H) f). Qed.
Lemma lem350125 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (x'' lt2 H f) = (term1236 A B x'' lt2 H f).
Proof. exact (TRANS (@lem350120 A B x'' lt2 H f) (@lem350124 A B x'' lt2 H f)). Qed.
Lemma lem350126 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem350127 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (x'' lt2 H f g) = (term1237 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350125 A B x'' lt2 H f) (@lem350126 A B g)). Qed.
Lemma lem350129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350130 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem350129 (A -> B) A f x). Qed.
Lemma lem350131 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1237 A B x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (@lem350130 A B (term1236 A B x'' lt2 H f) g). Qed.
Lemma lem350133 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem350127 A B x'' lt2 H f g) (@lem350131 A B x'' lt2 H f g)). Qed.
Lemma lem350134 {A B : Type'} (H : type549 A B) (f : A -> B) : (H f) = (H f).
Proof. exact (eq_refl (H f)). Qed.
Lemma lem350135 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1253 A B x'' lt2 H f g) = (term1254 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350134 A B H f) (@lem350133 A B x'' lt2 H f g)). Qed.
Lemma lem350137 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350138 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem350137 (A -> B) (A -> B) f x). Qed.
Lemma lem350139 {A B : Type'} (H : type549 A B) (f : A -> B) : (H f) = (@I ((A -> B) -> A -> B) H f).
Proof. exact (@lem350138 A B H f). Qed.
Lemma lem350140 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1238 A B x'' lt2 H f g) = (term1238 A B x'' lt2 H f g).
Proof. exact (eq_refl (term1238 A B x'' lt2 H f g)). Qed.
Lemma lem350141 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1254 A B x'' lt2 H f g) = (term1255 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350139 A B H f) (@lem350140 A B x'' lt2 H f g)). Qed.
Lemma lem350143 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350144 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350143 A B f x). Qed.
Lemma lem350145 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1255 A B x'' lt2 H f g) = (term1256 A B x'' lt2 H f g).
Proof. exact (@lem350144 A B (@I ((A -> B) -> A -> B) H f) (term1238 A B x'' lt2 H f g)). Qed.
Lemma lem350146 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1254 A B x'' lt2 H f g) = (term1256 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem350141 A B x'' lt2 H f g) (@lem350145 A B x'' lt2 H f g)). Qed.
Lemma lem350147 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1253 A B x'' lt2 H f g) = (term1256 A B x'' lt2 H f g).
Proof. exact (TRANS (@lem350135 A B x'' lt2 H f g) (@lem350146 A B x'' lt2 H f g)). Qed.
Lemma lem350148 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1257 A B x'' lt2 H f g) = (term1258 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350054 B) (@lem350096 A B x'' lt2 H f g)). Qed.
Lemma lem350149 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : ((term1250 A B x'' lt2 H f g) = (term1253 A B x'' lt2 H f g)) = ((term1252 A B x'' lt2 H f g) = (term1256 A B x'' lt2 H f g)).
Proof. exact (MK_COMB (@lem350148 A B x'' lt2 H f g) (@lem350147 A B x'' lt2 H f g)). Qed.
Lemma lem350150 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1259 A B x'' lt2 H f g) = (term1260 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350053) (@lem350149 A B x'' lt2 H f g)). Qed.
Lemma lem350151 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350152 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1261 A B x'' lt2 H f g) = (term1262 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350151) (@lem350150 A B x'' lt2 H f g)). Qed.
Lemma lem350153 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1263 A B x'' lt2 H f g) = (term1264 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350152 A B x'' lt2 H f g) (@lem350052 A B x'' lt2 H f g)). Qed.
Lemma lem350154 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350155 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1265 A B x'' lt2 H f g) = (term1266 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350154) (@lem350153 A B x'' lt2 H f g)). Qed.
Lemma lem350156 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1267 A B x'' lt2 H f g) = (term1268 A B x'' lt2 H f g).
Proof. exact (MK_COMB (@lem350155 A B x'' lt2 H f g) (@lem349954 A B f g)). Qed.
Lemma lem350157 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1269 A B x'' lt2 H f) = (term1270 A B x'' lt2 H f).
Proof. exact (fun_ext (fun g : A -> B => @lem350156 A B x'' lt2 H f g)). Qed.
Lemma lem350158 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem350159 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1271 A B x'' lt2 H f) = (term1272 A B x'' lt2 H f).
Proof. exact (MK_COMB (@lem350158 A B) (@lem350157 A B x'' lt2 H f)). Qed.
Lemma lem350160 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1273 A B x'' lt2 H) = (term1274 A B x'' lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem350159 A B x'' lt2 H f)). Qed.
Lemma lem350161 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem350162 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1275 A B x'' lt2 H) = (term1276 A B x'' lt2 H).
Proof. exact (MK_COMB (@lem350161 A B) (@lem350160 A B x'' lt2 H)). Qed.
Lemma lem350163 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem350164 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem350165 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350172 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350173 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem350172 (type1402 A) (type108 A B) f x). Qed.
Lemma lem350174 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) : (f' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f' lt2).
Proof. exact (@lem350173 A B f' lt2). Qed.
Lemma lem350175 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350176 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f' lt2 H).
Proof. exact (MK_COMB (@lem350174 A B f' lt2) (@lem350175 A B H)). Qed.
Lemma lem350178 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350179 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem350178 (type549 A B) (A -> B) f x). Qed.
Lemma lem350180 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f' lt2 H) = (term1178 A B f' lt2 H).
Proof. exact (@lem350179 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f' lt2) H). Qed.
Lemma lem350182 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f' lt2 H) = (term1178 A B f' lt2 H).
Proof. exact (TRANS (@lem350176 A B f' lt2 H) (@lem350180 A B f' lt2 H)). Qed.
Lemma lem350189 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350190 {A B : Type'} (f : type410 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem350189 (type1402 A) (type110 A B) f x). Qed.
Lemma lem350191 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) : (x' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2).
Proof. exact (@lem350190 A B x' lt2). Qed.
Lemma lem350192 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350193 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2 H).
Proof. exact (MK_COMB (@lem350191 A B x' lt2) (@lem350192 A B H)). Qed.
Lemma lem350195 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350196 {A B : Type'} (f : type110 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem350195 (type549 A B) A f x). Qed.
Lemma lem350197 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2 H) = (term1194 A B x' lt2 H).
Proof. exact (@lem350196 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2) H). Qed.
Lemma lem350199 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x' lt2 H) = (term1194 A B x' lt2 H).
Proof. exact (TRANS (@lem350193 A B x' lt2 H) (@lem350197 A B x' lt2 H)). Qed.
Lemma lem350200 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1181 A B f' lt2 H) = (term1182 A B f' lt2 H).
Proof. exact (MK_COMB (@lem350165 A B H) (@lem350182 A B f' lt2 H)). Qed.
Lemma lem350201 {A B : Type'} (f' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1195 A B f' x' lt2 H) = (term1196 A B f' x' lt2 H).
Proof. exact (MK_COMB (@lem350200 A B f' lt2 H) (@lem350199 A B x' lt2 H)). Qed.
Lemma lem350203 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350204 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem350203 (A -> B) (A -> B) f x). Qed.
Lemma lem350205 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1182 A B f' lt2 H) = (term1185 A B f' lt2 H).
Proof. exact (@lem350204 A B H (term1178 A B f' lt2 H)). Qed.
Lemma lem350206 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1194 A B x' lt2 H) = (term1194 A B x' lt2 H).
Proof. exact (eq_refl (term1194 A B x' lt2 H)). Qed.
Lemma lem350207 {A B : Type'} (f' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1196 A B f' x' lt2 H) = (term1197 A B f' x' lt2 H).
Proof. exact (MK_COMB (@lem350205 A B f' lt2 H) (@lem350206 A B x' lt2 H)). Qed.
Lemma lem350209 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350210 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350209 A B f x). Qed.
Lemma lem350211 {A B : Type'} (f' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1197 A B f' x' lt2 H) = (term1198 A B f' x' lt2 H).
Proof. exact (@lem350210 A B (term1185 A B f' lt2 H) (term1194 A B x' lt2 H)). Qed.
Lemma lem350212 {A B : Type'} (f' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1196 A B f' x' lt2 H) = (term1198 A B f' x' lt2 H).
Proof. exact (TRANS (@lem350207 A B f' x' lt2 H) (@lem350211 A B f' x' lt2 H)). Qed.
Lemma lem350213 {A B : Type'} (f' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1195 A B f' x' lt2 H) = (term1198 A B f' x' lt2 H).
Proof. exact (TRANS (@lem350201 A B f' x' lt2 H) (@lem350212 A B f' x' lt2 H)). Qed.
Lemma lem350214 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350221 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350222 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem350221 (type1402 A) (type108 A B) f x). Qed.
Lemma lem350223 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) : (g' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g' lt2).
Proof. exact (@lem350222 A B g' lt2). Qed.
Lemma lem350224 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350225 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (g' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g' lt2 H).
Proof. exact (MK_COMB (@lem350223 A B g' lt2) (@lem350224 A B H)). Qed.
Lemma lem350227 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350228 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem350227 (type549 A B) (A -> B) f x). Qed.
Lemma lem350229 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g' lt2 H) = (term1178 A B g' lt2 H).
Proof. exact (@lem350228 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g' lt2) H). Qed.
Lemma lem350231 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (g' lt2 H) = (term1178 A B g' lt2 H).
Proof. exact (TRANS (@lem350225 A B g' lt2 H) (@lem350229 A B g' lt2 H)). Qed.
Lemma lem350238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350239 {A B : Type'} (f : type410 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem350238 (type1402 A) (type110 A B) f x). Qed.
Lemma lem350240 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) : (x' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2).
Proof. exact (@lem350239 A B x' lt2). Qed.
Lemma lem350241 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350242 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2 H).
Proof. exact (MK_COMB (@lem350240 A B x' lt2) (@lem350241 A B H)). Qed.
Lemma lem350244 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350245 {A B : Type'} (f : type110 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem350244 (type549 A B) A f x). Qed.
Lemma lem350246 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2 H) = (term1194 A B x' lt2 H).
Proof. exact (@lem350245 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2) H). Qed.
Lemma lem350248 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x' lt2 H) = (term1194 A B x' lt2 H).
Proof. exact (TRANS (@lem350242 A B x' lt2 H) (@lem350246 A B x' lt2 H)). Qed.
Lemma lem350249 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1181 A B g' lt2 H) = (term1182 A B g' lt2 H).
Proof. exact (MK_COMB (@lem350214 A B H) (@lem350231 A B g' lt2 H)). Qed.
Lemma lem350250 {A B : Type'} (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1195 A B g' x' lt2 H) = (term1196 A B g' x' lt2 H).
Proof. exact (MK_COMB (@lem350249 A B g' lt2 H) (@lem350248 A B x' lt2 H)). Qed.
Lemma lem350252 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350253 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem350252 (A -> B) (A -> B) f x). Qed.
Lemma lem350254 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1182 A B g' lt2 H) = (term1185 A B g' lt2 H).
Proof. exact (@lem350253 A B H (term1178 A B g' lt2 H)). Qed.
Lemma lem350255 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1194 A B x' lt2 H) = (term1194 A B x' lt2 H).
Proof. exact (eq_refl (term1194 A B x' lt2 H)). Qed.
Lemma lem350256 {A B : Type'} (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1196 A B g' x' lt2 H) = (term1197 A B g' x' lt2 H).
Proof. exact (MK_COMB (@lem350254 A B g' lt2 H) (@lem350255 A B x' lt2 H)). Qed.
Lemma lem350258 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350259 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350258 A B f x). Qed.
Lemma lem350260 {A B : Type'} (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1197 A B g' x' lt2 H) = (term1198 A B g' x' lt2 H).
Proof. exact (@lem350259 A B (term1185 A B g' lt2 H) (term1194 A B x' lt2 H)). Qed.
Lemma lem350261 {A B : Type'} (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1196 A B g' x' lt2 H) = (term1198 A B g' x' lt2 H).
Proof. exact (TRANS (@lem350256 A B g' x' lt2 H) (@lem350260 A B g' x' lt2 H)). Qed.
Lemma lem350262 {A B : Type'} (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1195 A B g' x' lt2 H) = (term1198 A B g' x' lt2 H).
Proof. exact (TRANS (@lem350250 A B g' x' lt2 H) (@lem350261 A B g' x' lt2 H)). Qed.
Lemma lem350263 {A B : Type'} (f' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1199 A B f' x' lt2 H) = (term1200 A B f' x' lt2 H).
Proof. exact (MK_COMB (@lem350164 B) (@lem350213 A B f' x' lt2 H)). Qed.
Lemma lem350264 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1195 A B f' x' lt2 H) = (term1195 A B g' x' lt2 H)) = ((term1198 A B f' x' lt2 H) = (term1198 A B g' x' lt2 H)).
Proof. exact (MK_COMB (@lem350263 A B f' x' lt2 H) (@lem350262 A B g' x' lt2 H)). Qed.
Lemma lem350265 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1201 A B f' g' x' lt2 H) = (term1202 A B f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem350163) (@lem350264 A B f' g' x' lt2 H)). Qed.
Lemma lem350266 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem350275 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350276 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem350275 (type1402 A) (type108 A B) f x). Qed.
Lemma lem350277 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) : (f' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f' lt2).
Proof. exact (@lem350276 A B f' lt2). Qed.
Lemma lem350278 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350279 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f' lt2 H).
Proof. exact (MK_COMB (@lem350277 A B f' lt2) (@lem350278 A B H)). Qed.
Lemma lem350281 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350282 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem350281 (type549 A B) (A -> B) f x). Qed.
Lemma lem350283 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f' lt2 H) = (term1178 A B f' lt2 H).
Proof. exact (@lem350282 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f' lt2) H). Qed.
Lemma lem350284 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (f' lt2 H) = (term1178 A B f' lt2 H).
Proof. exact (TRANS (@lem350279 A B f' lt2 H) (@lem350283 A B f' lt2 H)). Qed.
Lemma lem350285 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem350286 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (f' lt2 H z) = (term1179 A B f' lt2 H z).
Proof. exact (MK_COMB (@lem350284 A B f' lt2 H) (@lem350285 A z)). Qed.
Lemma lem350288 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350289 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350288 A B f x). Qed.
Lemma lem350290 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1179 A B f' lt2 H z) = (term1180 A B f' lt2 H z).
Proof. exact (@lem350289 A B (term1178 A B f' lt2 H) z). Qed.
Lemma lem350292 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (f' lt2 H z) = (term1180 A B f' lt2 H z).
Proof. exact (TRANS (@lem350286 A B f' lt2 H z) (@lem350290 A B f' lt2 H z)). Qed.
Lemma lem350301 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350302 {A B : Type'} (f : type409 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem350301 (type1402 A) (type108 A B) f x). Qed.
Lemma lem350303 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) : (g' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g' lt2).
Proof. exact (@lem350302 A B g' lt2). Qed.
Lemma lem350304 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350305 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (g' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g' lt2 H).
Proof. exact (MK_COMB (@lem350303 A B g' lt2) (@lem350304 A B H)). Qed.
Lemma lem350307 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350308 {A B : Type'} (f : type108 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A -> B) f x).
Proof. exact (@lem350307 (type549 A B) (A -> B) f x). Qed.
Lemma lem350309 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g' lt2 H) = (term1178 A B g' lt2 H).
Proof. exact (@lem350308 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A -> B) g' lt2) H). Qed.
Lemma lem350310 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (g' lt2 H) = (term1178 A B g' lt2 H).
Proof. exact (TRANS (@lem350305 A B g' lt2 H) (@lem350309 A B g' lt2 H)). Qed.
Lemma lem350311 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem350312 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (g' lt2 H z) = (term1179 A B g' lt2 H z).
Proof. exact (MK_COMB (@lem350310 A B g' lt2 H) (@lem350311 A z)). Qed.
Lemma lem350314 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350315 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350314 A B f x). Qed.
Lemma lem350316 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1179 A B g' lt2 H z) = (term1180 A B g' lt2 H z).
Proof. exact (@lem350315 A B (term1178 A B g' lt2 H) z). Qed.
Lemma lem350318 {A B : Type'} (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (g' lt2 H z) = (term1180 A B g' lt2 H z).
Proof. exact (TRANS (@lem350312 A B g' lt2 H z) (@lem350316 A B g' lt2 H z)). Qed.
Lemma lem350319 {A B : Type'} (f' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1188 A B f' lt2 H z) = (term1189 A B f' lt2 H z).
Proof. exact (MK_COMB (@lem350266 B) (@lem350292 A B f' lt2 H z)). Qed.
Lemma lem350320 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : ((f' lt2 H z) = (g' lt2 H z)) = ((term1180 A B f' lt2 H z) = (term1180 A B g' lt2 H z)).
Proof. exact (MK_COMB (@lem350319 A B f' lt2 H z) (@lem350318 A B g' lt2 H z)). Qed.
Lemma lem350321 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem350330 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350331 {A B : Type'} (f : type410 A B) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem350330 (type1402 A) (type110 A B) f x). Qed.
Lemma lem350332 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) : (x' lt2) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2).
Proof. exact (@lem350331 A B x' lt2). Qed.
Lemma lem350333 {A B : Type'} (H : type549 A B) : H = H.
Proof. exact (eq_refl H). Qed.
Lemma lem350334 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x' lt2 H) = (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2 H).
Proof. exact (MK_COMB (@lem350332 A B x' lt2) (@lem350333 A B H)). Qed.
Lemma lem350336 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350337 {A B : Type'} (f : type110 A B) (x : type549 A B) : (f x) = (@I (((A -> B) -> A -> B) -> A) f x).
Proof. exact (@lem350336 (type549 A B) A f x). Qed.
Lemma lem350338 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2 H) = (term1194 A B x' lt2 H).
Proof. exact (@lem350337 A B (@I ((A -> A -> Prop) -> ((A -> B) -> A -> B) -> A) x' lt2) H). Qed.
Lemma lem350340 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (x' lt2 H) = (term1194 A B x' lt2 H).
Proof. exact (TRANS (@lem350334 A B x' lt2 H) (@lem350338 A B x' lt2 H)). Qed.
Lemma lem350341 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem350342 {A B : Type'} (z : A) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1203 A B z x' lt2 H) = (term1204 A B z x' lt2 H).
Proof. exact (MK_COMB (@lem350341 A lt2 z) (@lem350340 A B x' lt2 H)). Qed.
Lemma lem350344 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350345 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem350344 A (A -> Prop) f x). Qed.
Lemma lem350346 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem350345 A lt2 z). Qed.
Lemma lem350347 {A B : Type'} (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1194 A B x' lt2 H) = (term1194 A B x' lt2 H).
Proof. exact (eq_refl (term1194 A B x' lt2 H)). Qed.
Lemma lem350348 {A B : Type'} (z : A) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1204 A B z x' lt2 H) = (term1205 A B z x' lt2 H).
Proof. exact (MK_COMB (@lem350346 A lt2 z) (@lem350347 A B x' lt2 H)). Qed.
Lemma lem350350 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350351 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem350350 A Prop f x). Qed.
Lemma lem350352 {A B : Type'} (z : A) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1205 A B z x' lt2 H) = (term1206 A B z x' lt2 H).
Proof. exact (@lem350351 A (@I (A -> A -> Prop) lt2 z) (term1194 A B x' lt2 H)). Qed.
Lemma lem350353 {A B : Type'} (z : A) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1204 A B z x' lt2 H) = (term1206 A B z x' lt2 H).
Proof. exact (TRANS (@lem350348 A B z x' lt2 H) (@lem350352 A B z x' lt2 H)). Qed.
Lemma lem350354 {A B : Type'} (z : A) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1203 A B z x' lt2 H) = (term1206 A B z x' lt2 H).
Proof. exact (TRANS (@lem350342 A B z x' lt2 H) (@lem350353 A B z x' lt2 H)). Qed.
Lemma lem350355 {A B : Type'} (z : A) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1207 A B z x' lt2 H) = (term1208 A B z x' lt2 H).
Proof. exact (MK_COMB (@lem350321) (@lem350354 A B z x' lt2 H)). Qed.
Lemma lem350356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350357 {A B : Type'} (z : A) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1209 A B z x' lt2 H) = (term1210 A B z x' lt2 H).
Proof. exact (MK_COMB (@lem350356) (@lem350355 A B z x' lt2 H)). Qed.
Lemma lem350358 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1211 A B x' f' g' lt2 H z) = (term1212 A B x' f' g' lt2 H z).
Proof. exact (MK_COMB (@lem350357 A B z x' lt2 H) (@lem350320 A B f' g' lt2 H z)). Qed.
Lemma lem350359 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1213 A B x' f' g' lt2 H) = (term1214 A B x' f' g' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350358 A B x' f' g' lt2 H z)). Qed.
Lemma lem350360 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350361 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1215 A B x' f' g' lt2 H) = (term1216 A B x' f' g' lt2 H).
Proof. exact (MK_COMB (@lem350360 A) (@lem350359 A B x' f' g' lt2 H)). Qed.
Lemma lem350362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem350363 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1217 A B x' f' g' lt2 H) = (term1218 A B x' f' g' lt2 H).
Proof. exact (MK_COMB (@lem350362) (@lem350361 A B x' f' g' lt2 H)). Qed.
Lemma lem350364 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1219 A B f' g' x' lt2 H) = (term1220 A B f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem350363 A B x' f' g' lt2 H) (@lem350265 A B f' g' x' lt2 H)). Qed.
Lemma lem350365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350366 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1221 A B f' g' x' lt2 H) = (term1222 A B f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem350365) (@lem350364 A B f' g' x' lt2 H)). Qed.
Lemma lem350367 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1277 A B f' g' x' x'' lt2 H) = (term1278 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem350366 A B f' g' x' lt2 H) (@lem350162 A B x'' lt2 H)). Qed.
Lemma lem350368 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1279 A B f' g' x' x'' lt2) = (term1280 A B f' g' x' x'' lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem350367 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem350369 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem350370 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1281 A B f' g' x' x'' lt2) = (term1282 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem350369 A B) (@lem350368 A B f' g' x' x'' lt2)). Qed.
Lemma lem350371 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem350376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350377 {A : Type'} (f : type421 A) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> Prop) f x).
Proof. exact (@lem350376 (type1402 A) Prop f x). Qed.
Lemma lem350379 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem350377 A (@WF A) lt2). Qed.
Lemma lem350380 {A : Type'} (lt2 : type1402 A) : (term787 A lt2) = (term1229 A lt2).
Proof. exact (MK_COMB (@lem350371) (@lem350379 A lt2)). Qed.
Lemma lem350381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350382 {A : Type'} (lt2 : type1402 A) : (term524 A lt2) = (term1230 A lt2).
Proof. exact (MK_COMB (@lem350381) (@lem350380 A lt2)). Qed.
Lemma lem350383 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term934 A B f' g' x' x'' lt2) = (term1283 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem350382 A lt2) (@lem350370 A B f' g' x' x'' lt2)). Qed.
Lemma lem350384 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) : (term936 A B f' g' x' x'') = (term1284 A B f' g' x' x'').
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem350383 A B f' g' x' x'' lt2)). Qed.
Lemma lem350385 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem350386 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) : (term938 A B f' g' x' x'') = (term1285 A B f' g' x' x'').
Proof. exact (MK_COMB (@lem350385 A) (@lem350384 A B f' g' x' x'')). Qed.
Lemma lem350387 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1285 A B f' g' x' x''.
Proof. exact (EQ_MP (@lem350386 A B f' g' x' x'') (@lem349654 A B f' g' x' x'' h1)). Qed.
Lemma lem350394 {A B : Type'} (f''' : A -> B) (f'' : A -> B) : (term96 A B f''' f'') = (term96 A B f''' f'').
Proof. exact (eq_refl (term96 A B f''' f'')). Qed.
Lemma lem350395 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem350400 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350401 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350400 A B f x). Qed.
Lemma lem350403 {A B : Type'} (f''' : A -> B) (x : A) : (f''' x) = (@I (A -> B) f''' x).
Proof. exact (@lem350401 A B f''' x). Qed.
Lemma lem350410 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350411 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem350410 (A -> B) (A -> B) f x). Qed.
Lemma lem350412 {A B : Type'} (H : type549 A B) (f''' : A -> B) : (H f''') = (@I ((A -> B) -> A -> B) H f''').
Proof. exact (@lem350411 A B H f'''). Qed.
Lemma lem350413 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem350414 {A B : Type'} (H : type549 A B) (f''' : A -> B) (x : A) : (H f''' x) = (@I ((A -> B) -> A -> B) H f''' x).
Proof. exact (MK_COMB (@lem350412 A B H f''') (@lem350413 A x)). Qed.
Lemma lem350416 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350417 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350416 A B f x). Qed.
Lemma lem350418 {A B : Type'} (H : type549 A B) (f''' : A -> B) (x : A) : (@I ((A -> B) -> A -> B) H f''' x) = (term1286 A B H f''' x).
Proof. exact (@lem350417 A B (@I ((A -> B) -> A -> B) H f''') x). Qed.
Lemma lem350420 {A B : Type'} (H : type549 A B) (f''' : A -> B) (x : A) : (H f''' x) = (term1286 A B H f''' x).
Proof. exact (TRANS (@lem350414 A B H f''' x) (@lem350418 A B H f''' x)). Qed.
Lemma lem350421 {A B : Type'} (f''' : A -> B) (x : A) : (term1287 A B f''' x) = (term1288 A B f''' x).
Proof. exact (MK_COMB (@lem350395 B) (@lem350403 A B f''' x)). Qed.
Lemma lem350422 {A B : Type'} (H : type549 A B) (f''' : A -> B) (x : A) : ((f''' x) = (H f''' x)) = ((@I (A -> B) f''' x) = (term1286 A B H f''' x)).
Proof. exact (MK_COMB (@lem350421 A B f''' x) (@lem350420 A B H f''' x)). Qed.
Lemma lem350423 {A B : Type'} (H : type549 A B) (f''' : A -> B) : (term28 A B H f''') = (term1289 A B H f''').
Proof. exact (fun_ext (fun x : A => @lem350422 A B H f''' x)). Qed.
Lemma lem350424 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350425 {A B : Type'} (H : type549 A B) (f''' : A -> B) : (term29 A B H f''') = (term1290 A B H f''').
Proof. exact (MK_COMB (@lem350424 A) (@lem350423 A B H f''')). Qed.
Lemma lem350426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem350427 {A B : Type'} (H : type549 A B) (f''' : A -> B) : (term50 A B H f''') = (term1291 A B H f''').
Proof. exact (MK_COMB (@lem350426) (@lem350425 A B H f''')). Qed.
Lemma lem350428 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) : (term104 A B H f''' f'') = (term1292 A B H f''' f'').
Proof. exact (MK_COMB (@lem350427 A B H f''') (@lem350394 A B f''' f'')). Qed.
Lemma lem350429 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem350434 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350435 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350434 A B f x). Qed.
Lemma lem350437 {A B : Type'} (f'' : A -> B) (x : A) : (f'' x) = (@I (A -> B) f'' x).
Proof. exact (@lem350435 A B f'' x). Qed.
Lemma lem350444 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350445 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem350444 (A -> B) (A -> B) f x). Qed.
Lemma lem350446 {A B : Type'} (H : type549 A B) (f'' : A -> B) : (H f'') = (@I ((A -> B) -> A -> B) H f'').
Proof. exact (@lem350445 A B H f''). Qed.
Lemma lem350447 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem350448 {A B : Type'} (H : type549 A B) (f'' : A -> B) (x : A) : (H f'' x) = (@I ((A -> B) -> A -> B) H f'' x).
Proof. exact (MK_COMB (@lem350446 A B H f'') (@lem350447 A x)). Qed.
Lemma lem350450 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350451 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350450 A B f x). Qed.
Lemma lem350452 {A B : Type'} (H : type549 A B) (f'' : A -> B) (x : A) : (@I ((A -> B) -> A -> B) H f'' x) = (term1286 A B H f'' x).
Proof. exact (@lem350451 A B (@I ((A -> B) -> A -> B) H f'') x). Qed.
Lemma lem350454 {A B : Type'} (H : type549 A B) (f'' : A -> B) (x : A) : (H f'' x) = (term1286 A B H f'' x).
Proof. exact (TRANS (@lem350448 A B H f'' x) (@lem350452 A B H f'' x)). Qed.
Lemma lem350455 {A B : Type'} (f'' : A -> B) (x : A) : (term1287 A B f'' x) = (term1288 A B f'' x).
Proof. exact (MK_COMB (@lem350429 B) (@lem350437 A B f'' x)). Qed.
Lemma lem350456 {A B : Type'} (H : type549 A B) (f'' : A -> B) (x : A) : ((f'' x) = (H f'' x)) = ((@I (A -> B) f'' x) = (term1286 A B H f'' x)).
Proof. exact (MK_COMB (@lem350455 A B f'' x) (@lem350454 A B H f'' x)). Qed.
Lemma lem350457 {A B : Type'} (H : type549 A B) (f'' : A -> B) : (term28 A B H f'') = (term1289 A B H f'').
Proof. exact (fun_ext (fun x : A => @lem350456 A B H f'' x)). Qed.
Lemma lem350458 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350459 {A B : Type'} (H : type549 A B) (f'' : A -> B) : (term29 A B H f'') = (term1290 A B H f'').
Proof. exact (MK_COMB (@lem350458 A) (@lem350457 A B H f'')). Qed.
Lemma lem350460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem350461 {A B : Type'} (H : type549 A B) (f'' : A -> B) : (term50 A B H f'') = (term1291 A B H f'').
Proof. exact (MK_COMB (@lem350460) (@lem350459 A B H f'')). Qed.
Lemma lem350462 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) : (term106 A B H f''' f'') = (term1293 A B H f''' f'').
Proof. exact (MK_COMB (@lem350461 A B H f'') (@lem350428 A B H f''' f'')). Qed.
Lemma lem350463 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem350464 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem350465 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem350470 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350471 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem350470 (A -> B) A f x). Qed.
Lemma lem350473 {A B : Type'} (x''' : type569 A B) (f : A -> B) : (x''' f) = (@I ((A -> B) -> A) x''' f).
Proof. exact (@lem350471 A B x''' f). Qed.
Lemma lem350474 {A B : Type'} (x''' : type569 A B) (f : A -> B) : (term1294 A B x''' f) = (term1295 A B x''' f).
Proof. exact (MK_COMB (@lem350465 A B f) (@lem350473 A B x''' f)). Qed.
Lemma lem350476 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350477 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350476 A B f x). Qed.
Lemma lem350478 {A B : Type'} (x''' : type569 A B) (f : A -> B) : (term1295 A B x''' f) = (term1296 A B x''' f).
Proof. exact (@lem350477 A B f (@I ((A -> B) -> A) x''' f)). Qed.
Lemma lem350479 {A B : Type'} (x''' : type569 A B) (f : A -> B) : (term1294 A B x''' f) = (term1296 A B x''' f).
Proof. exact (TRANS (@lem350474 A B x''' f) (@lem350478 A B x''' f)). Qed.
Lemma lem350486 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350487 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem350486 (A -> B) A f x). Qed.
Lemma lem350489 {A B : Type'} (x''' : type569 A B) (f : A -> B) : (x''' f) = (@I ((A -> B) -> A) x''' f).
Proof. exact (@lem350487 A B x''' f). Qed.
Lemma lem350490 {A B : Type'} (H : type549 A B) (f : A -> B) : (H f) = (H f).
Proof. exact (eq_refl (H f)). Qed.
Lemma lem350491 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (f : A -> B) : (term1297 A B H x''' f) = (term1298 A B H x''' f).
Proof. exact (MK_COMB (@lem350490 A B H f) (@lem350489 A B x''' f)). Qed.
Lemma lem350493 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350494 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem350493 (A -> B) (A -> B) f x). Qed.
Lemma lem350495 {A B : Type'} (H : type549 A B) (f : A -> B) : (H f) = (@I ((A -> B) -> A -> B) H f).
Proof. exact (@lem350494 A B H f). Qed.
Lemma lem350496 {A B : Type'} (x''' : type569 A B) (f : A -> B) : (@I ((A -> B) -> A) x''' f) = (@I ((A -> B) -> A) x''' f).
Proof. exact (eq_refl (@I ((A -> B) -> A) x''' f)). Qed.
Lemma lem350497 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (f : A -> B) : (term1298 A B H x''' f) = (term1299 A B H x''' f).
Proof. exact (MK_COMB (@lem350495 A B H f) (@lem350496 A B x''' f)). Qed.
Lemma lem350499 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350500 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350499 A B f x). Qed.
Lemma lem350501 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (f : A -> B) : (term1299 A B H x''' f) = (term1300 A B H x''' f).
Proof. exact (@lem350500 A B (@I ((A -> B) -> A -> B) H f) (@I ((A -> B) -> A) x''' f)). Qed.
Lemma lem350502 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (f : A -> B) : (term1298 A B H x''' f) = (term1300 A B H x''' f).
Proof. exact (TRANS (@lem350497 A B H x''' f) (@lem350501 A B H x''' f)). Qed.
Lemma lem350503 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (f : A -> B) : (term1297 A B H x''' f) = (term1300 A B H x''' f).
Proof. exact (TRANS (@lem350491 A B H x''' f) (@lem350502 A B H x''' f)). Qed.
Lemma lem350504 {A B : Type'} (x''' : type569 A B) (f : A -> B) : (term1301 A B x''' f) = (term1302 A B x''' f).
Proof. exact (MK_COMB (@lem350464 B) (@lem350479 A B x''' f)). Qed.
Lemma lem350505 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (f : A -> B) : ((term1294 A B x''' f) = (term1297 A B H x''' f)) = ((term1296 A B x''' f) = (term1300 A B H x''' f)).
Proof. exact (MK_COMB (@lem350504 A B x''' f) (@lem350503 A B H x''' f)). Qed.
Lemma lem350506 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (f : A -> B) : (term273 A B H x''' f) = (term1303 A B H x''' f).
Proof. exact (MK_COMB (@lem350463) (@lem350505 A B H x''' f)). Qed.
Lemma lem350507 {A B : Type'} (H : type549 A B) (x''' : type569 A B) : (term275 A B H x''') = (term1304 A B H x''').
Proof. exact (fun_ext (fun f : A -> B => @lem350506 A B H x''' f)). Qed.
Lemma lem350508 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem350509 {A B : Type'} (H : type549 A B) (x''' : type569 A B) : (term277 A B H x''') = (term1305 A B H x''').
Proof. exact (MK_COMB (@lem350508 A B) (@lem350507 A B H x''')). Qed.
Lemma lem350510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350511 {A B : Type'} (H : type549 A B) (x''' : type569 A B) : (term296 A B H x''') = (term1306 A B H x''').
Proof. exact (MK_COMB (@lem350510) (@lem350509 A B H x''')). Qed.
Lemma lem350512 {A B : Type'} (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) : (term326 A B x''' H f''' f'') = (term1307 A B x''' H f''' f'').
Proof. exact (MK_COMB (@lem350511 A B H x''') (@lem350462 A B H f''' f'')). Qed.
Lemma lem350513 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem350520 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350521 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem350520 (A -> B) (A -> B) f x). Qed.
Lemma lem350522 {A B : Type'} (H : type549 A B) (f : A -> B) : (H f) = (@I ((A -> B) -> A -> B) H f).
Proof. exact (@lem350521 A B H f). Qed.
Lemma lem350523 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem350524 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (H f x) = (@I ((A -> B) -> A -> B) H f x).
Proof. exact (MK_COMB (@lem350522 A B H f) (@lem350523 A x)). Qed.
Lemma lem350526 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350527 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350526 A B f x). Qed.
Lemma lem350528 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (@I ((A -> B) -> A -> B) H f x) = (term1286 A B H f x).
Proof. exact (@lem350527 A B (@I ((A -> B) -> A -> B) H f) x). Qed.
Lemma lem350530 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (H f x) = (term1286 A B H f x).
Proof. exact (TRANS (@lem350524 A B H f x) (@lem350528 A B H f x)). Qed.
Lemma lem350537 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350538 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem350537 (A -> B) (A -> B) f x). Qed.
Lemma lem350539 {A B : Type'} (H : type549 A B) (g : A -> B) : (H g) = (@I ((A -> B) -> A -> B) H g).
Proof. exact (@lem350538 A B H g). Qed.
Lemma lem350540 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem350541 {A B : Type'} (H : type549 A B) (g : A -> B) (x : A) : (H g x) = (@I ((A -> B) -> A -> B) H g x).
Proof. exact (MK_COMB (@lem350539 A B H g) (@lem350540 A x)). Qed.
Lemma lem350543 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350543 A B f x). Qed.
Lemma lem350545 {A B : Type'} (H : type549 A B) (g : A -> B) (x : A) : (@I ((A -> B) -> A -> B) H g x) = (term1286 A B H g x).
Proof. exact (@lem350544 A B (@I ((A -> B) -> A -> B) H g) x). Qed.
Lemma lem350547 {A B : Type'} (H : type549 A B) (g : A -> B) (x : A) : (H g x) = (term1286 A B H g x).
Proof. exact (TRANS (@lem350541 A B H g x) (@lem350545 A B H g x)). Qed.
Lemma lem350548 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term1308 A B H f x) = (term1309 A B H f x).
Proof. exact (MK_COMB (@lem350513 B) (@lem350530 A B H f x)). Qed.
Lemma lem350549 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : ((H f x) = (H g x)) = ((term1286 A B H f x) = (term1286 A B H g x)).
Proof. exact (MK_COMB (@lem350548 A B H f x) (@lem350547 A B H g x)). Qed.
Lemma lem350550 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem350551 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem350552 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem350561 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350562 {A B : Type'} (f : type515 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> A -> A) f x).
Proof. exact (@lem350561 (A -> B) (type548 A B) f x). Qed.
Lemma lem350563 {A B : Type'} (z : type515 A B) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> A -> A) z f).
Proof. exact (@lem350562 A B z f). Qed.
Lemma lem350564 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem350565 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> A -> A) z f g).
Proof. exact (MK_COMB (@lem350563 A B z f) (@lem350564 A B g)). Qed.
Lemma lem350567 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350568 {A B : Type'} (f : type548 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> A) f x).
Proof. exact (@lem350567 (A -> B) (A -> A) f x). Qed.
Lemma lem350569 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> A -> A) z f g) = (term1310 A B z f g).
Proof. exact (@lem350568 A B (@I ((A -> B) -> (A -> B) -> A -> A) z f) g). Qed.
Lemma lem350570 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) : (z f g) = (term1310 A B z f g).
Proof. exact (TRANS (@lem350565 A B z f g) (@lem350569 A B z f g)). Qed.
Lemma lem350571 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem350572 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (z f g x) = (term1311 A B z f g x).
Proof. exact (MK_COMB (@lem350570 A B z f g) (@lem350571 A x)). Qed.
Lemma lem350574 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350575 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem350574 A A f x). Qed.
Lemma lem350576 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1311 A B z f g x) = (term1312 A B z f g x).
Proof. exact (@lem350575 A (term1310 A B z f g) x). Qed.
Lemma lem350578 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (z f g x) = (term1312 A B z f g x).
Proof. exact (TRANS (@lem350572 A B z f g x) (@lem350576 A B z f g x)). Qed.
Lemma lem350579 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1313 A B z f g x) = (term1314 A B z f g x).
Proof. exact (MK_COMB (@lem350552 A B f) (@lem350578 A B z f g x)). Qed.
Lemma lem350581 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350582 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350581 A B f x). Qed.
Lemma lem350583 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1314 A B z f g x) = (term1315 A B z f g x).
Proof. exact (@lem350582 A B f (term1312 A B z f g x)). Qed.
Lemma lem350584 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1313 A B z f g x) = (term1315 A B z f g x).
Proof. exact (TRANS (@lem350579 A B z f g x) (@lem350583 A B z f g x)). Qed.
Lemma lem350585 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem350594 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350595 {A B : Type'} (f : type515 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> A -> A) f x).
Proof. exact (@lem350594 (A -> B) (type548 A B) f x). Qed.
Lemma lem350596 {A B : Type'} (z : type515 A B) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> A -> A) z f).
Proof. exact (@lem350595 A B z f). Qed.
Lemma lem350597 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem350598 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> A -> A) z f g).
Proof. exact (MK_COMB (@lem350596 A B z f) (@lem350597 A B g)). Qed.
Lemma lem350600 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350601 {A B : Type'} (f : type548 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> A) f x).
Proof. exact (@lem350600 (A -> B) (A -> A) f x). Qed.
Lemma lem350602 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> A -> A) z f g) = (term1310 A B z f g).
Proof. exact (@lem350601 A B (@I ((A -> B) -> (A -> B) -> A -> A) z f) g). Qed.
Lemma lem350603 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) : (z f g) = (term1310 A B z f g).
Proof. exact (TRANS (@lem350598 A B z f g) (@lem350602 A B z f g)). Qed.
Lemma lem350604 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem350605 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (z f g x) = (term1311 A B z f g x).
Proof. exact (MK_COMB (@lem350603 A B z f g) (@lem350604 A x)). Qed.
Lemma lem350607 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350608 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem350607 A A f x). Qed.
Lemma lem350609 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1311 A B z f g x) = (term1312 A B z f g x).
Proof. exact (@lem350608 A (term1310 A B z f g) x). Qed.
Lemma lem350611 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (z f g x) = (term1312 A B z f g x).
Proof. exact (TRANS (@lem350605 A B z f g x) (@lem350609 A B z f g x)). Qed.
Lemma lem350612 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1316 A B z f g x) = (term1317 A B z f g x).
Proof. exact (MK_COMB (@lem350585 A B g) (@lem350611 A B z f g x)). Qed.
Lemma lem350614 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350615 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem350614 A B f x). Qed.
Lemma lem350616 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1317 A B z f g x) = (term1318 A B z f g x).
Proof. exact (@lem350615 A B g (term1312 A B z f g x)). Qed.
Lemma lem350617 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1316 A B z f g x) = (term1318 A B z f g x).
Proof. exact (TRANS (@lem350612 A B z f g x) (@lem350616 A B z f g x)). Qed.
Lemma lem350618 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1319 A B z f g x) = (term1320 A B z f g x).
Proof. exact (MK_COMB (@lem350551 B) (@lem350584 A B z f g x)). Qed.
Lemma lem350619 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : ((term1313 A B z f g x) = (term1316 A B z f g x)) = ((term1315 A B z f g x) = (term1318 A B z f g x)).
Proof. exact (MK_COMB (@lem350618 A B z f g x) (@lem350617 A B z f g x)). Qed.
Lemma lem350620 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1321 A B z f g x) = (term1322 A B z f g x).
Proof. exact (MK_COMB (@lem350550) (@lem350619 A B z f g x)). Qed.
Lemma lem350621 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem350630 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350631 {A B : Type'} (f : type515 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> A -> A) f x).
Proof. exact (@lem350630 (A -> B) (type548 A B) f x). Qed.
Lemma lem350632 {A B : Type'} (z : type515 A B) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> A -> A) z f).
Proof. exact (@lem350631 A B z f). Qed.
Lemma lem350633 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem350634 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> A -> A) z f g).
Proof. exact (MK_COMB (@lem350632 A B z f) (@lem350633 A B g)). Qed.
Lemma lem350636 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350637 {A B : Type'} (f : type548 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> A) f x).
Proof. exact (@lem350636 (A -> B) (A -> A) f x). Qed.
Lemma lem350638 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> A -> A) z f g) = (term1310 A B z f g).
Proof. exact (@lem350637 A B (@I ((A -> B) -> (A -> B) -> A -> A) z f) g). Qed.
Lemma lem350639 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) : (z f g) = (term1310 A B z f g).
Proof. exact (TRANS (@lem350634 A B z f g) (@lem350638 A B z f g)). Qed.
Lemma lem350640 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem350641 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (z f g x) = (term1311 A B z f g x).
Proof. exact (MK_COMB (@lem350639 A B z f g) (@lem350640 A x)). Qed.
Lemma lem350643 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350644 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem350643 A A f x). Qed.
Lemma lem350645 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1311 A B z f g x) = (term1312 A B z f g x).
Proof. exact (@lem350644 A (term1310 A B z f g) x). Qed.
Lemma lem350647 {A B : Type'} (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (z f g x) = (term1312 A B z f g x).
Proof. exact (TRANS (@lem350641 A B z f g x) (@lem350645 A B z f g x)). Qed.
Lemma lem350648 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem350649 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1323 A B lt2 z f g x) = (term1324 A B lt2 z f g x).
Proof. exact (MK_COMB (@lem350621 A lt2) (@lem350647 A B z f g x)). Qed.
Lemma lem350650 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1325 A B lt2 z f g x) = (term1326 A B lt2 z f g x).
Proof. exact (MK_COMB (@lem350649 A B lt2 z f g x) (@lem350648 A x)). Qed.
Lemma lem350652 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350653 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem350652 A (A -> Prop) f x). Qed.
Lemma lem350654 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1324 A B lt2 z f g x) = (term1327 A B lt2 z f g x).
Proof. exact (@lem350653 A lt2 (term1312 A B z f g x)). Qed.
Lemma lem350655 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem350656 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1326 A B lt2 z f g x) = (term1328 A B lt2 z f g x).
Proof. exact (MK_COMB (@lem350654 A B lt2 z f g x) (@lem350655 A x)). Qed.
Lemma lem350658 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350659 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem350658 A Prop f x). Qed.
Lemma lem350660 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1328 A B lt2 z f g x) = (term1329 A B lt2 z f g x).
Proof. exact (@lem350659 A (term1327 A B lt2 z f g x) x). Qed.
Lemma lem350661 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1326 A B lt2 z f g x) = (term1329 A B lt2 z f g x).
Proof. exact (TRANS (@lem350656 A B lt2 z f g x) (@lem350660 A B lt2 z f g x)). Qed.
Lemma lem350662 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1325 A B lt2 z f g x) = (term1329 A B lt2 z f g x).
Proof. exact (TRANS (@lem350650 A B lt2 z f g x) (@lem350661 A B lt2 z f g x)). Qed.
Lemma lem350663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem350664 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1330 A B lt2 z f g x) = (term1331 A B lt2 z f g x).
Proof. exact (MK_COMB (@lem350663) (@lem350662 A B lt2 z f g x)). Qed.
Lemma lem350665 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1332 A B lt2 z f g x) = (term1333 A B lt2 z f g x).
Proof. exact (MK_COMB (@lem350664 A B lt2 z f g x) (@lem350620 A B z f g x)). Qed.
Lemma lem350666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350667 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (g : A -> B) (x : A) : (term1334 A B lt2 z f g x) = (term1335 A B lt2 z f g x).
Proof. exact (MK_COMB (@lem350666) (@lem350665 A B lt2 z f g x)). Qed.
Lemma lem350668 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term1336 A B lt2 z f H g x) = (term1337 A B lt2 z f H g x).
Proof. exact (MK_COMB (@lem350667 A B lt2 z f g x) (@lem350549 A B f H g x)). Qed.
Lemma lem350669 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) (g : A -> B) : (term1338 A B lt2 z f H g) = (term1339 A B lt2 z f H g).
Proof. exact (fun_ext (fun x : A => @lem350668 A B lt2 z f H g x)). Qed.
Lemma lem350670 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350671 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) (g : A -> B) : (term1340 A B lt2 z f H g) = (term1341 A B lt2 z f H g).
Proof. exact (MK_COMB (@lem350670 A) (@lem350669 A B lt2 z f H g)). Qed.
Lemma lem350672 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) : (term1342 A B lt2 z f H) = (term1343 A B lt2 z f H).
Proof. exact (fun_ext (fun g : A -> B => @lem350671 A B lt2 z f H g)). Qed.
Lemma lem350673 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem350674 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) : (term249 A B lt2 z f H) = (term1344 A B lt2 z f H).
Proof. exact (MK_COMB (@lem350673 A B) (@lem350672 A B lt2 z f H)). Qed.
Lemma lem350675 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term251 A B lt2 z H) = (term1345 A B lt2 z H).
Proof. exact (fun_ext (fun f : A -> B => @lem350674 A B lt2 z f H)). Qed.
Lemma lem350676 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem350677 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term253 A B lt2 z H) = (term1346 A B lt2 z H).
Proof. exact (MK_COMB (@lem350676 A B) (@lem350675 A B lt2 z H)). Qed.
Lemma lem350678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem350679 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term348 A B lt2 z H) = (term1347 A B lt2 z H).
Proof. exact (MK_COMB (@lem350678) (@lem350677 A B lt2 z H)). Qed.
Lemma lem350680 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) : (term388 A B lt2 z x''' H f''' f'') = (term1348 A B lt2 z x''' H f''' f'').
Proof. exact (MK_COMB (@lem350679 A B lt2 z H) (@lem350512 A B x''' H f''' f'')). Qed.
Lemma lem350685 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem350686 {A : Type'} (f : type421 A) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> Prop) f x).
Proof. exact (@lem350685 (type1402 A) Prop f x). Qed.
Lemma lem350688 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem350686 A (@WF A) lt2). Qed.
Lemma lem350689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem350690 {A : Type'} (lt2 : type1402 A) : (term137 A lt2) = (term1349 A lt2).
Proof. exact (MK_COMB (@lem350689) (@lem350688 A lt2)). Qed.
Lemma lem350691 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) : (term461 A B lt2 z x''' H f''' f'') = (term1350 A B lt2 z x''' H f''' f'').
Proof. exact (MK_COMB (@lem350690 A lt2) (@lem350680 A B lt2 z x''' H f''' f'')). Qed.
Lemma lem350692 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1350 A B lt2 z x''' H f''' f''.
Proof. exact (EQ_MP (@lem350691 A B lt2 z x''' H f''' f'') (@lem349659 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem350693 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1348 A B lt2 z x''' H f''' f''.
Proof. exact (proj2 (@lem350692 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem350695 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1307 A B x''' H f''' f''.
Proof. exact (proj2 (@lem350693 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem350696 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1346 A B lt2 z H.
Proof. exact (proj1 (@lem350693 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem350697 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (h1 : term1305 A B H x''') : term1305 A B H x'''.
Proof. exact (h1). Qed.
Lemma lem350698 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1293 A B H f''' f''.
Proof. exact (h1). Qed.
Lemma lem350699 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1292 A B H f''' f''.
Proof. exact (proj2 (@lem350698 A B H f''' f'' h1)). Qed.
Lemma lem350700 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1290 A B H f''.
Proof. exact (proj1 (@lem350698 A B H f''' f'' h1)). Qed.
Lemma lem350702 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1290 A B H f'''.
Proof. exact (proj1 (@lem350699 A B H f''' f'' h1)). Qed.
Lemma lem350704 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1351 A P Q) = (term1352 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem350705 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1351 A P Q) = (term1352 A P Q).
Proof. exact (@lem350704 A P Q). Qed.
Lemma lem350706 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1353 A B f g x lt2 H) = (term1354 A B f g x lt2 H).
Proof. exact (@lem350705 A (term1214 A B x f g lt2 H) (term1202 A B f g x lt2 H)). Qed.
Lemma lem350707 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1355 A B x f g lt2 H z) = (term1212 A B x f g lt2 H z).
Proof. exact (eq_refl (term1355 A B x f g lt2 H z)). Qed.
Lemma lem350708 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1356 A B x f g lt2 H) = (term1214 A B x f g lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350707 A B x f g lt2 H z)). Qed.
Lemma lem350709 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350710 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1357 A B x f g lt2 H) = (term1216 A B x f g lt2 H).
Proof. exact (MK_COMB (@lem350709 A) (@lem350708 A B x f g lt2 H)). Qed.
Lemma lem350711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem350712 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1358 A B x f g lt2 H) = (term1218 A B x f g lt2 H).
Proof. exact (MK_COMB (@lem350711) (@lem350710 A B x f g lt2 H)). Qed.
Lemma lem350713 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1202 A B f g x lt2 H) = (term1202 A B f g x lt2 H).
Proof. exact (eq_refl (term1202 A B f g x lt2 H)). Qed.
Lemma lem350714 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1353 A B f g x lt2 H) = (term1220 A B f g x lt2 H).
Proof. exact (MK_COMB (@lem350712 A B x f g lt2 H) (@lem350713 A B f g x lt2 H)). Qed.
Lemma lem350715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem350716 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1359 A B f g x lt2 H) = (term1360 A B f g x lt2 H).
Proof. exact (MK_COMB (@lem350715) (@lem350714 A B f g x lt2 H)). Qed.
Lemma lem350717 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1355 A B x f g lt2 H z) = (term1212 A B x f g lt2 H z).
Proof. exact (eq_refl (term1355 A B x f g lt2 H z)). Qed.
Lemma lem350718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem350719 {A B : Type'} (x : type410 A B) (f : type409 A B) (g : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1361 A B x f g lt2 H z) = (term1362 A B x f g lt2 H z).
Proof. exact (MK_COMB (@lem350718) (@lem350717 A B x f g lt2 H z)). Qed.
Lemma lem350720 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1202 A B f g x lt2 H) = (term1202 A B f g x lt2 H).
Proof. exact (eq_refl (term1202 A B f g x lt2 H)). Qed.
Lemma lem350721 {A B : Type'} (z : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1363 A B z f g x lt2 H) = (term1364 A B z f g x lt2 H).
Proof. exact (MK_COMB (@lem350719 A B x f g lt2 H z) (@lem350720 A B f g x lt2 H)). Qed.
Lemma lem350722 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1365 A B f g x lt2 H) = (term1366 A B f g x lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350721 A B z f g x lt2 H)). Qed.
Lemma lem350723 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350724 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1354 A B f g x lt2 H) = (term1367 A B f g x lt2 H).
Proof. exact (MK_COMB (@lem350723 A) (@lem350722 A B f g x lt2 H)). Qed.
Lemma lem350725 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1353 A B f g x lt2 H) = (term1354 A B f g x lt2 H)) = ((term1220 A B f g x lt2 H) = (term1367 A B f g x lt2 H)).
Proof. exact (MK_COMB (@lem350716 A B f g x lt2 H) (@lem350724 A B f g x lt2 H)). Qed.
Lemma lem350726 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1220 A B f g x lt2 H) = (term1367 A B f g x lt2 H).
Proof. exact (EQ_MP (@lem350725 A B f g x lt2 H) (@lem350706 A B f g x lt2 H)). Qed.
Lemma lem350727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350728 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1222 A B f g x lt2 H) = (term1368 A B f g x lt2 H).
Proof. exact (MK_COMB (@lem350727) (@lem350726 A B f g x lt2 H)). Qed.
Lemma lem350729 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1193 A B f lt2 H) = (term1193 A B f lt2 H).
Proof. exact (eq_refl (term1193 A B f lt2 H)). Qed.
Lemma lem350730 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1224 A B g x f lt2 H) = (term1369 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350728 A B f g x lt2 H) (@lem350729 A B f lt2 H)). Qed.
Lemma lem350732 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1370 A P Q) = (term1371 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem350733 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1370 A P Q) = (term1371 A P Q).
Proof. exact (@lem350732 A P Q). Qed.
Lemma lem350734 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1372 A B g x f lt2 H) = (term1373 A B g x f lt2 H).
Proof. exact (@lem350733 A (term1366 A B f g x lt2 H) (term1193 A B f lt2 H)). Qed.
Lemma lem350735 {A B : Type'} (z : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1374 A B f g x lt2 H z) = (term1364 A B z f g x lt2 H).
Proof. exact (eq_refl (term1374 A B f g x lt2 H z)). Qed.
Lemma lem350736 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1375 A B f g x lt2 H) = (term1366 A B f g x lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350735 A B z f g x lt2 H)). Qed.
Lemma lem350737 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350738 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1376 A B f g x lt2 H) = (term1367 A B f g x lt2 H).
Proof. exact (MK_COMB (@lem350737 A) (@lem350736 A B f g x lt2 H)). Qed.
Lemma lem350739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350740 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1377 A B f g x lt2 H) = (term1368 A B f g x lt2 H).
Proof. exact (MK_COMB (@lem350739) (@lem350738 A B f g x lt2 H)). Qed.
Lemma lem350741 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1193 A B f lt2 H) = (term1193 A B f lt2 H).
Proof. exact (eq_refl (term1193 A B f lt2 H)). Qed.
Lemma lem350742 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1372 A B g x f lt2 H) = (term1369 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350740 A B f g x lt2 H) (@lem350741 A B f lt2 H)). Qed.
Lemma lem350743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem350744 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1378 A B g x f lt2 H) = (term1379 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350743) (@lem350742 A B g x f lt2 H)). Qed.
Lemma lem350745 {A B : Type'} (z : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1374 A B f g x lt2 H z) = (term1364 A B z f g x lt2 H).
Proof. exact (eq_refl (term1374 A B f g x lt2 H z)). Qed.
Lemma lem350746 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem350747 {A B : Type'} (z : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1380 A B f g x lt2 H z) = (term1381 A B z f g x lt2 H).
Proof. exact (MK_COMB (@lem350746) (@lem350745 A B z f g x lt2 H)). Qed.
Lemma lem350748 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1193 A B f lt2 H) = (term1193 A B f lt2 H).
Proof. exact (eq_refl (term1193 A B f lt2 H)). Qed.
Lemma lem350749 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1382 A B g x z f lt2 H) = (term1383 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350747 A B z f g x lt2 H) (@lem350748 A B f lt2 H)). Qed.
Lemma lem350750 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1384 A B g x f lt2 H) = (term1385 A B g x f lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350749 A B z g x f lt2 H)). Qed.
Lemma lem350751 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350752 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1373 A B g x f lt2 H) = (term1386 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350751 A) (@lem350750 A B g x f lt2 H)). Qed.
Lemma lem350753 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1372 A B g x f lt2 H) = (term1373 A B g x f lt2 H)) = ((term1369 A B g x f lt2 H) = (term1386 A B g x f lt2 H)).
Proof. exact (MK_COMB (@lem350744 A B g x f lt2 H) (@lem350752 A B g x f lt2 H)). Qed.
Lemma lem350754 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1369 A B g x f lt2 H) = (term1386 A B g x f lt2 H).
Proof. exact (EQ_MP (@lem350753 A B g x f lt2 H) (@lem350734 A B g x f lt2 H)). Qed.
Lemma lem350756 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem350757 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (@lem350756 A P Q). Qed.
Lemma lem350758 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1389 A B z g x f lt2 H) = (term1390 A B z g x f lt2 H).
Proof. exact (@lem350757 A (term1364 A B z f g x lt2 H) (term1191 A B f lt2 H)). Qed.
Lemma lem350759 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (term1391 A B f lt2 H x) = ((term1180 A B f lt2 H x) = (term1187 A B f lt2 H x)).
Proof. exact (eq_refl (term1391 A B f lt2 H x)). Qed.
Lemma lem350760 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1392 A B f lt2 H) = (term1191 A B f lt2 H).
Proof. exact (fun_ext (fun x : A => @lem350759 A B f lt2 H x)). Qed.
Lemma lem350761 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350762 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1393 A B f lt2 H) = (term1193 A B f lt2 H).
Proof. exact (MK_COMB (@lem350761 A) (@lem350760 A B f lt2 H)). Qed.
Lemma lem350763 {A B : Type'} (z : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1381 A B z f g x lt2 H) = (term1381 A B z f g x lt2 H).
Proof. exact (eq_refl (term1381 A B z f g x lt2 H)). Qed.
Lemma lem350764 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1389 A B z g x f lt2 H) = (term1383 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350763 A B z f g x lt2 H) (@lem350762 A B f lt2 H)). Qed.
Lemma lem350765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem350766 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1394 A B z g x f lt2 H) = (term1395 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350765) (@lem350764 A B z g x f lt2 H)). Qed.
Lemma lem350767 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x : A) : (term1391 A B f lt2 H x) = ((term1180 A B f lt2 H x) = (term1187 A B f lt2 H x)).
Proof. exact (eq_refl (term1391 A B f lt2 H x)). Qed.
Lemma lem350768 {A B : Type'} (z : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1381 A B z f g x lt2 H) = (term1381 A B z f g x lt2 H).
Proof. exact (eq_refl (term1381 A B z f g x lt2 H)). Qed.
Lemma lem350769 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x' : A) : (term1396 A B z g x f lt2 H x') = (term1397 A B z g x f lt2 H x').
Proof. exact (MK_COMB (@lem350768 A B z f g x lt2 H) (@lem350767 A B f lt2 H x')). Qed.
Lemma lem350770 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1398 A B z g x f lt2 H) = (term1399 A B z g x f lt2 H).
Proof. exact (fun_ext (fun x' : A => @lem350769 A B z g x f lt2 H x')). Qed.
Lemma lem350771 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350772 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1390 A B z g x f lt2 H) = (term1400 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350771 A) (@lem350770 A B z g x f lt2 H)). Qed.
Lemma lem350773 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1389 A B z g x f lt2 H) = (term1390 A B z g x f lt2 H)) = ((term1383 A B z g x f lt2 H) = (term1400 A B z g x f lt2 H)).
Proof. exact (MK_COMB (@lem350766 A B z g x f lt2 H) (@lem350772 A B z g x f lt2 H)). Qed.
Lemma lem350774 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1383 A B z g x f lt2 H) = (term1400 A B z g x f lt2 H).
Proof. exact (EQ_MP (@lem350773 A B z g x f lt2 H) (@lem350758 A B z g x f lt2 H)). Qed.
Lemma lem350775 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1385 A B g x f lt2 H) = (term1401 A B g x f lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350774 A B z g x f lt2 H)). Qed.
Lemma lem350776 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350777 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1386 A B g x f lt2 H) = (term1402 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350776 A) (@lem350775 A B g x f lt2 H)). Qed.
Lemma lem350778 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1369 A B g x f lt2 H) = (term1402 A B g x f lt2 H).
Proof. exact (TRANS (@lem350754 A B g x f lt2 H) (@lem350777 A B g x f lt2 H)). Qed.
Lemma lem350779 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1224 A B g x f lt2 H) = (term1402 A B g x f lt2 H).
Proof. exact (TRANS (@lem350730 A B g x f lt2 H) (@lem350778 A B g x f lt2 H)). Qed.
Lemma lem350780 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1226 A B g x f lt2) = (term1403 A B g x f lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem350779 A B g x f lt2 H)). Qed.
Lemma lem350781 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem350782 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1228 A B g x f lt2) = (term1404 A B g x f lt2).
Proof. exact (MK_COMB (@lem350781 A B) (@lem350780 A B g x f lt2)). Qed.
Lemma lem350783 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem350784 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1231 A B g x f lt2) = (term1405 A B g x f lt2).
Proof. exact (MK_COMB (@lem350783 A lt2) (@lem350782 A B g x f lt2)). Qed.
Lemma lem350786 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem350787 {A B : Type'} (P : Prop) (Q : type111 A B) : (term1406 A B P Q) = (term1407 A B P Q).
Proof. exact (@lem350786 (type549 A B) P Q). Qed.
Lemma lem350788 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1408 A B g x f lt2) = (term1409 A B g x f lt2).
Proof. exact (@lem350787 A B (term1229 A lt2) (term1403 A B g x f lt2)). Qed.
Lemma lem350789 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1410 A B g x f lt2 H) = (term1402 A B g x f lt2 H).
Proof. exact (eq_refl (term1410 A B g x f lt2 H)). Qed.
Lemma lem350790 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1411 A B g x f lt2) = (term1403 A B g x f lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem350789 A B g x f lt2 H)). Qed.
Lemma lem350791 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem350792 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1412 A B g x f lt2) = (term1404 A B g x f lt2).
Proof. exact (MK_COMB (@lem350791 A B) (@lem350790 A B g x f lt2)). Qed.
Lemma lem350793 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem350794 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1408 A B g x f lt2) = (term1405 A B g x f lt2).
Proof. exact (MK_COMB (@lem350793 A lt2) (@lem350792 A B g x f lt2)). Qed.
Lemma lem350795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem350796 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1413 A B g x f lt2) = (term1414 A B g x f lt2).
Proof. exact (MK_COMB (@lem350795) (@lem350794 A B g x f lt2)). Qed.
Lemma lem350797 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1410 A B g x f lt2 H) = (term1402 A B g x f lt2 H).
Proof. exact (eq_refl (term1410 A B g x f lt2 H)). Qed.
Lemma lem350798 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem350799 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1415 A B g x f lt2 H) = (term1416 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350798 A lt2) (@lem350797 A B g x f lt2 H)). Qed.
Lemma lem350800 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1417 A B g x f lt2) = (term1418 A B g x f lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem350799 A B g x f lt2 H)). Qed.
Lemma lem350801 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem350802 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1409 A B g x f lt2) = (term1419 A B g x f lt2).
Proof. exact (MK_COMB (@lem350801 A B) (@lem350800 A B g x f lt2)). Qed.
Lemma lem350803 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : ((term1408 A B g x f lt2) = (term1409 A B g x f lt2)) = ((term1405 A B g x f lt2) = (term1419 A B g x f lt2)).
Proof. exact (MK_COMB (@lem350796 A B g x f lt2) (@lem350802 A B g x f lt2)). Qed.
Lemma lem350804 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1405 A B g x f lt2) = (term1419 A B g x f lt2).
Proof. exact (EQ_MP (@lem350803 A B g x f lt2) (@lem350788 A B g x f lt2)). Qed.
Lemma lem350806 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem350807 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (@lem350806 A P Q). Qed.
Lemma lem350808 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1420 A B g x f lt2 H) = (term1421 A B g x f lt2 H).
Proof. exact (@lem350807 A (term1229 A lt2) (term1401 A B g x f lt2 H)). Qed.
Lemma lem350809 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1422 A B g x f lt2 H z) = (term1400 A B z g x f lt2 H).
Proof. exact (eq_refl (term1422 A B g x f lt2 H z)). Qed.
Lemma lem350810 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1423 A B g x f lt2 H) = (term1401 A B g x f lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350809 A B z g x f lt2 H)). Qed.
Lemma lem350811 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350812 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1424 A B g x f lt2 H) = (term1402 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350811 A) (@lem350810 A B g x f lt2 H)). Qed.
Lemma lem350813 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem350814 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1420 A B g x f lt2 H) = (term1416 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350813 A lt2) (@lem350812 A B g x f lt2 H)). Qed.
Lemma lem350815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem350816 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1425 A B g x f lt2 H) = (term1426 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350815) (@lem350814 A B g x f lt2 H)). Qed.
Lemma lem350817 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1422 A B g x f lt2 H z) = (term1400 A B z g x f lt2 H).
Proof. exact (eq_refl (term1422 A B g x f lt2 H z)). Qed.
Lemma lem350818 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem350819 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1427 A B g x f lt2 H z) = (term1428 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350818 A lt2) (@lem350817 A B z g x f lt2 H)). Qed.
Lemma lem350820 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1429 A B g x f lt2 H) = (term1430 A B g x f lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350819 A B z g x f lt2 H)). Qed.
Lemma lem350821 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350822 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1421 A B g x f lt2 H) = (term1431 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350821 A) (@lem350820 A B g x f lt2 H)). Qed.
Lemma lem350823 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1420 A B g x f lt2 H) = (term1421 A B g x f lt2 H)) = ((term1416 A B g x f lt2 H) = (term1431 A B g x f lt2 H)).
Proof. exact (MK_COMB (@lem350816 A B g x f lt2 H) (@lem350822 A B g x f lt2 H)). Qed.
Lemma lem350824 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1416 A B g x f lt2 H) = (term1431 A B g x f lt2 H).
Proof. exact (EQ_MP (@lem350823 A B g x f lt2 H) (@lem350808 A B g x f lt2 H)). Qed.
Lemma lem350826 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem350827 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (@lem350826 A P Q). Qed.
Lemma lem350828 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1432 A B z g x f lt2 H) = (term1433 A B z g x f lt2 H).
Proof. exact (@lem350827 A (term1229 A lt2) (term1399 A B z g x f lt2 H)). Qed.
Lemma lem350829 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x' : A) : (term1434 A B z g x f lt2 H x') = (term1397 A B z g x f lt2 H x').
Proof. exact (eq_refl (term1434 A B z g x f lt2 H x')). Qed.
Lemma lem350830 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1435 A B z g x f lt2 H) = (term1399 A B z g x f lt2 H).
Proof. exact (fun_ext (fun x' : A => @lem350829 A B z g x f lt2 H x')). Qed.
Lemma lem350831 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350832 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1436 A B z g x f lt2 H) = (term1400 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350831 A) (@lem350830 A B z g x f lt2 H)). Qed.
Lemma lem350833 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem350834 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1432 A B z g x f lt2 H) = (term1428 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350833 A lt2) (@lem350832 A B z g x f lt2 H)). Qed.
Lemma lem350835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem350836 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1437 A B z g x f lt2 H) = (term1438 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350835) (@lem350834 A B z g x f lt2 H)). Qed.
Lemma lem350837 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x' : A) : (term1434 A B z g x f lt2 H x') = (term1397 A B z g x f lt2 H x').
Proof. exact (eq_refl (term1434 A B z g x f lt2 H x')). Qed.
Lemma lem350838 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem350839 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x' : A) : (term1439 A B z g x f lt2 H x') = (term1440 A B z g x f lt2 H x').
Proof. exact (MK_COMB (@lem350838 A lt2) (@lem350837 A B z g x f lt2 H x')). Qed.
Lemma lem350840 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1441 A B z g x f lt2 H) = (term1442 A B z g x f lt2 H).
Proof. exact (fun_ext (fun x' : A => @lem350839 A B z g x f lt2 H x')). Qed.
Lemma lem350841 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350842 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1433 A B z g x f lt2 H) = (term1443 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350841 A) (@lem350840 A B z g x f lt2 H)). Qed.
Lemma lem350843 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1432 A B z g x f lt2 H) = (term1433 A B z g x f lt2 H)) = ((term1428 A B z g x f lt2 H) = (term1443 A B z g x f lt2 H)).
Proof. exact (MK_COMB (@lem350836 A B z g x f lt2 H) (@lem350842 A B z g x f lt2 H)). Qed.
Lemma lem350844 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1428 A B z g x f lt2 H) = (term1443 A B z g x f lt2 H).
Proof. exact (EQ_MP (@lem350843 A B z g x f lt2 H) (@lem350828 A B z g x f lt2 H)). Qed.
Lemma lem350845 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1430 A B g x f lt2 H) = (term1444 A B g x f lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350844 A B z g x f lt2 H)). Qed.
Lemma lem350846 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350847 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1431 A B g x f lt2 H) = (term1445 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350846 A) (@lem350845 A B g x f lt2 H)). Qed.
Lemma lem350848 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1416 A B g x f lt2 H) = (term1445 A B g x f lt2 H).
Proof. exact (TRANS (@lem350824 A B g x f lt2 H) (@lem350847 A B g x f lt2 H)). Qed.
Lemma lem350849 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1418 A B g x f lt2) = (term1446 A B g x f lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem350848 A B g x f lt2 H)). Qed.
Lemma lem350850 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem350851 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1419 A B g x f lt2) = (term1447 A B g x f lt2).
Proof. exact (MK_COMB (@lem350850 A B) (@lem350849 A B g x f lt2)). Qed.
Lemma lem350852 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1405 A B g x f lt2) = (term1447 A B g x f lt2).
Proof. exact (TRANS (@lem350804 A B g x f lt2) (@lem350851 A B g x f lt2)). Qed.
Lemma lem350853 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1231 A B g x f lt2) = (term1447 A B g x f lt2).
Proof. exact (TRANS (@lem350784 A B g x f lt2) (@lem350852 A B g x f lt2)). Qed.
Lemma lem350854 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) : (term1232 A B g x f) = (term1448 A B g x f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem350853 A B g x f lt2)). Qed.
Lemma lem350855 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem350856 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) : (term1233 A B g x f) = (term1449 A B g x f).
Proof. exact (MK_COMB (@lem350855 A) (@lem350854 A B g x f)). Qed.
Lemma lem350879 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x' : A) : (term1397 A B z g x f lt2 H x') = (term1450 A B z g x f lt2 H x').
Proof. exact (@lem19699 (term1212 A B x f g lt2 H z) (term1202 A B f g x lt2 H) ((term1180 A B f lt2 H x') = (term1187 A B f lt2 H x'))). Qed.
Lemma lem350882 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem350883 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x' : A) : (term1440 A B z g x f lt2 H x') = (term1451 A B z g x f lt2 H x').
Proof. exact (MK_COMB (@lem350882 A lt2) (@lem350879 A B z g x f lt2 H x')). Qed.
Lemma lem350890 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x' : A) : (term1451 A B z g x f lt2 H x') = (term1452 A B z g x f lt2 H x').
Proof. exact (@lem19490 (term1453 A B x g z f lt2 H x') (term1229 A lt2) (term1454 A B g x f lt2 H x')). Qed.
Lemma lem350891 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x' : A) : (term1440 A B z g x f lt2 H x') = (term1452 A B z g x f lt2 H x').
Proof. exact (TRANS (@lem350883 A B z g x f lt2 H x') (@lem350890 A B z g x f lt2 H x')). Qed.
Lemma lem350892 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1442 A B z g x f lt2 H) = (term1455 A B z g x f lt2 H).
Proof. exact (fun_ext (fun x' : A => @lem350891 A B z g x f lt2 H x')). Qed.
Lemma lem350893 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350894 {A B : Type'} (z : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1443 A B z g x f lt2 H) = (term1456 A B z g x f lt2 H).
Proof. exact (MK_COMB (@lem350893 A) (@lem350892 A B z g x f lt2 H)). Qed.
Lemma lem350895 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1444 A B g x f lt2 H) = (term1457 A B g x f lt2 H).
Proof. exact (fun_ext (fun z : A => @lem350894 A B z g x f lt2 H)). Qed.
Lemma lem350896 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem350897 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1445 A B g x f lt2 H) = (term1458 A B g x f lt2 H).
Proof. exact (MK_COMB (@lem350896 A) (@lem350895 A B g x f lt2 H)). Qed.
Lemma lem350898 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1446 A B g x f lt2) = (term1459 A B g x f lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem350897 A B g x f lt2 H)). Qed.
Lemma lem350899 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem350900 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) : (term1447 A B g x f lt2) = (term1460 A B g x f lt2).
Proof. exact (MK_COMB (@lem350899 A B) (@lem350898 A B g x f lt2)). Qed.
Lemma lem350901 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) : (term1448 A B g x f) = (term1461 A B g x f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem350900 A B g x f lt2)). Qed.
Lemma lem350902 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem350903 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) : (term1449 A B g x f) = (term1462 A B g x f).
Proof. exact (MK_COMB (@lem350902 A) (@lem350901 A B g x f)). Qed.
Lemma lem350904 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) : (term1233 A B g x f) = (term1462 A B g x f).
Proof. exact (TRANS (@lem350856 A B g x f) (@lem350903 A B g x f)). Qed.
Lemma lem350905 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1462 A B g x f.
Proof. exact (EQ_MP (@lem350904 A B g x f) (@lem349949 A B g x f h1)). Qed.
Lemma lem351193 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term1337 A B lt2 z f H g x) = (term1463 A B lt2 z f H g x).
Proof. exact (@lem19699 (term1329 A B lt2 z f g x) (term1322 A B z f g x) ((term1286 A B H f x) = (term1286 A B H g x))). Qed.
Lemma lem351194 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) (g : A -> B) : (term1339 A B lt2 z f H g) = (term1464 A B lt2 z f H g).
Proof. exact (fun_ext (fun x : A => @lem351193 A B lt2 z f H g x)). Qed.
Lemma lem351195 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351196 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) (g : A -> B) : (term1341 A B lt2 z f H g) = (term1465 A B lt2 z f H g).
Proof. exact (MK_COMB (@lem351195 A) (@lem351194 A B lt2 z f H g)). Qed.
Lemma lem351197 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) : (term1343 A B lt2 z f H) = (term1466 A B lt2 z f H).
Proof. exact (fun_ext (fun g : A -> B => @lem351196 A B lt2 z f H g)). Qed.
Lemma lem351198 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351199 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) : (term1344 A B lt2 z f H) = (term1467 A B lt2 z f H).
Proof. exact (MK_COMB (@lem351198 A B) (@lem351197 A B lt2 z f H)). Qed.
Lemma lem351200 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term1345 A B lt2 z H) = (term1468 A B lt2 z H).
Proof. exact (fun_ext (fun f : A -> B => @lem351199 A B lt2 z f H)). Qed.
Lemma lem351201 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351203 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term1346 A B lt2 z H) = (term1469 A B lt2 z H).
Proof. exact (MK_COMB (@lem351201 A B) (@lem351200 A B lt2 z H)). Qed.
Lemma lem351204 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1469 A B lt2 z H.
Proof. exact (EQ_MP (@lem351203 A B lt2 z H) (@lem350696 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351206 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (f : A -> B) : (term1303 A B H x''' f) = (term1303 A B H x''' f).
Proof. exact (eq_refl (term1303 A B H x''' f)). Qed.
Lemma lem351207 {A B : Type'} (H : type549 A B) (x''' : type569 A B) : (term1304 A B H x''') = (term1304 A B H x''').
Proof. exact (fun_ext (fun f : A -> B => @lem351206 A B H x''' f)). Qed.
Lemma lem351208 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351210 {A B : Type'} (H : type549 A B) (x''' : type569 A B) : (term1305 A B H x''') = (term1305 A B H x''').
Proof. exact (MK_COMB (@lem351208 A B) (@lem351207 A B H x''')). Qed.
Lemma lem351211 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (h1 : term1305 A B H x''') : term1305 A B H x'''.
Proof. exact (EQ_MP (@lem351210 A B H x''') (@lem350697 A B H x''' h1)). Qed.
Lemma lem351416 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1351 A P Q) = (term1352 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem351417 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1351 A P Q) = (term1352 A P Q).
Proof. exact (@lem351416 A P Q). Qed.
Lemma lem351418 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1353 A B f' g' x' lt2 H) = (term1354 A B f' g' x' lt2 H).
Proof. exact (@lem351417 A (term1214 A B x' f' g' lt2 H) (term1202 A B f' g' x' lt2 H)). Qed.
Lemma lem351419 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1355 A B x' f' g' lt2 H z) = (term1212 A B x' f' g' lt2 H z).
Proof. exact (eq_refl (term1355 A B x' f' g' lt2 H z)). Qed.
Lemma lem351420 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1356 A B x' f' g' lt2 H) = (term1214 A B x' f' g' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem351419 A B x' f' g' lt2 H z)). Qed.
Lemma lem351421 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351422 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1357 A B x' f' g' lt2 H) = (term1216 A B x' f' g' lt2 H).
Proof. exact (MK_COMB (@lem351421 A) (@lem351420 A B x' f' g' lt2 H)). Qed.
Lemma lem351423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem351424 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1358 A B x' f' g' lt2 H) = (term1218 A B x' f' g' lt2 H).
Proof. exact (MK_COMB (@lem351423) (@lem351422 A B x' f' g' lt2 H)). Qed.
Lemma lem351425 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1202 A B f' g' x' lt2 H) = (term1202 A B f' g' x' lt2 H).
Proof. exact (eq_refl (term1202 A B f' g' x' lt2 H)). Qed.
Lemma lem351426 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1353 A B f' g' x' lt2 H) = (term1220 A B f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem351424 A B x' f' g' lt2 H) (@lem351425 A B f' g' x' lt2 H)). Qed.
Lemma lem351427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem351428 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1359 A B f' g' x' lt2 H) = (term1360 A B f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem351427) (@lem351426 A B f' g' x' lt2 H)). Qed.
Lemma lem351429 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1355 A B x' f' g' lt2 H z) = (term1212 A B x' f' g' lt2 H z).
Proof. exact (eq_refl (term1355 A B x' f' g' lt2 H z)). Qed.
Lemma lem351430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem351431 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (H : type549 A B) (z : A) : (term1361 A B x' f' g' lt2 H z) = (term1362 A B x' f' g' lt2 H z).
Proof. exact (MK_COMB (@lem351430) (@lem351429 A B x' f' g' lt2 H z)). Qed.
Lemma lem351432 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1202 A B f' g' x' lt2 H) = (term1202 A B f' g' x' lt2 H).
Proof. exact (eq_refl (term1202 A B f' g' x' lt2 H)). Qed.
Lemma lem351433 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1363 A B z f' g' x' lt2 H) = (term1364 A B z f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem351431 A B x' f' g' lt2 H z) (@lem351432 A B f' g' x' lt2 H)). Qed.
Lemma lem351434 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1365 A B f' g' x' lt2 H) = (term1366 A B f' g' x' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem351433 A B z f' g' x' lt2 H)). Qed.
Lemma lem351435 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351436 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1354 A B f' g' x' lt2 H) = (term1367 A B f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem351435 A) (@lem351434 A B f' g' x' lt2 H)). Qed.
Lemma lem351437 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1353 A B f' g' x' lt2 H) = (term1354 A B f' g' x' lt2 H)) = ((term1220 A B f' g' x' lt2 H) = (term1367 A B f' g' x' lt2 H)).
Proof. exact (MK_COMB (@lem351428 A B f' g' x' lt2 H) (@lem351436 A B f' g' x' lt2 H)). Qed.
Lemma lem351438 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1220 A B f' g' x' lt2 H) = (term1367 A B f' g' x' lt2 H).
Proof. exact (EQ_MP (@lem351437 A B f' g' x' lt2 H) (@lem351418 A B f' g' x' lt2 H)). Qed.
Lemma lem351439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem351440 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1222 A B f' g' x' lt2 H) = (term1368 A B f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem351439) (@lem351438 A B f' g' x' lt2 H)). Qed.
Lemma lem351441 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1276 A B x'' lt2 H) = (term1276 A B x'' lt2 H).
Proof. exact (eq_refl (term1276 A B x'' lt2 H)). Qed.
Lemma lem351442 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1278 A B f' g' x' x'' lt2 H) = (term1470 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351440 A B f' g' x' lt2 H) (@lem351441 A B x'' lt2 H)). Qed.
Lemma lem351444 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1370 A P Q) = (term1371 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem351445 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1370 A P Q) = (term1371 A P Q).
Proof. exact (@lem351444 A P Q). Qed.
Lemma lem351446 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1471 A B f' g' x' x'' lt2 H) = (term1472 A B f' g' x' x'' lt2 H).
Proof. exact (@lem351445 A (term1366 A B f' g' x' lt2 H) (term1276 A B x'' lt2 H)). Qed.
Lemma lem351447 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1374 A B f' g' x' lt2 H z) = (term1364 A B z f' g' x' lt2 H).
Proof. exact (eq_refl (term1374 A B f' g' x' lt2 H z)). Qed.
Lemma lem351448 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1375 A B f' g' x' lt2 H) = (term1366 A B f' g' x' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem351447 A B z f' g' x' lt2 H)). Qed.
Lemma lem351449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351450 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1376 A B f' g' x' lt2 H) = (term1367 A B f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem351449 A) (@lem351448 A B f' g' x' lt2 H)). Qed.
Lemma lem351451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem351452 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1377 A B f' g' x' lt2 H) = (term1368 A B f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem351451) (@lem351450 A B f' g' x' lt2 H)). Qed.
Lemma lem351453 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1276 A B x'' lt2 H) = (term1276 A B x'' lt2 H).
Proof. exact (eq_refl (term1276 A B x'' lt2 H)). Qed.
Lemma lem351454 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1471 A B f' g' x' x'' lt2 H) = (term1470 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351452 A B f' g' x' lt2 H) (@lem351453 A B x'' lt2 H)). Qed.
Lemma lem351455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem351456 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1473 A B f' g' x' x'' lt2 H) = (term1474 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351455) (@lem351454 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351457 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1374 A B f' g' x' lt2 H z) = (term1364 A B z f' g' x' lt2 H).
Proof. exact (eq_refl (term1374 A B f' g' x' lt2 H z)). Qed.
Lemma lem351458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem351459 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1380 A B f' g' x' lt2 H z) = (term1381 A B z f' g' x' lt2 H).
Proof. exact (MK_COMB (@lem351458) (@lem351457 A B z f' g' x' lt2 H)). Qed.
Lemma lem351460 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1276 A B x'' lt2 H) = (term1276 A B x'' lt2 H).
Proof. exact (eq_refl (term1276 A B x'' lt2 H)). Qed.
Lemma lem351461 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1475 A B f' g' x' z x'' lt2 H) = (term1476 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351459 A B z f' g' x' lt2 H) (@lem351460 A B x'' lt2 H)). Qed.
Lemma lem351462 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1477 A B f' g' x' x'' lt2 H) = (term1478 A B f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem351461 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351463 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351464 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1472 A B f' g' x' x'' lt2 H) = (term1479 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351463 A) (@lem351462 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351465 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1471 A B f' g' x' x'' lt2 H) = (term1472 A B f' g' x' x'' lt2 H)) = ((term1470 A B f' g' x' x'' lt2 H) = (term1479 A B f' g' x' x'' lt2 H)).
Proof. exact (MK_COMB (@lem351456 A B f' g' x' x'' lt2 H) (@lem351464 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351466 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1470 A B f' g' x' x'' lt2 H) = (term1479 A B f' g' x' x'' lt2 H).
Proof. exact (EQ_MP (@lem351465 A B f' g' x' x'' lt2 H) (@lem351446 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351468 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem351469 {A B : Type'} (P : Prop) (Q : type572 A B) : (term1480 A B P Q) = (term1481 A B P Q).
Proof. exact (@lem351468 (A -> B) P Q). Qed.
Lemma lem351470 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1482 A B z f' g' x' x'' lt2 H) = (term1483 A B z f' g' x' x'' lt2 H).
Proof. exact (@lem351469 A B (term1364 A B z f' g' x' lt2 H) (term1274 A B x'' lt2 H)). Qed.
Lemma lem351471 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1484 A B x'' lt2 H f) = (term1272 A B x'' lt2 H f).
Proof. exact (eq_refl (term1484 A B x'' lt2 H f)). Qed.
Lemma lem351472 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1485 A B x'' lt2 H) = (term1274 A B x'' lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem351471 A B x'' lt2 H f)). Qed.
Lemma lem351473 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351474 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1486 A B x'' lt2 H) = (term1276 A B x'' lt2 H).
Proof. exact (MK_COMB (@lem351473 A B) (@lem351472 A B x'' lt2 H)). Qed.
Lemma lem351475 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1381 A B z f' g' x' lt2 H) = (term1381 A B z f' g' x' lt2 H).
Proof. exact (eq_refl (term1381 A B z f' g' x' lt2 H)). Qed.
Lemma lem351476 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1482 A B z f' g' x' x'' lt2 H) = (term1476 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351475 A B z f' g' x' lt2 H) (@lem351474 A B x'' lt2 H)). Qed.
Lemma lem351477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem351478 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1487 A B z f' g' x' x'' lt2 H) = (term1488 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351477) (@lem351476 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351479 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1484 A B x'' lt2 H f) = (term1272 A B x'' lt2 H f).
Proof. exact (eq_refl (term1484 A B x'' lt2 H f)). Qed.
Lemma lem351480 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1381 A B z f' g' x' lt2 H) = (term1381 A B z f' g' x' lt2 H).
Proof. exact (eq_refl (term1381 A B z f' g' x' lt2 H)). Qed.
Lemma lem351481 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1489 A B z f' g' x' x'' lt2 H f) = (term1490 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351480 A B z f' g' x' lt2 H) (@lem351479 A B x'' lt2 H f)). Qed.
Lemma lem351482 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1491 A B z f' g' x' x'' lt2 H) = (term1492 A B z f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem351481 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351483 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351484 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1483 A B z f' g' x' x'' lt2 H) = (term1493 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351483 A B) (@lem351482 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351485 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1482 A B z f' g' x' x'' lt2 H) = (term1483 A B z f' g' x' x'' lt2 H)) = ((term1476 A B z f' g' x' x'' lt2 H) = (term1493 A B z f' g' x' x'' lt2 H)).
Proof. exact (MK_COMB (@lem351478 A B z f' g' x' x'' lt2 H) (@lem351484 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351486 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1476 A B z f' g' x' x'' lt2 H) = (term1493 A B z f' g' x' x'' lt2 H).
Proof. exact (EQ_MP (@lem351485 A B z f' g' x' x'' lt2 H) (@lem351470 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351488 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem351489 {A B : Type'} (P : Prop) (Q : type572 A B) : (term1480 A B P Q) = (term1481 A B P Q).
Proof. exact (@lem351488 (A -> B) P Q). Qed.
Lemma lem351490 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1494 A B z f' g' x' x'' lt2 H f) = (term1495 A B z f' g' x' x'' lt2 H f).
Proof. exact (@lem351489 A B (term1364 A B z f' g' x' lt2 H) (term1270 A B x'' lt2 H f)). Qed.
Lemma lem351491 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1496 A B x'' lt2 H f g) = (term1268 A B x'' lt2 H f g).
Proof. exact (eq_refl (term1496 A B x'' lt2 H f g)). Qed.
Lemma lem351492 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1497 A B x'' lt2 H f) = (term1270 A B x'' lt2 H f).
Proof. exact (fun_ext (fun g : A -> B => @lem351491 A B x'' lt2 H f g)). Qed.
Lemma lem351493 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351494 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1498 A B x'' lt2 H f) = (term1272 A B x'' lt2 H f).
Proof. exact (MK_COMB (@lem351493 A B) (@lem351492 A B x'' lt2 H f)). Qed.
Lemma lem351495 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1381 A B z f' g' x' lt2 H) = (term1381 A B z f' g' x' lt2 H).
Proof. exact (eq_refl (term1381 A B z f' g' x' lt2 H)). Qed.
Lemma lem351496 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1494 A B z f' g' x' x'' lt2 H f) = (term1490 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351495 A B z f' g' x' lt2 H) (@lem351494 A B x'' lt2 H f)). Qed.
Lemma lem351497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem351498 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1499 A B z f' g' x' x'' lt2 H f) = (term1500 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351497) (@lem351496 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351499 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1496 A B x'' lt2 H f g) = (term1268 A B x'' lt2 H f g).
Proof. exact (eq_refl (term1496 A B x'' lt2 H f g)). Qed.
Lemma lem351500 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1381 A B z f' g' x' lt2 H) = (term1381 A B z f' g' x' lt2 H).
Proof. exact (eq_refl (term1381 A B z f' g' x' lt2 H)). Qed.
Lemma lem351501 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1501 A B z f' g' x' x'' lt2 H f g) = (term1502 A B z f' g' x' x'' lt2 H f g).
Proof. exact (MK_COMB (@lem351500 A B z f' g' x' lt2 H) (@lem351499 A B x'' lt2 H f g)). Qed.
Lemma lem351502 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1503 A B z f' g' x' x'' lt2 H f) = (term1504 A B z f' g' x' x'' lt2 H f).
Proof. exact (fun_ext (fun g : A -> B => @lem351501 A B z f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351503 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351504 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1495 A B z f' g' x' x'' lt2 H f) = (term1505 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351503 A B) (@lem351502 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351505 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : ((term1494 A B z f' g' x' x'' lt2 H f) = (term1495 A B z f' g' x' x'' lt2 H f)) = ((term1490 A B z f' g' x' x'' lt2 H f) = (term1505 A B z f' g' x' x'' lt2 H f)).
Proof. exact (MK_COMB (@lem351498 A B z f' g' x' x'' lt2 H f) (@lem351504 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351506 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1490 A B z f' g' x' x'' lt2 H f) = (term1505 A B z f' g' x' x'' lt2 H f).
Proof. exact (EQ_MP (@lem351505 A B z f' g' x' x'' lt2 H f) (@lem351490 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351507 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1492 A B z f' g' x' x'' lt2 H) = (term1506 A B z f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem351506 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351508 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351509 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1493 A B z f' g' x' x'' lt2 H) = (term1507 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351508 A B) (@lem351507 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351510 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1476 A B z f' g' x' x'' lt2 H) = (term1507 A B z f' g' x' x'' lt2 H).
Proof. exact (TRANS (@lem351486 A B z f' g' x' x'' lt2 H) (@lem351509 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351511 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1478 A B f' g' x' x'' lt2 H) = (term1508 A B f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem351510 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351512 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351513 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1479 A B f' g' x' x'' lt2 H) = (term1509 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351512 A) (@lem351511 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351514 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1470 A B f' g' x' x'' lt2 H) = (term1509 A B f' g' x' x'' lt2 H).
Proof. exact (TRANS (@lem351466 A B f' g' x' x'' lt2 H) (@lem351513 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351515 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1278 A B f' g' x' x'' lt2 H) = (term1509 A B f' g' x' x'' lt2 H).
Proof. exact (TRANS (@lem351442 A B f' g' x' x'' lt2 H) (@lem351514 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351516 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1280 A B f' g' x' x'' lt2) = (term1510 A B f' g' x' x'' lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem351515 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351517 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem351518 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1282 A B f' g' x' x'' lt2) = (term1511 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem351517 A B) (@lem351516 A B f' g' x' x'' lt2)). Qed.
Lemma lem351519 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351520 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1283 A B f' g' x' x'' lt2) = (term1512 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem351519 A lt2) (@lem351518 A B f' g' x' x'' lt2)). Qed.
Lemma lem351522 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem351523 {A B : Type'} (P : Prop) (Q : type111 A B) : (term1406 A B P Q) = (term1407 A B P Q).
Proof. exact (@lem351522 (type549 A B) P Q). Qed.
Lemma lem351524 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1513 A B f' g' x' x'' lt2) = (term1514 A B f' g' x' x'' lt2).
Proof. exact (@lem351523 A B (term1229 A lt2) (term1510 A B f' g' x' x'' lt2)). Qed.
Lemma lem351525 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1515 A B f' g' x' x'' lt2 H) = (term1509 A B f' g' x' x'' lt2 H).
Proof. exact (eq_refl (term1515 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351526 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1516 A B f' g' x' x'' lt2) = (term1510 A B f' g' x' x'' lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem351525 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351527 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem351528 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1517 A B f' g' x' x'' lt2) = (term1511 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem351527 A B) (@lem351526 A B f' g' x' x'' lt2)). Qed.
Lemma lem351529 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351530 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1513 A B f' g' x' x'' lt2) = (term1512 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem351529 A lt2) (@lem351528 A B f' g' x' x'' lt2)). Qed.
Lemma lem351531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem351532 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1518 A B f' g' x' x'' lt2) = (term1519 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem351531) (@lem351530 A B f' g' x' x'' lt2)). Qed.
Lemma lem351533 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1515 A B f' g' x' x'' lt2 H) = (term1509 A B f' g' x' x'' lt2 H).
Proof. exact (eq_refl (term1515 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351534 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351535 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1520 A B f' g' x' x'' lt2 H) = (term1521 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351534 A lt2) (@lem351533 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351536 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1522 A B f' g' x' x'' lt2) = (term1523 A B f' g' x' x'' lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem351535 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351537 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem351538 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1514 A B f' g' x' x'' lt2) = (term1524 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem351537 A B) (@lem351536 A B f' g' x' x'' lt2)). Qed.
Lemma lem351539 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : ((term1513 A B f' g' x' x'' lt2) = (term1514 A B f' g' x' x'' lt2)) = ((term1512 A B f' g' x' x'' lt2) = (term1524 A B f' g' x' x'' lt2)).
Proof. exact (MK_COMB (@lem351532 A B f' g' x' x'' lt2) (@lem351538 A B f' g' x' x'' lt2)). Qed.
Lemma lem351540 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1512 A B f' g' x' x'' lt2) = (term1524 A B f' g' x' x'' lt2).
Proof. exact (EQ_MP (@lem351539 A B f' g' x' x'' lt2) (@lem351524 A B f' g' x' x'' lt2)). Qed.
Lemma lem351542 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem351543 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (@lem351542 A P Q). Qed.
Lemma lem351544 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1525 A B f' g' x' x'' lt2 H) = (term1526 A B f' g' x' x'' lt2 H).
Proof. exact (@lem351543 A (term1229 A lt2) (term1508 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351545 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1527 A B f' g' x' x'' lt2 H z) = (term1507 A B z f' g' x' x'' lt2 H).
Proof. exact (eq_refl (term1527 A B f' g' x' x'' lt2 H z)). Qed.
Lemma lem351546 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1528 A B f' g' x' x'' lt2 H) = (term1508 A B f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem351545 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351547 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351548 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1529 A B f' g' x' x'' lt2 H) = (term1509 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351547 A) (@lem351546 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351549 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351550 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1525 A B f' g' x' x'' lt2 H) = (term1521 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351549 A lt2) (@lem351548 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem351552 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1530 A B f' g' x' x'' lt2 H) = (term1531 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351551) (@lem351550 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351553 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1527 A B f' g' x' x'' lt2 H z) = (term1507 A B z f' g' x' x'' lt2 H).
Proof. exact (eq_refl (term1527 A B f' g' x' x'' lt2 H z)). Qed.
Lemma lem351554 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351555 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1532 A B f' g' x' x'' lt2 H z) = (term1533 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351554 A lt2) (@lem351553 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351556 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1534 A B f' g' x' x'' lt2 H) = (term1535 A B f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem351555 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351557 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351558 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1526 A B f' g' x' x'' lt2 H) = (term1536 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351557 A) (@lem351556 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351559 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1525 A B f' g' x' x'' lt2 H) = (term1526 A B f' g' x' x'' lt2 H)) = ((term1521 A B f' g' x' x'' lt2 H) = (term1536 A B f' g' x' x'' lt2 H)).
Proof. exact (MK_COMB (@lem351552 A B f' g' x' x'' lt2 H) (@lem351558 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351560 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1521 A B f' g' x' x'' lt2 H) = (term1536 A B f' g' x' x'' lt2 H).
Proof. exact (EQ_MP (@lem351559 A B f' g' x' x'' lt2 H) (@lem351544 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351562 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem351563 {A B : Type'} (P : Prop) (Q : type572 A B) : (term1480 A B P Q) = (term1481 A B P Q).
Proof. exact (@lem351562 (A -> B) P Q). Qed.
Lemma lem351564 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1537 A B z f' g' x' x'' lt2 H) = (term1538 A B z f' g' x' x'' lt2 H).
Proof. exact (@lem351563 A B (term1229 A lt2) (term1506 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351565 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1539 A B z f' g' x' x'' lt2 H f) = (term1505 A B z f' g' x' x'' lt2 H f).
Proof. exact (eq_refl (term1539 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351566 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1540 A B z f' g' x' x'' lt2 H) = (term1506 A B z f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem351565 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351567 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351568 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1541 A B z f' g' x' x'' lt2 H) = (term1507 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351567 A B) (@lem351566 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351569 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351570 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1537 A B z f' g' x' x'' lt2 H) = (term1533 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351569 A lt2) (@lem351568 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem351572 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1542 A B z f' g' x' x'' lt2 H) = (term1543 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351571) (@lem351570 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351573 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1539 A B z f' g' x' x'' lt2 H f) = (term1505 A B z f' g' x' x'' lt2 H f).
Proof. exact (eq_refl (term1539 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351574 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351575 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1544 A B z f' g' x' x'' lt2 H f) = (term1545 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351574 A lt2) (@lem351573 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351576 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1546 A B z f' g' x' x'' lt2 H) = (term1547 A B z f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem351575 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351577 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351578 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1538 A B z f' g' x' x'' lt2 H) = (term1548 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351577 A B) (@lem351576 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351579 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : ((term1537 A B z f' g' x' x'' lt2 H) = (term1538 A B z f' g' x' x'' lt2 H)) = ((term1533 A B z f' g' x' x'' lt2 H) = (term1548 A B z f' g' x' x'' lt2 H)).
Proof. exact (MK_COMB (@lem351572 A B z f' g' x' x'' lt2 H) (@lem351578 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351580 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1533 A B z f' g' x' x'' lt2 H) = (term1548 A B z f' g' x' x'' lt2 H).
Proof. exact (EQ_MP (@lem351579 A B z f' g' x' x'' lt2 H) (@lem351564 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351582 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1387 A P Q) = (term1388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem351583 {A B : Type'} (P : Prop) (Q : type572 A B) : (term1480 A B P Q) = (term1481 A B P Q).
Proof. exact (@lem351582 (A -> B) P Q). Qed.
Lemma lem351584 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1549 A B z f' g' x' x'' lt2 H f) = (term1550 A B z f' g' x' x'' lt2 H f).
Proof. exact (@lem351583 A B (term1229 A lt2) (term1504 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351585 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1551 A B z f' g' x' x'' lt2 H f g) = (term1502 A B z f' g' x' x'' lt2 H f g).
Proof. exact (eq_refl (term1551 A B z f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351586 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1552 A B z f' g' x' x'' lt2 H f) = (term1504 A B z f' g' x' x'' lt2 H f).
Proof. exact (fun_ext (fun g : A -> B => @lem351585 A B z f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351587 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351588 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1553 A B z f' g' x' x'' lt2 H f) = (term1505 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351587 A B) (@lem351586 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351589 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351590 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1549 A B z f' g' x' x'' lt2 H f) = (term1545 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351589 A lt2) (@lem351588 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem351592 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1554 A B z f' g' x' x'' lt2 H f) = (term1555 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351591) (@lem351590 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351593 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1551 A B z f' g' x' x'' lt2 H f g) = (term1502 A B z f' g' x' x'' lt2 H f g).
Proof. exact (eq_refl (term1551 A B z f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351594 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351595 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1556 A B z f' g' x' x'' lt2 H f g) = (term1557 A B z f' g' x' x'' lt2 H f g).
Proof. exact (MK_COMB (@lem351594 A lt2) (@lem351593 A B z f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351596 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1558 A B z f' g' x' x'' lt2 H f) = (term1559 A B z f' g' x' x'' lt2 H f).
Proof. exact (fun_ext (fun g : A -> B => @lem351595 A B z f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351597 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351598 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1550 A B z f' g' x' x'' lt2 H f) = (term1560 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351597 A B) (@lem351596 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351599 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : ((term1549 A B z f' g' x' x'' lt2 H f) = (term1550 A B z f' g' x' x'' lt2 H f)) = ((term1545 A B z f' g' x' x'' lt2 H f) = (term1560 A B z f' g' x' x'' lt2 H f)).
Proof. exact (MK_COMB (@lem351592 A B z f' g' x' x'' lt2 H f) (@lem351598 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351600 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1545 A B z f' g' x' x'' lt2 H f) = (term1560 A B z f' g' x' x'' lt2 H f).
Proof. exact (EQ_MP (@lem351599 A B z f' g' x' x'' lt2 H f) (@lem351584 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351601 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1547 A B z f' g' x' x'' lt2 H) = (term1561 A B z f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem351600 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351602 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351603 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1548 A B z f' g' x' x'' lt2 H) = (term1562 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351602 A B) (@lem351601 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351604 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1533 A B z f' g' x' x'' lt2 H) = (term1562 A B z f' g' x' x'' lt2 H).
Proof. exact (TRANS (@lem351580 A B z f' g' x' x'' lt2 H) (@lem351603 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351605 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1535 A B f' g' x' x'' lt2 H) = (term1563 A B f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem351604 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351606 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351607 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1536 A B f' g' x' x'' lt2 H) = (term1564 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351606 A) (@lem351605 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351608 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1521 A B f' g' x' x'' lt2 H) = (term1564 A B f' g' x' x'' lt2 H).
Proof. exact (TRANS (@lem351560 A B f' g' x' x'' lt2 H) (@lem351607 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351609 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1523 A B f' g' x' x'' lt2) = (term1565 A B f' g' x' x'' lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem351608 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351610 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem351611 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1524 A B f' g' x' x'' lt2) = (term1566 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem351610 A B) (@lem351609 A B f' g' x' x'' lt2)). Qed.
Lemma lem351612 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1512 A B f' g' x' x'' lt2) = (term1566 A B f' g' x' x'' lt2).
Proof. exact (TRANS (@lem351540 A B f' g' x' x'' lt2) (@lem351611 A B f' g' x' x'' lt2)). Qed.
Lemma lem351613 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1283 A B f' g' x' x'' lt2) = (term1566 A B f' g' x' x'' lt2).
Proof. exact (TRANS (@lem351520 A B f' g' x' x'' lt2) (@lem351612 A B f' g' x' x'' lt2)). Qed.
Lemma lem351614 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) : (term1284 A B f' g' x' x'') = (term1567 A B f' g' x' x'').
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem351613 A B f' g' x' x'' lt2)). Qed.
Lemma lem351615 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem351616 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) : (term1285 A B f' g' x' x'') = (term1568 A B f' g' x' x'').
Proof. exact (MK_COMB (@lem351615 A) (@lem351614 A B f' g' x' x'')). Qed.
Lemma lem351651 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1502 A B z f' g' x' x'' lt2 H f g) = (term1569 A B z f' g' x' x'' lt2 H f g).
Proof. exact (@lem19699 (term1212 A B x' f' g' lt2 H z) (term1202 A B f' g' x' lt2 H) (term1268 A B x'' lt2 H f g)). Qed.
Lemma lem351654 {A : Type'} (lt2 : type1402 A) : (term1230 A lt2) = (term1230 A lt2).
Proof. exact (eq_refl (term1230 A lt2)). Qed.
Lemma lem351655 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1557 A B z f' g' x' x'' lt2 H f g) = (term1570 A B z f' g' x' x'' lt2 H f g).
Proof. exact (MK_COMB (@lem351654 A lt2) (@lem351651 A B z f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351662 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1570 A B z f' g' x' x'' lt2 H f g) = (term1571 A B z f' g' x' x'' lt2 H f g).
Proof. exact (@lem19490 (term1572 A B x' f' g' z x'' lt2 H f g) (term1229 A lt2) (term1573 A B f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351663 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) (g : A -> B) : (term1557 A B z f' g' x' x'' lt2 H f g) = (term1571 A B z f' g' x' x'' lt2 H f g).
Proof. exact (TRANS (@lem351655 A B z f' g' x' x'' lt2 H f g) (@lem351662 A B z f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351664 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1559 A B z f' g' x' x'' lt2 H f) = (term1574 A B z f' g' x' x'' lt2 H f).
Proof. exact (fun_ext (fun g : A -> B => @lem351663 A B z f' g' x' x'' lt2 H f g)). Qed.
Lemma lem351665 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351666 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f : A -> B) : (term1560 A B z f' g' x' x'' lt2 H f) = (term1575 A B z f' g' x' x'' lt2 H f).
Proof. exact (MK_COMB (@lem351665 A B) (@lem351664 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351667 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1561 A B z f' g' x' x'' lt2 H) = (term1576 A B z f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun f : A -> B => @lem351666 A B z f' g' x' x'' lt2 H f)). Qed.
Lemma lem351668 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351669 {A B : Type'} (z : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1562 A B z f' g' x' x'' lt2 H) = (term1577 A B z f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351668 A B) (@lem351667 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351670 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1563 A B f' g' x' x'' lt2 H) = (term1578 A B f' g' x' x'' lt2 H).
Proof. exact (fun_ext (fun z : A => @lem351669 A B z f' g' x' x'' lt2 H)). Qed.
Lemma lem351671 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351672 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) : (term1564 A B f' g' x' x'' lt2 H) = (term1579 A B f' g' x' x'' lt2 H).
Proof. exact (MK_COMB (@lem351671 A) (@lem351670 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351673 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1565 A B f' g' x' x'' lt2) = (term1580 A B f' g' x' x'' lt2).
Proof. exact (fun_ext (fun H : type549 A B => @lem351672 A B f' g' x' x'' lt2 H)). Qed.
Lemma lem351674 {A B : Type'} : (@all ((A -> B) -> A -> B)) = (@all ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B))). Qed.
Lemma lem351675 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) : (term1566 A B f' g' x' x'' lt2) = (term1581 A B f' g' x' x'' lt2).
Proof. exact (MK_COMB (@lem351674 A B) (@lem351673 A B f' g' x' x'' lt2)). Qed.
Lemma lem351676 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) : (term1567 A B f' g' x' x'') = (term1582 A B f' g' x' x'').
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem351675 A B f' g' x' x'' lt2)). Qed.
Lemma lem351677 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem351678 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) : (term1568 A B f' g' x' x'') = (term1583 A B f' g' x' x'').
Proof. exact (MK_COMB (@lem351677 A) (@lem351676 A B f' g' x' x'')). Qed.
Lemma lem351679 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) : (term1285 A B f' g' x' x'') = (term1583 A B f' g' x' x'').
Proof. exact (TRANS (@lem351616 A B f' g' x' x'') (@lem351678 A B f' g' x' x'')). Qed.
Lemma lem351680 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1583 A B f' g' x' x''.
Proof. exact (EQ_MP (@lem351679 A B f' g' x' x'') (@lem350387 A B f' g' x' x'' h1)). Qed.
Lemma lem351702 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term1337 A B lt2 z f H g x) = (term1463 A B lt2 z f H g x).
Proof. exact (@lem19699 (term1329 A B lt2 z f g x) (term1322 A B z f g x) ((term1286 A B H f x) = (term1286 A B H g x))). Qed.
Lemma lem351703 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) (g : A -> B) : (term1339 A B lt2 z f H g) = (term1464 A B lt2 z f H g).
Proof. exact (fun_ext (fun x : A => @lem351702 A B lt2 z f H g x)). Qed.
Lemma lem351704 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351705 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) (g : A -> B) : (term1341 A B lt2 z f H g) = (term1465 A B lt2 z f H g).
Proof. exact (MK_COMB (@lem351704 A) (@lem351703 A B lt2 z f H g)). Qed.
Lemma lem351706 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) : (term1343 A B lt2 z f H) = (term1466 A B lt2 z f H).
Proof. exact (fun_ext (fun g : A -> B => @lem351705 A B lt2 z f H g)). Qed.
Lemma lem351707 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351708 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (H : type549 A B) : (term1344 A B lt2 z f H) = (term1467 A B lt2 z f H).
Proof. exact (MK_COMB (@lem351707 A B) (@lem351706 A B lt2 z f H)). Qed.
Lemma lem351709 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term1345 A B lt2 z H) = (term1468 A B lt2 z H).
Proof. exact (fun_ext (fun f : A -> B => @lem351708 A B lt2 z f H)). Qed.
Lemma lem351710 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem351712 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) : (term1346 A B lt2 z H) = (term1469 A B lt2 z H).
Proof. exact (MK_COMB (@lem351710 A B) (@lem351709 A B lt2 z H)). Qed.
Lemma lem351713 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1469 A B lt2 z H.
Proof. exact (EQ_MP (@lem351712 A B lt2 z H) (@lem350696 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351715 {A B : Type'} (H : type549 A B) (f'' : A -> B) (x : A) : ((@I (A -> B) f'' x) = (term1286 A B H f'' x)) = ((@I (A -> B) f'' x) = (term1286 A B H f'' x)).
Proof. exact (eq_refl ((@I (A -> B) f'' x) = (term1286 A B H f'' x))). Qed.
Lemma lem351716 {A B : Type'} (H : type549 A B) (f'' : A -> B) : (term1289 A B H f'') = (term1289 A B H f'').
Proof. exact (fun_ext (fun x : A => @lem351715 A B H f'' x)). Qed.
Lemma lem351717 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351719 {A B : Type'} (H : type549 A B) (f'' : A -> B) : (term1290 A B H f'') = (term1290 A B H f'').
Proof. exact (MK_COMB (@lem351717 A) (@lem351716 A B H f'')). Qed.
Lemma lem351720 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1290 A B H f''.
Proof. exact (EQ_MP (@lem351719 A B H f'') (@lem350700 A B H f''' f'' h1)). Qed.
Lemma lem351722 {A B : Type'} (H : type549 A B) (f''' : A -> B) (x : A) : ((@I (A -> B) f''' x) = (term1286 A B H f''' x)) = ((@I (A -> B) f''' x) = (term1286 A B H f''' x)).
Proof. exact (eq_refl ((@I (A -> B) f''' x) = (term1286 A B H f''' x))). Qed.
Lemma lem351723 {A B : Type'} (H : type549 A B) (f''' : A -> B) : (term1289 A B H f''') = (term1289 A B H f''').
Proof. exact (fun_ext (fun x : A => @lem351722 A B H f''' x)). Qed.
Lemma lem351724 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem351726 {A B : Type'} (H : type549 A B) (f''' : A -> B) : (term1290 A B H f''') = (term1290 A B H f''').
Proof. exact (MK_COMB (@lem351724 A) (@lem351723 A B H f''')). Qed.
Lemma lem351727 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1290 A B H f'''.
Proof. exact (EQ_MP (@lem351726 A B H f''') (@lem350702 A B H f''' f'' h1)). Qed.
Lemma lem351732 {A B : Type'} (_7574 : type1402 A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1584 A B g x f _7574.
Proof. exact (@lem350905 A B g x f h1 _7574). Qed.
Lemma lem351733 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) : (term1584 A B g x f _7574) = (term1460 A B g x f _7574).
Proof. exact (eq_refl (term1584 A B g x f _7574)). Qed.
Lemma lem351734 {A B : Type'} (_7574 : type1402 A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1460 A B g x f _7574.
Proof. exact (EQ_MP (@lem351733 A B g x f _7574) (@lem351732 A B _7574 g x f h1)). Qed.
Lemma lem351735 {A B : Type'} (_7574 : type1402 A) (_7575 : type549 A B) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1585 A B g x f _7574 _7575.
Proof. exact (@lem351734 A B _7574 g x f h1 _7575). Qed.
Lemma lem351736 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1585 A B g x f _7574 _7575) = (term1458 A B g x f _7574 _7575).
Proof. exact (eq_refl (term1585 A B g x f _7574 _7575)). Qed.
Lemma lem351737 {A B : Type'} (_7574 : type1402 A) (_7575 : type549 A B) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1458 A B g x f _7574 _7575.
Proof. exact (EQ_MP (@lem351736 A B g x f _7574 _7575) (@lem351735 A B _7574 _7575 g x f h1)). Qed.
Lemma lem351738 {A B : Type'} (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1586 A B g x f _7574 _7575 _7576.
Proof. exact (@lem351737 A B _7574 _7575 g x f h1 _7576). Qed.
Lemma lem351739 {A B : Type'} (_7576 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1586 A B g x f _7574 _7575 _7576) = (term1456 A B _7576 g x f _7574 _7575).
Proof. exact (eq_refl (term1586 A B g x f _7574 _7575 _7576)). Qed.
Lemma lem351740 {A B : Type'} (_7576 : A) (_7574 : type1402 A) (_7575 : type549 A B) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1456 A B _7576 g x f _7574 _7575.
Proof. exact (EQ_MP (@lem351739 A B _7576 g x f _7574 _7575) (@lem351738 A B _7574 _7575 _7576 g x f h1)). Qed.
Lemma lem351741 {A B : Type'} (_7576 : A) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1587 A B _7576 g x f _7574 _7575 _7577.
Proof. exact (@lem351740 A B _7576 _7574 _7575 g x f h1 _7577). Qed.
Lemma lem351742 {A B : Type'} (_7576 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1587 A B _7576 g x f _7574 _7575 _7577) = (term1452 A B _7576 g x f _7574 _7575 _7577).
Proof. exact (eq_refl (term1587 A B _7576 g x f _7574 _7575 _7577)). Qed.
Lemma lem351743 {A B : Type'} (_7576 : A) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1452 A B _7576 g x f _7574 _7575 _7577.
Proof. exact (EQ_MP (@lem351742 A B _7576 g x f _7574 _7575 _7577) (@lem351741 A B _7576 _7574 _7575 _7577 g x f h1)). Qed.
Lemma lem351759 {A B : Type'} (_7583 : A -> B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1588 A B lt2 z H _7583.
Proof. exact (@lem351204 A B lt2 z x''' H f''' f'' h1 _7583). Qed.
Lemma lem351760 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (_7583 : A -> B) (H : type549 A B) : (term1588 A B lt2 z H _7583) = (term1467 A B lt2 z _7583 H).
Proof. exact (eq_refl (term1588 A B lt2 z H _7583)). Qed.
Lemma lem351761 {A B : Type'} (_7583 : A -> B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1467 A B lt2 z _7583 H.
Proof. exact (EQ_MP (@lem351760 A B lt2 z _7583 H) (@lem351759 A B _7583 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351762 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1589 A B lt2 z _7583 H _7584.
Proof. exact (@lem351761 A B _7583 lt2 z x''' H f''' f'' h1 _7584). Qed.
Lemma lem351763 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (_7583 : A -> B) (H : type549 A B) (_7584 : A -> B) : (term1589 A B lt2 z _7583 H _7584) = (term1465 A B lt2 z _7583 H _7584).
Proof. exact (eq_refl (term1589 A B lt2 z _7583 H _7584)). Qed.
Lemma lem351764 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1465 A B lt2 z _7583 H _7584.
Proof. exact (EQ_MP (@lem351763 A B lt2 z _7583 H _7584) (@lem351762 A B _7583 _7584 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351765 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1590 A B lt2 z _7583 H _7584 _7585.
Proof. exact (@lem351764 A B _7583 _7584 lt2 z x''' H f''' f'' h1 _7585). Qed.
Lemma lem351766 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (_7583 : A -> B) (H : type549 A B) (_7584 : A -> B) (_7585 : A) : (term1590 A B lt2 z _7583 H _7584 _7585) = (term1463 A B lt2 z _7583 H _7584 _7585).
Proof. exact (eq_refl (term1590 A B lt2 z _7583 H _7584 _7585)). Qed.
Lemma lem351767 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1463 A B lt2 z _7583 H _7584 _7585.
Proof. exact (EQ_MP (@lem351766 A B lt2 z _7583 H _7584 _7585) (@lem351765 A B _7583 _7584 _7585 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351768 {A B : Type'} (_7586 : A -> B) (H : type549 A B) (x''' : type569 A B) (h1 : term1305 A B H x''') : term1591 A B H x''' _7586.
Proof. exact (@lem351211 A B H x''' h1 _7586). Qed.
Lemma lem351769 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (_7586 : A -> B) : (term1591 A B H x''' _7586) = (term1303 A B H x''' _7586).
Proof. exact (eq_refl (term1591 A B H x''' _7586)). Qed.
Lemma lem351783 {A B : Type'} (_7591 : type1402 A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1592 A B f' g' x' x'' _7591.
Proof. exact (@lem351680 A B f' g' x' x'' h1 _7591). Qed.
Lemma lem351784 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) : (term1592 A B f' g' x' x'' _7591) = (term1581 A B f' g' x' x'' _7591).
Proof. exact (eq_refl (term1592 A B f' g' x' x'' _7591)). Qed.
Lemma lem351785 {A B : Type'} (_7591 : type1402 A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1581 A B f' g' x' x'' _7591.
Proof. exact (EQ_MP (@lem351784 A B f' g' x' x'' _7591) (@lem351783 A B _7591 f' g' x' x'' h1)). Qed.
Lemma lem351786 {A B : Type'} (_7591 : type1402 A) (_7592 : type549 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1593 A B f' g' x' x'' _7591 _7592.
Proof. exact (@lem351785 A B _7591 f' g' x' x'' h1 _7592). Qed.
Lemma lem351787 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1593 A B f' g' x' x'' _7591 _7592) = (term1579 A B f' g' x' x'' _7591 _7592).
Proof. exact (eq_refl (term1593 A B f' g' x' x'' _7591 _7592)). Qed.
Lemma lem351788 {A B : Type'} (_7591 : type1402 A) (_7592 : type549 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1579 A B f' g' x' x'' _7591 _7592.
Proof. exact (EQ_MP (@lem351787 A B f' g' x' x'' _7591 _7592) (@lem351786 A B _7591 _7592 f' g' x' x'' h1)). Qed.
Lemma lem351789 {A B : Type'} (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1594 A B f' g' x' x'' _7591 _7592 _7593.
Proof. exact (@lem351788 A B _7591 _7592 f' g' x' x'' h1 _7593). Qed.
Lemma lem351790 {A B : Type'} (_7593 : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1594 A B f' g' x' x'' _7591 _7592 _7593) = (term1577 A B _7593 f' g' x' x'' _7591 _7592).
Proof. exact (eq_refl (term1594 A B f' g' x' x'' _7591 _7592 _7593)). Qed.
Lemma lem351791 {A B : Type'} (_7593 : A) (_7591 : type1402 A) (_7592 : type549 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1577 A B _7593 f' g' x' x'' _7591 _7592.
Proof. exact (EQ_MP (@lem351790 A B _7593 f' g' x' x'' _7591 _7592) (@lem351789 A B _7591 _7592 _7593 f' g' x' x'' h1)). Qed.
Lemma lem351792 {A B : Type'} (_7593 : A) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1595 A B _7593 f' g' x' x'' _7591 _7592 _7594.
Proof. exact (@lem351791 A B _7593 _7591 _7592 f' g' x' x'' h1 _7594). Qed.
Lemma lem351793 {A B : Type'} (_7593 : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) : (term1595 A B _7593 f' g' x' x'' _7591 _7592 _7594) = (term1575 A B _7593 f' g' x' x'' _7591 _7592 _7594).
Proof. exact (eq_refl (term1595 A B _7593 f' g' x' x'' _7591 _7592 _7594)). Qed.
Lemma lem351794 {A B : Type'} (_7593 : A) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1575 A B _7593 f' g' x' x'' _7591 _7592 _7594.
Proof. exact (EQ_MP (@lem351793 A B _7593 f' g' x' x'' _7591 _7592 _7594) (@lem351792 A B _7593 _7591 _7592 _7594 f' g' x' x'' h1)). Qed.
Lemma lem351795 {A B : Type'} (_7593 : A) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1596 A B _7593 f' g' x' x'' _7591 _7592 _7594 _7595.
Proof. exact (@lem351794 A B _7593 _7591 _7592 _7594 f' g' x' x'' h1 _7595). Qed.
Lemma lem351796 {A B : Type'} (_7593 : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1596 A B _7593 f' g' x' x'' _7591 _7592 _7594 _7595) = (term1571 A B _7593 f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1596 A B _7593 f' g' x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem351797 {A B : Type'} (_7593 : A) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1571 A B _7593 f' g' x' x'' _7591 _7592 _7594 _7595.
Proof. exact (EQ_MP (@lem351796 A B _7593 f' g' x' x'' _7591 _7592 _7594 _7595) (@lem351795 A B _7593 _7591 _7592 _7594 _7595 f' g' x' x'' h1)). Qed.
Lemma lem351798 {A B : Type'} (_7596 : A -> B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1588 A B lt2 z H _7596.
Proof. exact (@lem351713 A B lt2 z x''' H f''' f'' h1 _7596). Qed.
Lemma lem351799 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (_7596 : A -> B) (H : type549 A B) : (term1588 A B lt2 z H _7596) = (term1467 A B lt2 z _7596 H).
Proof. exact (eq_refl (term1588 A B lt2 z H _7596)). Qed.
Lemma lem351800 {A B : Type'} (_7596 : A -> B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1467 A B lt2 z _7596 H.
Proof. exact (EQ_MP (@lem351799 A B lt2 z _7596 H) (@lem351798 A B _7596 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351801 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1589 A B lt2 z _7596 H _7597.
Proof. exact (@lem351800 A B _7596 lt2 z x''' H f''' f'' h1 _7597). Qed.
Lemma lem351802 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (_7596 : A -> B) (H : type549 A B) (_7597 : A -> B) : (term1589 A B lt2 z _7596 H _7597) = (term1465 A B lt2 z _7596 H _7597).
Proof. exact (eq_refl (term1589 A B lt2 z _7596 H _7597)). Qed.
Lemma lem351803 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1465 A B lt2 z _7596 H _7597.
Proof. exact (EQ_MP (@lem351802 A B lt2 z _7596 H _7597) (@lem351801 A B _7596 _7597 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351804 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1590 A B lt2 z _7596 H _7597 _7598.
Proof. exact (@lem351803 A B _7596 _7597 lt2 z x''' H f''' f'' h1 _7598). Qed.
Lemma lem351805 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (_7596 : A -> B) (H : type549 A B) (_7597 : A -> B) (_7598 : A) : (term1590 A B lt2 z _7596 H _7597 _7598) = (term1463 A B lt2 z _7596 H _7597 _7598).
Proof. exact (eq_refl (term1590 A B lt2 z _7596 H _7597 _7598)). Qed.
Lemma lem351806 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1463 A B lt2 z _7596 H _7597 _7598.
Proof. exact (EQ_MP (@lem351805 A B lt2 z _7596 H _7597 _7598) (@lem351804 A B _7596 _7597 _7598 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351807 {A B : Type'} (_7599 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1597 A B H f'' _7599.
Proof. exact (@lem351720 A B H f''' f'' h1 _7599). Qed.
Lemma lem351808 {A B : Type'} (H : type549 A B) (f'' : A -> B) (_7599 : A) : (term1597 A B H f'' _7599) = ((@I (A -> B) f'' _7599) = (term1286 A B H f'' _7599)).
Proof. exact (eq_refl (term1597 A B H f'' _7599)). Qed.
Lemma lem351810 {A B : Type'} (_7600 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1597 A B H f''' _7600.
Proof. exact (@lem351727 A B H f''' f'' h1 _7600). Qed.
Lemma lem351811 {A B : Type'} (H : type549 A B) (f''' : A -> B) (_7600 : A) : (term1597 A B H f''' _7600) = ((@I (A -> B) f''' _7600) = (term1286 A B H f''' _7600)).
Proof. exact (eq_refl (term1597 A B H f''' _7600)). Qed.
Lemma lem351818 {A B : Type'} (_7576 : A) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1598 A B x g _7576 f _7574 _7575 _7577.
Proof. exact (proj1 (@lem351743 A B _7576 _7574 _7575 _7577 g x f h1)). Qed.
Lemma lem351821 {A B : Type'} (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1599 A B f' g' x' x'' _7591 _7592 _7594 _7595.
Proof. exact (proj2 (@lem351797 A B (@el A) _7591 _7592 _7594 _7595 f' g' x' x'' h1)). Qed.
Lemma lem351822 {A B : Type'} (_7593 : A) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1600 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595.
Proof. exact (proj1 (@lem351797 A B _7593 _7591 _7592 _7594 _7595 f' g' x' x'' h1)). Qed.
Lemma lem351828 {A B : Type'} (_7586 : A -> B) (H : type549 A B) (x''' : type569 A B) (h1 : term1305 A B H x''') : term1303 A B H x''' _7586.
Proof. exact (EQ_MP (@lem351769 A B H x''' _7586) (@lem351768 A B _7586 H x''' h1)). Qed.
Lemma lem351834 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1601 A B lt2 z _7583 H _7584 _7585.
Proof. exact (proj1 (@lem351767 A B _7583 _7584 _7585 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351840 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1602 A B z _7583 H _7584 _7585.
Proof. exact (proj2 (@lem351767 A B _7583 _7584 _7585 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351897 {A B : Type'} (x : type410 A B) (g : type409 A B) (_7576 : A) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1453 A B x g _7576 f _7574 _7575 _7577) = (term1603 A B x g _7576 f _7574 _7575 _7577).
Proof. exact (@lem346591 (term1208 A B _7576 x _7574 _7575) ((term1180 A B f _7574 _7575 _7576) = (term1180 A B g _7574 _7575 _7576)) ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577))). Qed.
Lemma lem351898 {A : Type'} (_7574 : type1402 A) : (term1230 A _7574) = (term1230 A _7574).
Proof. exact (eq_refl (term1230 A _7574)). Qed.
Lemma lem351901 {A B : Type'} (x : type410 A B) (g : type409 A B) (_7576 : A) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1598 A B x g _7576 f _7574 _7575 _7577) = (term1604 A B x g _7576 f _7574 _7575 _7577).
Proof. exact (MK_COMB (@lem351898 A _7574) (@lem351897 A B x g _7576 f _7574 _7575 _7577)). Qed.
Lemma lem351902 {A B : Type'} (_7576 : A) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1604 A B x g _7576 f _7574 _7575 _7577.
Proof. exact (EQ_MP (@lem351901 A B x g _7576 f _7574 _7575 _7577) (@lem351818 A B _7576 _7574 _7575 _7577 g x f h1)). Qed.
Lemma lem351912 {A B : Type'} (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1605 A B g x f _7574 _7575 _7577.
Proof. exact (proj2 (@lem351743 A B (@el A) _7574 _7575 _7577 g x f h1)). Qed.
Lemma lem351920 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term96 A B f''' f''.
Proof. exact (proj2 (@lem350699 A B H f''' f'' h1)). Qed.
Lemma lem351926 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1601 A B lt2 z _7596 H _7597 _7598.
Proof. exact (proj1 (@lem351806 A B _7596 _7597 _7598 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351932 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1602 A B z _7596 H _7597 _7598.
Proof. exact (proj2 (@lem351806 A B _7596 _7597 _7598 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem351943 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1268 A B x'' _7591 _7592 _7594 _7595) = (term1606 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem346591 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1249 A B x'' _7591 _7592 _7594 _7595) (_7594 = _7595)). Qed.
Lemma lem351944 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) : (term1607 A B x' f' g' _7591 _7592 _7593) = (term1607 A B x' f' g' _7591 _7592 _7593).
Proof. exact (eq_refl (term1607 A B x' f' g' _7591 _7592 _7593)). Qed.
Lemma lem351945 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1572 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1608 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem351944 A B x' f' g' _7591 _7592 _7593) (@lem351943 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem351952 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1608 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1609 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem346591 (term1208 A B _7593 x' _7591 _7592) ((term1180 A B f' _7591 _7592 _7593) = (term1180 A B g' _7591 _7592 _7593)) (term1606 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem351953 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1572 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1609 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595).
Proof. exact (TRANS (@lem351945 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) (@lem351952 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem351954 {A : Type'} (_7591 : type1402 A) : (term1230 A _7591) = (term1230 A _7591).
Proof. exact (eq_refl (term1230 A _7591)). Qed.
Lemma lem351957 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1600 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1610 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem351954 A _7591) (@lem351953 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem351958 {A B : Type'} (_7593 : A) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1610 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595.
Proof. exact (EQ_MP (@lem351957 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) (@lem351822 A B _7593 _7591 _7592 _7594 _7595 f' g' x' x'' h1)). Qed.
Lemma lem351969 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1268 A B x'' _7591 _7592 _7594 _7595) = (term1606 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem346591 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1249 A B x'' _7591 _7592 _7594 _7595) (_7594 = _7595)). Qed.
Lemma lem351970 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1611 A B f' g' x' _7591 _7592) = (term1611 A B f' g' x' _7591 _7592).
Proof. exact (eq_refl (term1611 A B f' g' x' _7591 _7592)). Qed.
Lemma lem351973 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1573 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1612 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem351970 A B f' g' x' _7591 _7592) (@lem351969 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem351974 {A : Type'} (_7591 : type1402 A) : (term1230 A _7591) = (term1230 A _7591).
Proof. exact (eq_refl (term1230 A _7591)). Qed.
Lemma lem351977 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1599 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1613 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem351974 A _7591) (@lem351973 A B f' g' x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem351978 {A B : Type'} (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1613 A B f' g' x' x'' _7591 _7592 _7594 _7595.
Proof. exact (EQ_MP (@lem351977 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem351821 A B _7591 _7592 _7594 _7595 f' g' x' x'' h1)). Qed.
Lemma lem352290 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (proj1 (@lem350692 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem352291 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1614 A lt2.
Proof. exact (fun h0 : term1229 A lt2 => @lem352290 A B lt2 z x''' H f''' f'' h1). Qed.
Lemma lem352293 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem352294 {A : Type'} (lt2 : type1402 A) : (term1614 A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem352293 (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2)). Qed.
Lemma lem352295 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (EQ_MP (@lem352294 A lt2) (@lem352291 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem352297 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (proj1 (@lem350692 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem352298 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1614 A lt2.
Proof. exact (fun h0 : term1229 A lt2 => @lem352297 A B lt2 z x''' H f''' f'' h1). Qed.
Lemma lem352300 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem352301 {A : Type'} (lt2 : type1402 A) : (term1614 A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem352300 (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2)). Qed.
Lemma lem352302 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (EQ_MP (@lem352301 A lt2) (@lem352298 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem352305 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1202 A B f g x lt2 H) : term1202 A B f g x lt2 H.
Proof. exact (h1). Qed.
Lemma lem352306 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1202 A B f g x lt2 H) : term1616 A B f g x lt2 H.
Proof. exact (fun h0 : (term1198 A B f x lt2 H) = (term1198 A B g x lt2 H) => @lem352305 A B f g x lt2 H h1). Qed.
Lemma lem352308 (p : Prop) : (term1617 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem352309 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1616 A B f g x lt2 H) = (term1202 A B f g x lt2 H).
Proof. exact (@lem352308 ((term1198 A B f x lt2 H) = (term1198 A B g x lt2 H))). Qed.
Lemma lem352310 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1202 A B f g x lt2 H) : term1202 A B f g x lt2 H.
Proof. exact (EQ_MP (@lem352309 A B f g x lt2 H) (@lem352306 A B f g x lt2 H h1)). Qed.
Lemma lem352312 (b : Prop) (a : Prop) : (a \/ b) = (term1618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem352315 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : (term1601 A B lt2 z _7583 H _7584 _7585) = (term1619 A B H lt2 z _7583 _7584 _7585).
Proof. exact (@lem352312 ((term1286 A B H _7583 _7585) = (term1286 A B H _7584 _7585)) (term1329 A B lt2 z _7583 _7584 _7585)). Qed.
Lemma lem352318 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1619 A B H lt2 z _7583 _7584 _7585.
Proof. exact (EQ_MP (@lem352315 A B H lt2 z _7583 _7584 _7585) (@lem351834 A B _7583 _7584 _7585 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem352319 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1619 A B H lt2 z _7583 _7584 _7585.
Proof. exact (@lem352318 A B _7583 _7584 _7585 lt2 z x''' H f''' f'' h1). Qed.
Lemma lem352320 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1620 A B z f g x lt2 H.
Proof. exact (@lem352319 A B (term1178 A B f lt2 H) (term1178 A B g lt2 H) (term1194 A B x lt2 H) lt2 z x''' H f''' f'' h1). Qed.
Lemma lem352323 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f g x lt2 H) (h2 : term461 A B lt2 z x''' H f''' f'') : term1621 A B z f g x lt2 H.
Proof. exact (@lem352320 A B f g x lt2 z x''' H f''' f'' h2 (@lem352310 A B f g x lt2 H h1)). Qed.
Lemma lem352324 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f g x lt2 H) (h2 : term461 A B lt2 z x''' H f''' f'') : term1622 A B z f g x lt2 H.
Proof. exact (fun h0 : term1623 A B z f g x lt2 H => @lem352323 A B f g x lt2 z x''' H f''' f'' h1 h2). Qed.
Lemma lem352326 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem352327 {A B : Type'} (z : type515 A B) (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1622 A B z f g x lt2 H) = (term1621 A B z f g x lt2 H).
Proof. exact (@lem352326 (term1621 A B z f g x lt2 H)). Qed.
Lemma lem352328 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f g x lt2 H) (h2 : term461 A B lt2 z x''' H f''' f'') : term1621 A B z f g x lt2 H.
Proof. exact (EQ_MP (@lem352327 A B z f g x lt2 H) (@lem352324 A B f g x lt2 z x''' H f''' f'' h1 h2)). Qed.
Lemma lem352331 {A B : Type'} (x''' : type569 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1624 A B x''' f lt2 H) : term1624 A B x''' f lt2 H.
Proof. exact (h1). Qed.
Lemma lem352332 {A B : Type'} (x''' : type569 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1624 A B x''' f lt2 H) : term1625 A B x''' f lt2 H.
Proof. exact (fun h0 : (term1626 A B x''' f lt2 H) = (term1627 A B x''' f lt2 H) => @lem352331 A B x''' f lt2 H h1). Qed.
Lemma lem352334 (p : Prop) : (term1617 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem352335 {A B : Type'} (x''' : type569 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1625 A B x''' f lt2 H) = (term1624 A B x''' f lt2 H).
Proof. exact (@lem352334 ((term1626 A B x''' f lt2 H) = (term1627 A B x''' f lt2 H))). Qed.
Lemma lem352336 {A B : Type'} (x''' : type569 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1624 A B x''' f lt2 H) : term1624 A B x''' f lt2 H.
Proof. exact (EQ_MP (@lem352335 A B x''' f lt2 H) (@lem352332 A B x''' f lt2 H h1)). Qed.
Lemma lem352342 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem352343 {A B : Type'} (x : type410 A B) (g : type409 A B) (_7576 : A) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1604 A B x g _7576 f _7574 _7575 _7577) = (term1628 A B x g _7576 f _7574 _7575 _7577).
Proof. exact (@lem352342 (term1208 A B _7576 x _7574 _7575) (term1229 A _7574) (term1629 A B g _7576 f _7574 _7575 _7577)). Qed.
Lemma lem352357 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem352358 {A B : Type'} (g : type409 A B) (_7576 : A) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1630 A B g _7576 f _7574 _7575 _7577) = (term1631 A B g _7576 f _7574 _7575 _7577).
Proof. exact (@lem352357 ((term1180 A B f _7574 _7575 _7576) = (term1180 A B g _7574 _7575 _7576)) (term1229 A _7574) ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577))). Qed.
Lemma lem352374 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem352375 {A B : Type'} (f : type409 A B) (_7575 : type549 A B) (_7577 : A) (_7574 : type1402 A) : (term1632 A B f _7574 _7575 _7577) = (term1633 A B f _7575 _7577 _7574).
Proof. exact (@lem352374 ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577)) (term1229 A _7574)). Qed.
Lemma lem352383 {A B : Type'} (f : type409 A B) (g : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) : (term1634 A B f g _7574 _7575 _7576) = (term1634 A B f g _7574 _7575 _7576).
Proof. exact (eq_refl (term1634 A B f g _7574 _7575 _7576)). Qed.
Lemma lem352384 {A B : Type'} (g : type409 A B) (_7576 : A) (f : type409 A B) (_7575 : type549 A B) (_7577 : A) (_7574 : type1402 A) : (term1631 A B g _7576 f _7574 _7575 _7577) = (term1635 A B g _7576 f _7575 _7577 _7574).
Proof. exact (MK_COMB (@lem352383 A B f g _7574 _7575 _7576) (@lem352375 A B f _7575 _7577 _7574)). Qed.
Lemma lem352395 {A B : Type'} (g : type409 A B) (_7576 : A) (f : type409 A B) (_7575 : type549 A B) (_7577 : A) (_7574 : type1402 A) : (term1630 A B g _7576 f _7574 _7575 _7577) = (term1635 A B g _7576 f _7575 _7577 _7574).
Proof. exact (TRANS (@lem352358 A B g _7576 f _7574 _7575 _7577) (@lem352384 A B g _7576 f _7575 _7577 _7574)). Qed.
Lemma lem352396 {A B : Type'} (_7576 : A) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1210 A B _7576 x _7574 _7575) = (term1210 A B _7576 x _7574 _7575).
Proof. exact (eq_refl (term1210 A B _7576 x _7574 _7575)). Qed.
Lemma lem352397 {A B : Type'} (x : type410 A B) (g : type409 A B) (_7576 : A) (f : type409 A B) (_7575 : type549 A B) (_7577 : A) (_7574 : type1402 A) : (term1628 A B x g _7576 f _7574 _7575 _7577) = (term1636 A B x g _7576 f _7575 _7577 _7574).
Proof. exact (MK_COMB (@lem352396 A B _7576 x _7574 _7575) (@lem352395 A B g _7576 f _7575 _7577 _7574)). Qed.
Lemma lem352401 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem352402 {A B : Type'} (g : type409 A B) (_7576 : A) (x : type410 A B) (f : type409 A B) (_7575 : type549 A B) (_7577 : A) (_7574 : type1402 A) : (term1636 A B x g _7576 f _7575 _7577 _7574) = (term1637 A B g _7576 x f _7575 _7577 _7574).
Proof. exact (@lem352401 ((term1180 A B f _7574 _7575 _7576) = (term1180 A B g _7574 _7575 _7576)) (term1208 A B _7576 x _7574 _7575) (term1633 A B f _7575 _7577 _7574)). Qed.
Lemma lem352418 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem352419 {A B : Type'} (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1638 A B _7576 x f _7575 _7577 _7574) = (term1639 A B f _7577 _7576 x _7575 _7574).
Proof. exact (@lem352418 ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577)) (term1208 A B _7576 x _7574 _7575) (term1229 A _7574)). Qed.
Lemma lem352437 {A B : Type'} (f : type409 A B) (g : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) : (term1634 A B f g _7574 _7575 _7576) = (term1634 A B f g _7574 _7575 _7576).
Proof. exact (eq_refl (term1634 A B f g _7574 _7575 _7576)). Qed.
Lemma lem352438 {A B : Type'} (g : type409 A B) (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1637 A B g _7576 x f _7575 _7577 _7574) = (term1640 A B g f _7577 _7576 x _7575 _7574).
Proof. exact (MK_COMB (@lem352437 A B f g _7574 _7575 _7576) (@lem352419 A B f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352449 {A B : Type'} (g : type409 A B) (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1636 A B x g _7576 f _7575 _7577 _7574) = (term1640 A B g f _7577 _7576 x _7575 _7574).
Proof. exact (TRANS (@lem352402 A B g _7576 x f _7575 _7577 _7574) (@lem352438 A B g f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352450 {A B : Type'} (g : type409 A B) (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1628 A B x g _7576 f _7574 _7575 _7577) = (term1640 A B g f _7577 _7576 x _7575 _7574).
Proof. exact (TRANS (@lem352397 A B x g _7576 f _7575 _7577 _7574) (@lem352449 A B g f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352451 {A B : Type'} (g : type409 A B) (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1604 A B x g _7576 f _7574 _7575 _7577) = (term1640 A B g f _7577 _7576 x _7575 _7574).
Proof. exact (TRANS (@lem352343 A B x g _7576 f _7574 _7575 _7577) (@lem352450 A B g f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem352453 {A B : Type'} (g : type409 A B) (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1641 A B x g _7576 f _7574 _7575 _7577) = (term1642 A B g f _7577 _7576 x _7575 _7574).
Proof. exact (MK_COMB (@lem352452) (@lem352451 A B g f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352469 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem352470 {A B : Type'} (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1643 A B _7576 x f _7574 _7575 _7577) = (term1644 A B _7576 x f _7574 _7575 _7577).
Proof. exact (@lem352469 (term1208 A B _7576 x _7574 _7575) (term1229 A _7574) ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577))). Qed.
Lemma lem352484 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem352485 {A B : Type'} (f : type409 A B) (_7575 : type549 A B) (_7577 : A) (_7574 : type1402 A) : (term1632 A B f _7574 _7575 _7577) = (term1633 A B f _7575 _7577 _7574).
Proof. exact (@lem352484 ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577)) (term1229 A _7574)). Qed.
Lemma lem352493 {A B : Type'} (_7576 : A) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1210 A B _7576 x _7574 _7575) = (term1210 A B _7576 x _7574 _7575).
Proof. exact (eq_refl (term1210 A B _7576 x _7574 _7575)). Qed.
Lemma lem352494 {A B : Type'} (_7576 : A) (x : type410 A B) (f : type409 A B) (_7575 : type549 A B) (_7577 : A) (_7574 : type1402 A) : (term1644 A B _7576 x f _7574 _7575 _7577) = (term1638 A B _7576 x f _7575 _7577 _7574).
Proof. exact (MK_COMB (@lem352493 A B _7576 x _7574 _7575) (@lem352485 A B f _7575 _7577 _7574)). Qed.
Lemma lem352498 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem352499 {A B : Type'} (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1638 A B _7576 x f _7575 _7577 _7574) = (term1639 A B f _7577 _7576 x _7575 _7574).
Proof. exact (@lem352498 ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577)) (term1208 A B _7576 x _7574 _7575) (term1229 A _7574)). Qed.
Lemma lem352517 {A B : Type'} (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1644 A B _7576 x f _7574 _7575 _7577) = (term1639 A B f _7577 _7576 x _7575 _7574).
Proof. exact (TRANS (@lem352494 A B _7576 x f _7575 _7577 _7574) (@lem352499 A B f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352518 {A B : Type'} (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1643 A B _7576 x f _7574 _7575 _7577) = (term1639 A B f _7577 _7576 x _7575 _7574).
Proof. exact (TRANS (@lem352470 A B _7576 x f _7574 _7575 _7577) (@lem352517 A B f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352519 {A B : Type'} (f : type409 A B) (g : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) : (term1634 A B f g _7574 _7575 _7576) = (term1634 A B f g _7574 _7575 _7576).
Proof. exact (eq_refl (term1634 A B f g _7574 _7575 _7576)). Qed.
Lemma lem352520 {A B : Type'} (g : type409 A B) (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1645 A B g _7576 x f _7574 _7575 _7577) = (term1640 A B g f _7577 _7576 x _7575 _7574).
Proof. exact (MK_COMB (@lem352519 A B f g _7574 _7575 _7576) (@lem352518 A B f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352531 {A B : Type'} (g : type409 A B) (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : ((term1604 A B x g _7576 f _7574 _7575 _7577) = (term1645 A B g _7576 x f _7574 _7575 _7577)) = ((term1640 A B g f _7577 _7576 x _7575 _7574) = (term1640 A B g f _7577 _7576 x _7575 _7574)).
Proof. exact (MK_COMB (@lem352453 A B g f _7577 _7576 x _7575 _7574) (@lem352520 A B g f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352533 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem352534 (x : Prop) : (x = x) = True.
Proof. exact (@lem352533 Prop x). Qed.
Lemma lem352535 {A B : Type'} (g : type409 A B) (f : type409 A B) (_7577 : A) (_7576 : A) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : ((term1640 A B g f _7577 _7576 x _7575 _7574) = (term1640 A B g f _7577 _7576 x _7575 _7574)) = True.
Proof. exact (@lem352534 (term1640 A B g f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352536 {A B : Type'} (g : type409 A B) (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : ((term1604 A B x g _7576 f _7574 _7575 _7577) = (term1645 A B g _7576 x f _7574 _7575 _7577)) = True.
Proof. exact (TRANS (@lem352531 A B g f _7577 _7576 x _7575 _7574) (@lem352535 A B g f _7577 _7576 x _7575 _7574)). Qed.
Lemma lem352537 {A B : Type'} (g : type409 A B) (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : True = ((term1604 A B x g _7576 f _7574 _7575 _7577) = (term1645 A B g _7576 x f _7574 _7575 _7577)).
Proof. exact (SYM (@lem352536 A B g _7576 x f _7574 _7575 _7577)). Qed.
Lemma lem352538 {A B : Type'} (g : type409 A B) (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1604 A B x g _7576 f _7574 _7575 _7577) = (term1645 A B g _7576 x f _7574 _7575 _7577).
Proof. exact (EQ_MP (@lem352537 A B g _7576 x f _7574 _7575 _7577) (@lem0)). Qed.
Lemma lem352539 {A B : Type'} (_7576 : A) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1645 A B g _7576 x f _7574 _7575 _7577.
Proof. exact (EQ_MP (@lem352538 A B g _7576 x f _7574 _7575 _7577) (@lem351902 A B _7576 _7574 _7575 _7577 g x f h1)). Qed.
Lemma lem352541 (b : Prop) (a : Prop) : (a \/ b) = (term1618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem352542 {A B : Type'} (x : type410 A B) (_7577 : A) (f : type409 A B) (g : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) : (term1645 A B g _7576 x f _7574 _7575 _7577) = (term1646 A B x _7577 f g _7574 _7575 _7576).
Proof. exact (@lem352541 (term1643 A B _7576 x f _7574 _7575 _7577) ((term1180 A B f _7574 _7575 _7576) = (term1180 A B g _7574 _7575 _7576))). Qed.
Lemma lem352544 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem352545 {A B : Type'} (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1649 A B _7576 x f _7574 _7575 _7577) = (term1650 A B _7576 x f _7574 _7575 _7577).
Proof. exact (@lem352544 (term1229 A _7574) (term1651 A B _7576 x f _7574 _7575 _7577)). Qed.
Lemma lem352547 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem352548 {A : Type'} (_7574 : type1402 A) : (term1653 A _7574) = (@I ((A -> A -> Prop) -> Prop) (@WF A) _7574).
Proof. exact (@lem352547 (@I ((A -> A -> Prop) -> Prop) (@WF A) _7574)). Qed.
Lemma lem352549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem352550 {A : Type'} (_7574 : type1402 A) : (term1654 A _7574) = (term1349 A _7574).
Proof. exact (MK_COMB (@lem352549) (@lem352548 A _7574)). Qed.
Lemma lem352552 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem352553 {A B : Type'} (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1655 A B _7576 x f _7574 _7575 _7577) = (term1656 A B _7576 x f _7574 _7575 _7577).
Proof. exact (@lem352552 (term1208 A B _7576 x _7574 _7575) ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577))). Qed.
Lemma lem352555 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem352556 {A B : Type'} (_7576 : A) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1657 A B _7576 x _7574 _7575) = (term1206 A B _7576 x _7574 _7575).
Proof. exact (@lem352555 (term1206 A B _7576 x _7574 _7575)). Qed.
Lemma lem352557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem352558 {A B : Type'} (_7576 : A) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1658 A B _7576 x _7574 _7575) = (term1659 A B _7576 x _7574 _7575).
Proof. exact (MK_COMB (@lem352557) (@lem352556 A B _7576 x _7574 _7575)). Qed.
Lemma lem352559 {A B : Type'} (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1660 A B f _7574 _7575 _7577) = (term1660 A B f _7574 _7575 _7577).
Proof. exact (eq_refl (term1660 A B f _7574 _7575 _7577)). Qed.
Lemma lem352560 {A B : Type'} (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1656 A B _7576 x f _7574 _7575 _7577) = (term1661 A B _7576 x f _7574 _7575 _7577).
Proof. exact (MK_COMB (@lem352558 A B _7576 x _7574 _7575) (@lem352559 A B f _7574 _7575 _7577)). Qed.
Lemma lem352561 {A B : Type'} (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1655 A B _7576 x f _7574 _7575 _7577) = (term1661 A B _7576 x f _7574 _7575 _7577).
Proof. exact (TRANS (@lem352553 A B _7576 x f _7574 _7575 _7577) (@lem352560 A B _7576 x f _7574 _7575 _7577)). Qed.
Lemma lem352562 {A B : Type'} (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1650 A B _7576 x f _7574 _7575 _7577) = (term1662 A B _7576 x f _7574 _7575 _7577).
Proof. exact (MK_COMB (@lem352550 A _7574) (@lem352561 A B _7576 x f _7574 _7575 _7577)). Qed.
Lemma lem352563 {A B : Type'} (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1649 A B _7576 x f _7574 _7575 _7577) = (term1662 A B _7576 x f _7574 _7575 _7577).
Proof. exact (TRANS (@lem352545 A B _7576 x f _7574 _7575 _7577) (@lem352562 A B _7576 x f _7574 _7575 _7577)). Qed.
Lemma lem352564 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem352565 {A B : Type'} (_7576 : A) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1663 A B _7576 x f _7574 _7575 _7577) = (term1664 A B _7576 x f _7574 _7575 _7577).
Proof. exact (MK_COMB (@lem352564) (@lem352563 A B _7576 x f _7574 _7575 _7577)). Qed.
Lemma lem352566 {A B : Type'} (f : type409 A B) (g : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) : ((term1180 A B f _7574 _7575 _7576) = (term1180 A B g _7574 _7575 _7576)) = ((term1180 A B f _7574 _7575 _7576) = (term1180 A B g _7574 _7575 _7576)).
Proof. exact (eq_refl ((term1180 A B f _7574 _7575 _7576) = (term1180 A B g _7574 _7575 _7576))). Qed.
Lemma lem352567 {A B : Type'} (x : type410 A B) (_7577 : A) (f : type409 A B) (g : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) : (term1646 A B x _7577 f g _7574 _7575 _7576) = (term1665 A B x _7577 f g _7574 _7575 _7576).
Proof. exact (MK_COMB (@lem352565 A B _7576 x f _7574 _7575 _7577) (@lem352566 A B f g _7574 _7575 _7576)). Qed.
Lemma lem352568 {A B : Type'} (x : type410 A B) (_7577 : A) (f : type409 A B) (g : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) : (term1645 A B g _7576 x f _7574 _7575 _7577) = (term1665 A B x _7577 f g _7574 _7575 _7576).
Proof. exact (TRANS (@lem352542 A B x _7577 f g _7574 _7575 _7576) (@lem352567 A B x _7577 f g _7574 _7575 _7576)). Qed.
Lemma lem352570 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f g x lt2 H) (h2 : term1624 A B x''' f lt2 H) (h3 : term461 A B lt2 z x''' H f''' f'') : term1666 A B z g x x''' f lt2 H.
Proof. exact (conj (@lem352328 A B f g x lt2 z x''' H f''' f'' h1 h3) (@lem352336 A B x''' f lt2 H h2)). Qed.
Lemma lem352571 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f g x lt2 H) (h2 : term1624 A B x''' f lt2 H) (h3 : term461 A B lt2 z x''' H f''' f'') : term1667 A B z g x x''' f lt2 H.
Proof. exact (conj (@lem352302 A B lt2 z x''' H f''' f'' h3) (@lem352570 A B g x f lt2 z x''' H f''' f'' h1 h2 h3)). Qed.
Lemma lem352573 {A B : Type'} (_7577 : A) (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1665 A B x _7577 f g _7574 _7575 _7576.
Proof. exact (EQ_MP (@lem352568 A B x _7577 f g _7574 _7575 _7576) (@lem352539 A B _7576 _7574 _7575 _7577 g x f h1)). Qed.
Lemma lem352574 {A B : Type'} (_7577 : A) (_7574 : type1402 A) (_7575 : type549 A B) (_7576 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1665 A B x _7577 f g _7574 _7575 _7576.
Proof. exact (@lem352573 A B _7577 _7574 _7575 _7576 g x f h1). Qed.
Lemma lem352575 {A B : Type'} (x''' : type569 A B) (z : type515 A B) (lt2 : type1402 A) (H : type549 A B) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1668 A B x''' z f g x lt2 H.
Proof. exact (@lem352574 A B (term1669 A B x''' f lt2 H) lt2 H (term1670 A B z f g x lt2 H) g x f h1). Qed.
Lemma lem352578 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1202 A B f g x lt2 H) (h3 : term1624 A B x''' f lt2 H) (h4 : term461 A B lt2 z x''' H f''' f'') : (term1671 A B z f g x lt2 H) = (term1672 A B z f g x lt2 H).
Proof. exact (@lem352575 A B x''' z lt2 H g x f h1 (@lem352571 A B g x f lt2 z x''' H f''' f'' h2 h3 h4)). Qed.
Lemma lem352579 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1202 A B f g x lt2 H) (h3 : term1624 A B x''' f lt2 H) (h4 : term461 A B lt2 z x''' H f''' f'') : term1673 A B z f g x lt2 H.
Proof. exact (fun h0 : term1674 A B z f g x lt2 H => @lem352578 A B g x f lt2 z x''' H f''' f'' h1 h2 h3 h4). Qed.
Lemma lem352581 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem352582 {A B : Type'} (z : type515 A B) (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1673 A B z f g x lt2 H) = ((term1671 A B z f g x lt2 H) = (term1672 A B z f g x lt2 H)).
Proof. exact (@lem352581 ((term1671 A B z f g x lt2 H) = (term1672 A B z f g x lt2 H))). Qed.
Lemma lem352583 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1202 A B f g x lt2 H) (h3 : term1624 A B x''' f lt2 H) (h4 : term461 A B lt2 z x''' H f''' f'') : (term1671 A B z f g x lt2 H) = (term1672 A B z f g x lt2 H).
Proof. exact (EQ_MP (@lem352582 A B z f g x lt2 H) (@lem352579 A B g x f lt2 z x''' H f''' f'' h1 h2 h3 h4)). Qed.
Lemma lem352589 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem352590 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : (term1602 A B z _7583 H _7584 _7585) = (term1675 A B H z _7583 _7584 _7585).
Proof. exact (@lem352589 ((term1286 A B H _7583 _7585) = (term1286 A B H _7584 _7585)) (term1322 A B z _7583 _7584 _7585)). Qed.
Lemma lem352600 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem352601 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : (term1676 A B z _7583 H _7584 _7585) = (term1677 A B H z _7583 _7584 _7585).
Proof. exact (MK_COMB (@lem352600) (@lem352590 A B H z _7583 _7584 _7585)). Qed.
Lemma lem352611 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : (term1675 A B H z _7583 _7584 _7585) = (term1675 A B H z _7583 _7584 _7585).
Proof. exact (eq_refl (term1675 A B H z _7583 _7584 _7585)). Qed.
Lemma lem352612 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : ((term1602 A B z _7583 H _7584 _7585) = (term1675 A B H z _7583 _7584 _7585)) = ((term1675 A B H z _7583 _7584 _7585) = (term1675 A B H z _7583 _7584 _7585)).
Proof. exact (MK_COMB (@lem352601 A B H z _7583 _7584 _7585) (@lem352611 A B H z _7583 _7584 _7585)). Qed.
Lemma lem352614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem352615 (x : Prop) : (x = x) = True.
Proof. exact (@lem352614 Prop x). Qed.
Lemma lem352616 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : ((term1675 A B H z _7583 _7584 _7585) = (term1675 A B H z _7583 _7584 _7585)) = True.
Proof. exact (@lem352615 (term1675 A B H z _7583 _7584 _7585)). Qed.
Lemma lem352617 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : ((term1602 A B z _7583 H _7584 _7585) = (term1675 A B H z _7583 _7584 _7585)) = True.
Proof. exact (TRANS (@lem352612 A B H z _7583 _7584 _7585) (@lem352616 A B H z _7583 _7584 _7585)). Qed.
Lemma lem352618 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : True = ((term1602 A B z _7583 H _7584 _7585) = (term1675 A B H z _7583 _7584 _7585)).
Proof. exact (SYM (@lem352617 A B H z _7583 _7584 _7585)). Qed.
Lemma lem352619 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : (term1602 A B z _7583 H _7584 _7585) = (term1675 A B H z _7583 _7584 _7585).
Proof. exact (EQ_MP (@lem352618 A B H z _7583 _7584 _7585) (@lem0)). Qed.
Lemma lem352620 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1675 A B H z _7583 _7584 _7585.
Proof. exact (EQ_MP (@lem352619 A B H z _7583 _7584 _7585) (@lem351840 A B _7583 _7584 _7585 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem352622 (b : Prop) (a : Prop) : (a \/ b) = (term1618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem352623 {A B : Type'} (z : type515 A B) (_7583 : A -> B) (H : type549 A B) (_7584 : A -> B) (_7585 : A) : (term1675 A B H z _7583 _7584 _7585) = (term1678 A B z _7583 H _7584 _7585).
Proof. exact (@lem352622 (term1322 A B z _7583 _7584 _7585) ((term1286 A B H _7583 _7585) = (term1286 A B H _7584 _7585))). Qed.
Lemma lem352625 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem352626 {A B : Type'} (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : (term1679 A B z _7583 _7584 _7585) = ((term1315 A B z _7583 _7584 _7585) = (term1318 A B z _7583 _7584 _7585)).
Proof. exact (@lem352625 ((term1315 A B z _7583 _7584 _7585) = (term1318 A B z _7583 _7584 _7585))). Qed.
Lemma lem352627 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem352628 {A B : Type'} (z : type515 A B) (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) : (term1680 A B z _7583 _7584 _7585) = (term1681 A B z _7583 _7584 _7585).
Proof. exact (MK_COMB (@lem352627) (@lem352626 A B z _7583 _7584 _7585)). Qed.
Lemma lem352629 {A B : Type'} (_7583 : A -> B) (H : type549 A B) (_7584 : A -> B) (_7585 : A) : ((term1286 A B H _7583 _7585) = (term1286 A B H _7584 _7585)) = ((term1286 A B H _7583 _7585) = (term1286 A B H _7584 _7585)).
Proof. exact (eq_refl ((term1286 A B H _7583 _7585) = (term1286 A B H _7584 _7585))). Qed.
Lemma lem352630 {A B : Type'} (z : type515 A B) (_7583 : A -> B) (H : type549 A B) (_7584 : A -> B) (_7585 : A) : (term1678 A B z _7583 H _7584 _7585) = (term1682 A B z _7583 H _7584 _7585).
Proof. exact (MK_COMB (@lem352628 A B z _7583 _7584 _7585) (@lem352629 A B _7583 H _7584 _7585)). Qed.
Lemma lem352631 {A B : Type'} (z : type515 A B) (_7583 : A -> B) (H : type549 A B) (_7584 : A -> B) (_7585 : A) : (term1675 A B H z _7583 _7584 _7585) = (term1682 A B z _7583 H _7584 _7585).
Proof. exact (TRANS (@lem352623 A B z _7583 H _7584 _7585) (@lem352630 A B z _7583 H _7584 _7585)). Qed.
Lemma lem352634 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1682 A B z _7583 H _7584 _7585.
Proof. exact (EQ_MP (@lem352631 A B z _7583 H _7584 _7585) (@lem352620 A B _7583 _7584 _7585 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem352635 {A B : Type'} (_7583 : A -> B) (_7584 : A -> B) (_7585 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1682 A B z _7583 H _7584 _7585.
Proof. exact (@lem352634 A B _7583 _7584 _7585 lt2 z x''' H f''' f'' h1). Qed.
Lemma lem352636 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1683 A B z f g x lt2 H.
Proof. exact (@lem352635 A B (term1178 A B f lt2 H) (term1178 A B g lt2 H) (term1194 A B x lt2 H) lt2 z x''' H f''' f'' h1). Qed.
Lemma lem352639 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1202 A B f g x lt2 H) (h3 : term1624 A B x''' f lt2 H) (h4 : term461 A B lt2 z x''' H f''' f'') : (term1198 A B f x lt2 H) = (term1198 A B g x lt2 H).
Proof. exact (@lem352636 A B f g x lt2 z x''' H f''' f'' h4 (@lem352583 A B g x f lt2 z x''' H f''' f'' h1 h2 h3 h4)). Qed.
Lemma lem352640 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1624 A B x''' f lt2 H) (h3 : term461 A B lt2 z x''' H f''' f'') : term1684 A B f g x lt2 H.
Proof. exact (fun h0 : term1202 A B f g x lt2 H => @lem352639 A B g x f lt2 z x''' H f''' f'' h1 h0 h2 h3). Qed.
Lemma lem352642 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem352643 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1684 A B f g x lt2 H) = ((term1198 A B f x lt2 H) = (term1198 A B g x lt2 H)).
Proof. exact (@lem352642 ((term1198 A B f x lt2 H) = (term1198 A B g x lt2 H))). Qed.
Lemma lem352644 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1624 A B x''' f lt2 H) (h3 : term461 A B lt2 z x''' H f''' f'') : (term1198 A B f x lt2 H) = (term1198 A B g x lt2 H).
Proof. exact (EQ_MP (@lem352643 A B f g x lt2 H) (@lem352640 A B g x f lt2 z x''' H f''' f'' h1 h2 h3)). Qed.
Lemma lem352650 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem352651 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1605 A B g x f _7574 _7575 _7577) = (term1685 A B g x f _7574 _7575 _7577).
Proof. exact (@lem352650 (term1202 A B f g x _7574 _7575) (term1229 A _7574) ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577))). Qed.
Lemma lem352667 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem352668 {A B : Type'} (f : type409 A B) (_7575 : type549 A B) (_7577 : A) (_7574 : type1402 A) : (term1632 A B f _7574 _7575 _7577) = (term1633 A B f _7575 _7577 _7574).
Proof. exact (@lem352667 ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577)) (term1229 A _7574)). Qed.
Lemma lem352676 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1611 A B f g x _7574 _7575) = (term1611 A B f g x _7574 _7575).
Proof. exact (eq_refl (term1611 A B f g x _7574 _7575)). Qed.
Lemma lem352677 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (_7575 : type549 A B) (_7577 : A) (_7574 : type1402 A) : (term1685 A B g x f _7574 _7575 _7577) = (term1686 A B g x f _7575 _7577 _7574).
Proof. exact (MK_COMB (@lem352676 A B f g x _7574 _7575) (@lem352668 A B f _7575 _7577 _7574)). Qed.
Lemma lem352681 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem352682 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1686 A B g x f _7575 _7577 _7574) = (term1687 A B _7577 f g x _7575 _7574).
Proof. exact (@lem352681 ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577)) (term1202 A B f g x _7574 _7575) (term1229 A _7574)). Qed.
Lemma lem352702 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1685 A B g x f _7574 _7575 _7577) = (term1687 A B _7577 f g x _7575 _7574).
Proof. exact (TRANS (@lem352677 A B g x f _7575 _7577 _7574) (@lem352682 A B _7577 f g x _7575 _7574)). Qed.
Lemma lem352703 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1605 A B g x f _7574 _7575 _7577) = (term1687 A B _7577 f g x _7575 _7574).
Proof. exact (TRANS (@lem352651 A B g x f _7574 _7575 _7577) (@lem352702 A B _7577 f g x _7575 _7574)). Qed.
Lemma lem352704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem352705 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1688 A B g x f _7574 _7575 _7577) = (term1689 A B _7577 f g x _7575 _7574).
Proof. exact (MK_COMB (@lem352704) (@lem352703 A B _7577 f g x _7575 _7574)). Qed.
Lemma lem352721 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem352722 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1690 A B f g x _7574 _7575) = (term1691 A B f g x _7575 _7574).
Proof. exact (@lem352721 (term1202 A B f g x _7574 _7575) (term1229 A _7574)). Qed.
Lemma lem352730 {A B : Type'} (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1692 A B f _7574 _7575 _7577) = (term1692 A B f _7574 _7575 _7577).
Proof. exact (eq_refl (term1692 A B f _7574 _7575 _7577)). Qed.
Lemma lem352731 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : (term1693 A B _7577 f g x _7574 _7575) = (term1687 A B _7577 f g x _7575 _7574).
Proof. exact (MK_COMB (@lem352730 A B f _7574 _7575 _7577) (@lem352722 A B f g x _7575 _7574)). Qed.
Lemma lem352742 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : ((term1605 A B g x f _7574 _7575 _7577) = (term1693 A B _7577 f g x _7574 _7575)) = ((term1687 A B _7577 f g x _7575 _7574) = (term1687 A B _7577 f g x _7575 _7574)).
Proof. exact (MK_COMB (@lem352705 A B _7577 f g x _7575 _7574) (@lem352731 A B _7577 f g x _7575 _7574)). Qed.
Lemma lem352744 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem352745 (x : Prop) : (x = x) = True.
Proof. exact (@lem352744 Prop x). Qed.
Lemma lem352746 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7575 : type549 A B) (_7574 : type1402 A) : ((term1687 A B _7577 f g x _7575 _7574) = (term1687 A B _7577 f g x _7575 _7574)) = True.
Proof. exact (@lem352745 (term1687 A B _7577 f g x _7575 _7574)). Qed.
Lemma lem352747 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : ((term1605 A B g x f _7574 _7575 _7577) = (term1693 A B _7577 f g x _7574 _7575)) = True.
Proof. exact (TRANS (@lem352742 A B _7577 f g x _7575 _7574) (@lem352746 A B _7577 f g x _7575 _7574)). Qed.
Lemma lem352748 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : True = ((term1605 A B g x f _7574 _7575 _7577) = (term1693 A B _7577 f g x _7574 _7575)).
Proof. exact (SYM (@lem352747 A B _7577 f g x _7574 _7575)). Qed.
Lemma lem352749 {A B : Type'} (_7577 : A) (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1605 A B g x f _7574 _7575 _7577) = (term1693 A B _7577 f g x _7574 _7575).
Proof. exact (EQ_MP (@lem352748 A B _7577 f g x _7574 _7575) (@lem0)). Qed.
Lemma lem352750 {A B : Type'} (_7577 : A) (_7574 : type1402 A) (_7575 : type549 A B) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1693 A B _7577 f g x _7574 _7575.
Proof. exact (EQ_MP (@lem352749 A B _7577 f g x _7574 _7575) (@lem351912 A B _7574 _7575 _7577 g x f h1)). Qed.
Lemma lem352752 (b : Prop) (a : Prop) : (a \/ b) = (term1618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem352753 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1693 A B _7577 f g x _7574 _7575) = (term1694 A B g x f _7574 _7575 _7577).
Proof. exact (@lem352752 (term1690 A B f g x _7574 _7575) ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577))). Qed.
Lemma lem352755 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem352756 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1695 A B f g x _7574 _7575) = (term1696 A B f g x _7574 _7575).
Proof. exact (@lem352755 (term1229 A _7574) (term1202 A B f g x _7574 _7575)). Qed.
Lemma lem352758 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem352759 {A : Type'} (_7574 : type1402 A) : (term1653 A _7574) = (@I ((A -> A -> Prop) -> Prop) (@WF A) _7574).
Proof. exact (@lem352758 (@I ((A -> A -> Prop) -> Prop) (@WF A) _7574)). Qed.
Lemma lem352760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem352761 {A : Type'} (_7574 : type1402 A) : (term1654 A _7574) = (term1349 A _7574).
Proof. exact (MK_COMB (@lem352760) (@lem352759 A _7574)). Qed.
Lemma lem352763 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem352764 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1697 A B f g x _7574 _7575) = ((term1198 A B f x _7574 _7575) = (term1198 A B g x _7574 _7575)).
Proof. exact (@lem352763 ((term1198 A B f x _7574 _7575) = (term1198 A B g x _7574 _7575))). Qed.
Lemma lem352765 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1696 A B f g x _7574 _7575) = (term1698 A B f g x _7574 _7575).
Proof. exact (MK_COMB (@lem352761 A _7574) (@lem352764 A B f g x _7574 _7575)). Qed.
Lemma lem352766 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1695 A B f g x _7574 _7575) = (term1698 A B f g x _7574 _7575).
Proof. exact (TRANS (@lem352756 A B f g x _7574 _7575) (@lem352765 A B f g x _7574 _7575)). Qed.
Lemma lem352767 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem352768 {A B : Type'} (f : type409 A B) (g : type409 A B) (x : type410 A B) (_7574 : type1402 A) (_7575 : type549 A B) : (term1699 A B f g x _7574 _7575) = (term1700 A B f g x _7574 _7575).
Proof. exact (MK_COMB (@lem352767) (@lem352766 A B f g x _7574 _7575)). Qed.
Lemma lem352769 {A B : Type'} (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577)) = ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577)).
Proof. exact (eq_refl ((term1180 A B f _7574 _7575 _7577) = (term1187 A B f _7574 _7575 _7577))). Qed.
Lemma lem352770 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1694 A B g x f _7574 _7575 _7577) = (term1701 A B g x f _7574 _7575 _7577).
Proof. exact (MK_COMB (@lem352768 A B f g x _7574 _7575) (@lem352769 A B f _7574 _7575 _7577)). Qed.
Lemma lem352771 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) : (term1693 A B _7577 f g x _7574 _7575) = (term1701 A B g x f _7574 _7575 _7577).
Proof. exact (TRANS (@lem352753 A B g x f _7574 _7575 _7577) (@lem352770 A B g x f _7574 _7575 _7577)). Qed.
Lemma lem352773 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1624 A B x''' f lt2 H) (h3 : term461 A B lt2 z x''' H f''' f'') : term1698 A B f g x lt2 H.
Proof. exact (conj (@lem352295 A B lt2 z x''' H f''' f'' h3) (@lem352644 A B g x f lt2 z x''' H f''' f'' h1 h2 h3)). Qed.
Lemma lem352775 {A B : Type'} (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1701 A B g x f _7574 _7575 _7577.
Proof. exact (EQ_MP (@lem352771 A B g x f _7574 _7575 _7577) (@lem352750 A B _7577 _7574 _7575 g x f h1)). Qed.
Lemma lem352776 {A B : Type'} (_7574 : type1402 A) (_7575 : type549 A B) (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1701 A B g x f _7574 _7575 _7577.
Proof. exact (@lem352775 A B _7574 _7575 _7577 g x f h1). Qed.
Lemma lem352777 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (h1 : term1170 A B g x f) : term1701 A B g x f lt2 H _7577.
Proof. exact (@lem352776 A B lt2 H _7577 g x f h1). Qed.
Lemma lem352780 {A B : Type'} (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1624 A B x''' f lt2 H) (h3 : term461 A B lt2 z x''' H f''' f'') : (term1180 A B f lt2 H _7577) = (term1187 A B f lt2 H _7577).
Proof. exact (@lem352777 A B lt2 H _7577 g x f h1 (@lem352773 A B g x f lt2 z x''' H f''' f'' h1 h2 h3)). Qed.
Lemma lem352781 {A B : Type'} (_7577 : A) (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1624 A B x''' f lt2 H) (h3 : term461 A B lt2 z x''' H f''' f'') : (term1180 A B f lt2 H _7577) = (term1187 A B f lt2 H _7577).
Proof. exact (@lem352780 A B _7577 g x f lt2 z x''' H f''' f'' h1 h2 h3). Qed.
Lemma lem352782 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term1624 A B x''' f lt2 H) (h3 : term461 A B lt2 z x''' H f''' f'') : (term1626 A B x''' f lt2 H) = (term1627 A B x''' f lt2 H).
Proof. exact (@lem352781 A B (term1669 A B x''' f lt2 H) g x f lt2 z x''' H f''' f'' h1 h2 h3). Qed.
Lemma lem352783 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term461 A B lt2 z x''' H f''' f'') : term1702 A B x''' f lt2 H.
Proof. exact (fun h0 : term1624 A B x''' f lt2 H => @lem352782 A B g x f lt2 z x''' H f''' f'' h1 h0 h2). Qed.
Lemma lem352785 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem352786 {A B : Type'} (x''' : type569 A B) (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) : (term1702 A B x''' f lt2 H) = ((term1626 A B x''' f lt2 H) = (term1627 A B x''' f lt2 H)).
Proof. exact (@lem352785 ((term1626 A B x''' f lt2 H) = (term1627 A B x''' f lt2 H))). Qed.
Lemma lem352787 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term461 A B lt2 z x''' H f''' f'') : (term1626 A B x''' f lt2 H) = (term1627 A B x''' f lt2 H).
Proof. exact (EQ_MP (@lem352786 A B x''' f lt2 H) (@lem352783 A B g x f lt2 z x''' H f''' f'' h1 h2)). Qed.
Lemma lem352790 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem352792 {A B : Type'} (H : type549 A B) (x''' : type569 A B) (_7586 : A -> B) : (term1303 A B H x''' _7586) = (term1703 A B H x''' _7586).
Proof. exact (@lem352790 ((term1296 A B x''' _7586) = (term1300 A B H x''' _7586))). Qed.
Lemma lem352795 {A B : Type'} (_7586 : A -> B) (H : type549 A B) (x''' : type569 A B) (h1 : term1305 A B H x''') : term1703 A B H x''' _7586.
Proof. exact (EQ_MP (@lem352792 A B H x''' _7586) (@lem351828 A B _7586 H x''' h1)). Qed.
Lemma lem352796 {A B : Type'} (_7586 : A -> B) (H : type549 A B) (x''' : type569 A B) (h1 : term1305 A B H x''') : term1703 A B H x''' _7586.
Proof. exact (@lem352795 A B _7586 H x''' h1). Qed.
Lemma lem352797 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (H : type549 A B) (x''' : type569 A B) (h1 : term1305 A B H x''') : term1704 A B x''' f lt2 H.
Proof. exact (@lem352796 A B (term1178 A B f lt2 H) H x''' h1). Qed.
Lemma lem352800 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1305 A B H x''') (h2 : term1170 A B g x f) (h3 : term461 A B lt2 z x''' H f''' f'') : False.
Proof. exact (@lem352797 A B f lt2 H x''' h1 (@lem352787 A B g x f lt2 z x''' H f''' f'' h2 h3)). Qed.
Lemma lem352801 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1305 A B H x''') (h2 : term1170 A B g x f) (h3 : term461 A B lt2 z x''' H f''' f'') : term1705.
Proof. exact (fun h0 : ~ False => @lem352800 A B g x f lt2 z x''' H f''' f'' h1 h2 h3). Qed.
Lemma lem352803 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem352804 : term1705 = False.
Proof. exact (@lem352803 False). Qed.
Lemma lem352805 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1305 A B H x''') (h2 : term1170 A B g x f) (h3 : term461 A B lt2 z x''' H f''' f'') : False.
Proof. exact (EQ_MP (@lem352804) (@lem352801 A B g x f lt2 z x''' H f''' f'' h1 h2 h3)). Qed.
Lemma lem353091 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (proj1 (@lem350692 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem353092 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1614 A lt2.
Proof. exact (fun h0 : term1229 A lt2 => @lem353091 A B lt2 z x''' H f''' f'' h1). Qed.
Lemma lem353094 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem353095 {A : Type'} (lt2 : type1402 A) : (term1614 A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem353094 (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2)). Qed.
Lemma lem353096 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (EQ_MP (@lem353095 A lt2) (@lem353092 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem353098 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (proj1 (@lem350692 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem353099 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1614 A lt2.
Proof. exact (fun h0 : term1229 A lt2 => @lem353098 A B lt2 z x''' H f''' f'' h1). Qed.
Lemma lem353101 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem353102 {A : Type'} (lt2 : type1402 A) : (term1614 A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem353101 (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2)). Qed.
Lemma lem353103 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (EQ_MP (@lem353102 A lt2) (@lem353099 A B lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem353106 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1202 A B f' g' x' lt2 H) : term1202 A B f' g' x' lt2 H.
Proof. exact (h1). Qed.
Lemma lem353107 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1202 A B f' g' x' lt2 H) : term1616 A B f' g' x' lt2 H.
Proof. exact (fun h0 : (term1198 A B f' x' lt2 H) = (term1198 A B g' x' lt2 H) => @lem353106 A B f' g' x' lt2 H h1). Qed.
Lemma lem353109 (p : Prop) : (term1617 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem353110 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1616 A B f' g' x' lt2 H) = (term1202 A B f' g' x' lt2 H).
Proof. exact (@lem353109 ((term1198 A B f' x' lt2 H) = (term1198 A B g' x' lt2 H))). Qed.
Lemma lem353111 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1202 A B f' g' x' lt2 H) : term1202 A B f' g' x' lt2 H.
Proof. exact (EQ_MP (@lem353110 A B f' g' x' lt2 H) (@lem353107 A B f' g' x' lt2 H h1)). Qed.
Lemma lem353113 (b : Prop) (a : Prop) : (a \/ b) = (term1618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem353116 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : (term1601 A B lt2 z _7596 H _7597 _7598) = (term1619 A B H lt2 z _7596 _7597 _7598).
Proof. exact (@lem353113 ((term1286 A B H _7596 _7598) = (term1286 A B H _7597 _7598)) (term1329 A B lt2 z _7596 _7597 _7598)). Qed.
Lemma lem353119 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1619 A B H lt2 z _7596 _7597 _7598.
Proof. exact (EQ_MP (@lem353116 A B H lt2 z _7596 _7597 _7598) (@lem351926 A B _7596 _7597 _7598 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem353120 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1619 A B H lt2 z _7596 _7597 _7598.
Proof. exact (@lem353119 A B _7596 _7597 _7598 lt2 z x''' H f''' f'' h1). Qed.
Lemma lem353121 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1620 A B z f' g' x' lt2 H.
Proof. exact (@lem353120 A B (term1178 A B f' lt2 H) (term1178 A B g' lt2 H) (term1194 A B x' lt2 H) lt2 z x''' H f''' f'' h1). Qed.
Lemma lem353124 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f' g' x' lt2 H) (h2 : term461 A B lt2 z x''' H f''' f'') : term1621 A B z f' g' x' lt2 H.
Proof. exact (@lem353121 A B f' g' x' lt2 z x''' H f''' f'' h2 (@lem353111 A B f' g' x' lt2 H h1)). Qed.
Lemma lem353125 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f' g' x' lt2 H) (h2 : term461 A B lt2 z x''' H f''' f'') : term1622 A B z f' g' x' lt2 H.
Proof. exact (fun h0 : term1623 A B z f' g' x' lt2 H => @lem353124 A B f' g' x' lt2 z x''' H f''' f'' h1 h2). Qed.
Lemma lem353127 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem353128 {A B : Type'} (z : type515 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1622 A B z f' g' x' lt2 H) = (term1621 A B z f' g' x' lt2 H).
Proof. exact (@lem353127 (term1621 A B z f' g' x' lt2 H)). Qed.
Lemma lem353129 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f' g' x' lt2 H) (h2 : term461 A B lt2 z x''' H f''' f'') : term1621 A B z f' g' x' lt2 H.
Proof. exact (EQ_MP (@lem353128 A B z f' g' x' lt2 H) (@lem353125 A B f' g' x' lt2 z x''' H f''' f'' h1 h2)). Qed.
Lemma lem353131 {A B : Type'} (_7600 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (@I (A -> B) f''' _7600) = (term1286 A B H f''' _7600).
Proof. exact (EQ_MP (@lem351811 A B H f''' _7600) (@lem351810 A B _7600 H f''' f'' h1)). Qed.
Lemma lem353132 {A B : Type'} (_7600 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (@I (A -> B) f''' _7600) = (term1286 A B H f''' _7600).
Proof. exact (@lem353131 A B _7600 H f''' f'' h1). Qed.
Lemma lem353133 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (term1252 A B x'' lt2 H f''' f'') = (term1256 A B x'' lt2 H f''' f'').
Proof. exact (@lem353132 A B (term1238 A B x'' lt2 H f''' f'') H f''' f'' h1). Qed.
Lemma lem353134 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1706 A B x'' lt2 H f''' f''.
Proof. exact (fun h0 : term1260 A B x'' lt2 H f''' f'' => @lem353133 A B x'' lt2 H f''' f'' h1). Qed.
Lemma lem353136 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem353137 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) : (term1706 A B x'' lt2 H f''' f'') = ((term1252 A B x'' lt2 H f''' f'') = (term1256 A B x'' lt2 H f''' f'')).
Proof. exact (@lem353136 ((term1252 A B x'' lt2 H f''' f'') = (term1256 A B x'' lt2 H f''' f''))). Qed.
Lemma lem353138 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (term1252 A B x'' lt2 H f''' f'') = (term1256 A B x'' lt2 H f''' f'').
Proof. exact (EQ_MP (@lem353137 A B x'' lt2 H f''' f'') (@lem353134 A B x'' lt2 H f''' f'' h1)). Qed.
Lemma lem353140 {A B : Type'} (_7599 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (@I (A -> B) f'' _7599) = (term1286 A B H f'' _7599).
Proof. exact (EQ_MP (@lem351808 A B H f'' _7599) (@lem351807 A B _7599 H f''' f'' h1)). Qed.
Lemma lem353141 {A B : Type'} (_7599 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (@I (A -> B) f'' _7599) = (term1286 A B H f'' _7599).
Proof. exact (@lem353140 A B _7599 H f''' f'' h1). Qed.
Lemma lem353142 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (term1241 A B x'' lt2 H f''' f'') = (term1245 A B x'' lt2 H f''' f'').
Proof. exact (@lem353141 A B (term1238 A B x'' lt2 H f''' f'') H f''' f'' h1). Qed.
Lemma lem353143 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1707 A B x'' lt2 H f''' f''.
Proof. exact (fun h0 : term1249 A B x'' lt2 H f''' f'' => @lem353142 A B x'' lt2 H f''' f'' h1). Qed.
Lemma lem353145 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem353146 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) : (term1707 A B x'' lt2 H f''' f'') = ((term1241 A B x'' lt2 H f''' f'') = (term1245 A B x'' lt2 H f''' f'')).
Proof. exact (@lem353145 ((term1241 A B x'' lt2 H f''' f'') = (term1245 A B x'' lt2 H f''' f''))). Qed.
Lemma lem353147 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (term1241 A B x'' lt2 H f''' f'') = (term1245 A B x'' lt2 H f''' f'').
Proof. exact (EQ_MP (@lem353146 A B x'' lt2 H f''' f'') (@lem353143 A B x'' lt2 H f''' f'' h1)). Qed.
Lemma lem353150 {A B : Type'} (f''' : A -> B) (f'' : A -> B) (h1 : term96 A B f''' f'') : term96 A B f''' f''.
Proof. exact (h1). Qed.
Lemma lem353151 {A B : Type'} (f''' : A -> B) (f'' : A -> B) (h1 : term96 A B f''' f'') : term1708 A B f''' f''.
Proof. exact (fun h0 : f''' = f'' => @lem353150 A B f''' f'' h1). Qed.
Lemma lem353153 (p : Prop) : (term1617 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem353154 {A B : Type'} (f''' : A -> B) (f'' : A -> B) : (term1708 A B f''' f'') = (term96 A B f''' f'').
Proof. exact (@lem353153 (f''' = f'')). Qed.
Lemma lem353155 {A B : Type'} (f''' : A -> B) (f'' : A -> B) (h1 : term96 A B f''' f'') : term96 A B f''' f''.
Proof. exact (EQ_MP (@lem353154 A B f''' f'') (@lem353151 A B f''' f'' h1)). Qed.
Lemma lem353161 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353162 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1610 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1709 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353161 (term1208 A B _7593 x' _7591 _7592) (term1229 A _7591) (term1710 A B f' g' _7593 x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353176 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353177 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1711 A B f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1712 A B f' g' _7593 x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353176 ((term1180 A B f' _7591 _7592 _7593) = (term1180 A B g' _7591 _7592 _7593)) (term1229 A _7591) (term1606 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353193 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353194 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1713 A B x'' _7591 _7592 _7594 _7595) = (term1714 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353193 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591) (term1715 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353210 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353211 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7591 : type1402 A) (_7594 : A -> B) (_7595 : A -> B) : (term1716 A B x'' _7591 _7592 _7594 _7595) = (term1717 A B x'' _7592 _7591 _7594 _7595).
Proof. exact (@lem353210 (term1249 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591) (_7594 = _7595)). Qed.
Lemma lem353227 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem353228 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1718 A B _7591 _7594 _7595) = (term1719 A B _7594 _7595 _7591).
Proof. exact (@lem353227 (_7594 = _7595) (term1229 A _7591)). Qed.
Lemma lem353236 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1720 A B x'' _7591 _7592 _7594 _7595) = (term1720 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1720 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353237 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1717 A B x'' _7592 _7591 _7594 _7595) = (term1721 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353236 A B x'' _7591 _7592 _7594 _7595) (@lem353228 A B _7594 _7595 _7591)). Qed.
Lemma lem353241 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353242 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1721 A B x'' _7592 _7594 _7595 _7591) = (term1722 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353241 (_7594 = _7595) (term1249 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591)). Qed.
Lemma lem353262 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1717 A B x'' _7592 _7591 _7594 _7595) = (term1722 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353237 A B x'' _7592 _7594 _7595 _7591) (@lem353242 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353263 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1716 A B x'' _7591 _7592 _7594 _7595) = (term1722 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353211 A B x'' _7592 _7591 _7594 _7595) (@lem353262 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353264 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1262 A B x'' _7591 _7592 _7594 _7595) = (term1262 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1262 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353265 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1714 A B x'' _7591 _7592 _7594 _7595) = (term1723 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353264 A B x'' _7591 _7592 _7594 _7595) (@lem353263 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353269 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353270 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1723 A B x'' _7592 _7594 _7595 _7591) = (term1724 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353269 (_7594 = _7595) (term1260 A B x'' _7591 _7592 _7594 _7595) (term1725 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353302 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1714 A B x'' _7591 _7592 _7594 _7595) = (term1724 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353265 A B x'' _7592 _7594 _7595 _7591) (@lem353270 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353303 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1713 A B x'' _7591 _7592 _7594 _7595) = (term1724 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353194 A B x'' _7591 _7592 _7594 _7595) (@lem353302 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353304 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) : (term1634 A B f' g' _7591 _7592 _7593) = (term1634 A B f' g' _7591 _7592 _7593).
Proof. exact (eq_refl (term1634 A B f' g' _7591 _7592 _7593)). Qed.
Lemma lem353305 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1712 A B f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1726 A B f' g' _7593 x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353304 A B f' g' _7591 _7592 _7593) (@lem353303 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353316 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1711 A B f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1726 A B f' g' _7593 x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353177 A B f' g' _7593 x'' _7591 _7592 _7594 _7595) (@lem353305 A B f' g' _7593 x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353317 {A B : Type'} (_7593 : A) (x' : type410 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1210 A B _7593 x' _7591 _7592) = (term1210 A B _7593 x' _7591 _7592).
Proof. exact (eq_refl (term1210 A B _7593 x' _7591 _7592)). Qed.
Lemma lem353318 {A B : Type'} (x' : type410 A B) (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1709 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1727 A B x' f' g' _7593 x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353317 A B _7593 x' _7591 _7592) (@lem353316 A B f' g' _7593 x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353322 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353323 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1727 A B x' f' g' _7593 x'' _7592 _7594 _7595 _7591) = (term1728 A B f' g' _7593 x' x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353322 ((term1180 A B f' _7591 _7592 _7593) = (term1180 A B g' _7591 _7592 _7593)) (term1208 A B _7593 x' _7591 _7592) (term1724 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353339 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353340 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1729 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1730 A B _7593 x' x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353339 (_7594 = _7595) (term1208 A B _7593 x' _7591 _7592) (term1731 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353356 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353357 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1732 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1733 A B _7593 x' x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353356 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1208 A B _7593 x' _7591 _7592) (term1725 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353373 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353374 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1734 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1735 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (@lem353373 (term1249 A B x'' _7591 _7592 _7594 _7595) (term1208 A B _7593 x' _7591 _7592) (term1229 A _7591)). Qed.
Lemma lem353392 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1262 A B x'' _7591 _7592 _7594 _7595) = (term1262 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1262 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353393 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1733 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1736 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (MK_COMB (@lem353392 A B x'' _7591 _7592 _7594 _7595) (@lem353374 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353404 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1732 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1736 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (TRANS (@lem353357 A B _7593 x' x'' _7592 _7594 _7595 _7591) (@lem353393 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353405 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) : (term1737 A B _7594 _7595) = (term1737 A B _7594 _7595).
Proof. exact (eq_refl (term1737 A B _7594 _7595)). Qed.
Lemma lem353406 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1730 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1738 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (MK_COMB (@lem353405 A B _7594 _7595) (@lem353404 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353417 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1729 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1738 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (TRANS (@lem353340 A B _7593 x' x'' _7592 _7594 _7595 _7591) (@lem353406 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353418 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) : (term1634 A B f' g' _7591 _7592 _7593) = (term1634 A B f' g' _7591 _7592 _7593).
Proof. exact (eq_refl (term1634 A B f' g' _7591 _7592 _7593)). Qed.
Lemma lem353419 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1728 A B f' g' _7593 x' x'' _7592 _7594 _7595 _7591) = (term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (MK_COMB (@lem353418 A B f' g' _7591 _7592 _7593) (@lem353417 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353430 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1727 A B x' f' g' _7593 x'' _7592 _7594 _7595 _7591) = (term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (TRANS (@lem353323 A B f' g' _7593 x' x'' _7592 _7594 _7595 _7591) (@lem353419 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353431 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1709 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (TRANS (@lem353318 A B x' f' g' _7593 x'' _7592 _7594 _7595 _7591) (@lem353430 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353432 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1610 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (TRANS (@lem353162 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) (@lem353431 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem353434 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1740 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1741 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (MK_COMB (@lem353433) (@lem353432 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353450 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353451 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1742 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1743 A B _7593 x' x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353450 (term1208 A B _7593 x' _7591 _7592) (term1229 A _7591) (term1606 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353465 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353466 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1713 A B x'' _7591 _7592 _7594 _7595) = (term1714 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353465 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591) (term1715 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353482 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353483 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7591 : type1402 A) (_7594 : A -> B) (_7595 : A -> B) : (term1716 A B x'' _7591 _7592 _7594 _7595) = (term1717 A B x'' _7592 _7591 _7594 _7595).
Proof. exact (@lem353482 (term1249 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591) (_7594 = _7595)). Qed.
Lemma lem353499 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem353500 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1718 A B _7591 _7594 _7595) = (term1719 A B _7594 _7595 _7591).
Proof. exact (@lem353499 (_7594 = _7595) (term1229 A _7591)). Qed.
Lemma lem353508 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1720 A B x'' _7591 _7592 _7594 _7595) = (term1720 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1720 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353509 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1717 A B x'' _7592 _7591 _7594 _7595) = (term1721 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353508 A B x'' _7591 _7592 _7594 _7595) (@lem353500 A B _7594 _7595 _7591)). Qed.
Lemma lem353513 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353514 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1721 A B x'' _7592 _7594 _7595 _7591) = (term1722 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353513 (_7594 = _7595) (term1249 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591)). Qed.
Lemma lem353534 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1717 A B x'' _7592 _7591 _7594 _7595) = (term1722 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353509 A B x'' _7592 _7594 _7595 _7591) (@lem353514 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353535 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1716 A B x'' _7591 _7592 _7594 _7595) = (term1722 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353483 A B x'' _7592 _7591 _7594 _7595) (@lem353534 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353536 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1262 A B x'' _7591 _7592 _7594 _7595) = (term1262 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1262 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353537 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1714 A B x'' _7591 _7592 _7594 _7595) = (term1723 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353536 A B x'' _7591 _7592 _7594 _7595) (@lem353535 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353541 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353542 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1723 A B x'' _7592 _7594 _7595 _7591) = (term1724 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353541 (_7594 = _7595) (term1260 A B x'' _7591 _7592 _7594 _7595) (term1725 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353574 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1714 A B x'' _7591 _7592 _7594 _7595) = (term1724 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353537 A B x'' _7592 _7594 _7595 _7591) (@lem353542 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353575 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1713 A B x'' _7591 _7592 _7594 _7595) = (term1724 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353466 A B x'' _7591 _7592 _7594 _7595) (@lem353574 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353576 {A B : Type'} (_7593 : A) (x' : type410 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1210 A B _7593 x' _7591 _7592) = (term1210 A B _7593 x' _7591 _7592).
Proof. exact (eq_refl (term1210 A B _7593 x' _7591 _7592)). Qed.
Lemma lem353577 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1743 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1729 A B _7593 x' x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353576 A B _7593 x' _7591 _7592) (@lem353575 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353581 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353582 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1729 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1730 A B _7593 x' x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353581 (_7594 = _7595) (term1208 A B _7593 x' _7591 _7592) (term1731 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353598 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353599 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1732 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1733 A B _7593 x' x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353598 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1208 A B _7593 x' _7591 _7592) (term1725 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353615 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353616 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1734 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1735 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (@lem353615 (term1249 A B x'' _7591 _7592 _7594 _7595) (term1208 A B _7593 x' _7591 _7592) (term1229 A _7591)). Qed.
Lemma lem353634 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1262 A B x'' _7591 _7592 _7594 _7595) = (term1262 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1262 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353635 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1733 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1736 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (MK_COMB (@lem353634 A B x'' _7591 _7592 _7594 _7595) (@lem353616 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353646 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1732 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1736 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (TRANS (@lem353599 A B _7593 x' x'' _7592 _7594 _7595 _7591) (@lem353635 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353647 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) : (term1737 A B _7594 _7595) = (term1737 A B _7594 _7595).
Proof. exact (eq_refl (term1737 A B _7594 _7595)). Qed.
Lemma lem353648 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1730 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1738 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (MK_COMB (@lem353647 A B _7594 _7595) (@lem353646 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353659 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1729 A B _7593 x' x'' _7592 _7594 _7595 _7591) = (term1738 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (TRANS (@lem353582 A B _7593 x' x'' _7592 _7594 _7595 _7591) (@lem353648 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353660 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1743 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1738 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (TRANS (@lem353577 A B _7593 x' x'' _7592 _7594 _7595 _7591) (@lem353659 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353661 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1742 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1738 A B x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (TRANS (@lem353451 A B _7593 x' x'' _7591 _7592 _7594 _7595) (@lem353660 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353662 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) : (term1634 A B f' g' _7591 _7592 _7593) = (term1634 A B f' g' _7591 _7592 _7593).
Proof. exact (eq_refl (term1634 A B f' g' _7591 _7592 _7593)). Qed.
Lemma lem353663 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1744 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595) = (term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591).
Proof. exact (MK_COMB (@lem353662 A B f' g' _7591 _7592 _7593) (@lem353661 A B x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353674 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : ((term1610 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1744 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595)) = ((term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591) = (term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591)).
Proof. exact (MK_COMB (@lem353434 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591) (@lem353663 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353676 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem353677 (x : Prop) : (x = x) = True.
Proof. exact (@lem353676 Prop x). Qed.
Lemma lem353678 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (_7593 : A) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : ((term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591) = (term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591)) = True.
Proof. exact (@lem353677 (term1739 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353679 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : ((term1610 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1744 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595)) = True.
Proof. exact (TRANS (@lem353674 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591) (@lem353678 A B f' g' x'' _7594 _7595 _7593 x' _7592 _7591)). Qed.
Lemma lem353680 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : True = ((term1610 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1744 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595)).
Proof. exact (SYM (@lem353679 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353681 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1610 A B x' f' g' _7593 x'' _7591 _7592 _7594 _7595) = (term1744 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595).
Proof. exact (EQ_MP (@lem353680 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595) (@lem0)). Qed.
Lemma lem353682 {A B : Type'} (_7593 : A) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1744 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595.
Proof. exact (EQ_MP (@lem353681 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595) (@lem351958 A B _7593 _7591 _7592 _7594 _7595 f' g' x' x'' h1)). Qed.
Lemma lem353684 (b : Prop) (a : Prop) : (a \/ b) = (term1618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem353685 {A B : Type'} (x' : type410 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) : (term1744 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595) = (term1745 A B x' x'' _7594 _7595 f' g' _7591 _7592 _7593).
Proof. exact (@lem353684 (term1742 A B _7593 x' x'' _7591 _7592 _7594 _7595) ((term1180 A B f' _7591 _7592 _7593) = (term1180 A B g' _7591 _7592 _7593))). Qed.
Lemma lem353687 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem353688 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1746 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1747 A B _7593 x' x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353687 (term1229 A _7591) (term1748 A B _7593 x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353690 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem353691 {A : Type'} (_7591 : type1402 A) : (term1653 A _7591) = (@I ((A -> A -> Prop) -> Prop) (@WF A) _7591).
Proof. exact (@lem353690 (@I ((A -> A -> Prop) -> Prop) (@WF A) _7591)). Qed.
Lemma lem353692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem353693 {A : Type'} (_7591 : type1402 A) : (term1654 A _7591) = (term1349 A _7591).
Proof. exact (MK_COMB (@lem353692) (@lem353691 A _7591)). Qed.
Lemma lem353695 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem353696 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1749 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1750 A B _7593 x' x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353695 (term1208 A B _7593 x' _7591 _7592) (term1606 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353698 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem353699 {A B : Type'} (_7593 : A) (x' : type410 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1657 A B _7593 x' _7591 _7592) = (term1206 A B _7593 x' _7591 _7592).
Proof. exact (@lem353698 (term1206 A B _7593 x' _7591 _7592)). Qed.
Lemma lem353700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem353701 {A B : Type'} (_7593 : A) (x' : type410 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1658 A B _7593 x' _7591 _7592) = (term1659 A B _7593 x' _7591 _7592).
Proof. exact (MK_COMB (@lem353700) (@lem353699 A B _7593 x' _7591 _7592)). Qed.
Lemma lem353703 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem353704 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1751 A B x'' _7591 _7592 _7594 _7595) = (term1752 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353703 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1715 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353706 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem353707 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1753 A B x'' _7591 _7592 _7594 _7595) = ((term1252 A B x'' _7591 _7592 _7594 _7595) = (term1256 A B x'' _7591 _7592 _7594 _7595)).
Proof. exact (@lem353706 ((term1252 A B x'' _7591 _7592 _7594 _7595) = (term1256 A B x'' _7591 _7592 _7594 _7595))). Qed.
Lemma lem353708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem353709 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1754 A B x'' _7591 _7592 _7594 _7595) = (term1755 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem353708) (@lem353707 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353711 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem353712 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1756 A B x'' _7591 _7592 _7594 _7595) = (term1757 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353711 (term1249 A B x'' _7591 _7592 _7594 _7595) (_7594 = _7595)). Qed.
Lemma lem353714 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem353715 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1758 A B x'' _7591 _7592 _7594 _7595) = ((term1241 A B x'' _7591 _7592 _7594 _7595) = (term1245 A B x'' _7591 _7592 _7594 _7595)).
Proof. exact (@lem353714 ((term1241 A B x'' _7591 _7592 _7594 _7595) = (term1245 A B x'' _7591 _7592 _7594 _7595))). Qed.
Lemma lem353716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem353717 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1759 A B x'' _7591 _7592 _7594 _7595) = (term1760 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem353716) (@lem353715 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353718 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) : (term96 A B _7594 _7595) = (term96 A B _7594 _7595).
Proof. exact (eq_refl (term96 A B _7594 _7595)). Qed.
Lemma lem353719 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1757 A B x'' _7591 _7592 _7594 _7595) = (term1761 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem353717 A B x'' _7591 _7592 _7594 _7595) (@lem353718 A B _7594 _7595)). Qed.
Lemma lem353720 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1756 A B x'' _7591 _7592 _7594 _7595) = (term1761 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (TRANS (@lem353712 A B x'' _7591 _7592 _7594 _7595) (@lem353719 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353721 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1752 A B x'' _7591 _7592 _7594 _7595) = (term1762 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem353709 A B x'' _7591 _7592 _7594 _7595) (@lem353720 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353722 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1751 A B x'' _7591 _7592 _7594 _7595) = (term1762 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (TRANS (@lem353704 A B x'' _7591 _7592 _7594 _7595) (@lem353721 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353723 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1750 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1763 A B _7593 x' x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem353701 A B _7593 x' _7591 _7592) (@lem353722 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353724 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1749 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1763 A B _7593 x' x'' _7591 _7592 _7594 _7595).
Proof. exact (TRANS (@lem353696 A B _7593 x' x'' _7591 _7592 _7594 _7595) (@lem353723 A B _7593 x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353725 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1747 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1764 A B _7593 x' x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem353693 A _7591) (@lem353724 A B _7593 x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353726 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1746 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1764 A B _7593 x' x'' _7591 _7592 _7594 _7595).
Proof. exact (TRANS (@lem353688 A B _7593 x' x'' _7591 _7592 _7594 _7595) (@lem353725 A B _7593 x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353727 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem353728 {A B : Type'} (_7593 : A) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1765 A B _7593 x' x'' _7591 _7592 _7594 _7595) = (term1766 A B _7593 x' x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem353727) (@lem353726 A B _7593 x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353729 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) : ((term1180 A B f' _7591 _7592 _7593) = (term1180 A B g' _7591 _7592 _7593)) = ((term1180 A B f' _7591 _7592 _7593) = (term1180 A B g' _7591 _7592 _7593)).
Proof. exact (eq_refl ((term1180 A B f' _7591 _7592 _7593) = (term1180 A B g' _7591 _7592 _7593))). Qed.
Lemma lem353730 {A B : Type'} (x' : type410 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) : (term1745 A B x' x'' _7594 _7595 f' g' _7591 _7592 _7593) = (term1767 A B x' x'' _7594 _7595 f' g' _7591 _7592 _7593).
Proof. exact (MK_COMB (@lem353728 A B _7593 x' x'' _7591 _7592 _7594 _7595) (@lem353729 A B f' g' _7591 _7592 _7593)). Qed.
Lemma lem353731 {A B : Type'} (x' : type410 A B) (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) : (term1744 A B f' g' _7593 x' x'' _7591 _7592 _7594 _7595) = (term1767 A B x' x'' _7594 _7595 f' g' _7591 _7592 _7593).
Proof. exact (TRANS (@lem353685 A B x' x'' _7594 _7595 f' g' _7591 _7592 _7593) (@lem353730 A B x' x'' _7594 _7595 f' g' _7591 _7592 _7593)). Qed.
Lemma lem353733 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term96 A B f''' f'') (h2 : term1293 A B H f''' f'') : term1761 A B x'' lt2 H f''' f''.
Proof. exact (conj (@lem353147 A B x'' lt2 H f''' f'' h2) (@lem353155 A B f''' f'' h1)). Qed.
Lemma lem353734 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term96 A B f''' f'') (h2 : term1293 A B H f''' f'') : term1762 A B x'' lt2 H f''' f''.
Proof. exact (conj (@lem353138 A B x'' lt2 H f''' f'' h2) (@lem353733 A B x'' lt2 H f''' f'' h1 h2)). Qed.
Lemma lem353735 {A B : Type'} (x'' : type408 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f' g' x' lt2 H) (h2 : term96 A B f''' f'') (h3 : term1293 A B H f''' f'') (h4 : term461 A B lt2 z x''' H f''' f'') : term1768 A B z f' g' x' x'' lt2 H f''' f''.
Proof. exact (conj (@lem353129 A B f' g' x' lt2 z x''' H f''' f'' h1 h4) (@lem353734 A B x'' lt2 H f''' f'' h2 h3)). Qed.
Lemma lem353736 {A B : Type'} (x'' : type408 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1202 A B f' g' x' lt2 H) (h2 : term96 A B f''' f'') (h3 : term1293 A B H f''' f'') (h4 : term461 A B lt2 z x''' H f''' f'') : term1769 A B z f' g' x' x'' lt2 H f''' f''.
Proof. exact (conj (@lem353103 A B lt2 z x''' H f''' f'' h4) (@lem353735 A B x'' f' g' x' lt2 z x''' H f''' f'' h1 h2 h3 h4)). Qed.
Lemma lem353738 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1767 A B x' x'' _7594 _7595 f' g' _7591 _7592 _7593.
Proof. exact (EQ_MP (@lem353731 A B x' x'' _7594 _7595 f' g' _7591 _7592 _7593) (@lem353682 A B _7593 _7591 _7592 _7594 _7595 f' g' x' x'' h1)). Qed.
Lemma lem353739 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) (_7592 : type549 A B) (_7593 : A) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1767 A B x' x'' _7594 _7595 f' g' _7591 _7592 _7593.
Proof. exact (@lem353738 A B _7594 _7595 _7591 _7592 _7593 f' g' x' x'' h1). Qed.
Lemma lem353740 {A B : Type'} (f''' : A -> B) (f'' : A -> B) (z : type515 A B) (lt2 : type1402 A) (H : type549 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1770 A B x'' f''' f'' z f' g' x' lt2 H.
Proof. exact (@lem353739 A B f''' f'' lt2 H (term1670 A B z f' g' x' lt2 H) f' g' x' x'' h1). Qed.
Lemma lem353743 {A B : Type'} (x'' : type408 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term1202 A B f' g' x' lt2 H) (h3 : term96 A B f''' f'') (h4 : term1293 A B H f''' f'') (h5 : term461 A B lt2 z x''' H f''' f'') : (term1671 A B z f' g' x' lt2 H) = (term1672 A B z f' g' x' lt2 H).
Proof. exact (@lem353740 A B f''' f'' z lt2 H f' g' x' x'' h1 (@lem353736 A B x'' f' g' x' lt2 z x''' H f''' f'' h2 h3 h4 h5)). Qed.
Lemma lem353744 {A B : Type'} (x'' : type408 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term1202 A B f' g' x' lt2 H) (h3 : term96 A B f''' f'') (h4 : term1293 A B H f''' f'') (h5 : term461 A B lt2 z x''' H f''' f'') : term1673 A B z f' g' x' lt2 H.
Proof. exact (fun h0 : term1674 A B z f' g' x' lt2 H => @lem353743 A B x'' f' g' x' lt2 z x''' H f''' f'' h1 h2 h3 h4 h5). Qed.
Lemma lem353746 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem353747 {A B : Type'} (z : type515 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1673 A B z f' g' x' lt2 H) = ((term1671 A B z f' g' x' lt2 H) = (term1672 A B z f' g' x' lt2 H)).
Proof. exact (@lem353746 ((term1671 A B z f' g' x' lt2 H) = (term1672 A B z f' g' x' lt2 H))). Qed.
Lemma lem353748 {A B : Type'} (x'' : type408 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term1202 A B f' g' x' lt2 H) (h3 : term96 A B f''' f'') (h4 : term1293 A B H f''' f'') (h5 : term461 A B lt2 z x''' H f''' f'') : (term1671 A B z f' g' x' lt2 H) = (term1672 A B z f' g' x' lt2 H).
Proof. exact (EQ_MP (@lem353747 A B z f' g' x' lt2 H) (@lem353744 A B x'' f' g' x' lt2 z x''' H f''' f'' h1 h2 h3 h4 h5)). Qed.
Lemma lem353754 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem353755 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : (term1602 A B z _7596 H _7597 _7598) = (term1675 A B H z _7596 _7597 _7598).
Proof. exact (@lem353754 ((term1286 A B H _7596 _7598) = (term1286 A B H _7597 _7598)) (term1322 A B z _7596 _7597 _7598)). Qed.
Lemma lem353765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem353766 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : (term1676 A B z _7596 H _7597 _7598) = (term1677 A B H z _7596 _7597 _7598).
Proof. exact (MK_COMB (@lem353765) (@lem353755 A B H z _7596 _7597 _7598)). Qed.
Lemma lem353776 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : (term1675 A B H z _7596 _7597 _7598) = (term1675 A B H z _7596 _7597 _7598).
Proof. exact (eq_refl (term1675 A B H z _7596 _7597 _7598)). Qed.
Lemma lem353777 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : ((term1602 A B z _7596 H _7597 _7598) = (term1675 A B H z _7596 _7597 _7598)) = ((term1675 A B H z _7596 _7597 _7598) = (term1675 A B H z _7596 _7597 _7598)).
Proof. exact (MK_COMB (@lem353766 A B H z _7596 _7597 _7598) (@lem353776 A B H z _7596 _7597 _7598)). Qed.
Lemma lem353779 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem353780 (x : Prop) : (x = x) = True.
Proof. exact (@lem353779 Prop x). Qed.
Lemma lem353781 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : ((term1675 A B H z _7596 _7597 _7598) = (term1675 A B H z _7596 _7597 _7598)) = True.
Proof. exact (@lem353780 (term1675 A B H z _7596 _7597 _7598)). Qed.
Lemma lem353782 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : ((term1602 A B z _7596 H _7597 _7598) = (term1675 A B H z _7596 _7597 _7598)) = True.
Proof. exact (TRANS (@lem353777 A B H z _7596 _7597 _7598) (@lem353781 A B H z _7596 _7597 _7598)). Qed.
Lemma lem353783 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : True = ((term1602 A B z _7596 H _7597 _7598) = (term1675 A B H z _7596 _7597 _7598)).
Proof. exact (SYM (@lem353782 A B H z _7596 _7597 _7598)). Qed.
Lemma lem353784 {A B : Type'} (H : type549 A B) (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : (term1602 A B z _7596 H _7597 _7598) = (term1675 A B H z _7596 _7597 _7598).
Proof. exact (EQ_MP (@lem353783 A B H z _7596 _7597 _7598) (@lem0)). Qed.
Lemma lem353785 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1675 A B H z _7596 _7597 _7598.
Proof. exact (EQ_MP (@lem353784 A B H z _7596 _7597 _7598) (@lem351932 A B _7596 _7597 _7598 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem353787 (b : Prop) (a : Prop) : (a \/ b) = (term1618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem353788 {A B : Type'} (z : type515 A B) (_7596 : A -> B) (H : type549 A B) (_7597 : A -> B) (_7598 : A) : (term1675 A B H z _7596 _7597 _7598) = (term1678 A B z _7596 H _7597 _7598).
Proof. exact (@lem353787 (term1322 A B z _7596 _7597 _7598) ((term1286 A B H _7596 _7598) = (term1286 A B H _7597 _7598))). Qed.
Lemma lem353790 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem353791 {A B : Type'} (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : (term1679 A B z _7596 _7597 _7598) = ((term1315 A B z _7596 _7597 _7598) = (term1318 A B z _7596 _7597 _7598)).
Proof. exact (@lem353790 ((term1315 A B z _7596 _7597 _7598) = (term1318 A B z _7596 _7597 _7598))). Qed.
Lemma lem353792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem353793 {A B : Type'} (z : type515 A B) (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) : (term1680 A B z _7596 _7597 _7598) = (term1681 A B z _7596 _7597 _7598).
Proof. exact (MK_COMB (@lem353792) (@lem353791 A B z _7596 _7597 _7598)). Qed.
Lemma lem353794 {A B : Type'} (_7596 : A -> B) (H : type549 A B) (_7597 : A -> B) (_7598 : A) : ((term1286 A B H _7596 _7598) = (term1286 A B H _7597 _7598)) = ((term1286 A B H _7596 _7598) = (term1286 A B H _7597 _7598)).
Proof. exact (eq_refl ((term1286 A B H _7596 _7598) = (term1286 A B H _7597 _7598))). Qed.
Lemma lem353795 {A B : Type'} (z : type515 A B) (_7596 : A -> B) (H : type549 A B) (_7597 : A -> B) (_7598 : A) : (term1678 A B z _7596 H _7597 _7598) = (term1682 A B z _7596 H _7597 _7598).
Proof. exact (MK_COMB (@lem353793 A B z _7596 _7597 _7598) (@lem353794 A B _7596 H _7597 _7598)). Qed.
Lemma lem353796 {A B : Type'} (z : type515 A B) (_7596 : A -> B) (H : type549 A B) (_7597 : A -> B) (_7598 : A) : (term1675 A B H z _7596 _7597 _7598) = (term1682 A B z _7596 H _7597 _7598).
Proof. exact (TRANS (@lem353788 A B z _7596 H _7597 _7598) (@lem353795 A B z _7596 H _7597 _7598)). Qed.
Lemma lem353799 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1682 A B z _7596 H _7597 _7598.
Proof. exact (EQ_MP (@lem353796 A B z _7596 H _7597 _7598) (@lem353785 A B _7596 _7597 _7598 lt2 z x''' H f''' f'' h1)). Qed.
Lemma lem353800 {A B : Type'} (_7596 : A -> B) (_7597 : A -> B) (_7598 : A) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1682 A B z _7596 H _7597 _7598.
Proof. exact (@lem353799 A B _7596 _7597 _7598 lt2 z x''' H f''' f'' h1). Qed.
Lemma lem353801 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term461 A B lt2 z x''' H f''' f'') : term1683 A B z f' g' x' lt2 H.
Proof. exact (@lem353800 A B (term1178 A B f' lt2 H) (term1178 A B g' lt2 H) (term1194 A B x' lt2 H) lt2 z x''' H f''' f'' h1). Qed.
Lemma lem353804 {A B : Type'} (x'' : type408 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term1202 A B f' g' x' lt2 H) (h3 : term96 A B f''' f'') (h4 : term1293 A B H f''' f'') (h5 : term461 A B lt2 z x''' H f''' f'') : (term1198 A B f' x' lt2 H) = (term1198 A B g' x' lt2 H).
Proof. exact (@lem353801 A B f' g' x' lt2 z x''' H f''' f'' h5 (@lem353748 A B x'' f' g' x' lt2 z x''' H f''' f'' h1 h2 h3 h4 h5)). Qed.
Lemma lem353805 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term96 A B f''' f'') (h3 : term1293 A B H f''' f'') (h4 : term461 A B lt2 z x''' H f''' f'') : term1684 A B f' g' x' lt2 H.
Proof. exact (fun h0 : term1202 A B f' g' x' lt2 H => @lem353804 A B x'' f' g' x' lt2 z x''' H f''' f'' h1 h0 h2 h3 h4). Qed.
Lemma lem353807 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem353808 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (H : type549 A B) : (term1684 A B f' g' x' lt2 H) = ((term1198 A B f' x' lt2 H) = (term1198 A B g' x' lt2 H)).
Proof. exact (@lem353807 ((term1198 A B f' x' lt2 H) = (term1198 A B g' x' lt2 H))). Qed.
Lemma lem353809 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term96 A B f''' f'') (h3 : term1293 A B H f''' f'') (h4 : term461 A B lt2 z x''' H f''' f'') : (term1198 A B f' x' lt2 H) = (term1198 A B g' x' lt2 H).
Proof. exact (EQ_MP (@lem353808 A B f' g' x' lt2 H) (@lem353805 A B f' g' x' x'' lt2 z x''' H f''' f'' h1 h2 h3 h4)). Qed.
Lemma lem353811 {A B : Type'} (_7600 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (@I (A -> B) f''' _7600) = (term1286 A B H f''' _7600).
Proof. exact (EQ_MP (@lem351811 A B H f''' _7600) (@lem351810 A B _7600 H f''' f'' h1)). Qed.
Lemma lem353812 {A B : Type'} (_7600 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (@I (A -> B) f''' _7600) = (term1286 A B H f''' _7600).
Proof. exact (@lem353811 A B _7600 H f''' f'' h1). Qed.
Lemma lem353813 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (term1252 A B x'' lt2 H f''' f'') = (term1256 A B x'' lt2 H f''' f'').
Proof. exact (@lem353812 A B (term1238 A B x'' lt2 H f''' f'') H f''' f'' h1). Qed.
Lemma lem353814 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1706 A B x'' lt2 H f''' f''.
Proof. exact (fun h0 : term1260 A B x'' lt2 H f''' f'' => @lem353813 A B x'' lt2 H f''' f'' h1). Qed.
Lemma lem353816 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem353817 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) : (term1706 A B x'' lt2 H f''' f'') = ((term1252 A B x'' lt2 H f''' f'') = (term1256 A B x'' lt2 H f''' f'')).
Proof. exact (@lem353816 ((term1252 A B x'' lt2 H f''' f'') = (term1256 A B x'' lt2 H f''' f''))). Qed.
Lemma lem353818 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (term1252 A B x'' lt2 H f''' f'') = (term1256 A B x'' lt2 H f''' f'').
Proof. exact (EQ_MP (@lem353817 A B x'' lt2 H f''' f'') (@lem353814 A B x'' lt2 H f''' f'' h1)). Qed.
Lemma lem353820 {A B : Type'} (_7599 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (@I (A -> B) f'' _7599) = (term1286 A B H f'' _7599).
Proof. exact (EQ_MP (@lem351808 A B H f'' _7599) (@lem351807 A B _7599 H f''' f'' h1)). Qed.
Lemma lem353821 {A B : Type'} (_7599 : A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (@I (A -> B) f'' _7599) = (term1286 A B H f'' _7599).
Proof. exact (@lem353820 A B _7599 H f''' f'' h1). Qed.
Lemma lem353822 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (term1241 A B x'' lt2 H f''' f'') = (term1245 A B x'' lt2 H f''' f'').
Proof. exact (@lem353821 A B (term1238 A B x'' lt2 H f''' f'') H f''' f'' h1). Qed.
Lemma lem353823 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1707 A B x'' lt2 H f''' f''.
Proof. exact (fun h0 : term1249 A B x'' lt2 H f''' f'' => @lem353822 A B x'' lt2 H f''' f'' h1). Qed.
Lemma lem353825 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem353826 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) : (term1707 A B x'' lt2 H f''' f'') = ((term1241 A B x'' lt2 H f''' f'') = (term1245 A B x'' lt2 H f''' f'')).
Proof. exact (@lem353825 ((term1241 A B x'' lt2 H f''' f'') = (term1245 A B x'' lt2 H f''' f''))). Qed.
Lemma lem353827 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : (term1241 A B x'' lt2 H f''' f'') = (term1245 A B x'' lt2 H f''' f'').
Proof. exact (EQ_MP (@lem353826 A B x'' lt2 H f''' f'') (@lem353823 A B x'' lt2 H f''' f'' h1)). Qed.
Lemma lem353833 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353834 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1613 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1771 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353833 (term1202 A B f' g' x' _7591 _7592) (term1229 A _7591) (term1606 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353850 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353851 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1713 A B x'' _7591 _7592 _7594 _7595) = (term1714 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem353850 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591) (term1715 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353867 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353868 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7591 : type1402 A) (_7594 : A -> B) (_7595 : A -> B) : (term1716 A B x'' _7591 _7592 _7594 _7595) = (term1717 A B x'' _7592 _7591 _7594 _7595).
Proof. exact (@lem353867 (term1249 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591) (_7594 = _7595)). Qed.
Lemma lem353884 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem353885 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1718 A B _7591 _7594 _7595) = (term1719 A B _7594 _7595 _7591).
Proof. exact (@lem353884 (_7594 = _7595) (term1229 A _7591)). Qed.
Lemma lem353893 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1720 A B x'' _7591 _7592 _7594 _7595) = (term1720 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1720 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353894 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1717 A B x'' _7592 _7591 _7594 _7595) = (term1721 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353893 A B x'' _7591 _7592 _7594 _7595) (@lem353885 A B _7594 _7595 _7591)). Qed.
Lemma lem353898 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353899 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1721 A B x'' _7592 _7594 _7595 _7591) = (term1722 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353898 (_7594 = _7595) (term1249 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591)). Qed.
Lemma lem353919 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1717 A B x'' _7592 _7591 _7594 _7595) = (term1722 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353894 A B x'' _7592 _7594 _7595 _7591) (@lem353899 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353920 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1716 A B x'' _7591 _7592 _7594 _7595) = (term1722 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353868 A B x'' _7592 _7591 _7594 _7595) (@lem353919 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353921 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1262 A B x'' _7591 _7592 _7594 _7595) = (term1262 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1262 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem353922 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1714 A B x'' _7591 _7592 _7594 _7595) = (term1723 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353921 A B x'' _7591 _7592 _7594 _7595) (@lem353920 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353926 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353927 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1723 A B x'' _7592 _7594 _7595 _7591) = (term1724 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353926 (_7594 = _7595) (term1260 A B x'' _7591 _7592 _7594 _7595) (term1725 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353959 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1714 A B x'' _7591 _7592 _7594 _7595) = (term1724 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353922 A B x'' _7592 _7594 _7595 _7591) (@lem353927 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353960 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1713 A B x'' _7591 _7592 _7594 _7595) = (term1724 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem353851 A B x'' _7591 _7592 _7594 _7595) (@lem353959 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353961 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1611 A B f' g' x' _7591 _7592) = (term1611 A B f' g' x' _7591 _7592).
Proof. exact (eq_refl (term1611 A B f' g' x' _7591 _7592)). Qed.
Lemma lem353962 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1771 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1772 A B f' g' x' x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem353961 A B f' g' x' _7591 _7592) (@lem353960 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353966 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353967 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1772 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1773 A B f' g' x' x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353966 (_7594 = _7595) (term1202 A B f' g' x' _7591 _7592) (term1731 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem353983 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem353984 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1774 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1775 A B f' g' x' x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem353983 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1202 A B f' g' x' _7591 _7592) (term1725 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem354000 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem354001 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1776 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1777 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (@lem354000 (term1249 A B x'' _7591 _7592 _7594 _7595) (term1202 A B f' g' x' _7591 _7592) (term1229 A _7591)). Qed.
Lemma lem354021 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1262 A B x'' _7591 _7592 _7594 _7595) = (term1262 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1262 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354022 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1775 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1778 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (MK_COMB (@lem354021 A B x'' _7591 _7592 _7594 _7595) (@lem354001 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354033 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1774 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1778 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (TRANS (@lem353984 A B f' g' x' x'' _7592 _7594 _7595 _7591) (@lem354022 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354034 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) : (term1737 A B _7594 _7595) = (term1737 A B _7594 _7595).
Proof. exact (eq_refl (term1737 A B _7594 _7595)). Qed.
Lemma lem354035 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1773 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (MK_COMB (@lem354034 A B _7594 _7595) (@lem354033 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354046 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1772 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (TRANS (@lem353967 A B f' g' x' x'' _7592 _7594 _7595 _7591) (@lem354035 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354047 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1771 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (TRANS (@lem353962 A B f' g' x' x'' _7592 _7594 _7595 _7591) (@lem354046 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354048 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1613 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (TRANS (@lem353834 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem354047 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem354050 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1780 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1781 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (MK_COMB (@lem354049) (@lem354048 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354066 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem354067 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1782 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1783 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem354066 (term1202 A B f' g' x' _7591 _7592) (term1229 A _7591) (term1264 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354083 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem354084 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1784 A B x'' _7591 _7592 _7594 _7595) = (term1785 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem354083 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591) (term1249 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354100 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem354101 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1786 A B x'' _7591 _7592 _7594 _7595) = (term1725 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem354100 (term1249 A B x'' _7591 _7592 _7594 _7595) (term1229 A _7591)). Qed.
Lemma lem354109 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1262 A B x'' _7591 _7592 _7594 _7595) = (term1262 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1262 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354110 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1785 A B x'' _7591 _7592 _7594 _7595) = (term1731 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem354109 A B x'' _7591 _7592 _7594 _7595) (@lem354101 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem354121 {A B : Type'} (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1784 A B x'' _7591 _7592 _7594 _7595) = (term1731 A B x'' _7592 _7594 _7595 _7591).
Proof. exact (TRANS (@lem354084 A B x'' _7591 _7592 _7594 _7595) (@lem354110 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem354122 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1611 A B f' g' x' _7591 _7592) = (term1611 A B f' g' x' _7591 _7592).
Proof. exact (eq_refl (term1611 A B f' g' x' _7591 _7592)). Qed.
Lemma lem354123 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1783 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1774 A B f' g' x' x'' _7592 _7594 _7595 _7591).
Proof. exact (MK_COMB (@lem354122 A B f' g' x' _7591 _7592) (@lem354121 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem354127 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem354128 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (_7591 : type1402 A) : (term1774 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1775 A B f' g' x' x'' _7592 _7594 _7595 _7591).
Proof. exact (@lem354127 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1202 A B f' g' x' _7591 _7592) (term1725 A B x'' _7592 _7594 _7595 _7591)). Qed.
Lemma lem354144 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem354145 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1776 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1777 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (@lem354144 (term1249 A B x'' _7591 _7592 _7594 _7595) (term1202 A B f' g' x' _7591 _7592) (term1229 A _7591)). Qed.
Lemma lem354165 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1262 A B x'' _7591 _7592 _7594 _7595) = (term1262 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (eq_refl (term1262 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354166 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1775 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1778 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (MK_COMB (@lem354165 A B x'' _7591 _7592 _7594 _7595) (@lem354145 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354177 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1774 A B f' g' x' x'' _7592 _7594 _7595 _7591) = (term1778 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (TRANS (@lem354128 A B f' g' x' x'' _7592 _7594 _7595 _7591) (@lem354166 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354178 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1783 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1778 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (TRANS (@lem354123 A B f' g' x' x'' _7592 _7594 _7595 _7591) (@lem354177 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354179 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1782 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1778 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (TRANS (@lem354067 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem354178 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354180 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) : (term1737 A B _7594 _7595) = (term1737 A B _7594 _7595).
Proof. exact (eq_refl (term1737 A B _7594 _7595)). Qed.
Lemma lem354181 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : (term1787 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591).
Proof. exact (MK_COMB (@lem354180 A B _7594 _7595) (@lem354179 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354192 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : ((term1613 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1787 A B f' g' x' x'' _7591 _7592 _7594 _7595)) = ((term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591) = (term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591)).
Proof. exact (MK_COMB (@lem354050 A B x'' _7594 _7595 f' g' x' _7592 _7591) (@lem354181 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354194 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem354195 (x : Prop) : (x = x) = True.
Proof. exact (@lem354194 Prop x). Qed.
Lemma lem354196 {A B : Type'} (x'' : type408 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7592 : type549 A B) (_7591 : type1402 A) : ((term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591) = (term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591)) = True.
Proof. exact (@lem354195 (term1779 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354197 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : ((term1613 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1787 A B f' g' x' x'' _7591 _7592 _7594 _7595)) = True.
Proof. exact (TRANS (@lem354192 A B x'' _7594 _7595 f' g' x' _7592 _7591) (@lem354196 A B x'' _7594 _7595 f' g' x' _7592 _7591)). Qed.
Lemma lem354198 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : True = ((term1613 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1787 A B f' g' x' x'' _7591 _7592 _7594 _7595)).
Proof. exact (SYM (@lem354197 A B f' g' x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354199 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1613 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1787 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (EQ_MP (@lem354198 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem0)). Qed.
Lemma lem354200 {A B : Type'} (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1787 A B f' g' x' x'' _7591 _7592 _7594 _7595.
Proof. exact (EQ_MP (@lem354199 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem351978 A B _7591 _7592 _7594 _7595 f' g' x' x'' h1)). Qed.
Lemma lem354202 (b : Prop) (a : Prop) : (a \/ b) = (term1618 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem354203 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1787 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1788 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem354202 (term1782 A B f' g' x' x'' _7591 _7592 _7594 _7595) (_7594 = _7595)). Qed.
Lemma lem354205 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem354206 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1789 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1790 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem354205 (term1229 A _7591) (term1791 A B f' g' x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354208 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem354209 {A : Type'} (_7591 : type1402 A) : (term1653 A _7591) = (@I ((A -> A -> Prop) -> Prop) (@WF A) _7591).
Proof. exact (@lem354208 (@I ((A -> A -> Prop) -> Prop) (@WF A) _7591)). Qed.
Lemma lem354210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem354211 {A : Type'} (_7591 : type1402 A) : (term1654 A _7591) = (term1349 A _7591).
Proof. exact (MK_COMB (@lem354210) (@lem354209 A _7591)). Qed.
Lemma lem354213 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem354214 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1792 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1793 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem354213 (term1202 A B f' g' x' _7591 _7592) (term1264 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354216 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem354217 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1697 A B f' g' x' _7591 _7592) = ((term1198 A B f' x' _7591 _7592) = (term1198 A B g' x' _7591 _7592)).
Proof. exact (@lem354216 ((term1198 A B f' x' _7591 _7592) = (term1198 A B g' x' _7591 _7592))). Qed.
Lemma lem354218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem354219 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (_7591 : type1402 A) (_7592 : type549 A B) : (term1794 A B f' g' x' _7591 _7592) = (term1795 A B f' g' x' _7591 _7592).
Proof. exact (MK_COMB (@lem354218) (@lem354217 A B f' g' x' _7591 _7592)). Qed.
Lemma lem354221 (a : Prop) (b : Prop) : (term1647 a b) = (term1648 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem354222 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1796 A B x'' _7591 _7592 _7594 _7595) = (term1797 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (@lem354221 (term1260 A B x'' _7591 _7592 _7594 _7595) (term1249 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354224 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem354225 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1753 A B x'' _7591 _7592 _7594 _7595) = ((term1252 A B x'' _7591 _7592 _7594 _7595) = (term1256 A B x'' _7591 _7592 _7594 _7595)).
Proof. exact (@lem354224 ((term1252 A B x'' _7591 _7592 _7594 _7595) = (term1256 A B x'' _7591 _7592 _7594 _7595))). Qed.
Lemma lem354226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem354227 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1754 A B x'' _7591 _7592 _7594 _7595) = (term1755 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem354226) (@lem354225 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354229 (a : Prop) : (term1652 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem354230 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1758 A B x'' _7591 _7592 _7594 _7595) = ((term1241 A B x'' _7591 _7592 _7594 _7595) = (term1245 A B x'' _7591 _7592 _7594 _7595)).
Proof. exact (@lem354229 ((term1241 A B x'' _7591 _7592 _7594 _7595) = (term1245 A B x'' _7591 _7592 _7594 _7595))). Qed.
Lemma lem354231 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1797 A B x'' _7591 _7592 _7594 _7595) = (term1798 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem354227 A B x'' _7591 _7592 _7594 _7595) (@lem354230 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354232 {A B : Type'} (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1796 A B x'' _7591 _7592 _7594 _7595) = (term1798 A B x'' _7591 _7592 _7594 _7595).
Proof. exact (TRANS (@lem354222 A B x'' _7591 _7592 _7594 _7595) (@lem354231 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354233 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1793 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1799 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem354219 A B f' g' x' _7591 _7592) (@lem354232 A B x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354234 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1792 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1799 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (TRANS (@lem354214 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem354233 A B f' g' x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354235 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1790 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1800 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem354211 A _7591) (@lem354234 A B f' g' x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354236 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1789 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1800 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (TRANS (@lem354206 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem354235 A B f' g' x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354237 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem354238 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1801 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1802 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem354237) (@lem354236 A B f' g' x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354239 {A B : Type'} (_7594 : A -> B) (_7595 : A -> B) : (_7594 = _7595) = (_7594 = _7595).
Proof. exact (eq_refl (_7594 = _7595)). Qed.
Lemma lem354240 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1788 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1803 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (MK_COMB (@lem354238 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem354239 A B _7594 _7595)). Qed.
Lemma lem354241 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) : (term1787 A B f' g' x' x'' _7591 _7592 _7594 _7595) = (term1803 A B f' g' x' x'' _7591 _7592 _7594 _7595).
Proof. exact (TRANS (@lem354203 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem354240 A B f' g' x' x'' _7591 _7592 _7594 _7595)). Qed.
Lemma lem354243 {A B : Type'} (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1798 A B x'' lt2 H f''' f''.
Proof. exact (conj (@lem353818 A B x'' lt2 H f''' f'' h1) (@lem353827 A B x'' lt2 H f''' f'' h1)). Qed.
Lemma lem354244 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term96 A B f''' f'') (h3 : term1293 A B H f''' f'') (h4 : term461 A B lt2 z x''' H f''' f'') : term1799 A B f' g' x' x'' lt2 H f''' f''.
Proof. exact (conj (@lem353809 A B f' g' x' x'' lt2 z x''' H f''' f'' h1 h2 h3 h4) (@lem354243 A B x'' lt2 H f''' f'' h3)). Qed.
Lemma lem354245 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term96 A B f''' f'') (h3 : term1293 A B H f''' f'') (h4 : term461 A B lt2 z x''' H f''' f'') : term1800 A B f' g' x' x'' lt2 H f''' f''.
Proof. exact (conj (@lem353096 A B lt2 z x''' H f''' f'' h4) (@lem354244 A B f' g' x' x'' lt2 z x''' H f''' f'' h1 h2 h3 h4)). Qed.
Lemma lem354247 {A B : Type'} (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1803 A B f' g' x' x'' _7591 _7592 _7594 _7595.
Proof. exact (EQ_MP (@lem354241 A B f' g' x' x'' _7591 _7592 _7594 _7595) (@lem354200 A B _7591 _7592 _7594 _7595 f' g' x' x'' h1)). Qed.
Lemma lem354248 {A B : Type'} (_7591 : type1402 A) (_7592 : type549 A B) (_7594 : A -> B) (_7595 : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1803 A B f' g' x' x'' _7591 _7592 _7594 _7595.
Proof. exact (@lem354247 A B _7591 _7592 _7594 _7595 f' g' x' x'' h1). Qed.
Lemma lem354249 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (h1 : term938 A B f' g' x' x'') : term1803 A B f' g' x' x'' lt2 H f''' f''.
Proof. exact (@lem354248 A B lt2 H f''' f'' f' g' x' x'' h1). Qed.
Lemma lem354252 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term96 A B f''' f'') (h3 : term1293 A B H f''' f'') (h4 : term461 A B lt2 z x''' H f''' f'') : f''' = f''.
Proof. exact (@lem354249 A B lt2 H f''' f'' f' g' x' x'' h1 (@lem354245 A B f' g' x' x'' lt2 z x''' H f''' f'' h1 h2 h3 h4)). Qed.
Lemma lem354253 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term1293 A B H f''' f'') (h3 : term461 A B lt2 z x''' H f''' f'') : term1804 A B f''' f''.
Proof. exact (fun h0 : term96 A B f''' f'' => @lem354252 A B f' g' x' x'' lt2 z x''' H f''' f'' h1 h0 h2 h3). Qed.
Lemma lem354255 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem354256 {A B : Type'} (f''' : A -> B) (f'' : A -> B) : (term1804 A B f''' f'') = (f''' = f'').
Proof. exact (@lem354255 (f''' = f'')). Qed.
Lemma lem354257 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term1293 A B H f''' f'') (h3 : term461 A B lt2 z x''' H f''' f'') : f''' = f''.
Proof. exact (EQ_MP (@lem354256 A B f''' f'') (@lem354253 A B f' g' x' x'' lt2 z x''' H f''' f'' h1 h2 h3)). Qed.
Lemma lem354260 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem354262 {A B : Type'} (f''' : A -> B) (f'' : A -> B) : (term96 A B f''' f'') = (term1805 A B f''' f'').
Proof. exact (@lem354260 (f''' = f'')). Qed.
Lemma lem354265 {A B : Type'} (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1293 A B H f''' f'') : term1805 A B f''' f''.
Proof. exact (EQ_MP (@lem354262 A B f''' f'') (@lem351920 A B H f''' f'' h1)). Qed.
Lemma lem354268 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term1293 A B H f''' f'') (h3 : term461 A B lt2 z x''' H f''' f'') : False.
Proof. exact (@lem354265 A B H f''' f'' h2 (@lem354257 A B f' g' x' x'' lt2 z x''' H f''' f'' h1 h2 h3)). Qed.
Lemma lem354269 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term1293 A B H f''' f'') (h3 : term461 A B lt2 z x''' H f''' f'') : term1705.
Proof. exact (fun h0 : ~ False => @lem354268 A B f' g' x' x'' lt2 z x''' H f''' f'' h1 h2 h3). Qed.
Lemma lem354271 (p : Prop) : (term1615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem354272 : term1705 = False.
Proof. exact (@lem354271 False). Qed.
Lemma lem354273 {A B : Type'} (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term938 A B f' g' x' x'') (h2 : term1293 A B H f''' f'') (h3 : term461 A B lt2 z x''' H f''' f'') : False.
Proof. exact (EQ_MP (@lem354272) (@lem354269 A B f' g' x' x'' lt2 z x''' H f''' f'' h1 h2 h3)). Qed.
Lemma lem354274 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1305 A B H x''') (h2 : term1170 A B g x f) (h3 : term461 A B lt2 z x''' H f''' f'') : (term1305 A B H x''') = False.
Proof. exact (prop_ext (fun h4 : term1305 A B H x''' => @lem352805 A B g x f lt2 z x''' H f''' f'' h1 h2 h3) (fun h4 : False => @lem351211 A B H x''' h1)). Qed.
Lemma lem354275 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1305 A B H x''') (h2 : term1170 A B g x f) (h3 : term461 A B lt2 z x''' H f''' f'') : False.
Proof. exact (EQ_MP (@lem354274 A B g x f lt2 z x''' H f''' f'' h1 h2 h3) (@lem351211 A B H x''' h1)). Qed.
Lemma lem354276 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f''' : A -> B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term938 A B f' g' x' x'') (h3 : term461 A B lt2 z x''' H f''' f'') : False.
Proof. exact (or_elim (@lem350695 A B lt2 z x''' H f''' f'' h3) (fun h0 : term1305 A B H x''' => @lem354275 A B g x f lt2 z x''' H f''' f'' h0 h1 h3) (fun h0 : term1293 A B H f''' f'' => @lem354273 A B f' g' x' x'' lt2 z x''' H f''' f'' h2 h0 h3)). Qed.
Lemma lem354277 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (f'' : A -> B) (h1 : term1170 A B g x f) (h2 : term938 A B f' g' x' x'') (h3 : term464 A B lt2 z x''' H f'') : False.
Proof. exact (ex_elim (@lem349658 A B lt2 z x''' H f'' h3) (fun f''' : A -> B => fun h0 : term463 A B lt2 z x''' H f'' f''' => @lem354276 A B g x f f' g' x' x'' lt2 z x''' H f''' f'' h1 h2 h0)). Qed.
Lemma lem354278 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (x''' : type569 A B) (H : type549 A B) (h1 : term1170 A B g x f) (h2 : term938 A B f' g' x' x'') (h3 : term466 A B lt2 z x''' H) : False.
Proof. exact (ex_elim (@lem349657 A B lt2 z x''' H h3) (fun f'' : A -> B => fun h0 : term465 A B lt2 z x''' H f'' => @lem354277 A B g x f f' g' x' x'' lt2 z x''' H f'' h1 h2 h0)). Qed.
Lemma lem354279 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (z : type515 A B) (H : type549 A B) (h1 : term1170 A B g x f) (h2 : term938 A B f' g' x' x'') (h3 : term468 A B lt2 z H) : False.
Proof. exact (ex_elim (@lem349656 A B lt2 z H h3) (fun x''' : type569 A B => fun h0 : term467 A B lt2 z H x''' => @lem354278 A B g x f f' g' x' x'' lt2 z x''' H h1 h2 h0)). Qed.
Lemma lem354280 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (H : type549 A B) (h1 : term1170 A B g x f) (h2 : term938 A B f' g' x' x'') (h3 : term470 A B lt2 H) : False.
Proof. exact (ex_elim (@lem349655 A B lt2 H h3) (fun z : type515 A B => fun h0 : term469 A B lt2 H z => @lem354279 A B g x f f' g' x' x'' lt2 z H h1 h2 h0)). Qed.
Lemma lem354281 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (x'' : type408 A B) (lt2 : type1402 A) (h1 : term1170 A B g x f) (h2 : term938 A B f' g' x' x'') (h3 : term12 A B lt2) : False.
Proof. exact (ex_elim (@lem348037 A B lt2 h3) (fun H : type549 A B => fun h0 : term471 A B lt2 H => @lem354280 A B g x f f' g' x' x'' lt2 H h1 h2 h0)). Qed.
Lemma lem354282 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (f' : type409 A B) (g' : type409 A B) (x' : type410 A B) (lt2 : type1402 A) (h1 : term1170 A B g x f) (h2 : term941 A B f' g' x') (h3 : term12 A B lt2) : False.
Proof. exact (ex_elim (@lem349653 A B f' g' x' h2) (fun x'' : type408 A B => fun h0 : term940 A B f' g' x' x'' => @lem354281 A B g x f f' g' x' x'' lt2 h1 h0 h3)). Qed.
Lemma lem354283 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (f' : type409 A B) (g' : type409 A B) (lt2 : type1402 A) (h1 : term1170 A B g x f) (h2 : term943 A B f' g') (h3 : term12 A B lt2) : False.
Proof. exact (ex_elim (@lem349652 A B f' g' h2) (fun x' : type410 A B => fun h0 : term942 A B f' g' x' => @lem354282 A B g x f f' g' x' lt2 h1 h0 h3)). Qed.
Lemma lem354284 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (f' : type409 A B) (lt2 : type1402 A) (h1 : term1170 A B g x f) (h2 : term945 A B f') (h3 : term12 A B lt2) : False.
Proof. exact (ex_elim (@lem349651 A B f' h2) (fun g' : type409 A B => fun h0 : term944 A B f' g' => @lem354283 A B g x f f' g' lt2 h1 h0 h3)). Qed.
Lemma lem354285 {A B : Type'} (g : type409 A B) (x : type410 A B) (f : type409 A B) (lt2 : type1402 A) (h1 : term8 A B) (h2 : term1170 A B g x f) (h3 : term12 A B lt2) : False.
Proof. exact (ex_elim (@lem349007 A B h1) (fun f' : type409 A B => fun h0 : term946 A B f' => @lem354284 A B g x f f' lt2 h2 h0 h3)). Qed.
Lemma lem354286 {A B : Type'} (g : type409 A B) (f : type409 A B) (lt2 : type1402 A) (h1 : term8 A B) (h2 : term1173 A B g f) (h3 : term12 A B lt2) : False.
Proof. exact (ex_elim (@lem349649 A B g f h2) (fun x : type410 A B => fun h0 : term1172 A B g f x => @lem354285 A B g x f lt2 h1 h0 h3)). Qed.
Lemma lem354287 {A B : Type'} (f : type409 A B) (lt2 : type1402 A) (h1 : term8 A B) (h2 : term1175 A B f) (h3 : term12 A B lt2) : False.
Proof. exact (ex_elim (@lem349648 A B f h2) (fun g : type409 A B => fun h0 : term1174 A B f g => @lem354286 A B g f lt2 h1 h0 h3)). Qed.
Lemma lem354288 {A B : Type'} (lt2 : type1402 A) (h1 : term8 A B) (h2 : term7 A B) (h3 : term12 A B lt2) : False.
Proof. exact (ex_elim (@lem349647 A B h2) (fun f : type409 A B => fun h0 : term1176 A B f => @lem354287 A B f lt2 h1 h0 h3)). Qed.
Lemma lem354289 {A B : Type'} (lt2 : type1402 A) (h1 : term8 A B) (h2 : term12 A B lt2) : term17 A B.
Proof. exact (fun h0 : term7 A B => @lem354288 A B lt2 h1 h0 h2). Qed.
Lemma lem354290 {A B : Type'} : (term17 A B) = (term18 A B).
Proof. exact (@lem69 (term7 A B)). Qed.
Lemma lem354291 {A B : Type'} (lt2 : type1402 A) (h1 : term8 A B) (h2 : term12 A B lt2) : term18 A B.
Proof. exact (EQ_MP (@lem354290 A B) (@lem354289 A B lt2 h1 h2)). Qed.
Lemma lem354292 {A B : Type'} (lt2 : type1402 A) (h1 : term12 A B lt2) : term21 A B.
Proof. exact (fun h0 : term8 A B => @lem354291 A B lt2 h0 h1). Qed.
Lemma lem354293 {A B : Type'} (lt2 : type1402 A) : term23 A B lt2.
Proof. exact (fun h0 : term12 A B lt2 => @lem354292 A B lt2 h0). Qed.
Lemma lem354298 {A B : Type'} : term27 A B.
Proof. exact (fun lt2 : type1402 A => @lem354293 A B lt2). Qed.
Lemma lem354299 {A B : Type'} : term26 A B.
Proof. exact (EQ_MP (@lem347105 A B) (@lem354298 A B)). Qed.
Lemma lem354300 {A B : Type'} (lt2 : type1402 A) : term1806 A B lt2.
Proof. exact (@lem354299 A B lt2). Qed.
Lemma lem354301 {A B : Type'} (lt2 : type1402 A) : (term1806 A B lt2) = (term13 A B lt2).
Proof. exact (eq_refl (term1806 A B lt2)). Qed.
Lemma lem354302 {A B : Type'} (lt2 : type1402 A) : term13 A B lt2.
Proof. exact (EQ_MP (@lem354301 A B lt2) (@lem354300 A B lt2)). Qed.
Lemma lem354304 {A B : Type'} (lt2 : type1402 A) : term13 A B lt2.
Proof. exact (@lem346618 A B lt2 (@lem354302 A B lt2)). Qed.
Lemma lem354305 {A B : Type'} (lt2 : type1402 A) (h1 : term12 A B lt2) : term20 A B.
Proof. exact (@lem354304 A B lt2 (@lem346598 A B lt2 h1)). Qed.
Lemma lem354306 {A B : Type'} (lt2 : type1402 A) (h1 : term12 A B lt2) : term17 A B.
Proof. exact (@lem354305 A B lt2 h1 (@lem346601 A B)). Qed.
Lemma lem354307 {A B : Type'} (lt2 : type1402 A) (h1 : term12 A B lt2) : False.
Proof. exact (@lem354306 A B lt2 h1 (@lem346599 A B)). Qed.
Lemma lem354308 {A B : Type'} (lt2 : type1402 A) (h1 : term12 A B lt2) : (term12 A B lt2) = False.
Proof. exact (prop_ext (fun h2 : term12 A B lt2 => @lem354307 A B lt2 h1) (fun h2 : False => @lem346598 A B lt2 h1)). Qed.
Lemma lem354309 {A B : Type'} (lt2 : type1402 A) (h1 : term12 A B lt2) : False.
Proof. exact (EQ_MP (@lem354308 A B lt2 h1) (@lem346598 A B lt2 h1)). Qed.
Lemma lem354310 {A B : Type'} (lt2 : type1402 A) : term11 A B lt2.
Proof. exact (fun h0 : term12 A B lt2 => @lem354309 A B lt2 h0). Qed.
Lemma lem354311 {A B : Type'} (lt2 : type1402 A) : term10 A B lt2.
Proof. exact (EQ_MP (@lem346597 A B lt2) (@lem354310 A B lt2)). Qed.
