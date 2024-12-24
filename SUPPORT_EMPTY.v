Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUPPORT_EMPTY_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import IN_SUPPORT_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm82_spec.
Lemma lem5718597 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5718598 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5718599 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5718598 A x) (@lem5718597 A x)). Qed.
Lemma lem5718600 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5718640 {A : Type'} (s : A -> Prop) : term3 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5718641 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (eq_refl (term3 A s)). Qed.
Lemma lem5718642 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (EQ_MP (@lem5718641 A s) (@lem5718640 A s)). Qed.
Lemma lem5718643 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term5 A s t.
Proof. exact (@lem5718642 A s t). Qed.
Lemma lem5718644 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = ((s = t) = (term6 A s t)).
Proof. exact (eq_refl (term5 A s t)). Qed.
Lemma lem5718646 {_119826 _119829 : Type'} (op : type1400 _119826) : term7 _119826 _119829 op.
Proof. exact (@lem5718201 _119826 _119829 op). Qed.
Lemma lem5718647 {_119826 _119829 : Type'} (op : type1400 _119826) : (term7 _119826 _119829 op) = (term8 _119826 _119829 op).
Proof. exact (eq_refl (term7 _119826 _119829 op)). Qed.
Lemma lem5718648 {_119826 _119829 : Type'} (op : type1400 _119826) : term8 _119826 _119829 op.
Proof. exact (EQ_MP (@lem5718647 _119826 _119829 op) (@lem5718646 _119826 _119829 op)). Qed.
Lemma lem5718649 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) : term9 _119826 _119829 op f.
Proof. exact (@lem5718648 _119826 _119829 op f). Qed.
Lemma lem5718650 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : (term9 _119826 _119829 op f) = (term10 _119826 _119829 f op).
Proof. exact (eq_refl (term9 _119826 _119829 op f)). Qed.
Lemma lem5718651 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : term10 _119826 _119829 f op.
Proof. exact (EQ_MP (@lem5718650 _119826 _119829 f op) (@lem5718649 _119826 _119829 op f)). Qed.
Lemma lem5718652 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) (x : _119829) : term11 _119826 _119829 f op x.
Proof. exact (@lem5718651 _119826 _119829 f op x). Qed.
Lemma lem5718653 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term11 _119826 _119829 f op x) = (term12 _119826 _119829 f x op).
Proof. exact (eq_refl (term11 _119826 _119829 f op x)). Qed.
Lemma lem5718654 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : term12 _119826 _119829 f x op.
Proof. exact (EQ_MP (@lem5718653 _119826 _119829 f x op) (@lem5718652 _119826 _119829 f op x)). Qed.
Lemma lem5718655 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) (s : _119829 -> Prop) : term13 _119826 _119829 f x op s.
Proof. exact (@lem5718654 _119826 _119829 f x op s). Qed.
Lemma lem5718656 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term13 _119826 _119829 f x op s) = ((term14 _119826 _119829 x op f s) = (term15 _119826 _119829 s f x op)).
Proof. exact (eq_refl (term13 _119826 _119829 f x op s)). Qed.
Lemma lem5718687 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (EQ_MP (@lem5718644 A s t) (@lem5718643 A s t)). Qed.
Lemma lem5718688 {_119901 : Type'} (s : _119901 -> Prop) (t : _119901 -> Prop) : (s = t) = (term6 _119901 s t).
Proof. exact (@lem5718687 _119901 s t). Qed.
Lemma lem5718689 {_119887 _119901 : Type'} (op : type1400 _119887) (f : _119901 -> _119887) (s : _119901 -> Prop) : ((@support _119901 _119887 op f s) = (@EMPTY _119901)) = (term16 _119887 _119901 op f s).
Proof. exact (@lem5718688 _119901 (@support _119901 _119887 op f s) (@EMPTY _119901)). Qed.
Lemma lem5718699 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term14 _119826 _119829 x op f s) = (term15 _119826 _119829 s f x op).
Proof. exact (EQ_MP (@lem5718656 _119826 _119829 s f x op) (@lem5718655 _119826 _119829 f x op s)). Qed.
Lemma lem5718700 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term14 _119887 _119901 x op f s) = (term15 _119887 _119901 s f x op).
Proof. exact (@lem5718699 _119887 _119901 s f x op). Qed.
Lemma lem5718707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5718708 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term17 _119887 _119901 x op f s) = (term18 _119887 _119901 s f x op).
Proof. exact (MK_COMB (@lem5718707) (@lem5718700 _119887 _119901 s f x op)). Qed.
Lemma lem5718710 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5718600 A x (@lem5718599 A x)). Qed.
Lemma lem5718711 {_119901 : Type'} (x : _119901) : (@IN _119901 x (@EMPTY _119901)) = False.
Proof. exact (@lem5718710 _119901 x). Qed.
Lemma lem5718712 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : ((term14 _119887 _119901 x op f s) = (@IN _119901 x (@EMPTY _119901))) = ((term15 _119887 _119901 s f x op) = False).
Proof. exact (MK_COMB (@lem5718708 _119887 _119901 s f x op) (@lem5718711 _119901 x)). Qed.
Lemma lem5718714 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5718715 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : ((term15 _119887 _119901 s f x op) = False) = (term19 _119887 _119901 s f x op).
Proof. exact (@lem5718714 (term15 _119887 _119901 s f x op)). Qed.
Lemma lem5718722 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : ((term14 _119887 _119901 x op f s) = (@IN _119901 x (@EMPTY _119901))) = (term19 _119887 _119901 s f x op).
Proof. exact (TRANS (@lem5718712 _119887 _119901 s f x op) (@lem5718715 _119887 _119901 s f x op)). Qed.
Lemma lem5718723 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term20 _119887 _119901 op f s) = (term21 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5718722 _119887 _119901 s f x op)). Qed.
Lemma lem5718724 {_119901 : Type'} : (@all _119901) = (@all _119901).
Proof. exact (eq_refl (@all _119901)). Qed.
Lemma lem5718725 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term16 _119887 _119901 op f s) = (term22 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718724 _119901) (@lem5718723 _119887 _119901 s f op)). Qed.
Lemma lem5718730 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : ((@support _119901 _119887 op f s) = (@EMPTY _119901)) = (term22 _119887 _119901 s f op).
Proof. exact (TRANS (@lem5718689 _119887 _119901 op f s) (@lem5718725 _119887 _119901 s f op)). Qed.
Lemma lem5718731 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term23 _119887 _119901 s f op) = (term23 _119887 _119901 s f op).
Proof. exact (eq_refl (term23 _119887 _119901 s f op)). Qed.
Lemma lem5718732 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : ((term24 _119887 _119901 s f op) = ((@support _119901 _119887 op f s) = (@EMPTY _119901))) = ((term24 _119887 _119901 s f op) = (term22 _119887 _119901 s f op)).
Proof. exact (MK_COMB (@lem5718731 _119887 _119901 s f op) (@lem5718730 _119887 _119901 s f op)). Qed.
Lemma lem5718737 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) : (term25 _119887 _119901 op f) = (term26 _119887 _119901 f op).
Proof. exact (fun_ext (fun s : _119901 -> Prop => @lem5718732 _119887 _119901 s f op)). Qed.
Lemma lem5718738 {_119901 : Type'} : (@all (_119901 -> Prop)) = (@all (_119901 -> Prop)).
Proof. exact (eq_refl (@all (_119901 -> Prop))). Qed.
Lemma lem5718739 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) : (term27 _119887 _119901 op f) = (term28 _119887 _119901 f op).
Proof. exact (MK_COMB (@lem5718738 _119901) (@lem5718737 _119887 _119901 f op)). Qed.
Lemma lem5718744 {_119887 _119901 : Type'} (op : type1400 _119887) : (term29 _119887 _119901 op) = (term30 _119887 _119901 op).
Proof. exact (fun_ext (fun f : _119901 -> _119887 => @lem5718739 _119887 _119901 f op)). Qed.
Lemma lem5718745 {_119887 _119901 : Type'} : (@all (_119901 -> _119887)) = (@all (_119901 -> _119887)).
Proof. exact (eq_refl (@all (_119901 -> _119887))). Qed.
Lemma lem5718746 {_119887 _119901 : Type'} (op : type1400 _119887) : (term31 _119887 _119901 op) = (term32 _119887 _119901 op).
Proof. exact (MK_COMB (@lem5718745 _119887 _119901) (@lem5718744 _119887 _119901 op)). Qed.
Lemma lem5718751 {_119887 _119901 : Type'} : (term33 _119887 _119901) = (term34 _119887 _119901).
Proof. exact (fun_ext (fun op : type1400 _119887 => @lem5718746 _119887 _119901 op)). Qed.
Lemma lem5718752 {_119887 : Type'} : (@all (_119887 -> _119887 -> _119887)) = (@all (_119887 -> _119887 -> _119887)).
Proof. exact (eq_refl (@all (_119887 -> _119887 -> _119887))). Qed.
Lemma lem5718753 {_119887 _119901 : Type'} : (term35 _119887 _119901) = (term36 _119887 _119901).
Proof. exact (MK_COMB (@lem5718752 _119887) (@lem5718751 _119887 _119901)). Qed.
Lemma lem5718758 {_119887 _119901 : Type'} : (term36 _119887 _119901) = (term35 _119887 _119901).
Proof. exact (SYM (@lem5718753 _119887 _119901)). Qed.
Lemma lem5718760 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5718761 {_119887 _119901 : Type'} : (term36 _119887 _119901) = (term38 _119887 _119901).
Proof. exact (@lem5718760 (term36 _119887 _119901)). Qed.
Lemma lem5718762 {_119887 _119901 : Type'} : (term38 _119887 _119901) = (term36 _119887 _119901).
Proof. exact (SYM (@lem5718761 _119887 _119901)). Qed.
Lemma lem5718763 {_119887 _119901 : Type'} (h1 : term39 _119887 _119901) : term39 _119887 _119901.
Proof. exact (h1). Qed.
Lemma lem5718766 {_119887 _119901 : Type'} (h1 : term38 _119887 _119901) : term38 _119887 _119901.
Proof. exact (h1). Qed.
Lemma lem5718767 {_119887 _119901 : Type'} : term40 _119887 _119901.
Proof. exact (fun h0 : term38 _119887 _119901 => @lem5718766 _119887 _119901 h0). Qed.
Lemma lem5718768 {_119887 _119901 : Type'} (h1 : term40 _119887 _119901) : term40 _119887 _119901.
Proof. exact (h1). Qed.
Lemma lem5718769 {_119887 _119901 : Type'} (h1 : term38 _119887 _119901) : term38 _119887 _119901.
Proof. exact (h1). Qed.
Lemma lem5718770 {_119887 _119901 : Type'} (h1 : term38 _119887 _119901) (h2 : term40 _119887 _119901) : term38 _119887 _119901.
Proof. exact (@lem5718768 _119887 _119901 h2 (@lem5718769 _119887 _119901 h1)). Qed.
Lemma lem5718771 {_119887 _119901 : Type'} (h1 : term38 _119887 _119901) : term41 _119887 _119901.
Proof. exact (fun h0 : term40 _119887 _119901 => @lem5718770 _119887 _119901 h1 h0). Qed.
Lemma lem5718772 {_119887 _119901 : Type'} (h1 : term40 _119887 _119901) : term40 _119887 _119901.
Proof. exact (h1). Qed.
Lemma lem5718773 {_119887 _119901 : Type'} (h1 : term38 _119887 _119901) (h2 : term40 _119887 _119901) : term38 _119887 _119901.
Proof. exact (@lem5718771 _119887 _119901 h1 (@lem5718772 _119887 _119901 h2)). Qed.
Lemma lem5718774 {_119887 _119901 : Type'} (h1 : term40 _119887 _119901) : term40 _119887 _119901.
Proof. exact (fun h0 : term38 _119887 _119901 => @lem5718773 _119887 _119901 h0 h1). Qed.
Lemma lem5718775 {_119887 _119901 : Type'} : term42 _119887 _119901.
Proof. exact (fun h0 : term40 _119887 _119901 => @lem5718774 _119887 _119901 h0). Qed.
Lemma lem5718778 {_119887 _119901 : Type'} : term40 _119887 _119901.
Proof. exact (@lem5718775 _119887 _119901 (@lem5718767 _119887 _119901)). Qed.
Lemma lem5718779 {_119887 _119901 : Type'} : term40 _119887 _119901.
Proof. exact (@lem5718778 _119887 _119901). Qed.
Lemma lem5718781 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5718782 {_119887 _119901 : Type'} : (term38 _119887 _119901) = (term43 _119887 _119901).
Proof. exact (@lem5718781 (term39 _119887 _119901)). Qed.
Lemma lem5718784 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5718785 {_119887 _119901 : Type'} : (term43 _119887 _119901) = (term36 _119887 _119901).
Proof. exact (@lem5718784 (term36 _119887 _119901)). Qed.
Lemma lem5718814 {_119887 _119901 : Type'} : (term38 _119887 _119901) = (term36 _119887 _119901).
Proof. exact (TRANS (@lem5718782 _119887 _119901) (@lem5718785 _119887 _119901)). Qed.
Lemma lem5718823 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term19 _119887 _119901 s f x op) = (term19 _119887 _119901 s f x op).
Proof. exact (eq_refl (term19 _119887 _119901 s f x op)). Qed.
Lemma lem5718824 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term21 _119887 _119901 s f op) = (term21 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5718823 _119887 _119901 s f x op)). Qed.
Lemma lem5718825 {_119901 : Type'} : (@all _119901) = (@all _119901).
Proof. exact (eq_refl (@all _119901)). Qed.
Lemma lem5718826 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term22 _119887 _119901 s f op) = (term22 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718825 _119901) (@lem5718824 _119887 _119901 s f op)). Qed.
Lemma lem5718831 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term45 _119887 _119901 s f x op) = (term45 _119887 _119901 s f x op).
Proof. exact (eq_refl (term45 _119887 _119901 s f x op)). Qed.
Lemma lem5718832 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term46 _119887 _119901 s f op) = (term46 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5718831 _119887 _119901 s f x op)). Qed.
Lemma lem5718833 {_119901 : Type'} : (@all _119901) = (@all _119901).
Proof. exact (eq_refl (@all _119901)). Qed.
Lemma lem5718834 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term24 _119887 _119901 s f op) = (term24 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718833 _119901) (@lem5718832 _119887 _119901 s f op)). Qed.
Lemma lem5718835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5718836 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term23 _119887 _119901 s f op) = (term23 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718835) (@lem5718834 _119887 _119901 s f op)). Qed.
Lemma lem5718837 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : ((term24 _119887 _119901 s f op) = (term22 _119887 _119901 s f op)) = ((term24 _119887 _119901 s f op) = (term22 _119887 _119901 s f op)).
Proof. exact (MK_COMB (@lem5718836 _119887 _119901 s f op) (@lem5718826 _119887 _119901 s f op)). Qed.
Lemma lem5718838 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) : (term26 _119887 _119901 f op) = (term26 _119887 _119901 f op).
Proof. exact (fun_ext (fun s : _119901 -> Prop => @lem5718837 _119887 _119901 s f op)). Qed.
Lemma lem5718839 {_119901 : Type'} : (@all (_119901 -> Prop)) = (@all (_119901 -> Prop)).
Proof. exact (eq_refl (@all (_119901 -> Prop))). Qed.
Lemma lem5718840 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) : (term28 _119887 _119901 f op) = (term28 _119887 _119901 f op).
Proof. exact (MK_COMB (@lem5718839 _119901) (@lem5718838 _119887 _119901 f op)). Qed.
Lemma lem5718841 {_119887 _119901 : Type'} (op : type1400 _119887) : (term30 _119887 _119901 op) = (term30 _119887 _119901 op).
Proof. exact (fun_ext (fun f : _119901 -> _119887 => @lem5718840 _119887 _119901 f op)). Qed.
Lemma lem5718842 {_119887 _119901 : Type'} : (@all (_119901 -> _119887)) = (@all (_119901 -> _119887)).
Proof. exact (eq_refl (@all (_119901 -> _119887))). Qed.
Lemma lem5718843 {_119887 _119901 : Type'} (op : type1400 _119887) : (term32 _119887 _119901 op) = (term32 _119887 _119901 op).
Proof. exact (MK_COMB (@lem5718842 _119887 _119901) (@lem5718841 _119887 _119901 op)). Qed.
Lemma lem5718844 {_119887 _119901 : Type'} : (term34 _119887 _119901) = (term34 _119887 _119901).
Proof. exact (fun_ext (fun op : type1400 _119887 => @lem5718843 _119887 _119901 op)). Qed.
Lemma lem5718845 {_119887 : Type'} : (@all (_119887 -> _119887 -> _119887)) = (@all (_119887 -> _119887 -> _119887)).
Proof. exact (eq_refl (@all (_119887 -> _119887 -> _119887))). Qed.
Lemma lem5718846 {_119887 _119901 : Type'} : (term36 _119887 _119901) = (term36 _119887 _119901).
Proof. exact (MK_COMB (@lem5718845 _119887) (@lem5718844 _119887 _119901)). Qed.
Lemma lem5718883 {_119887 _119901 : Type'} : (term38 _119887 _119901) = (term36 _119887 _119901).
Proof. exact (TRANS (@lem5718814 _119887 _119901) (@lem5718846 _119887 _119901)). Qed.
Lemma lem5718884 {_119887 _119901 : Type'} : (term36 _119887 _119901) = (term38 _119887 _119901).
Proof. exact (SYM (@lem5718883 _119887 _119901)). Qed.
Lemma lem5718886 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5718887 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : ((term24 _119887 _119901 s f op) = (term22 _119887 _119901 s f op)) = (term47 _119887 _119901 s f op).
Proof. exact (@lem5718886 ((term24 _119887 _119901 s f op) = (term22 _119887 _119901 s f op))). Qed.
Lemma lem5718888 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term47 _119887 _119901 s f op) = ((term24 _119887 _119901 s f op) = (term22 _119887 _119901 s f op)).
Proof. exact (SYM (@lem5718887 _119887 _119901 s f op)). Qed.
Lemma lem5718889 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term48 _119887 _119901 s f op) : term48 _119887 _119901 s f op.
Proof. exact (h1). Qed.
Lemma lem5718898 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term49 _119887 _119901 s f x op) = (term15 _119887 _119901 s f x op).
Proof. exact (@lem17362 (@IN _119901 x s) ((f x) = (@neutral _119887 op))). Qed.
Lemma lem5718903 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term45 _119887 _119901 s f x op) = (term50 _119887 _119901 s f x op).
Proof. exact (@lem17265 (@IN _119901 x s) ((f x) = (@neutral _119887 op))). Qed.
Lemma lem5718904 {_119901 : Type'} (P : _119901 -> Prop) : (term51 _119901 P) = (term52 _119901 P).
Proof. exact (@lem18392 _119901 P). Qed.
Lemma lem5718905 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term53 _119887 _119901 s f op) = (term54 _119887 _119901 s f op).
Proof. exact (@lem5718904 _119901 (term46 _119887 _119901 s f op)). Qed.
Lemma lem5718906 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term55 _119887 _119901 s f op x) = (term45 _119887 _119901 s f x op).
Proof. exact (eq_refl (term55 _119887 _119901 s f op x)). Qed.
Lemma lem5718907 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5718908 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term56 _119887 _119901 s f op x) = (term49 _119887 _119901 s f x op).
Proof. exact (MK_COMB (@lem5718907) (@lem5718906 _119887 _119901 s f x op)). Qed.
Lemma lem5718909 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term56 _119887 _119901 s f op x) = (term15 _119887 _119901 s f x op).
Proof. exact (TRANS (@lem5718908 _119887 _119901 s f x op) (@lem5718898 _119887 _119901 s f x op)). Qed.
Lemma lem5718910 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term57 _119887 _119901 s f op) = (term58 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5718909 _119887 _119901 s f x op)). Qed.
Lemma lem5718911 {_119901 : Type'} : (@ex _119901) = (@ex _119901).
Proof. exact (eq_refl (@ex _119901)). Qed.
Lemma lem5718912 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term54 _119887 _119901 s f op) = (term59 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718911 _119901) (@lem5718910 _119887 _119901 s f op)). Qed.
Lemma lem5718913 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term53 _119887 _119901 s f op) = (term59 _119887 _119901 s f op).
Proof. exact (TRANS (@lem5718905 _119887 _119901 s f op) (@lem5718912 _119887 _119901 s f op)). Qed.
Lemma lem5718914 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term46 _119887 _119901 s f op) = (term60 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5718903 _119887 _119901 s f x op)). Qed.
Lemma lem5718915 {_119901 : Type'} : (@all _119901) = (@all _119901).
Proof. exact (eq_refl (@all _119901)). Qed.
Lemma lem5718916 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term24 _119887 _119901 s f op) = (term61 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718915 _119901) (@lem5718914 _119887 _119901 s f op)). Qed.
Lemma lem5718922 {_119887 _119901 : Type'} (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term62 _119887 _119901 f x op) = ((f x) = (@neutral _119887 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _119887 op))). Qed.
Lemma lem5718924 {_119901 : Type'} (x : _119901) (s : _119901 -> Prop) : (term63 _119901 x s) = (term63 _119901 x s).
Proof. exact (eq_refl (term63 _119901 x s)). Qed.
Lemma lem5718925 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term64 _119887 _119901 s f x op) = (term50 _119887 _119901 s f x op).
Proof. exact (MK_COMB (@lem5718924 _119901 x s) (@lem5718922 _119887 _119901 f x op)). Qed.
Lemma lem5718926 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term19 _119887 _119901 s f x op) = (term64 _119887 _119901 s f x op).
Proof. exact (@lem17045 (@IN _119901 x s) (term65 _119887 _119901 f x op)). Qed.
Lemma lem5718927 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term19 _119887 _119901 s f x op) = (term50 _119887 _119901 s f x op).
Proof. exact (TRANS (@lem5718926 _119887 _119901 s f x op) (@lem5718925 _119887 _119901 s f x op)). Qed.
Lemma lem5718932 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term66 _119887 _119901 s f x op) = (term15 _119887 _119901 s f x op).
Proof. exact (@lem16933 (term15 _119887 _119901 s f x op)). Qed.
Lemma lem5718933 {_119901 : Type'} (P : _119901 -> Prop) : (term51 _119901 P) = (term52 _119901 P).
Proof. exact (@lem18392 _119901 P). Qed.
Lemma lem5718934 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term67 _119887 _119901 s f op) = (term68 _119887 _119901 s f op).
Proof. exact (@lem5718933 _119901 (term21 _119887 _119901 s f op)). Qed.
Lemma lem5718935 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term69 _119887 _119901 s f op x) = (term19 _119887 _119901 s f x op).
Proof. exact (eq_refl (term69 _119887 _119901 s f op x)). Qed.
Lemma lem5718936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5718937 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term70 _119887 _119901 s f op x) = (term66 _119887 _119901 s f x op).
Proof. exact (MK_COMB (@lem5718936) (@lem5718935 _119887 _119901 s f x op)). Qed.
Lemma lem5718938 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term70 _119887 _119901 s f op x) = (term15 _119887 _119901 s f x op).
Proof. exact (TRANS (@lem5718937 _119887 _119901 s f x op) (@lem5718932 _119887 _119901 s f x op)). Qed.
Lemma lem5718939 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term71 _119887 _119901 s f op) = (term58 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5718938 _119887 _119901 s f x op)). Qed.
Lemma lem5718940 {_119901 : Type'} : (@ex _119901) = (@ex _119901).
Proof. exact (eq_refl (@ex _119901)). Qed.
Lemma lem5718941 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term68 _119887 _119901 s f op) = (term59 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718940 _119901) (@lem5718939 _119887 _119901 s f op)). Qed.
Lemma lem5718942 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term67 _119887 _119901 s f op) = (term59 _119887 _119901 s f op).
Proof. exact (TRANS (@lem5718934 _119887 _119901 s f op) (@lem5718941 _119887 _119901 s f op)). Qed.
Lemma lem5718943 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term21 _119887 _119901 s f op) = (term60 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5718927 _119887 _119901 s f x op)). Qed.
Lemma lem5718944 {_119901 : Type'} : (@all _119901) = (@all _119901).
Proof. exact (eq_refl (@all _119901)). Qed.
Lemma lem5718945 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term22 _119887 _119901 s f op) = (term61 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718944 _119901) (@lem5718943 _119887 _119901 s f op)). Qed.
Lemma lem5718946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5718947 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term72 _119887 _119901 s f op) = (term73 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718946) (@lem5718913 _119887 _119901 s f op)). Qed.
Lemma lem5718948 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term74 _119887 _119901 s f op) = (term75 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718947 _119887 _119901 s f op) (@lem5718945 _119887 _119901 s f op)). Qed.
Lemma lem5718949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5718950 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term76 _119887 _119901 s f op) = (term77 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718949) (@lem5718916 _119887 _119901 s f op)). Qed.
Lemma lem5718951 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term78 _119887 _119901 s f op) = (term79 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718950 _119887 _119901 s f op) (@lem5718942 _119887 _119901 s f op)). Qed.
Lemma lem5718952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5718953 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term80 _119887 _119901 s f op) = (term81 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718952) (@lem5718951 _119887 _119901 s f op)). Qed.
Lemma lem5718954 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term82 _119887 _119901 s f op) = (term83 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5718953 _119887 _119901 s f op) (@lem5718948 _119887 _119901 s f op)). Qed.
Lemma lem5718955 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term48 _119887 _119901 s f op) = (term82 _119887 _119901 s f op).
Proof. exact (@lem17646 (term24 _119887 _119901 s f op) (term22 _119887 _119901 s f op)). Qed.
Lemma lem5718956 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term48 _119887 _119901 s f op) = (term83 _119887 _119901 s f op).
Proof. exact (TRANS (@lem5718955 _119887 _119901 s f op) (@lem5718954 _119887 _119901 s f op)). Qed.
Lemma lem5719151 {A : Type'} (P : Prop) (Q : A -> Prop) : (term84 A P Q) = (term85 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5719152 {_119901 : Type'} (P : Prop) (Q : _119901 -> Prop) : (term84 _119901 P Q) = (term85 _119901 P Q).
Proof. exact (@lem5719151 _119901 P Q). Qed.
Lemma lem5719153 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term86 _119887 _119901 s f op) = (term87 _119887 _119901 s f op).
Proof. exact (@lem5719152 _119901 (term61 _119887 _119901 s f op) (term58 _119887 _119901 s f op)). Qed.
Lemma lem5719154 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term88 _119887 _119901 s f op x) = (term15 _119887 _119901 s f x op).
Proof. exact (eq_refl (term88 _119887 _119901 s f op x)). Qed.
Lemma lem5719155 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term89 _119887 _119901 s f op) = (term58 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719154 _119887 _119901 s f x op)). Qed.
Lemma lem5719156 {_119901 : Type'} : (@ex _119901) = (@ex _119901).
Proof. exact (eq_refl (@ex _119901)). Qed.
Lemma lem5719157 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term90 _119887 _119901 s f op) = (term59 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719156 _119901) (@lem5719155 _119887 _119901 s f op)). Qed.
Lemma lem5719158 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term77 _119887 _119901 s f op) = (term77 _119887 _119901 s f op).
Proof. exact (eq_refl (term77 _119887 _119901 s f op)). Qed.
Lemma lem5719159 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term86 _119887 _119901 s f op) = (term79 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719158 _119887 _119901 s f op) (@lem5719157 _119887 _119901 s f op)). Qed.
Lemma lem5719160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5719161 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term91 _119887 _119901 s f op) = (term92 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719160) (@lem5719159 _119887 _119901 s f op)). Qed.
Lemma lem5719162 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term88 _119887 _119901 s f op x) = (term15 _119887 _119901 s f x op).
Proof. exact (eq_refl (term88 _119887 _119901 s f op x)). Qed.
Lemma lem5719163 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term77 _119887 _119901 s f op) = (term77 _119887 _119901 s f op).
Proof. exact (eq_refl (term77 _119887 _119901 s f op)). Qed.
Lemma lem5719164 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term93 _119887 _119901 s f op x) = (term94 _119887 _119901 s f x op).
Proof. exact (MK_COMB (@lem5719163 _119887 _119901 s f op) (@lem5719162 _119887 _119901 s f x op)). Qed.
Lemma lem5719165 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term95 _119887 _119901 s f op) = (term96 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719164 _119887 _119901 s f x op)). Qed.
Lemma lem5719166 {_119901 : Type'} : (@ex _119901) = (@ex _119901).
Proof. exact (eq_refl (@ex _119901)). Qed.
Lemma lem5719167 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term87 _119887 _119901 s f op) = (term97 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719166 _119901) (@lem5719165 _119887 _119901 s f op)). Qed.
Lemma lem5719168 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : ((term86 _119887 _119901 s f op) = (term87 _119887 _119901 s f op)) = ((term79 _119887 _119901 s f op) = (term97 _119887 _119901 s f op)).
Proof. exact (MK_COMB (@lem5719161 _119887 _119901 s f op) (@lem5719167 _119887 _119901 s f op)). Qed.
Lemma lem5719169 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term79 _119887 _119901 s f op) = (term97 _119887 _119901 s f op).
Proof. exact (EQ_MP (@lem5719168 _119887 _119901 s f op) (@lem5719153 _119887 _119901 s f op)). Qed.
Lemma lem5719170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5719171 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term81 _119887 _119901 s f op) = (term98 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719170) (@lem5719169 _119887 _119901 s f op)). Qed.
Lemma lem5719173 {A : Type'} (P : A -> Prop) (Q : Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5719174 {_119901 : Type'} (P : _119901 -> Prop) (Q : Prop) : (term99 _119901 P Q) = (term100 _119901 P Q).
Proof. exact (@lem5719173 _119901 P Q). Qed.
Lemma lem5719175 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term101 _119887 _119901 s f op) = (term102 _119887 _119901 s f op).
Proof. exact (@lem5719174 _119901 (term58 _119887 _119901 s f op) (term61 _119887 _119901 s f op)). Qed.
Lemma lem5719176 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term88 _119887 _119901 s f op x) = (term15 _119887 _119901 s f x op).
Proof. exact (eq_refl (term88 _119887 _119901 s f op x)). Qed.
Lemma lem5719177 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term89 _119887 _119901 s f op) = (term58 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719176 _119887 _119901 s f x op)). Qed.
Lemma lem5719178 {_119901 : Type'} : (@ex _119901) = (@ex _119901).
Proof. exact (eq_refl (@ex _119901)). Qed.
Lemma lem5719179 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term90 _119887 _119901 s f op) = (term59 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719178 _119901) (@lem5719177 _119887 _119901 s f op)). Qed.
Lemma lem5719180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5719181 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term103 _119887 _119901 s f op) = (term73 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719180) (@lem5719179 _119887 _119901 s f op)). Qed.
Lemma lem5719182 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term61 _119887 _119901 s f op) = (term61 _119887 _119901 s f op).
Proof. exact (eq_refl (term61 _119887 _119901 s f op)). Qed.
Lemma lem5719183 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term101 _119887 _119901 s f op) = (term75 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719181 _119887 _119901 s f op) (@lem5719182 _119887 _119901 s f op)). Qed.
Lemma lem5719184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5719185 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term104 _119887 _119901 s f op) = (term105 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719184) (@lem5719183 _119887 _119901 s f op)). Qed.
Lemma lem5719186 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term88 _119887 _119901 s f op x) = (term15 _119887 _119901 s f x op).
Proof. exact (eq_refl (term88 _119887 _119901 s f op x)). Qed.
Lemma lem5719187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5719188 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term106 _119887 _119901 s f op x) = (term107 _119887 _119901 s f x op).
Proof. exact (MK_COMB (@lem5719187) (@lem5719186 _119887 _119901 s f x op)). Qed.
Lemma lem5719189 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term61 _119887 _119901 s f op) = (term61 _119887 _119901 s f op).
Proof. exact (eq_refl (term61 _119887 _119901 s f op)). Qed.
Lemma lem5719190 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term108 _119887 _119901 x s f op) = (term109 _119887 _119901 x s f op).
Proof. exact (MK_COMB (@lem5719188 _119887 _119901 s f x op) (@lem5719189 _119887 _119901 s f op)). Qed.
Lemma lem5719191 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term110 _119887 _119901 s f op) = (term111 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719190 _119887 _119901 x s f op)). Qed.
Lemma lem5719192 {_119901 : Type'} : (@ex _119901) = (@ex _119901).
Proof. exact (eq_refl (@ex _119901)). Qed.
Lemma lem5719193 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term102 _119887 _119901 s f op) = (term112 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719192 _119901) (@lem5719191 _119887 _119901 s f op)). Qed.
Lemma lem5719194 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : ((term101 _119887 _119901 s f op) = (term102 _119887 _119901 s f op)) = ((term75 _119887 _119901 s f op) = (term112 _119887 _119901 s f op)).
Proof. exact (MK_COMB (@lem5719185 _119887 _119901 s f op) (@lem5719193 _119887 _119901 s f op)). Qed.
Lemma lem5719195 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term75 _119887 _119901 s f op) = (term112 _119887 _119901 s f op).
Proof. exact (EQ_MP (@lem5719194 _119887 _119901 s f op) (@lem5719175 _119887 _119901 s f op)). Qed.
Lemma lem5719196 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term83 _119887 _119901 s f op) = (term113 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719171 _119887 _119901 s f op) (@lem5719195 _119887 _119901 s f op)). Qed.
Lemma lem5719198 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5719199 {_119901 : Type'} (P : _119901 -> Prop) (Q : _119901 -> Prop) : (term114 _119901 P Q) = (term115 _119901 P Q).
Proof. exact (@lem5719198 _119901 P Q). Qed.
Lemma lem5719200 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term116 _119887 _119901 s f op) = (term117 _119887 _119901 s f op).
Proof. exact (@lem5719199 _119901 (term96 _119887 _119901 s f op) (term111 _119887 _119901 s f op)). Qed.
Lemma lem5719201 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term118 _119887 _119901 s f op x) = (term94 _119887 _119901 s f x op).
Proof. exact (eq_refl (term118 _119887 _119901 s f op x)). Qed.
Lemma lem5719202 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term119 _119887 _119901 s f op) = (term96 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719201 _119887 _119901 s f x op)). Qed.
Lemma lem5719203 {_119901 : Type'} : (@ex _119901) = (@ex _119901).
Proof. exact (eq_refl (@ex _119901)). Qed.
Lemma lem5719204 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term120 _119887 _119901 s f op) = (term97 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719203 _119901) (@lem5719202 _119887 _119901 s f op)). Qed.
Lemma lem5719205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5719206 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term121 _119887 _119901 s f op) = (term98 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719205) (@lem5719204 _119887 _119901 s f op)). Qed.
Lemma lem5719207 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term122 _119887 _119901 s f op x) = (term109 _119887 _119901 x s f op).
Proof. exact (eq_refl (term122 _119887 _119901 s f op x)). Qed.
Lemma lem5719208 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term123 _119887 _119901 s f op) = (term111 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719207 _119887 _119901 x s f op)). Qed.
Lemma lem5719209 {_119901 : Type'} : (@ex _119901) = (@ex _119901).
Proof. exact (eq_refl (@ex _119901)). Qed.
Lemma lem5719210 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term124 _119887 _119901 s f op) = (term112 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719209 _119901) (@lem5719208 _119887 _119901 s f op)). Qed.
Lemma lem5719211 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term116 _119887 _119901 s f op) = (term113 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719206 _119887 _119901 s f op) (@lem5719210 _119887 _119901 s f op)). Qed.
Lemma lem5719212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5719213 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term125 _119887 _119901 s f op) = (term126 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719212) (@lem5719211 _119887 _119901 s f op)). Qed.
Lemma lem5719214 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term118 _119887 _119901 s f op x) = (term94 _119887 _119901 s f x op).
Proof. exact (eq_refl (term118 _119887 _119901 s f op x)). Qed.
Lemma lem5719215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5719216 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term127 _119887 _119901 s f op x) = (term128 _119887 _119901 s f x op).
Proof. exact (MK_COMB (@lem5719215) (@lem5719214 _119887 _119901 s f x op)). Qed.
Lemma lem5719217 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term122 _119887 _119901 s f op x) = (term109 _119887 _119901 x s f op).
Proof. exact (eq_refl (term122 _119887 _119901 s f op x)). Qed.
Lemma lem5719218 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term129 _119887 _119901 s f op x) = (term130 _119887 _119901 x s f op).
Proof. exact (MK_COMB (@lem5719216 _119887 _119901 s f x op) (@lem5719217 _119887 _119901 x s f op)). Qed.
Lemma lem5719219 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term131 _119887 _119901 s f op) = (term132 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719218 _119887 _119901 x s f op)). Qed.
Lemma lem5719220 {_119901 : Type'} : (@ex _119901) = (@ex _119901).
Proof. exact (eq_refl (@ex _119901)). Qed.
Lemma lem5719221 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term117 _119887 _119901 s f op) = (term133 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719220 _119901) (@lem5719219 _119887 _119901 s f op)). Qed.
Lemma lem5719222 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : ((term116 _119887 _119901 s f op) = (term117 _119887 _119901 s f op)) = ((term113 _119887 _119901 s f op) = (term133 _119887 _119901 s f op)).
Proof. exact (MK_COMB (@lem5719213 _119887 _119901 s f op) (@lem5719221 _119887 _119901 s f op)). Qed.
Lemma lem5719223 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term113 _119887 _119901 s f op) = (term133 _119887 _119901 s f op).
Proof. exact (EQ_MP (@lem5719222 _119887 _119901 s f op) (@lem5719200 _119887 _119901 s f op)). Qed.
Lemma lem5719225 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term83 _119887 _119901 s f op) = (term133 _119887 _119901 s f op).
Proof. exact (TRANS (@lem5719196 _119887 _119901 s f op) (@lem5719223 _119887 _119901 s f op)). Qed.
Lemma lem5719226 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term48 _119887 _119901 s f op) = (term133 _119887 _119901 s f op).
Proof. exact (TRANS (@lem5718956 _119887 _119901 s f op) (@lem5719225 _119887 _119901 s f op)). Qed.
Lemma lem5719227 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term48 _119887 _119901 s f op) : term133 _119887 _119901 s f op.
Proof. exact (EQ_MP (@lem5719226 _119887 _119901 s f op) (@lem5718889 _119887 _119901 s f op h1)). Qed.
Lemma lem5719228 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term130 _119887 _119901 x s f op) : term130 _119887 _119901 x s f op.
Proof. exact (h1). Qed.
Lemma lem5719247 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term50 _119887 _119901 s f x op) = (term50 _119887 _119901 s f x op).
Proof. exact (eq_refl (term50 _119887 _119901 s f x op)). Qed.
Lemma lem5719248 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term60 _119887 _119901 s f op) = (term60 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719247 _119887 _119901 s f x op)). Qed.
Lemma lem5719249 {_119901 : Type'} : (@all _119901) = (@all _119901).
Proof. exact (eq_refl (@all _119901)). Qed.
Lemma lem5719250 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term61 _119887 _119901 s f op) = (term61 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719249 _119901) (@lem5719248 _119887 _119901 s f op)). Qed.
Lemma lem5719271 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term107 _119887 _119901 s f x op) = (term107 _119887 _119901 s f x op).
Proof. exact (eq_refl (term107 _119887 _119901 s f x op)). Qed.
Lemma lem5719272 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term109 _119887 _119901 x s f op) = (term109 _119887 _119901 x s f op).
Proof. exact (MK_COMB (@lem5719271 _119887 _119901 s f x op) (@lem5719250 _119887 _119901 s f op)). Qed.
Lemma lem5719291 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term15 _119887 _119901 s f x op) = (term15 _119887 _119901 s f x op).
Proof. exact (eq_refl (term15 _119887 _119901 s f x op)). Qed.
Lemma lem5719310 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term50 _119887 _119901 s f x op) = (term50 _119887 _119901 s f x op).
Proof. exact (eq_refl (term50 _119887 _119901 s f x op)). Qed.
Lemma lem5719311 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term60 _119887 _119901 s f op) = (term60 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719310 _119887 _119901 s f x op)). Qed.
Lemma lem5719312 {_119901 : Type'} : (@all _119901) = (@all _119901).
Proof. exact (eq_refl (@all _119901)). Qed.
Lemma lem5719313 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term61 _119887 _119901 s f op) = (term61 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719312 _119901) (@lem5719311 _119887 _119901 s f op)). Qed.
Lemma lem5719314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5719315 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term77 _119887 _119901 s f op) = (term77 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719314) (@lem5719313 _119887 _119901 s f op)). Qed.
Lemma lem5719316 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term94 _119887 _119901 s f x op) = (term94 _119887 _119901 s f x op).
Proof. exact (MK_COMB (@lem5719315 _119887 _119901 s f op) (@lem5719291 _119887 _119901 s f x op)). Qed.
Lemma lem5719317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5719318 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term128 _119887 _119901 s f x op) = (term128 _119887 _119901 s f x op).
Proof. exact (MK_COMB (@lem5719317) (@lem5719316 _119887 _119901 s f x op)). Qed.
Lemma lem5719319 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term130 _119887 _119901 x s f op) = (term130 _119887 _119901 x s f op).
Proof. exact (MK_COMB (@lem5719318 _119887 _119901 s f x op) (@lem5719272 _119887 _119901 x s f op)). Qed.
Lemma lem5719320 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term130 _119887 _119901 x s f op) : term130 _119887 _119901 x s f op.
Proof. exact (EQ_MP (@lem5719319 _119887 _119901 x s f op) (@lem5719228 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719321 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term94 _119887 _119901 s f x op.
Proof. exact (h1). Qed.
Lemma lem5719322 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term109 _119887 _119901 x s f op.
Proof. exact (h1). Qed.
Lemma lem5719323 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term15 _119887 _119901 s f x op.
Proof. exact (proj2 (@lem5719321 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719324 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term61 _119887 _119901 s f op.
Proof. exact (proj1 (@lem5719321 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719327 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term61 _119887 _119901 s f op.
Proof. exact (proj2 (@lem5719322 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719328 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term15 _119887 _119901 s f x op.
Proof. exact (proj1 (@lem5719322 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719338 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term50 _119887 _119901 s f x op) = (term50 _119887 _119901 s f x op).
Proof. exact (eq_refl (term50 _119887 _119901 s f x op)). Qed.
Lemma lem5719339 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term60 _119887 _119901 s f op) = (term60 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719338 _119887 _119901 s f x op)). Qed.
Lemma lem5719340 {_119901 : Type'} : (@all _119901) = (@all _119901).
Proof. exact (eq_refl (@all _119901)). Qed.
Lemma lem5719342 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term61 _119887 _119901 s f op) = (term61 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719340 _119901) (@lem5719339 _119887 _119901 s f op)). Qed.
Lemma lem5719343 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term61 _119887 _119901 s f op.
Proof. exact (EQ_MP (@lem5719342 _119887 _119901 s f op) (@lem5719324 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719359 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term50 _119887 _119901 s f x op) = (term50 _119887 _119901 s f x op).
Proof. exact (eq_refl (term50 _119887 _119901 s f x op)). Qed.
Lemma lem5719360 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term60 _119887 _119901 s f op) = (term60 _119887 _119901 s f op).
Proof. exact (fun_ext (fun x : _119901 => @lem5719359 _119887 _119901 s f x op)). Qed.
Lemma lem5719361 {_119901 : Type'} : (@all _119901) = (@all _119901).
Proof. exact (eq_refl (@all _119901)). Qed.
Lemma lem5719363 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term61 _119887 _119901 s f op) = (term61 _119887 _119901 s f op).
Proof. exact (MK_COMB (@lem5719361 _119901) (@lem5719360 _119887 _119901 s f op)). Qed.
Lemma lem5719364 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term61 _119887 _119901 s f op.
Proof. exact (EQ_MP (@lem5719363 _119887 _119901 s f op) (@lem5719327 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719373 {_119887 _119901 : Type'} (_71736 : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term134 _119887 _119901 s f op _71736.
Proof. exact (@lem5719343 _119887 _119901 s f x op h1 _71736). Qed.
Lemma lem5719374 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (_71736 : _119901) (op : type1400 _119887) : (term134 _119887 _119901 s f op _71736) = (term50 _119887 _119901 s f _71736 op).
Proof. exact (eq_refl (term134 _119887 _119901 s f op _71736)). Qed.
Lemma lem5719376 {_119887 _119901 : Type'} (_71737 : _119901) (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term134 _119887 _119901 s f op _71737.
Proof. exact (@lem5719364 _119887 _119901 x s f op h1 _71737). Qed.
Lemma lem5719377 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (_71737 : _119901) (op : type1400 _119887) : (term134 _119887 _119901 s f op _71737) = (term50 _119887 _119901 s f _71737 op).
Proof. exact (eq_refl (term134 _119887 _119901 s f op _71737)). Qed.
Lemma lem5719384 {_119887 _119901 : Type'} (_71736 : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term50 _119887 _119901 s f _71736 op.
Proof. exact (EQ_MP (@lem5719374 _119887 _119901 s f _71736 op) (@lem5719373 _119887 _119901 _71736 s f x op h1)). Qed.
Lemma lem5719388 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term65 _119887 _119901 f x op.
Proof. exact (proj2 (@lem5719323 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719394 {_119887 _119901 : Type'} (_71737 : _119901) (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term50 _119887 _119901 s f _71737 op.
Proof. exact (EQ_MP (@lem5719377 _119887 _119901 s f _71737 op) (@lem5719376 _119887 _119901 _71737 x s f op h1)). Qed.
Lemma lem5719398 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term65 _119887 _119901 f x op.
Proof. exact (proj2 (@lem5719328 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719443 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : @IN _119901 x s.
Proof. exact (proj1 (@lem5719323 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719444 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term135 _119901 x s.
Proof. exact (fun h0 : term136 _119901 x s => @lem5719443 _119887 _119901 s f x op h1). Qed.
Lemma lem5719446 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5719447 {_119901 : Type'} (x : _119901) (s : _119901 -> Prop) : (term135 _119901 x s) = (@IN _119901 x s).
Proof. exact (@lem5719446 (@IN _119901 x s)). Qed.
Lemma lem5719448 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : @IN _119901 x s.
Proof. exact (EQ_MP (@lem5719447 _119901 x s) (@lem5719444 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719454 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5719455 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71736 : _119901) (s : _119901 -> Prop) : (term50 _119887 _119901 s f _71736 op) = (term138 _119887 _119901 f op _71736 s).
Proof. exact (@lem5719454 ((f _71736) = (@neutral _119887 op)) (term136 _119901 _71736 s)). Qed.
Lemma lem5719463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5719464 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71736 : _119901) (s : _119901 -> Prop) : (term139 _119887 _119901 s f _71736 op) = (term140 _119887 _119901 f op _71736 s).
Proof. exact (MK_COMB (@lem5719463) (@lem5719455 _119887 _119901 f op _71736 s)). Qed.
Lemma lem5719472 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71736 : _119901) (s : _119901 -> Prop) : (term138 _119887 _119901 f op _71736 s) = (term138 _119887 _119901 f op _71736 s).
Proof. exact (eq_refl (term138 _119887 _119901 f op _71736 s)). Qed.
Lemma lem5719473 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71736 : _119901) (s : _119901 -> Prop) : ((term50 _119887 _119901 s f _71736 op) = (term138 _119887 _119901 f op _71736 s)) = ((term138 _119887 _119901 f op _71736 s) = (term138 _119887 _119901 f op _71736 s)).
Proof. exact (MK_COMB (@lem5719464 _119887 _119901 f op _71736 s) (@lem5719472 _119887 _119901 f op _71736 s)). Qed.
Lemma lem5719475 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5719476 (x : Prop) : (x = x) = True.
Proof. exact (@lem5719475 Prop x). Qed.
Lemma lem5719477 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71736 : _119901) (s : _119901 -> Prop) : ((term138 _119887 _119901 f op _71736 s) = (term138 _119887 _119901 f op _71736 s)) = True.
Proof. exact (@lem5719476 (term138 _119887 _119901 f op _71736 s)). Qed.
Lemma lem5719478 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71736 : _119901) (s : _119901 -> Prop) : ((term50 _119887 _119901 s f _71736 op) = (term138 _119887 _119901 f op _71736 s)) = True.
Proof. exact (TRANS (@lem5719473 _119887 _119901 f op _71736 s) (@lem5719477 _119887 _119901 f op _71736 s)). Qed.
Lemma lem5719479 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71736 : _119901) (s : _119901 -> Prop) : True = ((term50 _119887 _119901 s f _71736 op) = (term138 _119887 _119901 f op _71736 s)).
Proof. exact (SYM (@lem5719478 _119887 _119901 f op _71736 s)). Qed.
Lemma lem5719480 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71736 : _119901) (s : _119901 -> Prop) : (term50 _119887 _119901 s f _71736 op) = (term138 _119887 _119901 f op _71736 s).
Proof. exact (EQ_MP (@lem5719479 _119887 _119901 f op _71736 s) (@lem0)). Qed.
Lemma lem5719481 {_119887 _119901 : Type'} (_71736 : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term138 _119887 _119901 f op _71736 s.
Proof. exact (EQ_MP (@lem5719480 _119887 _119901 f op _71736 s) (@lem5719384 _119887 _119901 _71736 s f x op h1)). Qed.
Lemma lem5719483 (b : Prop) (a : Prop) : (a \/ b) = (term141 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5719484 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (_71736 : _119901) (op : type1400 _119887) : (term138 _119887 _119901 f op _71736 s) = (term142 _119887 _119901 s f _71736 op).
Proof. exact (@lem5719483 (term136 _119901 _71736 s) ((f _71736) = (@neutral _119887 op))). Qed.
Lemma lem5719486 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5719487 {_119901 : Type'} (_71736 : _119901) (s : _119901 -> Prop) : (term143 _119901 _71736 s) = (@IN _119901 _71736 s).
Proof. exact (@lem5719486 (@IN _119901 _71736 s)). Qed.
Lemma lem5719488 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5719489 {_119901 : Type'} (_71736 : _119901) (s : _119901 -> Prop) : (term144 _119901 _71736 s) = (term145 _119901 _71736 s).
Proof. exact (MK_COMB (@lem5719488) (@lem5719487 _119901 _71736 s)). Qed.
Lemma lem5719490 {_119887 _119901 : Type'} (f : _119901 -> _119887) (_71736 : _119901) (op : type1400 _119887) : ((f _71736) = (@neutral _119887 op)) = ((f _71736) = (@neutral _119887 op)).
Proof. exact (eq_refl ((f _71736) = (@neutral _119887 op))). Qed.
Lemma lem5719491 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (_71736 : _119901) (op : type1400 _119887) : (term142 _119887 _119901 s f _71736 op) = (term45 _119887 _119901 s f _71736 op).
Proof. exact (MK_COMB (@lem5719489 _119901 _71736 s) (@lem5719490 _119887 _119901 f _71736 op)). Qed.
Lemma lem5719492 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (_71736 : _119901) (op : type1400 _119887) : (term138 _119887 _119901 f op _71736 s) = (term45 _119887 _119901 s f _71736 op).
Proof. exact (TRANS (@lem5719484 _119887 _119901 s f _71736 op) (@lem5719491 _119887 _119901 s f _71736 op)). Qed.
Lemma lem5719495 {_119887 _119901 : Type'} (_71736 : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term45 _119887 _119901 s f _71736 op.
Proof. exact (EQ_MP (@lem5719492 _119887 _119901 s f _71736 op) (@lem5719481 _119887 _119901 _71736 s f x op h1)). Qed.
Lemma lem5719496 {_119887 _119901 : Type'} (_71736 : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term45 _119887 _119901 s f _71736 op.
Proof. exact (@lem5719495 _119887 _119901 _71736 s f x op h1). Qed.
Lemma lem5719497 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term45 _119887 _119901 s f x op.
Proof. exact (@lem5719496 _119887 _119901 x s f x op h1). Qed.
Lemma lem5719500 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : (f x) = (@neutral _119887 op).
Proof. exact (@lem5719497 _119887 _119901 s f x op h1 (@lem5719448 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719501 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term146 _119887 _119901 f x op.
Proof. exact (fun h0 : term65 _119887 _119901 f x op => @lem5719500 _119887 _119901 s f x op h1). Qed.
Lemma lem5719503 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5719504 {_119887 _119901 : Type'} (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term146 _119887 _119901 f x op) = ((f x) = (@neutral _119887 op)).
Proof. exact (@lem5719503 ((f x) = (@neutral _119887 op))). Qed.
Lemma lem5719505 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : (f x) = (@neutral _119887 op).
Proof. exact (EQ_MP (@lem5719504 _119887 _119901 f x op) (@lem5719501 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719508 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5719510 {_119887 _119901 : Type'} (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term65 _119887 _119901 f x op) = (term147 _119887 _119901 f x op).
Proof. exact (@lem5719508 ((f x) = (@neutral _119887 op))). Qed.
Lemma lem5719513 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term147 _119887 _119901 f x op.
Proof. exact (EQ_MP (@lem5719510 _119887 _119901 f x op) (@lem5719388 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719516 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : False.
Proof. exact (@lem5719513 _119887 _119901 s f x op h1 (@lem5719505 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719517 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : term148.
Proof. exact (fun h0 : ~ False => @lem5719516 _119887 _119901 s f x op h1). Qed.
Lemma lem5719519 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5719520 : term148 = False.
Proof. exact (@lem5719519 False). Qed.
Lemma lem5719521 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) (h1 : term94 _119887 _119901 s f x op) : False.
Proof. exact (EQ_MP (@lem5719520) (@lem5719517 _119887 _119901 s f x op h1)). Qed.
Lemma lem5719566 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : @IN _119901 x s.
Proof. exact (proj1 (@lem5719328 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719567 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term135 _119901 x s.
Proof. exact (fun h0 : term136 _119901 x s => @lem5719566 _119887 _119901 x s f op h1). Qed.
Lemma lem5719569 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5719570 {_119901 : Type'} (x : _119901) (s : _119901 -> Prop) : (term135 _119901 x s) = (@IN _119901 x s).
Proof. exact (@lem5719569 (@IN _119901 x s)). Qed.
Lemma lem5719571 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : @IN _119901 x s.
Proof. exact (EQ_MP (@lem5719570 _119901 x s) (@lem5719567 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719577 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5719578 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71737 : _119901) (s : _119901 -> Prop) : (term50 _119887 _119901 s f _71737 op) = (term138 _119887 _119901 f op _71737 s).
Proof. exact (@lem5719577 ((f _71737) = (@neutral _119887 op)) (term136 _119901 _71737 s)). Qed.
Lemma lem5719586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5719587 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71737 : _119901) (s : _119901 -> Prop) : (term139 _119887 _119901 s f _71737 op) = (term140 _119887 _119901 f op _71737 s).
Proof. exact (MK_COMB (@lem5719586) (@lem5719578 _119887 _119901 f op _71737 s)). Qed.
Lemma lem5719595 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71737 : _119901) (s : _119901 -> Prop) : (term138 _119887 _119901 f op _71737 s) = (term138 _119887 _119901 f op _71737 s).
Proof. exact (eq_refl (term138 _119887 _119901 f op _71737 s)). Qed.
Lemma lem5719596 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71737 : _119901) (s : _119901 -> Prop) : ((term50 _119887 _119901 s f _71737 op) = (term138 _119887 _119901 f op _71737 s)) = ((term138 _119887 _119901 f op _71737 s) = (term138 _119887 _119901 f op _71737 s)).
Proof. exact (MK_COMB (@lem5719587 _119887 _119901 f op _71737 s) (@lem5719595 _119887 _119901 f op _71737 s)). Qed.
Lemma lem5719598 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5719599 (x : Prop) : (x = x) = True.
Proof. exact (@lem5719598 Prop x). Qed.
Lemma lem5719600 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71737 : _119901) (s : _119901 -> Prop) : ((term138 _119887 _119901 f op _71737 s) = (term138 _119887 _119901 f op _71737 s)) = True.
Proof. exact (@lem5719599 (term138 _119887 _119901 f op _71737 s)). Qed.
Lemma lem5719601 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71737 : _119901) (s : _119901 -> Prop) : ((term50 _119887 _119901 s f _71737 op) = (term138 _119887 _119901 f op _71737 s)) = True.
Proof. exact (TRANS (@lem5719596 _119887 _119901 f op _71737 s) (@lem5719600 _119887 _119901 f op _71737 s)). Qed.
Lemma lem5719602 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71737 : _119901) (s : _119901 -> Prop) : True = ((term50 _119887 _119901 s f _71737 op) = (term138 _119887 _119901 f op _71737 s)).
Proof. exact (SYM (@lem5719601 _119887 _119901 f op _71737 s)). Qed.
Lemma lem5719603 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) (_71737 : _119901) (s : _119901 -> Prop) : (term50 _119887 _119901 s f _71737 op) = (term138 _119887 _119901 f op _71737 s).
Proof. exact (EQ_MP (@lem5719602 _119887 _119901 f op _71737 s) (@lem0)). Qed.
Lemma lem5719604 {_119887 _119901 : Type'} (_71737 : _119901) (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term138 _119887 _119901 f op _71737 s.
Proof. exact (EQ_MP (@lem5719603 _119887 _119901 f op _71737 s) (@lem5719394 _119887 _119901 _71737 x s f op h1)). Qed.
Lemma lem5719606 (b : Prop) (a : Prop) : (a \/ b) = (term141 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5719607 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (_71737 : _119901) (op : type1400 _119887) : (term138 _119887 _119901 f op _71737 s) = (term142 _119887 _119901 s f _71737 op).
Proof. exact (@lem5719606 (term136 _119901 _71737 s) ((f _71737) = (@neutral _119887 op))). Qed.
Lemma lem5719609 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5719610 {_119901 : Type'} (_71737 : _119901) (s : _119901 -> Prop) : (term143 _119901 _71737 s) = (@IN _119901 _71737 s).
Proof. exact (@lem5719609 (@IN _119901 _71737 s)). Qed.
Lemma lem5719611 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5719612 {_119901 : Type'} (_71737 : _119901) (s : _119901 -> Prop) : (term144 _119901 _71737 s) = (term145 _119901 _71737 s).
Proof. exact (MK_COMB (@lem5719611) (@lem5719610 _119901 _71737 s)). Qed.
Lemma lem5719613 {_119887 _119901 : Type'} (f : _119901 -> _119887) (_71737 : _119901) (op : type1400 _119887) : ((f _71737) = (@neutral _119887 op)) = ((f _71737) = (@neutral _119887 op)).
Proof. exact (eq_refl ((f _71737) = (@neutral _119887 op))). Qed.
Lemma lem5719614 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (_71737 : _119901) (op : type1400 _119887) : (term142 _119887 _119901 s f _71737 op) = (term45 _119887 _119901 s f _71737 op).
Proof. exact (MK_COMB (@lem5719612 _119901 _71737 s) (@lem5719613 _119887 _119901 f _71737 op)). Qed.
Lemma lem5719615 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (_71737 : _119901) (op : type1400 _119887) : (term138 _119887 _119901 f op _71737 s) = (term45 _119887 _119901 s f _71737 op).
Proof. exact (TRANS (@lem5719607 _119887 _119901 s f _71737 op) (@lem5719614 _119887 _119901 s f _71737 op)). Qed.
Lemma lem5719618 {_119887 _119901 : Type'} (_71737 : _119901) (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term45 _119887 _119901 s f _71737 op.
Proof. exact (EQ_MP (@lem5719615 _119887 _119901 s f _71737 op) (@lem5719604 _119887 _119901 _71737 x s f op h1)). Qed.
Lemma lem5719619 {_119887 _119901 : Type'} (_71737 : _119901) (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term45 _119887 _119901 s f _71737 op.
Proof. exact (@lem5719618 _119887 _119901 _71737 x s f op h1). Qed.
Lemma lem5719620 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term45 _119887 _119901 s f x op.
Proof. exact (@lem5719619 _119887 _119901 x x s f op h1). Qed.
Lemma lem5719623 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : (f x) = (@neutral _119887 op).
Proof. exact (@lem5719620 _119887 _119901 x s f op h1 (@lem5719571 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719624 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term146 _119887 _119901 f x op.
Proof. exact (fun h0 : term65 _119887 _119901 f x op => @lem5719623 _119887 _119901 x s f op h1). Qed.
Lemma lem5719626 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5719627 {_119887 _119901 : Type'} (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term146 _119887 _119901 f x op) = ((f x) = (@neutral _119887 op)).
Proof. exact (@lem5719626 ((f x) = (@neutral _119887 op))). Qed.
Lemma lem5719628 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : (f x) = (@neutral _119887 op).
Proof. exact (EQ_MP (@lem5719627 _119887 _119901 f x op) (@lem5719624 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719631 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5719633 {_119887 _119901 : Type'} (f : _119901 -> _119887) (x : _119901) (op : type1400 _119887) : (term65 _119887 _119901 f x op) = (term147 _119887 _119901 f x op).
Proof. exact (@lem5719631 ((f x) = (@neutral _119887 op))). Qed.
Lemma lem5719636 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term147 _119887 _119901 f x op.
Proof. exact (EQ_MP (@lem5719633 _119887 _119901 f x op) (@lem5719398 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719639 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : False.
Proof. exact (@lem5719636 _119887 _119901 x s f op h1 (@lem5719628 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719640 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : term148.
Proof. exact (fun h0 : ~ False => @lem5719639 _119887 _119901 x s f op h1). Qed.
Lemma lem5719642 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5719643 : term148 = False.
Proof. exact (@lem5719642 False). Qed.
Lemma lem5719644 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term109 _119887 _119901 x s f op) : False.
Proof. exact (EQ_MP (@lem5719643) (@lem5719640 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719645 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term130 _119887 _119901 x s f op) : False.
Proof. exact (or_elim (@lem5719320 _119887 _119901 x s f op h1) (fun h0 : term94 _119887 _119901 s f x op => @lem5719521 _119887 _119901 s f x op h0) (fun h0 : term109 _119887 _119901 x s f op => @lem5719644 _119887 _119901 x s f op h0)). Qed.
Lemma lem5719646 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term130 _119887 _119901 x s f op) : (term130 _119887 _119901 x s f op) = False.
Proof. exact (prop_ext (fun h2 : term130 _119887 _119901 x s f op => @lem5719645 _119887 _119901 x s f op h1) (fun h2 : False => @lem5719320 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719647 {_119887 _119901 : Type'} (x : _119901) (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term130 _119887 _119901 x s f op) : False.
Proof. exact (EQ_MP (@lem5719646 _119887 _119901 x s f op h1) (@lem5719320 _119887 _119901 x s f op h1)). Qed.
Lemma lem5719648 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term48 _119887 _119901 s f op) : False.
Proof. exact (ex_elim (@lem5719227 _119887 _119901 s f op h1) (fun x : _119901 => fun h0 : term132 _119887 _119901 s f op x => @lem5719647 _119887 _119901 x s f op h0)). Qed.
Lemma lem5719649 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term48 _119887 _119901 s f op) : (term48 _119887 _119901 s f op) = False.
Proof. exact (prop_ext (fun h2 : term48 _119887 _119901 s f op => @lem5719648 _119887 _119901 s f op h1) (fun h2 : False => @lem5718889 _119887 _119901 s f op h1)). Qed.
Lemma lem5719650 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) (h1 : term48 _119887 _119901 s f op) : False.
Proof. exact (EQ_MP (@lem5719649 _119887 _119901 s f op h1) (@lem5718889 _119887 _119901 s f op h1)). Qed.
Lemma lem5719651 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : term47 _119887 _119901 s f op.
Proof. exact (fun h0 : term48 _119887 _119901 s f op => @lem5719650 _119887 _119901 s f op h0). Qed.
Lemma lem5719652 {_119887 _119901 : Type'} (s : _119901 -> Prop) (f : _119901 -> _119887) (op : type1400 _119887) : (term24 _119887 _119901 s f op) = (term22 _119887 _119901 s f op).
Proof. exact (EQ_MP (@lem5718888 _119887 _119901 s f op) (@lem5719651 _119887 _119901 s f op)). Qed.
Lemma lem5719657 {_119887 _119901 : Type'} (f : _119901 -> _119887) (op : type1400 _119887) : term28 _119887 _119901 f op.
Proof. exact (fun s : _119901 -> Prop => @lem5719652 _119887 _119901 s f op). Qed.
Lemma lem5719662 {_119887 _119901 : Type'} (op : type1400 _119887) : term32 _119887 _119901 op.
Proof. exact (fun f : _119901 -> _119887 => @lem5719657 _119887 _119901 f op). Qed.
Lemma lem5719667 {_119887 _119901 : Type'} : term36 _119887 _119901.
Proof. exact (fun op : type1400 _119887 => @lem5719662 _119887 _119901 op). Qed.
Lemma lem5719668 {_119887 _119901 : Type'} : term38 _119887 _119901.
Proof. exact (EQ_MP (@lem5718884 _119887 _119901) (@lem5719667 _119887 _119901)). Qed.
Lemma lem5719670 {_119887 _119901 : Type'} : term38 _119887 _119901.
Proof. exact (@lem5718779 _119887 _119901 (@lem5719668 _119887 _119901)). Qed.
Lemma lem5719671 {_119887 _119901 : Type'} (h1 : term39 _119887 _119901) : False.
Proof. exact (@lem5719670 _119887 _119901 (@lem5718763 _119887 _119901 h1)). Qed.
Lemma lem5719672 {_119887 _119901 : Type'} (h1 : term39 _119887 _119901) : (term39 _119887 _119901) = False.
Proof. exact (prop_ext (fun h2 : term39 _119887 _119901 => @lem5719671 _119887 _119901 h1) (fun h2 : False => @lem5718763 _119887 _119901 h1)). Qed.
Lemma lem5719673 {_119887 _119901 : Type'} (h1 : term39 _119887 _119901) : False.
Proof. exact (EQ_MP (@lem5719672 _119887 _119901 h1) (@lem5718763 _119887 _119901 h1)). Qed.
Lemma lem5719674 {_119887 _119901 : Type'} : term38 _119887 _119901.
Proof. exact (fun h0 : term39 _119887 _119901 => @lem5719673 _119887 _119901 h0). Qed.
Lemma lem5719675 {_119887 _119901 : Type'} : term36 _119887 _119901.
Proof. exact (EQ_MP (@lem5718762 _119887 _119901) (@lem5719674 _119887 _119901)). Qed.
Lemma lem5719676 {_119887 _119901 : Type'} : term35 _119887 _119901.
Proof. exact (EQ_MP (@lem5718758 _119887 _119901) (@lem5719675 _119887 _119901)). Qed.
